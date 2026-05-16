/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.abstracttype.LtExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import java.util.concurrent.TimeUnit

class CoinOfInfluenceMEPass<Pr : InvariantProof>(val cnf: Boolean, val prime_only: Boolean, val naive_collection: Boolean, val list_based: Boolean, val logger: Logger) : DirectionalMonolithicExprPass<Pr> {

  lateinit var action: ExprAction

  var removedExpr = 0

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    action = monolithicExpr.action()

    //CALC stat variables
    fun countExprs(expr: Expr<*>): Int {
      var count = 1
      expr.ops.forEach { it -> count += countExprs(it) }
      return count
    }

    val all_vars = monolithicExpr.vars.size
    val all_expr = countExprs(monolithicExpr.transExpr) + countExprs(monolithicExpr.initExpr)

    //START COI
    val stopwatch = Stopwatch.createStarted()
    logger.writeln(Logger.Level.RESULT, "Coin of Influence Pass")
    logger.writeln(Logger.Level.RESULT, "CNF: $cnf | Prime Only: $prime_only | Naive Collection: $naive_collection | List Based: $list_based")

    //VARS from Props and invariants are collected for building COI
    logger.writeln(Logger.Level.RESULT, "Building Dependency Graph - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    var coi_vars = ExprUtils.getVars(monolithicExpr.propExpr) as MutableSet<VarDecl<*>>
    val invariants = mutableListOf<VarDecl<*>>()
    monolithicExpr.transExpr.ops.map { op ->
      if (op is PrimeExpr<*>) {
        invariants.addAll(ExprUtils.getVars(op.ops))
      }
    }
    coi_vars.addAll(invariants)
    //Init Dependency graph
    val dependecy_graphs = Graph()
    coi_vars.forEach {
      dependecy_graphs.addNode(it)
    }

    //BUILD find dependencies
    logger.writeln(Logger.Level.RESULT, "Collecting Dependencies - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    val exprToCheck = if(cnf) ExprUtils.transformEquiSatCnf(ExprUtils.eliminateIte(monolithicExpr.transExpr)) else ExprUtils.eliminateIte(monolithicExpr.transExpr)
    val keepthem: MutableSet<VarDecl<*>>

    if(list_based) {
      var can_exit = false
      var before_dep_coll_size = coi_vars.size
      while(!can_exit){
        collectDependencyList(exprToCheck, coi_vars)
        if(before_dep_coll_size==coi_vars.size) can_exit = true else before_dep_coll_size = coi_vars.size
      }
      keepthem = coi_vars
    }else {
      collectDependency(exprToCheck, dependecy_graphs)
      keepthem = mutableSetOf()
      ExprUtils.getVars(monolithicExpr.propExpr).forEach { it ->
        keepthem.addAll(dependecy_graphs.getDependenciesMain(it))
      }
    }


    logger.writeln(Logger.Level.RESULT, "Collecting Vals for Removal - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    val can_remove = mutableListOf<VarDecl<*>>()
    if(keepthem.size != all_vars){
      monolithicExpr.vars.map { it ->
        if (!keepthem.contains(it)) {
          can_remove += it
        }
      }

    }

    if(can_remove.isEmpty()) {
      logger.writeln(Logger.Level.RESULT, "No Vars to remove - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")
      finalLog(0, all_vars, removedExpr, all_expr,stopwatch)
      return MonolithicExprPassResult(monolithicExpr)
    }

    logger.writeln(Logger.Level.RESULT, "Removing Vars Outside Cone of Influence - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    //REMOVE vars outside of the cone of influence
    val forret = MonolithicExpr(
      initExpr = removeExprsMain(monolithicExpr.initExpr, can_remove),
      transExpr = removeExprsMain(monolithicExpr.transExpr, can_remove),
      propExpr = removeExprsMain(monolithicExpr.propExpr, can_remove),
      transOffsetIndex = monolithicExpr.transOffsetIndex,
      vars = monolithicExpr.vars.filter { it !in can_remove },
      ctrlVars = monolithicExpr.ctrlVars,
      events = monolithicExpr.events,
    )
    finalLog(can_remove.size, all_vars, removedExpr,all_expr,stopwatch)

    return MonolithicExprPassResult(forret)
  }

  fun finalLog(var_removed: Int, all_vars: Int, removed_exprs: Int, all_expr: Int, sw: Stopwatch){
    logger.writeln(Logger.Level.RESULT, "Finished COI - t:${sw.elapsed(TimeUnit.MILLISECONDS)}")
    logger.writeln(Logger.Level.RESULT, "COI Pass - Removed Vars: $var_removed")
    logger.writeln(Logger.Level.RESULT, "COI Pass - All Vars: $all_vars")
    logger.writeln(Logger.Level.RESULT, "COI Pass - Removed Expr: $removed_exprs")
    logger.writeln(Logger.Level.RESULT, "COI Pass - All Expr: $all_expr")
    logger.writeln(Logger.Level.RESULT, "----------------")
  }

  //Collects All Variables in an Expr that are not part of an EqExpr
  fun getNotInEqVars(expr: Expr<*>, collectTo: HashSet<VarDecl<*>>){
    expr.ops.forEach { it -> if(it !is EqExpr<*>) getNotInEqVars(it, collectTo)}
    expr.ops.forEach { it -> if(it is RefExpr<*>) collectTo.addAll(ExprUtils.getVars(it))}
  }

  //Collects All Variables in an Expr that are in a PrimeExpr
  fun getPrimeExprVars(expr_to_check: Expr<*>, exprs: MutableSet<VarDecl<*>>){
    if(expr_to_check is PrimeExpr<*>) { exprs.addAll(ExprUtils.getVars(expr_to_check)); return }
    expr_to_check.ops.forEach { it -> getPrimeExprVars(it, exprs) }
  }

  fun collectDependencyList(expr: Expr<*>, coi_vars: MutableSet<VarDecl<*>>, deps: HashSet<VarDecl<*>> = hashSetOf()) {
    // Collecting Guard dependencies through Expr tree
    // Looks good might remove later -> All 'OrExpr' up the tree OR only the chain right above to the EqExpr
    if(expr is OrExpr) { expr.ops.forEach { getNotInEqVars(it, deps) }}
    if(expr is AndExpr && !naive_collection) { deps.clear()}

    expr.ops.forEach { it ->
      if(it is EqExpr<*>) {
        val left = ExprUtils.getVars(it.leftOp)
        val right = ExprUtils.getVars(it.rightOp)

        // Add the new node(s) dependent on prime_only: Only the variables that are set for the next transition
        // Looks good might remove later -> Collecting dependencies only for PrimeExpr || Collecting any type of dependency between Exprs
        var left_op_to_add = left
        if(prime_only) getPrimeExprVars(it.rightOp, left_op_to_add)

        left_op_to_add.forEach { l ->
          if(l !in coi_vars) return@forEach
          //Add the right side as VALUE type dependencies
          right.forEach { r -> coi_vars.add(r) }
          //Add the dependencies collected through the path in Expr-tree
          deps.forEach { d -> coi_vars.add(d) }
        }
      }
    }
    expr.ops.forEach { it -> collectDependencyList(it, coi_vars, deps)}
  }

  fun collectDependency(expr: Expr<*>, graph: Graph, deps: HashSet<VarDecl<*>> = hashSetOf()) {
    // Collecting Guard dependencies through Expr tree
    // Looks good might remove later -> All 'OrExpr' up the tree OR only the chain right above to the EqExpr
    if(expr is OrExpr) { expr.ops.forEach { getNotInEqVars(it, deps) }}
    if(expr is AndExpr && !naive_collection) deps.clear()

    expr.ops.forEach { it ->
      if(it is EqExpr<*>) {
        val left = ExprUtils.getVars(it.leftOp)
        val right = ExprUtils.getVars(it.rightOp)

        // Add the new node(s) dependent on prime_only: Only the variables that are set for the next transition
        // Looks good might remove later -> Collecting dependencies only for PrimeExpr || Collecting any type of dependency between Exprs
        var left_op_to_add = left
        if(prime_only) getPrimeExprVars(it.rightOp, left_op_to_add)

        left_op_to_add.forEach { l ->
          //Add the right side as VALUE type dependencies
          right.forEach { r -> graph.connect(l, r, EdgeType.VALUE) }
          //Add the dependencies collected through the path in Expr-tree
          deps.forEach { d -> graph.connect(l, d, EdgeType.GUARD) }
        }
      }
    }
    expr.ops.forEach { it -> collectDependency(it, graph, deps)}
  }

  //Recursive-function removes all variables in the list from the Expr
  fun removeExprsMain(expr: Expr<BoolType>, toRemove: List<VarDecl<*>>): Expr<BoolType> {
    val newexpr = removeExprs(expr, toRemove)
    return newexpr as Expr<BoolType> 
  }

  fun removeExprs(expr: Expr<*>, toRemove: List<VarDecl<*>>): Expr<*>? {
    if (expr is RefExpr && expr.decl in toRemove) {
      return null
    } else if(expr.ops.isEmpty()) {
      return expr
    }

    val keepers = ArrayList<Expr<*>>()
    for (op in expr.ops) {
      val cleaned = removeExprs(op, toRemove)
      if (cleaned == null) {
        if (removeWithChild(expr)) {
          return null
        }
        continue
      }else {
        keepers.add(cleaned)
      }
    }

    if (keepers.isEmpty()) {
      return null
    }

    val delta = expr.ops.size-keepers.size
    removedExpr += delta
    return expr.withOps(keepers)
  }

  fun removeWithChild(expr: Expr<*>): Boolean {
    if (expr is PrimeExpr<*> ||
      expr is NotExpr ||
      // expr is EqExpr<*> ||
      expr is LtExpr<*> ||
      expr is LeqExpr<*> ||
      expr is UnaryExpr<*, *> ||
      expr is BinaryExpr<*,*> ||
      expr is IteExpr<*>){return true}

    return false
  }
}


// Edge Types for Dependencies
enum class EdgeType{
  VALUE, // The dependency is from an EqExpr -> Direct dependence between the nodes
  GUARD // The dependency is a guard condition collected from the Expr Tree -> Indirect dependence, value is not directly used in value assignment
}
class Node(
  val data: VarDecl<*>
) {
  var neighbours: MutableSet<Pair<Node, EdgeType>> = mutableSetOf()

  fun connect(other: Node, edgeType: EdgeType) {
    neighbours.add(Pair(other, edgeType))
  }
}

class Graph {

  private val nodeMap: HashMap<VarDecl<*>, Node> = hashMapOf<VarDecl<*>, Node>()

  fun addNode(decl: VarDecl<*>): Node {
    return nodeMap.getOrPut(decl) {
      Node(decl)
    }
  }

  fun contains(decl: VarDecl<*>): Boolean {
    return nodeMap.containsKey(decl)
  }

  fun getValsInGraph(): Set<VarDecl<*>> {
    return nodeMap.keys
  }
  fun size(): Int { return nodeMap.size}

  fun connect(a: VarDecl<*>, b: VarDecl<*>, edgeType: EdgeType) {
    val nodeA = addNode(a)
    val nodeB = addNode(b)
    nodeA.connect(nodeB, edgeType)

  }

  fun getDependenciesMain(target: VarDecl<*>):HashSet<VarDecl<*>>{
    val forret = HashSet<VarDecl<*>>()
    nodeMap[target]?.let { getDependencies(it, forret) }
    return forret
  }

  fun getDependencies(
    target: Node,
    deps: HashSet<VarDecl<*>>,
  ) {
    val stack = ArrayDeque<Node>()

    if (deps.add(target.data)) {
      stack.add(target)
    }

    while (stack.isNotEmpty()) {
      val current = stack.removeLast()

      current.neighbours.forEach { neighbour ->
        if (deps.add(neighbour.first.data)) {
          stack.add(neighbour.first)
        }
      }
    }
  }
}
