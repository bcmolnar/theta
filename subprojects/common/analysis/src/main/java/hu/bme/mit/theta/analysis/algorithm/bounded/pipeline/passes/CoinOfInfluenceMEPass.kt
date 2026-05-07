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

class CoinOfInfluenceMEPass<Pr : InvariantProof>(val logger: Logger) : DirectionalMonolithicExprPass<Pr> {

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
    logger.writeln(Logger.Level.RESULT, "Starting Coin of Influence Pass")

    //VARS from Props and invariants are collected for building COI
    val coi_vars = ExprUtils.getVars(monolithicExpr.propExpr)
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

    //BUILD initial graph and find dependencies
    logger.writeln(Logger.Level.RESULT, "Start Collecting Dependencies - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")
    val noIteMonoTrans = ExprUtils.eliminateIte(monolithicExpr.transExpr)
    collectDependency(noIteMonoTrans, dependecy_graphs)

    val keepthem = dependecy_graphs.getValsInGraph()
    val can_remove = mutableListOf<VarDecl<*>>()
    if(keepthem.size != all_vars){
      monolithicExpr.vars.map { it ->
        if (!keepthem.contains(it)) {
          can_remove += it
        }
      }

    }

    if(can_remove.isEmpty()) {
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

  fun collectDependency(expr: Expr<*>, graph: Graph, deps: HashSet<VarDecl<*>> = hashSetOf()) {

    fun getNotInEqVars(expr: Expr<*>, collectTo: HashSet<VarDecl<*>>){
      expr.ops.forEach { it -> if(it !is EqExpr<*>) getNotInEqVars(it, collectTo)}
      expr.ops.forEach { it -> if(it is RefExpr<*>) collectTo.addAll(ExprUtils.getVars(it))}
    }

    if(expr is OrExpr) { expr.ops.forEach { it -> getNotInEqVars(it, deps) }}
    if(expr is AndExpr) deps.removeAll { true }

    expr.ops.forEach { it ->
      if(it is EqExpr<*>) {
        val left = ExprUtils.getVars(it.leftOp)
        val right = ExprUtils.getVars(it.rightOp)
        left.forEach { l ->
          graph.addNode(l)
          right.forEach { r ->
            graph.addToNode(l, r)
          }
        }
      }
    }

    expr.ops.forEach { it -> collectDependency(it, graph, deps)}
  }

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


class Node(
  val data: VarDecl<*>
) {
  val neighbors: MutableSet<Node> = mutableSetOf()

  fun connect(other: Node) {
    neighbors.add(other)
  }
}

class Graph {

  private val nodeMap: MutableMap<VarDecl<*>, Node> = mutableMapOf()

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

  fun connect(a: VarDecl<*>, b: VarDecl<*>) {
    val nodeA = addNode(a)
    val nodeB = addNode(b)
    nodeA.connect(nodeB)
  }

  fun addToNode(
    target: VarDecl<*>,
    elementToAdd: VarDecl<*>
  ): Boolean {
    val targetNode = nodeMap[target] ?: return false

    val newNode = addNode(elementToAdd)
    targetNode.connect(newNode)

    return true
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

      current.neighbors.forEach { neighbor ->
        if (deps.add(neighbor.data)) {
          stack.add(neighbor)
        }
      }
    }
  }
}
