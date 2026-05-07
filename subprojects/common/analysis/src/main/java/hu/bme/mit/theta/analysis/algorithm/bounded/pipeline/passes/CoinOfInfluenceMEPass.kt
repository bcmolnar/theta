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
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.expl.ExplState
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
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import java.util.concurrent.TimeUnit

class CoinOfInfluenceMEPass<Pr : InvariantProof>(val logger: Logger) : DirectionalMonolithicExprPass<Pr> {

  //data class CoinOfInfluence(val props: Expr<BoolType>, val )
  lateinit var action: ExprAction

  var all_vars = 0

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    //action = monolithicExpr.action()
    return MonolithicExprPassResult(monolithicExpr)
    val stopwatch = Stopwatch.createStarted()

    logger.writeln(Logger.Level.RESULT, "Start COI:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    all_vars = monolithicExpr.vars.size

    //Add Vars for collecting dependencies
    val coi_vars = ExprUtils.getVars(monolithicExpr.propExpr)

    //Add invariants
    val invariants = mutableListOf<VarDecl<*>>()
    monolithicExpr.transExpr.ops.map { op ->
      if (op is PrimeExpr<*>) {
        invariants.addAll(ExprUtils.getVars(op.ops))
      }
    }
    coi_vars.addAll(invariants)

    //Init Dependency graphs
    val dependecy_graphs = Graph()
    coi_vars.forEach {
      dependecy_graphs.addNode(it)
    }

    //logger.writeln(Logger.Level.RESULT, "Start collectDependency Time:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")
    //Build Dependency graphs

    collectDependencyNegyedhogy(monolithicExpr.transExpr, coi_vars as HashSet<VarDecl<*>?>, dependecy_graphs)

    val keepthem = hashSetOf<VarDecl<*>>()

    for (v in coi_vars) {
      keepthem.addAll(dependecy_graphs.getDependenciesMain(v!!))
    }

    var can_remove = listOf<VarDecl<*>>()
    monolithicExpr.vars.map { it ->
      if (!keepthem.contains(it)) {
        can_remove += it
      }
    }

    logger.writeln(Logger.Level.RESULT, "----------------")
    logger.writeln(Logger.Level.RESULT, "COI Pass Removed: ${can_remove.size}")
    logger.writeln(Logger.Level.RESULT, "COI Pass All: $all_vars")
    logger.writeln(Logger.Level.RESULT, "COI Pass ExprRem: $removedExprs")
    
    if(can_remove.isNotEmpty()) {
      val forret = MonolithicExpr(
        initExpr = removeRecursiveMain(monolithicExpr.initExpr, can_remove),
        transExpr = removeRecursiveMain(monolithicExpr.transExpr, can_remove),
        propExpr = removeRecursiveMain(monolithicExpr.propExpr, can_remove),
        transOffsetIndex = monolithicExpr.transOffsetIndex,
        vars = monolithicExpr.vars.filter { it !in can_remove },
        ctrlVars = monolithicExpr.ctrlVars,
        events = monolithicExpr.events,
      )
      logger.writeln(Logger.Level.RESULT, "Finish COI Pass Time:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

      return MonolithicExprPassResult(forret)

    }
    logger.writeln(Logger.Level.RESULT, "COI No Vars Removed")
    return MonolithicExprPassResult(monolithicExpr)
  }

  fun collectDependencyHarmadhogy(expr: Expr<*>, coi_vars: HashSet<VarDecl<*>?>, graph: Graph, deps: HashSet<VarDecl<*>?> = hashSetOf()) {
    if (expr.ops.isEmpty()) {
      if (expr is RefExpr) {
        val vars: MutableSet<VarDecl<*>?> = java.util.HashSet<VarDecl<*>?>()
        ExprUtils.collectVars(expr, vars)
        deps.addAll(vars)
      }
      return
    }

    for (it in expr.ops) {
      if (it !is EqExpr<*>) {
        collectDependencyHarmadhogy(it, coi_vars, graph, deps)
      }
    }

    // Végigmegyünk az összes ops-on és az EqExpr típusoknál bővítjük a gráfot.
    // Ha expr OrExpr akkor az itteni EqExpr-re nem vonatkoznak a dependency-k:
    // Az EqExpr-t csak akkor adjuk hozzá, ha az expr AndExpr. ??? Ez így van?
    for (it in expr.ops) {
      if (it is EqExpr<*>) {
        val left = ExprUtils.getVars(it.leftOp)
        val right = ExprUtils.getVars(it.rightOp)

        left.forEach { l -> //csak egy Ref lesz/lehet ref-ben de nem indexelek
          graph.addNode(l!!)
          right.forEach { r ->
            graph.addToNode(l, r!!)
          }
          if (expr is AndExpr) {
            deps.forEach { d ->
              graph.addToNode(l, d!!)
            }
          }

          //For coi_vars list
          if(l in coi_vars){
            right.forEach { r ->
              coi_vars.add(r)
            }
            deps.forEach { d ->
              coi_vars.add(d)
            }
          }
        }

        deps.addAll(left)
      }
    }
  }

  fun collectDependencyNegyedhogy(expr: Expr<*>, coi_vars: HashSet<VarDecl<*>?>, graph: Graph, deps: HashSet<VarDecl<*>?> = hashSetOf()) {
    expr.ops.forEach {
      val all_prime_vars = HashSet<VarDecl<*>>()
      val all_not_prime_vars = HashSet<VarDecl<*>>()
      getAllPrimeVars(it, all_prime_vars)
      getAllNotPrimeVars(it, all_not_prime_vars)
      all_prime_vars.forEach { p ->
        graph.addNode(p)
        all_not_prime_vars.forEach { d ->
          graph.addToNode(p, d)
        }
      }
    }
  }

  fun getAllPrimeVars(expr: Expr<*>, collectTo: HashSet<VarDecl<*>>){
    if(expr.ops.isEmpty()) return
    for (it in expr.ops) {
      if (it is PrimeExpr<*>) {
        collectTo.addAll(ExprUtils.getVars(it))
      } else {
        getAllPrimeVars(it, collectTo)
      }
    }
  }

  fun getAllNotPrimeVars(expr: Expr<*>, collectTo: HashSet<VarDecl<*>>){
    if(expr is PrimeExpr<*>) return
    if(expr is RefExpr) collectTo.addAll(ExprUtils.getVars(expr))
    if(expr.ops.isEmpty()) return
    for (it in expr.ops) {
      getAllNotPrimeVars(it, collectTo)
    }
  }

  fun collectDependency(expr: Expr<*>, coi_vars: HashSet<VarDecl<*>?>, graph: Graph) {
      var coi_discovered = coi_vars.size
      var coi_last_discovered = 0

      while (coi_discovered != coi_last_discovered) {
        // ExprUtils.eliminateIte(monolithicExpr.transExpr)
        // ExprUtils.collectDependency(monolithicExpr.transExpr, coi_vars as HashSet<VarDecl<*>?>?)

        if (expr is EqExpr<*>) {
          if (expr.getLeftOp() is PrimeExpr<*>) {
            val prime_vars: MutableSet<VarDecl<*>?> = java.util.HashSet<VarDecl<*>?>()
            ExprUtils.collectVars(expr.leftOp, prime_vars)
            for (v in prime_vars) {
              if (coi_vars.contains(v)) {
                val new_vars: MutableSet<VarDecl<*>?> = java.util.HashSet<VarDecl<*>?>()
                ExprUtils.collectVars(expr.rightOp, new_vars)
                coi_vars.addAll(new_vars)
                new_vars.forEach {
                  graph.addToNode(v!!, it!!)
                }
              }
            }
          }
        } else {
          expr.getOps().forEach { op: Expr<*>? -> collectDependency(op!!, coi_vars, graph) }
        }

        coi_discovered = coi_last_discovered
        coi_last_discovered = coi_vars.size
      }
  }

  var removedExprs = 0
  fun removeRecursiveMain(expr: Expr<BoolType>, toRemove: List<VarDecl<*>>): Expr<BoolType> {
    val newexpr = removeRecursive(expr, toRemove)
    return newexpr as Expr<BoolType> 
  }

  fun removeRecursive(expr: Expr<*>, toRemove: List<VarDecl<*>>): Expr<*>? {
    if (expr is RefExpr && expr.decl in toRemove) {
      return null
    } else if(expr.ops.isEmpty()) {
      return expr
    }

    val keepers = ArrayList<Expr<*>>()
    for (op in expr.ops) {
      val cleaned = removeRecursive(op, toRemove)
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
    removedExprs += delta
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

  fun size(): Int { return nodeMap.size}

  fun connect(a: VarDecl<*>, b: VarDecl<*>) {
    val nodeA = addNode(a)
    val nodeB = addNode(b)
    nodeA.connect(nodeB)
  }

  fun findVarDecl(predicate: (VarDecl<*>) -> Boolean): VarDecl<*>? {
    val visited = mutableSetOf<Node>()
    val queue: ArrayDeque<Node> = ArrayDeque()

    for (start in nodeMap.values) {
      if (start in visited) continue

      queue.add(start)
      visited.add(start)

      while (queue.isNotEmpty()) {
        val current = queue.removeFirst()

        if (predicate(current.data)) {
          return current.data
        }

        for (neighbor in current.neighbors) {
          if (neighbor !in visited) {
            visited.add(neighbor)
            queue.add(neighbor)
          }
        }
      }
    }

    return null
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
    deps: HashSet<VarDecl<*>> = HashSet<VarDecl<*>>(),
  ){
    //Elkerülni a köröket
    if (!deps.add(target.data)) return
    target.neighbors.forEach {
      getDependencies(it,deps)
    }
  }
}
