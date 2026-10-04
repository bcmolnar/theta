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
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import java.util.concurrent.TimeUnit

class COIUtils{
  companion object{
    fun finalLog(varRemoved: Int, allVars: Int, removedExpr: Int, allExpr: Int, startDeps: Long, endDeps: Long, sw: Stopwatch, logger: Logger){
      logger.writeln(Logger.Level.RESULT, "Finished COI - time(ms):${sw.elapsed(TimeUnit.MILLISECONDS)}")
      logger.writeln(Logger.Level.RESULT, "COI Pass - Removed Vars: $varRemoved")
      logger.writeln(Logger.Level.RESULT, "COI Pass - All Vars: $allVars")
      logger.writeln(Logger.Level.RESULT, "COI Pass - Removed Expr: $removedExpr")
      logger.writeln(Logger.Level.RESULT, "COI Pass - All Expr: $allExpr")
      logger.writeln(Logger.Level.RESULT, "COI Pass - Graph Search(ms): ${endDeps - startDeps}")
      logger.writeln(Logger.Level.RESULT, "----------------")
    }

    fun countExprs(expr: Expr<*>): Int {
      var count = 1
      expr.ops.forEach { it -> count += countExprs(it) }
      return count
    }
    fun getNotInEqVarsMashogy(expr: Expr<*>): Set<VarDecl<*>>{
      val forret = mutableSetOf<VarDecl<*>>()
      expr.ops.forEach {
        when (it) {
          is RefExpr<*> -> forret.addAll(ExprUtils.getVars(it))
          is EqExpr<*> -> return@forEach
          else -> forret.addAll(getNotInEqVarsMashogy(it))
        }
      }
      return forret
    }


    /**
     * Find Prime variables and Variables in an expression
     */
    fun assigneeAndDeps(expr: EqExpr<*>): Pair<Set<VarDecl<*>>, Set<VarDecl<*>>> {
      val primes = findPrimeVars(expr)
      val deps = findNotInPrimeVars(expr)
      return Pair(primes, deps)
    }

    fun findPrimeVars(expr: Expr<*>): Set<VarDecl<*>> {
      val forret = mutableSetOf<VarDecl<*>>()
      expr.ops.forEach {
        when (it) {
          is PrimeExpr<*> -> forret.addAll(ExprUtils.getVars(it))
          else -> forret.addAll(findPrimeVars(it))
        }
      }
      return forret
    }

    fun findNotInPrimeVars(expr: Expr<*>): Set<VarDecl<*>> {
      if(expr is RefExpr<*>) return ExprUtils.getVars(expr)
      val forret = mutableSetOf<VarDecl<*>>()
      expr.ops.forEach {
        when (it) {
          is PrimeExpr<*> -> return@forEach
          else -> forret.addAll(findNotInPrimeVars(it))
        }
      }
      return forret
    }
  }
}


/**
 * DEPENDENCY GRAPH IMPLEMENTATION
 */
enum class EdgeType {
  VALUE,  // direct dependency
  GUARD,  // conditional dependency
  INIT    // initialization guard (can be used for special traversal rules)
}

class Edge(
  val to: Node,
  val type: EdgeType
)

class Node(
  val variable: VarDecl<*>
) {
  val neighbours: ArrayList<Edge> = ArrayList(2)

  // Used for O(1) cycle detection without allocating sets
  var visitMark: Int = 0

  fun connect(other: Node, edgeType: EdgeType) {
    neighbours.add(Edge(other, edgeType))
  }
}

class Graph(topnode: VarDecl<*>? = null) {

  val topNode: VarDecl<*>? = topnode

  private val nodeMap: HashMap<VarDecl<*>, Node> = HashMap()

  // global traversal epoch (avoids allocating visited sets)
  private var visitEpoch: Int = 1

  init {
    if (topnode != null) addNode(topnode)
  }

  fun addNode(decl: VarDecl<*>): Node {
    return nodeMap.getOrPut(decl) {
      Node(decl)
    }
  }

  fun connect(a: VarDecl<*>, b: VarDecl<*>, edgeType: EdgeType) {
    val nodeA = addNode(a)
    val nodeB = addNode(b)
    nodeA.connect(nodeB, edgeType)
  }

  private fun visit(node: Node, epoch: Int): Boolean {
    if (node.visitMark == epoch) return false
    node.visitMark = epoch
    return true
  }

  fun getDependenciesMain(target: VarDecl<*>): ArrayList<VarDecl<*>> {
    val result = ArrayList<VarDecl<*>>()
    val start = nodeMap[target] ?: return result

    val epoch = ++visitEpoch

    val stack = ArrayDeque<Node>()
    val output = ArrayDeque<Node>()

    if (visit(start, epoch)) {
      stack.addLast(start)
    }

    while (stack.isNotEmpty()) {
      val current = stack.removeLast()

      output.addLast(current)

      val edges = current.neighbours
      for (i in edges.indices) {
        val next = edges[i].to

        if (visit(next, epoch)) {
          stack.addLast(next)
        }
      }
    }

    while (output.isNotEmpty()) {
      result.add(output.removeLast().variable)
    }

    return result
  }

  fun getDependenciesFastCOI(): ArrayList<VarDecl<*>> {
    val top = topNode ?: throw Exception("TopNode is null")
    return getDependenciesMain(top)
  }
}