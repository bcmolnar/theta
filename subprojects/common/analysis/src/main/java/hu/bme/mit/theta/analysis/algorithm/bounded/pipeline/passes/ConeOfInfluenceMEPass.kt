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
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.COIUtils.Companion.assigneeAndDeps
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.COIUtils.Companion.countExprs
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.COIUtils.Companion.finalLog
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.COIUtils.Companion.getNotInEqVarsMashogy
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import java.util.concurrent.TimeUnit

class ConeOfInfluenceMEPass<Pr : InvariantProof>(val logger: Logger) : DirectionalMonolithicExprPass<Pr> {

  lateinit var action: ExprAction
  var removedExpr = 0

  val cnf: Boolean = false;
  val coiFast: Boolean = true;
  val returncnf: Boolean = false

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    action = monolithicExpr.action()

    //CALC stat variables
    val all_vars = monolithicExpr.vars.size
    var all_expr = countExprs(monolithicExpr.transExpr) + countExprs(monolithicExpr.initExpr)

    //START COI
    val stopwatch = Stopwatch.createStarted()
    logger.writeln(Logger.Level.RESULT, "Cone of Influence Pass")
    logger.writeln(Logger.Level.RESULT, "CNF: $cnf | Fast-CoI: $coiFast | RetCNF: $returncnf")

    //VARS from Props and invariants are collected for building COI
    logger.writeln(Logger.Level.RESULT, "Building Dependency Graph - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    val coiVars = ExprUtils.getVars(monolithicExpr.propExpr) as MutableSet<VarDecl<*>>
    val invariants = mutableListOf<VarDecl<*>>()
    monolithicExpr.transExpr.ops.map { op ->
      if (op is PrimeExpr<*>) {
        invariants.addAll(ExprUtils.getVars(op.ops))
      }
    }
    coiVars.addAll(invariants)

    /**
     * Init Dependency graph
     */

    val dependencyGraph: Graph;

    if(coiFast){
      val topNode = coiVars.first()
      dependencyGraph = Graph(topNode)
      coiVars.forEach {
        dependencyGraph.connect(topNode, it, EdgeType.INIT)
      }
    }else{
      dependencyGraph = Graph()
      coiVars.forEach { dependencyGraph.addNode(it) }
    }

    /**
     * FIND dependencies
     */
    var exprToCheck: Expr<*>
    if(cnf)
      exprToCheck = ExprUtils.transformEquiSatCnf(ExprUtils.eliminateIte(monolithicExpr.transExpr))
    else
      exprToCheck = ExprUtils.eliminateIte(monolithicExpr.transExpr)

    if(returncnf) all_expr = countExprs(exprToCheck) + countExprs(monolithicExpr.initExpr)

    collectDependency(exprToCheck, dependencyGraph)

    logger.writeln(Logger.Level.RESULT, "Collecting Dependencies - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")
    val startDepSearch = stopwatch.elapsed(TimeUnit.MILLISECONDS)
    val keepThem: MutableSet<VarDecl<*>> = mutableSetOf()
    if(coiFast)
      keepThem.addAll(dependencyGraph.getDependenciesFastCOI())
    else
      coiVars.forEach { keepThem.addAll(dependencyGraph.getDependenciesMain(it))}

    val stopDepSearch = stopwatch.elapsed(TimeUnit.MILLISECONDS)

    /**
     * COLLECT VARS for removal
     */
    logger.writeln(Logger.Level.RESULT, "Collecting Vals for Removal - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    val canRemove = mutableListOf<VarDecl<*>>()
    if(keepThem.size != all_vars){
      monolithicExpr.vars.map { it ->
        if (!keepThem.contains(it)) {
          canRemove += it
        }
      }

    }

    if(canRemove.isEmpty()) {
      logger.writeln(Logger.Level.RESULT, "No Vars to remove - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")
      finalLog(0, all_vars, removedExpr, all_expr,startDepSearch,stopDepSearch,stopwatch, logger)
      return MonolithicExprPassResult(monolithicExpr)
    }

    /**
     * REMOVE VARS
     */
    logger.writeln(Logger.Level.RESULT, "Removing Vars Outside Cone of Influence - t:${stopwatch.elapsed(TimeUnit.MILLISECONDS)}")

    val newInit = removeExpressionsIter(monolithicExpr.initExpr, canRemove)
    val newTrans = if(returncnf) removeExpressionsIter(exprToCheck, canRemove) else removeExpressionsIter(monolithicExpr.transExpr, canRemove)

    if(newInit == null || newTrans == null) {
      logger.writeln(Logger.Level.RESULT, "One of the Expr returned null!!!");
      throw Exception("One of the Expr returned null!!!")
    }
    val forret = MonolithicExpr(
      initExpr = newInit,
      transExpr = newTrans,
      propExpr = monolithicExpr.propExpr,
      transOffsetIndex = monolithicExpr.transOffsetIndex,
      vars = monolithicExpr.vars.filter { it !in canRemove },
      ctrlVars = monolithicExpr.ctrlVars.filter { it !in canRemove },
      events = monolithicExpr.events,
    )
    val afterRemoveAllExpr = countExprs(forret.transExpr) + countExprs(forret.initExpr)
    finalLog(canRemove.size, all_vars, all_expr-afterRemoveAllExpr,all_expr,startDepSearch,stopDepSearch,stopwatch, logger)
    return MonolithicExprPassResult(forret)
  }

  private fun collectDependency(expr: Expr<*>, graph: Graph): Set<VarDecl<*>> {

    if(expr is EqExpr<*>) {
      val (primes, deps) = assigneeAndDeps(expr)

      primes.forEach { p ->
        deps.forEach { d ->
          graph.connect(p, d, EdgeType.VALUE) //Add the right side as VALUE type dependencies
        }
        primes.filter{ x-> x != p}.forEach { p2 ->
          graph.connect(p, p2, EdgeType.VALUE) //All primes depend on each other
        }
      }
      return primes
    }

    val all_dependents = mutableSetOf<VarDecl<*>>()
    expr.ops.forEach { a ->
      val dependents = collectDependency(a, graph)
      all_dependents.addAll(dependents)
      if(dependents.isNotEmpty() && expr is OrExpr) {
        val deps = mutableSetOf<VarDecl<*>>()
        expr.ops.filter{ b -> b != a}.forEach { c ->
          deps.addAll(getNotInEqVarsMashogy(c) )
        }

        dependents.forEach { d -> deps.forEach { e -> graph.connect(d, e, EdgeType.GUARD) } }
        graph.connect(
          ExprUtils.getVars(expr).first(),
          dependents.first(),
          EdgeType.GUARD
        )
      }
    }

    return all_dependents
  }

  //
  private fun <T : Type> removeExpressionsIter(expr: Expr<T>, toRemove: List<VarDecl<*>>): Expr<T>?{
    if(expr is OrExpr || expr is AndExpr){

      val keepers = ArrayList<Expr<*>>()
      for (op in expr.ops) {
        val cleaned = removeExpressionsIter(op, toRemove)
        if (cleaned != null) {
          keepers.add(cleaned)
        }
      }
      if (keepers.isEmpty()) {
        return null
      }

      var keepersNumExpr = 0
      keepers.forEach { k-> keepersNumExpr += countExprs(k)}

      val delta = countExprs(expr) - keepersNumExpr
      removedExpr += delta
      return expr.withOps(keepers)
    }
    if(ExprUtils.getVars(expr).intersect(toRemove).isNotEmpty()) return null
    return expr
  }
}
