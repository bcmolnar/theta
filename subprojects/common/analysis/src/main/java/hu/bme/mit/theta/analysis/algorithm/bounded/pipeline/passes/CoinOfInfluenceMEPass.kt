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

import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
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
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils

class CoinOfInfluenceMEPass<Pr : InvariantProof>(val logger: Logger) : DirectionalMonolithicExprPass<Pr> {

  //data class CoinOfInfluence(val props: Expr<BoolType>, val )
  lateinit var action: ExprAction

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    action = monolithicExpr.action()
    val coi_vars = ExprUtils.getVars(monolithicExpr.propExpr)
    collectDependency(monolithicExpr.transExpr, coi_vars as HashSet<VarDecl<*>?>)
    val startingvars = monolithicExpr.vars.size
    val invariants = mutableListOf<VarDecl<*>>()
    monolithicExpr.transExpr.ops.map { op ->
      if (op is PrimeExpr<*>) {
        invariants.addAll(ExprUtils.getVars(op.ops))
      }
    }
    coi_vars.addAll(invariants)

    val can_remove = mutableListOf<VarDecl<*>?>()
    monolithicExpr.vars.map { it ->
      if (!coi_vars.contains(it)) {
        if (it != null) {
          can_remove.add(it)
        }
      }
    }

    can_remove as List<VarDecl<*>>
    val monolithicCompare = monolithicExpr.copy(
      initExpr = monolithicExpr.initExpr, transExpr = monolithicExpr.transExpr, propExpr = monolithicExpr.propExpr
    )
    //removeOpsFromExpr(monolithicExpr.initExpr, can_remove)
    //removeOpsFromExpr(monolithicExpr.transExpr, can_remove)
    //removeOpsFromExpr(monolithicExpr.propExpr, can_remove)

    logger.writeln(Logger.Level.RESULT, "COI Pass Removed:${can_remove.size}")
    logger.writeln(Logger.Level.RESULT, "COI Pass All:$startingvars")
    logger.writeln(Logger.Level.RESULT, "COI Pass ExprRem:$removed")

    val forret = monolithicExpr.let { (initExpr, transExpr, propExpr, transOffsetIndex, vars, ctrlVars, events) ->
      MonolithicExpr(
        initExpr = removeRecursiveMain(initExpr, can_remove),
        transExpr = removeRecursiveMain(transExpr, can_remove),
        propExpr = removeRecursiveMain(propExpr, can_remove),
        transOffsetIndex = transOffsetIndex,
        vars = vars.filter { it !in can_remove },
        ctrlVars = ctrlVars,
        events = events,
      )
    }
    return MonolithicExprPassResult(forret)
  }

  fun collectDependency(expr: Expr<*>, coi_vars: HashSet<VarDecl<*>?>) {
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
              ExprUtils.collectVars(expr.rightOp, coi_vars)
            }
          }
        }
      } else {
        expr.getOps().forEach { op: Expr<*>? -> collectDependency(op!!, coi_vars) }
      }

      coi_discovered = coi_last_discovered
      coi_last_discovered = coi_vars.size
    }
  }

  var removed = 0
  fun removeRecursiveMain(expr: Expr<BoolType>, toRemove: List<VarDecl<*>>): Expr<BoolType> {
    val newexpr = removeRecursive(expr, toRemove) as? Expr<BoolType> ?: expr
    return newexpr
  }

  fun removeRecursive(expr: Expr<*>, toRemove: List<VarDecl<*>>): Expr<*>? {
    if (expr is RefExpr && expr.decl in toRemove) {
      return null
    } else if (expr is IteExpr) {
      if (ExprUtils.getVars(expr.cond).any { it in toRemove }) {
        return null
      }
    }

    val removeWithChild =
      expr is PrimeExpr<*> ||
        expr is NotExpr ||
        expr is EqExpr<*> ||
        expr is LtExpr<*> ||
        expr is LeqExpr<*> ||
        expr is UnaryExpr<*, *>

    if (expr.ops.isEmpty()) {
      return expr
    }
    val keepers = ArrayList<Expr<*>>()
    for (op in expr.ops) {
      val cleaned = removeRecursive(op, toRemove)
      if (cleaned == null) {
        if (removeWithChild) {
          return null
        }
        continue
      }
      keepers.add(cleaned)
    }

    if (keepers.isEmpty()) {
      return null
    }

    removed += expr.ops.size-keepers.size
    val newExpr = expr.withOps(keepers)
    return newExpr
  }
}
