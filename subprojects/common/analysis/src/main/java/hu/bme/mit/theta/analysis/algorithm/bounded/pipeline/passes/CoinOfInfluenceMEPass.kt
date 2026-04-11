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
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils

class CoinOfInfluenceMEPass<Pr : InvariantProof> : DirectionalMonolithicExprPass<Pr> {

  //data class CoinOfInfluence(val props: Expr<BoolType>, val )
  lateinit var action: ExprAction

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    action = monolithicExpr.action()
    val coi_vars = ExprUtils.getVars(monolithicExpr.propExpr)
    collectDependency(monolithicExpr.transExpr, coi_vars as HashSet<VarDecl<*>?>)

    val invariants = mutableListOf<VarDecl<*>>()
    monolithicExpr.transExpr.ops.map { op ->
      if(op is PrimeExpr<*>){
        invariants.addAll(ExprUtils.getVars(op.ops))
      }
    }
    coi_vars.addAll(invariants)

    val can_remove = mutableListOf<VarDecl<*>?>()
    monolithicExpr.vars.map { it ->
      if(!coi_vars.contains(it)){
        if (it != null) {
          can_remove.add(it)
        }
      }
    }
    can_remove as List<VarDecl<*>>
    val monolithicCompare = monolithicExpr.copy(initExpr = monolithicExpr.initExpr, transExpr = monolithicExpr.transExpr, propExpr = monolithicExpr.propExpr)
    removeOpsFromExpr(monolithicExpr.initExpr, can_remove)
    removeOpsFromExpr(monolithicExpr.transExpr, can_remove)
    removeOpsFromExpr(monolithicExpr.propExpr, can_remove)

    val samesame = monolithicCompare == monolithicExpr
    return MonolithicExprPassResult(
      monolithicExpr.let {

        it.copy(
          initExpr = it.initExpr,
          transExpr = it.transExpr,
          propExpr = it.propExpr,
        )
      }
    )
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
              //System.out.println("Check for DEP" + ((IntEqExpr) expr).getLeftOp() + " | " + coi_vars);
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

  fun removeNotDependencyVars(expr: Expr<*>, can_remove: MutableList<VarDecl<*>?>){
    val keep = ArrayList<Expr<*>?>()
    if(can_remove.isEmpty()) return
    expr.getOps().forEach { op: Expr<*>? ->
      for (cr in can_remove) {
        if (!ExprUtils.getVars(op).contains(cr)) {
          keep.add(op)
          break
        }
      }
    }
    expr.withOps(keep)
  }

  fun removeOpsFromExpr(expr: Expr<*>, to_remove: List<VarDecl<*>>){
    val rem_large = ArrayList<Expr<*>?>()

    expr.getOps().forEach { op: Expr<*> ->
      val rem_single = ArrayList<Expr<*>?>()

      if (op is EqExpr<*>) {
        if (op.getLeftOp() is PrimeExpr<*>) {
          val prime_vars: MutableSet<VarDecl<*>?> = java.util.HashSet<VarDecl<*>?>()
          ExprUtils.collectVars(op.leftOp, prime_vars)

          op.getLeftOp().ops.forEach { op2: Expr<*> ->
            if(op2 is RefExpr<*> && op2.decl in to_remove){
              rem_large.add(op)
            }
          }
        }
      }else{
        op.getOps().filter { op !in rem_large }.forEach { op2: Expr<*> ->
          if(op2 is RefExpr<*> && op2.decl in to_remove){
            rem_single.add(op2)
          }
        }
      }

      val keep = op.ops.filter { it !in rem_single }
      op.withOps(keep)
    }
    val keep = expr.ops.filter { it !in rem_large }
    expr.withOps(keep)

    expr.ops.forEach { op: Expr<*> -> removeOpsFromExpr(op, to_remove)}
  }
}