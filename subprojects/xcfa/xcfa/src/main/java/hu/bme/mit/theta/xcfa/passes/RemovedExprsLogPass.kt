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
package hu.bme.mit.theta.xcfa.passes

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.*
import java.util.concurrent.TimeUnit

/**
 * Records the total expression/variable counts before COI label removal and logs the final
 * removed expressions/variables count after the later cleanup passes. The first time it runs on a
 * procedure it saves a snapshot; the second time it logs the delta using the internal log function.
 * Only runs when [StaticCoiPass.enabled] is true.
 */
class RemovedExprsLogPass(private val logger: Logger = NullLogger.getInstance()) : ProcedurePass {

  companion object {
    private const val META_KEY_PREFIX = "RemovedExprsLog"

    private fun logStaticCoiResults(
      varRemoved: Int,
      allVars: Int,
      removedExpr: Int,
      allExpr: Int,
      startDeps: Long,
      endDeps: Long,
      sw: Stopwatch,
      logger: Logger
    ) {
      logger.writeln(Logger.Level.RESULT, "----------------")
      logger.writeln(Logger.Level.RESULT, "Finished Static COI - time(ms):${sw.elapsed(TimeUnit.MILLISECONDS)}")
      logger.writeln(Logger.Level.RESULT, "Static COI Pass - Removed Vars: $varRemoved")
      logger.writeln(Logger.Level.RESULT, "Static COI Pass - All Vars: $allVars")
      logger.writeln(Logger.Level.RESULT, "Static COI Pass - Removed Expr: $removedExpr")
      logger.writeln(Logger.Level.RESULT, "Static COI Pass - All Expr: $allExpr")
      logger.writeln(Logger.Level.RESULT, "Static COI Pass - Graph Search(ms): ${endDeps - startDeps}")
      logger.writeln(Logger.Level.RESULT, "----------------")
    }
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val meta = builder.metaData
    val savedKey = "$META_KEY_PREFIX.saved"

    if (meta[savedKey] == null) {
      // Pre-cleanup snapshot
      val allVars = builder.getVars().size
      val allExpr = countAllExprs(builder)
      val sw = Stopwatch.createStarted()
      val startDep = sw.elapsed(TimeUnit.MILLISECONDS)

      meta["$META_KEY_PREFIX.allVars"] = allVars
      meta["$META_KEY_PREFIX.allExpr"] = allExpr
      meta["$META_KEY_PREFIX.stopwatch"] = sw
      meta["$META_KEY_PREFIX.startDepSearch"] = startDep
      meta[savedKey] = true

      logger.writeln(Logger.Level.RESULT, "RemovedExprsLogPass: snapshot allVars=$allVars allExpr=$allExpr")
      return builder
    } else {
      // Post-cleanup logging
      val origAllVars = (meta["$META_KEY_PREFIX.allVars"] as? Int) ?: builder.getVars().size
      val origAllExpr = (meta["$META_KEY_PREFIX.allExpr"] as? Int) ?: countAllExprs(builder)
      val sw = meta["$META_KEY_PREFIX.stopwatch"] as? Stopwatch ?: Stopwatch.createStarted()
      val startDep = (meta["$META_KEY_PREFIX.startDepSearch"] as? Long) ?: 0L

      val newAllVars = builder.getVars().size
      val newAllExpr = countAllExprs(builder)

      val varRemoved = origAllVars - newAllVars
      val removedExpr = origAllExpr - newAllExpr
      val stopDep = sw.elapsed(TimeUnit.MILLISECONDS)

      logStaticCoiResults(varRemoved, origAllVars, removedExpr, origAllExpr, startDep, stopDep, sw, logger)

      // cleanup metadata so repeated runs don't accumulate stale data
      meta.remove("$META_KEY_PREFIX.allVars")
      meta.remove("$META_KEY_PREFIX.allExpr")
      meta.remove("$META_KEY_PREFIX.stopwatch")
      meta.remove("$META_KEY_PREFIX.startDepSearch")
      meta.remove(savedKey)

      return builder
    }
  }

  private fun countAllExprs(builder: XcfaProcedureBuilder): Int {
    var count = 0
    // iterate over all edges and their flat labels
    builder.getEdges().forEach { edge ->
      edge.getFlatLabels().forEach { label ->
        count += countExprsInLabel(label)
      }
    }
    return count
  }

  private fun countExprsInLabel(label: XcfaLabel): Int {
    return when (label) {
      is StmtLabel -> countExprsInStmt(label.stmt)
      is InvokeLabel -> label.params.sumOf { countExprs(it) }
      is StartLabel -> label.params.sumOf { countExprs(it) }
      is ReturnLabel -> countExprsInLabel(label.enclosedLabel)
      is FenceLabel -> countExprs(label.lock)
      else -> 0
    }
  }

  private fun countExprs(expr: Expr<*>): Int {
    var count = 1
    expr.ops.forEach { it -> count += countExprs(it) }
    return count
  }

  private fun countExprsInStmt(stmt: Stmt): Int {
    return when (stmt) {
      is AssignStmt<*> -> countExprs(stmt.expr)
      is AssumeStmt -> countExprs(stmt.cond)
      is MemoryAssignStmt<*, *, *> -> countExprs(stmt.deref) + countExprs(stmt.expr)
      is SkipStmt -> 0
      is HavocStmt<*> -> 0
      is NonDetStmt -> 0
      else -> {
        // Fallback: try to extract expressions via toString parsing is not reliable.
        0
      }
    }
  }
}
