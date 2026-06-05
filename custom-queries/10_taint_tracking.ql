/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards // NUOVO IMPORT! Questa è la libreria magica.

class NetworkByteSwap extends Expr {
  NetworkByteSwap () {
    exists(MacroInvocation mi |
      mi.getMacroName() in ["ntohs", "ntohl", "ntohll"] and
      this = mi.getExpr()
    )
  }
}

module MyConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    source.asExpr() instanceof NetworkByteSwap
  }

  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall call |
      call.getTarget().getName() = "memcpy" and
      sink.asExpr() = call.getArgument(2)
    )
  }

  // NUOVA BARRIERA
  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition guard, VariableAccess access |
      // 1. La guardia (l'if) decide se il codice del nostro nodo verrà eseguito
      guard.controls(node.asExpr().getBasicBlock(), _) and
      // 2. La guardia usa una variabile al suo interno
      guard.getAChild*() = access and
      // 3. e quella variabile è la stessa identica che sta arrivando alla memcpy!
      access.getTarget() = node.asExpr().(VariableAccess).getTarget()
    )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink) 
select sink, source, sink, "Network byte swap flows to memcpy (Verified via Guards!)"