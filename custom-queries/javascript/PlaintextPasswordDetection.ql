/**
 * @name Detect plain-text password usage
 * @kind path-problem
 * @id js/plaintext-password
 * @problem.severity warning
 * @tags security
 */

import javascript
import semmle.javascript.security.dataflow.TaintTracking
import DataFlow::PathGraph

// 1) Identify password-like names (password, pwd, secret)
predicate isPasswordLike(string name) {
  name.toLowerCase().matches("%password%") or
  name.toLowerCase().matches("%pwd%") or
  name.toLowerCase().matches("%secret%")
}

// 2) Identify masking functions by name
predicate isMaskingFunction(Function f) {
  f.getName().matches("%mask%") or
  f.getName().matches("%hash%") or
  f.getName().matches("%encrypt%")
}

// 3) Check for inline suppression comment: // codeql[no-password]
predicate isSuppressed(Node n) {
  n.getLocation().hasCommentMatching("%codeql[no-password]%")
}

// 4) Taint-tracking config: track from user input → sink
class PasswordFlowConfig extends TaintTracking::Configuration {
  PasswordFlowConfig() { this = "PasswordFlowConfig" }

  override predicate isSource(Node source) {
    // Any expression referencing req.body.* or a getInput(...) call
    source instanceof Expr and source.getText().matches("%req.body.%")
    or
    source instanceof CallExpression and source.getCallee().getName().matches("getInput")
  }

  override predicate isSink(Node sink) {
    // If the RHS of an assignment feeds into a variable whose name is "password", "pwd", or "secret"
    exists(Variable v |
      isPasswordLike(v.getName()) and
      sink = v.getAnAssignment().getRhs()
    )
  }
}

// 5) Find any flow from source → sink, unless it’s masked or suppressed
from PasswordFlowConfig cfg, Node source, Node sink
where cfg.hasFlow(source, sink)
  and not exists(CallExpression call |
    isMaskingFunction(call.getCallee()) and
    call.getArgument(0) = sink
  )
  and not sink.getLocation().getFile().getBaseName().matches("%test%")
  and not isSuppressed(sink)
select sink, source, "Possible use of plain-text password without masking."
