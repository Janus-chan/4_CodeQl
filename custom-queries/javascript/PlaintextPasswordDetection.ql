/**
 * @name Detect Plain-text Password Assignments
 * @description Detects assignments of plain-text passwords in JavaScript/Node.js code, avoiding masked or hashed outputs.
 * @kind problem
 * @problem.severity warning
 * @id js/plaintext-password-detected
 * @tags security
 *       external/cwe/cwe-312
 */

import javascript
import semmle.javascript.security.dataflow.DataFlow
import semmle.codeql.suppressions.Suppressions

/**
 * Predicate to check if the identifier looks like a password.
 */
predicate isPasswordLikeName(string name) {
  name.toLowerCase().regexpMatch(".*(password|pwd|secret).*")
}

/**
 * Predicate to match common masking function names.
 */
predicate isMaskingFunctionName(string name) {
  name.toLowerCase().regexpMatch(".*(mask|hash|encrypt).*")
}

/**
 * Predicate to identify known hash/base64 patterns.
 */
predicate looksLikeHashedOrBase64(string val) {
  val.regexpMatch("^[a-fA-F0-9]{32,64}$") or
  val.regexpMatch("^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$")
}

/**
 * Tracks masking functions like maskPassword()
 */
class MaskingFunctionCall extends FunctionCall {
  MaskingFunctionCall() {
    exists(Function f |
      this.getCallee() = f.getName() and
      isMaskingFunctionName(f.getName())
    )
  }
}

/**
 * Source: User-controlled or potentially sensitive input
 */
class Source extends DataFlow::SourceNode {
  Source() { this instanceof DataFlow::ParameterNode }
}

/**
 * Sink: Assignment to a variable with "password", "pwd", or "secret" in the name
 */
class Sink extends DataFlow::SinkNode {
  Sink() {
    exists(Variable v |
      v.getName() = name and
      isPasswordLikeName(name) and
      this.asExpr() = v.getAnAccess()
    )
  }
}

/**
 * Path from source to sink not masked by a masking function.
 */
from Source src, Sink sink, DataFlow::PathNode path
where DataFlow::localFlowPath(src, sink, path) and
      not exists(MaskingFunctionCall call |
        call.getArgument(0) = path.getNode().asExpr()
      ) and
      not looksLikeHashedOrBase64(path.getNode().asExpr().toString()) and
      not Suppressions::hasSuppression(path.getNode().getNode(), "no-password")
select sink.getNode(), "Possible plain-text password assignment."
