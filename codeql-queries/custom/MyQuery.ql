/**
 * Title: Avoid false positive when logging masked passwords
 * Description: Suppresses alerts when logging masked versions of sensitive data
 */

import javascript
import semmle.javascript.security.dataflow.ClearTextLogging
import DataFlow::PathGraph

class MaskedPasswordSanitizer extends TaintTracking::Sanitizer {
  MaskedPasswordSanitizer() { this = "MaskedPasswordSanitizer" }

  override predicate isSanitizer(DataFlow::Node node) {
    exists(FunctionCall fc |
      fc.getCalleeName() = "maskPassword" and
      node.asExpr() = fc
    )
  }
}

from ClearTextLogging::Source src, ClearTextLogging::Sink sink, PathNode path
where
  path.hasFlow(src, sink) and
  not exists(MaskedPasswordSanitizer sanitizer | sanitizer.isSanitizer(path.getNode(0)))
select sink, "Sensitive data from $@ is logged in clear text.", src, "this source"
