# Document highlight

Status: done

Answer `textDocument/documentHighlight`: every name in the draft's last good
parse with the same predicate and arity as the one at the position. A
statement's first name (head of a fact or rule, or a schema's name) is
`Write`; all other names are `Read`. No engine call is needed. Advertise
`documentHighlightProvider`.

## Acceptance

- In `p(a). q(X) :- p(X). p(X)?`, highlighting from any `p` returns three
  ranges: the first `Write`, the others `Read`.
- A same-named predicate of another arity is not highlighted.
- A position not on a predicate returns null.
