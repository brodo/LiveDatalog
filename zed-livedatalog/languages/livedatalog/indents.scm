; A rule's body is indented under its head.
(rule
  ":-" @start) @indent

(_
  "(" ")" @end) @indent

(_
  "[" "]" @end) @indent
