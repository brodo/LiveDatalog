; General patterns come first: when several patterns capture the same node,
; the later one takes precedence.

; Terms

(variable) @variable

(atom) @constant

(string) @string

(number) @number

; Predicates

(schema
  name: (_) @function)

(relation
  predicate: (_) @function)

(column
  name: (variable) @variable.parameter)

; Keywords

[
  "schema"
  "not"
  "order"
  "by"
  "asc"
  "desc"
] @keyword

; Built-in aggregate and term forms

[
  "setof"
  "cons"
] @function.builtin

; Types

(primitive_type) @type.builtin

(list_type
  "list" @type.builtin)

; Operators

[
  "="
  "!="
  "<>"
  "<"
  "<="
  ">"
  ">="
  "+"
  "-"
  "!"
  ":-"
  ":"
] @operator

; Punctuation

[
  "("
  ")"
  "["
  "]"
] @punctuation.bracket

"," @punctuation.delimiter

[
  "."
  "?"
  "~"
] @punctuation.special

(comment) @comment
