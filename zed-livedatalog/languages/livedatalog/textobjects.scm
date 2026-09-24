; A statement is the closest thing LiveDatalog has to a function: `af`
; selects a whole rule, `if` its body.

(rule
  body: (_) @function.inside) @function.around

[
  (schema)
  (fact)
  (query)
  (retraction)
] @function.around

(comment)+ @comment.around
