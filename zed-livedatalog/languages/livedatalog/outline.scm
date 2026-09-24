; Schemas and rules. Facts are left out: a data file holds too many of them
; for an outline to help.

(schema
  "schema" @context
  name: (_) @name) @item

(rule
  head: (relation
    predicate: (_) @name)) @item
