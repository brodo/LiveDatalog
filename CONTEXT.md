# LiveDatalog context

## Glossary

### Scalar

A ground, non-structural Datalog value. Scalars include atoms and supported
numeric values. LiveDatalog currently supports exact signed 64-bit integers;
floating-point scalars are reserved for future support.

Bare signed decimal integer literals denote canonical integer values. Quoted
numeric text remains an atom. Bare decimal or exponent-shaped literals are
reserved and return `NumericType` until floating-point scalars are supported.
Bare integer-shaped literals outside the signed 64-bit range return
`NumericOverflow`.

Scalar identity is numeric across integer and floating-point representations.
A future finite floating-point scalar that exactly represents an in-range
integer canonicalizes to that integer scalar, so facts, unification, equality,
and aggregation treat values such as `1` and `1.0` identically.

Mixed integer and floating-point comparisons are exact and do not first coerce
the integer to `f64`. Mixed arithmetic produces a floating-point result, then
canonicalizes an exact in-range integral result back to an integer scalar.

Canonical ground values have a deterministic total order: numbers in numeric
order, atoms in lexical byte order, `nil`, then cons values lexicographically
by head and tail. The total order reports equality exactly when scalar identity
is equal.
