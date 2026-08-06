# ADR 0001: Finite `f64` scalar policy

- Status: accepted
- Date: 2026-08-06
- Scope: Project S of
  [`deferred-projects-plan.md`](../deferred-projects-plan.md)

## Context

LiveDatalog's canonical scalars were atoms and exact signed 64-bit integers.
Decimal and exponent-shaped bare literals were reserved and returned
`NumericType`. First-class floating-point support needs a fixed public policy
for non-finite values, overflow, underflow, formatting, and near-miss numeric
syntax before implementation, so that later phases (canonical mixed semantics,
typed embedding) cannot drift.

## Decision

### Finite values only

Only finite `f64` values are representable as scalars. There is no scalar for
NaN or the infinities.

- A float that is NaN reports `NumericType` (NaN is "not a number").
- A float that is an infinity reports `NumericOverflow`.

These rules apply wherever a float enters the system: source literals, the
typed `input.float` descriptor (project phase S3), and arithmetic results
(phase S2). Arithmetic that produces a non-finite result therefore reports
`NumericOverflow` rather than storing the value.

### Literal syntax and rounding

The bare-literal grammar is unchanged from the reserved form: an optional
sign, one or more digits, then a fraction (`.` followed by one or more
digits), an exponent (`e` or `E`, an optional sign, one or more digits), or
both. At least one of fraction or exponent must be present; otherwise the
literal is integer syntax.

- Float literals round to the nearest `f64` (IEEE 754 round-to-nearest-even).
- A literal whose rounded magnitude exceeds the largest finite `f64` reports
  `NumericOverflow` (for example `1e400`).
- Gradual underflow is accepted: literals may denote subnormal values, and a
  literal that rounds to zero denotes canonical zero (for example `1e-999`).
- Integer-shaped literals stay on the checked `i64` path and report
  `NumericOverflow` immediately outside the `i64` range. They never fall back
  to floating point.
- Quoted text always constructs an atom: `'1.0'` remains an atom.

### Canonical numeric identity

An integral float exactly representable as `i64` — including both zero
signs — canonicalizes to the equal integer scalar at intern time. `1`, `1.0`,
and `1e0` share one scalar identity; stored float scalars are therefore either
non-integral or integral with magnitude at least 2^63. Callers never observe
which representation produced a canonical integer.

### Formatting

Floats format deterministically and locale-independently with shortest
round-trip digits:

- non-integral values with magnitude in `[1e-3, 1e16)` use plain decimal
  notation (`0.5`, `-0.025`);
- all other values use scientific notation (`5e-324`, `1e300`,
  `1.7976931348623157e308`).

Both spellings reparse as float literals, and every formatted float parses
back to the same canonical scalar identity. Values canonicalized to integers
format as integers.

### Malformed numeric-looking tokens

A bare token starting with an optional sign and a digit must be valid integer
or float syntax; otherwise it reports `InvalidSyntax`. Tokens such as `1e`,
`1e+`, `1.2.3`, and `12abc` are errors, never atoms. Consequently digit-leading
atoms (constructible only through quoting) always format quoted.

## Consequences

- Numeric recognition, canonicalization, ordering, and formatting live in the
  scalar module; the parser only tokenizes.
- No NaN and no negative zero can be stored, so float equality is exact value
  equality and the total ground order needs no special cases.
- Digit-leading alphanumeric tokens that previously parsed as bare atoms
  (for example `12abc`) now report `InvalidSyntax`; quoting restores the old
  meaning.
- Mixed integer/float ordering must be exact and never round the integer
  through `f64`; comparisons floor the float instead.
