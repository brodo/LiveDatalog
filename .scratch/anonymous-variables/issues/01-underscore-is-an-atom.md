# `_` is an atom, not an anonymous variable

Status: needs-triage

`_` parses as the atom `_`, because only a name starting with an uppercase
letter is a variable. So `p(X, _)?` matches only facts whose second argument
is literally the atom `_`, and returns nothing against `p(a, b).` — silently.
Most Datalogs, and Prolog, read `_` as an anonymous variable (each occurrence
a fresh one), and many also `_Name`.

Found while adding variable support to the language listener, which treats
only uppercase names as variables to match.

## To decide

- Should `_` be an anonymous variable? Should `_Name` be a named variable
  that singleton checks ignore?
- What happens to existing programs that use the atom `_` — quote it as
  `'_'`?
- A predicate name may start with `_` today (`_p(a).`); does that stay?

## Follow-up it unblocks

A singleton-variable warning in the language listener (a variable occurring
once in its scope is usually a typo, as in `q(X) :- p(Xs).`). It needs a way to
mark an intentional singleton, which `_`/`_Name` would give.
