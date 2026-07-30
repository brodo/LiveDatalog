# LiveDatalog language tutorial

This tutorial introduces LiveDatalog one idea at a time. You do not need prior
Datalog experience, but you should have Zig 0.16 or newer installed.

## What is Datalog?

A Datalog program describes data as **facts** and derives new information with
**rules**. You retrieve information by asking **queries**.

Unlike an imperative program, a Datalog program says what relationships hold,
not which steps the computer should execute. Rules let you query relationships
that were not written down as facts.

## Your first program

Create a file named `family.dl`:

```datalog
parent(alice, bob).
parent(bob, carol).

parent(alice, Child)?
```

Run it from the repository root:

```sh
zig build run -- family.dl
```

LiveDatalog prints:

```text
Child: bob
```

The first two lines are facts. The last line is a query. When a file contains
multiple statements, the command-line interpreter prints the result of the
last statement.

## Facts, atoms, and variables

A fact records a relationship:

```datalog
parent(alice, bob).
person(alice).
age(alice, 36).
```

The name before the parentheses is the **predicate**. The values inside the
parentheses are its **terms**.

Bare terms such as `alice`, `bob`, and `36` are atoms. A term whose first
character is uppercase is a variable:

```datalog
parent(alice, Child)?
```

LiveDatalog finds every value of `Child` that makes the query true. Constants
that begin with an uppercase letter must therefore be quoted.

Use single or double quotes for values containing whitespace, punctuation, or
an initial uppercase letter:

```datalog
note(alice, "works from home").
nickname(alice, 'Al').
note(bob, 'calls it \'the office\'').
```

A backslash escapes a quote or backslash inside a quoted value.

## Queries

A query ends with `?`. Ground queries contain no variables and answer a
yes-or-no question:

```datalog
parent(alice, bob)?
parent(carol, alice)?
```

Run these queries one at a time. They produce `Yes.` and `No.`, respectively,
against the facts above.

A query with variables returns bindings:

```datalog
parent(Parent, Child)?
```

```text
Parent: alice, Child: bob
Parent: bob, Child: carol
```

Separate goals with commas when every condition must be true:

```datalog
parent(alice, Child), parent(Child, Grandchild)?
```

```text
Child: bob, Grandchild: carol
```

The same variable always represents the same value within a query or rule.

## Rules

Rules derive new relationships from existing ones. `:-` can be read as “if”:

```datalog
grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
```

This says: `X` is a grandparent of `Z` if `X` is a parent of `Y` and `Y` is a
parent of `Z`.

Now this query succeeds even though `grandparent(alice, carol)` was not entered
as a fact:

```datalog
grandparent(alice, Grandchild)?
```

```text
Grandchild: carol
```

Every variable in a rule's head must be made available by its body. This rule
is invalid because nothing determines `Y`:

```datalog
unknown_parent(X, Y) :- person(X).
```

## Recursive rules

A rule may refer to its own predicate. Recursion is useful for relationships
such as ancestry and reachability:

```datalog
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- ancestor(X, Z), parent(Z, Y).
```

The first rule is the base case: every parent is an ancestor. The second rule
extends a known ancestry relationship by one generation.

```datalog
ancestor(alice, Descendant)?
```

```text
Descendant: bob
Descendant: carol
```

LiveDatalog rejects recursive rules that can grow forever. Structural list
recursion is allowed when a recursive call consumes a list tail; unrestricted
arithmetic generators and structurally growing recursion are rejected.

## Equality and comparisons

LiveDatalog provides these built-in operators:

- `=` for equality or binding
- `!=` and `<>` for inequality
- `<`, `<=`, `>`, and `>=` for numeric comparisons

Use a positive goal to bind variables before comparing them:

```datalog
age(alice, 36).
age(bob, 17).

adult(Person) :- age(Person, Years), Years >= 18.
adult(Person)?
```

```text
Person: alice
```

For every operator except `=`, both operands must already be bound. Equality
may bind one unbound side:

```datalog
person(alice).
same_person(X) :- person(X), X = alice.
```

Equality cannot bind two unbound variables. Numeric-looking atoms compare by
numeric value for equality, so `1 = 1.0` succeeds. Equality on other atoms and
structural values uses their actual contents.

## Negation

Write `not` before a goal to require that it has no match:

```datalog
person(alice).
person(bob).
employed(alice).

idle(X) :- person(X), not employed(X).
idle(X)?
```

```text
X: bob
```

Variables in a negated goal must already be bound by a positive goal. For
example, `person(X)` binds `X` before `not employed(X)` checks it.

Negation must also be **stratified**: it cannot participate in a recursive
cycle. LiveDatalog rejects this program:

```datalog
p(X) :- q(X).
q(X) :- not p(X), seed(X).
```

## Retracting facts

End a goal with `~` to remove matching base facts:

```datalog
parent(bob, carol)~
```

The interpreter prints `Yes.` if it removed at least one fact and `No.` if
nothing matched. Variables can retract multiple matching facts:

```datalog
parent(alice, Child)~
```

Rules are not retracted. Derived facts are recomputed from the remaining base
facts and rules the next time you run a query.

## Lists

Lists are useful for representing ordered collections as a single value. For
example, they can hold the children of a person, a path through a graph, or a
pair of values projected by an aggregate. Because lists are ordinary structural
terms, they can be nested, stored in facts, passed between relations, and
decomposed with pattern matching. This keeps collection processing in the
language: recursive relations can calculate properties such as length or sum
without requiring a separate built-in aggregate for each operation.

Lists are terms, so they must appear inside a fact, rule, query, or comparison.
Write a list with square brackets:

```datalog
items([]).
items([a, b, c]).
items([a, [b, c]]).
```

LiveDatalog also provides `cons(Head, Tail)` as term syntax for constructing a
list one element at a time. It is not a predicate and cannot be used as a
standalone statement. This complete program stores a list built with `cons`:

```datalog
items(cons(a, cons(b, []))).
items(Value)?
```

```text
Value: [a, b]
```

The value is printed as `[a, b]` because
`cons(a, cons(b, []))` and `[a, b]` are two ways to write the same list.

Use the `H!T` pattern to split a non-empty list into its head (`H`) and tail
(`T`):

```datalog
[alice, bob] = H!T?
```

```text
H: alice, T: [bob]
```

Lists enable ordinary recursive relations:

```datalog
length([], 0).
length(H!T, N) :- length(T, M), N = M + 1.

length([a, b, c], N)?
```

```text
N: 3
```

The variable `H` is unused here, but matching `H!T` proves that the input is a
non-empty list and makes the smaller tail available to the recursive call.

## Integer arithmetic

LiveDatalog supports addition and subtraction in equality expressions:

```datalog
N = A + B
N = A - B
```

Both operands on the right must already be bound integer atoms. Operations use
checked signed 64-bit arithmetic. Non-integer operands and overflow produce an
error.

Arithmetic can be used safely with structurally decreasing list recursion:

```datalog
sum([], 0).
sum(H!T, N) :- sum(T, M), N = M + H.

sum([1, 2, 3], Total)?
```

```text
Total: 6
```

## Aggregation with `setof`

`setof` is useful when a rule needs to turn all solutions of a goal into one
collection—for example, grouping every child by parent or collecting every node
reachable from a starting point. It expresses the collection declaratively,
without rules that manually build an accumulator. The result is deduplicated
and deterministically ordered, so it does not depend on fact or rule insertion
order. It also succeeds with an empty list when there are no matches, allowing
outer groups to remain in the result. The resulting list can then be passed to
ordinary list relations for operations such as length, sum, or further
structural processing.

`setof(Template, Goal, Result)` collects every distinct, fully determined value
of `Template` produced by `Goal`:

```datalog
person(alice).
person(bob).
parent(alice, bob).

children(X, Children) :- person(X), setof(Y, parent(X, Y), Children).
children(X, Children)?
```

```text
X: alice, Children: [bob]
X: bob, Children: []
```

Results are deterministically ordered. If the goal has no matches, `setof`
succeeds with `[]`.

Parenthesize a body containing multiple goals:

```datalog
setof([Score, Student], (score(Test, Student, Score), passed(Student)), Results)
```

Variables that correlate an aggregate with its surrounding rule must be bound
before the aggregate. Variables local to its template or body cannot escape
the aggregate. Aggregates may be nested, but an aggregate cannot recursively
depend on the predicate whose rule contains it.

The checked-in example combines `setof` with recursive list length:

```sh
zig build run -- examples/aggregation.dl
```

```text
X: alice, N: 1
X: bob, N: 0
```

## Comments

LiveDatalog accepts three comment styles:

```datalog
% A percent comment runs to the end of the line.
person(alice). // So does a double-slash comment.

/* Block comments may
   span multiple lines. */
person(bob).
```

## Syntax reference

```datalog
% Fact
predicate(atom, value).

% Rule
derived(X) :- source(X), condition(X).

% Query
derived(X)?

% Retraction
source(X)~

% Negation
allowed(X) :- item(X), not blocked(X).

% Equality, inequality, and numeric comparison
X = value
X != Y
X <> Y
N < 10
N <= 10
N > 10
N >= 10

% List terms (use them inside a statement)
[]
[a, b, c]
H!T
cons(H, T)

% Aggregate
setof(Template, Goal, Result)
setof(Template, (Goal1, Goal2), Result)
```

When experimenting interactively, start the REPL with `zig build run`. Enter
one statement per line, use `.help` for a reminder, and use `.quit` or `.exit`
to leave.
