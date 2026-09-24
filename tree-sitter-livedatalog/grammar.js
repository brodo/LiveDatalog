/**
 * @file Tree-sitter grammar for LiveDatalog
 *
 * Mirrors the hand-written parser in `src/parser.zig`. Where the two could
 * disagree, that parser is the reference: this grammar is for editors
 * (highlighting, folding, navigation) and accepts the same statements.
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const commaSep1 = (rule) => seq(rule, repeat(seq(',', rule)));

module.exports = grammar({
  name: 'livedatalog',

  extras: ($) => [/\s/, $.comment],

  // Keywords are contextual: `schema`, `order`, `cons` and the type names are
  // ordinary atoms wherever the keyword could not appear, as in the engine.
  word: ($) => $.atom,

  rules: {
    program: ($) => repeat($._statement),

    _statement: ($) =>
      choice($.schema, $.rule, $.fact, $.query, $.retraction),

    // schema p(Name: atom, list(int)).
    schema: ($) =>
      seq(
        'schema',
        field('name', $._predicate_name),
        '(',
        optional(commaSep1($.column)),
        ')',
        '.',
      ),

    column: ($) =>
      choice(
        seq(field('name', $.variable), ':', field('type', $._type)),
        field('type', $._type),
      ),

    _type: ($) => choice($.primitive_type, $.list_type),

    primitive_type: (_) => choice('atom', 'int', 'number', 'any', 'list'),

    list_type: ($) => seq('list', '(', field('element', $._type), ')'),

    fact: ($) => seq(field('head', $.relation), '.'),

    rule: ($) =>
      seq(field('head', $.relation), ':-', field('body', $.body), '.'),

    query: ($) =>
      seq(field('body', $.body), optional(field('order', $.order_by)), '?'),

    retraction: ($) => seq(field('body', $.body), '~'),

    body: ($) => commaSep1($._goal),

    order_by: ($) => seq('order', 'by', commaSep1($.sort_key)),

    sort_key: ($) =>
      seq(
        field('variable', $.variable),
        optional(field('direction', choice('asc', 'desc'))),
      ),

    _goal: ($) =>
      choice(
        $.relation,
        $.negation,
        $.comparison,
        $.arithmetic,
        $.type_test,
        $.setof,
      ),

    relation: ($) =>
      seq(
        field('predicate', $._predicate_name),
        '(',
        optional(commaSep1(field('argument', $._term))),
        ')',
      ),

    // `not` applies to one relation or one test, never to arithmetic.
    negation: ($) =>
      seq('not', choice($.relation, $.comparison, $.type_test)),

    comparison: ($) =>
      seq(
        field('left', $._term),
        field('operator', choice('=', '!=', '<>', '<', '<=', '>', '>=')),
        field('right', $._term),
      ),

    // Output = Left + Right, or Output = Left - Right.
    arithmetic: ($) =>
      seq(
        field('output', $._term),
        '=',
        field('left', $._term),
        field('operator', choice('+', '-')),
        field('right', $._term),
      ),

    type_test: ($) => seq(field('term', $._term), ':', field('type', $._type)),

    // setof(Template, Goal, Result) or setof(Template, (Goal, ...), Result).
    setof: ($) =>
      seq(
        'setof',
        '(',
        field('template', $._term),
        ',',
        field('goal', choice($._goal, $.parenthesized_body)),
        ',',
        field('result', $._term),
        ')',
      ),

    parenthesized_body: ($) => seq('(', commaSep1($._goal), ')'),

    _term: ($) => choice($._primary_term, $.cons_pattern),

    _primary_term: ($) =>
      choice(
        $.variable,
        $._atom,
        $.string,
        $.number,
        $.list,
        $.cons,
      ),

    // H!T: `!` binds within a term and associates to the right.
    cons_pattern: ($) =>
      prec.right(
        seq(field('head', $._primary_term), '!', field('tail', $._term)),
      ),

    cons: ($) =>
      seq(
        'cons',
        '(',
        field('head', $._term),
        ',',
        field('tail', $._term),
        ')',
      ),

    // A trailing comma is allowed: `[a, b,]`.
    list: ($) =>
      seq('[', optional(seq(commaSep1($._term), optional(','))), ']'),

    _predicate_name: ($) =>
      choice($.atom, alias('schema', $.atom), $.string),

    _atom: ($) =>
      choice($.atom, alias('schema', $.atom), alias('cons', $.atom)),

    variable: (_) => /[A-Z][A-Za-z0-9_]*/,

    atom: (_) => /[a-z_][A-Za-z0-9_]*/,

    number: (_) => /[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?/,

    string: (_) =>
      token(choice(/"([^"\\]|\\[\s\S])*"/, /'([^'\\]|\\[\s\S])*'/)),

    comment: (_) =>
      token(
        choice(
          seq('%', /[^\n]*/),
          seq('//', /[^\n]*/),
          seq('/*', /[^*]*\*+([^/*][^*]*\*+)*/, '/'),
        ),
      ),
  },
});
