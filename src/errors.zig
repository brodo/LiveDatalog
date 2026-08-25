//! The database's public error set.
//!
//! One set shared by every layer, so a caller handling a failure never has to
//! know which module produced it, and no module has to import another purely
//! to name an error.

pub const Error = error{
    InvalidFact,
    InvalidRule,
    InvalidQuery,
    InvalidTerm,
    InvalidSyntax,
    NotStratified,
    UnboundVariable,
    UnknownOperator,
    NumericType,
    NumericOverflow,
    NotAdmissible,
    UnknownVariable,
    TypeMismatch,
    /// Shadow verification found the maintained closure disagreeing with a
    /// fresh rebuild. Only reachable with `setShadowVerification(true)`.
    MaintenanceMismatch,
    /// Two view extensions a plan may read store under one name and arity, so
    /// no plan reading both could say which it meant. Reported when the
    /// selection is made rather than when a query is folded, because it is a
    /// property of the selection and no query makes it better.
    AmbiguousViewName,
    /// A view was published from a database rule, and the database's rules
    /// have changed since. Folding against it would reason from a definition
    /// the database no longer holds.
    StaleViewDefinition,
    /// A predicate no single rule defines was published as a view. A view has
    /// one definition; a predicate with none, or with several, has no
    /// definition to invert.
    UndefinedView,
    /// A fold handle outlived the views or the rules it was folded against.
    /// The plan it named has been discarded; fold the query again.
    StalePlan,
    /// The plan holds a term the evaluator has no meaning for, so there is
    /// nothing to run. Its rendering still says what it is.
    PlanNotExecutable,
};
