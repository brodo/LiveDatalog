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
};
