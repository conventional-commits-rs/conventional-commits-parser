//! A parser for the Conventional Commits specification v1.0.0.
//!
//! # Specification
//!
//! # License
//!
//! The project itself is licensed under the MIT or Apache-2.0 license. The
//! specification excerpts are licensed under the CC BY 3.0.

mod parser;

pub use conventional_commits_types::{Commit, Footer};
pub use parser::{
    parse_commit_msg, BREAKING_CHANGE_TOKEN, BREAKING_CHANGE_WITH_HYPHEN_TOKEN, SEPARATOR_COLON,
    SEPARATOR_HASHTAG,
};
