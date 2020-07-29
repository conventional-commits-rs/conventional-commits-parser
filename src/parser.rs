use conventional_commits_types::{Commit, Footer, FooterSeparator};
use nom::{
    branch::alt,
    bytes::complete::{tag, take, take_while1},
    character::complete::{line_ending, not_line_ending},
    combinator::{map, map_parser, map_res, not, opt, peek},
    error::{context, ParseError, VerboseError},
    multi::{count, many0},
    sequence::{delimited, preceded, terminated, tuple},
    IResult,
};
use nom_unicode::{complete::alpha1, is_alphabetic};
use std::str::FromStr;
use nom::combinator::{all_consuming, recognize};
use std::hint::unreachable_unchecked;

/// The `BREAKING CHANGE` token.
pub const BREAKING_CHANGE_TOKEN: &str = "BREAKING CHANGE";

/// The `BREAKING-CHANGE` token.
pub const BREAKING_CHANGE_WITH_HYPHEN_TOKEN: &str = "BREAKING-CHANGE";

/// The `:<space>` separator.
pub const SEPARATOR_COLON: &str = ": ";

/// The `<space>#` separator for footer notes.
pub const SEPARATOR_HASHTAG: &str = " #";

/// Parses the commit type.
///
/// A commit type is a consecutive sequence of unicode characters without any
/// whitespace in between.
///
/// # Specification
///
/// 1) Commits MUST be prefixed with a type, which consists of a noun, feat,
/// fix, etc., [...].
///
/// 2) The type `feat` MUST be used when a commit adds a new feature to your
/// application or library.
///
/// 3) The type `fix` MUST be used when a commit represents a bug fix for your
/// application.
fn r#type<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    alpha1(i)
}

/// Parses the commit scope.
///
/// A commit scope is an optional component. If present, it is surrounded by
/// parenthesis.
///
/// # Specification
///
/// 4) A scope MAY be provided after a type. A scope MUST consist of a noun
/// describing a section of the codebase surrounded by parenthesis, e.g.,
/// `fix(parser):`.
///
/// # Implementation
///
/// The current implementation does only allow for consecutive unicode
/// characters without any whitespace in between.
fn scope<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    preceded(tag("("), terminated(alpha1, tag(")")))(i)
}

// A simple colon parser.
fn colon<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    tag(":")(i)
}

// A simple exclamation mark parser.
fn exclamation_mark<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    tag("!")(i)
}

// Parses the `: ` separator.
fn colon_separator<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    let (rest, _) = colon(i)?;
    tag(" ")(rest)
}

/// Parses the commit description.
///
/// A commit description can be made out of any valid unicode character except
/// for a newline.
///
/// # Specification
///
/// 5) A description MUST immediately follow the colon and space after the
/// type/scope prefix. The description is a short summary of the code changes,
/// e.g., `fix: array parsing issue when multiple spaces were contained in
/// string`.
fn description<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    // We parse until the newline and remove it before returning the result.
    // let (rest, desc) = not_line_ending(i)?;
    // let (rest, _) = opt(line_ending)(rest)?;
    // Ok((rest, desc))
    not_line_ending(i)
}

/// Parses the commit body.
///
/// A commit body is an optional component. It consists of every valid unicode
/// character and whitespace. It terminates with a double newline.
///
/// # Specification
///
/// 6) A longer commit body MAY be provided after the short description,
/// providing additional contextual information about the code changes. The body
/// MUST begin one blank line after the description.
///
/// 7) A commit body is free-form and MAY consist of any number of newline
/// separated paragraphs.
// TODO: make function return Option<&str> and do not rely on empty strings being empty bodies.
fn body<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Option<&str>, E> {
    println!("body for: {:?}", i);

    // If the next token is actually a footer, the body is empty.
    if peek::<_, _, E, _>(footer_identifier)(i).is_ok() {
        return Ok((i, None));
    }

    let mut found_newline = false;
    let mut offset_to_split_off = 0usize;

    for (idx, line) in i.lines().enumerate() {
        println!("  idx body@{} -> {:?}", idx, line);
        // Check if the line is just a newline. Since we iterate over each line, the content of the
        // line will be empty in those cases.
        if line.is_empty() {
            println!("  found newline body");
            found_newline = true;
        } else if peek::<_, _, E, _>(footer_identifier)(line).is_ok() && found_newline {
            println!("  peeked at body: {:?}", line);
            // If the current line is a footer identifier, from the beginning until two
            // lines above. This removes the empty line before the footer
            // identifier and leaves the identifier still intact.
            //offset_to_split_off += 1;
            break;
        } else {
            // Reset trigger condition to make sure that we skip paragraphs that are not
            // followed by a footer identifier.
            println!("  newline @body");
            found_newline = false;
        }

        // +1 needed to accommodate for the missing newline that sits between each of
        // the enumerated lines.
        println!("  res: idx body@{} -> {}", idx, line.chars().count());
        offset_to_split_off += line.chars().count() + 1;
        println!("  res: idx body@{} -> offset: {}", idx, offset_to_split_off);
    }

    // let (rest, taken) = take(offset_to_split_off - 1)(i)?;
    // println!("taken: {:?}", taken);
    // println!("rest: {:?}", rest);
    // Ok((rest, taken))
    // println!()
    println!("  idx body@done -> before mapping: {}", offset_to_split_off);

    // Depending on whether a new line has been found and therefore a following footer, the offset has to be shortened by either 1 or 2 chars.
    let to_subtract = if found_newline {
        2
    } else {
        1
    };

    let (rest, b) = map(take(offset_to_split_off - to_subtract), str::trim)(i)?;
    Ok((rest, Some(b)))
}

/// Checks if a given input is a breaking change token.
///
/// # Returns
///
/// `true` if the input matches either
/// [BREAKING_CHANGE](consts.BREAKING_CHANGE_TOKEN.html)
/// or [BREAKING_CHANGE_WITH_HYPHEN_TOKEN](consts.
/// BREAKING_CHANGE_WITH_HYPHEN_TOKEN.html).
fn is_breaking_change_token(i: &str) -> bool {
    i == BREAKING_CHANGE_TOKEN || i == BREAKING_CHANGE_WITH_HYPHEN_TOKEN
}

fn breaking_change_footer_token<'a, E: ParseError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    alt((
        tag(BREAKING_CHANGE_TOKEN),
        tag(BREAKING_CHANGE_WITH_HYPHEN_TOKEN),
    ))(i)
}

/// Returns if the char is a valid footer token char.
///
/// Valid chars are all alphabetic unicode chars and the hyphen.
fn is_footer_token_char(c: char) -> bool {
    is_alphabetic(c) || c == '-'
}

/// Parses all footer tokens except the breaking changes one.
fn footer_token_other<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    // FIXME: use take_while1 with bool function if nom_unicode#3 gets resolved.
    take_while1(is_footer_token_char)(i)
}

/// Parses the footer token.
///
/// # Specification
///
/// 9. A footer’s token MUST use `-` in place of whitespace characters, e.g.,
/// `Acked-by` (this helps differentiate the footer section from a
/// multi-paragraph body). An exception is made for `BREAKING CHANGE`, which MAY
/// also be used as a token.
fn footer_token<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    alt((breaking_change_footer_token, footer_token_other))(i)
}

/// Parses the footer separator.
///
/// The footer separator separates the footer's token from its value.
fn footer_separator<'a, E: ParseError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, FooterSeparator, E> {
    map_res(alt((tag(SEPARATOR_COLON), tag(SEPARATOR_HASHTAG))), |v| {
        FooterSeparator::from_str(v)
    })(i)
}

/// A footer identifier is used to detect footers inside of a commit message.
///
/// The identifier is make out of a footer token followed by a footer separator.
type FooterIdentifier<'a> = (&'a str, FooterSeparator);

/// Parses a footer identifier.
fn footer_identifier<'a, E: ParseError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, FooterIdentifier<'a>, E> {
    tuple((footer_token, footer_separator))(i)
}

/// Parses a footer value.
///
/// A footer value is terminated by the next footer identifier.
///
/// # Specification
///
/// 10. A footer’s value MAY contain spaces and newlines, and parsing MUST
/// terminate when the next valid footer token/separator pair is observed.
fn footer_value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    // let mut char_offset = 0usize;
    // for line in i.lines() {
    //     if peek::<_, _, E, _>(footer_identifier)(line).is_ok() {
    //         char_offset += 1;
    //         break;
    //     }
    //
    //     char_offset += line.chars().count() + 1;
    // }
    //
    // map(take(char_offset - 1), str::trim_end)(i)
    println!("footer: {:?}", i);

    let mut offset_to_split_off = 0usize;
    for (idx, line) in i.lines().enumerate() {
        println!("  idx footer@{} -> {:?}", idx, line);
        // Check if the next line starts a new footer
        if peek::<_, _, E, _>(footer_identifier)(line).is_ok() {
            println!("  peeked at footer: {:?}", line);
            offset_to_split_off += 1;
            break;
        }

        offset_to_split_off += line.chars().count() + 1;
    }

    map(take(offset_to_split_off - 1), str::trim_end)(i)
}

type FooterType<'a> = (&'a str, FooterSeparator, &'a str);

///
///
/// # Specification
///
/// 8. One or more footers MAY be provided one blank line after the body. Each footer MUST consist of a word token, followed by either a :<space> or <space># separator, followed by a string value (this is inspired by the [git trailer convention](https://git-scm.com/docs/git-interpret-trailers)).
fn footer<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, FooterType<'a>, E> {
    println!("input@footer: {:?}", i);
    tuple((footer_token, footer_separator, footer_value))(i)
}

/// The first line of a commit.
///
/// These values MUST be included as defined in the specification.
///
/// # Parameters
///
/// - The commit type.
/// - The optional commit scope.
/// - The optional exclamation mark.
/// - The commit description.
type CommitFirstLine<'a> = (&'a str, Option<&'a str>, Option<&'a str>, &'a str);

/// Parses all mandatory parts of a commit.
///
/// # Specification
///
/// 1) Commits MUST be prefixed with a type, which consists of a noun, `feat`,
/// `fix`, etc., followed by the OPTIONAL scope, OPTIONAL `!`, and REQUIRED
/// terminal colon and space.
///
/// 5) A description MUST immediately follow the colon and space after the
/// type/scope prefix. The description is a short summary of the code changes,
/// e.g., `fix: array parsing issue when multiple spaces were contained in
/// string`.
fn commit<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, CommitFirstLine<'a>, E> {
    map(
        tuple((
            r#type,
            opt(scope),
            opt(exclamation_mark),
            colon_separator,
            description,
        )),
        |(ty, scope, exclamation_mark, _, description)| (ty, scope, exclamation_mark, description),
    )(i)
}

fn footers<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Vec<(&'a str, FooterSeparator, &'a str)>, E> {
    //many0(preceded(opt(line_ending), footer))(i)
    many0(footer)(i)
}

/// Parses a complete commit with all optional parts.
pub fn commit_complete<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Commit<'a>, E> {
    map(
        tuple((
            context("First line", commit),
            context("Optional body", |i| {
                println!("opt body: {:?}", i);
                // The body is separated by one empty line. However, the first line parser does not consume the newline after the description. This has to be done now.
                let (rest, line_end) = opt(line_ending::<_, E>)(i)?;
                if  line_end.is_none() {
                    println!("context:::: body -> no line feed found, assuming no body content. continue with: {:?}", i);
                    // No new line has been found, so the commit message only contains a description.
                    return Ok((i, None));
                } else {
                    println!("{:?}", rest);
                }

                let res = opt::<_, _, E, _>(preceded(line_ending, body))(rest)?;
                println!("not error :) -> {:?}", res);
                let (rest, optional_body) = res;

                // XXX: maybe this can be done better. Not sure how exactly though. The double option feels hacky and as far as I can tell, None doesn't happen anyway as we check it already early on.
                match optional_body {
                    // If None than no body has been found, i.e. only a description. In this case return the original input as the rest.
                    None => Ok((i, None)),
                    Some(inner_optional) => {
                        // If the inner value is None than no body has been found.
                        match inner_optional {
                            None => Ok((i, None)),
                            Some(b) => Ok((rest, Some(b)))
                        }
                    }
                }

                // return match res {
                //     (rest, Some(v)) if v.is_empty() => Ok((i, None)),
                //     (rest, None) => Ok((rest, None)),
                //     (rest, o) => Ok((rest, o)),
                // };

                // TODO: cleanup using conditional match. This didn't work though the first time I
                // tried...
                // return match o {
                //     Some(v) => {
                //         if v.is_none() {
                //             Ok((i, None))
                //         } else {
                //             Ok((rest, v))
                //         }
                //     },
                //     None => {
                //         Ok((i, None))
                //     }
                // };

                // Check if two new lines are occurring before the body part.
                // let res = count::<_, _, E, _>(line_ending, 2)(i);
                // if let Ok((rest, _)) = res {
                //     // If that is the case, run the body parser.
                //     let res: IResult<&str, &str, E> = body(rest);
                //     // Empty bodies are treated as non-existing
                //     // TODO: is this really a good idea? -> investigate!
                //
                //     // XXX: if not explicitly checked, body will always match, even if only a footer
                //     // is present. This is due to the fact that the body is terminated by a footer
                //     // and starts with a double newline. This does even apply to an empty body.
                //     if let Ok((rest, b)) = res {
                //         if b.is_empty() {
                //             println!("body is empty");
                //             return Ok((i, None));
                //         }
                //         return Ok((rest, Some(b)));
                //     }
                // }
                //
                // Ok((i, None))
            }),
            context("Optional footer", |i| {
                // println!("{:?}", i);
                // let res = count::<_, _, E, _>(line_ending, 2)(i);
                // if let Ok((rest, _)) = res {
                //     println!("matching on {:?}", rest);
                //     return many0(footer)(rest);
                // } else {
                //     println!("fucky fucky no matchi matchi");
                // }
                //
                // Ok((i, Vec::new()))
                println!("opt footer: {:?}", i);

                let (rest, line_end) = opt(line_ending::<_, E>)(i)?;
                if  line_end.is_none() {
                    println!("context:::: footer -> no line feed found, assuming no body content. continue with: {:?}", i);
                    // No new line has been found, so the commit message only contains a description.
                    return Ok((i, None));
                } else {
                    println!("rest -> {:?}", rest);
                }

                opt(preceded(line_ending, footers))(rest)
            }),
        )),
        |(first_line, body, footers)| {
            let footers = footers.unwrap_or_else(|| vec![]);
            let footers = footers
                .iter()
                .map(|f| Footer::from(f.0, f.1, f.2))
                .collect::<Vec<_>>();
            let is_breaking_change = first_line.2.is_some()
                || footers
                    .iter()
                    .find(|&f| is_breaking_change_token(f.token))
                    .is_some();

            Commit::from(
                first_line.0,
                first_line.1,
                first_line.3,
                body,
                is_breaking_change,
                footers,
            )
        },
    )(i)
}

pub fn parse_commit_msg(i: &str) -> Result<Commit, VerboseError<&str>> {
    let result = commit_complete::<VerboseError<_>>(i);
    result
        .map_err(|err| match err {
            nom::Err::Error(err) | nom::Err::Failure(err) => {
                println!("{}", nom::error::convert_error(i, err.clone()));
                err
            }
            _ => unreachable!(),
        })
        .map(|t| t.1)
}

#[cfg(test)]
mod tests {
    use super::r#type;
    use crate::parser::{body, description, footer, footer_token, scope, footers};
    use conventional_commits_types::FooterSeparator;
    use nom::{
        error::{ErrorKind, VerboseError},
        Err::Error,
        IResult,
    };

    fn simple_ok(i: &str) -> IResult<&str, &str> {
        Ok(("", i))
    }

    fn simple_rest<'a>(rest: &'a str, i: &'a str) -> IResult<&'a str, &'a str> {
        Ok((rest, i))
    }

    #[test]
    fn test_ty() {
        // ASCII test
        let i = "type";
        let res = simple_ok(i);
        assert_eq!(res, r#type(i));

        // Unicode test
        let i = "日本";
        let res = simple_ok(i);
        assert_eq!(res, r#type(i));

        // Non-alpha1 stops.
        let i = "日本\n";
        let res = simple_rest("\n", "日本");
        assert_eq!(res, r#type(i));
    }

    #[test]
    fn test_scope() {
        // ASCII test
        let i = "(scope)";
        let res = Ok(("", "scope"));
        assert_eq!(res, scope::<VerboseError<&str>>(i));

        // Unicode test
        let i = "(日本)";
        let res = Ok(("", "日本"));
        assert_eq!(res, scope::<VerboseError<&str>>(i));

        // Line breaks stops parsing
        let i = "(日本\n)";
        let res = Err(Error(("\n)", ErrorKind::Tag)));
        assert_eq!(res, scope(i));

        // Missing tags fail parsing
        let i = "(scope";
        let res = Err(Error(("", ErrorKind::Tag)));
        assert_eq!(res, scope(i));

        let i = "scope)";
        let res = Err(Error(("scope)", ErrorKind::Tag)));
        assert_eq!(res, scope(i));
    }

    #[test]
    fn test_description() {
        // ASCII test
        let i = "a short description";
        let res = simple_ok(i);
        assert_eq!(res, description(i));

        // Unicode test
        let i = "日本の本が好き";
        let res = simple_ok(i);
        assert_eq!(res, description(i));

        // Newline stops parsing
        let i = "a short description\n";
        let res = simple_rest("\n", "a short description");
        assert_eq!(res, description(i));
    }

    #[test]
    //#[ignore]
    fn test_body() {
        // // Body without footer
        let i = include_str!("../tests/body_no_footer.txt");
        let res = Ok(("", Some(i)));
        assert_eq!(res, body::<VerboseError<&str>>(i));

        // Body with footer
        let b = include_str!("../tests/body_no_footer.txt");
        let i = include_str!("../tests/body_no_footer2.txt");
        let res = Ok(("\n\nFixes #123", Some(b)));
        assert_eq!(res, body::<VerboseError<&str>>(i));
    }

    #[test]
    fn test_footer_token() {
        let i = "Fixes";
        let res = simple_ok(i);
        assert_eq!(res, footer_token(i));

        let i = "PR-close";
        let res = simple_ok(i);
        assert_eq!(res, footer_token(i));

        let i = "Signed-off-by";
        let res = simple_ok(i);
        assert_eq!(res, footer_token(i));

        let i = "Signed-off-by-日本";
        let res = simple_ok(i);
        assert_eq!(res, footer_token(i));
    }

    #[test]
    fn test_footer() {
        let i = "Fixes #123";
        let expected = Ok(("", ("Fixes", FooterSeparator::SpaceHashTag, "123")));
        assert_eq!(expected, footer::<VerboseError<&str>>(&i));

        let i = "\nFixes #123";
        assert!(footer::<VerboseError<&str>>(&i).is_err());

        let i = "Fixes: 123";
        let expected = Ok(("", ("Fixes", FooterSeparator::ColonSpace, "123")));
        assert_eq!(expected, footer::<VerboseError<&str>>(&i));

        let i = "Signed-off-by: me";
        let expected = Ok(("", ("Signed-off-by", FooterSeparator::ColonSpace, "me")));
        assert_eq!(expected, footer::<VerboseError<&str>>(&i));

        let i = "Check-日本: yes";
        let expected = Ok(("", ("Check-日本", FooterSeparator::ColonSpace, "yes")));
        assert_eq!(expected, footer::<VerboseError<&str>>(&i));
    }

    #[test]
    fn test_footers() {
        let i = "Fixes #123\nPR-Close #432";
        let expected = Ok(("", vec![
            ("Fixes", FooterSeparator::SpaceHashTag, "123"),
            ("PR-Close", FooterSeparator::SpaceHashTag, "432"),
        ]));
        assert_eq!(expected, footers::<VerboseError<&str>>(i));
    }

    #[cfg(feature = "serde")]
    #[test]
    //#[ignore]
    fn test_serialized_commit_messages() -> anyhow::Result<()> {
        use super::parse_commit_msg;
        use conventional_commits_types::Commit;
        use std::path::Path;
        use walkdir::{DirEntry, WalkDir};

        let tests_folder_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/serialized");
        let walker = WalkDir::new(&tests_folder_path).contents_first(true);
        for entry in walker
            .into_iter()
            .filter_entry(|e: &DirEntry| {
                println!("{}", e.path().display());
                if let Some(extension) = e.path().extension() {
                    extension == "txt"
                } else {
                    false
                }
            })
            .filter_map(|e| e.ok())
        {
            let stem = entry.path().file_stem();
            let folder_commit_msg_is_in =
                entry.path().parent().expect("failed to get folder parent");

            let result_ron_file =
                folder_commit_msg_is_in.join(&format!("{}.ron", stem.unwrap().to_str().unwrap()));

            // Parse the commit and compare it to the saved ron commit.
            // We trim the end of the commits as the command I (SirWindfield) used for exporting does
            // append some newlines.
            let commit_content = std::fs::read_to_string(entry.path())?;
            let commit_content_trimmed = commit_content.trim_end();
            let ser_commit_content = std::fs::read_to_string(result_ron_file)?;

            let commit = parse_commit_msg(commit_content_trimmed).expect("parse commit");
            let ser_commit: Commit<'_> = ron::from_str(&ser_commit_content)?;

            // left ron file, right parsed commit.
            assert_eq!(ser_commit, commit, "failed at: {:?}", &stem);
            println!("right assert");
        }

        Ok(())
    }
}
