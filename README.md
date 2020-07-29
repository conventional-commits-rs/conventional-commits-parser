# conventional-commits-parser

[![Maintenance](https://img.shields.io/badge/maintenance-actively%20maintained-brightgreen.svg)](https://github.com/conventional-commits-rs/conventional-commits-parser)
[![crates.io](https://img.shields.io/crates/v/conventional-commits-parser.svg)](https://crates.io/crates/conventional-commits-parser)
[![Documentation](https://docs.rs/conventional-commits-parser/badge.svg)](https://docs.rs/conventional-commits-parser)
[![docs_master_badge]][docs_master_url]

> A library for parsing conventional commits.

## Example

```rust
use conventional_commits_parser::parse_commit_msg;

fn main() {
    let msg = "feat(parser)!: remove parsing capabilities";
    let commit = parse_commit_msg(msg).expect("failed to parse commit message");
    println!("{:#?}", commit);
}
```

## Current Properties

- MSRV: 1.41.0 (tested)

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  https://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[docs_master_badge]: https://img.shields.io/badge/docs.rs-master-green
[docs_master_url]: https://<username>.github.io/<reponame>
