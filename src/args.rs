//! Module for handling command line arguments.

use std::borrow::Cow;
//use std::error::Error;
use std::fmt;
use std::ffi::OsString;
use std::iter::IntoIterator;
use std::path::PathBuf;
use std::str::FromStr;
use crate::Error;

use clap::{Parser};
use conv::errors::NoError;
use semver::{Version, VersionReq, ReqParseError, SemVerError};

use super::{NAME, VERSION};


/// Parse application options from given array of arguments
/// (*all* arguments, including binary name).
#[inline]
pub fn parse<I, T>(argv: I) -> Options
    where I: IntoIterator<Item=T>, T: Clone + Into<OsString> + PartialEq<str>
{
    // Detect `cargo intern` invocation, and remove the subcommand name.
    let mut argv: Vec<_> = argv.into_iter().collect();
    if argv.len() >= 2 && &argv[1] == "intern" {
        argv.remove(1);
    }

    Options::parse()
}


/// Structure to hold options received from the command line.
#[derive(Parser, Debug)]
#[clap(name = NAME, version = VERSION, author = "todo")]
pub struct Options {
    /// Crate to download.
    /// This can be just a crate name (like \"foo\"), in which case
    /// the newest version of the crate is fetched.
    /// Alternatively, the VERSION requirement can be given after
    /// the equal sign (=) in the usual Cargo.toml format
    /// (e.g. \"foo==0.9\" for the exact version).
    pub crate_: Crate,

    /// Verbosity of the logging output.
    ///
    /// Corresponds to the number of times the -v flag has been passed.
    #[clap(short, long, default_value("0"))]
    pub verbosity: isize,

    /// Whether to extract the crate's archive.
    /// Specify this flag to have the crate extracted automatically.
    /// Note that unless changed via the --output flag,
    /// this will extract the files to a new subdirectory
    /// bearing the name of the downloaded crate archive.
    #[clap(short, long, action)]
    pub extract: bool,

    /// Where to output the crate's archive.
    /// Normally, the compressed crate is dumped to standard output,
    /// while the extract one (-x flag) is placed in a directory corresponding
    /// to crate's name.
    /// This flag allows to change that by providing an explicit
    /// file or directory path.
    #[clap(short, long)]
    pub output: Option<Output>,
}

#[allow(dead_code)]
impl Options {
    #[inline]
    pub fn verbose(&self) -> bool { self.verbosity > 0 }
}

/// Specification of a crate to download.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Crate {
    name: String,
    version: CrateVersion,
}
impl FromStr for Crate {
    type Err = CrateError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<_> = s.splitn(2, "=").map(|p| p.trim()).collect();
        let name = parts[0].to_owned();
        if parts.len() < 2 {
            let valid_name =
                name.chars().all(|c| c.is_alphanumeric() || c == '-' || c == '_');
            if valid_name {
                Ok(Crate{
                    name,
                    version: CrateVersion::Other(VersionReq::any()),
                })
            } else {
                Err(CrateError::Name(name))
            }
        } else {
            let version = CrateVersion::from_str(parts[1])?;
            Ok(Crate{name, version})
        }
    }
}
impl Crate {
    #[inline]
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn exact_version(&self) -> Option<&Version> {
        match self.version {
            CrateVersion::Exact(ref v) => Some(v),
            _ => None,
        }
    }

    pub fn version_requirement(&self) -> Cow<VersionReq> {
        match self.version {
            CrateVersion::Exact(ref v) => Cow::Owned(VersionReq::exact(v)),
            CrateVersion::Other(ref r) => Cow::Borrowed(r),
        }
    }
}
impl fmt::Display for Crate {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}={}", self.name, self.version)
    }
}

/// Crate version.
#[derive(Debug, Clone, Eq, PartialEq)]
enum CrateVersion {
    /// Exact version, like =1.0.0.
    Exact(Version),
    /// Non-exact version, like ^1.0.0.
    Other(VersionReq)
}
impl FromStr for CrateVersion {
    type Err = CrateVersionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("=") {
            let version = Version::from_str(&s[1..])?;
            Ok(CrateVersion::Exact(version))
        } else {
            let version_req = VersionReq::from_str(s)?;
            Ok(CrateVersion::Other(version_req))
        }
    }
}
impl fmt::Display for CrateVersion {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &CrateVersion::Exact(ref v) => write!(fmt, "={}", v),
            &CrateVersion::Other(ref r) => write!(fmt, "{}", r),
        }
    }
}

/// Defines where the program's output should ho.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Output {
    /// Output should go to a file or directory of given path.
    Path(PathBuf),
    /// Output should be on standard output.
    Stdout,
}
impl<'s> From<&'s str> for Output {
    fn from(s: &'s str) -> Output {
        if s == "-" {
            Output::Stdout
        } else {
            Output::Path(s.into())
        }
    }
}
impl FromStr for Output {
    type Err = NoError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.into())
    }
}
impl fmt::Display for Output {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Output::Path(ref p) => write!(fmt, "{}", p.display()),
            &Output::Stdout => write!(fmt, "-"),
        }
    }
}

/// Error that can occur while parsing CRATE argument.
#[derive(Debug)]
pub enum CrateError {
    /// General syntax error of the crate specification.
    Name(String),
    /// Error parsing the semver spec of the crate.
    Version(CrateVersionError),
}
impl From<CrateVersionError> for CrateError {
    fn from(input: CrateVersionError) -> Self {
        CrateError::Version(input)
    }
}
impl Error for CrateError {
    fn description(&self) -> &str { "invalid crate specification" }
    fn cause(&self) -> Option<&dyn Error> {
        match self {
            &CrateError::Version(ref e) => Some(e),
            _ => None,
        }
    }
}
impl fmt::Display for CrateError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &CrateError::Name(ref n) => write!(fmt, "invalid crate name `{}`", n),
            &CrateError::Version(ref e) => write!(fmt, "invalid crate version: {}", e),
        }
    }
}

/// Error that can occur while parsing crate version.
#[derive(Debug, Error)]
pub enum CrateVersionError {
    Syntax(SemVerError),
    Semantics(ReqParseError),
}
