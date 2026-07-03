use anyhow::Context;
use clap::Parser;
use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
};

/// Quint ソースのコメント/コードを分離し、literate な Markdown を出力する。
#[derive(Parser)]
struct Opts {
    #[clap(short, long, default_value = "/dev/stdout")]
    output: PathBuf,
    file: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::parse();

    let src = fs::read_to_string(&opts.file)
        .with_context(|| format!("failed to read {}", opts.file.display()))?;

    let segments = marquint::parser::split(&src);
    let markdown = marquint::parser::to_markdown(&segments, "quint");

    let out = fs::File::create(&opts.output)
        .with_context(|| format!("failed to open {}", opts.output.display()))?;
    let mut out = io::BufWriter::new(out);
    out.write_all(markdown.as_bytes())?;
    out.flush()?;
    Ok(())
}
