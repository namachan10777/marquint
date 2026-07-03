//! Quint ソースを行単位で「コメント」と「コード」に分離し、literate な
//! Markdown へ織り込む（weave）ための最小パーサ。
//!
//! # 制限
//! - ブロックコメント `/* ... */` は非対応（行コメント `//` / `///` のみ）。
//! - 行末コメント（`x // note`）はコード側に残す。行頭が（空白を除いて）`//`
//!   で始まる行だけを本文として抜き出す。
//! - 文字列リテラル内の `//` は考慮しない。

/// [`split`] が返す、連続した同種の行のまとまり。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment {
    /// 連続するコメント行。先頭の `//` / `///` と続く空白 1 個を剥がした
    /// プローズ行の並び。`//` だけの行は空文字列になり、Markdown 上の
    /// 段落区切りとして機能する。
    Comment(Vec<String>),
    /// 連続するコード行。元のインデントを含めて原文どおり保持する。
    Code(Vec<String>),
}

/// 行頭（空白を除く）が `//` で始まるコメント行かどうか。
fn is_comment(line: &str) -> bool {
    line.trim_start().starts_with("//")
}

/// コメント行から `//` / `///` マーカーと続く空白 1 個を取り除いた本文を返す。
fn strip_comment(line: &str) -> String {
    let t = line.trim_start();
    let rest = t
        .strip_prefix("///")
        .or_else(|| t.strip_prefix("//"))
        .unwrap_or(t);
    rest.strip_prefix(' ').unwrap_or(rest).to_string()
}

/// コードセグメントの先頭・末尾の空行を落とす。内部の空行は保持する。
fn trim_blank_edges(mut lines: Vec<String>) -> Vec<String> {
    while lines.first().is_some_and(|l| l.trim().is_empty()) {
        lines.remove(0);
    }
    while lines.last().is_some_and(|l| l.trim().is_empty()) {
        lines.pop();
    }
    lines
}

/// コメントセグメントの末尾の空プローズ行を落とす。
fn trim_trailing_blank(mut lines: Vec<String>) -> Vec<String> {
    while lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines
}

/// ソースをコメント/コードのセグメント列へ分割する。
pub fn split(src: &str) -> Vec<Segment> {
    let mut segments = Vec::new();
    let mut comment: Vec<String> = Vec::new();
    let mut code: Vec<String> = Vec::new();

    for line in src.lines() {
        if is_comment(line) {
            // コメント行: 開いているコードセグメントを閉じる。
            if !code.is_empty() {
                segments.push(Segment::Code(trim_blank_edges(std::mem::take(&mut code))));
            }
            comment.push(strip_comment(line));
        } else if line.trim().is_empty() {
            // 空行: いま開いているセグメントに付随させる（先頭の空行は捨てる）。
            if !comment.is_empty() {
                comment.push(String::new());
            } else if !code.is_empty() {
                code.push(line.to_string());
            }
        } else {
            // コード行: 開いているコメントセグメントを閉じる。
            if !comment.is_empty() {
                segments.push(Segment::Comment(trim_trailing_blank(std::mem::take(
                    &mut comment,
                ))));
            }
            code.push(line.to_string());
        }
    }

    if !comment.is_empty() {
        segments.push(Segment::Comment(trim_trailing_blank(comment)));
    }
    if !code.is_empty() {
        segments.push(Segment::Code(trim_blank_edges(code)));
    }
    segments
}

/// セグメント列を literate な Markdown へ織り込む。
/// コメントはそのまま本文に、コードは ```` ```{lang} ```` フェンスドコード
/// ブロックとして出力する。
pub fn to_markdown(segments: &[Segment], lang: &str) -> String {
    let mut out = String::new();
    for segment in segments {
        match segment {
            Segment::Comment(lines) => {
                for line in lines {
                    out.push_str(line);
                    out.push('\n');
                }
            }
            Segment::Code(lines) => {
                out.push_str("```");
                out.push_str(lang);
                out.push('\n');
                for line in lines {
                    out.push_str(line);
                    out.push('\n');
                }
                out.push_str("```\n");
            }
        }
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splits_comment_and_code() {
        let src = "\
// # Title
//
// prose
module m {
  // ## section
  type T = int
}
";
        let segs = split(src);
        assert_eq!(
            segs,
            vec![
                Segment::Comment(vec![
                    "# Title".to_string(),
                    String::new(),
                    "prose".to_string(),
                ]),
                Segment::Code(vec!["module m {".to_string()]),
                Segment::Comment(vec!["## section".to_string()]),
                Segment::Code(vec!["  type T = int".to_string(), "}".to_string()]),
            ]
        );
    }

    #[test]
    fn strips_doc_and_line_markers() {
        assert_eq!(strip_comment("/// doc"), "doc");
        assert_eq!(strip_comment("// note"), "note");
        assert_eq!(strip_comment("//no-space"), "no-space");
        assert_eq!(strip_comment("  // indented"), "indented");
        assert_eq!(strip_comment("//"), "");
    }

    #[test]
    fn trailing_comment_stays_in_code() {
        let segs = split("let x = 1 // note\n");
        assert_eq!(
            segs,
            vec![Segment::Code(vec!["let x = 1 // note".to_string()])]
        );
    }

    #[test]
    fn weaves_to_markdown() {
        let segs = vec![
            Segment::Comment(vec!["# Title".to_string()]),
            Segment::Code(vec!["type T = int".to_string()]),
        ];
        assert_eq!(
            to_markdown(&segs, "quint"),
            "# Title\n\n```quint\ntype T = int\n```\n\n"
        );
    }
}
