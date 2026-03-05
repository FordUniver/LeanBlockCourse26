#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Generate TACTICS.md from tactic-data.json and course .lean files."""

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

HOMEPAGE = Path(__file__).resolve().parent.parent
ROOT = HOMEPAGE.parent
DATA_FILE = HOMEPAGE / "scripts" / "tactic-data.json"

# Regex for docstring blocks: /- ... -/
DOCSTRING_RE = re.compile(r"/-(.*?)-/", re.DOTALL)


# ---------------------------------------------------------------------------
# Introduction detection
# ---------------------------------------------------------------------------

@dataclass
class Introduction:
    part: str       # e.g., "P02"
    section: str    # e.g., "S01" or ""
    rel_path: str   # relative path to the .lean file
    line: int       # line number of first mention

    @property
    def sort_key(self) -> str:
        return f"{self.part} {self.section}:{self.line:06d}"

    @property
    def label(self) -> str:
        if self.section:
            return f"{self.part} {self.section}"
        return self.part


def _parse_location(path: Path, code_dir: Path) -> tuple[str, str]:
    """Extract (part, section) from a path like .../P02_Logic/S01_Fundamentals.lean."""
    parts = path.relative_to(code_dir).parts
    part = ""
    section = ""
    if len(parts) >= 1:
        m = re.match(r"(P\d+)", parts[0])
        if m:
            part = m.group(1)
    if len(parts) >= 2:
        m = re.match(r"(S\d+)", parts[1])
        if m:
            section = m.group(1)
    return part, section


def _resolve_detection_names(name: str) -> list[str]:
    """Get the names to search for in docstrings."""
    if " / " in name:
        return [n.strip() for n in name.split(" / ")]
    return [name]


def detect_introductions(
    code_dir: Path, tactic_names: list[str],
) -> dict[str, Introduction]:
    """Find where each tactic is first mentioned in a docstring block.

    Scans .lean files in course order. For each tactic, records the first
    docstring block that mentions it in backticks.
    """
    # Build search targets: map detection_name -> original_name
    targets: dict[str, str] = {}
    for name in tactic_names:
        for det_name in _resolve_detection_names(name):
            if det_name not in targets:
                targets[det_name] = name

    result: dict[str, Introduction] = {}
    found_original: set[str] = set()

    lean_files = sorted(code_dir.rglob("*.lean"))
    for f in lean_files:
        part, section = _parse_location(f, code_dir)
        if not part:
            continue

        text = f.read_text()
        rel_path = str(f.relative_to(ROOT))

        for block_match in DOCSTRING_RE.finditer(text):
            block = block_match.group(0)
            block_start = block_match.start()

            for det_name, orig_name in targets.items():
                if orig_name in found_original:
                    continue
                # Search for backtick-quoted mention
                pattern = re.compile(rf"`{re.escape(det_name)}`")
                m = pattern.search(block)
                if m:
                    line = text[:block_start + m.start()].count("\n") + 1
                    intro = Introduction(
                        part=part, section=section,
                        rel_path=rel_path, line=line,
                    )
                    # For compound names, record under the original name
                    if orig_name not in result or intro.sort_key < result[orig_name].sort_key:
                        result[orig_name] = intro
                        found_original.add(orig_name)

    # Inheritance: exact? inherits from exact, apply? from apply
    for derived, base in [("exact?", "exact"), ("apply?", "apply")]:
        if derived not in result and base in result:
            result[derived] = result[base]

    return result


def find_code_dir() -> Path | None:
    """Find the directory containing P0*_ course parts."""
    for candidate in sorted(ROOT.iterdir()):
        if candidate.is_dir() and not candidate.name.startswith("."):
            if any(candidate.glob("P0*_*")):
                return candidate
    return None


# ---------------------------------------------------------------------------
# Mathlib count formatting
# ---------------------------------------------------------------------------

def format_count(n: int) -> str:
    """Format a rounded count compactly: 70000 -> '~70k', 3200 -> '~3.2k', 800 -> '~800'."""
    if n >= 1000:
        k = n / 1000
        if k == int(k):
            return f"~{int(k)}k"
        s = f"{k:.1f}".rstrip("0").rstrip(".")
        return f"~{s}k"
    if n > 0:
        return f"~{n}"
    return "—"


# ---------------------------------------------------------------------------
# Markdown generation
# ---------------------------------------------------------------------------

def generate(
    data: dict,
    introductions: dict[str, Introduction],
    github_blob: str = "",
) -> str:
    lines = [
        "---",
        "title: Tactics",
        "parent: Cheat Sheets",
        "nav_order: 3",
        "---",
        "",
        "# Tactic Reference",
        "",
        "Tactics are commands used inside `by` blocks to construct proofs step by step.",
        "Grouped by purpose; see the [Lean Tactic Reference]"
        "(https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)"
        " for full documentation.",
        "",
    ]

    # Cheatsheet
    cheatsheet = data.get("cheatsheet", [])
    if cheatsheet:
        lines.append("## Quick Reference")
        lines.append("")
        lines.append("What tactic should I use when I see a particular pattern?")
        lines.append("")
        lines.append("| You see … | In the **goal** | In a **hypothesis** |")
        lines.append("|-----------|----------------|---------------------|")
        for row in cheatsheet:
            lines.append(
                f"| `{row['pattern']}` | {row['in_goal']} | {row['in_hyp']} |"
            )
        lines.append("")

    has_counts = any(
        t.get("mathlib_count_rounded", 0) > 0
        for g in data["groups"]
        for t in g["tactics"]
    )

    for group in data["groups"]:
        lines.append(f"## {group['title']}")
        lines.append("")
        lines.append(group["description"])
        lines.append("")

        # Table header
        if has_counts:
            lines.append("| Tactic | Effect | Introduced | Mathlib |")
            lines.append("|--------|--------|------------|---------|")
        else:
            lines.append("| Tactic | Effect | Introduced |")
            lines.append("|--------|--------|------------|")

        for tactic in group["tactics"]:
            tac_name = tactic["name"]
            tac_cell = f"`{tac_name}`"

            # Introduction cell
            intro_cell = ""
            intro = introductions.get(tac_name)
            if intro:
                label = intro.label
                if github_blob:
                    url = f"{github_blob}/{intro.rel_path}"
                    intro_cell = f"[{label}]({url})"
                else:
                    intro_cell = f"[{label}]({intro.rel_path})"

            # Mathlib count cell
            count_cell = ""
            if has_counts:
                n = tactic.get("mathlib_count_rounded", 0)
                count_cell = format_count(n) if n else "—"

            # Build row
            if has_counts:
                lines.append(f"| {tac_cell} | {tactic['effect']} | {intro_cell} | {count_cell} |")
            else:
                lines.append(f"| {tac_cell} | {tactic['effect']} | {intro_cell} |")

        # TODO: examples in collapsible sections — disabled until Jekyll
        # rendering of <details> + fenced code blocks is fixed.
        # examples = [
        #     (t["name"], t["example"])
        #     for t in group["tactics"]
        #     if t.get("example") and not t["example"].startswith("--")
        # ]
        # if examples:
        #     lines.append("")
        #     lines.append("<details>")
        #     lines.append("<summary>Examples</summary>")
        #     lines.append("")
        #     for name, ex in examples:
        #         lines.append(f"**`{name}`**")
        #         lines.append("```lean")
        #         lines.append(ex)
        #         lines.append("```")
        #         lines.append("")
        #     lines.append("</details>")

        lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", "-o", type=Path, default=None,
                        help="Output path (default: ROOT/TACTICS.md)")
    parser.add_argument("--data", type=Path, default=None,
                        help="Path to tactic-data.json (default: scripts/tactic-data.json)")
    parser.add_argument("--github-blob", default="",
                        help="GitHub blob URL prefix for links")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print to stdout instead of writing")
    args = parser.parse_args()

    output = args.output or HOMEPAGE / "TACTICS.md"
    data_file = args.data or DATA_FILE

    # Load tactic data
    if not data_file.exists():
        print(f"error: {data_file} not found", file=sys.stderr)
        sys.exit(1)
    data = json.loads(data_file.read_text())

    # Collect all tactic names for detection
    tactic_names = [t["name"] for g in data["groups"] for t in g["tactics"]]

    # Detect introductions from course files
    introductions: dict[str, Introduction] = {}
    code_dir = find_code_dir()
    if code_dir:
        introductions = detect_introductions(code_dir, tactic_names)
    else:
        print("warning: no course code directory found", file=sys.stderr)

    # Generate
    content = generate(data, introductions, github_blob=args.github_blob)

    if args.dry_run:
        print(content)
    else:
        output.write_text(content)
        print(f"Generated {output.relative_to(ROOT)}", file=sys.stderr)


if __name__ == "__main__":
    main()
