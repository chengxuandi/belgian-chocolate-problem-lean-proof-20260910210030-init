"""Lexical safety scan of every BCP Lean source; kernel audit is separate."""

from pathlib import Path
import re
import sys


def code_only(text: str) -> str:
    """Blank Lean nested comments and strings, preserving line numbers."""
    out = list(text)
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if text[i] == '"':
                    in_string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out[i] = " "
                i += 1
        elif text[i] == '"':
            in_string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    if depth or in_string:
        raise ValueError("Unterminated comment/string in Lean source")
    return "".join(out)


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    files = [root / "BCPThreshold.lean", *sorted((root / "BCPThreshold").rglob("*.lean"))]
    if not files[0].is_file() or len(files) < 2:
        raise SystemExit("BCP source tree missing")
    forbidden = re.compile(r"\b(sorry|admit|sorryAx|axiom)\b|debug\.skipKernelTC")
    failures = []
    for path in files:
        code = code_only(path.read_text(encoding="utf-8-sig"))
        for match in forbidden.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(root)}:{line}: {match.group()}")
    if failures:
        print("\n".join(failures))
        raise SystemExit(1)
    print(f"BCP_SOURCE_FILES_SCANNED = {len(files)}")
    print("ZERO_SORRY_CHECK = PASS")
    print("PROJECT_AXIOM_DECLARATIONS = NONE")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as exc:
        sys.exit(str(exc))
