"""Build all BCP modules in dependency order without parallel cold project imports."""

from pathlib import Path
import re
import subprocess
import sys

from audit_bcp_source import code_only


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    lake = sys.argv[1] if len(sys.argv) == 2 else "lake"
    paths = [root / "BCPThreshold.lean", *sorted((root / "BCPThreshold").rglob("*.lean"))]
    modules = {".".join(p.relative_to(root).with_suffix("").parts): p for p in paths}
    edges = {}
    for name, path in modules.items():
        code = code_only(path.read_text(encoding="utf-8-sig"))
        imports = []
        for line in code.splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                imports.extend(match.group(1).split())
        edges[name] = [n for n in imports if n == "BCPThreshold" or n.startswith("BCPThreshold.")]
        for dep in edges[name]:
            if dep not in modules:
                raise ValueError(f"Missing BCP dependency: {name} imports {dep}")

    active, done, order = set(), set(), []

    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise ValueError(f"BCP import cycle at {name}")
        active.add(name)
        for dep in edges[name]:
            visit(dep)
        active.remove(name)
        done.add(name)
        order.append(name)

    for name in sorted(modules):
        visit(name)
    for i, name in enumerate(order, 1):
        print(f"SERIAL_BUILD [{i}/{len(order)}]: {name}", flush=True)
        subprocess.run([lake, "--log-level=error", "build", name], cwd=root, check=True)
        print(f"MODULE_BUILD = PASS: {name}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(str(exc))
