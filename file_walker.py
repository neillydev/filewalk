#!/usr/bin/env python3
import argparse
import json
import os
import re
import sys
from collections import defaultdict, deque
from typing import Dict, List, Optional, Set, Tuple

FILE_EXT_DEFAULT = (".ts", ".tsx", ".js", ".jsx")


def absnorm(p: str) -> str:
    return os.path.normpath(os.path.abspath(p))


def read_text(path: str) -> Optional[str]:
    for enc in ("utf-8", "utf-8-sig", "latin-1"):
        try:
            with open(path, "r", encoding=enc, errors="ignore") as f:
                return f.read()
        except Exception:
            continue
    return None


def walk_files(root: str, exts: Tuple[str, ...]) -> List[str]:
    root = absnorm(root)
    out = []
    for dp, _, fns in os.walk(root):
        for fn in fns:
            if not exts or fn.lower().endswith(exts):
                out.append(absnorm(os.path.join(dp, fn)))
    return out


STRING_OPENERS = ("'", '"', "`")


def find_string_spans(code: str) -> List[Tuple[int, int, str]]:
    spans: List[Tuple[int, int, str]] = []
    i, n = 0, len(code)
    while i < n:
        ch = code[i]
        if ch in STRING_OPENERS:
            q = ch
            start = i
            i += 1
            while i < n:
                c = code[i]
                if c == "\\":
                    i += 2
                    continue
                if q == "`" and c == "$" and i + 1 < n and code[i + 1] == "{":
                    i += 2
                    depth = 1
                    while i < n and depth > 0:
                        if code[i] == "\\":
                            i += 2
                            continue
                        if code[i] == "{":
                            depth += 1
                        elif code[i] == "}":
                            depth -= 1
                        i += 1
                    continue
                if c == q:
                    spans.append((start, i + 1, q))
                    i += 1
                    break
                i += 1
            continue
        if ch == "/" and i + 1 < n:
            nxt = code[i + 1]
            if nxt == "/":
                i += 2
                while i < n and code[i] not in ("\n", "\r"):
                    i += 1
                continue
            if nxt == "*":
                i += 2
                while i + 1 < n and not (code[i] == "*" and code[i + 1] == "/"):
                    i += 1
                i += 2
                continue
        i += 1
    return spans


# function foo(...) { ... }
RE_FUNC_DECL = re.compile(
    r"(?:export\s+)?(?:async\s+)?function\s+(?P<name>[A-Za-z0-9_$]+)\s*\(", re.MULTILINE
)

# const|let|var foo = (...) : ReturnType => ...
RE_FUNC_ARROW = re.compile(
    r"(?:export\s+)?(?:const|let|var)\s+"
    r"(?P<name>[A-Za-z0-9_$]+)\s*=\s*"
    r"(?:async\s*)?"
    r"\([^()]*\)\s*"  # params (...)
    r"(?::\s*[^=(){;]+)?\s*"  # optional TS return type like : Promise<Row>
    r"=>",
    re.MULTILINE,
)

# class ClassName { ... }
RE_CLASS = re.compile(r"class\s+(?P<cls>[A-Za-z0-9_$]+)\s*", re.MULTILINE)

# methodName(...) {
RE_METHOD_SIG = re.compile(
    r"^\s*(?P<name>[A-Za-z0-9_$]+)\s*\([^()]*\)\s*\{", re.MULTILINE
)

# imports / exports (names only)
RE_IMPORT_NAMED = re.compile(
    r"import\s*{\s*([^}]+)\s*}\s*from\s*['\"][^'\"]+['\"]", re.MULTILINE
)
RE_EXPORT_NAMED = re.compile(r"export\s*{\s*([^}]+)\s*}\s*;?", re.MULTILINE)
RE_EXPORT_FUNC_DECL = re.compile(
    r"export\s+(?:async\s+)?function\s+([A-Za-z0-9_$]+)\s*\(", re.MULTILINE
)

# Router variable with prefix
RE_KOA_ROUTER_PREFIX = re.compile(
    r"\b(?:const|let|var)\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*=\s*new\s+Router\s*\(\s*{[^}]*\bprefix\s*:\s*(['\"])(?P<prefix>[^'\"]+)\1",
    re.DOTALL,
)

# Standalone routes: obj.get('/p', handlers...)
RE_KOA_ROUTE_CALL = re.compile(
    r"\b(?P<obj>[A-Za-z_][A-Za-z0-9_]*)\.(?P<method>get|post|put|patch|delete|all)\s*\(\s*(?P<path>['\"][^'\"]+['\"])\s*,\s*(?P<rest>[^)]*)\)",
    re.IGNORECASE | re.DOTALL,
)

# Chain start: obj . method ( '/p', handlers... )
RE_KOA_CHAIN_START = re.compile(
    r"\b(?P<obj>[A-Za-z_][A-Za-z0-9_]*)\s*\.\s*(?P<method>get|post|put|patch|delete|all)\s*\(\s*(?P<path>['\"][^'\"]+['\"])\s*,\s*(?P<rest>[^)]*)\)",
    re.IGNORECASE | re.DOTALL,
)

# Chain follow: .method('/p', handlers...)
RE_KOA_CHAIN_FOLLOW = re.compile(
    r"\s*\.\s*(?P<method>get|post|put|patch|delete|all)\s*\(\s*(?P<path>['\"][^'\"]+['\"])\s*,\s*(?P<rest>[^)]*)\)",
    re.IGNORECASE | re.DOTALL,
)


def call_pattern(name: str) -> re.Pattern:
    return re.compile(rf"\b{re.escape(name)}\s*\(", re.MULTILINE)


class FunctionDef:
    def __init__(
        self, name: str, file: str, start: int, end: int, cls: Optional[str] = None
    ):
        self.name = name
        self.file = file
        self.start = start
        self.end = end
        self.cls = cls

    def fqname(self) -> str:
        return f"{self.cls}.{self.name}" if self.cls else self.name


class Endpoint:
    def __init__(self, method: str, path: str, file: str, handler_names: List[str]):
        self.kind = "koa"
        self.method = method
        self.path = path
        self.file = file
        self.handlers = handler_names


class CodeIndex:
    def __init__(self):
        self.functions_by_file: Dict[str, List[FunctionDef]] = defaultdict(list)
        self.functions_by_name: Dict[str, List[FunctionDef]] = defaultdict(list)
        self.calls_by_file: Dict[str, Dict[str, List[int]]] = defaultdict(
            lambda: defaultdict(list)
        )
        self.exports_by_file: Dict[str, Set[str]] = defaultdict(set)
        self.imports_by_file: Dict[str, Set[str]] = defaultdict(set)
        self.koa_endpoints: List[Endpoint] = []
        self.router_prefixes_by_file: Dict[str, Dict[str, str]] = defaultdict(dict)

    def index_file(self, path: str, code: str):
        path = absnorm(path)

        for mp in RE_KOA_ROUTER_PREFIX.finditer(code):
            name = mp.group("name")
            pref = mp.group("prefix")
            if name and pref is not None:
                self.router_prefixes_by_file[path][name] = (
                    pref if pref.startswith("/") else "/" + pref
                )

        for m in RE_IMPORT_NAMED.finditer(code):
            for n in [t.strip() for t in m.group(1).split(",") if t.strip()]:
                self.imports_by_file[path].add(n)
        for m in RE_EXPORT_NAMED.finditer(code):
            for n in [t.strip() for t in m.group(1).split(",") if t.strip()]:
                self.exports_by_file[path].add(n)
        for m in RE_EXPORT_FUNC_DECL.finditer(code):
            self.exports_by_file[path].add(m.group(1))

        for m in RE_FUNC_DECL.finditer(code):
            name = m.group("name")
            start = m.start()
            end = self._approx_block_end(code, m.end())
            fd = FunctionDef(name, path, start, end)
            self.functions_by_file[path].append(fd)
            self.functions_by_name[name].append(fd)

        for m in RE_FUNC_ARROW.finditer(code):
            name = m.group("name")
            start = m.start()
            end = self._approx_block_end(code, m.end())
            fd = FunctionDef(name, path, start, end)
            self.functions_by_file[path].append(fd)
            self.functions_by_name[name].append(fd)

        for mc in RE_CLASS.finditer(code):
            cls = mc.group("cls")
            start_c = mc.end()
            end_c = self._approx_block_end(code, start_c)
            block = code[start_c:end_c]
            base = start_c
            for mm in RE_METHOD_SIG.finditer(block):
                name = mm.group("name")
                s = base + mm.start()
                e = base + self._approx_block_end(code, base + mm.end())
                fd = FunctionDef(name, path, s, e, cls=cls)
                self.functions_by_file[path].append(fd)
                self.functions_by_name[name].append(fd)

        prefixes = self.router_prefixes_by_file.get(path, {})
        for mk in RE_KOA_ROUTE_CALL.finditer(code):
            method = mk.group("method").upper()
            raw_path = mk.group("path").strip("'\"")
            rest = mk.group("rest") or ""
            obj = mk.group("obj")
            pathlit = raw_path
            if obj in prefixes:
                pathlit = (
                    prefixes[obj].rstrip("/") + "/" + raw_path.lstrip("/")
                ).replace("//", "/")
            handlers = extract_handler_names(rest)
            self.koa_endpoints.append(Endpoint(method, pathlit, path, handlers))

        pos = 0
        while True:
            start_m = RE_KOA_CHAIN_START.search(code, pos)
            if not start_m:
                break
            obj = start_m.group("obj")
            method = start_m.group("method").upper()
            raw_path = start_m.group("path").strip("'\"")
            rest = start_m.group("rest") or ""
            pref = prefixes.get(obj)
            pathlit = (
                (pref.rstrip("/") + "/" + raw_path.lstrip("/")).replace("//", "/")
                if pref
                else raw_path
            )
            handlers = extract_handler_names(rest)
            self.koa_endpoints.append(Endpoint(method, pathlit, path, handlers))

            pos2 = start_m.end()
            while True:
                foll = RE_KOA_CHAIN_FOLLOW.match(code, pos2)
                if not foll:
                    break
                method2 = foll.group("method").upper()
                raw_path2 = foll.group("path").strip("'\"")
                rest2 = foll.group("rest") or ""
                pathlit2 = (
                    (pref.rstrip("/") + "/" + raw_path2.lstrip("/")).replace("//", "/")
                    if pref
                    else raw_path2
                )
                handlers2 = extract_handler_names(rest2)
                self.koa_endpoints.append(Endpoint(method2, pathlit2, path, handlers2))
                pos2 = foll.end()
            pos = pos2

    def finalize_calls(self):
        names = list(self.functions_by_name.keys())
        texts: Dict[str, str] = {}
        for f in self.functions_by_file.keys():
            t = read_text(f)
            if t is not None:
                texts[f] = t
        for f, funcs in self.functions_by_file.items():
            code = texts.get(f, "")
            for name in names:
                for m in call_pattern(name).finditer(code):
                    self.calls_by_file[f][name].append(m.start())

    def _approx_block_end(self, code: str, start: int) -> int:
        n = len(code)
        i = start

        def skip_string(i: int) -> int:
            q = code[i]
            i += 1
            while i < n:
                c = code[i]
                if c == "\\":
                    i += 2
                    continue
                if q == "`" and c == "$" and i + 1 < n and code[i + 1] == "{":
                    i += 2
                    d = 1
                    while i < n and d > 0:
                        if code[i] == "\\":
                            i += 2
                            continue
                        if code[i] == "{":
                            d += 1
                        elif code[i] == "}":
                            d -= 1
                        i += 1
                    continue
                if c == q:
                    return i + 1
                i += 1
            return i

        while i < n and code[i] != "{":
            if code[i] in STRING_OPENERS:
                i = skip_string(i)
                continue
            if i + 1 < n and code[i] == "/":
                if code[i + 1] == "/":
                    i += 2
                    while i < n and code[i] not in ("\n", "\r"):
                        i += 1
                    continue
                if code[i + 1] == "*":
                    i += 2
                    while i + 1 < n and not (code[i] == "*" and code[i + 1] == "/"):
                        i += 1
                    i += 2
                    continue
            i += 1
        if i >= n or code[i] != "{":
            return min(n, start + 4000)

        depth = 0
        while i < n:
            c = code[i]
            if c in STRING_OPENERS:
                i = skip_string(i)
                continue
            if i + 1 < n and c == "/":
                if code[i + 1] == "/":
                    i += 2
                    while i < n and code[i] not in ("\n", "\r"):
                        i += 1
                    continue
                if code[i + 1] == "*":
                    i += 2
                    while i + 1 < n and not (code[i] == "*" and code[i + 1] == "/"):
                        i += 1
                    i += 2
                    continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return i + 1
            i += 1
        return n


# ------------------------------ detection utils -------------------------------


def extract_handler_names(arglist: str) -> List[str]:
    cleaned = re.sub(
        r"$begin:math:display$[^$end:math:display$]*\]",
        lambda m: ",".join(re.findall(r"[A-Za-z_][$A-Za-z0-9_]*", m.group(0))),
        arglist,
    )
    cleaned = re.sub(
        r"(?:async\s*)?\([^()]*\)\s*=>\s*\{.*?\}", "", cleaned, flags=re.DOTALL
    )
    cleaned = re.sub(
        r"function(?:\s+[A-Za-z0-9_$]+)?\s*$begin:math:text$[^()]*$end:math:text$\s*\{.*?\}",
        "",
        cleaned,
        flags=re.DOTALL,
    )
    cands: List[str] = []
    for part in cleaned.split(","):
        cands.extend(re.findall(r"[A-Za-z_][$A-Za-z0-9_]*", part))
    seen: Set[str] = set()
    out: List[str] = []
    for t in cands:
        if t not in seen:
            seen.add(t)
            out.append(t)
    return out


def proc_regexes(proc_names: List[str]) -> List[Tuple[str, re.Pattern]]:
    regs: List[Tuple[str, re.Pattern]] = []
    for p in proc_names:
        base = p.strip("`")
        regs.append(
            (
                p,
                re.compile(
                    rf"\bCALL\s+(?:`?[A-Za-z0-9_]+`?\.)?`?{re.escape(base)}`?\b",
                    re.IGNORECASE,
                ),
            )
        )
    return regs


def scan_proc_usages(root: str, exts: Tuple[str, ...], procs: List[str]) -> List[Dict]:
    hits: List[Dict] = []
    seen: Set[Tuple[str, int, str]] = set()
    regexes = proc_regexes(procs)
    for path in walk_files(root, exts):
        code = read_text(path)
        if not code:
            continue
        for s, e, q in find_string_spans(code):
            frag = code[s:e]
            for pname, rx in regexes:
                for m in rx.finditer(frag):
                    abs_pos = s + m.start()
                    key = (path, abs_pos, pname)
                    if key in seen:
                        continue
                    seen.add(key)
                    line = code.count("\n", 0, abs_pos) + 1
                    ls = code.rfind("\n", 0, abs_pos)
                    le = code.find("\n", abs_pos)
                    if ls == -1:
                        ls = 0
                    else:
                        ls += 1
                    if le == -1:
                        le = len(code)
                    snippet = code[ls:le].strip()
                    hits.append(
                        {
                            "file": path,  # already absolute from walk_files()
                            "line": line,
                            "pos": abs_pos,
                            "proc": pname,
                            "snippet": snippet,
                        }
                    )
    return hits


def find_enclosing_function(
    idx: CodeIndex, file: str, pos: int
) -> Optional[FunctionDef]:
    file = absnorm(file)
    funcs = idx.functions_by_file.get(file, [])
    best: Optional[FunctionDef] = None
    for f in funcs:
        if f.start <= pos <= f.end:
            if best is None or f.start >= best.start:
                best = f
    return best


def build_caller_map(idx: CodeIndex) -> Dict[str, Set[str]]:
    result: Dict[str, Set[str]] = defaultdict(set)
    for file, funcs in idx.functions_by_file.items():
        code = read_text(file) or ""
        for f in funcs:
            body = code[f.start : f.end]
            for name, defs in idx.functions_by_name.items():
                if call_pattern(name).search(body):
                    for d in defs:
                        result[name].add(f.fqname())
    return result


def uniq_endpoints(eps: List[Endpoint]) -> List[Endpoint]:
    seen = set()
    out: List[Endpoint] = []
    for ep in eps:
        key = (ep.kind, ep.method, ep.path, ep.file)
        if key not in seen:
            seen.add(key)
            out.append(ep)
    return out


def match_handlers_to_functions(idx: CodeIndex) -> Dict[str, List[Endpoint]]:
    mapping: Dict[str, List[Endpoint]] = defaultdict(list)
    for ep in idx.koa_endpoints:
        for h in ep.handlers:
            mapping[h].append(ep)
    # dedupe per handler
    for k in list(mapping.keys()):
        mapping[k] = uniq_endpoints(mapping[k])
    return mapping


def endpoint_string(ep: Endpoint) -> str:
    return f"{ep.method} {ep.path}  ({ep.file})"


def backtrace_to_endpoints(
    idx: CodeIndex,
    start_func: FunctionDef,
    caller_map: Dict[str, Set[str]],
    handler_map: Dict[str, List[Endpoint]],
    max_depth: int = 5,
) -> List[Tuple[List[str], List[Endpoint]]]:
    results: List[Tuple[List[str], List[Endpoint]]] = []
    fq_to_def: Dict[str, FunctionDef] = {}
    for _, defs in idx.functions_by_file.items():
        for d in defs:
            fq_to_def[d.fqname()] = d

    start_fq = start_func.fqname()
    queue = deque()
    queue.append(([start_fq], start_func))
    seen: Set[str] = {start_fq}

    while queue:
        chain, fdef = queue.popleft()

        eps = handler_map.get(fdef.name, [])
        eps = uniq_endpoints(eps)
        if eps:
            results.append((chain, eps))

        if len(chain) >= max_depth:
            continue

        for caller_fq in caller_map.get(fdef.name, set()):
            if caller_fq in seen:
                continue
            cdef = fq_to_def.get(caller_fq)
            if not cdef:
                cand = idx.functions_by_name.get(caller_fq.split(".")[-1], [])
                cdef = cand[0] if cand else None
            if cdef:
                seen.add(caller_fq)
                queue.append((chain + [caller_fq], cdef))

    return results


# ----------------------------------- CLI --------------------------------------


def parse_args(argv=None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Trace stored procedure usage to API entrypoints in TS/JS code."
    )
    ap.add_argument(
        "-r", "--root", default=".", help="Root directory to scan (default: .)"
    )
    ap.add_argument(
        "--ext",
        nargs="*",
        default=list(FILE_EXT_DEFAULT),
        help="File extensions to include",
    )
    ap.add_argument(
        "--procs",
        nargs="*",
        default=[],
        help="Stored procedure names to look for (bare or backticked)",
    )
    ap.add_argument("--procs-file", help="File with one procedure name per line")
    ap.add_argument(
        "--json", action="store_true", help="Emit JSON instead of human-readable output"
    )
    ap.add_argument(
        "--max-depth", type=int, default=5, help="Max backtrace depth (default 5)"
    )
    ap.add_argument("--debug", action="store_true", help="Print debug counters")
    return ap.parse_args(argv)


def main(argv=None) -> int:
    ns = parse_args(argv)

    procs = list(ns.procs)
    if ns.procs_file:
        try:
            with open(ns.procs_file, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        procs.append(line)
        except Exception as e:
            print(f"[ERR] failed to read {ns.procs_file}: {e}", file=sys.stderr)
            return 2
    if not procs:
        print("[i] No procs specified. Scanning for all CALL <proc> usages...")
        # fallback: a regex that matches any CALL <name>
        dynamic_procs = set()
        call_any = re.compile(
            r"\bCALL\s+(?:`?[A-Za-z0-9_]+`?\.)?`?([A-Za-z0-9_]+)`?", re.IGNORECASE
        )
        for path in walk_files(ns.root, tuple(ns.ext)):
            code = read_text(path)
            if not code:
                continue
            for s, e, q in find_string_spans(code):
                frag = code[s:e]
                for m in call_any.finditer(frag):
                    dynamic_procs.add(m.group(1))
        procs = list(dynamic_procs)
        if not procs:
            print(
                "[ERR] No stored procedure calls found in the codebase.",
                file=sys.stderr,
            )
            return 1

    exts = tuple(ns.ext)

    idx = CodeIndex()
    for path in walk_files(ns.root, exts):
        code = read_text(path)
        if code is None:
            continue
        idx.index_file(path, code)
    idx.finalize_calls()
    if ns.debug:
        total_funcs = sum(len(v) for v in idx.functions_by_file.values())
        print(
            f"[debug] files scanned: {len(list(walk_files(ns.root, exts)))}",
            file=sys.stderr,
        )
        print(f"[debug] functions indexed: {total_funcs}", file=sys.stderr)
        print(f"[debug] endpoints indexed: {len(idx.koa_endpoints)}", file=sys.stderr)
        print(f"[debug] procs considered: {len(procs)}", file=sys.stderr)
    usages = scan_proc_usages(ns.root, exts, procs)
    if ns.debug:
        print(f"[debug] proc usages found: {len(usages)}", file=sys.stderr)
        for u in usages[:5]:
            print(
                f"[debug] hit: {u['file']}:{u['line']} -> {u['snippet']}",
                file=sys.stderr,
            )

    caller_map = build_caller_map(idx)
    handler_map = match_handlers_to_functions(idx)

    report: List[Dict] = []
    gv_edges: List[Tuple[str, str]] = []
    gv_func_endpoints: Dict[str, List[str]] = defaultdict(list)

    for u in usages:
        file = u["file"]
        pos = u["pos"]
        fdef = find_enclosing_function(idx, file, pos)
        chains = []
        if fdef:
            traces = backtrace_to_endpoints(
                idx, fdef, caller_map, handler_map, max_depth=ns.max_depth
            )
            for chain, eps in traces:
                eps = uniq_endpoints(eps)
                for i in range(len(chain) - 1):
                    gv_edges.append((chain[i + 1], chain[i]))
                for ep in eps:
                    gv_func_endpoints[chain[-1]].append(endpoint_string(ep))
                chains.append(
                    {
                        "call_chain": chain,
                        "endpoints": [endpoint_string(ep) for ep in eps],
                    }
                )

        report.append(
            {
                "procedure": u["proc"],
                "file": file,
                "line": u["line"],
                "snippet": u["snippet"],
                "enclosing_function": fdef.fqname() if fdef else None,
                "function_file": fdef.file if fdef else None,
                "traces": chains,
            }
        )

    if ns.json:
        print(
            json.dumps(
                {"root": absnorm(ns.root), "procedures": procs, "results": report},
                indent=2,
            )
        )
    else:
        if not report:
            print("No stored procedure usages found.")
            return 1
        print("=" * 100)
        print(f"Root: {absnorm(ns.root)}")
        print(f"Procedures: {', '.join(procs)}")
        print("=" * 100)
        for r in report:
            print(f"\nPROC: {r['procedure']}")
            print(f"File: {r['file']}:{r['line']}")
            print(f"Line: {r['snippet']}")
            print(f"Enclosing function: {r['enclosing_function'] or '(not found)'}")
            if r["traces"]:
                for t in r["traces"]:
                    chain = "  ←  ".join(t["call_chain"])
                    print("  Call chain:")
                    print(f"    {chain}")
                    if t["endpoints"]:
                        print("  Endpoints:")
                        for ep in t["endpoints"]:
                            print(f"    - {ep}")
                    else:
                        print("  Endpoints: (none resolved)")
            else:
                print("  (no callers / endpoints resolved)")
            print("-" * 100)

    return 0


if __name__ == "__main__":
    sys.exit(main())
