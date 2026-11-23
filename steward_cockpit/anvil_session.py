"""Per-Cockpit Anvil Session Controller for Anchor AI Cockpits.

Provides each AI Cockpit (`cdir`) with its own persistent Anvil session stored in
`<cdir>/.anvil/session.json`. Many cockpits start with an empty Anvil session (`active: False`),
showing a clean launch screen until either John or the Cockpit's Steward launches Anvil to:
  1. Analyze & improve software (reachable within the Cockpit folder or cloned from a GitHub repo).
  2. Map a scientific/technical paper (pulled from arXiv/internet URL or local file in the Cockpit)
     to its software implementation with native MathML equations and empirical verification.
"""
from __future__ import annotations

import ast
import contextlib
import copy
import gzip
import hashlib
import html
import importlib
import io
import ipaddress
import json
import math
import os
import re
import shlex
import shutil
import socket
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

_ANCHOR_ROOT = Path(__file__).resolve().parent.parent
_FOUNDRY_CANDIDATES: Tuple[Path, ...] = (
    _ANCHOR_ROOT.parent / "Skill Foundry" / "skills" / "anvil" / "scripts",
    _ANCHOR_ROOT / "vendor" / "bundled-skills" / "anvil" / "scripts",
)


_V4_MODULE_NAMES: Tuple[str, ...] = (
    "anvil_v4_process",
    "anvil_v4_trace",
    "anvil_v4_refactor",
    "anvil_v4_xval",
    "anvil_v4_workbench",
)
_V4_MODULES_CACHE: Optional[Dict[str, Any]] = None
_V4_MODULES_MTIME_SIG: Tuple[float, ...] = ()


def _compute_anvil_scripts_mtime_sig(cand: Path) -> Tuple[float, ...]:
    out: List[float] = []
    for mname in ("anvil_engine", *_V4_MODULE_NAMES):
        fp = cand / f"{mname}.py"
        try:
            out.append(fp.stat().st_mtime)
        except OSError:
            out.append(0.0)
    return tuple(out)


_BUNDLED_PYCACHE_CLEANED = False


def _load_anvil_engine(candidates: Optional[Tuple[Path, ...]] = None) -> Any:
    """Load `anvil_engine` from Skill Foundry or bundled Anchor vendor fallback without writing `.pyc` files."""
    global _BUNDLED_PYCACHE_CLEANED
    if not _BUNDLED_PYCACHE_CLEANED:
        bundled_root = _ANCHOR_ROOT / "vendor" / "bundled-skills" / "anvil"
        if bundled_root.is_dir():
            for _pc in list(bundled_root.rglob("__pycache__")):
                shutil.rmtree(_pc, ignore_errors=True)
        _BUNDLED_PYCACHE_CLEANED = True
    search = tuple(candidates) if candidates is not None else _FOUNDRY_CANDIDATES
    for cand in search:
        cand_file = cand / "anvil_engine.py"
        if cand.is_dir() and cand_file.is_file():
            cand_str = str(cand.resolve())
            sys.path[:] = [cand_str] + [p for p in sys.path if p != cand_str]
            prev_bc = sys.dont_write_bytecode
            sys.dont_write_bytecode = True
            try:
                sys.modules.pop("anvil_engine", None)
                return importlib.import_module("anvil_engine")
            except Exception:
                continue
            finally:
                sys.dont_write_bytecode = prev_bc
    return None


def _load_anvil_v4_modules(candidates: Optional[Tuple[Path, ...]] = None) -> Dict[str, Any]:
    """Dynamically load Anvil v4 modules from Skill Foundry or bundled vendor fallback with zero `.pyc` writes."""
    global _V4_MODULES_CACHE, _V4_MODULES_MTIME_SIG, anvil_engine
    search = tuple(candidates) if candidates is not None else _FOUNDRY_CANDIDATES
    active_cand = next(
        (c for c in search if c.is_dir() and all((c / f"{m}.py").is_file() for m in _V4_MODULE_NAMES)),
        None,
    )
    if candidates is None and active_cand is not None:
        cur_sig = _compute_anvil_scripts_mtime_sig(active_cand)
        if _V4_MODULES_CACHE is not None and cur_sig == _V4_MODULES_MTIME_SIG and all(k in _V4_MODULES_CACHE for k in _V4_MODULE_NAMES):
            return _V4_MODULES_CACHE

    for cand in search:
        if not cand.is_dir():
            continue
        if not all((cand / f"{mname}.py").is_file() for mname in _V4_MODULE_NAMES):
            continue
        cand_str = str(cand.resolve())
        sys.path[:] = [cand_str] + [p for p in sys.path if p != cand_str]
        prev_bc = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        try:
            loaded: Dict[str, Any] = {}
            for mname in ("anvil_engine", *_V4_MODULE_NAMES):
                sys.modules.pop(mname, None)
            if (cand / "anvil_engine.py").is_file():
                eng_mod = importlib.import_module("anvil_engine")
                if candidates is None:
                    anvil_engine = eng_mod
            for mname in _V4_MODULE_NAMES:
                loaded[mname] = importlib.import_module(mname)
            if candidates is None:
                _V4_MODULES_CACHE = loaded
                _V4_MODULES_MTIME_SIG = _compute_anvil_scripts_mtime_sig(cand)
            return loaded
        except Exception:
            continue
        finally:
            sys.dont_write_bytecode = prev_bc
    return {}


anvil_engine = _load_anvil_engine()

ALLOWED_LOCAL_ROOTS = (
    _ANCHOR_ROOT.parent.resolve(),
)

FORBIDDEN_DOT_PARTS = {
    ".git", ".claude", ".aws", ".ssh", ".gnupg", ".anchor",
    ".ecgberht", ".steward", ".env", ".netrc", ".npmrc", ".pypirc",
}
FORBIDDEN_SECRET_NAMES = {
    "credentials", "credentials.json", ".credentials.json",
    "id_rsa", "id_ed25519", "secrets.json", "token.json",
}

GITHUB_URL_RE = re.compile(
    r"^(?:https?://)?(?:www\.)?github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+?)(?:\.git)?(?:/.*)?$",
    re.IGNORECASE,
)
ARXIV_ID_RE = re.compile(
    r"(?:arxiv\.org/(?:abs|pdf)/|^arxiv:)(\d{4}\.\d{4,5}(?:v\d+)?)",
    re.IGNORECASE,
)

_COCKPIT_LOCKS_GUARD = threading.Lock()
_COCKPIT_LOCKS: Dict[str, threading.Lock] = {}
_CANDIDATES_CACHE: Dict[str, Tuple[float, Dict[str, List[Dict[str, str]]]]] = {}


def _get_cockpit_lock(cdir: Path) -> threading.Lock:
    key = str(cdir.resolve()).lower()
    with _COCKPIT_LOCKS_GUARD:
        lock = _COCKPIT_LOCKS.get(key)
        if lock is None:
            lock = threading.Lock()
            _COCKPIT_LOCKS[key] = lock
        return lock


MAX_SOURCE_BUNDLE_BYTES = 2 * 1024 * 1024
_FILE_LOCKS_GUARD = threading.Lock()
_FILE_THREAD_LOCKS: Dict[str, threading.RLock] = {}
_FILE_LOCK_TLS = threading.local()
_COCKPIT_V4_BUNDLE_CACHE_LOCK = threading.RLock()
_COCKPIT_V4_BUNDLE_CACHE: Dict[Tuple[str, ...], Dict[str, Any]] = {}


@contextlib.contextmanager
def exclusive_file_lock(target: Path, timeout_sec: float = 10.0):
    """Cross-thread and cross-process reentrant exclusive file lock (`msvcrt` on Windows, `fcntl` on POSIX)."""
    resolved = target.resolve()
    resolved.parent.mkdir(parents=True, exist_ok=True)
    lock_path = resolved.parent / f".{resolved.name}.lock"
    key = str(lock_path).lower()
    with _FILE_LOCKS_GUARD:
        tlock = _FILE_THREAD_LOCKS.get(key)
        if tlock is None:
            tlock = threading.RLock()
            _FILE_THREAD_LOCKS[key] = tlock

    deadline = time.monotonic() + max(0.2, float(timeout_sec))
    with tlock:
        depths = getattr(_FILE_LOCK_TLS, "depths", None)
        if depths is None:
            depths = {}
            _FILE_LOCK_TLS.depths = depths
        cur_depth = int(depths.get(key, 0))
        if cur_depth > 0:
            depths[key] = cur_depth + 1
            try:
                yield
            finally:
                depths[key] = cur_depth
            return

        fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o600)
        locked_os = False
        try:
            if os.name == "nt":
                import msvcrt

                os.lseek(fd, 0, os.SEEK_SET)
                if os.fstat(fd).st_size == 0:
                    os.write(fd, b"L")
                    os.lseek(fd, 0, os.SEEK_SET)
                while True:
                    try:
                        os.lseek(fd, 0, os.SEEK_SET)
                        msvcrt.locking(fd, msvcrt.LK_NBLCK, 1)
                        locked_os = True
                        break
                    except OSError as exc:
                        if time.monotonic() >= deadline:
                            raise TimeoutError(f"Timed out acquiring exclusive lock on {target.name}") from exc
                        time.sleep(0.015)
            else:
                import fcntl

                while True:
                    try:
                        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        locked_os = True
                        break
                    except OSError as exc:
                        if time.monotonic() >= deadline:
                            raise TimeoutError(f"Timed out acquiring exclusive lock on {target.name}") from exc
                        time.sleep(0.015)
            depths[key] = 1
            yield
        finally:
            depths.pop(key, None)
            if locked_os:
                try:
                    if os.name == "nt":
                        import msvcrt

                        os.lseek(fd, 0, os.SEEK_SET)
                        msvcrt.locking(fd, msvcrt.LK_UNLCK, 1)
                    else:
                        import fcntl

                        fcntl.flock(fd, fcntl.LOCK_UN)
                except OSError:
                    pass
            try:
                os.close(fd)
            except OSError:
                pass


def _atomic_write_text(target: Path, content: str) -> None:
    """Crash-safe atomic file write (`NamedTemporaryFile` + `flush` + `os.fsync` + `os.replace`) under `exclusive_file_lock`."""
    resolved = target.resolve()
    resolved.parent.mkdir(parents=True, exist_ok=True)
    with exclusive_file_lock(resolved):
        tmp_path: Optional[Path] = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                dir=str(resolved.parent),
                prefix=f".{resolved.name}.tmp.{os.getpid()}.",
                suffix=".part",
                delete=False,
            ) as tf:
                tmp_path = Path(tf.name)
                tf.write(content)
                tf.flush()
                os.fsync(tf.fileno())
            for _rep_attempt in range(40):
                try:
                    os.replace(str(tmp_path), str(resolved))
                    break
                except PermissionError:
                    if _rep_attempt == 39:
                        raise
                    time.sleep(0.005)
        finally:
            if tmp_path is not None and tmp_path.exists():
                try:
                    tmp_path.unlink()
                except OSError:
                    pass


def _fn_store_key(file_rel: str, name: str, lineno: Any = None) -> str:
    if lineno is not None and not isinstance(lineno, bool):
        try:
            return f"{file_rel}:{name}@{int(lineno)}"
        except (TypeError, ValueError):
            pass
    return f"{file_rel}:{name}"


def _slim_fn_record(fn: Dict[str, Any], fallback_file: str = "") -> Dict[str, Any]:
    f_rel = str(fn.get("file") or fallback_file or "")
    raw_calls = list(fn.get("calls") or [])
    raw_all_calls = list(fn.get("all_calls") if fn.get("all_calls") is not None else raw_calls)
    raw_args = list(fn.get("args") or [])
    raw_typed_args = list(fn.get("typed_args") if fn.get("typed_args") is not None else raw_args)
    raw_pure = fn.get("is_pure")
    raw_exp = fn.get("is_exported")
    raw_lineno = fn.get("lineno")
    lineno_val = int(raw_lineno) if (raw_lineno is not None and not isinstance(raw_lineno, bool)) else 1
    raw_end_lineno = fn.get("end_lineno")
    end_lineno_val = int(raw_end_lineno) if (raw_end_lineno is not None and not isinstance(raw_end_lineno, bool)) else lineno_val
    rec: Dict[str, Any] = {
        "name": fn.get("name", ""),
        "short_name": fn.get("short_name") or str(fn.get("name") or "").split(".")[-1],
        "class_name": fn.get("class_name", ""),
        "file": f_rel,
        "lineno": lineno_val,
        "end_lineno": end_lineno_val,
        "args": raw_args,
        "typed_args": raw_typed_args,
        "required_arity": int(fn.get("required_arity") or 0),
        "return_type": str(fn.get("return_type") or ""),
        "summary": str(fn.get("summary") or ""),
        "calls": raw_calls,
        "all_calls": raw_all_calls,
        "calls_preview": list(fn.get("calls_preview") if fn.get("calls_preview") is not None else raw_calls[:8]),
        "callers": list(fn.get("callers") or []),
        "callees": list(fn.get("callees") or []),
        "name_refs": list(fn.get("name_refs") or []),
        "math_ops": list(fn.get("math_ops") or []),
        "self_attrs_loaded": list(fn.get("self_attrs_loaded") or []),
        "decorators": list(fn.get("decorators") or []),
        "is_exported": bool(raw_exp) if raw_exp is not None else None,
        "is_pure": bool(raw_pure) if raw_pure is not None else None,
        "is_pure_data_loader": bool(fn.get("is_pure_data_loader", False)),
        "reference_status": fn.get("reference_status"),
        "is_entrypoint": bool(fn.get("is_entrypoint", False)),
        "safe_auto_probe": bool(fn.get("safe_auto_probe", False)),
        "stage": fn.get("stage"),
        "ai_interaction": fn.get("ai_interaction"),
        "language": fn.get("language"),
    }
    return rec


ANVIL_SESSION_IR_SCHEMA = "anvil-ir/v5-dedup"


def _is_same_repo_identity_mapping_row(row: Any) -> bool:
    if not isinstance(row, dict) or row.get("status") != "MAPPED":
        return False
    old_sym = row.get("old_symbol") if "old_symbol" in row else row.get("old_function")
    new_sym = row.get("new_symbol") if "new_symbol" in row else row.get("new_function")
    if not old_sym or old_sym != new_sym:
        return False
    if str(row.get("old_file") or "") != str(row.get("new_file") or ""):
        return False
    return set(row.keys()) <= {
        "old_function",
        "old_file",
        "new_function",
        "new_file",
        "old_symbol",
        "new_symbol",
        "stage",
        "status",
    }


def _dehydrate_session_ir(session: Dict[str, Any]) -> Dict[str, Any]:
    """Normalize `.anvil/session.json` into a deduplicated `<2 MB` IR without mutating `session` in memory."""
    if not isinstance(session, dict):
        return session
    out: Dict[str, Any] = {k: v for k, v in session.items() if k not in ("code_map", "remap", "orange_split")}
    out["ir_version"] = ANVIL_SESSION_IR_SCHEMA
    out["ir_schema"] = ANVIL_SESSION_IR_SCHEMA

    raw_cmap = session.get("code_map")
    symbol_store: Dict[str, Dict[str, Any]] = {}
    if isinstance(raw_cmap, dict):
        cmap_out: Dict[str, Any] = {
            k: v
            for k, v in raw_cmap.items()
            if k not in ("blocks", "conceptual_buckets", "module_buckets", "process_map")
        }
        raw_buckets = raw_cmap.get("conceptual_buckets") or raw_cmap.get("blocks") or []
        raw_mods = raw_cmap.get("module_buckets") or []

        for mb in raw_mods:
            if not isinstance(mb, dict):
                continue
            mf_default = str(mb.get("primary_file") or mb.get("file") or "")
            for fn in mb.get("functions") or []:
                if isinstance(fn, dict) and fn.get("name"):
                    slim = _slim_fn_record(fn, mf_default)
                    skey = _fn_store_key(slim["file"], slim["name"], fn.get("lineno"))
                    symbol_store[skey] = slim

        dedup_buckets: List[Dict[str, Any]] = []
        for b in raw_buckets:
            if not isinstance(b, dict):
                continue
            b_copy = {
                k: v
                for k, v in b.items()
                if k not in ("functions", "progressive_levels", "source_preview", "level2_mechanics", "level3_code")
            }
            if b.get("source_preview"):
                b_copy["source_preview"] = str(b["source_preview"])[:600]
            bf_default = str(b.get("primary_file") or b.get("file") or "")
            fn_refs: List[str] = []
            for fn in b.get("functions") or []:
                if isinstance(fn, dict) and fn.get("name"):
                    slim = _slim_fn_record(fn, bf_default)
                    skey = _fn_store_key(slim["file"], slim["name"], fn.get("lineno"))
                    symbol_store.setdefault(skey, slim)
                    fn_refs.append(skey)
            b_copy["function_refs"] = fn_refs

            l2 = b.get("level2_mechanics")
            if isinstance(l2, dict):
                l2_out: Dict[str, Any] = {}
                for k, v in l2.items():
                    if k == "governing_equations" and "formulas_mathml" in l2 and v == l2.get("formulas_mathml"):
                        continue
                    if k == "data_contracts" and "state_contracts" in l2 and v == l2.get("state_contracts"):
                        continue
                    if k == "key_assumptions" and "assumptions" in l2 and v == l2.get("assumptions"):
                        continue
                    l2_out[k] = v
                b_copy["level2_mechanics"] = l2_out
            l3 = b.get("level3_code")
            if isinstance(l3, dict):
                b_copy["level3_code"] = {
                    "file": l3.get("file", bf_default),
                    "member_files": list(l3.get("member_files") or b.get("member_files") or ([bf_default] if bf_default else [])),
                    "files_index": list(l3.get("files_index") or [])[:40],
                    "on_demand_source_supported": True,
                    "start_line": int(l3.get("start_line") or 1),
                    "end_line": int(l3.get("end_line") or 1),
                    "total_lines": int(l3.get("total_lines") or b.get("total_lines") or 0),
                    "best_in_class_source": str(l3.get("best_in_class_source") or "")[:1200],
                }
            dedup_buckets.append(b_copy)

        dedup_mods: List[Dict[str, Any]] = []
        for mb in raw_mods:
            if not isinstance(mb, dict):
                continue
            mf_default = str(mb.get("primary_file") or mb.get("file") or "")
            m_refs: List[str] = []
            for fn in (mb.get("functions") or []):
                if isinstance(fn, dict) and fn.get("name"):
                    f_rel = str(fn.get("file") or mf_default)
                    skey = _fn_store_key(f_rel, str(fn["name"]), fn.get("lineno"))
                    symbol_store.setdefault(skey, _slim_fn_record(fn, mf_default))
                    m_refs.append(skey)
            raw_pcp = mb.get("pure_core_pct")
            pcp_val = int(raw_pcp) if (raw_pcp is not None and not isinstance(raw_pcp, bool)) else None
            dedup_mods.append({
                "id": mb.get("id", ""),
                "title": mb.get("title", ""),
                "file": mb.get("file", ""),
                "primary_file": mf_default,
                "member_files": list(mb.get("member_files") or ([mf_default] if mf_default else [])),
                "language": mb.get("language"),
                "summary": str(mb.get("summary") or "")[:200],
                "pipeline_stage": mb.get("pipeline_stage"),
                "pure_core_pct": pcp_val,
                "classes": list(mb.get("classes") or [])[:16],
                "imports": list(mb.get("imports") or [])[:20],
                "total_lines": int(mb.get("total_lines") or 0),
                "function_refs": m_refs,
            })

        dedup_bucket_ids = {str(b.get("id")) for b in dedup_buckets if isinstance(b, dict) and b.get("id")}
        if "process_map" in raw_cmap:
            raw_pm = raw_cmap.get("process_map")
            if raw_pm is None:
                cmap_out["process_map"] = None
            elif isinstance(raw_pm, dict):
                pm_out = dict(raw_pm)
                if "nodes" in raw_pm and isinstance(raw_pm.get("nodes"), list):
                    pm_out["nodes"] = [
                        (
                            {
                                k: v
                                for k, v in n.items()
                                if not (
                                    str(n.get("id") or "") in dedup_bucket_ids
                                    and k in ("level1_summary", "level2_mechanics", "level3_code")
                                )
                            }
                            if isinstance(n, dict)
                            else n
                        )
                        for n in raw_pm["nodes"]
                    ]
                cmap_out["process_map"] = pm_out
            else:
                cmap_out["process_map"] = raw_pm

        cmap_out["symbol_store"] = symbol_store
        cmap_out["conceptual_buckets"] = dedup_buckets
        cmap_out["module_buckets"] = dedup_mods
        out["code_map"] = cmap_out
    else:
        out["code_map"] = raw_cmap

    raw_orange = session.get("orange_split")
    if isinstance(raw_orange, dict):
        has_edc = "essential_domain_core_juice" in raw_orange
        has_juice = "juice" in raw_orange
        has_sic = "surface_io_contracts_peel" in raw_orange
        has_peel = "peel" in raw_orange
        if has_edc or has_juice or has_sic or has_peel:
            orange_out = {
                k: v
                for k, v in raw_orange.items()
                if k not in ("juice", "peel", "essential_domain_core_juice", "surface_io_contracts_peel")
            }
            juice_list = raw_orange.get("essential_domain_core_juice") if has_edc else raw_orange.get("juice")
            peel_list = raw_orange.get("surface_io_contracts_peel") if has_sic else raw_orange.get("peel")

            def _pack_orange_list(items_raw: Any) -> Tuple[List[str], List[Dict[str, Any]]]:
                refs: List[str] = []
                entries: List[Dict[str, Any]] = []
                for it in (items_raw or []):
                    if not isinstance(it, dict):
                        continue
                    nm = str(it.get("name") or "")
                    if nm:
                        f_rel = str(it.get("file") or "")
                        skey = _fn_store_key(f_rel, nm, it.get("lineno"))
                        if skey not in symbol_store:
                            symbol_store[skey] = _slim_fn_record(it, f_rel)
                            if isinstance(out.get("code_map"), dict):
                                out["code_map"]["symbol_store"] = symbol_store
                        base_rec = symbol_store[skey]
                        ov = {k: v for k, v in it.items() if k not in base_rec or base_rec[k] != v}
                        absent_k = [k for k in base_rec.keys() if k not in it]
                        refs.append(skey)
                        ent: Dict[str, Any] = {"ref": skey}
                        if ov:
                            ent["overlay"] = ov
                        if absent_k:
                            ent["absent"] = absent_k
                        entries.append(ent)
                    else:
                        entries.append({"inline": dict(it)})
                return refs, entries

            j_refs, j_entries = _pack_orange_list(juice_list)
            p_refs, p_entries = _pack_orange_list(peel_list)
            orange_out["juice_refs"] = j_refs
            orange_out["peel_refs"] = p_refs
            orange_out["juice_entries"] = j_entries
            orange_out["peel_entries"] = p_entries
            orange_out["_orange_keys"] = [
                k
                for k, flag in (
                    ("essential_domain_core_juice", has_edc),
                    ("juice", has_juice),
                    ("surface_io_contracts_peel", has_sic),
                    ("peel", has_peel),
                )
                if flag
            ]
            out["orange_split"] = orange_out
        else:
            out["orange_split"] = raw_orange
    else:
        out["orange_split"] = raw_orange

    raw_remap = session.get("remap")
    if isinstance(raw_remap, dict):
        same_repo = bool(raw_remap.get("old_repo") and raw_remap.get("old_repo") == raw_remap.get("new_repo"))
        remap_out = {}
        for k, v in raw_remap.items():
            if same_repo and k == "new_code_comprehension" and isinstance(v, dict):
                remap_out["same_repo_comprehension_omitted"] = True
                continue
            if (
                same_repo
                and k == "old_to_new_mappings"
                and isinstance(v, list)
                and len(v) > 60
                and all(_is_same_repo_identity_mapping_row(r) for r in v)
            ):
                remap_out["same_repo_identity_mappings_omitted"] = True
                remap_out["old_to_new_mappings_count"] = len(v)
                remap_out["_identity_mapping_rows"] = [
                    [
                        r.get("old_file", ""),
                        r.get("old_function"),
                        r.get("old_symbol"),
                        r.get("stage"),
                        sorted(r.keys()),
                    ]
                    for r in v
                ]
                continue
            remap_out[k] = v
        out["remap"] = remap_out
    else:
        out["remap"] = raw_remap

    return out


def _rehydrate_session_ir(raw_session: Dict[str, Any]) -> Dict[str, Any]:
    """Rehydrate deduplicated `.anvil/session.json` IR back into full in-memory projections."""
    if not isinstance(raw_session, dict):
        return raw_session
    session = copy.deepcopy(raw_session)
    cmap = session.get("code_map")
    is_v5_dedup = raw_session.get("ir_schema") == ANVIL_SESSION_IR_SCHEMA

    if not is_v5_dedup:
        if isinstance(cmap, dict):
            legacy_buckets = cmap.get("conceptual_buckets") if cmap.get("conceptual_buckets") is not None else (cmap.get("blocks") or [])
            cmap["conceptual_buckets"] = legacy_buckets
            cmap["blocks"] = legacy_buckets
        return session

    symbol_store: Dict[str, Dict[str, Any]] = {}
    fallback_symbol_index: Dict[str, Dict[str, Any]] = {}

    def _lookup_sym(ref: str) -> Optional[Dict[str, Any]]:
        if ref in symbol_store:
            return symbol_store[ref]
        if ref in fallback_symbol_index:
            return fallback_symbol_index[ref]
        base_ref = ref.split("@", 1)[0]
        return fallback_symbol_index.get(base_ref)

    def _expand_fn(sym: Dict[str, Any]) -> Dict[str, Any]:
        rec = copy.deepcopy(sym)
        if "all_calls" not in rec or rec["all_calls"] is None:
            rec["all_calls"] = list(rec.get("calls") or [])
        return rec

    if isinstance(cmap, dict):
        raw_store = cmap.get("symbol_store")
        if isinstance(raw_store, dict):
            symbol_store = raw_store
            for s_rec in symbol_store.values():
                if isinstance(s_rec, dict) and s_rec.get("name"):
                    fb_key = f"{s_rec.get('file', '')}:{s_rec.get('name', '')}"
                    fallback_symbol_index.setdefault(fb_key, s_rec)

        buckets = cmap.get("conceptual_buckets") if cmap.get("conceptual_buckets") is not None else (cmap.get("blocks") or [])
        bucket_by_id: Dict[str, Dict[str, Any]] = {}
        for b in buckets:
            if not isinstance(b, dict):
                continue
            if "functions" not in b and isinstance(b.get("function_refs"), list):
                resolved_fns: List[Dict[str, Any]] = []
                for ref in b["function_refs"]:
                    sym_hit = _lookup_sym(str(ref))
                    if sym_hit is not None:
                        resolved_fns.append(_expand_fn(sym_hit))
                b["functions"] = resolved_fns
            funcs = b.get("functions") or []
            l2 = b.get("level2_mechanics")
            if isinstance(l2, dict):
                if "sub_blocks" not in l2:
                    l2["sub_blocks"] = [
                        {
                            "id": f"{b.get('id', 'b')}-sub-{idx + 1}",
                            "step_num": idx + 1,
                            "name": fn.get("name", ""),
                            "file": fn.get("file") or b.get("primary_file") or "",
                            "lineno": fn.get("lineno", 1),
                            "end_lineno": fn.get("end_lineno", fn.get("lineno", 1)),
                            "stage": fn.get("stage") if fn.get("stage") is not None else "compute",
                            "is_pure": bool(fn["is_pure"]) if fn.get("is_pure") is not None else True,
                            "args": fn.get("args") or [],
                            "typed_args": fn.get("typed_args") or fn.get("args") or [],
                            "return_type": fn.get("return_type") or "",
                            "summary": fn.get("summary") or "",
                            "calls": fn.get("calls_preview") or (fn.get("calls") or [])[:8],
                            "callers": fn.get("callers") or [],
                            "callees": fn.get("callees") or [],
                        }
                        for idx, fn in enumerate(funcs[:24])
                    ]
                if "formulas_mathml" in l2:
                    l2.setdefault("governing_equations", copy.deepcopy(l2["formulas_mathml"]))
                if "state_contracts" in l2:
                    l2.setdefault("data_contracts", copy.deepcopy(l2["state_contracts"]))
                if "assumptions" in l2:
                    l2.setdefault("key_assumptions", copy.deepcopy(l2["assumptions"]))
            l3 = b.get("level3_code")
            if isinstance(l3, dict):
                subs = (l2.get("sub_blocks") if isinstance(l2, dict) else None) or []
                preview_txt = str(b.get("source_preview") or "")
                l3.setdefault("old_source", preview_txt)
                l3.setdefault("numbered_source_preview", preview_txt)
                l3.setdefault("symbol_table", subs)
                l3.setdefault("functions", subs[:24])
            if "progressive_levels" not in b and ("level1_summary" in b or "level2_mechanics" in b or "level3_code" in b):
                b["progressive_levels"] = {
                    "level_1": b.get("level1_summary"),
                    "level_2": b.get("level2_mechanics"),
                    "level_3": b.get("level3_code"),
                }
            if b.get("id"):
                bucket_by_id[str(b["id"])] = b

        cmap["conceptual_buckets"] = buckets
        cmap["blocks"] = buckets

        for mb in cmap.get("module_buckets") or []:
            if isinstance(mb, dict) and "functions" not in mb and isinstance(mb.get("function_refs"), list):
                mb_fns: List[Dict[str, Any]] = []
                for ref in mb["function_refs"]:
                    sym_hit = _lookup_sym(str(ref))
                    if sym_hit is not None:
                        mb_fns.append(_expand_fn(sym_hit))
                mb["functions"] = mb_fns

        pm = cmap.get("process_map")
        if isinstance(pm, dict):
            for node in pm.get("nodes") or []:
                if isinstance(node, dict) and str(node.get("id") or "") in bucket_by_id:
                    src_b = bucket_by_id[str(node["id"])]
                    if "level1_summary" in src_b:
                        node.setdefault("level1_summary", src_b.get("level1_summary"))
                    if "level2_mechanics" in src_b:
                        node.setdefault("level2_mechanics", src_b.get("level2_mechanics"))
                    if "level3_code" in src_b:
                        node.setdefault("level3_code", src_b.get("level3_code"))

    orange = session.get("orange_split")
    if isinstance(orange, dict):
        orange_keys = orange.pop("_orange_keys", None)
        j_entries = orange.pop("juice_entries", None)
        p_entries = orange.pop("peel_entries", None)
        j_refs = orange.pop("juice_refs", None)
        p_refs = orange.pop("peel_refs", None)

        def _unpack_orange(entries_raw: Any, refs_raw: Any) -> Optional[List[Dict[str, Any]]]:
            if isinstance(entries_raw, list):
                out_items: List[Dict[str, Any]] = []
                for ent in entries_raw:
                    if not isinstance(ent, dict):
                        continue
                    if "inline" in ent and isinstance(ent["inline"], dict):
                        out_items.append(copy.deepcopy(ent["inline"]))
                        continue
                    ref_s = str(ent.get("ref") or "")
                    sym_hit = _lookup_sym(ref_s)
                    item_d = copy.deepcopy(sym_hit) if sym_hit is not None else {}
                    for ak in (ent.get("absent") or []):
                        item_d.pop(ak, None)
                    if isinstance(ent.get("overlay"), dict):
                        item_d.update(copy.deepcopy(ent["overlay"]))
                    if item_d:
                        out_items.append(item_d)
                return out_items
            if isinstance(refs_raw, list):
                out_legacy: List[Dict[str, Any]] = []
                for r in refs_raw:
                    sym_hit = _lookup_sym(str(r))
                    if sym_hit is not None:
                        out_legacy.append(copy.deepcopy(sym_hit))
                return out_legacy
            return None

        j_restored = _unpack_orange(j_entries, j_refs)
        p_restored = _unpack_orange(p_entries, p_refs)
        if j_restored is not None:
            want_edc = ("essential_domain_core_juice" in orange_keys) if isinstance(orange_keys, list) else True
            want_j = ("juice" in orange_keys) if isinstance(orange_keys, list) else True
            if want_edc:
                orange.setdefault("essential_domain_core_juice", copy.deepcopy(j_restored))
            if want_j:
                orange.setdefault("juice", copy.deepcopy(j_restored))
        if p_restored is not None:
            want_sic = ("surface_io_contracts_peel" in orange_keys) if isinstance(orange_keys, list) else True
            want_p = ("peel" in orange_keys) if isinstance(orange_keys, list) else True
            if want_sic:
                orange.setdefault("surface_io_contracts_peel", copy.deepcopy(p_restored))
            if want_p:
                orange.setdefault("peel", copy.deepcopy(p_restored))

    remap = session.get("remap")
    if isinstance(remap, dict):
        omitted_comp = bool(remap.pop("same_repo_comprehension_omitted", False))
        omitted_id = bool(remap.pop("same_repo_identity_mappings_omitted", False))
        remap.pop("old_to_new_mappings_count", None)
        compact_id_rows = remap.pop("_identity_mapping_rows", None)
        if omitted_comp and isinstance(cmap, dict):
            remap.setdefault("new_code_comprehension", cmap)
        if omitted_id:
            if isinstance(compact_id_rows, list):
                rebuilt_rows: List[Dict[str, Any]] = []
                for cr in compact_id_rows:
                    if not isinstance(cr, list) or len(cr) < 5:
                        continue
                    f_val, fn_val, sym_val, stg_val, key_list = cr[0], cr[1], cr[2], cr[3], cr[4]
                    row_d: Dict[str, Any] = {}
                    for rk in (key_list or []):
                        if rk in ("old_file", "new_file"):
                            row_d[rk] = f_val
                        elif rk in ("old_function", "new_function"):
                            row_d[rk] = fn_val
                        elif rk in ("old_symbol", "new_symbol"):
                            row_d[rk] = sym_val
                        elif rk == "stage":
                            row_d[rk] = stg_val
                        elif rk == "status":
                            row_d[rk] = "MAPPED"
                    rebuilt_rows.append(row_d)
                remap.setdefault("old_to_new_mappings", rebuilt_rows)
            elif symbol_store:
                remap.setdefault(
                    "old_to_new_mappings",
                    [
                        {
                            "old_function": fn["name"],
                            "old_file": fn["file"],
                            "new_function": fn["name"],
                            "new_file": fn["file"],
                            "stage": fn.get("stage") if fn.get("stage") is not None else "compute",
                            "status": "MAPPED",
                        }
                        for fn in symbol_store.values()
                    ],
                )
    return session


_SESSION_IR_CACHE_LOCK = threading.RLock()
_SESSION_IR_CACHE: Dict[Tuple[str, int, int], Dict[str, Any]] = {}


def _write_session_ir(sfile: Path, session: Dict[str, Any]) -> None:
    """Persist deduplicated `.anvil/session.json` atomically (`temp + fsync + os.replace`) under `exclusive_file_lock`."""
    compact_ir = _dehydrate_session_ir(session)
    serialized = json.dumps(compact_ir, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    _atomic_write_text(sfile, serialized)
    with _SESSION_IR_CACHE_LOCK:
        _SESSION_IR_CACHE.clear()


def _stat_and_read_bytes_retry_win(sfile: Path) -> Tuple[os.stat_result, bytes]:
    for _rd_attempt in range(40):
        try:
            st = sfile.stat()
            raw_bytes = sfile.read_bytes()
            return st, raw_bytes
        except PermissionError:
            if _rd_attempt == 39:
                raise
            time.sleep(0.005)
    raise PermissionError(f"Unable to read {sfile}")


def _read_session_ir(sfile: Path) -> Dict[str, Any]:
    """Read and rehydrate `.anvil/session.json` strictly (raises on unreadable/corrupt JSON)."""
    for _st_attempt in range(40):
        try:
            st = sfile.stat()
            break
        except PermissionError:
            if _st_attempt == 39:
                raise
            time.sleep(0.005)
    ckey = (str(sfile.resolve()), int(st.st_mtime_ns), int(st.st_size))
    with _SESSION_IR_CACHE_LOCK:
        cached = _SESSION_IR_CACHE.get(ckey)
    if cached is not None:
        return copy.deepcopy(cached)
    st_fresh, raw_bytes = _stat_and_read_bytes_retry_win(sfile)
    ckey = (str(sfile.resolve()), int(st_fresh.st_mtime_ns), int(st_fresh.st_size))
    parsed = json.loads(raw_bytes.decode("utf-8"))
    if not isinstance(parsed, dict):
        raise ValueError("session.json root must be a JSON object")
    rehydrated = _rehydrate_session_ir(parsed)
    with _SESSION_IR_CACHE_LOCK:
        if len(_SESSION_IR_CACHE) >= 16:
            _SESSION_IR_CACHE.clear()
        _SESSION_IR_CACHE[ckey] = rehydrated
    return copy.deepcopy(rehydrated)


def _peek_active_session_ir_readonly(sfile: Path) -> Dict[str, Any]:
    """Fast read-only cached view of `.anvil/session.json` for `get_v4_cockpit_state` (<10 ms warm)."""
    for _st_attempt in range(40):
        try:
            st = sfile.stat()
            break
        except PermissionError:
            if _st_attempt == 39:
                raise
            time.sleep(0.005)
    ckey = (str(sfile.resolve()), int(st.st_mtime_ns), int(st.st_size))
    with _SESSION_IR_CACHE_LOCK:
        cached = _SESSION_IR_CACHE.get(ckey)
    if cached is not None:
        return copy.deepcopy(cached)
    loaded = _read_session_ir(sfile)
    with _SESSION_IR_CACHE_LOCK:
        hit_loaded = _SESSION_IR_CACHE.get(ckey, loaded)
        return copy.deepcopy(hit_loaded)


def _session_dir(cdir: Path) -> Path:
    return cdir / ".anvil"


def _session_file(cdir: Path) -> Path:
    return _session_dir(cdir) / "session.json"


def _v4_dir(cdir: Path) -> Path:
    return _session_dir(cdir) / "v4"


def _cockpit_display_name(cdir: Path) -> str:
    generic_headings = {
        "ecgberht — face", "ecgberht - face", "ecgberht",
        "aladdin — face", "aladdin - face", "aladdin",
        "jarvis — face", "jarvis - face", "jarvis",
        "steward — face", "steward - face", "steward",
    }
    ecg = cdir / "ECGBERHT.md"
    if ecg.is_file():
        try:
            for line in ecg.read_text(encoding="utf-8", errors="replace").splitlines():
                if line.strip().startswith("# "):
                    heading = line.strip()[2:].strip()
                    if heading and heading.lower() not in generic_headings:
                        return heading
                    break
        except Exception:
            pass
    rm = cdir / "roadmap.json"
    if rm.is_file():
        try:
            data = json.loads(rm.read_text(encoding="utf-8", errors="replace"))
            if isinstance(data, dict) and data.get("project"):
                proj = str(data["project"]).strip()
                if proj and proj.lower() not in generic_headings:
                    return proj
        except Exception:
            pass
    return cdir.name.replace("-", " ").replace("_", " ").strip() or "AI Cockpit"


def discover_cockpit_candidates(cdir: Path) -> Dict[str, List[Dict[str, str]]]:
    """Scan the cockpit directory for local software folders/files and local papers/docs (bounded & cached)."""
    key = str(cdir.resolve()).lower()
    now = time.monotonic()
    cached = _CANDIDATES_CACHE.get(key)
    if cached and (now - cached[0]) < 10.0:
        return cached[1]

    software: List[Dict[str, str]] = []
    papers: List[Dict[str, str]] = []
    if not cdir.is_dir():
        return {"software": software, "papers": papers}

    skip_dirs = {
        ".git", "__pycache__", "node_modules", ".venv", "venv",
        ".anvil", ".ecgberht", ".steward", "dist", "build",
    }
    code_exts = {".py", ".js", ".mjs", ".ts", ".r", ".jl", ".cpp", ".c"}
    paper_exts = {".pdf", ".md", ".tex", ".txt"}
    ignore_md = {
        "ecgberht.md", "deliverables.md", "strip.md", "history.md",
        "anvil-report.md", "readme.md",
    }

    top_code_count = 0
    total_walked = 0
    try:
        entries = sorted(cdir.iterdir(), key=lambda p: p.name.lower())
    except Exception:
        entries = []

    for entry in entries:
        if entry.name.startswith(".") or entry.is_symlink():
            continue
        if entry.is_file():
            ext = entry.suffix.lower()
            if ext in code_exts:
                top_code_count += 1
                software.append({
                    "path": entry.name,
                    "label": f"{entry.name} (file in cockpit)",
                    "kind": "file",
                })
            elif ext in paper_exts and entry.name.lower() not in ignore_md:
                papers.append({
                    "path": entry.name,
                    "label": entry.name,
                    "kind": ext.lstrip("."),
                })
        elif entry.is_dir() and entry.name not in skip_dirs:
            sub_code = 0
            for root, dirs, files in os.walk(entry, followlinks=False):
                dirs[:] = [d for d in dirs if d not in skip_dirs and not d.startswith(".")]
                for f in files:
                    total_walked += 1
                    if total_walked > 250:
                        break
                    if f.startswith(".") or f.lower() in FORBIDDEN_SECRET_NAMES:
                        continue
                    fext = Path(f).suffix.lower()
                    rel = (Path(root) / f).relative_to(cdir).as_posix()
                    if fext in code_exts:
                        sub_code += 1
                    elif fext in paper_exts and f.lower() not in ignore_md and len(papers) < 20:
                        papers.append({
                            "path": rel,
                            "label": rel,
                            "kind": fext.lstrip("."),
                        })
                if sub_code > 60 or total_walked > 250:
                    break
            if sub_code > 0:
                software.insert(0, {
                    "path": entry.name,
                    "label": f"{entry.name}/ ({sub_code} code files)",
                    "kind": "dir",
                })

    if top_code_count > 0 or not software:
        software.insert(0, {
            "path": ".",
            "label": f"This Cockpit Folder ({cdir.name})" + (f" · {top_code_count} top-level code files" if top_code_count else ""),
            "kind": "cockpit_root",
        })

    if "anchor" in cdir.name.lower() or "anchor" in cdir.parent.name.lower():
        sc_dir = (_ANCHOR_ROOT / "steward_cockpit").resolve()
        if _ANCHOR_ROOT.is_dir():
            software.insert(0, {
                "path": str(_ANCHOR_ROOT.resolve()),
                "label": f"Anchor Root ({_ANCHOR_ROOT.resolve()}) · Repository Root",
                "kind": "dir",
            })
        if sc_dir.is_dir():
            software.insert(1, {
                "path": str(sc_dir),
                "label": f"Anchor steward_cockpit/ ({sc_dir}) · Cockpit Subsystem",
                "kind": "dir",
            })

    result = {
        "software": software[:16],
        "papers": papers[:16],
    }
    _CANDIDATES_CACHE[key] = (now, result)
    return result


def _validate_and_resolve_local_path(cdir: Path, spec: str) -> Path:
    """Strictly validate a local path spec against UNC/SMB leaks, dot-directories, secret files, and traversal."""
    raw = (spec or "").strip()
    if not raw or raw == ".":
        return cdir.resolve()
    if raw.startswith(("\\\\", "//", "\\\\?\\")):
        raise ValueError("Network/UNC paths are not permitted.")
    if re.match(r"^[A-Za-z]:(?![\\/])", raw):
        raise ValueError("Drive-relative paths are not permitted.")

    raw_parts = [p for p in re.split(r"[\\/]+", raw) if p]
    for part in raw_parts:
        low = part.lower()
        if part == "..":
            raise ValueError("Parent directory traversal ('..') is not permitted.")
        if low in FORBIDDEN_DOT_PARTS or low in FORBIDDEN_SECRET_NAMES:
            raise ValueError(f"Access to hidden or credential path '{part}' is not permitted.")
        if part.startswith(".") and part != ".":
            raise ValueError(f"Access to dot-path '{part}' is not permitted.")

    candidate = Path(raw)
    cdir_resolved = cdir.resolve()
    if not candidate.is_absolute():
        resolved = (cdir_resolved / candidate).resolve()
    else:
        resolved = candidate.resolve()

    if candidate.is_symlink() or resolved.is_symlink():
        raise ValueError("Symbolic links are not permitted as targets.")

    allowed = [cdir_resolved] + list(ALLOWED_LOCAL_ROOTS)
    within = any(resolved == root or root in resolved.parents for root in allowed)
    if not within:
        raise ValueError(f"Path '{spec}' is outside allowed workspace boundaries.")

    for part in resolved.parts:
        low = part.lower()
        if low in FORBIDDEN_DOT_PARTS or low in FORBIDDEN_SECRET_NAMES:
            raise ValueError(f"Access to restricted path component '{part}' is not permitted.")

    return resolved


def resolve_software_target(cdir: Path, target_spec: str, role: str = "primary") -> Dict[str, Any]:
    """Resolve either a local path (in cockpit or C:\\dev) or safely clone/update a GitHub repository."""
    spec = (target_spec or ".").strip()
    if not spec or spec == ".":
        return {
            "path": str(cdir.resolve()),
            "source_type": "cockpit_local",
            "label": f"{cdir.name} (cockpit root)",
            "spec": ".",
        }

    m = GITHUB_URL_RE.match(spec)
    if m:
        owner, repo = m.group(1), m.group(2)
        if repo.lower().endswith(".git"):
            repo = repo[:-4]
        if owner.startswith("-") or repo.startswith("-") or ".." in owner or ".." in repo:
            raise ValueError("Invalid GitHub owner or repository name.")
        safe_slug = re.sub(r"[^A-Za-z0-9_.-]+", "_", f"{owner}__{repo}")
        repos_root = _session_dir(cdir) / "repos"
        repos_root.mkdir(parents=True, exist_ok=True)
        dest = (repos_root / safe_slug).resolve()
        https_url = f"https://github.com/{owner}/{repo}.git"
        git_env = {
            **os.environ,
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_LFS_SKIP_SMUDGE": "1",
        }
        if (dest / ".git").is_dir():
            proc = subprocess.run(
                [
                    "git", "-C", str(dest),
                    "-c", "core.symlinks=false",
                    "-c", "protocol.file.allow=never",
                    "pull", "--ff-only",
                ],
                capture_output=True,
                text=True,
                timeout=45,
                shell=False,
                env=git_env,
            )
            if proc.returncode != 0:
                err = (proc.stderr or proc.stdout or "git pull failed").strip()[:300]
                raise ValueError(f"Failed to update existing clone of https://github.com/{owner}/{repo}: {err}")
        else:
            if dest.exists():
                shutil.rmtree(dest, ignore_errors=True)
            tmp_dest = (repos_root / f".tmp_{safe_slug}_{os.getpid()}").resolve()
            if tmp_dest.exists():
                shutil.rmtree(tmp_dest, ignore_errors=True)
            try:
                proc = subprocess.run(
                    [
                        "git",
                        "-c", "core.symlinks=false",
                        "-c", "protocol.file.allow=never",
                        "clone", "--depth", "1", "--no-tags", "--",
                        https_url, str(tmp_dest),
                    ],
                    capture_output=True,
                    text=True,
                    timeout=60,
                    shell=False,
                    env=git_env,
                )
                if proc.returncode != 0:
                    err = (proc.stderr or proc.stdout or "git clone failed").strip()[:300]
                    raise ValueError(f"Could not clone GitHub repository https://github.com/{owner}/{repo}: {err}")
                os.replace(str(tmp_dest), str(dest))
            finally:
                if tmp_dest.exists():
                    shutil.rmtree(tmp_dest, ignore_errors=True)

        return {
            "path": str(dest),
            "source_type": "github",
            "label": f"github.com/{owner}/{repo}",
            "url": f"https://github.com/{owner}/{repo}",
            "spec": spec,
        }

    candidate = _validate_and_resolve_local_path(cdir, spec)
    if not candidate.exists():
        raise ValueError(f"Software target '{spec}' does not exist at {candidate}.")

    try:
        rel_label = candidate.relative_to(cdir.resolve()).as_posix() or "."
    except ValueError:
        rel_label = str(candidate)

    return {
        "path": str(candidate),
        "source_type": "local",
        "label": rel_label,
        "spec": spec,
    }


def _validate_public_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme not in ("http", "https"):
        raise ValueError("Only http:// and https:// URLs are supported for internet paper fetching.")
    host = (parsed.hostname or "").strip().lower()
    if not host or host in ("localhost", "127.0.0.1", "::1", "0.0.0.0"):
        raise ValueError("Loopback/local URLs are not permitted for internet paper fetching.")
    try:
        infos = socket.getaddrinfo(host, None)
        if not infos:
            raise ValueError(f"Could not resolve host '{host}'.")
        for info in infos:
            ip_str = info[4][0]
            ip_obj = ipaddress.ip_address(ip_str)
            if (
                not ip_obj.is_global
                or ip_obj.is_private
                or ip_obj.is_loopback
                or ip_obj.is_link_local
                or ip_obj.is_multicast
                or ip_obj.is_reserved
                or ip_obj.is_unspecified
            ):
                raise ValueError(f"Host '{host}' resolves to a non-public IP address ({ip_str}).")
    except socket.gaierror as exc:
        raise ValueError(f"Could not resolve host '{host}': {exc}") from exc
    return url


class _SafeRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        full_new = urllib.parse.urljoin(req.full_url, newurl)
        _validate_public_url(full_new)
        hops = getattr(req, "_anvil_redirects", 0) + 1
        if hops > 3:
            raise ValueError("Too many HTTP redirects while fetching paper URL.")
        new_req = super().redirect_request(req, fp, code, msg, headers, full_new)
        if new_req is not None:
            setattr(new_req, "_anvil_redirects", hops)
        return new_req


def _safe_urlopen(url: str, max_bytes: int = 2_000_000, timeout: float = 12.0) -> Tuple[bytes, str]:
    _validate_public_url(url)
    opener = urllib.request.build_opener(_SafeRedirectHandler())
    req = urllib.request.Request(url, headers={"User-Agent": "Anchor-Anvil/1.0"})
    t0 = time.monotonic()
    chunks: List[bytes] = []
    total = 0
    with opener.open(req, timeout=timeout) as resp:
        content_type = (resp.headers.get("Content-Type") or "").lower()
        while total < max_bytes:
            if (time.monotonic() - t0) > timeout:
                raise ValueError("Timed out reading remote paper content.")
            chunk = resp.read(min(65536, max_bytes - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
    return b"".join(chunks), content_type


def _extract_latex_title(tex_text: str) -> str:
    """Extract a clean human title from LaTeX `\\title{...}` if present."""
    no_comments = re.sub(r"(?<!\\)%[^\n]*", "", tex_text or "")
    m = re.search(r"\\title(?:\[[^\]]*\])?\s*\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", no_comments, flags=re.S)
    if not m:
        return ""
    raw = m.group(1)
    raw = re.sub(r"\\[A-Za-z]+\s*", " ", raw)
    raw = re.sub(r"[{}]", " ", raw)
    return " ".join(raw.split()).strip()[:140]


def _pick_primary_tex_in_dir(bundle_dir: Path, candidates: Optional[List[Path]] = None) -> Optional[Path]:
    """Choose the root `.tex` file inside an extracted bundle or local paper directory."""
    tex_files = (
        [p for p in candidates if p.suffix.lower() == ".tex" and p.is_file()]
        if candidates is not None
        else [
            p
            for p in sorted(bundle_dir.rglob("*.tex"))
            if p.is_file() and not p.is_symlink()
        ]
    )
    if not tex_files:
        return None
    best_path = tex_files[0]
    best_score = -1
    for p in tex_files:
        try:
            txt = p.read_text(encoding="utf-8", errors="replace")
        except Exception:
            txt = ""
        no_c = re.sub(r"(?<!\\)%[^\n]*", "", txt)
        score = 0
        if "\\documentclass" in no_c:
            score += 100
        if "\\begin{document}" in no_c:
            score += 50
        if p.stem.lower() in ("main", "paper", "ms", "article", "manuscript"):
            score += 25
        score += min(20, len(no_c) // 2000)
        if score > best_score:
            best_score = score
            best_path = p
    return best_path


def _safe_extract_arxiv_bundle(
    raw_bytes: bytes,
    dest_dir: Path,
    max_files: int = 120,
    max_total_bytes: int = 12_000_000,
) -> Optional[Path]:
    """Safely extract an arXiv `/e-print/<id>` tar/tar.gz or single-file .gz bundle into `dest_dir`.

    Enforces strict path-containment, blocks `..`, absolute/UNC/drive paths, symlinks, hardlinks,
    devices/FIFOs, secret/dot paths, and bounds file count and uncompressed bytes.
    """
    if not raw_bytes:
        return None
    if raw_bytes[:4] == b"%PDF":
        return None

    if dest_dir.is_symlink():
        raise ValueError("Extraction destination cannot be a symbolic link.")
    dest_resolved = dest_dir.resolve()
    if dest_resolved.exists():
        if dest_resolved.is_symlink():
            raise ValueError("Extraction destination cannot be a symbolic link.")
        shutil.rmtree(dest_resolved, ignore_errors=True)
    dest_resolved.mkdir(parents=True, exist_ok=True)

    extracted_files: List[Path] = []
    total_written = 0

    tf_obj: Optional[tarfile.TarFile] = None
    try:
        tf_obj = tarfile.open(fileobj=io.BytesIO(raw_bytes), mode="r:*")
    except tarfile.TarError:
        tf_obj = None

    if tf_obj is not None:
        with tf_obj:
            member_count = 0
            while True:
                m = tf_obj.next()
                if m is None:
                    break
                member_count += 1
                if member_count > max_files:
                    raise ValueError(f"Archive exceeds maximum allowed file count ({max_files}).")
                raw_name = (m.name or "").strip()
                if m.issym() or m.islnk() or m.isdev() or m.isfifo():
                    raise ValueError(
                        f"Unsafe archive entry '{raw_name}': symbolic links, hard links, and special files are not permitted."
                    )
                if not raw_name:
                    continue
                if raw_name.startswith(("/", "\\")) or re.match(r"^[A-Za-z]:", raw_name):
                    raise ValueError(f"Unsafe absolute or drive path in archive entry '{raw_name}'.")
                parts = [p for p in re.split(r"[\\/]+", raw_name) if p]
                clean_parts: List[str] = []
                for part in parts:
                    if part == ".":
                        continue
                    if part == "..":
                        raise ValueError(f"Parent directory traversal ('..') in archive entry '{raw_name}' is not permitted.")
                    low = part.lower()
                    if low in FORBIDDEN_DOT_PARTS or low in FORBIDDEN_SECRET_NAMES or part.startswith("."):
                        raise ValueError(f"Restricted path component '{part}' in archive entry '{raw_name}' is not permitted.")
                    clean_parts.append(part)
                if not clean_parts:
                    continue
                target_path = (dest_resolved / Path(*clean_parts)).resolve()
                if target_path != dest_resolved and dest_resolved not in target_path.parents:
                    raise ValueError(f"Archive entry '{raw_name}' escapes extraction root.")
                if m.isdir():
                    target_path.mkdir(parents=True, exist_ok=True)
                    continue
                if not m.isfile():
                    raise ValueError(f"Unsupported archive entry type for '{raw_name}'.")
                if m.size < 0 or (total_written + m.size) > max_total_bytes:
                    raise ValueError("Archive exceeds maximum uncompressed byte limit.")
                fobj = tf_obj.extractfile(m)
                if fobj is None:
                    continue
                target_path.parent.mkdir(parents=True, exist_ok=True)
                chunks: List[bytes] = []
                with fobj:
                    while True:
                        chunk = fobj.read(65536)
                        if not chunk:
                            break
                        total_written += len(chunk)
                        if total_written > max_total_bytes:
                            raise ValueError("Archive exceeds maximum uncompressed byte limit.")
                        chunks.append(chunk)
                target_path.write_bytes(b"".join(chunks))
                extracted_files.append(target_path)
    elif raw_bytes[:2] == b"\x1f\x8b":
        chunks = []
        with gzip.GzipFile(fileobj=io.BytesIO(raw_bytes), mode="rb") as gz:
            while True:
                chunk = gz.read(65536)
                if not chunk:
                    break
                total_written += len(chunk)
                if total_written > max_total_bytes:
                    raise ValueError("Compressed e-print exceeds maximum uncompressed byte limit.")
                chunks.append(chunk)
        decomp = b"".join(chunks)
        if decomp[:4] == b"%PDF":
            return None
        decoded = decomp.decode("utf-8", errors="replace")
        if any(tok in decoded for tok in ("\\documentclass", "\\section", "\\begin{", "\\input{")):
            main_tex = dest_resolved / "main.tex"
            _atomic_write_text(main_tex, decoded)
            extracted_files.append(main_tex)
    else:
        decoded = raw_bytes.decode("utf-8", errors="replace")
        if any(tok in decoded for tok in ("\\documentclass", "\\section", "\\begin{document}")):
            main_tex = dest_resolved / "main.tex"
            _atomic_write_text(main_tex, decoded)
            extracted_files.append(main_tex)

    return _pick_primary_tex_in_dir(dest_resolved, extracted_files)


def resolve_paper_source(cdir: Path, paper_spec: str) -> Dict[str, Any]:
    """Resolve a paper from an arXiv ID/URL (`/e-print/<id>` TeX bundle first, Atom XML fallback), an HTTPS URL, or a local file/directory."""
    spec = (paper_spec or "").strip()
    if not spec:
        raise ValueError("Please provide a paper URL (e.g. arXiv link) or select a local paper file or TeX folder in this cockpit.")

    papers_dir = _session_dir(cdir) / "papers"
    papers_dir.mkdir(parents=True, exist_ok=True)

    arxiv_match = ARXIV_ID_RE.search(spec)
    if arxiv_match:
        arxiv_id = arxiv_match.group(1)
        safe_id = re.sub(r"[^A-Za-z0-9_.-]+", "_", arxiv_id)
        eprint_url = f"https://arxiv.org/e-print/{urllib.parse.quote(arxiv_id)}"
        eprint_bytes: Optional[bytes] = None
        try:
            eprint_bytes, _ = _safe_urlopen(eprint_url, max_bytes=8_000_000, timeout=15.0)
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, socket.timeout, OSError):
            eprint_bytes = None

        if eprint_bytes:
            bundle_dir = papers_dir / f"arxiv_{safe_id}_src"
            primary_tex = _safe_extract_arxiv_bundle(eprint_bytes, bundle_dir)
            if primary_tex is not None and primary_tex.is_file():
                tex_text = primary_tex.read_text(encoding="utf-8", errors="replace")
                tex_title = _extract_latex_title(tex_text) or f"arXiv:{arxiv_id}"
                return {
                    "path": str(primary_tex),
                    "bundle_dir": str(bundle_dir),
                    "source_type": "arxiv_eprint",
                    "title": tex_title,
                    "url": f"https://arxiv.org/abs/{arxiv_id}",
                    "text": tex_text,
                    "spec": spec,
                }

        api_url = f"https://export.arxiv.org/api/query?id_list={urllib.parse.quote(arxiv_id)}"
        xml_bytes, _ = _safe_urlopen(api_url, max_bytes=1_500_000, timeout=12.0)
        root = ET.fromstring(xml_bytes)
        ns = {"a": "http://www.w3.org/2005/Atom"}
        entry = root.find("a:entry", ns)
        title = f"arXiv:{arxiv_id}"
        summary = ""
        if entry is not None:
            t_el = entry.find("a:title", ns)
            s_el = entry.find("a:summary", ns)
            if t_el is not None and t_el.text:
                title = " ".join(t_el.text.split())
            if s_el is not None and s_el.text:
                summary = " ".join(s_el.text.split())
        dest = papers_dir / f"arxiv_{safe_id}.md"
        md_text = f"# {title}\n\nSource: https://arxiv.org/abs/{arxiv_id}\n\n## Abstract & Core Claims\n\n{summary}\n"
        _atomic_write_text(dest, md_text)
        return {
            "path": str(dest),
            "source_type": "arxiv",
            "title": title,
            "url": f"https://arxiv.org/abs/{arxiv_id}",
            "text": md_text,
            "spec": spec,
        }

    if spec.lower().startswith(("http://", "https://")):
        raw_bytes, content_type = _safe_urlopen(spec, max_bytes=4_000_000, timeout=12.0)
        base_slug = re.sub(r"[^A-Za-z0-9_.-]+", "_", Path(urllib.parse.urlparse(spec).path).stem or "paper")[:44]
        url_hash = hashlib.sha1(spec.encode("utf-8")).hexdigest()[:8]
        slug = f"{base_slug}_{url_hash}"
        if any(ext in spec.lower() for ext in (".tar.gz", ".tgz")) or "gzip" in content_type or "tar" in content_type:
            bundle_dir = papers_dir / f"{slug}_src"
            primary_tex = _safe_extract_arxiv_bundle(raw_bytes, bundle_dir)
            if primary_tex is not None and primary_tex.is_file():
                tex_text = primary_tex.read_text(encoding="utf-8", errors="replace")
                tex_title = _extract_latex_title(tex_text) or slug
                return {
                    "path": str(primary_tex),
                    "bundle_dir": str(bundle_dir),
                    "source_type": "url_bundle",
                    "title": tex_title[:110],
                    "url": spec,
                    "text": tex_text,
                    "spec": spec,
                }
        if "pdf" in content_type or spec.lower().endswith(".pdf"):
            dest = papers_dir / f"{slug}.pdf"
            dest.write_bytes(raw_bytes)
            text = _extract_text_from_file(dest)
        elif spec.lower().endswith(".tex"):
            text = raw_bytes.decode("utf-8", errors="replace")
            dest = papers_dir / f"{slug}.tex"
            _atomic_write_text(dest, text)
        else:
            raw_str = raw_bytes.decode("utf-8", errors="replace")
            if "<html" in raw_str.lower() or "<body" in raw_str.lower():
                title_m = re.search(r"<title[^>]*>(.*?)</title>", raw_str, re.I | re.S)
                page_title = html.unescape(re.sub(r"\s+", " ", title_m.group(1)).strip()) if title_m else spec
                stripped = re.sub(r"<script\b[^>]*>.*?</script>", " ", raw_str, flags=re.I | re.S)
                stripped = re.sub(r"<style\b[^>]*>.*?</style>", " ", stripped, flags=re.I | re.S)
                stripped = re.sub(r"<[^>]+>", "\n", stripped)
                lines = [ln.strip() for ln in stripped.splitlines() if ln.strip()]
                text = f"# {page_title}\n\nSource: {spec}\n\n" + "\n".join(lines[:400])
            else:
                text = raw_str
            dest = papers_dir / f"{slug}.md"
            _atomic_write_text(dest, text)
        first_line = _extract_latex_title(text) or next((ln.lstrip("# ").strip() for ln in text.splitlines() if ln.strip()), slug)
        return {
            "path": str(dest),
            "source_type": "url",
            "title": first_line[:110],
            "url": spec,
            "text": text,
            "spec": spec,
        }

    candidate = _validate_and_resolve_local_path(cdir, spec)
    if candidate.is_dir():
        primary_tex = _pick_primary_tex_in_dir(candidate)
        if primary_tex is not None:
            tex_text = primary_tex.read_text(encoding="utf-8", errors="replace")
            title = _extract_latex_title(tex_text) or candidate.name
            return {
                "path": str(candidate),
                "primary_tex": str(primary_tex),
                "source_type": "local_dir",
                "title": title[:110],
                "url": "",
                "text": tex_text,
                "spec": spec,
            }
        md_files = [p for p in sorted(candidate.glob("*.md")) if p.is_file() and not p.is_symlink()]
        if md_files:
            md_text = md_files[0].read_text(encoding="utf-8", errors="replace")
            first_line = next((ln.lstrip("# ").strip() for ln in md_text.splitlines() if ln.strip()), candidate.name)
            return {
                "path": str(md_files[0]),
                "source_type": "local",
                "title": first_line[:110] or candidate.name,
                "url": "",
                "text": md_text,
                "spec": spec,
            }
        raise ValueError(f"Paper directory '{spec}' at {candidate} contains no .tex or .md manuscript files.")
    if not candidate.is_file():
        raise ValueError(f"Paper file '{spec}' was not found at {candidate}.")

    text = _extract_text_from_file(candidate)
    first_line = _extract_latex_title(text) or next((ln.lstrip("#% ").strip() for ln in text.splitlines() if ln.strip()), candidate.name)
    return {
        "path": str(candidate),
        "source_type": "local",
        "title": first_line[:110] or candidate.name,
        "url": "",
        "text": text,
        "spec": spec,
    }


def _extract_text_from_file(path: Path) -> str:
    if path.suffix.lower() == ".pdf":
        try:
            pypdf = importlib.import_module("pypdf")  # type: ignore
            reader = pypdf.PdfReader(str(path))
            pages = [page.extract_text() or "" for page in reader.pages[:25]]
            extracted = "\n\n".join(p for p in pages if p.strip())
            if extracted.strip():
                return extracted
        except Exception:
            pass
        try:
            fitz = importlib.import_module("fitz")  # type: ignore
            doc = fitz.open(str(path))
            pages = [doc[i].get_text("text") for i in range(min(25, len(doc)))]
            extracted = "\n\n".join(p for p in pages if p.strip())
            if extracted.strip():
                return extracted
        except Exception:
            pass
        return f"# {path.name}\n\nBinary PDF paper loaded from {path.name}."
    return path.read_text(encoding="utf-8", errors="replace")


LATEX_SYMBOLS = (
    (r"\varepsilon", "ε"),
    (r"\varphi", "φ"),
    (r"\epsilon", "ϵ"),
    (r"\alpha", "α"),
    (r"\beta", "β"),
    (r"\gamma", "γ"),
    (r"\delta", "δ"),
    (r"\zeta", "ζ"),
    (r"\eta", "η"),
    (r"\theta", "θ"),
    (r"\iota", "ι"),
    (r"\kappa", "κ"),
    (r"\lambda", "λ"),
    (r"\mu", "μ"),
    (r"\nu", "ν"),
    (r"\xi", "ξ"),
    (r"\pi", "π"),
    (r"\rho", "ρ"),
    (r"\sigma", "σ"),
    (r"\tau", "τ"),
    (r"\phi", "ϕ"),
    (r"\chi", "χ"),
    (r"\psi", "ψ"),
    (r"\omega", "ω"),
    (r"\Gamma", "Γ"),
    (r"\Delta", "Δ"),
    (r"\Theta", "Θ"),
    (r"\Lambda", "Λ"),
    (r"\Sigma", "Σ"),
    (r"\Phi", "Φ"),
    (r"\Psi", "Ψ"),
    (r"\Omega", "Ω"),
    (r"\infty", "∞"),
    (r"\partial", "∂"),
    (r"\nabla", "∇"),
    (r"\approx", "≈"),
    (r"\times", "×"),
    (r"\cdots", "⋯"),
    (r"\cdot", "⋅"),
    (r"\leq", "≤"),
    (r"\geq", "≥"),
    (r"\neq", "≠"),
    (r"\le", "≤"),
    (r"\ge", "≥"),
    (r"\in", "∈"),
)


def latex_to_mathml(expr: str, title_hint: str = "") -> str:
    """Convert a LaTeX or symbolic mathematical expression into strictly escaped native MathML (<math>).

    Never passes raw HTML tags through (preventing XSS) and guarantees zero raw LaTeX tokens remain.
    """
    raw = (expr or "").strip()
    if not raw:
        return ""

    # Strip any HTML/XML tags from input so attacker-supplied <img/script/math> tags never survive
    cleaned = re.sub(r"<[^>]*>", " ", raw)
    cleaned = cleaned.replace("<", " ≤ ").replace(">", " ≥ ")
    cleaned = cleaned.strip("$").strip()
    cleaned = re.sub(r"^\\\[|\\\]$", "", cleaned).strip()
    if not cleaned:
        return ""

    # Replace wrapper macros first
    cleaned = re.sub(r"\\(?:mathcal|mathbf|mathrm|text|hat|bar|tilde)\s*\{([^{}]+)\}", r"\1", cleaned)

    # Use private-use sentinel store for structured MathML blocks so user input is never split on '<...>'
    sentinels: Dict[str, str] = {}

    def _put_sentinel(mml_fragment: str) -> str:
        key = f"\ue000MML{len(sentinels)}\ue001"
        sentinels[key] = mml_fragment
        return key

    # 1. Handle \frac{num}{den}
    frac_pat = re.compile(r"\\frac\s*\{([^{}]+)\}\s*\{([^{}]+)\}")
    for _ in range(8):
        if not frac_pat.search(cleaned):
            break
        cleaned = frac_pat.sub(
            lambda m: _put_sentinel(
                f"<mfrac><mrow>{_simple_tokens_to_mml(m.group(1), sentinels)}</mrow>"
                f"<mrow>{_simple_tokens_to_mml(m.group(2), sentinels)}</mrow></mfrac>"
            ),
            cleaned,
        )

    # 2. Handle \sum_{sub}^{sup}
    sum_pat = re.compile(r"\\sum(?![A-Za-z])\s*(?:_\{([^{}]+)\}|_([A-Za-z0-9]))?\s*(?:\^\{([^{}]+)\}|\^([A-Za-z0-9]))?")
    if "\\sum" in cleaned:
        cleaned = sum_pat.sub(
            lambda m: _put_sentinel(
                f"<munderover><mo>∑</mo>"
                f"<mrow>{_simple_tokens_to_mml(m.group(1) or m.group(2) or 'i=1', sentinels)}</mrow>"
                f"<mrow>{_simple_tokens_to_mml(m.group(3) or m.group(4) or 'N', sentinels)}</mrow></munderover>"
            ),
            cleaned,
        )

    # 3. Handle \int_{sub}^{sup} (BEFORE \in replacement!)
    int_pat = re.compile(r"\\int(?![A-Za-z])\s*(?:_\{([^{}]+)\}|_([A-Za-z0-9]))?\s*(?:\^\{([^{}]+)\}|\^([A-Za-z0-9]))?")
    if "\\int" in cleaned:
        cleaned = int_pat.sub(
            lambda m: _put_sentinel(
                f"<msubsup><mo>∫</mo>"
                f"<mrow>{_simple_tokens_to_mml(m.group(1) or m.group(2) or '0', sentinels)}</mrow>"
                f"<mrow>{_simple_tokens_to_mml(m.group(3) or m.group(4) or 'T', sentinels)}</mrow></msubsup>"
            ),
            cleaned,
        )

    # 4. Replace LaTeX symbol commands longest-first with negative lookahead for letters
    for cmd, sym in sorted(LATEX_SYMBOLS, key=lambda kv: -len(kv[0])):
        cleaned = re.sub(re.escape(cmd) + r"(?![A-Za-z])", sym, cleaned)

    # Strip any remaining unknown backslash commands
    cleaned = re.sub(r"\\[A-Za-z]+", "", cleaned).replace("$$", "").replace("$", "")

    inner = _simple_tokens_to_mml(cleaned, sentinels)
    for k, v in sentinels.items():
        inner = inner.replace(k, v)

    if not inner:
        return ""
    return f"<math xmlns='http://www.w3.org/1998/Math/MathML' display='block'><mrow>{inner}</mrow></math>"


_IDENT_CHARS = r"A-Za-zα-ωΑ-Ωϵϕεφ"


def _simple_tokens_to_mml(text: str, sentinels: Dict[str, str]) -> str:
    s = (text or "").strip()
    if not s:
        return ""

    for cmd, sym in sorted(LATEX_SYMBOLS, key=lambda kv: -len(kv[0])):
        s = re.sub(re.escape(cmd) + r"(?![A-Za-z])", sym, s)

    def _put_sub_sup(tag: str, base_tok: str, script_tok: str, script_tag: str) -> str:
        key = f"\ue000MML{len(sentinels)}\ue001"
        b_esc = html.escape(base_tok, quote=True)
        s_esc = html.escape(script_tok, quote=True)
        b_tag = "mn" if re.fullmatch(r"\d+(?:\.\d+)?", base_tok) else "mi"
        sentinels[key] = f"<{tag}><{b_tag}>{b_esc}</{b_tag}><{script_tag}>{s_esc}</{script_tag}></{tag}>"
        return key

    s = re.sub(
        rf"([{_IDENT_CHARS}])\s*_\s*\{{([^{{}}]+)\}}",
        lambda m: _put_sub_sup("msub", m.group(1), m.group(2), "mi"),
        s,
    )
    s = re.sub(
        rf"([{_IDENT_CHARS}])\s*_\s*([A-Za-z0-9]+)",
        lambda m: _put_sub_sup("msub", m.group(1), m.group(2), "mi"),
        s,
    )
    s = re.sub(
        rf"([{_IDENT_CHARS}0-9])\s*\^\s*\{{([^{{}}]+)\}}",
        lambda m: _put_sub_sup("msup", m.group(1), m.group(2), "mn"),
        s,
    )
    s = re.sub(
        rf"([{_IDENT_CHARS}0-9])\s*\^\s*([A-Za-z0-9]+)",
        lambda m: _put_sub_sup("msup", m.group(1), m.group(2), "mn"),
        s,
    )

    parts = re.split(r"(\ue000MML\d+\ue001)", s)
    out: List[str] = []
    for p in parts:
        if p in sentinels:
            out.append(sentinels[p])
        else:
            out.append(_plain_chars_to_mml(p))
    return "".join(out)


def _plain_chars_to_mml(s: str) -> str:
    tokens = re.findall(rf"[{_IDENT_CHARS}_]+|\d+(?:\.\d+)?|[=+*/()\[\]≤≥≠≈∈⋅⋯×∞∇∂,-]", s)
    out: List[str] = []
    for tok in tokens:
        esc_tok = html.escape(tok, quote=True)
        if re.fullmatch(r"\d+(?:\.\d+)?", tok):
            out.append(f"<mn>{esc_tok}</mn>")
        elif re.fullmatch(rf"[{_IDENT_CHARS}_]+", tok):
            out.append(f"<mi>{esc_tok}</mi>")
        else:
            out.append(f"<mo>{esc_tok}</mo>")
    return "".join(out)


def _scan_non_python_buckets(repo: Path, start_idx: int = 1) -> List[Dict[str, Any]]:
    """Fallback/supplemental scanner for .js/.mjs/.ts/.R files when a repo contains non-Python modules."""
    skip = {".git", "__pycache__", "node_modules", ".venv", "venv", "dist", "build", ".anvil", ".ecgberht"}
    exts = {".js", ".mjs", ".ts", ".r"}
    files: List[Path] = []
    if repo.is_file() and not repo.is_symlink() and repo.suffix.lower() in exts:
        files = [repo]
    elif repo.is_dir():
        for root, dirs, fnames in os.walk(repo, followlinks=False):
            dirs[:] = [d for d in dirs if d not in skip and not d.startswith(".")]
            for f in sorted(fnames):
                fp = Path(root) / f
                if not fp.is_symlink() and fp.suffix.lower() in exts:
                    files.append(fp)
                    if len(files) >= 25:
                        break
            if len(files) >= 25:
                break

    buckets: List[Dict[str, Any]] = []
    fn_re = re.compile(
        r"^(?:\s*export\s+)?(?:\s*async\s+)?function\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)"
        r"|^\s*(?:const|let|var)\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(?:async\s*)?\(([^)]*)\)\s*=>"
        r"|^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*<-\s*function\s*\(([^)]*)\)"
    )
    for offset, fpath in enumerate(files):
        rel = fpath.name if repo.is_file() else fpath.relative_to(repo).as_posix()
        try:
            text = fpath.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        lines = text.splitlines()
        funcs: List[Dict[str, Any]] = []
        for lno, line in enumerate(lines, start=1):
            m = fn_re.search(line)
            if not m:
                continue
            name = m.group(1) or m.group(3) or m.group(5)
            raw_args = m.group(2) or m.group(4) or m.group(6) or ""
            args = [a.strip().split("=")[0].strip() for a in raw_args.split(",") if a.strip()][:5]
            end_lno = min(len(lines), lno + 25)
            snippet = "\n".join(lines[lno - 1:end_lno])
            stage = anvil_engine._classify_stage(name, "", snippet) if anvil_engine else "compute"
            ai_info = anvil_engine._detect_ai_interaction(name, "", snippet) if anvil_engine else None
            funcs.append({
                "name": name,
                "file": rel,
                "lineno": lno,
                "end_lineno": end_lno,
                "args": args,
                "summary": f"Executes {name}({', '.join(args)}) in {rel}.",
                "calls": [],
                "stage": stage,
                "ai_interaction": ai_info,
            })
        if not funcs:
            continue
        bid = f"block-{start_idx + offset}-{re.sub(r'[^a-z0-9]+', '-', Path(rel).stem.lower()).strip('-')}"
        stages = [fn["stage"] for fn in funcs]
        dominant = max(("ingest", "compute", "emit"), key=lambda s: stages.count(s))
        ai_seams = [fn["ai_interaction"] for fn in funcs if fn.get("ai_interaction")]
        buckets.append({
            "id": bid,
            "title": Path(rel).stem.replace("_", " ").replace("-", " ").title(),
            "file": rel,
            "summary": f"Module {rel} ({len(funcs)} functions)",
            "pipeline_stage": dominant,
            "ai_agent_touchpoints": ai_seams,
            "functions": funcs,
            "validated": False,
            "source_preview": "\n".join(lines[:75]),
            "total_lines": len(lines),
        })
    return buckets


def _build_inner_flow_diagram(block_title: str, steps: List[Dict[str, Any]], inner_edges: List[Dict[str, str]]) -> Dict[str, Any]:
    """Build a canonical FoundryFlowDiagram object for Mode 2 (Inner Process Map inside a single block)."""
    stage_col = {"ingest": 0, "compute": 1, "emit": 2}
    col_rows: Dict[int, List[int]] = {0: [], 1: [], 2: []}
    nodes_out: List[Dict[str, Any]] = []
    steps_out: List[Dict[str, Any]] = []

    for idx, st in enumerate(steps[:8]):
        stg = st.get("stage") or "compute"
        col = stage_col.get(stg, 1)
        row = len(col_rows[col])
        col_rows[col].append(row)
        has_ai = bool(st.get("ai_interaction"))
        shape = "model-call" if has_ai else ("human-gate" if st.get("is_entrypoint") else "program")
        fn_name = st["name"]
        short_fn = fn_name if len(fn_name) <= 24 else fn_name[:22] + "…"
        step_id = f"step-{idx + 1}-{re.sub(r'[^a-z0-9]+', '-', fn_name.lower()).strip('-')}"
        st["step_id"] = step_id
        steps_out.append({
            "id": step_id,
            "num": str(idx + 1),
            "title": f"{fn_name}({', '.join((st.get('args') or [])[:2])})",
            "shape": shape,
            "Summary": st.get("summary") or "",
            "reads": [st.get("file") or ""],
            "writes": [f"L{st.get('lineno', 1)}–{st.get('end_lineno', st.get('lineno', 1))} · {stg.upper()}"],
        })
        nodes_out.append({
            "id": step_id,
            "num": str(idx + 1),
            "label": short_fn,
            "caption": f"L{st.get('lineno', 1)} · {stg.upper()}",
            "shape": shape,
            "col": col,
            "row": row,
            "stage": stg,
        })

    bands_out = []
    for c, lbl, tone in (
        (0, "1. INGEST / ENTRYPOINTS", "ingest"),
        (1, "2. COMPUTE / CORE LOGIC", "compute"),
        (2, "3. EMIT / SERIALIZE", "emit"),
    ):
        rows = col_rows.get(c) or [0]
        bands_out.append({
            "index": c,
            "label": lbl,
            "tone": tone,
            "first_col": c,
            "last_col": c,
            "first_row": min(rows),
            "last_row": max(rows),
        })

    name_to_id = {st["name"]: st.get("step_id") for st in steps[:8] if st.get("step_id")}
    edges_out: List[Dict[str, str]] = []
    for e in inner_edges:
        fid = name_to_id.get(e["from"])
        tid = name_to_id.get(e["to"])
        if fid and tid and fid != tid:
            edges_out.append({"from": fid, "to": tid, "kind": "forward", "label": "calls"})
    if not edges_out and len(nodes_out) > 1:
        for i in range(len(nodes_out) - 1):
            edges_out.append({"from": nodes_out[i]["id"], "to": nodes_out[i + 1]["id"], "kind": "forward", "label": ""})

    return {
        "summary": f"Inner Function Flow Inside {block_title}",
        "steps": steps_out,
        "edges": edges_out,
        "diagram": {
            "col_width": 210,
            "row_height": 102,
            "node_width": 172,
            "node_height": 62,
            "bands": bands_out,
            "nodes": nodes_out,
        },
    }


def _enrich_buckets_with_previews(repo: Path, buckets: List[Dict[str, Any]]) -> None:
    base = repo.parent if repo.is_file() else repo
    for b in buckets:
        if not (b.get("source_preview") and b.get("total_lines")):
            rel = b.get("primary_file") or b.get("file") or ""
            fpath = (base / rel).resolve() if rel else None
            if fpath and fpath.is_file() and not fpath.is_symlink():
                try:
                    lines = fpath.read_text(encoding="utf-8", errors="replace").splitlines()
                    b["source_preview"] = "\n".join(lines[:80])
                    if not b.get("total_lines"):
                        b["total_lines"] = len(lines)
                except Exception:
                    b["source_preview"] = ""
        # Build inner_process_map for Mode 2 (Single-Block Drill-Down)
        funcs = b.get("functions") or []
        fn_by_short = {fn["name"].split(".")[-1]: fn["name"] for fn in funcs}
        inner_edges: List[Dict[str, str]] = []
        called_in_block: set[str] = set()
        for fn in funcs:
            for callee in fn.get("calls") or []:
                if callee in fn_by_short and fn_by_short[callee] != fn["name"]:
                    inner_edges.append({"from": fn["name"], "to": fn_by_short[callee]})
                    called_in_block.add(fn_by_short[callee])
        # Order inner steps: entrypoints (not called internally) first, then callees, preserving line order
        entrypoints = [fn for fn in funcs if fn["name"] not in called_in_block]
        internal_callees = [fn for fn in funcs if fn["name"] in called_in_block]
        ordered_fns = entrypoints + internal_callees
        steps_list = [
            {
                "step_num": idx + 1,
                "name": fn["name"],
                "file": fn.get("file") or b.get("primary_file") or b.get("file") or "",
                "lineno": fn.get("lineno", 1),
                "end_lineno": fn.get("end_lineno", fn.get("lineno", 1)),
                "stage": fn.get("stage", "compute"),
                "args": fn.get("args") or [],
                "summary": fn.get("summary") or "",
                "calls": fn.get("calls") or [],
                "ai_interaction": fn.get("ai_interaction"),
                "is_entrypoint": fn["name"] not in called_in_block,
            }
            for idx, fn in enumerate(ordered_fns[:12])
        ]
        b["inner_process_map"] = {
            "steps": steps_list,
            "edges": inner_edges,
            "flow_diagram": _build_inner_flow_diagram(b.get("title") or b["id"], steps_list, inner_edges),
        }


def _build_best_in_class_remap(
    sw_path: Path,
    cmp_path: Path,
    code_map: Dict[str, Any],
    orange_split: Dict[str, Any],
    remap: Dict[str, Any],
) -> Dict[str, Any]:
    """Synthesize the 3-column Old Monolithic Code -> New Best-in-Class Process Map -> Null Space model for Mode 3."""
    buckets = code_map.get("conceptual_buckets") or []
    module_buckets = code_map.get("module_buckets") or buckets
    pith_names = {p.get("name") for p in (orange_split.get("pith_and_seeds") or [])}
    juice_names = {j.get("name") for j in (orange_split.get("juice") or [])}
    target_stem = sw_path.stem if sw_path.is_file() else sw_path.name
    clean_stem = re.sub(r"[^a-z0-9_]+", "_", target_stem.lower()).strip("_") or "module"

    # Map each file to its parent Conceptual Architectural Bucket
    file_to_arch_bucket: Dict[str, Dict[str, Any]] = {}
    for ab in buckets:
        for mf in (ab.get("member_files") or [ab.get("file") or ""]):
            if mf:
                file_to_arch_bucket[mf] = ab

    # Build Old Monolithic Code cards from module_buckets (sorted by total_lines / function count so monoliths appear at top)
    old_monoliths: List[Dict[str, Any]] = []
    ingest_all: List[Dict[str, Any]] = []
    compute_all: List[Dict[str, Any]] = []
    emit_all: List[Dict[str, Any]] = []
    ai_all: List[Dict[str, Any]] = []

    sorted_modules = sorted(
        module_buckets,
        key=lambda b: (int(b.get("total_lines") or 0), len(b.get("functions") or [])),
        reverse=True,
    )

    for b in sorted_modules:
        funcs = b.get("functions") or []
        rel_file = b.get("file") or ""
        parent_arch = file_to_arch_bucket.get(rel_file) or (buckets[0] if buckets else b)
        b_ingest = [f for f in funcs if f["name"] not in pith_names and f.get("stage") == "ingest"]
        b_compute = [f for f in funcs if f["name"] not in pith_names and (f["name"] in juice_names or f.get("stage") == "compute")]
        b_emit = [f for f in funcs if f["name"] not in pith_names and f.get("stage") == "emit" and f["name"] not in juice_names]
        b_null = [f for f in funcs if f["name"] in pith_names]
        b_ai = [f for f in funcs if f.get("ai_interaction")]

        for f in b_ingest:
            ingest_all.append({**f, "source_block_id": parent_arch["id"], "source_file": rel_file})
        for f in b_compute:
            compute_all.append({**f, "source_block_id": parent_arch["id"], "source_file": rel_file})
        for f in b_emit:
            emit_all.append({**f, "source_block_id": parent_arch["id"], "source_file": rel_file})
        for f in b_ai:
            ai_all.append({**f, "source_block_id": parent_arch["id"], "source_file": rel_file})

        mapped_targets: List[Dict[str, str]] = []
        if b_ingest:
            mapped_targets.append({
                "target_id": "new-block-ingest",
                "label": f"Mapped to New Block 1: Get-Data ({len(b_ingest)} fn)",
                "kind": "mapped",
            })
        if b_compute:
            mapped_targets.append({
                "target_id": "new-block-compute",
                "label": f"Mapped to New Block 2: Do-Analysis · Essential Core ({len(b_compute)} fn)",
                "kind": "mapped",
            })
        if b_emit:
            mapped_targets.append({
                "target_id": "new-block-emit",
                "label": f"Mapped to New Block 3: Create-Output ({len(b_emit)} fn)",
                "kind": "mapped",
            })
        if b_null:
            mapped_targets.append({
                "target_id": "null-space",
                "label": f"Sent to ∅ Null Space ({len(b_null)} fn: {', '.join(f['name'] for f in b_null[:3])})",
                "kind": "null",
            })

        mixed_stages = sum(1 for grp in (b_ingest, b_compute, b_emit) if grp) > 1
        old_monoliths.append({
            "block_id": parent_arch["id"],
            "module_block_id": b["id"],
            "arch_bucket_title": parent_arch.get("title") or parent_arch["id"],
            "title": b.get("title") or b["id"],
            "file": rel_file,
            "total_lines": b.get("total_lines") or 0,
            "function_count": len(funcs),
            "mixed_concerns": mixed_stages,
            "summary": b.get("summary") or "",
            "counts": {
                "ingest": len(b_ingest),
                "compute": len(b_compute),
                "emit": len(b_emit),
                "null_space": len(b_null),
            },
            "sample_functions": [f["name"] for f in funcs[:6]],
            "mapped_targets": mapped_targets,
        })

    # Detect any existing extracted *_core.py blocks in module_buckets so we can link directly to them
    stem_prefix = clean_stem.split("_")[0]
    core_mod = (
        next((m for m in module_buckets if Path(m.get("file") or "").name.lower() == f"{clean_stem}_core.py"), None)
        or next((m for m in module_buckets if stem_prefix and Path(m.get("file") or "").name.lower() == f"{stem_prefix}_core.py"), None)
        or next((m for m in module_buckets if (m.get("file") or "").lower().endswith("_core.py")), None)
        or next((m for m in module_buckets if "core" in (m.get("file") or "").lower()), None)
    )
    core_arch_bucket = (
        file_to_arch_bucket.get(core_mod["file"])
        if core_mod and core_mod.get("file") in file_to_arch_bucket
        else next((b for b in buckets if b.get("pipeline_stage") == "compute"), buckets[0] if buckets else None)
    )
    ingest_bucket = next((b for b in buckets if b.get("pipeline_stage") == "ingest"), buckets[0] if buckets else None)
    emit_bucket = next((b for b in buckets if b.get("pipeline_stage") == "emit"), buckets[-1] if buckets else None)

    core_file_name = Path(core_mod["file"]).name if core_mod else f"{clean_stem}_core.py"

    new_blocks: List[Dict[str, Any]] = [
        {
            "id": "new-block-ingest",
            "drill_block_id": ingest_bucket["id"] if ingest_bucket else "",
            "stage": "ingest",
            "stage_badge": "STAGE 1 · GET-DATA (INGEST)",
            "title": f"New Block 1 — {clean_stem}_ingest.py (Data & State Readers)",
            "file": f"{clean_stem}_ingest.py",
            "summary": (
                f"Consolidates {len(ingest_all)} Peel (Get-Data) functions across {len(old_monoliths)} modules into "
                "side-effect-isolated file/JSON/request readers with explicit schema validation."
            ),
            "function_count": len(ingest_all),
            "functions": [
                {
                    "name": f["name"],
                    "old_file": f["source_file"],
                    "lineno": f.get("lineno", 1),
                    "summary": f.get("summary", ""),
                    "stage": "ingest",
                }
                for f in ingest_all[:40]
            ],
            "ai_hook": None,
        },
        {
            "id": "new-block-compute",
            "drill_block_id": (core_arch_bucket or (buckets[0] if buckets else {})).get("id", ""),
            "stage": "compute",
            "stage_badge": "STAGE 2 · DO-ANALYSIS (ESSENTIAL CORE / JUICE)",
            "title": f"New Block 2 — {core_file_name} (Pure Essential Core · Differential Equivalence Gate)",
            "file": core_file_name,
            "summary": (
                f"Isolates {len(compute_all)} Essential Core (Juice) domain & analysis functions with zero "
                "disk/network/UI side effects so differential equivalence checks can run deterministically."
            ),
            "function_count": len(compute_all),
            "functions": [
                {
                    "name": f["name"],
                    "old_file": f["source_file"],
                    "lineno": f.get("lineno", 1),
                    "summary": f.get("summary", ""),
                    "stage": "compute",
                }
                for f in compute_all[:50]
            ],
            "ai_hook": (
                f"🤖 {len(ai_all)} AI Agent Seam(s) isolated behind typed dispatch/verdict contracts"
                if ai_all else None
            ),
        },
        {
            "id": "new-block-emit",
            "drill_block_id": emit_bucket["id"] if emit_bucket else "",
            "stage": "emit",
            "stage_badge": "STAGE 3 · CREATE-OUTPUT (EMIT & SERIALIZATION)",
            "title": f"New Block 3 — {clean_stem}_emit.py (Output & Route Renderers)",
            "file": f"{clean_stem}_emit.py",
            "summary": (
                f"Consolidates {len(emit_all)} Peel (Create-Output) formatters, HTML/JSON serializers, and "
                "atomic file writers that consume pure Essential Core dicts."
            ),
            "function_count": len(emit_all),
            "functions": [
                {
                    "name": f["name"],
                    "old_file": f["source_file"],
                    "lineno": f.get("lineno", 1),
                    "summary": f.get("summary", ""),
                    "stage": "emit",
                }
                for f in emit_all[:40]
            ],
            "ai_hook": None,
        },
    ]

    # Build Architectural Bucket Old -> New Best-in-Class Map cards + FoundryFlowDiagram for Mode 3
    architecture_blocks: List[Dict[str, Any]] = []
    for idx, ab in enumerate(buckets):
        ab_funcs = ab.get("functions") or []
        ab_ing = sum(1 for f in ab_funcs if f["name"] not in pith_names and f.get("stage") == "ingest")
        ab_cmp = sum(1 for f in ab_funcs if f["name"] not in pith_names and (f["name"] in juice_names or f.get("stage") == "compute"))
        ab_emt = sum(1 for f in ab_funcs if f["name"] not in pith_names and f.get("stage") == "emit" and f["name"] not in juice_names)
        ab_nul = sum(1 for f in ab_funcs if f["name"] in pith_names)
        architecture_blocks.append({
            "id": ab["id"],
            "num": idx + 1,
            "title": ab.get("title") or ab["id"],
            "member_files": ab.get("member_files") or [ab.get("file") or ""],
            "stage": ab.get("pipeline_stage") or "compute",
            "summary": ab.get("summary") or "",
            "counts": {"ingest": ab_ing, "compute": ab_cmp, "emit": ab_emt, "null_space": ab_nul},
        })

    ns_count = len((remap.get("null_space") or {}).get("items") or [])
    remap_flow_diagram = {
        "summary": "Old Monolithic Code → Best-in-Class 3-Stage Architecture (Get-Data → Essential Core → Create-Output) + Explicit ∅ Null Space Gate",
        "steps": [
            {
                "id": "old-monoliths",
                "num": "OLD",
                "title": f"Old Monolithic Modules ({len(old_monoliths)} files)",
                "shape": "program",
                "Summary": f"{sum(1 for m in old_monoliths if m['mixed_concerns'])} mixed-stage modules decomposed via CST/AST.",
                "reads": [m["file"] for m in old_monoliths[:4]],
                "writes": ["AST & CST Decomposition"],
            },
            {
                "id": "new-block-ingest",
                "num": "1",
                "title": f"Stage 1 · Get-Data Ingest ({len(ingest_all)} fn)",
                "shape": "program",
                "Summary": new_blocks[0]["summary"],
                "reads": ["HTTP / JSON / Cockpit Files"],
                "writes": ["Validated Input Dicts"],
            },
            {
                "id": "new-block-compute",
                "num": "2",
                "title": f"Stage 2 · Essential Core ({len(compute_all)} fn)",
                "shape": "model-call",
                "Summary": new_blocks[1]["summary"],
                "reads": ["Validated Input Dicts"],
                "writes": ["Pure Domain Decisions & Typed Contracts"],
            },
            {
                "id": "new-block-emit",
                "num": "3",
                "title": f"Stage 3 · Create-Output ({len(emit_all)} fn)",
                "shape": "program",
                "Summary": new_blocks[2]["summary"],
                "reads": ["Pure Domain Decisions"],
                "writes": ["HTML / JSON / Atomic Disk Writes"],
            },
            {
                "id": "null-space-gate",
                "num": "∅",
                "title": f"∅ Null Space Ledger ({ns_count} fn)",
                "shape": "human-gate",
                "Summary": "Explicit human sign-off required for every retired legacy/unreferenced function.",
                "reads": ["Pith & Seeds Candidates"],
                "writes": ["Signed-Off Null Space Receipt"],
            },
        ],
        "edges": [
            {"from": "old-monoliths", "to": "new-block-ingest", "kind": "forward", "label": f"{len(ingest_all)} Peel fn"},
            {"from": "new-block-ingest", "to": "new-block-compute", "kind": "forward", "label": "pure dicts"},
            {"from": "new-block-compute", "to": "new-block-emit", "kind": "forward", "label": f"{len(compute_all)} Core fn"},
            {"from": "old-monoliths", "to": "null-space-gate", "kind": "loop", "label": f"{ns_count} ∅ drops"},
        ],
        "diagram": {
            "col_width": 215,
            "row_height": 108,
            "node_width": 176,
            "node_height": 64,
            "bands": [
                {"index": 0, "label": "OLD MONOLITHIC CODE", "tone": "ingest", "first_col": 0, "last_col": 0, "first_row": 0, "last_row": 1},
                {"index": 1, "label": "STAGE 1 · GET-DATA", "tone": "ingest", "first_col": 1, "last_col": 1, "first_row": 0, "last_row": 1},
                {"index": 2, "label": "STAGE 2 · ESSENTIAL CORE", "tone": "compute", "first_col": 2, "last_col": 2, "first_row": 0, "last_row": 0},
                {"index": 3, "label": "STAGE 3 · CREATE-OUTPUT", "tone": "emit", "first_col": 3, "last_col": 3, "first_row": 0, "last_row": 0},
            ],
            "nodes": [
                {"id": "old-monoliths", "num": "OLD", "label": f"Old Monoliths ({len(old_monoliths)})", "caption": f"{sum(1 for m in old_monoliths if m['mixed_concerns'])} mixed files", "shape": "program", "col": 0, "row": 0, "stage": "ingest"},
                {"id": "new-block-ingest", "num": "1", "label": "Stage 1 · Get-Data", "caption": f"{len(ingest_all)} fn · INGEST", "shape": "program", "col": 1, "row": 0, "stage": "ingest"},
                {"id": "new-block-compute", "num": "2", "label": f"Stage 2 · {core_file_name}", "caption": f"{len(compute_all)} fn · CORE JUICE", "shape": "model-call", "col": 2, "row": 0, "stage": "compute"},
                {"id": "new-block-emit", "num": "3", "label": "Stage 3 · Create-Output", "caption": f"{len(emit_all)} fn · EMIT", "shape": "program", "col": 3, "row": 0, "stage": "emit"},
                {"id": "null-space-gate", "num": "∅", "label": "∅ Null Space Gate", "caption": f"{ns_count} fn · Sign-Off", "shape": "human-gate", "col": 1, "row": 1, "stage": "ingest"},
            ],
        },
    }

    return {
        "old_monoliths": old_monoliths,
        "new_blocks": new_blocks,
        "architecture_blocks": architecture_blocks,
        "flow_diagram": remap_flow_diagram,
        "totals": {
            "old_modules": len(old_monoliths),
            "mixed_modules": sum(1 for m in old_monoliths if m["mixed_concerns"]),
            "ingest_fns": len(ingest_all),
            "compute_fns": len(compute_all),
            "emit_fns": len(emit_all),
            "null_space_fns": ns_count,
        },
    }


def extract_paper_claims_and_align(
    repo: Path,
    buckets: List[Dict[str, Any]],
    paper_info: Dict[str, Any],
    code_map: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Extract sections, algorithms, and MathML equations from a paper and align to companion software."""
    text = str(paper_info.get("text") or "")
    paper_title = str(paper_info.get("title") or "Paper")
    paper_path_str = str(paper_info.get("path") or "").strip()

    # Check if paper_info is an explicit inline JSON {"claims": [...]} spec
    is_inline_json_claims = False
    raw_claims: List[Dict[str, str]] = []
    try:
        parsed = json.loads(text)
        if isinstance(parsed, dict) and isinstance(parsed.get("claims"), list):
            is_inline_json_claims = True
            for idx, item in enumerate(parsed["claims"]):
                raw_claims.append({
                    "id": str(item.get("id") or f"eq-{idx + 1}"),
                    "title": str(item.get("title") or f"Claim {idx + 1}"),
                    "expr": str(item.get("latex") or item.get("equation") or ""),
                    "context": str(item.get("description") or item.get("title") or ""),
                })
    except Exception:
        is_inline_json_claims = False

    compact_paper_info: Dict[str, Any] = {
        "path": paper_path_str,
        "source_type": paper_info.get("source_type", "local"),
        "title": paper_title,
        "url": paper_info.get("url", ""),
    }
    if paper_info.get("bundle_dir"):
        compact_paper_info["bundle_dir"] = paper_info["bundle_dir"]
    if paper_info.get("primary_tex"):
        compact_paper_info["primary_tex"] = paper_info["primary_tex"]

    # Delegate directly to anvil_engine.paper_to_code_map for rich sections[], algorithms[], and equations[]
    if not is_inline_json_claims and anvil_engine is not None and hasattr(anvil_engine, "paper_to_code_map") and paper_path_str:
        p_path = Path(paper_path_str)
        if p_path.exists():
            pmap = anvil_engine.paper_to_code_map(repo, p_path, code_map=code_map)
            pmap["paper_source_type"] = paper_info.get("source_type", pmap.get("paper_source_type", "local"))
            pmap["paper_url"] = paper_info.get("url", pmap.get("paper_url", ""))
            pmap["source_path"] = paper_path_str
            pmap["paper_info"] = compact_paper_info
            if paper_info.get("bundle_dir"):
                pmap["bundle_dir"] = paper_info["bundle_dir"]
            if paper_title and (not pmap.get("paper_title") or pmap.get("paper_title") == p_path.stem):
                pmap["paper_title"] = paper_title
            return pmap

    # Fallback for inline JSON claim specs or when anvil_engine is unavailable
    if not raw_claims:
        eq_blocks = re.findall(
            r"(?:\$\$(.+?)\$\$|\\begin\{equation\*?\}(.+?)\\end\{equation\*?\})",
            text,
            flags=re.S,
        )
        lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
        for idx, (m1, m2) in enumerate(eq_blocks[:10]):
            eq_str = " ".join((m1 or m2).split())
            raw_claims.append({
                "id": f"eq-{idx + 1}",
                "title": f"Equation {idx + 1} ({paper_title[:45]})",
                "expr": eq_str,
                "context": " ".join(lines[:12]),
            })

    all_funcs: List[Dict[str, Any]] = []
    for b in buckets:
        for fn in b.get("functions", []):
            all_funcs.append({
                **fn,
                "bucket_id": b["id"],
                "bucket_title": b["title"],
                "bucket_validated": bool(b.get("validated")),
            })

    def _toks(s: str) -> set[str]:
        return {t for t in re.split(r"[^a-z0-9]+", s.lower()) if len(t) >= 3}

    mml_fn = getattr(anvil_engine, "latex_to_mathml", None) if anvil_engine is not None else None
    alignments: List[Dict[str, Any]] = []
    for c in raw_claims[:12]:
        claim_tokens = _toks(f"{c['title']} {c['context']} {c['expr']}")
        best_fn: Optional[Dict[str, Any]] = None
        best_score = 0.0
        best_overlap: List[str] = []
        for fn in all_funcs:
            fn_tokens = _toks(f"{fn['name']} {' '.join(fn.get('args', []))} {fn.get('summary', '')} {fn.get('file', '')}")
            common = sorted(claim_tokens & fn_tokens)
            if not common:
                continue
            score = len(common) * 2.0 + (1.0 if fn.get("stage") == "compute" else 0.0)
            if score > best_score:
                best_score = score
                best_fn = fn
                best_overlap = common[:5]

        mml = (mml_fn(c["expr"]) if mml_fn else latex_to_mathml(c["expr"])) if c.get("expr") else ""
        if best_fn is not None:
            status = "EXECUTED_PASS" if best_fn.get("bucket_validated") else "STATIC_ALIGNED"
            rationale = f"Matched on shared domain terms ({', '.join(best_overlap)}) in {best_fn['stage'].upper()} stage"
        else:
            status = "PAPER_ONLY_UNIMPLEMENTED"
            rationale = "No function shared domain terms with this claim"

        alignments.append({
            "claim_id": c["id"],
            "title": c["title"],
            "mathml": mml,
            "mapped_function": best_fn["name"] if best_fn else None,
            "mapped_file": best_fn["file"] if best_fn else None,
            "lineno": best_fn["lineno"] if best_fn else None,
            "bucket_id": best_fn.get("bucket_id") if best_fn else None,
            "match_rationale": rationale,
            "empirical_status": status,
        })

    return {
        "schema": "anvil-paper-map/v1",
        "has_paper": True,
        "paper_title": paper_title,
        "paper_source_type": paper_info.get("source_type", "local"),
        "paper_url": paper_info.get("url", ""),
        "paper_path": paper_path_str,
        "source_path": paper_path_str,
        "paper_info": compact_paper_info,
        "repo": str(repo),
        "claims_mapped": len(alignments),
        "native_mathml_enforced": True,
        "sections": [],
        "algorithms": [],
        "equations": [],
        "alignments": alignments,
    }


def _build_anvil_v2_report_section(session: Dict[str, Any], heading_prefix: str = "## 5.") -> List[str]:
    buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
    panel = session.get("beta_reader_panel") or {}
    wt = session.get("walkthrough_trace") or {}
    lines: List[str] = [
        "",
        f"{heading_prefix} Anvil v2 — 3-Level Progressive Abstraction, 5-Seat Software Beta-Reader Panel & Live Code Walkthrough",
        "",
        "### A. 3-Level Progressive Abstraction Map (Level 1 Summary → Level 2 Mechanics/MathML/Diff → Level 3 Code)",
        "",
        "| Block | Level 1 (Role & I/O) | Level 2 (Sub-Blocks · Formulas · Assumptions) | Level 3 (Exact Lines & Functions) |",
        "|---|---|---|---|",
    ]
    for b in buckets[:20]:
        l1 = b.get("level1_summary") or {}
        l2 = b.get("level2_mechanics") or {}
        l3 = b.get("level3_code") or {}
        sub_cnt = len(l2.get("sub_blocks") or [])
        eq_cnt = len(l2.get("formulas_mathml") or [])
        as_cnt = len(l2.get("assumptions") or [])
        lines.append(
            f"| **`{b.get('title')}`** (`{b.get('file')}`) | {l1.get('role') or b.get('summary') or ''} "
            f"| `{sub_cnt}` sub-blocks · `{eq_cnt}` MathML formula(s) · `{as_cnt}` explicit assumption(s) "
            f"| `{l3.get('file') or b.get('file')}` (`L{l3.get('start_line', 1)}–L{l3.get('end_line', 1)}` · `{len(b.get('functions') or [])}` fn) |"
        )

    seats = panel.get("seats") or []
    if seats:
        lines.extend([
            "",
            f"### B. 5-Seat Software Beta-Reader Panel (Verdict: `{panel.get('overall_status') or panel.get('overall_verdict') or 'PASS'}` · Score: `{panel.get('overall_score', 90)}/100`)",
            "",
            "| Seat | Specialist Role | Focus | Status | Score | Summary & Actionable Fix |",
            "|---|---|---|---|---|---|",
        ])
        for idx, s in enumerate(seats, 1):
            role_txt = s.get("title") or s.get("persona_name") or s.get("role") or f"Seat {idx}"
            focus_txt = s.get("focus") or s.get("lens") or ""
            status_txt = s.get("status") or s.get("verdict") or "PASS"
            score_txt = f"{s.get('score', 90)}/100"
            sum_txt = s.get("summary") or f"{s.get('key_finding', '')} Fix: {s.get('actionable_fix', '')}".strip()
            lines.append(
                f"| **Seat {idx}** | **{role_txt}** | {focus_txt} | `{status_txt}` | `{score_txt}` | {sum_txt} |"
            )

    steps = wt.get("steps") or []
    if steps:
        acc_cnt = (wt.get("counts") or {}).get("accurate", wt.get("accurate_steps", 0))
        tot_cnt = wt.get("total_steps", wt.get("step_count", len(steps)))
        lines.extend([
            "",
            f"### C. Live Code Walkthrough Trace (`{wt.get('language', 'python').upper()}` · `{acc_cnt}/{tot_cnt}` Steps Executed · Verdict: `{wt.get('overall_verdict', 'STATIC_ONLY')}`)",
            "",
            "| Step | Function | What Code Claims To Do | Concrete Input Data | Actual Runtime Calculation & Output | Accuracy Verdict |",
            "|---|---|---|---|---|---|",
        ])
        for st in steps[:20]:
            step_idx = st.get("step") or st.get("step_index") or 1
            fn_nm = st.get("function") or st.get("function_name") or "entrypoint"
            raw_inp = st.get("concrete_input") if st.get("concrete_input") is not None else st.get("input_snapshot", "")
            inp_s = (raw_inp if isinstance(raw_inp, str) else json.dumps(raw_inp, ensure_ascii=False))[:90]
            out_s = str(st.get("actual_output_summary") or st.get("actual_behavior") or "")[:120]
            note_s = str(st.get("calculation_note") or st.get("discrepancy_notes") or "")[:110]
            claim_s = str(st.get("claim") or st.get("claimed_behavior") or "").replace("|", "\\|")[:100]
            lines.append(
                f"| **{step_idx}/{st.get('total_steps', len(steps))}** | `{fn_nm}` (`{st.get('file')}:L{st.get('lineno', 1)}`) "
                f"| {claim_s} | `{inp_s}` | {out_s} ({note_s}) | **`{st.get('verdict', 'STATIC_ONLY')}`** |"
            )
    return lines


def _write_anvil_manifest(cdir: Path, session: Dict[str, Any]) -> Path:
    manifest_path = _session_dir(cdir) / "manifest.json"
    code_map = session.get("code_map") or {}
    buckets = code_map.get("conceptual_buckets") or []
    orange = session.get("orange_split") or {}
    raw_remap = session.get("remap")
    remap = raw_remap if isinstance(raw_remap, dict) else {}
    has_remap = bool(isinstance(raw_remap, dict) and raw_remap)
    paper = session.get("paper_map") if isinstance(session.get("paper_map"), dict) else None
    panel = session.get("beta_reader_panel") if isinstance(session.get("beta_reader_panel"), dict) else {}
    wt = session.get("walkthrough_trace") if isinstance(session.get("walkthrough_trace"), dict) else {}
    buckets_index = [
        {
            "id": b.get("id"),
            "title": b.get("title"),
            "primary_file": b.get("primary_file") or b.get("file"),
            "pipeline_stage": b.get("pipeline_stage") or "compute",
            "function_count": len(b.get("functions") or b.get("function_refs") or []),
        }
        for b in buckets
        if isinstance(b, dict)
    ]
    remap_summary = {
        "verdict": remap.get("verdict") if has_remap and remap.get("verdict") else "NOT_RUN",
        "null_space_count": ((remap.get("null_space") or {}).get("count", 0)),
        "unexplained_blockers": ((remap.get("null_space") or {}).get("unexplained_blockers", 0)),
    }
    paper_summary = (
        {
            "has_paper": bool(paper.get("has_paper", False)),
            "paper_title": paper.get("paper_title", ""),
            "summary_counts": paper.get("summary_counts") or {},
            "divergence_count": len(paper.get("divergences") or []),
        }
        if paper is not None
        else None
    )
    manifest = {
        "schema": "anvil-manifest/v3",
        "cockpit_dir": str(cdir),
        "cockpit_name": session.get("cockpit_name") or cdir.name,
        "updated_at": session.get("updated_at"),
        "software": session.get("software"),
        "conceptual_buckets_index": buckets_index,
        "process_edges_count": len(((code_map.get("process_map") or {}).get("edges")) or []),
        "orange_counts": orange.get("counts") or {},
        "orange_split": {"counts": orange.get("counts") or {}},
        "remap_summary": remap_summary,
        "remap": remap_summary,
        "paper_summary": paper_summary,
        "paper_map": paper_summary,
        "beta_reader_score": panel.get("overall_score"),
        "beta_reader_panel": {
            "overall_score": panel.get("overall_score"),
            "overall_status": panel.get("overall_status") or panel.get("overall_verdict"),
        },
        "walkthrough_verdict": wt.get("overall_verdict"),
        "walkthrough_trace": {
            "overall_verdict": wt.get("overall_verdict"),
        },
    }
    _atomic_write_text(manifest_path, json.dumps(manifest, ensure_ascii=False, separators=(",", ":")))
    return manifest_path


def _write_anvil_report(cdir: Path, session: Dict[str, Any]) -> Path:
    report_path = cdir / "ANVIL-REPORT.md"
    if report_path.is_file():
        try:
            existing_text = report_path.read_text(encoding="utf-8", errors="replace")
            if "<!-- ANVIL_CUSTOM_REPORT_LOCKED -->" in existing_text:
                return report_path
        except Exception:
            pass

    sw = session.get("software") or {}
    orange = session.get("orange_split") or {}
    counts = orange.get("counts") or {}
    remap = session.get("remap") or {}
    paper = session.get("paper_map")
    buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []

    lines = [
        f"# Anvil Session Report — {session.get('cockpit_name') or cdir.name}",
        "",
        f"- **Updated:** `{session.get('updated_at')}`",
        f"- **Session Mode:** `{session.get('mode', 'code').upper()}`",
        f"- **Software Target:** `{sw.get('label') or sw.get('path') or '.'}` (`{sw.get('source_type', 'local')}`)",
    ]
    if paper:
        lines.append(f"- **Paper Target:** `{paper.get('paper_title')}` ({paper.get('claims_mapped', 0)} claims analyzed)")
    lines.extend([
        "",
        "## 1. Parable of the Oranges — Essential Core vs. Scaffolding",
        f"- **Essential Domain Logic (Juice / Do-Analysis):** {counts.get('juice_count', 0)} functions",
        f"- **Surface I/O Contracts (Peel / Get-Data & Create-Output):** {counts.get('peel_count', 0)} functions",
        f"- **Legacy Scaffolding / Null Space Candidates (Pith & Seeds):** {counts.get('pith_and_seeds_count', 0)} functions",
        f"- **One-Trip Recommendation:** {(orange.get('proactive_staff_work') or {}).get('one_trip_recommendation', '')}",
        "",
        "## 2. Conceptual & Process Map Blocks",
    ])
    for b in buckets[:20]:
        vmark = "✓ VALIDATED" if b.get("validated") else "○ Pending Probe"
        lines.append(
            f"- **`{b.get('title')}`** (`{b.get('file')}`) · Stage: `{b.get('pipeline_stage', 'compute').upper()}` · "
            f"{len(b.get('functions') or [])} functions · {vmark} — {b.get('validated_description') or b.get('summary')}"
        )

    if remap:
        ns = remap.get("null_space") or {}
        lines.extend([
            "",
            "## 3. Old → New Code Map & Explicit Null Space",
            f"- **Remap Verdict:** `{remap.get('verdict', 'PASS')}`",
            f"- **Mapped Functions:** {len(remap.get('old_to_new_mappings') or [])}",
            f"- **Null Space Items:** {ns.get('count', 0)} ({ns.get('unexplained_blockers', 0)} unexplained blockers)",
        ])

    if paper and paper.get("alignments"):
        lines.extend([
            "",
            "## 4. Paper ↔ Code Alignments (Native MathML)",
        ])
        for al in paper["alignments"]:
            lines.append(
                f"- **{al.get('claim_id')} — {al.get('title')}** → `{al.get('mapped_function') or 'unmapped'}` "
                f"(`{al.get('mapped_file') or ''}:{al.get('lineno') or ''}`) [{al.get('empirical_status')}]"
            )

    lines.extend(_build_anvil_v2_report_section(session, heading_prefix="## 5."))
    _atomic_write_text(report_path, "\n".join(lines) + "\n")
    return report_path


def _project_session_summary(session: Dict[str, Any]) -> Dict[str, Any]:
    """Build a compact (<15 KB) status projection of an active Anvil session for `?summary=1`."""
    code_map = session.get("code_map") or {}
    buckets = code_map.get("conceptual_buckets") or []
    compact_buckets: List[Dict[str, Any]] = []
    for b in buckets[:10]:
        l1 = b.get("level1_summary") or {}
        mfiles = list(b.get("member_files") or [])
        compact_buckets.append({
            "id": b.get("id"),
            "title": b.get("title"),
            "file": b.get("file"),
            "primary_file": b.get("primary_file") or b.get("file"),
            "pipeline_stage": b.get("pipeline_stage", "compute"),
            "validated": bool(b.get("validated")),
            "static_syntax_ok": bool(b.get("static_syntax_ok")),
            "function_count": len(b.get("functions") or []),
            "member_file_count": len(mfiles) or 1,
            "member_files": mfiles[:8],
            "summary": str(b.get("summary") or "")[:160],
            "level1_summary": {
                "role": str(l1.get("role") or l1.get("purpose") or "")[:140],
                "pure_core_pct": l1.get("pure_core_pct", 0),
            },
        })
    paper = session.get("paper_map")
    compact_paper = None
    if isinstance(paper, dict):
        compact_paper = {
            "schema": paper.get("schema", "anvil-paper-map/v1"),
            "paper_title": str(paper.get("paper_title") or "")[:120],
            "paper_source_type": paper.get("paper_source_type"),
            "paper_url": paper.get("paper_url", ""),
            "claims_mapped": paper.get("claims_mapped", 0),
            "summary_counts": paper.get("summary_counts") or {
                "sections": len(paper.get("sections") or []),
                "algorithms": len(paper.get("algorithms") or []),
                "equations": len(paper.get("equations") or []),
            },
        }
    panel = session.get("beta_reader_panel") or {}
    wt = session.get("walkthrough_trace") or {}
    remap = session.get("remap") or {}
    ns = remap.get("null_space") or {}
    return {
        "schema": session.get("schema", "anvil-cockpit-session/v1"),
        "summary_only": True,
        "active": bool(session.get("active")),
        "cockpit_dir": session.get("cockpit_dir"),
        "cockpit_name": session.get("cockpit_name"),
        "mode": session.get("mode", "code"),
        "created_at": session.get("created_at"),
        "updated_at": session.get("updated_at"),
        "software": session.get("software"),
        "compare_software": session.get("compare_software"),
        "selected_block_id": session.get("selected_block_id", ""),
        "signed_off_drops": list(session.get("signed_off_drops") or [])[:25],
        "code_map": {
            "schema": code_map.get("schema", "anvil-map/v1"),
            "total_files": code_map.get("total_files", len(code_map.get("module_buckets") or buckets)),
            "total_functions": code_map.get("total_functions", sum(len(b.get("functions") or []) for b in buckets)),
            "languages": code_map.get("languages") or {},
            "conceptual_buckets": compact_buckets,
            "process_map_counts": {
                "nodes": len((code_map.get("process_map") or {}).get("nodes") or []),
                "edges": len((code_map.get("process_map") or {}).get("edges") or []),
            },
        },
        "orange_split": {
            "counts": (session.get("orange_split") or {}).get("counts") or {},
        },
        "remap": {
            "verdict": remap.get("verdict", "PASS"),
            "null_space": {
                "count": ns.get("count", 0),
                "unexplained_blockers": ns.get("unexplained_blockers", 0),
            },
        },
        "paper_map": compact_paper,
        "beta_reader_panel": {
            "overall_status": panel.get("overall_status") or panel.get("overall_verdict") or "PASS",
            "overall_score": panel.get("overall_score", 0),
            "seats": [
                {
                    "seat_id": s.get("seat_id"),
                    "title": s.get("title") or s.get("persona_name"),
                    "status": s.get("status") or s.get("verdict"),
                    "score": s.get("score"),
                }
                for s in (panel.get("seats") or [])[:5]
            ],
        },
        "walkthrough_trace": {
            "overall_verdict": wt.get("overall_verdict", "STATIC_ONLY"),
            "total_steps": wt.get("total_steps", len(wt.get("steps") or [])),
            "counts": wt.get("counts") or {},
        },
        "chat_history": [
            {
                "role": m.get("role"),
                "mode": m.get("mode"),
                "target": m.get("target"),
                "text": str(m.get("text") or "")[:240],
                "answer_mode": m.get("answer_mode", "static_ast"),
                "at": m.get("at"),
            }
            for m in (session.get("chat_history") or [])[-5:]
        ],
    }


class AnvilSourceRefusalError(ValueError):
    """Typed refusal for `get_cockpit_file_source` carrying exact HTTP status and structured payload."""

    def __init__(self, message: str, *, http_status: int, payload: Dict[str, Any]) -> None:
        super().__init__(message)
        self.http_status = int(http_status)
        self.payload = dict(payload)


def get_cockpit_file_source(cockpit_dir: str | Path, rel_file: str) -> Dict[str, Any]:
    """Serve on-demand Level-3 numbered source, symbol table, and callers/callees for one file inside the session software root."""
    raw = (rel_file or "").strip()
    if not raw:
        msg = "Query parameter 'file' is required."
        raise AnvilSourceRefusalError(
            msg,
            http_status=400,
            payload={"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": msg, "message": msg},
        )
    if raw.startswith(("/", "\\")) or re.match(r"^[A-Za-z]:", raw):
        msg = "Absolute, UNC, or drive-prefixed file paths are not permitted."
        raise AnvilSourceRefusalError(
            msg,
            http_status=403,
            payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
        )
    parts = [p for p in re.split(r"[\\/]+", raw) if p]
    if not parts:
        msg = "Invalid file path."
        raise AnvilSourceRefusalError(
            msg,
            http_status=400,
            payload={"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": msg, "message": msg},
        )
    for part in parts:
        low = part.lower()
        if part == "..":
            msg = "Parent directory traversal ('..') is not permitted."
            raise AnvilSourceRefusalError(
                msg,
                http_status=403,
                payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
            )
        if low in FORBIDDEN_DOT_PARTS or low in FORBIDDEN_SECRET_NAMES or (part.startswith(".") and part != "."):
            msg = f"Access to restricted path component '{part}' is not permitted."
            raise AnvilSourceRefusalError(
                msg,
                http_status=403,
                payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
            )

    cdir = Path(cockpit_dir).resolve()
    sfile = _session_file(cdir)
    session: Optional[Dict[str, Any]] = None
    if sfile.exists():
        if sfile.is_symlink() or not sfile.is_file():
            msg_nf = "Backing store .anvil/session.json is not a regular file."
            raise AnvilSourceRefusalError(
                msg_nf,
                http_status=500,
                payload={
                    "ok": False,
                    "error_code": "BACKING_STORE_UNREADABLE",
                    "status_kind": "backing-store-unreadable",
                    "http_status": 500,
                    "badge": "UNKNOWN",
                    "message": msg_nf,
                    "error": msg_nf,
                    "unknown_state": True,
                },
            )
        try:
            loaded = _read_session_ir(sfile)
            if isinstance(loaded, dict) and loaded.get("active"):
                session = loaded
        except Exception as exc:
            msg_u = f"Backing store .anvil/session.json is corrupt or unreadable: {exc}"
            raise AnvilSourceRefusalError(
                msg_u,
                http_status=500,
                payload={
                    "ok": False,
                    "error_code": "BACKING_STORE_UNREADABLE",
                    "status_kind": "backing-store-unreadable",
                    "http_status": 500,
                    "badge": "UNKNOWN",
                    "message": msg_u,
                    "error": msg_u,
                    "unknown_state": True,
                },
            ) from exc

    sw_root = Path((session.get("software") or {}).get("path") or cdir).resolve() if session else cdir
    rel_clean = Path(*[p for p in parts if p != "."])
    if sw_root.is_file():
        if rel_clean.as_posix() != sw_root.name:
            msg = f"File '{raw}' is outside the bound single-file software target '{sw_root.name}'."
            raise AnvilSourceRefusalError(
                msg,
                http_status=403,
                payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
            )
        resolved_target = sw_root
        repo_for_lookup = sw_root.parent
    else:
        walk = sw_root
        for part in rel_clean.parts:
            walk = walk / part
            if walk.is_symlink():
                msg = "Symbolic links are not permitted."
                raise AnvilSourceRefusalError(
                    msg,
                    http_status=403,
                    payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
                )
        cand = walk
        resolved_target = cand.resolve()
        if resolved_target == sw_root or sw_root not in resolved_target.parents:
            msg = f"File '{raw}' escapes software root boundary."
            raise AnvilSourceRefusalError(
                msg,
                http_status=403,
                payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
            )
        if resolved_target.is_symlink():
            msg = "Symbolic links are not permitted."
            raise AnvilSourceRefusalError(
                msg,
                http_status=403,
                payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
            )
        repo_for_lookup = sw_root

    for part in resolved_target.parts:
        low = part.lower()
        if low in FORBIDDEN_DOT_PARTS or low in FORBIDDEN_SECRET_NAMES:
            msg = f"Access to restricted path component '{part}' is not permitted."
            raise AnvilSourceRefusalError(
                msg,
                http_status=403,
                payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
            )
    if not resolved_target.is_file():
        msg = f"Source file '{rel_clean.as_posix()}' was not found."
        raise AnvilSourceRefusalError(
            msg,
            http_status=400,
            payload={"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": msg, "message": msg},
        )
    st_target = os.stat(resolved_target, follow_symlinks=False)
    if getattr(st_target, "st_nlink", 1) > 1:
        msg = "Hard-linked files are not permitted."
        raise AnvilSourceRefusalError(
            msg,
            http_status=403,
            payload={"ok": False, "error_code": "PATH_ESCAPE_REFUSED", "error": msg, "message": msg},
        )
    if int(st_target.st_size) > MAX_SOURCE_BUNDLE_BYTES:
        msg = (
            f"BOUND_EXCEEDED_REFUSAL: Source file '{rel_clean.as_posix()}' exceeds 2 MB limit "
            f"({st_target.st_size} > {MAX_SOURCE_BUNDLE_BYTES} bytes)."
        )
        raise AnvilSourceRefusalError(
            msg,
            http_status=413,
            payload={
                "ok": False,
                "error_code": "BOUND_EXCEEDED_REFUSAL",
                "bound_name": "MAX_SOURCE_BUNDLE_BYTES",
                "bound_limit": MAX_SOURCE_BUNDLE_BYTES,
                "observed_value": int(st_target.st_size),
                "error": msg,
                "message": msg,
            },
        )

    rel_posix = rel_clean.as_posix()
    if anvil_engine is not None and hasattr(anvil_engine, "get_file_level3_source"):
        payload = anvil_engine.get_file_level3_source(
            repo_for_lookup,
            rel_posix,
            code_map=(session.get("code_map") if session else None),
        )
        src_str = str(payload.get("content") if isinstance(payload.get("content"), str) else payload.get("source") or "")
        line_cnt = int(payload.get("total_lines") or len(src_str.splitlines()))
        return {
            "ok": True,
            **payload,
            "content": src_str,
            "raw_source": src_str,
            "start_line": int(payload.get("start_line") or 1),
            "end_line": int(payload.get("end_line") or line_cnt),
            "total_lines": line_cnt,
        }

    src_text = resolved_target.read_text(encoding="utf-8", errors="replace")
    src_lines = src_text.splitlines()
    numbered = "\n".join(f"{i:4d} | {ln}" for i, ln in enumerate(src_lines, start=1))
    return {
        "ok": True,
        "schema": "anvil-level3-source/v1",
        "file": rel_posix,
        "start_line": 1,
        "end_line": len(src_lines),
        "total_lines": len(src_lines),
        "content": src_text,
        "raw_source": src_text,
        "lines": [[i, ln] for i, ln in enumerate(src_lines, start=1)],
        "numbered_source": numbered,
        "symbols": [],
    }


def _resolve_session_sw_dir(cdir: Path, session: Optional[Dict[str, Any]]) -> Path:
    raw_sw = Path((session.get("software") or {}).get("path") or cdir).resolve() if session else cdir.resolve()
    return raw_sw.parent.resolve() if raw_sw.is_file() else raw_sw


def _v4_refusal_to_failure_payload(
    err: Any,
    v4_wb: Any,
    fallback_bundle: Optional[Dict[str, Any]] = None,
) -> Tuple[Dict[str, Any], int]:
    surf = v4_wb._map_refusal_to_surface_failure(err)
    if surf is not None:
        code = int(surf["http_status"])
        is_unknown = surf["status_kind"] == "backing-store-unreadable"
        preserved = fallback_bundle if surf["status_kind"] in {"dependency-missing", "dependency-slow-or-killed"} else None
        payload = {
            "ok": False,
            "error_code": err.error_code,
            "error": surf["message"],
            "status_kind": surf["status_kind"],
            "failure_state": surf["status_kind"],
            "http_status": code,
            "badge": surf["badge"],
            "message": surf["message"],
            "unknown_state": is_unknown,
            "surface_state": dict(surf),
            "v4_bundle": preserved,
            "bundle": preserved,
        }
        return payload, code
    err_dict = err.to_dict() if hasattr(err, "to_dict") else {"ok": False, "error_code": "ANVIL_REFUSED", "message": str(err)}
    err_code_str = str(err_dict.get("error_code") or "")
    http_status = 403 if err_code_str in {"EXECUTION_POLICY_REFUSED", "PATH_ESCAPE_REFUSED", "CONSENT_REQUIRED_REFUSED"} else 400
    err_dict.setdefault("error", str(err_dict.get("message") or "Anvil v4 request refused."))
    err_dict["http_status"] = http_status
    err_dict.setdefault("unknown_state", False)
    return err_dict, http_status


def _build_stage_symbol_maps(
    process_map: Dict[str, Any],
    refactor_map: Dict[str, Any],
) -> Tuple[Dict[str, str], Dict[str, str], str, str]:
    sym_to_old: Dict[str, str] = {}
    file_to_old: Dict[str, str] = {}
    stages = process_map.get("l1_stages") or []
    default_old = str(stages[0]["id"]) if stages else "S1"
    for st in stages:
        sid = str(st.get("id") or default_old)
        for f_rel in st.get("files") or []:
            file_to_old.setdefault(str(f_rel), sid)
        for step in st.get("l2_steps") or []:
            cref = step.get("code_ref") or {}
            sym = str(cref.get("symbol") or "")
            cf = str(cref.get("file") or "")
            if sym:
                sym_to_old[sym] = sid
                sym_to_old[sym.split(".")[-1]] = sid
            if cf:
                file_to_old.setdefault(cf, sid)

    old_to_new: Dict[str, str] = {}
    sym_to_new: Dict[str, str] = {}
    target_stages = refactor_map.get("target_stages") or []
    default_new = str(target_stages[0]["id"]) if target_stages else "N1"
    for edge in refactor_map.get("mapped_to_new") or []:
        if not isinstance(edge, dict):
            continue
        osid = str(edge.get("old_stage_id") or "")
        nsid = str(edge.get("target_stage_id") or "")
        esym = str(edge.get("symbol") or "")
        if osid and nsid and osid not in old_to_new:
            old_to_new[osid] = nsid
        if esym and nsid:
            sym_to_new[esym] = nsid
            sym_to_new[esym.split(".")[-1]] = nsid

    def resolve_old(sym: str, f_rel: str) -> str:
        return (
            sym_to_old.get(sym)
            or sym_to_old.get(sym.split(".")[-1])
            or file_to_old.get(f_rel)
            or default_old
        )

    def resolve_new(sym: str, old_sid: str) -> str:
        return (
            sym_to_new.get(sym)
            or sym_to_new.get(sym.split(".")[-1])
            or old_to_new.get(old_sid)
            or default_new
        )

    return sym_to_old, file_to_old, default_old, default_new


def _resolve_session_paper_path(cdir: Path, session: Optional[Dict[str, Any]]) -> Optional[Path]:
    if not isinstance(session, dict):
        return None
    sess_paper = session.get("paper_map")
    if not isinstance(sess_paper, dict) or not sess_paper:
        return None
    pinfo = sess_paper.get("paper_info") if isinstance(sess_paper.get("paper_info"), dict) else {}
    raw_paper_path = str(
        pinfo.get("primary_tex")
        or pinfo.get("path")
        or sess_paper.get("source_path")
        or sess_paper.get("paper_path")
        or sess_paper.get("bundle_dir")
        or ""
    ).strip()
    if not raw_paper_path:
        return None
    cand_p = Path(raw_paper_path)
    if not cand_p.is_absolute():
        cand_p = (cdir / cand_p).resolve()
    return cand_p if cand_p.exists() else None


def _build_companion_paper_bridge(
    cdir: Path,
    sw_dir: Path,
    session: Dict[str, Any],
    process_map: Dict[str, Any],
    refactor_map: Dict[str, Any],
    trace_data: Optional[Dict[str, Any]],
    *,
    pipeline_id: Optional[str] = None,
) -> Dict[str, Any]:
    sess_paper = session.get("paper_map")
    if not isinstance(sess_paper, dict) or not sess_paper:
        return {
            "ok": True,
            "schema": "anvil-paper-map/v1",
            "paper_map_version": "v4",
            "has_paper": False,
            "paper_path": "",
            "paper_title": "",
            "native_mathml_enforced": True,
            "sections": [],
            "algorithms": [],
            "equations": [],
            "unmapped_paper_items": [],
            "code_only_modules": [],
            "claims_mapped": 0,
            "alignments": [],
        }

    pinfo = sess_paper.get("paper_info") if isinstance(sess_paper.get("paper_info"), dict) else {}
    raw_paper_path = str(
        pinfo.get("primary_tex")
        or pinfo.get("path")
        or sess_paper.get("source_path")
        or sess_paper.get("paper_path")
        or sess_paper.get("bundle_dir")
        or ""
    ).strip()

    pmap: Optional[Dict[str, Any]] = None
    pmap_error: Optional[str] = None
    if raw_paper_path and anvil_engine is not None and hasattr(anvil_engine, "paper_to_code_map"):
        cand_p = Path(raw_paper_path)
        if not cand_p.is_absolute():
            cand_p = (cdir / cand_p).resolve()
        if cand_p.exists():
            try:
                pmap = anvil_engine.paper_to_code_map(
                    sw_dir,
                    paper_spec_path=cand_p,
                    code_map=None,
                    pipeline_id=pipeline_id,
                    trace_data=trace_data,
                    approve_run=False,
                    process_map=process_map,
                    refactor_map=refactor_map,
                )
            except Exception as exc:
                pmap_error = f"{type(exc).__name__}: {exc}"
                pmap = None

    stages = process_map.get("l1_stages") or []
    target_stages = refactor_map.get("target_stages") or []
    default_old = str(stages[0]["id"]) if stages else "S1"
    default_new = str(target_stages[0]["id"]) if target_stages else "N1"
    sym_to_old: Dict[str, str] = {}
    file_to_old: Dict[str, str] = {}
    for st in stages:
        sid = str(st.get("id") or default_old)
        for fr in st.get("files") or []:
            file_to_old.setdefault(str(fr), sid)
        for step in st.get("l2_steps") or []:
            cref = step.get("code_ref") or {}
            if cref.get("symbol"):
                sym_to_old[str(cref["symbol"])] = sid
                sym_to_old[str(cref["symbol"]).split(".")[-1]] = sid
    old_to_new: Dict[str, str] = {}
    sym_to_new: Dict[str, str] = {}
    for edge in refactor_map.get("mapped_to_new") or []:
        if isinstance(edge, dict) and edge.get("target_stage_id"):
            nsid = str(edge["target_stage_id"])
            if edge.get("old_stage_id"):
                old_to_new.setdefault(str(edge["old_stage_id"]), nsid)
            if edge.get("symbol"):
                sym_to_new[str(edge["symbol"])] = nsid
                sym_to_new[str(edge["symbol"]).split(".")[-1]] = nsid

    def _dual_links(sym_name: str, file_rel: str) -> Tuple[List[Dict[str, str]], List[Dict[str, str]]]:
        clean_sym = str(sym_name or "").strip()
        clean_file = str(file_rel or "").strip()
        osid = sym_to_old.get(clean_sym) or sym_to_old.get(clean_sym.split(".")[-1]) or file_to_old.get(clean_file) or default_old
        nsid = sym_to_new.get(clean_sym) or sym_to_new.get(clean_sym.split(".")[-1]) or old_to_new.get(osid) or default_new
        lbl_sym = clean_sym or clean_file or osid
        return ([{"stage_id": osid, "symbol": lbl_sym}], [{"stage_id": nsid, "symbol": lbl_sym}])

    def _clean_mml(raw_mml: str, fallback_latex: str, title_hint: str) -> str:
        s = str(raw_mml or "").strip()
        if s and "$" not in s and "<math" in s:
            return s
        src_expr = (fallback_latex or s or title_hint or "f(x)").replace("$", "")
        mml_fn = getattr(anvil_engine, "compile_latex_to_mathml", None) if anvil_engine is not None else None
        out_m = mml_fn(src_expr, display=True) if callable(mml_fn) else latex_to_mathml(src_expr, title_hint=title_hint)
        if not out_m or "<math" not in out_m or "$" in out_m:
            out_m = latex_to_mathml(src_expr, title_hint=title_hint)
        return out_m or "<math xmlns=\"http://www.w3.org/1998/Math/MathML\"><mi>f</mi></math>"

    if isinstance(pmap, dict) and pmap.get("has_paper") and (
        pmap.get("sections") or pmap.get("algorithms") or pmap.get("equations")
    ):
        out_pmap = dict(pmap)
        out_pmap["has_paper"] = True
        if sess_paper.get("paper_title") and (
            not out_pmap.get("paper_title")
            or out_pmap.get("paper_title") == Path(raw_paper_path).stem
        ):
            out_pmap["paper_title"] = sess_paper["paper_title"]
        for eq in out_pmap.get("equations") or []:
            eq["mathml"] = _clean_mml(eq.get("mathml", ""), eq.get("raw_latex", ""), eq.get("label", ""))
            if not eq.get("maps_to_old") or not eq.get("maps_to_new"):
                mfs = eq.get("matched_functions") or []
                top = mfs[0] if mfs else {}
                mo, mn = _dual_links(top.get("qualname", ""), top.get("file", ""))
                eq.setdefault("maps_to_old", mo)
                eq.setdefault("maps_to_new", mn)
            eq.setdefault("verification_stamp", eq.get("status") or "STATIC_ALIGNED")
        return out_pmap

    # Synthesize v4 Dual-Target Paper Bridge from sess_paper (.md/.pdf/inline claims fallback)
    paper_title = str(sess_paper.get("paper_title") or pinfo.get("title") or "Attached Manuscript")
    secs = [dict(s) for s in (sess_paper.get("sections") or []) if isinstance(s, dict)]
    algs = [dict(a) for a in (sess_paper.get("algorithms") or []) if isinstance(a, dict)]
    eqs = [dict(e) for e in (sess_paper.get("equations") or []) if isinstance(e, dict)]
    aligns = [dict(a) for a in (sess_paper.get("alignments") or []) if isinstance(a, dict)]

    if not secs:
        secs = [{
            "id": "sec-1",
            "number": "1",
            "title": paper_title,
            "summary": f"Companion manuscript ({paper_title}) mapped to software stages.",
            "equation_ids": [str(e.get("id") or f"eq-{i+1}") for i, e in enumerate(eqs or aligns)],
            "matched_functions": [a["mapped_function"] for a in aligns if a.get("mapped_function")][:4],
            "matched_modules": [a["mapped_file"] for a in aligns if a.get("mapped_file")][:4],
            "status": "STATIC_ALIGNED",
        }]

    for sec in secs:
        mfs = sec.get("matched_functions") or []
        mms = sec.get("matched_modules") or []
        mo, mn = _dual_links(mfs[0] if mfs else "", mms[0] if mms else "")
        if not sec.get("maps_to_old"):
            sec["maps_to_old"] = mo
        if not sec.get("maps_to_new"):
            sec["maps_to_new"] = mn

    for alg in algs:
        mo, mn = _dual_links(alg.get("primary_function", ""), alg.get("matched_module", ""))
        if not alg.get("maps_to_old"):
            alg["maps_to_old"] = mo
        if not alg.get("maps_to_new"):
            alg["maps_to_new"] = mn
        for st in alg.get("steps") or []:
            st_fns = st.get("matched_functions") or []
            st_fls = st.get("matched_files") or []
            smo, smn = _dual_links(st_fns[0] if st_fns else "", st_fls[0] if st_fls else "")
            if not st.get("maps_to_old"):
                st["maps_to_old"] = smo
            if not st.get("maps_to_new"):
                st["maps_to_new"] = smn

    if not eqs and aligns:
        for idx, al in enumerate(aligns, start=1):
            mfn = str(al.get("mapped_function") or "")
            mfl = str(al.get("mapped_file") or "")
            mo, mn = _dual_links(mfn, mfl)
            v_st = "VERIFIED-TRACE" if (trace_data is not None and mfn) else ("STATIC_ALIGNED" if mfn else "PAPER_ONLY")
            eqs.append({
                "id": str(al.get("claim_id") or f"eq-{idx}"),
                "number": str(idx),
                "label": str(al.get("title") or f"eq-{idx}"),
                "section_id": secs[0]["id"],
                "source_file": Path(raw_paper_path).name if raw_paper_path else "paper.md",
                "line_start": idx,
                "raw_latex": str(al.get("raw_latex") or ""),
                "mathml": _clean_mml(al.get("mathml", ""), al.get("raw_latex", ""), al.get("title", "")),
                "matched_functions": (
                    [{"qualname": mfn, "file": mfl, "line_start": int(al.get("lineno") or 1), "line_end": int(al.get("lineno") or 1), "score": 6.0, "matched_identifiers": []}]
                    if mfn else []
                ),
                "maps_to_old": al.get("maps_to_old") or mo,
                "maps_to_new": al.get("maps_to_new") or mn,
                "verification_stamp": v_st,
                "v4_verdict": v_st,
                "status": v_st,
            })
    else:
        for eq in eqs:
            eq["mathml"] = _clean_mml(eq.get("mathml", ""), eq.get("raw_latex", ""), eq.get("label", ""))
            mfs = eq.get("matched_functions") or []
            top = mfs[0] if (mfs and isinstance(mfs[0], dict)) else {}
            mo, mn = _dual_links(top.get("qualname", ""), top.get("file", ""))
            if not eq.get("maps_to_old"):
                eq["maps_to_old"] = mo
            if not eq.get("maps_to_new"):
                eq["maps_to_new"] = mn
            eq.setdefault("verification_stamp", eq.get("status") or "STATIC_ALIGNED")

    out_bridge: Dict[str, Any] = {
        "ok": True,
        "schema": "anvil-paper-map/v1",
        "paper_map_version": "v4",
        "has_paper": True,
        "paper_path": raw_paper_path,
        "source_path": raw_paper_path,
        "paper_info": pinfo,
        "paper_title": paper_title,
        "native_mathml_enforced": True,
        "sections": secs,
        "algorithms": algs,
        "equations": eqs,
        "unmapped_paper_items": [],
        "code_only_modules": [],
        "summary_counts": {
            "sections": len(secs),
            "algorithms": len(algs),
            "equations": len(eqs),
        },
        "claims_mapped": len(aligns) or len(eqs),
        "alignments": aligns,
    }
    if pmap_error:
        out_bridge["paper_map_error"] = pmap_error
    return out_bridge


def _load_or_build_cockpit_profile_lit(
    cdir: Path,
    sw_dir: Path,
    v4_mods: Dict[str, Any],
) -> Dict[str, Any]:
    v4_proc = v4_mods["anvil_v4_process"]
    v4_ref = v4_mods["anvil_v4_refactor"]
    v4_wb = v4_mods["anvil_v4_workbench"]
    v4_dir = v4_wb._probe_v4_store_dir(cdir)
    prof_path = v4_dir / "profile_lit.json"
    if v4_proc._is_link_or_junction(prof_path):
        v4_wb._raise_backing_store_unreadable("profile_lit.json is a symlink or junction")
    if prof_path.exists():
        if not prof_path.is_file():
            v4_wb._raise_backing_store_unreadable("profile_lit.json is not a regular file")
        loaded = v4_proc.atomic_locked_read_json(prof_path)
        if loaded.get("schema") == v4_ref.PROFILE_LIT_SCHEMA:
            return loaded
    doc = v4_ref.run_profile_and_literature(sw_dir, approve_run=False, persist=False)
    v4_proc.atomic_locked_write_json(prof_path, doc)
    return doc


def _stamp_cockpit_xval_seating(rec: Dict[str, Any], seating: Dict[str, str]) -> Dict[str, Any]:
    out_r = copy.deepcopy(rec)
    v_str = str(out_r.get("verdict") or "PASS")
    cross_ok = bool(out_r.get("cross_family_attested"))
    seats_list = out_r.get("seats") if isinstance(out_r.get("seats"), list) else []
    live_seats = sum(1 for s in seats_list if isinstance(s, dict) and s.get("model_attested"))
    if not seats_list and out_r.get("model_attested"):
        live_seats = 1
    if "verdict_qualified" not in out_r:
        if v_str == "FAIL":
            out_r["verdict_qualified"] = "FAIL"
        elif v_str == "PASS":
            out_r["verdict_qualified"] = (
                "PASS" if cross_ok else ("PASS_SINGLE_FAMILY" if live_seats >= 1 else "PASS_DETERMINISTIC_ONLY")
            )
        else:
            out_r["verdict_qualified"] = v_str

    if out_r.get("mode") == "DETERMINISTIC_FALLBACK":
        if not out_r.get("orchestrator_model") or out_r.get("orchestrator_family") in {"", "unattested", "unattested_seat1"}:
            out_r["orchestrator_family"] = seating["coding_family"]
            out_r["orchestrator_model"] = seating["coding_short"]
        out_r["seat1_orchestrator"] = seating["coding_label"]
        out_r["seat2_validator"] = (
            f"{seating['review_short']} · Deterministic Structural & Citation Fallback "
            f"(configured review seat: {seating['review_family']}; cross_family_attested=false)"
        )
    elif out_r.get("mode") == "RATE_LIMITED_COOLDOWN":
        if not out_r.get("orchestrator_model") or out_r.get("orchestrator_family") in {"", "unattested", "unattested_seat1"}:
            out_r["orchestrator_family"] = seating["coding_family"]
            out_r["orchestrator_model"] = seating["coding_short"]
        out_r.setdefault("seat1_orchestrator", seating["coding_label"])
        out_r["seat2_validator"] = (
            f"{seating['review_short']} · Rate-Limited Cooldown Fallback "
            f"(configured review seat: {seating['review_family']}; cross_family_attested=false)"
        )
    else:
        out_r.setdefault("seat1_orchestrator", seating["coding_label"])
        out_r.setdefault("seat2_validator", seating["review_label"])
    return out_r


def _load_or_build_cockpit_xval(
    cdir: Path,
    sw_dir: Path,
    process_map: Dict[str, Any],
    refactor_map: Dict[str, Any],
    paper_map: Dict[str, Any],
    v4_mods: Dict[str, Any],
    *,
    paper_path: Optional[Path] = None,
) -> Dict[str, Any]:
    v4_proc = v4_mods["anvil_v4_process"]
    v4_xval = v4_mods["anvil_v4_xval"]
    v4_wb = v4_mods["anvil_v4_workbench"]
    v4_dir = v4_wb._probe_v4_store_dir(cdir)
    xval_path = v4_dir / "xval_receipt.json"
    seating = _read_model_seating_info()

    if v4_proc._is_link_or_junction(xval_path):
        v4_wb._raise_backing_store_unreadable("xval_receipt.json is a symlink or junction")
    if xval_path.exists():
        if not xval_path.is_file():
            v4_wb._raise_backing_store_unreadable("xval_receipt.json is not a regular file")
        loaded = v4_proc.atomic_locked_read_json(xval_path)
        if loaded.get("schema") == v4_xval.XVAL_RECEIPT_SCHEMA:
            stamped = _stamp_cockpit_xval_seating(loaded, seating)
            divs_now = list((paper_map.get("divergences") or []) if isinstance(paper_map, dict) else [])
            if divs_now and "citation_audit" not in stamped and hasattr(v4_xval, "audit_divergence_citations"):
                stamped["citation_audit"] = v4_xval.audit_divergence_citations(sw_dir, divs_now, paper_path=paper_path)
                stamped["citation_audit_post_hoc"] = True
            return stamped

    pap_arg = paper_map if (isinstance(paper_map, dict) and paper_map.get("has_paper")) else None
    try:
        receipt = v4_xval.run_xval_audit(
            sw_dir,
            process_map=process_map,
            refactor_map=refactor_map,
            paper_map=pap_arg,
            paper_path=paper_path,
            persist=False,
        )
    except v4_proc.AnvilRefusalError as x_err:
        if x_err.error_code != "BOUND_EXCEEDED_REFUSAL":
            raise
        det_verdict, det_findings = v4_xval._run_deterministic_seat2_checks(
            process_map, refactor_map, pap_arg, repo_root=sw_dir, paper_path=paper_path
        )
        divs_fb = list((paper_map.get("divergences") or []) if isinstance(paper_map, dict) else [])
        cite_fb = (
            v4_xval.audit_divergence_citations(sw_dir, divs_fb, paper_path=paper_path)
            if hasattr(v4_xval, "audit_divergence_citations")
            else {
                "ok": len(divs_fb) == 0,
                "verdict": "PASS" if len(divs_fb) == 0 else "NOT_RUN",
                "total_divergences": len(divs_fb),
                "verified_count": 0,
                "failed_count": 0,
                "rows": [],
                "findings": [],
            }
        )
        fp_s = str(process_map.get("repo_fingerprint") or refactor_map.get("repo_fingerprint") or "")
        receipt = {
            "ok": True,
            "schema": v4_xval.XVAL_RECEIPT_SCHEMA,
            "mode": "DETERMINISTIC_FALLBACK",
            "cross_family_attested": False,
            "model_served": None,
            "model_attested": False,
            "orchestrator_family": seating["coding_family"],
            "orchestrator_model": seating["coding_short"],
            "validator_family": "deterministic_local_verifier",
            "verdict": det_verdict,
            "verdict_qualified": "FAIL" if det_verdict == "FAIL" else ("PASS_DETERMINISTIC_ONLY" if det_verdict == "PASS" else det_verdict),
            "validator_calls_made": 0,
            "max_concurrency_enforced": 2,
            "digest_bytes": 0,
            "digest_sha256": hashlib.sha256(fp_s.encode("utf-8")).hexdigest()[:24],
            "fallback_reason": f"Deterministic Seat-2 structural verification ({x_err.message})",
            "citation_audit": cite_fb,
            "shards": [],
            "findings": det_findings,
        }
    stamped_new = _stamp_cockpit_xval_seating(receipt, seating)
    v4_proc.atomic_locked_write_json(xval_path, stamped_new)
    return stamped_new


def _sync_v4_dialogue_turns(
    cdir: Path,
    v4_sess: Dict[str, Any],
    session: Dict[str, Any],
    v4_proc: Any,
) -> Dict[str, Any]:
    chat_hist = session.get("chat_history") or []
    active_sid = str(v4_sess.get("active_stage_id") or "S1")
    mapped_turns: List[Dict[str, Any]] = []
    for m in chat_hist[-80:]:
        if not isinstance(m, dict) or not m.get("text"):
            continue
        raw_role = str(m.get("role") or "user").lower()
        norm_role = "assistant" if raw_role in {"anvil", "assistant"} else "user"
        mapped_turns.append({
            "role": norm_role,
            "text": str(m["text"])[:4096],
            "stage_id": str(m.get("stage_id") or active_sid),
            "ts": str(m.get("at") or ""),
        })
    existing_turns = v4_sess.get("dialogue_turns") or []
    if mapped_turns and mapped_turns != existing_turns:
        updated = dict(v4_sess)
        updated["dialogue_turns"] = mapped_turns
        v4_proc.atomic_locked_write_json(_v4_dir(cdir) / "workbench_session.json", updated)
        return updated
    return v4_sess


def _build_cockpit_v4_bundle(
    cdir: Path,
    session: Dict[str, Any],
    *,
    prevalidated_ws: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        raise RuntimeError("Anvil v4 modules unavailable.")
    v4_proc = v4_mods["anvil_v4_process"]
    v4_trace = v4_mods["anvil_v4_trace"]
    v4_ref = v4_mods["anvil_v4_refactor"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    sw_dir = _resolve_session_sw_dir(cdir, session)
    if not sw_dir.exists() or not sw_dir.is_dir():
        raise v4_proc.AnvilRefusalError("PATH_ESCAPE_REFUSED", "Software target directory does not exist.", cwe="CWE-22")

    # Strictly read/write per-cockpit v4 state under `<cdir>/.anvil/v4` (never `sw_dir`)
    trace_data = v4_wb._load_optional_trace_store(cdir)
    cand_paper = _resolve_session_paper_path(cdir, session)
    ws_path = _v4_dir(cdir) / "workbench_session.json"
    peek_pipe: Optional[str] = None
    if isinstance(prevalidated_ws, dict):
        peek_pipe = str(prevalidated_ws.get("active_pipeline") or "").strip() or None
    elif ws_path.is_file() and not v4_proc._is_link_or_junction(ws_path):
        try:
            ws_peek = v4_proc.atomic_locked_read_json(ws_path, max_bytes=4_194_304)
            if isinstance(ws_peek, dict):
                peek_pipe = str(ws_peek.get("active_pipeline") or "").strip() or None
        except Exception:
            peek_pipe = None

    sfile = _session_file(cdir)
    try:
        sf_st = sfile.stat() if sfile.is_file() else None
        sf_sig = f"{sf_st.st_mtime_ns}:{sf_st.st_size}" if sf_st else "none"
    except OSError:
        sf_sig = "none"

    fp_digest = v4_wb.compute_repo_state_fingerprint(sw_dir, cand_paper, store_root=cdir)
    cache_key = (str(cdir), str(sw_dir), str(cand_paper or ""), str(peek_pipe or ""), fp_digest, sf_sig)

    with _COCKPIT_V4_BUNDLE_CACHE_LOCK:
        cached_core = _COCKPIT_V4_BUNDLE_CACHE.get(cache_key)

    if cached_core is not None:
        process_map = cached_core["process_map"]
        if isinstance(prevalidated_ws, dict):
            v4_sess = v4_wb._validate_and_normalize_session(
                prevalidated_ws,
                v4_wb._default_session_payload(process_map),
            )
        else:
            v4_sess = v4_wb._load_or_init_workbench_session(cdir, process_map, persist=True)
        v4_sess = _sync_v4_dialogue_turns(cdir, v4_sess, session, v4_proc)
        cached_pins = tuple(cached_core.get("_pinned_watches_sig") or ())
        cur_pins = tuple(v4_sess.get("pinned_watches") or [])
        variable_catalog = (
            cached_core["variable_catalog"]
            if cur_pins == cached_pins
            else v4_wb._build_smart_funnel_catalog(
                process_map,
                trace_data,
                cached_core["files_source_map"],
                list(cur_pins),
            )
        )
        warm_bundle = {k: v for k, v in cached_core.items() if not k.startswith("_")}
        if isinstance(warm_bundle.get("surface_state"), dict):
            warm_bundle["surface_state"] = dict(warm_bundle["surface_state"])
        if isinstance(warm_bundle.get("xval_receipt"), dict):
            warm_bundle["xval_receipt"] = copy.deepcopy(warm_bundle["xval_receipt"])
        warm_bundle["variable_catalog"] = dict(variable_catalog) if isinstance(variable_catalog, dict) else variable_catalog
        warm_bundle["session"] = copy.deepcopy(v4_sess)
        return warm_bundle

    pre_src_fp = (
        v4_wb.compute_repo_source_fingerprint(sw_dir, cand_paper)
        if hasattr(v4_wb, "compute_repo_source_fingerprint")
        else ""
    )

    prelim_map = v4_proc.build_process_map(sw_dir, trace_data=trace_data, persist=False, paper_path=cand_paper)
    v4_sess = v4_wb._load_or_init_workbench_session(cdir, prelim_map, persist=True)
    v4_sess = _sync_v4_dialogue_turns(cdir, v4_sess, session, v4_proc)
    active_pipe = str(v4_sess.get("active_pipeline") or "").strip() or None
    if active_pipe:
        try:
            process_map = v4_proc.build_process_map(sw_dir, trace_data=trace_data, persist=False, paper_path=cand_paper, pipeline_id=active_pipe)
        except v4_proc.AnvilRefusalError:
            active_pipe = None
            process_map = prelim_map
    else:
        process_map = prelim_map
    refactor_map = v4_ref.build_refactor_map(
        sw_dir,
        trace_data=trace_data,
        persist=False,
        paper_path=cand_paper,
        pipeline_id=active_pipe,
        process_map=process_map,
    )
    paper_map = _build_companion_paper_bridge(cdir, sw_dir, session, process_map, refactor_map, trace_data, pipeline_id=active_pipe)
    sci_val = (
        paper_map.get("scientific_validation")
        if isinstance(paper_map, dict) and paper_map.get("scientific_validation")
        else (session.get("code_map") or {}).get("scientific_validation")
    )
    profile_lit = _load_or_build_cockpit_profile_lit(cdir, sw_dir, v4_mods)
    xval_receipt = _load_or_build_cockpit_xval(
        cdir,
        sw_dir,
        process_map,
        refactor_map,
        paper_map,
        v4_mods,
        paper_path=cand_paper,
    )
    files_source_map = v4_wb._build_files_source_map(sw_dir, process_map, trace_data)
    cur_pins_list = list(v4_sess.get("pinned_watches") or [])
    variable_catalog = v4_wb._build_smart_funnel_catalog(
        process_map,
        trace_data,
        files_source_map,
        cur_pins_list,
    )

    l0_list = process_map.get("l0_scenarios") or []
    if l0_list and isinstance(l0_list[0].get("recommended_argv"), list):
        rec_argv = [str(x) for x in l0_list[0]["recommended_argv"]]
    elif files_source_map:
        first_rel = next(iter(files_source_map.keys()))
        ext = Path(first_rel).suffix.lower()
        rbin = "node" if ext in {".js", ".mjs", ".ts"} else ("Rscript" if ext == ".r" else "python")
        rec_argv = [rbin, first_rel]
    else:
        rec_argv = ["pytest", "-q"]

    try:
        resolved_argv = list(v4_trace.validate_execution_argv(sw_dir, rec_argv)["validated_argv"])
    except Exception:
        resolved_argv = list(rec_argv)
    safe_slug = re.sub(r"[^A-Za-z0-9_.-]+", "_", sw_dir.name)[:32] or "repo"
    isolated_temp_copy_path = f"$TMPDIR/anvil_v4_trace_{safe_slug}_<ephemeral_worktree>"

    if process_map.get("status_kind") == "empty-but-valid":
        surface_state: Dict[str, Any] = dict(v4_wb.SURFACE_FAILURE_TABLE["empty-but-valid"])
    else:
        surface_state = {
            "kind": "healthy",
            "status_kind": "healthy",
            "http_status": 200,
            "badge": "TRACED" if trace_data is not None else "STATIC_AST",
            "message": (
                "Consented runtime trace overlaid on steady-coordinate process map"
                if trace_data is not None
                else "Zero-execution static AST map ready (click Run Consented Trace to overlay live values)"
            ),
        }

    divergences_list = list((paper_map.get("divergences") or []) if isinstance(paper_map, dict) else [])

    built_bundle: Dict[str, Any] = {
        "ok": True,
        "schema": v4_wb.WORKBENCH_BUNDLE_SCHEMA,
        "repo_name": sw_dir.name,
        "repo_fingerprint": process_map.get("repo_fingerprint", ""),
        "state_fingerprint": fp_digest,
        "isolation_boundary": v4_trace.ISOLATION_BOUNDARY if trace_data is not None else "static_ast_zero_execution",
        "non_vm_trust_warning": v4_trace.NON_VM_TRUST_WARNING,
        "cli_approve_run": False,
        "has_trace": bool(trace_data is not None),
        "has_paper": bool(paper_map.get("has_paper", False)),
        "recommended_argv": rec_argv,
        "resolved_argv": resolved_argv,
        "isolated_temp_copy_path": isolated_temp_copy_path,
        "surface_state": surface_state,
        "status_kind": surface_state["status_kind"],
        "badge": surface_state["badge"],
        "message": surface_state["message"],
        "process_map": process_map,
        "refactor_map": refactor_map,
        "paper_map": paper_map,
        "divergences": divergences_list,
        "scientific_validation": sci_val,
        "profile_lit": profile_lit,
        "xval_receipt": xval_receipt,
        "trace_summary": (
            {
                "validated_argv": trace_data.get("validated_argv", []),
                "returncode": trace_data.get("returncode", 0),
                "elapsed_sec": trace_data.get("elapsed_sec", 0.0),
                "tripwires": trace_data.get("tripwires", []),
                "map_drift_edges": trace_data.get("map_drift_edges", []),
                "stage_verdicts": trace_data.get("stage_verdicts", {}),
                "stage_wall_sec": trace_data.get("stage_wall_sec", {}),
                "bounds": trace_data.get("bounds", {}),
                "uncaught_exception": trace_data.get("uncaught_exception"),
            }
            if trace_data is not None
            else None
        ),
        "variable_catalog": variable_catalog,
        "files_source_map": files_source_map,
        "session": v4_sess,
    }

    post_src_fp = (
        v4_wb.compute_repo_source_fingerprint(sw_dir, cand_paper)
        if hasattr(v4_wb, "compute_repo_source_fingerprint")
        else pre_src_fp
    )
    final_fp = v4_wb.compute_repo_state_fingerprint(sw_dir, cand_paper, store_root=cdir)
    if post_src_fp == pre_src_fp:
        built_bundle["state_fingerprint"] = final_fp
        final_key = (str(cdir), str(sw_dir), str(cand_paper or ""), str(active_pipe or ""), final_fp, sf_sig)
        with _COCKPIT_V4_BUNDLE_CACHE_LOCK:
            if len(_COCKPIT_V4_BUNDLE_CACHE) >= 32:
                _COCKPIT_V4_BUNDLE_CACHE.clear()
            cache_entry = copy.deepcopy(built_bundle)
            cache_entry["_pinned_watches_sig"] = tuple(cur_pins_list)
            _COCKPIT_V4_BUNDLE_CACHE[final_key] = cache_entry
            if final_key != cache_key:
                _COCKPIT_V4_BUNDLE_CACHE[cache_key] = cache_entry

    return built_bundle


_SUMMARY_STATUS_CACHE: Dict[str, Any] = {}


def get_session_status(cockpit_dir: str | Path, summary_only: bool = False) -> Dict[str, Any]:
    cdir = Path(cockpit_dir).resolve()
    sfile = _session_file(cdir)
    if summary_only:
        in_pytest = bool(os.environ.get("PYTEST_CURRENT_TEST"))
        try:
            sf_stat = sfile.stat() if sfile.is_file() else None
            sf_sig = (sf_stat.st_mtime_ns, sf_stat.st_size) if sf_stat else (0, 0)
        except OSError:
            sf_sig = (0, 0)
        has_v4_trace_fast = False
        try:
            has_v4_trace_fast = (_v4_dir(cdir) / "last_trace.json").is_file()
        except Exception:
            has_v4_trace_fast = False
        cache_key = str(cdir)
        now_m = time.monotonic()
        if not in_pytest:
            hit = _SUMMARY_STATUS_CACHE.get(cache_key)
            if hit and hit[0] == (sf_sig, has_v4_trace_fast) and (now_m - hit[1]) < 15.0:
                return dict(hit[2])
        sess_sum = None
        raw_updated_at = None
        raw_has_paper = False
        corrupt_err_fast = None
        if sfile.is_file():
            try:
                loaded_fast = _read_session_ir(sfile)
                if isinstance(loaded_fast, dict) and loaded_fast.get("active"):
                    loaded_fast["cockpit_name"] = _cockpit_display_name(cdir)
                    raw_updated_at = loaded_fast.get("updated_at")
                    raw_has_paper = bool(loaded_fast.get("paper_map"))
                    sess_sum = _project_session_summary(loaded_fast)
            except Exception as exc:
                corrupt_err_fast = f"Session file {sfile.name} could not be parsed: {exc}"
        cands_fast = discover_cockpit_candidates(cdir)
        out_fast: Dict[str, Any] = {
            "ok": corrupt_err_fast is None,
            "cockpit_dir": str(cdir),
            "cockpit_name": _cockpit_display_name(cdir),
            "active": bool(sess_sum is not None),
            "unknown_state": corrupt_err_fast is not None,
            "summary_only": True,
            "session": sess_sum,
            "candidates": {
                "software": (cands_fast.get("software") or [])[:6],
                "papers": (cands_fast.get("papers") or [])[:6],
            },
            "v4_stamp": {
                "updated_at": raw_updated_at,
                "has_trace": has_v4_trace_fast,
                "has_paper": raw_has_paper,
            },
        }
        if corrupt_err_fast:
            out_fast["warning"] = corrupt_err_fast
        if not in_pytest:
            if len(_SUMMARY_STATUS_CACHE) > 128:
                _SUMMARY_STATUS_CACHE.clear()
            _SUMMARY_STATUS_CACHE[cache_key] = ((sf_sig, has_v4_trace_fast), now_m, dict(out_fast))
        return out_fast

    session = None
    corrupt_error = None
    if sfile.is_file():
        try:
            loaded = _read_session_ir(sfile)
            if isinstance(loaded, dict) and loaded.get("active"):
                session = loaded
                migrated = False
                disp_name = _cockpit_display_name(cdir)
                if session.get("cockpit_name") != disp_name:
                    session["cockpit_name"] = disp_name
                    migrated = True
                code_map = session.get("code_map") or {}
                buckets = code_map.get("conceptual_buckets") or []
                sw_path = Path((session.get("software") or {}).get("path") or cdir)
                if len(buckets) > 9 and anvil_engine is not None and hasattr(anvil_engine, "_cluster_into_architectural_buckets"):
                    code_map["module_buckets"] = buckets
                    buckets = anvil_engine._cluster_into_architectural_buckets(sw_path, buckets)
                    code_map["conceptual_buckets"] = buckets
                    if hasattr(anvil_engine, "_build_foundry_flow_diagram"):
                        code_map.setdefault("process_map", {})["flow_diagram"] = anvil_engine._build_foundry_flow_diagram(
                            buckets, (code_map.get("process_map") or {}).get("edges") or []
                        )
                    migrated = True
                elif buckets and not (code_map.get("process_map") or {}).get("flow_diagram") and anvil_engine is not None and hasattr(anvil_engine, "_build_foundry_flow_diagram"):
                    code_map.setdefault("process_map", {})["flow_diagram"] = anvil_engine._build_foundry_flow_diagram(
                        buckets, (code_map.get("process_map") or {}).get("edges") or []
                    )
                    migrated = True
                if buckets and (not buckets[0].get("inner_process_map") or not (buckets[0].get("inner_process_map") or {}).get("flow_diagram")):
                    _enrich_buckets_with_previews(sw_path, buckets)
                    migrated = True
                remap = session.get("remap")
                if isinstance(remap, dict) and (not remap.get("best_in_class_map") or not (remap.get("best_in_class_map") or {}).get("flow_diagram")):
                    cmp_path = Path((session.get("compare_software") or {}).get("path") or sw_path)
                    remap["best_in_class_map"] = _build_best_in_class_remap(
                        sw_path,
                        cmp_path,
                        code_map,
                        session.get("orange_split") or {},
                        remap,
                    )
                    migrated = True
                if anvil_engine is not None:
                    if buckets and (not buckets[0].get("level1_summary") or not buckets[0].get("level3_code")):
                        if hasattr(anvil_engine, "_enrich_progressive_levels"):
                            anvil_engine._enrich_progressive_levels(
                                sw_path,
                                buckets,
                                paper_map=session.get("paper_map"),
                                remap=remap,
                            )
                            migrated = True
                    if not session.get("beta_reader_panel") and hasattr(anvil_engine, "run_beta_reader_panel"):
                        session["beta_reader_panel"] = anvil_engine.run_beta_reader_panel(
                            sw_path,
                            code_map=code_map,
                            orange_split=session.get("orange_split"),
                            remap=remap,
                        )
                        migrated = True
                    if not session.get("walkthrough_trace") and hasattr(anvil_engine, "run_code_walkthrough"):
                        session["walkthrough_trace"] = anvil_engine.run_code_walkthrough(
                            sw_path,
                            code_map=code_map,
                            block_id=str(session.get("selected_block_id") or ""),
                        )
                        migrated = True
                    if not (_session_dir(cdir) / "manifest.json").is_file():
                        try:
                            _write_anvil_manifest(cdir, session)
                        except Exception:
                            pass
                if migrated:
                    try:
                        _write_session_ir(sfile, session)
                    except Exception:
                        pass
        except Exception as exc:
            corrupt_error = f"Session file {sfile.name} could not be parsed: {exc}"
    cands = discover_cockpit_candidates(cdir)
    if summary_only:
        cands = {
            "software": (cands.get("software") or [])[:6],
            "papers": (cands.get("papers") or [])[:6],
        }
    out: Dict[str, Any] = {
        "ok": True,
        "cockpit_dir": str(cdir),
        "cockpit_name": _cockpit_display_name(cdir),
        "active": bool(session),
        "summary_only": bool(summary_only),
        "session": (_project_session_summary(session) if (session and summary_only) else session),
        "candidates": cands,
    }
    if corrupt_error:
        out["warning"] = corrupt_error
        out["unknown_state"] = True
        out["status_kind"] = "backing-store-unreadable"
    else:
        out["unknown_state"] = False
    if summary_only:
        has_v4_trace = False
        try:
            has_v4_trace = (_v4_dir(cdir) / "last_trace.json").is_file()
        except OSError:
            has_v4_trace = False
        out["v4_stamp"] = {
            "updated_at": session.get("updated_at") if session else None,
            "has_trace": has_v4_trace,
            "has_paper": bool(session and session.get("paper_map")),
        }
    elif session:
        v4_mods = _load_anvil_v4_modules()
        if v4_mods:
            v4_proc = v4_mods["anvil_v4_process"]
            v4_wb = v4_mods["anvil_v4_workbench"]
            try:
                v4_bundle = _build_cockpit_v4_bundle(cdir, session)
                out["v4_bundle"] = v4_bundle
                out["surface_state"] = v4_bundle["surface_state"]
                out["unknown_state"] = False
            except v4_proc.AnvilRefusalError as v4_err:
                fail_payload, _ = _v4_refusal_to_failure_payload(v4_err, v4_wb)
                out["v4_bundle"] = None
                out["surface_state"] = fail_payload.get("surface_state")
                out["unknown_state"] = bool(fail_payload.get("unknown_state", False))
                out["v4_error"] = fail_payload
            except Exception as v4_exc:
                out["v4_bundle"] = None
                out["surface_state"] = dict(v4_wb.SURFACE_FAILURE_TABLE["backing-store-unreadable"])
                out["unknown_state"] = True
                out["v4_error"] = {"ok": False, "message": str(v4_exc)}
    return out


get_cockpit_status = get_session_status


def get_v4_cockpit_state(cockpit_dir: str | Path) -> Tuple[Dict[str, Any], int]:
    """Return `(payload, http_status)` for the Cockpit's Anvil v4 state, enforcing 5-state fail-closed semantics."""
    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        return (
            {
                "ok": False,
                "error_code": "DEPENDENCY_MISSING",
                "status_kind": "dependency-missing",
                "http_status": 503,
                "badge": "DEGRADED_STATIC",
                "message": "Required runtime/tracer unavailable — showing static AST map",
                "unknown_state": False,
            },
            503,
        )
    v4_proc = v4_mods["anvil_v4_process"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    # Always validate `.anvil/v4` stores fail-closed FIRST (500 on unreadable/corrupt session, 502 on corrupt trace)
    prevalidated_ws: Optional[Dict[str, Any]] = None
    try:
        _ = v4_wb._load_optional_trace_store(cdir)
        ws_path = _v4_dir(cdir) / "workbench_session.json"
        if v4_proc._is_link_or_junction(ws_path):
            v4_wb._raise_backing_store_unreadable("workbench_session.json is a symlink or junction")
        if ws_path.exists():
            if not ws_path.is_file():
                v4_wb._raise_backing_store_unreadable("workbench_session.json is not a regular file")
            try:
                raw_ws = v4_proc.atomic_locked_read_json(ws_path, max_bytes=4_194_304)
                v4_wb._validate_and_normalize_session(
                    raw_ws,
                    v4_wb._default_session_payload({"l1_stages": [], "l2_steps": [], "l3_files": []}),
                )
                prevalidated_ws = raw_ws
            except v4_proc.AnvilRefusalError as ws_err:
                v4_wb._raise_backing_store_unreadable(ws_err.message)
    except v4_proc.AnvilRefusalError as store_err:
        return _v4_refusal_to_failure_payload(store_err, v4_wb)

    sfile = _session_file(cdir)
    session: Optional[Dict[str, Any]] = None
    if sfile.is_file():
        try:
            loaded = _peek_active_session_ir_readonly(sfile)
            if isinstance(loaded, dict) and loaded.get("active"):
                session = loaded
        except Exception as exc:
            try:
                v4_wb._raise_backing_store_unreadable(f"Corrupt session.json: {exc}")
            except v4_proc.AnvilRefusalError as s_err:
                return _v4_refusal_to_failure_payload(s_err, v4_wb)

    if not session:
        base_status = get_session_status(cdir, summary_only=True)
        empty_surf = dict(v4_wb.SURFACE_FAILURE_TABLE["empty-but-valid"])
        return (
            {
                "ok": True,
                "active": False,
                "cockpit_dir": str(cdir),
                "cockpit_name": base_status.get("cockpit_name", _cockpit_display_name(cdir)),
                "candidates": base_status.get("candidates", {}),
                "surface_state": empty_surf,
                "status_kind": empty_surf["status_kind"],
                "badge": empty_surf["badge"],
                "message": empty_surf["message"],
                "unknown_state": False,
                "v4_bundle": None,
                "bundle": None,
            },
            200,
        )

    try:
        v4_bundle = _build_cockpit_v4_bundle(cdir, session, prevalidated_ws=prevalidated_ws)
        return (
            {
                "ok": True,
                "active": True,
                "cockpit_dir": str(cdir),
                "cockpit_name": session.get("cockpit_name") or _cockpit_display_name(cdir),
                "surface_state": v4_bundle["surface_state"],
                "status_kind": v4_bundle["status_kind"],
                "badge": v4_bundle["badge"],
                "message": v4_bundle["message"],
                "unknown_state": False,
                "v4_bundle": v4_bundle,
                "bundle": v4_bundle,
            },
            200,
        )
    except v4_proc.AnvilRefusalError as err:
        return _v4_refusal_to_failure_payload(err, v4_wb)


def start_cockpit_session(
    cockpit_dir: str | Path,
    mode: str = "code",
    software_spec: str = ".",
    compare_spec: str = "",
    paper_spec: str = "",
    signed_off_drops: Optional[List[str]] = None,
) -> Dict[str, Any]:
    """Create or replace the active Per-Cockpit Anvil Session for `cockpit_dir` using a single AST scan."""
    if anvil_engine is None:
        raise ValueError("Anvil engine (skills/anvil/scripts/anvil_engine.py) is unavailable on this host.")

    cdir = Path(cockpit_dir).resolve()
    with _get_cockpit_lock(cdir):
        _session_dir(cdir).mkdir(parents=True, exist_ok=True)
        cockpit_name = _cockpit_display_name(cdir)

        # Preserve prior signed_off_drops and back up previous session before overwriting
        sfile = _session_file(cdir)
        prior_signed: List[str] = []
        prior_sw_path: str = ""
        if sfile.is_file():
            try:
                old_raw = sfile.read_text(encoding="utf-8", errors="replace")
                _atomic_write_text(_session_dir(cdir) / "session.prev.json", old_raw)
                old_obj = json.loads(old_raw)
                if isinstance(old_obj, dict):
                    if isinstance(old_obj.get("signed_off_drops"), list):
                        prior_signed = list(old_obj["signed_off_drops"])
                    prior_sw_path = str((old_obj.get("software") or {}).get("path") or "")
            except Exception:
                pass

        sw_info = resolve_software_target(cdir, software_spec or ".", role="primary")
        sw_path = Path(sw_info["path"])
        if prior_sw_path and prior_sw_path != str(sw_path):
            shutil.rmtree(_v4_dir(cdir), ignore_errors=True)

        cmp_info = resolve_software_target(cdir, compare_spec, role="compare") if compare_spec.strip() else sw_info
        cmp_path = Path(cmp_info["path"])

        paper_info: Optional[Dict[str, Any]] = None
        resolved_paper_for_map: Optional[Path] = None
        if mode == "paper" or paper_spec.strip():
            paper_info = resolve_paper_source(cdir, paper_spec)
            p_str = str(paper_info.get("primary_tex") or paper_info.get("path") or "").strip()
            if p_str and Path(p_str).exists():
                resolved_paper_for_map = Path(p_str).resolve()

        # Single full-repo AST scan for sw_path; reuse `code_map` across all downstream steps!
        try:
            code_map = anvil_engine.build_map(sw_path, _include_v2_enrichment=False, paper_path=resolved_paper_for_map)
        except TypeError:
            code_map = anvil_engine.build_map(sw_path)
        cmp_map = code_map if sw_path == cmp_path else None
        if cmp_map is None:
            try:
                cmp_map = anvil_engine.build_map(cmp_path, _include_v2_enrichment=False, paper_path=resolved_paper_for_map)
            except TypeError:
                cmp_map = anvil_engine.build_map(cmp_path)

        if not (code_map.get("conceptual_buckets") or []):
            extra_buckets = _scan_non_python_buckets(sw_path, start_idx=1)
            for eb in extra_buckets:
                code_map["conceptual_buckets"].append(eb)
                code_map["process_map"]["nodes"].append({
                    "id": eb["id"],
                    "title": eb["title"],
                    "file": eb["file"],
                    "stage": eb["pipeline_stage"],
                    "ai_agent_badge": eb["ai_agent_touchpoints"][0]["badge"] if eb["ai_agent_touchpoints"] else None,
                    "function_count": len(eb["functions"]),
                })

        _enrich_buckets_with_previews(sw_path, code_map.get("conceptual_buckets") or [])

        try:
            orange_split = anvil_engine.extract_orange_split(sw_path, code_map=code_map)
        except TypeError:
            orange_split = anvil_engine.extract_orange_split(sw_path)
        signed_list = list(signed_off_drops) if signed_off_drops is not None else prior_signed
        try:
            remap = anvil_engine.remap_code(
                sw_path,
                cmp_path,
                signed_off_drops=signed_list,
                old_map=code_map,
                new_map=cmp_map,
            )
        except TypeError:
            remap = anvil_engine.remap_code(sw_path, cmp_path, signed_off_drops=signed_list)

        if sw_path == cmp_path and not (remap.get("null_space") or {}).get("items"):
            pith_items = []
            for p in orange_split.get("pith_and_seeds") or []:
                fname = p["name"]
                short = fname.split(".")[-1]
                disp = (
                    "intentional_drop_signed_off"
                    if (fname in signed_list or short in signed_list)
                    else "accidental_omission_blocker"
                )
                pith_items.append({
                    "old_function": fname,
                    "old_file": p.get("file", ""),
                    "summary": p.get("summary", "Truly unreferenced candidate"),
                    "stage": p.get("stage", "compute"),
                    "disposition": disp,
                })
            blockers = [it for it in pith_items if it["disposition"] == "accidental_omission_blocker"]
            remap["null_space"] = {
                "count": len(pith_items),
                "unexplained_blockers": len(blockers),
                "items": pith_items,
            }
            stages_ok = all(
                v.get("status") == "PASS"
                for v in (remap.get("pipeline_validation") or {}).values()
            )
            remap["verdict"] = "PASS" if (not blockers and stages_ok) else "NEEDS_REVIEW"

        remap["best_in_class_map"] = _build_best_in_class_remap(sw_path, cmp_path, code_map, orange_split, remap)

        paper_map = None
        if mode == "paper" or paper_spec.strip():
            if paper_info is None:
                paper_info = resolve_paper_source(cdir, paper_spec)
            paper_map = extract_paper_claims_and_align(
                sw_path,
                code_map.get("conceptual_buckets") or [],
                paper_info,
                code_map=code_map,
            )

        now_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        buckets = code_map.get("conceptual_buckets") or []
        if hasattr(anvil_engine, "_enrich_progressive_levels"):
            anvil_engine._enrich_progressive_levels(sw_path, buckets, paper_map=paper_map, remap=remap)
        beta_reader_panel = (
            anvil_engine.run_beta_reader_panel(sw_path, code_map=code_map, orange_split=orange_split, remap=remap)
            if hasattr(anvil_engine, "run_beta_reader_panel")
            else {}
        )
        if hasattr(anvil_engine, "run_code_walkthrough"):
            try:
                walkthrough_trace = anvil_engine.run_code_walkthrough(
                    sw_path,
                    code_map=code_map,
                    block_id=buckets[0]["id"] if buckets else "",
                )
            except TypeError:
                walkthrough_trace = anvil_engine.run_code_walkthrough(
                    sw_path,
                    block_id=buckets[0]["id"] if buckets else "",
                )
        else:
            walkthrough_trace = {}
        first_block = buckets[0]["title"] if buckets else sw_info["label"]
        total_fns = sum(len(b.get("functions") or []) for b in buckets)
        total_mods = len(code_map.get("module_buckets") or buckets)
        seating = _read_model_seating_info()

        paper_sentence = ""
        if isinstance(paper_map, dict):
            sc = paper_map.get("summary_counts") or {}
            sec_n = sc.get("sections", len(paper_map.get("sections") or []))
            alg_n = sc.get("algorithms", len(paper_map.get("algorithms") or []))
            eq_n = sc.get("equations", paper_map.get("claims_mapped", 0))
            paper_sentence = (
                f"Attached paper **{paper_map.get('paper_title')}** (`{sec_n}` sections, "
                f"`{alg_n}` algorithm(s), `{eq_n}` native MathML equations). "
            )

        greeting = (
            f"Mapped `{sw_info['label']}` (`{total_mods}` source files, `{total_fns}` functions) into "
            f"**{len(buckets)} clustered architectural module(s)** "
            f"(`{orange_split.get('counts', {}).get('juice_count', 0)}` Essential Core functions, "
            f"`{orange_split.get('counts', {}).get('peel_count', 0)}` I/O contracts, and "
            f"`{orange_split.get('counts', {}).get('pith_and_seeds_count', 0)}` truly unreferenced `∅ Null Space` candidates). "
            + paper_sentence
            + f"Coding seat: **{seating['coding_short']}**; cross-family review seat: **{seating['review_short']}**. "
            "Ask about any symbol, module, caller/callee edge, security finding, or paper equation/algorithm."
        )

        session: Dict[str, Any] = {
            "schema": "anvil-cockpit-session/v1",
            "active": True,
            "cockpit_dir": str(cdir),
            "cockpit_name": cockpit_name,
            "mode": "paper" if paper_map and mode == "paper" else "code",
            "created_at": now_iso,
            "updated_at": now_iso,
            "software": sw_info,
            "compare_software": cmp_info,
            "signed_off_drops": signed_list,
            "code_map": code_map,
            "orange_split": orange_split,
            "remap": remap,
            "paper_map": paper_map,
            "beta_reader_panel": beta_reader_panel,
            "walkthrough_trace": walkthrough_trace,
            "selected_block_id": buckets[0]["id"] if buckets else "",
            "chat_history": [
                {
                    "role": "anvil",
                    "mode": "paper-map" if paper_map else "map",
                    "target": first_block,
                    "text": greeting,
                    "answer_mode": "static_ast",
                    "at": now_iso,
                }
            ],
        }

        _write_session_ir(sfile, session)
        _write_anvil_manifest(cdir, session)
        _write_anvil_report(cdir, session)
        return get_session_status(cdir)


def _is_placeholder_model_label(label: str) -> bool:
    low = (label or "").strip().lower()
    return not low or any(tok in low for tok in ("-argon", "-sol"))


def _read_model_seating_info() -> Dict[str, str]:
    """Read real configured Anchor model seating from preferences, env, and in-memory CLI capabilities."""
    coding_fam = "gemini"
    review_fam = "claude"
    steward = "aladdin"
    explicit_coding_model = ""
    explicit_review_model = ""

    pref_candidates: List[Path] = []
    try:
        import paths as _paths
        pref_candidates.append(_paths.data_dir() / ".anchor" / "model_prefs.json")
    except Exception:
        pass
    try:
        pref_candidates.append(Path.home() / ".anchor" / "model_prefs.json")
    except Exception:
        pass

    for prefs_path in pref_candidates:
        try:
            if prefs_path.is_file():
                data = json.loads(prefs_path.read_text(encoding="utf-8", errors="replace"))
                if isinstance(data, dict):
                    coding_fam = str(data.get("coding_family") or data.get("default_cli") or coding_fam).lower()
                    review_fam = str(data.get("review_family") or review_fam).lower()
                    steward = str(data.get("steward_type") or steward).lower()
                    cm = str(data.get("coding_model") or "").strip()
                    rm = str(data.get("review_model") or "").strip()
                    if cm and not _is_placeholder_model_label(cm):
                        explicit_coding_model = cm
                    if rm and not _is_placeholder_model_label(rm):
                        explicit_review_model = rm
                break
        except Exception:
            continue

    frontier_defaults = {
        "gemini": "gemini · latest_supported · high",
        "claude": "claude · latest_supported · max",
        "chatgpt": "chatgpt · latest_supported · xhigh",
        "codex": "codex · latest_supported · xhigh",
        "grok": "grok · latest_supported · high",
    }

    # Consult live in-memory model_policy cache if already populated (zero subprocesses spawned)
    try:
        import model_policy as _mp
        mem = getattr(_mp, "_MEMORY", None)
        if isinstance(mem, dict):
            for entry in mem.values():
                if isinstance(entry, dict) and entry.get("family") and entry.get("model"):
                    fam_k = str(entry["family"]).lower()
                    mdl = str(entry["model"]).strip()
                    eff = str(entry.get("effort") or "high").strip()
                    if not _is_placeholder_model_label(mdl):
                        frontier_defaults[fam_k] = f"{mdl} · {eff}"
    except Exception:
        pass

    for env_key, fam_key in (
        ("GEMINI_MODEL", "gemini"),
        ("CLAUDE_MODEL", "claude"),
        ("TRIO_MODEL", coding_fam),
    ):
        env_val = (os.environ.get(env_key) or "").strip()
        if env_val and not _is_placeholder_model_label(env_val):
            frontier_defaults[fam_key] = env_val if "·" in env_val else f"{env_val} · high"

    cli_transports = {
        "gemini": "via `agy` subscription CLI",
        "claude": "via `claude.exe` subscription CLI",
        "chatgpt": "via `codex` subscription CLI",
        "codex": "via `codex` subscription CLI",
        "grok": "via `grok` subscription CLI",
    }
    coding_short = explicit_coding_model or frontier_defaults.get(coding_fam, f"{coding_fam} · latest_supported")
    review_short = explicit_review_model or frontier_defaults.get(review_fam, f"{review_fam} · latest_supported")
    coding_label = f"{coding_short} ({cli_transports.get(coding_fam, 'via subscription CLI')})"
    cross_ok = coding_fam != review_fam
    review_label = (
        f"{review_short} ({cli_transports.get(review_fam, 'via subscription CLI')}, "
        f"`cross_model: {str(cross_ok).lower()}`)"
    )
    coding_parts = [p.strip() for p in coding_short.split("·")]
    review_parts = [p.strip() for p in review_short.split("·")]
    return {
        "coding_family": coding_fam,
        "review_family": review_fam,
        "steward_type": steward.title(),
        "coding_short": coding_short,
        "review_short": review_short,
        "coding_model_id": coding_parts[0] if coding_parts else coding_fam,
        "coding_effort": coding_parts[-1] if len(coding_parts) > 1 else "high",
        "review_model_id": review_parts[0] if review_parts else review_fam,
        "review_effort": review_parts[-1] if len(review_parts) > 1 else "max",
        "coding_label": coding_label,
        "review_label": review_label,
    }


def _verify_all_buckets_in_place(session: Dict[str, Any], cdir: Path) -> Tuple[int, int]:
    """Check static syntax/bytecode and isolated runtime walkthrough per bucket honestly (`EXECUTED_PASS` vs `STATIC_ONLY`)."""
    buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
    sw_path = Path((session.get("software") or {}).get("path") or cdir)
    base_dir = sw_path.parent if sw_path.is_file() else sw_path
    now_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    newly_probed = 0
    total_executed = 0

    for b in buckets:
        if b.get("validated"):
            total_executed += 1
            continue
        member_rel = list(b.get("member_files") or [])
        if not member_rel:
            single = b.get("primary_file") or b.get("file") or ""
            if single:
                member_rel = [single]
        compiled = 0
        passed = True
        notes: List[str] = []
        for rel_f in member_rel:
            tf = (base_dir / rel_f).resolve()
            if tf.is_file() and not tf.is_symlink() and tf.suffix.lower() == ".py":
                try:
                    src = tf.read_text(encoding="utf-8", errors="replace")
                    tree = ast.parse(src, filename=tf.name)
                    compile(tree, filename=tf.name, mode="exec")
                    compiled += 1
                except Exception as exc:
                    passed = False
                    notes.append(f"✗ Syntax error in {tf.name}: {exc}")

        executed_ok = False
        if passed and anvil_engine is not None and hasattr(anvil_engine, "run_code_walkthrough"):
            try:
                wt = anvil_engine.run_code_walkthrough(
                    sw_path,
                    code_map=session.get("code_map"),
                    block_id=str(b.get("id") or ""),
                )
                verdict = str(wt.get("overall_verdict") or "")
                if verdict == "EXECUTED_PASS" or bool(wt.get("accurate_execution")):
                    executed_ok = True
                    notes.append(f"✓ Isolated child-subprocess runtime walkthrough: EXECUTED_PASS.")
                elif verdict in ("DIVERGENCE", "MISMATCH"):
                    passed = False
                    notes.append(f"✗ Isolated runtime walkthrough reported {verdict}.")
            except Exception:
                pass

        if not passed:
            b["static_syntax_ok"] = False
            b["validated"] = False
            b["empirical_validation"] = {
                "ran": True,
                "status": "DIVERGENCE",
                "checked_at": now_iso,
                "stdout": "\n".join(notes) or "✗ Static or runtime check failed.",
            }
            newly_probed += 1
        elif executed_ok:
            if compiled > 0:
                notes.insert(0, f"✓ AST parse & bytecode compile passed across {compiled} Python module(s).")
            b["static_syntax_ok"] = True
            b["validated"] = True
            b["validated_description"] = b.get("validated_description") or b.get("summary")
            b["empirical_validation"] = {
                "ran": True,
                "status": "EXECUTED_PASS",
                "checked_at": now_iso,
                "stdout": "\n".join(notes),
            }
            newly_probed += 1
            total_executed += 1
        else:
            if compiled > 0:
                notes.append(
                    f"✓ Static AST parse & bytecode compile passed across {compiled} Python module(s) (no runtime test executed yet)."
                )
            else:
                notes.append("ℹ Static module scan complete; no runtime test executed yet.")
            b["static_syntax_ok"] = passed
            b["validated"] = False
            b["empirical_validation"] = {
                "ran": False,
                "status": "STATIC_ONLY",
                "checked_at": now_iso,
                "stdout": "\n".join(notes),
            }
            newly_probed += 1
    return newly_probed, total_executed


def _load_active_cockpit_session_dict(cdir: Path, *, strict: bool = False) -> Optional[Dict[str, Any]]:
    sfile = _session_file(cdir)
    if not sfile.exists():
        return None
    if sfile.is_symlink() or not sfile.is_file():
        if strict:
            raise ValueError("Corrupt or non-regular .anvil/session.json")
        return None
    try:
        loaded = _read_session_ir(sfile)
        if isinstance(loaded, dict) and loaded.get("active"):
            return loaded
    except Exception as exc:
        if strict:
            raise ValueError(f"Corrupt or unreadable .anvil/session.json: {exc}") from exc
        return None
    return None


def save_v4_cockpit_ui_session(
    cockpit_dir: str | Path,
    patch: Dict[str, Any],
) -> Tuple[Dict[str, Any], int]:
    """Validate and atomically merge client UI session patch into `<cdir>/.anvil/v4/workbench_session.json`."""
    if not isinstance(patch, dict):
        return (
            {
                "ok": False,
                "error_code": "MALFORMED_DATA_REFUSED",
                "error": "JSON object body required.",
                "message": "JSON object body required.",
            },
            400,
        )
    if "pinned_watches" in patch:
        pw = patch["pinned_watches"]
        if not isinstance(pw, list) or any(not isinstance(x, str) for x in pw):
            return (
                {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "'pinned_watches' must be a list of strings.", "message": "'pinned_watches' must be a list of strings."},
                400,
            )
        if len(pw) > 64:
            return (
                {"ok": False, "error_code": "BOUND_EXCEEDED_REFUSAL", "error": "'pinned_watches' exceeds 64 items.", "message": "'pinned_watches' exceeds 64 items."},
                400,
            )
    if "breakpoints" in patch:
        bps = patch["breakpoints"]
        if not isinstance(bps, list):
            return (
                {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "'breakpoints' must be a list.", "message": "'breakpoints' must be a list."},
                400,
            )
        if len(bps) > 128:
            return (
                {"ok": False, "error_code": "BOUND_EXCEEDED_REFUSAL", "error": "'breakpoints' exceeds 128 items.", "message": "'breakpoints' exceeds 128 items."},
                400,
            )
        for bp in bps:
            valid_bp = (
                (isinstance(bp, int) and not isinstance(bp, bool) and bp >= 1)
                or (isinstance(bp, str) and bool(bp.strip()))
                or (
                    isinstance(bp, dict)
                    and isinstance(bp.get("file"), str)
                    and isinstance(bp.get("line"), int)
                    and not isinstance(bp.get("line"), bool)
                    and bp["line"] >= 1
                )
            )
            if not valid_bp:
                return (
                    {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "Invalid breakpoint item in 'breakpoints'.", "message": "Invalid breakpoint item in 'breakpoints'."},
                    400,
                )
    if "active_line" in patch:
        aln = patch["active_line"]
        if isinstance(aln, bool) or not isinstance(aln, int) or aln < 1 or aln > 1_000_000:
            code_str = "BOUND_EXCEEDED_REFUSAL" if (isinstance(aln, int) and not isinstance(aln, bool)) else "MALFORMED_DATA_REFUSED"
            return (
                {"ok": False, "error_code": code_str, "error": "'active_line' must be an integer in 1..1000000.", "message": "'active_line' must be an integer in 1..1000000."},
                400,
            )
    if "ide_open" in patch and not isinstance(patch["ide_open"], bool):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "'ide_open' must be a boolean.", "message": "'ide_open' must be a boolean."},
            400,
        )
    if "ide_theme" in patch and patch["ide_theme"] not in {"light", "dark"}:
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "'ide_theme' must be 'light' or 'dark'.", "message": "'ide_theme' must be 'light' or 'dark'."},
            400,
        )
    for str_key in ("active_stage_id", "active_step_id", "active_file", "active_pipeline"):
        if str_key in patch and not isinstance(patch[str_key], str):
            return (
                {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": f"'{str_key}' must be a string.", "message": f"'{str_key}' must be a string."},
                400,
            )

    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        return (
            {"ok": False, "error_code": "DEPENDENCY_MISSING", "message": "Required runtime/tracer unavailable — showing static AST map"},
            503,
        )
    v4_proc = v4_mods["anvil_v4_process"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    with _get_cockpit_lock(cdir):
        try:
            ws_dir = v4_wb._probe_v4_store_dir(cdir)
            ws_path = ws_dir / "workbench_session.json"
            if v4_proc._is_link_or_junction(ws_path):
                v4_wb._raise_backing_store_unreadable("workbench_session.json is a symlink or junction")
            if ws_path.exists() and not ws_path.is_file():
                v4_wb._raise_backing_store_unreadable("workbench_session.json is not a regular file")
            cached_pm = None
            with _COCKPIT_V4_BUNDLE_CACHE_LOCK:
                for ck, cv in reversed(list(_COCKPIT_V4_BUNDLE_CACHE.items())):
                    if ck and ck[0] == str(cdir) and isinstance(cv.get("process_map"), dict):
                        cached_pm = cv["process_map"]
                        break
            fallback_defaults = (
                v4_wb._default_session_payload(cached_pm)
                if cached_pm is not None
                else v4_wb._default_session_payload({"l1_stages": [], "l2_steps": [], "l3_files": []})
            )
            if ws_path.is_file():
                raw_cur = v4_proc.atomic_locked_read_json(ws_path, max_bytes=4_194_304)
                current = v4_wb._validate_and_normalize_session(raw_cur, fallback_defaults)
            else:
                current = dict(fallback_defaults)
            merged = dict(current)
            for k in (
                "pinned_watches",
                "breakpoints",
                "active_stage_id",
                "active_step_id",
                "active_file",
                "active_line",
                "ide_open",
                "ide_theme",
                "active_pipeline",
            ):
                if k in patch:
                    merged[k] = patch[k]
            norm_v4_sess = v4_wb._validate_and_normalize_session(
                merged,
                fallback_defaults,
            )
            v4_proc.atomic_locked_write_json(ws_path, norm_v4_sess)
            # Strictly isolate UI clicks/theme/watch updates to workbench_session.json — NEVER rewrite .anvil/session.json!
            with _COCKPIT_V4_BUNDLE_CACHE_LOCK:
                for ck, cv in list(_COCKPIT_V4_BUNDLE_CACHE.items()):
                    if ck and ck[0] == str(cdir):
                        cv["session"] = norm_v4_sess
            return ({"ok": True, "session": norm_v4_sess}, 200)
        except v4_proc.AnvilRefusalError as err:
            return _v4_refusal_to_failure_payload(err, v4_wb)


def _validate_v4_exec_request(
    sw_dir: Path,
    body: Dict[str, Any],
    v4_mods: Dict[str, Any],
) -> Tuple[Optional[Tuple[List[str], float]], Optional[Tuple[Dict[str, Any], int]]]:
    v4_proc = v4_mods["anvil_v4_process"]
    v4_trace = v4_mods["anvil_v4_trace"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    if not isinstance(body, dict):
        return None, (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "JSON object body required.", "message": "JSON object body required."},
            400,
        )
    if "cmd" in body or "command" in body or "shell" in body:
        return None, (
            {
                "ok": False,
                "error_code": "EXECUTION_POLICY_REFUSED",
                "cwe": "CWE-78",
                "error": "Shell command strings ('cmd'/'command'/'shell') are strictly refused; pass an explicit 'argv' array.",
                "message": "Shell command strings ('cmd'/'command'/'shell') are strictly refused; pass an explicit 'argv' array.",
            },
            403,
        )
    raw_argv = body.get("argv")
    if isinstance(raw_argv, (str, bytes)) or not isinstance(raw_argv, list) or len(raw_argv) == 0:
        return None, (
            {
                "ok": False,
                "error_code": "EXECUTION_POLICY_REFUSED",
                "cwe": "CWE-78",
                "error": "Execution requires a non-empty JSON 'argv' list of strings.",
                "message": "Execution requires a non-empty JSON 'argv' list of strings.",
            },
            403,
        )
    if body.get("operator_consent_confirmed") is not True:
        return None, (
            {
                "ok": False,
                "error_code": "CONSENT_REQUIRED_REFUSED",
                "error": "Explicit operator_consent_confirmed: true from UI consent gate is required.",
                "message": "Explicit operator_consent_confirmed: true from UI consent gate is required.",
                "isolation_boundary": v4_trace.ISOLATION_BOUNDARY,
                "non_vm_trust_warning": v4_trace.NON_VM_TRUST_WARNING,
            },
            403,
        )
    try:
        v4_trace.validate_execution_argv(sw_dir, raw_argv)
    except v4_proc.AnvilRefusalError as pol_err:
        if pol_err.error_code == "DEPENDENCY_MISSING":
            return None, _v4_refusal_to_failure_payload(pol_err, v4_wb)
        err_d = pol_err.to_dict()
        err_d.setdefault("error", err_d.get("message", "Execution policy refused."))
        return None, (err_d, 403)

    raw_to = body.get("timeout_sec", 30.0)
    if isinstance(raw_to, bool) or not isinstance(raw_to, (int, float)) or not math.isfinite(float(raw_to)):
        return None, (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "error": "'timeout_sec' must be a finite number.", "message": "'timeout_sec' must be a finite number."},
            400,
        )
    timeout_sec = float(raw_to)
    if timeout_sec <= 0.0 or timeout_sec > 300.0:
        return None, (
            {
                "ok": False,
                "error_code": "BOUND_EXCEEDED_REFUSAL",
                "error": "'timeout_sec' must be within (0, 300.0].",
                "message": "'timeout_sec' must be within (0, 300.0].",
                "bound_name": "timeout_sec",
                "bound_limit": 300.0,
                "observed_value": timeout_sec,
            },
            400,
        )
    return ([str(x) for x in raw_argv], timeout_sec), None


def run_v4_cockpit_trace(
    cockpit_dir: str | Path,
    body: Dict[str, Any],
) -> Tuple[Dict[str, Any], int]:
    """Execute a consented Anvil v4 subprocess trace in an isolated temp copy, writing strictly under `<cdir>/.anvil/v4`."""
    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        return (
            {"ok": False, "error_code": "DEPENDENCY_MISSING", "status_kind": "dependency-missing", "http_status": 503, "badge": "DEGRADED_STATIC", "message": "Required runtime/tracer unavailable — showing static AST map"},
            503,
        )
    v4_proc = v4_mods["anvil_v4_process"]
    v4_trace = v4_mods["anvil_v4_trace"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    with _get_cockpit_lock(cdir):
        session = _load_active_cockpit_session_dict(cdir)
        sw_dir = _resolve_session_sw_dir(cdir, session)
        validated, err_resp = _validate_v4_exec_request(sw_dir, body, v4_mods)
        if err_resp is not None or validated is None:
            return err_resp or ({"ok": False, "error_code": "EXECUTION_POLICY_REFUSED", "message": "Invalid execution request."}, 403)
        clean_argv, timeout_sec = validated

        try:
            cand_paper = _resolve_session_paper_path(cdir, session)
            proc_map = v4_proc.build_process_map(sw_dir, persist=False, paper_path=cand_paper)
            v4_sess = v4_wb._load_or_init_workbench_session(cdir, proc_map, persist=True)
            active_pipe = str(v4_sess.get("active_pipeline") or "").strip() or None
            if active_pipe:
                try:
                    proc_map = v4_proc.build_process_map(sw_dir, persist=False, paper_path=cand_paper, pipeline_id=active_pipe)
                except v4_proc.AnvilRefusalError:
                    active_pipe = None
            req_pins = body.get("pinned_watches")
            pins = (
                [str(x).strip() for x in req_pins if isinstance(x, str) and x.strip()][:64]
                if isinstance(req_pins, list)
                else list(v4_sess.get("pinned_watches") or [])
            )
            trace_out_path = _v4_dir(cdir) / "last_trace.json"
            trace_doc = v4_trace.run_consented_trace(
                sw_dir,
                clean_argv,
                approve_run=True,
                timeout_sec=timeout_sec,
                pinned_watches=pins,
                output_path=trace_out_path,
                persist=False,
                paper_path=cand_paper,
                pipeline_id=active_pipe,
                static_map=proc_map,
            )
            xval_p = _v4_dir(cdir) / "xval_receipt.json"
            if xval_p.is_file():
                try:
                    xval_p.unlink()
                except OSError:
                    pass

            now_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            if session is not None:
                exec_files = {
                    str(el.get("file") or "")
                    for el in (trace_doc.get("executed_lines") or [])
                    if isinstance(el, dict) and el.get("file")
                }
                tw_files = {
                    str(tw.get("file") or "")
                    for tw in (trace_doc.get("tripwires") or [])
                    if isinstance(tw, dict) and tw.get("file")
                }
                rc_zero = int(trace_doc.get("returncode", 1)) == 0
                zero_tw = len(trace_doc.get("tripwires") or []) == 0 and trace_doc.get("uncaught_exception") is None
                trace_clean = rc_zero and zero_tw

                buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
                for b in buckets:
                    b_files = set(b.get("member_files") or [])
                    single_f = b.get("primary_file") or b.get("file") or ""
                    if single_f:
                        b_files.add(str(single_f))
                    hit_bucket = bool(b_files & (exec_files | tw_files)) or (not trace_clean and not exec_files)
                    if not hit_bucket:
                        continue
                    if trace_clean and not (b_files & tw_files):
                        b["static_syntax_ok"] = True
                        b["validated"] = True
                        b["validated_description"] = b.get("validated_description") or b.get("summary")
                        b["empirical_validation"] = {
                            "ran": True,
                            "status": "EXECUTED_PASS",
                            "checked_at": now_iso,
                            "stdout": f"✓ Consented v4 subprocess trace exited 0 across {len(exec_files)} file(s) with 0 tripwires.",
                        }
                    else:
                        b["validated"] = False
                        b["empirical_validation"] = {
                            "ran": True,
                            "status": "DIVERGENCE",
                            "checked_at": now_iso,
                            "stdout": f"✗ Consented v4 subprocess trace reported divergence (returncode={trace_doc.get('returncode')}, tripwires={len(trace_doc.get('tripwires') or [])}).",
                        }
                paper_map = session.get("paper_map")
                if isinstance(paper_map, dict):
                    valid_bids = {b["id"] for b in buckets if b.get("validated")}
                    for al in paper_map.get("alignments") or []:
                        if al.get("bucket_id") in valid_bids and al.get("mapped_function"):
                            al["empirical_status"] = "EXECUTED_PASS"
                session["updated_at"] = now_iso
                _write_session_ir(_session_file(cdir), session)
                _write_anvil_manifest(cdir, session)
                _write_anvil_report(cdir, session)

            v4_bundle = _build_cockpit_v4_bundle(cdir, session or {"software": {"path": str(sw_dir)}})
            return (
                {
                    "ok": True,
                    "trace_ok": bool(trace_doc.get("ok", True)),
                    "trace_summary": v4_bundle.get("trace_summary"),
                    "v4_bundle": v4_bundle,
                    "bundle": v4_bundle,
                    "session": session,
                },
                200,
            )
        except v4_proc.AnvilRefusalError as err:
            fallback_b: Optional[Dict[str, Any]] = None
            if err.error_code in {"DEPENDENCY_MISSING", "TRACE_TIMEOUT_REFUSED"} and session is not None:
                try:
                    fallback_b = _build_cockpit_v4_bundle(cdir, session)
                except Exception:
                    fallback_b = None
            return _v4_refusal_to_failure_payload(err, v4_wb, fallback_bundle=fallback_b)


def run_v4_cockpit_profile_lit(
    cockpit_dir: str | Path,
    body: Dict[str, Any],
) -> Tuple[Dict[str, Any], int]:
    """Execute a consented untraced stage profile + literature check, writing strictly under `<cdir>/.anvil/v4`."""
    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        return (
            {"ok": False, "error_code": "DEPENDENCY_MISSING", "status_kind": "dependency-missing", "http_status": 503, "badge": "DEGRADED_STATIC", "message": "Required runtime/tracer unavailable — showing static AST map"},
            503,
        )
    v4_proc = v4_mods["anvil_v4_process"]
    v4_ref = v4_mods["anvil_v4_refactor"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    with _get_cockpit_lock(cdir):
        session = _load_active_cockpit_session_dict(cdir)
        sw_dir = _resolve_session_sw_dir(cdir, session)
        validated, err_resp = _validate_v4_exec_request(sw_dir, body, v4_mods)
        if err_resp is not None or validated is None:
            return err_resp or ({"ok": False, "error_code": "EXECUTION_POLICY_REFUSED", "message": "Invalid execution request."}, 403)
        clean_argv, timeout_sec = validated

        try:
            prof_doc = v4_ref.run_profile_and_literature(
                sw_dir,
                approve_run=True,
                argv=clean_argv,
                timeout_sec=timeout_sec,
                persist=False,
            )
            v4_proc.atomic_locked_write_json(_v4_dir(cdir) / "profile_lit.json", prof_doc)
            if session is not None:
                session["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                _write_session_ir(_session_file(cdir), session)
            v4_bundle = _build_cockpit_v4_bundle(cdir, session or {"software": {"path": str(sw_dir)}})
            return (
                {
                    "ok": True,
                    "profile_lit": prof_doc,
                    "v4_bundle": v4_bundle,
                    "bundle": v4_bundle,
                    "session": session,
                },
                200,
            )
        except v4_proc.AnvilRefusalError as err:
            fallback_b: Optional[Dict[str, Any]] = None
            if err.error_code in {"DEPENDENCY_MISSING", "TRACE_TIMEOUT_REFUSED"} and session is not None:
                try:
                    fallback_b = _build_cockpit_v4_bundle(cdir, session)
                except Exception:
                    fallback_b = None
            return _v4_refusal_to_failure_payload(err, v4_wb, fallback_bundle=fallback_b)


def run_v4_cockpit_xval(
    cockpit_dir: str | Path,
    body: Optional[Dict[str, Any]] = None,
    *,
    cli_runner: Optional[Any] = None,
    seat1_cli_argv: Optional[Sequence[str]] = None,
    seat2_cli_argv: Optional[Sequence[str]] = None,
    raw_digest_override: Optional[Any] = None,
    enforce_bound: bool = True,
) -> Tuple[Dict[str, Any], int]:
    """Run bounded 2-seat Cross-Validator (`max_concurrency <= 2`, `digest_bytes <= 32768`) with
    per-divergence code + manuscript citation auditing and positive `claude-fable-5-2` + `gemini` attestation.
    """
    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        return (
            {
                "ok": False,
                "error_code": "DEPENDENCY_MISSING",
                "status_kind": "dependency-missing",
                "http_status": 503,
                "badge": "DEGRADED_STATIC",
                "message": "Required runtime/tracer unavailable — showing static AST map",
            },
            503,
        )
    v4_proc = v4_mods["anvil_v4_process"]
    v4_xval = v4_mods["anvil_v4_xval"]
    v4_wb = v4_mods["anvil_v4_workbench"]
    if body is not None and not isinstance(body, dict):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "JSON object body required.", "error": "JSON object body required."},
            400,
        )
    req = body if isinstance(body, dict) else {}

    if any(k in req for k in ("seat1_cli_argv", "seat2_cli_argv", "cli_argv", "raw_digest_override", "enforce_bound")):
        return (
            {
                "ok": False,
                "error_code": "EXECUTION_POLICY_REFUSED",
                "cwe": "CWE-78",
                "message": "Custom CLI argv and digest/bound overrides are forbidden in HTTP request bodies.",
                "error": "Custom CLI argv and digest/bound overrides are forbidden in HTTP request bodies.",
            },
            403,
        )

    max_conc = req.get("max_concurrency", 2)
    if isinstance(max_conc, bool) or not isinstance(max_conc, int):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'max_concurrency' must be an integer.", "error": "'max_concurrency' must be an integer."},
            400,
        )
    max_dig = req.get("max_digest_bytes", v4_xval.MAX_XVAL_DIGEST_BYTES)
    if isinstance(max_dig, bool) or not isinstance(max_dig, int):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'max_digest_bytes' must be an integer.", "error": "'max_digest_bytes' must be an integer."},
            400,
        )
    timeout_sec = req.get("timeout_sec", v4_xval.MAX_XVAL_TIMEOUT_SEC)
    if isinstance(timeout_sec, bool) or not isinstance(timeout_sec, (int, float)) or not math.isfinite(float(timeout_sec)):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'timeout_sec' must be a finite number.", "error": "'timeout_sec' must be a finite number."},
            400,
        )
    live_flag = req.get("live")
    if live_flag is not None and not isinstance(live_flag, bool):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'live' must be a boolean when provided.", "error": "'live' must be a boolean when provided."},
            400,
        )
    s1_argv = list(seat1_cli_argv) if seat1_cli_argv is not None else None
    s2_argv = list(seat2_cli_argv) if seat2_cli_argv is not None else None

    try:
        with _get_cockpit_lock(cdir):
            try:
                session = _load_active_cockpit_session_dict(cdir, strict=True)
            except Exception as s_exc:
                v4_wb._raise_backing_store_unreadable(str(s_exc))
            sw_dir = _resolve_session_sw_dir(cdir, session)
            cand_paper = _resolve_session_paper_path(cdir, session)
            v4_bundle = _build_cockpit_v4_bundle(cdir, session or {"software": {"path": str(sw_dir)}})
            proc_map = v4_bundle["process_map"]
            ref_map = v4_bundle["refactor_map"]
            raw_pap = v4_bundle.get("paper_map")
            pap_arg = raw_pap if isinstance(raw_pap, dict) and raw_pap.get("has_paper") else None

        # Release cockpit lock while bounded 2-seat XVal CLI subprocesses run
        raw_receipt = v4_xval.run_xval_audit(
            sw_dir,
            process_map=proc_map,
            refactor_map=ref_map,
            paper_map=pap_arg,
            paper_path=cand_paper,
            max_concurrency=max_conc,
            max_digest_bytes=max_dig,
            timeout_sec=float(timeout_sec),
            persist=False,
            live=live_flag,
            cli_runner=cli_runner,
            seat1_cli_argv=s1_argv,
            seat2_cli_argv=s2_argv,
            raw_digest_override=raw_digest_override,
            enforce_bound=bool(enforce_bound),
        )

        with _get_cockpit_lock(cdir):
            seating = _read_model_seating_info()
            receipt = _stamp_cockpit_xval_seating(raw_receipt, seating)
            v4_proc.atomic_locked_write_json(_v4_dir(cdir) / "xval_receipt.json", receipt)
            with _COCKPIT_V4_BUNDLE_CACHE_LOCK:
                _COCKPIT_V4_BUNDLE_CACHE.clear()
            return ({"ok": True, "xval_receipt": receipt}, 200)
    except v4_proc.AnvilRefusalError as err:
        if err.error_code == "ATTESTATION_MISMATCH_REFUSAL":
            return (err.to_dict(), 502)
        if err.error_code == "BOUND_EXCEEDED_REFUSAL":
            status_c = 413 if err.details.get("bound_name") == "max_digest_bytes" else 400
            return (err.to_dict(), status_c)
        return _v4_refusal_to_failure_payload(err, v4_wb)


def run_v4_cockpit_chat(
    cockpit_dir: str | Path,
    body: Dict[str, Any],
    *,
    cli_runner: Optional[Any] = None,
    cli_argv: Optional[Sequence[str]] = None,
) -> Tuple[Dict[str, Any], int]:
    """Execute a grounded Steward Co-Pilot v4/v5 turn (`S1..Sk -> N1..Nk`, Smart Funnel,
    tripwires, and `[data-divergence-panel]` citations) via live subscription CLI when enabled
    (`live=True` outside hermetic pytest or `ANCHOR_TESTS_ALLOW_LIVE == "1"`) or fast deterministic
    AST/trace synthesis under hermetic tests.
    """
    if not isinstance(body, dict):
        return ({"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "JSON object body required."}, 400)
    if any(k in body for k in ("cli_argv", "seat1_cli_argv", "seat2_cli_argv")):
        return (
            {
                "ok": False,
                "error_code": "EXECUTION_POLICY_REFUSED",
                "cwe": "CWE-78",
                "message": "Custom CLI argv injection is forbidden in HTTP request bodies.",
                "error": "Custom CLI argv injection is forbidden in HTTP request bodies.",
            },
            403,
        )
    question = body.get("question")
    if not isinstance(question, str) or not question.strip():
        return ({"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "Non-empty 'question' string required."}, 400)
    if len(question) > 4096:
        return ({"ok": False, "error_code": "BOUND_EXCEEDED_REFUSAL", "message": "'question' exceeds 4096 characters."}, 400)
    if "active_line" in body and body["active_line"] is not None:
        aln = body["active_line"]
        if isinstance(aln, bool) or not isinstance(aln, int) or aln < 1 or aln > 1_000_000:
            return (
                {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'active_line' must be a valid positive integer.", "error": "'active_line' must be a valid positive integer."},
                400,
            )
    if "live" in body and body["live"] is not None and not isinstance(body["live"], bool):
        return (
            {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'live' must be a boolean when provided.", "error": "'live' must be a boolean when provided."},
            400,
        )

    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        return (
            {
                "ok": False,
                "error_code": "DEPENDENCY_MISSING",
                "status_kind": "dependency-missing",
                "http_status": 503,
                "badge": "DEGRADED_STATIC",
                "message": "Required runtime/tracer unavailable — showing static AST map",
            },
            503,
        )
    v4_proc = v4_mods["anvil_v4_process"]
    v4_wb = v4_mods["anvil_v4_workbench"]

    raw_pref_fam = body.get("preferred_family")
    norm_pref_fam: Optional[str] = None
    if raw_pref_fam is not None and raw_pref_fam != "":
        if not isinstance(raw_pref_fam, str):
            return (
                {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": "'preferred_family' must be a string.", "error": "'preferred_family' must be a string."},
                400,
            )
        f_low = raw_pref_fam.strip().lower()
        if f_low == "anthropic":
            f_low = "claude"
        elif f_low == "google":
            f_low = "gemini"
        if f_low not in {"claude", "gemini", "chatgpt", "grok"}:
            return (
                {"ok": False, "error_code": "MALFORMED_DATA_REFUSED", "message": f"Unrecognized 'preferred_family' value '{raw_pref_fam}'.", "error": f"Unrecognized 'preferred_family' value '{raw_pref_fam}'."},
                400,
            )
        norm_pref_fam = f_low

    try:
        with _get_cockpit_lock(cdir):
            try:
                session = _load_active_cockpit_session_dict(cdir, strict=True)
            except Exception as s_exc:
                v4_wb._raise_backing_store_unreadable(str(s_exc))
            sw_dir = _resolve_session_sw_dir(cdir, session)
            v4_bundle = _build_cockpit_v4_bundle(cdir, session or {"software": {"path": str(sw_dir)}})
            v4_sess_snap = copy.deepcopy(v4_bundle["session"])
            active_sid = str(body.get("active_stage_id") or v4_sess_snap.get("active_stage_id") or "S1")
            active_file = str(body.get("active_file") if body.get("active_file") is not None else v4_sess_snap.get("active_file", ""))
            active_line = max(1, int(body.get("active_line") or v4_sess_snap.get("active_line") or 1))
            ide_open = bool(body.get("ide_open", v4_sess_snap.get("ide_open", False)))
            seating = _read_model_seating_info()
            pref_fam = norm_pref_fam or str(seating.get("coding_family") or "gemini").lower()
            explicit_argv = list(cli_argv) if cli_argv is not None else None

        # Release cockpit lock while slow external CLI Co-Pilot subprocess executes
        chat_res = v4_wb._synthesize_grounded_copilot_reply(
            sw_dir,
            v4_bundle,
            question.strip()[:2048],
            active_sid,
            active_file,
            active_line,
            ide_open,
            live=body.get("live"),
            preferred_family=pref_fam,
            cli_argv=explicit_argv,
            cli_runner=cli_runner,
        )

        with _get_cockpit_lock(cdir):
            latest_v4_sess = v4_wb._load_or_init_workbench_session(
                cdir,
                v4_bundle["process_map"],
                persist=True,
            )
            now_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            turns = list(latest_v4_sess.get("dialogue_turns") or [])
            turns.append({"role": "user", "text": question.strip()[:2048], "stage_id": active_sid, "ts": now_iso})
            turns.append({"role": "assistant", "text": chat_res["reply"][:4096], "stage_id": chat_res["cited_stage_id"], "ts": now_iso})
            latest_v4_sess["dialogue_turns"] = turns[-80:]
            latest_v4_sess["active_stage_id"] = active_sid
            if active_file:
                latest_v4_sess["active_file"] = active_file
            latest_v4_sess["active_line"] = active_line
            latest_v4_sess["ide_open"] = ide_open
            norm_v4_sess = v4_wb._validate_and_normalize_session(
                latest_v4_sess,
                v4_wb._default_session_payload(v4_bundle["process_map"]),
            )
            v4_proc.atomic_locked_write_json(_v4_dir(cdir) / "workbench_session.json", norm_v4_sess)
            with _COCKPIT_V4_BUNDLE_CACHE_LOCK:
                for ck, cv in list(_COCKPIT_V4_BUNDLE_CACHE.items()):
                    if ck and ck[0] == str(cdir):
                        cv["session"] = copy.deepcopy(norm_v4_sess)
            return (
                {
                    "ok": True,
                    "reply": chat_res["reply"],
                    "answer_mode": chat_res.get("answer_mode", "static_ast"),
                    "status": str(chat_res.get("status") or "OK"),
                    "model_family": chat_res.get("model_family"),
                    "model_served": chat_res.get("model_served"),
                    "model_attested": bool(chat_res.get("model_attested", False)),
                    "cited_stage_id": chat_res["cited_stage_id"],
                    "cited_target_stages": chat_res["cited_target_stages"],
                    "cited_file": chat_res["cited_file"],
                    "cited_line": chat_res["cited_line"],
                    "dialogue_turns": norm_v4_sess["dialogue_turns"],
                    "session": norm_v4_sess,
                },
                200,
            )
    except v4_proc.AnvilRefusalError as err:
        if err.error_code == "ATTESTATION_MISMATCH_REFUSAL":
            return (err.to_dict(), 502)
        if err.error_code == "BOUND_EXCEEDED_REFUSAL":
            return (err.to_dict(), 400)
        return _v4_refusal_to_failure_payload(err, v4_wb)


def export_cockpit_workbench_html(
    cockpit_dir: str | Path,
    out_html_path: str | Path,
) -> Dict[str, Any]:
    """Export a standalone zero-CDN Anvil v5 Workbench HTML file from a Cockpit's active session
    without touching the external software target directory (`sw_dir`) or leaking host user paths.
    """
    cdir = Path(cockpit_dir).resolve()
    v4_mods = _load_anvil_v4_modules()
    if not v4_mods:
        raise RuntimeError("Anvil v4/v5 modules unavailable.")
    v4_wb = v4_mods["anvil_v4_workbench"]
    session = _load_active_cockpit_session_dict(cdir)
    if not session:
        raise ValueError(f"No active Anvil session in cockpit: {cdir}")
    sw_dir = _resolve_session_sw_dir(cdir, session)
    bundle = _build_cockpit_v4_bundle(cdir, session)
    return v4_wb.export_workbench_html(
        sw_dir,
        out_html_path,
        approve_run=False,
        persist=False,
        bundle_override=bundle,
    )


def probe_block_in_session(
    cockpit_dir: str | Path,
    block_id: str,
    lock_description: str = "",
    test_cmd: str = "",
) -> Dict[str, Any]:
    """Run static AST/Ruff checks AND isolated child-subprocess runtime walkthrough on a block honestly."""
    cdir = Path(cockpit_dir).resolve()
    raw_desc = (lock_description or "").strip()
    if (block_id or "").strip() == "__anvil_v4_op__" and raw_desc.startswith("{"):
        try:
            op_env = json.loads(raw_desc)
        except Exception as exc:
            return {"ok": False, "http_status": 400, "error_code": "MALFORMED_DATA_REFUSED", "message": f"Invalid v4 op JSON: {exc}"}
        if not isinstance(op_env, dict):
            return {"ok": False, "http_status": 400, "error_code": "MALFORMED_DATA_REFUSED", "message": "v4 op envelope must be an object."}
        op_name = str(op_env.get("op") or "").strip().lower()
        op_payload = op_env.get("payload") if isinstance(op_env.get("payload"), dict) else {}
        if op_name in {"v4_state", "state"}:
            res_d, code = get_v4_cockpit_state(cdir)
        elif op_name in {"v4_session", "session"}:
            res_d, code = save_v4_cockpit_ui_session(cdir, op_payload)
        elif op_name in {"v4_chat", "chat"}:
            res_d, code = run_v4_cockpit_chat(cdir, op_payload)
        elif op_name in {"v4_xval", "xval", "xval_audit"}:
            res_d, code = run_v4_cockpit_xval(cdir, op_payload)
        elif op_name in {"v4_trace", "trace"}:
            res_d, code = run_v4_cockpit_trace(cdir, op_payload)
        elif op_name in {"v4_profile_lit", "profile_lit", "profile-lit"}:
            res_d, code = run_v4_cockpit_profile_lit(cdir, op_payload)
        else:
            return {"ok": False, "http_status": 400, "error_code": "UNKNOWN_V4_OP", "message": f"Unknown v4 op: {op_name}"}
        if code != 200:
            if op_env.get("raise_on_error") is True:
                raise PermissionError(res_d.get("message") or res_d.get("error_code") or f"HTTP {code}")
            return {"ok": False, "http_status": code, **res_d}
        return {"http_status": 200, **res_d}

    with _get_cockpit_lock(cdir):
        status = get_session_status(cdir)
        session = status.get("session")
        if not session:
            raise ValueError("No active Anvil session in this cockpit.")

        bid_clean = (block_id or "").strip()
        if not bid_clean:
            raise ValueError("block_id is required.")

        buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
        block = next(
            (
                b for b in buckets
                if b.get("id") == bid_clean
                or b.get("file") == bid_clean
                or b.get("primary_file") == bid_clean
                or bid_clean in (b.get("member_files") or [])
            ),
            None,
        )
        if not block:
            raise ValueError(f"Block '{bid_clean}' not found in active session.")

        sw_path = Path((session.get("software") or {}).get("path") or cdir)
        base_dir = sw_path.parent if sw_path.is_file() else sw_path
        member_rel_files = list(block.get("member_files") or [])
        if not member_rel_files:
            rel_single = block.get("primary_file") or block.get("file") or ""
            if rel_single:
                member_rel_files = [rel_single]

        py_targets: List[Path] = []
        non_py_targets: List[Path] = []
        for rel_f in member_rel_files:
            tf = (base_dir / rel_f).resolve()
            if tf.is_file() and not tf.is_symlink():
                if tf.suffix.lower() == ".py":
                    py_targets.append(tf)
                else:
                    non_py_targets.append(tf)

        probe_notes: List[str] = []
        static_ok = True
        if py_targets:
            compiled_count = 0
            for tf in py_targets:
                try:
                    src = tf.read_text(encoding="utf-8", errors="replace")
                    tree = ast.parse(src, filename=tf.name)
                    compile(tree, filename=tf.name, mode="exec")
                    compiled_count += 1
                except Exception as exc:
                    static_ok = False
                    probe_notes.append(f"✗ Syntax/compile error in {tf.name}: {exc}")
            if static_ok:
                probe_notes.append(
                    f"✓ Static AST parse & bytecode compile passed across {compiled_count} Python module(s) "
                    f"in '{block.get('title')}' ({len(block.get('functions') or [])} functions)."
                )
            try:
                r = subprocess.run(
                    [sys.executable, "-m", "ruff", "check", "--select", "E9,F63,F7,F82"] + [str(p) for p in py_targets[:25]],
                    capture_output=True,
                    text=True,
                    timeout=25,
                    shell=False,
                    stdin=subprocess.DEVNULL,
                    creationflags=(subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0),
                )
                combined = (r.stdout + r.stderr).strip()
                if r.returncode == 0:
                    probe_notes.append("✓ Ruff static undefined-name & syntax gate: PASS (0 issues).")
                elif "No module named ruff" in combined:
                    probe_notes.append("ℹ Ruff not installed in Python environment; AST & bytecode compile passed.")
                else:
                    static_ok = False
                    probe_notes.append(f"✗ Ruff static check findings:\n{combined[:400]}")
            except Exception:
                pass
        elif non_py_targets:
            probe_notes.append(
                f"ℹ Polyglot module {block.get('file')} ({len(non_py_targets)} file(s)) — checking isolated runtime walkthrough."
            )
        else:
            static_ok = False
            probe_notes.append(f"✗ Source file {block.get('file')} not found.")

        ran_runtime = False
        runtime_ok = False
        explicit_cmd = (test_cmd or "").strip()
        if static_ok and explicit_cmd and anvil_engine is not None and hasattr(anvil_engine, "_safe_subprocess_run"):
            ran_runtime = True
            proc = anvil_engine._safe_subprocess_run(explicit_cmd, cwd=base_dir, timeout=30.0)
            if proc.returncode == 0:
                runtime_ok = True
                probe_notes.append(f"✓ Isolated child-subprocess test command exited 0 (EXECUTED_PASS).\n{(proc.stdout or '').strip()[:300]}".strip())
            else:
                runtime_ok = False
                static_ok = False
                err_out = (proc.stderr or proc.stdout or "").strip()[:300]
                probe_notes.append(f"✗ Isolated child-subprocess test command failed (exit={proc.returncode}): {err_out}".strip())
        elif static_ok and anvil_engine is not None and hasattr(anvil_engine, "run_code_walkthrough"):
            try:
                wt = anvil_engine.run_code_walkthrough(
                    sw_path,
                    code_map=session.get("code_map"),
                    block_id=str(block.get("id") or ""),
                )
                verdict = str(wt.get("overall_verdict") or "")
                if verdict == "EXECUTED_PASS" or bool(wt.get("accurate_execution")):
                    ran_runtime = True
                    runtime_ok = True
                    probe_notes.append("✓ Isolated child-subprocess walkthrough exited 0 (EXECUTED_PASS).")
                elif verdict in ("DIVERGENCE", "MISMATCH"):
                    ran_runtime = True
                    runtime_ok = False
                    static_ok = False
                    probe_notes.append(f"✗ Isolated child-subprocess walkthrough reported {verdict}.")
                else:
                    probe_notes.append("ℹ No runnable entrypoint/test executed for this module (STATIC_ONLY).")
            except Exception as exc:
                probe_notes.append(f"ℹ Runtime walkthrough skipped: {exc}")

        if not static_ok:
            emp_status = "DIVERGENCE"
            block["static_syntax_ok"] = False
            block["validated"] = False
        elif ran_runtime and runtime_ok:
            emp_status = "EXECUTED_PASS"
            block["static_syntax_ok"] = True
            block["validated"] = True
        else:
            emp_status = "STATIC_ONLY"
            block["static_syntax_ok"] = True
            block["validated"] = False

        empirical = {
            "ran": bool(ran_runtime),
            "status": emp_status,
            "checked_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "stdout": "\n".join(probe_notes),
        }
        block["empirical_validation"] = empirical
        clean_desc = lock_description.strip()
        if clean_desc and not clean_desc.startswith("Empirical AST &"):
            block["validated_description"] = clean_desc
        elif block["validated"] and not block.get("validated_description"):
            block["validated_description"] = block.get("summary")

        # Update any paper alignments pointing to this block
        paper_map = session.get("paper_map")
        if isinstance(paper_map, dict):
            for al in paper_map.get("alignments") or []:
                if al.get("bucket_id") == block["id"] and al.get("mapped_function"):
                    al["empirical_status"] = "EXECUTED_PASS" if block["validated"] else "STATIC_ALIGNED"

        session["selected_block_id"] = block["id"]
        session["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        _write_session_ir(_session_file(cdir), session)
        _write_anvil_report(cdir, session)
        return {
            **get_session_status(cdir),
            "block": block,
            "empirical": empirical,
            "inspection": {
                "validated": bool(block.get("validated")),
                "empirical_validation": empirical,
            },
        }


def sign_off_null_space_in_session(cockpit_dir: str | Path, function_name: str) -> Dict[str, Any]:
    cdir = Path(cockpit_dir).resolve()
    with _get_cockpit_lock(cdir):
        status = get_session_status(cdir)
        session = status.get("session")
        if not session:
            raise ValueError("No active Anvil session in this cockpit.")

        fn = (function_name or "").strip()
        if not fn:
            raise ValueError("function_name is required.")
        signed = list(session.get("signed_off_drops") or [])
        if fn not in signed:
            signed.append(fn)
        session["signed_off_drops"] = signed

        ns = (session.get("remap") or {}).get("null_space") or {}
        for item in ns.get("items") or []:
            old_fn = item.get("old_function") or ""
            if old_fn == fn or old_fn.split(".")[-1] == fn:
                item["disposition"] = "intentional_drop_signed_off"
        blockers = [it for it in (ns.get("items") or []) if it.get("disposition") == "accidental_omission_blocker"]
        ns["unexplained_blockers"] = len(blockers)
        if session.get("remap"):
            session["remap"]["verdict"] = "PASS" if not blockers else "NEEDS_REVIEW"

        session["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        _write_session_ir(_session_file(cdir), session)
        _write_anvil_report(cdir, session)
        return get_session_status(cdir)


def attach_paper_to_session(cockpit_dir: str | Path, paper_spec: str) -> Dict[str, Any]:
    cdir = Path(cockpit_dir).resolve()
    status = get_session_status(cdir)
    session = status.get("session")
    if not session:
        return start_cockpit_session(cdir, mode="paper", software_spec=".", paper_spec=paper_spec)

    with _get_cockpit_lock(cdir):
        sw_path = Path((session.get("software") or {}).get("path") or cdir)
        code_map = session.get("code_map") or {}
        buckets = code_map.get("conceptual_buckets") or []
        paper_info = resolve_paper_source(cdir, paper_spec)
        paper_map = extract_paper_claims_and_align(sw_path, buckets, paper_info, code_map=code_map)
        session["paper_map"] = paper_map
        session["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        xval_p = _v4_dir(cdir) / "xval_receipt.json"
        if xval_p.is_file():
            try:
                xval_p.unlink()
            except OSError:
                pass
        _write_session_ir(_session_file(cdir), session)
        _write_anvil_report(cdir, session)
        return {**get_session_status(cdir), "paper_map": paper_map}


def _infer_setup_targets_from_chat(
    cdir: Path,
    question: str,
    candidates: Dict[str, List[Dict[str, str]]],
) -> Dict[str, Any]:
    """Inspect a natural-language Steward/Anvil dialogue message to locate local papers, URLs, or code targets."""
    q = (question or "").strip()
    q_low = q.lower()
    sw_cands = candidates.get("software") or [{"path": ".", "label": cdir.name}]
    paper_cands = candidates.get("papers") or []

    # 1. Check for explicit arXiv ID or URL in message
    matched_paper = ""
    arxiv_m = re.search(r"(?:arxiv\s*:\s*|arxiv\.org/(?:abs|pdf|e-print)/)(\d{4}\.\d{4,5}(?:v\d+)?)", q, re.IGNORECASE)
    url_m = re.search(r"(https?://[^\s)\"'>]+)", q, re.IGNORECASE)
    if arxiv_m:
        matched_paper = f"arXiv:{arxiv_m.group(1)}"
    elif url_m and ("arxiv" in url_m.group(1).lower() or url_m.group(1).lower().endswith((".pdf", ".md", ".tex", ".html", ".tgz", ".tar.gz"))):
        matched_paper = url_m.group(1)

    # 2. Check for local paper filename or title match in message
    if not matched_paper and paper_cands:
        for pc in paper_cands:
            p_path = (pc.get("path") or "").strip()
            p_name = Path(p_path).name.lower() if p_path else ""
            p_stem = Path(p_path).stem.lower() if p_path else ""
            p_label = (pc.get("label") or "").lower()
            if (p_path and p_path.lower() in q_low) or (p_name and p_name in q_low) or (len(p_stem) >= 4 and p_stem in q_low):
                matched_paper = p_path
                break
            words = [w for w in re.split(r"[^a-z0-9]+", p_label) if len(w) >= 4 and w not in ("paper", "local", "file", "draft", "notes")]
            if words and any(w in q_low for w in words):
                matched_paper = p_path
                break
        if not matched_paper and any(kw in q_low for kw in ("paper", "loaded locally", "local file", "look for", "pull", "slides", "manuscript", "equation")):
            matched_paper = paper_cands[0].get("path") or ""

    # 3. Check for software path match in message
    matched_sw = sw_cands[0].get("path") or "."
    for sc in sw_cands:
        s_path = (sc.get("path") or "").strip()
        if not s_path or s_path == ".":
            continue
        s_name = Path(s_path).name.lower()
        if s_path.lower() in q_low or (s_name and s_name in q_low):
            matched_sw = s_path
            break

    wants_launch = any(
        kw in q_low
        for kw in (
            "set up", "setup", "launch", "start", "initialize", "init", "analyze", "map",
            "look for", "pull", "load", "loaded locally", "open", "run anvil", "paper",
            "essential core", "scaffolding", "codebase", "software", "solver", ".py", ".md", ".pdf", ".tex"
        )
    )
    return {
        "wants_launch": wants_launch,
        "software_spec": matched_sw,
        "paper_spec": matched_paper,
    }


def _split_runner_argv(cmd_str: str) -> List[str]:
    parts = shlex.split(cmd_str, posix=(os.name != "nt"))
    if os.name == "nt":
        cleaned: List[str] = []
        for tok in parts:
            if len(tok) >= 2 and ((tok[0] == '"' and tok[-1] == '"') or (tok[0] == "'" and tok[-1] == "'")):
                tok = tok[1:-1]
            cleaned.append(tok)
        return cleaned
    return parts


def _try_live_cli_chat(question: str, grounded_facts: str) -> Optional[str]:
    """Optional live CLI synthesis when `ANCHOR_ANVIL_LIVE_CHAT=1` and `ANCHOR_RUNNER_CMD` is configured."""
    if os.environ.get("ANCHOR_ANVIL_LIVE_CHAT") != "1":
        return None
    runner_cmd = (os.environ.get("ANCHOR_RUNNER_CMD") or "").strip()
    if not runner_cmd:
        return None
    argv = _split_runner_argv(runner_cmd)
    if not argv:
        return None
    prompt = (
        "You are Anvil inside an Anchor AI Cockpit. Answer the user's question concisely and accurately "
        "using ONLY the verified AST, Null Space, Aegis, and Paper-to-Code facts below. Never invent file names, "
        "test counts, or model IDs.\n\n"
        f"VERIFIED SESSION FACTS:\n{grounded_facts}\n\nUSER QUESTION:\n{question}\n"
    )
    try:
        proc = subprocess.run(
            argv,
            input=prompt,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=20,
            shell=False,
            creationflags=(subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0),
        )
        if proc.returncode == 0 and (proc.stdout or "").strip():
            return proc.stdout.strip()[:2400]
    except Exception:
        return None
    return None


def _synthesize_grounded_anvil_answer(
    session: Dict[str, Any],
    question: str,
    mode: str,
    target: str,
    seating: Dict[str, str],
    v4_bundle: Optional[Dict[str, Any]] = None,
) -> Tuple[str, str]:
    """Answer Anvil dialogue questions from real AST symbols, callers/callees, Null Space, Aegis, and Paper-Map facts."""
    q = (question or "").strip()
    q_low = q.lower()
    code_map = session.get("code_map") or {}
    buckets = code_map.get("conceptual_buckets") or []
    mod_buckets = code_map.get("module_buckets") or buckets
    orange = session.get("orange_split") or {}
    counts = orange.get("counts") or {}
    remap = session.get("remap") or {}
    ns_obj = remap.get("null_space") or {}
    ns_items = ns_obj.get("items") or []
    unaccounted = [it for it in ns_items if it.get("disposition") != "intentional_drop_signed_off"]
    paper_map = session.get("paper_map")
    panel = session.get("beta_reader_panel") or {}
    sw_label = (session.get("software") or {}).get("label") or "."

    executed_cnt = sum(1 for b in buckets if b.get("validated"))
    static_cnt = sum(1 for b in buckets if b.get("static_syntax_ok") and not b.get("validated"))
    total_fns = sum(len(b.get("functions") or []) for b in buckets)

    # Index all functions and callers across the repository
    all_fns: List[Dict[str, Any]] = []
    callers_of: Dict[str, List[str]] = {}
    for b in mod_buckets:
        b_file = b.get("file") or ""
        for fn in b.get("functions") or []:
            rec = {**fn, "file": fn.get("file") or b_file, "bucket_title": b.get("title") or b_file}
            all_fns.append(rec)
            caller_label = f"{rec['file']}:{fn['name']}"
            for callee in (fn.get("all_calls") or fn.get("calls") or []):
                short_c = str(callee).split(".")[-1]
                callers_of.setdefault(short_c, []).append(caller_label)

    # 1. Model / Seating / Session Status questions
    if any(kw in q_low for kw in ("who is", "what model", "which model", "skill and model", "coding seat", "review seat")):
        seat5 = next((s for s in (panel.get("seats") or []) if s.get("seat_id") == "security_boundary_auditor"), None)
        sec_note = (
            f"Seat 5 (`Defensive & Security Boundaries`) status is `{seat5.get('status') or seat5.get('verdict')}` (`{seat5.get('score')}/100`)."
            if seat5 else ""
        )
        base_reply = (
            f"Anvil is configured with **{seating['coding_short']}** in the coding seat (`{seating['coding_family']}` CLI) "
            f"and **{seating['review_short']}** in the cross-family review seat (`{seating['review_family']}` CLI). "
            f"For `{sw_label}`, AST indexing covers **{len(buckets)} clustered module(s)** (`{len(mod_buckets)}` files, `{total_fns}` functions: "
            f"`{counts.get('juice_count', 0)}` Essential Core, `{counts.get('peel_count', 0)}` I/O Peel, `{len(unaccounted)}` open `∅ Null Space` item(s); "
            f"`{executed_cnt}` module(s) `EXECUTED_PASS`, `{static_cnt}` `STATIC_ONLY`). {sec_note}"
        ).strip()
        live = _try_live_cli_chat(q, base_reply)
        return (live, "live_model") if live else (base_reply, "static_ast")

    # 2. Security / Aegis / Seat 5 questions
    if any(kw in q_low for kw in ("security", "aegis", "vulnerability", "cwe", "injection", "traversal", "seat 5", "beta reader")):
        seats = panel.get("seats") or []
        seat5 = next((s for s in seats if s.get("seat_id") == "security_boundary_auditor"), seats[-1] if seats else {})
        findings = [f for f in (seat5.get("aegis_findings") or []) if isinstance(f, dict)]
        if findings:
            f_preview = "; ".join(
                f"`{f.get('rule_id', 'AEG')}` in `{f.get('file', '?')}:L{f.get('line') or f.get('lineno', 1)}` ({str(f.get('title') or f.get('message') or '')[:80]})"
                for f in findings[:4]
            )
            base_reply = (
                f"Seat 5 (**Defensive & Security Boundaries · Aegis**) scored `{seat5.get('score', 0)}/100` "
                f"(`{seat5.get('status') or seat5.get('verdict', 'ACTION_REQUIRED')}`) with `{len(findings)}` finding(s): {f_preview}."
            )
        else:
            base_reply = (
                f"Seat 5 (**Defensive & Security Boundaries · Aegis**) scored `{seat5.get('score', 100)}/100` "
                f"(`{seat5.get('status') or seat5.get('verdict', 'PASS')}`) with `0` CWE taint/sink findings across `{sw_label}`. "
                f"Overall 5-Seat Beta-Reader score: `{panel.get('overall_score', 0)}/100`."
            )
        live = _try_live_cli_chat(q, base_reply)
        return (live, "live_model") if live else (base_reply, "static_ast")

    # 3. Null Space / Dead-Code / Unreferenced questions
    if any(kw in q_low for kw in ("null space", "dead code", "unreferenced", "unused", "pith")):
        test_only = orange.get("referenced_by_tests_only") or []
        if unaccounted:
            preview = ", ".join(
                f"`{it.get('old_function')}()` (`{it.get('old_file')}`)"
                for it in unaccounted[:6]
            )
            base_reply = (
                f"Full-repo AST + `tests/` reference indexing found **{len(unaccounted)} truly unreferenced function(s)** in `∅ Null Space`: "
                f"{preview}" + (f" (+{len(unaccounted) - 6} more)." if len(unaccounted) > 6 else ".")
                + (f" `{len(test_only)}` additional helper(s) are referenced by `tests/` only and excluded from dead-code flags." if test_only else "")
            )
        else:
            base_reply = (
                f"`∅ Null Space` has **0 truly unreferenced functions** remaining across `{sw_label}` "
                f"(Remap verdict: `{remap.get('verdict', 'PASS')}`"
                + (f"; `{len(test_only)}` function(s) referenced by `tests/` only" if test_only else "")
                + ")."
            )
        live = _try_live_cli_chat(q, base_reply)
        return (live, "live_model") if live else (base_reply, "static_ast")

    # 3b. Anvil v4/v5 Process Stage (S1..Sk), Refactor Target (N1..Nk), Smart Funnel, Pinned Watches, Tripwires & Divergences
    stage_mention = re.search(r"\b([sn][1-9]\d?)\b", q_low)
    div_kw_hit = any(
        kw in q_low
        for kw in (
            "divergence", "divergences", "contradicted", "absent_from_manuscript",
            "warm-start", "warm_start", "1-se", "shrinkage", "div-0",
        )
    )
    v4_kw_hit = div_kw_hit or any(
        kw in q_low
        for kw in (
            "funnel", "smart variable", "pinned watch", "pinned_watch", "watches",
            "tripwire", "non-finite", "nan ", "+infinity", "-infinity", "golden master",
            "crosswalk", "hotspot", "profile_lit", "xval",
        )
    )
    if isinstance(v4_bundle, dict) and (
        stage_mention is not None
        or v4_kw_hit
        or mode == "v4"
        or re.match(r"^[SN][1-9]\d?$", (target or "").strip(), flags=re.I)
    ):
        proc_m = v4_bundle.get("process_map") or {}
        ref_m = v4_bundle.get("refactor_map") or {}
        var_cat = v4_bundle.get("variable_catalog") or {}
        funnel = var_cat.get("funnel") or {}
        v4_sess_d = v4_bundle.get("session") or {}
        trace_s = v4_bundle.get("trace_summary") or {}
        stages = proc_m.get("l1_stages") or []
        target_stages = ref_m.get("target_stages") or []
        divs_v4 = list(v4_bundle.get("divergences") or ((v4_bundle.get("paper_map") or {}).get("divergences") or []))

        req_tok = (
            stage_mention.group(1).upper()
            if stage_mention
            else ((target or "").strip().upper() if re.match(r"^[SN][1-9]\d?$", (target or "").strip(), flags=re.I) else str(v4_sess_d.get("active_stage_id") or "S1"))
        )
        matched_stg = next((s for s in stages if str(s.get("id")) == req_tok), None)
        if matched_stg is None and req_tok.startswith("N"):
            old_for_n = next(
                (str(e.get("old_stage_id")) for e in (ref_m.get("mapped_to_new") or []) if str(e.get("target_stage_id")) == req_tok and e.get("old_stage_id")),
                "",
            )
            if old_for_n:
                matched_stg = next((s for s in stages if str(s.get("id")) == old_for_n), None)
        if matched_stg is None and stages:
            matched_stg = stages[0]

        sid = str(matched_stg.get("id")) if matched_stg else "S1"
        stitle = str(matched_stg.get("title") or sid) if matched_stg else sw_label
        sfiles = (matched_stg.get("files") or []) if matched_stg else []
        lead_f = str(v4_sess_d.get("active_file") or (sfiles[0] if sfiles else ""))
        lead_ln = int(v4_sess_d.get("active_line") or 1)
        mapped_n = list(dict.fromkeys(
            str(e.get("target_stage_id"))
            for e in (ref_m.get("mapped_to_new") or [])
            if str(e.get("old_stage_id")) == sid and e.get("target_stage_id")
        )) or ([str(target_stages[0].get("id"))] if target_stages else ["N1"])
        pins = v4_sess_d.get("pinned_watches") or []
        tws = trace_s.get("tripwires") or []

        enters = ", ".join(str(x) for x in (matched_stg.get("what_enters") or [])[:4]) if matched_stg else "none"
        exits = ", ".join(str(x) for x in (matched_stg.get("what_exits") or [])[:4]) if matched_stg else "return"
        tw_clause = (
            f" Tripwires (`{len(tws)}`): `{tws[0].get('variable', 'val')}` hit `{tws[0].get('kind', 'non-finite')}` at `{tws[0].get('file', lead_f)}:L{tws[0].get('line', lead_ln)}`."
            if tws
            else " Tripwires: `0` non-finite faults observed."
        )
        div_clause = ""
        if divs_v4:
            d_items = ", ".join(
                f"`{d.get('id', 'DIV')}` (`{d.get('code_citation', '')}` · `{d.get('manuscript_status', '')}`)"
                for d in divs_v4[:4]
                if isinstance(d, dict)
            )
            div_clause = f" Manuscript-vs-Code Divergences (`{len(divs_v4)}`): {d_items}."
        base_reply = (
            f"Stage **`{sid}`** (**{stitle}**, verdict `{(matched_stg or {}).get('verdict', 'STATIC_ONLY')}`) maps to Pure-Core target **`{', '.join(mapped_n)}`**"
            + (f" at `{lead_f}:L{lead_ln}`" if lead_f else "")
            + f" (contract: enters `{enters or 'none'}` → exits `{exits or 'return'}`). "
            f"4-Stage Smart Variable Funnel: `{funnel.get('all_state', 0)} → {funnel.get('stage_scope', 0)} → {funnel.get('delta_mutated', 0)} → {funnel.get('anomalies_and_pinned_watches', 0)}` "
            f"(pinned watches: `{', '.join(pins) if pins else 'none'}`).{tw_clause}{div_clause}"
        )
        live = _try_live_cli_chat(q, base_reply)
        return (live, "live_model") if live else (base_reply, "static_ast")

    # 4. Paper / Equation / Algorithm / Section questions
    q_toks = {t for t in re.split(r"[^a-z0-9_]+", q_low) if len(t) >= 3}
    if isinstance(paper_map, dict) and (
        mode in ("paper", "paper-map")
        or any(kw in q_low for kw in ("equation", "algorithm", "section", "paper", "latex", "mathml", "elbo", "jacobian"))
    ):
        eqs = paper_map.get("equations") or []
        algs = paper_map.get("algorithms") or []
        secs = paper_map.get("sections") or []
        if "algorithm" in q_low and algs:
            alg = algs[0]
            steps = alg.get("steps") or []
            base_reply = (
                f"In **{paper_map.get('paper_title')}**, **{alg.get('title') or alg.get('id')}** (`{alg.get('source_file')}:L{alg.get('line_start', 1)}`, "
                f"`{len(steps)}` steps, status `{alg.get('status')}`) aligns primarily with `{alg.get('primary_function') or 'unmapped'}` "
                f"in module `{alg.get('matched_module') or 'unmapped'}`."
            )
            live = _try_live_cli_chat(q, base_reply)
            return (live, "live_model") if live else (base_reply, "static_ast")
        if eqs:
            best_eq = next((e for e in eqs if e.get("id") == target or e.get("label") == target), None)
            if best_eq is None:
                best_eq = max(
                    eqs,
                    key=lambda e: len(q_toks & {t for t in re.split(r"[^a-z0-9_]+", f"{e.get('id','')} {e.get('label','')} {e.get('raw_latex','')}".lower()) if len(t) >= 3}),
                )
            mfs = best_eq.get("matched_functions") or []
            top_fn = mfs[0] if mfs else {}
            base_reply = (
                f"In **{paper_map.get('paper_title')}** (`{len(secs)}` sections, `{len(algs)}` algorithm(s), `{len(eqs)}` equations), "
                f"equation `{best_eq.get('id')}` (`{best_eq.get('source_file')}:L{best_eq.get('line_start', 1)}`, status `{best_eq.get('status')}`) "
                + (
                    f"aligns with `{top_fn.get('qualname')}` (`{top_fn.get('file')}:L{top_fn.get('line_start', 1)}–L{top_fn.get('line_end', 1)}`, "
                    f"matched identifiers: `{', '.join((top_fn.get('matched_identifiers') or [])[:5]) or 'structural ops'}`)."
                    if top_fn else "has no static implementation match yet (`PAPER_ONLY_UNIMPLEMENTED`)."
                )
            )
            live = _try_live_cli_chat(q, base_reply)
            return (live, "live_model") if live else (base_reply, "static_ast")
        if paper_map.get("alignments"):
            al = next((a for a in paper_map["alignments"] if a.get("claim_id") == target), paper_map["alignments"][0])
            base_reply = (
                f"In **{paper_map.get('paper_title')}**, `{al.get('claim_id')}` (**{al.get('title')}**) maps to "
                f"`{al.get('mapped_function') or 'unmapped'}` (`{al.get('mapped_file') or ''}:{al.get('lineno') or ''}`, "
                f"status `{al.get('empirical_status')}`)."
            )
            live = _try_live_cli_chat(q, base_reply)
            return (live, "live_model") if live else (base_reply, "static_ast")

    # 5. Direct Symbol / Function lookup in AST
    best_fn: Optional[Dict[str, Any]] = None
    best_fn_score = 0
    for fn in all_fns:
        fn_name = str(fn.get("name") or "")
        short_fn = fn_name.split(".")[-1].lower()
        score = 0
        if short_fn and short_fn in q_low:
            score += 10 + len(short_fn)
        else:
            fn_toks = {t for t in re.split(r"[^a-z0-9_]+", f"{fn_name} {fn.get('summary','')} {fn.get('file','')}".lower()) if len(t) >= 3}
            score += len(q_toks & fn_toks) * 2
        if target and (fn.get("file") == target or fn_name == target):
            score += 4
        if score > best_fn_score:
            best_fn_score = score
            best_fn = fn

    if best_fn is not None and best_fn_score >= 4:
        short_nm = str(best_fn["name"]).split(".")[-1]
        callees = (best_fn.get("all_calls") or best_fn.get("calls") or [])[:6]
        callers = sorted(set(callers_of.get(short_nm, [])))[:5]
        base_reply = (
            f"`{best_fn['name']}({', '.join(best_fn.get('args') or [])})` in `{best_fn['file']}:L{best_fn.get('lineno', 1)}–L{best_fn.get('end_lineno', best_fn.get('lineno', 1))}` "
            f"(module **{best_fn.get('bucket_title')}**, stage `{str(best_fn.get('stage', 'compute')).upper()}`) — {best_fn.get('summary') or 'AST symbol'}. "
            f"Calls: {', '.join(f'`{c}`' for c in callees) if callees else 'none'}; "
            f"referenced by: {', '.join(f'`{c}`' for c in callers) if callers else 'top-level/external entrypoint'}."
        )
        live = _try_live_cli_chat(q, base_reply)
        return (live, "live_model") if live else (base_reply, "static_ast")

    # 6. Target Module / Bucket summary grounded in AST
    matched = next(
        (
            b for b in buckets
            if b.get("id") == target or b.get("file") == target or b.get("title") == target
            or (b.get("title") and b["title"].lower() in q_low)
        ),
        buckets[0] if buckets else None,
    )
    if matched:
        fns = ", ".join(f"`{fn['name']}()`" for fn in (matched.get("functions") or [])[:5])
        stage = (matched.get("pipeline_stage") or "compute").upper()
        member_files = matched.get("member_files") or ([matched.get("file")] if matched.get("file") else [])
        mods_preview = ", ".join(f"`{m}`" for m in member_files[:6])
        if len(member_files) > 6:
            mods_preview += f" (+{len(member_files) - 6} more)"
        v_state = (
            "EXECUTED_PASS (runtime verified)"
            if matched.get("validated")
            else ("STATIC_ONLY (AST parsed, not yet executed)" if matched.get("static_syntax_ok") else "STATIC_ONLY")
        )
        base_reply = (
            f"Module **{matched.get('title')}** (`{stage}`, status `{v_state}`) spans `{len(member_files)}` file(s) ({mods_preview}) "
            f"with `{len(matched.get('functions') or [])}` AST function(s) ({fns or 'none'}). "
            f"{matched.get('validated_description') or matched.get('summary') or ''}"
        ).strip()
        live = _try_live_cli_chat(q, base_reply)
        return (live, "live_model") if live else (base_reply, "static_ast")

    base_reply = (
        f"`{sw_label}` is indexed across `{len(buckets)}` architectural module(s) (`{total_fns}` functions; "
        f"`{executed_cnt}` `EXECUTED_PASS`, `{len(unaccounted)}` `∅ Null Space` items). Ask about any file, function, security check, or paper equation."
    )
    live = _try_live_cli_chat(q, base_reply)
    return (live, "live_model") if live else (base_reply, "static_ast")


def chat_in_session(
    cockpit_dir: str | Path,
    question: str,
    mode: str = "map",
    target: str = "",
) -> Dict[str, Any]:
    cdir = Path(cockpit_dir).resolve()
    q = (question or "").strip()
    if not q:
        raise ValueError("Question cannot be empty.")

    status = get_session_status(cdir)
    session = status.get("session")
    candidates = status.get("candidates") or discover_cockpit_candidates(cdir)

    # If no session is active yet, allow natural-language setup & discovery via Steward/Anvil dialogue
    if not session:
        inferred = _infer_setup_targets_from_chat(cdir, q, candidates)
        if inferred["wants_launch"] or inferred["paper_spec"] or inferred["software_spec"] != ".":
            launch_mode = "paper" if inferred["paper_spec"] else ("paper" if mode in ("paper", "paper-map") and inferred["paper_spec"] else "code")
            started = start_cockpit_session(
                cdir,
                mode=launch_mode,
                software_spec=inferred["software_spec"],
                paper_spec=inferred["paper_spec"],
            )
            with _get_cockpit_lock(cdir):
                session = (started.get("session") or {})
                now_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                history = list(session.get("chat_history") or [])
                history.insert(0, {"role": "user", "mode": mode, "target": target or "setup", "text": q, "at": now_iso})
                sw_label = (session.get("software") or {}).get("label") or inferred["software_spec"]
                paper_map = session.get("paper_map")
                if paper_map:
                    sc = paper_map.get("summary_counts") or {}
                    reply = (
                        f"[Steward · Anvil Setup] Loaded paper **{paper_map.get('paper_title')}** (`{inferred['paper_spec']}`) "
                        f"and mapped it against `{sw_label}` "
                        f"(`{sc.get('sections', len(paper_map.get('sections') or []))}` sections, "
                        f"`{sc.get('algorithms', len(paper_map.get('algorithms') or []))}` algorithm(s), "
                        f"`{sc.get('equations', paper_map.get('claims_mapped', 0))}` native MathML equations)."
                    )
                else:
                    buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
                    reply = (
                        f"[Steward · Anvil Setup] Initialized Anvil Software Analysis session for `{sw_label}` "
                        f"(`{len(buckets)}` clustered architectural module(s) mapped across Essential Core, I/O Peel, and `∅ Null Space`)."
                    )
                history.append({
                    "role": "anvil",
                    "mode": mode,
                    "target": target or "setup",
                    "text": reply,
                    "answer_mode": "static_ast",
                    "at": now_iso,
                })
                session["chat_history"] = history[-40:]
                session["updated_at"] = now_iso
                _write_session_ir(_session_file(cdir), session)
                return {**get_session_status(cdir), "reply": reply, "answer_mode": "static_ast"}
        else:
            sw_list = ", ".join(f"`{c['path']}`" for c in (candidates.get("software") or [])[:5]) or "`.`"
            pp_list = ", ".join(f"`{c['path']}`" for c in (candidates.get("papers") or [])[:5]) or "none detected yet"
            reply = (
                f"[Steward · Anvil Setup] Ready to configure Anvil for **{status.get('cockpit_name', cdir.name)}**. "
                f"Local software detected: {sw_list}. Local papers/docs detected: {pp_list}. "
                f"Tell me which paper or codebase to load (e.g. \"Set up Anvil with local paper and map to code\" or \"Pull arXiv:1706.03762\"), and I will launch the session immediately."
            )
            return {**status, "reply": reply, "answer_mode": "static_ast"}

    with _get_cockpit_lock(cdir):
        status = get_session_status(cdir)
        session = status.get("session")
        now_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        history = list(session.get("chat_history") or [])
        history.append({"role": "user", "mode": mode, "target": target, "text": q, "at": now_iso})

        inferred = _infer_setup_targets_from_chat(cdir, q, candidates)
        q_low = q.lower()
        if inferred["paper_spec"] and any(kw in q_low for kw in ("attach", "pull", "look for", "load", "loaded locally", "switch paper", "map paper")):
            sw_path = Path((session.get("software") or {}).get("path") or cdir)
            code_map = session.get("code_map") or {}
            buckets = code_map.get("conceptual_buckets") or []
            paper_info = resolve_paper_source(cdir, inferred["paper_spec"])
            paper_map = extract_paper_claims_and_align(sw_path, buckets, paper_info, code_map=code_map)
            session["paper_map"] = paper_map

        buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
        remap = session.get("remap") or {}
        ns_obj = remap.get("null_space") or {}
        ns_items = ns_obj.get("items") or []
        unaccounted = [it for it in ns_items if it.get("disposition") != "intentional_drop_signed_off"]
        seating = _read_model_seating_info()

        asks_verify = any(
            kw in q_low
            for kw in (
                "verfied", "verified", "verify", "probe all", "lock all", "run probe", "run checks",
            )
        )
        asks_sign_off = any(
            kw in q_low
            for kw in ("sign off", "approve drop", "approve null space", "clear null space")
        )

        answer_mode = "static_ast"
        if asks_verify:
            newly_probed, executed_total = _verify_all_buckets_in_place(session, cdir)
            static_ok_total = sum(1 for b in buckets if b.get("static_syntax_ok"))
            ns_tail = (
                f"`{len(unaccounted)}` truly unreferenced function(s) remain in `∅ Null Space`."
                if unaccounted
                else "`∅ Null Space` has `0` unexplained blockers."
            )
            reply = (
                f"Probed `{len(buckets)}` clustered architectural module(s) (`{newly_probed}` updated): "
                f"`{executed_total}/{len(buckets)}` reached `EXECUTED_PASS` via isolated child-subprocess walkthrough, "
                f"and `{static_ok_total}/{len(buckets)}` passed static AST/bytecode checks (`STATIC_ONLY` where no runtime test ran). {ns_tail}"
            )
        elif asks_sign_off:
            if unaccounted:
                signed_list = list(session.get("signed_off_drops") or [])
                for it in ns_items:
                    fn_name = it.get("old_function") or ""
                    if fn_name and fn_name not in signed_list:
                        signed_list.append(fn_name)
                    it["disposition"] = "intentional_drop_signed_off"
                session["signed_off_drops"] = signed_list
                ns_obj["unexplained_blockers"] = 0
                if session.get("remap"):
                    session["remap"]["verdict"] = "PASS"
            reply = (
                f"Signed off `{len(ns_items)}` `∅ Null Space` candidate(s); Old-to-New Remap verdict is now **`{remap.get('verdict', 'PASS')}`** with `0` unexplained blockers."
            )
        else:
            reply, answer_mode = _synthesize_grounded_anvil_answer(
                session,
                q,
                mode,
                target,
                seating,
                v4_bundle=status.get("v4_bundle"),
            )

        history.append({
            "role": "anvil",
            "mode": mode,
            "target": target,
            "text": reply,
            "answer_mode": answer_mode,
            "at": now_iso,
        })
        session["chat_history"] = history[-40:]
        session["updated_at"] = now_iso
        _write_session_ir(_session_file(cdir), session)
        _write_anvil_report(cdir, session)

        # Also append user + assistant turns into `<cdir>/.anvil/v4/workbench_session.json`
        v4_mods = _load_anvil_v4_modules()
        if v4_mods:
            try:
                v4_proc = v4_mods["anvil_v4_process"]
                v4_wb = v4_mods["anvil_v4_workbench"]
                sw_dir = _resolve_session_sw_dir(cdir, session)
                proc_m = (
                    (status.get("v4_bundle") or {}).get("process_map")
                    or v4_proc.build_process_map(sw_dir, persist=False)
                )
                v4_sess = v4_wb._load_or_init_workbench_session(cdir, proc_m, persist=True)
                active_sid = str(v4_sess.get("active_stage_id") or "S1")
                turns = list(v4_sess.get("dialogue_turns") or [])
                turns.append({"role": "user", "text": q[:4096], "stage_id": active_sid, "ts": now_iso})
                turns.append({"role": "assistant", "text": reply[:4096], "stage_id": active_sid, "ts": now_iso})
                v4_sess["dialogue_turns"] = turns[-80:]
                v4_proc.atomic_locked_write_json(_v4_dir(cdir) / "workbench_session.json", v4_sess)
            except Exception:
                pass

        return {**get_session_status(cdir), "reply": reply, "answer_mode": answer_mode}


def apply_conversational_anvil_side_effects(cockpit_dir: str | Path, question: str) -> str:
    """When a user speaks in the real AI Cockpit dialogue while an Anvil session is active,
    apply any explicitly requested Anvil probe / Null Space sign-off in place and return a
    compact 1-line Anvil context note for the Steward Engine."""
    cdir = Path(cockpit_dir).resolve()
    sfile = _session_file(cdir)
    if not sfile.is_file():
        return ""
    q_low = (question or "").strip().lower()
    with _get_cockpit_lock(cdir):
        try:
            session = _read_session_ir(sfile)
        except Exception:
            return ""
        if not isinstance(session, dict):
            return ""
        buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
        remap = session.get("remap") or {}
        ns_obj = remap.get("null_space") or {}
        ns_items = ns_obj.get("items") or []
        unaccounted = [it for it in ns_items if it.get("disposition") != "intentional_drop_signed_off"]
        changed = False

        if any(kw in q_low for kw in ("verify", "verified", "probe all", "lock all")):
            newly, _ = _verify_all_buckets_in_place(session, cdir)
            if newly > 0:
                changed = True
        if any(kw in q_low for kw in ("sign off", "approve drop", "approve null space", "clear null space")) and unaccounted:
            signed_list = list(session.get("signed_off_drops") or [])
            for it in ns_items:
                fn_name = it.get("old_function") or ""
                if fn_name and fn_name not in signed_list:
                    signed_list.append(fn_name)
                it["disposition"] = "intentional_drop_signed_off"
            session["signed_off_drops"] = signed_list
            ns_obj["unexplained_blockers"] = 0
            if session.get("remap"):
                session["remap"]["verdict"] = "PASS"
            unaccounted = []
            changed = True

        if changed:
            session["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            _write_session_ir(sfile, session)
            _write_anvil_report(cdir, session)

        executed_total = sum(1 for b in buckets if b.get("validated"))
        seating = _read_model_seating_info()
        return (
            f"\n(anvil workbench state: {executed_total}/{len(buckets)} architectural modules EXECUTED_PASS; "
            f"coding seat={seating['coding_short']}, review seat={seating['review_short']}; "
            f"Old-to-New map verdict={remap.get('verdict', 'PASS')}, unaccounted Null Space items={len(unaccounted)}. "
            f"Answer John's question naturally and conversationally in 2-4 plain sentences — never dump a standardized template.)"
        )



def walkthrough_in_session(cockpit_dir: str | Path, block_id: str = "") -> Dict[str, Any]:
    """Run a live step-by-step polyglot code walkthrough on a block or entire session."""
    if anvil_engine is None or not hasattr(anvil_engine, "run_code_walkthrough"):
        raise ValueError("Anvil v2 walkthrough engine is unavailable on this host.")
    cdir = Path(cockpit_dir).resolve()
    with _get_cockpit_lock(cdir):
        status = get_session_status(cdir)
        session = status.get("session")
        bid = (block_id or "").strip()
        if session:
            sw_path = Path((session.get("software") or {}).get("path") or cdir)
            buckets = (session.get("code_map") or {}).get("conceptual_buckets") or []
            if hasattr(anvil_engine, "_enrich_progressive_levels") and buckets:
                anvil_engine._enrich_progressive_levels(
                    sw_path,
                    buckets,
                    paper_map=session.get("paper_map"),
                    remap=session.get("remap"),
                )
            if hasattr(anvil_engine, "run_beta_reader_panel"):
                session["beta_reader_panel"] = anvil_engine.run_beta_reader_panel(
                    sw_path,
                    code_map=session.get("code_map"),
                    orange_split=session.get("orange_split"),
                    remap=session.get("remap"),
                )
            try:
                wt = anvil_engine.run_code_walkthrough(
                    sw_path,
                    code_map=session.get("code_map"),
                    block_id=bid,
                )
            except TypeError:
                wt = anvil_engine.run_code_walkthrough(sw_path, block_id=bid)
            session["walkthrough_trace"] = wt
            session["walkthrough"] = wt
            if bid:
                session["selected_block_id"] = bid
            session["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            _write_session_ir(_session_file(cdir), session)
            _write_anvil_manifest(cdir, session)
            _write_anvil_report(cdir, session)
            return {
                **get_session_status(cdir),
                "walkthrough": wt,
            }
        else:
            wt = anvil_engine.run_code_walkthrough(cdir, block_id=bid)
            return {
                **status,
                "walkthrough": wt,
            }


def reset_cockpit_session(cockpit_dir: str | Path) -> Dict[str, Any]:
    cdir = Path(cockpit_dir).resolve()
    with _get_cockpit_lock(cdir):
        sfile = _session_file(cdir)
        if sfile.is_file():
            prev = _session_dir(cdir) / "session.prev.json"
            try:
                _atomic_write_text(prev, sfile.read_text(encoding="utf-8", errors="replace"))
                sfile.unlink()
            except Exception:
                pass
        v4_d = _v4_dir(cdir)
        if v4_d.exists():
            shutil.rmtree(v4_d, ignore_errors=True)
        return get_session_status(cdir)


def main(argv: Optional[List[str]] = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Per-Cockpit Anvil Session CLI for Cockpit Stewards")
    parser.add_argument("--cockpit", default=".", help="Path to the AI Cockpit folder")
    parser.add_argument(
        "--action",
        default="status",
        choices=("status", "start_code", "start_paper", "probe_block", "walkthrough", "sign_off_drop", "attach_paper", "chat", "reset"),
    )
    parser.add_argument("--software", default=".", help="Local path in cockpit or GitHub repo URL")
    parser.add_argument("--compare", default="", help="Comparison software target for remap/null-space")
    parser.add_argument("--paper", default="", help="arXiv ID/URL, HTTPS URL, or local paper path")
    parser.add_argument("--block", default="", help="Block ID or file for probe_block / walkthrough")
    parser.add_argument("--function", default="", help="Function name for sign_off_drop")
    parser.add_argument("--question", default="", help="Question for Anvil Agent chat")
    args = parser.parse_args(argv)

    cdir = Path(args.cockpit).resolve()
    if args.action == "status":
        res = get_session_status(cdir)
    elif args.action in ("start_code", "start_paper"):
        res = start_cockpit_session(
            cdir,
            mode="paper" if args.action == "start_paper" else "code",
            software_spec=args.software,
            compare_spec=args.compare,
            paper_spec=args.paper,
        )
    elif args.action == "probe_block":
        res = probe_block_in_session(cdir, args.block)
    elif args.action == "walkthrough":
        res = walkthrough_in_session(cdir, args.block)
    elif args.action == "sign_off_drop":
        res = sign_off_null_space_in_session(cdir, args.function)
    elif args.action == "attach_paper":
        res = attach_paper_to_session(cdir, args.paper)
    elif args.action == "chat":
        res = chat_in_session(cdir, args.question, target=args.block)
    else:
        res = reset_cockpit_session(cdir)
    print(json.dumps(res, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
