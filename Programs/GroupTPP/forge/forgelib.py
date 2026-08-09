"""
forgelib.py — Shared forge library for parallel Sage programs.

Provides:
  - WorkerPool: parent-process driver scheduling chunked work units
    to N single-core ``sage`` worker subprocesses (GAP is single-threaded;
    parallelism comes from N independent processes, not threads).
  - Sharded JSONL output with re-shardable resume: done-ids are unioned
    across ALL shard files matching the glob pattern, so running with
    4 local workers then 256 on the forge needs no checkpoint migration.
  - Atomic checkpoint writes (tmp + os.replace).
  - Parseable progress protocol (PROGRESS prefix, one line per interval).
  - Sage-type JSON sanitizer (Integer/RR/RDF -> native Python).
  - --dry-run projection helpers (space size, rate, projected wall clock).

Convention: every forge program imports forgelib as a plain Python module
(NOT a .sage file) so that it works both under ``sage script.sage`` and
``python3 -c 'import forgelib'``.  Sage-specific types (Integer, RR) are
detected by duck-typing, never by importing sage.all at module scope.
"""

import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path


# ---------------------------------------------------------------------------
# Sage-type JSON sanitizer
# ---------------------------------------------------------------------------

def sanitize(obj):
    """Recursively convert Sage Integer/RR/RDF/GapElement types to native
    Python types that json.dumps accepts.

    Handles: dict, list, tuple, bool, int-like (__index__), float, str.
    Falls back to float() then str() for unknown numeric-ish types
    (e.g. RealDoubleElement, RealField elements).
    """
    if isinstance(obj, dict):
        return {sanitize(k): sanitize(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [sanitize(x) for x in obj]
    if isinstance(obj, bool):
        return obj
    if hasattr(obj, "__index__"):
        return int(obj)
    if isinstance(obj, float):
        return obj
    if isinstance(obj, str):
        return obj
    if obj is None:
        return obj
    # Catch Sage RealDoubleElement, RealField elements, etc.
    try:
        return float(obj)
    except (TypeError, ValueError):
        pass
    return str(obj)


def dump_jsonl(rec):
    """Serialize a record to compact JSON, sanitizing Sage types."""
    return json.dumps(sanitize(rec), separators=(",", ":"))


# ---------------------------------------------------------------------------
# Sharded JSONL: resume across all shards
# ---------------------------------------------------------------------------

def shard_filename(base_name, shard_i, shard_n):
    """Deterministic shard file name: <base>.shard<I>of<N>.jsonl."""
    return "%s.shard%dof%d.jsonl" % (base_name, shard_i, shard_n)


def load_done_ids(out_dir, base_glob, id_key="id"):
    """Union done-ids across ALL shard files matching ``base_glob``
    (e.g. ``cascade*.jsonl``) in ``out_dir``.

    Returns a set of tuples.  Each JSONL record is expected to carry
    ``id_key`` as a list of ints (e.g. [order, idx]).  Records with
    a ``"type"`` key (control records) are skipped.
    """
    done = set()
    out_path = Path(out_dir)
    for path in sorted(out_path.glob(base_glob)):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    if rec.get("type"):
                        continue
                    gid = rec.get(id_key)
                    if gid:
                        done.add(tuple(gid))
                except (json.JSONDecodeError, TypeError, KeyError):
                    continue
    return done


def load_legacy_done_ids(checkpoint_dir, id_key="id"):
    """Load done-ids from legacy per-order checkpoint files
    (``checkpoints/order_N.jsonl``).  Only records from complete
    orders are imported (the control record must say ``order_complete``)."""
    done = set()
    ckpt = Path(checkpoint_dir)
    if not ckpt.is_dir():
        return done
    for path in sorted(ckpt.glob("order_*.jsonl")):
        records = []
        is_complete = False
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                except (json.JSONDecodeError, TypeError):
                    continue
                t = rec.get("type")
                if t == "order_complete":
                    is_complete = True
                elif t is None:
                    records.append(rec)
        # Legacy files without any control record are treated as complete
        if is_complete or not any(True for r in records if r.get("type")):
            for rec in records:
                gid = rec.get(id_key)
                if gid:
                    done.add(tuple(gid))
    return done


# ---------------------------------------------------------------------------
# Atomic checkpoint writes
# ---------------------------------------------------------------------------

def atomic_write_jsonl(path, records, control_rec=None):
    """Write records + optional control record atomically via tmp+rename."""
    path = Path(path)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".jsonl.tmp")
    try:
        with os.fdopen(fd, "w") as f:
            for rec in records:
                f.write(dump_jsonl(rec) + "\n")
            if control_rec is not None:
                f.write(dump_jsonl(control_rec) + "\n")
        os.replace(tmp, str(path))
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def append_jsonl(path, rec):
    """Append one sanitized record to a JSONL file (no atomic rewrite)."""
    with open(path, "a") as f:
        f.write(dump_jsonl(rec) + "\n")


# ---------------------------------------------------------------------------
# Progress protocol
# ---------------------------------------------------------------------------

def progress_line(unit_id, done, total, elapsed_s, prefix=""):
    """Format one machine-parseable progress line.

    Example: PROGRESS unit=256:0-2000 done=1500 total=2000 rate=45.2/s eta=11s
    """
    rate = done / elapsed_s if elapsed_s > 0 else 0.0
    remaining = total - done
    eta = remaining / rate if rate > 0 else 0.0
    return "%sPROGRESS unit=%s done=%d total=%d rate=%.1f/s eta=%.0fs" % (
        prefix, unit_id, done, total, rate, eta)


# ---------------------------------------------------------------------------
# Dry-run projection helpers
# ---------------------------------------------------------------------------

def dry_run_projection(space_size, rate_per_core, n_workers, label=""):
    """Print projected wall-clock time as a function of worker count."""
    per_worker = space_size / max(n_workers, 1)
    wall_s = per_worker / rate_per_core if rate_per_core > 0 else float("inf")
    wall_min = wall_s / 60
    wall_h = wall_s / 3600
    lines = []
    if label:
        lines.append("--- %s ---" % label)
    lines.append("  Space: %d work items" % space_size)
    lines.append("  Rate assumption: %.1f items/s/core" % rate_per_core)
    lines.append("  Workers: %d" % n_workers)
    lines.append("  Per-worker load: %d items" % int(per_worker))
    if wall_h >= 1:
        lines.append("  Projected wall clock: %.1f hours (%.0f min)" % (wall_h, wall_min))
    else:
        lines.append("  Projected wall clock: %.1f min (%.0f s)" % (wall_min, wall_s))
    return "\n".join(lines)


def dry_run_table(space_size, rate_per_core, worker_counts, label=""):
    """Print a table of projected wall-clock times for multiple worker counts."""
    lines = []
    if label:
        lines.append("--- %s ---" % label)
    lines.append("  Space: %d items | Rate: %.1f items/s/core"
                 % (space_size, rate_per_core))
    lines.append("  Workers | Per-worker | Wall clock")
    lines.append("  --------|------------|----------")
    for nw in worker_counts:
        per_worker = space_size / max(nw, 1)
        wall_s = per_worker / rate_per_core if rate_per_core > 0 else float("inf")
        if wall_s >= 3600:
            wall_str = "%.1f hours" % (wall_s / 3600)
        elif wall_s >= 60:
            wall_str = "%.1f min" % (wall_s / 60)
        else:
            wall_str = "%.0f s" % wall_s
        lines.append("  %7d | %10d | %s" % (nw, int(per_worker), wall_str))
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Worker pool
# ---------------------------------------------------------------------------

class WorkerPool:
    """Spawn N single-core ``sage`` worker subprocesses and wait.

    Each worker runs the same Sage script with ``--shard I/N`` to select
    its deterministic slice.  Workers are independent processes; GAP's
    single-threaded C kernel cannot share state.

    Ctrl-C propagates SIGINT to all workers (same process group);
    each worker is responsible for checkpointing before exit.
    The pool waits for all workers to finish, then returns the OR
    of their exit codes.

    Usage::

        pool = WorkerPool(
            script="cascade.sage",
            n_workers=4,
            extra_args=["--out-dir", "forge/out/cascade"],
        )
        rc = pool.run()
    """

    def __init__(self, script, n_workers, extra_args=None,
                 sage_bin="sage", env=None):
        self.script = str(script)
        self.n_workers = int(n_workers)
        self.extra_args = list(extra_args or [])
        self.sage_bin = sage_bin
        self.env = env

    def run(self):
        """Spawn workers and wait; returns combined exit code."""
        procs = []
        for i in range(self.n_workers):
            cmd = [self.sage_bin, self.script, "--",
                   "--shard", "%d/%d" % (i, self.n_workers)]
            cmd.extend(self.extra_args)
            procs.append(subprocess.Popen(cmd, env=self.env))

        rc = 0
        try:
            for p in procs:
                ret = p.wait()
                if ret != 0:
                    rc = ret
        except KeyboardInterrupt:
            # Ctrl-C hits the whole process group; workers get SIGINT too.
            # Wait for them to checkpoint and exit.
            print("\nInterrupt — waiting for workers to checkpoint...",
                  file=sys.stderr, flush=True)
            for p in procs:
                try:
                    p.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    p.kill()
                    p.wait()
            rc = 130
        return rc


# ---------------------------------------------------------------------------
# Work-unit chunking helpers
# ---------------------------------------------------------------------------

def chunk_range(start, end, chunk_size):
    """Yield (chunk_start, chunk_end) pairs covering [start, end]."""
    i = int(start)
    end = int(end)
    chunk_size = int(chunk_size)
    while i <= end:
        yield (i, min(i + chunk_size - 1, end))
        i += chunk_size


def make_work_units(orders_and_counts, chunk_size=2000):
    """Build a flat list of work units from [(order, n_groups), ...].

    Each work unit is a dict: {"order": N, "idx_start": S, "idx_end": E,
    "unit_id": "N:S-E"}.  Orders with n_groups <= chunk_size produce a
    single unit; larger orders are split into chunks of ``chunk_size``
    so that (e.g.) order 256 with 56,092 groups produces ~28 units
    that can be distributed across workers.
    """
    units = []
    for order, n_groups in orders_and_counts:
        for cstart, cend in chunk_range(1, n_groups, chunk_size):
            units.append({
                "order": int(order),
                "idx_start": int(cstart),
                "idx_end": int(cend),
                "unit_id": "%d:%d-%d" % (order, cstart, cend),
            })
    return units
