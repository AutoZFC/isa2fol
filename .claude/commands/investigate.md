# Investigate Bug

Structured bug investigation for the isa2fol pipeline. You MUST follow this
protocol exactly. Do NOT skip steps. Do NOT write code until the report is
approved.

## Input

The user provides: $ARGUMENTS

This may be a proof name, error message, checker output, or general symptom.

## Step 0: Choose Mode

- **Mode 1 (Root Cause Analysis):** The symptom is clear but the source is
  unknown (e.g., "proof X fails," "key missing from HashMap," checker error).
  Use this when investigating a broad category of failures or when the user
  asks for a full RCA. Findings are shared across sessions.
- **Mode 2 (Investigate Specific Bug):** The user already knows the location
  or construct that's wrong (e.g., "lambda translation is wrong for nested
  lambdas," "Pure.eq handling drops the body"). Use this when working on a
  single task from the parallel task list.

State which mode you're using and why.

## Mode 1: Root Cause Analysis

### Step 1: Reproduce

Find the minimal trigger. Get concrete data:
- Which proof file? (serial number + theory)
- Run it: `MEM=16G scripts/capped.sh swift test --filter <test>` (rule 10).
  Corpus state comes from `scripts/source-surface.py`, which regenerates
  `docs/SOURCE_SURFACE.md`; a single unit from the real `proof_checker`
- Capture the actual output vs what was expected

If the user gave an error message, find the exact proof/theorem that triggers it.

### Step 2: Localize

Identify which pipeline stage diverges. The pipeline is:

```
YXML file → parse → Graph of isa.* ops (types obj/prop/meta/fn)
  → LowerMeta   ⟹ ⋀ ≡ Trueprop  →  fol connectives + guards
  → LowerFn     binder scopes → Regions; operands → classes (S5)
  → legalize    fol-zfc ops only, no cast, no meta/fn types
  → render text
```

`Graph.dump()` prints any stage. Use it to binary-search which
stage produces the wrong output. Check the stage BEFORE the first broken one —
that's where the bug likely is.

### Step 3: Trace Upstream

From the divergence point, trace BACKWARD through the pipeline. At each stage ask:
- What data comes in?
- What does this stage do with it?
- Is the input already wrong? (If yes, go one stage further back.)

**CRITICAL:** Do NOT stop at the first place that looks wrong. The symptom
(e.g., "key not in HashMap") is rarely the cause. Keep asking "WHY is this
state wrong?" until you reach the stage that INTRODUCED the bad state.

### Step 4: Diagnose and Share

State the root cause precisely: "Phase X produces Y because of Z. The correct
behavior is W."

If the fix doesn't fit the current design, say so explicitly. Do NOT force a
fix into a wrong design. Instead state: "The current design assumes A, but the
correct assumption is B. The design needs to change."

**Immediately after diagnosis**, share findings across sessions. See
"Sharing findings across sessions" below. Do this BEFORE presenting the
report, so other sessions can start working on orthogonal issues in parallel.

## Mode 2: Investigate Specific Bug

Mode 2 is for focused work on a single task. Do NOT share findings to memory
— the current session owns this task and should stay focused on it.

### Step 1: Understand the Construct

Read the Isabelle source for the construct in question. Check:
- The YXML representation (read a real proof file that contains it)
- The translation rules table in CLAUDE.md
- The relevant Isabelle semantics (Pure.eq, Pure.imp, quantifiers, etc.)

### Step 2: Trace the Specific Path

Follow this ONE construct through each pipeline stage that touches it.
Read the actual code at each stage:
- `Sources/YXML/Parse.swift` — how is the transfer format read?
- the reader into `IR.Graph` — which `isa.*` op does the node become?
- `Sources/IR/Pass.swift` — which pattern rewrites it, and to what?
- `Sources/IR/Legalize.swift` — does it survive lowering? `Graph.dump()` shows.
- `Sources/FolDialect/Render.swift` — how is it rendered to text?

### Step 3: Identify the Gap

Compare what the code does vs what it should do for this construct.
The gap may be:
- Wrong classification (e.g., term vs schema)
- Missing case in a match
- Wrong transformation in a pass
- Design mismatch (the architecture doesn't accommodate this construct)

## Report (REQUIRED before any code)

Present your findings in this exact format:

### Isabelle Original
The source construct as Isabelle sees it.
```
Example: ⋀x::i. P(x) ⟹ Q(x)
```

### Current Translation
What the pipeline currently produces (paste actual output).
```
Example: forall x. P(x) -> Q(x)    ← missing apply_fn encoding for P
```

### Desired Translation
What the correct FOL-ZFC output should be, with reasoning from the
translation rules.
```
Example: forall x. (exists _v0. (apply_fn1(P, x, _v0) & exists _v1. elem(_v1, _v0))) -> Q(x)
```

### Root Cause
- Which phase introduced the bug
- Which assumption was wrong
- Why the current code does what it does (not just "it's wrong")

### Proposed Fix
- Where the fix belongs (file + function)
- Whether the design needs changing
- If design change: what the new design should be

## Implementation (after report is approved)

### Step 0: Create a worktree

Before writing any code, create a git worktree so your changes are isolated
from other parallel sessions:

```bash
cd /home/arthur/repos/isa2fol
git worktree add .claude/worktrees/<task-name> HEAD
cd .claude/worktrees/<task-name>/rs
```

**Branch from `HEAD`, not from `main`.** Work lives on a long-running feature
branch far ahead of `main`; branching from `main` silently discards it. There is
no local `master` — `origin/master` is stale, `origin/HEAD -> origin/main`.

Skip the worktree when no other session is running: it exists to isolate
parallel work, not as ceremony. Say which you chose.

All implementation work happens in the worktree. After the fix is complete
and verified, merge back to the branch you started from.

### Step 1: Write a test or verification

For bugs in a single function or pass, write a unit test:

```rust
#[test]
fn descriptive_name_of_what_was_broken() {
    // Design: [explain the Isabelle construct and its correct semantics]
    // [explain what went wrong and why]
    //
    // Isabelle: [original construct, e.g. ⋀x::i. P(x) ⟹ Q(x)]
    // Bug:     [what the buggy code produces]
    // Correct: [what the correct output should be]

    // ... test setup ...
    let result = /* exercise the buggy path */;

    // CURRENT (wrong) behavior — proves the test hits the bug:
    assert_eq!(result, "wrong_output");

    // TODO after fix: change to correct behavior:
    // assert_eq!(result, "correct_output");
}
```

Run it capped and confirm this test PASSES (asserting the broken output).

For bugs that span multiple pipeline stages (e.g., claim-proof encoding
mismatch), use the corpus census tests as the verification instead:
1. Record what `the_p4_blocker_census` and the walk's `w.failed` say now
2. This is your "before" baseline

### Step 2: Flip to correct behavior

Change the assertion to what the output SHOULD be (unit test), or define
the expected checker improvement (integration test). The test now FAILS.

### Step 3: Implement the fix

Make the test pass with the minimal correct fix. Do not add unrelated
changes, refactors, or "improvements."

**If the fix doesn't work cleanly after 2 attempts — STOP.** Do not hack,
do not add workarounds, do not add guards. A fix that requires hacks means
the diagnosis was wrong. Go back to the Report step:

1. State what you tried and why it failed
2. Explain what this reveals about the actual root cause
3. Re-investigate with this new information
4. Present an updated Report — include whether you recommend reverting
   the previous attempt or building on it
5. **Wait for user approval before attempting the next fix**

This is recursive. Every iteration requires a Report and user approval
before any code is written. The investigation is not done until the fix
is clean.

### Step 4: Clean up

Remove TODO comments from tests. Keep only the correct assertion with the
design comment.

## Verification and merge

After the fix is implemented and tests pass:

1. **Run the full suite**, always capped (CLAUDE.md rule 10):
   ```bash
   PROOF_CHECKER=~/repos/fol-zfc-comb/bazel-bin/src/tools/proof_checker \
     MEM=16G scripts/capped.sh swift test
   ```

2. **Record numbers**: passed/failed, and the census counts your change touches.

3. **Check for regressions**: compare against the baseline from before your fix.
   `.claude/STATE.md` §0 holds it. Zero lost is required, and the baseline
   failures are the ones §0 names — not zero.

4. **Rebase and merge** onto the branch you started from. Other sessions may
   have committed since you branched, so always rebase first:
   ```bash
   cd /home/arthur/repos/isa2fol/.claude/worktrees/<task-name>
   git rebase feature/<branch>
   # resolve conflicts if any, re-run the suite after rebase
   cd /home/arthur/repos/isa2fol
   git merge --ff-only .claude/worktrees/<task-name>
   git worktree remove .claude/worktrees/<task-name>
   ```

5. **Include numbers in commit message**: every commit must state the
   verification result so regressions are traceable:
   ```
   Fix iff_elim direction in optimize pass

   <description>

   Results: 542 passed, 5 failed -- the same baseline failures, 0 regressions.
   ```

6. **Re-pin what moved.** Coverage changes move count pins across `theorem/`
   and `export/` that are not discoverable from the change; run the suite and
   re-pin from MEASUREMENT. Update `.claude/STATE.md` §0 if a row moved.

## Sharing findings across sessions (Mode 1 only)

After completing Mode 1 diagnosis, record each distinct issue so parallel
sessions can pick up related work.

**⚠ `project_status.md` AND `project_parallel_tasks.md` DO NOT EXIST** and the
project memory directory is empty. Until someone designs that split
deliberately, `.claude/STATE.md` is the durable record — §4 for what is
verified, §5 for what is not, §6 for what needs a decision. Do NOT create the
two files below on the strength of this paragraph alone.

### What to save

Update `project_parallel_tasks.md` with each distinct issue found:
- **Symptom**: checker error message pattern
- **Root cause**: which pipeline phase, what assumption is wrong
- **Example proofs**: 2-3 specific proof names to reproduce
- **Fix location**: file + function where the fix belongs
- **Orthogonality**: whether this issue can be fixed independently of others

### Orthogonality analysis

For each issue found, state whether it is:
- **Orthogonal** — can be fixed in a separate session without conflicts.
  Different issues are orthogonal when they touch different pipeline phases,
  different code paths, or different proof populations.
- **Dependent** — must be fixed in sequence because the fix for one changes
  the error profile of another (e.g., fixing A reveals B, or A and B touch
  the same code).
- **Overlapping** — same proofs fail for multiple reasons; fixing one changes
  which error the proof hits. Note the overlap population.

Group orthogonal issues as separate tasks that parallel sessions can claim.
Group dependent issues as a single ordered task.

### When to save

- After Mode 1 Step 4 (Diagnose) — save immediately, before presenting report
- After implementation — update with fix status and new numbers

Counts live in the tests that produce them and in `.claude/STATE.md` §0 —
never in prose that nothing re-runs.

## Hard Rules

- **NEVER** propose adding a fallback, guard, unwrap_or_default, or
  skip-when-not-found as the fix. If a value is missing, the bug is WHY
  it's missing.
- **NEVER** write code before presenting the report and getting approval.
- **NEVER** say "I couldn't determine the root cause" and propose a
  workaround. If you can't explain WHY the bad state occurs, keep
  investigating.
- **ALWAYS** read CLAUDE.md before starting — especially the Coding Rules
  and Debugging Methodology sections.
- **ALWAYS** save investigation findings to memory files immediately after
  Mode 1 RCA, not after being reminded.
