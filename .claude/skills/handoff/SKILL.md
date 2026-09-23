---
name: handoff
description: Save or restore working state across sessions. Use when ending a session ("wrap up", "save state", "we continue next session") or beginning one ("load state", "where were we", "continue"). Writes/reads .claude/STATE.md — final state only, never session history, and every claim carries a way to verify it first-hand.
argument-hint: save | load
allowed-tools: Read Grep Glob Bash Edit Write
---

# /handoff — state, not story

`.claude/STATE.md` is the handoff file. Two modes: `save` writes it, `load`
restores from it.

## The failure this exists to prevent

A fresh session reads a summary and **treats it as knowledge**. It never opens the
code, never re-runs the checks, and inherits the previous session's conclusions —
including the wrong ones — as settled fact. Worse, it inherits them *without their
justification*, so it cannot tell a measured claim from a guess.

Two mechanisms prevent that, and both are mandatory:

1. **Every claim carries a verification handle** — a command, a test name, or a
   `file:line`. A claim with no handle is not state; it is a belief, and it goes in
   the quarantined section.
2. **The file carries its own falsification conditions.** `§0` lists commands with
   expected outputs. Loading runs them *first*. A mismatch means the file is stale
   and must be distrusted — the code wins, always.

## Hard rules

- **NO HISTORY.** Never "we first did X, then fixed Y", never "this session
  we…", never a changelog. Git already has the history and it is better at it.
  Write only what is **true now**. If a sentence has a past-tense verb about the
  work, delete it.
  - ✗ *"Fixed the sort order bug, then added tests."*
  - ✓ *"Closure order is first-occurrence (`statement/mod.rs:186`), pinned by
    `closure_follows_first_occurrence_not_alphabetical`."*
- **Exception:** a *correction* survives if a future session would otherwise
  repeat it. Write it as a standing warning, not as an event.
  - ✓ *"Do NOT sort the closure alphabetically — `ZAppt` forces first-occurrence
    order. Logically equivalent, so nothing catches it until P6."*
- **No unverifiable numbers.** Every count/measurement names the command or test
  that reproduces it. If you cannot name one, the number does not go in.
- **Keep it short.** Target under 120 lines. A long file gets read *instead of*
  the code, which is the failure mode. Point at sources; do not summarise them.
- **Separate verified from believed.** This is the most important line in the
  file. Anything you reasoned to but did not check goes in `§5`, flagged.

---

## Mode: `save`

Write `.claude/STATE.md` with exactly these sections. Omit a section only if it is
genuinely empty; do not pad.

```markdown
# STATE — <project>
<commit sha> · <branch> · <date>.  RUN §0 BEFORE TRUSTING ANY LINE BELOW.

## 0. Staleness checks
| command | expect |
|---|---|
| `<cmd>` | `<value>` |
If any row disagrees, THIS FILE IS STALE. Trust the code and fix this file first.

## 1. Where
Worktree, branch, and how to confirm you are in the right one.

## 2. Read these first-hand
3–6 paths, each with *what to look for*. These are primary sources; §4 is not a
substitute for them.

## 3. Invariants
What must stay true, and what enforces it. Include the standing warnings —
mistakes that are silent when repeated.
| invariant | enforced by |

## 4. State
What is true now. Every row names a verification handle.
| claim | verified by |

## 5. Beliefs — NOT verified
Reasoned but unchecked. Re-derive or test before acting on any of it.

## 6. Open decisions
Needs the user. State the options and the tradeoff, not a recommendation essay.

## 7. Next action
One action, and the criterion that says it is done.
```

Before writing, **run the staleness commands yourself** so §0's expected values
are real, not remembered. Then commit the file if the repo is clean.

---

## Mode: `load`

Do these **in order**. Do not read §2–§7 before finishing step 1.

1. **Run every §0 command.** Report mismatches immediately and stop trusting the
   file where it disagrees. This is your first contact with the project and it is
   first-hand by construction.
2. **Read §1**, confirm the worktree/branch, check `git status` and `git log -1`.
3. **Open every §2 path with Read.** Actually read them. This is the step that
   the failure mode skips, and skipping it is why sessions inherit
   misunderstandings.
4. **Read §3–§7.**
5. **Spot-check.** Pick at least two `§4` rows and verify them against their
   handles. If either fails, treat all of §4 as suspect and say so.
6. **Report**: what §0 confirmed, what you verified, what you found stale, and
   the §7 next action. Do not restate §4 back to the user as if it were news —
   they wrote it.

Treat `§4` rows as **hypotheses with evidence attached**, not as facts. Treat
`§5` as explicitly unreliable. If a §4 claim matters to what you are about to do,
verify it before relying on it, however plausible it looks.

## When save and load disagree

The code is right and the file is wrong. Fix the file in the same session you
notice, and say what was stale — a handoff file that has silently rotted is worse
than none, because it is trusted.
