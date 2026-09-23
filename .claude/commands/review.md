# Code Review

Rigorous code review for the isa2fol codebase. You MUST follow this protocol
exactly. Do NOT skip sections. Do NOT approve code that violates any principle.

## Input

The user provides: $ARGUMENTS

This may be a file path, a set of files, a git diff range, "staged changes",
"last commit", or "all modified files". If empty, review all unstaged changes.

## Scope

Determine what to review:
- File path(s): review those files in full
- "staged" / "last commit" / diff range: review only the changed lines + enough
  surrounding context to judge correctness
- No argument: `git diff` for unstaged changes

## Review Dimensions

Evaluate EVERY change against ALL of the following. Each dimension gets a
verdict: PASS, ISSUE (must fix), or NOTE (non-blocking observation).

### 1. Behavioral Correctness

The code MUST produce identical output for identical input. For refactors:
- Does this change any match arm ordering that could alter behavior?
- Does this change any iteration order (HashMap, BTreeMap, Vec)?
- Does this rename or restructure anything that could affect string output?
- Does this change any early-return, continue, or break condition?
- Does this change any default value, unwrap, or error path?

**Test:** If the change claims to be a refactor, the reviewer MUST verify
no-op status. Unit tests alone are insufficient. State what end-to-end
verification is needed.

### 2. Duplication

No duplicated logic. Every concept has ONE canonical implementation.
- Is there an existing function that does the same thing?
- Are there two code paths that handle the same construct differently?
- Could a shared abstraction replace repeated patterns?
- Is there copy-paste code with minor variations?

**Standard:** Three similar lines is tolerable. Three similar blocks is not.
If you see duplication, identify the abstraction that eliminates it.

### 3. Coupling and Hardcoding

Code must be decoupled into independent, composable units.
- Are there magic strings, hardcoded indices, or literal constants that should
  be named constants or derived from data?
- Does a function reach into another module's internals?
- Does a change require updating multiple places for a single logical change?
- Are there implicit dependencies (e.g., must call A before B, ordering
  assumptions, hidden shared state)?

**Standard:** A single logical change should require editing ONE place.
If changing behavior X requires touching files A, B, and C, the abstraction
boundary is wrong.

### 4. Scalability and Abstraction

Code must accommodate growth without structural rewrites.
- Will this approach work when the input grows 10x?
- Is there a general pattern hiding behind a special case?
- Are data structures appropriate for the access patterns?
- Could a trait, enum, or generic replace a chain of if/else or match arms
  that will grow over time?

**Standard:** Adding a new variant or case should require adding ONE match arm
or ONE impl block, not touching multiple functions.

### 5. Unified Code Paths

ONE way to handle each construct. No fallbacks, no legacy paths.
- Is there a "try A, fall back to B" pattern? (NOT acceptable)
- Is there dead code, cfg-gated paths, or commented-out alternatives?
- Are there parallel implementations (e.g., two ways to sanitize names)?
- Does the code handle the "old format" alongside the "new format"?

**Standard:** If a case can't be handled, it MUST fail explicitly. Silent
degradation is a bug.

### 6. Code Clarity

Code must be immediately readable by an LLM or experienced developer scanning
at speed.
- Are variable names descriptive of their role, not their type?
- Are function names verbs that describe what they do?
- Is control flow linear (early returns for edge cases, main logic unindented)?
- Are there deeply nested blocks (3+ levels) that should be extracted?
- Is the code self-documenting, or does it require comments to explain "what"?
  (Comments should explain "why", never "what".)
- Are there long functions (50+ lines) doing multiple things that should be
  split?

**Standard:** A reader should understand each function's purpose from its
signature and first 3 lines. If you need to read the whole body to know what
it does, the name or structure is wrong.

### 7. Error Handling

Errors must be honest and informative.
- Does the code use unwrap/expect where it should propagate errors?
- Are error messages specific enough to diagnose the problem?
- Is there any silent swallowing of errors (ok(), unwrap_or_default, _ => {})?
- Does the code distinguish "can't happen" (assert/panic) from "might fail"
  (Result/Option)?

**Standard:** Every error path either recovers meaningfully or fails with
enough context to diagnose the problem without a debugger.

## Report Format

Present findings grouped by dimension. For each issue:

```
### [Dimension]: [PASS|ISSUE|NOTE]

**[file:line]** — [one-line summary]
[Explanation of why this is a problem]
[Concrete suggestion for how to fix it]
```

## Summary

End with:

```
## Verdict: [APPROVE | REQUEST CHANGES | NEEDS DISCUSSION]

Issues: N
Notes: N

[If REQUEST CHANGES: ordered list of what must change before approval]
[If NEEDS DISCUSSION: specific questions that need answers]
```

## Hard Rules

- **NEVER** approve code with duplication when an abstraction exists.
- **NEVER** approve hardcoded values that should be derived or named.
- **NEVER** approve fallback code paths. Fail or succeed, never degrade.
- **NEVER** approve a "refactor" without stating how to verify it's no-op.
- **NEVER** let "it works" override "it's wrong." Working code with bad
  structure is tech debt that compounds.
- **ALWAYS** read the actual code, not just the diff. Context matters.
- **ALWAYS** check CLAUDE.md coding rules — violations are automatic issues.
