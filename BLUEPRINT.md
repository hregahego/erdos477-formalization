# Blueprint: Erdős Problem 477 — the thirteenth powers tile ℤ (have a tiling complement)

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`
(Liu–Peng–Yu–Tao–Wang–Zhao). Let `B = {m¹³ : m ∈ ℤ}` be the set of thirteenth
powers and `D = B − B` its difference set. The construction builds, by a greedy
`ℕ`-indexed process, a set `A ⊆ ℤ` whose translates `a + B` (`a ∈ A`) partition
`ℤ`: every integer `n` is `a + m¹³` for a **unique** pair `(a, m)`. The one idea
that makes it work: for `c` not a thirteenth power the "bad shifts"
`S_c(T) = {t : |t| ≤ T, t¹³ − c ∈ D}` are *sparse* (`|S_c(T)| = O_c(T^{5/6}) =
o(T)`), so finitely many constraints exclude only `o(T)` of the `2T+1` candidate
shifts and a good shift always remains — which is exactly the hypothesis a purely
combinatorial greedy criterion needs to produce the tiling complement.

- **Headline target (frozen theorem `erdos_477`).**
  `∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n`. The
  uniqueness is over the *pair* `(a, m)`; it references only `Set ℤ` and integer
  arithmetic (no custom predicate) so its faithfulness is self-evident. It is
  assembled from `greedy_tiling` (the combinatorial criterion), `criterion_for_B`
  (its hypothesis, verified for `B`), and `pow13_injective` (to upgrade `(a,b)`-
  uniqueness to `(a,m)`-uniqueness).
- **Recommended intermediate milestone (prove first):** `greedy_tiling` — the
  pure set-theoretic criterion "if every finite `C ⊆ ℤ\B` admits `b ∈ B` with
  `(C − b) ∩ (B−B) = ∅`, then `B` has a tiling complement". It is self-contained
  (no number theory), de-risks the whole project, and is citable on its own. The
  **mathematical heart** is `badShift_bound` (the `O_c(T^{5/6})` estimate), which
  is the only place the deep external input enters.
- **Setting / ground assumptions:** everything lives over `ℤ`; the counting
  bound is stated over `ℝ` (real exponent `5/6` via `Real.rpow`). No analysis is
  formalized *inside* the development — the single analytic result (Heath-Brown's
  determinant-method count) is isolated as one `axiom`. Route B (elementary
  Vandermonde exclusion) is used, so **nothing else is axiomatized**: no
  Brownawell–Masser, no Mason–Stothers, no function-field machinery.

> **Why this is tractable.** The whole proof is finite/combinatorial once the one
> analytic count is assumed: a greedy `ℕ`-recursion, an explicit cofactor
> inequality (`κ = 1/2`, no compactness), a bounded-degree polynomial-coefficient
> argument, and cardinality bookkeeping. The real risk is **mis-modeling**, not
> depth: (a) weakening the headline's `∃!` (unique pair) to mere existence or to
> `(a,b)` without the `m ↦ m¹³` injectivity upgrade; (b) softening `no_linear_param`
> — the exclusion must cover *all* linear (`natDegree ≤ 1`) triples, not just a
> couple; (c) stating the axiom too strongly (baking in the conclusion) or losing
> the `c ∉ B ⟹ u ≠ v` hypothesis that makes bad shifts sparse; (d) crude bounds
> that degrade the coordinate estimate `T^{13/12}` to `O(T²)` and destroy `o(T)`.

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is a compiling skeleton in which **every `Definition` and
every `Theorem` statement is written and frozen**, all proofs `:= sorry`. Once
frozen, `Erdos477/Defs.lean` and `Erdos477/Theorems.lean` are **never edited
again** during proving. Everything proved later lives in `Erdos477/Proofs/**`
and may not change a single character of the frozen statements.

> **★ SETUP PREREQUISITE — the Heath-Brown axiom must be permitted.** This proof
> assumes **exactly one** deep analytic result as a Lean `axiom`:
> `Erdos477.heath_brown_diagonal_13` (Heath-Brown 2009, Theorem 2, specialized —
> see §2 below). It is the textbook example of an assumed certificate (the
> determinant method is far beyond current formalization). The current
> `USER_NOTES.md` says *"None — no assumed axioms"*, which would make `verify.sh`
> checks (2) and (4) correctly **reject** this axiom and the project unbuildable.
> **The user must widen the axiom policy in `USER_NOTES.md` to permit
> `heath_brown_diagonal_13` before `init.py` runs.** `init.py` then declares the
> axiom in `Defs.lean` and records its fully-qualified name
> (`Erdos477.heath_brown_diagonal_13`) in `scripts/ALLOWED_AXIOMS.txt`; from then
> on `verify.sh` permits that name (plus the standard three) and bans every other
> axiom. The architect does not edit `USER_NOTES.md` — the user owns it.

### 1. Create the Lean project

```bash
cd /Users/siyua/dev/erdos477-formalization
lake +leanprover/lean4:v4.31.0 new Erdos477 math   # pin a recent stable toolchain
# pin Mathlib in lakefile.toml + lake-manifest.json to the matching rev, then:
lake exe cache get
lake build            # must succeed on the bare skeleton before anything else
```

`init.py` should pin the latest stable `lean-toolchain` and the matching Mathlib
rev (both recorded in `lake-manifest.json`); `v4.31.0` above is only a concrete
example. Then reshape the generated tree into the frozen layout:

```
erdos477-formalization/
  Erdos477/
    Defs.lean                     -- FROZEN: B, D, Qcof, Sset + the HB axiom
    Theorems.lean                 -- FROZEN: the 10 frozen statements as `sorry`
    Proofs/
      Elementary/Basic.lean       -- Layer 0: L0.1–L0.6 (pow13_injective, Dset_neg_mem)
      Cofactor/Basic.lean         -- Layer 1: L1.1–L1.2 (cofactor_lower_bound, pow13_gap, factor)
      ParamExclusion/Basic.lean   -- Layer 2: L2.1 (no_linear_param, Route B)
      Greedy/Basic.lean           -- Layer 4: L4.1 (greedy_tiling) — self-contained
      BadShift/Basic.lean         -- Layer 3: P3.1 (badShift_bound) — uses the HB axiom
      Assembly/Basic.lean         -- Layer 5: P5.1 (criterion_for_B) + erdos_477
    Discharge.lean                -- `@Frozen = @Proof := rfl` for every frozen name
    Solution.lean                 -- restates each frozen theorem in Erdos477.Solution, proven
  Erdos477.lean                   -- imports everything
  SKETCH.md                       -- the problem + NL proof sketch (math source of truth)
  BLUEPRINT.md                    -- this file
  USER_NOTES.md                   -- user's special instructions / permitted assumed-axioms
  PROGRESS.md                     -- append-only work log (workers write here; see §4)
  TASKS.md                        -- append-only delegation log (Plan agent; see §5)
  REVIEW.md                       -- append-only audit log (Review agent; see §5)
  scripts/
    verify.sh                     -- the verification harness
    frozen.sha256                 -- SHA-256 pins of Defs.lean + Theorems.lean
    ALLOWED_AXIOMS.txt            -- axiom allowlist init.py derives from USER_NOTES.md
```

All support declarations live in `namespace Erdos477` (never shadow a frozen
name). `Solution.lean` re-exposes each frozen theorem as
`Erdos477.Solution.<name>` after it is proven; `Discharge.lean` machine-checks
that each proof has *exactly* the frozen type (`@Frozen = @Proof := rfl`).

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, in dependency order. **Make decisive
modeling choices here and write them down — they cannot change later.**

**D1. `Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}`** — the thirteenth powers.
- *MODELING DECISION.* A `Set ℤ` comprehension, not a `Finset`/`Subtype` (`B` is
  infinite). The witness order is `b = m ^ 13` (not `m ^ 13 = b`) to match the
  sketch's phrasing and keep `Bset`-membership introductions uniform. `0 ∈ Bset`
  via `m = 0` (L0.1) is used repeatedly, so this shape is deliberate. Rejected: a
  `Set.range (· ^ 13)` encoding — equal, but the explicit `∃ m` unfolds more
  predictably in the `criterion_for_B`/`erdos_477` bookkeeping.

**D2. `Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}`** — the difference
set `D = B − B`.
- *MODELING DECISION.* Rendered directly as `{u¹³ − v¹³}`, **not** as the generic
  `B − B = {x − y | x ∈ B, y ∈ B}`. The two are *equal* (support lemma
  `Dset_eq_Bset_sub` in `Proofs/Assembly`), but the `u,v`-form is what every
  number-theoretic step (`Dset_neg_mem`, the bad-shift analysis) manipulates. The
  general `greedy_tiling` theorem is stated over an **abstract** `B` with its own
  `{d | ∃ x ∈ B, ∃ y ∈ B, d = x − y}` set, precisely so it does not depend on
  this concrete choice; the bridge is `Dset_eq_Bset_sub`. Do not conflate the two
  in a frozen statement.

**D3. `Qcof {R : Type*} [CommRing R] (u v : R) : R := ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)`**
— the degree-12 homogeneous cofactor `Q(u,v)` in `u¹³ − v¹³ = (u−v)·Q(u,v)`.
- *MODELING DECISION.* Polymorphic over a `CommRing` so the *same* definition
  serves the integer factorization (`pow13_sub_pow13_factor` at `ℤ`) and the real
  lower bound (`cofactor_lower_bound` at `ℝ`); casting commutes with it via
  `push_cast`. The exponent `12 - i` uses ℕ-truncated subtraction, which is exact
  on `range 13` (`i = 0..12`). Rejected: two separate `ℤ`/`ℝ` definitions (would
  need a compatibility lemma and risk drift). Rejected: `Polynomial`/`Finset.geom`
  wrappers (heavier; the bare sum is what `ring`/`geom_sum₂_mul` want).

**D4. `Sset (c : ℤ) (T : ℤ) : Finset ℤ` — the bad shifts `S_c(T)`.**
```lean
open Classical in
noncomputable def Sset (c T : ℤ) : Finset ℤ :=
  (Finset.Icc (-T) T).filter (fun t => t ^ 13 - c ∈ Dset)
```
- *MODELING DECISION.* A `Finset` obtained by `filter` over `Finset.Icc (-T) T`,
  made `noncomputable` via `Classical` decidability of the undecidable predicate
  `t¹³ − c ∈ Dset`. This gives `Sset.card` directly (the object the count bounds)
  and a clean `Finset.card_le_card` route in `criterion_for_B`. Rejected: a
  `Set ℤ` + `Set.ncard` + separate `Set.Finite` proof (more finiteness
  bookkeeping). The interval is `Icc (-T) T`, giving `2T+1` candidates
  (`Int.card_Icc`), which is what the strict count `< 2T+1` in P5.1 consumes — do
  **not** silently switch to `Ico`/`Ioo` or a one-sided range.

**D5. The Heath-Brown axiom (assumed certificate — declared as an `axiom`).**
```lean
/-- Heath-Brown, *Sums and differences of three k-th powers*, J. Number Theory
129 (2009), Theorem 2, specialized to the diagonal cubic-free form `x¹³+y¹³+z¹³=M`.
Assumed (the determinant method is far beyond current formalization). Permitted
via USER_NOTES.md / scripts/ALLOWED_AXIOMS.txt. -/
axiom heath_brown_diagonal_13 (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
        p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
        p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
        p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      (({v : ℤ × ℤ × ℤ | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = M ∧
          |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ X ∧ |(v.2.2 : ℝ)| ≤ X}).ncard : ℝ)
        ≤ K * X ^ ((10 : ℝ) / 13)
```
- *MODELING DECISION.* The **conditional** form (SKETCH §3, "recommended Lean
  form"): the exclusion hypothesis `hexcl` is provided by `no_linear_param`, so
  the axiom never has to *define* "lies on a parametrization" or nonsingularity.
  Stated for arbitrary nonzero `M` (the paper's `ε_c = sgn(−c)` sign
  normalization is absorbed — SKETCH §3 point 1), all `X ≥ 1` (the bounded range
  `X < |M|` folded into `K` — SKETCH §3 point 3), with the real exponent
  `X^(10/13)` via `Real.rpow`. `natDegree pᵢ = 0` denotes "constant" (covers the
  zero polynomial). **This is the ONLY axiom.** Do not strengthen it (e.g. drop
  `hexcl`, drop `hM`, or replace `ncard` by a value that presupposes the bound) —
  a too-strong axiom is a silent cheat. Do not add a second axiom (Route B needs
  none).

> **Cheat watch (Defs).** Each predicate must be the **genuine textbook notion**,
> quantified exactly as the sketch states it. `Bset`/`Dset` are the honest infinite
> sets — never a finite truncation. `Sset` uses `|t| ≤ T` (⇒ `2T+1` candidates) —
> never a smaller window that makes the pigeonhole trivially succeed. The HB axiom
> must keep **both** its hypotheses (`hM : M ≠ 0` and the full `hexcl` over *all*
> linear triples) and conclude only the `O(X^{10/13})` **bound** — never a form
> that already contains the sparsity you must derive. Adding a hypothesis to, or
> weakening the conclusion of, any of these makes the headline vacuous.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of 10 frozen statements, all `:= sorry`, then freeze
the file. Each renders a claim of `SKETCH.md` faithfully and minimally, with a
stable binding name (referenced by `verify.sh`, `Discharge.lean`, `Solution.lean`,
`init.py` — these names cannot drift).

```lean
-- L0.2 — D is symmetric.
theorem Dset_neg_mem {d : ℤ} (hd : d ∈ Dset) : -d ∈ Dset := sorry

-- L0.3 — odd-power injectivity (needed for the (a,b)→(a,m) uniqueness upgrade).
theorem pow13_injective : Function.Injective (fun m : ℤ => m ^ 13) := sorry

-- L1 factorization (§4 display) — u¹³ − v¹³ = (u − v)·Q(u,v).
theorem pow13_sub_pow13_factor (u v : ℤ) :
    u ^ 13 - v ^ 13 = (u - v) * Qcof u v := sorry

-- L1.1 — explicit cofactor lower bound (κ = 1/2), over ℝ.
theorem cofactor_lower_bound (u v : ℝ) :
    (1 / 2 : ℝ) * max |u| |v| ^ 12 ≤ Qcof u v := sorry

-- L1.2 — gap bound for distinct integer thirteenth powers.
theorem pow13_gap (u v : ℤ) (huv : u ≠ v) :
    (1 / 2 : ℝ) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := sorry

-- L2.1 — exclusion of linear parametrizations (Route B); supplies HB's hexcl.
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := sorry

-- P3.1 — the bad-shift estimate |S_c(T)| ≤ K_c · T^(5/6)  (the mathematical HEART).
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := sorry

-- L4.1 — greedy tiling criterion (self-contained combinatorics), abstract B.
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := sorry

-- P5.1 — B satisfies the criterion's hypothesis H.
theorem criterion_for_B :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := sorry

-- Theorem 1.1 — HEADLINE.
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := sorry
```

Mapping to `SKETCH.md`:

| Frozen name | Sketch item | Role |
| --- | --- | --- |
| `Dset_neg_mem` | L0.2 | support (symmetry of `D`), used in L0.6 & L4.1 |
| `pow13_injective` | L0.3 | support, used in the headline uniqueness upgrade |
| `pow13_sub_pow13_factor` | §4 factorization | support algebraic identity |
| `cofactor_lower_bound` | L1.1 | support, the explicit `κ = 1/2` bound |
| `pow13_gap` | L1.2 | support, coordinate size control feeding P3.1 |
| `no_linear_param` | L2.1 | supplies `hexcl` of the HB axiom |
| `badShift_bound` | P3.1 (Prop 4.1) | **milestone / heart** — only user of the HB axiom |
| `greedy_tiling` | L4.1 (Lemma 5.1) | **milestone** — self-contained, prove first |
| `criterion_for_B` | P5.1 (Prop 5.2) | verifies `H` for `B` |
| `erdos_477` | Theorem 1.1 | **HEADLINE** payoff |

**Why these 10.** The decidable/self-contained *heart* is `badShift_bound` (the
only theorem touching the axiom) and `greedy_tiling` (pure combinatorics). The
support lemmas (`Dset_neg_mem`, `pow13_injective`, `pow13_sub_pow13_factor`,
`cofactor_lower_bound`, `pow13_gap`, `no_linear_param`) are the honest renderings
of L0–L2 that feed them. `criterion_for_B` is the bridge, and `erdos_477` is the
payoff. Trivial facts L0.1 (`0 ∈ B`), L0.4 (rational root), L0.5 (`c ≠ 0`), L0.6
(`c − t¹³ ∈ D ↔ t¹³ − c ∈ D`) are **not** frozen — they are one-line support
lemmas inside `Proofs/**` (L0.6 is a direct corollary of `Dset_neg_mem`).

**Re-build gate.** After freezing, `lake build` must succeed (all `sorry`, but
the *statements* must typecheck — in particular `Sset`, `Qcof`, and the axiom
must elaborate). Do not write a line of proof until the skeleton compiles. Record
the SHA-256 of `Defs.lean` and `Theorems.lean` into `scripts/frozen.sha256`, then
log a PROGRESS entry: "SETUP frozen, skeleton builds, pins recorded."

### 4. Progress logging (`PROGRESS.md`, append-only — MANDATORY)

There is a single shared log at the repo root, **`PROGRESS.md`**. It is the
project's memory: read by an auditor and by freshly launched agents with **no
prior context** who must figure out, from the log alone, what is done, in
progress, and where to start. Read it first, write it last.

**Inviolable rules (read before doing anything):**

- **APPEND ONLY. NEVER delete, edit, overwrite, reword, or "tidy up" any existing
  entry — not your own, not anyone else's, not ever.** The log is immutable
  history. If something you wrote earlier turns out wrong, append a *new* entry
  correcting it (`📝 decision`, "supersedes the entry at <timestamp>"). Deleting
  or rewriting history is itself a cheating signal.
- **Every entry is timestamped and stage-annotated.** Get real UTC with
  `date -u +"%Y-%m-%dT%H:%M:%SZ"` — never invent or approximate a timestamp.
- **One entry per event, newest appended at the bottom**, in this exact format:

  ```
  ## <UTC timestamp> — <stage/item, e.g. "Stage BadShift · badShift_bound">
  Agent: <your short label, e.g. "agent-badshift">
  Status: ✅ proved | ⚠️ blocked | 🔧 in progress | 📝 decision
  Check: <#print axioms result, lake build result, or n/a>
  Note: <one or two lines — what you did, key lemma used, or exactly what blocks you>
  Next: <for a ✅/⚠️ entry: what this unblocks or what a follow-up agent should do
         next, with exact lemma/file names to build on; "n/a" only if truly terminal>
  ```

- **The `Next:` line is mandatory on every `✅` and `⚠️` entry.** Point the next
  agent at the related work — which stage is now unblocked, the exact names of the
  lemmas/defs you produced, and any gotcha. A fresh agent should read the latest
  entries and know exactly where to start.
- **Log at least when you:** (a) start a stage (`🔧 in progress`, so two agents
  don't collide), (b) finish a lemma/stage (`✅`, with `#print axioms` output as
  `Check:`), (c) hit a blocker (`⚠️` — write the *exact* failing goal/error, then
  move to the next independent target rather than thrashing), or (d) make a
  non-obvious modeling/proof decision (`📝`).
- **Never fake a `✅`.** Only mark proved what compiles with a clean
  `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`, plus the
  permitted `Erdos477.heath_brown_diagonal_13` where the theorem legitimately uses
  it; no `sorryAx`, no `native_decide`/`Lean.ofReduceBool`). A `✅` that does not
  match the build state is the most serious audit failure.
- **Do not stop to ask for confirmation between stages — work straight through**,
  logging as you go.

**Why this matters (do not skip):** `PROGRESS.md` is the input to a
**faithfulness / cheating audit conducted by the orchestrator, not by you.** The
auditor cross-checks every `✅` against the actual Lean source and axiom output,
and checks that no frozen file or earlier log entry was tampered with. An
accurate, complete, append-only log protects your work; gaps, edited history, or
unsupported `✅`s cause the stage to be re-audited or discarded.

### 5. The iteration loop & agent-onboarding protocol

After SETUP the project is driven by an **orchestrator** running repeated
iterations of three phases, executed by short-lived agents that share **no memory
beyond the files on disk** — they coordinate entirely through `TASKS.md`,
`PROGRESS.md`, and `REVIEW.md` (all append-only):

1. **PLAN** — one agent reads `REVIEW.md` (the auditor's prior findings — its
   "Required follow-ups" are top priority), `PROGRESS.md`, `SKETCH.md`, and
   `BLUEPRINT.md`. It chooses the most valuable batch of work that respects the
   dependency graph, splits it across **up to 4 parallel workers with
   NON-OVERLAPPING files**, and **appends a `## Iteration N` block to `TASKS.md`**
   with one `Agent k:` line per active worker (inactive workers omitted). It
   writes no proofs.
2. **WORKERS** — up to 4 agents run **in parallel**, one per `Agent k:` line.
   Each owns only the files its line assigns (this is what makes parallelism
   collision-free).
3. **REVIEW** — one independent, adversarial auditor re-runs the build,
   `#print axioms`, and `scripts/verify.sh`, checks faithfulness against
   `SKETCH.md`/`BLUEPRINT.md`, and **appends a `## Review — Iteration N` block to
   `REVIEW.md`** ending in `Verdict: COMPLETE | INCOMPLETE`. Every 5th iteration
   is a full-project audit. The loop ends when a verdict is `COMPLETE` and a final
   full audit confirms it.

**Worker onboarding ritual — do this BEFORE writing any code:**

1. **Read `TASKS.md`**, find `## Iteration N`, then your own `Agent k:` line.
   *That line is your assignment.* Ignore the other agents' lines (they run now).
2. **Read `PROGRESS.md` end to end.** Respect every `✅` (reuse, don't redo),
   `🔧` (another agent holds it — do not touch), `⚠️` (blocked), `📝` (a fixed
   decision you must follow).
3. **Read the `BLUEPRINT.md` stage(s) your task names — including the Cheat-watch
   box — and the cited `SKETCH.md` step(s).** The cheat-watch boxes are binding.
4. **Append a `🔧 in progress` entry** to `PROGRESS.md` claiming your work, then
   work only on your assigned files, then append `✅`/`⚠️` as you go.

**Dependency discipline.** Respect the order graph in "Suggested formalization
order"; the Plan agent must never assign work whose prerequisites are not yet
`✅`. Workers must **never edit the frozen `Defs.lean`/`Theorems.lean`** and must
**never weaken a frozen statement** — if a task seems to need that, append a `⚠️`
entry describing the obstacle and stop, rather than touching a frozen file.

---

## Part 0 — What Mathlib already gives you (reuse, do not rebuild)

| Need | Mathlib handle |
| --- | --- |
| odd-power strict monotonicity / injectivity on `ℤ` | `Odd.strictMono` / `Odd.pow_right_injective` / `Odd.pow_left_injective` (locate with `loogle`/`leansearch`) |
| `a^n − b^n = (a−b)·∑ aⁱ b^{n−1−i}` | `Commute.geom_sum₂_mul` / `geom_sum₂_mul_comm` / `mul_comm`+`geom_sum₂_mul` |
| geometric-sum identity `(1−s)·∑_{j<n} sʲ = 1 − sⁿ` | `geom_sum_mul` / `mul_geom_sum` / `Finset.geom_sum_eq` |
| Vandermonde determinant (distinct nodes ⇒ nonzero) | `Matrix.det_vandermonde` (or hand-rolled 2×2/3×3 — usually simpler here) |
| binomial expansion of `(a·X + C b)^13` | `add_pow`; coeff via `Polynomial.coeff_*`, `Polynomial.eq_X_add_C_of_natDegree_le_one` |
| interval cardinality `|Icc (−T) T| = 2T+1` | `Int.card_Icc`, `Int.toNat_of_nonneg` |
| filter / injective-image / biUnion card bounds | `Finset.card_filter`, `Finset.card_le_card_of_injOn`, `Finset.card_biUnion_le`, `Finset.card_lt_card`, `Finset.exists_of_ssubset` |
| enumeration `ℕ ≃ ℤ` for the greedy recursion | `Denumerable ℤ` / `Denumerable.eqv ℤ` |
| classical choice (pairs `(u_t,v_t)`, `b_j`, `t₀`) | `Classical.choose`/`Exists.choose`/`Classical.dec` |
| real-exponent algebra (`(T^{13/12})^{10/13} = T^{5/6}`) | `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_nonneg` |
| `Set.ncard` of the solution box (in the axiom's conclusion) | `Set.ncard`, `Set.Finite.subset` |

**Hinges & avoidances.** The whole proof hinges on two Mathlib pieces:
`geom_sum₂_mul` (for the factorization) and `Matrix.det_vandermonde` (for the
exclusion; can be sidestepped by explicit 2×2/3×3 elimination). Machinery you can
**avoid**: no compactness / `IsCompact.exists_isMinOn` (the cofactor bound uses
the explicit `κ = 1/2`); no Mason–Stothers / Brownawell–Masser / function fields
(Route B only); no `Polynomial.roots`/splitting-field theory (coefficient
comparison suffices). If the real-`rpow` bookkeeping proves painful, the
integer-only `156`-power reformulation (SKETCH §9.4) is an *internal* proof
technique — but the **frozen** `badShift_bound` statement stays in the `T^{5/6}`
`rpow` form.

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #  | Object | Role |
| -- | ------ | ---- |
| D1 | `Bset : Set ℤ` | the thirteenth powers `B = {m¹³}` |
| D2 | `Dset : Set ℤ` | the difference set `D = B − B = {u¹³ − v¹³}` |
| D3 | `Qcof {R} [CommRing R] (u v : R) : R` | degree-12 cofactor `Q(u,v)` in `u¹³−v¹³=(u−v)Q` |
| D4 | `Sset (c T : ℤ) : Finset ℤ` | bad shifts `S_c(T) = {|t|≤T : t¹³−c ∈ D}` |
| D5 | `heath_brown_diagonal_13` (`axiom`) | the one assumed analytic count (Heath-Brown 2009) |

Modeling decisions for each are recorded in Part −1 §2; later stages may
*characterize* these but may never redefine or silently swap them.

---

## Part 2 — Theorems and lemmas to prove (in order)

### Stage Elementary — Layer 0 groundwork (`Proofs/Elementary/`)

Goal: the reusable elementary facts. Produces frozen `Dset_neg_mem`,
`pow13_injective`, and the support lemmas L0.1 (`zero_mem_Bset`), L0.5
(`ne_zero_of_notMem_Bset`), L0.6 (`badShift_iff : c − t¹³ ∈ Dset ↔ t¹³ − c ∈ Dset`).

**E1 — `Dset_neg_mem` (L0.2).** `d ∈ Dset → -d ∈ Dset`. From `d = u¹³ − v¹³` take
the witness `(v, u)`: `-d = v¹³ − u¹³`. Just swap `u`,`v`; **no** sign-of-odd-power
manipulation.

**E2 — `pow13_injective` (L0.3).** `Function.Injective (· ^ 13 : ℤ → ℤ)`. 13 is
`Odd`; use `Odd.pow_right_injective`/`Odd.strictMono` (confirm exact name). Record
the corollary `x¹³ = −y¹³ → x = −y` (rewrite `−y¹³ = (−y)¹³`) as a support lemma —
it is used in `no_linear_param` and the headline.

**E3 — support L0.1/L0.5/L0.6.** `zero_mem_Bset` (`m = 0`); `c ∉ Bset → c ≠ 0`
(contrapositive of L0.1); `badShift_iff` (two applications of `Dset_neg_mem`).

> **Cheat watch (Stage Elementary).** `pow13_injective` must be the genuine
> injectivity of `m ↦ m¹³` on **all** of `ℤ` — not a `decide` over a finite range,
> not a restriction to `m ≥ 0`. `Dset_neg_mem` must be `∀ d`, not a fixed `d`.
> Guardrail `example`s: `pow13_injective` gives `(2:ℤ)^13 ≠ 3^13` and
> `(-2:ℤ)^13 ≠ 2^13`; `Dset_neg_mem` closes on an arbitrary opened witness.

### Stage Cofactor — Layer 1 explicit bounds (`Proofs/Cofactor/`)

Goal: the explicit cofactor inequality and the resulting gap bound. Produces
frozen `pow13_sub_pow13_factor`, `cofactor_lower_bound`, `pow13_gap`.

**C1 — `pow13_sub_pow13_factor`.** `u¹³ − v¹³ = (u − v) * Qcof u v` over `ℤ`. Via
`geom_sum₂_mul` (`(∑ i in range 13, uⁱ v^{12−i})·(u−v) = u¹³ − v¹³`) + `mul_comm`,
or `ring`/`Finset.sum` telescoping. Unfold `Qcof` to the `range 13` sum.

**C2 — `cofactor_lower_bound` (L1.1).** `(1/2)·max |u| |v| ^ 12 ≤ Qcof u v` over
`ℝ`. Route (SKETCH §4): WLOG `|v| ≤ |u|` by the reindex-symmetry `Qcof u v =
Qcof v u`; if `u = 0` both sides `0`; else set `s := v/u ∈ [−1,1]`, factor
`Qcof u v = u¹² · q(s)` with `q(s) = ∑_{j<13} sʲ`, and show `q(s) ≥ 1/2`:
`0 ≤ s`⇒`q ≥ 1` (the `j=0` term); `s < 0`⇒ use `(1−s)·q(s) = 1 − s¹³` with
`s¹³ < 0` (13 odd) and `0 < 1−s ≤ 2`. Then `max^12 = |u|^12 = u^12`.

**C3 — `pow13_gap` (L1.2).** For `u ≠ v` (integers), cast to `ℝ`, factor via C1,
use `|u − v| ≥ 1` (distinct integers) and `Qcof ≥ 0` (from C2): `|u¹³ − v¹³| =
|u−v|·Qcof ≥ 1·(1/2)max^12`. Note `Qcof (u:ℝ) (v:ℝ)` equals `((Qcof u v : ℤ)):ℝ`
by `push_cast` — keep the cast direction consistent.

> **Cheat watch (Stage Cofactor).** `cofactor_lower_bound` is `∀ u v : ℝ` — not
> just integer `u,v`, and not the weaker `0 ≤ Qcof`. The constant is exactly
> `1/2`; do **not** prove a vacuous bound with a smaller constant that later fails
> to give `T^{13/12}`. Do **not** replace the equality factorization by a one-sided
> inequality. Guardrail: `example : Qcof (1:ℝ) (-1) = 1` (the alternating sum);
> `example : (1/2:ℝ) * max |(1:ℝ)| |(-1)| ^ 12 ≤ Qcof 1 (-1)`.

### Stage ParamExclusion — Layer 2, Route B (`Proofs/ParamExclusion/`)

Goal: the elementary exclusion of nonconstant linear parametrizations. Produces
frozen `no_linear_param` — the `hexcl` hypothesis the HB axiom demands.

**P1 — `no_linear_param` (L2.1, Route B).** Write `pᵢ = aᵢX + C bᵢ` (from
`natDegree ≤ 1`, `Polynomial.eq_X_add_C_of_natDegree_le_one`). Extract the
coefficient equations `(E_j): ∑ᵢ aᵢ^{13−j} bᵢʲ = 0` (`j=0..12`) via `add_pow`
and `Polynomial.coeff`. Let `I = {i : aᵢ ≠ 0}`; suppose `I ≠ ∅`. By small-case
Vandermonde / bare 2×2–3×3 elimination on `|I| ∈ {1,2,3}` and coincidences of the
ratios `rᵢ = bᵢ/aᵢ` (over `ℚ`), force all `i ∈ I` to share one ratio `r` with
`∑_{i∈I} aᵢ¹³ = 0`. Then `|I| = 3 ⇒ c = 0 ∈ Bset`; `|I| = 2 ⇒ a₁ = −a₂` (E2) so
`c = (−b₃)¹³ ∈ Bset`; `|I| = 1` impossible — each contradicts `c ∉ Bset`. Hence
`I = ∅`: all `pᵢ` constant. (SKETCH §5.1 + Lean notes give the full case tree.)

> **Cheat watch (Stage ParamExclusion).** The conclusion must be `∀ p₁ p₂ p₃`
> with `natDegree ≤ 1` ⇒ *all three* `natDegree = 0` — the genuine exclusion, not
> a check of a couple of examples and not "generically true". Do not add a
> hypothesis (e.g. `pᵢ ≠ 0`, or `a₁,a₂,a₃` all nonzero) to dodge the case split.
> Keep the target `Polynomial.C (-c)` (the `M = −c` normalization the axiom
> consumes). Guardrail: `example` that a genuinely nonconstant witness like
> `p₁ = X, p₂ = -X, p₃ = C b` with `∑ pᵢ¹³ = C(-c)` forces `c ∈ Bset` — matching
> the `|I| = 2` branch.

### Stage Greedy — Layer 4 combinatorial criterion (`Proofs/Greedy/`) — MILESTONE

Goal: the self-contained tiling criterion. Produces frozen `greedy_tiling`.
**Independent of all number theory — prove first / in parallel.**

**G1 — `greedy_tiling` (L4.1).** Abstract `B : Set ℤ` with hypothesis `H`.
Enumerate `ℤ` via `Denumerable ℤ`. Build `Aseq : ℕ → Finset ℤ` by `Nat.rec` with
invariants `(I1)` `D`-separated (`∀ a a' ∈ Aⱼ, a ≠ a' → a − a' ∉ B−B`) and `(I2)`
`nᵢ ∈ Aⱼ + B` for `i ≤ j`. Case 2 uses `H` on `Cⱼ = (Aⱼ).image (nⱼ − ·) ⊆ ℤ\B`
to pick `bⱼ`, sets `aⱼ = nⱼ − bⱼ`; symmetry of the difference set (the abstract
analogue of `Dset_neg_mem`) gives both `aⱼ − a ∉ B−B` and `a − aⱼ ∉ B−B`, and
`aⱼ ∉ Aⱼ₋₁` from `0 ∈ B−B`. Take `A = ⋃ⱼ Aⱼ`; covering from `(I2)` + the
enumeration, uniqueness from `D`-separatedness (chain ⇒ both live in one `Aⱼ`).

> **Cheat watch (Stage Greedy).** Deliver the **full** `∃!` (existence *and*
> uniqueness of the pair `(a,b)`). Do not prove only existence, and do not fix `A`
> to a convenient set — it must be produced from `H`. `H` is `∀` finite `C ⊆ ℤ\B`;
> keep it universally quantified (never a fixed `C`). The difference set in the
> statement is the abstract `{d | ∃ x ∈ B, ∃ y ∈ B, d = x − y}` — do not swap in
> `Dset` here (this theorem is generic in `B`). Guardrail: instantiate `B = univ`
> and confirm the criterion still yields a valid (degenerate) tiling.

### Stage BadShift — Layer 3, the estimate (`Proofs/BadShift/`) — HEART

Goal: the `O_c(T^{5/6})` bad-shift bound. Produces frozen `badShift_bound`.
**The only theorem that uses the HB axiom.** Depends on Cofactor + ParamExclusion.

**B1 — `badShift_bound` (P3.1).** Fix `c ∉ Bset` (⇒ `M := −c ≠ 0`, via L0.5).
For each `t ∈ Sset c T`, `t¹³ − c ∈ Dset` gives `(u_t, v_t)` with `u_t ≠ v_t`
(else `c = t¹³ ∈ Bset`); set `Φ t = (u_t, −v_t, −t)`, an **injective** map (third
coordinate recovers `t`) into `{x¹³+y¹³+z¹³ = −c}`. Via `pow13_gap` (C3) and
`|t| ≤ T`: `max(|u_t|,|v_t|) ≤ C_c·T^{13/12}`, so every `Φ t` sits in the box
`max ≤ X := C_c·T^{13/12}`. Feed `no_linear_param c hc` as `hexcl` to
`heath_brown_diagonal_13 (−c)` to get `K` with `#box ≤ K·X^{10/13}`. Then
`(Sset c T).card ≤ #box ≤ K·X^{10/13} = K·C_c^{10/13}·T^{5/6}`; take
`K_c := K·C_c^{10/13}` (or any upper bound). Exponent identity
`(T^{13/12})^{10/13} = T^{5/6}` via `Real.rpow_mul`. (SKETCH §6; §9.4 gives the
integer-only internal route if `rpow` bites.)

> **Cheat watch (Stage BadShift).** Keep `hc : c ∉ Bset` live — it is exactly
> what forces `u_t ≠ v_t` and hence sparsity; dropping it collapses the bound.
> Invoke the HB axiom with the **real** `no_linear_param` as `hexcl` — never a
> `sorry`'d or specialized stand-in, and never assume the count directly. The
> exponent must land on **exactly** `5/6`; a crude `max ≤ O(T²)` bound gives
> `T^{20/13} `… breaking `o(T)` — use `T^{13/12}` faithfully. `#print axioms
> badShift_bound` must show `heath_brown_diagonal_13` (permitted) and nothing else
> outside the standard three.

### Stage Assembly — Layer 5, criterion + headline (`Proofs/Assembly/`) — HEADLINE

Goal: verify `H` for `B` and assemble Theorem 1.1. Produces frozen
`criterion_for_B` and `erdos_477`. Depends on BadShift + Greedy + Elementary.

**A1 — `criterion_for_B` (P5.1).** `C = ∅ ⇒ b = 0` (L0.1). Else, for `c ∈ C`,
`b = t¹³` is bad ⇔ `c − t¹³ ∈ Dset` ⇔ (L0.6) `t¹³ − c ∈ Dset`, so the bad `t`
with `|t| ≤ T` are exactly `Sset c T`. With `K := ∑_{c∈C} K_c` (from
`badShift_bound`), pick integer `T > K⁶`; then `|⋃_{c∈C} Sset c T| ≤ K·T^{5/6} <
T^{1/6}·T^{5/6} = T < 2T+1 = |Icc (−T) T|` (pigeonhole, `Finset.card_biUnion_le`
+ `Int.card_Icc`), giving `t₀` avoiding every `Sset c T`; set `b = t₀¹³`.

**A2 — `erdos_477` (Theorem 1.1).** Apply `greedy_tiling Bset H` with `H` from
`criterion_for_B` (bridging `Dset` to `{d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x−y}` via
support lemma `Dset_eq_Bset_sub`). Get `A` with unique `(a,b)`, `b ∈ Bset`.
Upgrade to `(a,m)`: existence since `b = m¹³`; uniqueness since `a = a'` and
`m¹³ = m'¹³ ⇒ m = m'` by `pow13_injective`. (SKETCH §8.2.)

> **Cheat watch (Stage Assembly).** `criterion_for_B` is `∀` finite `C ⊆ ℤ\Bset`
> — never a fixed/singleton `C`, never with an added size cap. The pigeonhole must
> be **strict** (`< 2T+1`) off the honest `2T+1`-element interval. `erdos_477`
> must deliver `∃!` over the **pair** `(a, m)` — the `pow13_injective` upgrade is
> mandatory; proving only `(a,b)`-uniqueness, or only existence, is the headline
> cheat. Do not weaken `∃!` to `∃`. Guardrail: `example` deriving a contradiction
> from two distinct representations of a fixed `n`.

### Discharge & Solution (after the frozen theorems are proved)

In `Erdos477/Solution.lean`, restate each frozen theorem **verbatim** in
`namespace Erdos477.Solution` and set it `:= <name>_proof` (the sorry-free
declaration from `Proofs/**`). In `Erdos477/Discharge.lean`, for each frozen name
write `example : @Erdos477.<name> = @Erdos477.Solution.<name>_proof := rfl` — this
compiles **iff** the proof has *exactly* the frozen proposition (machine-checked
no-drift). `verify.sh` checks both modules build and that
`#print axioms Erdos477.Solution.<name>` is within the allowlist for every frozen
name.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems + HB axiom; skeleton builds; pins recorded;
       USER_NOTES permits heath_brown_diagonal_13)
      │
      ├───────────────► Stage Greedy  (greedy_tiling)  ── self-contained; PROVE FIRST
      │
      ▼
Stage Elementary (Dset_neg_mem, pow13_injective, L0.* support)
      │
      ├───► Stage Cofactor (factor, cofactor_lower_bound, pow13_gap) ──┐
      │                                                                 │  (Cofactor and
      └───► Stage ParamExclusion (no_linear_param) ────────────────────┤   ParamExclusion
                                                                        ▼   independent → parallel)
                                            Stage BadShift (badShift_bound)  ◄── uses HB axiom  [HEART]
                                                                        │
                                                                        ▼
                                            Stage Assembly (criterion_for_B → erdos_477)  [HEADLINE]
                                                                        │
                                                                        ▼
                                            Discharge.lean + Solution.lean  (#print axioms clean)
```

- **Parallelizable:** `Greedy` is independent of everything (start immediately,
  alongside SETUP-review). `Cofactor` and `ParamExclusion` are independent of each
  other (run in parallel once `Elementary` is `✅`).
- **Milestone after which a citable result exists:** `greedy_tiling` (pure
  combinatorics) and, jointly, `badShift_bound` (the analytic heart).
- **Hardest engineering:** `no_linear_param` (binomial coefficient extraction +
  small linear algebra) and `badShift_bound` (choice + injective count + `rpow`
  exponent arithmetic). Budget effort there.

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them; problem-specific traps
follow.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem is hypothesis-free wherever the sketch's claim is unconditional. The
  legitimate hypotheses here are exactly `hc : c ∉ Bset` (`no_linear_param`,
  `badShift_bound`), `huv : u ≠ v` (`pow13_gap`), the criterion `H`
  (`greedy_tiling`), and `hexcl`/`hM` **inside the axiom**. Do not add any other
  `(h : …)`; do not prove a `∀` only on examples; do not replace an equality with
  a one-sided inclusion.

- **Keep every predicate the textbook definition.** `Bset`/`Dset` are the honest
  infinite sets; `H` is `∀` finite `C`; `no_linear_param` is `∀` linear triples;
  `greedy_tiling`/`erdos_477` deliver full `∃!`. Softening any quantifier can make
  the headline vacuous.

- **Get the modeling right once, in SETUP, and freeze it.** Validate before
  freezing with guardrail `example`s: `zero_mem_Bset`, `Qcof (1:ℝ) (-1) = 1`,
  `Int.card_Icc (-T) T`, and that the HB axiom elaborates. A dropped hypothesis in
  the axiom, or a wrong interval in `Sset`, silently changes the object.

- **Discharge structural facts, never `sorry` them.** The factorization is a
  `ring`/`geom_sum₂_mul` identity; the interval card is `Int.card_Icc`; injectivity
  is `Odd.*`. If you feel the urge to `sorry` an algebraic identity, you modeled
  `Qcof`/`Sset` wrong.

- **`decide` budget — and `native_decide` is BANNED.** Nothing here is a finite
  decidable check (the sets are infinite); prove everything structurally. Reserve
  `decide` for tiny numeric facts (`(13 : ℕ).Odd`, `12 - i` values). `native_decide`
  would add a compiler-trust axiom and dirty `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean`/`Theorems.lean` are
  byte-frozen (pinned in `scripts/frozen.sha256`). A missing *definition* belongs
  in a `Proofs/**` support file; a *statement* that seems wrong means a modeling
  bug to fix **before** re-freezing, not a hypothesis to bolt on.

- **Keep `#print axioms` clean.** Every solved theorem depends only on
  `{propext, Classical.choice, Quot.sound}` **plus** the single permitted
  `Erdos477.heath_brown_diagonal_13` (only `badShift_bound`, `criterion_for_B`,
  `erdos_477`, and their `Solution.*` restatements legitimately carry it; the
  Layer-0/1/2/4 lemmas must **not**). No `sorryAx`, no `native_decide`/
  `ofReduceBool`, no other axiom. Checked per theorem by `verify.sh` (checks 2, 4).

- **Assumed certificates go in as `axiom`s, never as hypotheses.** The HB count is
  assumed as the `axiom heath_brown_diagonal_13` in `Defs.lean` (SETUP), permitted
  via `USER_NOTES.md` → `scripts/ALLOWED_AXIOMS.txt`. It is **never** bolted onto a
  frozen theorem as a hypothesis `(h : …)`. No second axiom is introduced (Route B
  is elementary).

- **Problem-specific traps.**
  1. **Uniqueness upgrade `(a,b) → (a,m)`** needs `pow13_injective` (13 odd). Do
     not stop at `(a,b)`-uniqueness — the headline is over `(a,m)`.
  2. **Symmetry of `D`** is used silently (L0.6 in P5.1; `a − aⱼ ∉ D` in L4.1) —
     make `Dset_neg_mem` explicit, and its abstract analogue inside `greedy_tiling`.
  3. **`u ≠ v` from `c ∉ Bset`** in BadShift Step 1 is the crux of sparsity — never
     drop `hc`.
  4. **Exponent must be exactly `5/6`.** `max ≲ T^{13/12}` (degree-12 cofactor) ∘
     `count ≲ X^{10/13}` (HB) = `T^{5/6} = o(T)`. Any crude bound degrading `13/12`
     to `2` breaks `o(T)` and the whole pigeonhole in P5.1.
  5. **`Dset` vs abstract `B−B`.** `criterion_for_B` speaks `Dset`; `greedy_tiling`
     speaks `{d | ∃ x ∈ B, ∃ y ∈ B, d = x−y}`. Bridge with `Dset_eq_Bset_sub`; do
     not conflate them inside a frozen statement.
  6. **`Sset` window `|t| ≤ T`** gives the `2T+1` count the strict pigeonhole
     `< 2T+1` needs — keep `Icc (−T) T`, not a smaller/one-sided range.
