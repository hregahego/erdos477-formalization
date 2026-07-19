# Blueprint: The thirteenth powers have a tiling complement in ℤ (Erdős 477)

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
Let `B = {m¹³ : m ∈ ℤ}` be the set of thirteenth powers and `D = B − B` its
difference set. The theorem builds a set `A ⊆ ℤ` whose translates `a + B`
(`a ∈ A`) **tile** `ℤ`: every integer `n` is uniquely `a + m¹³`. The single idea
that makes it work: for `c` not a thirteenth power, the "bad shifts"
`t` with `t¹³ − c ∈ D` are sparse — only `O_c(T^{5/6}) = o(T)` of them with
`|t| ≤ T` — so out of the `2T+1` candidate shifts a *good* one always survives
finitely many constraints, and a greedy ℕ-indexed construction assembles `A`.

- **Headline target (frozen theorem `erdos_477`).** `∃ A : Set ℤ, ∀ n : ℤ,
  ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n`. Uniqueness is over the *pair*
  `(a, m)`; it decomposes into uniqueness of the `(a, b)` representation with
  `b ∈ B` (delivered by `greedy_tiling`) plus injectivity of `m ↦ m¹³` on `ℤ`
  (13 is odd). The predicates it references — `Bset`, `Dset` — are frozen in
  `Defs.lean`. There is no separate witness theorem: `A` is produced by the
  existential proof of `greedy_tiling` specialised to `Bset`.
- **Recommended intermediate milestone (prove first): `greedy_tiling`.** The
  pure combinatorial criterion (§7 / Layer 4): *if every finite `C ⊆ ℤ∖B` has a
  `b ∈ B` with `(C − b) ∩ D = ∅`, then `B` has a tiling complement.* It is
  self-contained set theory, depends on **nothing else**, de-risks the whole
  project, and is citable on its own. Prove it before the number theory.
- **The mathematical heart (hardest engineering): `badShift_bound`.** The sparse-
  bad-shift estimate `|S_c(T)| ≤ K_c · T^{5/6}` (§6 / Layer 3). It is the only
  place the deep external input (Heath-Brown, assumed as an `axiom`) enters, and
  the only place with real-exponent arithmetic. Budget the most effort here.
- **Setting / ground assumptions:** everything is over `ℤ`; inequalities in the
  bad-shift layer are stated in `ℝ` after casting (`Real.rpow` for the `5/6`
  exponent — an integer-only reformulation is available, see Stage E). The
  exponent 13 is a fixed odd number; **no** analysis beyond casting/`rpow`
  algebra is used *outside* the one Heath-Brown axiom. Choice is used
  classically in three spots (a witnessing pair `(u_t,v_t)`, the greedy shift
  `b_j`, the good shift `t₀`); no constructive content is claimed.

> **Why this is tractable.** Four of the five layers are elementary: telescoping
> factorisation + a geometric-sum bound (Cofactor), binomial-coefficient +
> Vandermonde linear algebra (ParamExclusion), and a greedy induction on `ℕ`
> (Greedy). All the genuine analytic depth (the determinant method) is quarantined
> into **one** axiom, `heath_brown_diagonal_13`, stated in a *conditional*,
> self-contained form that never needs the notions "nonsingular form" or "lies on
> a parametrisation". The real risk is **mis-modeling**: (a) weakening the headline
> uniqueness to mere existence or dropping the `∃!`; (b) softening `S_c(T)`,
> `Bset`, or `Dset`; (c) inflating the coordinate bound `T^{13/12}` to `O(T²)`,
> which silently degrades `5/6` past `1` and *destroys* the `o(T)` sparsity the
> whole argument needs; (d) sneaking the exclusion hypothesis of the axiom in as a
> free `axiom` instead of *proving* it via `no_linear_param`.

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is to produce a compiling skeleton in which **every
`Definition` and every `Theorem` statement is written and frozen**, with all
proofs `:= sorry`. Once frozen, `Defs.lean` and `Theorems.lean` are **never
edited again** during the proving phase. Everything proved later lives in
support files and may not change a single character of the frozen statements.

### 1. Create the Lean project

```bash
cd <project-dir>          # /Users/siyua/dev/erdos477-FORM
lake +leanprover/lean4:v4.15.0 new Erdos477 math   # scaffolds Erdos477/ + lakefile
# pin Mathlib in lakefile.toml (or lakefile.lean) + lake-manifest.json to the rev
# matching the v4.15.0 toolchain, then:
lake exe cache get        # fetch prebuilt Mathlib oleans
lake build                # must succeed on the bare skeleton before anything else
```

(Any recent toolchain with a matching Mathlib rev is fine; `v4.15.0` is a
concrete pin. What matters is that `lean-toolchain` and the Mathlib rev agree and
`lake exe cache get` succeeds so Mathlib is not rebuilt from scratch.)

Layout (rename only the bracketed parts already filled in for this project):

```
erdos477-FORM/
  Erdos477/
    Defs.lean          -- FROZEN: Bset, Dset, Qcof, Sset; AXIOM heath_brown_diagonal_13
    Theorems.lean      -- FROZEN: the 5 frozen theorem statements (sorry)
    Proofs/
      Elementary/      -- Stage A: L0.1–L0.6 (0∈B, D symmetric, odd-power inj., …)
      Cofactor/        -- Stage B: L1.1, L1.2 (explicit κ = 1/2 cofactor bound)
      ParamExclusion/  -- Stage C: L2.1 (Route B: Vandermonde/case analysis)
      Greedy/          -- Stage D: L4.1 (self-contained; prove first / in parallel)
      BadShift/        -- Stage E: P3.1 (bad-shift estimate; uses the axiom)
      Assembly/        -- Stage F: P5.1 + Theorem 1.1 (criterion verified, headline)
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `Erdos477.Solution`, proven (clean names)
  Erdos477.lean        -- imports everything
  SKETCH.md            -- the problem + NL proof sketch (math source of truth)
  BLUEPRINT.md         -- this file
  USER_NOTES.md        -- user's special instructions / permitted assumed-axioms (user-owned)
  PROGRESS.md          -- append-only work log (workers write here; see §4)
  TASKS.md             -- append-only delegation log (the Plan agent writes here; see §5)
  REVIEW.md            -- append-only audit log (the Review agent writes here; see §5)
  scripts/
    verify.sh          -- the verification harness
    frozen.sha256      -- SHA-256 pins of Defs.lean + Theorems.lean
    ALLOWED_AXIOMS.txt -- axiom allowlist init.py derives from USER_NOTES.md
```

All support declarations live in `namespace Erdos477` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface; `Solution.lean`
re-exposes each as `Erdos477.Solution.<name>` after it is proven, and
`Discharge.lean` machine-checks that each proof has *exactly* the frozen type
(`@Frozen = @Proof := rfl`).

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.**

- **`Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}`** — the thirteenth powers.
  - **MODELING DECISION.** A `Set ℤ` carved by an existential, *not* a `Finset`
    (it is infinite) and *not* the range of a bundled function. The equation is
    `b = m ^ 13` (image form) rather than `∃ m, m ^ 13 = b`; either is faithful,
    but fix this orientation so support lemmas are stated once. `0 ∈ Bset` via
    `m = 0` (L0.1) is definitional-ish and used repeatedly; do not add `b ≠ 0` or
    any positivity. Exponent literal is `13 : ℕ`.
- **`Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}`** — the difference set
  `B − B`.
  - **MODELING DECISION.** Encoded *directly* as differences of two thirteenth
    powers, **not** as the Minkowski difference `Bset - Bset` of the set library.
    Rationale: the direct form is what every downstream step manipulates (`(4.1)`
    of the sketch). A support lemma `dset_eq_sub : Dset = {d | ∃ x ∈ Bset, ∃ y ∈
    Bset, d = x - y}` bridges to the `B − B` phrasing that `greedy_tiling` uses
    at the abstract level — prove it in Stage A, do **not** redefine `Dset`.
    Symmetry (`d ∈ Dset → -d ∈ Dset`, L0.2) is a lemma, not baked in.
- **`Qcof (u v : ℤ) : ℤ := ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)`** — the
  degree-12 homogeneous cofactor `Q(u,v)` with `u¹³ − v¹³ = (u−v)·Q(u,v)`.
  - **MODELING DECISION.** A `Finset.range 13` sum over `ℤ` (13 terms, `i = 0..12`,
    exponent pair `(i, 12−i)` with `12 − i : ℕ` truncated subtraction — safe since
    `i ≤ 12`). Chosen over Mathlib's `∑ i in range n, x^i * y^(n-1-i)` wrapper so
    the factorisation lemma can be proved either by `ring`-after-`Finset.sum`
    manipulation or by matching `geom_sum₂_mul`. The explicit-constant bound uses
    `κ = 1/2` over `ℝ` (L1.1) — the `ℝ`-valued statement lives in Stage B; `Qcof`
    itself stays integer-valued and is cast when needed.
- **`Sset (c T : ℤ) : Finset ℤ := (Finset.Icc (-T) T).filter (fun t => t ^ 13 - c ∈ Dset)`**
  — the bad-shift set `S_c(T) = {t : |t| ≤ T ∧ t¹³ − c ∈ D}`.
  - **MODELING DECISION.** A `Finset` (so `.card` is available and finiteness is
    free), realised as a `filter` over `Finset.Icc (-T) T`. The predicate
    `t ^ 13 - c ∈ Dset` is not decidable constructively, so open `Classical`
    (`Classical.decPred`) for the `filter`. The interval `Icc (-T) T` has
    `2T + 1` elements when `T ≥ 0` (`Int.card_Icc`); keep `|t| ≤ T` as the
    two-sided interval, **not** `Finset.range` or `t ∈ [0,T]` — the strict count
    `< 2T+1` in Stage F depends on exactly `2T+1` candidates.
- **`axiom heath_brown_diagonal_13 …`** — the ONE deep external input (see §3
  below for the exact statement and citation).
  - **MODELING DECISION.** Declared as a Lean `axiom` inside `Defs.lean` (so it
    surfaces in every `#print axioms` and is checked deterministically), in the
    *conditional* form: it takes an **exclusion hypothesis** `hexcl` (no
    nonconstant linear parametrisation) as an argument and returns the counting
    bound. This is what lets us *prove* the hypothesis (via `no_linear_param`)
    rather than assume more than necessary. It is an assumed certificate: it is
    permitted **only** if the user records it in `USER_NOTES.md`, so that init.py
    copies its name into `scripts/ALLOWED_AXIOMS.txt` and `verify.sh` whitelists
    exactly `heath_brown_diagonal_13` (and the three standard axioms), banning
    every other axiom. **Never** attach it as a hypothesis to a frozen theorem.

> **⚠️ USER ACTION REQUIRED — read before running init.py.** As of this
> scaffolding, `USER_NOTES.md` reads *"None — no assumed axioms."* That is
> **inconsistent with the mathematics**: `SKETCH.md` §3 states plainly that
> Heath-Brown's determinant-method count is far beyond current formalization
> technology and **must** be assumed as an axiom — the entire bad-shift layer
> (Stage E), and hence the headline, is *impossible* to prove without it. Under
> the current `USER_NOTES.md` the pipeline is maximally strict: init.py will not
> declare `heath_brown_diagonal_13`, `verify.sh` will ban it, and Stage E / Stage
> F cannot be completed (they would need a `sorry` or a banned `axiom`). **Before
> running init.py**, the user must add `heath_brown_diagonal_13` to the "Allowed
> axioms" section of `USER_NOTES.md` (what/why/where, per that file's template),
> naming it as the sole assumed certificate. The rest of the project (Stages A–D,
> `greedy_tiling`, `no_linear_param`) needs **no** axiom and is unaffected. This
> blueprint is written for the mathematically necessary configuration (HB
> permitted); if the user deliberately keeps the axiom banned, the achievable
> deliverable is Stages A–D plus `no_linear_param`, with `badShift_bound`,
> `criterion_holds`, and `erdos_477` left blocked.

A definition once frozen is binding: later stages may *characterize* it with
support lemmas but may never redefine or silently swap it.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook notion**,
> quantified exactly as the source states it. `Bset`/`Dset` are the *full*
> infinite sets — do not restrict to a bounded window. `Sset` must keep the
> two-sided `|t| ≤ T` (the `2T+1` count is load-bearing) and the *genuine*
> membership `t¹³ − c ∈ Dset` (not a decidable surrogate that only checks small
> `u,v`). `Qcof` must be the full 13-term sum, not a truncation. The axiom must
> keep its `hexcl` argument (conditional form) — an unconditional counting axiom
> would let a worker skip Stage C entirely and is a cheat. A "simplification" here
> can make the headline vacuous or the sparsity bound false.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each renders a claim of `SKETCH.md`
faithfully and minimally. Names are **stable and binding** (referenced by
`verify.sh`'s `ALL_THEOREMS`, `Discharge.lean`, `Solution.lean`, and `init.py`).

```lean
-- L2.1 (§5.1, Route B): the diagonal surface admits no nonconstant *linear*
-- polynomial parametrisation — i.e. the exclusion hypothesis of the axiom holds.
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0

-- P3.1 (§6, Prop 4.1): the bad-shift estimate |S_c(T)| ≤ K_c · T^{5/6}.
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)

-- L4.1 (§7, Lemma 5.1): the greedy tiling criterion (pure combinatorics).
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n

-- P5.1 (§8.1, Prop 5.2): Bset satisfies the criterion (H).
theorem criterion_holds :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset

-- Theorem 1.1 (§8.2): the headline — the thirteenth powers tile ℤ.
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n
```

Mapping to `SKETCH.md`:

- `no_linear_param` ↔ §5 L2.1 (Route B). Verifies the axiom's `hexcl`.
- `badShift_bound` ↔ §6 P3.1 / Prop 4.1. The `5/6` exponent.
- `greedy_tiling` ↔ §7 L4.1 / Lemma 5.1. Abstract `B`.
- `criterion_holds` ↔ §8.1 P5.1 / Prop 5.2. Instantiates the criterion for `Bset`.
- `erdos_477` ↔ §0 target + §8.2. The payoff existential with `∃!`.

**Why these five.** They are exactly the five layers of the architecture (§1 of
`SKETCH.md`). `greedy_tiling` is the self-contained **combinatorial** milestone;
`badShift_bound` is the analytic **heart** (and the only axiom consumer);
`no_linear_param` is the elementary linear-algebra **support** that feeds the
axiom; `criterion_holds` is the **bridge** (bad-shift sparsity ⇒ criterion);
`erdos_477` is the **payoff**. The elementary facts L0.1–L0.6 and the cofactor
bounds L1.1–L1.2 are *not* frozen as theorems — they are internal support lemmas
living in `Proofs/Elementary/` and `Proofs/Cofactor/`, consumed by the five
above; freezing them would over-constrain their exact Lean phrasing without
adding a claim of the sketch.

**Re-build gate.** After freezing, `lake build` must succeed (everything is
`sorry`, but the *statements* must typecheck — in particular `Sset`, `Qcof`,
`Bset`, `Dset` and the `axiom` must all elaborate, and `Real.rpow` must be in
scope for `badShift_bound`). Do not write a line of proof until the skeleton
compiles. Record the SHA-256 of `Defs.lean` and `Theorems.lean` into
`scripts/frozen.sha256`, then log a PROGRESS entry: "SETUP frozen, skeleton
builds, pins recorded."

### 4. Progress logging (`PROGRESS.md`, append-only — MANDATORY)

There is a single shared log at the repo root, **`PROGRESS.md`**. It is the
project's memory: it is read by an auditor (see below) and by freshly launched
agents that have **no prior context** and must figure out, from the log alone,
what is done, what is in progress, and where they should start. Treat it as the
first thing you read and the last thing you write.

**Inviolable rules (read before doing anything):**

- **APPEND ONLY. NEVER delete, edit, overwrite, reword, or "tidy up" any existing
  entry — not your own, not anyone else's, not ever.** The log is an immutable
  history. If something you wrote earlier turns out to be wrong, do **not** remove
  it: append a *new* entry that corrects it (`📝 decision`, noting "supersedes the
  entry at <timestamp>"). Deleting or rewriting history is itself treated as a
  cheating signal in the audit.
- **Every entry is timestamped and stage-annotated.** Get the real UTC time with
  `date -u +"%Y-%m-%dT%H:%M:%SZ"` — do not invent or approximate timestamps.
- **One entry per event, newest appended at the bottom**, in this exact format:

  ```
  ## <UTC timestamp> — <stage/item, e.g. "Stage C · no_linear_param">
  Agent: <your short label, e.g. "agent-stageC">
  Status: ✅ proved | ⚠️ blocked | 🔧 in progress | 📝 decision
  Check: <#print axioms result, lake build result, or n/a>
  Note: <one or two lines — what you did, key lemma used, or exactly what blocks you>
  Next: <for a ✅/⚠️ entry: what work this unblocks or what a follow-up agent should
         do next, with exact lemma/file names to build on; "n/a" only if truly terminal>
  ```

- **The `Next:` line is mandatory on every `✅` and `⚠️` entry.** Point the next
  agent at the related work: which stage is now unblocked, the exact names of the
  lemmas/defs you produced that they will consume, and any gotcha you hit. A fresh
  agent with no context should be able to read the latest entries and know exactly
  where to start — this is what makes sessions resumable.

- **Log at least when you:** (a) start work on a stage (`🔧 in progress`, so two
  agents don't collide on the same lemma), (b) finish/close a lemma or stage
  (`✅`, with the `#print axioms` output as `Check:`), (c) hit a blocker (`⚠️` —
  write the *exact* failing goal/error, then move to the next independent target
  rather than thrashing), or (d) make a non-obvious modeling or proof decision
  (`📝`). Append a prominent entry at each milestone.
- **Never fake a `✅`.** Only mark proved what compiles with a clean
  `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`, plus the
  whitelisted `heath_brown_diagonal_13` where it is legitimately used; no
  `sorryAx`, no `native_decide`/`Lean.ofReduceBool`). A `✅` that does not match
  the actual build state is the most serious audit failure.
- **Do not stop to ask for confirmation between stages — work straight through**,
  logging as you go.

**Why this matters (do not skip):** `PROGRESS.md` is the input to a
**faithfulness / cheating audit conducted by the orchestrator, not by you.** The
auditor cross-checks every `✅` entry against the actual Lean source and axiom
output, and checks that no frozen file or earlier log entry was tampered with. An
accurate, complete, append-only log protects your work from being thrown out; a
log with gaps, edited history, or unsupported `✅`s causes the whole stage to be
re-audited or discarded.

### 5. The iteration loop & agent-onboarding protocol

After SETUP, the project is driven by an **orchestrator** that runs repeated
iterations. Each iteration has three phases, executed by short-lived agents that
share **no memory** beyond the files on disk — they coordinate entirely through
`TASKS.md`, `PROGRESS.md`, and `REVIEW.md` (all append-only):

1. **PLAN** — one agent reads `REVIEW.md` (the auditor's prior findings — its
   "Required follow-ups" are top priority), `PROGRESS.md` (what is `✅`/`🔧`/`⚠️`/
   `📝`), `SKETCH.md`, and `BLUEPRINT.md`. It chooses the most valuable batch of
   work that respects the dependency graph, splits it across **up to 4 parallel
   workers with NON-OVERLAPPING files**, and **appends a `## Iteration N` block to
   `TASKS.md`** with one `Agent k:` line per active worker (inactive workers
   omitted). It writes no proofs.
2. **WORKERS** — up to 4 agents run **in parallel**, one per `Agent k:` line.
   Each owns only the files its line assigns (this is what makes parallelism
   collision-free).
3. **REVIEW** — one independent, adversarial auditor re-runs the build, `#print
   axioms`, and `scripts/verify.sh`, checks faithfulness against `SKETCH.md`/
   `BLUEPRINT.md`, and **appends a `## Review — Iteration N` block to `REVIEW.md`**
   ending in `Verdict: COMPLETE | INCOMPLETE`. Every 5th iteration is a full-
   project audit. The loop ends when a verdict is `COMPLETE` and a final full
   audit confirms it.

**Worker onboarding ritual — do this BEFORE writing any code:**

1. **Read `TASKS.md`**, find `## Iteration N`, then your own `Agent k:` line.
   *That line is your assignment* — the files you own and the lemmas to produce.
   Ignore the other agents' lines (they are running right now in parallel).
2. **Read `PROGRESS.md` end to end.** Respect every `✅` (done — reuse, don't
   redo), `🔧` (another agent holds it — do not touch), `⚠️` (blocked), and `📝`
   (a fixed modeling/proof decision you must follow).
3. **Read the `BLUEPRINT.md` stage(s) your task names — including the Cheat-watch
   box — and the cited `SKETCH.md` step(s).** Do not work from the stage title
   alone; the cheat-watch boxes are binding.
4. **Append a `🔧 in progress` entry** to `PROGRESS.md` claiming your work, then
   work only on your assigned files, then append `✅`/`⚠️` as you go.

**Dependency discipline.** Respect the order graph in "Suggested formalization
order"; the Plan agent must never assign work whose prerequisites are not yet
`✅`. Workers must **never edit the frozen `Defs.lean`/`Theorems.lean`** and must
**never weaken a frozen statement** (see the cardinal cheat rule below) — if a
task seems to need that, append a `⚠️` entry describing the obstacle and stop,
rather than touching a frozen file.

---

## Part 0 — What Mathlib already gives you (reuse, do not rebuild)

| Need                                             | Mathlib handle                                                                 |
| ------------------------------------------------ | ------------------------------------------------------------------------------ |
| odd-power strict monotonicity / injectivity on ℤ | `Odd.strictMono` / `Odd.pow_right_strictMono` / `Odd.pow_left_injective` (search `loogle`/`leansearch`) |
| `x¹³ = y¹³ → x = y`, `x¹³ = -y¹³ → x = -y`        | from the above + `neg_pow`/`Odd.neg_pow` (13 odd)                               |
| geometric sum identity `(1−s)·∑_{j<n} sʲ = 1−sⁿ` | `geom_sum_mul`, `mul_geom_sum`, `Finset.geom_sum_eq`                            |
| factorisation `aⁿ − bⁿ = (a−b)·∑ aⁱ b^(n−1−i)`    | `geom_sum₂_mul` / `Commute.geom_sum₂_mul` / `geom_sum₂_mul_comm`               |
| binomial theorem for polynomials                 | `add_pow`; coeff extraction: `Polynomial.coeff_add`, `coeff_C_mul`, `coeff_X_pow` |
| linear polynomial normal form                    | `Polynomial.eq_X_add_C_of_natDegree_le_one`, `Polynomial.natDegree_le_one_iff` |
| Vandermonde determinant (distinct nodes ⇒ ≠ 0)   | `Matrix.vandermonde`, `Matrix.det_vandermonde` (or hand-rolled 2×2/3×3)         |
| interval cardinality `#Icc (-T) T = 2T+1`        | `Int.card_Icc` (`= (b+1-a).toNat`)                                              |
| card of a filter ≤ / injective-image card        | `Finset.card_filter_le`, `Finset.card_le_card_of_injOn`, `Finset.card_biUnion_le` |
| pigeonhole `bad.card < Icc.card ⇒ ∃ t ∈ Icc, ∉ bad` | `Finset.exists_mem_not_mem_of_card_lt_card` / `ssubset` + `Finset.exists_of_ssubset` |
| enumeration `ℕ ≃ ℤ`                              | `Denumerable ℤ` / `Denumerable.eqv ℤ` / `Encodable`                             |
| real fractional-power algebra                    | `Real.rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_left_iff` |
| casting `|(t:ℝ)| = |t|`                          | `Int.cast_abs`, `abs_intCast`, `Int.cast_le`                                    |

**The two nontrivial dependencies the whole proof hinges on:** (1) the
factorisation `geom_sum₂_mul` — everything in Stage B rests on
`u¹³ − v¹³ = (u−v)·Qcof u v`; (2) `Matrix.det_vandermonde` (or the equivalent
small-case eliminations) — the core of Stage C. **Machinery you can avoid:** the
sketch's Route A (Brownawell–Masser / Mason–Stothers over function fields, §5.2)
is **not needed** — because `⌊13/10⌋ = 1`, only linear parametrisations matter and
those are excluded elementarily (Route B). Do **not** import
`Mathlib/NumberTheory/FLT/MasonStothers.lean` or introduce a second axiom.

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #  | Object                                    | Role                                                                    |
| -- | ----------------------------------------- | ----------------------------------------------------------------------- |
| D1 | `Bset : Set ℤ`                            | the thirteenth powers `{m¹³}`; the set being tiled                      |
| D2 | `Dset : Set ℤ`                            | the difference set `B − B = {u¹³ − v¹³}`; "bad" shifts live here        |
| D3 | `Qcof : ℤ → ℤ → ℤ`                        | degree-12 cofactor with `u¹³ − v¹³ = (u−v)·Qcof u v`; source of the size bound |
| D4 | `Sset : ℤ → ℤ → Finset ℤ`                 | bad-shift set `S_c(T)`; its `.card` is what Heath-Brown bounds          |
| A1 | `axiom heath_brown_diagonal_13`           | the one deep external input (determinant method), conditional form      |

(Modeling decisions for each live in Part −1 §2 — do not re-derive them.)

---

## Part 2 — Theorems and lemmas to prove (in order)

Six stages, each mapped to `Erdos477/Proofs/<Stage>/`. Order by dependency.
**Every stage ends with a Cheat-watch box.** Require a clean `#print axioms` at
each milestone.

### Stage A — Elementary facts L0.1–L0.6 (`Proofs/Elementary/`)

Goal: the trivial-but-ubiquitous lemmas everything else cites. Produces no frozen
theorem, but its lemmas are consumed by every later stage.

**A1 — `zero_mem_B`, `zero_mem_D`.** `(0:ℤ) ∈ Bset` (via `m = 0`) and `0 ∈ Dset`
(via `u = v = 0`). (L0.1)

**A2 — `dset_neg`.** `d ∈ Dset → -d ∈ Dset`, by swapping `u,v`
(`u¹³ − v¹³ ↦ v¹³ − u¹³`). *No* odd-power sign manipulation. (L0.2 — symmetry of
`D`; used silently by the paper in both `criterion_holds` and `greedy_tiling`.)

**A3 — `pow13_inj`.** `m ↦ m ^ 13` is injective on `ℤ` (13 odd ⇒ strictly
monotone). Corollaries: `x¹³ = y¹³ → x = y` and `x¹³ = -y¹³ → x = -y`. (L0.3)

**A4 — `not_B_ne_zero`.** `c ∉ Bset → c ≠ 0` (from A1). (L0.5)

**A5 — `mem_D_symm_shift`.** For `c t : ℤ`, `c − t¹³ ∈ Dset ↔ t¹³ − c ∈ Dset`
(A2 both directions). (L0.6)

**A6 — `dset_eq_sub`.** `Dset = {d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x − y}`
(unfold membership both ways). Bridges `Dset` to the abstract `B − B` form used
by `greedy_tiling`.

> **Cheat watch (Stage A).** These are trivial but must be *stated and proved*,
> not `sorry`'d or inlined ad hoc — the audit checks symmetry of `D` (A2) and
> odd-power injectivity (A3) are genuine lemmas, since the whole `∃!` uniqueness
> and the bad-shift reindexing silently depend on them. Do **not** prove `pow13_inj`
> only on a bounded range or only for nonneg inputs — it is a global `Function.Injective`.
> Do **not** state `dset_eq_sub` as a one-way `⊆`; it is an equality of sets.

### Stage B — Cofactor lower bound L1.1–L1.2 (`Proofs/Cofactor/`)

Goal: the explicit-constant size bound that forces `max(|u|,|v|) ≲ T^{13/12}`.
Feeds Stage E. Produces no frozen theorem.

**B1 — `qcof_factor`.** `(u v : ℤ) : u ^ 13 - v ^ 13 = (u - v) * Qcof u v`
(telescoping/`geom_sum₂_mul`, or `ring` after unfolding the `range 13` sum).

**B2 — `qcof_lower` (L1.1, over ℝ).** `∀ u v : ℝ, (1/2) * (max |u| |v|) ^ 12 ≤
∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)`. Proof via the sketch §4: WLOG
`|v| ≤ |u|`, substitute `s = v/u ∈ [−1,1]`, factor `u¹²`, and show `q(s) =
∑_{j<13} sʲ ≥ 1/2` using `geom_sum_mul` (`(1−s)·q(s) = 1 − s¹³`, and `s¹³ < 0`
for `s < 0`). Keep the constant exactly `1/2`.

**B3 — `pow13_gap` (L1.2).** For **distinct** integers `u ≠ v`:
`(1/2) * (max |u| |v| : ℝ) ^ 12 ≤ |(u:ℝ) ^ 13 - v ^ 13|`, combining B1 (so
`|u¹³−v¹³| = |u−v|·Qcof`), `|u − v| ≥ 1`, and B2 (`Qcof ≥ 0`). Cast to ℝ.

> **Cheat watch (Stage B).** Prove B2 **for all reals** with the honest constant
> `1/2` — do **not** shortcut with an unproven "compactness gives some κ>0"
> (that is the paper's route the sketch deliberately replaces) and do **not**
> inflate to a weaker bound like `max^12 ≤ |u¹³−v¹³|²` or a crude `O(T²)` size
> bound: any slack that degrades the eventual `T^{13/12}` to `T²` destroys the
> `o(T)` sparsity (see sketch §9.5 pitfall 10). B3's hypothesis `u ≠ v` is
> essential and must **not** be dropped or replaced by `u,v ≥ 0`. Guardrail: an
> `example` checking `qcof_factor` at a concrete pair (e.g. `u=2,v=1`) by `decide`/`norm_num`.

### Stage C — Parametrisation exclusion L2.1, Route B (`Proofs/ParamExclusion/`)

Goal: prove the frozen **`no_linear_param`** — the exclusion hypothesis of the
axiom. This is the most intricate *elementary* piece.

**C1 — `linear_coeffs`.** From `p.natDegree ≤ 1`, extract `a := p.coeff 1`,
`b := p.coeff 0` with `p = C a * X + C b` (`Polynomial.eq_X_add_C_of_natDegree_le_one`).

**C2 — `coeff_equations`.** Expand `(a•X + C b)^13` by `add_pow` and read off, for
`j = 0,…,12`, the coefficient of `T^{13-j}` in `∑ᵢ pᵢ¹³ = C(-c)`:
`∑_i C(13,j) · aᵢ^{13−j} · bᵢʲ = 0`, i.e. `∑_i aᵢ^{13−j} bᵢʲ = 0` (since
`C(13,j) ≠ 0`), plus the constant equation `∑ bᵢ¹³ = -c`.

**C3 — `no_linear_param` (the frozen theorem).** Suppose `I := {i | aᵢ ≠ 0}` is
nonempty. Over `ℚ`, with `rᵢ := bᵢ/aᵢ`, `wᵢ := aᵢ¹³ ≠ 0`, the equations become
`∑_{i∈I} wᵢ rᵢʲ = 0` for `j = 0,…,12`. By the sketch's **case analysis on
`|I| ∈ {1,2,3}`** and which ratios coincide (Vandermonde with distinct nodes ⇒
weights vanish): a singleton group forces `aᵢ¹³ = 0` (contradiction), so all
`i ∈ I` share one ratio `r` with `∑_{i∈I} aᵢ¹³ = 0`. Then `|I|=3 ⇒ c = 0 ∈ Bset`;
`|I|=2 ⇒ a₁ = -a₂` (A3) ⇒ `c = (-b₃)¹³ ∈ Bset`; `|I|=1` already excluded — each
contradicts `hc : c ∉ Bset`. Hence `I = ∅`: all `natDegree pᵢ = 0`. (Prefer the
direct 2×2/3×3 elimination over instantiating `Matrix.det_vandermonde`, per the
sketch's Lean notes.)

> **Cheat watch (Stage C).** The frozen statement is `∀ p₁ p₂ p₃`, all three with
> `natDegree ≤ 1`, concluding **all three** `natDegree = 0`. Do **not** prove it
> only for a fixed example triple, only for `c` in a finite set, or only under an
> extra hypothesis (e.g. `aᵢ ≠ 0`) — it must hold for *every* linear triple with
> that sum. Do **not** silently assume the ratios `rᵢ` are distinct (the equal-ratio
> case is where `c ∈ Bset` is derived — that IS the crux). `natDegree = 0` is the
> genuine "constant" (covers the zero polynomial); do not weaken to `≤ 1`. The
> contradiction must land on `c ∉ Bset`, not on an assumed fact.

### Stage D — Greedy tiling criterion L4.1 (`Proofs/Greedy/`) — MILESTONE, independent

Goal: prove the frozen **`greedy_tiling`** for an abstract `B : Set ℤ`. Pure
combinatorics; **depends on nothing else** — good first / parallel target and a
citable result on its own.

**D1 — `Aseq`.** Enumerate `ℤ` via `Denumerable ℤ`. Define `Aseq : ℕ → Finset ℤ`
by `Nat.rec`: `Aseq 0 = ∅`; at step `j`, if `n_j ∈ Aseq (j-1) + B` keep it, else
apply `H` to `C_j := (Aseq (j-1)).image (fun a => n_j - a)` (⊆ `ℤ∖B` because
`n_j ∉ Aseq(j-1)+B`) to get `b_j ∈ B`, set `a_j := n_j - b_j`, `Aseq j :=
insert a_j (Aseq (j-1))`. Use `Classical.dec` for the membership case split.

**D2 — invariants `(I1)` `D`-separated, `(I2)` covers `n_i (i≤j)`.** Combined
induction (`And` motive). Separation of the new `a_j` from old `a` uses
`a_j - a = (n_j - a) - b_j ∉ D` (the `H`-property) and `dset_neg` (A2) for the
reverse; `a_j ∉ Aseq(j-1)` via `0 ∈ D` (sketch §9.5 pitfall 9).

**D3 — monotone chain.** `i ≤ j → Aseq i ⊆ Aseq j` by induction.

**D4 — `greedy_tiling` (the frozen theorem).** `A := ⋃ j, ↑(Aseq j)`. Covering
from `(I2)` + surjectivity of the enumeration; `D`-separation of `A` from the
chain + `(I1)`; **uniqueness** of the `(a,b)` pair: `a + b = a' + b'` with
`a ≠ a'` gives `a − a' = b' − b ∈ B − B = D`, contradicting separation; then
`b = b'` by cancellation. Deliver as the `∃! ab : ℤ × ℤ`.

> **Cheat watch (Stage D).** Keep `B` **abstract** (a universally quantified
> `Set ℤ`) — do **not** specialise to `Bset` here (that conflates Stage D with
> Stage F and hides whether the criterion is really general). The conclusion is
> `∃!` — prove **both** existence *and* uniqueness; a proof of existence alone
> (mere cover) is the classic weakening and makes "tiling" meaningless. The
> hypothesis `H` quantifies over **all finite** `C` — do not use it only for
> singletons. Do not assume `A` finite or that the construction terminates.

### Stage E — Bad-shift estimate P3.1 (`Proofs/BadShift/`) — the HEART

Goal: prove the frozen **`badShift_bound`**. The only stage that invokes
`heath_brown_diagonal_13`; requires Stages A, B, C.

**E1 — `bad_to_solution`.** For `t ∈ Sset c T`: pick (Classical choice) `(u,v)`
with `t¹³ − c = u¹³ − v¹³`; `u ≠ v` (else `c = t¹³ ∈ Bset`, contra `hc`). Set
`Φ t := (u, -v, -t)`; then `u¹³ + (-v)¹³ + (-t)¹³ = -c` (odd exponent) and `Φ` is
injective (third coordinate recovers `t`). (Sketch §6 Step 1.)

**E2 — `coord_bound`.** From B3 (`pow13_gap`) and `|t| ≤ T`, `T ≥ 1`:
`max(|u|,|v|) ≤ C_c · T^{13/12}` with `C_c := (2(1+|c|))^{1/12} ≥ 1`, hence every
`Φ t` lands in the box `max(|x|,|y|,|z|) ≤ X`, `X := C_c · T^{13/12} ≥ 1`.
(Sketch §6 Step 2, eq (4.2).)

**E3 — `apply_HB`.** Discharge the axiom's `hexcl` via **`no_linear_param`**
(Stage C) for `M = -c ≠ 0` (A4), obtaining `K ≥ 1` with
`#{(x,y,z) : sum = -c, box ≤ X} ≤ K · X^{10/13}`. (Sketch §6 Steps 3–4.)

**E4 — `badShift_bound` (the frozen theorem).** `Sset c T` injects (via `Φ`,
E1) into the counted solution set, so `|Sset c T| ≤ K · X^{10/13} = K · C_c^{10/13}
· T^{5/6}`; set `K_c := K · C_c^{10/13}`. Real-exponent bookkeeping:
`(T^{13/12})^{10/13} = T^{5/6}` via `Real.rpow_mul`/`Real.rpow_natCast`.
(Sketch §6 Step 4.) *Optional* integer-only route (sketch §9.4): prove
`|Sset c T|^{156} ≤ K' · T^{130}` first (all in `ℤ`, no `rpow`) and derive the
`ℝ` statement by monotone roots — a support lemma, but the **frozen** statement
stays the `5/6`-rpow form.

> **Cheat watch (Stage E).** The exponent must come out **exactly `5/6`** — any
> crude bound that replaces the coordinate bound `T^{13/12}` by `O(T²)` yields an
> exponent `≥ 1` and silently kills sparsity (sketch §9.5 pitfall 10); the audit
> checks the literal `(5:ℝ)/6`. The exclusion hypothesis of the axiom must be
> supplied by **`no_linear_param`**, *not* by adding a hypothesis to the frozen
> theorem or by assuming a second axiom. Keep `u ≠ v` (E1) — it is exactly where
> `c ∉ Bset` is used (pitfall 3). `#print axioms badShift_bound` must be
> `{propext, Classical.choice, Quot.sound, heath_brown_diagonal_13}` — no other
> axiom, no `sorryAx`.

### Stage F — Criterion + headline P5.1, Thm 1.1 (`Proofs/Assembly/`) — HEADLINE

Goal: prove the frozen **`criterion_holds`** and **`erdos_477`**. Requires D + E.

**F1 — `criterion_holds` (the frozen theorem).** `C = ∅ ⇒ b = 0 ∈ Bset` (A1,
vacuous). Else: bad `t` for `c` (`|t| ≤ T`) are exactly `Sset c T` (via A5:
`c − t¹³ ∈ D ↔ t¹³ − c ∈ D`). With `K := ∑_{c∈C} K_c` (badShift_bound) and an
integer `T > K^6`, `|⋃_{c∈C} Sset c T| ≤ ∑ K_c T^{5/6} = K·T^{5/6} < T < 2T+1 =
#Icc(-T)T` (`Finset.card_biUnion_le`, `Int.card_Icc`). Pigeonhole gives
`t₀`, `|t₀| ≤ T`, `t₀ ∉ Sset c T ∀c`; take `b := t₀¹³ ∈ Bset`; then `c − b ∉ D`
(A5). (Sketch §8.1.)

**F2 — `erdos_477` (the headline).** Apply **`greedy_tiling`** to `B := Bset`,
its hypothesis discharged by **`criterion_holds`** (rewrite `Dset` via
`dset_eq_sub`, A6). Get `A` with unique `(a,b)`, `b ∈ Bset`. Upgrade `(a,b) →
(a,m)`: existence via surjectivity of `m ↦ m¹³` onto `Bset` (definition);
uniqueness via `pow13_inj` (A3, `m¹³ = m'¹³ ⇒ m = m'`). Deliver `∃! p : ℤ × ℤ,
p.1 ∈ A ∧ p.1 + p.2¹³ = n`. (Sketch §8.2.)

> **Cheat watch (Stage F).** In F1 the count comparison must be **strict** and use
> the **full** `2T+1` two-sided interval — a one-sided `[0,T]` (only `T+1`
> candidates) or a non-strict `≤` breaks the pigeonhole. `K := ∑_{c∈C} K_c` must
> range over **all** of `C` (not a sub-family). In F2 keep the `∃!` and the
> **pair** `(a,m)` uniqueness — do not silently drop uniqueness of `m` (that needs
> A3) or restate as mere existence. Do not re-open `Defs.lean` to "adjust" `Bset`;
> bridge with `dset_eq_sub`/support lemmas only. `#print axioms erdos_477` must be
> `{propext, Classical.choice, Quot.sound, heath_brown_diagonal_13}`.

### Discharge & Solution (after the frozen theorems are proved)

In `Erdos477/Solution.lean`, restate each of the five frozen theorems
**verbatim** in `namespace Erdos477.Solution` and set it `:= <name>_proof` (the
sorry-free declaration from `Proofs/`). In `Erdos477/Discharge.lean`, for each
pair write `example : @<Frozen> = @<Proof> := rfl` — this compiles **iff** the
proof has *exactly* the frozen proposition (machine-checked no-drift). `verify.sh`
checks both modules build and that `#print axioms Erdos477.Solution.<name>` is
within the allowlist for every frozen name.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems + axiom, skeleton builds, pins recorded)
      │
      ├───────────────► Stage D  (Greedy / greedy_tiling)      ── INDEPENDENT, prove first (MILESTONE)
      │
      ▼
   Stage A  (Elementary L0.*)
      │
      ├──► Stage B  (Cofactor L1.*)  ──┐
      │                                 │  B and C independent → run in parallel
      └──► Stage C  (ParamExclusion / no_linear_param) ──┐
                                        │                 │
                                        ▼                 ▼
                                  Stage E  (BadShift / badShift_bound)   ── the HEART, hardest
                                        │        (also needs the axiom)
                                        ▼
                                  Stage F  (Assembly / criterion_holds, erdos_477)  ── HEADLINE
                                        │        (also needs Stage D)
                                        ▼
                              Discharge.lean + Solution.lean   (#print axioms clean)
```

- **Parallelism.** Stage D is independent of everything and should be launched
  immediately alongside Stage A. After A, Stages B and C run in parallel. Stage E
  waits on A+B+C; Stage F waits on D+E.
- **Milestone.** After Stage D, `greedy_tiling` is a citable stand-alone result.
- **Hardest engineering.** Stage E (bad-shift estimate) — real-exponent
  arithmetic, the injective transfer `Φ`, and the sole axiom invocation. Budget
  effort here; Stage C is the second-hardest (coefficient extraction + linear
  algebra).

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them, and see the problem-
specific traps at the end.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem must be hypothesis-free wherever the source claim is unconditional.
  Forbidden moves: adding `(h : …)` to a frozen statement; proving a `∀ x` claim
  only for generators / a finite subset and claiming the general case; replacing
  an equality with a one-sided inclusion. If a sub-proof seems to need an
  assumption, **derive it or restructure** — do not weaken the statement.
  Downstream stages instantiate these at *arbitrary* elements, so a quiet
  weakening breaks the assembly silently.

- **Keep every predicate the textbook definition — do not soften it.** `Bset`,
  `Dset`, `Sset`, and the `H`-criterion must be exactly as in `SKETCH.md` (`∀`
  finite `C`, two-sided `|t| ≤ T`, genuine `t¹³ − c ∈ D`). A softened predicate
  can make the headline vacuous or the sparsity false.

- **Get the modeling right once, in SETUP, and freeze it.** A dropped or extra
  relation in a frozen definition silently changes the object. Validate the core
  facts before freezing (`qcof_factor` at a concrete pair; `#Icc (-T) T = 2T+1`)
  with small guardrail `example`s.

- **Discharge algebraic identities once — never `sorry` them.** `qcof_factor` and
  the binomial coefficient extraction come from Mathlib (`geom_sum₂_mul`,
  `add_pow`); do not `sorry` a `ring`-provable identity.

- **Keep the two "difference-set" phrasings distinct but bridged.** `Dset` (concrete
  `u¹³−v¹³`) vs the abstract `{d | ∃ x∈B, ∃ y∈B, d = x−y}` used by `greedy_tiling`:
  fix both, bridge with `dset_eq_sub` (A6), and never conflate or silently swap them.

- **`decide` budget — and `native_decide` is BANNED.** Only the tiny guardrail
  identities are `decide`-able; the sums, casts, and `∃!` are structural. `Sset`
  and `Bset` are **noncomputable** (Classical membership) and will not reduce —
  do not attempt `decide` on them. `native_decide` adds a compiler-trust axiom and
  would dirty `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen (pinned in `scripts/frozen.sha256`). A missing *definition*
  belongs in a `Proofs/` support file; a *statement* that seems wrong means re-read
  `SKETCH.md` — the frozen statements are the minimal faithful rendering.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` **plus** the one whitelisted assumed
  certificate `heath_brown_diagonal_13` (recorded in `scripts/ALLOWED_AXIOMS.txt`
  from `USER_NOTES.md`) — and only where it is legitimately used (only
  `badShift_bound`, `criterion_holds`, `erdos_477` may depend on it; `greedy_tiling`,
  `no_linear_param` must **not**). No `sorryAx`, no `native_decide`/`ofReduceBool`.
  Checked per theorem by `verify.sh` (checks 2 and 4).

- **Assumed certificates go in as `axiom`s, never as hypotheses.**
  `heath_brown_diagonal_13` is the sole assumed certificate: it is Heath-Brown's
  determinant-method count (`J. Number Theory 129 (2009), Theorem 2`), far beyond
  current formalization, and is permitted **only** if the user records it in
  `USER_NOTES.md` (see the ⚠️ callout in Part −1 §2 — it is *not* yet recorded).
  When permitted, it is declared as a Lean `axiom` in `Defs.lean` during SETUP
  (so it appears in `#print axioms`), and is exempt from the axiom ban via
  `scripts/ALLOWED_AXIOMS.txt`. This NEVER relaxes the cardinal rule: it is never
  bolted onto a frozen theorem as a hypothesis `(h : …)`, and its `hexcl` argument
  must be **proved** (`no_linear_param`), not assumed. Do **not** introduce a
  second axiom (e.g. Brownawell–Masser / Route A) — Route B makes it unnecessary.

- **Problem-specific traps.**
  1. **Exponent slack.** Replacing the sharp coordinate bound `T^{13/12}` by any
     `O(T²)` degrades `5/6 → ≥ 1` and *destroys* `o(T)` — the entire proof fails
     silently (sketch §9.5 #10). Keep B2's constant `1/2` and E2's `13/12`.
  2. **Dropping `u ≠ v`.** In E1 the distinctness of `(u,v)` is exactly where
     `c ∉ Bset` enters; lose it and Stage B's gap bound (which needs `|u−v| ≥ 1`)
     collapses (#3).
  3. **Uniqueness erosion.** `greedy_tiling` and `erdos_477` are `∃!`; proving mere
     existence (a cover, not a tiling) is the headline-defeating cheat. The `(a,m)`
     upgrade *needs* odd-power injectivity (A3) — do not drop `m`-uniqueness (#4).
  4. **Strict pigeonhole.** F1 needs `<` against the full `2T+1` (two-sided
     interval); a one-sided interval or `≤` yields no good shift (#5).
  5. **Conditional axiom.** The axiom's power comes *only* through its proved
     `hexcl`; an unconditional counting axiom, or assuming `hexcl`, is a cheat that
     smuggles Stage C away.
