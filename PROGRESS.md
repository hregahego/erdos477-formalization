# PROGRESS — Erdős 477 (thirteenth-power tiling complement) formalization

Append-only log. **Never delete, edit, or reword an existing entry.** Correct a
prior entry only by appending a new one (`📝 decision`, noting which it
supersedes). Get timestamps with `date -u +"%Y-%m-%dT%H:%M:%SZ"`. See
`BLUEPRINT.md` Part −1 §4 for the full rules and §5 for the agent-onboarding
ritual.

Entry format (one per event, newest appended at the bottom):

```
## <UTC timestamp> — <stage/item>
Agent: <short label>
Status: ✅ proved | ⚠️ blocked | 🔧 in progress | 📝 decision
Check: <#print axioms result, lake build result, or n/a>
Note: <what you did, key lemma, or exactly what blocks you>
Next: <what this unblocks / where a follow-up agent should start — mandatory on ✅ and ⚠️>
```

---

<!-- The first entry is appended by init.py once SETUP freezes Defs + Theorems
     and records the SHA pins. Do not pre-fill log entries. -->

## 2026-07-19T19:45:41Z — SETUP · freeze Defs + Theorems + axioms, build skeleton
Agent: agent-setup
Status: ✅ proved
Check: `lake build` → "Build completed successfully (8569 jobs)"; only warnings are
  the 5 expected `declaration uses 'sorry'` from Theorems.lean (lines 24,31,38,46,52);
  no errors, no other warnings. SHA pins recorded in scripts/frozen.sha256
  (Defs.lean 42a2e988…, Theorems.lean 26981420…).
Note: Created the Lean4+Mathlib project in-place (`lake init Erdos477 math`). Toolchain
  and Mathlib pinned to **v4.31.0** (lean-toolchain + lakefile.toml `rev = "v4.31.0"`);
  `lake exe cache get` succeeded (8542 files). NOTE: the blueprint's suggested v4.15.0
  pin was abandoned — its prebuilt `cache` binary fails to run on this macOS (Darwin 25 /
  Tahoe) with a dyld `SG_READ_ONLY` error; v4.31.0 (stable, matching Mathlib rev) is the
  working pin, consistent with the blueprint's "any recent toolchain with a matching
  Mathlib rev" clause. Froze Erdos477/Defs.lean (Bset, Dset, Qcof, Sset + 2 axioms) and
  Erdos477/Theorems.lean (the 5 statements, all `:= sorry`). Wrote Proofs/<Stage>/Basic.lean
  placeholders, Solution.lean + Discharge.lean stubs, and root Erdos477.lean importing all.
  Wrote scripts/ALLOWED_AXIOMS.txt with both permitted axiom FQNs.
Next: Stages are now unblocked. Prove Stage D (`greedy_tiling`, Proofs/Greedy/, independent,
  MILESTONE) and Stage A (`Proofs/Elementary/`: zero_mem_B/D, dset_neg, pow13_inj,
  not_B_ne_zero, mem_D_symm_shift, dset_eq_sub) first, in parallel. Then B (Cofactor:
  qcof_factor, qcof_lower κ=1/2, pow13_gap) ∥ C (ParamExclusion: no_linear_param via Route B),
  then E (BadShift: badShift_bound, the only consumer of `heath_brown_diagonal_13`), then F
  (Assembly: criterion_holds, erdos_477). As each frozen `<name>` is proved sorry-free as
  `<name>_proof`, add its verbatim restatement to Solution.lean and its `@Frozen=@Proof:=rfl`
  gate to Discharge.lean. NEVER edit Defs.lean/Theorems.lean (byte-frozen; SHA-pinned).

## 2026-07-19T19:45:41Z — SETUP · modeling decisions committed (frozen)
Agent: agent-setup
Status: 📝 decision
Check: n/a
Note: Frozen modeling choices (binding — later stages characterize with support lemmas but
  never change these):
  • `Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}` — image form `b = m^13`, infinite, no
    positivity/`b≠0`; exponent literal `13 : ℕ`.
  • `Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}` — direct difference-of-powers
    encoding, NOT Minkowski `Bset - Bset`. Symmetry (`dset_neg`) and the bridge
    `dset_eq_sub : Dset = {d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y}` are Stage-A lemmas.
  • `Qcof (u v : ℤ) : ℤ := ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)` — full 13-term sum,
    integer-valued (cast to ℝ for the κ=1/2 bound in Stage B); `12 - i : ℕ` truncated (safe, i≤12).
  • `Sset (c T : ℤ) : Finset ℤ` — `noncomputable`, `(Finset.Icc (-T) T).filter (fun t => t^13 - c ∈ Dset)`
    under `open scoped Classical`; two-sided `|t| ≤ T` kept (the `2T+1` count is load-bearing).
  Assumed-certificate AXIOMS declared in Defs.lean (namespace Erdos477), both permitted by
  USER_NOTES.md and listed in scripts/ALLOWED_AXIOMS.txt:
  • `heath_brown_diagonal_13 (M hM hexcl) : ∃ K ≥ 1, ∀ X ≥ 1, (#{(x,y,z): x^13+y^13+z^13=M,
    box ≤ X}).ncard ≤ K·X^(10/13)` — Heath-Brown determinant-method count (paper Thm 2.2),
    CONDITIONAL form taking the degree-≤1 exclusion `hexcl` as a hypothesis (kept so Stage C
    must *prove* it via `no_linear_param`, never assume it). ASSUMED, not proved: the
    determinant method is far beyond current formalization. Consumed only by `badShift_bound`.
  • `brownawell_masser_P1_four_term {k}[Field][IsAlgClosed][CharZero] (A : Fin 4 → MvPolynomial
    (Fin 2) k) (d) (hne hhom hcoprime hsum hsub hratio) : (d:ℤ) ≤ 3·((#{projective zeros of
    ∏A}).ncard - 2)` — four-term Brownawell–Masser S-unit inequality on ℙ¹ (paper Thm 2.1),
    BM4 bivariate-forms formulation (SKETCH §5.2.1). ASSUMED, not proved: Mathlib has only the
    3-term case (Mason–Stothers); the 4-term case (generalized Wronskians) is unformalized.
    Permitted so the paper-faithful Route A is available; expected UNUSED since Route B
    (elementary Vandermonde) proves `no_linear_param` directly — preferred `#print axioms
    erdos_477` shows only `heath_brown_diagonal_13` beyond the standard three.
Next: Workers must treat these as fixed. Discharge `heath_brown_diagonal_13`'s `hexcl` in
  Stage E via `no_linear_param` (Stage C) with `M = -c`; do not add a hypothesis to any
  frozen theorem and do not introduce a third axiom.

## 2026-07-19T20:16:04Z — Stage A · Elementary L0.1–L0.6 (A1–A6)
Agent: agent-iter1-2
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/Elementary/Basic.lean` (and any new file under
  `Erdos477/Proofs/Elementary/`). Will prove zero_mem_B, zero_mem_D, dset_neg,
  pow13_inj (+ pow13_eq_iff, pow13_eq_neg), not_B_ne_zero, mem_D_symm_shift,
  dset_eq_sub. No other file touched.
Next: n/a (in progress)

## 2026-07-19T20:16:04Z — Stage B · Cofactor L1.1–L1.2 (B1–B3)
Agent: agent-iter1-3
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/Cofactor/Basic.lean` (and any new file under
  `Erdos477/Proofs/Cofactor/`). Proving `qcof_factor`, `qcof_lower` (κ = 1/2, all reals),
  `pow13_gap`. Will NOT import Stage A (Agent 2 holds it); only `Erdos477.Defs` + Mathlib.
Next: on ✅ Stage E may cite `Erdos477.qcof_factor`, `Erdos477.qcof_lower`, `Erdos477.pow13_gap`.

## 2026-07-19T20:17:13Z — Stage D · greedy_tiling (D1–D4)
Agent: agent-iter1-1
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/Greedy/Basic.lean`, `Erdos477/Solution.lean`,
  `Erdos477/Discharge.lean` per TASKS.md Iteration 1 / Agent 1. Building the greedy
  construction (Aseq via Denumerable ℤ enumeration, invariants I1/I2, monotone chain,
  union) to prove `Erdos477.greedy_tiling_proof` with the frozen type. B kept abstract.
Next: on success, Solution restatement + Discharge `rfl` gate + ✅ entry.

## 2026-07-19T20:18:03Z — Stage A · Elementary L0.1–L0.6 (A1–A6)
Agent: agent-iter1-2
Status: ✅ proved
Check: `lake build Erdos477.Proofs.Elementary.Basic` → "Build completed successfully
  (8559 jobs)", no errors/warnings, no `sorry`. `#print axioms` on all nine
  declarations (via `lake env lean` on a scratch file): each is a subset of
  {propext, Classical.choice, Quot.sound} — zero_mem_B/zero_mem_D/dset_neg/
  not_B_ne_zero/mem_D_symm_shift → [propext]; dset_eq_sub → [propext, Quot.sound];
  pow13_inj/pow13_eq_iff/pow13_eq_neg → [propext, Classical.choice, Quot.sound].
  No assumed-certificate axiom appears anywhere in Stage A.
Note: All six Stage-A items proved in `Erdos477/Proofs/Elementary/Basic.lean` (only
  file touched; no new files, so `Erdos477.lean` unchanged). Details:
  • `zero_mem_B : (0:ℤ) ∈ Bset` (witness m = 0), `zero_mem_D : (0:ℤ) ∈ Dset` (u = v = 0).
  • `dset_neg : ∀ d : ℤ, d ∈ Dset → -d ∈ Dset` — proved by SWAPPING the witnesses
    (`rintro ⟨u, v, rfl⟩; exact ⟨v, u, by ring⟩`), not by odd-power sign tricks.
  • `pow13_inj : Function.Injective (fun m : ℤ => m ^ 13)` — GLOBAL on ℤ, via
    `(Odd.strictMono_pow (R := ℤ) odd_thirteen).injective`; the exact Mathlib name is
    **`Odd.strictMono_pow : Odd n → StrictMono fun a : R => a ^ n`**
    (Mathlib/Algebra/Order/Ring/Basic.lean:178) — NOT `Odd.pow_right_strictMono` /
    `Odd.pow_left_injective`, which do not exist at this Mathlib rev (v4.31.0).
    Private helper `odd_thirteen : Odd (13:ℕ) := ⟨6, by norm_num⟩`.
    Corollaries exported: `pow13_eq_iff {x y : ℤ} : x ^ 13 = y ^ 13 ↔ x = y` and
    `pow13_eq_neg {x y : ℤ} (h : x ^ 13 = -(y ^ 13)) : x = -y` (uses `Odd.neg_pow`).
  • `not_B_ne_zero : ∀ c : ℤ, c ∉ Bset → c ≠ 0` from `zero_mem_B`.
  • `mem_D_symm_shift : ∀ c t : ℤ, c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset` — `dset_neg`
    in both directions (`simpa` closes the `-(c - t^13) = t^13 - c` rewrites).
  • `dset_eq_sub : Dset = {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y}` — a genuine
    `Set.ext` EQUALITY, both inclusions proved (→ by exhibiting x = u^13, y = v^13;
    ← by destructing the Bset memberships).
Next: Stages C, E, F may now cite, from `Erdos477.Proofs.Elementary.Basic` (import
  `Erdos477.Proofs.Elementary.Basic`), the names `Erdos477.zero_mem_B`,
  `Erdos477.zero_mem_D`, `Erdos477.dset_neg`, `Erdos477.pow13_inj`,
  `Erdos477.pow13_eq_iff`, `Erdos477.pow13_eq_neg`, `Erdos477.not_B_ne_zero`,
  `Erdos477.mem_D_symm_shift`, `Erdos477.dset_eq_sub`. In particular Stage F's
  `criterion_holds`/`erdos_477` assembly should use `dset_eq_sub` to rewrite the
  abstract difference set in `greedy_tiling` into `Dset`, `mem_D_symm_shift` for the
  bad-shift reindexing, and `not_B_ne_zero` for the `c ≠ 0` side condition feeding
  `heath_brown_diagonal_13`. Stage A needs no follow-up work.

## 2026-07-19T20:19:06Z — Stage B · Cofactor L1.1–L1.2 (B1–B3) COMPLETE
Agent: agent-iter1-3
Status: ✅ proved
Check: `lake build Erdos477.Proofs.Cofactor.Basic` → "Built ... (8.2s), Build completed
  successfully (8559 jobs)", zero errors, zero warnings (no `sorry`). `#print axioms` on
  ALL seven declarations (`qcof_factor`, `qcof_lower`, `pow13_gap`, `sub_pow13_eq`,
  `two_mul_qcof_eq`, `max_abs_pow12_le`, `qcof_nonneg`) → `[propext, Classical.choice,
  Quot.sound]` only.
Note: All of Stage B proved in `Erdos477/Proofs/Cofactor/Basic.lean` (only file touched;
  no new files, so `Erdos477.lean` unchanged). Imports only `Erdos477.Defs` + Mathlib —
  Stage A NOT imported.
  • `sub_pow13_eq (R) [CommRing R] (u v : R) : u^13 - v^13 = (u - v) * ∑ i ∈ range 13,
    u^i * v^(12-i)` — proved by `simp only [Finset.sum_range_succ, Finset.sum_range_zero];
    norm_num; ring`. Stated over an arbitrary `CommRing` so both the ℤ form (B1) and the
    ℝ form needed by B3 are instances; no `geom_sum₂_mul` index-convention wrangling needed.
  • `qcof_factor (u v : ℤ) : u^13 - v^13 = (u - v) * Qcof u v := sub_pow13_eq ℤ u v` (B1),
    plus the mandated guardrail `example : (2:ℤ)^13 - 1^13 = (2-1) * Qcof 2 1` by `norm_num`.
  • `qcof_lower (u v : ℝ) : (1/2) * (max |u| |v|)^12 ≤ ∑ i ∈ range 13, u^i * v^(12-i)` (B2 /
    L1.1) — ALL reals, constant EXACTLY 1/2, no compactness, no unnamed κ. 📝 PROOF DECISION:
    instead of SKETCH §4's `s := v/u ∈ [-1,1]` substitution I used an equivalent but much
    more Lean-friendly SUM-OF-SQUARES identity (`two_mul_qcof_eq`, proved by `ring`):
      `2·Q(u,v) = u^12 + v^12 + (v^6+uv^5)^2 + (uv^5+u^2v^4)^2 + (u^2v^4+u^3v^3)^2
                  + (u^3v^3+u^4v^2)^2 + (u^4v^2+u^5v)^2 + (u^5v+u^6)^2`
    (for odd i, `term_{i-1} + 2·term_i + term_{i+1}` is a perfect square; the six squares
    consume every term of `2Q` except `u^12 + v^12`). Hence `Q ≥ (u^12+v^12)/2 ≥
    (1/2)·max(|u|,|v|)^12` via `max_abs_pow12_le : (max |u| |v|)^12 ≤ u^12 + v^12`. This
    proves the SAME inequality with the SAME constant — no weakening. It also yields the
    strictly stronger `Q ≥ (u^12+v^12)/2` should a later stage want it.
  • `qcof_nonneg (u v : ℝ) : 0 ≤ ∑ i ∈ range 13, u^i * v^(12-i)` — corollary of B2.
  • `pow13_gap (u v : ℤ) (huv : u ≠ v) : (1/2) * (max |(u:ℝ)| |(v:ℝ)|)^12 ≤
    |(u:ℝ)^13 - (v:ℝ)^13|` (B3 / L1.2) — hypothesis `u ≠ v` KEPT; via `sub_pow13_eq ℝ`,
    `Int.one_le_abs (sub_ne_zero.mpr huv)` cast to ℝ for `1 ≤ |u - v|`, and `qcof_lower`
    (which also supplies `Q ≥ 0`, so `|Q| = Q`).
Next: Stage E (`Proofs/BadShift/`) may now cite, from `Erdos477.Proofs.Cofactor.Basic`:
  `Erdos477.pow13_gap` (the coordinate bound `max(|u|,|v|) ≤ (2|t^13 - c|)^(1/12) ≪ T^(13/12)`),
  `Erdos477.qcof_lower`, `Erdos477.qcof_nonneg`, `Erdos477.qcof_factor`, and the ring-generic
  `Erdos477.sub_pow13_eq`. Stage E must add `import Erdos477.Proofs.Cofactor.Basic`.
  Nothing in Stage B is blocked or outstanding.

## 2026-07-19T20:19:37Z — Stage D · greedy_tiling (D1–D4) — MILESTONE
Agent: agent-iter1-1
Status: ✅ proved
Check: `lake build Erdos477.Proofs.Greedy.Basic Erdos477.Solution Erdos477.Discharge` →
  success, no errors, no warnings from my files (only the 5 expected `uses sorry`
  warnings from the frozen Theorems.lean).
  `#print axioms Erdos477.Solution.greedy_tiling` → `[propext, Classical.choice, Quot.sound]`
  `#print axioms Erdos477.greedy_tiling_proof`   → `[propext, Classical.choice, Quot.sound]`
  (no `heath_brown_diagonal_13`, no `sorryAx`.)
Note: `Erdos477/Proofs/Greedy/Basic.lean` now proves `Erdos477.greedy_tiling_proof` with
  EXACTLY the frozen type (machine-checked by the new `example : @Erdos477.greedy_tiling =
  @Erdos477.greedy_tiling_proof := rfl` in `Erdos477/Discharge.lean`), and
  `Erdos477/Solution.lean` carries the verbatim restatement `Erdos477.Solution.greedy_tiling`.
  `B` stays ABSTRACT; `H` is used on the FULL image `Finset` `C = S.image (n - ·)`
  (not singletons); both existence AND uniqueness are proved. Declarations added, all in
  `namespace Erdos477.Greedy` except the theorem itself (`namespace Erdos477`):
  • `Dabs (B : Set ℤ) : Set ℤ := {d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}` — the abstract difference
    set of the frozen statement (defeq to the set-builder there; `Hyp B` coerces by `have H' :
    Hyp B := H`).
  • `neg_mem_Dabs` (symmetry, proved LOCALLY by swapping witnesses — independent of Stage A's
    `dset_neg`), `zero_mem_Dabs`, `nonempty_of_Hyp` (H on `C = ∅`).
  • `Sep B S := ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a - a' ∉ Dabs B` (invariant I1), `sep_empty`.
  • D1 `extend_exists (H) (S) (n) : ∃ S', S ⊆ S' ∧ (∃ a ∈ S', ∃ b ∈ B, a + b = n) ∧
    (Sep B S → Sep B S')` — the single greedy step (case split `by_cases` on whether `n` is
    already covered; in Case 2 `H` applied to `S.image (n - ·)`, new point `n - b`). Note the
    covering conjunct is UNCONDITIONAL, which is what lets the recursion be defined by plain
    `Classical.choose` without a subtype. `stepF := (extend_exists …).choose` with the three
    projections `subset_stepF`, `cover_stepF`, `sep_stepF`.
  • `enum j := (Denumerable.eqv ℤ).symm j`, `enum_surjective`.
  • D1 `Aseq (H) : ℕ → Finset ℤ` (`Aseq 0 = ∅`, `Aseq (j+1) = stepF H (Aseq H j) (enum j)`).
  • D2 `Aseq_sep : ∀ j, Sep B (Aseq H j)` (I1); `Aseq_cover : ∀ j, ∀ i < j, ∃ a ∈ Aseq H j,
    ∃ b ∈ B, a + b = enum i` (I2). D3 `Aseq_mono : i ≤ j → Aseq H i ⊆ Aseq H j`.
  • D4 `Aset H := ⋃ j, ↑(Aseq H j)` + `mem_Aset`; existence from `enum_surjective` + `Aseq_cover`
    at `j = i+1`; uniqueness by pulling both `a, a'` into `Aseq H (max (i+1) j')` via `Aseq_mono`
    and contradicting `Aseq_sep` with `a' - a = b - b' ∈ Dabs B`, then `b = b'` by cancellation.
  Note `a₀ ∉ S` is NOT needed anywhere (the `Finset.mem_insert` case analysis covers it), so
  `zero_mem_Dabs`/`nonempty_of_Hyp` are exported for downstream use but not load-bearing here.
Next: Stage D is DONE and needs no follow-up. Stage F (`Proofs/Assembly/`) can now finish
  `erdos_477` by combining `Erdos477.greedy_tiling_proof` (or `Erdos477.Solution.greedy_tiling`)
  with `criterion_holds` and Stage A's `dset_eq_sub : Dset = {d | ∃ x ∈ Bset, ∃ y ∈ Bset,
  d = x - y}` (Agent 2, `Proofs/Elementary/Basic.lean`) — that bridge is exactly what turns
  `criterion_holds` (stated over `Dset`) into the `H` argument of `greedy_tiling_proof`
  (stated over the abstract `{d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}` at `B := Bset`); then convert
  the resulting `∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ Bset ∧ ab.1 + ab.2 = n` into the frozen
  `∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n` using `pow13_inj` (Stage A) for uniqueness of
  the exponent witness `m`. Whoever edits `Solution.lean`/`Discharge.lean` next: they now
  import `Erdos477.Proofs.Greedy.Basic` and contain the `greedy_tiling` restatement + gate —
  APPEND only, do not rewrite.

## 2026-07-19T20:27:05Z — Stage F · Assembly (F1 criterion_holds_of_badShift, F2 erdos_477_of_criterion)
Agent: agent-iter2-3
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/Assembly/Basic.lean` (and any new file under
  `Erdos477/Proofs/Assembly/`) per TASKS.md Iteration 2 / Agent 3. Proving the two
  support lemmas `criterion_holds_of_badShift (hBS)` and `erdos_477_of_criterion (hcrit)`,
  each taking its not-yet-proved input as an explicit argument. Will NOT touch
  Solution.lean/Discharge.lean (Agent 1 owns them) nor BadShift/ParamExclusion.
Next: on ✅ iteration 3 wires `hBS := badShift_bound_proof` and `hcrit := criterion_holds_proof`.

## 2026-07-19T20:26:40Z — Harness · scripts/verify.sh (REVIEW.md follow-up #1)
Agent: agent-iter2-4
Status: 🔧 in progress
Check: n/a
Note: Claiming `scripts/verify.sh` ONLY (no .lean file touched). Fixing the `set -e`
  premature-abort at lines 235-236 and auditing the rest of the script for the same
  command-substitution-capture pattern.
Next: rerun `bash scripts/verify.sh` end-to-end and quote the RESULT block.

## 2026-07-19T20:27:10Z — Stage E · badShift_bound_of_hexcl (E1–E4)
Agent: agent-iter2-2
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/BadShift/Basic.lean` (and any new file under
  `Erdos477/Proofs/BadShift/`) per TASKS.md Iteration 2 / Agent 2. Proving
  `badShift_bound_of_hexcl` (frozen `badShift_bound` conclusion, with `hexcl`
  as an extra argument of this SUPPORT lemma only). Imports Stage A + Stage B
  only; NOT ParamExclusion/Assembly. No other file touched.
Next: n/a (in progress)

## 2026-07-19T20:27:33Z — Stage C · no_linear_param (C1–C3, Route B)
Agent: agent-iter2-1
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/ParamExclusion/Basic.lean` (and any new file under
  `Erdos477/Proofs/ParamExclusion/`), plus APPEND-ONLY edits to `Erdos477/Solution.lean`
  and `Erdos477/Discharge.lean` per TASKS.md Iteration 2 / Agent 1. Proving
  `Erdos477.no_linear_param_proof` via Route B (coefficient equations E_0,E_1,E_2,E_13
  + elementary elimination). Route A / `brownawell_masser_P1_four_term` stays unused.
Next: on success, Solution restatement + Discharge `rfl` gate + ✅ entry.

## 2026-07-19T20:29:10Z — Harness · scripts/verify.sh (REVIEW.md follow-up #1)
Agent: agent-iter2-4
Status: ✅ proved
Check: `bash scripts/verify.sh` now runs END-TO-END (exit code 1 = 1 failed check, and it
  DOES write to logs/verify_log.jsonl again):
  ```
  --- Check 1: Frozen SHA pins ---
  PASS: Erdos477/Defs.lean pin matches
  PASS: Erdos477/Theorems.lean pin matches
  --- Check 2: Banned keywords ---
  PASS: no banned keywords (sorry allowed only in Theorems.lean)
  --- Check 3: lake build ---
  Build completed successfully (8569 jobs).
  PASS: build clean (only expected Theorems.lean sorry warnings)
  --- Check 4: #print axioms (Erdos477.Solution.*) ---
  FAIL: no_linear_param — no axiom output (build/name error)
  FAIL: badShift_bound — no axiom output (build/name error)
  PASS: greedy_tiling — axioms within allowlist {propext Classical.choice Quot.sound
        + Erdos477.heath_brown_diagonal_13 Erdos477.brownawell_masser_P1_four_term}
  FAIL: criterion_holds — no axiom output (build/name error)
  FAIL: erdos_477 — no axiom output (build/name error)
  --- Check 5: Statement gates (Discharge / Solution) ---
  PASS: Erdos477.Discharge compiles (statement↔proof gate holds)
  PASS: Erdos477.Solution compiles (statement↔proof gate holds)

  === RESULT: FAIL (1 issue(s), 17s) ===
  ```
  logs/verify_log.jsonl tail:
  {"timestamp":"2026-07-19T20:27:20Z","target":"--all","build_errors":0,"build_warnings":0,
   "issues":1,"duration_sec":17,"success":false}
Note: Touched `scripts/verify.sh` ONLY (no .lean file, no Defs/Theorems, no frozen.sha256,
  no ALLOWED_AXIOMS.txt). Three `set -e` premature-abort sites fixed; NO check weakened,
  no allowlist entry added, no check removed, exit-code semantics unchanged (exit = number
  of failed checks):
  1. Check 4 (the reported defect, old lines 235-236): `line=$(… | grep "…depends on axioms")`
     and `noax=$(… | grep "…does not depend on any axioms")` now end in `|| true`, so a frozen
     theorem missing from Solution.lean is reported as `FAIL: <name> — no axiom output` and the
     loop/Check 5/RESULT/log all still run. (Verified above: 4 per-theorem FAILs printed,
     `greedy_tiling` still PASSes, Check 5 and the RESULT summary now appear.)
  2. Check 2 (SAME latent pattern, found by the requested scan): `BANNED_OUT=$(… python3 …)`
     is followed by `BANNED_EXIT=$?`, but the helper exits 1 exactly when it FINDS banned
     keywords — under `set -e` the assignment itself would have killed the script before the
     `FAIL: banned keywords detected` branch ever ran. Now wrapped in `set +e` / `set -e`
     (not `|| true`, which would have clobbered `$?`). Confirmed in a throwaway /tmp sandbox
     with a planted `native_decide`: the script prints `FAIL: banned keywords detected` and
     continues through Checks 3-5 to `=== RESULT: FAIL (4 issue(s)) ===` (exit 4).
  3. Check 1 hardening: `actual=$(sha256_of "$REPO_ROOT/$relpath" 2>/dev/null || true)` — a
     missing/unreadable pinned file is now a pin MISMATCH FAIL (empty ≠ pinned) instead of an
     abort. Still strictly a FAIL, no weakening.
  Audited every other `x=$(…)` capture: lines 214/236/272 (`lake` runs) are already inside
  `set +e`/`set -e`; 218 and 264 already end in `|| true`; 253 uses `sed -n` (exit 0 on
  no-match); the `[ … ] && VAR=…` idioms (lines 121/128/261/278/282) are exempt from `set -e`
  as non-final members of an AND-list (checked empirically in bash on this machine).
Next: the audit gate is FUNCTIONAL again — any agent/iteration can now run
  `bash scripts/verify.sh` (or `bash scripts/verify.sh <theorem>` for a single one) and get a
  complete Checks 1-5 report plus a `logs/verify_log.jsonl` entry, whatever subset of the five
  frozen theorems is restated in `Solution.lean` so far. The 4 remaining Check-4 FAILs are
  CONTENT, not harness: they clear as Iteration 2/3 append `no_linear_param` (Agent 1, this
  iteration), then `badShift_bound`, `criterion_holds`, `erdos_477` (Iteration 3 wiring of
  `badShift_bound_of_hexcl` / `criterion_holds_of_badShift` / `erdos_477_of_criterion`) to
  `Erdos477/Solution.lean` + `Erdos477/Discharge.lean`. No follow-up work on `scripts/verify.sh`
  is outstanding.

## 2026-07-19T20:31:12Z — Stage F · Assembly F1+F2 (criterion_holds_of_badShift, erdos_477_of_criterion)
Agent: agent-iter2-3
Status: ✅ proved
Check: `lake build Erdos477.Proofs.Assembly.Basic` → "Build completed successfully (8561 jobs)",
  zero errors, zero warnings, no `sorry`. `#print axioms` on ALL six declarations
  (`criterion_holds_of_badShift`, `erdos_477_of_criterion`, `mem_Sset`, `Sset_subset`,
  `card_Icc_neg`, `mul_rpow_lt_self`) → `[propext, Classical.choice, Quot.sound]` only —
  in particular NEITHER depends on `heath_brown_diagonal_13` (it will enter only through
  the `hBS` argument in iteration 3). Type-shape gate (scratch file, compiles): the frozen
  `criterion_holds` conclusion is inhabited by `criterion_holds_of_badShift hBS`, the frozen
  `erdos_477` conclusion by `erdos_477_of_criterion hcrit`, and `hBS`'s type is verbatim the
  ∀-form of the frozen `badShift_bound`.
Note: Only `Erdos477/Proofs/Assembly/Basic.lean` touched (no new files, so `Erdos477.lean`
  unchanged; Solution.lean/Discharge.lean NOT touched — Agent 1 owns them). Imports
  `Erdos477.Defs`, `Erdos477.Proofs.Elementary.Basic`, `Erdos477.Proofs.Greedy.Basic` only.
  • `mem_Sset {c T t} : t ∈ Sset c T ↔ t ∈ Finset.Icc (-T) T ∧ t ^ 13 - c ∈ Dset` (`simp [Sset]`).
  • `Sset_subset (c T) : Sset c T ⊆ Finset.Icc (-T) T` (`Finset.filter_subset`).
  • `card_Icc_neg (T) (0 ≤ T) : ((Finset.Icc (-T) T).card : ℤ) = 2 * T + 1` — the FULL
    two-sided `2T+1` count (`Int.card_Icc` + `Int.toNat_of_nonneg`), load-bearing.
  • `mul_rpow_lt_self (0 ≤ K) (1 ≤ x) (K ^ 6 < x) : K * x ^ ((5:ℝ)/6) < x` — the STRICT step,
    proved by sixth powers exactly as SKETCH §8.1 suggests: `(K * x^(5/6))^6 = K^6 * x^5 <
    x * x^5 = x^6`, then `lt_of_pow_lt_pow_left₀ 6`. Key rewrite
    `(x ^ ((5:ℝ)/6)) ^ (6:ℕ) = x ^ (5:ℕ)` via `← Real.rpow_natCast`, `← Real.rpow_mul`, `norm_num`.
  • **F1** `criterion_holds_of_badShift (hBS : ∀ c : ℤ, c ∉ Bset → ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ,
    1 ≤ T → ((Sset c T).card : ℝ) ≤ K * (T:ℝ) ^ ((5:ℝ)/6)) : ∀ C : Finset ℤ,
    (∀ c ∈ C, c ∉ Bset) → ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset`. `choose KK` over a TOTAL
    auxiliary (`K_c` for `c ∈ C`, dummy `1` elsewhere) so `K := ∑ c ∈ C, KK c` ranges over ALL
    of `C`; `T := max 1 (⌈K^6⌉ + 1)` gives `1 ≤ T` and `K^6 < (T:ℝ)`; then
    `|⋃_{c∈C} Sset c T| ≤ ∑_{c∈C} |Sset c T| ≤ K * T^(5/6) < T < 2T+1 = #Icc (-T) T`
    (`Finset.card_biUnion_le`, `Finset.sum_le_sum`, `Finset.sum_mul`, `card_Icc_neg`), all
    comparisons STRICT where the sketch demands. Pigeonhole by `Finset.card_le_card` on the
    contrapositive gives `t₀ ∈ Icc (-T) T` outside every `Sset c T`; `b := t₀ ^ 13 ∈ Bset`;
    `c - b ∉ Dset` by `mem_D_symm_shift` (Stage A) + `mem_Sset`. Note the `C = ∅` case needs no
    separate branch here (the empty sum gives `K = 0` and the condition is vacuous), so
    `zero_mem_B` is not used — the general argument covers it.
  • **F2** `erdos_477_of_criterion (hcrit : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
    ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset) : ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
    p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n`. `hcrit` is turned into the `H` of `greedy_tiling_proof`
    at `B := Bset` by rewriting with `dset_eq_sub` (Stage A) — the only bridge used, `Defs.lean`
    untouched. The `∃!` is kept: existence takes `b = m ^ 13` from `hb : b ∈ Bset`; uniqueness of
    the PAIR `(a,m)` comes from greedy's pair-uniqueness (`a' = a`, `m'^13 = m^13`) plus
    `pow13_eq_iff`/`pow13_inj` (Stage A) for `m' = m`.
Next: Iteration 3 wiring, once Stage C (`no_linear_param_proof`, Agent 1) and Stage E
  (`badShift_bound_of_hexcl`, Agent 2) land:
    `theorem badShift_bound_proof (c) (hc) := badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)`
    `theorem criterion_holds_proof : ... := criterion_holds_of_badShift badShift_bound_proof`
    `theorem erdos_477_proof : ... := erdos_477_of_criterion criterion_holds_proof`
  (`badShift_bound_proof` must be η-fed as `fun c hc => badShift_bound_proof c hc` if the
  binder shape differs; the scratch gate confirms the ∀-form typechecks). Then APPEND the
  verbatim restatements to `Erdos477/Solution.lean` and the `@Frozen = @Proof := rfl` gates to
  `Erdos477/Discharge.lean` for `criterion_holds` and `erdos_477`. Expected
  `#print axioms Erdos477.Solution.erdos_477` = `{propext, Classical.choice, Quot.sound,
  Erdos477.heath_brown_diagonal_13}`. Nothing in Stage F is blocked or outstanding.

## 2026-07-19T20:31:52Z — Stage E · badShift_bound_of_hexcl (E1–E4) COMPLETE
Agent: agent-iter2-2
Status: ✅ proved
Check: `lake build Erdos477.Proofs.BadShift.Basic` → "Built ... (9.4s), Build completed
  successfully (8561 jobs)", zero errors, zero warnings, no `sorry`.
  `#print axioms Erdos477.badShift_bound_of_hexcl` →
  `[propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]`
  — exactly the permitted set, no `sorryAx`, no `brownawell_masser_P1_four_term`.
  All support lemmas (`coord_bound`, `Phi_inj`, `sol_finite`, …) →
  `[propext, Classical.choice, Quot.sound]` only.
  FROZEN-TYPE GATE (scratch file, `lake env lean`, type-checked OK):
  `example : ∀ (c : ℤ), c ∉ Bset → (∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
     ((Sset c T).card : ℝ) ≤ K * (T:ℝ) ^ ((5:ℝ)/6)) :=
   fun c hc => badShift_bound_of_hexcl c hc (no_linear_param c hc)`
  — i.e. feeding the frozen `no_linear_param` into my lemma yields EXACTLY the frozen
  `badShift_bound` type. Only `Erdos477/Proofs/BadShift/Basic.lean` touched (no new
  files, so `Erdos477.lean` unchanged).
Note: Stage E fully proved in `Erdos477/Proofs/BadShift/Basic.lean`, namespace
  `Erdos477` (helpers in `Erdos477.BadShift`). Exponent is the literal `(5:ℝ)/6`;
  `hexcl` is an argument of THIS SUPPORT LEMMA ONLY — the frozen statement is untouched.
  • `mem_Sset_iff : t ∈ Sset c T ↔ (-T ≤ t ∧ t ≤ T) ∧ t ^ 13 - c ∈ Dset` (`simp [Sset]`).
  • E1: `pair_exists c t : ∃ p : ℤ × ℤ, t^13 - c ∈ Dset → t^13 - c = p.1^13 - p.2^13`
    (always-true existential, so the choice `pairOf c t := (pair_exists c t).choose` needs
    no `dite`/subtype); `pairOf_spec`; `pairOf_ne` — the witnesses are DISTINCT, the one
    place `hc : c ∉ Bset` is used (else `c = t^13 ∈ Bset`); `Phi c t := (u, -v, -t)`;
    `Phi_inj` (third coordinate recovers `t`); `Phi_sum : u^13 + (-v)^13 + (-t)^13 = -c`
    via `Odd.neg_pow ⟨6, _⟩`.
  • E2: `Cc c := (2*(1+|(c:ℝ)|)) ^ ((1:ℝ)/12)` with `one_le_Cc`, `Cc_pow12 : Cc c ^ 12 =
    2*(1+|c|)`; `Xb c T := Cc c * (T:ℝ) ^ ((13:ℝ)/12)` with `one_le_Xb`, `T_le_Xb`,
    `Xb_pow12 : Xb c T ^ 12 = 2*(1+|c|)*(T:ℝ)^13`. `coord_bound` chains Stage B's
    `pow13_gap u v hne` with `|t^13 - c| ≤ (1+|c|)*T^13` (from `|t| ≤ T`, `T ≥ 1`) to get
    `m^12 ≤ (Xb c T)^12` (`m := max |u| |v|`), then `le_of_pow_le_pow_left₀`. So the box
    radius really is `≍ T^(13/12)` — no `O(T²)` slack.
  • Finiteness: `mem_Icc_ceil` (`|(x:ℝ)| ≤ X → x ∈ Set.Icc (-⌈X⌉) ⌈X⌉`, via `Int.le_ceil`)
    and `sol_finite M X : {v : ℤ×ℤ×ℤ | sum = M ∧ box ≤ X}.Finite` (subset of a product of
    three `Set.Icc`). This is ESSENTIAL: without it `ncard = 0` makes the axiom vacuous.
  • E3/E4: one invocation `heath_brown_diagonal_13 (-c) (neg_ne_zero.mpr (not_B_ne_zero c hc))
    hexcl` (Stage A's `not_B_ne_zero`), passing `hexcl` through unchanged; then
    `Finset.card_image_of_injective _ (Phi_inj c)` + `Set.ncard_le_ncard hsub (sol_finite …)`
    + `Set.ncard_coe_finset` give `#Sset c T ≤ ncard(solutions) ≤ K * X^(10/13)`, and
    `Real.mul_rpow` / `← Real.rpow_mul` give `X^(10/13) = Cc c ^(10/13) * T^(5/6)`.
    Final constant `K_c := max 1 (K * Cc c ^ ((10:ℝ)/13))` (so `1 ≤ K_c` is `le_max_left`).
  Mathlib names that differ at v4.31.0 (for later agents): `Set.ncard_coe_finset` (NOT
  `Set.ncard_coe_Finset`), `pow_le_pow_left₀`, `le_of_pow_le_pow_left₀`, `one_le_pow₀`.
  Note `rw [Xb]` is needed before `nlinarith` — `nlinarith` does not unfold the def.
Next: ITERATION 3 wiring (one line, in whichever file owns the frozen restatements):
  `theorem badShift_bound_proof (c : ℤ) (hc : c ∉ Bset) :
     ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T → ((Sset c T).card : ℝ) ≤ K * (T:ℝ) ^ ((5:ℝ)/6) :=
   Erdos477.badShift_bound_of_hexcl c hc (Erdos477.no_linear_param_proof c hc)`
  (import `Erdos477.Proofs.BadShift.Basic` and `Erdos477.Proofs.ParamExclusion.Basic`);
  that type-checked here against the frozen `no_linear_param`, so it will type-check
  against Stage C's `no_linear_param_proof` as soon as Agent 1 lands it. Then APPEND the
  `badShift_bound` restatement to `Solution.lean` and the `rfl` gate to `Discharge.lean`.
  Stage F's `criterion_holds_of_badShift` takes exactly this `∀ c, c ∉ Bset → ∃ K …`
  as its `hBS` argument. Nothing in Stage E is outstanding.

## 2026-07-19T20:33:45Z — Stage C · no_linear_param (C1–C3, Route B) COMPLETE
Agent: agent-iter2-1
Status: ✅ proved
Check: `lake build Erdos477.Proofs.ParamExclusion.Basic` → "Built ... (9.4s), Build
  completed successfully (8560 jobs)", zero errors, zero warnings (no `sorry`).
  `lake build Erdos477.Solution Erdos477.Discharge` → success (only the 5 expected
  `uses sorry` warnings from the frozen Theorems.lean); in particular the no-drift gate
  `example : @Erdos477.no_linear_param = @Erdos477.no_linear_param_proof := rfl`
  ELABORATES, so the proof carries EXACTLY the frozen type.
  `#print axioms` → `[propext, Classical.choice, Quot.sound]` for ALL of
  `Erdos477.Solution.no_linear_param`, `Erdos477.no_linear_param_proof`,
  `Erdos477.linear_coeff_vanish`, `Erdos477.two_nonzero_case`, `Erdos477.coeff_lin_pow13`.
  Neither `heath_brown_diagonal_13` nor `brownawell_masser_P1_four_term` appears
  (Route B only; `Mathlib/NumberTheory/FLT/MasonStothers.lean` never imported).
  Banned-keyword grep on the new file: no `sorry`/`native_decide`/`admit`/`unsafe`/`axiom`.
Note: Stage C proved in `Erdos477/Proofs/ParamExclusion/Basic.lean` (only new content;
  `Erdos477.lean` unchanged since the module already existed), plus APPEND-ONLY additions
  to `Erdos477/Solution.lean` (`import Erdos477.Proofs.ParamExclusion.Basic` +
  `Erdos477.Solution.no_linear_param := no_linear_param_proof`) and
  `Erdos477/Discharge.lean` (same import + the `rfl` gate). Iteration-1 content in those
  two files was left byte-identical. Declarations added (all `namespace Erdos477`):
  • `coeff_lin_pow13 (a b : ℤ) (k : ℕ) (hk : k ≤ 13) :
      ((C a * X + C b : ℤ[X])^13).coeff k = (Nat.choose 13 k : ℤ) * a^k * b^(13-k)` (C2).
    Proved via `add_pow` + `Polynomial.finsetSum_coeff`, rewriting each summand as
    `C ((13.choose m) * a^m * b^(13-m)) * X^m` (`simp only [mul_pow, ← C_pow,
    ← C_eq_natCast, C_mul]; ring`) and collapsing with `Finset.sum_ite_eq'`.
    📝 NOTE: the natCast→C lemma at this Mathlib rev is **`Polynomial.C_eq_natCast`**
    (`C (n : R) = (n : R[X])`); there is no `C_natCast`.
  • `two_nonzero_case (a a' b b' b'' c : ℤ) (ha' : a' ≠ 0) (E0 : a^13 + a'^13 = 0)
      (E1 : a^12*b + a'^12*b' = 0) (E13 : b^13+b'^13+b''^13 = -c) : c ∈ Bset`
    — the `|I| = 2` crux: `a = -a'` by Stage A's `pow13_eq_neg`, then `(-a')^12 = a'^12`
    turns E1 into `a'^12*(b+b') = 0`, so `b' = -b`, the two 13th powers cancel and
    `c = (-b'')^13 ∈ Bset`.
  • `linear_coeff_vanish (c a₁ a₂ a₃ b₁ b₂ b₃ : ℤ) (hc : c ∉ Bset) (E0) (E1) (E2) (E13) :
      a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0` (C3) — the arithmetic core over the four coefficient
    equations `E₀ : Σaᵢ¹³ = 0`, `E₁ : Σaᵢ¹²bᵢ = 0`, `E₂ : Σaᵢ¹¹bᵢ² = 0`, `E₁₃ : Σbᵢ¹³ = -c`.
    Full 8-way `by_cases` on which `aᵢ` vanish: |I|=1 killed by E₀; the three |I|=2 cases by
    `two_nonzero_case`; |I|=3 by the Vandermonde/equal-ratio argument over ℚ.
    📝 PROOF DECISION (equivalent to SKETCH §5.1 Step 2, no weakening): instead of
    `Matrix.det_vandermonde` I use the SKETCH's recommended direct elimination in the
    slick form `Σᵢ wᵢ(qᵢ-q₂)(qᵢ-q₃) = E₂ - (q₂+q₃)E₁ + q₂q₃E₀ = 0`, which isolates
    `w₁(q₁-q₂)(q₁-q₃) = 0` (one `linear_combination` each for the three indices); with
    `wᵢ = (aᵢ:ℚ)^13 ≠ 0` this gives the three "each ratio equals one of the others"
    equations, whence `q₁ = q₂ = q₃` by a 4-line case bash. Equal ratios + E₁₃ then give
    `(c:ℚ) = q₁¹³ · Σ(aᵢ:ℚ)¹³ = 0`, so `c = 0 ∈ Bset` (Stage A `zero_mem_B`) — contradiction.
    The ratios are obtained as `∃ q : ℚ, (bᵢ:ℚ) = q * (aᵢ:ℚ)` (`field_simp`), never assumed
    distinct.
  • `no_linear_param_proof (c : ℤ) (hc : c ∉ Bset) : <frozen statement>` — C1 by
    `Polynomial.eq_X_add_C_of_natDegree_le_one` (all three `pᵢ`, no extra hypothesis),
    C2 by taking `coeff` at k = 13, 12, 11, 0 of `hsum` through `coeff_lin_pow13`
    (RHS via `Polynomial.coeff_C`; the binomial factors 13 and 78 cancelled by
    `mul_eq_zero`), C3 by `linear_coeff_vanish`; finally `natDegree pᵢ = 0` from
    `pᵢ = C 0 * X + C bᵢ` by `simp`. Uses from Stage A: `pow13_eq_neg`, `zero_mem_B`.
Next: Stage E (Agent 2, `Proofs/BadShift/`) and iteration 3 may now cite
  `Erdos477.no_linear_param_proof : ∀ (c : ℤ), c ∉ Bset → ∀ p₁ p₂ p₃ : Polynomial ℤ,
  p₁^13 + p₂^13 + p₃^13 = Polynomial.C (-c) → p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 →
  p₃.natDegree ≤ 1 → p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0`
  from `Erdos477.Proofs.ParamExclusion.Basic` (or `Erdos477.Solution.no_linear_param`).
  Concretely, iteration 3 should define, in a file that may import BOTH Stage C and
  Stage E, `theorem badShift_bound_proof (c : ℤ) (hc : c ∉ Bset) : <frozen> :=
  badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)` and add the corresponding
  `Solution.lean` restatement + `Discharge.lean` `rfl` gate (APPEND-ONLY; both files now
  import `Erdos477.Proofs.Greedy.Basic` and `Erdos477.Proofs.ParamExclusion.Basic` and
  contain the `greedy_tiling` and `no_linear_param` entries). Stage C needs no follow-up.

## 2026-07-19T20:39:07Z — Iteration 3 · Final wiring (Discharge & Solution)
Agent: agent-iter3-1
Status: 🔧 in progress
Check: n/a
Note: Claiming `Erdos477/Proofs/Wiring.lean` (NEW), plus APPEND-ONLY edits to
  `Erdos477/Solution.lean`, `Erdos477/Discharge.lean`, and one `import` line in
  `Erdos477.lean`. Composing `no_linear_param_proof` → `badShift_bound_of_hexcl` →
  `criterion_holds_of_badShift` → `erdos_477_of_criterion` into the three remaining
  frozen theorems `badShift_bound`, `criterion_holds`, `erdos_477`.
Next: `✅`/`⚠️` entry with the verify.sh RESULT block and `#print axioms` lines.

## 2026-07-19T20:41:31Z — Iteration 3 · Final wiring (Discharge & Solution) COMPLETE
Agent: agent-iter3-1
Status: ✅ proved
Check: `lake build` → "Build completed successfully (8570 jobs)", zero errors, only the
  5 expected `declaration uses \`sorry\`` warnings from the byte-frozen Theorems.lean
  (lines 24, 31, 38, 46, 52). `bash scripts/verify.sh` full run:
  ```
  --- Check 1: Frozen SHA pins ---
  PASS: Erdos477/Defs.lean pin matches
  PASS: Erdos477/Theorems.lean pin matches
  --- Check 2: Banned keywords ---
  PASS: no banned keywords (sorry allowed only in Theorems.lean)
  --- Check 3: lake build ---
  Build completed successfully (8570 jobs).
  PASS: build clean (only expected Theorems.lean sorry warnings)
  --- Check 4: #print axioms (Erdos477.Solution.*) ---
  PASS: no_linear_param — axioms within allowlist
  PASS: badShift_bound — axioms within allowlist
  PASS: greedy_tiling — axioms within allowlist
  PASS: criterion_holds — axioms within allowlist
  PASS: erdos_477 — axioms within allowlist
  --- Check 5: Statement gates (Discharge / Solution) ---
  PASS: Erdos477.Discharge compiles (statement↔proof gate holds)
  PASS: Erdos477.Solution compiles (statement↔proof gate holds)
  === RESULT: PASS (0 issue(s), 18s) ===
  ```
  `#print axioms` (via `lake env lean` on a scratch file importing Erdos477.Solution):
  `'Erdos477.Solution.no_linear_param' depends on axioms: [propext, Classical.choice, Quot.sound]`
  `'Erdos477.Solution.badShift_bound' depends on axioms: [propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]`
  `'Erdos477.Solution.greedy_tiling' depends on axioms: [propext, Classical.choice, Quot.sound]`
  `'Erdos477.Solution.criterion_holds' depends on axioms: [propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]`
  `'Erdos477.Solution.erdos_477' depends on axioms: [propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]`
  — no `sorryAx`, no `brownawell_masser_P1_four_term` anywhere.
Note: BLUEPRINT §"Discharge & Solution" is now CLOSED; all five frozen theorems are
  restated sorry-free in `Erdos477/Solution.lean` and gated by `rfl` in
  `Erdos477/Discharge.lean`. No new mathematics — pure composition. Files touched
  (exactly the four assigned; Defs.lean/Theorems.lean/verify.sh/ALLOWED_AXIOMS.txt
  untouched, SHA pins still match):
  • NEW `Erdos477/Proofs/Wiring.lean` (namespace `Erdos477`), three declarations with
    statements VERBATIM from Theorems.lean:
      – `badShift_bound_proof (c : ℤ) (hc : c ∉ Bset) := badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)`
        — the axiom's `hexcl` is discharged HERE by Stage C; the frozen statement gains
        no hypothesis, and the exponent stays the literal `(5:ℝ)/6`.
      – `criterion_holds_proof := criterion_holds_of_badShift (fun c hc => badShift_bound_proof c hc)`
        (the η-expanded `fun c hc => …` is what Stage F1's `hBS` binder shape wants).
      – `erdos_477_proof := erdos_477_of_criterion criterion_holds_proof`.
  • `Erdos477.lean`: one added line `import Erdos477.Proofs.Wiring` after the other
    `Proofs.*` imports, before `Erdos477.Solution`; every other line unchanged.
  • `Erdos477/Solution.lean`: APPEND-ONLY — added `import Erdos477.Proofs.Wiring` and,
    after the untouched Iteration-1/2 `greedy_tiling`/`no_linear_param` entries, the three
    verbatim restatements `Erdos477.Solution.badShift_bound`, `.criterion_holds`, `.erdos_477`.
  • `Erdos477/Discharge.lean`: APPEND-ONLY — same import plus the three no-drift gates
    `example : @Erdos477.badShift_bound = @Erdos477.badShift_bound_proof := rfl`,
    `… @Erdos477.criterion_holds = @Erdos477.criterion_holds_proof := rfl`,
    `… @Erdos477.erdos_477 = @Erdos477.erdos_477_proof := rfl`. ALL THREE ELABORATE on the
    first try — no type drift anywhere in the chain
    `no_linear_param → badShift_bound → criterion_holds → erdos_477`.
Next: Nothing outstanding for the formalization proper — every frozen theorem is proved
  and gated, and the only non-standard dependency is the user-permitted certificate
  `Erdos477.heath_brown_diagonal_13` (entering exactly where expected: `badShift_bound`
  and its two downstream consumers; `greedy_tiling` and `no_linear_param` are free of it).
  A follow-up agent could (a) refresh `REVIEW.md`/`README.md` to record that Iteration-2
  required follow-ups #1 and #2 are now cleared and `verify.sh` reports PASS (0 issues),
  and (b) optionally golf `Erdos477/Proofs/**`; no proof work remains.
