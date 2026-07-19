# REVIEW — Erdős 477 (thirteenth-power tiling complement) formalization

Append-only audit log. The Review agent appends one `## Review — Iteration N`
block per iteration with its findings and a `Verdict: COMPLETE | INCOMPLETE`
line. NEVER edit or delete an existing block.

## Review -- INIT faithfulness audit (Defs + Theorems)
Auditor: init-faithfulness
Files audited: Erdos477/Defs.lean, Erdos477/Theorems.lean
  (frozen SHA-256 in scripts/frozen.sha256 verified to match the on-disk files —
   no tampering; no `sorry` in Defs.lean; exactly two `axiom` decls, both permitted.)
Per-item verdicts:
  Definitions (Defs.lean):
  - Bset (Defs.lean:41): FAITHFUL -- `{b | ∃ m : ℤ, b = m ^ 13}`, the full infinite
    set of 13th powers in image form; matches SKETCH §0 / BLUEPRINT D1. No positivity,
    no `b ≠ 0`, exponent `13 : ℕ`, `Set ℤ` (not a Finset/range). Textbook.
  - Dset (Defs.lean:45): FAITHFUL -- `{d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}`, the
    difference set encoded directly (not Minkowski `Bset - Bset`); matches SKETCH §0 /
    BLUEPRINT D2. Symmetry left as a lemma (correct — not baked in).
  - Qcof (Defs.lean:50): FAITHFUL -- `∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)`,
    the full 13-term (i = 0..12) homogeneous cofactor; matches SKETCH §4 / BLUEPRINT D3.
    Not truncated; `12 - i` nat-sub is safe since `i ≤ 12`.
  - Sset (Defs.lean:56): FAITHFUL -- `(Finset.Icc (-T) T).filter (fun t => t ^ 13 - c ∈ Dset)`,
    the bad-shift set over the TWO-SIDED interval (load-bearing 2T+1 count preserved),
    with the genuine membership `t^13 - c ∈ Dset` (not a decidable small-(u,v) surrogate);
    matches SKETCH §0 / BLUEPRINT D4.
  - axiom heath_brown_diagonal_13 (Defs.lean:74): FAITHFUL -- verbatim the specialized
    CONDITIONAL Lean form of SKETCH §3 (M ≠ 0; keeps the `hexcl` exclusion hypothesis so
    Stage C cannot be skipped; conclusion `ncard{sol in box} ≤ K·X^(10/13)`, K ≥ 1).
    Permitted by USER_NOTES Axiom 1 and listed in ALLOWED_AXIOMS.txt as
    Erdos477.heath_brown_diagonal_13. Not a disguised restatement of any frozen conclusion.
  - axiom brownawell_masser_P1_four_term (Defs.lean:102): FAITHFUL -- the concrete
    bivariate-forms "BM4" of SKETCH §5.2.1 / USER_NOTES Axiom 2: alg-closed char-0 `k`,
    4 nonzero homogeneous forms of common degree `d`, coprime (any common divisor is a
    unit), summing to 0, no proper nonempty vanishing sub-sum (`hsub`), not all ratios
    constant (`hratio = ¬∀ i j ∃ c, A i = C c * A j`), conclude `d ≤ 3(z-2)` with `z` the
    ncard of projective zeros of `∏ A i`. Matches the sketch's hypotheses one-for-one;
    not broader than stated. Listed in ALLOWED_AXIOMS.txt as
    Erdos477.brownawell_masser_P1_four_term; USER_NOTES explicitly permits it for Route A
    (may end up unused under Route B — both outcomes blessed).
  Theorems (Theorems.lean):
  - no_linear_param (Theorems.lean:24): FAITHFUL -- `∀ p₁ p₂ p₃`, sum `= C (-c)`, each
    `natDegree ≤ 1` ⇒ each `natDegree = 0`; matches SKETCH L2.1 / BLUEPRINT lines 202-206.
    `hc : c ∉ Bset` is the genuine hypothesis of L2.1 (NOT an added weakening). Feeds the
    axiom's `hexcl` with M = -c. Concludes all-three-constant, not a single example / not ≤1.
  - badShift_bound (Theorems.lean:31): FAITHFUL -- `∃ K, 1 ≤ K ∧ ∀ T ≥ 1,
    (Sset c T).card ≤ K * T^((5:ℝ)/6)`; exponent EXACTLY 5/6; matches SKETCH P3.1.
    `hc : c ∉ Bset` genuine (from the sketch's "for every c ∈ ℤ∖B").
  - greedy_tiling (Theorems.lean:38): FAITHFUL -- abstract `B : Set ℤ`, hypothesis over
    ALL finite `C ⊆ ℤ∖B`, conclusion `∃ A, ∀ n, ∃! ab : ℤ×ℤ, ab.1∈A ∧ ab.2∈B ∧ ab.1+ab.2=n`.
    Keeps `∃!` (both existence AND uniqueness); B not specialized to Bset; matches SKETCH
    L4.1 / BLUEPRINT lines 214-217.
  - criterion_holds (Theorems.lean:46): FAITHFUL -- `∀ C, (∀ c∈C, c∉Bset) → ∃ b∈Bset,
    ∀ c∈C, c-b ∉ Dset`; matches SKETCH P5.1. Universally quantified over all finite C;
    genuine `∉ Dset`.
  - erdos_477 (Theorems.lean:52): FAITHFUL -- `∃ A, ∀ n, ∃! p : ℤ×ℤ, p.1∈A ∧ p.1+p.2^13=n`;
    verbatim the target statement SKETCH §0 line 39-40 / §8.2. `∃!` over the PAIR (a,m)
    preserved (not weakened to plain `∃`); no added hypothesis.
Findings: none. Both frozen files match their pinned SHA-256 (no tampering). Defs.lean
  contains no `sorry` and exactly the two axioms permitted by USER_NOTES and listed in
  scripts/ALLOWED_AXIOMS.txt (no unlisted axiom; no allowlist name lacking a matching
  axiom). Every definition is the genuine textbook object with no dropped/weakened/extra
  clause; every theorem is a minimal, hypothesis-clean rendering of the sketch's claim
  (both `∃!`s intact, exponent literally 5/6, two-sided interval, all-constant conclusion).
Verdict: FAITHFUL

## Review -- Iteration 1
Auditor: review-iter1
Checks run:
  - `shasum -a 256 -c scripts/frozen.sha256` → `Erdos477/Defs.lean: OK`, `Erdos477/Theorems.lean: OK` (both pins intact).
  - `lake build` → "Build completed successfully (8569 jobs)"; 0 errors; the only warnings are the 5 expected `declaration uses 'sorry'` at Theorems.lean:24,31,38,46,52.
  - `bash scripts/verify.sh` → Check 1 PASS (pins), Check 2 PASS (no banned keywords; `sorry` only in Theorems.lean), Check 3 PASS (build clean), then the script **aborted inside Check 4 with exit code 1** and never printed Check 5 / RESULT (see finding below).
  - Manual re-run of Check 4 via `lake env lean` on a scratch `import Erdos477` file, `#print axioms` on 16 declarations:
      `Erdos477.Solution.greedy_tiling` → [propext, Classical.choice, Quot.sound]
      `Erdos477.greedy_tiling_proof`   → [propext, Classical.choice, Quot.sound]
      `zero_mem_B`, `zero_mem_D`, `dset_neg`, `not_B_ne_zero`, `mem_D_symm_shift` → [propext]
      `dset_eq_sub` → [propext, Quot.sound]
      `pow13_inj`, `pow13_eq_iff`, `pow13_eq_neg`, `qcof_factor`, `qcof_lower`, `pow13_gap`, `sub_pow13_eq`, `qcof_nonneg` → [propext, Classical.choice, Quot.sound]
    No `sorryAx`, no `heath_brown_diagonal_13`, no `brownawell_masser_P1_four_term` anywhere in iteration-1 output.
  - Manual Check 5: `lake build Erdos477.Discharge Erdos477.Solution` → exit 0, no errors (the `example : @Erdos477.greedy_tiling = @Erdos477.greedy_tiling_proof := rfl` gate at Discharge.lean:16 compiles).
  - `grep -rn "native_decide|sorry|admit|^axiom|unsafe" Erdos477/` → only doc-comment prose plus the two allowlisted axioms at Defs.lean:74 and Defs.lean:102.
Findings:
  - CONFIRMED GOOD (frozen files): Defs.lean and Theorems.lean are byte-identical to their SHA pins; no tampering, no new axiom, no edit to any frozen statement. Earlier PROGRESS.md/REVIEW.md entries are intact and this iteration only appended.
  - CONFIRMED GOOD — MILESTONE `greedy_tiling` genuinely proved. `Erdos477/Proofs/Greedy/Basic.lean:160` `greedy_tiling_proof` carries EXACTLY the frozen type (machine-checked by the `rfl` gate, Discharge.lean:16), and `Erdos477/Solution.lean:24` restates it verbatim. Adversarial checks all pass: `B` stays an abstract `Set ℤ` (Greedy/Basic.lean:28) and is never specialised to `Bset`; the conclusion is the full `∃!`, with uniqueness actually proved (Greedy/Basic.lean:171-186), not existence-only; `H` is applied to the FULL image Finset `S.image (n - ·)` (Greedy/Basic.lean:71), not to singletons; `A` is the infinite union `⋃ j, ↑(Aseq j)` (Greedy/Basic.lean:148) with no finiteness or termination assumption; abstract-difference-set symmetry is proved locally (`neg_mem_Dabs`, Greedy/Basic.lean:32), not imported. `Greedy.Dabs` (Greedy/Basic.lean:26) is the literal set-builder of the frozen statement — no trivialising redefinition.
  - CONFIRMED GOOD — Stage A (`Erdos477/Proofs/Elementary/Basic.lean`): all six items are named, stated, sorry-free lemmas over the frozen `Bset`/`Dset`. `dset_neg` (:30) is by witness swap, not sign tricks; `pow13_inj` (:40) is GLOBAL `Function.Injective (fun m : ℤ => m ^ 13)` via `Odd.strictMono_pow`, unbounded and not sign-restricted; `dset_eq_sub` (:76) is a genuine `Set.ext` EQUALITY with both inclusions proved, not a one-sided `⊆`.
  - CONFIRMED GOOD — Stage B (`Erdos477/Proofs/Cofactor/Basic.lean`): `qcof_factor` (:28) with the mandated `norm_num` guardrail `example` (:32); `qcof_lower` (:69) is over ALL reals `u v : ℝ` with the constant literally `1/2` — no compactness, no unnamed κ, no weakened bound. The worker's substitution of a sum-of-squares identity (`two_mul_qcof_eq`, :44, closed by `ring`) for SKETCH §4's `s := v/u` route changes the PROOF only, not the statement or constant, and I re-derived the chain `2Q = u^12+v^12+6 squares ⇒ Q ≥ (u^12+v^12)/2 ≥ (1/2)max(|u|,|v|)^12` — sound and in fact slightly stronger. `pow13_gap` (:91) KEEPS the essential hypothesis `u ≠ v` and is not restricted to nonnegatives.
  - CONFIRMED GOOD — process: file ownership respected (Elementary/, Cofactor/, Greedy/+Solution/Discharge each touched by exactly the owning agent; no new files, `Erdos477.lean` unchanged from SETUP); PROGRESS.md was append-only with plausible `date -u` timestamps; every ✅ claim in PROGRESS.md reproduced exactly as stated — no faked ✅ detected this iteration.
  - HARNESS DEFECT (not a cheat, but it blinds the gate): `scripts/verify.sh:235-236` assigns `line=$(echo "$AX_OUTPUT" | grep …)` under `set -euo pipefail`; when a theorem is not yet in Solution.lean the `grep` returns 1 and the whole script DIES mid-Check-4 with exit 1, printing neither the intended `FAIL: <name> — no axiom output` line, nor Check 5, nor the `=== RESULT ===` summary, and writing no entry to `logs/verify_log.jsonl`. So `verify.sh` currently cannot report a pass/fail for ANY iteration until all five theorems exist. I worked around it by hand (above); it must be fixed or the audit gate is non-functional. Suggested fix: `line=$(… || true)` (and likewise for `noax`).
  - REMAINING WORK (expected at iteration 1, not a regression): 4 of 5 frozen theorems are still `sorry` in Theorems.lean and absent from Solution.lean — `no_linear_param` (Theorems.lean:24), `badShift_bound` (:31), `criterion_holds` (:46), `erdos_477` (:52). `Erdos477/Proofs/{ParamExclusion,BadShift,Assembly}/Basic.lean` are still SETUP placeholders.
  - NET-PROGRESS VERDICT: **net progress toward `erdos_477`**. One of the five frozen theorems (the independent combinatorial MILESTONE `greedy_tiling`) is fully discharged sorry-free with a clean axiom footprint, and Stages A and B landed nine and seven named, proved, reusable leaves that later stages cite directly. This is iteration 1, so there is no recurring "Next:" crux and no circling; nothing here is lateral re-wrapping.
Required follow-ups:
  1. Fix `scripts/verify.sh:235-236` (append `|| true` to the two `grep` capture assignments, or drop `set -e` around them) so Check 4 reports per-theorem FAILs and Check 5 + the RESULT summary actually run before all five theorems are proved. Until then no iteration can be certified by the script itself.
  2. Assign Stage C (`Erdos477/Proofs/ParamExclusion/Basic.lean`): prove `no_linear_param` via SKETCH §5.1 Route B (elementary Vandermonde), keeping `brownawell_masser_P1_four_term` unused.
  3. Assign Stage E (`Erdos477/Proofs/BadShift/Basic.lean`): `badShift_bound` with the exponent EXACTLY `5/6`, the sole permitted consumer of `heath_brown_diagonal_13`; its `hexcl` must be discharged by Stage C's `no_linear_param` at `M = -c`, never assumed.
  4. Assign Stage F (`Erdos477/Proofs/Assembly/Basic.lean`): `criterion_holds` then `erdos_477`, using `dset_eq_sub` as the concrete/abstract bridge into `greedy_tiling_proof` and `pow13_inj` for uniqueness of the exponent witness.
  5. Whoever next edits `Solution.lean`/`Discharge.lean` must APPEND the four remaining verbatim restatements and `rfl` gates — the two files are now owned jointly and must not be rewritten.
Verdict: INCOMPLETE

## Review -- Iteration 2
Auditor: review-iter2
Checks run:
  - `bash scripts/verify.sh --no-log --all` (I ran the harness myself, exit code 1):
    Check 1 PASS (both SHA pins match), Check 2 PASS (no banned keywords; `sorry`
    only in Theorems.lean), Check 3 PASS ("Build completed successfully (8569 jobs)",
    0 errors, 0 unexpected warnings), Check 4 = **PASS `no_linear_param`,
    PASS `greedy_tiling`, FAIL `badShift_bound`, FAIL `criterion_holds`,
    FAIL `erdos_477` ("no axiom output" — not yet restated in Solution.lean)**,
    Check 5 PASS (both `Erdos477.Discharge` and `Erdos477.Solution` compile).
    `=== RESULT: FAIL (1 issue(s), 26s) ===`. The script now runs end-to-end and
    prints Checks 1-5 + RESULT, so Iteration-1 follow-up #1 is genuinely fixed.
  - `lake env lean` on a scratch `import Erdos477` file, `#print axioms` on 7 decls:
      `Erdos477.Solution.no_linear_param` → [propext, Classical.choice, Quot.sound]
      `Erdos477.no_linear_param_proof`    → [propext, Classical.choice, Quot.sound]
      `Erdos477.badShift_bound_of_hexcl`  → [propext, Classical.choice,
                                             Erdos477.heath_brown_diagonal_13, Quot.sound]
      `Erdos477.criterion_holds_of_badShift` → [propext, Classical.choice, Quot.sound]
      `Erdos477.erdos_477_of_criterion`      → [propext, Classical.choice, Quot.sound]
      `Erdos477.greedy_tiling_proof`, `Erdos477.Solution.greedy_tiling`
                                            → [propext, Classical.choice, Quot.sound]
    No `sorryAx`, no `native_decide`, no `brownawell_masser_P1_four_term` anywhere.
  - INDEPENDENT WIRING GATE (my own scratch file, not the workers'): I composed the
    three support lemmas myself —
      `bs_proof c hc := badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)`,
      `ch_proof := criterion_holds_of_badShift bs_proof`,
      `e477_proof := erdos_477_of_criterion ch_proof` —
    and the three no-drift gates `example : @Erdos477.badShift_bound = @bs_proof := rfl`,
    `… @criterion_holds = @ch_proof := rfl`, `… @erdos_477 = @e477_proof := rfl` ALL
    ELABORATE. `#print axioms e477_proof` → [propext, Classical.choice,
    heath_brown_diagonal_13, Quot.sound]. So the mathematics of all five frozen
    theorems is in fact complete and sorry-free; only the Solution/Discharge
    restatements are missing.
  - `grep -rn` over `Erdos477/**.lean` for `heath_brown_diagonal_13`,
    `brownawell_masser_P1_four_term`, `MasonStothers`, `Polynomial.abc`,
    `native_decide`: exactly ONE axiom invocation site
    (`Erdos477/Proofs/BadShift/Basic.lean:213`), all other hits are doc comments.
  - File mtimes: Defs.lean/Theorems.lean/frozen.sha256/ALLOWED_AXIOMS.txt untouched
    since SETUP; Elementary/Cofactor/Greedy untouched since Iteration 1; only
    ParamExclusion, BadShift, Assembly, Solution, Discharge and scripts/verify.sh
    changed this iteration.
Findings:
  - CONFIRMED GOOD (frozen files intact): `Erdos477/Defs.lean` and
    `Erdos477/Theorems.lean` still match their SHA-256 pins byte-for-byte
    (scripts/frozen.sha256:3-4). No frozen statement weakened, no hypothesis added,
    no `∀` specialized, no equality replaced by an inclusion. `Erdos477.lean` is
    unchanged (no new modules were needed). Earlier PROGRESS.md/REVIEW.md history is
    intact and this iteration only appended.
  - CONFIRMED GOOD — Stage C (`no_linear_param`) is a REAL, sorry-free proof of the
    frozen statement. `Erdos477/Proofs/ParamExclusion/Basic.lean:173`
    `no_linear_param_proof` has EXACTLY the frozen type (machine-checked by the `rfl`
    gate at `Erdos477/Discharge.lean:21`), restated verbatim at
    `Erdos477/Solution.lean:33`, axioms `{propext, Classical.choice, Quot.sound}` —
    Route B only, `brownawell_masser_P1_four_term` NOT used and MasonStothers never
    imported. Adversarial checks all pass: it is `∀ p₁ p₂ p₃` (Basic.lean:174-176),
    concludes all three `natDegree = 0` (not `≤ 1`, not one example, not a finite set
    of `c`); the only hypotheses are the frozen `hc : c ∉ Bset` and the three
    `natDegree ≤ 1`; no `aᵢ ≠ 0` assumption sneaked in. The equal-ratio case is
    genuinely handled and is where `c ∈ Bset` is derived: the ratios `qᵢ` are
    constructed (Basic.lean:104-109), never assumed distinct, and the |I|=3 branch
    (Basic.lean:100-167) derives `c = 0 ∈ Bset` from `q₁=q₂=q₃`, while the |I|=2
    branches go through `two_nonzero_case` (Basic.lean:49) giving `c = (-b'')^13 ∈ Bset`.
    The Vandermonde substitution `Σ wᵢ(qᵢ-q_j)(qᵢ-q_k) = E₂-(q_j+q_k)E₁+q_jq_kE₀`
    (Basic.lean:125-142) is a PROOF change only, statement-preserving.
  - CONFIRMED GOOD — Stage E (`badShift_bound_of_hexcl`,
    `Erdos477/Proofs/BadShift/Basic.lean:204`). Conclusion is the frozen
    `badShift_bound` conclusion verbatim with exponent literally `(5:ℝ)/6`
    (Basic.lean:210); `hexcl` is an argument of THIS SUPPORT LEMMA ONLY and TASKS.md
    Iteration 2 explicitly sanctioned that — and it is now moot, since I verified
    myself that feeding `no_linear_param_proof` yields the frozen type by `rfl`. The
    box radius is the genuine `C_c · T^(13/12)` (`Xb`, Basic.lean:102) derived from
    Stage B's `pow13_gap` with constant `1/2` (Basic.lean:168-175) — no `O(T²)` slack,
    so the `5/6` is real. `u ≠ v` is kept and is exactly where `hc : c ∉ Bset` is used
    (`pairOf_ne`, Basic.lean:59-64). The counted solution set is proved FINITE
    (`sol_finite`, Basic.lean:186) so the `ncard` bound is not vacuous, and `Φ` is
    injective (Basic.lean:70). Exactly one invocation of the axiom (Basic.lean:213),
    in its conditional form with the received `hexcl` passed through unchanged.
  - CONFIRMED GOOD — Stage F (`Erdos477/Proofs/Assembly/Basic.lean:58` F1,
    `:129` F2), axioms `{propext, Classical.choice, Quot.sound}` — neither depends on
    `heath_brown_diagonal_13`, as required. F1's count comparison is STRICT and against
    the FULL two-sided `2T+1` (`card_Icc_neg`, Basic.lean:31; `hstrict`/`hlt`,
    Basic.lean:100-108), the strict step is the honest sixth-power argument
    (`mul_rpow_lt_self`, Basic.lean:39), and `K := ∑_{c ∈ C} KK c` ranges over ALL of
    `C` via a total `choose` (Basic.lean:65-74) — no sub-family. F2 keeps the `∃!` over
    the PAIR `(a,m)` with uniqueness of `m` actually proved via `pow13_eq_iff`
    (Basic.lean:149); the concrete/abstract bridge is `dset_eq_sub` only
    (Basic.lean:138) — `Defs.lean` never reopened.
  - CONFIRMED GOOD — harness fix (Iteration-1 follow-up #1). `scripts/verify.sh` now
    completes: I re-read the whole script and confirmed NO check was weakened — the
    SHA-pin check, the banned-keyword check (still bans sorry/native_decide/admit/
    unsafe/implemented_by/ofReduceBool and non-whitelisted `axiom`), the build check,
    the allowlist parsing and `exit = number of failed checks` are all unchanged; the
    only edits are `|| true` / `set +e` guards that stop `set -e` aborting mid-check.
    No theorem name was added to any allowlist; `ALLOWED_AXIOMS.txt` and
    `frozen.sha256` are untouched.
  - CONFIRMED GOOD — process: file ownership respected exactly as assigned (Agent 1:
    ParamExclusion + append-only Solution/Discharge, whose Iteration-1 `greedy_tiling`
    content is byte-identical; Agent 2: BadShift; Agent 3: Assembly; Agent 4:
    verify.sh only). PROGRESS.md was append-only with plausible `date -u` timestamps,
    and every ✅ claim in it reproduced under my own tooling — NO faked ✅ this iteration.
  - REMAINING WORK (not a cheat, not a regression): three frozen theorems are still
    absent from `Erdos477/Solution.lean` and `Erdos477/Discharge.lean` —
    `badShift_bound` (Theorems.lean:31), `criterion_holds` (:46), `erdos_477` (:52) —
    which is the single `verify.sh` issue. This is pure mechanical wiring: my
    independent gate above shows the composition typechecks against the frozen types
    today, with axiom footprint `{propext, Classical.choice, Quot.sound,
    heath_brown_diagonal_13}`.
  - NET-PROGRESS VERDICT: **net progress toward `erdos_477`** — decisively, not
    scaffolding. Iteration 2 discharged the frozen `no_linear_param` outright (2 of 5
    frozen theorems now sorry-free in Solution.lean) and landed the entire remaining
    mathematical content: the `5/6` bad-shift estimate (the HEART, Stage E), the
    pigeonhole criterion and the headline assembly (Stage F). No "Next:" crux recurs
    from Iteration 1 — Iteration 1's stated next steps were exactly Stages C/E/F and
    the harness fix, and all four landed. The remaining `Next:` (the Solution/Discharge
    restatements) is strictly simpler than anything named before: a discharged leaf,
    not a re-expression.
Required follow-ups:
  1. Assign ONE agent (owning `Erdos477/Solution.lean`, `Erdos477/Discharge.lean` and
     one new file, e.g. `Erdos477/Proofs/Wiring.lean`, importing BOTH
     `Erdos477.Proofs.ParamExclusion.Basic` and `Erdos477.Proofs.BadShift.Basic` and
     `Erdos477.Proofs.Assembly.Basic`, with the import added to `Erdos477.lean`) to
     define, APPEND-ONLY:
       `badShift_bound_proof c hc := badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)`
       `criterion_holds_proof := criterion_holds_of_badShift badShift_bound_proof`
       `erdos_477_proof := erdos_477_of_criterion criterion_holds_proof`
     then APPEND the three verbatim frozen restatements to `Solution.lean` and the
     three `@Frozen = @Proof := rfl` gates to `Discharge.lean`. This exact composition
     is already verified to elaborate — no new mathematics is required.
  2. Re-run `bash scripts/verify.sh` and require `=== RESULT: PASS (0 issue(s)) ===`
     with `Erdos477.Solution.erdos_477` showing
     `{propext, Classical.choice, Quot.sound, Erdos477.heath_brown_diagonal_13}`.
Verdict: INCOMPLETE

## Review -- Iteration 3
Auditor: review-iter3
Checks run:
  - `shasum -a 256 Erdos477/Defs.lean Erdos477/Theorems.lean` vs `scripts/frozen.sha256`
    → BOTH match byte-for-byte (42a2e988…, 26981420…). Frozen files untampered
    (mtimes 15:42/15:44, i.e. SETUP-era, older than every Iteration-3 edit).
  - `bash scripts/verify.sh` → full Checks 1–5, `=== RESULT: PASS (0 issue(s), 17s) ===`,
    exit 0. Check 4 PASSes all five `Erdos477.Solution.*`; Check 5 PASSes both gates.
  - `lake env lean /tmp/ax_audit.lean` (my own scratch file, `import Erdos477`), 11
    `#print axioms` + an independent `example : @Erdos477.erdos_477 =
    @Erdos477.erdos_477_proof := rfl` (elaborated, no output):
      Solution.no_linear_param → [propext, Classical.choice, Quot.sound]
      Solution.greedy_tiling   → [propext, Classical.choice, Quot.sound]
      Solution.badShift_bound  → [propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]
      Solution.criterion_holds → [propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]
      Solution.erdos_477       → [propext, Classical.choice, Erdos477.heath_brown_diagonal_13, Quot.sound]
      erdos_477_proof / badShift_bound_of_hexcl → same 4; criterion_holds_of_badShift,
      erdos_477_of_criterion, greedy_tiling_proof, no_linear_param_proof → standard three only.
    No `sorryAx`, no `brownawell_masser_P1_four_term`, no axiom off
    `scripts/ALLOWED_AXIOMS.txt`.
  - `grep -rnE "sorry|native_decide|admit|axiom|unsafe|implemented_by|ofReduceBool"
    Erdos477 --include=*.lean` minus Defs/Theorems → only prose hits in doc-comments; no
    `sorry` outside `Erdos477/Theorems.lean`, no `axiom` declaration outside `Defs.lean`.
  - Read in full: `Erdos477/Proofs/Wiring.lean`, `Solution.lean`, `Discharge.lean`,
    `Proofs/Greedy/Basic.lean`, `Proofs/Assembly/Basic.lean`, and `Proofs/BadShift/Basic.lean`
    (E3/E4), diffed the three new statements character-by-character against
    `Theorems.lean:31,46,52`.
Findings:
  - CONFIRMED GOOD — the three new frozen theorems are genuinely discharged. Statements in
    `Erdos477/Proofs/Wiring.lean:29-31`, `:35-37`, `:41-42` and their restatements in
    `Erdos477/Solution.lean:42-45`, `:49-52`, `:56-58` are VERBATIM `Theorems.lean:31-33`,
    `:46-48`, `:52-53`: exponent literally `(5:ℝ)/6`, `criterion_holds` still `∀ C : Finset ℤ`,
    `erdos_477` still `∃!` over the PAIR `p : ℤ × ℤ`. No hypothesis added, no `∀`
    specialised, no equality weakened to an inclusion.
  - CONFIRMED GOOD — `hexcl` is DISCHARGED, not inherited. `Erdos477/Proofs/Wiring.lean:32`
    feeds `Erdos477.no_linear_param_proof c hc` into `badShift_bound_of_hexcl`; the frozen
    `badShift_bound` carries only `(c : ℤ) (hc : c ∉ Bset)`. The five no-drift gates at
    `Erdos477/Discharge.lean:20,22,24,26,28` all elaborate, and I reproduced the
    `erdos_477` one independently in my own scratch file.
  - CONFIRMED GOOD — axiom hygiene and faithfulness. Only `Erdos477.heath_brown_diagonal_13`
    appears beyond the standard three, entering at exactly one site
    (`Erdos477/Proofs/BadShift/Basic.lean:214`) in its CONDITIONAL form with the received
    `hexcl` passed through unchanged. Its Lean statement (`Erdos477/Defs.lean:74-82`) matches
    USER_NOTES.md §"Axiom 1" point-for-point: `M ≠ 0`, exclusion hypothesis on degree-≤1
    triples, `∃ K ≥ 1`, `∀ X ≥ 1`, `ncard` of the box-`X` solution set `≤ K * X^(10/13)`.
    `brownawell_masser_P1_four_term` (`Defs.lean:102-112`, faithful to USER_NOTES.md
    §"Axiom 2": common degree `d`, coprime, `∑ = 0`, no vanishing proper sub-sum, ratios not
    all constant, `d ≤ 3*(z-2)`) is declared but UNUSED — the preferred Route-B outcome.
  - CONFIRMED GOOD — no trivialization. The counted solution set is proved FINITE
    (`sol_finite`, `Proofs/BadShift/Basic.lean:187`) so the `ncard` bound is not vacuous;
    `Φ` is injective (`Phi_inj`, `:70`) and the box radius is the honest `C_c·T^(13/12)`
    (`Xb`, `:102`), so the `5/6` is real, not `O(T²)` slack. `criterion_holds_of_badShift`
    (`Proofs/Assembly/Basic.lean:58`) keeps the STRICT comparison against the FULL
    two-sided `2T+1` (`:100-108`, `card_Icc_neg` `:31`) with `K = ∑_{c ∈ C} KK c` over ALL
    of `C` (`:74`). `greedy_tiling_proof` (`Proofs/Greedy/Basic.lean:160`) keeps `B`
    abstract, applies `H` to the full image Finset (`:71`) and proves BOTH existence and
    uniqueness (`:169-186`). `erdos_477_of_criterion` (`:129`) keeps uniqueness of `m` via
    `pow13_eq_iff` (`:149`) and bridges only through `dset_eq_sub` (`:138`).
  - CONFIRMED GOOD — process. Iteration 3's agent touched exactly its four assigned files
    (`Proofs/Wiring.lean` new, plus one `import` line in `Erdos477.lean:14` and append-only
    additions to `Solution.lean`/`Discharge.lean`, whose Iteration-1/2 `greedy_tiling` and
    `no_linear_param` entries are intact at `Solution.lean:25-39` / `Discharge.lean:20,22`).
    `scripts/verify.sh` (mtime 16:26), `scripts/frozen.sha256`, `scripts/ALLOWED_AXIOMS.txt`,
    `Defs.lean` and `Theorems.lean` were NOT modified this iteration. PROGRESS.md is
    append-only and every Iteration-3 claim in it reproduced under my own tooling — no
    faked ✅.
  - NET-PROGRESS VERDICT: **net progress toward `erdos_477`** — this iteration closed the
    goal. Three of the five frozen theorems went from unstated to proved-and-gated
    sorry-free; no crux recurred from Iterations 1–2 (Iteration 2's stated `Next:` was
    exactly this wiring, and it landed). Nothing lateral, nothing re-wrapped.
Required follow-ups: none.
Verdict: COMPLETE

## Review -- Iteration 3  (FULL PROJECT AUDIT)
Auditor: review-iter3
Checks run:
  - `bash scripts/verify.sh` (full, my own run) → Checks 1-5 all PASS,
    `=== RESULT: PASS (0 issue(s), 16s) ===`, exit 0. Check 4 PASSes all five
    `Erdos477.Solution.*`; Check 5 PASSes both the Discharge and Solution gates.
  - `shasum -a 256 Erdos477/Defs.lean Erdos477/Theorems.lean` compared by eye against
    `scripts/frozen.sha256` → both match byte-for-byte (42a2e988…, 26981420…).
  - `lake build` (inside verify.sh Check 3) → "Build completed successfully (8570 jobs)",
    0 errors, 0 warnings other than the 5 expected `declaration uses 'sorry'` from the
    byte-frozen `Erdos477/Theorems.lean`.
  - `lake env lean /tmp/audit_ax.lean` — my own scratch file (`import Erdos477.Solution`,
    `import Erdos477.Discharge`) with 16 `#print axioms` plus an INDEPENDENT re-statement
    gate `example : ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
    Erdos477.erdos_477_proof` (elaborated with no error), results:
      Solution.no_linear_param, Solution.greedy_tiling, no_linear_param_proof,
      greedy_tiling_proof, criterion_holds_of_badShift, erdos_477_of_criterion,
      pow13_gap, qcof_lower → [propext, Classical.choice, Quot.sound]
      dset_eq_sub → [propext, Quot.sound]
      Solution.badShift_bound, Solution.criterion_holds, Solution.erdos_477,
      badShift_bound_proof, criterion_holds_proof, erdos_477_proof,
      badShift_bound_of_hexcl → [propext, Classical.choice,
      Erdos477.heath_brown_diagonal_13, Quot.sound]
    No `sorryAx`, no `brownawell_masser_P1_four_term`, no axiom outside
    `scripts/ALLOWED_AXIOMS.txt`.
  - `grep -rn --include='*.lean' -E "sorry|native_decide|admit|^axiom |unsafe|implemented_by"`
    over `Erdos477/` + `Erdos477.lean` → only doc-comment prose plus the two whitelisted
    `axiom` declarations at `Erdos477/Defs.lean:74,102`. No `sorry` outside `Theorems.lean`.
  - Read END-TO-END, line by line (full-project pass, not just this iteration):
    `Defs.lean`, `Theorems.lean`, `Solution.lean`, `Discharge.lean`, `Erdos477.lean`,
    `Proofs/Wiring.lean`, `Proofs/Elementary/Basic.lean`, `Proofs/Cofactor/Basic.lean`,
    `Proofs/ParamExclusion/Basic.lean`, `Proofs/Greedy/Basic.lean`,
    `Proofs/BadShift/Basic.lean`, `Proofs/Assembly/Basic.lean`, and all 297 lines of
    `scripts/verify.sh`; compared every frozen statement against `SKETCH.md` §0 (target),
    §9.2 (suggested statements), §3 (HB axiom) and `USER_NOTES.md` §Axiom 1 / §Axiom 2.
Findings:
  - CONFIRMED GOOD — every iteration-3 ✅ reproduces. The three theorems wired this
    iteration (`Erdos477/Proofs/Wiring.lean:29,35,41`) carry statements character-identical
    to `Erdos477/Theorems.lean:31-33,46-48,52-53`, are restated verbatim at
    `Erdos477/Solution.lean:42-45,49-52,56-58`, and all five no-drift gates
    (`Erdos477/Discharge.lean:20,22,24,26,28`) elaborate. Exponent is literally `(5:ℝ)/6`;
    `criterion_holds` is still `∀ C : Finset ℤ`; `erdos_477` is still `∃!` over the PAIR.
  - CONFIRMED GOOD — `hexcl` is discharged, never inherited. `Proofs/Wiring.lean:32` feeds
    `no_linear_param_proof c hc` into `badShift_bound_of_hexcl`; the frozen `badShift_bound`
    has exactly the two binders `(c : ℤ) (hc : c ∉ Bset)`. No frozen statement anywhere
    gained a hypothesis, lost a `∀`, or had an equality softened to an inclusion.
  - CONFIRMED GOOD — axiom faithfulness. `Erdos477.heath_brown_diagonal_13`
    (`Defs.lean:74-82`) matches `USER_NOTES.md` §Axiom 1 point for point: `M ≠ 0`, the
    conditional degree-≤1 exclusion hypothesis, `∃ K ≥ 1`, `∀ real X ≥ 1`, `ncard` of the
    box-`X` solution set `≤ K * X^(10/13)`. It is invoked at exactly ONE site
    (`Proofs/BadShift/Basic.lean:213`), in conditional form, with the received `hexcl`
    passed through unchanged. `brownawell_masser_P1_four_term` (`Defs.lean:102-112`) is
    faithful to §Axiom 2 and is UNUSED — the preferred Route-B outcome.
  - CONFIRMED GOOD — no large-scale trivialization anywhere in the chain, re-derived by
    hand: (a) `Bset`/`Dset`/`Qcof`/`Sset` (`Defs.lean:41,45,50,56`) are the honest objects;
    `Sset` filters the FULL two-sided `Icc (-T) T`. (b) `dset_eq_sub`
    (`Proofs/Elementary/Basic.lean:76`) is a genuine `Set.ext` equality, both inclusions
    proved; `pow13_inj` (`:40`) is global on ℤ. (c) `qcof_lower`
    (`Proofs/Cofactor/Basic.lean:69`) holds for ALL reals with the honest constant exactly
    `1/2`, via the `ring`-checked sum-of-squares identity `two_mul_qcof_eq` (`:44`) — an
    equivalent route to SKETCH §4, not a weaker bound; `pow13_gap` (`:91`) keeps `u ≠ v`.
    (d) `no_linear_param_proof` (`Proofs/ParamExclusion/Basic.lean:173`) is proved for ALL
    triples with no side hypothesis: the full 8-way case split at `:81`, the `|I|=2` crux
    `two_nonzero_case` (`:49`) landing on `c ∈ Bset`, and the equal-ratio (Vandermonde)
    case at `:99-167` where the ratios are never assumed distinct. (e) Stage E is not
    vacuous: the counted set is proved finite (`sol_finite`, `Proofs/BadShift/Basic.lean:186`)
    so the `ncard` bound has content, `Phi` is injective (`:70`), and the box radius is the
    honest `C_c · T^(13/12)` (`Xb`, `:102`, with `Xb_pow12` `:127`) — no `O(T²)` slack, so
    the `5/6` is real. (f) `criterion_holds_of_badShift`
    (`Proofs/Assembly/Basic.lean:58`) sums `K` over ALL of `C` via a total `choose` (`:65-74`)
    and uses the STRICT sixth-power step (`mul_rpow_lt_self`, `:39`) against the FULL
    `2T+1 = #Icc (-T) T` (`card_Icc_neg`, `:31`). (g) `greedy_tiling_proof`
    (`Proofs/Greedy/Basic.lean:160`) keeps `B` abstract, applies `H` to the whole image
    Finset (`:71`), and proves existence AND uniqueness (`:169-186`).
    (h) `erdos_477_of_criterion` (`:129`) keeps uniqueness of `m` via `pow13_eq_iff` (`:149`)
    and bridges concrete→abstract only through `dset_eq_sub` (`:138`).
  - CONFIRMED GOOD — harness integrity. I re-read `scripts/verify.sh` in full: no check is
    weakened. It still bans `sorry`(outside Theorems.lean)/`sorryAx`/`native_decide`/
    `admit`/`unsafe`/`implemented_by`/`ofReduceBool` and any non-whitelisted `axiom`,
    still requires a warning-clean build, still parses the axiom list per theorem against
    `{propext, Classical.choice, Quot.sound} ∪ ALLOWED_AXIOMS.txt`, and still exits with
    the number of failed checks. `scripts/ALLOWED_AXIOMS.txt` contains exactly the two
    user-permitted names and `scripts/frozen.sha256` is unchanged.
  - CONFIRMED GOOD — process. Iteration 3's agent touched exactly its four assigned files
    (new `Proofs/Wiring.lean`; one added `import` at `Erdos477.lean:14`; append-only
    additions to `Solution.lean`/`Discharge.lean`, whose Iteration-1/2 entries are intact
    at `Solution.lean:25-39` and `Discharge.lean:20,22`). `PROGRESS.md` is append-only with
    no rewritten history, and every ✅ in it — from SETUP through Iteration 3 — reproduced
    under my own tooling. NO faked ✅ found anywhere in the project.
  - NO cheats, NO regressions, NO faithfulness gaps found in the full end-to-end pass.
    Minor, non-blocking cosmetics only: the unused hypothesis `_hK` in `mul_rpow_lt_self`
    (`Proofs/Assembly/Basic.lean:39`) and the exported-but-unused
    `zero_mem_Dabs`/`nonempty_of_Hyp` (`Proofs/Greedy/Basic.lean:37,55`). Neither affects
    any statement or proof.
  - NET-PROGRESS VERDICT: **net progress toward `erdos_477` — the goal is reached.** This
    iteration turned three still-open frozen theorems (`badShift_bound`, `criterion_holds`,
    `erdos_477`) into proved, gated, sorry-free declarations; all five frozen theorems are
    now discharged. No crux recurred across iterations: Iteration 2's stated `Next:` was
    exactly this wiring, and it landed. Nothing lateral, nothing re-wrapped.
Required follow-ups: none.
Verdict: COMPLETE
