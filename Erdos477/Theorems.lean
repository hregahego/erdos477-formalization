/-
  Erdős 477 — the frozen theorem statement.

  This file holds exactly ONE declaration: the headline `erdos_477`
  (the paper's Theorem 1.1), as a `:= sorry` stub. It is BYTE-FROZEN after
  SETUP (pinned in `scripts/frozen.sha256`): NOTHING in this file — not a
  character of the statement — may change during the proving phase. `sorry` is
  permitted ONLY here.

  The actual proof lives in `Erdos477/Proofs/**` (as the sorry-free
  `Erdos477.erdos_477_proof`, Stage Assembly) and is re-exposed, sorry-free, as
  `Erdos477.Solution.erdos_477`; `Erdos477/Discharge.lean` gates the two
  against each other by `rfl`.

  Every INTERMEDIATE result of the development — the paper's L0.2, L0.3, §4,
  L1.1, L1.2, L2.1, P3.1, L4.1, P5.1 — is no longer stated here. Each is a
  working lemma of the stage that proves it, stated where it is proved
  (see `BLUEPRINT.md` Part −1 §3 for the full sketch↔Lean table):
    * L0.2 `Dset_neg_mem_proof`, L0.3 `pow13_injective_proof`
                             — `Erdos477/Proofs/Elementary/Basic.lean`
    * §4 `pow13_sub_pow13_factor_proof`, L1.1 `cofactor_lower_bound_proof`,
      L1.2 `pow13_gap_proof`  — `Erdos477/Proofs/Cofactor/Basic.lean`
    * L2.1 `no_linear_param_proof`
                             — `Erdos477/Proofs/ParamExclusion/Spine.lean`
    * P3.1 `badShift_bound_proof`  — `Erdos477/Proofs/BadShift/Basic.lean`
    * L4.1 `greedy_tiling_proof`   — `Erdos477/Proofs/Greedy/Basic.lean`
    * P5.1 `criterion_for_B_proof` — `Erdos477/Proofs/Assembly/Basic.lean`
-/
import Erdos477.Defs

namespace Erdos477

/-- **Theorem 1.1 — HEADLINE.** The thirteenth powers have a tiling complement:
there is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m¹³` with `a ∈ A`,
`m ∈ ℤ` (uniqueness over the PAIR `(a, m)`). -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := sorry

end Erdos477
