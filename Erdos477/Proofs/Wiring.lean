/-
  Erdős 477 — final wiring (BLUEPRINT §"Discharge & Solution").

  No new mathematics: this module only COMPOSES the sorry-free support lemmas
  proved in earlier stages into the three remaining frozen statements.

      Stage C  `no_linear_param_proof`      (Proofs/ParamExclusion/Basic.lean)
        ↓ discharges `hexcl`
      Stage E  `badShift_bound_of_hexcl`    (Proofs/BadShift/Basic.lean)
        ↓ discharges `hBS`
      Stage F1 `criterion_holds_of_badShift`(Proofs/Assembly/Basic.lean)
        ↓ discharges `hcrit`
      Stage F2 `erdos_477_of_criterion`     (Proofs/Assembly/Basic.lean)

  Each statement below is VERBATIM the frozen one in `Erdos477/Theorems.lean`;
  the `rfl` gates in `Erdos477/Discharge.lean` machine-check that.
-/
import Erdos477.Defs
import Erdos477.Theorems
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.BadShift.Basic
import Erdos477.Proofs.Assembly.Basic

namespace Erdos477

/-- **P3.1 (§6, Prop 4.1).** The bad-shift estimate `|S_c(T)| ≤ K_c · T^(5/6)`.
The axiom's exclusion hypothesis `hexcl` is discharged HERE by Stage C — the
frozen statement gains no hypothesis. -/
theorem badShift_bound_proof (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) :=
  Erdos477.badShift_bound_of_hexcl c hc (Erdos477.no_linear_param_proof c hc)

/-- **P5.1 (§8.1, Prop 5.2).** `Bset` satisfies the criterion `(H)`. -/
theorem criterion_holds_proof :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset :=
  Erdos477.criterion_holds_of_badShift (fun c hc => badShift_bound_proof c hc)

/-- **Theorem 1.1 (§8.2).** The headline: the thirteenth powers tile `ℤ`. -/
theorem erdos_477_proof :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  Erdos477.erdos_477_of_criterion criterion_holds_proof

end Erdos477
