/-
  Erdős 477 — clean, sorry-free restatements of the ten frozen theorems.

  For each frozen theorem `<name>` proved in `Erdos477/Proofs/**` (as a
  sorry-free declaration `<name>_proof`), this file holds, in
  `namespace Erdos477.Solution`, a VERBATIM restatement

      theorem <name> : <frozen statement> := <name>_proof

  `verify.sh` Check 4 runs `#print axioms Erdos477.Solution.<name>` for each of
  the ten frozen names and requires the axioms to lie within the allowlist
  ({propext, Classical.choice, Quot.sound} ∪ scripts/ALLOWED_AXIOMS.txt). Per
  `USER_NOTES.md`, `#print axioms Erdos477.Solution.erdos_477` must show BOTH
  `Erdos477.heath_brown_diagonal_13` AND
  `Erdos477.brownawell_masser_P1_four_term`.

  Currently wired (Iteration 2): the six theorems proved in Iteration 1 —
  Dset_neg_mem, pow13_injective, pow13_sub_pow13_factor, cofactor_lower_bound,
  pow13_gap, greedy_tiling. Still frozen `sorry` stubs upstream (NOT restated
  here yet): no_linear_param, badShift_bound, criterion_for_B, erdos_477.
-/
import Erdos477.Theorems
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.ParamExclusion.Degenerate
import Erdos477.Proofs.ParamExclusion.Spine
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.BadShift.Basic
import Erdos477.Proofs.Assembly.Basic

namespace Erdos477.Solution

/-- **L0.2 — `D` is symmetric.** From `d = u¹³ − v¹³` swap the witnesses. -/
theorem Dset_neg_mem {d : ℤ} (hd : d ∈ Dset) : -d ∈ Dset :=
  Dset_neg_mem_proof hd

/-- **L0.3 — odd-power injectivity** (needed for the `(a,b) → (a,m)` uniqueness
upgrade in the headline). -/
theorem pow13_injective : Function.Injective (fun m : ℤ => m ^ 13) :=
  pow13_injective_proof

/-- **L1 factorization (§4 display).** `u¹³ − v¹³ = (u − v) · Q(u,v)` over `ℤ`. -/
theorem pow13_sub_pow13_factor (u v : ℤ) :
    u ^ 13 - v ^ 13 = (u - v) * Qcof u v :=
  pow13_sub_pow13_factor_proof u v

/-- **L1.1 — explicit cofactor lower bound** (`κ = 1/2`), over `ℝ`. -/
theorem cofactor_lower_bound (u v : ℝ) :
    (1 / 2 : ℝ) * max |u| |v| ^ 12 ≤ Qcof u v :=
  cofactor_lower_bound_proof u v

/-- **L1.2 — gap bound** for distinct integer thirteenth powers. -/
theorem pow13_gap (u v : ℤ) (huv : u ≠ v) :
    (1 / 2 : ℝ) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| :=
  pow13_gap_proof u v huv

/-- **L4.1 — greedy tiling criterion** (self-contained combinatorics), for an
abstract `B` with the abstract difference set `{d | ∃ x ∈ B, ∃ y ∈ B, d = x − y}`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n :=
  greedy_tiling_proof B H

/-- **L2.1 — exclusion of linear parametrizations.** Supplies the exclusion
input to the Heath-Brown count for `M = −c`, `c ∉ Bset`. Per `USER_NOTES.md`
the proof feeding the main theorem must follow the paper's Route A (Lemma 3.1 +
Corollary 3.2 via `brownawell_masser_P1_four_term`), not Route B. -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 :=
  no_linear_param_proof c hc

/-- **P3.1 — the bad-shift estimate** `|S_c(T)| ≤ K_c · T^(5/6)` (the
mathematical HEART; the only frozen theorem whose proof invokes the Heath-Brown
axiom). -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) :=
  badShift_bound_proof c hc

/-- **P5.1 — `Bset` satisfies the criterion's hypothesis `H`.** -/
theorem criterion_for_B :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset :=
  criterion_for_B_of_bound badShift_bound_proof

/-- **Theorem 1.1 — HEADLINE.** The thirteenth powers have a tiling complement:
there is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m¹³` with `a ∈ A`,
`m ∈ ℤ` (uniqueness over the PAIR `(a, m)`). -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  erdos_477_of_criterion (criterion_for_B_of_bound badShift_bound_proof)

end Erdos477.Solution
