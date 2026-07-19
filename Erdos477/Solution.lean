/-
  Erdős 477 — clean, sorry-free restatements of the five frozen theorems.

  SETUP STUB. Once a frozen theorem `<name>` is proved in `Erdos477/Proofs/**`
  (as a sorry-free declaration `<name>_proof`), add here, in
  `namespace Erdos477.Solution`, a VERBATIM restatement

      theorem <name> : <frozen statement> := <name>_proof

  `verify.sh` Check 4 runs `#print axioms Erdos477.Solution.<name>` for each of
  no_linear_param, badShift_bound, greedy_tiling, criterion_holds, erdos_477 and
  requires the axioms to lie within the allowlist. At SETUP these are still
  `sorry` upstream, so this stub intentionally defines none of them yet.
-/
import Erdos477.Theorems
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.ParamExclusion.Basic
import Erdos477.Proofs.Wiring

namespace Erdos477.Solution

/-- **L4.1 (§7, Lemma 5.1).** The greedy tiling criterion (pure combinatorics):
if every finite `C ⊆ ℤ∖B` has a `b ∈ B` with `(C − b) ∩ (B − B) = ∅`, then `B`
has a tiling complement `A` with a UNIQUE `(a,b)` representation of every `n`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n :=
  Erdos477.greedy_tiling_proof B H

/-- **L2.1 (§5.1, Route B).** The diagonal surface admits no nonconstant *linear*
polynomial parametrisation: for `c ∉ Bset`, every triple of polynomials of degree
`≤ 1` whose thirteenth powers sum to the constant `-c` is a triple of constants. -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 :=
  Erdos477.no_linear_param_proof c hc

/-- **P3.1 (§6, Prop 4.1).** The bad-shift estimate `|S_c(T)| ≤ K_c · T^(5/6)`. -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) :=
  Erdos477.badShift_bound_proof c hc

/-- **P5.1 (§8.1, Prop 5.2).** `Bset` satisfies the criterion `(H)`: every finite
`C ⊆ ℤ∖Bset` has a `b ∈ Bset` with `c − b ∉ Dset` for all `c ∈ C`. -/
theorem criterion_holds :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset :=
  Erdos477.criterion_holds_proof

/-- **Theorem 1.1 (§8.2).** The headline — the thirteenth powers tile `ℤ`: there
is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m ^ 13` with `a ∈ A`, `m ∈ ℤ`. -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  Erdos477.erdos_477_proof

end Erdos477.Solution
