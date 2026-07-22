/-
  Erdős 477 — the clean, sorry-free restatement of the frozen theorem.

  The frozen statement `Erdos477.erdos_477` of `Erdos477/Theorems.lean` is
  proved, sorry-free, as `Erdos477.erdos_477_proof` in
  `Erdos477/Proofs/Assembly/Basic.lean`. This file holds, in
  `namespace Erdos477.Solution`, its VERBATIM restatement

      theorem erdos_477 : <frozen statement> := erdos_477_proof

  `verify.sh` Check 4 runs `#print axioms Erdos477.Solution.erdos_477` and
  requires the axioms to lie within the allowlist
  ({propext, Classical.choice, Quot.sound} ∪ scripts/ALLOWED_AXIOMS.txt). Per
  `USER_NOTES.md`, that print must show BOTH
  `Erdos477.heath_brown_diagonal_13` AND
  `Erdos477.brownawell_masser_P1_four_term`.
-/
import Erdos477.Theorems
import Erdos477.Proofs.Assembly.Basic

namespace Erdos477.Solution

/-- **Theorem 1.1 — HEADLINE.** The thirteenth powers have a tiling complement:
there is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m¹³` with `a ∈ A`,
`m ∈ ℤ` (uniqueness over the PAIR `(a, m)`). -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  erdos_477_proof

end Erdos477.Solution
