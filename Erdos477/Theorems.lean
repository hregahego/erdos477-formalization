/-
  Erdős 477 — the FIVE frozen theorem statements.

  This file is BYTE-FROZEN after SETUP (pinned in `scripts/frozen.sha256`).
  Every statement is `:= sorry`; the actual proofs live in `Erdos477/Proofs/**`
  and are re-exposed, sorry-free, in `Erdos477/Solution.lean`. NOTHING in this
  file — not a character of any statement — may change during the proving phase.
  `sorry` is permitted ONLY in this file (the frozen stubs).

  Mapping to `SKETCH.md`:
    * `no_linear_param` ↔ §5 L2.1 (Route B). Verifies the axiom's `hexcl`.
    * `badShift_bound`  ↔ §6 P3.1 / Prop 4.1. The `5/6` exponent (the HEART).
    * `greedy_tiling`   ↔ §7 L4.1 / Lemma 5.1. Abstract `B` (the MILESTONE).
    * `criterion_holds` ↔ §8.1 P5.1 / Prop 5.2. Instantiates the criterion.
    * `erdos_477`       ↔ §0 target + §8.2. The payoff `∃!` (the HEADLINE).
-/
import Erdos477.Defs

namespace Erdos477

/-- **L2.1 (§5.1, Route B).** The diagonal surface admits no nonconstant *linear*
polynomial parametrisation — i.e. the exclusion hypothesis `hexcl` of the axiom
`heath_brown_diagonal_13` holds for `M = -c` when `c ∉ Bset`. -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := sorry

/-- **P3.1 (§6, Prop 4.1).** The bad-shift estimate `|S_c(T)| ≤ K_c · T^(5/6)`. -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := sorry

/-- **L4.1 (§7, Lemma 5.1).** The greedy tiling criterion (pure combinatorics):
if every finite `C ⊆ ℤ∖B` has a `b ∈ B` with `(C − b) ∩ (B − B) = ∅`, then `B`
has a tiling complement `A` with a UNIQUE `(a,b)` representation of every `n`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n :=
  sorry

/-- **P5.1 (§8.1, Prop 5.2).** `Bset` satisfies the criterion `(H)`: every finite
`C ⊆ ℤ∖Bset` has a `b ∈ Bset` with `c − b ∉ Dset` for all `c ∈ C`. -/
theorem criterion_holds :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := sorry

/-- **Theorem 1.1 (§8.2).** The headline — the thirteenth powers tile `ℤ`: there
is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m ^ 13` with `a ∈ A`, `m ∈ ℤ`. -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := sorry

end Erdos477
