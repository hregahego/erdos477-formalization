/-
  Erdős 477 — the TEN frozen theorem statements.

  This file is BYTE-FROZEN after SETUP (pinned in `scripts/frozen.sha256`).
  Every statement is `:= sorry`; the actual proofs live in `Erdos477/Proofs/**`
  and are re-exposed, sorry-free, in `Erdos477/Solution.lean`. NOTHING in this
  file — not a character of any statement — may change during the proving phase.
  `sorry` is permitted ONLY in this file (the frozen stubs).

  Mapping to `SKETCH.md` (see BLUEPRINT.md Part −1 §3 for the full table):
    * `Dset_neg_mem`           ↔ L0.2   (symmetry of `D`)
    * `pow13_injective`        ↔ L0.3   (odd-power injectivity)
    * `pow13_sub_pow13_factor` ↔ §4     (factorization `u¹³−v¹³ = (u−v)·Q`)
    * `cofactor_lower_bound`   ↔ L1.1   (explicit `κ = 1/2` bound, over ℝ)
    * `pow13_gap`              ↔ L1.2   (gap bound for distinct 13th powers)
    * `no_linear_param`        ↔ L2.1   (exclusion of linear parametrizations;
                                         per USER_NOTES.md its proof must follow
                                         the paper's Route A via Theorem 2.1)
    * `badShift_bound`         ↔ P3.1 / Prop 4.1 (the `5/6` exponent — HEART)
    * `greedy_tiling`          ↔ L4.1 / Lemma 5.1 (abstract `B` — MILESTONE)
    * `criterion_for_B`        ↔ P5.1 / Prop 5.2 (the criterion holds for `B`)
    * `erdos_477`              ↔ Theorem 1.1 (the HEADLINE `∃!`)
-/
import Erdos477.Defs

namespace Erdos477

/-- **L0.2 — `D` is symmetric.** From `d = u¹³ − v¹³` swap the witnesses. -/
theorem Dset_neg_mem {d : ℤ} (hd : d ∈ Dset) : -d ∈ Dset := sorry

/-- **L0.3 — odd-power injectivity** (needed for the `(a,b) → (a,m)` uniqueness
upgrade in the headline). -/
theorem pow13_injective : Function.Injective (fun m : ℤ => m ^ 13) := sorry

/-- **L1 factorization (§4 display).** `u¹³ − v¹³ = (u − v) · Q(u,v)` over `ℤ`. -/
theorem pow13_sub_pow13_factor (u v : ℤ) :
    u ^ 13 - v ^ 13 = (u - v) * Qcof u v := sorry

/-- **L1.1 — explicit cofactor lower bound** (`κ = 1/2`), over `ℝ`. -/
theorem cofactor_lower_bound (u v : ℝ) :
    (1 / 2 : ℝ) * max |u| |v| ^ 12 ≤ Qcof u v := sorry

/-- **L1.2 — gap bound** for distinct integer thirteenth powers. -/
theorem pow13_gap (u v : ℤ) (huv : u ≠ v) :
    (1 / 2 : ℝ) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := sorry

/-- **L2.1 — exclusion of linear parametrizations.** Supplies the exclusion
input to the Heath-Brown count for `M = −c`, `c ∉ Bset`. Per `USER_NOTES.md`
the proof feeding the main theorem must follow the paper's Route A (Lemma 3.1 +
Corollary 3.2 via `brownawell_masser_P1_four_term`), not Route B. -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) :
    ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := sorry

/-- **P3.1 — the bad-shift estimate** `|S_c(T)| ≤ K_c · T^(5/6)` (the
mathematical HEART; the only frozen theorem whose proof invokes the Heath-Brown
axiom). -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := sorry

/-- **L4.1 — greedy tiling criterion** (self-contained combinatorics), for an
abstract `B` with the abstract difference set `{d | ∃ x ∈ B, ∃ y ∈ B, d = x − y}`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
         ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := sorry

/-- **P5.1 — `Bset` satisfies the criterion's hypothesis `H`.** -/
theorem criterion_for_B :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := sorry

/-- **Theorem 1.1 — HEADLINE.** The thirteenth powers have a tiling complement:
there is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m¹³` with `a ∈ A`,
`m ∈ ℤ` (uniqueness over the PAIR `(a, m)`). -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := sorry

end Erdos477
