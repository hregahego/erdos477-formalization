/-
  Stage Assembly (Layer 5) — criterion_for_B and erdos_477 (HEADLINE), plus the bridge Dset_eq_Bset_sub.

  Iteration 2 delivered the support bridge `Dset_eq_Bset_sub` (BLUEPRINT Part −1
  §2 D2 modeling note / Stage Assembly A2) — the identification of the frozen
  `Dset` (differences of thirteenth powers, `u ^ 13 - v ^ 13` directly) with the
  abstract Minkowski-style difference set `{d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x − y}`
  that the frozen `greedy_tiling` speaks about.

  Iteration 3 adds the CONDITIONAL Assembly layer: both stage-A payloads proved
  as support lemmas whose single extra hypothesis is character-exact a frozen
  statement, so that iteration 4 discharges frozen `criterion_for_B` and
  `erdos_477` by pure composition once `badShift_bound_proof` lands:
    * `criterion_for_B_of_bound` — hypothesis = the ∀-closure of frozen
      `badShift_bound`; conclusion = frozen `criterion_for_B`, character-exact
      (SKETCH §8.1 / P5.1, the strict pigeonhole off `Finset.Icc (-T) T`).
    * `erdos_477_of_criterion` — hypothesis = frozen `criterion_for_B`,
      character-exact; conclusion = frozen `erdos_477`, character-exact
      (SKETCH §8.2, `greedy_tiling_proof` at `B := Bset` + the mandatory
      `pow13_injective` upgrade from `(a, b)`- to `(a, m)`-uniqueness).

  Support declarations go in `namespace Erdos477` (never shadow a frozen name);
  the frozen statements themselves live untouched in `Erdos477/Theorems.lean`.
-/
import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.BadShift.Basic

namespace Erdos477

/-- **A2 bridge — `Dset` is the difference set of `Bset`.** Both inclusions by
witness manipulation: `u ^ 13 − v ^ 13` corresponds to `x − y` with
`x := u ^ 13 ∈ Bset`, `y := v ^ 13 ∈ Bset`, and conversely. This lets the
assembly of `erdos_477` apply the frozen `greedy_tiling` (stated for an abstract
`B` with its abstract difference set) to `B := Bset`, translating its avoidance
condition into the frozen `Dset` of `criterion_for_B`. -/
theorem Dset_eq_Bset_sub : Dset = {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y} := by
  ext d
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨u ^ 13, ⟨u, rfl⟩, v ^ 13, ⟨v, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, rfl⟩, y, ⟨v, rfl⟩, rfl⟩
    exact ⟨u, v, rfl⟩

/-- **A1 conditional — P5.1 modulo the bad-shift bound.** The hypothesis `hbnd`
is the ∀-closure of the frozen `badShift_bound` statement, verbatim; the
conclusion is character-exact the frozen `criterion_for_B`. Proof per SKETCH
§8.1: `C = ∅` takes `b := 0`; otherwise sum the constants `K_c` to `K`, pick an
integer `T > K ^ 6`, bound the bad set `⋃_{c ∈ C} Sset c T` strictly below `T`
(hence strictly below the `2T + 1` elements of `Finset.Icc (-T) T`), and turn
the surviving shift `t₀` into `b := t₀ ^ 13` via `badShift_iff`. -/
theorem criterion_for_B_of_bound
    (hbnd : ∀ c : ℤ, c ∉ Bset → ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)) :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := by
  intro C hC
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨0, zero_mem_Bset, by simp⟩
  -- Choose the constants `K_c` (with `K := 1` off `C`, so `choose` is total).
  have hchoice : ∀ c : ℤ, ∃ K : ℝ, 1 ≤ K ∧ (c ∈ C → ∀ T : ℤ, 1 ≤ T →
      ((Sset c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)) := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨K, hK1, hKb⟩ := hbnd c (hC c hc)
      exact ⟨K, hK1, fun _ => hKb⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose Kf hKf1 hKfb using hchoice
  set K : ℝ := ∑ c ∈ C, Kf c with hKdef
  obtain ⟨c₀, hc₀⟩ := hCne
  have hKsum : Kf c₀ ≤ K := by
    rw [hKdef]
    exact Finset.single_le_sum (fun c _ => zero_le_one.trans (hKf1 c)) hc₀
  have hK1 : 1 ≤ K := (hKf1 c₀).trans hKsum
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK1
  -- The threshold: an explicit integer `T ≥ 1` with `K ^ 6 < T`.
  set T : ℤ := ((⌈K⌉₊ : ℤ)) ^ 6 + 1 with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact le_add_of_nonneg_left (pow_nonneg (Int.natCast_nonneg _) 6)
  have hTR : (0 : ℝ) < (T : ℝ) := by
    have h : (0 : ℤ) < T := by omega
    exact_mod_cast h
  have hKT : K ^ 6 < (T : ℝ) := by
    have hceil : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    have h6 : K ^ 6 ≤ ((⌈K⌉₊ : ℝ)) ^ 6 := by gcongr
    have hcast : (T : ℝ) = ((⌈K⌉₊ : ℝ)) ^ 6 + 1 := by rw [hTdef]; push_cast; ring
    linarith
  -- The union of the bad shift sets, bounded by `K · T^(5/6)`.
  set bad : Finset ℤ := C.biUnion (fun c => Sset c T) with hbaddef
  have hbad_le : (bad.card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := by
    calc (bad.card : ℝ)
        ≤ ((∑ c ∈ C, (Sset c T).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ = ∑ c ∈ C, ((Sset c T).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ c ∈ C, Kf c * (T : ℝ) ^ ((5 : ℝ) / 6) :=
          Finset.sum_le_sum fun c hc => hKfb c hc T hT1
      _ = K * (T : ℝ) ^ ((5 : ℝ) / 6) := by rw [hKdef, Finset.sum_mul]
  -- The strict pigeonhole input: `K · T^(5/6) < T`, via sixth powers.
  have hTpow6 : ((T : ℝ) ^ ((5 : ℝ) / 6)) ^ (6 : ℕ) = (T : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast ((T : ℝ) ^ ((5 : ℝ) / 6)) 6, ← Real.rpow_mul hTR.le,
      ← Real.rpow_natCast (T : ℝ) 5]
    norm_num
  have hlt : K * (T : ℝ) ^ ((5 : ℝ) / 6) < (T : ℝ) := by
    refine lt_of_pow_lt_pow_left₀ 6 hTR.le ?_
    calc (K * (T : ℝ) ^ ((5 : ℝ) / 6)) ^ 6 = K ^ 6 * (T : ℝ) ^ 5 := by rw [mul_pow, hTpow6]
      _ < (T : ℝ) * (T : ℝ) ^ 5 := mul_lt_mul_of_pos_right hKT (by positivity)
      _ = (T : ℝ) ^ 6 := by ring
  -- Strictly fewer bad shifts than the `2T + 1` candidates in `Icc (-T) T`.
  have hIccT : ((Finset.Icc (-T) T).card : ℤ) = 2 * T + 1 := by
    rw [Int.card_Icc]
    omega
  have hbad_lt : bad.card < (Finset.Icc (-T) T).card := by
    have h2 : (bad.card : ℤ) < T := by exact_mod_cast lt_of_le_of_lt hbad_le hlt
    omega
  obtain ⟨t₀, ht₀, ht₀bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
  -- `b := t₀ ^ 13` works: `t₀ ∉ Sset c T` unfolds to `t₀ ^ 13 - c ∉ Dset`.
  refine ⟨t₀ ^ 13, ⟨t₀, rfl⟩, fun c hc hmem => ?_⟩
  have hD : t₀ ^ 13 - c ∈ Dset := badShift_iff.mp hmem
  have hmemS : t₀ ∈ Sset c T := by
    simp only [Sset, Finset.mem_filter]
    exact ⟨ht₀, hD⟩
  exact ht₀bad (Finset.mem_biUnion.mpr ⟨c, hc, hmemS⟩)

/-- **A2 conditional — Theorem 1.1 modulo the criterion.** The hypothesis
`hcrit` is character-exact the frozen `criterion_for_B` statement; the
conclusion is character-exact the frozen `erdos_477`. Proof per SKETCH §8.2:
apply `greedy_tiling_proof` at `B := Bset` (transporting the avoidance
condition through `Dset_eq_Bset_sub`), then upgrade the `(a, b)`-uniqueness to
the headline `(a, m)`-uniqueness via `pow13_injective_proof` (the MANDATORY
upgrade — BLUEPRINT Stage Assembly pitfall 1). -/
theorem erdos_477_of_criterion
    (hcrit : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := by
  have H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y} := by
    simpa only [← Dset_eq_Bset_sub] using hcrit
  obtain ⟨A, hA⟩ := greedy_tiling_proof Bset H
  refine ⟨A, fun n => ?_⟩
  obtain ⟨⟨a, b⟩, ⟨haA, hbB, hab⟩, huniq⟩ := hA n
  obtain ⟨m, rfl⟩ := hbB
  refine ⟨(a, m), ⟨haA, hab⟩, ?_⟩
  rintro ⟨a', m'⟩ ⟨ha'A, hn'⟩
  have hkey : ((a', m' ^ 13) : ℤ × ℤ) = (a, m ^ 13) :=
    huniq (a', m' ^ 13) ⟨ha'A, ⟨m', rfl⟩, hn'⟩
  have h1 : a' = a := (Prod.ext_iff.mp hkey).1
  have h3 : m' = m := pow13_injective_proof (Prod.ext_iff.mp hkey).2
  subst h1; subst h3; rfl

/-! ### The unconditional discharge

`badShift_bound_proof` (Stage BadShift) is now available, so both conditionals
above collapse to closed theorems. `erdos_477_proof` is the ONLY statement
restated in `Erdos477/Solution.lean` and gated in `Erdos477/Discharge.lean` —
its type is CHARACTER-EXACT the frozen `Erdos477.erdos_477`. -/

/-- **P5.1 — `Bset` satisfies the criterion's hypothesis `H`**: the conditional
`criterion_for_B_of_bound` fed with the bad-shift estimate. -/
theorem criterion_for_B_proof :
    ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset :=
  criterion_for_B_of_bound badShift_bound_proof

/-- **Theorem 1.1 — HEADLINE** (statement CHARACTER-EXACT to the frozen
`Erdos477.erdos_477` of `Erdos477/Theorems.lean`). The thirteenth powers have a
tiling complement: there is `A ⊆ ℤ` such that every `n` is UNIQUELY `a + m¹³`
with `a ∈ A`, `m ∈ ℤ` (uniqueness over the PAIR `(a, m)`).

Carries BOTH permitted axioms: `heath_brown_diagonal_13` (through the
Heath-Brown count in `badShift_bound_proof`) and
`brownawell_masser_P1_four_term` (through the Route-A exclusion
`no_linear_param_proof`). -/
theorem erdos_477_proof :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  erdos_477_of_criterion criterion_for_B_proof

/-- Guardrail (BLUEPRINT "Cheat watch (Stage Assembly)"): two DISTINCT
`(a, m)`-representations of one fixed `n` contradict the headline `∃!`. -/
example (A : Set ℤ) (hA : ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n)
    (a m a' m' : ℤ) (haA : a ∈ A) (ha'A : a' ∈ A)
    (heq : a + m ^ 13 = a' + m' ^ 13) (hne : ((a, m) : ℤ × ℤ) ≠ (a', m')) : False := by
  obtain ⟨p, -, huniq⟩ := hA (a + m ^ 13)
  exact hne ((huniq (a, m) ⟨haA, rfl⟩).trans (huniq (a', m') ⟨ha'A, heq.symm⟩).symm)

end Erdos477
