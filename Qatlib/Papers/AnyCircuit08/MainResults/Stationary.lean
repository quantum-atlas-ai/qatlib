/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AnyCircuit08.MainResults.Basic

/-!
# Stationarity of the Pauli weights

This module decomposes `randomCircuitStep` into fixed-pair sums `stepInner` and establishes
coordinate-update identities for `pairUpdate`. These identities support the proof that the
explicit weight function `stationaryWeight` is fixed by the circuit update for every natural
size [HallgrenHarrow2008].

## Main statements

* `randomCircuitStep_eq`: rewrites the circuit step as an average of fixed-pair sums.
* `pairUpdate_injective`: shows distinct label pairs yield distinct updates at distinct
  coordinates.
* `randomCircuitStep_stationary`: proves invariance of the proposed weights.

## References

* [Hallgren and Harrow, 2008][HallgrenHarrow2008]
-/

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

open scoped BigOperators

/-- The common nonzero-string weight `1 / (4 ^ n + 2 ^ n)`. -/
noncomputable def pauliConst (n : ℕ) : ℝ := 1 / ((4:ℝ) ^ n + (2:ℝ) ^ n)

/-- The stationary weight of a nonzero Pauli string equals `pauliConst n`. -/
theorem stationaryWeight_of_ne_zero {n : ℕ} {p : PauliString n} (hp : p ≠ 0) :
    stationaryWeight n p = pauliConst n := by
  simp [stationaryWeight, pauliConst, hp]

/-- The sum of incoming weights for the local Pauli update at the specified coordinate pair. -/
noncomputable def stepInner (n : ℕ) (μ : PauliString n → ℝ) (i j : Fin n)
    (q : PauliString n) : ℝ :=
  ∑ p : PauliString n,
    μ p *
      (if p i = 0 ∧ p j = 0 then
        (if q = p then 1 else 0)
       else if q i = 0 ∧ q j = 0 then 0
       else if (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k) then (1 / 15 : ℝ)
       else 0)

/-- The circuit step is the identity for `n < 2` and otherwise is the normalized sum of
`stepInner` over ordered distinct coordinate pairs [HallgrenHarrow2008]. -/
theorem randomCircuitStep_eq (n : ℕ) (μ : PauliString n → ℝ) (q : PauliString n) :
    randomCircuitStep n μ q =
      if n < 2 then μ q
      else (1 / (((n * (n - 1) : ℕ)) : ℝ)) *
        ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then stepInner n μ i j q else 0 := rfl

/-- The Pauli string obtained by updating coordinate `i` to the first label and then coordinate
`j` to the second label. -/
def pairUpdate {n : ℕ} (q : PauliString n) (i j : Fin n) (ab : Fin 4 × Fin 4) :
    PauliString n :=
  Function.update (Function.update q i ab.1) j ab.2

/-- A pair update preserves every coordinate distinct from both updated coordinates. -/
theorem pairUpdate_of_ne {n : ℕ} (q : PauliString n) {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (ab : Fin 4 × Fin 4) :
    pairUpdate q i j ab k = q k := by
  unfold pairUpdate
  rw [Function.update_of_ne hkj, Function.update_of_ne hki]

/-- At distinct update coordinates, `pairUpdate` takes its first assigned label at coordinate
`i`. -/
theorem pairUpdate_i {n : ℕ} (q : PauliString n) {i j : Fin n} (hij : i ≠ j)
    (ab : Fin 4 × Fin 4) :
    pairUpdate q i j ab i = ab.1 := by
  unfold pairUpdate
  rw [Function.update_of_ne hij]
  exact Function.update_self i ab.1 q

/-- A pair update takes its second assigned label at coordinate `j`. -/
theorem pairUpdate_j {n : ℕ} (q : PauliString n) {i j : Fin n}
    (ab : Fin 4 × Fin 4) :
    pairUpdate q i j ab j = ab.2 := by
  unfold pairUpdate
  exact Function.update_self j ab.2 (Function.update q i ab.1)

/-- Updating two distinct coordinates gives an injective map from label pairs to Pauli strings
[HallgrenHarrow2008]. -/
theorem pairUpdate_injective {n : ℕ} (q : PauliString n) {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (pairUpdate q i j) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : a = a' := by
    have := congrFun h i
    rw [pairUpdate_i q hij, pairUpdate_i q hij] at this
    exact this
  have h2 : b = b' := by
    have := congrFun h j
    rw [pairUpdate_j q, pairUpdate_j q] at this
    exact this
  exact Prod.ext h1 h2

/-- Updating distinct coordinates with a nonzero label pair yields a nonzero Pauli string. -/
theorem pairUpdate_ne_zero {n : ℕ} (q : PauliString n) {i j : Fin n} (hij : i ≠ j)
    {ab : Fin 4 × Fin 4} (hab : ab ≠ (0, 0)) : pairUpdate q i j ab ≠ 0 := by
  intro h
  apply hab
  have h1 : ab.1 = 0 := by
    have := congrFun h i
    rw [pairUpdate_i q hij] at this
    simpa using this
  have h2 : ab.2 = 0 := by
    have := congrFun h j
    rw [pairUpdate_j q] at this
    simpa using this
  exact Prod.ext h1 h2

/-- For every natural size `n`, the circuit update fixes `stationaryWeight n`
[HallgrenHarrow2008]. -/
theorem randomCircuitStep_stationary (n : ℕ) :
    randomCircuitStep n (stationaryWeight n) = stationaryWeight n := by
  funext q
  rw [randomCircuitStep_eq]
  by_cases hn : n < 2
  · rw [if_pos hn]
  rw [if_neg hn]
  have hn2 : 2 ≤ n := by omega

  have hpair : ∀ i j : Fin n, i ≠ j →
      stepInner n (stationaryWeight n) i j q = stationaryWeight n q := by
    intro i j hij
    unfold stepInner
    by_cases hq0 : q = 0
    · subst hq0
      rw [Finset.sum_eq_single (0 : PauliString n)]
      · simp [stationaryWeight]
      · intro p _ hp
        by_cases hpp : p i = 0 ∧ p j = 0
        · have hpq : ¬ ((0 : PauliString n) = p) := by
            intro hq; exact hp hq.symm
          simp [hpp, hpq]
        · simp [hpp]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [stationaryWeight_of_ne_zero hq0]
      by_cases hzero : q i = 0 ∧ q j = 0
      · rw [Finset.sum_eq_single q]
        · simp [hzero, stationaryWeight_of_ne_zero hq0]
        · intro p _ hp
          by_cases hpp : p i = 0 ∧ p j = 0
          · have hpq : ¬ (q = p) := by
              intro h; exact hp h.symm
            simp [hpp, hpq]
          · simp [hpp, hzero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hsum_eq :
            (∑ p : PauliString n, stationaryWeight n p *
              (if p i = 0 ∧ p j = 0 then (if q = p then 1 else 0)
               else if q i = 0 ∧ q j = 0 then 0
               else if (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k) then (1 / 15 : ℝ)
               else 0))
              = ∑ p : PauliString n,
                  stationaryWeight n p *
                    (if (p i = 0 ∧ p j = 0) then 0
                     else if (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k) then (1 / 15 : ℝ)
                     else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hpp : p i = 0 ∧ p j = 0
          · have hpq : ¬ (q = p) := by
              intro h
              exact hzero (h ▸ hpp)
            simp [hpp, hpq]
          · simp [hpp, hzero]
        rw [hsum_eq]

        set P : Finset (PauliString n) :=
          Finset.univ.filter (fun p => ¬ (p i = 0 ∧ p j = 0) ∧
            (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k)) with hP
        have hfilter :
            (∑ p : PauliString n,
                stationaryWeight n p *
                  (if (p i = 0 ∧ p j = 0) then 0
                   else if (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k) then (1 / 15 : ℝ)
                   else 0))
              = ∑ p ∈ P, stationaryWeight n p * (1 / 15 : ℝ) := by
          rw [hP, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p _
          by_cases hpp : p i = 0 ∧ p j = 0
          · have hc : ¬ (¬ (p i = 0 ∧ p j = 0) ∧
                (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k)) := fun h => h.1 hpp
            simp [hpp, hc]
          · by_cases hm : (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k)
            · have hc : ¬ (p i = 0 ∧ p j = 0) ∧
                  (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k) := ⟨hpp, hm⟩
              simp [hpp, hm, hc]
            · have hc : ¬ (¬ (p i = 0 ∧ p j = 0) ∧
                  (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k)) := fun h => hm h.2
              simp [hpp, hm, hc]
        rw [hfilter]

        let S : Finset (Fin 4 × Fin 4) := Finset.univ.erase (0, 0)
        have hbij : ∑ p ∈ P, stationaryWeight n p * (1 / 15 : ℝ)
            = ∑ ab ∈ S, stationaryWeight n (pairUpdate q i j ab) * (1 / 15 : ℝ) := by

          have hmem : ∀ p ∈ P, (p i, p j) ∈ S := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨_, hpnz, _⟩ := hp
            simp only [S, Finset.mem_erase, Finset.mem_univ, and_true]
            intro h
            apply hpnz
            rw [Prod.ext_iff] at h
            simpa using h
          have hinj : ∀ p1 ∈ P, ∀ p2 ∈ P, (p1 i, p1 j) = (p2 i, p2 j) → p1 = p2 := by
            intro p1 hp1 p2 hp2 h
            rw [Finset.mem_filter] at hp1 hp2
            obtain ⟨_, _, hm1⟩ := hp1
            obtain ⟨_, _, hm2⟩ := hp2
            rw [Prod.ext_iff] at h
            funext k
            by_cases hki : k = i
            · subst hki; exact h.1
            · by_cases hkj : k = j
              · subst hkj; exact h.2
              · exact (hm1 k hki hkj).symm.trans (hm2 k hki hkj)
          have hsurj : ∀ ab ∈ S, ∃ p, ∃ _ : p ∈ P, (p i, p j) = ab := by
            intro ab hab
            simp only [S, Finset.mem_erase, Finset.mem_univ, and_true] at hab
            refine ⟨pairUpdate q i j ab, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_, ?_⟩
              · intro h
                apply hab
                have h1 : ab.1 = 0 := by
                  have hh := h.1
                  rwa [pairUpdate_i q hij] at hh
                have h2 : ab.2 = 0 := by
                  have hh := h.2
                  rwa [pairUpdate_j q] at hh
                exact Prod.ext h1 h2
              · intro k hki hkj
                exact (pairUpdate_of_ne q hki hkj ab).symm
            · rw [Prod.ext_iff]
              exact ⟨pairUpdate_i q hij ab, pairUpdate_j q ab⟩
          refine Finset.sum_bij (s := P) (t := S)
            (f := fun p => stationaryWeight n p * (1 / 15 : ℝ))
            (g := fun ab => stationaryWeight n (pairUpdate q i j ab) * (1 / 15 : ℝ))
            (fun p _ => (p i, p j)) hmem hinj hsurj ?_

          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨_, _, hmatch⟩ := hp
          have huniq : pairUpdate q i j (p i, p j) = p := by
            funext k
            by_cases hki : k = i
            · subst hki; rw [pairUpdate_i q hij]
            · by_cases hkj : k = j
              · subst hkj; rw [pairUpdate_j q]
              · rw [pairUpdate_of_ne q hki hkj]
                exact hmatch k hki hkj
          change stationaryWeight n p * (1 / 15 : ℝ)
            = stationaryWeight n (pairUpdate q i j (p i, p j)) * (1 / 15 : ℝ)
          rw [huniq]
        rw [hbij]

        have hterm : ∀ ab ∈ S,
            stationaryWeight n (pairUpdate q i j ab) * (1 / 15 : ℝ)
              = pauliConst n / 15 := by
          intro ab hab
          have hab' : ab ≠ (0, 0) := by
            simp only [S, Finset.mem_erase] at hab
            exact hab.1
          rw [stationaryWeight_of_ne_zero (pairUpdate_ne_zero q hij hab')]
          ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        have hcard : S.card = 15 := by
          simp only [S]
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
          simp [Fintype.card_prod, Fintype.card_fin]
        rw [hcard]
        push_cast
        ring

  have hsum : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then stepInner n (stationaryWeight n) i j q
        else 0)
      = ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then stationaryWeight n q else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · rw [if_pos hij, if_pos hij]
      exact hpair i j hij
  rw [hsum]

  have hinner : ∀ i : Fin n,
      (∑ j : Fin n, if i ≠ j then stationaryWeight n q else 0)
        = ((n - 1 : ℕ) : ℝ) * stationaryWeight n q := by
    intro i
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter (fun j : Fin n => i ≠ j))
        = Finset.univ.erase i := by
      ext j; simp [not_not, eq_comm]
    rw [hfilter]
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 ≤ 2) hn2)
  have hnm1 : (0:ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) this)
  have hnm1ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hnm1
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have hprod : ((n * (n - 1) : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
      have hpos : (0:ℕ) < n * (n - 1) := by
        have : (0:ℕ) < n - 1 := by omega
        positivity
      exact_mod_cast hpos
    exact ne_of_gt this
  field_simp
  rw [Nat.cast_mul]

end Qatlib.Papers.AnyCircuit08.MainResults
