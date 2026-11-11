/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionDefs

/-!
# Fermionic local gates and covariance transformations

This module proves local gate-list realizations of Jordan–Wigner annihilation, creation,
number, and hopping operators, following the encoding of [JordanWigner1928]. It establishes
exact weighted gate-list encodings of quadratic and Hubbard Hamiltonian sums, bounds their
defined gate, bit, and space costs, and derives two-site block representations with the
intervening Pauli Z strings.

The Majorana operators satisfy Clifford relations, and real changes of basis transform
covariance matrices by congruence. These identities connect occupation expectations to
covariance entries and give covariance updates under unitaries whose induced Majorana
transformation is supplied as a hypothesis, as in fermionic linear optics
[Bravyi2005Fermionic]. The module also proves unitarity of match gates with skew-Hermitian
coefficients and exact evolution factorization for commuting generators.

## Main statements

* `jwLocalGateList_annihilation` and `jwCreationGateList_op`: exact local gate lists for
  annihilation and creation operators.
* `majorana_clifford`: the Majorana anticommutation relations.
* `covarianceMatrix_congruence_of_induced`: covariance congruence under an assumed induced
  real Majorana transformation.
* `occupationExpectation_eq_occupationFromCovariance`: recovery of occupation from covariance
  when the real norm trace is one.
* `quadraticHamiltonianWord_op` and `hubbardHamiltonianWord_eq_termSum`: exact Hamiltonian
  word representations.
* `quadraticGenerator_adjacent_block`: a two-site block representation for consecutive modes.
* `hamiltonianEvolution_trotter_exact_of_commute`: exact factorization for commuting generators.

## References

* [Jordan and Wigner, 1928][JordanWigner1928]
* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion

open Matrix
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

/-- The matrix entry of a gate at site `j` is the corresponding entry of `G` when the registers
agree elsewhere, and zero otherwise. -/
theorem localGate_apply {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (y x : Reg n) :
    localGate j G y x =
      (if ∀ k : Fin n, k ≠ j → y k = x k then G (boolEquivFin2 (y j)) (boolEquivFin2 (x j))
       else 0) := rfl

/-- Embedding a diagonal single-site matrix as `localGate` gives zero entries between distinct
registers. -/
theorem localGate_diagonal {n : ℕ} (j : Fin n) {G : Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ b c : Fin 2, G b c ≠ 0 → b = c) (y x : Reg n) (h : y ≠ x) :
    localGate j G y x = 0 := by
  rw [localGate_apply]
  by_cases hc : ∀ k : Fin n, k ≠ j → y k = x k
  · have hne : boolEquivFin2 (y j) ≠ boolEquivFin2 (x j) := by
      intro hh
      apply h
      funext k
      by_cases hk : k = j
      · rw [hk]
        exact boolEquivFin2.injective hh
      · exact hc k hk
    have hz : G (boolEquivFin2 (y j)) (boolEquivFin2 (x j)) = 0 := by
      by_contra hcon
      exact hne (hG _ _ hcon)
    simp [hc, hz]
  · simp [hc]

/-- A local Pauli Z gate has zero entries between distinct registers. -/
theorem localGate_oneQubitZ_diagonal {n : ℕ} (j : Fin n) (y x : Reg n) (h : y ≠ x) :
    localGate j oneQubitZ y x = 0 := by
  refine localGate_diagonal j (G := oneQubitZ) ?_ y x h
  intro b c hc
  by_cases hbc : b = c
  · exact hbc
  · simp [oneQubitZ, hbc] at hc

/-- The onsite phase gate has zero entries between distinct registers. -/
theorem onsiteLocalGate_diagonal {n : ℕ} (i : Fin n) (θ : ℝ) (y x : Reg n) (h : y ≠ x) :
    onsiteLocalGate i θ y x = 0 := by
  unfold onsiteLocalGate
  have hG : ∀ b c : Fin 2, oneQubitPhase θ b c ≠ 0 → b = c := by
    intro b c hc
    by_cases hbc : b = c
    · exact hbc
    · simp [oneQubitPhase, hbc] at hc
  exact localGate_diagonal i (G := oneQubitPhase θ) hG y x h

/-- The diagonal entry of the onsite phase gate is `exp (-I * θ)` at an occupied site and one at
an unoccupied site. -/
theorem onsiteLocalGate_apply {n : ℕ} (i : Fin n) (θ : ℝ) (x : Reg n) :
    onsiteLocalGate i θ x x = (if x i then Complex.exp (-Complex.I * θ) else 1) := by
  unfold onsiteLocalGate
  rw [localGate_apply]
  simp only [if_true]
  rw [oneQubitPhase]
  by_cases hi : x i
  · simp [hi, boolEquivFin2]
  · simp [hi, boolEquivFin2]

/-- The gate count of a local gate list equals its length. -/
theorem localGateCount_eq_length {n : ℕ} (gl : LocalGateList n) :
    localGateCount gl = gl.length := by
  induction gl with
  | nil => rfl
  | cons g rest ih =>
      rw [localGateCount, List.length_cons, ih]
      omega

/-- Concatenating local gate lists corresponds to multiplying their operators in list order. -/
theorem localGateListOp_append {n : ℕ} (l₁ l₂ : LocalGateList n) :
    localGateListOp (l₁ ++ l₂) = localGateListOp l₁ * localGateListOp l₂ := by
  induction l₁ with
  | nil => simp [localGateListOp]
  | cons p rest ih =>
      show localGate p.1 p.2 * localGateListOp (rest ++ l₂)
        = (localGate p.1 p.2 * localGateListOp rest) * localGateListOp l₂
      rw [ih, Matrix.mul_assoc]

/-- A nonzero entry of `oneQubitZ` has equal row and column indices. -/
theorem oneQubitZ_diagonal (b c : Fin 2) (h : oneQubitZ b c ≠ 0) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  · have h2 : (if b = c then (if c = 1 then -1 else 1 : ℂ) else 0) ≠ 0 := by
      simpa [oneQubitZ, Matrix.of_apply, hbc] using! h
    simp [hbc] at h2

/-- The diagonal entry of `oneQubitZ` is minus one at index one and one otherwise. -/
theorem oneQubitZ_diagEntry (b : Fin 2) :
    oneQubitZ b b = (if b = 1 then -1 else 1) := by
  simp [oneQubitZ, Matrix.of_apply]

/-- A product over `Fin n` splits into the factors below `i`, the factor at `i`, and the factors
above `i`. -/
theorem prod_split {n : ℕ} (i : Fin n) (f : Fin n → ℂ) :
    (∏ j : Fin n, f j)
      = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod f * f i
        * ((Finset.univ : Finset (Fin n)).filter (i < ·)).prod f := by
  classical
  have hmem : (Finset.univ : Finset (Fin n)).erase i
      = (Finset.univ : Finset (Fin n)).filter (· < i)
        ∪ (Finset.univ : Finset (Fin n)).filter (i < ·) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, Finset.mem_union,
      and_true, true_and]
    constructor
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro h he
      rcases h with h | h
      · exact absurd (he ▸ h) (lt_irrefl _)
      · exact absurd (he.symm ▸ h) (lt_irrefl _)
  have hdis : Disjoint ((Finset.univ : Finset (Fin n)).filter (· < i))
      ((Finset.univ : Finset (Fin n)).filter (i < ·)) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    have h1 : a < i := (Finset.mem_filter.mp ha).2
    have h2 : i < a := (Finset.mem_filter.mp hb).2
    omega
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin n)) f (Finset.mem_univ i)]
  rw [hmem, Finset.prod_union hdis]
  ring

/-- The embedding of a diagonal single-site matrix has its corresponding local entry on the
diagonal and zero elsewhere. -/
theorem localGate_diag_apply {n : ℕ} (j : Fin n) {G : Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ b c : Fin 2, G b c ≠ 0 → b = c) (y x : Reg n) :
    localGate j G y x
      = if y = x then G (boolEquivFin2 (y j)) (boolEquivFin2 (x j)) else 0 := by
  rw [localGate_apply]
  by_cases hyx : y = x
  · subst hyx
    simp
  · by_cases hc : ∀ k : Fin n, k ≠ j → y k = x k
    · have hne : boolEquivFin2 (y j) ≠ boolEquivFin2 (x j) := by
        intro hh
        apply hyx
        funext k
        by_cases hk : k = j
        · rw [hk]
          exact boolEquivFin2.injective hh
        · exact hc k hk
      have hz : G (boolEquivFin2 (y j)) (boolEquivFin2 (x j)) = 0 := by
        by_contra hcon
        exact hne (hG _ _ hcon)
      rw [if_pos hc, hz]
      simp [hyx]
    · rw [if_neg hc]
      simp [hyx]

/-- A list of diagonal local gates gives a diagonal operator whose diagonal entries are products
of the local diagonal entries. -/
theorem localGateListOp_diag {n : ℕ} :
    ∀ (gl : LocalGateList n),
      (∀ p ∈ gl, ∀ b c : Fin 2, p.2 b c ≠ 0 → b = c) →
      ∀ (y x : Reg n),
        localGateListOp gl y x
          = if y = x then (gl.map (fun p => localGateDiagEntry p y)).prod else 0 := by
  intro gl
  induction gl with
  | nil =>
      intro _ y x
      simp [localGateListOp, Matrix.one_apply]
  | cons p rest ih =>
      intro hG y x
      have hGp : ∀ b c : Fin 2, p.2 b c ≠ 0 → b = c :=
        fun b c hbc => hG p (by simp) b c hbc
      have hGr : ∀ q ∈ rest, ∀ b c : Fin 2, q.2 b c ≠ 0 → b = c := by
        intro q hq b c hbc
        exact hG q (by simp [hq]) b c hbc
      have hA : ∀ z, localGate p.1 p.2 y z
          = if y = z then localGateDiagEntry p y else 0 := by
        intro z
        rw [localGate_diag_apply p.1 hGp y z]
        by_cases h : y = z
        · rw [if_pos h]
          simp [h, localGateDiagEntry]
        · rw [if_neg h]
          simp [h]
      have hB : ∀ z, localGateListOp rest y z
          = if y = z then (rest.map (fun q => localGateDiagEntry q y)).prod else 0 :=
        fun z => ih hGr y z
      rw [localGateListOp, Matrix.mul_apply]
      by_cases hyx : y = x
      · subst hyx
        rw [Finset.sum_eq_single y]
        · rw [hA y, hB y]
          simp [List.map_cons, List.prod_cons]
        · intro z _ hzy
          rw [hA z, if_neg hzy.symm, zero_mul]
        · intro h
          exact absurd h (by simp)
      · have hsum : (∑ j, localGate p.1 p.2 y j * localGateListOp rest j x) = 0 := by
          apply Finset.sum_eq_zero
          intro z _
          by_cases hzy : z = y
          · subst hzy
            rw [hB x, if_neg hyx]
            ring
          · rw [hA z, if_neg (fun h => hzy h.symm), zero_mul]
        rw [hsum]
        simp [hyx]

/-- Left multiplication by a diagonal matrix multiplies each entry by the diagonal entry in its
row. -/
theorem mul_apply_diag_left {n : ℕ} (P : Matrix (Reg n) (Reg n) ℂ) (B : Matrix (Reg n) (Reg n) ℂ)
    (hP : ∀ y x : Reg n, y ≠ x → P y x = 0) (y x : Reg n) :
    (P * B) y x = P y y * B y x := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single y ?_ ?_
  · intro z _ hzy
    rw [hP y z hzy.symm, zero_mul]
  · intro h
    exact absurd h (by simp)

/-- The local gate list for mode `i` represents its Jordan–Wigner Pauli word [JordanWigner1928]. -/
theorem jwLocalGateList_op {n : ℕ} (i : Fin n) :
    localGateListOp (jwLocalGateList i) = jwPauliWord i := by
  classical
  apply Matrix.ext
  intro y x
  have hZdiag : ∀ (j : Fin n) (y : Reg n),
      localGateDiagEntry (j, oneQubitZ) y = (if y j then -1 else 1) := by
    intro j y
    show oneQubitZ (boolEquivFin2 (y j)) (boolEquivFin2 (y j)) = (if y j then -1 else 1)
    by_cases hy : y j
    · have hb : boolEquivFin2 (y j) = 1 := by simp [boolEquivFin2, hy]
      rw [oneQubitZ_diagEntry, hb]
      simp [hy]
    · have hb : boolEquivFin2 (y j) = 0 := by simp [boolEquivFin2, hy]
      rw [oneQubitZ_diagEntry, hb]
      simp [hy]
  have hprefix_diag : ∀ (y' x' : Reg n), y' ≠ x' →
      localGateListOp (jwZPrefix i) y' x' = 0 := by
    intro y' x' hne
    have h := localGateListOp_diag (jwZPrefix i)
      (fun p hp b c hbc =>
        oneQubitZ_diagonal b c (by rw [jwZPrefix_mem i hp] at hbc; exact hbc)) y' x'
    rw [if_neg hne] at h
    exact h
  have hprefix_entry : ∀ (y : Reg n),
      localGateListOp (jwZPrefix i) y y
        = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1)) := by
    intro y
    have h := localGateListOp_diag (jwZPrefix i)
      (fun p hp b c hbc =>
        oneQubitZ_diagonal b c (by rw [jwZPrefix_mem i hp] at hbc; exact hbc)) y y
    rw [if_pos rfl] at h
    rw [h, jwZPrefix, List.map_map, Finset.prod_map_toList]
    apply Finset.prod_congr rfl
    intro j hj
    exact hZdiag j y
  have hsplit : localGateListOp (jwLocalGateList i)
      = localGateListOp (jwZPrefix i) * localGate i sigmaMinus := by
    rw [jwLocalGateList, localGateListOp_append]
    have hsingle : localGateListOp [(i, sigmaMinus)] = localGate i sigmaMinus := by
      simp [localGateListOp]
    rw [hsingle]
  have hR : jwPauliWord i y x
      = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (jwSiteFactor i · y x)
        * jwSiteFactor i i y x
        * ((Finset.univ : Finset (Fin n)).filter (i < ·)).prod (jwSiteFactor i · y x) := by
    rw [jwPauliWord_eq_siteFactors, prod_split]
  by_cases hloc : ∀ k : Fin n, k ≠ i → y k = x k
  · have hM : localGate i sigmaMinus y x
        = sigmaMinus (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by
      rw [localGate_apply, if_pos hloc]
    have hMid : jwSiteFactor i i y x
        = sigmaMinus (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by
      simp [jwSiteFactor]
    have hpre : ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (jwSiteFactor i · y x)
        = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjlt : j < i := (Finset.mem_filter.mp hj).2
      have hji : j ≠ i := by omega
      have hyj : y j = x j := hloc j hji
      rw [jwSiteFactor, if_pos hjlt, if_pos hyj, hyj]
    have hsu : ((Finset.univ : Finset (Fin n)).filter (i < ·)).prod (jwSiteFactor i · y x) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hjgt : i < j := (Finset.mem_filter.mp hj).2
      have hji : j ≠ i := by omega
      have hyj : y j = x j := hloc j hji
      rw [jwSiteFactor, if_neg (by omega : ¬ (j < i)), if_pos hjgt, if_pos hyj]
    have hLHS : localGateListOp (jwLocalGateList i) y x
        = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1))
          * sigmaMinus (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by
      calc localGateListOp (jwLocalGateList i) y x
          = (localGateListOp (jwZPrefix i) * localGate i sigmaMinus) y x := by rw [hsplit]
        _ = localGateListOp (jwZPrefix i) y y * (localGate i sigmaMinus) y x :=
            mul_apply_diag_left _ _ hprefix_diag y x
        _ = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod
                (fun j => (if y j then -1 else 1))
            * (localGate i sigmaMinus) y x := by rw [hprefix_entry]
        _ = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod
                (fun j => (if y j then -1 else 1))
            * sigmaMinus (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by rw [hM]
    have hRHS : jwPauliWord i y x
        = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1))
          * sigmaMinus (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by
      calc jwPauliWord i y x
          = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (jwSiteFactor i · y x)
            * jwSiteFactor i i y x
            * ((Finset.univ : Finset (Fin n)).filter (i < ·)).prod (jwSiteFactor i · y x) := hR
        _ = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1))
            * jwSiteFactor i i y x * 1 := by rw [hpre, hsu]
        _ = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1))
            * sigmaMinus (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by rw [hMid, mul_one]
    rw [hLHS, hRHS]
  · obtain ⟨k, hki, hky⟩ : ∃ k : Fin n, k ≠ i ∧ y k ≠ x k := by
      rw [not_forall] at hloc
      obtain ⟨k, hk⟩ := hloc
      rw [Classical.not_imp] at hk
      exact ⟨k, hk.1, fun h => hk.2 h⟩
    have hne : ¬ (∀ k' : Fin n, k' ≠ i → y k' = x k') := by
      intro hc'
      exact hky (hc' k hki)
    have hM0 : localGate i sigmaMinus y x = 0 := by
      rw [localGate_apply, if_neg hne]
    have hLHS0 : localGateListOp (jwLocalGateList i) y x = 0 := by
      rw [hsplit, mul_apply_diag_left _ _ hprefix_diag y x, hprefix_entry, hM0]
      ring
    have hRHS0 : jwPauliWord i y x = 0 := by
      by_cases hki_lt : k < i
      · have hpre0 : ((Finset.univ : Finset (Fin n)).filter (· < i)).prod
            (jwSiteFactor i · y x) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki_lt⟩)
          rw [jwSiteFactor, if_pos hki_lt, if_neg hky]
        rw [hR, hpre0]
        ring
      · have hki_gt : i < k := by omega
        have hsu0 : ((Finset.univ : Finset (Fin n)).filter (i < ·)).prod
            (jwSiteFactor i · y x) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki_gt⟩)
          rw [jwSiteFactor, if_neg hki_lt, if_pos hki_gt, if_neg hky]
        rw [hR, hsu0]
        ring
    rw [hLHS0, hRHS0]

/-- The Jordan–Wigner local gate list represents the annihilation operator at mode `i`
[JordanWigner1928]. -/
theorem jwLocalGateList_annihilation {n : ℕ} (i : Fin n) :
    localGateListOp (jwLocalGateList i) = annihilation i := by
  rw [jwLocalGateList_op]
  exact ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2.1 i).1.symm

/-- The difference between the Jordan–Wigner gate-list operator and its Pauli word vanishes
entrywise. -/
theorem jwLocalGateList_error {n : ℕ} (i : Fin n) :
    ∀ (y x : Reg n), (localGateListOp (jwLocalGateList i) - jwPauliWord i) y x = 0 := by
  intro y x
  rw [jwLocalGateList_op, sub_self, Matrix.zero_apply]

/-- There are `i.val` indices in `Fin n` strictly below `i`. -/
theorem card_filter_lt {n : ℕ} (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (· < i)).card = i.val := by
  classical
  have h : ((Finset.univ : Finset (Fin n)).filter (· < i)).card
      = (Finset.range i.val).card := by
    apply Finset.card_bij (s := (Finset.univ : Finset (Fin n)).filter (· < i))
      (t := Finset.range i.val) (fun a _ => a.val)
    · intro a ha
      rw [Finset.mem_range]
      have hlt : a.val < i.val := (Fin.lt_def.mp (Finset.mem_filter.mp ha).2)
      omega
    · intro a₁ ha₁ a₂ ha₂ h
      exact Fin.val_injective h
    · intro b hb
      rw [Finset.mem_range] at hb
      refine ⟨⟨b, by omega⟩, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Fin.lt_def]
      omega
  simpa [Finset.card_range] using! h

/-- The gate count is additive under concatenation of local gate lists. -/
theorem localGateCount_append {n : ℕ} (l₁ l₂ : LocalGateList n) :
    localGateCount (l₁ ++ l₂) = localGateCount l₁ + localGateCount l₂ := by
  induction l₁ with
  | nil => simp [localGateCount]
  | cons p rest ih => simp [localGateCount, ih, Nat.succ_add]

/-- The Jordan–Wigner gate list for mode `i` contains `i.val + 1` local gates. -/
theorem jwLocalGateList_count {n : ℕ} (i : Fin n) :
    localGateCount (jwLocalGateList i) = i.val + 1 := by
  rw [localGateCount_eq_length, jwLocalGateList, jwZPrefix, List.length_append,
    List.length_map, Finset.length_toList, card_filter_lt]
  rfl

/-- Majorana indices associated with distinct modes are distinct, regardless of their
within-mode indices. -/
theorem majoranaIndices_ne_mode {n : ℕ} (i j : Fin n) (hij : i ≠ j) (b c : Fin 2) :
    majoranaIndices i b ≠ majoranaIndices j c := by
  intro h
  exact hij ((majoranaIndices_eq i j b c).mp h).1

/-- For distinct modes, `localSlot` recovers the slot used by `localIndices`. -/
theorem localSlot_localIndices {n : ℕ} (i j : Fin n) (hij : i ≠ j) (p : Fin 4) :
    localSlot i j (localIndices i j p) = p := by
  rcases p with ⟨k, hk⟩
  interval_cases k
  · simp [localIndices, localSlot]
  · have h1 : majoranaIndices i 1 ≠ majoranaIndices i 0 := majoranaIndices_ne i 1 0 (by decide)
    have h2 : majoranaIndices i 1 ≠ majoranaIndices j 0 := majoranaIndices_ne_mode i j hij 1 0
    simp [localIndices, localSlot, h1, h2]
  · have h1 : majoranaIndices j 0 ≠ majoranaIndices i 0 :=
        (majoranaIndices_ne_mode i j hij 0 0).symm
    simp [localIndices, localSlot, h1]
  · have h1 : majoranaIndices j 1 ≠ majoranaIndices i 0 :=
        majoranaIndices_ne_mode j i (Ne.symm hij) 1 0
    have h2 : majoranaIndices j 1 ≠ majoranaIndices j 0 := majoranaIndices_ne j 1 0 (by decide)
    have h3 : majoranaIndices j 1 ≠ majoranaIndices i 1 :=
        majoranaIndices_ne_mode j i (Ne.symm hij) 1 1
    simp [localIndices, localSlot, h1, h2, h3]

/-- Every index selected by `localIndices i j` is a local Majorana index for these modes. -/
theorem isLocalMajorana_localIndices {n : ℕ} (i j : Fin n) (p : Fin 4) :
    isLocalMajorana i j (localIndices i j p) := by
  rcases p with ⟨k, hk⟩
  interval_cases k <;> simp [isLocalMajorana, localIndices]

/-- For distinct modes, the local block of a covariance update is `R * localBlock Γ i j *
R.transpose`. -/
theorem localBlock_covarianceUpdate {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (hij : i ≠ j) :
    localBlock (covarianceUpdate Γ i j R) i j = R * localBlock Γ i j * R.transpose := by
  ext p q
  unfold covarianceUpdate
  simp only [localBlock, Matrix.of_apply]
  rw [if_pos ⟨isLocalMajorana_localIndices i j p, isLocalMajorana_localIndices i j q⟩]
  rw [localSlot_localIndices i j hij p, localSlot_localIndices i j hij q]

/-- The ring connectivity list has length `n` when `n` is positive. -/
theorem length_ringConnectivity {n : ℕ} (h : 0 < n) : (ringConnectivity n).length = n := by
  have h1 : 1 ≤ n := by omega
  simp [ringConnectivity, h, length_linearConnectivity, Nat.sub_add_cancel h1]

/-- A nonzero annihilation matrix entry connects registers that agree away from the annihilated
mode. -/
theorem annihilation_support {n : ℕ} (j : Fin n) (z x : Reg n) (h : annihilation j z x ≠ 0) :
    ∀ k : Fin n, k ≠ j → z k = x k := by
  have hcond : x j ∧ z = Function.update x j false := by
    by_contra hc
    have hz : annihilation j z x = 0 := by
      rw [annihilation, Matrix.of_apply, if_neg hc]
    rw [hz] at h
    exact h rfl
  intro k hk
  simp [hcond.2, hk]

/-- A nonzero creation matrix entry connects registers that agree away from the created mode. -/
theorem creation_support {n : ℕ} (i : Fin n) (y z : Reg n) (h : creation i y z ≠ 0) :
    ∀ k : Fin n, k ≠ i → y k = z k := by
  have hcond : ¬ z i ∧ y = Function.update z i true := by
    by_contra hc
    have hz : creation i y z = 0 := by
      rw [creation, Matrix.of_apply, if_neg hc]
    rw [hz] at h
    exact h rfl
  intro k hk
  simp [hcond.2, hk]

/-- The symmetric hopping operator has zero entries between registers differing at a site
outside its two modes. -/
theorem hoppingTerm_preservesOutside {n : ℕ} (i j : Fin n) (k : Fin n)
    (hk : k ≠ i) (hk' : k ≠ j) (y x : Reg n) (hne : y k ≠ x k) :
    (creation i * annihilation j + creation j * annihilation i) y x = 0 := by
  have h1 : (creation i * annihilation j) y x = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hcz : creation i y z = 0
    · rw [hcz, zero_mul]
    · by_cases haz : annihilation j z x = 0
      · rw [haz, mul_zero]
      · have hzy : y k = z k := creation_support i y z hcz k hk
        have hzx : z k = x k := annihilation_support j z x haz k hk'
        exact absurd (hzy.trans hzx) hne
  have h2 : (creation j * annihilation i) y x = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hcz : creation j y z = 0
    · rw [hcz, zero_mul]
    · by_cases haz : annihilation i z x = 0
      · rw [haz, mul_zero]
      · have hzy : y k = z k := creation_support j y z hcz k hk'
        have hzx : z k = x k := annihilation_support i z x haz k hk
        exact absurd (hzy.trans hzx) hne
  rw [Matrix.add_apply, h1, h2, add_zero]

/-- If `T` preserves all register bits outside `i` and `j`, its Hamiltonian evolution preserves
those bits as well. -/
theorem hamiltonianEvolution_actsOnlyOn {n : ℕ} (i j : Fin n) (T : Matrix (Reg n) (Reg n) ℂ)
    (hT : ∀ k : Fin n, k ≠ i → k ≠ j → ∀ y x : Reg n, y k ≠ x k → T y x = 0) (s : ℝ) :
    ∀ y x : Reg n, (∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k) →
      (HamiltonianEvolution T s) y x = 0 := by
  intro y x hex
  obtain ⟨k, hk, hk', hne⟩ := hex
  set b : Reg n → ℤ := fun x => if x k then 1 else 0 with hb
  have hby : b y ≠ b x := by
    by_cases hy : y k
    · by_cases hx : x k
      · exact absurd hne (by simp [hy, hx])
      · simp [hb, hy, hx]
    · by_cases hx : x k
      · simp [hb, hy, hx]
      · exact absurd hne (by simp [hy, hx])
  have htri : BlockTriangular T b := by
    intro y' x' hyx
    by_cases hyk : y' k
    · by_cases hxk : x' k
      · exfalso
        exact absurd hyx (by simp [hb, hyk, hxk])
      · exact hT k hk hk' y' x' (by simp [hyk, hxk])
    · by_cases hxk : x' k
      · exfalso
        exact absurd hyx (by simp [hb, hyk, hxk])
      · exfalso
        exact absurd hyx (by simp [hb, hyk, hxk])
  have htri' : BlockTriangular T (-b) := by
    intro y' x' hyx
    by_cases hyk : y' k
    · by_cases hxk : x' k
      · exfalso
        exact absurd hyx (by simp [hb, hyk, hxk])
      · exfalso
        exact absurd hyx (by simp [hb, hyk, hxk])
    · by_cases hxk : x' k
      · exact hT k hk hk' y' x' (by simp [hyk, hxk])
      · exfalso
        exact absurd hyx (by simp [hb, hyk, hxk])
  have htriS : BlockTriangular ((-Complex.I * (s : ℂ)) • T) b := by
    intro y' x' hyx
    rw [Matrix.smul_apply, htri hyx]
    simp only [smul_zero]
  have htriS' : BlockTriangular ((-Complex.I * (s : ℂ)) • T) (-b) := by
    intro y' x' hyx
    rw [Matrix.smul_apply, htri' hyx]
    simp only [smul_zero]
  have hb1 : BlockTriangular (NormedSpace.exp ((-Complex.I * (s : ℂ)) • T)) b :=
    BlockTriangular.exp htriS
  have hb2 : BlockTriangular (NormedSpace.exp ((-Complex.I * (s : ℂ)) • T)) (-b) :=
    BlockTriangular.exp htriS'
  have hkey : NormedSpace.exp ((-Complex.I * (s : ℂ)) • T) x y = 0 := by
    by_cases hlt : b y < b x
    · exact hb1 hlt
    · have hgt : b x < b y := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hby)
      exact hb2 (neg_lt_neg hgt)
  have hkey' : NormedSpace.exp ((-Complex.I * (s : ℂ)) • T) y x = 0 := by
    by_cases hlt : b x < b y
    · exact hb1 hlt
    · have hgt : b y < b x := lt_of_le_of_ne (le_of_not_gt hlt) hby
      exact hb2 (neg_lt_neg hgt)
  change NormedSpace.exp ((-Complex.I * (s : ℂ)) • T) y x = 0
  exact hkey'

/-- Hamiltonian evolution of the symmetric hopping operator preserves register bits outside its
two modes. -/
theorem hamiltonianEvolution_hoppingTerm_actsOnlyOn {n : ℕ} (i j : Fin n) (s : ℝ) :
    ∀ y x : Reg n, (∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k) →
      (HamiltonianEvolution
        (creation i * annihilation j + creation j * annihilation i) s) y x = 0 := by
  intro y x hex
  refine hamiltonianEvolution_actsOnlyOn i j _ ?_ s y x hex
  intro k hk hk' y x hne
  exact hoppingTerm_preservesOutside i j k hk hk' y x hne

/-- Creation at a mode is the conjugate transpose of annihilation at that mode. -/
theorem creation_eq_annihilation_conjTranspose {n : ℕ} (k : Fin n) :
    creation k = (annihilation k)ᴴ := (Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.1 k

/-- Annihilation at a mode is the conjugate transpose of creation at that mode. -/
theorem annihilation_eq_creation_conjTranspose {n : ℕ} (k : Fin n) :
    annihilation k = (creation k)ᴴ := by
  have h1 := ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2.1 k).1
  have h2 := ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2.1 k).2
  calc annihilation k = jwPauliWord k := h1
    _ = ((jwPauliWord k)ᴴ)ᴴ := by rw [Matrix.conjTranspose_conjTranspose]
    _ = (creation k)ᴴ := by rw [h2]

/-- The number operator is Hermitian. -/
theorem numberOp_hermitian {n : ℕ} (i : Fin n) : (numberOp i)ᴴ = numberOp i := by
  have hnum : numberOp i = (annihilation i)ᴴ * annihilation i := by
    calc numberOp i = creation i * annihilation i := ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.1 i).1
      _ = (annihilation i)ᴴ * annihilation i := by
          rw [creation_eq_annihilation_conjTranspose]
  rw [hnum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Taking the conjugate transpose of a hopping monomial reverses its creation and annihilation
modes. -/
theorem creation_mul_annihilation_conjTranspose {n : ℕ} (i j : Fin n) :
    (creation i * annihilation j)ᴴ = creation j * annihilation i := by
  rw [Matrix.conjTranspose_mul]
  have e1 : (annihilation j)ᴴ = creation j :=
    (creation_eq_annihilation_conjTranspose j).symm
  have e2 : (creation i)ᴴ = annihilation i := (annihilation_eq_creation_conjTranspose i).symm
  rw [e1, e2]

/-- The conjugate transpose of a quadratic generator conjugates its coefficients and reverses
its hopping monomials. -/
theorem quadraticGenerator_conjTranspose {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (quadraticGenerator i j A)ᴴ
      = (star (A 0 0)) • (numberOp i)
        + (star (A 0 1)) • (creation j * annihilation i)
        + (star (A 1 0)) • (creation i * annihilation j)
        + (star (A 1 1)) • (numberOp j) := by
  have hnum : ∀ k : Fin n, creation k * annihilation k = numberOp k := by
    intro k
    exact ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.1 k).1.symm
  rw [quadraticGenerator]
  simp only [hnum]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  rw [numberOp_hermitian i, numberOp_hermitian j,
    creation_mul_annihilation_conjTranspose i j,
    creation_mul_annihilation_conjTranspose j i]

/-- A skew-Hermitian coefficient matrix gives a skew-Hermitian quadratic generator. -/
theorem quadraticGenerator_skewHermitian {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    (quadraticGenerator i j A)ᴴ = -quadraticGenerator i j A := by
  have h00 : star (A 0 0) = -(A 0 0) := by
    have h := congrArg (fun M => M 0 0) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h11 : star (A 1 1) = -(A 1 1) := by
    have h := congrArg (fun M => M 1 1) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h01 : star (A 0 1) = -(A 1 0) := by
    have h := congrArg (fun M => M 1 0) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h10 : star (A 1 0) = -(A 0 1) := by
    have h := congrArg (fun M => M 0 1) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have hnum : ∀ k : Fin n, creation k * annihilation k = numberOp k := by
    intro k
    exact ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.1 k).1.symm
  rw [quadraticGenerator_conjTranspose, quadraticGenerator]
  simp only [hnum]
  rw [h00, h01, h10, h11]
  simp only [neg_smul]
  abel

/-- The match gate generated by a skew-Hermitian coefficient matrix is unitary. -/
theorem matchGate_unitary {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Aᴴ = -A) : matchGate i j A ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [matchGate]
  exact exp_unitary_of_skewHermitian (quadraticGenerator_skewHermitian i j A hA)

/-- A covariance matrix entry is minus one half of the imaginary part of the trace of the
sandwiched Majorana commutator. -/
theorem covarianceMatrix_eq_im {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (a b : Fin (2 * n)) :
    covarianceMatrix M a b
      = -(1 / 2 : ℝ) * (Matrix.trace
          (Mᴴ * (majorana a * majorana b - majorana b * majorana a) * M)).im := by
  simp only [covarianceMatrix, Matrix.of_apply]
  rw [Complex.mul_re]
  simp [Complex.I_re, Complex.I_im]

/-- Interchanging the two indices of the covariance matrix negates its entry. -/
theorem covarianceMatrix_antisymm {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (a b : Fin (2 * n)) :
    covarianceMatrix M b a = -covarianceMatrix M a b := by
  rw [covarianceMatrix_eq_im, covarianceMatrix_eq_im]
  have hneg : majorana b * majorana a - majorana a * majorana b
      = -(majorana a * majorana b - majorana b * majorana a) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, add_comm, neg_add]
    abel
  rw [hneg, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_im]
  ring

/-- Every two-mode local block of a covariance matrix is antisymmetric. -/
theorem localBlock_covariance_antisymm {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n)
    (p q : Fin 4) :
    localBlock (covarianceMatrix M) i j q p = -localBlock (covarianceMatrix M) i j p q := by
  simp only [localBlock, Matrix.of_apply]
  exact covarianceMatrix_antisymm M (localIndices i j p) (localIndices i j q)

/-- The trace of a finite sum of matrices equals the sum of their traces. -/
lemma trace_sum {ι : Type*} [Fintype ι] {m : Type*} [Fintype m]
    (g : ι → Matrix m m ℂ) :
    (∑ x, g x).trace = ∑ x, (g x).trace := by
  rw [Matrix.trace_sum]

/-- The trace of a matrix sandwich distributes over addition in the middle factor. -/
lemma trace_sandwich_add {m : Type*} [Fintype m] (A B X Y : Matrix m m ℂ) :
    (A * (X + Y) * B).trace = (A * X * B).trace + (A * Y * B).trace := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

/-- A complex scalar multiplying the middle factor of a matrix sandwich factors out of its
trace. -/
lemma trace_sandwich_smul {m : Type*} [Fintype m] (A B : Matrix m m ℂ) (r : ℂ)
    (X : Matrix m m ℂ) :
    (A * (r • X) * B).trace = r * (A * X * B).trace := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  rfl

/-- The trace of a matrix sandwich distributes over a finite sum in the middle factor. -/
lemma trace_sandwich_finset {ι : Type*} [Fintype ι] {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : ι → Matrix m m ℂ) :
    (A * (∑ x, f x) * B).trace = ∑ x, (A * f x * B).trace := by
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]

/-- The trace of a matrix sandwich distributes over subtraction in the middle factor. -/
lemma trace_sandwich_sub {m : Type*} [Fintype m] (A B X Y : Matrix m m ℂ) :
    (A * (X - Y) * B).trace = (A * X * B).trace - (A * Y * B).trace := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]

/-- An identity matrix in the middle of a trace sandwich can be removed. -/
lemma trace_sandwich_one {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) :
    (A * (1 : Matrix m m ℂ) * B).trace = (A * B).trace := by
  rw [Matrix.mul_one]

/-- The trace of a sandwiched finite linear combination equals the corresponding linear
combination of sandwich traces. -/
lemma trace_sandwich_smul_sum {ι : Type*} [Fintype ι] {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (k : ι → ℂ) (Z : ι → Matrix m m ℂ) :
    (A * (∑ x, k x • Z x) * B).trace = ∑ x, (k x) * (A * Z x * B).trace := by
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  rfl

/-- The trace of a sandwiched double linear combination equals the double sum of its weighted
sandwich traces. -/
lemma trace_sandwich_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] {m : Type*}
    [Fintype m] (A B : Matrix m m ℂ) (k : ι → κ → ℂ)
    (Z : ι → κ → Matrix m m ℂ) :
    (A * (∑ c, ∑ d, k c d • Z c d) * B).trace
      = ∑ c, ∑ d, (k c d) * (A * Z c d * B).trace := by
  rw [trace_sandwich_finset]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [trace_sandwich_smul_sum]

/-- The product of two finite matrix linear combinations expands as the double sum of pairwise
products with multiplied coefficients. -/
lemma sum_mul_sum {ι : Type*} [Fintype ι] {m n p : Type*} [Fintype n] [Fintype p]
    (u : ι → ℂ) (f : ι → Matrix m n ℂ) (v : ι → ℂ) (g : ι → Matrix n p ℂ) :
    (∑ c, u c • f c) * (∑ d, v d • g d) = ∑ c, ∑ d, (u c * v d) • (f c * g d) := by
  rw [Matrix.sum_mul Finset.univ]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [Matrix.mul_sum Finset.univ]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

/-- The difference of the two weighted double sums equals the weighted sum of `T c d - T d c`. -/
lemma sum_congruence {ι : Type*} [Fintype ι] (k l : ι → ℂ) (T : ι → ι → ℂ) :
    (∑ c, ∑ d, (k c * l d) * T c d) - (∑ c, ∑ d, (l c * k d) * T c d)
      = ∑ c, ∑ d, (k c * l d) * (T c d - T d c) := by
  have h : (∑ c, ∑ d, (l c * k d) * T c d) = (∑ c, ∑ d, (k c * l d) * T d c) := by
    calc
      (∑ c, ∑ d, (l c * k d) * T c d)
          = ∑ d, ∑ c, (l c * k d) * T c d := Finset.sum_comm
      _ = ∑ d, ∑ c, (k d * l c) * T c d := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        refine Finset.sum_congr rfl ?_
        intro c hc
        ring
      _ = ∑ c, ∑ d, (k c * l d) * T d c := rfl
  have h2 : (∑ c, ∑ d, (k c * l d) * T c d) - (∑ c, ∑ d, (k c * l d) * T d c)
      = ∑ c, ∑ d, ((k c * l d) * T c d - (k c * l d) * T d c) := by
    have houter : (∑ c, ∑ d, (k c * l d) * T c d) - (∑ c, ∑ d, (k c * l d) * T d c)
        = ∑ c, ((∑ d, (k c * l d) * T c d) - (∑ d, (k c * l d) * T d c)) := by
      rw [← Finset.sum_sub_distrib]
    rw [houter]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [← Finset.sum_sub_distrib]
  rw [h, h2]
  refine Finset.sum_congr rfl ?_
  intro c hc
  refine Finset.sum_congr rfl ?_
  intro d hd
  ring

/-- The imaginary part of a finite complex sum equals the sum of the imaginary parts. -/
lemma im_univ_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) :
    (∑ x, f x).im = ∑ x, (f x).im := by
  have aux : ∀ s : Finset ι, (∑ x ∈ s, f x).im = ∑ x ∈ s, (f x).im := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Complex.add_im, ih, Finset.sum_insert ha]
  simpa using! aux Finset.univ

/-- Two real factors can be pulled outside the imaginary part of their product with a complex
number. -/
lemma im_real_prod {x y : ℝ} {z : ℂ} :
    (((x : ℂ) * (y : ℂ) * z).im) = x * y * z.im := by
  rw [mul_assoc, Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.ofReal_re,
    Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.ofReal_re]
  ring

/-- The complex covariance pairing expands bilinearly over finite complex linear combinations. -/
theorem covarianceComplexOf_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (M : Matrix (Reg n) (Reg n) ℂ) (u v : ι → ℂ) (f : ι → Matrix (Reg n) (Reg n) ℂ) :
    covarianceComplexOf M (∑ c, u c • f c) (∑ d, v d • f d)
      = ∑ c, ∑ d, (u c * v d) * covarianceComplexOf M (f c) (f d) := by
  unfold covarianceComplexOf
  have e1 : (∑ c, u c • f c) * (∑ d, v d • f d)
      = ∑ c, ∑ d, (u c * v d) • (f c * f d) := sum_mul_sum u f v f
  have e2 : (∑ d, v d • f d) * (∑ c, u c • f c)
      = ∑ d, ∑ c, (v d * u c) • (f d * f c) := sum_mul_sum v f u f
  have t1 : ((Mᴴ * (∑ c, ∑ d, (u c * v d) • (f c * f d))) * M).trace
      = ∑ c, ∑ d, (u c * v d) * (Mᴴ * (f c * f d) * M).trace :=
    trace_sandwich_sum_sum Mᴴ M (fun c d => u c * v d) (fun c d => f c * f d)
  have t2' : ((Mᴴ * (∑ d, ∑ c, (v d * u c) • (f d * f c))) * M).trace
      = ∑ d, ∑ c, (v d * u c) * (Mᴴ * (f d * f c) * M).trace :=
    trace_sandwich_sum_sum Mᴴ M (fun d c => v d * u c) (fun d c => f d * f c)
  have t2 : ((Mᴴ * (∑ d, ∑ c, (v d * u c) • (f d * f c))) * M).trace
      = ∑ c, ∑ d, (v c * u d) * (Mᴴ * (f c * f d) * M).trace := t2'
  have hsum := sum_congruence u v (fun c d => (Mᴴ * (f c * f d) * M).trace)
  rw [e1, e2, t1, t2]
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro c hc
  refine Finset.sum_congr rfl ?_
  intro d hd
  rfl

/-- The real covariance pairing expands bilinearly over finite real linear combinations. -/
theorem covarianceOf_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : Matrix (Reg n) (Reg n) ℂ) (u v : ι → ℝ) (f : ι → Matrix (Reg n) (Reg n) ℂ) :
    covarianceOf M (∑ c, (u c : ℂ) • f c) (∑ d, (v d : ℂ) • f d)
      = ∑ c, ∑ d, (u c) * ((v d) * covarianceOf M (f c) (f d)) := by
  unfold covarianceOf
  have hcomplex := covarianceComplexOf_sum M (fun c => (u c : ℂ)) (fun d => (v d : ℂ)) f
  rw [hcomplex]
  have him : (∑ c, ∑ d, ((u c : ℂ) * (v d : ℂ)) * covarianceComplexOf M (f c) (f d)).im
      = ∑ c, ∑ d, (u c) * ((v d) * (covarianceComplexOf M (f c) (f d)).im) := by
    have h1 :=
        im_univ_sum (fun c => ∑ d, ((u c : ℂ) * (v d : ℂ)) * covarianceComplexOf M (f c) (f d))
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro c hc
    have h2 := im_univ_sum (fun d => ((u c : ℂ) * (v d : ℂ)) * covarianceComplexOf M (f c) (f d))
    rw [h2]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [im_real_prod]
    ring
  rw [him]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  ring

/-- A covariance matrix entry equals the covariance pairing of the corresponding Majorana
operators. -/
theorem covarianceMatrix_eq_covarianceOf {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (a b : Fin (2 * n)) :
    covarianceMatrix M a b = covarianceOf M (majorana a) (majorana b) := by
  rw [covarianceMatrix_eq_im, covarianceOf, covarianceComplexOf]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_im]

/-- An entry of `R * Λ * R.transpose` is the double sum of entries of `Λ` weighted by the
corresponding rows of `R`. -/
lemma mul_congruence_apply {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (Λ : Matrix (Fin m) (Fin m) ℝ) (p q : Fin m) :
    (R * Λ * R.transpose) p q = ∑ s, ∑ t, (R p s) * ((R q t) * Λ s t) := by
  calc
    (R * Λ * R.transpose) p q
        = ∑ d, (R * Λ) p d * R.transpose d q := Matrix.mul_apply ..
    _ = ∑ d, (∑ c, R p c * Λ c d) * R q d := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ d, ∑ c, R p c * (Λ c d * R q d) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro c hc
        ring
    _ = ∑ c, ∑ d, R p c * (Λ c d * R q d) := Finset.sum_comm
    _ = ∑ c, ∑ d, (R p c) * ((R q d) * Λ c d) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        refine Finset.sum_congr rfl ?_
        intro d hd
        ring

/-- Changing the Majorana basis by `S` transforms the covariance matrix to `S * covarianceMatrix
M * S.transpose`. -/
theorem covarianceInBasis_eq_congruence {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    covarianceInBasis M S = S * covarianceMatrix M * S.transpose := by
  ext a b
  simp only [covarianceInBasis, Matrix.of_apply]
  unfold majoranaInBasis
  have hl := covarianceOf_sum M (fun c => S a c) (fun d => S b d) (fun c => majorana c)
  rw [hl]
  rw [mul_congruence_apply S (covarianceMatrix M) a b]
  refine Finset.sum_congr rfl ?_
  intro c hc
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [covarianceMatrix_eq_covarianceOf]

/-- The covariance in a transformed local basis is the congruence of the original local
covariance block by `R`. -/
theorem localCovarianceInBasis_eq {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n)
    (R : Matrix (Fin 4) (Fin 4) ℝ) :
    localCovarianceInBasis M i j R = R * localBlock (covarianceMatrix M) i j * R.transpose := by
  ext p q
  simp only [localCovarianceInBasis, Matrix.of_apply]
  unfold localMajoranaInBasis
  have hl := covarianceOf_sum M (fun s => R p s) (fun t => R q t)
    (fun s => majorana (localIndices i j s))
  rw [hl]
  rw [mul_congruence_apply R (localBlock (covarianceMatrix M) i j) p q]
  refine Finset.sum_congr rfl ?_
  intro s hs
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [← covarianceMatrix_eq_covarianceOf]
  simp only [localBlock, Matrix.of_apply]

/-- For distinct modes, the local block of a covariance update equals the covariance in the
rotated local basis. -/
theorem covarianceUpdate_local_eq_rotatedBasis {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (hij : i ≠ j) :
    localBlock (covarianceUpdate (covarianceMatrix M) i j R) i j = localCovarianceInBasis M i j R := by
  rw [localBlock_covarianceUpdate (covarianceMatrix M) i j R hij, localCovarianceInBasis_eq]

/-- Congruence by a real matrix preserves antisymmetry. -/
lemma mul_congruence_antisymm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (Λ : Matrix (Fin m) (Fin m) ℝ) (h : ∀ p q, Λ q p = -Λ p q) (p q : Fin m) :
    (S * Λ * S.transpose) q p = -(S * Λ * S.transpose) p q := by
  have hΛ : Λ.transpose = -Λ := by
    ext r s
    simp only [Matrix.transpose_apply]
    exact h r s
  have hT : (S * Λ * S.transpose).transpose = -(S * Λ * S.transpose) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hΛ, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have h2 := congrArg (fun X : Matrix (Fin m) (Fin m) ℝ => X q p) hT
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h2
  rw [h2]
  ring

/-- The covariance matrix in any real transformed Majorana basis is antisymmetric. -/
theorem covarianceInBasis_antisymm {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (a b : Fin (2 * n)) :
    covarianceInBasis M S b a = -covarianceInBasis M S a b := by
  rw [covarianceInBasis_eq_congruence]
  exact mul_congruence_antisymm S (covarianceMatrix M)
    (fun p q => covarianceMatrix_antisymm M p q) a b

/-- A covariance update preserves antisymmetry of the local block for distinct modes. -/
theorem localBlock_covarianceUpdate_antisymm {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (hij : i ≠ j) (p q : Fin 4)
    (h : ∀ s t : Fin 4, localBlock Γ i j t s = -localBlock Γ i j s t) :
    localBlock (covarianceUpdate Γ i j R) i j q p
      = -localBlock (covarianceUpdate Γ i j R) i j p q := by
  rw [localBlock_covarianceUpdate Γ i j R hij]
  exact mul_congruence_antisymm R (localBlock Γ i j) h p q

/-- Equal covariance matrices have equal updates for the same modes and local transformation. -/
theorem covarianceUpdate_eq_of_covariance_eq {n : ℕ} {Γ Γ' : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ}
    (h : Γ = Γ') (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) :
    covarianceUpdate Γ i j R = covarianceUpdate Γ' i j R := by
  rw [h]

open Matrix
open scoped BigOperators
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

/-- The anticommutator of annihilation at `i` and creation at `j` is the identity when the modes
coincide and zero otherwise. -/
theorem car_aa (n : ℕ) (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i
      = (if i = j then (1 : Matrix (Reg n) (Reg n) ℂ) else 0) :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).1 i j).1

/-- Two annihilation operators have zero anticommutator. -/
theorem car_ann (n : ℕ) (i j : Fin n) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).1 i j).2.1

/-- Two creation operators have zero anticommutator. -/
theorem car_cre (n : ℕ) (i j : Fin n) :
    creation i * creation j + creation j * creation i = 0 :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).1 i j).2.2

/-- A complex matrix whose sum with itself is zero is zero. -/
theorem add_self_eq_zero_of_complex {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (h : A + A = 0) : A = 0 := by
  ext i j
  have h1 : A i j + A i j = 0 := by
    have := congrArg (fun M : Matrix ι κ ℂ => M i j) h
    simpa using! this
  have h2 : (2 : ℂ) • A i j = 0 := by
    simpa [add_smul, smul_eq_mul] using! h1
  rcases (smul_eq_zero.mp h2) with hz | hz
  · exact absurd hz (by norm_num)
  · exact hz

/-- The even Majorana operator at mode `k`, defined as creation plus annihilation. -/
def majoranaEven {n : ℕ} (k : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  creation k + annihilation k

/-- The odd Majorana operator at mode `k`, defined as `I` times annihilation minus creation. -/
def majoranaOdd {n : ℕ} (k : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Complex.I • (annihilation k - creation k)

/-- The Majorana operator with index `2 * k.val` equals `majoranaEven k`. -/
theorem majorana_even_eq (n : ℕ) (k : Fin n) :
    majorana ⟨2 * k.val, by omega⟩ = majoranaEven k := by
  unfold majorana majoranaEven
  rw [if_pos (by omega : (2 * k.val) % 2 = 0)]
  have h1 : (⟨2 * k.val, by omega⟩ : Fin (2 * n)).val / 2 = k.val := by
    rw [Fin.val_mk]; omega
  simp only [h1]

/-- The square of an even Majorana operator is the identity. -/
theorem majoranaEven_sq (n : ℕ) (k : Fin n) : majoranaEven k * majoranaEven k = 1 := by
  have hann : annihilation k * annihilation k = 0 := by
    have h' : annihilation k * annihilation k + annihilation k * annihilation k = 0 := by
      simpa using! (car_ann n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hcre : creation k * creation k = 0 := by
    have h' : creation k * creation k + creation k * creation k = 0 := by
      simpa using! (car_cre n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hcar : annihilation k * creation k + creation k * annihilation k = 1 := by
    have h := car_aa n k k
    rw [if_pos rfl] at h
    exact h
  unfold majoranaEven
  calc (creation k + annihilation k) * (creation k + annihilation k)
      = creation k * creation k
        + (annihilation k * creation k
          + (creation k * annihilation k + annihilation k * annihilation k)) := by
            noncomm_ring
    _ = 0 + (annihilation k * creation k + (creation k * annihilation k + 0)) := by
          rw [hcre, hann]
    _ = annihilation k * creation k + creation k * annihilation k := by
          rw [add_zero, zero_add]
    _ = 1 := hcar

open Matrix
open scoped BigOperators
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

/-- The Majorana operator with index `2 * k.val + 1` equals `majoranaOdd k`. -/
theorem majorana_odd_eq (n : ℕ) (k : Fin n) :
    majorana ⟨2 * k.val + 1, by omega⟩ = majoranaOdd k := by
  unfold majorana majoranaOdd
  rw [if_neg (by omega : ¬ (2 * k.val + 1) % 2 = 0)]
  have h1 : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * n)).val / 2 = k.val := by
    rw [Fin.val_mk]; omega
  simp only [h1]

/-- Even Majorana operators at distinct modes anticommute. -/
theorem majoranaEven_anticommute (n : ℕ) (k l : Fin n) (hkl : k ≠ l) :
    majoranaEven k * majoranaEven l + majoranaEven l * majoranaEven k = 0 := by
  have hann : annihilation k * annihilation l + annihilation l * annihilation k = 0 :=
    car_ann n k l
  have hcre : creation k * creation l + creation l * creation k = 0 :=
    car_cre n k l
  have hcar1 : annihilation k * creation l + creation l * annihilation k = 0 := by
    have h := car_aa n k l
    rw [if_neg (by omega : ¬ (k = l))] at h
    exact h
  have hcar2 : annihilation l * creation k + creation k * annihilation l = 0 := by
    have h := car_aa n l k
    rw [if_neg (by omega : ¬ (l = k))] at h
    exact h
  unfold majoranaEven
  calc (creation k + annihilation k) * (creation l + annihilation l)
      + (creation l + annihilation l) * (creation k + annihilation k)
      = (creation k * creation l + creation l * creation k)
        + ((creation k * annihilation l + annihilation l * creation k)
          + ((annihilation k * creation l + creation l * annihilation k)
            + (annihilation k * annihilation l + annihilation l * annihilation k))) := by
              noncomm_ring
    _ = 0 + ((creation k * annihilation l + annihilation l * creation k)
        + ((annihilation k * creation l + creation l * annihilation k) + 0)) := by
          rw [hcre, hann]
    _ = (creation k * annihilation l + annihilation l * creation k)
        + (annihilation k * creation l + creation l * annihilation k) := by
          rw [add_zero, zero_add]
    _ = 0 + 0 := by
      have h3 : creation k * annihilation l + annihilation l * creation k = 0 := by
        calc creation k * annihilation l + annihilation l * creation k
            = annihilation l * creation k + creation k * annihilation l := by rw [add_comm]
            _ = 0 := hcar2
      have h4 : annihilation k * creation l + creation l * annihilation k = 0 := by
        exact hcar1
      rw [h3, h4]
    _ = 0 := by simp

/-- Multiplying a complex matrix by `I` twice equals multiplying it by minus one. -/
lemma I_smul_I_smul {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) :
    Complex.I • (Complex.I • M) = (-1 : ℂ) • M := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hII : Complex.I * Complex.I = -1 := by norm_num
  calc Complex.I * (Complex.I * M i j) = (Complex.I * Complex.I) * M i j := by ring
    _ = (-1) * M i j := by rw [hII]

/-- The square of an odd Majorana operator is the identity. -/
theorem majoranaOdd_sq {n : ℕ} (k : Fin n) :
    majoranaOdd k * majoranaOdd k = 1 := by
  have hsq_c : creation k * creation k = 0 := by
    have h' : creation k * creation k + creation k * creation k = 0 := by
      simpa using! (car_cre n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hsq_a : annihilation k * annihilation k = 0 := by
    have h' : annihilation k * annihilation k + annihilation k * annihilation k = 0 := by
      simpa using! (car_ann n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hcar : annihilation k * creation k + creation k * annihilation k = 1 := by
    have h := car_aa n k k
    rw [if_pos rfl] at h
    exact h
  have hX : (annihilation k - creation k) * (annihilation k - creation k)
      = -(1 : Matrix (Reg n) (Reg n) ℂ) := by
    calc (annihilation k - creation k) * (annihilation k - creation k)
        = annihilation k * annihilation k - annihilation k * creation k
          - (creation k * annihilation k - creation k * creation k) := by
            noncomm_ring
      _ = 0 - annihilation k * creation k
          - (creation k * annihilation k - 0) := by rw [hsq_a, hsq_c]
      _ = -(annihilation k * creation k + creation k * annihilation k) := by
            noncomm_ring
      _ = -(1 : Matrix (Reg n) (Reg n) ℂ) := by rw [hcar]
  unfold majoranaOdd
  rw [Matrix.smul_mul, Matrix.mul_smul, I_smul_I_smul, hX]
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, h]

/-- Odd Majorana operators at distinct modes anticommute. -/
theorem majoranaOdd_anticommute {n : ℕ} (k l : Fin n) (hkl : k ≠ l) :
    majoranaOdd k * majoranaOdd l + majoranaOdd l * majoranaOdd k = 0 := by
  have hAA : annihilation k * annihilation l + annihilation l * annihilation k = 0 :=
    car_ann n k l
  have hCC : creation k * creation l + creation l * creation k = 0 :=
    car_cre n k l
  have hAC : annihilation k * creation l + creation l * annihilation k = 0 := by
    have h := car_aa n k l
    rw [if_neg hkl] at h
    exact h
  have hCA : creation k * annihilation l + annihilation l * creation k = 0 := by
    have h := car_aa n l k
    rw [if_neg (fun h => hkl h.symm)] at h
    simpa [add_comm] using! h
  have hX : (annihilation k - creation k) * (annihilation l - creation l)
      + (annihilation l - creation l) * (annihilation k - creation k) = 0 := by
    calc (annihilation k - creation k) * (annihilation l - creation l)
        + (annihilation l - creation l) * (annihilation k - creation k)
        = (annihilation k * annihilation l + annihilation l * annihilation k)
          - (annihilation k * creation l + creation l * annihilation k)
          - ((creation k * annihilation l + annihilation l * creation k)
            - (creation k * creation l + creation l * creation k)) := by
            noncomm_ring
      _ = 0 - 0 - (0 - 0) := by rw [hAA, hAC, hCA, hCC]
      _ = 0 := by noncomm_ring
  unfold majoranaOdd
  calc (Complex.I • (annihilation k - creation k)) * (Complex.I • (annihilation l - creation l))
      + (Complex.I • (annihilation l - creation l)) * (Complex.I • (annihilation k - creation k))
      = Complex.I • (Complex.I • ((annihilation k - creation k) * (annihilation l - creation l)))
        + Complex.I • (Complex.I • ((annihilation l - creation l) * (annihilation k - creation k))) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
    _ = (-1 : ℂ) • ((annihilation k - creation k) * (annihilation l - creation l))
        + (-1 : ℂ) • ((annihilation l - creation l) * (annihilation k - creation k)) := by
          rw [I_smul_I_smul, I_smul_I_smul]
    _ = (-1 : ℂ) • (((annihilation k - creation k) * (annihilation l - creation l))
        + ((annihilation l - creation l) * (annihilation k - creation k))) := by
          rw [← smul_add]
    _ = 0 := by rw [hX, smul_zero]

/-- An even and an odd Majorana operator at distinct modes anticommute. -/
theorem majoranaEven_majoranaOdd_anticommute {n : ℕ} (k l : Fin n) (hkl : k ≠ l) :
    majoranaEven k * majoranaOdd l + majoranaOdd l * majoranaEven k = 0 := by
  have hAA : annihilation k * annihilation l + annihilation l * annihilation k = 0 :=
    car_ann n k l
  have hCC : creation k * creation l + creation l * creation k = 0 :=
    car_cre n k l
  have hAC : annihilation k * creation l + creation l * annihilation k = 0 := by
    have h := car_aa n k l
    rw [if_neg hkl] at h
    exact h
  have hCA : creation k * annihilation l + annihilation l * creation k = 0 := by
    have h := car_aa n l k
    rw [if_neg (fun h => hkl h.symm)] at h
    simpa [add_comm] using! h
  have hX : (creation k + annihilation k) * (annihilation l - creation l)
      + (annihilation l - creation l) * (creation k + annihilation k) = 0 := by
    calc (creation k + annihilation k) * (annihilation l - creation l)
        + (annihilation l - creation l) * (creation k + annihilation k)
        = (creation k * annihilation l + annihilation l * creation k)
          - (creation k * creation l + creation l * creation k)
          + (annihilation k * annihilation l + annihilation l * annihilation k)
          - (annihilation k * creation l + creation l * annihilation k) := by
            noncomm_ring
      _ = 0 - 0 + 0 - 0 := by rw [hCA, hCC, hAA, hAC]
      _ = 0 := by noncomm_ring
  unfold majoranaEven majoranaOdd
  calc (creation k + annihilation k) * (Complex.I • (annihilation l - creation l))
      + (Complex.I • (annihilation l - creation l)) * (creation k + annihilation k)
      = Complex.I • ((creation k + annihilation k) * (annihilation l - creation l))
        + Complex.I • ((annihilation l - creation l) * (creation k + annihilation k)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = Complex.I • (((creation k + annihilation k) * (annihilation l - creation l))
        + ((annihilation l - creation l) * (creation k + annihilation k))) := by
          rw [← smul_add]
    _ = 0 := by rw [hX, smul_zero]

/-- Creation followed by annihilation at the same mode equals its number operator. -/
theorem creation_mul_annihilation_eq_numberOp {n : ℕ} (k : Fin n) :
    creation k * annihilation k = numberOp k :=
  ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.1 k).1.symm

/-- Annihilation followed by creation at the same mode equals the identity minus its number
operator. -/
theorem annihilation_mul_creation_eq_one_sub_numberOp {n : ℕ} (k : Fin n) :
    annihilation k * creation k = 1 - numberOp k := by
  have hcar : annihilation k * creation k + creation k * annihilation k = 1 := by
    have h := car_aa n k k
    rw [if_pos rfl] at h
    exact h
  calc annihilation k * creation k
      = (annihilation k * creation k + creation k * annihilation k)
          - creation k * annihilation k := by
            rw [add_sub_cancel_right]
    _ = 1 - numberOp k := by rw [hcar, creation_mul_annihilation_eq_numberOp]

/-- The even Majorana times the odd Majorana at a mode equals `I` times twice its number
operator minus the identity. -/
theorem majoranaEven_majoranaOdd {n : ℕ} (k : Fin n) :
    majoranaEven k * majoranaOdd k
      = Complex.I • (numberOp k + numberOp k - 1) := by
  have hsq_c : creation k * creation k = 0 := by
    have h' : creation k * creation k + creation k * creation k = 0 := by
      simpa using! (car_cre n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hsq_a : annihilation k * annihilation k = 0 := by
    have h' : annihilation k * annihilation k + annihilation k * annihilation k = 0 := by
      simpa using! (car_ann n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hca : creation k * annihilation k = numberOp k :=
    creation_mul_annihilation_eq_numberOp k
  have hac : annihilation k * creation k = 1 - numberOp k :=
    annihilation_mul_creation_eq_one_sub_numberOp k
  unfold majoranaEven majoranaOdd
  rw [Matrix.mul_smul]
  congr 1
  calc (creation k + annihilation k) * (annihilation k - creation k)
      = creation k * annihilation k - creation k * creation k
        + (annihilation k * annihilation k - annihilation k * creation k) := by
          noncomm_ring
    _ = numberOp k - 0 + (0 - (1 - numberOp k)) := by
          rw [hca, hsq_c, hsq_a, hac]
    _ = numberOp k + numberOp k - 1 := by
          noncomm_ring

/-- The odd Majorana times the even Majorana at a mode equals `I` times the identity minus twice
its number operator. -/
theorem majoranaOdd_majoranaEven {n : ℕ} (k : Fin n) :
    majoranaOdd k * majoranaEven k
      = Complex.I • (1 - numberOp k - numberOp k) := by
  have hsq_c : creation k * creation k = 0 := by
    have h' : creation k * creation k + creation k * creation k = 0 := by
      simpa using! (car_cre n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hsq_a : annihilation k * annihilation k = 0 := by
    have h' : annihilation k * annihilation k + annihilation k * annihilation k = 0 := by
      simpa using! (car_ann n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hca : creation k * annihilation k = numberOp k :=
    creation_mul_annihilation_eq_numberOp k
  have hac : annihilation k * creation k = 1 - numberOp k :=
    annihilation_mul_creation_eq_one_sub_numberOp k
  unfold majoranaEven majoranaOdd
  rw [Matrix.smul_mul]
  congr 1
  calc (annihilation k - creation k) * (creation k + annihilation k)
      = annihilation k * creation k + annihilation k * annihilation k
        - (creation k * creation k + creation k * annihilation k) := by
          noncomm_ring
    _ = (1 - numberOp k) + 0 - (0 + numberOp k) := by
          rw [hac, hsq_a, hsq_c, hca]
    _ = 1 - numberOp k - numberOp k := by
          noncomm_ring

/-- The even and odd Majorana operators at the same mode anticommute. -/
theorem majoranaEven_majoranaOdd_anticommute_same (n : ℕ) (k : Fin n) :
    majoranaEven k * majoranaOdd k + majoranaOdd k * majoranaEven k = 0 := by
  have hsq_c : creation k * creation k = 0 := by
    have h' : creation k * creation k + creation k * creation k = 0 := by
      simpa using! (car_cre n k k)
    exact add_self_eq_zero_of_complex _ h'
  have hsq_a : annihilation k * annihilation k = 0 := by
    have h' : annihilation k * annihilation k + annihilation k * annihilation k = 0 := by
      simpa using! (car_ann n k k)
    exact add_self_eq_zero_of_complex _ h'
  calc majoranaEven k * majoranaOdd k + majoranaOdd k * majoranaEven k
      = Complex.I • ((creation k + annihilation k) * (annihilation k - creation k)
          + (annihilation k - creation k) * (creation k + annihilation k)) := by
            unfold majoranaEven majoranaOdd
            rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
      _ = Complex.I • ((annihilation k * annihilation k + annihilation k * annihilation k)
          - (creation k * creation k + creation k * creation k)) := by
            apply congrArg (fun T : Matrix (Reg n) (Reg n) ℂ => Complex.I • T)
            noncomm_ring
      _ = 0 := by
            rw [hsq_c, hsq_a]
            simp

/-- The Majorana operator selected by the even within-mode index equals `majoranaEven`. -/
theorem majoranaIndices_even (n : ℕ) (k : Fin n) :
    majorana (majoranaIndices k 0) = majoranaEven k := by
  have hidx : majoranaIndices k 0 = ⟨2 * k.val, by omega⟩ := by
    apply Fin.ext
    simp only [majoranaIndices]
    omega
  rw [hidx]
  unfold majorana
  rw [if_pos (by omega : (2 * k.val) % 2 = 0)]
  have h1 : (⟨2 * k.val, by omega⟩ : Fin (2 * n)).val / 2 = k.val := by
    rw [Fin.val_mk]; omega
  simp only [h1]
  rfl

/-- The Majorana operator selected by the odd within-mode index equals `majoranaOdd`. -/
theorem majoranaIndices_odd (n : ℕ) (k : Fin n) :
    majorana (majoranaIndices k 1) = majoranaOdd k := by
  have hidx : majoranaIndices k 1 = ⟨2 * k.val + 1, by omega⟩ := by
    apply Fin.ext
    simp only [majoranaIndices]
    omega
  rw [hidx]
  unfold majorana
  rw [if_neg (by omega : ¬ (2 * k.val + 1) % 2 = 0)]
  have h1 : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * n)).val / 2 = k.val := by
    rw [Fin.val_mk]; omega
  simp only [h1]
  rfl

/-- The commutator of the even and odd Majorana operators at a mode is expressed in terms of its
number operator. -/
theorem majorana_comm {n : ℕ} (k : Fin n) :
    majoranaEven k * majoranaOdd k - majoranaOdd k * majoranaEven k
      = Complex.I • ((numberOp k + numberOp k - 1) - (1 - numberOp k - numberOp k)) := by
  rw [majoranaEven_majoranaOdd, majoranaOdd_majoranaEven, ← smul_sub]

/-- The trace of the sandwiched same-mode Majorana commutator is `I` times four times the
number-operator sandwich trace minus twice the norm trace. -/
theorem trace_sandwich_majorana_comm {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) :
    (Mᴴ * (majoranaEven k * majoranaOdd k
        - majoranaOdd k * majoranaEven k) * M).trace
      = Complex.I * ((4 : ℂ) * (Mᴴ * (numberOp k) * M).trace
          - (2 : ℂ) * (Mᴴ * M).trace) := by
  have hcomm := majorana_comm k
  have hsand : Mᴴ * (majoranaEven k * majoranaOdd k
        - majoranaOdd k * majoranaEven k) * M
      = Complex.I • (Mᴴ * ((numberOp k + numberOp k - 1)
          - (1 - numberOp k - numberOp k)) * M) := by
    rw [hcomm, Matrix.mul_smul, Matrix.smul_mul]
  have e1 : (Mᴴ * (numberOp k + numberOp k - 1) * M).trace
      = (Mᴴ * (numberOp k + numberOp k) * M).trace
        - (Mᴴ * (1 : Matrix (Reg n) (Reg n) ℂ) * M).trace := by
    exact trace_sandwich_sub Mᴴ M _ _
  have e2 : (Mᴴ * (1 - numberOp k - numberOp k) * M).trace
      = (Mᴴ * (1 - numberOp k) * M).trace
        - (Mᴴ * (numberOp k) * M).trace := by
    exact trace_sandwich_sub Mᴴ M _ _
  have e3 : (Mᴴ * (1 - numberOp k) * M).trace
      = (Mᴴ * (1 : Matrix (Reg n) (Reg n) ℂ) * M).trace
        - (Mᴴ * (numberOp k) * M).trace := by
    exact trace_sandwich_sub Mᴴ M _ _
  have e4 : (Mᴴ * (numberOp k + numberOp k) * M).trace
      = (Mᴴ * (numberOp k) * M).trace + (Mᴴ * (numberOp k) * M).trace := by
    exact trace_sandwich_add Mᴴ M _ _
  have e5 : (Mᴴ * (1 : Matrix (Reg n) (Reg n) ℂ) * M).trace = (Mᴴ * M).trace := by
    exact trace_sandwich_one Mᴴ M
  have htr : (Mᴴ * ((numberOp k + numberOp k - 1)
        - (1 - numberOp k - numberOp k)) * M).trace
      = (4 : ℂ) * (Mᴴ * (numberOp k) * M).trace
        - (2 : ℂ) * (Mᴴ * M).trace := by
    rw [trace_sandwich_sub, e1, e2, e3, e4, e5]
    ring
  rw [hsand, Matrix.trace_smul, smul_eq_mul, htr]

/-- The same-mode even–odd covariance entry equals the real norm trace minus twice the real
number-operator sandwich trace. -/
theorem covarianceMatrix_occupation {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) :
    covarianceMatrix M (majoranaIndices k 0) (majoranaIndices k 1)
      = (Matrix.trace (Mᴴ * M)).re
        - 2 * (Matrix.trace (Mᴴ * (numberOp k) * M)).re := by
  rw [covarianceMatrix_eq_im, majoranaIndices_even, majoranaIndices_odd]
  rw [trace_sandwich_majorana_comm]
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_re]
  simp
  linarith

/-- Twice the occupation expectation equals the real norm trace minus the same-mode even–odd
covariance entry. -/
theorem occupationExpectation_eq_of_covariance {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (k : Fin n) :
    2 * occupationExpectation M k
      = (Matrix.trace (Mᴴ * M)).re
        - covarianceMatrix M (majoranaIndices k 0) (majoranaIndices k 1) := by
  rw [occupationExpectation]
  have h := covarianceMatrix_occupation M k
  linarith

/-- For a matrix with real norm trace one, the occupation expectation is recovered from its
covariance matrix [Bravyi2005Fermionic]. -/
theorem occupationExpectation_eq_occupationFromCovariance {n : ℕ}
    (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n)
    (hM : (Matrix.trace (Mᴴ * M)).re = 1) :
    occupationExpectation M k = occupationFromCovariance (covarianceMatrix M) k := by
  unfold occupationExpectation occupationFromCovariance
  have h := covarianceMatrix_occupation M k
  rw [h, hM]
  linarith

/-- An even–odd covariance entry between minus one and one yields an occupation value between
zero and one. -/
theorem occupationFromCovariance_bounds {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (k : Fin n) (hlo : -1 ≤ Γ (majoranaIndices k 0) (majoranaIndices k 1))
    (hhi : Γ (majoranaIndices k 0) (majoranaIndices k 1) ≤ 1) :
    0 ≤ occupationFromCovariance Γ k ∧ occupationFromCovariance Γ k ≤ 1 := by
  unfold occupationFromCovariance
  constructor <;> linarith

/-- For a positive register size, the defined classical occupation cost is strictly smaller than
the physical measurement cost. -/
theorem occupationClassicalCost_lt_physical {n : ℕ} (k : Fin n) (h : 0 < n) :
    occupationClassicalCost k < physicalMeasurementCost n := by
  unfold occupationClassicalCost physicalMeasurementCost
  have hpos : ∀ m : ℕ, (0 : ℕ) < 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [Nat.pow_succ]; omega
  have heq : 2 ^ n = 2 ^ (n - 1) * 2 := by
    have h := Nat.pow_succ (2) (n - 1)
    rw [← h]
    congr 1
    omega
  rw [heq]
  have h1 : (1 : ℕ) ≤ 2 ^ (n - 1) := hpos (n - 1)
  omega

/-- Every Majorana operator is the even or odd operator of its mode, according to the parity of
its index. -/
theorem majorana_eq_flavour (n : ℕ) (a : Fin (2 * n)) :
    majorana a = if a.val % 2 = 0 then majoranaEven ⟨a.val / 2, by omega⟩
                 else majoranaOdd ⟨a.val / 2, by omega⟩ := by
  by_cases h : a.val % 2 = 0
  · simp [majorana, majoranaEven, h]
  · simp [majorana, majoranaOdd, h]

/-- The sum of two identity matrices equals twice the identity matrix. -/
lemma one_add_one_eq_two (n : ℕ) :
    (1 : Matrix (Reg n) (Reg n) ℂ) + 1 = (2 : ℂ) • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp; norm_num
  · simp [h]

/-- The Majorana anticommutator is twice the identity for equal indices and zero for distinct
indices. -/
theorem majorana_clifford (n : ℕ) (a b : Fin (2 * n)) :
    majorana a * majorana b + majorana b * majorana a
      = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  have hka : a.val / 2 < n := by omega
  have hkb : b.val / 2 < n := by omega
  have hval (m : ℕ) : m = 2 * (m / 2) + m % 2 := by
    have := Nat.div_add_mod m 2; omega
  have hA : majorana a
      = if a.val % 2 = 0 then majoranaEven ⟨a.val / 2, hka⟩ else majoranaOdd ⟨a.val / 2, hka⟩ := by
    by_cases h : a.val % 2 = 0
    · simp [majorana, majoranaEven, h]
    · simp [majorana, majoranaOdd, h]
  have hB : majorana b
      = if b.val % 2 = 0 then majoranaEven ⟨b.val / 2, hkb⟩ else majoranaOdd ⟨b.val / 2, hkb⟩ := by
    by_cases h : b.val % 2 = 0
    · simp [majorana, majoranaEven, h]
    · simp [majorana, majoranaOdd, h]
  have heq_of (h : a.val / 2 = b.val / 2) :
      (⟨b.val / 2, hkb⟩ : Fin n) = ⟨a.val / 2, hka⟩ := by
    apply Fin.ext; exact h.symm
  have hne_of (h : a.val / 2 ≠ b.val / 2) :
      (⟨a.val / 2, hka⟩ : Fin n) ≠ ⟨b.val / 2, hkb⟩ := by
    intro hh; apply h; simpa using! (congrArg Fin.val hh)
  have hne_of' (h : a.val / 2 ≠ b.val / 2) :
      (⟨b.val / 2, hkb⟩ : Fin n) ≠ ⟨a.val / 2, hka⟩ := by
    intro hh; apply h; simpa using! (congrArg Fin.val hh).symm
  have hab_of (pa : a.val % 2 = 0) (pb : b.val % 2 = 0) (h : a.val / 2 = b.val / 2) : a = b := by
    apply Fin.ext
    have ha' := hval a.val
    have hb' := hval b.val
    omega
  have hab_of_odd (pa : a.val % 2 = 1) (pb : b.val % 2 = 1) (h : a.val / 2 = b.val / 2) :
      a = b := by
    apply Fin.ext
    have ha' := hval a.val
    have hb' := hval b.val
    omega
  have hne_same (pa : a.val % 2 = 0) (pb : b.val % 2 = 0) (h : a.val / 2 ≠ b.val / 2) :
      a ≠ b := by
    intro hh
    apply h
    have hval' := congrArg Fin.val hh
    have ha' := hval a.val
    have hb' := hval b.val
    omega
  have hne_same_odd (pa : a.val % 2 = 1) (pb : b.val % 2 = 1) (h : a.val / 2 ≠ b.val / 2) :
      a ≠ b := by
    intro hh
    apply h
    have hval' := congrArg Fin.val hh
    have ha' := hval a.val
    have hb' := hval b.val
    omega
  have hne_mixed (ha : a.val % 2 = 0) (hb : b.val % 2 = 1) : a ≠ b := by
    intro hh
    have hval' := congrArg Fin.val hh
    have ha' := hval a.val
    have hb' := hval b.val
    omega
  have hne_mixed' (ha : a.val % 2 = 1) (hb : b.val % 2 = 0) : a ≠ b := by
    intro hh
    have hval' := congrArg Fin.val hh
    have ha' := hval a.val
    have hb' := hval b.val
    omega
  by_cases ha : a.val % 2 = 0
  · by_cases hb : b.val % 2 = 0
    · rw [hA, if_pos ha, hB, if_pos hb]
      by_cases h : a.val / 2 = b.val / 2
      · have hab : a = b := hab_of ha hb h
        rw [if_pos hab]
        rw [heq_of h]
        have hsq := majoranaEven_sq n ⟨a.val / 2, hka⟩
        calc majoranaEven _ * majoranaEven _ + majoranaEven _ * majoranaEven _
            = 1 + 1 := by rw [hsq]
          _ = (2 : ℂ) • 1 := one_add_one_eq_two n
      · have hz := majoranaEven_anticommute n ⟨a.val / 2, hka⟩ ⟨b.val / 2, hkb⟩ (hne_of h)
        rw [hz]
        rw [if_neg (hne_same ha hb h)]
        simp
    · have hb1 : b.val % 2 = 1 := by omega
      rw [hA, if_pos ha, hB, if_neg hb]
      by_cases h : a.val / 2 = b.val / 2
      · have hz : majoranaEven ⟨a.val / 2, hka⟩ * majoranaOdd ⟨b.val / 2, hkb⟩
            + majoranaOdd ⟨b.val / 2, hkb⟩ * majoranaEven ⟨a.val / 2, hka⟩ = 0 := by
          rw [heq_of h]
          exact majoranaEven_majoranaOdd_anticommute_same n ⟨a.val / 2, hka⟩
        rw [hz]
        rw [if_neg (hne_mixed ha hb1)]
        simp
      · have hz := majoranaEven_majoranaOdd_anticommute ⟨a.val / 2, hka⟩ ⟨b.val / 2, hkb⟩
            (hne_of h)
        rw [hz]
        rw [if_neg (hne_mixed ha hb1)]
        simp
  · by_cases hb : b.val % 2 = 0
    · have ha1 : a.val % 2 = 1 := by omega
      rw [hA, if_neg ha, hB, if_pos hb]
      by_cases h : a.val / 2 = b.val / 2
      · have hz : majoranaOdd ⟨a.val / 2, hka⟩ * majoranaEven ⟨b.val / 2, hkb⟩
            + majoranaEven ⟨b.val / 2, hkb⟩ * majoranaOdd ⟨a.val / 2, hka⟩ = 0 := by
          rw [heq_of h, add_comm]
          exact majoranaEven_majoranaOdd_anticommute_same n ⟨a.val / 2, hka⟩
        rw [hz]
        rw [if_neg (hne_mixed' ha1 hb)]
        simp
      · have hz := majoranaEven_majoranaOdd_anticommute ⟨b.val / 2, hkb⟩ ⟨a.val / 2, hka⟩
            (hne_of' h)
        rw [add_comm, hz]
        rw [if_neg (hne_mixed' ha1 hb)]
        simp
    · have ha1 : a.val % 2 = 1 := by omega
      have hb1 : b.val % 2 = 1 := by omega
      rw [hA, if_neg ha, hB, if_neg hb]
      by_cases h : a.val / 2 = b.val / 2
      · have hab : a = b := hab_of_odd ha1 hb1 h
        rw [if_pos hab]
        rw [heq_of h]
        have hsq := majoranaOdd_sq ⟨a.val / 2, hka⟩
        calc majoranaOdd _ * majoranaOdd _ + majoranaOdd _ * majoranaOdd _
            = 1 + 1 := by rw [hsq]
          _ = (2 : ℂ) • 1 := one_add_one_eq_two n
      · have hz := majoranaOdd_anticommute ⟨a.val / 2, hka⟩ ⟨b.val / 2, hkb⟩ (hne_of h)
        rw [hz]
        rw [if_neg (hne_same_odd ha1 hb1 h)]
        simp

/-- The Gram matrix entry of two rows of the real matrix `S`, defined as their dot product. -/
def gramMatrix {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (a b : Fin (2 * n)) : ℝ :=
  ∑ c, S a c * S b c

/-- Interchanging two scalar factors does not change their product acting on a matrix over a
commutative semiring. -/
lemma smul_comm {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {α : Type} [CommSemiring α] [AddCommMonoid α] (r s : α) (M : Matrix m n α) :
    (r * s) • M = (s * r) • M := by
  ext i j
  simp [Matrix.smul_apply, mul_comm]

/-- A finite sum weighted by twice the equality indicator at `c` equals `2 * w c`. -/
lemma sum_clifford_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) (c : ι) :
    (∑ d, w d * (if c = d then (2 : ℂ) else 0)) = w c * 2 := by
  classical
  have hform : ∀ d, w d * (if c = d then (2 : ℂ) else 0)
      = if d = c then w d * 2 else 0 := by
    intro d
    by_cases h : c = d
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl (fun d _ => hform d), Finset.sum_ite_eq']
  simp

/-- The anticommutator of transformed Majorana operators equals twice the complex row dot
product of `S` times the identity. -/
theorem majoranaInBasis_anticommutator {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a b : Fin (2 * n)) :
    majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
      = (2 * ∑ c : Fin (2 * n), (S a c : ℂ) * (S b c : ℂ)) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  have hexp : majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
      = ∑ c, ∑ d, ((S a c : ℂ) * (S b d : ℂ)) •
          (majorana c * majorana d + majorana d * majorana c) := by
    simp only [majoranaInBasis]
    rw [sum_mul_sum, sum_mul_sum]
    have hB : (∑ d, ∑ c, ((S b d : ℂ) * (S a c : ℂ)) • (majorana d * majorana c))
        = ∑ c, ∑ d, ((S a c : ℂ) * (S b d : ℂ)) • (majorana d * majorana c) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro c hc
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [smul_comm]
    rw [hB]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [← smul_add]
  rw [hexp]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
      congrArg (fun X : Matrix (Reg n) (Reg n) ℂ => ((S a c : ℂ) * (S b d : ℂ)) • X)
        (majorana_clifford n c d)))]
  have hinner : ∀ (c : Fin (2 * n)),
      (∑ d, ((S a c : ℂ) * (S b d : ℂ)) • ((if c = d then (2 : ℂ) else 0)
          • (1 : Matrix (Reg n) (Reg n) ℂ)))
        = ((S a c : ℂ) * (S b c : ℂ) * 2) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
    intro c
    have hform : ∀ d : Fin (2 * n),
        ((S a c : ℂ) * (S b d : ℂ)) • ((if c = d then (2 : ℂ) else 0)
            • (1 : Matrix (Reg n) (Reg n) ℂ))
          = (((S a c : ℂ) * (S b d : ℂ)) * (if c = d then (2 : ℂ) else 0))
            • (1 : Matrix (Reg n) (Reg n) ℂ) := by
      intro d
      rw [smul_smul]
    rw [Finset.sum_congr rfl (fun d _ => hform d)]
    rw [← Finset.sum_smul]
    rw [sum_clifford_ite]
  rw [Finset.sum_congr rfl (fun c _ => hinner c)]
  rw [← Finset.sum_smul]
  rw [← Finset.sum_mul]
  apply congrArg (fun T : ℂ => T • (1 : Matrix (Reg n) (Reg n) ℂ))
  ring

/-- The row Gram matrix entry of `S` equals the corresponding entry of `S * S.transpose`. -/
theorem gramMatrix_eq_mul_transpose {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a b : Fin (2 * n)) :
    gramMatrix S a b = (S * S.transpose) a b := by
  rw [gramMatrix, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [Matrix.transpose_apply]

/-- The anticommutator of transformed Majorana operators equals twice the real Gram matrix entry
times the identity. -/
theorem majoranaInBasis_anticommutator_real {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a b : Fin (2 * n)) :
    majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
      = ((2 * gramMatrix S a b : ℝ) : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [majoranaInBasis_anticommutator]
  apply congrArg (fun T : ℂ => T • (1 : Matrix (Reg n) (Reg n) ℂ))
  have hcast : (∑ c : Fin (2 * n), (S a c : ℂ) * (S b c : ℂ)) = (gramMatrix S a b : ℂ) := by
    simp [gramMatrix, Complex.ofReal_mul, Complex.ofReal_sum]
  rw [hcast]
  have hone : (2 : ℂ) * (gramMatrix S a b : ℂ) = ((2 * gramMatrix S a b : ℝ) : ℂ) := by
    have h5 := (Complex.ofReal_mul (2 : ℝ) (gramMatrix S a b)).symm
    norm_num at h5 ⊢
  exact hone

/-- Complex scalars giving equal scalar multiples of the register identity matrix are equal. -/
lemma smul_one_inj {n : ℕ} (r s : ℂ)
    (h : r • (1 : Matrix (Reg n) (Reg n) ℂ) = s • (1 : Matrix (Reg n) (Reg n) ℂ)) : r = s := by
  have h0 := congrArg (fun M : Matrix (Reg n) (Reg n) ℂ => M (fun _ => false) (fun _ => false)) h
  simp only [Matrix.smul_apply, Matrix.one_apply] at h0
  simp at h0
  exact h0

/-- An orthogonal real basis transformation preserves the Majorana Clifford relations. -/
theorem majoranaInBasis_clifford_of_orthogonal {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hS : S * S.transpose = 1) (a b : Fin (2 * n)) :
    majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
      = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [majoranaInBasis_anticommutator_real, gramMatrix_eq_mul_transpose, hS]
  have hone : (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a b = if a = b then 1 else 0 := by
    simp [Matrix.one_apply]
  rw [hone]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

/-- A real transformation whose Majorana operators satisfy the Clifford relations has `S *
S.transpose = 1`. -/
theorem majoranaInBasis_orthogonal_of_clifford {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hS : ∀ a b : Fin (2 * n),
      majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
        = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ))
    : S * S.transpose = 1 := by
  ext a b
  have hone : (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a b = if a = b then 1 else 0 := by
    simp [Matrix.one_apply]
  rw [hone, ← gramMatrix_eq_mul_transpose]
  have hgram : gramMatrix S a b = if a = b then 1 else 0 := by
    have h1 := hS a b
    have h2 := majoranaInBasis_anticommutator_real S a b
    have h4 := smul_one_inj _ _ (h2.symm.trans h1)
    by_cases h : a = b
    · have h6 := congrArg Complex.re h4
      rw [Complex.ofReal_re] at h6
      simp only [if_pos h] at h6
      norm_num at h6
      simp only [if_pos h]
      linarith
    · have h6 := congrArg Complex.re h4
      rw [Complex.ofReal_re] at h6
      simp only [if_neg h] at h6
      norm_num at h6
      simp only [if_neg h]
      linarith
  exact hgram

/-- Distinct local slots for two distinct modes select distinct Majorana indices. -/
theorem localMajoranaIndices_ne {n : ℕ} (i j : Fin n) (hij : i ≠ j) (p q : Fin 4)
    (hpq : p ≠ q) : localIndices i j p ≠ localIndices i j q := by
  intro hh
  have hslot : localSlot i j (localIndices i j p) = localSlot i j (localIndices i j q) := by
    rw [hh]
  rw [localSlot_localIndices i j hij p, localSlot_localIndices i j hij q] at hslot
  exact hpq hslot

/-- The four Majorana operators of two distinct modes satisfy the Clifford relations. -/
theorem localMajorana_clifford {n : ℕ} (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    majorana (localIndices i j p) * majorana (localIndices i j q)
      + majorana (localIndices i j q) * majorana (localIndices i j p)
      = (if p = q then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  by_cases hpq : p = q
  · subst hpq
    simpa using! (majorana_clifford n (localIndices i j p) (localIndices i j p))
  · have hab : localIndices i j p ≠ localIndices i j q := localMajoranaIndices_ne i j hij p q hpq
    have h := majorana_clifford n (localIndices i j p) (localIndices i j q)
    rw [if_neg hab] at h
    rw [if_neg hpq]
    exact h

/-- For distinct modes, the anticommutator of transformed local Majoranas is twice the complex
row dot product of `R` times the identity. -/
theorem localMajoranaInBasis_anticommutator {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (p q : Fin 4) :
    localMajoranaInBasis i j R p * localMajoranaInBasis i j R q
      + localMajoranaInBasis i j R q * localMajoranaInBasis i j R p
      = (2 * ∑ s : Fin 4, (R p s : ℂ) * (R q s : ℂ)) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  have hexp : localMajoranaInBasis i j R p * localMajoranaInBasis i j R q
      + localMajoranaInBasis i j R q * localMajoranaInBasis i j R p
      = ∑ c, ∑ d, ((R p c : ℂ) * (R q d : ℂ)) •
          (majorana (localIndices i j c) * majorana (localIndices i j d)
            + majorana (localIndices i j d) * majorana (localIndices i j c)) := by
    simp only [localMajoranaInBasis]
    rw [sum_mul_sum, sum_mul_sum]
    have hB : (∑ d, ∑ c, ((R q d : ℂ) * (R p c : ℂ)) •
          (majorana (localIndices i j d) * majorana (localIndices i j c)))
        = ∑ c, ∑ d, ((R p c : ℂ) * (R q d : ℂ)) •
          (majorana (localIndices i j d) * majorana (localIndices i j c)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro c hc
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [smul_comm]
    rw [hB]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [← smul_add]
  rw [hexp]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
      congrArg (fun X : Matrix (Reg n) (Reg n) ℂ => ((R p c : ℂ) * (R q d : ℂ)) • X)
        (localMajorana_clifford i j hij c d)))]
  have hinner : ∀ (c : Fin 4),
      (∑ d, ((R p c : ℂ) * (R q d : ℂ)) • ((if c = d then (2 : ℂ) else 0)
          • (1 : Matrix (Reg n) (Reg n) ℂ)))
        = ((R p c : ℂ) * (R q c : ℂ) * 2) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
    intro c
    have hform : ∀ d : Fin 4,
        ((R p c : ℂ) * (R q d : ℂ)) • ((if c = d then (2 : ℂ) else 0)
            • (1 : Matrix (Reg n) (Reg n) ℂ))
          = (((R p c : ℂ) * (R q d : ℂ)) * (if c = d then (2 : ℂ) else 0))
            • (1 : Matrix (Reg n) (Reg n) ℂ) := by
      intro d
      rw [smul_smul]
    rw [Finset.sum_congr rfl (fun d _ => hform d)]
    rw [← Finset.sum_smul]
    rw [sum_clifford_ite]
  rw [Finset.sum_congr rfl (fun c _ => hinner c)]
  rw [← Finset.sum_smul]
  rw [← Finset.sum_mul]
  apply congrArg (fun T : ℂ => T • (1 : Matrix (Reg n) (Reg n) ℂ))
  ring

/-- For distinct modes, the anticommutator of transformed local Majoranas is twice the real row
dot product of `R` times the identity. -/
theorem localMajoranaInBasis_anticommutator_real {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (p q : Fin 4) :
    localMajoranaInBasis i j R p * localMajoranaInBasis i j R q
      + localMajoranaInBasis i j R q * localMajoranaInBasis i j R p
      = ((2 * (∑ s : Fin 4, R p s * R q s) : ℝ) : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [localMajoranaInBasis_anticommutator i j hij R p q]
  apply congrArg (fun T : ℂ => T • (1 : Matrix (Reg n) (Reg n) ℂ))
  have hcast : (∑ s : Fin 4, (R p s : ℂ) * (R q s : ℂ))
      = ((∑ s : Fin 4, R p s * R q s : ℝ) : ℂ) := by
    simp [Complex.ofReal_mul, Complex.ofReal_sum]
  rw [hcast]
  have hone : (2 : ℂ) * ((∑ s : Fin 4, R p s * R q s : ℝ) : ℂ)
      = ((2 * (∑ s : Fin 4, R p s * R q s) : ℝ) : ℂ) := by
    have h5 := (Complex.ofReal_mul (2 : ℝ) (∑ s : Fin 4, R p s * R q s)).symm
    norm_num at h5 ⊢
  exact hone

/-- An orthogonal local transformation preserves the Clifford relations for the Majoranas of two
distinct modes. -/
theorem localMajoranaInBasis_clifford_of_orthogonal {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : R * R.transpose = 1) (p q : Fin 4) :
    localMajoranaInBasis i j R p * localMajoranaInBasis i j R q
      + localMajoranaInBasis i j R q * localMajoranaInBasis i j R p
      = (if p = q then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [localMajoranaInBasis_anticommutator_real i j hij R p q]
  have hgram : ∀ (p q : Fin 4), (∑ s, R p s * R q s : ℝ) = (R * R.transpose) p q := by
    intro p q
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [Matrix.transpose_apply]
  rw [hgram, hR]
  have hone : (1 : Matrix (Fin 4) (Fin 4) ℝ) p q = if p = q then 1 else 0 := by
    simp [Matrix.one_apply]
  rw [hone]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

/-- If twice a real Gram entry equals the corresponding complex Clifford coefficient, the Gram
entry is the equality indicator. -/
lemma gramMatrix_eq_ite {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (a b : Fin (2 * n))
    (h : ((2 * gramMatrix S a b : ℝ) : ℂ) = (if a = b then 2 else 0 : ℂ)) :
    gramMatrix S a b = if a = b then 1 else 0 := by
  have h6 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h6
  by_cases hab : a = b
  · simp only [if_pos hab] at h6
    norm_num at h6
    simp only [if_pos hab]
    linarith
  · simp only [if_neg hab] at h6
    norm_num at h6
    simp only [if_neg hab]
    linarith

/-- The conjugate transpose of a matrix product is the product of the conjugate transposes in
reverse order. -/
lemma mul_conjTranspose {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) : (A * B)ᴴ = Bᴴ * Aᴴ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, star_mul]

/-- When `U * Uᴴ = 1`, conjugation by `U` distributes over a product of register matrices. -/
lemma conj_mul_conj {n : ℕ} (U X Y : Matrix (Reg n) (Reg n) ℂ)
    (hU : U * Uᴴ = 1) :
    Uᴴ * (X * Y) * U = (Uᴴ * X * U) * (Uᴴ * Y * U) := by
  calc Uᴴ * (X * Y) * U = Uᴴ * X * Y * U := by ac_rfl
    _ = (Uᴴ * X * U) * (Uᴴ * Y * U) := by
      have hform : (Uᴴ * X * U) * (Uᴴ * Y * U) = Uᴴ * X * (U * Uᴴ) * Y * U := by ac_rfl
      rw [hform, hU, Matrix.mul_one]

/-- When `U * Uᴴ = 1`, the anticommutator of conjugated matrices is the conjugate of their
anticommutator. -/
lemma conj_anticommutator {n : ℕ} (U X Y : Matrix (Reg n) (Reg n) ℂ)
    (hU : U * Uᴴ = 1) :
    (Uᴴ * X * U) * (Uᴴ * Y * U) + (Uᴴ * Y * U) * (Uᴴ * X * U) = Uᴴ * (X * Y + Y * X) * U := by
  calc (Uᴴ * X * U) * (Uᴴ * Y * U) + (Uᴴ * Y * U) * (Uᴴ * X * U)
      = (Uᴴ * X * (U * Uᴴ) * Y * U) + (Uᴴ * Y * (U * Uᴴ) * X * U) := by
        ac_rfl
    _ = (Uᴴ * X * Y * U) + (Uᴴ * Y * X * U) := by rw [hU, Matrix.mul_one, Matrix.mul_one]
    _ = Uᴴ * (X * Y + Y * X) * U := by
      rw [Matrix.mul_add, Matrix.add_mul]
      ac_rfl

/-- When `U * Uᴴ = 1`, multiplying `M` by `U` transfers to conjugation of both arguments of the
complex covariance pairing. -/
lemma covarianceComplexOf_conj {n : ℕ} (U M X Y : Matrix (Reg n) (Reg n) ℂ) (hU : U * Uᴴ = 1) :
    covarianceComplexOf (U * M) X Y = covarianceComplexOf M (Uᴴ * X * U) (Uᴴ * Y * U) := by
  have hconj : (U * M)ᴴ = Mᴴ * Uᴴ := mul_conjTranspose U M
  have e1 : Matrix.trace ((Mᴴ * Uᴴ) * (X * Y) * (U * M))
      = Matrix.trace (Mᴴ * ((Uᴴ * X * U) * (Uᴴ * Y * U)) * M) := by
    have hstep : (Mᴴ * Uᴴ) * (X * Y) * (U * M) = Mᴴ * (Uᴴ * (X * Y) * U) * M := by
      ac_rfl
    rw [hstep]
    have hstep2 : Mᴴ * (Uᴴ * (X * Y) * U) * M
        = Mᴴ * ((Uᴴ * X * U) * (Uᴴ * Y * U)) * M := by
      rw [conj_mul_conj U X Y hU]
    rw [hstep2]
  have e2 : Matrix.trace ((Mᴴ * Uᴴ) * (Y * X) * (U * M))
      = Matrix.trace (Mᴴ * ((Uᴴ * Y * U) * (Uᴴ * X * U)) * M) := by
    have hstep : (Mᴴ * Uᴴ) * (Y * X) * (U * M) = Mᴴ * (Uᴴ * (Y * X) * U) * M := by
      ac_rfl
    rw [hstep]
    have hstep2 : Mᴴ * (Uᴴ * (Y * X) * U) * M
        = Mᴴ * ((Uᴴ * Y * U) * (Uᴴ * X * U)) * M := by
      rw [conj_mul_conj U Y X hU]
    rw [hstep2]
  unfold covarianceComplexOf
  rw [hconj, e1, e2]

/-- When `U * Uᴴ = 1`, multiplying `M` by `U` transfers to conjugation of both arguments of the
real covariance pairing. -/
lemma covarianceOf_conj {n : ℕ} (U M X Y : Matrix (Reg n) (Reg n) ℂ) (hU : U * Uᴴ = 1) :
    covarianceOf (U * M) X Y = covarianceOf M (Uᴴ * X * U) (Uᴴ * Y * U) := by
  unfold covarianceOf
  rw [covarianceComplexOf_conj U M X Y hU]

/-- If conjugation by `U` induces the real Majorana transformation `S` and `U * Uᴴ = 1`, the
covariance transforms by congruence with `S`. -/
theorem covarianceMatrix_congruence_of_induced {n : ℕ} (U M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hU : U * Uᴴ = 1)
    (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a) :
    covarianceMatrix (U * M) = S * covarianceMatrix M * S.transpose := by
  ext a b
  have h1 : covarianceMatrix (U * M) a b
      = covarianceOf M (majoranaInBasis S a) (majoranaInBasis S b) := by
    rw [covarianceMatrix_eq_covarianceOf]
    have hc := covarianceOf_conj U M (majorana a) (majorana b) hU
    rw [hS a, hS b] at hc
    exact hc
  have h2 : covarianceOf M (majoranaInBasis S a) (majoranaInBasis S b)
      = covarianceInBasis M S a b := rfl
  have h3 : covarianceInBasis M S a b = (S * covarianceMatrix M * S.transpose) a b := by
    have := congrArg (fun N : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ => N a b)
      (covarianceInBasis_eq_congruence M S)
    exact this
  rw [h1, h2, h3]

/-- A real Majorana transformation induced by conjugation with `U` is orthogonal when `Uᴴ * U =
1`. -/
theorem induced_frame_orthogonal_of_unitary {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : Uᴴ * U = 1) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a) :
    S * S.transpose = 1 := by
  ext a b
  have hone : (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a b = if a = b then 1 else 0 := by
    simp [Matrix.one_apply]
  rw [hone, ← gramMatrix_eq_mul_transpose]
  refine gramMatrix_eq_ite S a b ?_
  have hU' : U * Uᴴ = 1 := (mul_eq_one_comm (a := Uᴴ) (b := U)).mp hU
  have hconj : (Uᴴ * majorana a * U) * (Uᴴ * majorana b * U)
        + (Uᴴ * majorana b * U) * (Uᴴ * majorana a * U)
      = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
    calc (Uᴴ * majorana a * U) * (Uᴴ * majorana b * U)
          + (Uᴴ * majorana b * U) * (Uᴴ * majorana a * U)
        = Uᴴ * (majorana a * majorana b + majorana b * majorana a) * U :=
          conj_anticommutator U (majorana a) (majorana b) hU'
      _ = Uᴴ * ((if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ)) * U := by
          rw [majorana_clifford]
      _ = (if a = b then (2 : ℂ) else 0) • ((Uᴴ * 1) * U) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
          rw [Matrix.mul_one, hU]
  have hgram := majoranaInBasis_anticommutator_real S a b
  have hfr : (Uᴴ * majorana a * U) * (Uᴴ * majorana b * U)
        + (Uᴴ * majorana b * U) * (Uᴴ * majorana a * U)
      = majoranaInBasis S a * majoranaInBasis S b
        + majoranaInBasis S b * majoranaInBasis S a := by
      rw [hS a, hS b]
  have h3 : ((2 * gramMatrix S a b : ℝ) : ℂ) = (if a = b then 2 else 0 : ℂ) :=
    smul_one_inj _ _ (hgram.symm.trans (hfr.symm.trans hconj))
  exact h3

/-- The identity basis transformation leaves each Majorana operator unchanged. -/
theorem majoranaInBasis_one {n : ℕ} (a : Fin (2 * n)) : majoranaInBasis 1 a = majorana a := by
  simp [majoranaInBasis, Matrix.one_apply]

/-- Under an induced Majorana transformation `S` with `U * Uᴴ = 1`, twice the evolved occupation
is the original real norm trace minus the transformed even–odd covariance entry. -/
theorem occupationExpectation_congruence_of_induced_general {n : ℕ}
    (U M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hU : U * Uᴴ = 1)
    (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a)
    (k : Fin n) :
    2 * occupationExpectation (U * M) k
      = (Matrix.trace (Mᴴ * M)).re
        - (S * covarianceMatrix M * S.transpose) (majoranaIndices k 0) (majoranaIndices k 1) := by
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have h1 : (U * M)ᴴ * (U * M) = Mᴴ * M := by
    calc (U * M)ᴴ * (U * M) = Mᴴ * (Uᴴ * (U * M)) := by
          rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * ((Uᴴ * U) * M) := by rw [← Matrix.mul_assoc Uᴴ U M]
      _ = Mᴴ * M := by rw [hUU, Matrix.one_mul]
  have h2 := occupationExpectation_eq_of_covariance (U * M) k
  rw [h1] at h2
  rw [covarianceMatrix_congruence_of_induced U M S hU hS] at h2
  exact h2

/-- For real norm trace one, an induced Majorana transformation `S` with `U * Uᴴ = 1` computes
the evolved occupation from the covariance congruence. -/
theorem occupationExpectation_congruence_of_induced {n : ℕ} (U M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hU : U * Uᴴ = 1)
    (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a)
    (k : Fin n) (hM : (Matrix.trace (Mᴴ * M)).re = 1) :
    occupationExpectation (U * M) k
      = occupationFromCovariance (S * covarianceMatrix M * S.transpose) k := by
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hnorm : (Matrix.trace ((U * M)ᴴ * (U * M))).re = 1 := by
    have h1 : (U * M)ᴴ * (U * M) = Mᴴ * M := by
      calc (U * M)ᴴ * (U * M) = Mᴴ * (Uᴴ * (U * M)) := by
            rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Mᴴ * ((Uᴴ * U) * M) := by rw [← Matrix.mul_assoc Uᴴ U M]
        _ = Mᴴ * M := by rw [hUU, Matrix.one_mul]
    rw [h1]
    exact hM
  rw [occupationExpectation_eq_occupationFromCovariance (U * M) k hnorm]
  rw [covarianceMatrix_congruence_of_induced U M S hU hS]

/-- A match gate with skew-Hermitian coefficients transforms covariance by congruence with any
real Majorana transformation it induces. -/
theorem matchGate_covariance_congruence {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Aᴴ = -A) (M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hS : ∀ a : Fin (2 * n), (matchGate i j A)ᴴ * majorana a * (matchGate i j A)
      = majoranaInBasis S a) :
    covarianceMatrix (matchGate i j A * M) = S * covarianceMatrix M * S.transpose := by
  have hU : matchGate i j A * (matchGate i j A)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (matchGate_unitary i j A hA)
  exact covarianceMatrix_congruence_of_induced (matchGate i j A) M S hU hS

/-- For real norm trace one, occupation after a match gate with skew-Hermitian coefficients is
recovered from the covariance congruence of its assumed induced Majorana transformation. -/
theorem matchGate_occupation_congruence {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Aᴴ = -A) (M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (hS : ∀ a : Fin (2 * n), (matchGate i j A)ᴴ * majorana a * (matchGate i j A)
      = majoranaInBasis S a)
    (k : Fin n) (hM : (Matrix.trace (Mᴴ * M)).re = 1) :
    occupationExpectation (matchGate i j A * M) k
      = occupationFromCovariance (S * covarianceMatrix M * S.transpose) k := by
  have hU : matchGate i j A * (matchGate i j A)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (matchGate_unitary i j A hA)
  exact occupationExpectation_congruence_of_induced (matchGate i j A) M S hU hS k hM

/-- The defined circuit operation count plus one occupation cost is at most `64 * matchGateCount
gl + 1`. -/
theorem classicalSimulationCost_le {n : ℕ} (gl : MatchGateCircuit n) (k : Fin n) :
    matchGateCircuitClassicalOps gl + occupationClassicalCost k
      ≤ 64 * matchGateCount gl + 1 := by
  have h := matchGateCircuitClassicalOps_le gl
  rw [occupationClassicalCost]
  omega

/-- Circuits with equal match-gate counts have equal defined classical operation counts after
adding the same occupation cost. -/
theorem classicalSimulationCost_indep_of_register {n m : ℕ} (gl : MatchGateCircuit n)
    (gl' : MatchGateCircuit m) (h : matchGateCount gl = matchGateCount gl') (k : Fin n) :
    matchGateCircuitClassicalOps gl + occupationClassicalCost k
      = matchGateCircuitClassicalOps gl' + occupationClassicalCost k := by
  rw [occupationClassicalCost]
  simp only [matchGateCircuitClassicalOps, matchGateClassicalOps]
  rw [h]

/-- The even Majorana plus `I` times the odd Majorana equals twice the creation operator. -/
theorem majorana_even_odd_sum {n : ℕ} (k : Fin n) :
    majoranaEven k + Complex.I • majoranaOdd k = (2 : ℂ) • creation k := by
  unfold majoranaEven majoranaOdd
  have hI : Complex.I • (Complex.I • (annihilation k - creation k))
      = -((annihilation k - creation k)) := by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  rw [hI, neg_sub]
  have h : (creation k + annihilation k) + (creation k - annihilation k)
      = (creation k + creation k) + (annihilation k + -annihilation k) := by abel
  rw [h]
  have h2 : (2 : ℂ) = 1 + 1 := by norm_num
  rw [h2, add_smul, one_smul]
  abel

/-- The even Majorana minus `I` times the odd Majorana equals twice the annihilation operator. -/
theorem majorana_even_odd_diff {n : ℕ} (k : Fin n) :
    majoranaEven k - Complex.I • majoranaOdd k = (2 : ℂ) • annihilation k := by
  unfold majoranaEven majoranaOdd
  have hI : Complex.I • (Complex.I • (annihilation k - creation k))
      = -((annihilation k - creation k)) := by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  rw [hI, neg_sub]
  have h : (creation k + annihilation k) - (creation k - annihilation k)
      = (annihilation k + annihilation k) + (creation k + -creation k) := by abel
  rw [h]
  have h2 : (2 : ℂ) = 1 + 1 := by norm_num
  rw [h2, add_smul, one_smul]
  abel

/-- Creation is one half of the even Majorana plus `I` times the odd Majorana. -/
theorem creation_eq_majorana_half {n : ℕ} (k : Fin n) :
    creation k = (1 / 2 : ℂ) • (majoranaEven k + Complex.I • majoranaOdd k) := by
  rw [majorana_even_odd_sum k, smul_smul]
  have h : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h, one_smul]

/-- Annihilation is one half of the even Majorana minus `I` times the odd Majorana. -/
theorem annihilation_eq_majorana_half {n : ℕ} (k : Fin n) :
    annihilation k = (1 / 2 : ℂ) • (majoranaEven k - Complex.I • majoranaOdd k) := by
  rw [majorana_even_odd_diff k, smul_smul]
  have h : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h, one_smul]

/-- For distinct modes, half the sum of the even–even and odd–odd Majorana products equals the
antisymmetric hopping combination. -/
theorem cross_quad_sum {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (1 / 2 : ℂ) • (majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j)
      = creation i * annihilation j - creation j * annihilation i := by
  have hO : majoranaOdd i * majoranaOdd j
      = -((annihilation i - creation i) * (annihilation j - creation j)) := by
    unfold majoranaOdd
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.smul_mul, Complex.I_mul_I]
    rw [neg_smul, one_smul, neg_mul]
  rw [majoranaEven, majoranaEven, hO, ← sub_eq_add_neg]
  have hPQ : (creation i + annihilation i) * (creation j + annihilation j)
      - (annihilation i - creation i) * (annihilation j - creation j)
      = creation i * annihilation j + annihilation i * creation j
        + creation i * annihilation j + annihilation i * creation j := by
    simp only [sub_mul, mul_sub, add_mul, mul_add]
    noncomm_ring
  rw [hPQ]
  have h2 : (1 / 2 : ℂ)
      • (creation i * annihilation j + annihilation i * creation j
        + creation i * annihilation j + annihilation i * creation j)
      = creation i * annihilation j + annihilation i * creation j := by
    have habel : creation i * annihilation j + annihilation i * creation j
        + creation i * annihilation j + annihilation i * creation j
        = (2 : ℂ) • (creation i * annihilation j + annihilation i * creation j) := by
      calc _ = (creation i * annihilation j + annihilation i * creation j)
          + (creation i * annihilation j + annihilation i * creation j) := by abel
        _ = (1 + 1 : ℂ) • (creation i * annihilation j + annihilation i * creation j) := by
          rw [add_smul, one_smul]
        _ = (2 : ℂ) • (creation i * annihilation j + annihilation i * creation j) := by norm_num
    rw [habel, smul_smul]
    have hh : (1 / 2 : ℂ) * 2 = 1 := by norm_num
    rw [hh, one_smul]
  rw [h2]
  have hcar : annihilation i * creation j + creation j * annihilation i = 0 := by
    have h := car_aa n i j
    rw [if_neg (fun h => hij h)] at h
    exact h
  have hog : annihilation i * creation j = -(creation j * annihilation i) :=
    add_eq_zero_iff_eq_neg.mp hcar
  rw [hog, sub_eq_add_neg]

/-- For distinct modes, half the even–odd minus odd–even Majorana products equals `I` times the
symmetric hopping combination. -/
theorem cross_quad_diff {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (1 / 2 : ℂ) • (majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j)
      = Complex.I • (creation i * annihilation j + creation j * annihilation i) := by
  have h1 : majoranaEven i * majoranaOdd j
      = Complex.I • ((creation i + annihilation i) * (annihilation j - creation j)) := by
    unfold majoranaEven majoranaOdd
    rw [Matrix.mul_smul]
  have h2 : majoranaOdd i * majoranaEven j
      = Complex.I • ((annihilation i - creation i) * (creation j + annihilation j)) := by
    unfold majoranaEven majoranaOdd
    rw [← Matrix.smul_mul]
  have hcar : annihilation i * creation j + creation j * annihilation i = 0 := by
    have h := car_aa n i j
    rw [if_neg (fun h => hij h)] at h
    exact h
  have hog : annihilation i * creation j = -(creation j * annihilation i) :=
    add_eq_zero_iff_eq_neg.mp hcar
  have hPQ : (creation i + annihilation i) * (annihilation j - creation j)
      - (annihilation i - creation i) * (creation j + annihilation j)
      = creation i * annihilation j + creation j * annihilation i
        + creation i * annihilation j + creation j * annihilation i := by
    simp only [sub_mul, mul_sub, add_mul, mul_add]
    rw [hog]
    noncomm_ring
  rw [h1, h2]
  rw [← smul_sub, hPQ]
  have habel : creation i * annihilation j + creation j * annihilation i
        + creation i * annihilation j + creation j * annihilation i
      = (2 : ℂ) • (creation i * annihilation j + creation j * annihilation i) := by
      calc _ = (creation i * annihilation j + creation j * annihilation i)
          + (creation i * annihilation j + creation j * annihilation i) := by abel
        _ = (1 + 1 : ℂ) • (creation i * annihilation j + creation j * annihilation i) := by
          rw [add_smul, one_smul]
        _ = (2 : ℂ) • (creation i * annihilation j + creation j * annihilation i) := by norm_num
  rw [smul_smul, habel, smul_smul]
  have hI : ((1 / 2 : ℂ) * Complex.I) * 2 = Complex.I := by ring
  rw [hI]

/-- For distinct modes, the quadratic generator expands as a scalar identity term and explicit
quadratic Majorana terms. -/
theorem quadraticGenerator_eq_majoranaForm {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    quadraticGenerator i j A
      = ((A 0 0 + A 1 1) / 2) • 1
        + (-(Complex.I) * A 0 0 / 2) • (majoranaEven i * majoranaOdd i)
        + (-(Complex.I) * A 1 1 / 2) • (majoranaEven j * majoranaOdd j)
        + ((A 0 1 - A 1 0) / 4)
            • (majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j)
        + (-(Complex.I) * (A 0 1 + A 1 0) / 4)
            • (majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j) := by
  have hnum (k : Fin n) : creation k * annihilation k = numberOp k := by
    exact ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.1 k).1.symm
  have hsplit (a : ℂ) (X : Matrix (Reg n) (Reg n) ℂ) :
      a • X = (a / 2) • (X + X - 1) + (a / 2) • 1 := by
    have h1 : (a / 2 : ℂ) + (a / 2 : ℂ) = a := by ring
    have h2 : (a / 2 : ℂ) • (X + X) = a • X := by
      rw [smul_add, ← add_smul, h1]
    rw [smul_sub, h2, sub_add_cancel]
  have hcross (a b : ℂ) (X Y : Matrix (Reg n) (Reg n) ℂ) :
      ((a - b) / 2) • (X - Y) + ((a + b) / 2) • (X + Y) = a • X + b • Y := by
    have h1 : (a - b) / 2 + (a + b) / 2 = a := by ring
    have h2 : (a + b) / 2 - (a - b) / 2 = b := by ring
    have hkey : ((a - b) / 2) • (X - Y) + ((a + b) / 2) • (X + Y)
        = ((a - b) / 2 + (a + b) / 2) • X
          + ((a + b) / 2 - (a - b) / 2) • Y := by
      rw [smul_sub, smul_add]
      rw [add_smul, sub_smul]
      simp only [sub_eq_add_neg]
      abel
    calc
      ((a - b) / 2) • (X - Y) + ((a + b) / 2) • (X + Y)
          = ((a - b) / 2 + (a + b) / 2) • X
            + ((a + b) / 2 - (a - b) / 2) • Y := hkey
      _ = a • X + b • Y := by rw [h1, h2]
  have hinv1 : majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j
      = (2 : ℂ) • (creation i * annihilation j - creation j * annihilation i) := by
    have h := cross_quad_sum i j hij
    calc
      majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j
          = (2 : ℂ) • ((1 / 2 : ℂ)
              • (majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j)) := by
                rw [smul_smul, show (2 : ℂ) * (1 / 2 : ℂ) = 1 by ring, one_smul]
      _ = (2 : ℂ) • (creation i * annihilation j - creation j * annihilation i) := by
                rw [h]
  have hinv2 : majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j
      = (2 : ℂ) • (Complex.I
          • (creation i * annihilation j + creation j * annihilation i)) := by
    have h := cross_quad_diff i j hij
    calc
      majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j
          = (2 : ℂ) • ((1 / 2 : ℂ)
              • (majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j)) := by
                rw [smul_smul, show (2 : ℂ) * (1 / 2 : ℂ) = 1 by ring, one_smul]
      _ = (2 : ℂ) • (Complex.I
          • (creation i * annihilation j + creation j * annihilation i)) := by
                rw [h]
  have hRHS : ((A 0 0 + A 1 1) / 2) • 1
        + (-(Complex.I) * A 0 0 / 2) • (majoranaEven i * majoranaOdd i)
        + (-(Complex.I) * A 1 1 / 2) • (majoranaEven j * majoranaOdd j)
        + ((A 0 1 - A 1 0) / 4)
            • (majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j)
        + (-(Complex.I) * (A 0 1 + A 1 0) / 4)
            • (majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j)
      = ((A 0 0 + A 1 1) / 2) • 1
        + (A 0 0 / 2) • (numberOp i + numberOp i - 1)
        + (A 1 1 / 2) • (numberOp j + numberOp j - 1)
        + ((A 0 1 - A 1 0) / 2)
            • (creation i * annihilation j - creation j * annihilation i)
        + ((A 0 1 + A 1 0) / 2)
            • (creation i * annihilation j + creation j * annihilation i) := by
    rw [majoranaEven_majoranaOdd i, majoranaEven_majoranaOdd j, hinv1, hinv2]
    rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
    have eI (z : ℂ) : (-(Complex.I) * z / 2) * Complex.I = z / 2 := by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc
        (-(Complex.I) * z / 2) * Complex.I
            = -(Complex.I * ((z / 2) * Complex.I)) := by ring
        _ = -(Complex.I * (Complex.I * (z / 2))) := by rw [mul_comm (z / 2) Complex.I]
        _ = -((Complex.I * Complex.I) * (z / 2)) := by rw [mul_assoc]
        _ = -((-1) * (z / 2)) := by rw [hI]
        _ = z / 2 := by ring
    have e1 : (-(Complex.I) * A 0 0 / 2) * Complex.I = A 0 0 / 2 := eI (A 0 0)
    have e2 : (-(Complex.I) * A 1 1 / 2) * Complex.I = A 1 1 / 2 := eI (A 1 1)
    have e3 : ((A 0 1 - A 1 0) / 4) * 2 = (A 0 1 - A 1 0) / 2 := by ring
    have eI2 (z : ℂ) : (-Complex.I * z / 4 * 2) * Complex.I = z / 2 := by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc
        (-Complex.I * z / 4 * 2) * Complex.I
            = -(Complex.I * ((z / 2) * Complex.I)) := by ring
        _ = -(Complex.I * (Complex.I * (z / 2))) := by rw [mul_comm (z / 2) Complex.I]
        _ = -((Complex.I * Complex.I) * (z / 2)) := by rw [mul_assoc]
        _ = -((-1) * (z / 2)) := by rw [hI]
        _ = z / 2 := by ring
    have e4 : (-Complex.I * (A 0 1 + A 1 0) / 4 * 2) * Complex.I
        = (A 0 1 + A 1 0) / 2 := eI2 (A 0 1 + A 1 0)
    rw [e1, e2, e3, e4]
  calc
    quadraticGenerator i j A
        = (A 0 0) • numberOp i + (A 0 1) • (creation i * annihilation j)
          + (A 1 0) • (creation j * annihilation i) + (A 1 1) • numberOp j := by
            rw [quadraticGenerator, hnum i, hnum j]
    _ = (A 0 1) • (creation i * annihilation j) + (A 1 0) • (creation j * annihilation i)
          + ((A 0 0) • numberOp i + (A 1 1) • numberOp j) := by abel
    _ = ((A 0 1 - A 1 0) / 2) • (creation i * annihilation j - creation j * annihilation i)
          + ((A 0 1 + A 1 0) / 2) • (creation i * annihilation j + creation j * annihilation i)
          + ((A 0 0) • numberOp i + (A 1 1) • numberOp j) := by
            rw [← hcross (A 0 1) (A 1 0) (creation i * annihilation j)
              (creation j * annihilation i)]
    _ = ((A 0 1 - A 1 0) / 2) • (creation i * annihilation j - creation j * annihilation i)
          + ((A 0 1 + A 1 0) / 2) • (creation i * annihilation j + creation j * annihilation i)
          + ((A 0 0 / 2) • (numberOp i + numberOp i - 1) + (A 0 0 / 2) • 1
            + ((A 1 1 / 2) • (numberOp j + numberOp j - 1) + (A 1 1 / 2) • 1)) := by
            rw [hsplit (A 0 0) (numberOp i), hsplit (A 1 1) (numberOp j)]
    _ = ((A 0 0 + A 1 1) / 2) • 1
          + (A 0 0 / 2) • (numberOp i + numberOp i - 1)
          + (A 1 1 / 2) • (numberOp j + numberOp j - 1)
          + ((A 0 1 - A 1 0) / 2) • (creation i * annihilation j - creation j * annihilation i)
          + ((A 0 1 + A 1 0) / 2) • (creation i * annihilation j + creation j * annihilation i) := by
            rw [show ((A 0 0 + A 1 1) / 2 : ℂ) = A 0 0 / 2 + A 1 1 / 2 by ring]
            rw [add_smul]
            abel
    _ = ((A 0 0 + A 1 1) / 2) • 1
        + (-(Complex.I) * A 0 0 / 2) • (majoranaEven i * majoranaOdd i)
        + (-(Complex.I) * A 1 1 / 2) • (majoranaEven j * majoranaOdd j)
        + ((A 0 1 - A 1 0) / 4)
            • (majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j)
        + (-(Complex.I) * (A 0 1 + A 1 0) / 4)
            • (majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j) :=
      hRHS.symm

/-- For a skew-Hermitian coefficient matrix, the four displayed quadratic Majorana coefficients
have zero imaginary part. -/
theorem quadraticGenerator_majoranaForm_coef_real {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Aᴴ = -A) :
    ((-(Complex.I) * A 0 0 / 2 : ℂ).im : ℂ) = 0
      ∧ ((-(Complex.I) * A 1 1 / 2 : ℂ).im : ℂ) = 0
      ∧ (((A 0 1 - A 1 0) / 4 : ℂ).im : ℂ) = 0
      ∧ ((-(Complex.I) * (A 0 1 + A 1 0) / 4 : ℂ).im : ℂ) = 0 := by
  have h00 : star (A 0 0) = -(A 0 0) := by
    have h := congrArg (fun M => M 0 0) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h11 : star (A 1 1) = -(A 1 1) := by
    have h := congrArg (fun M => M 1 1) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h01 : star (A 0 1) = -(A 1 0) := by
    have h := congrArg (fun M => M 1 0) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h10 : star (A 1 0) = -(A 0 1) := by
    have h := congrArg (fun M => M 0 1) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h00re : (A 0 0).re = 0 := by
    have h := congrArg Complex.re h00
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  have h11re : (A 1 1).re = 0 := by
    have h := congrArg Complex.re h11
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  have hcrossim : ((A 0 1 - A 1 0 : ℂ).im) = 0 := by
    have h := congrArg Complex.im h01
    rw [RCLike.star_def, Complex.conj_im, Complex.neg_im] at h
    have h2 := congrArg Complex.im h10
    rw [RCLike.star_def, Complex.conj_im, Complex.neg_im] at h2
    rw [Complex.sub_im]
    linarith
  have hsumre : ((A 0 1 + A 1 0 : ℂ).re) = 0 := by
    have h := congrArg Complex.re h01
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h
    have h2 := congrArg Complex.re h10
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h2
    rw [Complex.add_re]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Complex.div_im, Complex.mul_im]
    simp [h00re]
  · rw [Complex.div_im, Complex.mul_im]
    simp [h11re]
  · rw [Complex.div_im, hcrossim]
    simp
  · rw [Complex.div_im, Complex.mul_im]
    simp [hsumre]

/-- The real local form matrix is skew-symmetric. -/
theorem localFormMatrix_transpose (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (localFormMatrix A).transpose = -(localFormMatrix A) := by
  unfold localFormMatrix
  rw [Matrix.transpose_sub]
  abel

/-- The six upper-triangular entries of the local form matrix are the specified half real or
imaginary parts of the coefficient entries. -/
theorem localFormMatrix_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    localFormMatrix A 0 1 = (A 0 0).im / 2
      ∧ localFormMatrix A 2 3 = (A 1 1).im / 2
      ∧ localFormMatrix A 0 2 = (A 0 1).re / 2
      ∧ localFormMatrix A 1 3 = (A 0 1).re / 2
      ∧ localFormMatrix A 0 3 = (A 0 1).im / 2
      ∧ localFormMatrix A 1 2 = -(A 0 1).im / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [localFormMatrix, localFormSym, Matrix.sub_apply, Matrix.transpose_apply]
  · simp [localFormMatrix, localFormSym, Matrix.sub_apply, Matrix.transpose_apply]
  · simp [localFormMatrix, localFormSym, Matrix.sub_apply, Matrix.transpose_apply]
  · simp [localFormMatrix, localFormSym, Matrix.sub_apply, Matrix.transpose_apply]
  · simp [localFormMatrix, localFormSym, Matrix.sub_apply, Matrix.transpose_apply]
  · simp [localFormMatrix, localFormSym, Matrix.sub_apply, Matrix.transpose_apply]

/-- The six upper-triangular entries of `localFormSym` are the specified half real or imaginary
parts of the coefficient entries. -/
theorem localFormSym_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    localFormSym A 0 1 = (A 0 0).im / 2 ∧
    localFormSym A 2 3 = (A 1 1).im / 2 ∧
    localFormSym A 0 2 = (A 0 1).re / 2 ∧
    localFormSym A 1 3 = (A 0 1).re / 2 ∧
    localFormSym A 0 3 = (A 0 1).im / 2 ∧
    localFormSym A 1 2 = -((A 0 1).im / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [localFormSym, Matrix.of_apply]
  · simp [localFormSym, Matrix.of_apply]
  · simp [localFormSym, Matrix.of_apply]
  · simp [localFormSym, Matrix.of_apply]
  · simp [localFormSym, Matrix.of_apply]
  · simp [localFormSym, Matrix.of_apply]; ring

/-- The local rotation satisfies `localRotation A * (localRotation A).transpose = 1`. -/
theorem localRotation_mul_transpose (A : Matrix (Fin 2) (Fin 2) ℂ) :
    localRotation A * (localRotation A).transpose = 1 := by
  have hskew : (localFormMatrix A).transpose = -(localFormMatrix A) :=
    localFormMatrix_transpose A
  have h1 : (localRotation A).transpose
      = NormedSpace.exp (-((2 : ℝ) • localFormMatrix A)) := by
    rw [localRotation, ← Matrix.exp_transpose, Matrix.transpose_smul, hskew, smul_neg]
  rw [h1]
  unfold localRotation
  have hcomm : Commute ((2 : ℝ) • localFormMatrix A) (-((2 : ℝ) • localFormMatrix A)) := by
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply]
  rw [← Matrix.exp_add_of_commute _ _ hcomm]
  rw [add_neg_cancel, NormedSpace.exp_zero]

/-- Each local Majorana index is the index of its selected mode and within-mode bit. -/
theorem localIndices_eq_majoranaIndices {n : ℕ} (i j : Fin n) (p : Fin 4) :
    localIndices i j p = majoranaIndices (localMode i j p) (localBit p) := by
  rcases p with ⟨k, hk⟩
  interval_cases k <;> simp [localIndices, localMode, localBit, majoranaIndices]

/-- For distinct modes, equality of local Majorana indices implies equality of their slots. -/
theorem localIndices_inj {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : Fin 4) :
    localIndices i j a = localIndices i j b → a = b := by
  intro h
  rw [localIndices_eq_majoranaIndices, localIndices_eq_majoranaIndices] at h
  have hpair :=
    (majoranaIndices_eq (localMode i j a) (localMode i j b) (localBit a) (localBit b)).mp h
  have hmode : localMode i j a = localMode i j b := hpair.1
  have hbit : localBit a = localBit b := hpair.2
  have hval : a.val = b.val := by
    by_cases ha : a.val < 2
    · have hma : localMode i j a = i := by simp [localMode, ha]
      have hmb : localMode i j b = i := by rw [← hmode]; exact hma
      have hb : b.val < 2 := by
        by_contra hb
        have hmb' : localMode i j b = j := by simp [localMode, hb]
        have hne : localMode i j a = localMode i j b := hmode
        have hne2 : i = j := hma.symm.trans (hne.trans hmb')
        exact hij hne2
      have h1 : a.val % 2 = a.val := Nat.mod_eq_of_lt ha
      have h2 : b.val % 2 = b.val := Nat.mod_eq_of_lt hb
      have h3 : a.val % 2 = b.val % 2 := congrArg Fin.val hbit
      omega
    · have hma : localMode i j a = j := by simp [localMode, ha]
      have hb : ¬ b.val < 2 := by
        intro hb
        have hmb : localMode i j b = i := by simp [localMode, hb]
        have hne : localMode i j a = localMode i j b := hmode
        have hne2 : j = i := hma.symm.trans (hne.trans hmb)
        exact hij hne2.symm
      have h3 : a.val % 2 = b.val % 2 := congrArg Fin.val hbit
      have h1 : a.val % 2 = a.val - 2 := by
        have hz : a.val = 2 ∨ a.val = 3 := by omega
        rcases hz with hz | hz <;> rw [hz]
      have h2 : b.val % 2 = b.val - 2 := by
        have hz : b.val = 2 ∨ b.val = 3 := by omega
        rcases hz with hz | hz <;> rw [hz]
      omega
  exact Fin.ext hval

/-- Every local Majorana index is selected by some slot of `localIndices`. -/
theorem exists_localIndices {n : ℕ} (i j : Fin n) (b : Fin (2 * n))
    (hb : isLocalMajorana i j b) : ∃ a : Fin 4, localIndices i j a = b := by
  rcases hb with hb | hb | hb | hb
  · exact ⟨⟨0, by norm_num⟩, by simp [localIndices, hb]⟩
  · exact ⟨⟨1, by norm_num⟩, by simp [localIndices, hb]⟩
  · exact ⟨⟨2, by norm_num⟩, by simp [localIndices, hb]⟩
  · exact ⟨⟨3, by norm_num⟩, by simp [localIndices, hb]⟩

/-- For distinct modes, selecting the slot of a local Majorana index recovers that index. -/
theorem localIndices_localSlot {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fin (2 * n))
    (ha : isLocalMajorana i j a) : localIndices i j (localSlot i j a) = a := by
  obtain ⟨p, hp⟩ := exists_localIndices i j a ha
  have h1 : localSlot i j (localIndices i j p) = p := localSlot_localIndices i j hij p
  calc localIndices i j (localSlot i j a) = localIndices i j (localSlot i j (localIndices i j p)) :=
        by rw [hp]
    _ = localIndices i j p := by rw [h1]
    _ = a := hp

/-- For distinct modes, equal local slots of local Majorana indices imply equal indices. -/
theorem localSlot_inj_local {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : Fin (2 * n))
    (ha : isLocalMajorana i j a) (hb : isLocalMajorana i j b) :
    localSlot i j a = localSlot i j b → a = b := by
  have h1 : a = localIndices i j (localSlot i j a) := (localIndices_localSlot i j hij a ha).symm
  have h2 : b = localIndices i j (localSlot i j b) := (localIndices_localSlot i j hij b hb).symm
  intro h
  rw [h1, h2, h]

/-- On local Majorana indices, a frame rotation has the entries of the corresponding local
rotation at their slots. -/
theorem frameRotation_apply_local {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin (2 * n)) (ha : isLocalMajorana i j a) (hb : isLocalMajorana i j b) :
    frameRotation i j A a b = (localRotation A) (localSlot i j a) (localSlot i j b) := by
  simp [frameRotation, ha, hb]

/-- On indices outside the local modes, a frame rotation has identity matrix entries. -/
theorem frameRotation_apply_away {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b) :
    frameRotation i j A a b = if a = b then 1 else 0 := by
  simp [frameRotation, ha, hb]

/-- A frame rotation entry is zero when its row is local and its column is outside the local
modes. -/
theorem frameRotation_apply_left_local_right_away {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (a c : Fin (2 * n))
    (ha : isLocalMajorana i j a) (hc : ¬ isLocalMajorana i j c) :
    frameRotation i j A a c = 0 := by
  have hne : a ≠ c := by
    intro h
    exact hc (h ▸ ha)
  simp [frameRotation, ha, hc, hne]

/-- A frame rotation entry is zero when its row is outside the local modes and its column is
local. -/
theorem frameRotation_apply_right_local_left_away {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (a c : Fin (2 * n))
    (ha : ¬ isLocalMajorana i j a) (hc : isLocalMajorana i j c) :
    frameRotation i j A a c = 0 := by
  have hne : a ≠ c := by
    intro h
    exact ha (h ▸ hc)
  simp [frameRotation, ha, hc, hne]

/-- A frame rotation has zero off-diagonal entries between indices outside the local modes. -/
theorem frameRotation_apply_away_neq {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b)
    (hne : a ≠ b) :
    frameRotation i j A a b = 0 := by
  simp [frameRotation, ha, hb, hne]

/-- A frame rotation has diagonal entry one at each index outside the local modes. -/
theorem frameRotation_apply_away_eq {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) :
    frameRotation i j A a a = 1 := by
  simp [frameRotation, ha]

/-- For distinct modes, a sum supported on their local Majorana indices reduces to the sum over
four local slots. -/
theorem sum_localMajorana {n : ℕ} {ι : Type} [AddCommMonoid ι] (i j : Fin n) (hij : i ≠ j)
    (φ : Fin (2 * n) → ι)
    (hzero : ∀ a, ¬ isLocalMajorana i j a → φ a = 0) :
    ∑ a : Fin (2 * n), φ a = ∑ p : Fin 4, φ (localIndices i j p) := by
  classical
  have h1 : ∑ a ∈ (localMajoranaFinset i j : Finset (Fin (2 * n))), φ a
      = ∑ a : Fin (2 * n), φ a := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro b hb hnot
    exact hzero b (by simpa [localMajoranaFinset] using! hnot)
  have h2 : ∑ p ∈ (Finset.univ : Finset (Fin 4)), φ (localIndices i j p)
      = ∑ a ∈ (localMajoranaFinset i j : Finset (Fin (2 * n))), φ a := by
    refine Finset.sum_bij (s := (Finset.univ : Finset (Fin 4)))
      (t := localMajoranaFinset i j)
      (f := fun p => φ (localIndices i j p)) (g := φ)
      (fun p _ => localIndices i j p) ?_ ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, isLocalMajorana_localIndices i j p⟩
    · intro p hp q hq heq
      exact localIndices_inj i j hij p q heq
    · intro b hb
      obtain ⟨p, hp⟩ := exists_localIndices i j b (Finset.mem_filter.mp hb).2
      exact ⟨p, Finset.mem_univ _, hp⟩
    · intro p hp
      rfl
  rw [← h1, ← h2]

/-- For distinct modes, a frame rotation transforms each local Majorana into the corresponding
locally transformed Majorana. -/
theorem majoranaInBasis_frameRotation_local {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 4) :
    majoranaInBasis (frameRotation i j A) (localIndices i j p)
      = localMajoranaInBasis i j (localRotation A) p := by
  have hz : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
      (frameRotation i j A (localIndices i j p) c : ℂ) • majorana c = 0 := by
    intro c hc
    rw [frameRotation_apply_left_local_right_away i j A (localIndices i j p) c
      (isLocalMajorana_localIndices i j p) hc]
    simp
  have hsum := sum_localMajorana i j hij
    (fun c : Fin (2 * n) => (frameRotation i j A (localIndices i j p) c : ℂ) • majorana c) hz
  simp only [majoranaInBasis, localMajoranaInBasis]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro s hs
  (try dsimp only)
  rw [frameRotation_apply_local i j A _ _ (isLocalMajorana_localIndices i j p)
    (isLocalMajorana_localIndices i j s)]
  rw [localSlot_localIndices i j hij p, localSlot_localIndices i j hij s]

/-- A frame rotation leaves Majorana operators outside the local modes unchanged. -/
theorem majoranaInBasis_frameRotation_away {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) :
    majoranaInBasis (frameRotation i j A) a = majorana a := by
  classical
  have haa : frameRotation i j A a a = 1 := by
    simp [frameRotation, ha]
  have hconv : majorana a = (frameRotation i j A a a : ℂ) • majorana a := by
    rw [haa]
    simp
  have hzero : ∀ b : Fin (2 * n), b ≠ a →
      (frameRotation i j A a b : ℂ) • majorana b = 0 := by
    intro b hb
    by_cases hbl : isLocalMajorana i j b
    · rw [frameRotation_apply_right_local_left_away i j A a b ha hbl]
      simp
    · rw [frameRotation_apply_away_neq i j A a b ha hbl hb.symm]
      simp
  simp only [majoranaInBasis]
  rw [hconv]
  refine Finset.sum_eq_single a ?_ ?_
  · intro b hb hne
    exact hzero b hne
  · intro h
    exact (h (Finset.mem_univ a)).elim

/-- For distinct modes, the local covariance block after a frame rotation is its congruence by
the local rotation. -/
theorem localBlock_covarianceInBasis_frameRotation {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (i j : Fin n) (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    localBlock (covarianceInBasis M (frameRotation i j A)) i j
      = (localRotation A) * localBlock (covarianceMatrix M) i j * (localRotation A).transpose := by
  have hloc : ∀ p q : Fin 4,
      localCovarianceInBasis M i j (localRotation A) p q
        = ((localRotation A) * localBlock (covarianceMatrix M) i j
            * (localRotation A).transpose) p q := by
    intro p q
    have h := congrFun (congrFun (localCovarianceInBasis_eq M i j (localRotation A)) p) q
    simpa [localCovarianceInBasis, Matrix.of_apply, localBlock, Matrix.of_apply] using! h
  ext p q
  simp only [localBlock, covarianceInBasis, Matrix.of_apply]
  rw [majoranaInBasis_frameRotation_local i j hij A p,
    majoranaInBasis_frameRotation_local i j hij A q]
  change localCovarianceInBasis M i j (localRotation A) p q = _
  exact hloc p q

/-- For distinct modes, the frame rotation satisfies `frameRotation i j A * (frameRotation i j
A).transpose = 1`. -/
theorem frameRotation_mul_transpose {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    frameRotation i j A * (frameRotation i j A).transpose = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · have hz : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
          frameRotation i j A a c * frameRotation i j A b c = 0 := by
        intro c hc
        rw [frameRotation_apply_left_local_right_away i j A a c ha hc,
          frameRotation_apply_left_local_right_away i j A b c hb hc]
        simp
      have hsum := sum_localMajorana i j hij
        (fun c : Fin (2 * n) => frameRotation i j A a c * frameRotation i j A b c) hz
      rw [hsum]
      have hrewrite : ∀ p : Fin 4,
          frameRotation i j A a (localIndices i j p) * frameRotation i j A b (localIndices i j p)
            = (localRotation A) (localSlot i j a) p * (localRotation A) (localSlot i j b) p := by
        intro p
        rw [frameRotation_apply_local i j A a (localIndices i j p) ha
            (isLocalMajorana_localIndices i j p),
          frameRotation_apply_local i j A b (localIndices i j p) hb
            (isLocalMajorana_localIndices i j p),
          localSlot_localIndices i j hij p]
      calc (∑ p : Fin 4, frameRotation i j A a (localIndices i j p)
            * frameRotation i j A b (localIndices i j p))
          = ∑ p : Fin 4, (localRotation A) (localSlot i j a) p
            * (localRotation A) (localSlot i j b) p := by
              apply Finset.sum_congr rfl
              intro p hp
              exact hrewrite p
        _ = ((localRotation A) * (localRotation A).transpose) (localSlot i j a) (localSlot i j b) := by
              simp [Matrix.mul_apply, Matrix.transpose_apply]
        _ = (1 : Matrix (Fin 4) (Fin 4) ℝ) (localSlot i j a) (localSlot i j b) := by
              rw [localRotation_mul_transpose]
        _ = (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a b := by
              by_cases h : a = b
              · subst h
                simp
              · have h2 : localSlot i j a ≠ localSlot i j b := by
                  intro hh
                  exact h (localSlot_inj_local i j hij a b ha hb hh)
                simp [h2, h]
    · have hz : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
          frameRotation i j A a c * frameRotation i j A b c = 0 := by
        intro c hc
        rw [frameRotation_apply_left_local_right_away i j A a c ha hc]
        simp
      have hsum := sum_localMajorana i j hij
        (fun c : Fin (2 * n) => frameRotation i j A a c * frameRotation i j A b c) hz
      rw [hsum]
      calc (∑ p : Fin 4, frameRotation i j A a (localIndices i j p)
            * frameRotation i j A b (localIndices i j p))
          = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              rw [frameRotation_apply_right_local_left_away i j A b (localIndices i j p) hb
                  (isLocalMajorana_localIndices i j p)]
              simp
        _ = (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a b := by
              have hne : a ≠ b := by
                intro h
                exact hb (h ▸ ha)
              simp [hne]
  · by_cases hb : isLocalMajorana i j b
    · have hz : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
          frameRotation i j A a c * frameRotation i j A b c = 0 := by
        intro c hc
        rw [frameRotation_apply_left_local_right_away i j A b c hb hc]
        simp
      have hsum := sum_localMajorana i j hij
        (fun c : Fin (2 * n) => frameRotation i j A a c * frameRotation i j A b c) hz
      rw [hsum]
      calc (∑ p : Fin 4, frameRotation i j A a (localIndices i j p)
            * frameRotation i j A b (localIndices i j p))
          = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              rw [frameRotation_apply_right_local_left_away i j A a (localIndices i j p) ha
                  (isLocalMajorana_localIndices i j p)]
              simp
        _ = (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a b := by
              have hne : a ≠ b := by
                intro h
                exact ha (h ▸ hb)
              simp [hne]
    · have hzero : ∀ c : Fin (2 * n), c ≠ a →
          frameRotation i j A a c * frameRotation i j A b c = 0 := by
        intro c hc
        by_cases hcl : isLocalMajorana i j c
        · rw [frameRotation_apply_right_local_left_away i j A a c ha hcl]
          simp
        · rw [frameRotation_apply_away_neq i j A a c ha hcl hc.symm]
          simp
      have hconv : (if a = b then 1 else 0 : ℝ)
          = frameRotation i j A a a * frameRotation i j A b a := by
        by_cases h : a = b
        · rw [if_pos h, frameRotation_apply_away_eq i j A a ha]
          have h1 : frameRotation i j A b a = 1 := by
            rw [← h]
            exact frameRotation_apply_away_eq i j A a ha
          rw [h1, mul_one]
        · rw [if_neg h, frameRotation_apply_away_eq i j A a ha,
            frameRotation_apply_away_neq i j A b a hb ha (Ne.symm h), mul_zero]
      rw [hconv]
      refine Finset.sum_eq_single a ?_ ?_
      · intro c hc hne
        exact hzero c hne
      · intro h
        exact (h (Finset.mem_univ a)).elim

/-- Complex square matrices indexed by the occupation registers of `n` fermionic modes. -/
abbrev FermMat (n : ℕ) := Matrix (Reg n) (Reg n) ℂ

/-- Twice a fermionic register matrix equals its sum with itself. -/
lemma smul_two {n : ℕ} (M : FermMat n) : (2 : ℂ) • M = M + M := by
  ext i j; simp [Matrix.smul_apply, Matrix.add_apply]; ring

/-- Minus twice a fermionic register matrix equals the negative of its sum with itself. -/
lemma smul_neg_two {n : ℕ} (M : FermMat n) : (-2 : ℂ) • M = -(M + M) := by
  ext i j; simp [Matrix.smul_apply, Matrix.add_apply]; ring

/-- Every Majorana operator squares to the identity. -/
theorem majorana_sq (n : ℕ) (a : Fin (2 * n)) : majorana a * majorana a = (1 : FermMat n) := by
  have h := majorana_clifford n a a
  rw [if_pos rfl] at h
  rw [two_smul] at h
  have h2 : (majorana a * majorana a - (1 : FermMat n)) + (majorana a * majorana a - (1 : FermMat n)) = 0 := by
    calc (majorana a * majorana a - (1 : FermMat n)) + (majorana a * majorana a - (1 : FermMat n))
        = (majorana a * majorana a + majorana a * majorana a) - ((1 : FermMat n) + (1 : FermMat n)) := by abel
      _ = 0 := sub_eq_zero.mpr h
  exact sub_eq_zero.mp (add_self_eq_zero_of_complex _ h2)

/-- Majorana operators with distinct indices anticommute. -/
theorem majorana_anticommute (n : ℕ) (a b : Fin (2 * n)) (hab : a ≠ b) :
    majorana a * majorana b + majorana b * majorana a = 0 := by
  have h := majorana_clifford n a b
  rw [if_neg hab] at h
  simpa using! h

/-- For distinct indices, the commutator of a Majorana pair with its first factor is minus twice
its second factor. -/
theorem majorana_comm_left (n : ℕ) (a b : Fin (2 * n)) (hab : a ≠ b) :
    majorana a * majorana b * majorana a - majorana a * majorana a * majorana b
      = (-2 : ℂ) • majorana b := by
  have hanti := majorana_anticommute n a b hab
  have hsq := majorana_sq n a
  have hone : (1 : FermMat n) * majorana b = majorana b := Matrix.one_mul _
  have h2 : majorana a * (majorana a * majorana b) = majorana b := by
    calc majorana a * (majorana a * majorana b)
        = (majorana a * majorana a) * majorana b := (Matrix.mul_assoc _ _ _).symm
      _ = ((1 : FermMat n) * majorana b) := congrArg (fun X : FermMat n => X * majorana b) hsq
      _ = majorana b := hone
  have e : majorana a * (majorana b * majorana a)
      = majorana a * (-(majorana a * majorana b)) :=
    congrArg (fun X : FermMat n => majorana a * X) (eq_neg_of_add_eq_zero_right hanti)
  calc majorana a * majorana b * majorana a - majorana a * majorana a * majorana b
      = majorana a * (majorana b * majorana a) - majorana a * (majorana a * majorana b) := by
        noncomm_ring
    _ = majorana a * (-(majorana a * majorana b)) - majorana a * (majorana a * majorana b) := by
        exact congrArg (fun X : FermMat n => X - majorana a * (majorana a * majorana b)) e
    _ = -(majorana a * (majorana a * majorana b)) - (majorana a * (majorana a * majorana b)) := by
        rw [Matrix.mul_neg]
    _ = -majorana b - majorana b := by rw [h2]
    _ = (-2 : ℂ) • majorana b := by rw [smul_neg_two, neg_add, sub_eq_add_neg]

/-- For distinct indices, the commutator of a Majorana pair with its second factor is twice its
first factor. -/
theorem majorana_comm_right (n : ℕ) (a b : Fin (2 * n)) (hab : a ≠ b) :
    majorana a * majorana b * majorana b - majorana b * majorana a * majorana b
      = (2 : ℂ) • majorana a := by
  have hanti := majorana_anticommute n a b hab
  have hsq := majorana_sq n b
  have hone : majorana a * (1 : FermMat n) = majorana a := Matrix.mul_one _
  have h3 : (majorana a * majorana b) * majorana b = majorana a := by
    calc (majorana a * majorana b) * majorana b
        = majorana a * (majorana b * majorana b) := Matrix.mul_assoc _ _ _
      _ = majorana a * (1 : FermMat n) := congrArg (fun X : FermMat n => majorana a * X) hsq
      _ = majorana a := hone
  have h2 : majorana a * (majorana b * majorana b) = majorana a := by
    calc majorana a * (majorana b * majorana b)
        = (majorana a * majorana b) * majorana b := (Matrix.mul_assoc _ _ _).symm
      _ = majorana a := h3
  have e : (majorana b * majorana a) * majorana b
      = (-(majorana a * majorana b)) * majorana b :=
    congrArg (fun X : FermMat n => X * majorana b) (eq_neg_of_add_eq_zero_right hanti)
  calc majorana a * majorana b * majorana b - majorana b * majorana a * majorana b
      = majorana a * (majorana b * majorana b) - (majorana b * majorana a) * majorana b := by
        noncomm_ring
    _ = majorana a * (majorana b * majorana b) - (-(majorana a * majorana b)) * majorana b := by
        exact congrArg (fun X : FermMat n => majorana a * (majorana b * majorana b) - X) e
    _ = majorana a * (majorana b * majorana b) + (majorana a * majorana b) * majorana b := by
        rw [neg_mul, sub_eq_add_neg, neg_neg]
    _ = majorana a + majorana a := by rw [h2, h3]
    _ = (2 : ℂ) • majorana a := by rw [smul_two]

/-- A product of two Majorana operators commutes with a third Majorana whose index differs from
both. -/
theorem majorana_comm_third (n : ℕ) (a b c : Fin (2 * n)) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    majorana a * majorana b * majorana c = majorana c * majorana a * majorana b := by
  have e1 : majorana b * majorana c = -(majorana c * majorana b) :=
    eq_neg_of_add_eq_zero_left (majorana_anticommute n b c hbc)
  have e2 : majorana a * majorana c = -(majorana c * majorana a) :=
    eq_neg_of_add_eq_zero_left (majorana_anticommute n a c hac)
  have f1 : majorana a * (majorana b * majorana c)
      = majorana a * (-(majorana c * majorana b)) := congrArg (fun X : FermMat n => majorana a * X) e1
  have f2 : (majorana a * majorana c) * majorana b
      = (-(majorana c * majorana a)) * majorana b := congrArg (fun X : FermMat n => X * majorana b) e2
  calc majorana a * majorana b * majorana c
      = majorana a * (majorana b * majorana c) := by noncomm_ring
    _ = majorana a * (-(majorana c * majorana b)) := by rw [f1]
    _ = -(majorana a * (majorana c * majorana b)) := by rw [Matrix.mul_neg]
    _ = -((majorana a * majorana c) * majorana b) := by rw [← Matrix.mul_assoc]
    _ = -((-(majorana c * majorana a)) * majorana b) := by rw [f2]
    _ = (majorana c * majorana a) * majorana b := by simp only [neg_mul, neg_neg]

/-- The commutator of a distinct Majorana pair with another Majorana is minus twice the second
factor, twice the first factor, or zero according to its index. -/
theorem majoranaPair_comm {n : ℕ} (a b c : Fin (2 * n)) (hab : a ≠ b) :
    majorana a * majorana b * majorana c - majorana c * majorana a * majorana b
      = if c = a then (-2 : ℂ) • majorana b
        else if c = b then (2 : ℂ) • majorana a
        else 0 := by
  by_cases hca : c = a
  · rw [if_pos hca, hca]
    exact majorana_comm_left n a b hab
  · by_cases hcb : c = b
    · rw [if_neg hca, if_pos hcb, hcb]
      exact majorana_comm_right n a b hab
    · rw [if_neg hca, if_neg hcb]
      have h1 : majorana a * majorana b * majorana c = majorana c * majorana a * majorana b :=
        majorana_comm_third n a b c hab (Ne.symm hcb) (Ne.symm hca)
      rw [h1]
      simp

/-- A complex number with zero real part equals its imaginary part times `I`. -/
theorem of_re_zero_eq (z : ℂ) (hz : z.re = 0) : z = z.im * Complex.I := by
  have h := Complex.re_add_im z
  rw [hz] at h
  simp only [Complex.ofReal_zero, zero_add] at h
  exact h.symm

/-- Complex conjugation fixes the real part and negates the imaginary part. -/
theorem conj_eq (z : ℂ) : star z = z.re - z.im * Complex.I := by
  apply Complex.ext
  · rw [RCLike.star_def, Complex.conj_re]
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  · rw [RCLike.star_def, Complex.conj_im]
    simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- For a skew-Hermitian two-by-two matrix, the lower off-diagonal entry is minus the conjugate
of the upper off-diagonal entry. -/
theorem hA_10 {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) : A 1 0 = -star (A 0 1) := by
  have h := congrArg (fun M => M 1 0) hA
  have h' : star (A 0 1) = -(A 1 0) := by
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h2 := congrArg Neg.neg h'.symm
  simpa using! h2

/-- The first diagonal entry of a skew-Hermitian two-by-two matrix has zero real part. -/
theorem hA_re_00 {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) : (A 0 0).re = 0 := by
  have h := congrArg (fun M => M 0 0) hA
  have h' : star (A 0 0) = -(A 0 0) := by
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h2 := congrArg Complex.re h'
  rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h2
  linarith

/-- The second diagonal entry of a skew-Hermitian two-by-two matrix has zero real part. -/
theorem hA_re_11 {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) : (A 1 1).re = 0 := by
  have h := congrArg (fun M => M 1 1) hA
  have h' : star (A 1 1) = -(A 1 1) := by
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h2 := congrArg Complex.re h'
  rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h2
  linarith

/-- For skew-Hermitian `A`, the coefficient `(A 0 1 - A 1 0) / 4` equals half the real part of
`A 0 1`. -/
theorem coeff_cross {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) :
    (A 0 1 - A 1 0) / 4 = Complex.ofReal ((A 0 1).re / 2) := by
  have h10 := hA_10 hA
  have hkey : A 0 1 - A 1 0 = 2 * Complex.ofReal ((A 0 1).re) := by
    rw [h10, conj_eq (A 0 1)]
    apply Complex.ext
    · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re] <;> ring
    · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_im] <;> ring
  rw [hkey, Complex.ofReal_div]
  push_cast
  ring

/-- For skew-Hermitian `A`, the coefficient `-I * (A 0 1 + A 1 0) / 4` equals half the imaginary
part of `A 0 1`. -/
theorem coeff_mixed {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) :
    -(Complex.I) * (A 0 1 + A 1 0) / 4 = Complex.ofReal ((A 0 1).im / 2) := by
  have h10 := hA_10 hA
  have hre : (A 0 1 + A 1 0).re = 0 := by
    rw [h10, conj_eq (A 0 1)]
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
      Complex.I_re, Complex.I_im] <;> ring
  have him : (A 0 1 + A 1 0).im = 2 * (A 0 1).im := by
    rw [h10, conj_eq (A 0 1)]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im] <;> ring
  have hz := of_re_zero_eq (A 0 1 + A 1 0) hre
  rw [hz]
  have hkey : (A 0 1 + A 1 0).im = 2 * (A 0 1).im := him
  rw [hkey]
  apply Complex.ext
  · simp [Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im] <;> ring
  · simp [Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring

/-- The Majorana operator at within-mode index zero equals the even Majorana operator. -/
theorem majorana_even_index {n : ℕ} (i : Fin n) :
    majorana (majoranaIndices i 0) = majoranaEven i := by
  have h : majoranaIndices i 0 = ⟨2 * i.val, by omega⟩ := by
    apply Fin.ext
    simp [majoranaIndices]
  rw [h, majorana_even_eq]

/-- The Majorana operator at within-mode index one equals the odd Majorana operator. -/
theorem majorana_odd_index {n : ℕ} (i : Fin n) :
    majorana (majoranaIndices i 1) = majoranaOdd i := by
  have h : majoranaIndices i 1 = ⟨2 * i.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [majoranaIndices]
  rw [h, majorana_odd_eq]

/-- For a complex number with zero real part, `-I * z / 2` is the real embedding of half its
imaginary part. -/
theorem negI_mul (z : ℂ) (hz : z.re = 0) :
    -(Complex.I) * z / 2 = Complex.ofReal (z.im / 2) := by
  have hid := of_re_zero_eq z hz
  rw [hid]
  apply Complex.ext
  · simp [Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im] <;> ring
  · simp [Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring

/-- For skew-Hermitian `A`, `-I * A 0 0 / 2` is the real embedding of half the imaginary part of
its first diagonal entry. -/
theorem coeff_diag_00 {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) :
    -(Complex.I) * A 0 0 / 2 = Complex.ofReal ((A 0 0).im / 2) :=
  negI_mul _ (hA_re_00 hA)

/-- For skew-Hermitian `A`, `-I * A 1 1 / 2` is the real embedding of half the imaginary part of
its second diagonal entry. -/
theorem coeff_diag_11 {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) :
    -(Complex.I) * A 1 1 / 2 = Complex.ofReal ((A 1 1).im / 2) :=
  negI_mul _ (hA_re_11 hA)

/-- Multiplying the complex embedding of a real number by minus one gives the embedding of its
negative. -/
theorem ofReal_neg_one_mul {r : ℝ} :
    (-1 : ℂ) • Complex.ofReal r = Complex.ofReal (-r) := by
  rw [neg_smul, one_smul, ← Complex.ofReal_neg]

/-- Multiplying the complex embedding of a real number by two gives the embedding of twice that
number. -/
theorem ofReal_mul_two {r : ℝ} :
    Complex.ofReal r * (2 : ℂ) = Complex.ofReal (2 * r) := by
  have h : Complex.ofReal (2 * r) = Complex.ofReal 2 * Complex.ofReal r := by
    rw [← Complex.ofReal_mul]
  have h2 : Complex.ofReal 2 = (2 : ℂ) := by norm_num
  rw [h, h2]
  ring

/-- Multiplying the complex embedding of a real number by minus two gives the embedding of minus
twice that number. -/
theorem ofReal_mul_neg_two {r : ℝ} :
    Complex.ofReal r * (-2 : ℂ) = Complex.ofReal (-2 * r) := by
  have h : Complex.ofReal (-2 * r) = Complex.ofReal (-2) * Complex.ofReal r := by
    rw [← Complex.ofReal_mul]
  have h2 : Complex.ofReal (-2) = (-2 : ℂ) := by norm_num
  rw [h, h2]
  ring

/-- The matrix commutator distributes over addition in its first argument. -/
theorem comm_add {n : ℕ} (X Y Z : FermMat n) :
    (X + Y) * Z - Z * (X + Y) = (X * Z - Z * X) + (Y * Z - Z * Y) := by
  rw [Matrix.add_mul, Matrix.mul_add]
  abel

/-- A complex scalar in the first argument factors out of the matrix commutator. -/
theorem comm_smul {n : ℕ} (c : ℂ) (X Y : FermMat n) :
    (c • X) * Y - Y * (c • X) = c • (X * Y - Y * X) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- Majorana indices from distinct modes are distinct for every choice of within-mode bits. -/
theorem localIndices_ne_ij {n : ℕ} (i j : Fin n) (hij : i ≠ j) (b c : Fin 2) :
    majoranaIndices i b ≠ majoranaIndices j c := by
  intro h
  have h2 := (majoranaIndices_eq i j b c).mp h
  omega

/-- Successive complex scalar multiplications of a register matrix combine into multiplication
of the scalars. -/
theorem smul_smul_matrix {n : ℕ} (a b : ℂ) (M : FermMat n) :
    a • (b • M) = (a * b) • M := by
  ext i j
  simp [Matrix.smul_apply]
  ring

/-- For distinct modes and skew-Hermitian coefficients, the quadratic generator is a scalar
identity term plus six Majorana products with explicit real coefficients. -/
theorem quadraticGenerator_eq_localForm {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    quadraticGenerator i j A
      = ((A 0 0 + A 1 1) / 2) • (1 : FermMat n)
        + Complex.ofReal ((A 0 0).im / 2)
            • (majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1))
        + Complex.ofReal ((A 0 1).re / 2)
            • (majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0))
        + Complex.ofReal ((A 0 1).im / 2)
            • (majorana (majoranaIndices i 0) * majorana (majoranaIndices j 1))
        + Complex.ofReal (-((A 0 1).im / 2))
            • (majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0))
        + Complex.ofReal ((A 0 1).re / 2)
            • (majorana (majoranaIndices i 1) * majorana (majoranaIndices j 1))
        + Complex.ofReal ((A 1 1).im / 2)
            • (majorana (majoranaIndices j 0) * majorana (majoranaIndices j 1)) := by
  have h00 := coeff_diag_00 hA
  have h11 := coeff_diag_11 hA
  have hcr := coeff_cross hA
  have hmx := coeff_mixed hA
  rw [quadraticGenerator_eq_majoranaForm i j hij A]
  simp only [majorana_even_index i, majorana_odd_index i, majorana_even_index j,
      majorana_odd_index j]
  rw [h00, h11, hcr, hmx]
  rw [smul_add, smul_sub]
  rw [sub_eq_add_neg, ← neg_smul, ← Complex.ofReal_neg]
  abel

/-- For distinct modes and skew-Hermitian coefficients, the generator commutator with the even
Majorana of `i` is the displayed combination of the other three local Majoranas. -/
theorem generator_comm_even_even {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    quadraticGenerator i j A * (majorana (majoranaIndices i 0))
        - (majorana (majoranaIndices i 0)) * quadraticGenerator i j A
      = Complex.ofReal (-2 * localFormSym A 0 1)
            • (majorana (majoranaIndices i 1))
        + Complex.ofReal (-2 * localFormSym A 0 2)
            • (majorana (majoranaIndices j 0))
        + Complex.ofReal (-2 * localFormSym A 0 3)
            • (majorana (majoranaIndices j 1)) := by
  have hne1 : majoranaIndices i 0 ≠ majoranaIndices i 1 := majoranaIndices_ne i 0 1 (by decide)
  have hne2 : majoranaIndices i 0 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 0 0
  have hne3 : majoranaIndices i 0 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 0 1
  have hne4 : majoranaIndices j 0 ≠ majoranaIndices i 0 := (localIndices_ne_ij i j hij 0 0).symm
  have hne5 : majoranaIndices j 1 ≠ majoranaIndices i 0 := (localIndices_ne_ij i j hij 0 1).symm
  have hne6 : majoranaIndices j 0 ≠ majoranaIndices j 1 := majoranaIndices_ne j 0 1 (by decide)
  have hne8 : majoranaIndices i 1 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 1 0
  have hne9 : majoranaIndices i 1 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 1 1
  have hne12 : majoranaIndices i 1 ≠ majoranaIndices i 0 :=
      (majoranaIndices_ne i 0 1 (by decide)).symm
  have c01 : majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices i 0)
      - majorana (majoranaIndices i 0) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices i 1)
      = (-2 : ℂ) • majorana (majoranaIndices i 1) :=
    majorana_comm_left n (majoranaIndices i 0) (majoranaIndices i 1) hne1
  have c02 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices i 0)
      - majorana (majoranaIndices i 0) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 0)
      = (-2 : ℂ) • majorana (majoranaIndices j 0) :=
    majorana_comm_left n (majoranaIndices i 0) (majoranaIndices j 0) hne2
  have c03 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices i 0)
      - majorana (majoranaIndices i 0) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 1)
      = (-2 : ℂ) • majorana (majoranaIndices j 1) :=
    majorana_comm_left n (majoranaIndices i 0) (majoranaIndices j 1) hne3
  have c04 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices i 0)
      = majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 0) :=
    majorana_comm_third n (majoranaIndices i 1) (majoranaIndices j 0) (majoranaIndices i 0)
      hne8 hne4 hne12
  have c05 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices i 0)
      = majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 1) :=
    majorana_comm_third n (majoranaIndices i 1) (majoranaIndices j 1) (majoranaIndices i 0)
      hne9 hne5 hne12
  have c06 : majorana (majoranaIndices j 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices i 0)
      = majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 1) :=
    majorana_comm_third n (majoranaIndices j 0) (majoranaIndices j 1) (majoranaIndices i 0)
      hne6 hne5 hne4
  rw [quadraticGenerator_eq_localForm i j hij A hA]
  simp only [comm_add, comm_smul, ← Matrix.mul_assoc]
  rw [c01, c02, c03, c04, c05, c06]
  simp only [smul_smul_matrix]
  rw [ofReal_mul_neg_two, ofReal_mul_neg_two, ofReal_mul_neg_two]
  simp [localFormSym, Matrix.of_apply]

/-- For distinct modes and skew-Hermitian coefficients, the generator commutator with the odd
Majorana of `i` is the displayed combination of the other three local Majoranas. -/
theorem generator_comm_odd_even {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    quadraticGenerator i j A * (majorana (majoranaIndices i 1))
        - (majorana (majoranaIndices i 1)) * quadraticGenerator i j A
      = Complex.ofReal (2 * localFormSym A 0 1) • (majorana (majoranaIndices i 0))
        + Complex.ofReal (-2 * localFormSym A 1 2) • (majorana (majoranaIndices j 0))
        + Complex.ofReal (-2 * localFormSym A 1 3) • (majorana (majoranaIndices j 1)) := by
  have hne1 : majoranaIndices i 0 ≠ majoranaIndices i 1 := majoranaIndices_ne i 0 1 (by decide)
  have hne2 : majoranaIndices i 0 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 0 0
  have hne3 : majoranaIndices i 0 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 0 1
  have hne6 : majoranaIndices j 0 ≠ majoranaIndices j 1 := majoranaIndices_ne j 0 1 (by decide)
  have hne8 : majoranaIndices i 1 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 1 0
  have hne9 : majoranaIndices i 1 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 1 1
  have hne13 : majoranaIndices j 1 ≠ majoranaIndices i 1 := (localIndices_ne_ij i j hij 1 1).symm
  have hne14 : majoranaIndices j 0 ≠ majoranaIndices i 1 := (localIndices_ne_ij i j hij 1 0).symm
  have c01 : majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices i 1)
      - majorana (majoranaIndices i 1) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices i 1)
      = (2 : ℂ) • majorana (majoranaIndices i 0) :=
    majorana_comm_right n (majoranaIndices i 0) (majoranaIndices i 1) hne1
  have c02 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices i 1)
      = majorana (majoranaIndices i 1) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 0) :=
    majorana_comm_third n (majoranaIndices i 0) (majoranaIndices j 0) (majoranaIndices i 1)
      hne2 hne14 hne1
  have c03 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices i 1)
      = majorana (majoranaIndices i 1) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 1) :=
    majorana_comm_third n (majoranaIndices i 0) (majoranaIndices j 1) (majoranaIndices i 1)
      hne3 hne13 hne1
  have c04 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices i 1)
      - majorana (majoranaIndices i 1) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 0)
      = (-2 : ℂ) • majorana (majoranaIndices j 0) :=
    majorana_comm_left n (majoranaIndices i 1) (majoranaIndices j 0) hne8
  have c05 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices i 1)
      - majorana (majoranaIndices i 1) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 1)
      = (-2 : ℂ) • majorana (majoranaIndices j 1) :=
    majorana_comm_left n (majoranaIndices i 1) (majoranaIndices j 1) hne9
  have c06 : majorana (majoranaIndices j 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices i 1)
      = majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 1) :=
    majorana_comm_third n (majoranaIndices j 0) (majoranaIndices j 1) (majoranaIndices i 1)
      hne6 hne13 hne14
  rw [quadraticGenerator_eq_localForm i j hij A hA]
  simp only [comm_add, comm_smul, ← Matrix.mul_assoc]
  rw [c01, c02, c03, c04, c05, c06]
  simp only [smul_smul_matrix]
  rw [ofReal_mul_two, ofReal_mul_neg_two, ofReal_mul_neg_two]
  simp only [Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero, add_zero, zero_add]
  obtain ⟨h01, _, _, h13, _, h12⟩ := localFormSym_apply A
  rw [h01, h12, h13]

/-- For distinct modes and skew-Hermitian coefficients, the generator commutator with the even
Majorana of `j` is the displayed combination of the other three local Majoranas. -/
theorem generator_comm_even_j {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    quadraticGenerator i j A * (majorana (majoranaIndices j 0))
        - (majorana (majoranaIndices j 0)) * quadraticGenerator i j A
      = Complex.ofReal (2 * localFormSym A 0 2) • (majorana (majoranaIndices i 0))
        + Complex.ofReal (2 * localFormSym A 1 2) • (majorana (majoranaIndices i 1))
        + Complex.ofReal (-2 * localFormSym A 2 3) • (majorana (majoranaIndices j 1)) := by
  have hne1 : majoranaIndices i 0 ≠ majoranaIndices i 1 := majoranaIndices_ne i 0 1 (by decide)
  have hne2 : majoranaIndices i 0 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 0 0
  have hne3 : majoranaIndices i 0 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 0 1
  have hne6 : majoranaIndices j 0 ≠ majoranaIndices j 1 := majoranaIndices_ne j 0 1 (by decide)
  have hne8 : majoranaIndices i 1 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 1 0
  have hne9 : majoranaIndices i 1 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 1 1
  have hne15 : majoranaIndices j 1 ≠ majoranaIndices j 0 :=
      (majoranaIndices_ne j 0 1 (by decide)).symm
  have c01 : majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 0)
      = majorana (majoranaIndices j 0) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices i 1) :=
    majorana_comm_third n (majoranaIndices i 0) (majoranaIndices i 1) (majoranaIndices j 0)
      hne1 hne8 hne2
  have c02 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 0)
      - majorana (majoranaIndices j 0) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 0)
      = (2 : ℂ) • majorana (majoranaIndices i 0) :=
    majorana_comm_right n (majoranaIndices i 0) (majoranaIndices j 0) hne2
  have c03 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices j 0)
      = majorana (majoranaIndices j 0) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 1) :=
    majorana_comm_third n (majoranaIndices i 0) (majoranaIndices j 1) (majoranaIndices j 0)
      hne3 hne15 hne2
  have c04 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 0)
      - majorana (majoranaIndices j 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 0)
      = (2 : ℂ) • majorana (majoranaIndices i 1) :=
    majorana_comm_right n (majoranaIndices i 1) (majoranaIndices j 0) hne8
  have c05 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices j 0)
      = majorana (majoranaIndices j 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 1) :=
    majorana_comm_third n (majoranaIndices i 1) (majoranaIndices j 1) (majoranaIndices j 0)
      hne9 hne15 hne8
  have c06 : majorana (majoranaIndices j 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices j 0)
      - majorana (majoranaIndices j 0) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 1)
      = (-2 : ℂ) • majorana (majoranaIndices j 1) :=
    majorana_comm_left n (majoranaIndices j 0) (majoranaIndices j 1) hne6
  rw [quadraticGenerator_eq_localForm i j hij A hA]
  simp only [comm_add, comm_smul, ← Matrix.mul_assoc]
  rw [c01, c02, c03, c04, c05, c06]
  simp only [smul_smul_matrix]
  rw [ofReal_mul_two, ofReal_mul_two, ofReal_mul_neg_two]
  simp only [Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero, add_zero, zero_add]
  obtain ⟨_, h23, h02, _, _, h12⟩ := localFormSym_apply A
  rw [h23, h02, h12]

/-- For distinct modes and skew-Hermitian coefficients, the generator commutator with the odd
Majorana of `j` is the displayed combination of the other three local Majoranas. -/
theorem generator_comm_odd_j {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    quadraticGenerator i j A * (majorana (majoranaIndices j 1))
        - (majorana (majoranaIndices j 1)) * quadraticGenerator i j A
      = Complex.ofReal (2 * localFormSym A 0 3) • (majorana (majoranaIndices i 0))
        + Complex.ofReal (2 * localFormSym A 1 3) • (majorana (majoranaIndices i 1))
        + Complex.ofReal (2 * localFormSym A 2 3) • (majorana (majoranaIndices j 0)) := by
  have hne1 : majoranaIndices i 0 ≠ majoranaIndices i 1 := majoranaIndices_ne i 0 1 (by decide)
  have hne2 : majoranaIndices i 0 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 0 0
  have hne3 : majoranaIndices i 0 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 0 1
  have hne6 : majoranaIndices j 0 ≠ majoranaIndices j 1 := majoranaIndices_ne j 0 1 (by decide)
  have hne8 : majoranaIndices i 1 ≠ majoranaIndices j 0 := localIndices_ne_ij i j hij 1 0
  have hne9 : majoranaIndices i 1 ≠ majoranaIndices j 1 := localIndices_ne_ij i j hij 1 1
  have c01 : majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 1)
      = majorana (majoranaIndices j 1) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices i 1) :=
    majorana_comm_third n (majoranaIndices i 0) (majoranaIndices i 1) (majoranaIndices j 1)
      hne1 hne9 hne3
  have c02 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 1)
      = majorana (majoranaIndices j 1) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 0) :=
    majorana_comm_third n (majoranaIndices i 0) (majoranaIndices j 0) (majoranaIndices j 1)
      hne2 hne6 hne3
  have c03 : majorana (majoranaIndices i 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices j 1)
      - majorana (majoranaIndices j 1) * majorana (majoranaIndices i 0)
        * majorana (majoranaIndices j 1)
      = (2 : ℂ) • majorana (majoranaIndices i 0) :=
    majorana_comm_right n (majoranaIndices i 0) (majoranaIndices j 1) hne3
  have c04 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 1)
      = majorana (majoranaIndices j 1) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 0) :=
    majorana_comm_third n (majoranaIndices i 1) (majoranaIndices j 0) (majoranaIndices j 1)
      hne8 hne6 hne9
  have c05 : majorana (majoranaIndices i 1) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices j 1)
      - majorana (majoranaIndices j 1) * majorana (majoranaIndices i 1)
        * majorana (majoranaIndices j 1)
      = (2 : ℂ) • majorana (majoranaIndices i 1) :=
    majorana_comm_right n (majoranaIndices i 1) (majoranaIndices j 1) hne9
  have c06 : majorana (majoranaIndices j 0) * majorana (majoranaIndices j 1)
        * majorana (majoranaIndices j 1)
      - majorana (majoranaIndices j 1) * majorana (majoranaIndices j 0)
        * majorana (majoranaIndices j 1)
      = (2 : ℂ) • majorana (majoranaIndices j 0) :=
    majorana_comm_right n (majoranaIndices j 0) (majoranaIndices j 1) hne6
  rw [quadraticGenerator_eq_localForm i j hij A hA]
  simp only [comm_add, comm_smul, ← Matrix.mul_assoc]
  rw [c01, c02, c03, c04, c05, c06]
  simp only [smul_smul_matrix]
  rw [ofReal_mul_two, ofReal_mul_two, ofReal_mul_two]
  simp only [Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero, add_zero, zero_add]
  obtain ⟨_, h23, _, h13, h03, _⟩ := localFormSym_apply A
  rw [h23, h13, h03]

/-- Collects classical cost bounds, local covariance updates, Majorana Clifford relations, and
conditional covariance congruences, together with local generator and frame-rotation
identities. -/
theorem clause3_endpoint_partial :
    (∀ (n : ℕ) (gl : MatchGateCircuit n),
      matchGateCircuitClassicalOps gl ≤ 64 * matchGateCount gl)
      ∧ (∀ (n : ℕ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n)
        (R : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin (2 * n)),
        ¬ isLocalMajorana i j a → ¬ isLocalMajorana i j b →
          covarianceUpdate Γ i j R a b = Γ a b)
      ∧ (∀ (n : ℕ) (i : Fin n) (b c : Fin 2), b ≠ c →
          majoranaIndices i b ≠ majoranaIndices i c)
      ∧ (∀ (n : ℕ), (linearConnectivity n).length = n - 1)
      ∧ (∀ (n : ℕ) (h : 0 < n), (ringConnectivity n).length = n)
      ∧ (∀ (n : ℕ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n)
        (R : Matrix (Fin 4) (Fin 4) ℝ) (hij : i ≠ j),
          localBlock (covarianceUpdate Γ i j R) i j = R * localBlock Γ i j * R.transpose)
      ∧ (∀ (m : ℕ), determinantOpCost m ≤ m ^ 3)
      ∧ (∀ (m : ℕ), pfaffianOpCost m ≤ (2 * m) ^ 3)
      ∧ (∀ (n : ℕ) (i : Fin n), (numberOp i)ᴴ = numberOp i)
      ∧ (∀ (n : ℕ) (i j : Fin n),
        (creation i * annihilation j)ᴴ = creation j * annihilation i)
      ∧ (∀ (n : ℕ) (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ),
        (quadraticGenerator i j A)ᴴ
          = (star (A 0 0)) • (numberOp i)
            + (star (A 0 1)) • (creation j * annihilation i)
            + (star (A 1 0)) • (creation i * annihilation j)
            + (star (A 1 1)) • (numberOp j))
      ∧ (∀ (n : ℕ) (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A),
        (quadraticGenerator i j A)ᴴ = -quadraticGenerator i j A)
      ∧ (∀ (n : ℕ) (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A),
        matchGate i j A ∈ Matrix.unitaryGroup (Reg n) ℂ)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (a b : Fin (2 * n)),
        covarianceMatrix M b a = -covarianceMatrix M a b)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (p q : Fin 4),
        localBlock (covarianceMatrix M) i j q p = -localBlock (covarianceMatrix M) i j p q)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ),
        covarianceInBasis M S = S * covarianceMatrix M * S.transpose)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ),
        localCovarianceInBasis M i j R = R * localBlock (covarianceMatrix M) i j * R.transpose)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
          (hij : i ≠ j),
        localBlock (covarianceUpdate (covarianceMatrix M) i j R) i j = localCovarianceInBasis M i j R)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
          (a b : Fin (2 * n)),
        covarianceInBasis M S b a = -covarianceInBasis M S a b)
      ∧ (∀ (n : ℕ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
          (hij : i ≠ j) (p q : Fin 4),
        (∀ s t : Fin 4, localBlock Γ i j t s = -localBlock Γ i j s t) →
          localBlock (covarianceUpdate Γ i j R) i j q p
            = -localBlock (covarianceUpdate Γ i j R) i j p q)
      ∧ (∀ (n : ℕ) (Γ Γ' : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ),
        Γ = Γ' → covarianceUpdate Γ i j R = covarianceUpdate Γ' i j R)
      ∧ (∀ (n : ℕ) (k : Fin n), majoranaEven k * majoranaEven k = 1)
      ∧ (∀ (n : ℕ) (k l : Fin n) (hkl : k ≠ l),
        majoranaEven k * majoranaEven l + majoranaEven l * majoranaEven k = 0)
      ∧ (∀ (n : ℕ) (k : Fin n), majorana ⟨2 * k.val, by omega⟩ = majoranaEven k)
      ∧ (∀ (n : ℕ) (k : Fin n), majorana ⟨2 * k.val + 1, by omega⟩ = majoranaOdd k)
      ∧ (∀ (n : ℕ) (k : Fin n), majorana (majoranaIndices k 0) = majoranaEven k)
      ∧ (∀ (n : ℕ) (k : Fin n), majorana (majoranaIndices k 1) = majoranaOdd k)
      ∧ (∀ (n : ℕ) (k : Fin n),
        majoranaEven k * majoranaOdd k = Complex.I • (numberOp k + numberOp k - 1))
      ∧ (∀ (n : ℕ) (k : Fin n),
        majoranaOdd k * majoranaEven k = Complex.I • (1 - numberOp k - numberOp k))
      ∧ (∀ (n : ℕ) (k : Fin n), majoranaOdd k * majoranaOdd k = 1)
      ∧ (∀ (n : ℕ) (k l : Fin n) (hkl : k ≠ l),
        majoranaOdd k * majoranaOdd l + majoranaOdd l * majoranaOdd k = 0)
      ∧ (∀ (n : ℕ) (k l : Fin n) (hkl : k ≠ l),
        majoranaEven k * majoranaOdd l + majoranaOdd l * majoranaEven k = 0)
      ∧ (∀ (n : ℕ) (k : Fin n),
        majoranaEven k * majoranaOdd k + majoranaOdd k * majoranaEven k = 0)
      ∧ (∀ (n : ℕ) (a b : Fin (2 * n)),
        majorana a * majorana b + majorana b * majorana a
          = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ))
      ∧ (∀ (n : ℕ) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (a b : Fin (2 * n)),
        majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
          = ((2 * gramMatrix S a b : ℝ) : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ))
      ∧ (∀ (n : ℕ) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
          (hS : S * S.transpose = 1) (a b : Fin (2 * n)),
        majoranaInBasis S a * majoranaInBasis S b + majoranaInBasis S b * majoranaInBasis S a
          = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ))
      ∧ (∀ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (R : Matrix (Fin 4) (Fin 4) ℝ)
          (hR : R * R.transpose = 1) (p q : Fin 4),
        localMajoranaInBasis i j R p * localMajoranaInBasis i j R q
          + localMajoranaInBasis i j R q * localMajoranaInBasis i j R p
          = (if p = q then (2 : ℂ) else 0) • (1 : Matrix (Reg n) (Reg n) ℂ))
      ∧ (∀ (n : ℕ) (U M : Matrix (Reg n) (Reg n) ℂ)
          (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hU : U * Uᴴ = 1)
          (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a),
        covarianceMatrix (U * M) = S * covarianceMatrix M * S.transpose)
      ∧ (∀ (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) (hU : Uᴴ * U = 1)
          (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
          (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a),
        S * S.transpose = 1)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n),
        covarianceMatrix M (majoranaIndices k 0) (majoranaIndices k 1)
          = (Matrix.trace (Mᴴ * M)).re
            - 2 * (Matrix.trace (Mᴴ * (numberOp k) * M)).re)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n)
          (hM : (Matrix.trace (Mᴴ * M)).re = 1),
        occupationExpectation M k = occupationFromCovariance (covarianceMatrix M) k)
      ∧ (∀ (n : ℕ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (k : Fin n)
          (hlo : -1 ≤ Γ (majoranaIndices k 0) (majoranaIndices k 1))
          (hhi : Γ (majoranaIndices k 0) (majoranaIndices k 1) ≤ 1),
        0 ≤ occupationFromCovariance Γ k ∧ occupationFromCovariance Γ k ≤ 1)
      ∧ (∀ (n : ℕ) (k : Fin n) (h : 0 < n),
        occupationClassicalCost k < physicalMeasurementCost n)
      ∧ (∀ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ),
        quadraticGenerator i j A
          = ((A 0 0 + A 1 1) / 2) • 1
            + (-(Complex.I) * A 0 0 / 2) • (majoranaEven i * majoranaOdd i)
            + (-(Complex.I) * A 1 1 / 2) • (majoranaEven j * majoranaOdd j)
            + ((A 0 1 - A 1 0) / 4)
                • (majoranaEven i * majoranaEven j + majoranaOdd i * majoranaOdd j)
            + (-(Complex.I) * (A 0 1 + A 1 0) / 4)
                • (majoranaEven i * majoranaOdd j - majoranaOdd i * majoranaEven j))
      ∧ (∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A),
        ((-(Complex.I) * A 0 0 / 2 : ℂ).im : ℂ) = 0
          ∧ ((-(Complex.I) * A 1 1 / 2 : ℂ).im : ℂ) = 0
          ∧ (((A 0 1 - A 1 0) / 4 : ℂ).im : ℂ) = 0
          ∧ ((-(Complex.I) * (A 0 1 + A 1 0) / 4 : ℂ).im : ℂ) = 0)
      ∧ (∀ (A : Matrix (Fin 2) (Fin 2) ℂ),
        (localFormMatrix A).transpose = -(localFormMatrix A))
      ∧ (∀ (A : Matrix (Fin 2) (Fin 2) ℂ),
        localRotation A * (localRotation A).transpose = 1)
      ∧ (∀ (A : Matrix (Fin 2) (Fin 2) ℂ),
        localFormMatrix A 0 1 = (A 0 0).im / 2
          ∧ localFormMatrix A 2 3 = (A 1 1).im / 2
          ∧ localFormMatrix A 0 2 = (A 0 1).re / 2
          ∧ localFormMatrix A 1 3 = (A 0 1).re / 2
          ∧ localFormMatrix A 0 3 = (A 0 1).im / 2
          ∧ localFormMatrix A 1 2 = -(A 0 1).im / 2)
      ∧ (∀ (n : ℕ) (a : Fin (2 * n)), majoranaInBasis 1 a = majorana a)
      ∧ (∀ (n : ℕ) (U M : Matrix (Reg n) (Reg n) ℂ)
          (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hU : U * Uᴴ = 1)
          (hS : ∀ a : Fin (2 * n), Uᴴ * majorana a * U = majoranaInBasis S a) (k : Fin n),
        2 * occupationExpectation (U * M) k
          = (Matrix.trace (Mᴴ * M)).re
            - (S * covarianceMatrix M * S.transpose) (majoranaIndices k 0) (majoranaIndices k 1))
      ∧ (∀ (n : ℕ) (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A)
          (M : Matrix (Reg n) (Reg n) ℂ) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
          (hS : ∀ a : Fin (2 * n),
            (matchGate i j A)ᴴ * majorana a * (matchGate i j A) = majoranaInBasis S a),
        covarianceMatrix (matchGate i j A * M) = S * covarianceMatrix M * S.transpose)
      ∧ (∀ (n : ℕ) (gl : MatchGateCircuit n) (k : Fin n),
        matchGateCircuitClassicalOps gl + occupationClassicalCost k
          ≤ 64 * matchGateCount gl + 1)

      ∧ (∀ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ),
        frameRotation i j A * (frameRotation i j A).transpose = 1)
      ∧ (∀ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 4),
        majoranaInBasis (frameRotation i j A) (localIndices i j p)
          = localMajoranaInBasis i j (localRotation A) p)
      ∧ (∀ (n : ℕ) (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin (2 * n)),
        ¬ isLocalMajorana i j a → majoranaInBasis (frameRotation i j A) a = majorana a)
      ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i ≠ j)
          (A : Matrix (Fin 2) (Fin 2) ℂ),
        localBlock (covarianceInBasis M (frameRotation i j A)) i j
          = (localRotation A) * localBlock (covarianceMatrix M) i j * (localRotation A).transpose)
      ∧ (∀ (n : ℕ) (a b : Fin (2 * n)) (hab : a ≠ b),
        majorana a * majorana b * majorana a - majorana a * majorana a * majorana b
          = (-2 : ℂ) • majorana b)
      ∧ (∀ (n : ℕ) (a b : Fin (2 * n)) (hab : a ≠ b),
        majorana a * majorana b * majorana b - majorana b * majorana a * majorana b
          = (2 : ℂ) • majorana a)
      ∧ (∀ (n : ℕ) (a b c : Fin (2 * n)) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c),
        majorana a * majorana b * majorana c = majorana c * majorana a * majorana b)
      ∧ (∀ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ)
          (hA : Aᴴ = -A),
        quadraticGenerator i j A
          = ((A 0 0 + A 1 1) / 2) • (1 : FermMat n)
            + Complex.ofReal ((A 0 0).im / 2)
                • (majorana (majoranaIndices i 0) * majorana (majoranaIndices i 1))
            + Complex.ofReal ((A 0 1).re / 2)
                • (majorana (majoranaIndices i 0) * majorana (majoranaIndices j 0))
            + Complex.ofReal ((A 0 1).im / 2)
                • (majorana (majoranaIndices i 0) * majorana (majoranaIndices j 1))
            + Complex.ofReal (-((A 0 1).im / 2))
                • (majorana (majoranaIndices i 1) * majorana (majoranaIndices j 0))
            + Complex.ofReal ((A 0 1).re / 2)
                • (majorana (majoranaIndices i 1) * majorana (majoranaIndices j 1))
            + Complex.ofReal ((A 1 1).im / 2)
                • (majorana (majoranaIndices j 0) * majorana (majoranaIndices j 1)))
      ∧ (∀ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ)
          (hA : Aᴴ = -A),
        quadraticGenerator i j A * (majorana (majoranaIndices i 0))
            - (majorana (majoranaIndices i 0)) * quadraticGenerator i j A
          = Complex.ofReal (-2 * localFormSym A 0 1)
                • (majorana (majoranaIndices i 1))
            + Complex.ofReal (-2 * localFormSym A 0 2)
                • (majorana (majoranaIndices j 0))
            + Complex.ofReal (-2 * localFormSym A 0 3)
                • (majorana (majoranaIndices j 1))) :=
  ⟨fun n gl => matchGateCircuitClassicalOps_le gl,
   fun n Γ i j R a b ha hb => covarianceUpdate_eq_of_not_local Γ i j R a b ha hb,
   fun n i b c hbc => majoranaIndices_ne i b c hbc,
   fun n => length_linearConnectivity n,
   fun n h => length_ringConnectivity h,
   fun n Γ i j R hij => localBlock_covarianceUpdate Γ i j R hij,
   fun m => determinantOpCost_le m,
   fun m => pfaffianOpCost_le m,
   fun n i => numberOp_hermitian i,
   fun n i j => creation_mul_annihilation_conjTranspose i j,
   fun n i j A => quadraticGenerator_conjTranspose i j A,
   fun n i j A hA => quadraticGenerator_skewHermitian i j A hA,
   fun n i j A hA => matchGate_unitary i j A hA,
   fun n M a b => covarianceMatrix_antisymm M a b,
   fun n M i j p q => localBlock_covariance_antisymm M i j p q,
   fun n M S => covarianceInBasis_eq_congruence M S,
   fun n M i j R => localCovarianceInBasis_eq M i j R,
   fun n M i j R hij => covarianceUpdate_local_eq_rotatedBasis M i j R hij,
   fun n M S a b => covarianceInBasis_antisymm M S a b,
   fun n Γ i j R hij p q h => localBlock_covarianceUpdate_antisymm Γ i j R hij p q h,
   fun n Γ Γ' i j R h => covarianceUpdate_eq_of_covariance_eq h i j R,
   fun n k => majoranaEven_sq n k,
   fun n k l hkl => majoranaEven_anticommute n k l hkl,
   fun n k => majorana_even_eq n k,
   fun n k => majorana_odd_eq n k,
   fun n k => majoranaIndices_even n k,
   fun n k => majoranaIndices_odd n k,
   fun n k => majoranaEven_majoranaOdd (n := n) k,
   fun n k => majoranaOdd_majoranaEven (n := n) k,
   fun n k => majoranaOdd_sq k,
   fun n k l hkl => majoranaOdd_anticommute k l hkl,
   fun n k l hkl => majoranaEven_majoranaOdd_anticommute k l hkl,
   fun n k => majoranaEven_majoranaOdd_anticommute_same n k,
   fun n a b => majorana_clifford n a b,
   fun n S a b => majoranaInBasis_anticommutator_real S a b,
   fun n S hS a b => majoranaInBasis_clifford_of_orthogonal S hS a b,
   fun n i j hij R hR p q => localMajoranaInBasis_clifford_of_orthogonal i j hij R hR p q,
   fun n U M S hU hS => covarianceMatrix_congruence_of_induced U M S hU hS,
   fun n U hU S hS => induced_frame_orthogonal_of_unitary U hU S hS,
   fun n M k => covarianceMatrix_occupation M k,
   fun n M k hM => occupationExpectation_eq_occupationFromCovariance M k hM,
   fun n Γ k hlo hhi => occupationFromCovariance_bounds Γ k hlo hhi,
   fun n k h => occupationClassicalCost_lt_physical k h,
   fun n i j hij A => quadraticGenerator_eq_majoranaForm i j hij A,
   fun A hA => quadraticGenerator_majoranaForm_coef_real hA,
   fun A => localFormMatrix_transpose A,
   fun A => localRotation_mul_transpose A,
   fun A => localFormMatrix_apply A,
  fun n a => majoranaInBasis_one a,
  fun n U M S hU hS k => occupationExpectation_congruence_of_induced_general U M S hU hS k,
  fun n i j A hA M S hS => matchGate_covariance_congruence i j A hA M S hS,
  fun n gl k => classicalSimulationCost_le gl k,
  fun n i j hij A => frameRotation_mul_transpose i j hij A,
  fun n i j hij A p => majoranaInBasis_frameRotation_local i j hij A p,
  fun n i j A a ha => majoranaInBasis_frameRotation_away i j A a ha,
  fun n M i j hij A => localBlock_covarianceInBasis_frameRotation M i j hij A,
  fun n a b hab => majorana_comm_left n a b hab,
  fun n a b hab => majorana_comm_right n a b hab,
  fun n a b c hab hbc hac => majorana_comm_third n a b c hab hbc hac,
  fun n i j hij A hA => quadraticGenerator_eq_localForm i j hij A hA,
  fun n i j hij A hA => generator_comm_even_even i j hij A hA⟩

/-- The creation matrix `sigmaPlus` is the two-by-two matrix with its sole nonzero entry equal
to one in row one, column zero. -/
theorem sigmaPlus_eq : sigmaPlus = !![0, 0; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [sigmaPlus, pauliX, pauliY, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul] <;>
    norm_num

/-- In Boolean indices, `sigmaPlus` has value one from an unoccupied input to an occupied output
and zero otherwise. -/
theorem sigmaPlus_apply (a b : Bool) :
    sigmaPlus (boolEquivFin2 a) (boolEquivFin2 b) = if a then (if b then 0 else 1) else 0 := by
  rw [sigmaPlus_eq]
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    simp [boolEquivFin2]

/-- The annihilation matrix `sigmaMinus` is the two-by-two matrix with its sole nonzero entry
equal to one in row zero, column one. -/
theorem sigmaMinus_eq : sigmaMinus = !![0, 1; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [sigmaMinus, pauliX, pauliY, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul] <;>
    norm_num

/-- In Boolean indices, `sigmaMinus` has value one from an occupied input to an unoccupied
output and zero otherwise. -/
theorem sigmaMinus_apply (a b : Bool) :
    sigmaMinus (boolEquivFin2 a) (boolEquivFin2 b) = if a then 0 else if b then 1 else 0 := by
  rw [sigmaMinus_eq]
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    simp [boolEquivFin2]

/-- The single-qubit Pauli Z matrix is Hermitian. -/
theorem oneQubitZ_conjTranspose :
    (oneQubitZ : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = oneQubitZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [oneQubitZ, Matrix.conjTranspose_apply]

/-- The conjugate transpose of the single-qubit annihilation matrix is the creation matrix. -/
theorem sigmaMinus_conjTranspose :
    (sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = sigmaPlus := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.conjTranspose_apply, sigmaMinus_eq, sigmaPlus_eq]

/-- The conjugate transpose of the single-qubit creation matrix is the annihilation matrix. -/
theorem sigmaPlus_conjTranspose :
    (sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = sigmaMinus := by
  rw [← sigmaMinus_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- Taking the conjugate transpose of a local gate conjugate-transposes its single-site matrix. -/
theorem localGate_conjTranspose {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (localGate j G)ᴴ = localGate j Gᴴ := by
  ext y x
  rw [Matrix.conjTranspose_apply, localGate_apply, localGate_apply]
  by_cases h : ∀ k : Fin n, k ≠ j → x k = y k
  · have h' : ∀ k : Fin n, k ≠ j → y k = x k := by
      intro k hk
      exact (h k hk).symm
    rw [if_pos h, if_pos h']
    simp [Matrix.conjTranspose_apply]
  · have h' : ¬ (∀ k : Fin n, k ≠ j → y k = x k) := by
      intro hh
      exact h (fun k hk => (hh k hk).symm)
    rw [if_neg h, if_neg h']
    simp

/-- The operator of a singleton local gate list is its local gate. -/
theorem localGateListOp_singleton {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    localGateListOp [(j, G)] = localGate j G := by
  simp [localGateListOp]

/-- The conjugate transpose of a gate-list operator reverses the list and conjugate-transposes
every local matrix. -/
theorem localGateListOp_conjTranspose {n : ℕ} (gl : LocalGateList n) :
    (localGateListOp gl)ᴴ = localGateListOp (gl.reverse.map (fun p => (p.1, p.2ᴴ))) := by
  induction gl with
  | nil => simp [localGateListOp, Matrix.conjTranspose_one]
  | cons p rest ih =>
      show (localGate p.1 p.2 * localGateListOp rest)ᴴ = _
      rw [Matrix.conjTranspose_mul, ih, localGate_conjTranspose]
      rw [List.reverse_cons, List.map_append, localGateListOp_append]
      simp [localGateListOp]

/-- Reversing a list of diagonal local gates leaves its operator unchanged. -/
theorem localGateListOp_reverse_eq {n : ℕ} (gl : LocalGateList n)
    (hG : ∀ p ∈ gl, ∀ b c : Fin 2, p.2 b c ≠ 0 → b = c) :
    localGateListOp gl.reverse = localGateListOp gl := by
  apply Matrix.ext
  intro y x
  have hd := localGateListOp_diag gl hG y x
  have hd' := localGateListOp_diag gl.reverse
    (fun p hp b c hbc => hG p ((List.mem_reverse (x := p) (as := gl)).mp hp) b c hbc) y x
  rw [hd, hd']
  congr 1
  simp only [List.map_reverse]
  exact List.prod_reverse _

/-- Replacing local matrices by two functions that agree on the list gives equal gate-list
operators. -/
theorem localGateListOp_map_eq_of {n : ℕ} (gl : LocalGateList n)
    (f g : (Fin n × Matrix (Fin 2) (Fin 2) ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ p ∈ gl, f p = g p) :
    localGateListOp (gl.map (fun p => (p.1, f p))) = localGateListOp (gl.map (fun p => (p.1, g p))) := by
  induction gl with
  | nil => simp [localGateListOp]
  | cons p rest ih =>
      have h' : ∀ q ∈ rest, f q = g q := fun q hq => h q (by simp [hq])
      show localGate p.1 (f p) * localGateListOp (rest.map (fun q => (q.1, f q)))
        = localGate p.1 (g p) * localGateListOp (rest.map (fun q => (q.1, g q)))
      rw [ih h', h p (by simp)]

/-- Replacing every matrix in a local gate list by `G` leaves its operator unchanged when every
matrix already equals `G`. -/
theorem localGateListOp_map_id {n : ℕ} (gl : LocalGateList n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : ∀ p ∈ gl, p.2 = G) :
    localGateListOp (gl.map (fun p => (p.1, G))) = localGateListOp gl := by
  have h := localGateListOp_map_eq_of gl (fun _ => G) (fun p => p.2) (by
    intro p hp
    exact (hG p hp).symm)
  rw [h]
  simp

/-- A diagonal entry of the Jordan–Wigner Z prefix is the product of occupation signs at sites
below `i`. -/
theorem jwZPrefix_op_diag {n : ℕ} (i : Fin n) (y : Reg n) :
    localGateListOp (jwZPrefix i) y y
      = ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun j => (if y j then -1 else 1)) := by
  have h := localGateListOp_diag (jwZPrefix i)
    (fun p hp b c hbc => oneQubitZ_diagonal b c (by rw [jwZPrefix_mem i hp] at hbc; exact hbc)) y y
  rw [if_pos rfl] at h
  rw [h, jwZPrefix, List.map_map, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro j hj
  show oneQubitZ (boolEquivFin2 (y j)) (boolEquivFin2 (y j)) = (if y j then -1 else 1)
  by_cases hy : y j
  · have hb : boolEquivFin2 (y j) = 1 := by simp [boolEquivFin2, hy]
    rw [oneQubitZ_diagEntry, hb]
    simp [hy]
  · have hb : boolEquivFin2 (y j) = 0 := by simp [boolEquivFin2, hy]
    rw [oneQubitZ_diagEntry, hb]
    simp [hy]

/-- The operator of the Jordan–Wigner Z prefix is Hermitian. -/
theorem jwZPrefix_op_hermitian {n : ℕ} (i : Fin n) :
    (localGateListOp (jwZPrefix i))ᴴ = localGateListOp (jwZPrefix i) := by
  rw [localGateListOp_conjTranspose]
  rw [localGateListOp_map_eq_of (jwZPrefix i).reverse (fun p => p.2ᴴ) (fun _ => oneQubitZ) (by
    intro p hp
    have hp' : p ∈ jwZPrefix i := (List.mem_reverse (x := p) (as := jwZPrefix i)).mp hp
    show p.2ᴴ = oneQubitZ
    rw [jwZPrefix_mem i hp', oneQubitZ_conjTranspose])]
  rw [localGateListOp_map_id (jwZPrefix i).reverse oneQubitZ (by
    intro p hp
    exact jwZPrefix_mem i ((List.mem_reverse (x := p) (as := jwZPrefix i)).mp hp))]
  exact localGateListOp_reverse_eq (jwZPrefix i)
    (fun p hp b c hbc => oneQubitZ_diagonal b c (by rw [jwZPrefix_mem i hp] at hbc; exact hbc))

/-- For `i < j`, multiplying occupation-sign products below `i` and below `j` gives the sign
product on the interval from `i` inclusive to `j` exclusive. -/
theorem prod_paritySign_mul {n : ℕ} (i j : Fin n) (hij : i < j) (x : Reg n) :
    ((Finset.univ : Finset (Fin n)).filter (· < i)).prod (fun k => (if x k then -1 else 1 : ℂ))
      * ((Finset.univ : Finset (Fin n)).filter (· < j)).prod (fun k => (if x k then -1 else 1 : ℂ))
      = ((Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j)).prod
          (fun k => (if x k then -1 else 1 : ℂ)) := by
  classical
  set A := (Finset.univ : Finset (Fin n)).filter (· < i) with hA
  set B := (Finset.univ : Finset (Fin n)).filter (· < j) with hB
  set C := (Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j) with hC
  have hAB : A ⊆ B := by
    intro k hk
    have hk' : k < i := by
      simpa only [hA, Finset.mem_filter, Finset.mem_univ, true_and] using! hk
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsq : ∀ k : Fin n, (if x k then -1 else 1 : ℂ) * (if x k then -1 else 1 : ℂ) = 1 := by
    intro k
    by_cases hk : x k <;> simp [hk]
  have hprod : (A.prod (fun k => (if x k then -1 else 1 : ℂ)))
      * (A.prod (fun k => (if x k then -1 else 1 : ℂ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k hk
    exact hsq k
  have hBprod : (B.prod (fun k => (if x k then -1 else 1 : ℂ)))
      = (B \ A).prod (fun k => (if x k then -1 else 1 : ℂ))
        * (A.prod (fun k => (if x k then -1 else 1 : ℂ))) :=
    (Finset.prod_sdiff hAB).symm
  have hBA : B \ A = C := by
    ext k
    constructor
    · intro hk
      have hkB : k ∈ B := (Finset.mem_sdiff.mp hk).1
      have hkA : k ∉ A := (Finset.mem_sdiff.mp hk).2
      have hkj : k < j := by
        simpa only [hB, Finset.mem_filter, Finset.mem_univ, true_and] using! hkB
      have hnlt : ¬ (k < i) := by
        simpa only [hA, Finset.mem_filter, Finset.mem_univ, true_and] using! hkA
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, hkj⟩
    · intro hk
      have hk' : i ≤ k ∧ k < j := by
        simpa only [hC, Finset.mem_filter, Finset.mem_univ, true_and] using! hk
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa only [hB, Finset.mem_filter, Finset.mem_univ, true_and] using! hk'.2
      · have hnlt : ¬ (k < i) := by omega
        simpa only [hA, Finset.mem_filter, Finset.mem_univ, true_and] using! hnlt
  calc (A.prod (fun k => (if x k then -1 else 1 : ℂ)))
      * (B.prod (fun k => (if x k then -1 else 1 : ℂ)))
      = (A.prod (fun k => (if x k then -1 else 1 : ℂ)))
          * ((B \ A).prod (fun k => (if x k then -1 else 1 : ℂ))
            * (A.prod (fun k => (if x k then -1 else 1 : ℂ)))) := by rw [hBprod]
    _ = ((A.prod (fun k => (if x k then -1 else 1 : ℂ)))
          * (A.prod (fun k => (if x k then -1 else 1 : ℂ))))
          * (B \ A).prod (fun k => (if x k then -1 else 1 : ℂ)) := by ring
    _ = (B \ A).prod (fun k => (if x k then -1 else 1 : ℂ)) := by rw [hprod, one_mul]
    _ = C.prod (fun k => (if x k then -1 else 1 : ℂ)) := by rw [hBA]

/-- The Jordan–Wigner creation gate list represents the creation operator at mode `i`
[JordanWigner1928]. -/
theorem jwCreationGateList_op {n : ℕ} (i : Fin n) :
    localGateListOp (jwCreationGateList i) = creation i := by
  have hadj : (localGateListOp (jwLocalGateList i))ᴴ
      = localGate i sigmaPlus * localGateListOp (jwZPrefix i) := by
    rw [localGateListOp_conjTranspose, jwLocalGateList, List.reverse_append, List.map_append,
      List.reverse_singleton, List.map_cons, List.map_nil]
    rw [sigmaMinus_conjTranspose]
    rw [localGateListOp_append, localGateListOp_singleton]
    rw [localGateListOp_map_eq_of (jwZPrefix i).reverse (fun p => p.2ᴴ) (fun _ => oneQubitZ) (by
      intro p hp
      have hp' : p ∈ jwZPrefix i := (List.mem_reverse (x := p) (as := jwZPrefix i)).mp hp
      show p.2ᴴ = oneQubitZ
      rw [jwZPrefix_mem i hp', oneQubitZ_conjTranspose])]
    rw [localGateListOp_map_id (jwZPrefix i).reverse oneQubitZ (by
      intro p hp
      exact jwZPrefix_mem i ((List.mem_reverse (x := p) (as := jwZPrefix i)).mp hp))]
    rw [localGateListOp_reverse_eq (jwZPrefix i)
      (fun p hp b c hbc => oneQubitZ_diagonal b c (by rw [jwZPrefix_mem i hp] at hbc; exact hbc))]
  have h1 : localGateListOp (jwCreationGateList i)
      = localGate i sigmaPlus * localGateListOp (jwZPrefix i) := by
    rw [jwCreationGateList, localGateListOp_append, localGateListOp_singleton]
  have h3 : creation i = (localGateListOp (jwLocalGateList i))ᴴ := by
    rw [jwLocalGateList_annihilation]
    exact (Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.1 i
  rw [h3, h1, hadj]

/-- The difference between the creation gate-list operator and the creation operator vanishes
entrywise. -/
theorem jwCreationGateList_error {n : ℕ} (i : Fin n) :
    ∀ (y x : Reg n), (localGateListOp (jwCreationGateList i) - creation i) y x = 0 := by
  intro y x
  rw [jwCreationGateList_op, sub_self, Matrix.zero_apply]

/-- Creation at mode `i` factors as its local creation matrix times the Jordan–Wigner Z-prefix
operator. -/
theorem jwCreationGateList_op_decomp {n : ℕ} (i : Fin n) :
    creation i = localGate i sigmaPlus * localGateListOp (jwZPrefix i) := by
  have h := (jwCreationGateList_op i).symm
  rw [jwCreationGateList, localGateListOp_append, localGateListOp_singleton] at h
  exact h

/-- The Jordan–Wigner creation gate list contains `i.val + 1` local gates. -/
theorem jwCreationGateList_count {n : ℕ} (i : Fin n) :
    localGateCount (jwCreationGateList i) = i.val + 1 := by
  rw [localGateCount_eq_length, jwCreationGateList, List.length_append, List.length_cons,
    List.length_nil, jwZPrefix, List.length_map, Finset.length_toList, card_filter_lt]
  omega

/-- A nonzero entry of the single-qubit number matrix has equal row and column indices. -/
theorem oneQubitNumber_diagonal (b c : Fin 2) (h : oneQubitNumber b c ≠ 0) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  · have h2 : oneQubitNumber b c = 0 := by
      simp [oneQubitNumber, Matrix.of_apply, hbc]
    exact absurd h2 h

/-- The number gate list represents the number operator at its mode. -/
theorem numberGateList_op {n : ℕ} (i : Fin n) :
    localGateListOp (numberGateList i) = numberOp i := by
  rw [numberGateList, localGateListOp_singleton]
  ext y x
  rw [localGate_apply, numberOp_apply]
  by_cases h : ∀ k : Fin n, k ≠ i → y k = x k
  · rw [if_pos h]
    by_cases hyx : y = x
    · subst hyx
      by_cases hi : y i
      · have hb : boolEquivFin2 (y i) = 1 := by simp [boolEquivFin2, hi]
        rw [hb]
        simp [oneQubitNumber, Matrix.of_apply, hi]
      · have hb : boolEquivFin2 (y i) = 0 := by simp [boolEquivFin2, hi]
        rw [hb]
        simp [oneQubitNumber, Matrix.of_apply, hi]
    · have hne : boolEquivFin2 (y i) ≠ boolEquivFin2 (x i) := by
        intro hh
        apply hyx
        funext k
        by_cases hk : k = i
        · rw [hk]
          exact boolEquivFin2.injective hh
        · exact h k hk
      have hz : oneQubitNumber (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) = 0 := by
        by_contra hcon
        exact hne (oneQubitNumber_diagonal _ _ hcon)
      rw [hz]
      have hne' : x ≠ y := by
        intro hxy
        exact hyx hxy.symm
      simp [hne']
  · rw [if_neg h]
    have hne' : x ≠ y := by
      intro hxy
      exact h (fun k hk => by rw [hxy])
    simp [hne']

/-- The number gate list contains one local gate. -/
theorem numberGateList_count {n : ℕ} (i : Fin n) :
    localGateCount (numberGateList i) = 1 := by
  simp [numberGateList, localGateCount]

/-- A diagonal entry of the Z-range operator is the product of occupation signs from `i`
inclusive to `j` exclusive. -/
theorem zRangeGateList_op_diag {n : ℕ} (i j : Fin n) (y : Reg n) :
    localGateListOp (zRangeGateList i j) y y
      = ((Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j)).prod
          (fun k => (if y k then -1 else 1)) := by
  have h := localGateListOp_diag (zRangeGateList i j)
    (fun p hp b c hbc => oneQubitZ_diagonal b c (by
      simp only [zRangeGateList, List.mem_map] at hp
      obtain ⟨q, -, rfl⟩ := hp
      exact hbc)) y y
  rw [if_pos rfl] at h
  rw [h, zRangeGateList, List.map_map, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro k hk
  show oneQubitZ (boolEquivFin2 (y k)) (boolEquivFin2 (y k)) = (if y k then -1 else 1)
  by_cases hy : y k
  · have hb : boolEquivFin2 (y k) = 1 := by simp [boolEquivFin2, hy]
    rw [oneQubitZ_diagEntry, hb]
    simp [hy]
  · have hb : boolEquivFin2 (y k) = 0 := by simp [boolEquivFin2, hy]
    rw [oneQubitZ_diagEntry, hb]
    simp [hy]

/-- For `i < j`, the Z-range operator equals the product of the Jordan–Wigner Z prefixes at `i`
and `j`. -/
theorem zRange_op_eq {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateListOp (zRangeGateList i j)
      = localGateListOp (jwZPrefix i) * localGateListOp (jwZPrefix j) := by
  have hlist : localGateListOp (jwZPrefix i ++ jwZPrefix j)
      = localGateListOp (zRangeGateList i j) := by
    have hdiagi : ∀ (y x : Reg n), y ≠ x → localGateListOp (jwZPrefix i) y x = 0 := by
      intro y x hne
      have h := localGateListOp_diag (jwZPrefix i)
        (fun p hp b c hbc => oneQubitZ_diagonal b c (by rw [jwZPrefix_mem i hp] at hbc; exact hbc)) y x
      rw [if_neg hne] at h
      exact h
    have hdiagj : ∀ (y x : Reg n), y ≠ x → localGateListOp (jwZPrefix j) y x = 0 := by
      intro y x hne
      have h := localGateListOp_diag (jwZPrefix j)
        (fun p hp b c hbc => oneQubitZ_diagonal b c (by rw [jwZPrefix_mem j hp] at hbc; exact hbc)) y x
      rw [if_neg hne] at h
      exact h
    have hdiagz : ∀ (y x : Reg n), y ≠ x → localGateListOp (zRangeGateList i j) y x = 0 := by
      intro y x hne
      have h := localGateListOp_diag (zRangeGateList i j)
        (fun p hp b c hbc => oneQubitZ_diagonal b c (by
          simp only [zRangeGateList, List.mem_map] at hp
          obtain ⟨q, -, rfl⟩ := hp
          exact hbc)) y x
      rw [if_neg hne] at h
      exact h
    apply Matrix.ext
    intro y x
    rw [localGateListOp_append,
      mul_apply_diag_left (localGateListOp (jwZPrefix i)) (localGateListOp (jwZPrefix j))
        hdiagi y x]
    by_cases hyx : y = x
    · subst hyx
      rw [jwZPrefix_op_diag i y, jwZPrefix_op_diag j y, zRangeGateList_op_diag]
      exact prod_paritySign_mul i j hij y
    · have hdiagjxy : localGateListOp (jwZPrefix j) y x = 0 := hdiagj y x (by
        intro h
        exact hyx h)
      have hdiagzxy : localGateListOp (zRangeGateList i j) y x = 0 := hdiagz y x (by
        intro h
        exact hyx h)
      rw [hdiagjxy, mul_zero, hdiagzxy]
  rw [← localGateListOp_append, hlist]

/-- For `i < j`, the forward hopping gate list represents `creation i * annihilation j`. -/
theorem hopForwardGateList_op {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateListOp (hopForwardGateList i j) = creation i * annihilation j := by
  have hdec : annihilation j = localGateListOp (jwZPrefix j) * localGate j sigmaMinus := by
    have h := (jwLocalGateList_annihilation j).symm
    rw [jwLocalGateList, localGateListOp_append, localGateListOp_singleton] at h
    exact h
  rw [hopForwardGateList]
  simp only [localGateListOp_append, localGateListOp_singleton]
  rw [jwCreationGateList_op_decomp, hdec, zRange_op_eq i j hij]
  simp only [Matrix.mul_assoc]

/-- For `i < j`, the backward hopping gate list represents `creation j * annihilation i`. -/
theorem hopBackwardGateList_op {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateListOp (hopBackwardGateList i j) = creation j * annihilation i := by
  have hc : ∀ k : Fin n, creation k = (annihilation k)ᴴ :=
    fun k => (Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.1 k
  have ha : ∀ k : Fin n, annihilation k = (creation k)ᴴ := by
    intro k
    have h1 := ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2.1 k).1
    have h2 := ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.2.2.1 k).2
    calc annihilation k = jwPauliWord k := h1
      _ = ((jwPauliWord k)ᴴ)ᴴ := by rw [Matrix.conjTranspose_conjTranspose]
      _ = (creation k)ᴴ := by rw [h2]
  have h1 : (creation i * annihilation j)ᴴ = creation j * annihilation i := by
    rw [Matrix.conjTranspose_mul]
    have e1 : (annihilation j)ᴴ = creation j := (hc j).symm
    have e2 : (creation i)ᴴ = annihilation i := (ha i).symm
    rw [e1, e2]
  have hZ : ∀ p ∈ zRangeGateList i j, p.2 = oneQubitZ := by
    intro p hp
    simp only [zRangeGateList, List.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    rfl
  have hZrev : ∀ p ∈ (zRangeGateList i j).reverse, p.2 = oneQubitZ := by
    intro p hp
    exact hZ p ((List.mem_reverse (x := p) (as := zRangeGateList i j)).mp hp)
  have hrev : localGateListOp ((zRangeGateList i j).reverse.map (fun p => (p.1, oneQubitZ)))
      = localGateListOp (zRangeGateList i j) := by
    rw [localGateListOp_map_id (zRangeGateList i j).reverse oneQubitZ hZrev]
    exact localGateListOp_reverse_eq (zRangeGateList i j)
      (fun p hp b c hbc => oneQubitZ_diagonal b c (by
        simp only [zRangeGateList, List.mem_map] at hp
        obtain ⟨q, -, rfl⟩ := hp
        exact hbc))
  have h2 : (creation i * annihilation j)ᴴ = localGateListOp (hopBackwardGateList i j) := by
    rw [← hopForwardGateList_op i j hij, localGateListOp_conjTranspose]
    rw [hopForwardGateList]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.map_append,
      List.map_cons, List.map_nil, List.nil_append]
    rw [sigmaMinus_conjTranspose, sigmaPlus_conjTranspose]
    rw [localGateListOp_append, localGateListOp_append]
    rw [localGateListOp_singleton, localGateListOp_singleton]
    rw [localGateListOp_map_eq_of (zRangeGateList i j).reverse (fun p => p.2ᴴ)
      (fun _ => oneQubitZ) (by
        intro p hp
        have hp' : p ∈ zRangeGateList i j :=
          (List.mem_reverse (x := p) (as := zRangeGateList i j)).mp hp
        show p.2ᴴ = oneQubitZ
        rw [hZ p hp', oneQubitZ_conjTranspose])]
    rw [hrev]
    rw [hopBackwardGateList, localGateListOp_append, localGateListOp_append]
    rw [localGateListOp_singleton, localGateListOp_singleton]
    simp only [Matrix.mul_assoc]
  rw [← h1, h2]

/-- For `i < j`, the interval from `i` inclusive to `j` exclusive contains `j.val - i.val`
indices. -/
theorem card_filter_between {n : ℕ} (i j : Fin n) (hij : i < j) :
    ((Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j)).card = j.val - i.val := by
  classical
  have hAB : ((Finset.univ : Finset (Fin n)).filter (· < i))
      ⊆ ((Finset.univ : Finset (Fin n)).filter (· < j)) := by
    intro k hk
    have hk' : k < i := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using! hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hdiff : (Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j)
      = ((Finset.univ : Finset (Fin n)).filter (· < j))
        \ ((Finset.univ : Finset (Fin n)).filter (· < i)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk1, hk2⟩
      exact ⟨hk2, by omega⟩
    · rintro ⟨hk1, hk2⟩
      exact ⟨by omega, hk1⟩
  rw [hdiff, Finset.card_sdiff_of_subset hAB, card_filter_lt j, card_filter_lt i]

/-- For `i < j`, the forward hopping gate list contains `j.val - i.val + 2` local gates. -/
theorem hopForwardGateList_count {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateCount (hopForwardGateList i j) = j.val - i.val + 2 := by
  rw [localGateCount_eq_length, hopForwardGateList, List.length_append, List.length_append,
    List.length_cons, List.length_nil, zRangeGateList, List.length_map, Finset.length_toList,
    zRangeSet, card_filter_between i j hij]
  simp only [List.length_cons, List.length_nil]
  omega

/-- For `i < j`, the backward hopping gate list contains `j.val - i.val + 2` local gates. -/
theorem hopBackwardGateList_count {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateCount (hopBackwardGateList i j) = j.val - i.val + 2 := by
  rw [localGateCount_eq_length, hopBackwardGateList, List.length_append, List.length_append,
    List.length_cons, List.length_nil, zRangeGateList, List.length_map, Finset.length_toList,
    zRangeSet, card_filter_between i j hij]
  simp only [List.length_cons, List.length_nil]
  omega

/-- For `i < j`, the forward hopping bit cost is `(j.val - i.val + 2) * modeAddressBits n`. -/
theorem hopForwardGateList_bitCost {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateBitCost (hopForwardGateList i j)
      = (j.val - i.val + 2) * modeAddressBits n := by
  rw [localGateBitCost, hopForwardGateList_count i j hij]

/-- The defined space cost of a forward hopping gate list is `n`. -/
theorem hopForwardGateList_spaceCost {n : ℕ} (i j : Fin n) :
    localGateSpaceCost (hopForwardGateList i j) = n := rfl

/-- For `i < j`, the quadratic generator is the sum of four coefficient-weighted number and
hopping gate-list operators. -/
theorem quadraticGenerator_eq_localTerms {n : ℕ} (i j : Fin n) (hij : i < j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    quadraticGenerator i j A
      = A 0 0 • (localGateListOp (numberGateList i))
        + A 0 1 • (localGateListOp (hopForwardGateList i j))
        + A 1 0 • (localGateListOp (hopBackwardGateList i j))
        + A 1 1 • (localGateListOp (numberGateList j)) := by
  have hnum : ∀ k : Fin n, creation k * annihilation k = numberOp k := by
    intro k
    exact ((Qatlib.Concepts.FermionAlgebra.CarJordanWigner.g1 n).2.2.1 k).1.symm
  rw [quadraticGenerator]
  simp only [hnum]
  rw [numberGateList_op i, hopForwardGateList_op i j hij,
    hopBackwardGateList_op i j hij, numberGateList_op j]

/-- A creation–annihilation product has zero entries between registers differing outside its two
modes. -/
theorem creation_annihilation_supports {n : ℕ} (p q : Fin n) (y x : Reg n)
    (hk : ∃ k : Fin n, k ≠ p ∧ k ≠ q ∧ y k ≠ x k) :
    (creation p * annihilation q) y x = 0 := by
  have hz : ∀ z : Reg n, creation p y z * annihilation q z x = 0 := by
    intro z
    by_cases h1 : creation p y z = 0
    · simp [h1]
    · by_cases h2 : annihilation q z x = 0
      · simp [h2]
      · have hc := creation_support p y z h1
        have ha := annihilation_support q z x h2
        obtain ⟨k, hk1, hk2, hk3⟩ := hk
        have hkx : y k = x k := (hc k hk1).trans (ha k hk2)
        exact absurd hkx hk3
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero (fun z _ => hz z)

/-- A quadratic generator has zero entries between registers differing outside its two modes. -/
theorem quadraticGenerator_supports_twoModes {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (y x : Reg n)
    (hk : ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k) :
    quadraticGenerator i j A y x = 0 := by
  have hkII : ∃ k : Fin n, k ≠ i ∧ k ≠ i ∧ y k ≠ x k := by
    obtain ⟨k, h1, _, h3⟩ := hk
    exact ⟨k, h1, h1, h3⟩
  have hkIJ : ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k := hk
  have hkJI : ∃ k : Fin n, k ≠ j ∧ k ≠ i ∧ y k ≠ x k := by
    obtain ⟨k, h1, h2, h3⟩ := hk
    exact ⟨k, h2, h1, h3⟩
  have hkJJ : ∃ k : Fin n, k ≠ j ∧ k ≠ j ∧ y k ≠ x k := by
    obtain ⟨k, _, h2, h3⟩ := hk
    exact ⟨k, h2, h2, h3⟩
  unfold quadraticGenerator
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [creation_annihilation_supports i i y x hkII,
    creation_annihilation_supports i j y x hkIJ,
    creation_annihilation_supports j i y x hkJI,
    creation_annihilation_supports j j y x hkJJ]
  ring

/-- For `i < j`, the four local gate lists representing a quadratic generator have total gate
count `2 * (j.val - i.val) + 6`. -/
theorem quadraticGenerator_localTerms_count {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateCount (numberGateList i)
        + localGateCount (hopForwardGateList i j)
        + localGateCount (hopBackwardGateList i j)
        + localGateCount (numberGateList j)
      = 2 * (j.val - i.val) + 6 := by
  rw [numberGateList_count, hopForwardGateList_count i j hij,
    hopBackwardGateList_count i j hij, numberGateList_count]
  omega

/-- The number operator is the diagonal matrix indicating occupation of its mode. -/
theorem numberOp_eq_diagonal {n : ℕ} (i : Fin n) :
    numberOp i = Matrix.diagonal (fun x => if x i then 1 else 0) := by
  ext y x
  by_cases h : x = y
  · subst h
    rw [Matrix.diagonal_apply_eq]
    simp [numberOp, Matrix.of_apply]
  · rw [Matrix.diagonal_apply_ne' _ h]
    simp [numberOp, Matrix.of_apply, h]

/-- The onsite phase gate is diagonal, with phase `exp (-I * s)` on occupied registers and one
on unoccupied registers. -/
theorem onsiteLocalGate_eq_diagonal {n : ℕ} (i : Fin n) (s : ℝ) :
    onsiteLocalGate i s
      = Matrix.diagonal (fun x => if x i then Complex.exp (-Complex.I * s) else 1) := by
  ext y x
  by_cases h : x = y
  · subst h
    rw [Matrix.diagonal_apply_eq]
    unfold onsiteLocalGate
    rw [localGate_apply]
    rw [oneQubitPhase, Matrix.of_apply]
    by_cases hi : x i
    · simp [hi, boolEquivFin2]
    · simp [hi, boolEquivFin2]
  · rw [Matrix.diagonal_apply_ne' _ h]
    unfold onsiteLocalGate
    rw [localGate_apply]
    by_cases hc : ∀ k : Fin n, k ≠ i → y k = x k
    · have hne : boolEquivFin2 (y i) ≠ boolEquivFin2 (x i) := by
        intro hh
        apply h
        funext k
        by_cases hk : k = i
        · rw [hk]
          exact boolEquivFin2.injective hh.symm
        · exact (hc k hk).symm
      rw [oneQubitPhase, Matrix.of_apply, if_neg hne]
      simp
    · simp [hc]

/-- Hamiltonian evolution under a number operator equals the corresponding onsite phase gate. -/
theorem hamiltonianEvolution_numberOp_eq_onsiteLocalGate {n : ℕ} (i : Fin n) (s : ℝ) :
    HamiltonianEvolution (numberOp i) s = onsiteLocalGate i s := by
  have hmain : HamiltonianEvolution (numberOp i) s
      = Matrix.diagonal (fun x => if x i then Complex.exp (-Complex.I * s) else 1) := by
    unfold HamiltonianEvolution
    rw [numberOp_eq_diagonal i, ← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    funext x
    by_cases hx : x i
    · simp [hx, ← Complex.exp_eq_exp_ℂ]
    · simp [hx, ← Complex.exp_eq_exp_ℂ]
  rw [hmain, onsiteLocalGate_eq_diagonal]

/-- A register-indexed sum supported on two distinct registers equals the sum of its values at
those registers. -/
private theorem sum_pair {n : ℕ} (f : Reg n → ℂ) (a b : Reg n) (hne : a ≠ b)
    (h0 : ∀ z : Reg n, z ≠ a → z ≠ b → f z = 0) :
    (∑ z : Reg n, f z) = f a + f b := by
  have hset : ({a, b} : Finset (Reg n)) = insert a ({b} : Finset (Reg n)) := by
    ext z
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hsub : (∑ z : Reg n, f z) = ∑ z ∈ ({a, b} : Finset (Reg n)), f z := by
    have h := (Finset.sum_subset (s₁ := ({a, b} : Finset (Reg n)))
      (s₂ := (Finset.univ : Finset (Reg n))) (f := f) (by simp)
      (by intro z hz hz1
          have hz1' : z ≠ a ∧ z ≠ b := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using! hz1
          exact h0 z hz1'.1 hz1'.2)).symm
    simpa using! h
  rw [hsub, hset, Finset.sum_insert (by simpa using! hne), Finset.sum_singleton]

/-- A register-indexed sum supported on one register equals its value at that register. -/
private theorem sum_single {n : ℕ} (f : Reg n → ℂ) (a : Reg n)
    (h0 : ∀ z : Reg n, z ≠ a → f z = 0) :
    (∑ z : Reg n, f z) = f a := by
  have hsub : (∑ z : Reg n, f z) = ∑ z ∈ ({a} : Finset (Reg n)), f z := by
    have h := (Finset.sum_subset (s₁ := ({a} : Finset (Reg n)))
      (s₂ := (Finset.univ : Finset (Reg n))) (f := f) (by simp)
      (by intro z hz hz1
          have hz1' : z ≠ a := by
            simpa [Finset.mem_singleton] using! hz1
          exact h0 z hz1')).symm
    simpa using! h
  rw [hsub, Finset.sum_singleton]

/-- The Boolean-to-`Fin 2` equivalence sends `false` to zero. -/
private theorem boolEquivFin2_false : boolEquivFin2 false = 0 := by
  simp [boolEquivFin2]

/-- The Boolean-to-`Fin 2` equivalence sends `true` to one. -/
private theorem boolEquivFin2_true : boolEquivFin2 true = 1 := by
  simp [boolEquivFin2]

/-- A register agreeing with `y` away from `j` is obtained by updating `y` at `j` with that
register's value. -/
private theorem agree_update {n : ℕ} (y : Reg n) (j : Fin n) (z : Reg n)
    (h : ∀ k : Fin n, k ≠ j → y k = z k) : z = Function.update y j (z j) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [Function.update_self]
  · simp [Function.update_of_ne hk, h k hk]

/-- A local gate entry from a single-site update of `y` to `y` equals the corresponding entry of
its local matrix. -/
private theorem localGate_apply_update {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (y : Reg n) (b : Bool) :
    localGate j G y (Function.update y j b) = G (boolEquivFin2 (y j)) (boolEquivFin2 b) := by
  rw [localGate_apply]
  have hcond : ∀ k : Fin n, k ≠ j → y k = Function.update y j b k := by
    intro k hk
    rw [Function.update_of_ne hk]
  rw [if_pos hcond]
  simp [Function.update_self, boolEquivFin2]

/-- When registers agree away from `j`, updating the row register at `j` gives the corresponding
local matrix entry. -/
private theorem localGate_apply_update' {n : ℕ} (j : Fin n) (H : Matrix (Fin 2) (Fin 2) ℂ)
    (y x : Reg n) (b : Bool) (hyx : ∀ k : Fin n, k ≠ j → y k = x k) :
    localGate j H (Function.update y j b) x = H (boolEquivFin2 b) (boolEquivFin2 (x j)) := by
  rw [localGate_apply]
  have hcond : ∀ k : Fin n, k ≠ j → Function.update y j b k = x k := by
    intro k hk
    rw [Function.update_of_ne hk]
    exact hyx k hk
  rw [if_pos hcond]
  simp [Function.update_self, boolEquivFin2]

/-- Multiplying two local gates at the same site embeds the product of their local matrices. -/
theorem localGate_mul_localGate_same {n : ℕ} (j : Fin n) (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    localGate j G * localGate j H = localGate j (G * H) := by
  classical
  ext y x
  rw [Matrix.mul_apply]
  by_cases hyx : ∀ k : Fin n, k ≠ j → y k = x k
  · have hconv : (∑ z : Reg n, (localGate j G y z) * (localGate j H z x))
        = (localGate j G y (Function.update y j false)) * (localGate j H (Function.update y j false) x)
          + (localGate j G y (Function.update y j true)) * (localGate j H (Function.update y j true) x) := by
      refine sum_pair (fun z => (localGate j G y z) * (localGate j H z x))
        (Function.update y j false) (Function.update y j true) ?_ ?_
      · intro hh
        have hthis := congrFun hh j
        simp at hthis
      · intro z hz1 hz2
        by_cases hcond : ∀ k : Fin n, k ≠ j → y k = z k
        · have hz : z = Function.update y j (z j) := agree_update y j z hcond
          by_cases hb : z j = true
          · have hztrue : z = Function.update y j true := by
              calc z = Function.update y j (z j) := hz
                _ = Function.update y j true := by
                  rw [show z j = true from hb]
            exact absurd hztrue hz2
          · have hzfalse : z = Function.update y j false := by
              calc z = Function.update y j (z j) := hz
                _ = Function.update y j false := by
                  rw [show z j = false from Bool.eq_false_of_not_eq_true hb]
            exact absurd hzfalse hz1
        · show localGate j G y z * localGate j H z x = 0
          rw [localGate_apply, if_neg hcond]
          simp
    rw [hconv]
    rw [localGate_apply_update j G y false, localGate_apply_update' j H y x false hyx,
      localGate_apply_update j G y true, localGate_apply_update' j H y x true hyx]
    rw [boolEquivFin2_false, boolEquivFin2_true]
    rw [localGate_apply]
    simp only [if_pos hyx]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  · have hzero : (∑ z : Reg n, (localGate j G y z) * (localGate j H z x)) = 0 := by
      have h1 : (∑ z : Reg n, (localGate j G y z) * (localGate j H z x))
          = (localGate j G y (Function.update y j false)) * (localGate j H (Function.update y j false) x) := by
        refine sum_single (fun z => (localGate j G y z) * (localGate j H z x))
          (Function.update y j false) ?_
        intro z hz
        by_cases hcond : ∀ k : Fin n, k ≠ j → y k = z k
        · have hz' : z = Function.update y j (z j) := agree_update y j z hcond
          have h2 : ¬ ∀ k : Fin n, k ≠ j → z k = x k := by
            intro h2
            apply hyx
            intro k hk
            have hyz : y k = z k := by
              rw [hz']
              exact (Function.update_of_ne hk (z j) y).symm
            exact hyz.trans (h2 k hk)
          show localGate j G y z * localGate j H z x = 0
          rw [localGate_apply, localGate_apply, if_pos hcond, if_neg h2]
          simp
        · show localGate j G y z * localGate j H z x = 0
          rw [localGate_apply, if_neg hcond]
          simp
      rw [h1]
      show localGate j G y (Function.update y j false) * localGate j H
          (Function.update y j false) x = 0
      rw [localGate_apply, localGate_apply]
      have hcond1 : ∀ k : Fin n, k ≠ j → y k = Function.update y j false k := by
        intro k hk
        rw [Function.update_of_ne hk]
      have hcond2 : ¬ ∀ k : Fin n, k ≠ j → Function.update y j false k = x k := by
        intro h2
        apply hyx
        intro k hk
        exact (Function.update_of_ne hk false y).symm.trans (h2 k hk)
      rw [if_pos hcond1, if_neg hcond2]
      simp
    rw [hzero, localGate_apply]
    simp only [if_neg hyx]

/-- A nonzero local gate entry connects registers that agree away from its site. -/
private theorem localGate_ne_zero {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (y z : Reg n) (h : localGate j G y z ≠ 0) : ∀ k : Fin n, k ≠ j → y k = z k := by
  by_contra hcon
  rw [localGate_apply, if_neg hcon] at h
  exact h rfl

/-- Successive updates at `j` and `k` leave a register value unchanged at a site distinct from
both. -/
private theorem update2_apply {n : ℕ} (y x : Reg n) (j k m : Fin n)
    (_hj : m ≠ j) (hk : m ≠ k) :
    Function.update (Function.update y j (x j)) k (y k) m = y m := by
  have h1 : Function.update (Function.update y j (x j)) k (y k) m
      = Function.update y j (x j) m := Function.update_of_ne hk (y k) (Function.update y j (x j))
  exact h1.trans (Function.update_of_ne _hj (x j) y)

/-- For distinct `j` and `k`, updating `y` at `j` with `x j` and then at `k` with `y k` gives
value `x j` at `j`. -/
private theorem update2_apply_j {n : ℕ} (y x : Reg n) (j k : Fin n) (hk : j ≠ k) :
    Function.update (Function.update y j (x j)) k (y k) j = x j := by
  rw [Function.update_of_ne hk (y k) (Function.update y j (x j)), Function.update_self]

/-- Updating `y` at `j` with `x j` and then at `k` with `y k` gives value `y k` at `k`. -/
private theorem update2_apply_k {n : ℕ} (y x : Reg n) (j k : Fin n) (hj : k ≠ j) :
    Function.update (Function.update y j (x j)) k (y k) k = y k := by
  rw [Function.update_self]

/-- For gates at distinct sites, any register giving two nonzero consecutive matrix entries is
the specified update of the row register. -/
private theorem localGate_mul_ne_unique {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) (y x z : Reg n)
    (h1 : localGate j G y z ≠ 0) (h2 : localGate k H z x ≠ 0) :
    z = Function.update (Function.update y j (x j)) k (y k) := by
  have hy : ∀ m : Fin n, m ≠ j → y m = z m := localGate_ne_zero j G y z h1
  have hz : ∀ m : Fin n, m ≠ k → z m = x m := localGate_ne_zero k H z x h2
  funext m
  by_cases hm1 : m = j
  · rw [hm1, update2_apply_j y x j k hjk]
    exact hz j hjk
  by_cases hm2 : m = k
  · rw [hm2, update2_apply_k y x j k (Ne.symm hjk)]
    exact (hy k (Ne.symm hjk)).symm
  rw [update2_apply y x j k m hm1 hm2]
  exact (hy m hm1).symm

/-- For distinct sites, the local gate entry against the specified two-update register is the
corresponding entry of `G`. -/
private theorem localGate_apply_update2 {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (y x : Reg n) :
    localGate j G y (Function.update (Function.update y j (x j)) k (y k))
      = G (boolEquivFin2 (y j)) (boolEquivFin2 (x j)) := by
  rw [localGate_apply]
  have hcond : ∀ m : Fin n, m ≠ j → y m = Function.update (Function.update y j (x j)) k (y k) m := by
    intro m hm
    by_cases hm2 : m = k
    · rw [hm2, update2_apply_k y x j k (Ne.symm hjk)]
    · rw [update2_apply y x j k m hm hm2]
  rw [if_pos hcond, update2_apply_j y x j k hjk]

/-- For distinct sites and registers agreeing elsewhere, the local gate entry from the specified
intermediate register is the corresponding entry of `H`. -/
private theorem localGate_apply_update2' {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (H : Matrix (Fin 2) (Fin 2) ℂ) (y x : Reg n)
    (hyx : ∀ m : Fin n, m ≠ j → m ≠ k → y m = x m) :
    localGate k H (Function.update (Function.update y j (x j)) k (y k)) x
      = H (boolEquivFin2 (y k)) (boolEquivFin2 (x k)) := by
  rw [localGate_apply]
  have hcond : ∀ m : Fin n, m ≠ k →
      Function.update (Function.update y j (x j)) k (y k) m = x m := by
    intro m hm
    by_cases hm2 : m = j
    · rw [hm2, update2_apply_j y x j k hjk]
    · rw [update2_apply y x j k m hm2 hm]
      exact hyx m hm2 hm
  rw [if_pos hcond, update2_apply_k y x j k (Ne.symm hjk)]

/-- For gates at distinct sites and registers agreeing elsewhere, the product entry is the
product of the two local matrix entries. -/
private theorem localGate_mul_ne_entry {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) (y x : Reg n)
    (hyx : ∀ m : Fin n, m ≠ j → m ≠ k → y m = x m) :
    (localGate j G * localGate k H) y x
      = G (boolEquivFin2 (y j)) (boolEquivFin2 (x j)) * H (boolEquivFin2 (y k)) (boolEquivFin2 (x k)) := by
  classical
  rw [Matrix.mul_apply]
  have h1 : (∑ z : Reg n, (localGate j G y z) * (localGate k H z x))
      = (localGate j G y (Function.update (Function.update y j (x j)) k (y k)))
        * (localGate k H (Function.update (Function.update y j (x j)) k (y k)) x) := by
    refine sum_single (fun z => (localGate j G y z) * (localGate k H z x))
      (Function.update (Function.update y j (x j)) k (y k)) ?_
    intro z hz
    by_cases hz1 : localGate j G y z = 0
    · show localGate j G y z * localGate k H z x = 0
      rw [hz1, zero_mul]
    · by_cases hz2 : localGate k H z x = 0
      · show localGate j G y z * localGate k H z x = 0
        rw [hz2, mul_zero]
      · exact absurd (localGate_mul_ne_unique j k hjk G H y x z hz1 hz2) hz
  rw [h1, localGate_apply_update2 j k hjk G y x,
    localGate_apply_update2' j k hjk H y x hyx]

/-- A product of gates at distinct sites has zero entries between registers that disagree
outside those sites. -/
private theorem localGate_mul_ne_zero {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) (y x : Reg n)
    (hyx : ¬ ∀ m : Fin n, m ≠ j → m ≠ k → y m = x m) :
    (localGate j G * localGate k H) y x = 0 := by
  classical
  rw [Matrix.mul_apply]
  have hz0 : (localGate j G y (Function.update (Function.update y j (x j)) k (y k)))
      * (localGate k H (Function.update (Function.update y j (x j)) k (y k)) x) = 0 := by
    by_cases hz1 : localGate j G y (Function.update (Function.update y j (x j)) k (y k)) = 0
    · rw [hz1, zero_mul]
    · by_cases hz2 : localGate k H (Function.update (Function.update y j (x j)) k (y k)) x = 0
      · rw [hz2, mul_zero]
      · have hy : ∀ m : Fin n, m ≠ j →
            y m = (Function.update (Function.update y j (x j)) k (y k)) m :=
          localGate_ne_zero j G y _ hz1
        have hzz : ∀ m : Fin n, m ≠ k →
            (Function.update (Function.update y j (x j)) k (y k)) m = x m :=
          localGate_ne_zero k H _ x hz2
        have h3 : ∀ m : Fin n, m ≠ j → m ≠ k → y m = x m := by
          intro m hm1 hm2
          exact (hy m hm1).trans (hzz m hm2)
        exact absurd h3 hyx
  calc (∑ z : Reg n, (localGate j G y z) * (localGate k H z x))
      = (localGate j G y (Function.update (Function.update y j (x j)) k (y k)))
          * (localGate k H (Function.update (Function.update y j (x j)) k (y k)) x) := by
        refine sum_single (fun z => (localGate j G y z) * (localGate k H z x))
          (Function.update (Function.update y j (x j)) k (y k)) ?_
        intro z hz
        by_cases hz1 : localGate j G y z = 0
        · show localGate j G y z * localGate k H z x = 0
          rw [hz1, zero_mul]
        · by_cases hz2 : localGate k H z x = 0
          · show localGate j G y z * localGate k H z x = 0
            rw [hz2, mul_zero]
          · exact absurd (localGate_mul_ne_unique j k hjk G H y x z hz1 hz2) hz
    _ = 0 := hz0

/-- Local gates at distinct sites commute. -/
theorem localGate_mul_localGate_ne {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    localGate j G * localGate k H = localGate k H * localGate j G := by
  classical
  ext y x
  by_cases hyx : ∀ m : Fin n, m ≠ j → m ≠ k → y m = x m
  · rw [localGate_mul_ne_entry j k hjk G H y x hyx,
      localGate_mul_ne_entry k j (Ne.symm hjk) H G y x (fun m h1 h2 => hyx m h2 h1)]
    exact mul_comm _ _
  · rw [localGate_mul_ne_zero j k hjk G H y x hyx,
      localGate_mul_ne_zero k j (Ne.symm hjk) H G y x
        (by intro hQ; exact hyx (fun m h1 h2 => hQ m h2 h1))]

/-- A local gate commutes with a gate-list operator when every site in the list differs from its
site. -/
theorem localGateListOp_commute_of_distinct {n : ℕ} (gl : LocalGateList n) (j : Fin n)
    (h : ∀ p ∈ gl, p.1 ≠ j) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    localGateListOp gl * localGate j G = localGate j G * localGateListOp gl := by
  induction gl with
  | nil => simp [localGateListOp]
  | cons p rest ih =>
      have h1 : p.1 ≠ j := h p (List.mem_cons_self)
      have hrest : ∀ q ∈ rest, q.1 ≠ j := by
        intro q hq
        exact h q (List.mem_cons_of_mem _ hq)
      simp only [localGateListOp]
      rw [Matrix.mul_assoc, ih hrest, ← Matrix.mul_assoc,
        ← localGate_mul_localGate_ne j p.1 (Ne.symm h1) G p.2, Matrix.mul_assoc]

/-- Swapping the first two gates at distinct sites leaves a gate-list operator unchanged. -/
theorem localGateListOp_swap {n : ℕ} (p q : Fin n × Matrix (Fin 2) (Fin 2) ℂ)
    (gl : LocalGateList n) (h : p.1 ≠ q.1) :
    localGateListOp (p :: q :: gl) = localGateListOp (q :: p :: gl) := by
  simp only [localGateListOp]
  rw [← Matrix.mul_assoc, localGate_mul_localGate_ne p.1 q.1 h p.2 q.2, Matrix.mul_assoc]

/-- For distinct sites, the product of two local gates equals the two-site embedding of their
tensor-product entries. -/
theorem twoSiteGate_eq_localGate_mul {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    localGate i G * localGate j H
      = twoSiteGate i j (fun a c => G a.1 c.1 * H a.2 c.2) := by
  classical
  ext y x
  by_cases hyx : ∀ m : Fin n, m ≠ i → m ≠ j → y m = x m
  · rw [localGate_mul_ne_entry i j hij G H y x hyx]
    unfold twoSiteGate
    rw [Matrix.of_apply, if_pos hyx]
  · rw [localGate_mul_ne_zero i j hij G H y x hyx]
    unfold twoSiteGate
    rw [Matrix.of_apply, if_neg hyx]

/-- The sum of forward and backward hopping monomials is Hermitian. -/
theorem hoppingTerm_hermitian {n : ℕ} (i j : Fin n) :
    (creation i * annihilation j + creation j * annihilation i)ᴴ
      = creation i * annihilation j + creation j * annihilation i := by
  rw [Matrix.conjTranspose_add, creation_mul_annihilation_conjTranspose,
    creation_mul_annihilation_conjTranspose]
  exact add_comm _ _

/-- Hamiltonian evolution under the symmetric hopping operator is unitary. -/
theorem hamiltonianEvolution_hoppingTerm_unitary {n : ℕ} (i j : Fin n) (s : ℝ) :
    HamiltonianEvolution (creation i * annihilation j + creation j * annihilation i) s
      ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply hamiltonianEvolution_unitary
  exact hoppingTerm_hermitian i j

/-- The commutator of the number operator with creation at the same mode equals creation. -/
theorem numberOp_creation_commutator {n : ℕ} (i : Fin n) :
    numberOp i * creation i - creation i * numberOp i = creation i := by
  have hsq_c : creation i * creation i = 0 := by
    have h' : creation i * creation i + creation i * creation i = 0 := by
      simpa using! (car_cre n i i)
    exact add_self_eq_zero_of_complex _ h'
  have hac' : annihilation i * creation i = 1 - creation i * annihilation i := by
    rw [annihilation_mul_creation_eq_one_sub_numberOp i,
      creation_mul_annihilation_eq_numberOp i]
  have hna : numberOp i = creation i * annihilation i :=
    (creation_mul_annihilation_eq_numberOp i).symm
  calc numberOp i * creation i - creation i * numberOp i
      = (creation i * annihilation i) * creation i
        - creation i * (creation i * annihilation i) := by rw [hna]
    _ = creation i * (annihilation i * creation i)
        - creation i * (creation i * annihilation i) := by noncomm_ring
    _ = creation i * (1 - creation i * annihilation i)
        - creation i * (creation i * annihilation i) := by rw [hac']
    _ = creation i * 1 - (creation i * creation i) * annihilation i
        - (creation i * creation i) * annihilation i := by
          rw [Matrix.mul_sub]; simp only [← Matrix.mul_assoc]
    _ = creation i := by
      rw [hsq_c, Matrix.zero_mul, Matrix.mul_one, sub_zero, sub_zero]

/-- The commutator of the number operator with annihilation at the same mode equals minus
annihilation. -/
theorem numberOp_annihilation_commutator {n : ℕ} (i : Fin n) :
    numberOp i * annihilation i - annihilation i * numberOp i = -annihilation i := by
  have hsq_a : annihilation i * annihilation i = 0 := by
    have h' : annihilation i * annihilation i + annihilation i * annihilation i = 0 := by
      simpa using! (car_ann n i i)
    exact add_self_eq_zero_of_complex _ h'
  have hac' : annihilation i * creation i = 1 - creation i * annihilation i := by
    rw [annihilation_mul_creation_eq_one_sub_numberOp i,
      creation_mul_annihilation_eq_numberOp i]
  have hna : numberOp i = creation i * annihilation i :=
    (creation_mul_annihilation_eq_numberOp i).symm
  calc numberOp i * annihilation i - annihilation i * numberOp i
      = (creation i * annihilation i) * annihilation i
        - annihilation i * (creation i * annihilation i) := by rw [hna]
    _ = creation i * (annihilation i * annihilation i)
        - (annihilation i * creation i) * annihilation i := by noncomm_ring
    _ = 0 - (1 - creation i * annihilation i) * annihilation i := by
          rw [hsq_a, Matrix.mul_zero, hac']
    _ = -annihilation i + (creation i * annihilation i) * annihilation i := by
          rw [zero_sub, Matrix.sub_mul, Matrix.one_mul]; noncomm_ring

    _ = -annihilation i := by
      have hz : numberOp i * annihilation i = 0 := by
        calc numberOp i * annihilation i
            = (creation i * annihilation i) * annihilation i := by rw [hna]
          _ = creation i * (annihilation i * annihilation i) := by noncomm_ring
          _ = 0 := by rw [hsq_a, Matrix.mul_zero]
      rw [creation_mul_annihilation_eq_numberOp i, hz, add_zero]

/-- The four weighted local gate lists encoding the two number terms and two hopping terms of a
quadratic term. -/
def quadraticTermWord {n : ℕ} (t : QuadraticTerm n) : LocalGateSum n :=
  [(t.A 0 0, numberGateList t.i), (t.A 0 1, hopForwardGateList t.i t.j),
   (t.A 1 0, hopBackwardGateList t.i t.j), (t.A 1 1, numberGateList t.j)]

/-- The operator of concatenated weighted gate lists is the sum of their operators. -/
theorem localGateSumOp_append {n : ℕ} (l₁ l₂ : LocalGateSum n) :
    localGateSumOp (l₁ ++ l₂) = localGateSumOp l₁ + localGateSumOp l₂ := by
  induction l₁ with
  | nil => simp [localGateSumOp]
  | cons c rest ih =>
      cases c with
      | mk a gl =>
          simp only [List.cons_append, localGateSumOp]
          rw [ih]
          abel

/-- The total gate count of weighted gate lists is additive under concatenation. -/
theorem localGateSumCount_append {n : ℕ} (l₁ l₂ : LocalGateSum n) :
    localGateSumCount (l₁ ++ l₂) = localGateSumCount l₁ + localGateSumCount l₂ := by
  induction l₁ with
  | nil => simp [localGateSumCount]
  | cons c rest ih =>
      cases c with
      | mk a gl =>
          simp only [List.cons_append, localGateSumCount]
          rw [ih]
          omega

/-- The operator of a flattened list of weighted gate lists equals the sum of their operators,
expressed as a right fold. -/
theorem localGateSumOp_flatMap {n : ℕ} {α : Type} (f : α → LocalGateSum n) (l : List α) :
    localGateSumOp (l.flatMap f)
      = l.foldr (fun a acc => localGateSumOp (f a) + acc) 0 := by
  induction l with
  | nil => simp [localGateSumOp]
  | cons a l ih =>
      rw [List.flatMap_cons, localGateSumOp_append, List.foldr_cons, ih]

/-- The gate count of a flattened list of weighted gate lists equals the sum of their counts,
expressed as a right fold. -/
theorem localGateSumCount_flatMap {n : ℕ} {α : Type} (f : α → LocalGateSum n) (l : List α) :
    localGateSumCount (l.flatMap f)
      = l.foldr (fun a acc => localGateSumCount (f a) + acc) 0 := by
  induction l with
  | nil => simp [localGateSumCount]
  | cons a l ih =>
      rw [List.flatMap_cons, localGateSumCount_append, List.foldr_cons, ih]

/-- The weighted gate lists of a quadratic term represent its quadratic generator. -/
theorem quadraticTermWord_op {n : ℕ} (t : QuadraticTerm n) :
    localGateSumOp (quadraticTermWord t) = quadraticGenerator t.i t.j t.A := by
  simp only [quadraticTermWord, localGateSumOp]
  rw [quadraticGenerator_eq_localTerms t.i t.j t.hij t.A]
  rw [numberGateList_op t.i, numberGateList_op t.j, hopForwardGateList_op t.i t.j t.hij,
    hopBackwardGateList_op t.i t.j t.hij]
  abel

/-- The local gate count for a quadratic term is `2 * (t.j.val - t.i.val) + 6`. -/
theorem quadraticTermWord_count {n : ℕ} (t : QuadraticTerm n) :
    localGateSumCount (quadraticTermWord t) = 2 * (t.j.val - t.i.val) + 6 := by
  simp only [quadraticTermWord, localGateSumCount]
  rw [numberGateList_count, hopForwardGateList_count t.i t.j t.hij,
    hopBackwardGateList_count t.i t.j t.hij, numberGateList_count]
  omega

/-- The weighted local gate lists obtained by concatenating the encodings of a list of quadratic
terms. -/
def quadraticHamiltonianWord {n : ℕ} (terms : List (QuadraticTerm n)) : LocalGateSum n :=
  terms.flatMap quadraticTermWord

/-- The quadratic Hamiltonian word represents the sum of the quadratic generators in its term
list. -/
theorem quadraticHamiltonianWord_op {n : ℕ} (terms : List (QuadraticTerm n)) :
    localGateSumOp (quadraticHamiltonianWord terms)
      = terms.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0 := by
  rw [quadraticHamiltonianWord, localGateSumOp_flatMap]
  induction terms with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldr_cons]
      rw [quadraticTermWord_op, ih]

/-- The difference between the quadratic Hamiltonian word operator and the sum of its generators
is zero. -/
theorem quadraticHamiltonianWord_error {n : ℕ} (terms : List (QuadraticTerm n)) :
    (localGateSumOp (quadraticHamiltonianWord terms)
      - terms.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0) = 0 := by
  rw [quadraticHamiltonianWord_op]
  simp

/-- The gate count for a quadratic term on `n` modes is at most `2 * n + 4`. -/
theorem quadraticTermWord_count_le {n : ℕ} (t : QuadraticTerm n) :
    localGateSumCount (quadraticTermWord t) ≤ 2 * n + 4 := by
  rw [quadraticTermWord_count]
  have hj : t.j.val < n := t.j.isLt
  have hi : 0 ≤ t.i.val := Nat.zero_le _
  omega

/-- The gate count of a quadratic Hamiltonian word is at most `(2 * n + 4) * terms.length`. -/
theorem quadraticHamiltonianWord_count_le {n : ℕ} (terms : List (QuadraticTerm n)) :
    localGateSumCount (quadraticHamiltonianWord terms) ≤ (2 * n + 4) * terms.length := by
  rw [quadraticHamiltonianWord, localGateSumCount_flatMap]
  induction terms with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldr_cons]
      have h1 := quadraticTermWord_count_le t
      have h3 : (2 * n + 4) * (t :: rest).length
          = (2 * n + 4) * rest.length + (2 * n + 4) := by
        rw [List.length_cons]
        ring
      omega

/-- The bit cost of weighted local gate lists equals their total gate count times
`modeAddressBits n`. -/
theorem localGateSumBitCost_eq {n : ℕ} (l : LocalGateSum n) :
    localGateSumBitCost l = localGateSumCount l * modeAddressBits n := by
  induction l with
  | nil => simp [localGateSumBitCost, localGateSumCount]
  | cons c rest ih =>
      cases c with
      | mk a gl =>
          simp only [localGateSumBitCost, localGateSumCount]
          rw [localGateBitCost, ih]
          ring

/-- The bit cost of a quadratic Hamiltonian word is at most `(2 * n + 4) * terms.length *
modeAddressBits n`. -/
theorem quadraticHamiltonianWord_bitCost_le {n : ℕ} (terms : List (QuadraticTerm n)) :
    localGateSumBitCost (quadraticHamiltonianWord terms)
      ≤ (2 * n + 4) * terms.length * modeAddressBits n := by
  rw [localGateSumBitCost_eq]
  exact Nat.mul_le_mul_right _ (quadraticHamiltonianWord_count_le terms)

/-- The defined space cost of any weighted local gate list is at most `n`. -/
theorem localGateSumSpaceCost_le {n : ℕ} (l : LocalGateSum n) :
    localGateSumSpaceCost l ≤ n := by
  induction l with
  | nil => simp [localGateSumSpaceCost]
  | cons c rest ih =>
      cases c with
      | mk a gl =>
          simp only [localGateSumSpaceCost]
          omega

/-- The defined space cost of a quadratic Hamiltonian word is at most `n`. -/
theorem quadraticHamiltonianWord_spaceCost_le {n : ℕ} (terms : List (QuadraticTerm n)) :
    localGateSumSpaceCost (quadraticHamiltonianWord terms) ≤ n := by
  exact localGateSumSpaceCost_le (quadraticHamiltonianWord terms)

/-- The concatenated weighted gate-list encodings of one-body number terms and two-mode
quadratic terms. -/
def generalQuadraticHamiltonianWord {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) : LocalGateSum n :=
  oneBody.flatMap oneBodyWord ++ twoBody.flatMap quadraticTermWord

/-- A one-body word represents its coefficient times the number operator at its mode. -/
theorem oneBodyWord_op {n : ℕ} (t : OneBodyTerm n) :
    localGateSumOp (oneBodyWord t) = t.h • numberOp t.i := by
  simp only [oneBodyWord, localGateSumOp]
  rw [numberGateList_op t.i]
  simp

/-- A one-body word has local gate count one. -/
theorem oneBodyWord_count {n : ℕ} (t : OneBodyTerm n) :
    localGateSumCount (oneBodyWord t) = 1 := by
  simp [oneBodyWord, localGateSumCount, numberGateList_count]

/-- A one-body word operator has zero entries between distinct registers. -/
theorem oneBodyWord_op_diagonal {n : ℕ} (t : OneBodyTerm n) (y x : Reg n) (h : y ≠ x) :
    localGateSumOp (oneBodyWord t) y x = 0 := by
  rw [oneBodyWord_op, numberOp_eq_diagonal, Matrix.smul_apply]
  rw [Matrix.diagonal_apply_ne' _ h.symm]
  simp

/-- The gate count of a quadratic term word is at least six. -/
theorem quadraticTermWord_count_ge_six {n : ℕ} (t : QuadraticTerm n) :
    6 ≤ localGateSumCount (quadraticTermWord t) := by
  rw [quadraticTermWord_count]
  omega

/-- The general quadratic Hamiltonian word represents the sum of its weighted number operators
and quadratic generators. -/
theorem generalQuadraticHamiltonianWord_op {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) :
    localGateSumOp (generalQuadraticHamiltonianWord oneBody twoBody)
      = oneBody.foldr (fun t acc => t.h • numberOp t.i + acc) 0
        + twoBody.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0 := by
  rw [generalQuadraticHamiltonianWord, localGateSumOp_append, localGateSumOp_flatMap,
    localGateSumOp_flatMap]
  have hone : oneBody.foldr (fun t acc => localGateSumOp (oneBodyWord t) + acc) 0
      = oneBody.foldr (fun t acc => t.h • numberOp t.i + acc) 0 := by
    induction oneBody with
    | nil => simp
    | cons t rest ih =>
        simp only [List.foldr_cons]
        rw [oneBodyWord_op, ih]
  have htwo : twoBody.foldr (fun t acc => localGateSumOp (quadraticTermWord t) + acc) 0
      = twoBody.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0 := by
    induction twoBody with
    | nil => simp
    | cons t rest ih =>
        simp only [List.foldr_cons]
        rw [quadraticTermWord_op, ih]
  rw [hone, htwo]

/-- The difference between the general quadratic Hamiltonian word operator and its specified sum
of terms is zero. -/
theorem generalQuadraticHamiltonianWord_error {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) :
    (localGateSumOp (generalQuadraticHamiltonianWord oneBody twoBody)
      - (oneBody.foldr (fun t acc => t.h • numberOp t.i + acc) 0
        + twoBody.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0)) = 0 := by
  rw [generalQuadraticHamiltonianWord_op]
  simp

/-- The general quadratic Hamiltonian word has one gate per one-body term plus `2 * (t.j.val -
t.i.val) + 6` gates per quadratic term. -/
theorem generalQuadraticHamiltonianWord_count {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) :
    localGateSumCount (generalQuadraticHamiltonianWord oneBody twoBody)
      = oneBody.length
        + twoBody.foldr (fun t acc => 2 * (t.j.val - t.i.val) + 6 + acc) 0 := by
  rw [generalQuadraticHamiltonianWord, localGateSumCount_append, localGateSumCount_flatMap,
    localGateSumCount_flatMap]
  have hone : oneBody.foldr (fun t acc => localGateSumCount (oneBodyWord t) + acc) 0
      = oneBody.length := by
    induction oneBody with
    | nil => simp
    | cons t rest ih =>
        simp only [List.foldr_cons, List.length_cons]
        rw [oneBodyWord_count, ih]
        omega
  have htwo : twoBody.foldr (fun t acc => localGateSumCount (quadraticTermWord t) + acc) 0
      = twoBody.foldr (fun t acc => 2 * (t.j.val - t.i.val) + 6 + acc) 0 := by
    induction twoBody with
    | nil => simp
    | cons t rest ih =>
        simp only [List.foldr_cons]
        rw [quadraticTermWord_count, ih]
  rw [hone, htwo]

/-- The general quadratic Hamiltonian word has gate count at most `oneBody.length + (2 * n + 4)
* twoBody.length`. -/
theorem generalQuadraticHamiltonianWord_count_le {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) :
    localGateSumCount (generalQuadraticHamiltonianWord oneBody twoBody)
      ≤ oneBody.length + (2 * n + 4) * twoBody.length := by
  rw [generalQuadraticHamiltonianWord_count]
  have htwo : twoBody.foldr (fun t acc => 2 * (t.j.val - t.i.val) + 6 + acc) 0
      ≤ (2 * n + 4) * twoBody.length := by
    induction twoBody with
    | nil => simp
    | cons t rest ih =>
        simp only [List.foldr_cons]
        have h1 := quadraticTermWord_count t
        have h2 := quadraticTermWord_count_le t
        have h3 : (2 * n + 4) * (t :: rest).length
            = (2 * n + 4) * rest.length + (2 * n + 4) := by
          rw [List.length_cons]
          ring
        omega
  omega

/-- The general quadratic Hamiltonian word has bit cost at most `(oneBody.length + (2 * n + 4) *
twoBody.length) * modeAddressBits n`. -/
theorem generalQuadraticHamiltonianWord_bitCost_le {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) :
    localGateSumBitCost (generalQuadraticHamiltonianWord oneBody twoBody)
      ≤ (oneBody.length + (2 * n + 4) * twoBody.length) * modeAddressBits n := by
  rw [localGateSumBitCost_eq]
  exact Nat.mul_le_mul_right _ (generalQuadraticHamiltonianWord_count_le oneBody twoBody)

/-- The defined space cost of a general quadratic Hamiltonian word is at most `n`. -/
theorem generalQuadraticHamiltonianWord_spaceCost_le {n : ℕ} (oneBody : List (OneBodyTerm n))
    (twoBody : List (QuadraticTerm n)) :
    localGateSumSpaceCost (generalQuadraticHamiltonianWord oneBody twoBody) ≤ n :=
  localGateSumSpaceCost_le _

/-- Every pair in `modePairList n` has its first mode strictly below its second. -/
theorem modePairList_lt {n : ℕ} {p : Fin n × Fin n} (hp : p ∈ modePairList n) : p.1 < p.2 := by
  rw [modePairList, Finset.mem_toList] at hp
  exact (Finset.mem_filter.mp hp).2

/-- The mode-pair list has length at most `n * n`. -/
theorem modePairList_length_le (n : ℕ) : (modePairList n).length ≤ n * n := by
  rw [modePairList, Finset.length_toList]
  have h1 : modePairs n ⊆ (Finset.univ : Finset (Fin n × Fin n)) := Finset.filter_subset _ _
  have h2 := Finset.card_mono h1
  simpa [Fintype.card_prod, Fintype.card_fin] using! h2

/-- A quadratic Hamiltonian word with at most `n * n` terms has gate count at most `(2 * n + 4)
* n ^ 2`. -/
theorem quadraticHamiltonianWord_count_le_pow {n : ℕ} (terms : List (QuadraticTerm n))
    (h : terms.length ≤ n * n) :
    localGateSumCount (quadraticHamiltonianWord terms) ≤ (2 * n + 4) * n ^ 2 := by
  have h1 := quadraticHamiltonianWord_count_le terms
  calc localGateSumCount (quadraticHamiltonianWord terms)
      ≤ (2 * n + 4) * terms.length := h1
    _ ≤ (2 * n + 4) * (n * n) := Nat.mul_le_mul (le_refl _) h
    _ = (2 * n + 4) * n ^ 2 := by ring

/-- For positive `n`, a quadratic Hamiltonian word with at most `n * n` terms has gate count at
most `8 * n ^ 3`. -/
theorem quadraticHamiltonianWord_count_le_cubic {n : ℕ} (terms : List (QuadraticTerm n))
    (hn : 0 < n) (h : terms.length ≤ n * n) :
    localGateSumCount (quadraticHamiltonianWord terms) ≤ 8 * n ^ 3 := by
  have h1 := quadraticHamiltonianWord_count_le_pow terms h
  have h2 : 2 * n + 4 ≤ 8 * n := by omega
  calc localGateSumCount (quadraticHamiltonianWord terms)
      ≤ (2 * n + 4) * n ^ 2 := h1
    _ ≤ (8 * n) * n ^ 2 := Nat.mul_le_mul h2 (le_refl _)
    _ = 8 * n ^ 3 := by ring

/-- The Hubbard onsite word represents `μ` times the number operator at its mode. -/
theorem hubbardOnsiteWord_op {n : ℕ} (μ : ℂ) (i : Fin n) :
    localGateSumOp (hubbardOnsiteWord μ i) = μ • numberOp i := by
  simp only [hubbardOnsiteWord, localGateSumOp, add_zero]
  rw [numberGateList_op]

/-- The Hubbard interaction word represents `U` times the product of the two number operators. -/
theorem hubbardInteractionWord_op {n : ℕ} (U : ℂ) (i j : Fin n) :
    localGateSumOp (hubbardInteractionWord U i j) = U • (numberOp i * numberOp j) := by
  simp only [hubbardInteractionWord, localGateSumOp, add_zero]
  rw [localGateListOp_append, numberGateList_op, numberGateList_op]

/-- For `i < j`, the Hubbard hopping word represents `t` times the sum of forward and backward
hopping monomials. -/
theorem hubbardHoppingWord_op {n : ℕ} (t : ℂ) (i j : Fin n) (hij : i < j) :
    localGateSumOp (hubbardHoppingWord t i j)
      = t • (creation i * annihilation j + creation j * annihilation i) := by
  simp only [hubbardHoppingWord, localGateSumOp, add_zero]
  rw [hopForwardGateList_op i j hij, hopBackwardGateList_op i j hij]
  rw [← smul_add]

/-- A right fold over a mapped list equals a right fold applying the mapping inside the folding
function. -/
theorem foldr_map {α : Type} {β : Type} {γ : Type} (g : α → β) (f : β → γ → γ)
    (l : List α) (b : γ) :
    (l.map g).foldr f b = l.foldr (fun a acc => f (g a) acc) b := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih]

/-- A right fold over a concatenation folds the second list first and uses its result as the
initial value for the first list. -/
theorem foldr_append' {α : Type} {γ : Type} (f : α → γ → γ) (l₁ l₂ : List α) (b : γ) :
    (l₁ ++ l₂).foldr f b = l₁.foldr f (l₂.foldr f b) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, List.foldr_cons, ih]

/-- An additive right fold with initial value `x` equals the same fold with initial value zero
plus `x`. -/
theorem foldr_add_const {α : Type} {γ : Type} [AddCommMonoid γ] (g : α → γ) (l : List α)
    (x : γ) :
    l.foldr (fun a acc => g a + acc) x = l.foldr (fun a acc => g a + acc) 0 + x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons]
      rw [ih]
      abel

/-- Every pair in `fermionPairs n` has its first mode strictly below its second. -/
theorem fermionPairs_lt {n : ℕ} {p : Fin n × Fin n} (hp : p ∈ fermionPairs n) : p.1 < p.2 := by
  unfold fermionPairs at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨i, -, hp⟩ := hp
  rw [List.mem_filterMap] at hp
  obtain ⟨j, hj, heq⟩ := hp
  by_cases hij : i < j
  · rw [if_pos hij] at heq
    have hpair : (i, j) = p := Option.some.inj heq
    obtain ⟨rfl, rfl⟩ := hpair
    exact hij
  · rw [if_neg hij] at heq
    cases heq

/-- Folding Hubbard onsite word operators equals folding the corresponding weighted number
operators with the same initial matrix. -/
theorem hubbardOnsiteFold {n : ℕ} (l : List (Fin n)) (μ : ℂ) (acc : Matrix (Reg n) (Reg n) ℂ) :
    l.foldr (fun i acc => localGateSumOp (hubbardOnsiteWord μ i) + acc) acc
      = l.foldr (fun i acc => μ • numberOp i + acc) acc := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldr_cons]
      rw [hubbardOnsiteWord_op, ih]

/-- Folding Hubbard interaction word operators equals folding the corresponding weighted
products of number operators with the same initial matrix. -/
theorem hubbardInteractionFold {n : ℕ} (l : List (Fin n × Fin n)) (U : ℂ)
    (acc : Matrix (Reg n) (Reg n) ℂ) :
    l.foldr (fun p acc => localGateSumOp (hubbardInteractionWord U p.1 p.2) + acc) acc
      = l.foldr (fun p acc => U • (numberOp p.1 * numberOp p.2) + acc) acc := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.foldr_cons]
      rw [hubbardInteractionWord_op, ih]

/-- For a list of strictly ordered mode pairs, folding Hubbard hopping word operators equals
folding the weighted symmetric hopping operators. -/
theorem hubbardHoppingFold {n : ℕ} {l : List (Fin n × Fin n)} (t : ℂ)
    (acc : Matrix (Reg n) (Reg n) ℂ) (hl : ∀ p ∈ l, p.1 < p.2) :
    l.foldr (fun p acc => localGateSumOp (hubbardHoppingWord t p.1 p.2) + acc) acc
      = l.foldr
          (fun p acc => t • (creation p.1 * annihilation p.2 + creation p.2 * annihilation p.1) + acc)
          acc := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.foldr_cons]
      rw [hubbardHoppingWord_op t p.1 p.2 (hl p (List.mem_cons_self))]
      rw [ih (fun q hq => hl q (List.mem_cons_of_mem p hq))]

/-- The Hubbard term sum equals its onsite sum plus its interaction and hopping sums. -/
theorem hubbardTermSum_eq {n : ℕ} (t μ U : ℂ) :
    hubbardTermSum (n := n) t μ U
      = hubbardOnsiteSum (n := n) μ
        + (hubbardInteractionSum (n := n) U + hubbardHoppingSum (n := n) t) := by
  unfold hubbardTermSum hubbardJWTerms
  rw [foldr_append', foldr_append', foldr_map, foldr_map, foldr_map]
  rw [foldr_add_const (fun p => U • (numberOp p.1 * numberOp p.2)) (fermionPairs n)
      (List.foldr
          (fun a acc => t • (creation a.1 * annihilation a.2 + creation a.2 * annihilation a.1) + acc)
          0 (fermionPairs n))]
  rw [foldr_add_const (fun i => μ • numberOp i) (List.finRange n)
      (List.foldr (fun a acc => U • (numberOp a.1 * numberOp a.2) + acc) 0 (fermionPairs n)
        + List.foldr
            (fun a acc => t • (creation a.1 * annihilation a.2 + creation a.2 * annihilation a.1) + acc)
            0 (fermionPairs n))]
  rfl

/-- The Hubbard Hamiltonian word represents the sum of the onsite, interaction, and hopping
contributions. -/
theorem hubbardHamiltonianWord_op {n : ℕ} (t μ U : ℂ) :
    localGateSumOp (hubbardHamiltonianWord (n := n) t μ U)
      = hubbardOnsiteSum (n := n) μ
        + (hubbardInteractionSum (n := n) U + hubbardHoppingSum (n := n) t) := by
  rw [hubbardHamiltonianWord, localGateSumOp_append, localGateSumOp_append,
    localGateSumOp_flatMap, localGateSumOp_flatMap, localGateSumOp_flatMap,
    hubbardOnsiteFold, hubbardInteractionFold]
  rw [hubbardHoppingFold t 0 (fun p hp => fermionPairs_lt hp)]
  unfold hubbardOnsiteSum hubbardInteractionSum hubbardHoppingSum
  abel

/-- The Hubbard Hamiltonian word operator equals `hubbardTermSum`. -/
theorem hubbardHamiltonianWord_eq_termSum {n : ℕ} (t μ U : ℂ) :
    localGateSumOp (hubbardHamiltonianWord (n := n) t μ U) = hubbardTermSum (n := n) t μ U := by
  rw [hubbardHamiltonianWord_op, hubbardTermSum_eq]

/-- The difference between the Hubbard Hamiltonian word operator and `hubbardTermSum` is zero. -/
theorem hubbardHamiltonianWord_error {n : ℕ} (t μ U : ℂ) :
    (localGateSumOp (hubbardHamiltonianWord (n := n) t μ U) - hubbardTermSum (n := n) t μ U) = 0 := by
  rw [hubbardHamiltonianWord_eq_termSum]
  simp

/-- A Hubbard onsite word has local gate count one. -/
theorem hubbardOnsiteWord_count {n : ℕ} (μ : ℂ) (i : Fin n) :
    localGateSumCount (hubbardOnsiteWord μ i) = 1 := by
  simp only [hubbardOnsiteWord, localGateSumCount]
  rw [numberGateList_count]

/-- A Hubbard interaction word has local gate count two. -/
theorem hubbardInteractionWord_count {n : ℕ} (U : ℂ) (i j : Fin n) :
    localGateSumCount (hubbardInteractionWord U i j) = 2 := by
  simp only [hubbardInteractionWord, localGateSumCount, localGateCount_eq_length, numberGateList,
    List.length_append, List.length_cons, List.length_nil]

/-- For `i < j`, a Hubbard hopping word has local gate count `2 * (j.val - i.val) + 4`. -/
theorem hubbardHoppingWord_count {n : ℕ} (t : ℂ) (i j : Fin n) (hij : i < j) :
    localGateSumCount (hubbardHoppingWord t i j) = 2 * (j.val - i.val) + 4 := by
  simp only [hubbardHoppingWord, localGateSumCount]
  rw [hopForwardGateList_count i j hij, hopBackwardGateList_count i j hij]
  omega

/-- A right fold adding a constant `k` at every list element equals `k * l.length` plus its
initial value. -/
theorem foldr_const {α : Type} (k : ℕ) (l : List α) (acc : ℕ) :
    l.foldr (fun _ acc => k + acc) acc = k * l.length + acc := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [ih]
      omega

/-- An additive right fold of nonnegative integer weights bounded by `C` is at most `C` times
the list length. -/
theorem foldr_count_le {α : Type} (g : α → ℕ) (C : ℕ) : ∀ (l : List α),
    (∀ a ∈ l, g a ≤ C) → l.foldr (fun a acc => g a + acc) 0 ≤ C * l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      simp only [List.foldr_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      have ha := h a (List.mem_cons_self)
      have hb : ∀ b ∈ l, g b ≤ C := fun b hb => h b (List.mem_cons_of_mem a hb)
      have hih := ih hb
      omega

/-- Filtering and mapping a list through an optional-valued function cannot increase its length. -/
theorem length_filterMap_le {α : Type} {β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases h : f a with
      | none =>
          have h1 : (a :: l).filterMap f = l.filterMap f := by
            simp only [List.filterMap_cons, h]
          simp only [h1, List.length_cons]
          omega
      | some b =>
          have h1 : (a :: l).filterMap f = b :: l.filterMap f := by
            simp only [List.filterMap_cons, h]
          simp only [h1, List.length_cons]
          omega

/-- If each mapped list has length at most `k`, the flattened list has length at most `k` times
the original length. -/
theorem length_flatMap_le {α : Type} {β : Type} (f : α → List β) : ∀ (l : List α) (k : ℕ),
    (∀ a ∈ l, (f a).length ≤ k) → (l.flatMap f).length ≤ k * l.length := by
  intro l k
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      have ha := h a (List.mem_cons_self)
      have hb : ∀ b ∈ l, (f b).length ≤ k := fun b hb => h b (List.mem_cons_of_mem a hb)
      have hih := ih hb
      omega

/-- The fermionic mode-pair list has length at most `n * n`. -/
theorem fermionPairs_length_le (n : ℕ) : (fermionPairs n).length ≤ n * n := by
  unfold fermionPairs
  refine le_trans (length_flatMap_le _ (List.finRange n) n ?_) ?_
  · intro i _
    exact le_trans (length_filterMap_le _ _) (by simp)
  · simp

/-- Folding Hubbard onsite gate counts is equivalent to adding one per mode with the same
initial count. -/
theorem hubbardOnsiteCountFold {n : ℕ} (l : List (Fin n)) (μ : ℂ) (acc : ℕ) :
    l.foldr (fun i acc => localGateSumCount (hubbardOnsiteWord μ i) + acc) acc
      = l.foldr (fun _ acc => 1 + acc) acc := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldr_cons]
      rw [hubbardOnsiteWord_count, ih]

/-- Folding Hubbard interaction gate counts is equivalent to adding two per mode pair with the
same initial count. -/
theorem hubbardInteractionCountFold {n : ℕ} (l : List (Fin n × Fin n)) (U : ℂ) (acc : ℕ) :
    l.foldr (fun p acc => localGateSumCount (hubbardInteractionWord U p.1 p.2) + acc) acc
      = l.foldr (fun _ acc => 2 + acc) acc := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.foldr_cons]
      rw [hubbardInteractionWord_count, ih]

/-- For strictly ordered mode pairs, the hopping count fold adds `2 * (p.2.val - p.1.val) + 4`
per pair. -/
theorem hubbardHoppingCountFold {n : ℕ} {l : List (Fin n × Fin n)} (t : ℂ) (acc : ℕ)
    (hl : ∀ p ∈ l, p.1 < p.2) :
    l.foldr (fun p acc => localGateSumCount (hubbardHoppingWord t p.1 p.2) + acc) acc
      = l.foldr (fun p acc => 2 * (p.2.val - p.1.val) + 4 + acc) acc := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.foldr_cons]
      rw [hubbardHoppingWord_count t p.1 p.2 (hl p (List.mem_cons_self))]
      rw [ih (fun q hq => hl q (List.mem_cons_of_mem p hq))]

/-- The Hubbard word gate count is at most `n` plus two per fermionic pair and at most `2 * n +
4` further gates per pair. -/
theorem hubbardHamiltonianWord_count_le {n : ℕ} (t μ U : ℂ) :
    localGateSumCount (hubbardHamiltonianWord (n := n) t μ U)
      ≤ n + 2 * (fermionPairs n).length + (2 * n + 4) * (fermionPairs n).length := by
  rw [hubbardHamiltonianWord, localGateSumCount_append, localGateSumCount_append,
    localGateSumCount_flatMap, localGateSumCount_flatMap, localGateSumCount_flatMap]
  rw [hubbardOnsiteCountFold, hubbardInteractionCountFold]
  rw [hubbardHoppingCountFold t 0 (fun p hp => fermionPairs_lt hp)]
  rw [foldr_const 1 (List.finRange n) 0, foldr_const 2 (fermionPairs n) 0]
  have hhop : (fermionPairs n).foldr (fun p acc => 2 * (p.2.val - p.1.val) + 4 + acc) 0
      ≤ (2 * n + 4) * (fermionPairs n).length := by
    refine foldr_count_le (fun p => 2 * (p.2.val - p.1.val) + 4) (2 * n + 4)
      (fermionPairs n) ?_
    intro p hp
    have hlt := fermionPairs_lt hp
    have hp2 := p.2.isLt
    (try dsimp only)
    omega
  have hmain : 2 * (fermionPairs n).length
        + (fermionPairs n).foldr (fun p acc => 2 * (p.2.val - p.1.val) + 4 + acc) 0
      ≤ 2 * (fermionPairs n).length + (2 * n + 4) * (fermionPairs n).length :=
    Nat.add_le_add_left hhop _
  simp only [List.length_finRange, Nat.one_mul, add_zero]
  omega

/-- The Hubbard Hamiltonian word has gate count at most `2 * n ^ 3 + 6 * n ^ 2 + n`. -/
theorem hubbardHamiltonianWord_count_le_pow {n : ℕ} (t μ U : ℂ) :
    localGateSumCount (hubbardHamiltonianWord (n := n) t μ U)
      ≤ 2 * n ^ 3 + 6 * n ^ 2 + n := by
  have h1 := hubbardHamiltonianWord_count_le (n := n) t μ U
  have hp := fermionPairs_length_le n
  calc localGateSumCount (hubbardHamiltonianWord (n := n) t μ U)
      ≤ n + 2 * (fermionPairs n).length + (2 * n + 4) * (fermionPairs n).length := h1
    _ ≤ n + 2 * (n * n) + (2 * n + 4) * (n * n) := by
        have h2 : 2 * (fermionPairs n).length ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 hp
        have h3 : (2 * n + 4) * (fermionPairs n).length ≤ (2 * n + 4) * (n * n) :=
          Nat.mul_le_mul_left (2 * n + 4) hp
        exact Nat.add_le_add (Nat.add_le_add_left h2 n) h3
    _ = 2 * n ^ 3 + 6 * n ^ 2 + n := by ring

/-- For positive `n`, the Hubbard Hamiltonian word has gate count at most `9 * n ^ 3`. -/
theorem hubbardHamiltonianWord_count_le_cubic {n : ℕ} (t μ U : ℂ) (hn : 0 < n) :
    localGateSumCount (hubbardHamiltonianWord (n := n) t μ U) ≤ 9 * n ^ 3 := by
  have h1 := hubbardHamiltonianWord_count_le_pow (n := n) t μ U
  have hp2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (show 2 ≤ 3 by omega)
  have hp3 : n ≤ n ^ 3 := by
    have hp3' := Nat.pow_le_pow_right hn (show 1 ≤ 3 by omega)
    simpa using! hp3'
  have h6 : 6 * n ^ 2 ≤ 6 * n ^ 3 := Nat.mul_le_mul_left 6 hp2
  calc localGateSumCount (hubbardHamiltonianWord (n := n) t μ U)
      ≤ 2 * n ^ 3 + 6 * n ^ 2 + n := h1
    _ ≤ 2 * n ^ 3 + 6 * n ^ 3 + n ^ 3 := Nat.add_le_add (Nat.add_le_add_left h6 (2 * n ^ 3)) hp3
    _ = 9 * n ^ 3 := by ring

/-- The Hubbard Hamiltonian word has bit cost at most `(2 * n ^ 3 + 6 * n ^ 2 + n) *
modeAddressBits n`. -/
theorem hubbardHamiltonianWord_bitCost_le {n : ℕ} (t μ U : ℂ) :
    localGateSumBitCost (hubbardHamiltonianWord (n := n) t μ U)
      ≤ (2 * n ^ 3 + 6 * n ^ 2 + n) * modeAddressBits n := by
  rw [localGateSumBitCost_eq]
  exact Nat.mul_le_mul_right _ (hubbardHamiltonianWord_count_le_pow (n := n) t μ U)

/-- The defined space cost of the Hubbard Hamiltonian word is at most `n`. -/
theorem hubbardHamiltonianWord_spaceCost_le {n : ℕ} (t μ U : ℂ) :
    localGateSumSpaceCost (hubbardHamiltonianWord (n := n) t μ U) ≤ n := by
  exact localGateSumSpaceCost_le _

/-- Complex scalar multiples of commuting square matrices commute. -/
theorem commute_smul_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : Commute A B) (r q : ℂ) :
    Commute (r • A) (q • B) := by
  rw [commute_iff_eq]
  ext y x
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have hsum : (∑ z, A y z * B z x) = ∑ z, B y z * A z x := by
    have hcon := congrArg (fun M : Matrix ι ι ℂ => M y x) h.eq
    simpa only [Matrix.mul_apply] using! hcon
  calc
    (∑ z, (r * A y z) * (q * B z x))
        = ∑ z, (r * q) * (A y z * B z x) := by
          apply Finset.sum_congr rfl
          intro z hz
          ring
    _ = (r * q) * ∑ z, (A y z * B z x) := by rw [Finset.mul_sum]
    _ = (r * q) * ∑ z, (B y z * A z x) := by rw [hsum]
    _ = ∑ z, (r * q) * (B y z * A z x) := by rw [← Finset.mul_sum]
    _ = ∑ z, (q * B y z) * (r * A z x) := by
          apply Finset.sum_congr rfl
          intro z hz
          ring

/-- For commuting generators, the product of their Hamiltonian evolutions at the same time
equals evolution under their sum. -/
theorem hamiltonianEvolution_trotter_exact_of_commute {n : ℕ}
    (T₁ T₂ : Matrix (Reg n) (Reg n) ℂ) (s : ℝ) (h : Commute T₁ T₂) :
    HamiltonianEvolution T₁ s * HamiltonianEvolution T₂ s
      = HamiltonianEvolution (T₁ + T₂) s := by
  have hcomm : Commute ((-Complex.I * (s : ℂ)) • T₁) ((-Complex.I * (s : ℂ)) • T₂) :=
    commute_smul_smul h (-Complex.I * (s : ℂ)) (-Complex.I * (s : ℂ))
  have hexp : NormedSpace.exp ((-Complex.I * (s : ℂ)) • T₁)
        * NormedSpace.exp ((-Complex.I * (s : ℂ)) • T₂)
      = NormedSpace.exp ((-Complex.I * (s : ℂ)) • T₁ + (-Complex.I * (s : ℂ)) • T₂) :=
    (Matrix.exp_add_of_commute _ _ hcomm).symm
  have hsum : ((-Complex.I * (s : ℂ)) • T₁ + (-Complex.I * (s : ℂ)) • T₂)
      = ((-Complex.I * (s : ℂ)) • (T₁ + T₂)) := by
    ext y x
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  rw [HamiltonianEvolution, HamiltonianEvolution, HamiltonianEvolution, hexp, hsum]

/-- Number operators at any two modes commute. -/
theorem numberOp_commute {n : ℕ} (i j : Fin n) : Commute (numberOp i) (numberOp j) := by
  rw [commute_iff_eq]
  ext y x
  rw [numberOp_eq_diagonal, numberOp_eq_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  by_cases h : x = y
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    exact mul_comm _ _
  · rw [Matrix.diagonal_apply_ne' _ h, Matrix.diagonal_apply_ne' _ h]

/-- The product of evolutions under two number operators equals evolution under their sum at the
same time. -/
theorem hamiltonianEvolution_trotter_exact_onsite {n : ℕ} (i j : Fin n) (s : ℝ) :
    HamiltonianEvolution (numberOp i) s * HamiltonianEvolution (numberOp j) s
      = HamiltonianEvolution (numberOp i + numberOp j) s := by
  exact hamiltonianEvolution_trotter_exact_of_commute (numberOp i) (numberOp j) s
    (numberOp_commute i j)

/-- For `i < j`, the Z-range set is obtained by inserting `i` into the strict Z-tail set. -/
theorem zRangeSet_eq_insert_tail {n : ℕ} (i j : Fin n) (hij : i < j) :
    zRangeSet i j = insert i (zTailSet i j) := by
  ext k
  simp only [zRangeSet, zTailSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hki : k = i
    · exact Or.inl hki
    · exact Or.inr ⟨by omega, h2⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, h2⟩

/-- The local diagonal entry of a Pauli Z gate is minus one on an occupied site and one
otherwise. -/
theorem localGateDiagEntry_oneQubitZ {n : ℕ} (k : Fin n) (y : Reg n) :
    localGateDiagEntry (k, oneQubitZ) y = (if y k then -1 else 1) := by
  cases h : y k <;>
    simp [localGateDiagEntry, oneQubitZ_diagEntry, h, boolEquivFin2_false,
      boolEquivFin2_true]

/-- In Boolean indices, the diagonal Pauli Z entry is minus one for occupation and one
otherwise. -/
theorem oneQubitZ_diagEntry_bool {n : ℕ} (k : Fin n) (y : Reg n) :
    oneQubitZ (boolEquivFin2 (y k)) (boolEquivFin2 (y k)) = (if y k then -1 else 1) := by
  exact localGateDiagEntry_oneQubitZ k y

/-- The diagonal entry of a list of Pauli Z gates over a finite site set is the product of the
corresponding occupation signs. -/
theorem zListOp_diag_entry {n : ℕ} (S : Finset (Fin n)) (y : Reg n) :
    localGateListOp (S.toList.map (fun k => (k, oneQubitZ))) y y
      = S.prod (fun k => (if y k then -1 else 1)) := by
  have h := localGateListOp_diag (S.toList.map (fun k => (k, oneQubitZ)))
    (fun p hp b c hbc => by
      simp only [List.mem_map] at hp
      obtain ⟨q, -, rfl⟩ := hp
      exact oneQubitZ_diagonal b c hbc) y y
  rw [if_pos rfl] at h
  rw [h, List.map_map, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro k hk
  exact localGateDiagEntry_oneQubitZ k y

/-- Adding a new site to a finite set of Pauli Z gates multiplies its operator by the local Z
gate at that site. -/
theorem zListOp_insert {n : ℕ} (S : Finset (Fin n)) (k : Fin n) (hk : k ∉ S) :
    localGateListOp ((insert k S).toList.map (fun m => (m, oneQubitZ)))
      = localGate k oneQubitZ * localGateListOp (S.toList.map (fun m => (m, oneQubitZ))) := by
  classical
  have hloc : ∀ (y z : Reg n), y ≠ z → localGate k oneQubitZ y z = 0 := by
    intro y z hne
    rw [localGate_diag_apply k oneQubitZ_diagonal y z, if_neg hne]
  have hdiagL : ∀ (y x : Reg n), y ≠ x →
      localGateListOp ((insert k S).toList.map (fun m => (m, oneQubitZ))) y x = 0 := by
    intro y x hne
    have h := localGateListOp_diag ((insert k S).toList.map (fun m => (m, oneQubitZ)))
      (fun p hp b c hbc => by
        simp only [List.mem_map] at hp
        obtain ⟨q, -, rfl⟩ := hp
        exact oneQubitZ_diagonal b c hbc) y x
    rw [if_neg hne] at h
    exact h
  have hdiagR : ∀ (y x : Reg n), y ≠ x →
      localGateListOp (S.toList.map (fun m => (m, oneQubitZ))) y x = 0 := by
    intro y x hne
    have h := localGateListOp_diag (S.toList.map (fun m => (m, oneQubitZ)))
      (fun p hp b c hbc => by
        simp only [List.mem_map] at hp
        obtain ⟨q, -, rfl⟩ := hp
        exact oneQubitZ_diagonal b c hbc) y x
    rw [if_neg hne] at h
    exact h
  ext y x
  by_cases hyx : y = x
  · subst hyx
    rw [mul_apply_diag_left _ _ hloc y y, zListOp_diag_entry (insert k S) y,
      zListOp_diag_entry S y, Finset.prod_insert hk,
      localGate_diag_apply k oneQubitZ_diagonal y y]
    simp only [if_true]
    rw [oneQubitZ_diagEntry_bool k y]
  · rw [hdiagL y x hyx, mul_apply_diag_left _ _ hloc y x, hdiagR y x hyx]
    simp

/-- For `i < j`, the Z-range operator factors into the Z gate at `i` times the strict Z-tail
operator. -/
theorem zRangeGateList_op_eq {n : ℕ} (i j : Fin n) (hij : i < j) :
    localGateListOp (zRangeGateList i j)
      = localGate i oneQubitZ * localGateListOp (zTailGateList i j) := by
  have hnotmem : i ∉ zTailSet i j := by
    simp only [zTailSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h
    omega
  rw [zRangeGateList, zTailGateList, zRangeSet_eq_insert_tail i j hij]
  exact zListOp_insert (zTailSet i j) i hnotmem

/-- Right multiplication of `sigmaPlus` by the Pauli Z matrix leaves `sigmaPlus` unchanged. -/
theorem sigmaPlus_mul_oneQubitZ : sigmaPlus * oneQubitZ = sigmaPlus := by
  have hone : oneQubitZ = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oneQubitZ, Matrix.of_apply]
  rw [hone, sigmaPlus_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Left multiplication of `sigmaMinus` by the Pauli Z matrix leaves `sigmaMinus` unchanged. -/
theorem oneQubitZ_mul_sigmaMinus : oneQubitZ * sigmaMinus = sigmaMinus := by
  have hone : oneQubitZ = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [oneQubitZ, Matrix.of_apply]
  rw [hone, sigmaMinus_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Every gate in a strict Z-tail list acts at a site distinct from `i`. -/
theorem zTailGateList_ne_i {n : ℕ} (i j : Fin n) {p : Fin n × Matrix (Fin 2) (Fin 2) ℂ}
    (hp : p ∈ zTailGateList i j) : p.1 ≠ i := by
  simp only [zTailGateList, List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  simp only [Finset.mem_toList] at hk
  simp only [zTailSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hlt : i.val < k.val := hk.1
  intro hcon
  have hki : k = i := by simpa using! hcon
  subst hki
  exact (Nat.lt_irrefl _ hlt)

/-- Every gate in a strict Z-tail list acts at a site distinct from `j`. -/
theorem zTailGateList_ne_j {n : ℕ} (i j : Fin n) {p : Fin n × Matrix (Fin 2) (Fin 2) ℂ}
    (hp : p ∈ zTailGateList i j) : p.1 ≠ j := by
  simp only [zTailGateList, List.mem_map] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  simp only [Finset.mem_toList] at hk
  simp only [zTailSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hlt : k.val < j.val := hk.2
  intro hcon
  have hkj : k = j := by simpa using! hcon
  subst hkj
  exact (Nat.lt_irrefl _ hlt)

/-- For `i < j`, forward hopping is the two-site embedding of `hopForwardBlock` multiplied by
the intervening Z-tail operator. -/
theorem hopForward_twoSiteBlock {n : ℕ} (i j : Fin n) (hij : i < j) :
    creation i * annihilation j
      = twoSiteGate i j hopForwardBlock * localGateListOp (zTailGateList i j) := by
  have hne_j : ∀ p ∈ zTailGateList i j, p.1 ≠ j := fun p hp => zTailGateList_ne_j i j hp
  have hcomm_j : localGateListOp (zTailGateList i j) * localGate j sigmaMinus
      = localGate j sigmaMinus * localGateListOp (zTailGateList i j) :=
    localGateListOp_commute_of_distinct (zTailGateList i j) j hne_j sigmaMinus
  have hij' : i ≠ j := by omega
  have hop : localGateListOp (hopForwardGateList i j)
      = twoSiteGate i j hopForwardBlock * localGateListOp (zTailGateList i j) := by
    calc localGateListOp (hopForwardGateList i j)
        = localGate i sigmaPlus * (localGate i oneQubitZ * localGateListOp (zTailGateList i j))
            * localGate j sigmaMinus := by
            simp only [hopForwardGateList, localGateListOp_append, localGateListOp_singleton,
              zRangeGateList_op_eq i j hij]
      _ = localGate i (sigmaPlus * oneQubitZ)
            * (localGate j sigmaMinus * localGateListOp (zTailGateList i j)) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hcomm_j,
              ← Matrix.mul_assoc (localGate i sigmaPlus) (localGate i oneQubitZ)
                (localGate j sigmaMinus * localGateListOp (zTailGateList i j)),
              localGate_mul_localGate_same]
      _ = twoSiteGate i j hopForwardBlock * localGateListOp (zTailGateList i j) := by
            have h2 : localGate i sigmaPlus * localGate j sigmaMinus
                = twoSiteGate i j hopForwardBlock := by
              rw [twoSiteGate_eq_localGate_mul i j hij' sigmaPlus sigmaMinus]
              rfl
            rw [← Matrix.mul_assoc (localGate i (sigmaPlus * oneQubitZ)) (localGate j sigmaMinus)
              (localGateListOp (zTailGateList i j)), sigmaPlus_mul_oneQubitZ, ← h2]
  rw [← hopForwardGateList_op i j hij, hop]

/-- For `i < j`, backward hopping is the two-site embedding of `hopBackwardBlock` multiplied by
the intervening Z-tail operator. -/
theorem hopBackward_twoSiteBlock {n : ℕ} (i j : Fin n) (hij : i < j) :
    creation j * annihilation i
      = twoSiteGate i j hopBackwardBlock * localGateListOp (zTailGateList i j) := by
  have hne_i : ∀ p ∈ zTailGateList i j, p.1 ≠ i := fun p hp => zTailGateList_ne_i i j hp
  have hcomm_i : localGateListOp (zTailGateList i j) * localGate i oneQubitZ
      = localGate i oneQubitZ * localGateListOp (zTailGateList i j) :=
    localGateListOp_commute_of_distinct (zTailGateList i j) i hne_i oneQubitZ
  have hcomm_i' : localGateListOp (zTailGateList i j) * localGate i sigmaMinus
      = localGate i sigmaMinus * localGateListOp (zTailGateList i j) :=
    localGateListOp_commute_of_distinct (zTailGateList i j) i hne_i sigmaMinus
  have hcomm_j : localGate j sigmaPlus * localGateListOp (zTailGateList i j)
      = localGateListOp (zTailGateList i j) * localGate j sigmaPlus :=
    (localGateListOp_commute_of_distinct (zTailGateList i j) j
      (fun p hp => zTailGateList_ne_j i j hp) sigmaPlus).symm
  have hij' : i ≠ j := by omega
  have hop : localGateListOp (hopBackwardGateList i j)
      = twoSiteGate i j hopBackwardBlock * localGateListOp (zTailGateList i j) := by
    calc localGateListOp (hopBackwardGateList i j)
        = localGate j sigmaPlus * (localGate i oneQubitZ * localGateListOp (zTailGateList i j))
            * localGate i sigmaMinus := by
            simp only [hopBackwardGateList, localGateListOp_append, localGateListOp_singleton,
              zRangeGateList_op_eq i j hij]
      _ = localGate j sigmaPlus
            * (localGate i oneQubitZ * (localGate i sigmaMinus * localGateListOp (zTailGateList i j))) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hcomm_i']
      _ = localGate j sigmaPlus * (localGate i sigmaMinus * localGateListOp (zTailGateList i j)) := by
            rw [← Matrix.mul_assoc (localGate i oneQubitZ) (localGate i sigmaMinus)
              (localGateListOp (zTailGateList i j)), localGate_mul_localGate_same,
              oneQubitZ_mul_sigmaMinus]
      _ = (localGate i sigmaMinus * localGate j sigmaPlus)
            * localGateListOp (zTailGateList i j) := by
            rw [← Matrix.mul_assoc (localGate j sigmaPlus) (localGate i sigmaMinus)
              (localGateListOp (zTailGateList i j)),
              localGate_mul_localGate_ne j i (Ne.symm hij') sigmaPlus sigmaMinus]
      _ = twoSiteGate i j hopBackwardBlock * localGateListOp (zTailGateList i j) := by
            have h2 : localGate i sigmaMinus * localGate j sigmaPlus
                = twoSiteGate i j hopBackwardBlock := by
              rw [twoSiteGate_eq_localGate_mul i j hij' sigmaMinus sigmaPlus]
              rfl
            rw [← h2]
  rw [← hopBackwardGateList_op i j hij, hop]

/-- A two-site gate entry is the corresponding block entry when the registers agree outside its
two sites, and zero otherwise. -/
theorem twoSiteGate_apply {n : ℕ} (i j : Fin n)
    (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (y x : Reg n) :
    twoSiteGate i j B y x
      = if ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k then
          B (boolEquivFin2 (y i), boolEquivFin2 (y j)) (boolEquivFin2 (x i), boolEquivFin2 (x j))
        else 0 := by
  rw [twoSiteGate, Matrix.of_apply]

/-- The two-site embedding sends `c • B + D` to `c • twoSiteGate i j B + twoSiteGate i j D`. -/
theorem twoSiteGate_linear {n : ℕ} (i j : Fin n) (c : ℂ)
    (B D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    twoSiteGate i j (c • B + D) = c • twoSiteGate i j B + twoSiteGate i j D := by
  ext y x
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · rw [twoSiteGate_apply, if_pos hout, Matrix.add_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.smul_apply, twoSiteGate_apply, if_pos hout,
      twoSiteGate_apply, if_pos hout]
  · rw [twoSiteGate_apply, if_neg hout, Matrix.add_apply, Matrix.smul_apply,
      twoSiteGate_apply, if_neg hout, twoSiteGate_apply, if_neg hout]
    simp

/-- The two-site embedding preserves addition of block matrices. -/
theorem twoSiteGate_add {n : ℕ} (i j : Fin n)
    (B D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    twoSiteGate i j (B + D) = twoSiteGate i j B + twoSiteGate i j D := by
  ext y x
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · rw [twoSiteGate_apply, if_pos hout, Matrix.add_apply, Matrix.add_apply,
      twoSiteGate_apply, if_pos hout, twoSiteGate_apply, if_pos hout]
  · rw [twoSiteGate_apply, if_neg hout, Matrix.add_apply,
      twoSiteGate_apply, if_neg hout, twoSiteGate_apply, if_neg hout]
    simp

/-- A complex scalar multiple of a two-site gate equals the embedding of the scalar-multiplied
block. -/
theorem twoSiteGate_smul {n : ℕ} (i j : Fin n) (c : ℂ)
    (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    c • twoSiteGate i j B = twoSiteGate i j (c • B) := by
  ext y x
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · rw [Matrix.smul_apply, twoSiteGate_apply, if_pos hout, twoSiteGate_apply, if_pos hout,
      Matrix.smul_apply]
  · rw [Matrix.smul_apply, twoSiteGate_apply, if_neg hout, twoSiteGate_apply, if_neg hout]
    simp

/-- For distinct modes, the number operator at the first mode is the two-site embedding of
`numberBlockI`. -/
theorem numberOp_twoSiteGate_i {n : ℕ} (i j : Fin n) (_hij : i ≠ j) :
    numberOp i = twoSiteGate i j numberBlockI := by
  ext y x
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · by_cases hxy : x = y
    · subst hxy
      rw [numberOp, Matrix.of_apply, twoSiteGate_apply, if_pos hout]
      cases h : x i <;>
        simp [numberBlockI, boolEquivFin2_false, boolEquivFin2_true]
    · rw [numberOp, Matrix.of_apply, twoSiteGate_apply, if_pos hout]
      have hbits : (boolEquivFin2 (y i), boolEquivFin2 (y j))
          ≠ (boolEquivFin2 (x i), boolEquivFin2 (x j)) := by
        intro hcon
        apply hxy
        have h1 : y i = x i := by simpa using! congrArg Prod.fst hcon
        have h2 : y j = x j := by simpa using! congrArg Prod.snd hcon
        funext k
        by_cases hk : k = i
        · simp [hk, h1]
        · by_cases hk2 : k = j
          · simp [hk2, h2]
          · exact (hout k hk hk2).symm
      simp [numberBlockI, hbits, hxy]
  · rw [numberOp, Matrix.of_apply, twoSiteGate_apply, if_neg hout]
    have hxy : ¬ x = y := by
      intro h
      exact hout (fun k hk1 hk2 => by rw [h])
    simp [hxy]

/-- For distinct modes, the number operator at the second mode is the two-site embedding of
`numberBlockJ`. -/
theorem numberOp_twoSiteGate_j {n : ℕ} (i j : Fin n) (_hij : i ≠ j) :
    numberOp j = twoSiteGate i j numberBlockJ := by
  ext y x
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · by_cases hxy : x = y
    · subst hxy
      rw [numberOp, Matrix.of_apply, twoSiteGate_apply, if_pos hout]
      cases h : x j <;>
        simp [numberBlockJ, boolEquivFin2_false, boolEquivFin2_true]
    · rw [numberOp, Matrix.of_apply, twoSiteGate_apply, if_pos hout]
      have hbits : (boolEquivFin2 (y i), boolEquivFin2 (y j))
          ≠ (boolEquivFin2 (x i), boolEquivFin2 (x j)) := by
        intro hcon
        apply hxy
        have h1 : y i = x i := by simpa using! congrArg Prod.fst hcon
        have h2 : y j = x j := by simpa using! congrArg Prod.snd hcon
        funext k
        by_cases hk : k = i
        · simp [hk, h1]
        · by_cases hk2 : k = j
          · simp [hk2, h2]
          · exact (hout k hk hk2).symm
      simp [numberBlockJ, hbits, hxy]
  · rw [numberOp, Matrix.of_apply, twoSiteGate_apply, if_neg hout]
    have hxy : ¬ x = y := by
      intro h
      exact hout (fun k hk1 hk2 => by rw [h])
    simp [hxy]

/-- The strict Z-tail set is empty for consecutive mode indices. -/
theorem zTailSet_eq_empty_of_adjacent {n : ℕ} (i j : Fin n) (hadj : j.val = i.val + 1) :
    zTailSet i j = ∅ := by
  ext k
  simp only [zTailSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hk
    exact (by omega : False).elim
  · intro hk
    exact (by simpa using! hk : False).elim

/-- The strict Z-tail gate list is empty for consecutive mode indices. -/
theorem zTailGateList_eq_nil_of_adjacent {n : ℕ} (i j : Fin n) (hadj : j.val = i.val + 1) :
    zTailGateList i j = [] := by
  rw [zTailGateList, zTailSet_eq_empty_of_adjacent i j hadj]
  simp

/-- For consecutive distinct modes, the quadratic generator is the two-site embedding of
`generatorBlock A`. -/
theorem quadraticGenerator_adjacent_block {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (hadj : j.val = i.val + 1) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    quadraticGenerator i j A = twoSiteGate i j (generatorBlock A) := by
  have htail : localGateListOp (zTailGateList i j) = 1 := by
    rw [zTailGateList_eq_nil_of_adjacent i j hadj]
    rfl
  rw [quadraticGenerator]
  calc A 0 0 • (creation i * annihilation i) + A 0 1 • (creation i * annihilation j)
      + A 1 0 • (creation j * annihilation i) + A 1 1 • (creation j * annihilation j)
      = A 0 0 • twoSiteGate i j numberBlockI
          + A 0 1 • (twoSiteGate i j hopForwardBlock * 1)
          + A 1 0 • (twoSiteGate i j hopBackwardBlock * 1)
          + A 1 1 • twoSiteGate i j numberBlockJ := by
            simp only [creation_mul_annihilation_eq_numberOp, numberOp_twoSiteGate_i i j hij,
              numberOp_twoSiteGate_j i j hij, hopForward_twoSiteBlock i j (by omega),
              hopBackward_twoSiteBlock i j (by omega), htail]
      _ = A 0 0 • twoSiteGate i j numberBlockI
          + A 0 1 • twoSiteGate i j hopForwardBlock
          + A 1 0 • twoSiteGate i j hopBackwardBlock
          + A 1 1 • twoSiteGate i j numberBlockJ := by
            simp only [Matrix.mul_one]
      _ = twoSiteGate i j (A 0 0 • numberBlockI + A 0 1 • hopForwardBlock
          + A 1 0 • hopBackwardBlock + A 1 1 • numberBlockJ) := by
            rw [twoSiteGate_smul i j (A 0 0) numberBlockI,
              twoSiteGate_smul i j (A 0 1) hopForwardBlock,
              twoSiteGate_smul i j (A 1 0) hopBackwardBlock,
              twoSiteGate_smul i j (A 1 1) numberBlockJ,
              ← twoSiteGate_add i j (A 0 0 • numberBlockI) (A 0 1 • hopForwardBlock),
              ← twoSiteGate_add i j (A 0 0 • numberBlockI + A 0 1 • hopForwardBlock)
                (A 1 0 • hopBackwardBlock),
              ← twoSiteGate_add i j (A 0 0 • numberBlockI + A 0 1 • hopForwardBlock
                + A 1 0 • hopBackwardBlock) (A 1 1 • numberBlockJ)]
      _ = twoSiteGate i j (generatorBlock A) := by
            rfl

/-- For `i < j`, the quadratic generator expands into two weighted number blocks and two
weighted hopping blocks, each hopping block followed by the Z-tail operator. -/
theorem quadraticGenerator_twoSiteBlock {n : ℕ} (i j : Fin n) (hij : i < j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    quadraticGenerator i j A
      = A 0 0 • twoSiteGate i j numberBlockI
        + (A 0 1 • twoSiteGate i j hopForwardBlock) * localGateListOp (zTailGateList i j)
        + (A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j)
        + A 1 1 • twoSiteGate i j numberBlockJ := by
  rw [quadraticGenerator]
  calc A 0 0 • (creation i * annihilation i) + A 0 1 • (creation i * annihilation j)
      + A 1 0 • (creation j * annihilation i) + A 1 1 • (creation j * annihilation j)
      = A 0 0 • twoSiteGate i j numberBlockI
          + (A 0 1 • twoSiteGate i j hopForwardBlock) * localGateListOp (zTailGateList i j)
          + (A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j)
          + A 1 1 • twoSiteGate i j numberBlockJ := by
            simp only [creation_mul_annihilation_eq_numberOp, numberOp_twoSiteGate_i i j
              (by omega), numberOp_twoSiteGate_j i j (by omega),
              hopForward_twoSiteBlock i j hij, hopBackward_twoSiteBlock i j hij,
              ← smul_mul]

/-- For `i < j`, the quadratic generator is the sum of its weighted number blocks and a combined
weighted hopping block multiplied by the Z-tail operator. -/
theorem quadraticGenerator_twoSiteBlock_combined {n : ℕ} (i j : Fin n) (hij : i < j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    quadraticGenerator i j A
      = A 0 0 • twoSiteGate i j numberBlockI + A 1 1 • twoSiteGate i j numberBlockJ
        + (A 0 1 • twoSiteGate i j hopForwardBlock
            + A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j) := by
  rw [quadraticGenerator_twoSiteBlock i j hij A]
  calc A 0 0 • twoSiteGate i j numberBlockI
        + (A 0 1 • twoSiteGate i j hopForwardBlock) * localGateListOp (zTailGateList i j)
        + (A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j)
        + A 1 1 • twoSiteGate i j numberBlockJ
      = (A 0 1 • twoSiteGate i j hopForwardBlock) * localGateListOp (zTailGateList i j)
        + (A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j)
        + (A 0 0 • twoSiteGate i j numberBlockI + A 1 1 • twoSiteGate i j numberBlockJ) := by
          abel
      _ = (A 0 1 • twoSiteGate i j hopForwardBlock
            + A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j)
        + (A 0 0 • twoSiteGate i j numberBlockI + A 1 1 • twoSiteGate i j numberBlockJ) := by
          rw [← add_mul]
      _ = A 0 0 • twoSiteGate i j numberBlockI + A 1 1 • twoSiteGate i j numberBlockJ
        + (A 0 1 • twoSiteGate i j hopForwardBlock
            + A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j) := by
          abel

/-- The two-site register coordinates are the Boolean-to-`Fin 2` images of its bits at `i` and
`j`. -/
theorem twoSiteBits_def {n : ℕ} (i j : Fin n) (y : Reg n) :
    twoSiteBits i j y = (boolEquivFin2 (y i), boolEquivFin2 (y j)) := rfl

/-- The extension of local coordinates has first coordinate `w.1`, converted to a Boolean, at
site `i`. -/
theorem twoSiteExtend_bit_i {n : ℕ} (i j : Fin n) (y : Reg n) (w : Fin 2 × Fin 2) :
    twoSiteExtend i j y w i = boolEquivFin2.symm w.1 := by
  simp [twoSiteExtend]

/-- For distinct sites, the extension of local coordinates has second coordinate `w.2`,
converted to a Boolean, at site `j`. -/
theorem twoSiteExtend_bit_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y : Reg n)
    (w : Fin 2 × Fin 2) :
    twoSiteExtend i j y w j = boolEquivFin2.symm w.2 := by
  simp [twoSiteExtend, Ne.symm hij]

/-- Extending local coordinates leaves the register unchanged outside the two sites. -/
theorem twoSiteExtend_out {n : ℕ} (i j : Fin n) (y : Reg n) (w : Fin 2 × Fin 2) (k : Fin n)
    (hk : k ≠ i) (hk' : k ≠ j) : twoSiteExtend i j y w k = y k := by
  simp [twoSiteExtend, hk, hk']

/-- Converting the bit of a local-coordinate extension at `i` to `Fin 2` recovers `w.1`. -/
theorem boolEquivFin2_twoSiteExtend_i {n : ℕ} (i j : Fin n) (y : Reg n) (w : Fin 2 × Fin 2) :
    boolEquivFin2 (twoSiteExtend i j y w i) = w.1 := by
  rw [twoSiteExtend_bit_i]
  exact boolEquivFin2.apply_symm_apply _

/-- For distinct sites, converting the bit of a local-coordinate extension at `j` to `Fin 2`
recovers `w.2`. -/
theorem boolEquivFin2_twoSiteExtend_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y : Reg n)
    (w : Fin 2 × Fin 2) :
    boolEquivFin2 (twoSiteExtend i j y w j) = w.2 := by
  rw [twoSiteExtend_bit_j i j hij y w]
  exact boolEquivFin2.apply_symm_apply _

/-- For distinct sites, extracting the coordinates of a local-coordinate extension recovers
those coordinates. -/
theorem twoSiteBits_extend {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y : Reg n)
    (w : Fin 2 × Fin 2) :
    twoSiteBits i j (twoSiteExtend i j y w) = w := by
  exact Prod.ext (boolEquivFin2_twoSiteExtend_i i j y w)
    (boolEquivFin2_twoSiteExtend_j i j hij y w)

/-- For distinct sites, a register agreeing with `y` elsewhere is recovered by extending its
two-site coordinates into `y`. -/
theorem twoSiteExtend_of_agrees {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y z : Reg n)
    (h : ∀ k : Fin n, k ≠ i → k ≠ j → z k = y k) :
    twoSiteExtend i j y (twoSiteBits i j z) = z := by
  funext k
  by_cases hki : k = i
  · rw [hki]
    rw [twoSiteExtend_bit_i]
    show boolEquivFin2.symm (twoSiteBits i j z).1 = z i
    rw [twoSiteBits]
    exact boolEquivFin2.symm_apply_apply _
  · by_cases hkj : k = j
    · rw [hkj]
      rw [twoSiteExtend_bit_j i j hij y (twoSiteBits i j z)]
      show boolEquivFin2.symm (twoSiteBits i j z).2 = z j
      rw [twoSiteBits]
      exact boolEquivFin2.symm_apply_apply _
    · have hk := h k hki hkj
      simp [twoSiteExtend, hki, hkj, hk]

/-- For distinct sites, multiplying two embedded blocks equals embedding their matrix product. -/
theorem twoSiteGate_mul {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (B C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    twoSiteGate i j B * twoSiteGate i j C = twoSiteGate i j (B * C) := by
  classical
  ext y x
  rw [Matrix.mul_apply]
  set P : Set (Reg n) := {z | ∀ k : Fin n, k ≠ i → k ≠ j → z k = y k} with hP
  have hzero : ∀ z : Reg n, z ∉ P → (twoSiteGate i j B) y z = 0 := by
    intro z hz
    rw [twoSiteGate_apply]
    by_cases hc : ∀ k : Fin n, k ≠ i → k ≠ j → y k = z k
    · exfalso
      exact hz (fun k hk hk' => (hc k hk hk').symm)
    · simp [hc]
  have hsum : (∑ z : Reg n, (twoSiteGate i j B) y z * (twoSiteGate i j C) z x)
      = ∑ z ∈ (Finset.univ : Finset (Reg n)).filter P,
          (twoSiteGate i j B) y z * (twoSiteGate i j C) z x := by
    exact (Finset.sum_subset (Finset.filter_subset _ _)
      (fun z _ hz => by
        have hzP : z ∉ P := fun hp => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hp⟩)
        rw [hzero z hzP]
        simp)).symm
  rw [hsum]
  have hreindex :
      (∑ z ∈ (Finset.univ : Finset (Reg n)).filter P,
          (twoSiteGate i j B) y z * (twoSiteGate i j C) z x)
        = ∑ w : Fin 2 × Fin 2,
            ((twoSiteGate i j B) y (twoSiteExtend i j y w)
              * (twoSiteGate i j C) (twoSiteExtend i j y w) x) := by
    refine Finset.sum_bij (fun z _ => twoSiteBits i j z) ?_ ?_ ?_ ?_
    · intro z hz
      exact Finset.mem_univ _
    · intro z1 hz1 z2 hz2 heq
      have e1 : z1 i = z2 i := by
        apply boolEquivFin2.injective
        simpa [twoSiteBits] using! congrArg Prod.fst heq
      have e2 : z1 j = z2 j := by
        apply boolEquivFin2.injective
        simpa [twoSiteBits] using! congrArg Prod.snd heq
      have hz1' : ∀ k : Fin n, k ≠ i → k ≠ j → z1 k = y k :=
        (Finset.mem_filter.mp hz1).2
      have hz2' : ∀ k : Fin n, k ≠ i → k ≠ j → z2 k = y k :=
        (Finset.mem_filter.mp hz2).2
      funext k
      by_cases hki : k = i
      · rw [hki, e1]
      · by_cases hkj : k = j
        · rw [hkj, e2]
        · rw [hz1' k hki hkj, hz2' k hki hkj]
    · intro w hw
      refine ⟨twoSiteExtend i j y w, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro k hk hk'
        exact twoSiteExtend_out i j y w k hk hk'
      · exact twoSiteBits_extend i j hij y w
    · intro z hz
      have hz' : ∀ k : Fin n, k ≠ i → k ≠ j → z k = y k :=
        (Finset.mem_filter.mp hz).2
      show (twoSiteGate i j B) y z * (twoSiteGate i j C) z x
        = ((twoSiteGate i j B) y (twoSiteExtend i j y (twoSiteBits i j z))
          * (twoSiteGate i j C) (twoSiteExtend i j y (twoSiteBits i j z)) x)
      rw [twoSiteExtend_of_agrees i j hij y z hz']
  rw [hreindex]
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · have hstep : ∀ w : Fin 2 × Fin 2,
        (twoSiteGate i j B) y (twoSiteExtend i j y w)
          = B (twoSiteBits i j y) w := by
      intro w
      rw [twoSiteGate_apply,
        if_pos (fun k hk hk' => (twoSiteExtend_out i j y w k hk hk').symm)]
      rw [boolEquivFin2_twoSiteExtend_i i j y w,
        boolEquivFin2_twoSiteExtend_j i j hij y w]
      simp [twoSiteBits]
    have hstep2 : ∀ w : Fin 2 × Fin 2,
        (twoSiteGate i j C) (twoSiteExtend i j y w) x
          = C w (twoSiteBits i j x) := by
      intro w
      rw [twoSiteGate_apply,
        if_pos (fun k hk hk' => (twoSiteExtend_out i j y w k hk hk').trans (hout k hk hk'))]
      rw [boolEquivFin2_twoSiteExtend_i i j y w,
        boolEquivFin2_twoSiteExtend_j i j hij y w]
      simp [twoSiteBits]
    simp only [hstep, hstep2]
    rw [twoSiteGate_apply, if_pos hout, Matrix.mul_apply]
    simp only [twoSiteBits]
  · have hex : ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k := by
      by_contra hcon
      have hcon' : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k := by
        intro k hk hk'
        by_contra hc
        exact hcon ⟨k, hk, hk', hc⟩
      exact hout hcon'
    have hzero2 : ∀ w : Fin 2 × Fin 2,
        (twoSiteGate i j C) (twoSiteExtend i j y w) x = 0 := by
      intro w
      rw [twoSiteGate_apply]
      by_cases hc : ∀ k : Fin n, k ≠ i → k ≠ j → twoSiteExtend i j y w k = x k
      · exfalso
        obtain ⟨k, hk, hk', hne⟩ := hex
        have hzy : twoSiteExtend i j y w k = y k := twoSiteExtend_out i j y w k hk hk'
        have hcx := hc k hk hk'
        rw [hzy] at hcx
        exact absurd hcx hne
      · simp [hc]
    simp only [hzero2, mul_zero]
    rw [twoSiteGate_apply, if_neg hout]
    simp

/-- Embedding the identity block as a two-site gate gives the register identity matrix. -/
theorem twoSiteGate_one {n : ℕ} (i j : Fin n) :
    twoSiteGate i j 1 = 1 := by
  ext y x
  by_cases hout : ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k
  · rw [twoSiteGate_apply, if_pos hout, Matrix.one_apply]
    by_cases heq : y = x
    · subst heq
      simp
    · have hbits : (boolEquivFin2 (y i), boolEquivFin2 (y j))
          ≠ (boolEquivFin2 (x i), boolEquivFin2 (x j)) := by
        intro h
        have e1 : y i = x i := boolEquivFin2.injective (congrArg Prod.fst h)
        have e2 : y j = x j := boolEquivFin2.injective (congrArg Prod.snd h)
        have hyx : y = x := by
          funext k
          by_cases hki : k = i
          · rw [hki, e1]
          · by_cases hkj : k = j
            · rw [hkj, e2]
            · rw [hout k hki hkj]
        exact heq hyx
      simp [hbits, heq]
  · rw [twoSiteGate_apply, if_neg hout, Matrix.one_apply]
    have hne : y ≠ x := by
      intro hyx
      subst hyx
      exact hout (fun k hk hk' => rfl)
    simp [hne]

/-- For distinct sites, a natural power of an embedded two-site block equals the embedding of
that power. -/
theorem twoSiteGate_pow {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : ℕ) :
    (twoSiteGate i j B)^k = twoSiteGate i j (B^k) := by
  induction k with
  | zero => simp [twoSiteGate_one]
  | succ k ih =>
      have hmul := twoSiteGate_mul i j hij (B^k) B
      have hpow : B^(Nat.succ k) = B^k * B := by rw [pow_succ]
      have hsq : (twoSiteGate i j B)^(Nat.succ k)
          = (twoSiteGate i j B)^k * twoSiteGate i j B := by rw [pow_succ]
      rw [hsq, ih, hmul, hpow]

/-- Collects exact Jordan–Wigner gate-list representations, locality and evolution identities,
quadratic and Hubbard word encodings with cost bounds, and two-site block decompositions. It
also includes exact factorization of evolution for commuting generators. -/
theorem clause2_endpoint_partial :
    (∀ (n : ℕ) (i : Fin n) (y x : Reg n),
      jwPauliWord i y x = ∏ j : Fin n, jwSiteFactor i j y x)
      ∧ (∀ (n : ℕ) (i : Fin n) (y x : Reg n),
        (∃ k : Fin n, k ≠ i ∧ y k ≠ x k) → jwPauliWord i y x = 0)
      ∧ (∀ (n : ℕ) (j : Fin n) (y x : Reg n), y ≠ x → localGate j oneQubitZ y x = 0)
      ∧ (∀ (n : ℕ) (i : Fin n) (θ : ℝ) (x : Reg n),
        onsiteLocalGate i θ x x = (if x i then Complex.exp (-Complex.I * θ) else 1))
      ∧ (∀ (n : ℕ) (i : Fin n) (θ : ℝ) (y x : Reg n), y ≠ x → onsiteLocalGate i θ y x = 0)
      ∧ (∀ (n : ℕ) (i : Fin n), i.val + 1 ≤ n)
      ∧ (∀ (n : ℕ) (gl : LocalGateList n), localGateCount gl = gl.length)
      ∧ (∀ (n : ℕ) (gl : LocalGateList n),
        localGateBitCost gl = localGateCount gl * modeAddressBits n)
      ∧ (∀ (n : ℕ) (gl : LocalGateList n), localGateSpaceCost gl = n)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateListOp (jwLocalGateList i) = jwPauliWord i)
      ∧ (∀ (n : ℕ) (i : Fin n) (y x : Reg n),
        (localGateListOp (jwLocalGateList i) - jwPauliWord i) y x = 0)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateListOp (jwLocalGateList i) = annihilation i)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateCount (jwLocalGateList i) = i.val + 1)
      ∧ (∀ (n : ℕ) (i : Fin n),
        localGateBitCost (jwLocalGateList i) = (i.val + 1) * modeAddressBits n)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateSpaceCost (jwLocalGateList i) = n)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateListOp (jwCreationGateList i) = creation i)
      ∧ (∀ (n : ℕ) (i : Fin n) (y x : Reg n),
        (localGateListOp (jwCreationGateList i) - creation i) y x = 0)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateCount (jwCreationGateList i) = i.val + 1)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateListOp (numberGateList i) = numberOp i)
      ∧ (∀ (n : ℕ) (i : Fin n), localGateCount (numberGateList i) = 1)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        localGateListOp (hopForwardGateList i j) = creation i * annihilation j)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        localGateListOp (hopBackwardGateList i j) = creation j * annihilation i)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        localGateCount (hopForwardGateList i j) = j.val - i.val + 2)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        localGateCount (hopBackwardGateList i j) = j.val - i.val + 2)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j) (A : Matrix (Fin 2) (Fin 2) ℂ),
        quadraticGenerator i j A
          = A 0 0 • (localGateListOp (numberGateList i))
            + A 0 1 • (localGateListOp (hopForwardGateList i j))
            + A 1 0 • (localGateListOp (hopBackwardGateList i j))
            + A 1 1 • (localGateListOp (numberGateList j)))
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        localGateCount (numberGateList i)
            + localGateCount (hopForwardGateList i j)
            + localGateCount (hopBackwardGateList i j)
            + localGateCount (numberGateList j)
          = 2 * (j.val - i.val) + 6)
      ∧ (∀ (n : ℕ) (i j : Fin n) (k : Fin n) (hk : k ≠ i) (hk' : k ≠ j) (y x : Reg n),
        y k ≠ x k →
          (creation i * annihilation j + creation j * annihilation i) y x = 0)
      ∧ (∀ (n : ℕ) (i j : Fin n) (T : Matrix (Reg n) (Reg n) ℂ) (s : ℝ),
        (∀ (k : Fin n) (hk : k ≠ i) (hk' : k ≠ j) (y x : Reg n),
          y k ≠ x k → T y x = 0) →
          ∀ (y x : Reg n), (∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k) →
            (HamiltonianEvolution T s) y x = 0)
      ∧ (∀ (n : ℕ) (i j : Fin n) (s : ℝ) (y x : Reg n),
        (∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ y k ≠ x k) →
          (HamiltonianEvolution
            (creation i * annihilation j + creation j * annihilation i) s) y x = 0)
      ∧ (∀ (n : ℕ) (j : Fin n) (G H : Matrix (Fin 2) (Fin 2) ℂ),
        localGate j G * localGate j H = localGate j (G * H))
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i ≠ j) (G H : Matrix (Fin 2) (Fin 2) ℂ),
        localGate i G * localGate j H = localGate j H * localGate i G)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i ≠ j) (G H : Matrix (Fin 2) (Fin 2) ℂ),
        localGate i G * localGate j H
          = twoSiteGate i j (fun a c => G a.1 c.1 * H a.2 c.2))
      ∧ (∀ (n : ℕ) (i : Fin n) (s : ℝ),
        HamiltonianEvolution (numberOp i) s = onsiteLocalGate i s)
      ∧ (∀ (n : ℕ) (i j : Fin n),
        (creation i * annihilation j + creation j * annihilation i)ᴴ
          = creation i * annihilation j + creation j * annihilation i)
      ∧ (∀ (n : ℕ) (i : Fin n),
        numberOp i * creation i - creation i * numberOp i = creation i)
      ∧ (∀ (n : ℕ) (i : Fin n),
        numberOp i * annihilation i - annihilation i * numberOp i = -annihilation i)
      ∧ (∀ (n : ℕ) (i j : Fin n) (s : ℝ),
        HamiltonianEvolution (creation i * annihilation j + creation j * annihilation i) s
          ∈ Matrix.unitaryGroup (Reg n) ℂ)
      ∧ (∀ (n : ℕ) (terms : List (QuadraticTerm n)),
        localGateSumOp (quadraticHamiltonianWord terms)
          = terms.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0)
      ∧ (∀ (n : ℕ) (terms : List (QuadraticTerm n)),
        (localGateSumOp (quadraticHamiltonianWord terms)
          - terms.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0) = 0)
      ∧ (∀ (n : ℕ) (terms : List (QuadraticTerm n)),
        localGateSumCount (quadraticHamiltonianWord terms) ≤ (2 * n + 4) * terms.length)
      ∧ (∀ (n : ℕ) (terms : List (QuadraticTerm n)),
        localGateSumBitCost (quadraticHamiltonianWord terms)
          ≤ (2 * n + 4) * terms.length * modeAddressBits n)
      ∧ (∀ (n : ℕ) (terms : List (QuadraticTerm n)),
        localGateSumSpaceCost (quadraticHamiltonianWord terms) ≤ n)
      ∧ (∀ (n : ℕ) (terms : List (QuadraticTerm n)) (h : terms.length ≤ n * n),
        localGateSumCount (quadraticHamiltonianWord terms) ≤ (2 * n + 4) * n ^ 2)
      ∧ (∀ (n : ℕ) (t : OneBodyTerm n),
        localGateSumOp (oneBodyWord t) = t.h • numberOp t.i)
      ∧ (∀ (n : ℕ) (t : OneBodyTerm n),
        localGateSumCount (oneBodyWord t) = 1)
      ∧ (∀ (n : ℕ) (t : OneBodyTerm n) (y x : Reg n), y ≠ x →
        localGateSumOp (oneBodyWord t) y x = 0)
      ∧ (∀ (n : ℕ) (t : QuadraticTerm n),
        6 ≤ localGateSumCount (quadraticTermWord t))
      ∧ (∀ (n : ℕ) (oneBody : List (OneBodyTerm n)) (twoBody : List (QuadraticTerm n)),
        localGateSumOp (generalQuadraticHamiltonianWord oneBody twoBody)
          = oneBody.foldr (fun t acc => t.h • numberOp t.i + acc) 0
            + twoBody.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0)
      ∧ (∀ (n : ℕ) (oneBody : List (OneBodyTerm n)) (twoBody : List (QuadraticTerm n)),
        (localGateSumOp (generalQuadraticHamiltonianWord oneBody twoBody)
          - (oneBody.foldr (fun t acc => t.h • numberOp t.i + acc) 0
            + twoBody.foldr (fun t acc => quadraticGenerator t.i t.j t.A + acc) 0)) = 0)
      ∧ (∀ (n : ℕ) (oneBody : List (OneBodyTerm n)) (twoBody : List (QuadraticTerm n)),
        localGateSumCount (generalQuadraticHamiltonianWord oneBody twoBody)
          = oneBody.length
            + twoBody.foldr (fun t acc => 2 * (t.j.val - t.i.val) + 6 + acc) 0)
      ∧ (∀ (n : ℕ) (oneBody : List (OneBodyTerm n)) (twoBody : List (QuadraticTerm n)),
        localGateSumCount (generalQuadraticHamiltonianWord oneBody twoBody)
          ≤ oneBody.length + (2 * n + 4) * twoBody.length)
      ∧ (∀ (n : ℕ) (oneBody : List (OneBodyTerm n)) (twoBody : List (QuadraticTerm n)),
        localGateSumBitCost (generalQuadraticHamiltonianWord oneBody twoBody)
          ≤ (oneBody.length + (2 * n + 4) * twoBody.length) * modeAddressBits n)
      ∧ (∀ (n : ℕ) (oneBody : List (OneBodyTerm n)) (twoBody : List (QuadraticTerm n)),
        localGateSumSpaceCost (generalQuadraticHamiltonianWord oneBody twoBody) ≤ n)
      ∧ (∀ (n : ℕ) (t μ U : ℂ),
        localGateSumOp (hubbardHamiltonianWord (n := n) t μ U) = hubbardTermSum (n := n) t μ U)
      ∧ (∀ (n : ℕ) (t μ U : ℂ),
        (localGateSumOp (hubbardHamiltonianWord (n := n) t μ U)
          - hubbardTermSum (n := n) t μ U) = 0)
      ∧ (∀ (n : ℕ) (t μ U : ℂ),
        localGateSumCount (hubbardHamiltonianWord (n := n) t μ U)
          ≤ 2 * n ^ 3 + 6 * n ^ 2 + n)
      ∧ (∀ (n : ℕ) (t μ U : ℂ),
        localGateSumBitCost (hubbardHamiltonianWord (n := n) t μ U)
          ≤ (2 * n ^ 3 + 6 * n ^ 2 + n) * modeAddressBits n)
      ∧ (∀ (n : ℕ) (t μ U : ℂ),
        localGateSumSpaceCost (hubbardHamiltonianWord (n := n) t μ U) ≤ n)
      ∧ (∀ (n : ℕ) (T₁ T₂ : Matrix (Reg n) (Reg n) ℂ) (s : ℝ),
        Commute T₁ T₂ →
          HamiltonianEvolution T₁ s * HamiltonianEvolution T₂ s
            = HamiltonianEvolution (T₁ + T₂) s)
      ∧ (∀ (n : ℕ) (i j : Fin n) (s : ℝ),
        HamiltonianEvolution (numberOp i) s * HamiltonianEvolution (numberOp j) s
          = HamiltonianEvolution (numberOp i + numberOp j) s)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        creation i * annihilation j
          = twoSiteGate i j hopForwardBlock * localGateListOp (zTailGateList i j))
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j),
        creation j * annihilation i
          = twoSiteGate i j hopBackwardBlock * localGateListOp (zTailGateList i j))
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i ≠ j), numberOp i = twoSiteGate i j numberBlockI)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i ≠ j), numberOp j = twoSiteGate i j numberBlockJ)
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i ≠ j) (hadj : j.val = i.val + 1)
        (A : Matrix (Fin 2) (Fin 2) ℂ),
        quadraticGenerator i j A = twoSiteGate i j (generatorBlock A))
      ∧ (∀ (n : ℕ) (i j : Fin n) (_hij : i < j) (A : Matrix (Fin 2) (Fin 2) ℂ),
        quadraticGenerator i j A
          = A 0 0 • twoSiteGate i j numberBlockI + A 1 1 • twoSiteGate i j numberBlockJ
            + (A 0 1 • twoSiteGate i j hopForwardBlock
                + A 1 0 • twoSiteGate i j hopBackwardBlock) * localGateListOp (zTailGateList i j)) :=
  ⟨fun n i y x => jwPauliWord_eq_siteFactors i y x,
   fun n i y x h => jwPauliWord_local i y x h,
   fun n j y x h => localGate_oneQubitZ_diagonal j y x h,
   fun n i θ x => onsiteLocalGate_apply i θ x,
   fun n i θ y x h => onsiteLocalGate_diagonal i θ y x h,
   fun n i => jwPauliWord_gateCount i,
   fun n gl => localGateCount_eq_length gl,
   fun n gl => rfl,
   fun n gl => rfl,
   fun _ i => jwLocalGateList_op i,
   fun _ i => jwLocalGateList_error i,
   fun _ i => jwLocalGateList_annihilation i,
   fun _ i => jwLocalGateList_count i,
   fun _ i => by rw [localGateBitCost, jwLocalGateList_count],
   fun _ i => rfl,
   fun _ i => jwCreationGateList_op i,
   fun _ i => jwCreationGateList_error i,
   fun _ i => jwCreationGateList_count i,
   fun _ i => numberGateList_op i,
   fun _ i => numberGateList_count i,
   fun _ i j hij => hopForwardGateList_op i j hij,
   fun _ i j hij => hopBackwardGateList_op i j hij,
   fun _ i j hij => hopForwardGateList_count i j hij,
   fun _ i j hij => hopBackwardGateList_count i j hij,
   fun _ i j hij A => quadraticGenerator_eq_localTerms i j hij A,
   fun _ i j hij => quadraticGenerator_localTerms_count i j hij,
   fun _ i j k hk hk' y x hne => hoppingTerm_preservesOutside i j k hk hk' y x hne,
   fun _ i j T s hT => hamiltonianEvolution_actsOnlyOn i j T hT s,
   fun _ i j s y x hex => hamiltonianEvolution_hoppingTerm_actsOnlyOn i j s y x hex,
   fun _ j G H => localGate_mul_localGate_same j G H,
   fun _ i j hij G H => localGate_mul_localGate_ne i j hij G H,
   fun _ i j hij G H => twoSiteGate_eq_localGate_mul i j hij G H,
   fun _ i s => hamiltonianEvolution_numberOp_eq_onsiteLocalGate i s,
   fun _ i j => hoppingTerm_hermitian i j,
   fun _ i => numberOp_creation_commutator i,
   fun _ i => numberOp_annihilation_commutator i,
   fun _ i j s => hamiltonianEvolution_hoppingTerm_unitary i j s,
   fun n terms => quadraticHamiltonianWord_op terms,
   fun n terms => quadraticHamiltonianWord_error terms,
   fun n terms => quadraticHamiltonianWord_count_le terms,
   fun n terms => quadraticHamiltonianWord_bitCost_le terms,
   fun n terms => quadraticHamiltonianWord_spaceCost_le terms,
   fun n terms h => quadraticHamiltonianWord_count_le_pow terms h,
   fun _ t => oneBodyWord_op t,
   fun _ t => oneBodyWord_count t,
   fun _ t y x h => oneBodyWord_op_diagonal t y x h,
   fun _ t => quadraticTermWord_count_ge_six t,
   fun n oneBody twoBody => generalQuadraticHamiltonianWord_op oneBody twoBody,
   fun n oneBody twoBody => generalQuadraticHamiltonianWord_error oneBody twoBody,
   fun n oneBody twoBody => generalQuadraticHamiltonianWord_count oneBody twoBody,
   fun n oneBody twoBody => generalQuadraticHamiltonianWord_count_le oneBody twoBody,
   fun n oneBody twoBody => generalQuadraticHamiltonianWord_bitCost_le oneBody twoBody,
   fun n oneBody twoBody => generalQuadraticHamiltonianWord_spaceCost_le oneBody twoBody,
   fun n t μ U => hubbardHamiltonianWord_eq_termSum (n := n) t μ U,
   fun n t μ U => hubbardHamiltonianWord_error (n := n) t μ U,
   fun n t μ U => hubbardHamiltonianWord_count_le_pow (n := n) t μ U,
   fun n t μ U => hubbardHamiltonianWord_bitCost_le (n := n) t μ U,
   fun n t μ U => hubbardHamiltonianWord_spaceCost_le (n := n) t μ U,
   fun n T₁ T₂ s h => hamiltonianEvolution_trotter_exact_of_commute T₁ T₂ s h,
   fun n i j s => hamiltonianEvolution_trotter_exact_onsite i j s,
   fun _ i j hij => hopForward_twoSiteBlock i j hij,
   fun _ i j hij => hopBackward_twoSiteBlock i j hij,
   fun _ i j hij => numberOp_twoSiteGate_i i j hij,
   fun _ i j hij => numberOp_twoSiteGate_j i j hij,
   fun _ i j hij hadj A => quadraticGenerator_adjacent_block i j hij hadj A,
   fun _ i j hij A => quadraticGenerator_twoSiteBlock_combined i j hij A⟩

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
