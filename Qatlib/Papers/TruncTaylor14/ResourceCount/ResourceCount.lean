/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation
public import Qatlib.Papers.TruncTaylor14.FactorialTaylor.LogLogCutoff.SourceEquation18
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Resource counting for the truncated Taylor simulation (Eqs. (22)-(25))

Fixed source: Berry, Childs, Cleve, Kothari and Somma, arXiv:1412.4687v1, p. 4, Eqs. (22)-(25).
This module formalizes the discrete resource side of the four printed cost
expressions: the ancilla register width (Eq. (22)), the gate count of the
PREPARE operation `B` together with its rotation-cascade realizability
(Eq. (23)), the controlled-`select(H)` decomposition for Pauli-product terms
(Eq. (24)), and the sparse-oracle segment gate scaling (Eq. (25)).

The asymptotic statements reuse the certified log/loglog cutoff rate of
`factorialTaylorCutoff` (source Eq. (18), registered as
`source_equation18_precision`): with precision parameter
`m = factorialTaylorPrecision s k` the counts are bounded by explicit absolute
constants times the printed orders.  These are discrete rates in `m`; a continuous `T/ε` conversion and the
full simulation segment count are separate bridges. `prepGates`,
`selectVGates` and `sparseSegGates` are prescribed per-segment ledgers,
not measured counts of generated elementary circuits. The unary rotation
matrices act on a `(K+1)`-dimensional subspace; their embedding and
decomposition on the physical `K`-qubit unary register are not constructed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TruncTaylor14.ResourceCount

open Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Papers.TruncTaylor14.FactorialTaylor.LogLogCutoff

/-- A finite sum supported on at most two points equals the two values. -/
private theorem sum_two_pts {n : ℕ} (f : Fin n → ℂ) (p q : Fin n) (hpq : p ≠ q)
    (h : ∀ c, c ≠ p → c ≠ q → f c = 0) : ∑ c, f c = f p + f q := by
  have h1 : ∑ c ∈ Finset.univ, f c = f p + ∑ c ∈ Finset.univ.erase p, f c := by
    have h := Finset.univ.sum_erase_add f (Finset.mem_univ p)
    calc
      ∑ c ∈ Finset.univ, f c = ∑ x ∈ Finset.univ.erase p, f x + f p := h.symm
      _ = f p + ∑ c ∈ Finset.univ.erase p, f c := add_comm _ _
  have h2 : ∑ c ∈ Finset.univ.erase p, f c =
      f q + ∑ c ∈ (Finset.univ.erase p).erase q, f c := by
    have h := (Finset.univ.erase p).sum_erase_add f
      (Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩)
    calc
      ∑ c ∈ Finset.univ.erase p, f c = ∑ x ∈ (Finset.univ.erase p).erase q, f x + f q := h.symm
      _ = f q + ∑ c ∈ (Finset.univ.erase p).erase q, f c := add_comm _ _
  have h3 : ∑ c ∈ (Finset.univ.erase p).erase q, f c = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hcq : c ≠ q := (Finset.mem_erase.mp hc).1
    have hcp : c ≠ p := (Finset.mem_erase.mp (Finset.mem_of_subset (Finset.erase_subset _ _) hc)).1
    exact h c hcp hcq
  rw [h1, h2, h3, add_zero]

/-! ### Eq. (22): ancilla qubits -/

/-- The unary register encoding of Eq. (22): the basis index `k ≤ K` is stored
as the bit string `1^k 0^{K-k}`. -/
def unaryReg (K : ℕ) : Fin (K + 1) → Fin K → Bool :=
  fun k j => decide (j.val < k.val)

/-- Distinct basis indices have distinct unary encodings, so `K` unary ancilla
qubits store all `K + 1` values of the first register of Eq. (22). -/
theorem unaryReg_inj (K : ℕ) : Function.Injective (unaryReg K) := by
  intro a b hab
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · exfalso
    have haK : a.val < K := by
      rcases Nat.lt_or_ge a.val K with h' | h'
      · exact h'
      · exact absurd h (by have := b.isLt; omega)
    have h1 := congrFun hab (⟨a.val, haK⟩ : Fin K)
    simp only [unaryReg, decide_eq_true h] at h1
    simp at h1
  · exact Fin.ext h
  · exfalso
    have hbK : b.val < K := by
      rcases Nat.lt_or_ge b.val K with h' | h'
      · exact h'
      · exact absurd h (by have := a.isLt; omega)
    have h1 := congrFun hab (⟨b.val, hbK⟩ : Fin K)
    simp only [unaryReg, decide_eq_true h] at h1
    simp at h1

/-- The ancilla width of Eq. (22): `K` unary qubits plus `K` copies of a
`⌈log₂ L⌉`-qubit `ℓ`-register. -/
def ancillaBits (K L : ℕ) : ℕ := K + K * Nat.clog 2 L

/-- Eq. (22), exact counting side: for `L ≥ 2` the ancilla width satisfies
`K + K·⌈log₂ L⌉ ≤ 2·K·⌈log₂ L⌉`. -/
theorem ancBits_le (K L : ℕ) (hL : 2 ≤ L) :
    ancillaBits K L ≤ 2 * K * Nat.clog 2 L := by
  have hc : 1 ≤ Nat.clog 2 L := by
    rcases Nat.eq_zero_or_pos (Nat.clog 2 L) with h0 | h1
    · exfalso
      have hp := Nat.le_pow_clog (by norm_num : 1 < 2) L
      rw [h0, pow_zero] at hp
      omega
    · omega
  have hkle : K ≤ K * Nat.clog 2 L := by
    have hm := Nat.mul_le_mul_left K hc
    omega
  unfold ancillaBits
  calc
    K + K * Nat.clog 2 L ≤ (K * Nat.clog 2 L) + (K * Nat.clog 2 L) :=
      Nat.add_le_add_right hkle _
    _ = 2 * K * Nat.clog 2 L := by ring

/-- Eq. (22): with the certified cutoff `K = factorialTaylorCutoff m` at
precision `m = factorialTaylorPrecision s k`, the ancilla width is at most a
constant times `log L · m / log₂ m`, the printed order
`O(log L · log(T/ε) / log log(T/ε))` in the precision parameter. -/
theorem eq22_ancilla_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (L s k : ℕ), 2 ≤ L → m₀ ≤ factorialTaylorPrecision s k →
      (ancillaBits (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℝ) ≤
        (C : ℝ) * (Nat.clog 2 L : ℝ) *
          ((factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ := source_equation18_precision
  refine ⟨2 * C, m₀, by omega, hm₀, fun L s k hL hm => ?_⟩
  have hm2 : 2 ≤ factorialTaylorPrecision s k := hm₀.trans hm
  have hlog : 0 < Nat.log 2 (factorialTaylorPrecision s k) :=
    Nat.log_pos (b := 2) (by norm_num) hm2
  have hcb : (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
      (C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
        (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := hrate s k hm
  have h1 : ((ancillaBits (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℕ) : ℝ) ≤
      2 * (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) *
        (Nat.clog 2 L : ℝ) := by
    have h2 : ((ancillaBits (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℕ) : ℝ) ≤
        ((2 * factorialTaylorCutoff (factorialTaylorPrecision s k) * Nat.clog 2 L : ℕ) : ℝ) :=
      (Nat.cast_le (α := ℝ)).mpr (ancBits_le (factorialTaylorCutoff
        (factorialTaylorPrecision s k)) L hL)
    push_cast at h2 ⊢
    linarith
  have hnn : 0 ≤ (Nat.clog 2 L : ℝ) := by positivity
  have hnc : 0 ≤ (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := by positivity
  calc
    (ancillaBits (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℝ)
        ≤ 2 * (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) *
            (Nat.clog 2 L : ℝ) := h1
    _ ≤ 2 * ((C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) *
          (Nat.clog 2 L : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb (by norm_num)) hnn
    _ = ((2 * C : ℕ) : ℝ) * (Nat.clog 2 L : ℝ) *
          ((factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
        push_cast
        field_simp

/-! ### Eq. (23): the rotation cascade of the PREPARE unitary `B` -/

/-- One step of the unary rotation cascade of Eq. (23): an embedded real
rotation between the adjacent unary positions `j` and `j+1`, acting as the
identity on all other positions. -/
def cascM (K : ℕ) (θ : ℝ) (j : Fin K) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  Matrix.of fun a b =>
    if b = j.castSucc then
      if a = j.castSucc then (Real.cos θ : ℂ)
      else if a = j.succ then (Real.sin θ : ℂ) else 0
    else if b = j.succ then
      if a = j.castSucc then (-(Real.sin θ) : ℂ)
      else if a = j.succ then (Real.cos θ : ℂ) else 0
    else if a = b then 1 else 0

private theorem casc_ne (K : ℕ) (j : Fin K) :
    j.castSucc ≠ (j.succ : Fin (K + 1)) := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

private theorem casc_cs_cs (K : ℕ) (θ : ℝ) (j : Fin K) :
    cascM K θ j j.castSucc j.castSucc = (Real.cos θ : ℂ) := by
  simp [cascM]

private theorem casc_cs_su (K : ℕ) (θ : ℝ) (j : Fin K) :
    cascM K θ j j.castSucc (j.succ) = (-(Real.sin θ) : ℂ) := by
  simp [cascM, (casc_ne K j).symm]

private theorem casc_su_cs (K : ℕ) (θ : ℝ) (j : Fin K) :
    cascM K θ j (j.succ) j.castSucc = (Real.sin θ : ℂ) := by
  simp [cascM, (casc_ne K j).symm]

private theorem casc_su_su (K : ℕ) (θ : ℝ) (j : Fin K) :
    cascM K θ j (j.succ) (j.succ) = (Real.cos θ : ℂ) := by
  simp [cascM, (casc_ne K j).symm]

private theorem casc_diag (K : ℕ) (θ : ℝ) (j : Fin K) (a : Fin (K + 1))
    (h1 : a ≠ j.castSucc) (h2 : a ≠ j.succ) : cascM K θ j a a = 1 := by
  simp [cascM, h1, h2]

/-- A cascade entry with row outside the two rotated positions vanishes unless
the row equals the column. -/
private theorem casc_row_out (K : ℕ) (θ : ℝ) (j : Fin K) (a c : Fin (K + 1))
    (h1 : a ≠ j.castSucc) (h2 : a ≠ j.succ) (h3 : a ≠ c) : cascM K θ j a c = 0 := by
  simp [cascM, h1, h2, h3]

/-- A cascade entry with column outside the two rotated positions and row
different from the column vanishes. -/
private theorem casc_col_out (K : ℕ) (θ : ℝ) (j : Fin K) (a c : Fin (K + 1))
    (h1 : c ≠ j.castSucc) (h2 : c ≠ j.succ) (h3 : a ≠ c) : cascM K θ j a c = 0 := by
  simp [cascM, h1, h2, h3]

/-- Each cascade step is unitary: it is the identity outside two adjacent unary
positions and a real rotation on their span. -/
theorem cascM_uni (K : ℕ) (θ : ℝ) (j : Fin K) :
    cascM K θ j ∈ Matrix.unitaryGroup (Fin (K + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hne := casc_ne K j
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    by_cases hacs : a = j.castSucc
    · subst hacs
      rw [sum_two_pts
        (fun c => cascM K θ j j.castSucc c * star (cascM K θ j j.castSucc c))
        j.castSucc j.succ hne ?_]
      · rw [casc_cs_cs, casc_cs_su]
        simp only [Complex.star_def, Complex.conj_ofReal, star_neg, neg_mul_neg]
        push_cast
        have h1 : ((Real.cos θ) * (Real.cos θ) + (Real.sin θ) * (Real.sin θ) : ℝ) = 1 := by
          have h0 := Real.sin_sq_add_cos_sq θ
          rw [sq, sq] at h0
          linarith
        exact_mod_cast h1
      · intro c h1 h2
        rw [casc_col_out K θ j j.castSucc c h1 h2 (Ne.symm h1)]
        ring
    · by_cases hasu : a = j.succ
      · subst hasu
        rw [sum_two_pts
          (fun c => cascM K θ j j.succ c * star (cascM K θ j j.succ c))
          j.castSucc j.succ hne ?_]
        · rw [casc_su_cs, casc_su_su]
          simp only [Complex.star_def, Complex.conj_ofReal]
          rw [add_comm]
          push_cast
          have h1 : ((Real.cos θ) * (Real.cos θ) + (Real.sin θ) * (Real.sin θ) : ℝ) = 1 := by
            have h0 := Real.sin_sq_add_cos_sq θ
            rw [sq, sq] at h0
            linarith
          exact_mod_cast h1
        · intro c h1 h2
          rw [casc_col_out K θ j j.succ c h1 h2 (Ne.symm h2)]
          ring
      · rw [Finset.sum_eq_single a
          (fun c _ hca => by rw [casc_row_out K θ j a c hacs hasu (Ne.symm hca), zero_mul])
          (fun h => absurd (Finset.mem_univ a) h)]
        rw [casc_diag K θ j a hacs hasu]
        simp
  · rw [Matrix.one_apply_ne hab]
    by_cases hacs : a = j.castSucc
    · subst hacs
      by_cases hbsu : b = j.succ
      · subst hbsu
        rw [sum_two_pts
          (fun c => cascM K θ j j.castSucc c * star (cascM K θ j j.succ c))
          j.castSucc j.succ hne ?_]
        · rw [casc_cs_cs, casc_cs_su, casc_su_cs, casc_su_su]
          simp only [Complex.star_def, Complex.conj_ofReal]
          push_cast
          ring
        · intro c h1 h2
          rw [casc_col_out K θ j j.castSucc c h1 h2 (Ne.symm h1)]
          ring
      · -- b outside the rotated pair
        have hb1 : b ≠ j.castSucc := fun h => hab h.symm
        have hb2 : b ≠ j.succ := fun h => hbsu h
        rw [Finset.sum_eq_zero]
        intro c _
        by_cases hccs : c = j.castSucc
        · subst hccs
          rw [casc_cs_cs, casc_row_out K θ j b j.castSucc hb1 hb2 hb1, star_zero,
            mul_zero]
        · by_cases hcsu : c = j.succ
          · subst hcsu
            rw [casc_cs_su, casc_row_out K θ j b j.succ hb1 hb2 hb2, star_zero, mul_zero]
          · rw [casc_col_out K θ j j.castSucc c hccs hcsu (Ne.symm hccs)]
            ring
    · by_cases hasu : a = j.succ
      · subst hasu
        by_cases hbcs : b = j.castSucc
        · subst hbcs
          rw [sum_two_pts
            (fun c => cascM K θ j j.succ c * star (cascM K θ j j.castSucc c))
            j.castSucc j.succ hne ?_]
          · rw [casc_su_cs, casc_su_su, casc_cs_cs, casc_cs_su]
            simp only [Complex.star_def, Complex.conj_ofReal, star_neg]
            push_cast
            ring
          · intro c h1 h2
            rw [casc_col_out K θ j j.succ c h1 h2 (Ne.symm h2)]
            ring
        · have hb1 : b ≠ j.castSucc := hbcs
          have hb2 : b ≠ j.succ := fun h => hab h.symm
          rw [Finset.sum_eq_zero]
          intro c _
          by_cases hcsu : c = j.succ
          · subst hcsu
            rw [casc_su_su, casc_row_out K θ j b j.succ hb1 hb2 hb2, star_zero, mul_zero]
          · by_cases hccs : c = j.castSucc
            · subst hccs
              rw [casc_su_cs, casc_row_out K θ j b j.castSucc hb1 hb2 hb1, star_zero,
                mul_zero]
            · rw [casc_col_out K θ j j.succ c hccs hcsu (Ne.symm hcsu)]
              ring
      · -- a outside the rotated pair; split on b
        by_cases hbcs : b = j.castSucc
        · subst hbcs
          rw [Finset.sum_eq_zero]
          intro c _
          by_cases hca : c = a
          · rw [hca, casc_diag K θ j a hacs hasu,
              casc_col_out K θ j j.castSucc a hacs hasu (Ne.symm hacs)]
            simp
          · rw [casc_row_out K θ j a c hacs hasu (Ne.symm hca), zero_mul]
        · by_cases hbsu : b = j.succ
          · subst hbsu
            rw [Finset.sum_eq_zero]
            intro c _
            by_cases hca : c = a
            · rw [hca, casc_diag K θ j a hacs hasu,
                casc_col_out K θ j j.succ a hacs hasu (Ne.symm hasu)]
              simp
            · rw [casc_row_out K θ j a c hacs hasu (Ne.symm hca), zero_mul]
          · -- a and b both outside the rotated pair
            have hb1 : b ≠ j.castSucc := hbcs
            have hb2 : b ≠ j.succ := hbsu
            rw [Finset.sum_eq_zero]
            intro c _
            by_cases hca : c = a
            · rw [hca, casc_diag K θ j a hacs hasu,
                casc_row_out K θ j b a hb1 hb2 (fun h => hab h.symm), star_zero, mul_zero]
            · rw [casc_row_out K θ j a c hacs hasu (Ne.symm hca), zero_mul]

/-- Eq. (23), gate-count side: the preparation unitary `B` costs `K` cascade
rotations for the order register plus `L` gates for each of the `K` index
registers. -/
def prepGates (K L : ℕ) : ℕ := K + K * L

/-- Eq. (23): with the certified cutoff `K = factorialTaylorCutoff m` at
precision `m = factorialTaylorPrecision s k`, the gate count of `B` is at
most a constant times `L · m / log₂ m`, the printed order
`O(L · log(T/ε)/loglog(T/ε))`. -/
theorem eq23_prep_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (L s k : ℕ), 1 ≤ L →
      m₀ ≤ factorialTaylorPrecision s k →
      (prepGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℝ) ≤
        (C : ℝ) * (L : ℝ) *
          ((factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ := source_equation18_precision
  refine ⟨2 * C, m₀, by omega, hm₀, fun L s k hL hm => ?_⟩
  have hm2 : 2 ≤ factorialTaylorPrecision s k := hm₀.trans hm
  have hlog : 0 < Nat.log 2 (factorialTaylorPrecision s k) :=
    Nat.log_pos (b := 2) (by norm_num) hm2
  have hcb : (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
      (C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
        (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := hrate s k hm
  have h1 : ((prepGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℕ) : ℝ) ≤
      2 * ((L : ℝ) * (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ)) := by
    have hkle : factorialTaylorCutoff (factorialTaylorPrecision s k) ≤
        factorialTaylorCutoff (factorialTaylorPrecision s k) * L :=
      Nat.le_mul_of_pos_right _ hL
    have h2 : (prepGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℕ) ≤
        2 * (factorialTaylorCutoff (factorialTaylorPrecision s k) * L) := by
      unfold prepGates
      omega
    have h3 := Nat.cast_le (α := ℝ) |>.mpr h2
    push_cast at h3
    linarith
  have hnn : 0 ≤ (L : ℝ) := by positivity
  calc
    (prepGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) L : ℝ)
        ≤ 2 * ((L : ℝ) * (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ)) := h1
    _ ≤ 2 * ((L : ℝ) * ((C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcb (by norm_num)) (by norm_num)
    _ = ((2 * C : ℕ) : ℝ) * (L : ℝ) *
          ((factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
        push_cast
        field_simp

/-! ### Eq. (24): controlled `select(H)` for Pauli-product terms -/

/-- The single-qubit Pauli operators `I, X, Y, Z` indexed by `0, 1, 2, 3`. -/
def pauli (p : Fin 4) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    match p with
    | 0 => if a = b then 1 else 0
    | 1 => if a = !b then 1 else 0
    | 2 => if a = !b then (if b then (-(Complex.I) : ℂ) else 1) else 0
    | 3 => if a = b then (if b then (-1 : ℂ) else 1) else 0

/-- Every Pauli operator is unitary and Hermitian, so its columns are
orthonormal: `Σ_x conj(P x a) * P x b = δ_{a b}`. -/
theorem pauli_col_ortho (p : Fin 4) (a b : Bool) :
    ∑ x : Bool, (pauli p a x) * star (pauli p b x) = if a = b then 1 else 0 := by
  fin_cases p <;> cases a <;> cases b <;>
    simp [pauli, Complex.conj_I, Complex.I_mul_I]

/-- A Pauli tensor product on `n` qubits, specified by a word
`w : Fin n → Fin 4` of single-qubit Pauli indices. -/
def pauliWord (n : ℕ) (w : Fin n → Fin 4) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.of fun x y => ∏ i, pauli (w i) (x i) (y i)

/-- Pauli tensor products are unitary: each word is a product of commuting
Hermitian unitaries, verified entrywise from the orthonormal-column factors. -/
theorem pauliWord_unitary (n : ℕ) (w : Fin n → Fin 4) :
    pauliWord n w * Matrix.conjTranspose (pauliWord n w) = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, pauliWord,
    Matrix.of_apply, star_prod]
  have hswap : (∑ x : Fin n → Bool, ∏ i, pauli (w i) (a i) (x i) *
      star (pauli (w i) (b i) (x i))) =
      ∏ i, ∑ x : Bool, pauli (w i) (a i) x *
        star (pauli (w i) (b i) x) := by
    classical
    calc ∑ x : Fin n → Bool, ∏ i, pauli (w i) (a i) (x i) *
          star (pauli (w i) (b i) (x i))
        = ∑ x ∈ Fintype.piFinset (fun _ => (Finset.univ : Finset Bool)), ∏ i,
            pauli (w i) (a i) (x i) * star (pauli (w i) (b i) (x i)) := by
          rw [Fintype.piFinset_univ]
      _ = ∏ i, ∑ j ∈ (Finset.univ : Finset Bool), pauli (w i) (a i) j *
          star (pauli (w i) (b i) j) :=
        (Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool))
          (fun i j => pauli (w i) (a i) (j) * star (pauli (w i) (b i) (j)))).symm
  have hmerge : ∀ j : Fin n → Bool,
      (∏ i, pauli (w i) (a i) (j i)) * (∏ i, star (pauli (w i) (b i) (j i))) =
      ∏ i, (pauli (w i) (a i) (j i) * star (pauli (w i) (b i) (j i))) :=
    fun _ => Finset.prod_mul_distrib.symm
  rw [Finset.sum_congr rfl fun j _ => hmerge j, hswap]
  by_cases hab : a = b
  · subst hab
    have h1 : ∀ j : Fin n, (∑ x : Bool, pauli (w j) (a j) (x) *
        star (pauli (w j) (a j) (x))) = 1 := by
      intro j
      simpa using pauli_col_ortho (w j) (a j) (a j)
    simp only [h1, Finset.prod_const]
    simp
  · have habi : ∃ i, a i ≠ b i := by
      by_contra hc
      have hall : ∀ i, a i = b i := fun i => Classical.byContradiction fun ne => hc ⟨i, ne⟩
      exact hab (funext hall)
    obtain ⟨i, hi⟩ := habi
    have h0 : (∑ x : Bool, pauli (w i) (a i) (x) *
        star (pauli (w i) (b i) (x))) = 0 := by
      have h := pauli_col_ortho (w i) (a i) (b i)
      rw [ite_eq_right hi] at h
      exact h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    rw [ite_eq_right hab]

/-- The controlled `select(H)` over `L` Pauli-product terms on `n` qubits:
block-diagonal in the term index, applying `pauliWord n (w ℓ)` in block `ℓ`. -/
def pauliSelect (L n : ℕ) (w : Fin L → Fin n → Fin 4) :
    Matrix (Fin L × (Fin n → Bool)) (Fin L × (Fin n → Bool)) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 then pauliWord n (w a.1) a.2 b.2 else 0

/-- Summing a block-diagonal kernel over the index register, only the block
matching the row index contributes. -/
private theorem sel_sum_fiber {L n : ℕ} {M : Type*} [AddCommMonoid M] [DecidableEq (Fin L)]
    (a : Fin L) (g : (Fin n → Bool) → M) :
    ∑ c : Fin L × (Fin n → Bool), (if a = c.1 then g c.2 else 0) = ∑ y, g y := by
  rw [Fintype.sum_prod_type]
  have h2 : ∀ ℓ : Fin L, (∑ y : Fin n → Bool, (if a = ℓ then g y else 0)) =
      (if a = ℓ then (∑ y : Fin n → Bool, g y) else 0) := by
    intro ℓ
    by_cases hc : a = ℓ
    · simp [hc]
    · simp [hc]
  simp only [h2]
  exact Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ a)

/-- Eq. (24), well-formedness side: the Pauli-product `select(H)` is unitary,
being block-diagonal with unitary Pauli-word blocks. -/
theorem pauliSelect_unitary (L n : ℕ) (w : Fin L → Fin n → Fin 4) :
    pauliSelect L n w * Matrix.conjTranspose (pauliSelect L n w) = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, pauliSelect,
    Matrix.of_apply]
  by_cases hab : a.1 = b.1
  · rw [← hab]
    have hstep : ∀ c : Fin L × (Fin n → Bool),
        ((if a.1 = c.1 then pauliWord n (w a.1) a.2 c.2 else 0) *
          star (if a.1 = c.1 then pauliWord n (w a.1) b.2 c.2 else 0)) =
        (if a.1 = c.1 then pauliWord n (w a.1) a.2 c.2 *
          star (pauliWord n (w a.1) b.2 c.2) else 0) := by
      intro c
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun c _ => hstep c]
    rw [sel_sum_fiber a.1 (fun y => pauliWord n (w a.1) a.2 y *
      star (pauliWord n (w a.1) b.2 y))]
    have hword := congrFun (congrFun (pauliWord_unitary n (w a.1)) a.2) b.2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hword
    rw [hword]
    by_cases h2 : a.2 = b.2
    · have habb : a = b := by
        rw [Prod.ext_iff]
        exact ⟨hab, h2⟩
      simp [habb]
    · have hne : a ≠ b := fun h => h2 (congrArg Prod.snd h)
      simp [h2, hne]
  · have hzero : ∀ c : Fin L × (Fin n → Bool),
        ((if a.1 = c.1 then pauliWord n (w a.1) a.2 c.2 else 0) *
          star (if b.1 = c.1 then pauliWord n (w b.1) b.2 c.2 else 0)) = 0 := by
      intro c
      by_cases h1 : a.1 = c.1
      · have hb : ¬(b.1 = c.1) := fun h => hab (h1.trans h.symm)
        simp [h1, hb]
      · simp [h1]
    rw [Finset.sum_congr rfl fun c _ => hzero c]
    have hne : a ≠ b := fun h => hab (congrArg Prod.fst h)
    simp [hne]

/-- Eq. (24), gate-count model: one controlled `select(H)` costs
`L·(n + ⌈log₂ L⌉)` gates (`L` controlled Pauli words on `n` qubits plus
`⌈log₂ L⌉` index logic), and `select(V)` uses `K` of them. -/
def selectVGates (K L n : ℕ) : ℕ := K * (L * (n + Nat.clog 2 (max 1 L)))

/-- Eq. (24): with the certified cutoff `K = factorialTaylorCutoff m` at
precision `m = factorialTaylorPrecision s k`, the gate count of `select(V)`
is at most a constant times `L·(n + log₂ L)·m / log₂ m`, the printed order
`O(L(n+log L)·log(T/ε)/loglog(T/ε))`. -/
theorem eq24_select_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (L n s k : ℕ), m₀ ≤ factorialTaylorPrecision s k →
      (selectVGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) L n : ℝ) ≤
        (C : ℝ) * ((L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ))) *
          ((factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ := source_equation18_precision
  refine ⟨C, m₀, hC, hm₀, fun L n s k hm => ?_⟩
  have hm2 : 2 ≤ factorialTaylorPrecision s k := hm₀.trans hm
  have hlog : 0 < Nat.log 2 (factorialTaylorPrecision s k) :=
    Nat.log_pos (b := 2) (by norm_num) hm2
  have hcb : (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
      (C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
        (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := hrate s k hm
  have hnn : 0 ≤ (L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ)) := by positivity
  calc
    (selectVGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) L n : ℝ)
        = (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) *
            ((L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ))) := by
          unfold selectVGates
          push_cast
          ring
    _ ≤ ((C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) *
          ((L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ))) :=
        mul_le_mul_of_nonneg_right hcb hnn
    _ = (C : ℝ) * ((L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ))) *
          ((factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
          ring

/-! ### Eq. (25): sparse-oracle segment gates -/

/-- Per-segment gate model of Eq. (25) for a sparse-oracle Hamiltonian:
`K` sparse-select operations, each costing `n` qubit-wide oracle work plus
`m` synthesis gates (with `log₂ L ≤ m` in the precision parameter). -/
def sparseSegGates (K n m : ℕ) : ℕ := K * (n + m)

/-- Eq. (25): with the certified cutoff at precision
`m = factorialTaylorPrecision s k` and `2 ≤ n`, the sparse-oracle segment
cost is at most a constant times `n·m²/log₂ m`, the printed order
`O(n·log²(T/ε)/loglog(T/ε))`. -/
theorem eq25_sparse_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (n s k : ℕ), 2 ≤ n →
      m₀ ≤ factorialTaylorPrecision s k →
      (sparseSegGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) n
          (factorialTaylorPrecision s k) : ℝ) ≤
        (C : ℝ) * (n : ℝ) *
          ((factorialTaylorPrecision s k : ℝ) ^
              (2 : ℕ) / (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ := source_equation18_precision
  refine ⟨C, m₀, hC, hm₀, fun n s k hn hm => ?_⟩
  have hm2 : 2 ≤ factorialTaylorPrecision s k := hm₀.trans hm
  have hlog : 0 < Nat.log 2 (factorialTaylorPrecision s k) :=
    Nat.log_pos (b := 2) (by norm_num) hm2
  have hcb : (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
      (C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
        (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := hrate s k hm
  have hmR : (2 : ℝ) ≤ (factorialTaylorPrecision s k : ℝ) := by exact_mod_cast hm2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsub : ((n : ℝ) + (factorialTaylorPrecision s k : ℝ)) ≤
      (n : ℝ) * (factorialTaylorPrecision s k : ℝ) := by
    have hkey : (1 : ℝ) ≤ ((n : ℝ) - 1) * ((factorialTaylorPrecision s k : ℝ) - 1) := by
      nlinarith [hmR, hnR]
    nlinarith [hkey]
  have hnn : 0 ≤ (n : ℝ) := by positivity
  have hpow : ((factorialTaylorPrecision s k : ℝ) ^ (2 : ℕ)) =
      (factorialTaylorPrecision s k : ℝ) * (factorialTaylorPrecision s k : ℝ) := by ring
  calc
    (sparseSegGates (factorialTaylorCutoff (factorialTaylorPrecision s k)) n
        (factorialTaylorPrecision s k) : ℝ)
        = (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) *
            ((n : ℝ) + (factorialTaylorPrecision s k : ℝ)) := by
          unfold sparseSegGates
          push_cast
          ring
    _ ≤ (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) *
          ((n : ℝ) * (factorialTaylorPrecision s k : ℝ)) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
    _ ≤ ((C : ℝ) * (factorialTaylorPrecision s k : ℝ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) *
          ((n : ℝ) * (factorialTaylorPrecision s k : ℝ)) :=
        mul_le_mul_of_nonneg_right hcb (by positivity)
    _ = (C : ℝ) * (n : ℝ) *
          ((factorialTaylorPrecision s k : ℝ) ^ (2 : ℕ) /
            (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) := by
          rw [hpow]
          ring

end Qatlib.Papers.TruncTaylor14.ResourceCount
