/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.ProjectorQAOA26.StageStability.OpNormBridge
import Qatlib.Papers.ProjectorQAOA26.StageStability.RankOneOpNorm
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped Matrix Matrix.Norms.L2Operator BigOperators

theorem sum_sq_le_card_mul_sum_sq {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have key : ∀ i j : ι, f i * f j ≤ (f i ^ 2 + f j ^ 2) / 2 := by
    intro i j
    have h := sq_nonneg (f i - f j)
    nlinarith
  have cardsmul : ∀ (c : ℝ), ∑ _ ∈ s, c = (s.card : ℝ) * c := by
    intro c
    rw [Finset.sum_const]
    norm_num
  calc (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i * f j := by
        rw [sq, Finset.sum_mul_sum]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
        have key1 : ∀ i ∈ s, ∑ j ∈ s, f i ^ 2 / 2 = ((s.card : ℝ) / 2) * f i ^ 2 := by
          intro i _
          rw [cardsmul]
          ring
        have half1 : ∑ i ∈ s, ∑ j ∈ s, f i ^ 2 / 2
            = ((s.card : ℝ) / 2) * ∑ i ∈ s, f i ^ 2 := by
          rw [Finset.sum_congr rfl key1, Finset.mul_sum]
        have half2 : ∑ i ∈ s, ∑ j ∈ s, f j ^ 2 / 2
            = ((s.card : ℝ) / 2) * ∑ i ∈ s, f i ^ 2 := by
          rw [Finset.sum_comm]
          exact half1
        have hsplit : ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) / 2
            = ∑ i ∈ s, ∑ j ∈ s, f i ^ 2 / 2 + ∑ i ∈ s, ∑ j ∈ s, f j ^ 2 / 2 := by
          simp_rw [add_div, Finset.sum_add_distrib]
        rw [hsplit, half1, half2]
        ring

private theorem sum_const_real {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ℝ) :
    ∑ _ ∈ s, c = (s.card : ℝ) * c := by
  rw [Finset.sum_const]
  norm_num

def ec3SatB (v : Fin 3 → Bool) : Bool :=
  (v 0 && !v 1 && !v 2) || (!v 0 && v 1 && !v 2) || (!v 0 && !v 1 && v 2)

def ec3TrueIndex (v : Fin 3 → Bool) : Fin 3 := if v 1 then 1 else if v 2 then 2 else 0

theorem ec3TrueIndex_decide_self (i : Fin 3) :
    ec3TrueIndex (fun j => decide (j = i)) = i := by
  fin_cases i <;> simp [ec3TrueIndex]

theorem ec3SatB_decide_true (i : Fin 3) :
    ec3SatB (fun j => decide (j = i)) = true := by
  fin_cases i <;> simp [ec3SatB]

theorem ec3SatB_spec {v : Fin 3 → Bool} (h : ec3SatB v = true) (j : Fin 3) :
    v j = decide (j = ec3TrueIndex v) := by
  by_cases h0 : v 0 = true <;> by_cases h1 : v 1 = true <;>
    by_cases h2 : v 2 = true <;>
    simp [ec3SatB, ec3TrueIndex, h0, h1, h2] at h ⊢ <;>
    fin_cases j <;> simp [h0, h1, h2]

def EC3Feasible (m f : ℕ) : Type :=
  {g : (Fin m × Fin 3) ⊕ Fin f → Bool //
    ∀ c : Fin m, ec3SatB (fun j => g (Sum.inl (c, j))) = true}

instance ec3FeasibleFintype (m f : ℕ) : Fintype (EC3Feasible m f) := by
  unfold EC3Feasible
  infer_instance

def ec3FeasibleEquiv (m f : ℕ) :
    EC3Feasible m f ≃ ((Fin m → Fin 3) × (Fin f → Bool)) where
  toFun g := (fun c => ec3TrueIndex (fun j => g.1 (Sum.inl (c, j))),
    fun k => g.1 (Sum.inr k))
  invFun p := ⟨Sum.elim
      (fun q : Fin m × Fin 3 => decide (q.2 = p.1 q.1)) p.2,
    fun c => by
      have := ec3SatB_decide_true (p.1 c)
      exact this⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    cases i with
    | inl q =>
        simp only [Sum.elim_inl]
        exact (ec3SatB_spec (g.2 q.1) q.2).symm
    | inr k => simp only [Sum.elim_inr]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext c
      exact ec3TrueIndex_decide_self (p.1 c)
    · funext k
      rfl

theorem card_EC3Feasible (m f : ℕ) :
    Fintype.card (EC3Feasible m f) = 3 ^ m * 2 ^ f := by
  have h := Fintype.card_congr (ec3FeasibleEquiv m f)
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at h
  exact h

theorem ec3L_real (m f : ℕ) :
    (Fintype.card (EC3Feasible m f) : ℝ)
      = (2 : ℝ) ^ (3 * m + f) * ((3 : ℝ) / 8) ^ m := by
  have h : ((3 ^ m * 2 ^ f : ℕ) : ℝ) = (3 : ℝ) ^ m * (2 : ℝ) ^ f := by
    push_cast
    ring
  rw [card_EC3Feasible, h]
  have h8 : ((2 : ℝ) ^ 3) = 8 := by norm_num
  rw [pow_add, pow_mul, h8, div_pow]
  field_simp

section Moments

variable {C : Type} [Fintype C] [DecidableEq C]

def ec3A1 (xstar : C) (E : C → ℝ) : ℝ :=
  (Fintype.card C : ℝ)⁻¹ * ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹

def ec3A2 (xstar : C) (E : C → ℝ) : ℝ :=
  (Fintype.card C : ℝ)⁻¹ * ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2)

variable {xstar : C} {E : C → ℝ} {R : ℝ}

theorem ec3A1_nonneg (hx : ∀ x ≠ xstar, 1 ≤ E x) : 0 ≤ ec3A1 xstar E := by
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) (Finset.sum_nonneg ?_)
  intro x hx'
  exact inv_nonneg.mpr (le_trans zero_le_one (hx x (Finset.ne_of_mem_erase hx')))

theorem ec3A2_nonneg (_hx : ∀ x ≠ xstar, 1 ≤ E x) : 0 ≤ ec3A2 xstar E := by
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) (Finset.sum_nonneg ?_)
  intro x hx'
  exact sq_nonneg ((E x)⁻¹)

theorem ec3A1_ge (hR : 1 ≤ R) (hER : ∀ x ≠ xstar, E x ≤ R)
    (hE1 : ∀ x ≠ xstar, 1 ≤ E x) (hL : 1 ≤ Fintype.card C) :
    ((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R) ≤ ec3A1 xstar E := by
  have hLn : 1 ≤ Fintype.card C := hL
  have hLp : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hLn
  have hRp : (0 : ℝ) < R := by linarith
  have hcard : ((Finset.univ.erase xstar).card : ℝ) = (Fintype.card C : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xstar), Finset.card_univ,
      Nat.cast_sub hLn]
    norm_num
  have hsum : ((Finset.univ.erase xstar).card : ℝ) * R⁻¹
      ≤ ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹ := by
    calc ((Finset.univ.erase xstar).card : ℝ) * R⁻¹
        = ∑ x ∈ Finset.univ.erase xstar, R⁻¹ := (sum_const_real _ _).symm
      _ ≤ ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹ := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le
            (lt_of_lt_of_le zero_lt_one (hE1 x (Finset.ne_of_mem_erase hx)))
            (hER x (Finset.ne_of_mem_erase hx))
  calc ((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R)
      = (Fintype.card C : ℝ)⁻¹ * (((Finset.univ.erase xstar).card : ℝ) * R⁻¹) := by
        rw [hcard]
        field_simp
    _ ≤ (Fintype.card C : ℝ)⁻¹ * ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hLp.le)
    _ = ec3A1 xstar E := rfl

theorem ec3A1_le_one (hE1 : ∀ x ≠ xstar, 1 ≤ E x) (hL : 1 ≤ Fintype.card C) :
    ec3A1 xstar E ≤ 1 := by
  have hLn : 1 ≤ Fintype.card C := hL
  have hLp : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hLn
  have hcard : ((Finset.univ.erase xstar).card : ℝ) = (Fintype.card C : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xstar), Finset.card_univ,
      Nat.cast_sub hLn]
    norm_num
  have hsum : ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹
      ≤ ((Finset.univ.erase xstar).card : ℝ) * 1 := by
    calc ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹
        ≤ ∑ x ∈ Finset.univ.erase xstar, 1 := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx1 : 1 ≤ E x := hE1 x (Finset.ne_of_mem_erase hx)
          rw [← one_div, div_le_iff₀ (by linarith : (0 : ℝ) < E x)]
          linarith
      _ = ((Finset.univ.erase xstar).card : ℝ) * 1 := sum_const_real _ _
  calc ec3A1 xstar E
      = (Fintype.card C : ℝ)⁻¹ * ∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹ := rfl
    _ ≤ (Fintype.card C : ℝ)⁻¹ * (((Finset.univ.erase xstar).card : ℝ) * 1) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hLp.le)
    _ ≤ 1 := by
        rw [hcard, mul_one, inv_mul_eq_div, div_le_one hLp]
        linarith

theorem ec3A2_ge (hR : 1 ≤ R) (hER : ∀ x ≠ xstar, E x ≤ R)
    (hE1 : ∀ x ≠ xstar, 1 ≤ E x) (hL : 1 ≤ Fintype.card C) :
    ((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R ^ 2) ≤ ec3A2 xstar E := by
  have hLn : 1 ≤ Fintype.card C := hL
  have hLp : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hLn
  have hRp : (0 : ℝ) < R := by linarith
  have hcard : ((Finset.univ.erase xstar).card : ℝ) = (Fintype.card C : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xstar), Finset.card_univ,
      Nat.cast_sub hLn]
    norm_num
  have hsum : ((Finset.univ.erase xstar).card : ℝ) * R⁻¹ ^ 2
      ≤ ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2) := by
    calc ((Finset.univ.erase xstar).card : ℝ) * R⁻¹ ^ 2
        = ∑ x ∈ Finset.univ.erase xstar, (R⁻¹ ^ 2) := (sum_const_real _ _).symm
      _ ≤ ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hin : R⁻¹ ≤ (E x)⁻¹ := by
            rw [← one_div, ← one_div]
            exact one_div_le_one_div_of_le
              (lt_of_lt_of_le zero_lt_one (hE1 x (Finset.ne_of_mem_erase hx)))
              (hER x (Finset.ne_of_mem_erase hx))
          have hnn : 0 ≤ R⁻¹ := inv_nonneg.mpr hRp.le
          have hnE : 0 ≤ (E x)⁻¹ := by
            exact inv_nonneg.mpr (le_trans zero_le_one
              (hE1 x (Finset.ne_of_mem_erase hx)))
          have e1 := mul_le_mul_of_nonneg_left hin hnn
          have e2 := mul_le_mul_of_nonneg_right hin hnE
          nlinarith [e1, e2]
  calc ((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R ^ 2)
      = (Fintype.card C : ℝ)⁻¹ * (((Finset.univ.erase xstar).card : ℝ) * R⁻¹ ^ 2) := by
        rw [hcard]
        field_simp
    _ ≤ (Fintype.card C : ℝ)⁻¹ * ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hLp.le)
    _ = ec3A2 xstar E := rfl

theorem ec3A2_pos (hR : 1 ≤ R) (hER : ∀ x ≠ xstar, E x ≤ R)
    (hE1 : ∀ x ≠ xstar, 1 ≤ E x) (hL2 : 2 ≤ Fintype.card C) :
    0 < ec3A2 xstar E := by
  have h1 := ec3A2_ge hR hER hE1 (le_trans (by omega) hL2)
  have hR0 : (0 : ℝ) < R := by linarith
  have hL0 : (0 : ℝ) < (Fintype.card C : ℝ) := by
    exact_mod_cast le_trans (by omega) hL2
  have hnum : (0 : ℝ) < (Fintype.card C : ℝ) - 1 := by
    have : (1 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hL2
    linarith
  have hden : (0 : ℝ) < (Fintype.card C : ℝ) * R ^ 2 := by
    positivity
  have hpos : (0 : ℝ) < ((Fintype.card C : ℝ) - 1)
      / ((Fintype.card C : ℝ) * R ^ 2) := div_pos hnum hden
  linarith

theorem ec3A2_le_one (hE1 : ∀ x ≠ xstar, 1 ≤ E x) (hL : 1 ≤ Fintype.card C) :
    ec3A2 xstar E ≤ 1 := by
  have hLn : 1 ≤ Fintype.card C := hL
  have hLp : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hLn
  have hcard : ((Finset.univ.erase xstar).card : ℝ) = (Fintype.card C : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xstar), Finset.card_univ,
      Nat.cast_sub hLn]
    norm_num
  have hsum : ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2)
      ≤ ((Finset.univ.erase xstar).card : ℝ) * 1 := by
    calc ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2)
        ≤ ∑ x ∈ Finset.univ.erase xstar, 1 := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx1 : 1 ≤ E x := hE1 x (Finset.ne_of_mem_erase hx)
          have hin : (E x)⁻¹ ≤ 1 := by
            rw [← one_div, div_le_iff₀ (by linarith : (0 : ℝ) < E x)]
            linarith
          have hnn : 0 ≤ (E x)⁻¹ := by positivity
          have e1 := mul_le_mul_of_nonneg_left hin hnn
          nlinarith [e1]
      _ = ((Finset.univ.erase xstar).card : ℝ) * 1 := sum_const_real _ _
  calc ec3A2 xstar E
      = (Fintype.card C : ℝ)⁻¹ * ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2) := rfl
    _ ≤ (Fintype.card C : ℝ)⁻¹ * (((Finset.univ.erase xstar).card : ℝ) * 1) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hLp.le)
    _ ≤ 1 := by
        rw [hcard, mul_one, inv_mul_eq_div, div_le_one hLp]
        linarith

theorem ec3A1_sq_le (hL : 1 ≤ Fintype.card C) :
    (ec3A1 xstar E) ^ 2 ≤ ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ)
      * ec3A2 xstar E := by
  have hLn : 1 ≤ Fintype.card C := hL
  have hLp : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hLn
  have hcard : ((Finset.univ.erase xstar).card : ℝ) = (Fintype.card C : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xstar), Finset.card_univ,
      Nat.cast_sub hLn]
    norm_num
  have hcs := sum_sq_le_card_mul_sum_sq (Finset.univ.erase xstar)
    (fun x => (E x)⁻¹)
  rw [hcard] at hcs
  have hsm2 : ∑ x ∈ Finset.univ.erase xstar, ((E x)⁻¹ ^ 2)
      = (Fintype.card C : ℝ) * ec3A2 xstar E := by
    rw [ec3A2, mul_comm]
    field_simp
  rw [hsm2] at hcs
  calc (ec3A1 xstar E) ^ 2
      = ((Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ)⁻¹
          * (∑ x ∈ Finset.univ.erase xstar, (E x)⁻¹) ^ 2)) := by
        unfold ec3A1
        rw [mul_pow]
        ring
    _ ≤ ((Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ)⁻¹
          * (((Fintype.card C : ℝ) - 1) * ((Fintype.card C : ℝ)
            * ec3A2 xstar E)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs
          (inv_nonneg.mpr hLp.le)) (inv_nonneg.mpr hLp.le)
    _ = ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ) * ec3A2 xstar E := by
        field_simp

end Moments

section Prefactor

variable {C : Type} [Fintype C] [DecidableEq C]

def ec3QN (xstar : C) (E : C → ℝ) : ℝ :=
  2 * ec3A1 xstar E / ((1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E))

variable {xstar : C} {E : C → ℝ} {R : ℝ}

theorem ec3QN_le_two (hA1 : 0 ≤ ec3A1 xstar E) (hA2pos : 0 < ec3A2 xstar E)
    (_hA2le : ec3A2 xstar E ≤ 1) (hcs : (ec3A1 xstar E) ^ 2 ≤ ec3A2 xstar E) :
    ec3QN xstar E ≤ 2 := by
  have hd : (0 : ℝ) < (1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr hA2pos)
  have hs : ec3A1 xstar E ≤ Real.sqrt (ec3A2 xstar E) := by
    calc ec3A1 xstar E = Real.sqrt ((ec3A1 xstar E) ^ 2) :=
          (Real.sqrt_sq hA1).symm
      _ ≤ Real.sqrt (ec3A2 xstar E) := Real.sqrt_le_sqrt hcs
  have hkey : ec3A1 xstar E
      ≤ (1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E) := by
    calc ec3A1 xstar E ≤ Real.sqrt (ec3A2 xstar E) := hs
      _ ≤ 1 * Real.sqrt (ec3A2 xstar E) := by rw [one_mul]
      _ ≤ (1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          linarith
  rw [ec3QN, div_le_iff₀ hd]
  exact mul_le_mul_of_nonneg_left hkey zero_le_two

theorem le_ec3QN (hA1ge : ((Fintype.card C : ℝ) - 1)
      / ((Fintype.card C : ℝ) * R) ≤ ec3A1 xstar E)
    (hA1 : 0 ≤ ec3A1 xstar E) (hA1le : ec3A1 xstar E ≤ 1)
    (hA2pos : 0 < ec3A2 xstar E) (hA2le : ec3A2 xstar E ≤ 1) :
    ((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R) ≤ ec3QN xstar E := by
  have hd : (0 : ℝ) < (1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr hA2pos)
  have hsqrt : Real.sqrt (ec3A2 xstar E) ≤ 1 := by
    calc Real.sqrt (ec3A2 xstar E) ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt hA2le
      _ = 1 := Real.sqrt_one
  rw [ec3QN, le_div_iff₀ hd]
  calc (((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R))
      * ((1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E))
      ≤ ec3A1 xstar E * ((1 + ec3A1 xstar E) * Real.sqrt (ec3A2 xstar E)) :=
        mul_le_mul_of_nonneg_right hA1ge (by
          refine mul_nonneg ?_ (Real.sqrt_nonneg _)
          linarith)
    _ ≤ ec3A1 xstar E * ((1 + ec3A1 xstar E) * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hA1
        exact mul_le_mul_of_nonneg_left hsqrt (by linarith)
    _ = ec3A1 xstar E + (ec3A1 xstar E) * (ec3A1 xstar E) := by ring
    _ ≤ 2 * ec3A1 xstar E := by
        have e : (0 : ℝ) ≤ ec3A1 xstar E * (1 - ec3A1 xstar E) :=
          mul_nonneg hA1 (by linarith)
        nlinarith [e]

end Prefactor

section Interpolation

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem opNorm_diagonal_le {d : I → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ‖d i‖ ≤ r) : ‖Matrix.diagonal d‖ ≤ r := by
  refine opNorm_le_of_l2 hr ?_
  intro x
  have hvec : ∀ i, (Matrix.diagonal d *ᵥ x) i = d i * x i := by
    intro i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  refine le_of_sq_le (l2norm_nonneg _) (mul_nonneg hr (l2norm_nonneg x)) ?_
  calc l2norm (Matrix.diagonal d *ᵥ x) ^ 2
      = ∑ i, Complex.normSq (d i * x i) := by
        rw [l2norm_sq]
        exact Finset.sum_congr rfl fun i _ => by rw [hvec i]
    _ = ∑ i, Complex.normSq (d i) * Complex.normSq (x i) := by
        exact Finset.sum_congr rfl fun i _ => Complex.normSq_mul _ _
    _ ≤ ∑ i, r ^ 2 * Complex.normSq (x i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (Complex.normSq_nonneg _)
        rw [Complex.normSq_eq_norm_sq]
        exact sq_le_sq' (by have := norm_nonneg (d i); linarith) (h i)
    _ = r ^ 2 * l2norm x ^ 2 := by
        rw [← Finset.mul_sum, l2norm_sq]
    _ = (r * l2norm x) ^ 2 := by rw [mul_pow]

theorem opNorm_one_sub_rankOne_le_one {ω : I → ℂ} (hω : l2norm ω = 1) :
    ‖(1 : Matrix I I ℂ) - rankOne ω‖ ≤ 1 := by
  refine opNorm_le_of_l2 zero_le_one ?_
  intro x
  have hvec : ((1 : Matrix I I ℂ) - rankOne ω) *ᵥ x = x - l2inner ω x • ω := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, rankOne_mulVec]
  have hsplit : l2inner x (l2inner ω x • ω) = l2inner ω x * star (l2inner ω x) := by
    rw [l2inner_smul_right, l2inner_symm ω x]
  have hre : (l2inner ω x * star (l2inner ω x)).re = Complex.normSq (l2inner ω x) := by
    simp [Complex.normSq]
  refine le_of_sq_le (l2norm_nonneg _)
    (mul_nonneg zero_le_one (l2norm_nonneg x)) ?_
  calc l2norm (((1 : Matrix I I ℂ) - rankOne ω) *ᵥ x) ^ 2
      = l2norm x ^ 2 + (Real.sqrt (Complex.normSq (l2inner ω x)) * l2norm ω) ^ 2
          - 2 * Complex.normSq (l2inner ω x) := by
        rw [hvec, l2norm_sub_sq, l2norm_smul, hsplit, hre]
    _ = l2norm x ^ 2 + Complex.normSq (l2inner ω x)
          - 2 * Complex.normSq (l2inner ω x) := by
        rw [hω, mul_pow, Real.sq_sqrt (Complex.normSq_nonneg _), one_pow, mul_one]
    _ ≤ l2norm x ^ 2 := by
        have := Complex.normSq_nonneg (l2inner ω x)
        linarith
    _ = (1 * l2norm x) ^ 2 := by rw [one_mul]

def interpHF (E : I → ℂ) (ω : I → ℂ) (s : ℝ) : Matrix I I ℂ :=
  (1 - s) • ((1 : Matrix I I ℂ) - rankOne ω) + s • Matrix.diagonal E

omit [Fintype I] in

theorem interpHF_sub (E : I → ℂ) (ω : I → ℂ) (s : ℝ) :
    interpHF E ω s - ((1 : Matrix I I ℂ) - rankOne ω)
      = s • (Matrix.diagonal E - ((1 : Matrix I I ℂ) - rankOne ω)) := by
  unfold interpHF
  module

theorem opNorm_real_smul_le (M : Matrix I I ℂ) (s : ℝ) (hs : 0 ≤ s) :
    ‖s • M‖ ≤ s * ‖M‖ := by
  refine opNorm_le_of_l2 (mul_nonneg hs (norm_nonneg M)) ?_
  intro x
  have hEq : (s • M) *ᵥ x = (s : ℝ) • (M *ᵥ x) := by
    funext i
    simp only [Matrix.mulVec, Pi.smul_apply, dotProduct, Finset.smul_sum,
      Matrix.smul_apply]
    exact Finset.sum_congr rfl fun j _ =>
      smul_mul_assoc s (M i j) (x j)
  have h1 : l2norm ((s : ℝ) • (M *ᵥ x)) ^ 2 ≤ (|s| * l2norm (M *ᵥ x)) ^ 2 := by
    have h2 : ∀ i, Complex.normSq (((s : ℝ) • (M *ᵥ x)) i)
        ≤ s ^ 2 * Complex.normSq ((M *ᵥ x) i) := by
      intro i
      rw [Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
        Complex.normSq_ofReal, ← sq]
    calc l2norm ((s : ℝ) • (M *ᵥ x)) ^ 2
        = ∑ i, Complex.normSq (((s : ℝ) • (M *ᵥ x)) i) := l2norm_sq _
      _ ≤ ∑ i, s ^ 2 * Complex.normSq ((M *ᵥ x) i) :=
          Finset.sum_le_sum (fun i _ => h2 i)
      _ = s ^ 2 * l2norm (M *ᵥ x) ^ 2 := by
          rw [← Finset.mul_sum, l2norm_sq]
      _ = (|s| * l2norm (M *ᵥ x)) ^ 2 := by rw [mul_pow, sq_abs]
  rw [hEq]
  calc l2norm ((s : ℝ) • (M *ᵥ x))
      ≤ |s| * l2norm (M *ᵥ x) :=
        le_of_sq_le (l2norm_nonneg _)
          (mul_nonneg (abs_nonneg s) (l2norm_nonneg _)) h1
    _ = s * l2norm (M *ᵥ x) := by rw [abs_of_nonneg hs]
    _ ≤ s * ‖M‖ * l2norm x := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (l2norm_mulVec_le M x) hs

theorem opNorm_interpHF_sub_le {E : I → ℂ} {ω : I → ℂ} {R s : ℝ}
    (hω : l2norm ω = 1) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hE : ∀ i, ‖E i‖ ≤ R) :
    ‖interpHF E ω s - ((1 : Matrix I I ℂ) - rankOne ω)‖ ≤ s * (R + 1) := by
  have h1 : ‖Matrix.diagonal E - ((1 : Matrix I I ℂ) - rankOne ω)‖ ≤ R + 1 := by
    calc ‖Matrix.diagonal E - ((1 : Matrix I I ℂ) - rankOne ω)‖
        ≤ ‖Matrix.diagonal E‖ + ‖(1 : Matrix I I ℂ) - rankOne ω‖ :=
          norm_sub_le _ _
      _ ≤ R + 1 := add_le_add (opNorm_diagonal_le hR hE)
          (opNorm_one_sub_rankOne_le_one hω)
  rw [interpHF_sub]
  calc ‖s • (Matrix.diagonal E - ((1 : Matrix I I ℂ) - rankOne ω))‖
      ≤ s * ‖Matrix.diagonal E - ((1 : Matrix I I ℂ) - rankOne ω)‖ :=
        opNorm_real_smul_le _ _ hs
    _ ≤ s * (R + 1) := mul_le_mul_of_nonneg_left h1 hs

end Interpolation

section Core

variable {C : Type} [Fintype C] [DecidableEq C]

theorem ec3_deterministic_core {xstar : C} {E : C → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hE : ∀ x ≠ xstar, 1 ≤ E x ∧ E x ≤ R)
    (hL2 : 2 ≤ Fintype.card C) :
    ((Fintype.card C : ℝ) - 1) / ((Fintype.card C : ℝ) * R) ≤ ec3QN xstar E
      ∧ ec3QN xstar E ≤ 2 := by
  have hE1 : ∀ x ≠ xstar, 1 ≤ E x := fun x hx => (hE x hx).1
  have hER : ∀ x ≠ xstar, E x ≤ R := fun x hx => (hE x hx).2
  have hL1 : 1 ≤ Fintype.card C := le_trans (by omega) hL2
  have hA1ge := ec3A1_ge hR hER hE1 hL1
  have hA1 := ec3A1_nonneg hE1
  have hA1le := ec3A1_le_one hE1 hL1
  have hA2pos := ec3A2_pos hR hER hE1 hL2
  have hA2le := ec3A2_le_one hE1 hL1
  have hA1sq := ec3A1_sq_le (xstar := xstar) (E := E) hL1
  have hLp : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hL1
  have hcs : (ec3A1 xstar E) ^ 2 ≤ ec3A2 xstar E := by
    calc (ec3A1 xstar E) ^ 2
        ≤ ((Fintype.card C : ℝ) - 1) / (Fintype.card C : ℝ) * ec3A2 xstar E := hA1sq
      _ ≤ 1 * ec3A2 xstar E := by
          refine mul_le_mul_of_nonneg_right ?_ hA2pos.le
          rw [div_le_one hLp]
          linarith
      _ = ec3A2 xstar E := by rw [one_mul]
  exact ⟨le_ec3QN hA1ge hA1 hA1le hA2pos hA2le, ec3QN_le_two hA1 hA2pos hA2le hcs⟩

end Core

end Qatlib.Papers.ProjectorQAOA26.StageStability
