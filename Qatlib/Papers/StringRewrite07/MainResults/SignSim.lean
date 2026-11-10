/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StringRewrite07.MainResults.HamiltonianPower
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StringRewrite07.MainResults

open Matrix

def sigmaX : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i ≠ j then 1 else 0

def minusVec : Fin 2 → ℝ :=
  fun a => if a = 0 then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹

def plusVec : Fin 2 → ℝ := fun _ => (Real.sqrt 2)⁻¹

theorem sigmaX_mulVec_minus : sigmaX *ᵥ minusVec = -minusVec := by
  funext i
  fin_cases i <;>
    simp [sigmaX, minusVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem one_mulVec_minus : (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ minusVec = minusVec := by
  simp

theorem minusVec_dot_self : minusVec ⬝ᵥ minusVec = 1 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [minusVec, dotProduct, Fin.sum_univ_two]
  field_simp
  nlinarith

theorem minusVec_dot_plusVec : minusVec ⬝ᵥ plusVec = 0 := by
  simp [minusVec, plusVec, dotProduct, Fin.sum_univ_two]

def blockLift {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  fun x y => M (A x.1 y.1) x.2 y.2

def tensorMinus {ι : Type} (w : ι → ℝ) : ι × Fin 2 → ℝ := fun x => w x.1 * minusVec x.2

def tensorPlus {ι : Type} (w : ι → ℝ) : ι × Fin 2 → ℝ := fun x => w x.1 * plusVec x.2

theorem tensorMinus_smul {ι : Type} (c : ℝ) (w : ι → ℝ) :
    tensorMinus (c • w) = c • tensorMinus w := by
  funext x
  simp [tensorMinus, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem tensorMinus_dot {ι : Type} [Fintype ι] (x z : ι → ℝ) :
    tensorMinus x ⬝ᵥ tensorMinus z = (x ⬝ᵥ z) * (minusVec ⬝ᵥ minusVec) := by
  simp only [dotProduct, tensorMinus, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem plusVec_dot_minusVec : plusVec ⬝ᵥ minusVec = 0 := by
  rw [dotProduct_comm]
  exact minusVec_dot_plusVec

theorem tensorPlus_dot_tensorMinus {ι : Type} [Fintype ι] (x z : ι → ℝ) :
    tensorPlus x ⬝ᵥ tensorMinus z = 0 := by
  have hfac : tensorPlus x ⬝ᵥ tensorMinus z = (x ⬝ᵥ z) * (plusVec ⬝ᵥ minusVec) := by
    simp only [dotProduct, tensorPlus, tensorMinus, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfac, plusVec_dot_minusVec, mul_zero]

theorem blockLift_isSymm {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.IsSymm) (hMsym : ∀ mu : ℝ, (M mu).IsSymm) :
    (blockLift A M).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro x y
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  simp only [blockLift]
  rw [hA.apply i j]
  exact ((hMsym (A i j)).apply b a).symm

theorem blockLift_tensorMinus {ι : Type} [Fintype ι]
    (A : Matrix ι ι ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ mu : ℝ, M mu *ᵥ minusVec = (Real.sqrt 2 * mu) • minusVec)
    (w : ι → ℝ) :
    blockLift A M *ᵥ tensorMinus w = tensorMinus (Real.sqrt 2 • (A *ᵥ w)) := by
  funext x
  obtain ⟨i, a⟩ := x
  have hL : (blockLift A M *ᵥ tensorMinus w) (i, a)
      = ∑ j : ι, ∑ b : Fin 2, M (A i j) a b * (w j * minusVec b) := by
    simp only [Matrix.mulVec, dotProduct, blockLift, tensorMinus, Fintype.sum_prod_type]
  have hR : tensorMinus (Real.sqrt 2 • (A *ᵥ w)) (i, a)
      = (Real.sqrt 2 * (A *ᵥ w) i) * minusVec a := by
    simp [tensorMinus, Pi.smul_apply, smul_eq_mul]
  rw [hL, hR]
  calc ∑ j : ι, ∑ b : Fin 2, M (A i j) a b * (w j * minusVec b)
      = ∑ j : ι, w j * (∑ b : Fin 2, M (A i j) a b * minusVec b) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = ∑ j : ι, w j * (Real.sqrt 2 * A i j * minusVec a) := by
        apply Finset.sum_congr rfl
        intro j _
        have hb : (∑ b : Fin 2, M (A i j) a b * minusVec b) = (M (A i j) *ᵥ minusVec) a := by
          rw [Matrix.mulVec, dotProduct]
        rw [hb, hM]
        simp [Pi.smul_apply, smul_eq_mul]
    _ = (Real.sqrt 2 * (A *ᵥ w) i) * minusVec a := by
        have hfac : ∑ j : ι, w j * (Real.sqrt 2 * A i j * minusVec a)
            = Real.sqrt 2 * minusVec a * ∑ j : ι, A i j * w j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hfac, Matrix.mulVec, dotProduct]
        ring

theorem blockLift_pow_tensorMinus {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ mu : ℝ, M mu *ᵥ minusVec = (Real.sqrt 2 * mu) • minusVec)
    (m : ℕ) (w : ι → ℝ) :
    ((blockLift A M) ^ m) *ᵥ tensorMinus w
      = tensorMinus (((Real.sqrt 2) ^ m) • ((A ^ m) *ᵥ w)) := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
      calc ((blockLift A M) ^ (m + 1)) *ᵥ tensorMinus w
          = ((blockLift A M) ^ m * blockLift A M) *ᵥ tensorMinus w := by rw [pow_succ]
        _ = ((blockLift A M) ^ m) *ᵥ (blockLift A M *ᵥ tensorMinus w) := by
              rw [← Matrix.mulVec_mulVec]
        _ = ((blockLift A M) ^ m) *ᵥ tensorMinus (Real.sqrt 2 • (A *ᵥ w)) := by
              rw [blockLift_tensorMinus A M hM]
        _ = tensorMinus
              (((Real.sqrt 2) ^ m) • ((A ^ m) *ᵥ (Real.sqrt 2 • (A *ᵥ w)))) := ih _
        _ = tensorMinus (((Real.sqrt 2) ^ (m + 1)) • ((A ^ (m + 1)) *ᵥ w)) := by
              have h1 : (A ^ m) *ᵥ (Real.sqrt 2 • (A *ᵥ w))
                  = Real.sqrt 2 • ((A ^ (m + 1)) *ᵥ w) := by
                rw [Matrix.mulVec_smul, pow_succ, ← Matrix.mulVec_mulVec]
              rw [h1, smul_smul]
              simp only [pow_succ]

theorem sign_sim_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ mu : ℝ, M mu *ᵥ minusVec = (Real.sqrt 2 * mu) • minusVec)
    (m : ℕ) (x y : ι → ℝ) :
    tensorMinus x ⬝ᵥ (((blockLift A M) ^ m) *ᵥ tensorMinus y)
      = (Real.sqrt 2) ^ m * (x ⬝ᵥ ((A ^ m) *ᵥ y)) := by
  rw [blockLift_pow_tensorMinus A M hM m y, tensorMinus_smul, dotProduct_smul,
    tensorMinus_dot, minusVec_dot_self, mul_one]
  simp [smul_eq_mul]

theorem sign_sim_no_plus_transition {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ mu : ℝ, M mu *ᵥ minusVec = (Real.sqrt 2 * mu) • minusVec)
    (m : ℕ) (x y : ι → ℝ) :
    tensorPlus x ⬝ᵥ (((blockLift A M) ^ m) *ᵥ tensorMinus y) = 0 := by
  rw [blockLift_pow_tensorMinus A M hM m y, tensorMinus_smul, dotProduct_smul,
    tensorPlus_dot_tensorMinus]
  simp

theorem difference_from_minus_sector {σ : Type} [Fintype σ]
    (B : Matrix σ σ ℝ) (a0 a1 w0 wp wm am : σ → ℝ)
    (ham : a0 - a1 = -(Real.sqrt 2 • am))
    (hw0 : w0 = (Real.sqrt 2)⁻¹ • (wp + wm))
    (hplus : am ⬝ᵥ (B *ᵥ wp) = 0) :
    a0 ⬝ᵥ (B *ᵥ w0) - a1 ⬝ᵥ (B *ᵥ w0) = -(am ⬝ᵥ (B *ᵥ wm)) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hc : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ hs
  have hneg : (-(Real.sqrt 2)) * (Real.sqrt 2)⁻¹ = -1 := by
    rw [neg_mul, hc]
  have hBw : B *ᵥ w0 = (Real.sqrt 2)⁻¹ • (B *ᵥ wp + B *ᵥ wm) := by
    rw [hw0, Matrix.mulVec_smul, Matrix.mulVec_add]
  rw [← sub_dotProduct]
  have hdiff : a0 - a1 = (-(Real.sqrt 2)) • am := by
    rw [ham, neg_smul]
  rw [hdiff, smul_dotProduct, hBw, dotProduct_smul, dotProduct_add, hplus, zero_add]
  simp only [smul_eq_mul]
  rw [← mul_assoc, hneg, neg_one_mul]

theorem string_rewriting_entry_reduction {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.IsSymm) (hMsym : ∀ mu : ℝ, (M mu).IsSymm)
    (hM : ∀ mu : ℝ, M mu *ᵥ minusVec = (Real.sqrt 2 * mu) • minusVec)
    (m : ℕ) (a0 a1 w0 : ι × Fin 2 → ℝ) (aM wM : ι → ℝ)
    (ham : a0 - a1 = -(Real.sqrt 2 • tensorMinus aM))
    (hw0 : w0 = (Real.sqrt 2)⁻¹ • (tensorPlus wM + tensorMinus wM)) :
    a0 ⬝ᵥ (((blockLift A M) ^ m) *ᵥ w0)
        - a1 ⬝ᵥ (((blockLift A M) ^ m) *ᵥ w0)
      = -(Real.sqrt 2) ^ m * (aM ⬝ᵥ ((A ^ m) *ᵥ wM)) := by
  have hBsym : ((blockLift A M) ^ m).IsSymm := (blockLift_isSymm A M hA hMsym).pow m
  have hplus : tensorMinus aM ⬝ᵥ (((blockLift A M) ^ m) *ᵥ tensorPlus wM) = 0 := by
    rw [dot_mulVec_comm hBsym]
    exact sign_sim_no_plus_transition A M hM m wM aM
  have h := difference_from_minus_sector ((blockLift A M) ^ m) a0 a1 w0
    (tensorPlus wM) (tensorMinus wM) (tensorMinus aM) ham hw0 hplus
  rw [h, sign_sim_entry A M hM m aM wM, neg_mul]

abbrev ProgramSymbol : Type := Fin 14

abbrev DataSymbol : Type := Fin 4

abbrev AuxSymbol : Type := Fin 2

abbrev SimSymbol : Type := Fin 2

abbrev CellSymbol : Type := ProgramSymbol × DataSymbol × AuxSymbol × SimSymbol

theorem cellDim_eq_224 : Fintype.card CellSymbol = 224 := by
  simp [CellSymbol, ProgramSymbol, DataSymbol, AuxSymbol, SimSymbol,
    Fintype.card_prod, Fintype.card_fin]

theorem cellDim_eq_prod :
    Fintype.card CellSymbol = 14 * 4 * 2 * 2 := by
  rw [cellDim_eq_224]

end Qatlib.Papers.StringRewrite07.MainResults
