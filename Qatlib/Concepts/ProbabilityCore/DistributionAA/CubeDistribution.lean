/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs

namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

def cubeExpect (n : ℕ) (w : (Fin n → Bool) → ℝ) (g : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ x : Fin n → Bool, w x * g x

def CubeWeight (n : ℕ) (w : (Fin n → Bool) → ℝ) : Prop :=
  (∀ x : Fin n → Bool, 0 ≤ w x) ∧ ∑ x : Fin n → Bool, w x = 1

def muWeight (p : ℝ) (n : ℕ) : (Fin n → Bool) → ℝ :=
  fun x => ∏ i : Fin n, (if x i then p else 1 - p)

def cubeHamming {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

noncomputable def sliceWeight (n k : ℕ) : (Fin n → Bool) → ℝ :=
  fun x =>
    if cubeHamming x = k then
      ((Finset.univ.filter (fun y : Fin n → Bool => cubeHamming y = k)).card : ℝ)⁻¹
    else 0

noncomputable def nuWeight (p : ℝ) (n : ℕ) : (Fin n → Bool) → ℝ :=
  sliceWeight n (Nat.floor (p * n))

def cubeFlip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !x j else x j

def cubeSwap {n : ℕ} (x : Fin n → Bool) (i j : Fin n) : Fin n → Bool :=
  fun k => if k = i then x j else if k = j then x i else x k

def cubeVar (n : ℕ) (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  cubeExpect n w (fun x => (f x - cubeExpect n w f) ^ 2)

def cubeInf (n : ℕ) (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  cubeExpect n w (fun x => (f x - f (cubeFlip x i)) ^ 2)

def cubeTotalInf (n : ℕ) (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ i : Fin n, cubeInf n w f i

def CubeDegreeLE {n : ℕ} (d : ℕ) (f : (Fin n → Bool) → ℝ) : Prop :=
  ∃ c : Finset (Fin n) → ℝ,
    (∀ S : Finset (Fin n), d < S.card → c S = 0) ∧
    ∀ x : Fin n → Bool,
      f x = ∑ S : Finset (Fin n), c S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)

def CubeFamily : Type := (n : ℕ) → ((Fin n → Bool) → ℝ)

def muFamily (p : ℝ) : CubeFamily :=
  fun n => muWeight p n

noncomputable def nuFamily (p : ℝ) : CubeFamily :=
  fun n => nuWeight p n

def AAWith (Λ : CubeFamily) (S : ℝ → ℕ → ℝ) : Prop :=
  ∀ n d : ℕ, ∀ v : ℝ, 0 < v → v ≤ 1 / 4 →
    ∀ f : (Fin n → Bool) → ℝ, (∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) → CubeDegreeLE d f →
      v ≤ cubeVar n (Λ n) f → ∃ i : Fin n, S v d ≤ cubeInf n (Λ n) f i

def AAHolds (Λ : CubeFamily) : Prop :=
  ∃ c : ℝ, ∃ C : ℕ, 0 < c ∧ AAWith Λ (fun v d => c * (v / (d : ℝ)) ^ C)

noncomputable def biasGadgetSize (a : ℝ) (D : ℕ) (v : ℝ) (d : ℕ) : ℕ :=
  Nat.ceil ((4 * (D : ℝ) / a) * Real.logb 2 ((d : ℝ) / v))

noncomputable def biasTransferS (S : ℝ → ℕ → ℝ) (a : ℝ) (D : ℕ) : ℝ → ℕ → ℝ :=
  fun v d => S (v / 2) (d * biasGadgetSize a D v d) - (v / (d : ℝ)) ^ D

noncomputable def sliceTransferS (S : ℝ → ℕ → ℝ) : ℝ → ℕ → ℝ :=
  fun v d => min (v ^ 5) (v * S (v / 2) d ^ 4) / (10 ^ 9 * (d : ℝ) ^ 8)

open scoped Classical BigOperators

theorem muWeight_cubeWeight {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) :
    CubeWeight n (muWeight p n) := by
  constructor
  · intro x
    apply Finset.prod_nonneg
    intro i _
    split_ifs <;> linarith
  · unfold muWeight
    calc
      _ = ∏ i : Fin n, ∑ b : Bool, (if b then p else 1-p) :=
        (Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then p else 1-p)).symm
      _ = 1 := by simp

theorem sliceWeight_cubeWeight (n k : ℕ) (hk : k ≤ n) : CubeWeight n (sliceWeight n k) := by
  let S := Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x = k)
  let x : Fin n → Bool := fun i => decide ((i : ℕ) < k)
  have hx : cubeHamming x = k := by
    simp only [cubeHamming, x, decide_eq_true_eq]
    rw [Fin.card_filter_val_lt, min_eq_right hk]
  have hS : 0 < S.card := Finset.card_pos.2 ⟨x, by simp [S, hx]⟩
  constructor
  · intro y
    unfold sliceWeight
    split_ifs <;> positivity
  · change (∑ y, if cubeHamming y = k then (S.card : ℝ)⁻¹ else 0) = 1
    rw [← Finset.sum_filter]
    change (∑ _y ∈ S, (S.card : ℝ)⁻¹) = 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hS.ne')

theorem nuWeight_cubeWeight {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (n : ℕ) :
    CubeWeight n (nuWeight p n) := by
  apply sliceWeight_cubeWeight
  have hf := Nat.floor_le (show 0 ≤ p*(n : ℝ) by positivity)
  have hp := mul_le_mul_of_nonneg_right h1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [one_mul] at hp
  exact_mod_cast hf.trans hp

theorem cubeInf_nonneg (n : ℕ) {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) (i : Fin n) : 0 ≤ cubeInf n w f i := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (sq_nonneg _)

theorem cubeVar_nonneg (n : ℕ) {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) : 0 ≤ cubeVar n w f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (sq_nonneg _)

theorem cube_var_eq_second_moment_sub_sq (n : ℕ) {w : (Fin n → Bool) → ℝ}
    (hw : CubeWeight n w) (f : (Fin n → Bool) → ℝ) :
    cubeVar n w f = cubeExpect n w (fun x => f x ^ 2)-(cubeExpect n w f)^2 := by
  let m := cubeExpect n w f
  have he (x : Fin n → Bool) : w x*(f x-m)^2 = w x*f x^2-2*m*(w x*f x)+m^2*w x := by ring
  change (∑ x, w x*(f x-m)^2) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw.2]
  change cubeExpect n w (fun x => f x^2)-2*m*m+m^2*1 = _
  dsimp [m]
  ring

theorem cubeVar_le_one_quarter (n : ℕ) {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    {f : (Fin n → Bool) → ℝ} (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) :
    cubeVar n w f ≤ 1/4 := by
  have hm : cubeExpect n w (fun x => f x^2) ≤ cubeExpect n w f := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hw.1 x)
    nlinarith [(hb x).1, (hb x).2]
  rw [cube_var_eq_second_moment_sub_sq n hw f]
  nlinarith only [hm, sq_nonneg (cubeExpect n w f-1/2)]

end Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
noncomputable section

theorem cube_expect_add (n : ℕ) (w : (Fin n → Bool) → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => f x+g x) = cubeExpect n w f+cubeExpect n w g := by
  simp [cubeExpect, mul_add, Finset.sum_add_distrib]
end
noncomputable section

theorem cube_expect_const_mul (n : ℕ) (w : (Fin n → Bool) → ℝ) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => c*f x) = c*cubeExpect n w f := by
  unfold cubeExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
end
noncomputable section

theorem cube_expect_sub (n : ℕ) (w : (Fin n → Bool) → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => f x-g x) = cubeExpect n w f-cubeExpect n w g := by
  simp [cubeExpect, mul_sub, Finset.sum_sub_distrib]
end
noncomputable section

theorem cube_expect_abs_le {n : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : |cubeExpect n w f| ≤ C := by
  unfold cubeExpect
  calc
    _ ≤ ∑ x, |w x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x*|f x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hw.1 x)]
    _ ≤ ∑ x, w x*C := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (hw.1 x)
    _ = C := by rw [← Finset.sum_mul, hw.2, one_mul]
end
noncomputable section

theorem cube_expect_sum {ι : Type} [Fintype ι] (n : ℕ) (w : (Fin n → Bool) → ℝ)
    (f : ι → (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => ∑ i, f i x) = ∑ i, cubeExpect n w (f i) := by
  unfold cubeExpect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
end
end Qatlib.Concepts.ProbabilityCore.DistributionAA
