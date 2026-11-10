/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonhomogPDE18.WaveModel

abbrev Mode : Type := Fin 3

abbrev Wave : Type := (Mode → ℝ) → ℂ

def j : Mode := 0
def k : Mode := 1
def l : Mode := 2

def multOp (g : Wave) : Wave → Wave := fun f x => g x * f x

def subOp (σ : (Mode → ℝ) → (Mode → ℝ)) : Wave → Wave := fun f => f ∘ σ

@[simp] theorem multOp_apply (g f : Wave) (x : Mode → ℝ) :
    multOp g f x = g x * f x := rfl

@[simp] theorem subOp_apply (σ : (Mode → ℝ) → (Mode → ℝ)) (f : Wave) (x : Mode → ℝ) :
    subOp σ f x = f (σ x) := rfl

theorem subOp_comp (σ τ : (Mode → ℝ) → (Mode → ℝ)) :
    subOp σ ∘ subOp τ = subOp (τ ∘ σ) := rfl

theorem subOp_multOp (σ : (Mode → ℝ) → (Mode → ℝ)) (g : Wave) :
    subOp σ ∘ multOp g = multOp (g ∘ σ) ∘ subOp σ := by
  funext f x
  simp [multOp, subOp, Function.comp]

theorem multOp_comp (g h : Wave) :
    multOp g ∘ multOp h = multOp (fun x => g x * h x) := by
  funext f x
  simp only [Function.comp_apply, multOp_apply, mul_assoc]

theorem multOp_comm (g h : Wave) : multOp g ∘ multOp h = multOp h ∘ multOp g := by
  funext f x
  simp only [Function.comp_apply, multOp_apply]
  ring

def cexpI (p : (Mode → ℝ) → ℝ) : Wave := fun x => Complex.exp (Complex.I * (p x : ℂ))

@[simp] theorem cexpI_apply (p : (Mode → ℝ) → ℝ) (x : Mode → ℝ) :
    cexpI p x = Complex.exp (Complex.I * (p x : ℂ)) := rfl

theorem cexpI_mul (p q : (Mode → ℝ) → ℝ) :
    (fun x => cexpI p x * cexpI q x) = cexpI (fun x => p x + q x) := by
  funext x
  simp only [cexpI_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

def sh (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i + x k)

def shInv (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i - x k)

def shSq (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i + (x k) ^ 2)

def shSqInv (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i - (x k) ^ 2)

theorem shInv_comp_sh {i m : Mode} (h : i ≠ m) :
    shInv i m ∘ sh i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [sh, shInv, Function.update_of_ne (Ne.symm h)]
  · simp [sh, shInv, Function.update_of_ne hq]

theorem sh_comp_shInv {i m : Mode} (h : i ≠ m) :
    sh i m ∘ shInv i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [sh, shInv, Function.update_of_ne (Ne.symm h)]
  · simp [sh, shInv, Function.update_of_ne hq]

theorem shSqInv_comp_shSq {i m : Mode} (h : i ≠ m) :
    shSqInv i m ∘ shSq i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [shSq, shSqInv, Function.update_of_ne (Ne.symm h)]
  · simp [shSq, shSqInv, Function.update_of_ne hq]

theorem shSq_comp_shSqInv {i m : Mode} (h : i ≠ m) :
    shSq i m ∘ shSqInv i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [shSq, shSqInv, Function.update_of_ne (Ne.symm h)]
  · simp [shSq, shSqInv, Function.update_of_ne hq]

theorem subOp_shInv_sh {i m : Mode} (h : i ≠ m) :
    subOp (shInv i m) ∘ subOp (sh i m) = id := by
  rw [subOp_comp, sh_comp_shInv h]
  rfl

theorem subOp_shSqInv_shSq {i m : Mode} (h : i ≠ m) :
    subOp (shSqInv i m) ∘ subOp (shSq i m) = id := by
  rw [subOp_comp, shSq_comp_shSqInv h]
  rfl

theorem subOp_id : subOp id = id := rfl

theorem sh_apply_self {i m : Mode} (_h : i ≠ m) (x : Mode → ℝ) :
    sh i m x i = x i + x m := by
  simp [sh]

theorem sh_apply_ne {i m q : Mode} (hq : q ≠ i) (x : Mode → ℝ) :
    sh i m x q = x q := by
  simp [sh, hq]

theorem shSq_apply_self {i m : Mode} (_h : i ≠ m) (x : Mode → ℝ) :
    shSq i m x i = x i + (x m) ^ 2 := by
  simp [shSq]

theorem shSq_apply_ne {i m q : Mode} (hq : q ≠ i) (x : Mode → ℝ) :
    shSq i m x q = x q := by
  simp [shSq, hq]

theorem conj_mult {σ τ : (Mode → ℝ) → (Mode → ℝ)} {g : Wave} (h : τ ∘ σ = id) :
    subOp σ ∘ (multOp g ∘ subOp τ) = multOp (g ∘ σ) := by
  funext f x
  show g (σ x) * f (τ (σ x)) = (g ∘ σ) x * f x
  rw [show τ (σ x) = x by simpa [Function.comp] using congrFun h x]
  rfl

theorem cexpI_comp (p : (Mode → ℝ) → ℝ) (σ : (Mode → ℝ) → (Mode → ℝ)) :
    cexpI p ∘ σ = cexpI (p ∘ σ) := rfl

theorem cexpI_comp_congr (σ : (Mode → ℝ) → (Mode → ℝ)) {p q : (Mode → ℝ) → ℝ}
    (h : ∀ x, p (σ x) = q x) : cexpI p ∘ σ = cexpI q := by
  funext x
  simp only [Function.comp_apply, cexpI_apply, h x]

theorem multOp_cexpI_mul (p q : (Mode → ℝ) → ℝ) :
    multOp (cexpI p) ∘ multOp (cexpI q)
      = multOp (cexpI (fun x => p x + q x)) := by
  rw [multOp_comp]
  congr 1
  exact cexpI_mul p q

theorem merge_three (a b c : (Mode → ℝ) → ℝ) :
    multOp (cexpI a) ∘ (multOp (cexpI b) ∘ multOp (cexpI c))
      = multOp (cexpI (fun x => a x + b x + c x)) := by
  rw [multOp_cexpI_mul, multOp_cexpI_mul]
  congr 1
  funext x
  ring

theorem merge_five (a b c d e : (Mode → ℝ) → ℝ) :
    multOp (cexpI a) ∘
        (multOp (cexpI b) ∘
          (multOp (cexpI c) ∘ (multOp (cexpI d) ∘ multOp (cexpI e))))
      = multOp (cexpI (fun x => a x + b x + c x + d x + e x)) := by
  rw [multOp_cexpI_mul, multOp_cexpI_mul, multOp_cexpI_mul, multOp_cexpI_mul]
  congr 1
  funext x
  ring

end Qatlib.Papers.NonhomogPDE18.WaveModel
