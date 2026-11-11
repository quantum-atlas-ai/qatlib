/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Wave functions, phases, and coordinate shears

Defines three-mode complex wave functions, multiplication operators, and substitution operators.
Linear and quadratic shears provide the coordinate changes used to conjugate phase gates, while
phase multiplication identities combine the resulting exponents. See [ArrazolaEtAl2019].

## Main statements

* `conj_mult`: conjugating a multiplication operator pulls back its multiplier.
* `multOp_cexpI_mul`: successive phase operators add their exponents.
* `merge_five`: five phase operators combine into a single multiplier.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonhomogPDE18.WaveModel

/-- The three-element index type for the wave-function modes. -/
abbrev Mode : Type := Fin 3

/-- Complex-valued functions on the real coordinate space of the three modes. -/
abbrev Wave : Type := (Mode → ℝ) → ℂ

/-- The first mode, indexed by zero. -/
def j : Mode := 0
/-- The second mode, indexed by one. -/
def k : Mode := 1
/-- The third mode, indexed by two. -/
def l : Mode := 2

/-- The operator multiplying a wave function pointwise by `g`. -/
def multOp (g : Wave) : Wave → Wave := fun f x => g x * f x

/-- The operator pulling a wave function back along the coordinate map `σ`. -/
def subOp (σ : (Mode → ℝ) → (Mode → ℝ)) : Wave → Wave := fun f => f ∘ σ

/-- Pointwise evaluation of `multOp` is multiplication of the multiplier and input values. -/
@[simp] theorem multOp_apply (g f : Wave) (x : Mode → ℝ) :
    multOp g f x = g x * f x := rfl

/-- Evaluating a substituted wave function at `x` evaluates the original wave function at `σ x`. -/
@[simp] theorem subOp_apply (σ : (Mode → ℝ) → (Mode → ℝ)) (f : Wave) (x : Mode → ℝ) :
    subOp σ f x = f (σ x) := rfl

/-- Composition of substitution operators reverses the order of the coordinate maps. -/
theorem subOp_comp (σ τ : (Mode → ℝ) → (Mode → ℝ)) :
    subOp σ ∘ subOp τ = subOp (τ ∘ σ) := rfl

/-- Pulling back a multiplication operator pulls back its multiplier and then the input wave
function. -/
theorem subOp_multOp (σ : (Mode → ℝ) → (Mode → ℝ)) (g : Wave) :
    subOp σ ∘ multOp g = multOp (g ∘ σ) ∘ subOp σ := by
  funext f x
  simp [multOp, subOp, Function.comp]

/-- Composition of multiplication operators multiplies their multipliers pointwise. -/
theorem multOp_comp (g h : Wave) :
    multOp g ∘ multOp h = multOp (fun x => g x * h x) := by
  funext f x
  simp only [Function.comp_apply, multOp_apply, mul_assoc]

/-- Multiplication operators on wave functions commute. -/
theorem multOp_comm (g h : Wave) : multOp g ∘ multOp h = multOp h ∘ multOp g := by
  funext f x
  simp only [Function.comp_apply, multOp_apply]
  ring

/-- The complex phase function exp(i p(x)) associated with a real-valued exponent `p`. -/
def cexpI (p : (Mode → ℝ) → ℝ) : Wave := fun x => Complex.exp (Complex.I * (p x : ℂ))

/-- Evaluation of `cexpI` is the complex exponential of i times the real exponent. -/
@[simp] theorem cexpI_apply (p : (Mode → ℝ) → ℝ) (x : Mode → ℝ) :
    cexpI p x = Complex.exp (Complex.I * (p x : ℂ)) := rfl

/-- The pointwise product of two complex phase functions is the phase of the sum of their
exponents. -/
theorem cexpI_mul (p q : (Mode → ℝ) → ℝ) :
    (fun x => cexpI p x * cexpI q x) = cexpI (fun x => p x + q x) := by
  funext x
  simp only [cexpI_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The coordinate map replacing `x i` by `x i + x k`. -/
def sh (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i + x k)

/-- The coordinate map replacing `x i` by `x i - x k`. -/
def shInv (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i - x k)

/-- The coordinate map replacing `x i` by `x i + (x k) ^ 2`. -/
def shSq (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i + (x k) ^ 2)

/-- The coordinate map replacing `x i` by `x i - (x k) ^ 2`. -/
def shSqInv (i k : Mode) : (Mode → ℝ) → (Mode → ℝ) :=
  fun x => Function.update x i (x i - (x k) ^ 2)

/-- For distinct modes, the subtractive linear shear is a left inverse of the additive linear
shear. -/
theorem shInv_comp_sh {i m : Mode} (h : i ≠ m) :
    shInv i m ∘ sh i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [sh, shInv, Function.update_of_ne (Ne.symm h)]
  · simp [sh, shInv, Function.update_of_ne hq]

/-- For distinct modes, the additive linear shear is a left inverse of the subtractive linear
shear. -/
theorem sh_comp_shInv {i m : Mode} (h : i ≠ m) :
    sh i m ∘ shInv i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [sh, shInv, Function.update_of_ne (Ne.symm h)]
  · simp [sh, shInv, Function.update_of_ne hq]

/-- For distinct modes, the subtractive quadratic shear is a left inverse of the additive
quadratic shear. -/
theorem shSqInv_comp_shSq {i m : Mode} (h : i ≠ m) :
    shSqInv i m ∘ shSq i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [shSq, shSqInv, Function.update_of_ne (Ne.symm h)]
  · simp [shSq, shSqInv, Function.update_of_ne hq]

/-- For distinct modes, the additive quadratic shear is a left inverse of the subtractive
quadratic shear. -/
theorem shSq_comp_shSqInv {i m : Mode} (h : i ≠ m) :
    shSq i m ∘ shSqInv i m = id := by
  funext x q
  by_cases hq : q = i
  · subst hq
    simp [shSq, shSqInv, Function.update_of_ne (Ne.symm h)]
  · simp [shSq, shSqInv, Function.update_of_ne hq]

/-- For distinct modes, `subOp (shInv i m) ∘ subOp (sh i m)` is the identity wave operator. -/
theorem subOp_shInv_sh {i m : Mode} (h : i ≠ m) :
    subOp (shInv i m) ∘ subOp (sh i m) = id := by
  rw [subOp_comp, sh_comp_shInv h]
  rfl

/-- For distinct modes, `subOp (shSqInv i m) ∘ subOp (shSq i m)` is the identity wave operator. -/
theorem subOp_shSqInv_shSq {i m : Mode} (h : i ≠ m) :
    subOp (shSqInv i m) ∘ subOp (shSq i m) = id := by
  rw [subOp_comp, shSq_comp_shSqInv h]
  rfl

/-- Substitution by the identity coordinate map is the identity wave operator. -/
theorem subOp_id : subOp id = id := rfl

/-- At its target mode, a linear shear adds the control coordinate. -/
theorem sh_apply_self {i m : Mode} (_h : i ≠ m) (x : Mode → ℝ) :
    sh i m x i = x i + x m := by
  simp [sh]

/-- A linear shear leaves every coordinate other than its target unchanged. -/
theorem sh_apply_ne {i m q : Mode} (hq : q ≠ i) (x : Mode → ℝ) :
    sh i m x q = x q := by
  simp [sh, hq]

/-- At its target mode, a quadratic shear adds the square of the control coordinate. -/
theorem shSq_apply_self {i m : Mode} (_h : i ≠ m) (x : Mode → ℝ) :
    shSq i m x i = x i + (x m) ^ 2 := by
  simp [shSq]

/-- A quadratic shear leaves every coordinate other than its target unchanged. -/
theorem shSq_apply_ne {i m q : Mode} (hq : q ≠ i) (x : Mode → ℝ) :
    shSq i m x q = x q := by
  simp [shSq, hq]

/-- If `τ ∘ σ` is the identity, conjugating multiplication by substitution along these maps
gives multiplication by `g ∘ σ`. -/
theorem conj_mult {σ τ : (Mode → ℝ) → (Mode → ℝ)} {g : Wave} (h : τ ∘ σ = id) :
    subOp σ ∘ (multOp g ∘ subOp τ) = multOp (g ∘ σ) := by
  funext f x
  show g (σ x) * f (τ (σ x)) = (g ∘ σ) x * f x
  rw [show τ (σ x) = x by simpa [Function.comp] using congrFun h x]
  rfl

/-- Pulling back a complex phase function pulls back its real exponent. -/
theorem cexpI_comp (p : (Mode → ℝ) → ℝ) (σ : (Mode → ℝ) → (Mode → ℝ)) :
    cexpI p ∘ σ = cexpI (p ∘ σ) := rfl

/-- If the pullback of exponent `p` along `σ` equals `q` pointwise, the corresponding
pulled-back phases agree. -/
theorem cexpI_comp_congr (σ : (Mode → ℝ) → (Mode → ℝ)) {p q : (Mode → ℝ) → ℝ}
    (h : ∀ x, p (σ x) = q x) : cexpI p ∘ σ = cexpI q := by
  funext x
  simp only [Function.comp_apply, cexpI_apply, h x]

/-- Composition of two phase multiplication operators adds their real exponents. -/
theorem multOp_cexpI_mul (p q : (Mode → ℝ) → ℝ) :
    multOp (cexpI p) ∘ multOp (cexpI q)
      = multOp (cexpI (fun x => p x + q x)) := by
  rw [multOp_comp]
  congr 1
  exact cexpI_mul p q

/-- Three successive phase multiplication operators combine into the phase of the sum of their
exponents. -/
theorem merge_three (a b c : (Mode → ℝ) → ℝ) :
    multOp (cexpI a) ∘ (multOp (cexpI b) ∘ multOp (cexpI c))
      = multOp (cexpI (fun x => a x + b x + c x)) := by
  rw [multOp_cexpI_mul, multOp_cexpI_mul]
  congr 1
  funext x
  ring

/-- Five successive phase multiplication operators combine into the phase of the sum of their
exponents. -/
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
