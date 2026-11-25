/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaScalars

/-!
# The Rañada density, chart transitions and the global Hopf electromagnetic fields

[IrvineBouwmeester2008KnottedLight], equation (2), p. 717,
[DOI](https://doi.org/10.1038/nphys1056).
For a complex scalar `w` with spatial gradient data `dw`, the paper's field
pattern is the stereographic density `(1/(4πi)) (∇w × ∇w̄) / (1 + w w̄)^2`.

This module proves the two chart-transition laws for that density:
holomorphic reciprocation `w ↦ 1/w` produces *the same* density (the
orientation is preserved, which is what makes the field regular at the poles
of the scalar), while conjugated reciprocation `w ↦ 1/w̄` reverses its
orientation. Both are proved for arbitrary gradient data, so they apply to
every chart change of the construction.

The magnetic scalar `eta` and the electric scalar `zeta` of
`Qatlib.Papers.KnottedLight08.HopfField.RanadaScalars` are then used to
define electromagnetic fields on all of spacetime by the homogeneous formula
`(1/(4πi)) (b ∇a − a ∇b) × (b̄ ∇ā − ā ∇b̄) / (|a|² + |b|²)²`, whose denominator
never vanishes because the quaternionic coordinate never vanishes. The
gradients of all four complex letter pairs are computed explicitly and
certified by `HasDerivAt` lemmas; the homogeneous fields are proved to agree
with the printed density formula wherever the respective scalar is finite,
and with the same density in the reciprocal chart around genuine poles — the
smooth-gluing mechanism of the construction. Both fields take real values
everywhere; their exact values at the spacetime origin are
`B = (−2/π, 0, 0)` and `E = (0, 2/π, 0)`.

Vacuum Maxwell equations, spatial decay, energy integrals and linking remain
outside this module. The cross product is `Qatlib.Papers.KnottedLight08.HopfField.cross3`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.HopfField (cross3)
open scoped ComplexConjugate

/-! ### Conjugation helpers -/

/-- Conjugation is additive. -/
theorem conj_add' (a b : ℂ) : conj (a + b) = conj a + conj b := map_add _ _ _

/-- Conjugation is multiplicative. -/
theorem conj_mul' (a b : ℂ) : conj (a * b) = conj a * conj b := map_mul _ _ _

/-- Conjugation negates. -/
theorem conj_neg' (a : ℂ) : conj (-a) = -(conj a) := map_neg _ _

/-- Conjugation subtracts. -/
theorem conj_sub' (a b : ℂ) : conj (a - b) = conj a - conj b := map_sub _ _ _

/-- Conjugation divides. -/
theorem conj_div' (a b : ℂ) : conj (a / b) = conj a / conj b := by
  rw [div_eq_inv_mul, map_mul, map_inv₀, div_eq_inv_mul]

/-- Conjugation commutes with powers. -/
theorem conj_pow' (a : ℂ) (n : ℕ) : conj (a ^ n) = (conj a) ^ n := map_pow _ _ _

/-- A nonzero number has nonzero conjugate. -/
theorem conj_ne_zero' {w : ℂ} (hw : w ≠ 0) : conj w ≠ 0 := by
  intro h
  apply hw
  have h2 : conj (conj w) = conj 0 := by rw [h]
  rw [Complex.conj_conj, map_zero] at h2
  exact h2

/-- The conjugate of the printed prefactor is its negative. -/
theorem conj_prefactor :
    conj (1 / (4 * Real.pi * Complex.I)) = -(1 / (4 * Real.pi * Complex.I)) := by
  simp only [conj_div', conj_mul', map_one, Complex.conj_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  rw [mul_neg, div_neg]

/-- The squared modulus of a real-plus-imaginary pair. -/
theorem ofReal_add_iMul_normSq (p s : ℝ) :
    ((p : ℂ) + Complex.I * (s : ℂ)) * conj ((p : ℂ) + Complex.I * (s : ℂ)) =
      (p : ℂ) ^ 2 + (s : ℂ) ^ 2 := by
  simp only [conj_add', conj_mul', Complex.conj_ofReal, Complex.conj_I]
  linear_combination (-(s : ℂ) ^ 2) * Complex.I_mul_I

/-! ### The abstract stereographic density and its chart transitions -/

/-- The equation (2) field pattern of a complex scalar with gradient data
`dw`: the `(1/(4πi))`-normalized cross product of the gradient with its
conjugate, divided by the squared stereographic denominator. -/
noncomputable def density (w : ℂ) (dw : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun j => (1 / (4 * Real.pi * Complex.I)) *
    (cross3 dw (fun k => conj (dw k)) j) / (1 + w * conj w) ^ 2

/-- Scaling both factors of the cross product scales the result. -/
theorem cross3_smul_smul (c d : ℂ) (u v : Fin 3 → ℂ) :
    cross3 (fun j => c * u j) (fun j => d * v j) = fun j => (c * d) * cross3 u v j := by
  funext j
  fin_cases j <;> simp [cross3] <;> try ring

/-- Dividing both factors of the cross product divides the result. -/
theorem cross3_div_div (u v : Fin 3 → ℂ) (c d : ℂ) :
    cross3 (fun j => u j / c) (fun j => v j / d) = fun j => cross3 u v j / (c * d) := by
  funext j
  fin_cases j <;> simp [cross3, div_eq_mul_inv] <;> try ring

/-- Negating both factors preserves the cross product. -/
theorem cross3_neg_neg (u v : Fin 3 → ℂ) :
    cross3 (fun j => -u j) (fun j => -v j) = cross3 u v := by
  funext j
  fin_cases j <;> simp [cross3]

/-- Swapping the factors negates the cross product. -/
theorem cross3_swap (u v : Fin 3 → ℂ) :
    cross3 v u = fun j => -(cross3 u v j) := by
  funext j
  fin_cases j <;> simp [cross3] <;> try ring

/-- The cross product of a vector with its conjugate is purely imaginary. -/
theorem cross3_add_conj_self_eq_zero (u : Fin 3 → ℂ) (j : Fin 3) :
    cross3 u (fun k => conj (u k)) j +
      conj (cross3 u (fun k => conj (u k)) j) = 0 := by
  fin_cases j <;> simp [cross3] <;> try ring

/-- The real denominator of the density is fixed by conjugation. -/
theorem conj_one_add (w : ℂ) : conj (1 + w * conj w) = 1 + w * conj w := by
  rw [conj_add', map_one, conj_mul', Complex.conj_conj]
  ring

/-- Holomorphic reciprocation `w ↦ 1/w` preserves the density: the chart
change at a pole leaves the field pattern unchanged. -/
theorem density_recip (w : ℂ) (dw : Fin 3 → ℂ) (hw : w ≠ 0) :
    density (1 / w) (fun j => -(dw j) / w ^ 2) = density w dw := by
  have hcw : conj w ≠ 0 := conj_ne_zero' hw
  have hprod : w * conj w ≠ 0 := mul_ne_zero hw hcw
  have hconjw : conj (1 / w) = 1 / conj w := by
    rw [conj_div', map_one]
  have hconjgrad : (fun k => conj (-(dw k) / w ^ 2))
      = fun k => -(conj (dw k)) / (conj w) ^ 2 := by
    funext k
    simp only [conj_div', conj_neg', conj_pow']
  funext j
  show (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (fun k => -(dw k) / w ^ 2) (fun k => conj (-(dw k) / w ^ 2)) j) /
      (1 + (1 / w) * (conj (1 / w))) ^ 2 =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 dw (fun k => conj (dw k)) j) / (1 + w * conj w) ^ 2
  rw [hconjw, hconjgrad, cross3_div_div, cross3_neg_neg]
  field_simp [hw, hcw, hprod]
  ring

/-- Conjugated reciprocation `w ↦ 1/w̄` reverses the orientation of the
density. -/
theorem density_conjRecip (w : ℂ) (dw : Fin 3 → ℂ) (hw : w ≠ 0) :
    density ((conj w)⁻¹) (fun j => -(conj (dw j)) / (conj w) ^ 2) =
      fun j => -density w dw j := by
  have hcw : conj w ≠ 0 := conj_ne_zero' hw
  have hprod : w * conj w ≠ 0 := mul_ne_zero hw hcw
  have hconjw : conj ((conj w)⁻¹) = w ⁻¹ := by
    rw [map_inv₀, Complex.conj_conj]
  have hconjgrad : (fun k => conj (-(conj (dw k)) / (conj w) ^ 2))
      = fun k => -(dw k) / w ^ 2 := by
    funext k
    simp only [conj_div', conj_neg', conj_pow', Complex.conj_conj]
  funext j
  show (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (fun k => -(conj (dw k)) / (conj w) ^ 2)
        (fun k => conj (-(conj (dw k)) / (conj w) ^ 2)) j) /
      (1 + (conj w)⁻¹ * (conj ((conj w)⁻¹))) ^ 2 =
    -((1 / (4 * Real.pi * Complex.I)) *
      (cross3 dw (fun k => conj (dw k)) j) / (1 + w * conj w) ^ 2)
  rw [hconjw, hconjgrad, cross3_div_div, cross3_swap, cross3_neg_neg]
  field_simp [hw, hcw, hprod]
  ring

/-- The density takes real values for arbitrary scalar and gradient data. -/
theorem density_re (w : ℂ) (dw : Fin 3 → ℂ) (j : Fin 3) :
    conj (density w dw j) = density w dw j := by
  have hc := cross3_add_conj_self_eq_zero dw j
  have hd : conj ((1 + w * conj w) ^ 2) = (1 + w * conj w) ^ 2 := by
    rw [conj_pow', conj_one_add]
  have h2 : conj (cross3 dw (fun k => conj (dw k)) j) =
      -(cross3 dw (fun k => conj (dw k)) j) := by linear_combination hc
  show conj ((1 / (4 * Real.pi * Complex.I)) *
      (cross3 dw (fun k => conj (dw k)) j) / (1 + w * conj w) ^ 2) =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 dw (fun k => conj (dw k)) j) / (1 + w * conj w) ^ 2
  rw [conj_div', conj_mul', conj_prefactor, h2, hd]
  ring

/-- The imaginary part of the density vanishes. -/
theorem density_im (w : ℂ) (dw : Fin 3 → ℂ) (j : Fin 3) :
    (density w dw j).im = 0 := by
  have h := congrArg Complex.im (density_re w dw j)
  simp only [Complex.conj_im] at h
  linarith

/-! ### The complex letter pairs of the two scalars -/

/-- The numerator `Q + iR` of the printed magnetic scalar. -/
noncomputable def etaNum (x y z t : ℝ) : ℂ :=
  (ranadaQ x y z t : ℂ) + Complex.I * (ranadaR x y z t : ℂ)

/-- The denominator `P + iS` of the printed magnetic scalar. -/
noncomputable def etaDen (x y z t : ℝ) : ℂ :=
  (ranadaP x y z t : ℂ) + Complex.I * (ranadaS x y z t : ℂ)

/-- The numerator `P + iQ` of the printed electric scalar. -/
noncomputable def zetaNum (x y z t : ℝ) : ℂ :=
  (ranadaP x y z t : ℂ) + Complex.I * (ranadaQ x y z t : ℂ)

/-- The denominator `R + iS` of the printed electric scalar. -/
noncomputable def zetaDen (x y z t : ℝ) : ℂ :=
  (ranadaR x y z t : ℂ) + Complex.I * (ranadaS x y z t : ℂ)

/-- The magnetic scalar is the ratio of its letter pair. -/
theorem ranadaEta_def (x y z t : ℝ) :
    ranadaEta x y z t = etaNum x y z t / etaDen x y z t := rfl

/-- The electric scalar is the ratio of its letter pair. -/
theorem ranadaZeta_def (x y z t : ℝ) :
    ranadaZeta x y z t = zetaNum x y z t / zetaDen x y z t := rfl

/-- The squared moduli of the magnetic letter pair sum to the real
quaternionic norm. -/
theorem etaPairNormSq (x y z t : ℝ) :
    etaNum x y z t * conj (etaNum x y z t) +
      etaDen x y z t * conj (etaDen x y z t) =
    ((ranadaP x y z t ^ 2 + ranadaQ x y z t ^ 2 + ranadaR x y z t ^ 2 +
      ranadaS x y z t ^ 2 : ℝ) : ℂ) := by
  have h1 : etaNum x y z t * conj (etaNum x y z t) =
      ((ranadaQ x y z t : ℂ)) ^ 2 + ((ranadaR x y z t : ℂ)) ^ 2 :=
    ofReal_add_iMul_normSq _ _
  have h2 : etaDen x y z t * conj (etaDen x y z t) =
      ((ranadaP x y z t : ℂ)) ^ 2 + ((ranadaS x y z t : ℂ)) ^ 2 :=
    ofReal_add_iMul_normSq _ _
  rw [h1, h2]
  push_cast
  ring

/-- The electric pair shares the same total squared modulus. -/
theorem zetaPairNormSq (x y z t : ℝ) :
    zetaNum x y z t * conj (zetaNum x y z t) +
      zetaDen x y z t * conj (zetaDen x y z t) =
    ((ranadaP x y z t ^ 2 + ranadaQ x y z t ^ 2 + ranadaR x y z t ^ 2 +
      ranadaS x y z t ^ 2 : ℝ) : ℂ) := by
  have h1 : zetaNum x y z t * conj (zetaNum x y z t) =
      ((ranadaP x y z t : ℂ)) ^ 2 + ((ranadaQ x y z t : ℂ)) ^ 2 :=
    ofReal_add_iMul_normSq _ _
  have h2 : zetaDen x y z t * conj (zetaDen x y z t) =
      ((ranadaR x y z t : ℂ)) ^ 2 + ((ranadaS x y z t : ℂ)) ^ 2 :=
    ofReal_add_iMul_normSq _ _
  rw [h1, h2]
  push_cast
  ring

/-! ### Certified derivatives of the letters -/

/-- The `A` letter is its own coordinate derivative in `x`. -/
theorem hasDerivAt_ranadaA_x (y z t x : ℝ) :
    HasDerivAt (fun s => ranadaA s y z t) x x := by
  have h1 : HasDerivAt (fun s => s ^ 2) (2 * x) x :=
    hasDerivAt_pow 2 x |>.congr_deriv (by norm_num)
  have h5' : HasDerivAt (fun s => s ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 + 1) (2 * x) x :=
    (HasDerivAt.fun_add (HasDerivAt.sub (HasDerivAt.fun_add
      (HasDerivAt.fun_add h1 (hasDerivAt_const x (y ^ 2))) (hasDerivAt_const x (z ^ 2)))
      (hasDerivAt_const x (t ^ 2))) (hasDerivAt_const x (1 : ℝ))).congr_deriv (by ring)
  simp only [ranadaA]
  exact HasDerivAt.div_const
    (h5'.congr_of_eventuallyEq (Eq.eventuallyEq (by funext s; ring))) 2 |>.congr_deriv
      (by ring)

/-- The `A` letter is its own coordinate derivative in `y`. -/
theorem hasDerivAt_ranadaA_y (x z t y : ℝ) :
    HasDerivAt (fun s => ranadaA x s z t) y y := by
  have h1 : HasDerivAt (fun s => s ^ 2) (2 * y) y :=
    hasDerivAt_pow 2 y |>.congr_deriv (by norm_num)
  have h5' : HasDerivAt (fun s => x ^ 2 + s ^ 2 + z ^ 2 - t ^ 2 + 1) (2 * y) y :=
    (HasDerivAt.fun_add (HasDerivAt.sub (HasDerivAt.fun_add
      (HasDerivAt.fun_add (hasDerivAt_const y (x ^ 2)) h1) (hasDerivAt_const y (z ^ 2)))
      (hasDerivAt_const y (t ^ 2))) (hasDerivAt_const y (1 : ℝ))).congr_deriv (by ring)
  simp only [ranadaA]
  exact HasDerivAt.div_const
    (h5'.congr_of_eventuallyEq (Eq.eventuallyEq (by funext s; ring))) 2 |>.congr_deriv
      (by ring)

/-- The `A` letter is its own coordinate derivative in `z`. -/
theorem hasDerivAt_ranadaA_z (x y t z : ℝ) :
    HasDerivAt (fun s => ranadaA x y s t) z z := by
  have h1 : HasDerivAt (fun s => s ^ 2) (2 * z) z :=
    hasDerivAt_pow 2 z |>.congr_deriv (by norm_num)
  have h5' : HasDerivAt (fun s => x ^ 2 + y ^ 2 + s ^ 2 - t ^ 2 + 1) (2 * z) z :=
    (HasDerivAt.fun_add (HasDerivAt.sub (HasDerivAt.fun_add
      (HasDerivAt.fun_add (hasDerivAt_const z (x ^ 2)) (hasDerivAt_const z (y ^ 2))) h1)
      (hasDerivAt_const z (t ^ 2))) (hasDerivAt_const z (1 : ℝ))).congr_deriv (by ring)
  simp only [ranadaA]
  exact HasDerivAt.div_const
    (h5'.congr_of_eventuallyEq (Eq.eventuallyEq (by funext s; ring))) 2 |>.congr_deriv
      (by ring)

/-- The `t`-derivative of the `A` letter is minus `t`. -/
theorem hasDerivAt_ranadaA_t (x y z t : ℝ) :
    HasDerivAt (fun s => ranadaA x y z s) (-t) t := by
  have h1 : HasDerivAt (fun s => s ^ 2) (2 * t) t :=
    hasDerivAt_pow 2 t |>.congr_deriv (by norm_num)
  have h5' : HasDerivAt (fun s => x ^ 2 + y ^ 2 + z ^ 2 - s ^ 2 + 1) (-2 * t) t :=
    (HasDerivAt.fun_add (HasDerivAt.sub (HasDerivAt.fun_add
      (HasDerivAt.fun_add (hasDerivAt_const t (x ^ 2)) (hasDerivAt_const t (y ^ 2)))
      (hasDerivAt_const t (z ^ 2))) h1) (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  simp only [ranadaA]
  exact HasDerivAt.div_const
    (h5'.congr_of_eventuallyEq (Eq.eventuallyEq (by funext s; ring))) 2 |>.congr_deriv
      (by ring)

/-- The `P` letter partial derivatives are as printed. -/
theorem hasDerivAt_ranadaP_x (y z t x : ℝ) :
    HasDerivAt (fun s => ranadaP s y z t) (x * x + ranadaA x y z t) x := by
  have hA := hasDerivAt_ranadaA_x y z t x
  have hfin : HasDerivAt (fun s => ranadaA s y z t * s + t * y)
      (x * x + ranadaA x y z t) x :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_id' x))
      (hasDerivAt_const x (t * y))).congr_deriv (by ring)
  simp only [ranadaP]
  exact hfin

/-- The `y` derivative of the Rañada letter `P`. -/
theorem hasDerivAt_ranadaP_y (x z t y : ℝ) :
    HasDerivAt (fun s => ranadaP x s z t) (y * x + t) y := by
  have hA := hasDerivAt_ranadaA_y x z t y
  have hfin : HasDerivAt (fun s => ranadaA x s z t * x + t * s) (y * x + t) y :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_const y x))
      (HasDerivAt.fun_mul (hasDerivAt_const y t) (hasDerivAt_id' y))).congr_deriv (by ring)
  simp only [ranadaP]
  exact hfin

/-- The `z` derivative of the Rañada letter `P`. -/
theorem hasDerivAt_ranadaP_z (x y t z : ℝ) :
    HasDerivAt (fun s => ranadaP x y s t) (z * x) z := by
  have hA := hasDerivAt_ranadaA_z x y t z
  have hfin : HasDerivAt (fun s => ranadaA x y s t * x + t * y) (z * x) z :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_const z x))
      (hasDerivAt_const z (t * y))).congr_deriv (by ring)
  simp only [ranadaP]
  exact hfin

/-- The `t` derivative of the Rañada letter `P`. -/
theorem hasDerivAt_ranadaP_t (x y z t : ℝ) :
    HasDerivAt (fun s => ranadaP x y z s) (y - t * x) t := by
  have hA := hasDerivAt_ranadaA_t x y z t
  have hfin : HasDerivAt (fun s => ranadaA x y z s * x + s * y) (y - t * x) t :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_const t x))
      (HasDerivAt.fun_mul (hasDerivAt_id' t) (hasDerivAt_const t y))).congr_deriv (by ring)
  simp only [ranadaP]
  exact hfin

/-- The `Q` letter partial derivatives are as printed. -/
theorem hasDerivAt_ranadaQ_x (y z t x : ℝ) :
    HasDerivAt (fun s => ranadaQ s y z t) (x * z + t * x) x := by
  have hA := hasDerivAt_ranadaA_x y z t x
  have hfin : HasDerivAt (fun s => ranadaA s y z t * z + t * (ranadaA s y z t - 1))
      (x * z + t * x) x :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_const x z))
      (HasDerivAt.fun_mul (hasDerivAt_const x t)
        (HasDerivAt.sub hA (hasDerivAt_const x (1 : ℝ))))).congr_deriv (by ring)
  simp only [ranadaQ]
  exact hfin

/-- The `y` derivative of the Rañada letter `Q`. -/
theorem hasDerivAt_ranadaQ_y (x z t y : ℝ) :
    HasDerivAt (fun s => ranadaQ x s z t) (y * z + t * y) y := by
  have hA := hasDerivAt_ranadaA_y x z t y
  have hfin : HasDerivAt (fun s => ranadaA x s z t * z + t * (ranadaA x s z t - 1))
      (y * z + t * y) y :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_const y z))
      (HasDerivAt.fun_mul (hasDerivAt_const y t)
        (HasDerivAt.sub hA (hasDerivAt_const y (1 : ℝ))))).congr_deriv (by ring)
  simp only [ranadaQ]
  exact hfin

/-- The `z` derivative of the Rañada letter `Q`. -/
theorem hasDerivAt_ranadaQ_z (x y t z : ℝ) :
    HasDerivAt (fun s => ranadaQ x y s t) (z * z + ranadaA x y z t + t * z) z := by
  have hA := hasDerivAt_ranadaA_z x y t z
  have hfin : HasDerivAt (fun s => ranadaA x y s t * s + t * (ranadaA x y s t - 1))
      (z * z + ranadaA x y z t + t * z) z :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_id' z))
      (HasDerivAt.fun_mul (hasDerivAt_const z t)
        (HasDerivAt.sub hA (hasDerivAt_const z (1 : ℝ))))).congr_deriv (by ring)
  simp only [ranadaQ]
  exact hfin

/-- The `t` derivative of the Rañada letter `Q`. -/
theorem hasDerivAt_ranadaQ_t (x y z t : ℝ) :
    HasDerivAt (fun s => ranadaQ x y z s) (ranadaA x y z t - 1 - t * z - t ^ 2) t := by
  have hA := hasDerivAt_ranadaA_t x y z t
  have hfin : HasDerivAt (fun s => ranadaA x y z s * z + s * (ranadaA x y z s - 1))
      (ranadaA x y z t - 1 - t * z - t ^ 2) t :=
    (HasDerivAt.fun_add (HasDerivAt.fun_mul hA (hasDerivAt_const t z))
      (HasDerivAt.fun_mul (hasDerivAt_id' t)
        (HasDerivAt.sub hA (hasDerivAt_const t (1 : ℝ))))).congr_deriv (by simp only [Pi.sub_apply]; ring)
  simp only [ranadaQ]
  exact hfin

/-- The `R` letter partial derivatives are as printed. -/
theorem hasDerivAt_ranadaR_x (y z t x : ℝ) :
    HasDerivAt (fun s => ranadaR s y z t) (t - x * y) x := by
  have hA := hasDerivAt_ranadaA_x y z t x
  have hfin : HasDerivAt (fun s => t * s - ranadaA s y z t * y) (t - x * y) x :=
    (HasDerivAt.sub (HasDerivAt.fun_mul (hasDerivAt_const x t) (hasDerivAt_id' x))
      (HasDerivAt.fun_mul hA (hasDerivAt_const x y))).congr_deriv (by ring)
  simp only [ranadaR]
  exact hfin

/-- The `y` derivative of the Rañada letter `R`. -/
theorem hasDerivAt_ranadaR_y (x z t y : ℝ) :
    HasDerivAt (fun s => ranadaR x s z t) (-(y * y + ranadaA x y z t)) y := by
  have hA := hasDerivAt_ranadaA_y x z t y
  have hfin : HasDerivAt (fun s => t * x - ranadaA x s z t * s)
      (-(y * y + ranadaA x y z t)) y :=
    (HasDerivAt.sub (hasDerivAt_const y (t * x))
      (HasDerivAt.fun_mul hA (hasDerivAt_id' y))).congr_deriv (by ring)
  simp only [ranadaR]
  exact hfin

/-- The `z` derivative of the Rañada letter `R`. -/
theorem hasDerivAt_ranadaR_z (x y t z : ℝ) :
    HasDerivAt (fun s => ranadaR x y s t) (-(z * y)) z := by
  have hA := hasDerivAt_ranadaA_z x y t z
  have hfin : HasDerivAt (fun s => t * x - ranadaA x y s t * y) (-(z * y)) z :=
    (HasDerivAt.sub (hasDerivAt_const z (t * x))
      (HasDerivAt.fun_mul hA (hasDerivAt_const z y))).congr_deriv (by ring)
  simp only [ranadaR]
  exact hfin

/-- The `t` derivative of the Rañada letter `R`. -/
theorem hasDerivAt_ranadaR_t (x y z t : ℝ) :
    HasDerivAt (fun s => ranadaR x y z s) (x + t * y) t := by
  have hA := hasDerivAt_ranadaA_t x y z t
  have hfin : HasDerivAt (fun s => s * x - ranadaA x y z s * y) (x + t * y) t :=
    (HasDerivAt.sub (HasDerivAt.fun_mul (hasDerivAt_id' t) (hasDerivAt_const t x))
      (HasDerivAt.fun_mul hA (hasDerivAt_const t y))).congr_deriv (by ring)
  simp only [ranadaR]
  exact hfin

/-- The `S` letter partial derivatives are as printed. -/
theorem hasDerivAt_ranadaS_x (y z t x : ℝ) :
    HasDerivAt (fun s => ranadaS s y z t) (x * (2 * ranadaA x y z t - 1)) x := by
  have hA := hasDerivAt_ranadaA_x y z t x
  have hfin : HasDerivAt (fun s => ranadaA s y z t * (ranadaA s y z t - 1) - t * z)
      (x * (2 * ranadaA x y z t - 1)) x :=
    (HasDerivAt.sub (HasDerivAt.fun_mul hA
      (HasDerivAt.sub hA (hasDerivAt_const x (1 : ℝ))))
      (hasDerivAt_const x (t * z))).congr_deriv (by simp only [Pi.sub_apply]; ring)
  simp only [ranadaS]
  exact hfin

/-- The `y` derivative of the Rañada letter `S`. -/
theorem hasDerivAt_ranadaS_y (x z t y : ℝ) :
    HasDerivAt (fun s => ranadaS x s z t) (y * (2 * ranadaA x y z t - 1)) y := by
  have hA := hasDerivAt_ranadaA_y x z t y
  have hfin : HasDerivAt (fun s => ranadaA x s z t * (ranadaA x s z t - 1) - t * z)
      (y * (2 * ranadaA x y z t - 1)) y :=
    (HasDerivAt.sub (HasDerivAt.fun_mul hA
      (HasDerivAt.sub hA (hasDerivAt_const y (1 : ℝ))))
      (hasDerivAt_const y (t * z))).congr_deriv (by simp only [Pi.sub_apply]; ring)
  simp only [ranadaS]
  exact hfin

/-- The `z` derivative of the Rañada letter `S`. -/
theorem hasDerivAt_ranadaS_z (x y t z : ℝ) :
    HasDerivAt (fun s => ranadaS x y s t) (z * (2 * ranadaA x y z t - 1) - t) z := by
  have hA := hasDerivAt_ranadaA_z x y t z
  have hfin : HasDerivAt (fun s => ranadaA x y s t * (ranadaA x y s t - 1) - t * s)
      (z * (2 * ranadaA x y z t - 1) - t) z :=
    (HasDerivAt.sub (HasDerivAt.fun_mul hA
      (HasDerivAt.sub hA (hasDerivAt_const z (1 : ℝ))))
      (HasDerivAt.fun_mul (hasDerivAt_const z t) (hasDerivAt_id' z))).congr_deriv (by simp only [Pi.sub_apply]; ring)
  simp only [ranadaS]
  exact hfin

/-- The `t` derivative of the Rañada letter `S`. -/
theorem hasDerivAt_ranadaS_t (x y z t : ℝ) :
    HasDerivAt (fun s => ranadaS x y z s) (-(t * (2 * ranadaA x y z t - 1)) - z) t := by
  have hA := hasDerivAt_ranadaA_t x y z t
  have hfin : HasDerivAt (fun s => ranadaA x y z s * (ranadaA x y z s - 1) - s * z)
      (-(t * (2 * ranadaA x y z t - 1)) - z) t :=
    (HasDerivAt.sub (HasDerivAt.fun_mul hA
      (HasDerivAt.sub hA (hasDerivAt_const t (1 : ℝ))))
      (HasDerivAt.fun_mul (hasDerivAt_id' t) (hasDerivAt_const t z))).congr_deriv (by simp only [Pi.sub_apply]; ring)
  simp only [ranadaS]
  exact hfin

/-! ### Certified spatial gradients of the letter pairs -/

/-- The `x`-partial of the magnetic numerator `Q + iR`. -/
noncomputable def etaNumX (x y z t : ℝ) : ℂ :=
  ((x * z + t * x : ℝ) : ℂ) + Complex.I * ((t - x * y : ℝ) : ℂ)

/-- The `y`-partial of the magnetic numerator. -/
noncomputable def etaNumY (x y z t : ℝ) : ℂ :=
  ((y * z + t * y : ℝ) : ℂ) + Complex.I * ((-(y ^ 2 + ranadaA x y z t) : ℝ) : ℂ)

/-- The `z`-partial of the magnetic numerator. -/
noncomputable def etaNumZ (x y z t : ℝ) : ℂ :=
  ((z ^ 2 + ranadaA x y z t + t * z : ℝ) : ℂ) +
    Complex.I * ((-(z * y) : ℝ) : ℂ)

/-- The spatial gradient of the magnetic numerator. -/
noncomputable def etaNumGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  ![etaNumX x y z t, etaNumY x y z t, etaNumZ x y z t]

/-- The `x`-partial of the magnetic denominator `P + iS`. -/
noncomputable def etaDenX (x y z t : ℝ) : ℂ :=
  ((ranadaA x y z t + x ^ 2 : ℝ) : ℂ) +
    Complex.I * ((x * (2 * ranadaA x y z t - 1) : ℝ) : ℂ)

/-- The `y`-partial of the magnetic denominator. -/
noncomputable def etaDenY (x y z t : ℝ) : ℂ :=
  ((x * y + t : ℝ) : ℂ) + Complex.I * ((y * (2 * ranadaA x y z t - 1) : ℝ) : ℂ)

/-- The `z`-partial of the magnetic denominator. -/
noncomputable def etaDenZ (x y z t : ℝ) : ℂ :=
  ((x * z : ℝ) : ℂ) + Complex.I * ((z * (2 * ranadaA x y z t - 1) - t : ℝ) : ℂ)

/-- The spatial gradient of the magnetic denominator. -/
noncomputable def etaDenGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  ![etaDenX x y z t, etaDenY x y z t, etaDenZ x y z t]

/-- The `x`-partial of the electric numerator `P + iQ`. -/
noncomputable def zetaNumX (x y z t : ℝ) : ℂ :=
  ((ranadaA x y z t + x ^ 2 : ℝ) : ℂ) + Complex.I * ((x * z + t * x : ℝ) : ℂ)

/-- The `y`-partial of the electric numerator. -/
noncomputable def zetaNumY (x y z t : ℝ) : ℂ :=
  ((x * y + t : ℝ) : ℂ) + Complex.I * ((y * z + t * y : ℝ) : ℂ)

/-- The `z`-partial of the electric numerator. -/
noncomputable def zetaNumZ (x y z t : ℝ) : ℂ :=
  ((x * z : ℝ) : ℂ) + Complex.I * ((z ^ 2 + ranadaA x y z t + t * z : ℝ) : ℂ)

/-- The spatial gradient of the electric numerator. -/
noncomputable def zetaNumGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  ![zetaNumX x y z t, zetaNumY x y z t, zetaNumZ x y z t]

/-- The `x`-partial of the electric denominator `R + iS`. -/
noncomputable def zetaDenX (x y z t : ℝ) : ℂ :=
  ((t - x * y : ℝ) : ℂ) + Complex.I * ((x * (2 * ranadaA x y z t - 1) : ℝ) : ℂ)

/-- The `y`-partial of the electric denominator. -/
noncomputable def zetaDenY (x y z t : ℝ) : ℂ :=
  ((-(y ^ 2 + ranadaA x y z t) : ℝ) : ℂ) +
    Complex.I * ((y * (2 * ranadaA x y z t - 1) : ℝ) : ℂ)

/-- The `z`-partial of the electric denominator. -/
noncomputable def zetaDenZ (x y z t : ℝ) : ℂ :=
  ((-(z * y) : ℝ) : ℂ) + Complex.I * ((z * (2 * ranadaA x y z t - 1) - t : ℝ) : ℂ)

/-- The spatial gradient of the electric denominator. -/
noncomputable def zetaDenGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  ![zetaDenX x y z t, zetaDenY x y z t, zetaDenZ x y z t]

/-- Each letter pair has certified spatial derivatives. -/
theorem hasDerivAt_etaNum_x (y z t x : ℝ) :
    HasDerivAt (fun s => etaNum s y z t) (etaNumX x y z t) x := by
  simp only [etaNum, etaNumX]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaQ_x y z t x).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const x Complex.I)
      (hasDerivAt_ranadaR_x y z t x).ofReal_comp) |>.congr_deriv
      (by simp)

/-- The `y` derivative of the magnetic numerator. -/
theorem hasDerivAt_etaNum_y (x z t y : ℝ) :
    HasDerivAt (fun s => etaNum x s z t) (etaNumY x y z t) y := by
  simp only [etaNum, etaNumY]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaQ_y x z t y).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const y Complex.I)
      (hasDerivAt_ranadaR_y x z t y).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `z` derivative of the magnetic numerator. -/
theorem hasDerivAt_etaNum_z (x y t z : ℝ) :
    HasDerivAt (fun s => etaNum x y s t) (etaNumZ x y z t) z := by
  simp only [etaNum, etaNumZ]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaQ_z x y t z).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const z Complex.I)
      (hasDerivAt_ranadaR_z x y t z).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `x` derivative of the magnetic denominator. -/
theorem hasDerivAt_etaDen_x (y z t x : ℝ) :
    HasDerivAt (fun s => etaDen s y z t) (etaDenX x y z t) x := by
  simp only [etaDen, etaDenX]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaP_x y z t x).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const x Complex.I)
      (hasDerivAt_ranadaS_x y z t x).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `y` derivative of the magnetic denominator. -/
theorem hasDerivAt_etaDen_y (x z t y : ℝ) :
    HasDerivAt (fun s => etaDen x s z t) (etaDenY x y z t) y := by
  simp only [etaDen, etaDenY]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaP_y x z t y).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const y Complex.I)
      (hasDerivAt_ranadaS_y x z t y).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `z` derivative of the magnetic denominator. -/
theorem hasDerivAt_etaDen_z (x y t z : ℝ) :
    HasDerivAt (fun s => etaDen x y s t) (etaDenZ x y z t) z := by
  simp only [etaDen, etaDenZ]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaP_z x y t z).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const z Complex.I)
      (hasDerivAt_ranadaS_z x y t z).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `x` derivative of the electric numerator. -/
theorem hasDerivAt_zetaNum_x (y z t x : ℝ) :
    HasDerivAt (fun s => zetaNum s y z t) (zetaNumX x y z t) x := by
  simp only [zetaNum, zetaNumX]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaP_x y z t x).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const x Complex.I)
      (hasDerivAt_ranadaQ_x y z t x).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `y` derivative of the electric numerator. -/
theorem hasDerivAt_zetaNum_y (x z t y : ℝ) :
    HasDerivAt (fun s => zetaNum x s z t) (zetaNumY x y z t) y := by
  simp only [zetaNum, zetaNumY]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaP_y x z t y).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const y Complex.I)
      (hasDerivAt_ranadaQ_y x z t y).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `z` derivative of the electric numerator. -/
theorem hasDerivAt_zetaNum_z (x y t z : ℝ) :
    HasDerivAt (fun s => zetaNum x y s t) (zetaNumZ x y z t) z := by
  simp only [zetaNum, zetaNumZ]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaP_z x y t z).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const z Complex.I)
      (hasDerivAt_ranadaQ_z x y t z).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `x` derivative of the electric denominator. -/
theorem hasDerivAt_zetaDen_x (y z t x : ℝ) :
    HasDerivAt (fun s => zetaDen s y z t) (zetaDenX x y z t) x := by
  simp only [zetaDen, zetaDenX]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaR_x y z t x).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const x Complex.I)
      (hasDerivAt_ranadaS_x y z t x).ofReal_comp) |>.congr_deriv
      (by simp)

/-- The `y` derivative of the electric denominator. -/
theorem hasDerivAt_zetaDen_y (x z t y : ℝ) :
    HasDerivAt (fun s => zetaDen x s z t) (zetaDenY x y z t) y := by
  simp only [zetaDen, zetaDenY]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaR_y x z t y).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const y Complex.I)
      (hasDerivAt_ranadaS_y x z t y).ofReal_comp) |>.congr_deriv
      (by simp; ring)

/-- The `z` derivative of the electric denominator. -/
theorem hasDerivAt_zetaDen_z (x y t z : ℝ) :
    HasDerivAt (fun s => zetaDen x y s t) (zetaDenZ x y z t) z := by
  simp only [zetaDen, zetaDenZ]
  exact HasDerivAt.fun_add (hasDerivAt_ranadaR_z x y t z).ofReal_comp
    (HasDerivAt.fun_mul (hasDerivAt_const z Complex.I)
      (hasDerivAt_ranadaS_z x y t z).ofReal_comp) |>.congr_deriv
      (by simp)

/-! ### The global Hopf electromagnetic fields -/

/-- The homogeneous numerator vector `b ∇a − a ∇b` of the magnetic field,
with `a` the magnetic numerator and `b` the magnetic denominator, and
gradients detailed below. -/
noncomputable def etaHomog (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => etaDen x y z t * etaNumGrad x y z t j - etaNum x y z t * etaDenGrad x y z t j

/-- The total squared modulus of the magnetic letter pair. -/
noncomputable def etaSumSq (x y z t : ℝ) : ℂ :=
  etaNum x y z t * conj (etaNum x y z t) +
    etaDen x y z t * conj (etaDen x y z t)

/-- The magnetic field of the Hopf construction, defined on all of spacetime
by the homogeneous formula with never-vanishing denominator. -/
noncomputable def ranadaB (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => (1 / (4 * Real.pi * Complex.I)) *
    (cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) /
    (etaSumSq x y z t) ^ 2

/-- The homogeneous numerator vector of the electric field. -/
noncomputable def zetaHomog (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => zetaDen x y z t * zetaNumGrad x y z t j - zetaNum x y z t * zetaDenGrad x y z t j

/-- The total squared modulus of the electric letter pair. -/
noncomputable def zetaSumSq (x y z t : ℝ) : ℂ :=
  zetaNum x y z t * conj (zetaNum x y z t) +
    zetaDen x y z t * conj (zetaDen x y z t)

/-- The electric field of the Hopf construction, defined on all of spacetime
by the homogeneous formula with never-vanishing denominator. -/
noncomputable def ranadaE (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => (1 / (4 * Real.pi * Complex.I)) *
    (cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j) /
    (zetaSumSq x y z t) ^ 2

/-- The magnetic total squared modulus never vanishes. -/
theorem etaSumSq_ne_zero (x y z t : ℝ) : etaSumSq x y z t ≠ 0 := by
  rw [etaSumSq, etaPairNormSq]
  exact fun h => absurd h (Complex.ofReal_ne_zero.mpr (ne_of_gt (ranadaNormSq_pos x y z t)))

/-- The electric total squared modulus never vanishes either. -/
theorem zetaSumSq_ne_zero (x y z t : ℝ) : zetaSumSq x y z t ≠ 0 := by
  rw [zetaSumSq, zetaPairNormSq]
  exact fun h => absurd h (Complex.ofReal_ne_zero.mpr (ne_of_gt (ranadaNormSq_pos x y z t)))

/-- The magnetic field takes real values. -/
theorem ranadaB_re (x y z t : ℝ) (j : Fin 3) :
    conj (ranadaB x y z t j) = ranadaB x y z t j := by
  have hc := cross3_add_conj_self_eq_zero (etaHomog x y z t) j
  have hd : conj ((etaSumSq x y z t) ^ 2) = (etaSumSq x y z t) ^ 2 := by
    rw [conj_pow', etaSumSq]
    simp only [conj_add', conj_mul', Complex.conj_conj]
    ring
  have h2 : conj (cross3 (etaHomog x y z t)
      (fun k => conj (etaHomog x y z t k)) j) =
      -(cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) := by
    linear_combination hc
  show conj ((1 / (4 * Real.pi * Complex.I)) *
      (cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) /
      (etaSumSq x y z t) ^ 2) =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) /
      (etaSumSq x y z t) ^ 2
  rw [conj_div', conj_mul', hd, h2, conj_prefactor]
  ring

/-- The magnetic field has vanishing imaginary part. -/
theorem ranadaB_im (x y z t : ℝ) (j : Fin 3) : (ranadaB x y z t j).im = 0 := by
  have h := congrArg Complex.im (ranadaB_re x y z t j)
  simp only [Complex.conj_im] at h
  linarith

/-- The electric field takes real values. -/
theorem ranadaE_re (x y z t : ℝ) (j : Fin 3) :
    conj (ranadaE x y z t j) = ranadaE x y z t j := by
  have hc := cross3_add_conj_self_eq_zero (zetaHomog x y z t) j
  have hd : conj ((zetaSumSq x y z t) ^ 2) = (zetaSumSq x y z t) ^ 2 := by
    rw [conj_pow', zetaSumSq]
    simp only [conj_add', conj_mul', Complex.conj_conj]
    ring
  have h2 : conj (cross3 (zetaHomog x y z t)
      (fun k => conj (zetaHomog x y z t k)) j) =
      -(cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j) := by
    linear_combination hc
  show conj ((1 / (4 * Real.pi * Complex.I)) *
      (cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j) /
      (zetaSumSq x y z t) ^ 2) =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j) /
      (zetaSumSq x y z t) ^ 2
  rw [conj_div', conj_mul', hd, h2, conj_prefactor]
  ring

/-- The electric field has vanishing imaginary part. -/
theorem ranadaE_im (x y z t : ℝ) (j : Fin 3) : (ranadaE x y z t j).im = 0 := by
  have h := congrArg Complex.im (ranadaE_re x y z t j)
  simp only [Complex.conj_im] at h
  linarith

/-! ### Agreement with the printed formula and the reciprocal chart -/

/-- Component access for the magnetic numerator gradient. -/
theorem etaNumGrad_zero (x y z t : ℝ) : etaNumGrad x y z t 0 = etaNumX x y z t := rfl
/-- The `y` component of the gradient of the magnetic numerator. -/
theorem etaNumGrad_one (x y z t : ℝ) : etaNumGrad x y z t 1 = etaNumY x y z t := rfl
/-- The `z` component of the gradient of the magnetic numerator. -/
theorem etaNumGrad_two (x y z t : ℝ) : etaNumGrad x y z t 2 = etaNumZ x y z t := rfl

/-- Component access for the magnetic denominator gradient. -/
theorem etaDenGrad_zero (x y z t : ℝ) : etaDenGrad x y z t 0 = etaDenX x y z t := rfl
/-- The `y` component of the gradient of the magnetic denominator. -/
theorem etaDenGrad_one (x y z t : ℝ) : etaDenGrad x y z t 1 = etaDenY x y z t := rfl
/-- The `z` component of the gradient of the magnetic denominator. -/
theorem etaDenGrad_two (x y z t : ℝ) : etaDenGrad x y z t 2 = etaDenZ x y z t := rfl

/-- Component access for the electric gradients. -/
theorem zetaNumGrad_one (x y z t : ℝ) : zetaNumGrad x y z t 1 = zetaNumY x y z t := rfl
/-- The `z` component of the gradient of the electric numerator. -/
theorem zetaNumGrad_two (x y z t : ℝ) : zetaNumGrad x y z t 2 = zetaNumZ x y z t := rfl
/-- The `y` component of the gradient of the electric denominator. -/
theorem zetaDenGrad_one (x y z t : ℝ) : zetaDenGrad x y z t 1 = zetaDenY x y z t := rfl
/-- The `z` component of the gradient of the electric denominator. -/
theorem zetaDenGrad_two (x y z t : ℝ) : zetaDenGrad x y z t 2 = zetaDenZ x y z t := rfl

/-- The quotient-form spatial gradient of the printed magnetic scalar. -/
noncomputable def etaGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => (etaDen x y z t * etaNumGrad x y z t j - etaNum x y z t * etaDenGrad x y z t j) /
    (etaDen x y z t ^ 2)

/-- The quotient-form spatial gradient of the printed electric scalar. -/
noncomputable def zetaGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => (zetaDen x y z t * zetaNumGrad x y z t j - zetaNum x y z t * zetaDenGrad x y z t j) /
    (zetaDen x y z t ^ 2)

/-- The quotient-form gradient is the `x`-derivative of the magnetic scalar. -/
theorem hasDerivAt_ranadaEta_x {x y z t : ℝ} (hd : etaDen x y z t ≠ 0) :
    HasDerivAt (fun s => ranadaEta s y z t) (etaGrad x y z t 0) x := by
  simp only [ranadaEta_def]
  exact (HasDerivAt.div (hasDerivAt_etaNum_x y z t x) (hasDerivAt_etaDen_x y z t x)
    (by simpa using hd)).congr_deriv (by
      simp only [etaGrad, etaNumGrad, etaDenGrad, Matrix.cons_val_zero]
      ring)

/-- The `y` derivative of the magnetic scalar on its affine chart. -/
theorem hasDerivAt_ranadaEta_y {x y z t : ℝ} (hd : etaDen x y z t ≠ 0) :
    HasDerivAt (fun s => ranadaEta x s z t) (etaGrad x y z t 1) y := by
  simp only [ranadaEta_def]
  exact (HasDerivAt.div (hasDerivAt_etaNum_y x z t y) (hasDerivAt_etaDen_y x z t y)
    (by simpa using hd)).congr_deriv (by
      simp only [etaGrad]
      rw [etaNumGrad_one, etaDenGrad_one]
      ring)

/-- The `z` derivative of the magnetic scalar on its affine chart. -/
theorem hasDerivAt_ranadaEta_z {x y z t : ℝ} (hd : etaDen x y z t ≠ 0) :
    HasDerivAt (fun s => ranadaEta x y s t) (etaGrad x y z t 2) z := by
  simp only [ranadaEta_def]
  exact (HasDerivAt.div (hasDerivAt_etaNum_z x y t z) (hasDerivAt_etaDen_z x y t z)
    (by simpa using hd)).congr_deriv (by
      simp only [etaGrad]
      rw [etaNumGrad_two, etaDenGrad_two]
      ring)

/-- The quotient-form gradient is the `x`-derivative of the electric scalar. -/
theorem hasDerivAt_ranadaZeta_x {x y z t : ℝ} (hd : zetaDen x y z t ≠ 0) :
    HasDerivAt (fun s => ranadaZeta s y z t) (zetaGrad x y z t 0) x := by
  simp only [ranadaZeta_def]
  exact (HasDerivAt.div (hasDerivAt_zetaNum_x y z t x) (hasDerivAt_zetaDen_x y z t x)
    (by simpa using hd)).congr_deriv (by
      simp only [zetaGrad, zetaNumGrad, zetaDenGrad, Matrix.cons_val_zero]
      ring)

/-- The `y` derivative of the electric scalar on its affine chart. -/
theorem hasDerivAt_ranadaZeta_y {x y z t : ℝ} (hd : zetaDen x y z t ≠ 0) :
    HasDerivAt (fun s => ranadaZeta x s z t) (zetaGrad x y z t 1) y := by
  simp only [ranadaZeta_def]
  exact (HasDerivAt.div (hasDerivAt_zetaNum_y x z t y) (hasDerivAt_zetaDen_y x z t y)
    (by simpa using hd)).congr_deriv (by
      simp only [zetaGrad]
      rw [zetaNumGrad_one, zetaDenGrad_one]
      ring)

/-- The `z` derivative of the electric scalar on its affine chart. -/
theorem hasDerivAt_ranadaZeta_z {x y z t : ℝ} (hd : zetaDen x y z t ≠ 0) :
    HasDerivAt (fun s => ranadaZeta x y s t) (zetaGrad x y z t 2) z := by
  simp only [ranadaZeta_def]
  exact (HasDerivAt.div (hasDerivAt_zetaNum_z x y t z) (hasDerivAt_zetaDen_z x y t z)
    (by simpa using hd)).congr_deriv (by
      simp only [zetaGrad]
      rw [zetaNumGrad_two, zetaDenGrad_two]
      ring)

/-- Wherever the printed magnetic scalar is finite, the global magnetic field
is exactly the printed density of the scalar. -/
theorem ranadaB_eq_density {x y z t : ℝ} (hd : etaDen x y z t ≠ 0) :
    density (ranadaEta x y z t) (etaGrad x y z t) = ranadaB x y z t := by
  have hc : conj (etaDen x y z t) ≠ 0 := conj_ne_zero' hd
  have hprod : etaDen x y z t * conj (etaDen x y z t) ≠ 0 := mul_ne_zero hd hc
  have hsum := etaSumSq_ne_zero x y z t
  have hkey : (1 + ranadaEta x y z t * conj (ranadaEta x y z t)) *
      (etaDen x y z t * conj (etaDen x y z t)) = etaSumSq x y z t := by
    rw [ranadaEta_def, conj_div', etaSumSq]
    field_simp [hd]
    ring
  have hgrad : etaGrad x y z t =
      fun k => etaHomog x y z t k / (etaDen x y z t ^ 2) := rfl
  have hden2 : 1 + ranadaEta x y z t * conj (ranadaEta x y z t) =
      etaSumSq x y z t / (etaDen x y z t * conj (etaDen x y z t)) := by
    rw [eq_div_iff hprod]
    exact hkey
  have hcg : (fun k => conj (etaHomog x y z t k / etaDen x y z t ^ 2))
      = fun k => conj (etaHomog x y z t k) / (conj (etaDen x y z t)) ^ 2 := by
    funext k
    simp only [conj_div', conj_pow']
  funext j
  show (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (etaGrad x y z t) (fun k => conj (etaGrad x y z t k)) j) /
      (1 + ranadaEta x y z t * conj (ranadaEta x y z t)) ^ 2 =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) /
      (etaSumSq x y z t) ^ 2
  rw [hgrad, hcg, cross3_div_div, hden2]
  field_simp [hd, hc, hprod, hsum]

/-- Wherever the printed electric scalar is finite, the global electric field
is exactly the printed density of the scalar. -/
theorem ranadaE_eq_density {x y z t : ℝ} (hd : zetaDen x y z t ≠ 0) :
    density (ranadaZeta x y z t) (zetaGrad x y z t) = ranadaE x y z t := by
  have hc : conj (zetaDen x y z t) ≠ 0 := conj_ne_zero' hd
  have hprod : zetaDen x y z t * conj (zetaDen x y z t) ≠ 0 := mul_ne_zero hd hc
  have hsum := zetaSumSq_ne_zero x y z t
  have hkey : (1 + ranadaZeta x y z t * conj (ranadaZeta x y z t)) *
      (zetaDen x y z t * conj (zetaDen x y z t)) = zetaSumSq x y z t := by
    rw [ranadaZeta_def, conj_div', zetaSumSq]
    field_simp [hd]
    ring
  have hgrad : zetaGrad x y z t =
      fun k => zetaHomog x y z t k / (zetaDen x y z t ^ 2) := rfl
  have hden2 : 1 + ranadaZeta x y z t * conj (ranadaZeta x y z t) =
      zetaSumSq x y z t / (zetaDen x y z t * conj (zetaDen x y z t)) := by
    rw [eq_div_iff hprod]
    exact hkey
  have hcg : (fun k => conj (zetaHomog x y z t k / zetaDen x y z t ^ 2))
      = fun k => conj (zetaHomog x y z t k) / (conj (zetaDen x y z t)) ^ 2 := by
    funext k
    simp only [conj_div', conj_pow']
  funext j
  show (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (zetaGrad x y z t) (fun k => conj (zetaGrad x y z t k)) j) /
      (1 + ranadaZeta x y z t * conj (ranadaZeta x y z t)) ^ 2 =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j) /
      (zetaSumSq x y z t) ^ 2
  rw [hgrad, hcg, cross3_div_div, hden2]
  field_simp [hd, hc, hprod, hsum]

/-- The reciprocal-chart scalar of the magnetic letter pair, finite at the
genuine poles of the magnetic scalar. -/
noncomputable def etaRecip (x y z t : ℝ) : ℂ :=
  etaDen x y z t / etaNum x y z t

/-- The reciprocal-chart gradient, quotient form in the letters. -/
noncomputable def etaRecipGrad (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => (etaNum x y z t * etaDenGrad x y z t j - etaDen x y z t * etaNumGrad x y z t j) /
    (etaNum x y z t ^ 2)

/-- The reciprocal-chart scalar is the inverse of the printed magnetic
scalar wherever the latter is finite. -/
theorem etaRecip_eq_inv {x y z t : ℝ} (hn : etaNum x y z t ≠ 0) :
    etaRecip x y z t = (ranadaEta x y z t)⁻¹ := by
  rw [etaRecip, ranadaEta_def]
  field_simp [hn]

/-- The reciprocal-chart gradient is the `x`-derivative of the
reciprocal-chart scalar. -/
theorem hasDerivAt_etaRecip_x {x y z t : ℝ} (hn : etaNum x y z t ≠ 0) :
    HasDerivAt (fun s => etaRecip s y z t) (etaRecipGrad x y z t 0) x := by
  simp only [etaRecip]
  exact (HasDerivAt.div (hasDerivAt_etaDen_x y z t x) (hasDerivAt_etaNum_x y z t x)
    (by simpa using hn)).congr_deriv (by
      simp only [etaRecipGrad, etaNumGrad, etaDenGrad, Matrix.cons_val_zero]
      ring)

/-- The `y` derivative of the magnetic scalar on its reciprocal chart. -/
theorem hasDerivAt_etaRecip_y {x y z t : ℝ} (hn : etaNum x y z t ≠ 0) :
    HasDerivAt (fun s => etaRecip x s z t) (etaRecipGrad x y z t 1) y := by
  simp only [etaRecip]
  exact (HasDerivAt.div (hasDerivAt_etaDen_y x z t y) (hasDerivAt_etaNum_y x z t y)
    (by simpa using hn)).congr_deriv (by
      simp only [etaRecipGrad]
      rw [etaNumGrad_one, etaDenGrad_one]
      ring)

/-- The `z` derivative of the magnetic scalar on its reciprocal chart. -/
theorem hasDerivAt_etaRecip_z {x y z t : ℝ} (hn : etaNum x y z t ≠ 0) :
    HasDerivAt (fun s => etaRecip x y s t) (etaRecipGrad x y z t 2) z := by
  simp only [etaRecip]
  exact (HasDerivAt.div (hasDerivAt_etaDen_z x y t z) (hasDerivAt_etaNum_z x y t z)
    (by simpa using hn)).congr_deriv (by
      simp only [etaRecipGrad]
      rw [etaNumGrad_two, etaDenGrad_two]
      ring)

/-- Around genuine poles of the printed magnetic scalar (numerator nonzero),
the global magnetic field equals the same density computed in the
reciprocal chart — the smooth-gluing statement of the construction. -/
theorem ranadaB_eq_density_recip {x y z t : ℝ} (hn : etaNum x y z t ≠ 0) :
    density (etaRecip x y z t) (etaRecipGrad x y z t) = ranadaB x y z t := by
  have hc : conj (etaNum x y z t) ≠ 0 := conj_ne_zero' hn
  have hprod : etaNum x y z t * conj (etaNum x y z t) ≠ 0 := mul_ne_zero hn hc
  have hsum := etaSumSq_ne_zero x y z t
  have hkey : (1 + etaRecip x y z t * conj (etaRecip x y z t)) *
      (etaNum x y z t * conj (etaNum x y z t)) = etaSumSq x y z t := by
    rw [etaRecip, conj_div', etaSumSq]
    field_simp [hn]
  have hgrad : etaRecipGrad x y z t =
      fun k => (-(etaHomog x y z t k)) / (etaNum x y z t ^ 2) := by
    funext k
    simp only [etaRecipGrad, etaHomog]
    ring
  have hden2 : 1 + etaRecip x y z t * conj (etaRecip x y z t) =
      etaSumSq x y z t / (etaNum x y z t * conj (etaNum x y z t)) := by
    rw [eq_div_iff hprod]
    exact hkey
  have hcg : (fun k => conj ((-(etaHomog x y z t k)) / etaNum x y z t ^ 2))
      = fun k => -(conj (etaHomog x y z t k)) / (conj (etaNum x y z t)) ^ 2 := by
    funext k
    simp only [conj_div', conj_neg', conj_pow']
  funext j
  show (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (etaRecipGrad x y z t) (fun k => conj (etaRecipGrad x y z t k)) j) /
      (1 + etaRecip x y z t * conj (etaRecip x y z t)) ^ 2 =
    (1 / (4 * Real.pi * Complex.I)) *
      (cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) /
      (etaSumSq x y z t) ^ 2
  rw [hgrad, hcg, cross3_div_div, cross3_neg_neg, hden2]
  field_simp [hn, hc, hprod, hsum]

end Qatlib.Papers.KnottedLight08.HopfField
