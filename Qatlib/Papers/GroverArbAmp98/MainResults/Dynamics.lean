/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Grover dynamics for arbitrary complex amplitudes

This module represents marked and unmarked amplitude vectors by `Amps` and derives their exact
evolution under `step` and `orbit`. The combinations `fplus` and `fminus` diagonalize the
mean-amplitude recurrence, giving closed formulas and invariant norms as in [BihamEtAl1999].

The marked squared-amplitude mass is then expressed as a cosine oscillation with baseline `Pav`,
amplitude `DeltaP`, and upper envelope `Pmax`. The results apply to arbitrary initial complex
amplitudes with nonempty marked and unmarked sectors where required.

## Main statements

* `source_exact_dynamics`: amplitude formulas, mean formulas, and invariants along the orbit.
* `probMarked_orbit_eq`: the oscillatory marked-mass formula.
* `source_success_probability`: the cosine representation and its upper envelope.

## References

* [Biham et al., 1999][BihamEtAl1999]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GroverArbAmp98.MainResults.Dynamics

variable {r m : ℕ}

/-- A pair of complex amplitude vectors for `r` marked and `m` unmarked states. -/
abbrev Amps (r m : ℕ) := (Fin r → ℂ) × (Fin m → ℂ)

/-- The arithmetic mean of a finite complex amplitude vector, using the totalized inverse of its
length. -/
def ampAvg {n : ℕ} (v : Fin n → ℂ) : ℂ := (n : ℂ)⁻¹ * ∑ i, v i

/-- Summing `c + v i` over a finite index type gives the length times `c` plus the sum of `v`. -/
@[simp] lemma sum_add_const {n : ℕ} (c : ℂ) (v : Fin n → ℂ) :
    ∑ i, (c + v i) = (n : ℂ) * c + ∑ i, v i := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Summing `c - v i` over a finite index type gives the length times `c` minus the sum of `v`. -/
@[simp] lemma sum_sub_const {n : ℕ} (c : ℂ) (v : Fin n → ℂ) :
    ∑ i, (c - v i) = (n : ℂ) * c - ∑ i, v i := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The common increment `2 * (m * ampAvg x.2 - r * ampAvg x.1) / (r+m)` in the amplitude
update. -/
def idxC (x : Amps r m) : ℂ :=
  (2 : ℂ) * (((r + m : ℕ) : ℂ))⁻¹ *
    ((m : ℂ) * ampAvg x.2 - (r : ℂ) * ampAvg x.1)

/-- One Grover update, adding `idxC x` to each marked amplitude and subtracting each unmarked
amplitude from `idxC x`. -/
def step (x : Amps r m) : Amps r m :=
  (fun i => idxC x + x.1 i, fun j => idxC x - x.2 j)

/-- The sequence of amplitude pairs obtained by repeatedly applying `step` to `x0`. -/
def orbit (x0 : Amps r m) : ℕ → Amps r m
  | 0 => x0
  | t + 1 => step (orbit x0 t)

/-- The amplitude orbit at time zero is the initial amplitude pair. -/
@[simp] lemma orbit_zero (x0 : Amps r m) : orbit x0 0 = x0 := rfl

/-- The amplitude orbit at time `t + 1` is obtained by applying one Grover step at time `t`. -/
@[simp] lemma orbit_succ (x0 : Amps r m) (t : ℕ) :
    orbit x0 (t + 1) = step (orbit x0 t) := rfl

/-- The mean marked amplitude at time `t` along the orbit. -/
def kbar (x0 : Amps r m) (t : ℕ) : ℂ := ampAvg (orbit x0 t).1

/-- The mean unmarked amplitude at time `t` along the orbit. -/
def lbar (x0 : Amps r m) (t : ℕ) : ℂ := ampAvg (orbit x0 t).2

/-- The initial marked mean is the mean of the initial marked amplitude vector. -/
@[simp] lemma kbar_zero (x0 : Amps r m) : kbar x0 0 = ampAvg x0.1 := rfl

/-- The initial unmarked mean is the mean of the initial unmarked amplitude vector. -/
@[simp] lemma lbar_zero (x0 : Amps r m) : lbar x0 0 = ampAvg x0.2 := rfl

/-- For a nonempty marked sector, the marked mean at the next step is its current mean plus the
common increment. -/
theorem kbar_succ (hr : 1 ≤ r) (x0 : Amps r m) (t : ℕ) :
    kbar x0 (t + 1) = idxC (orbit x0 t) + kbar x0 t := by
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [kbar, orbit_succ, step, ampAvg]
  rw [sum_add_const, mul_add, ← mul_assoc, inv_mul_cancel₀ hrC, one_mul]

/-- For a nonempty unmarked sector, the next unmarked mean is the common increment minus the
current unmarked mean. -/
theorem lbar_succ (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    lbar x0 (t + 1) = idxC (orbit x0 t) - lbar x0 t := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [lbar, orbit_succ, step, ampAvg]
  rw [sum_sub_const, mul_sub, ← mul_assoc, inv_mul_cancel₀ hmC, one_mul]

/-- For a nonempty marked sector, a Grover step adds `idxC x` to the marked mean. -/
theorem ampAvg_step_marked (hr : 1 ≤ r) (x : Amps r m) :
    ampAvg (step x).1 = idxC x + ampAvg x.1 := by
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [step, ampAvg]
  rw [sum_add_const, mul_add, ← mul_assoc, inv_mul_cancel₀ hrC, one_mul]

/-- For a nonempty unmarked sector, a Grover step replaces the unmarked mean by `idxC x` minus
that mean. -/
theorem ampAvg_step_unmarked (hm : 1 ≤ m) (x : Amps r m) :
    ampAvg (step x).2 = idxC x - ampAvg x.2 := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [step, ampAvg]
  rw [sum_sub_const, mul_sub, ← mul_assoc, inv_mul_cancel₀ hmC, one_mul]

/-- The real scaling factor `√(r/m)` relating the marked and unmarked mean amplitudes. -/
def sReal (r m : ℕ) : ℝ := Real.sqrt ((r : ℝ) / (m : ℝ))

/-- The complex embedding of the real scaling factor `sReal r m`. -/
def sC (r m : ℕ) : ℂ := (sReal r m : ℂ)

/-- The rotation angle `arccos (1 - 2r/(r+m))` for the mean-amplitude dynamics. -/
def omega (r m : ℕ) : ℝ := Real.arccos (1 - 2 * (r : ℝ) / ((r + m : ℕ) : ℝ))

/-- The unmarked mean plus `I * sC r m` times the marked mean. -/
def fplus (x : Amps r m) : ℂ := ampAvg x.2 + Complex.I * (sC r m) * ampAvg x.1

/-- The unmarked mean minus `I * sC r m` times the marked mean. -/
def fminus (x : Amps r m) : ℂ := ampAvg x.2 - Complex.I * (sC r m) * ampAvg x.1

/-- The complex one-step multiplier `2m/(r+m) * (1 + I * sC r m) - 1` for `fplus`. -/
def wC (r m : ℕ) : ℂ :=
  (2 : ℂ) * ((m : ℂ) / (((r + m : ℕ) : ℂ))) * (1 + Complex.I * sC r m) - 1

/-- For `m ≥ 1`, the square of `sC r m` is the complex ratio `r/m`. -/
lemma sC_sq (r m : ℕ) (hm : 1 ≤ m) : (sC r m) ^ 2 = (r : ℂ) / (m : ℂ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [sC, sReal, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  rfl

/-- For `m ≥ 1`, multiplying the square of `sC r m` by `m` gives `r`. -/
lemma m_mul_sC_sq (r m : ℕ) (hm : 1 ≤ m) : (m : ℂ) * (sC r m) ^ 2 = (r : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [sC_sq r m hm]
  field_simp

/-- Replacing the total size by a complex value `N` equal to `r+m` rewrites `wC` using the
factor `2 * m * N⁻¹`. -/
lemma wC_eq' (r m : ℕ) (N : ℂ) (hN : N = ((r + m : ℕ) : ℂ)) :
    wC r m = (2 : ℂ) * (m : ℂ) * N⁻¹ * (1 + Complex.I * sC r m) - 1 := by
  rw [hN, wC, div_eq_mul_inv]
  ring

/-- For nonempty marked and unmarked sectors, a Grover step multiplies `fplus` by `wC r m`. -/
theorem fplus_step (hr : 1 ≤ r) (hm : 1 ≤ m) (x : Amps r m) :
    fplus (step x) = wC r m * fplus x := by
  have hN0 : (((r + m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsq : (m : ℂ) * (sC r m) ^ 2 = (r : ℂ) := m_mul_sC_sq r m hm
  set lb : ℂ := ampAvg x.2 with hlb
  set kb : ℂ := ampAvg x.1 with hkb
  unfold fplus
  rw [ampAvg_step_marked hr, ampAvg_step_unmarked hm]
  simp only [idxC, wC]
  rw [← hlb, ← hkb]
  field_simp [hN0]
  have hNc : (((r + m : ℕ) : ℂ)) = (r : ℂ) + (m : ℂ) := by push_cast; ring
  rw [hNc]
  linear_combination ((-2 : ℂ) * (m : ℂ) * kb * (sC r m) ^ 2) * Complex.I_sq
    + ((2 : ℂ) * kb) * hsq

/-- For nonempty marked and unmarked sectors, a Grover step multiplies `fminus` by `2m/(r+m) *
(1 - I * sC r m) - 1`. -/
theorem fminus_step (hr : 1 ≤ r) (hm : 1 ≤ m) (x : Amps r m) :
    fminus (step x) =
      ((2 : ℂ) * ((m : ℂ) / (((r + m : ℕ) : ℂ))) * (1 - Complex.I * sC r m) - 1) *
        fminus x := by
  have hN0 : (((r + m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsq : (m : ℂ) * (sC r m) ^ 2 = (r : ℂ) := m_mul_sC_sq r m hm
  set lb : ℂ := ampAvg x.2 with hlb
  set kb : ℂ := ampAvg x.1 with hkb
  unfold fminus
  rw [ampAvg_step_marked hr, ampAvg_step_unmarked hm]
  simp only [idxC]
  rw [← hlb, ← hkb]
  field_simp [hN0]
  have hNc : (((r + m : ℕ) : ℂ)) = (r : ℂ) + (m : ℂ) := by push_cast; ring
  rw [hNc]
  linear_combination ((-2 : ℂ) * (m : ℂ) * kb * (sC r m) ^ 2) * Complex.I_sq
    + ((2 : ℂ) * kb) * hsq

/-- The complex one-step multiplier `2m/(r+m) * (1 - I * sC r m) - 1` for `fminus`. -/
def wbarC (r m : ℕ) : ℂ :=
  (2 : ℂ) * ((m : ℂ) / (((r + m : ℕ) : ℂ))) * (1 - Complex.I * sC r m) - 1

/-- For nonempty marked and unmarked sectors, a Grover step multiplies `fminus` by `wbarC r m`. -/
theorem fminus_step' (hr : 1 ≤ r) (hm : 1 ≤ m) (x : Amps r m) :
    fminus (step x) = wbarC r m * fminus x := by
  simpa only [wbarC] using fminus_step (r := r) (m := m) hr hm x

/-- For positive total size, the cosine of the rotation angle is `1 - 2r/(r+m)`. -/
lemma omega_cos (r m : ℕ) (hN : 0 < r + m) :
    Real.cos (omega r m) = 1 - 2 * (r : ℝ) / ((r + m : ℕ) : ℝ) := by
  have hNpos : (0 : ℝ) < ((r + m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [omega]
  apply Real.cos_arccos
  · have hrN : (r : ℝ) ≤ ((r + m : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right r m
    have hle : 2 * (r : ℝ) / ((r + m : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]; nlinarith
    linarith
  · have hnn : 0 ≤ 2 * (r : ℝ) / ((r + m : ℕ) : ℝ) := by positivity
    linarith

/-- For positive total size, the sine of the rotation angle is `2√(r*m)/(r+m)`. -/
lemma omega_sin (r m : ℕ) (hN : 0 < r + m) :
    Real.sin (omega r m) = 2 * Real.sqrt ((r : ℝ) * (m : ℝ)) / ((r + m : ℕ) : ℝ) := by
  have hNpos : (0 : ℝ) < ((r + m : ℕ) : ℝ) := by exact_mod_cast hN
  have hN0 : ((r + m : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  rw [omega, Real.sin_arccos]
  have hNm : ((r + m : ℕ) : ℝ) = (r : ℝ) + (m : ℝ) := by push_cast; ring
  have hNm0 : (r : ℝ) + (m : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (r : ℝ) + (m : ℝ) := by rw [← hNm]; exact_mod_cast hN
    exact ne_of_gt hpos
  have hquad : 1 - (1 - 2 * (r : ℝ) / ((r + m : ℕ) : ℝ)) ^ 2
      = 4 * (r : ℝ) * (m : ℝ) / ((r + m : ℕ) : ℝ) ^ 2 := by
    rw [hNm]
    have ht : 1 - (1 - 2 * (r : ℝ) / ((r : ℝ) + (m : ℝ))) ^ 2
        = (2 * (r : ℝ) / ((r : ℝ) + (m : ℝ))) *
            (2 - 2 * (r : ℝ) / ((r : ℝ) + (m : ℝ))) := by ring
    rw [ht]
    have h2 : 2 - 2 * (r : ℝ) / ((r : ℝ) + (m : ℝ))
        = (2 * ((r : ℝ) + (m : ℝ)) - 2 * (r : ℝ)) / ((r : ℝ) + (m : ℝ)) := by
      field_simp [hNm0]
    rw [h2]
    field_simp [hNm0]
    ring
  rw [hquad]
  have hrm : (0 : ℝ) ≤ (r : ℝ) * (m : ℝ) := by positivity
  have hsq : 4 * (r : ℝ) * (m : ℝ) / ((r + m : ℕ) : ℝ) ^ 2
      = (2 * Real.sqrt ((r : ℝ) * (m : ℝ)) / ((r + m : ℕ) : ℝ)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hrm]; field_simp; ring
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- For positive `r` and `m`, the product `2 * sReal r m * √(m/(4r))` equals one. -/
lemma two_s_sqrt (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    2 * sReal r m * Real.sqrt ((m : ℝ) / (4 * (r : ℝ))) = 1 := by
  have hp1 : (0 : ℝ) ≤ (r : ℝ) / (m : ℝ) := by positivity
  have hp2 : (0 : ℝ) ≤ (m : ℝ) / (4 * (r : ℝ)) := by positivity
  have hmul : Real.sqrt ((r : ℝ) / (m : ℝ)) * Real.sqrt ((m : ℝ) / (4 * (r : ℝ))) = 1 / 2 := by
    rw [← Real.sqrt_mul hp1 ((m : ℝ) / (4 * (r : ℝ)))]
    have hprod : ((r : ℝ) / (m : ℝ)) * ((m : ℝ) / (4 * (r : ℝ))) = 1 / 4 := by
      field_simp
    rw [hprod, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [sReal]
  linear_combination (2 : ℝ) * hmul

/-- For positive total size, the cosine of the rotation angle can be written as `2m/(r+m) - 1`. -/
lemma cos_omega_eq (r m : ℕ) (hN : 0 < r + m) :
    Real.cos (omega r m) = 2 * (m : ℝ) / ((r + m : ℕ) : ℝ) - 1 := by
  have hNm : ((r + m : ℕ) : ℝ) = (r : ℝ) + (m : ℝ) := by push_cast; ring
  have hNm0 : (r : ℝ) + (m : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (r : ℝ) + (m : ℝ) := by rw [← hNm]; exact_mod_cast hN
    exact ne_of_gt hpos
  rw [omega_cos r m hN, hNm]
  have h2 : (1:ℝ) - 2*(r:ℝ)/((r:ℝ)+(m:ℝ))
      = (((r:ℝ)+(m:ℝ)) - 2*(r:ℝ))/((r:ℝ)+(m:ℝ)) := by
    field_simp [hNm0]
  have h3 : (2:ℝ)*(m:ℝ)/((r:ℝ)+(m:ℝ)) - 1
      = (2*(m:ℝ) - ((r:ℝ)+(m:ℝ)))/((r:ℝ)+(m:ℝ)) := by
    field_simp [hNm0]
  rw [h2, h3]
  congr 1
  ring

/-- For `m ≥ 1`, the sine of the rotation angle is `2 * m * sReal r m / (r+m)`. -/
lemma sin_omega_eq (r m : ℕ) (hm : 1 ≤ m) :
    Real.sin (omega r m) = 2 * (m : ℝ) * sReal r m / ((r + m : ℕ) : ℝ) := by
  have hN : 0 < r + m := by omega
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmpos : (0 : ℝ) ≤ (m : ℝ) := by positivity
  rw [omega_sin r m hN]
  have hsm : (m : ℝ) * sReal r m = Real.sqrt ((r : ℝ) * (m : ℝ)) := by
    have hp1 : (0 : ℝ) ≤ (r : ℝ) / (m : ℝ) := by positivity
    rw [sReal, mul_comm]
    rw [show Real.sqrt ((r : ℝ) / (m : ℝ)) * (m : ℝ)
        = Real.sqrt ((r : ℝ) / (m : ℝ)) * Real.sqrt ((m : ℝ) * (m : ℝ))
        from by rw [Real.sqrt_mul_self hmpos]]
    rw [← Real.sqrt_mul hp1 ((m : ℝ) * (m : ℝ))]
    congr 1
    field_simp
  rw [← hsm]; ring

/-- For `m ≥ 1`, the multiplier `wC r m` equals `exp (I * omega r m)`. -/
lemma wC_eq_exp (r m : ℕ) (hm : 1 ≤ m) :
    wC r m = Complex.exp ((omega r m : ℂ) * Complex.I) := by
  have hN : 0 < r + m := by omega
  have hN0 : (((r + m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.exp_ofReal_mul_I, cos_omega_eq r m hN, sin_omega_eq r m hm]
  unfold wC sC
  push_cast
  field_simp [hN0]
  ring

/-- For `m ≥ 1`, the multiplier `wbarC r m` equals `exp (-I * omega r m)`. -/
lemma wbarC_eq_exp (r m : ℕ) (hm : 1 ≤ m) :
    wbarC r m = Complex.exp (-((omega r m : ℂ) * Complex.I)) := by
  have hN : 0 < r + m := by omega
  have hN0 : (((r + m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show -((omega r m : ℂ) * Complex.I) = (((-(omega r m)) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    cos_omega_eq r m hN, sin_omega_eq r m hm]
  unfold wbarC sC
  push_cast
  field_simp [hN0]
  ring

/-- The positive-phase rotation factor `exp (I * t * omega r m)`. -/
def rot (r m : ℕ) (t : ℕ) : ℂ := Complex.exp ((t : ℂ) * (omega r m : ℂ) * Complex.I)

/-- The negative-phase rotation factor `exp (-I * t * omega r m)`. -/
def rotNeg (r m : ℕ) (t : ℕ) : ℂ :=
  Complex.exp (-((t : ℂ) * (omega r m : ℂ) * Complex.I))

/-- For `m ≥ 1`, the rotation factor at time `t` is the `t`th power of `wC r m`. -/
lemma rot_eq_pow (r m : ℕ) (hm : 1 ≤ m) (t : ℕ) : rot r m t = (wC r m) ^ t := by
  unfold rot
  rw [wC_eq_exp r m hm, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- For `m ≥ 1`, the negative rotation factor at time `t` is the `t`th power of `wbarC r m`. -/
lemma rotNeg_eq_pow (r m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    rotNeg r m t = (wbarC r m) ^ t := by
  unfold rotNeg
  rw [wbarC_eq_exp r m hm, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- For nonempty marked and unmarked sectors, `fplus` at time `t` equals its initial value
multiplied by the `t`th power of `wC r m`. -/
lemma fplus_orbit (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    fplus (orbit x0 t) = (wC r m) ^ t * fplus x0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [orbit_succ, fplus_step hr hm, ih, pow_succ']
    ring

/-- For nonempty marked and unmarked sectors, `fminus` at time `t` equals its initial value
multiplied by the `t`th power of `wbarC r m`. -/
lemma fminus_orbit (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    fminus (orbit x0 t) = (wbarC r m) ^ t * fminus x0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [orbit_succ, fminus_step' hr hm, ih, pow_succ']
    ring

/-- For nonempty marked and unmarked sectors, `fplus` evolves by the rotation factor `rot r m
t`. -/
lemma fplus_orbit_exp (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    fplus (orbit x0 t) = rot r m t * fplus x0 := by
  rw [fplus_orbit hr hm, ← rot_eq_pow r m hm t]

/-- For nonempty marked and unmarked sectors, `fminus` evolves by the negative rotation factor
`rotNeg r m t`. -/
lemma fminus_orbit_exp (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    fminus (orbit x0 t) = rotNeg r m t * fminus x0 := by
  rw [fminus_orbit hr hm, ← rotNeg_eq_pow r m hm t]

/-- Adding `fplus` and `fminus` gives twice the unmarked mean. -/
lemma fplus_add (x : Amps r m) : fplus x + fminus x = 2 * ampAvg x.2 := by
  simp only [fplus, fminus]; ring

/-- Subtracting `fminus` from `fplus` gives `2 * I * sC r m` times the marked mean. -/
lemma fplus_sub (x : Amps r m) :
    fplus x - fminus x = 2 * Complex.I * sC r m * ampAvg x.1 := by
  simp only [fplus, fminus]; ring

/-- The coefficient `-I * √(m/(4r))` used to recover the marked mean from the rotating
components. -/
def kappaC (r m : ℕ) : ℂ := -Complex.I * (Real.sqrt ((m : ℝ) / (4 * (r : ℝ))) : ℂ)

/-- For positive `r` and `m`, multiplying `kappaC r m` by `2 * I * sC r m` gives one. -/
lemma kappaC_mul (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    kappaC r m * (2 * Complex.I * sC r m) = 1 := by
  have h := two_s_sqrt r m hr hm
  have hmain : (-Complex.I * ((Real.sqrt ((m : ℝ) / (4 * (r : ℝ)))) : ℂ)) *
      (2 * Complex.I * ((sReal r m) : ℂ))
      = ((2 * sReal r m * Real.sqrt ((m : ℝ) / (4 * (r : ℝ))) : ℝ) : ℂ) := by
    have hstep : (-Complex.I * ((Real.sqrt ((m : ℝ) / (4 * (r : ℝ)))) : ℂ)) *
        (2 * Complex.I * ((sReal r m) : ℂ))
        = -(2 * ((Real.sqrt ((m : ℝ) / (4 * (r : ℝ)))) : ℂ) * ((sReal r m) : ℂ)) *
            (Complex.I * Complex.I) := by ring
    rw [hstep, Complex.I_mul_I]
    push_cast
    ring
  unfold kappaC sC
  rw [hmain, h]
  norm_num

/-- For `m ≥ 1`, the multiplier `wC r m` has norm one. -/
lemma norm_wC (r m : ℕ) (hm : 1 ≤ m) : ‖wC r m‖ = 1 := by
  rw [wC_eq_exp r m hm]
  exact Complex.norm_exp_ofReal_mul_I (omega r m)

/-- For nonempty marked and unmarked sectors, the norm of `fplus` is constant along the Grover
orbit. -/
lemma fplus_norm_invariant (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    ‖fplus (orbit x0 t)‖ = ‖fplus x0‖ := by
  rw [fplus_orbit hr hm, norm_mul, norm_pow, norm_wC r m hm, one_pow, one_mul]

/-- For `m ≥ 1`, the multiplier `wbarC r m` has norm one. -/
lemma norm_wbarC (r m : ℕ) (hm : 1 ≤ m) : ‖wbarC r m‖ = 1 := by
  rw [wbarC_eq_exp r m hm, show -((omega r m : ℂ) * Complex.I)
    = (((-(omega r m)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-omega r m)

/-- For nonempty marked and unmarked sectors, the norm of `fminus` is constant along the Grover
orbit. -/
lemma fminus_norm_invariant (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    ‖fminus (orbit x0 t)‖ = ‖fminus x0‖ := by
  rw [fminus_orbit hr hm, norm_mul, norm_pow, norm_wbarC r m hm, one_pow, one_mul]

/-- For nonempty marked and unmarked sectors, the unmarked mean is half the sum of the
positively and negatively rotating initial components. -/
lemma lbar_closed (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    lbar x0 t = (1 / 2) * (rot r m t * fplus x0 + rotNeg r m t * fminus x0) := by
  have h := fplus_add (orbit x0 t)
  have hl : ampAvg (orbit x0 t).2
      = (1 / 2) * (fplus (orbit x0 t) + fminus (orbit x0 t)) := by
    rw [h]; ring
  rw [lbar, hl, fplus_orbit_exp hr hm, fminus_orbit_exp hr hm]

/-- For nonempty marked and unmarked sectors, the marked mean is `kappaC r m` times the
difference of the positively and negatively rotating initial components. -/
lemma kbar_closed (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    kbar x0 t = kappaC r m * (rot r m t * fplus x0 - rotNeg r m t * fminus x0) := by
  have hsub := fplus_sub (orbit x0 t)
  have hk : ampAvg (orbit x0 t).1
      = kappaC r m * (fplus (orbit x0 t) - fminus (orbit x0 t)) := by
    rw [hsub, ← mul_assoc, kappaC_mul r m hr hm, one_mul]
  rw [kbar, hk, fplus_orbit_exp hr hm, fminus_orbit_exp hr hm]

/-- For a nonempty marked sector, each marked amplitude's deviation from the marked mean is
constant along the orbit. -/
lemma marked_deviation_invariant (hr : 1 ≤ r) (x0 : Amps r m) (t : ℕ) (i : Fin r) :
    (orbit x0 t).1 i - kbar x0 t = x0.1 i - kbar x0 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [orbit_succ, kbar_succ hr]
    simp only [step]
    rw [← ih]
    ring

/-- For a nonempty unmarked sector, each unmarked amplitude's deviation from the unmarked mean
is its initial deviation multiplied by `(-1)^t`. -/
lemma unmarked_deviation (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) (j : Fin m) :
    (orbit x0 t).2 j - lbar x0 t = (-1 : ℂ) ^ t * (x0.2 j - lbar x0 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [orbit_succ, lbar_succ hm]
    simp only [step]
    rw [show (-1 : ℂ) ^ (t + 1) = -1 * (-1 : ℂ) ^ t by rw [pow_succ]; ring]
    linear_combination -ih

/-- For a nonempty marked sector, each amplitude equals the current marked mean plus its initial
deviation from that mean. -/
lemma marked_amplitude_eq (hr : 1 ≤ r) (x0 : Amps r m) (t : ℕ) (i : Fin r) :
    (orbit x0 t).1 i = kbar x0 t + (x0.1 i - kbar x0 0) := by
  have h := marked_deviation_invariant hr x0 t i
  linear_combination h

/-- For a nonempty unmarked sector, each amplitude equals the current unmarked mean plus its
initial deviation multiplied by `(-1)^t`. -/
lemma unmarked_amplitude_eq (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) (j : Fin m) :
    (orbit x0 t).2 j = lbar x0 t + (-1 : ℂ) ^ t * (x0.2 j - lbar x0 0) := by
  have h := unmarked_deviation hm x0 t j
  linear_combination h

/-- For nonempty marked and unmarked sectors, the orbit satisfies the exact amplitude and mean
formulas, rotating-component formulas, and component-norm invariants [BihamEtAl1999]. -/
theorem source_exact_dynamics (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) :
    (∀ t i, (orbit x0 t).1 i = kbar x0 t + (x0.1 i - kbar x0 0)) ∧
    (∀ t j, (orbit x0 t).2 j = lbar x0 t + (-1 : ℂ) ^ t * (x0.2 j - lbar x0 0)) ∧
    (∀ t, fplus (orbit x0 t) = rot r m t * fplus x0) ∧
    (∀ t, fminus (orbit x0 t) = rotNeg r m t * fminus x0) ∧
    (∀ t, ‖fplus (orbit x0 t)‖ = ‖fplus x0‖) ∧
    (∀ t, ‖fminus (orbit x0 t)‖ = ‖fminus x0‖) ∧
    (∀ t, kbar x0 t =
      kappaC r m * (rot r m t * fplus x0 - rotNeg r m t * fminus x0)) ∧
    (∀ t, lbar x0 t =
      (1 / 2) * (rot r m t * fplus x0 + rotNeg r m t * fminus x0)) := by
  exact ⟨fun t i => marked_amplitude_eq hr x0 t i,
    fun t j => unmarked_amplitude_eq hm x0 t j,
    fun t => fplus_orbit_exp hr hm x0 t,
    fun t => fminus_orbit_exp hr hm x0 t,
    fun t => fplus_norm_invariant hr hm x0 t,
    fun t => fminus_norm_invariant hr hm x0 t,
    fun t => kbar_closed hr hm x0 t,
    fun t => lbar_closed hr hm x0 t⟩

/-- The sum of the squared norms of the marked amplitudes. -/
def probMarked (x : Amps r m) : ℝ := ∑ i, Complex.normSq (x.1 i)

/-- The sum of the squared norms of the unmarked amplitudes. -/
def probUnmarked (x : Amps r m) : ℝ := ∑ j, Complex.normSq (x.2 j)

/-- The sum of squared deviations of the initial marked amplitudes from their mean. -/
def varMarked (x0 : Amps r m) : ℝ := ∑ i, Complex.normSq (x0.1 i - kbar x0 0)

/-- Complex conjugation written with `star` agrees with the complex star ring endomorphism. -/
lemma star_eq_starRingEnd (z : ℂ) : star z = (starRingEnd ℂ) z := rfl

/-- The complex oscillation coefficient `(m/2) * fplus x0 * star (fminus x0)`. -/
def hC (x0 : Amps r m) : ℂ := (((m : ℝ) / 2 : ℝ) : ℂ) * (fplus x0 * star (fminus x0))

/-- The norm of the complex oscillation coefficient `hC x0`. -/
def DeltaP (x0 : Amps r m) : ℝ := ‖hC x0‖

/-- The sum of the initial marked squared deviations and `m/4` times the squared norms of the
two rotating components. -/
def Pav (x0 : Amps r m) : ℝ :=
  varMarked x0 + ((m : ℝ) / 4) * (Complex.normSq (fplus x0) + Complex.normSq (fminus x0))

/-- The upper-envelope expression `Pav x0 + DeltaP x0`. -/
def Pmax (x0 : Amps r m) : ℝ := Pav x0 + DeltaP x0

/-- The oscillation amplitude `DeltaP x0` is nonnegative. -/
lemma DeltaP_nonneg (x0 : Amps r m) : 0 ≤ DeltaP x0 := norm_nonneg _

/-- The upper-envelope expression equals the baseline plus the oscillation amplitude. -/
lemma Pmax_eq (x0 : Amps r m) : Pmax x0 = Pav x0 + DeltaP x0 := rfl

/-- The oscillation amplitude is at most the baseline marked-mass expression [BihamEtAl1999]. -/
lemma DeltaP_le_Pav (x0 : Amps r m) : DeltaP x0 ≤ Pav x0 := by
  have hm2 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have hDP : DeltaP x0 = ((m : ℝ) / 2) * (‖fplus x0‖ * ‖fminus x0‖) := by
    unfold DeltaP hC
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star,
      abs_of_nonneg hm2]
  have hvar : 0 ≤ varMarked x0 := by
    unfold varMarked
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hPav : Pav x0
      = varMarked x0 + ((m : ℝ) / 4) * (‖fplus x0‖ ^ 2 + ‖fminus x0‖ ^ 2) := by
    unfold Pav
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hkey : ((m : ℝ) / 2) * (‖fplus x0‖ * ‖fminus x0‖)
      ≤ ((m : ℝ) / 4) * (‖fplus x0‖ ^ 2 + ‖fminus x0‖ ^ 2) := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) / 4)
      (sq_nonneg (‖fplus x0‖ - ‖fminus x0‖))]
  rw [hDP, hPav]
  linarith

/-- A cosine model with nonnegative amplitude is bounded above by its baseline plus that
amplitude. -/
lemma cos_model_le_Pmax (Pav₀ ΔP₀ θ : ℝ) (hΔ0 : 0 ≤ ΔP₀) :
    Pav₀ - ΔP₀ * Real.cos θ ≤ Pav₀ + ΔP₀ := by
  have h : -ΔP₀ ≤ ΔP₀ * Real.cos θ := by
    have := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hΔ0
    simpa using this
  linarith

/-- For a nonempty complex vector, the sum of squared norms equals the sum of squared deviations
from the mean plus the length times the squared norm of the mean. -/
lemma sum_normSq_centered {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℂ) :
    (∑ i, Complex.normSq (v i)) =
      (∑ i, Complex.normSq (v i - ampAvg v)) + (n : ℝ) * Complex.normSq (ampAvg v) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set c : ℂ := ampAvg v with hc
  have hsum0 : ∑ i, (v i - c) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hc, ampAvg]
    field_simp
    ring
  have hcross : ∑ i, ((v i - c) * (starRingEnd ℂ) c).re = 0 := by
    have hzero : ∑ i : Fin n, (v i - c) * (starRingEnd ℂ) c = 0 := by
      have hz := Finset.sum_mul (Finset.univ : Finset (Fin n)) (fun i => v i - c)
        ((starRingEnd ℂ) c)
      rw [← hz]
      rw [show (∑ i ∈ (Finset.univ : Finset (Fin n)), (v i - c)) = 0 from by
        simpa using hsum0]
      simp
    calc ∑ i, ((v i - c) * (starRingEnd ℂ) c).re
        = (∑ i, (v i - c) * (starRingEnd ℂ) c).re := by simp
      _ = 0 := by rw [hzero, Complex.zero_re]
  calc (∑ i, Complex.normSq (v i))
      = ∑ i, (Complex.normSq (v i - c) + Complex.normSq c
          + 2 * ((v i - c) * (starRingEnd ℂ) c).re) := by
        apply Finset.sum_congr rfl
        intro i _
        have hv : v i = (v i - c) + c := by ring
        conv_lhs => rw [hv]
        rw [Complex.normSq_add]
    _ = (∑ i, Complex.normSq (v i - c)) + (n : ℝ) * Complex.normSq c := by
        have h1 : (∑ i : Fin n, Complex.normSq c) = (n : ℝ) * Complex.normSq c := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h2 : (∑ i : Fin n, 2 * ((v i - c) * (starRingEnd ℂ) c).re) = 0 := by
          have hz := Finset.mul_sum (Finset.univ : Finset (Fin n))
            (fun i => ((v i - c) * (starRingEnd ℂ) c).re) (2 : ℝ)
          rw [← hz, hcross, mul_zero]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]
        ring

/-- For a nonempty marked sector, the marked mass at time `t` is the initial marked
squared-deviation sum plus `r` times the squared norm of the current marked mean. -/
lemma probMarked_orbit (hr : 1 ≤ r) (x0 : Amps r m) (t : ℕ) :
    probMarked (orbit x0 t) = varMarked x0 + (r : ℝ) * Complex.normSq (kbar x0 t) := by
  unfold probMarked varMarked
  have h := sum_normSq_centered (n := r) hr (fun i => (orbit x0 t).1 i)
  rw [h]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change Complex.normSq ((orbit x0 t).1 i - kbar x0 t)
      = Complex.normSq (x0.1 i - kbar x0 0)
    rw [marked_deviation_invariant hr]

/-- The squared norm of the complex exponential of a purely imaginary real multiple is one. -/
lemma normSq_exp_I (x : ℝ) :
    Complex.normSq (Complex.exp ((x : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add]
  nlinarith [Real.cos_sq_add_sin_sq x]

/-- The positive-phase rotation factor has squared norm one. -/
lemma normSq_rot (r m : ℕ) (t : ℕ) : Complex.normSq (rot r m t) = 1 := by
  have h : rot r m t = Complex.exp ((((omega r m * (t : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    unfold rot
    congr 1
    push_cast
    ring
  rw [h, normSq_exp_I]

/-- The negative-phase rotation factor has squared norm one. -/
lemma normSq_rotNeg (r m : ℕ) (t : ℕ) : Complex.normSq (rotNeg r m t) = 1 := by
  have h : rotNeg r m t
      = Complex.exp ((((-(omega r m * (t : ℝ))) : ℝ) : ℂ) * Complex.I) := by
    unfold rotNeg
    congr 1
    push_cast
    ring
  rw [h, normSq_exp_I]

/-- The positive-phase rotation factor has norm one. -/
lemma norm_rot (r m : ℕ) (t : ℕ) : ‖rot r m t‖ = 1 := by
  have h : rot r m t = Complex.exp ((((omega r m * (t : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    unfold rot
    congr 1
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The squared norm of `kappaC r m` equals the totalized real quotient `m/(4r)`. -/
lemma normSq_kappaC (r m : ℕ) :
    Complex.normSq (kappaC r m) = (m : ℝ) / (4 * (r : ℝ)) := by
  unfold kappaC
  rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, one_mul,
    Complex.normSq_ofReal]
  rw [show Real.sqrt ((m : ℝ) / (4 * (r : ℝ))) * Real.sqrt ((m : ℝ) / (4 * (r : ℝ)))
      = Real.sqrt ((m : ℝ) / (4 * (r : ℝ))) ^ 2 by ring]
  rw [Real.sq_sqrt (by positivity)]

/-- For positive `r` and `m`, the marked-mean mass splits into `m/4` times the two rotating
squared norms minus `m/2` times their real cross term. -/
lemma kbar_normSq_decomp (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    (r : ℝ) * Complex.normSq (kbar x0 t)
      = ((m : ℝ) / 4) *
          (Complex.normSq (rot r m t * fplus x0) +
           Complex.normSq (rotNeg r m t * fminus x0))
        - ((m : ℝ) / 2) *
          (((rot r m t * fplus x0) * star (rotNeg r m t * fminus x0)).re) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    positivity
  rw [kbar_closed hr hm x0 t, Complex.normSq_mul, normSq_kappaC, Complex.normSq_sub]
  field_simp
  simp only [star_eq_starRingEnd]
  ring

/-- The product of the positive rotation and the conjugate negative rotation equals the positive
rotation at twice the time. -/
lemma rot_mul_star_rotNeg (r m : ℕ) (t : ℕ) :
    rot r m t * star (rotNeg r m t) = rot r m (2 * t) := by
  unfold rot rotNeg
  change Complex.exp ((t : ℂ) * (omega r m : ℂ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp (-((t : ℂ) * (omega r m : ℂ) * Complex.I)))
    = Complex.exp (((2 * t : ℕ) : ℂ) * (omega r m : ℂ) * Complex.I)
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, map_natCast, Complex.conj_ofReal]
  push_cast
  ring

/-- The cross term of the two rotating components is the doubled-time rotation times `fplus x0 *
star (fminus x0)`. -/
lemma cross_term_eq (r m : ℕ) (t : ℕ) (x0 : Amps r m) :
    (rot r m t * fplus x0) * star (rotNeg r m t * fminus x0)
      = rot r m (2 * t) * (fplus x0 * star (fminus x0)) := by
  calc (rot r m t * fplus x0) * star (rotNeg r m t * fminus x0)
      = (rot r m t * star (rotNeg r m t)) * (fplus x0 * star (fminus x0)) := by
        rw [star_mul]
        ring
    _ = rot r m (2 * t) * (fplus x0 * star (fminus x0)) := by
        rw [rot_mul_star_rotNeg]

/-- The real part of the rotated coefficient `hC x0` is `m/2` times the real part of the rotated
component product. -/
lemma hC_re_rot (r m : ℕ) (t : ℕ) (x0 : Amps r m) :
    (rot r m (2 * t) * hC x0).re
      = ((m : ℝ) / 2) *
          ((rot r m (2 * t) * (fplus x0 * star (fminus x0))).re) := by
  unfold hC
  rw [← mul_assoc, mul_comm (rot r m (2 * t)) ((((m : ℝ) / 2 : ℝ) : ℂ)), mul_assoc,
    Complex.re_ofReal_mul]

/-- For nonempty marked and unmarked sectors, the marked mass equals `Pav x0` minus the real
part of `rot r m (2*t) * hC x0`. -/
lemma probMarked_orbit_eq (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) (t : ℕ) :
    probMarked (orbit x0 t) = Pav x0 - (rot r m (2 * t) * hC x0).re := by
  rw [probMarked_orbit hr x0 t, kbar_normSq_decomp hr hm x0 t]
  have hA : Complex.normSq (rot r m t * fplus x0) = Complex.normSq (fplus x0) := by
    rw [Complex.normSq_mul, normSq_rot, one_mul]
  have hB : Complex.normSq (rotNeg r m t * fminus x0) = Complex.normSq (fminus x0) := by
    rw [Complex.normSq_mul, normSq_rotNeg, one_mul]
  rw [hA, hB, cross_term_eq r m t x0, hC_re_rot r m t x0]
  unfold Pav
  ring

/-- The real part of the doubled-time rotated coefficient equals `DeltaP x0` times the cosine
with phase offset `(hC x0).arg / 2`. -/
lemma re_rot_hC_cos (r m : ℕ) (x0 : Amps r m) (t : ℕ) :
    (rot r m (2 * t) * hC x0).re
      = DeltaP x0 * Real.cos (2 * (omega r m * (t : ℝ) + (hC x0).arg / 2)) := by
  have hrot : rot r m (2 * t)
      = Complex.exp ((((2 * (omega r m * (t : ℝ))) : ℝ) : ℂ) * Complex.I) := by
    unfold rot
    congr 1
    push_cast
    ring
  rw [hrot, Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add]
  rw [← Complex.norm_mul_cos_arg (hC x0), ← Complex.norm_mul_sin_arg (hC x0)]
  unfold DeltaP
  have hang : 2 * (omega r m * (t : ℝ) + (hC x0).arg / 2)
      = 2 * (omega r m * (t : ℝ)) + (hC x0).arg := by ring
  rw [hang, Real.cos_add]
  ring

/-- For nonempty marked and unmarked sectors, the marked mass has a cosine representation with
baseline `Pav` and amplitude `DeltaP` and is bounded at every natural time by `Pmax = Pav +
DeltaP` [BihamEtAl1999]. -/
theorem source_success_probability (hr : 1 ≤ r) (hm : 1 ≤ m) (x0 : Amps r m) :
    (Pmax x0 = Pav x0 + DeltaP x0) ∧
    (∀ t, probMarked (orbit x0 t) ≤ Pmax x0) ∧
    (∃ φ : ℝ, ∀ t, probMarked (orbit x0 t)
      = Pav x0 - DeltaP x0 * Real.cos (2 * (omega r m * (t : ℝ) + φ))) := by
  refine ⟨Pmax_eq x0, ?_, ⟨(hC x0).arg / 2, ?_⟩⟩
  · intro t
    rw [probMarked_orbit_eq hr hm x0 t, Pmax_eq]
    have hz : ‖rot r m (2 * t) * hC x0‖ = DeltaP x0 := by
      rw [norm_mul, norm_rot, one_mul]
      rfl
    have hge : -(DeltaP x0) ≤ (rot r m (2 * t) * hC x0).re := by
      rw [← hz]
      exact (abs_le.mp (Complex.abs_re_le_norm _)).1
    linarith
  · intro t
    rw [probMarked_orbit_eq hr hm x0 t, re_rot_hC_cos r m x0 t]

end Qatlib.Papers.GroverArbAmp98.MainResults.Dynamics
