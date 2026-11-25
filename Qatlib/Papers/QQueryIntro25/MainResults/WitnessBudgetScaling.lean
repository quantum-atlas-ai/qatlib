/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgram

@[expose] public section

/-!
# Rescaling a source dual witness to the geometric-mean budget

Lemma 65 of [Hamoudi, 2025][Hamoudi2025QueryIntro] takes a span-program dual witness `v` whose
fiber energies `∑_{j,k} ‖v x j k‖²` are bounded by `T0` on the false inputs and by `T1` on the
true inputs, and rescales it so that both sides share the budget `√(T0 * T1)`. Multiplying the
false-side entries by `(T1 / T0)^(1/4)` and the true-side entries by `(T0 / T1)^(1/4)` scales the
false-side energies by `√(T1 / T0)` and the true-side energies by `√(T0 / T1)`. Since the two
scale factors multiply to one, every difference-coordinate inner product sum is unchanged, so the
rescaled family is again a `Qatlib.Concepts.QueryComplexity.Reflections.SourceDualFeasible`
witness, now with the symmetric budget `√(T0 * T1)`.

## Main statements

* `fiberEnergy`: the squared Frobenius energy of one witness fiber.
* `fiberScaledWitness`: the rescaled witness family.
* `sourceDualFeasible_fiberScaled`: source dual feasibility of the rescaled family with budget
  `√(T0 * T1)`.
* `sourceDualFeasible_fiberMax`: the specialization in which `T0` and `T1` are the maximal fiber
  energies of the two sides.

## Boundary

The construction requires `0 < T0` and `0 < T1`; the two scale factors are undefined otherwise.
With both sides nonempty and one side of zero energy no witness of this shape can have unit
overlap, so no degenerate substitute is provided on that side. When one side carries no input the
overlap constraint is vacuous, and `sourceDualFeasible_zero` records that the zero witness is
feasible with budget zero. Nothing is claimed about optimality of the budget `√(T0 * T1)`.

## References

* [Hamoudi, 2025][Hamoudi2025QueryIntro], Lemma 65.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QQueryIntro25.MainResults.WitnessBudgetScaling

open Qatlib.Concepts.QueryComplexity.Reflections

/-- The fourth root of a real number, written as a nested square root so that no real power
notation is needed. -/
def fourthRoot (r : ℝ) : ℝ := Real.sqrt (Real.sqrt r)

/-- The fourth root is nonnegative. -/
theorem fourthRoot_nonneg (r : ℝ) : 0 ≤ fourthRoot r := Real.sqrt_nonneg _

/-- Squaring the fourth root of a number returns its square root. -/
theorem fourthRoot_sq (r : ℝ) : fourthRoot r ^ 2 = Real.sqrt r :=
  Real.sq_sqrt (Real.sqrt_nonneg r)

/-- The fourth power of the fourth root of a nonnegative number is that number. -/
theorem fourthRoot_pow_four {r : ℝ} (hr : 0 ≤ r) : fourthRoot r ^ 4 = r := by
  have hsq := fourthRoot_sq r
  have hfour : fourthRoot r ^ 4 = (fourthRoot r ^ 2) ^ 2 := by ring
  rw [hfour, hsq, Real.sq_sqrt hr]

/-- The fourth roots of two reciprocal positive ratios multiply to one. -/
theorem fourthRoot_div_mul_fourthRoot_div {T0 T1 : ℝ} (h0 : 0 < T0) (h1 : 0 < T1) :
    fourthRoot (T1 / T0) * fourthRoot (T0 / T1) = 1 := by
  have hA : 0 ≤ T1 / T0 := le_of_lt (div_pos h1 h0)
  have hsqrt : Real.sqrt (T1 / T0) * Real.sqrt (T0 / T1) = 1 := by
    rw [← Real.sqrt_mul hA]
    have hone : T1 / T0 * (T0 / T1) = 1 := by field_simp
    rw [hone, Real.sqrt_one]
  calc fourthRoot (T1 / T0) * fourthRoot (T0 / T1)
      = Real.sqrt (Real.sqrt (T1 / T0) * Real.sqrt (T0 / T1)) := by
        rw [fourthRoot, fourthRoot, ← Real.sqrt_mul (Real.sqrt_nonneg (T1 / T0))]
    _ = 1 := by rw [hsqrt, Real.sqrt_one]

section EnergyAlgebra

variable {N M : ℕ}

/-- Multiplying a matrix by a nonnegative real multiplies its squared Frobenius energy by the
square of that real. -/
theorem sum_sq_norm_const_mul (c : ℝ) (hc : 0 ≤ c) (w : Fin N → Fin M → ℂ) :
    (∑ j, ∑ k, ‖(c : ℂ) * w j k‖ ^ 2) = c ^ 2 * ∑ j, ∑ k, ‖w j k‖ ^ 2 := by
  have hpt : ∀ j k, ‖(c : ℂ) * w j k‖ ^ 2 = c ^ 2 * ‖w j k‖ ^ 2 := by
    intro j k
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, mul_pow]
  simp only [hpt, Finset.mul_sum]

/-- Scaling one fiber by a nonnegative real scales its energy by the square of that real. -/
theorem sum_sq_norm_smul (c : ℝ) (hc : 0 ≤ c) (w : Fin N → Fin M → ℂ) :
    (∑ j, ∑ k, ‖((c : ℂ) • w) j k‖ ^ 2) = c ^ 2 * ∑ j, ∑ k, ‖w j k‖ ^ 2 := by
  simp only [Pi.smul_apply, smul_eq_mul]
  exact sum_sq_norm_const_mul c hc w

/-- Scaling both arguments of the complex inner product by real numbers multiplies the value by
their product. -/
theorem inner_const_mul (c d : ℝ) (u w : Fin M → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner ((c : ℂ) • u) ((d : ℂ) • w)
      = ((c * d : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner u w := by
  have hstar : star (c : ℂ) = (c : ℂ) := by simp
  have hpt : ∀ k, star (((c : ℂ) • u) k) * (((d : ℂ) • w) k)
      = ((c * d : ℝ) : ℂ) * (star (u k) * w k) := by
    intro k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, star_mul, hstar]
    push_cast
    ring
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.star_apply]
  exact hpt k

/-- The false-side scale factor sends the budget `T0` to the geometric mean `√(T0 * T1)`. -/
theorem sqrt_div_false_mul {T0 T1 : ℝ} (h0 : 0 < T0) (h1 : 0 < T1) :
    Real.sqrt (T1 / T0) * T0 = Real.sqrt (T0 * T1) := by
  have hT : Real.sqrt (T1 / T0) * T0 = Real.sqrt (T1 / T0) * Real.sqrt (T0 ^ 2) := by
    rw [Real.sqrt_sq (le_of_lt h0)]
  rw [hT, ← Real.sqrt_mul (le_of_lt (div_pos h1 h0))]
  congr 1
  field_simp

/-- The true-side scale factor sends the budget `T1` to the geometric mean `√(T0 * T1)`. -/
theorem sqrt_div_true_mul {T0 T1 : ℝ} (h0 : 0 < T0) (h1 : 0 < T1) :
    Real.sqrt (T0 / T1) * T1 = Real.sqrt (T0 * T1) := by
  have hT : Real.sqrt (T0 / T1) * T1 = Real.sqrt (T0 / T1) * Real.sqrt (T1 ^ 2) := by
    rw [Real.sqrt_sq (le_of_lt h1)]
  rw [hT, ← Real.sqrt_mul (le_of_lt (div_pos h0 h1))]
  congr 1
  field_simp

end EnergyAlgebra

variable {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}

/-- The squared Frobenius energy `∑_{j,k} ‖v x j k‖²` of the witness fiber at the input `x`. -/
def fiberEnergy (v : X → Fin n → Fin m → ℂ) (x : X) : ℝ :=
  ∑ j, ∑ k, ‖v x j k‖ ^ 2

/-- The witness family rescaled to the geometric-mean budget: false-side inputs are multiplied by
`(T1 / T0)^(1/4)` and true-side inputs by `(T0 / T1)^(1/4)`. -/
def fiberScaledWitness (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (T0 T1 : ℝ) :
    X → Fin n → Fin m → ℂ :=
  fun x => if f x then (fourthRoot (T0 / T1) : ℂ) • v x else (fourthRoot (T1 / T0) : ℂ) • v x

omit [Fintype X] [DecidableEq X] in
/-- On a false input the rescaled witness has fiber energy scaled by `√(T1 / T0)`. -/
theorem fiberEnergy_scaled_false {f : X → Bool} {v : X → Fin n → Fin m → ℂ} {T0 T1 : ℝ}
    {x : X} (hx : f x = false) :
    (∑ j, ∑ k, ‖fiberScaledWitness f v T0 T1 x j k‖ ^ 2)
      = Real.sqrt (T1 / T0) * fiberEnergy v x := by
  have hval : fiberScaledWitness f v T0 T1 x = (fourthRoot (T1 / T0) : ℂ) • v x := by
    simp [fiberScaledWitness, hx]
  rw [hval, sum_sq_norm_smul (fourthRoot (T1 / T0)) (fourthRoot_nonneg _), fourthRoot_sq]
  rw [fiberEnergy]

omit [Fintype X] [DecidableEq X] in
/-- On a true input the rescaled witness has fiber energy scaled by `√(T0 / T1)`. -/
theorem fiberEnergy_scaled_true {f : X → Bool} {v : X → Fin n → Fin m → ℂ} {T0 T1 : ℝ}
    {x : X} (hx : f x = true) :
    (∑ j, ∑ k, ‖fiberScaledWitness f v T0 T1 x j k‖ ^ 2)
      = Real.sqrt (T0 / T1) * fiberEnergy v x := by
  have hval : fiberScaledWitness f v T0 T1 x = (fourthRoot (T0 / T1) : ℂ) • v x := by
    simp [fiberScaledWitness, hx]
  rw [hval, sum_sq_norm_smul (fourthRoot (T0 / T1)) (fourthRoot_nonneg _), fourthRoot_sq]
  rw [fiberEnergy]

omit [Fintype X] [DecidableEq X] in
/-- Rescaling a source dual witness to the geometric-mean budget keeps it feasible: the fiber
energy bounds `T0` and `T1` become `√(T0 * T1)` on both sides while the unit overlap of every
false-true pair is preserved. -/
theorem sourceDualFeasible_fiberScaled (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W T0 T1 : ℝ)
    (hd : SourceDualFeasible input f v W) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (h0 : ∀ x, f x = false → fiberEnergy v x ≤ T0)
    (h1 : ∀ x, f x = true → fiberEnergy v x ≤ T1) :
    SourceDualFeasible input f (fiberScaledWitness f v T0 T1) (Real.sqrt (T0 * T1)) := by
  constructor
  · intro x
    rcases hx : f x with _ | _
    · rw [fiberEnergy_scaled_false hx]
      have hstep : Real.sqrt (T1 / T0) * fiberEnergy v x ≤ Real.sqrt (T1 / T0) * T0 :=
        mul_le_mul_of_nonneg_left (h0 x hx) (Real.sqrt_nonneg _)
      exact hstep.trans_eq (sqrt_div_false_mul hT0 hT1)
    · rw [fiberEnergy_scaled_true hx]
      have hstep : Real.sqrt (T0 / T1) * fiberEnergy v x ≤ Real.sqrt (T0 / T1) * T1 :=
        mul_le_mul_of_nonneg_left (h1 x hx) (Real.sqrt_nonneg _)
      exact hstep.trans_eq (sqrt_div_true_mul hT0 hT1)
  · intro x y hx hy
    have hprod : fourthRoot (T1 / T0) * fourthRoot (T0 / T1) = 1 :=
      fourthRoot_div_mul_fourthRoot_div hT0 hT1
    have hxw : fiberScaledWitness f v T0 T1 x = (fourthRoot (T1 / T0) : ℂ) • v x := by
      simp [fiberScaledWitness, hx]
    have hyw : fiberScaledWitness f v T0 T1 y = (fourthRoot (T0 / T1) : ℂ) • v y := by
      simp [fiberScaledWitness, hy]
    simp only [hxw, hyw]
    calc ∑ j : Fin n, (if input x j ≠ input y j then
            Qatlib.Foundations.PureStateMath.Inner ((fourthRoot (T1 / T0) : ℂ) • v x j)
              ((fourthRoot (T0 / T1) : ℂ) • v y j)
          else 0)
        = ∑ j : Fin n, (if input x j ≠ input y j then
            ((fourthRoot (T1 / T0) * fourthRoot (T0 / T1) : ℝ) : ℂ) *
              Qatlib.Foundations.PureStateMath.Inner (v x j) (v y j)
          else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs with h
          · rw [inner_const_mul]
          · rfl
      _ = ((fourthRoot (T1 / T0) * fourthRoot (T0 / T1) : ℝ) : ℂ) *
            ∑ j : Fin n, (if input x j ≠ input y j then
              Qatlib.Foundations.PureStateMath.Inner (v x j) (v y j) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
      _ = 1 := by rw [hd.2 x y hx hy, hprod]; norm_num

/-- The maximal fiber energy over the inputs on which `f` takes the value `b`, or `0` when there
is no such input. -/
noncomputable def fiberMax (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (b : Bool) : ℝ :=
  if h : (Finset.univ.filter fun x => f x = b).Nonempty then
    (Finset.univ.filter fun x => f x = b).sup' h (fun x => fiberEnergy v x)
  else 0

omit [DecidableEq X] in
/-- The fiber energy at an input is bounded by the maximal fiber energy on the same side. -/
theorem fiberEnergy_le_fiberMax {f : X → Bool} {v : X → Fin n → Fin m → ℂ} {b : Bool}
    {x : X} (hx : f x = b) : fiberEnergy v x ≤ fiberMax f v b := by
  classical
  have hmem : x ∈ Finset.univ.filter (fun y => f y = b) := by simp [hx]
  have hne : (Finset.univ.filter fun y => f y = b).Nonempty := ⟨x, hmem⟩
  have hval : fiberMax f v b
      = (Finset.univ.filter fun y => f y = b).sup' hne (fun y => fiberEnergy v y) := by
    rw [fiberMax, dite_eq_left hne]
  rw [hval]
  exact Finset.le_sup' (fun y => fiberEnergy v y) hmem

omit [DecidableEq X] in
/-- With `T0` and `T1` instantiated by the maximal fiber energies of the two sides, the rescaled
witness is source dual feasible with budget the geometric mean of those maxima. -/
theorem sourceDualFeasible_fiberMax (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) (hd : SourceDualFeasible input f v W)
    (hT0 : 0 < fiberMax f v false) (hT1 : 0 < fiberMax f v true) :
    SourceDualFeasible input f (fiberScaledWitness f v (fiberMax f v false) (fiberMax f v true))
      (Real.sqrt (fiberMax f v false * fiberMax f v true)) :=
  sourceDualFeasible_fiberScaled input f v W _ _ hd hT0 hT1
    (fun _ hx => fiberEnergy_le_fiberMax hx)
    (fun _ hx => fiberEnergy_le_fiberMax hx)

omit [Fintype X] [DecidableEq X] in
/-- When every input is a true input the overlap constraint is vacuous, and the zero witness is
source dual feasible with budget zero. -/
theorem sourceDualFeasible_zero (input : X → Fin n → Bool) (f : X → Bool)
    (h : ∀ x, f x = true) :
    SourceDualFeasible input f (fun (_ : X) (_ : Fin n) (_ : Fin m) => (0 : ℂ)) 0 := by
  constructor
  · intro x
    simp
  · intro x _ hx _
    exact absurd hx (by simp [h x])

omit [Fintype X] [DecidableEq X] in
/-- When every input is a false input the overlap constraint is vacuous as well, and the zero
witness is source dual feasible with budget zero. -/
theorem sourceDualFeasible_zero_of_no_true (input : X → Fin n → Bool) (f : X → Bool)
    (h : ∀ x, f x = false) :
    SourceDualFeasible input f (fun (_ : X) (_ : Fin n) (_ : Fin m) => (0 : ℂ)) 0 := by
  constructor
  · intro x
    simp
  · intro _ y _ hy
    exact absurd hy (by simp [h y])

end Qatlib.Papers.QQueryIntro25.MainResults.WitnessBudgetScaling
