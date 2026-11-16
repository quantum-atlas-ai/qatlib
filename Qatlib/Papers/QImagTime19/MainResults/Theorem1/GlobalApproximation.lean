/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Papers.QImagTime19.MainResults.LinearSpaceStep
public import Qatlib.Papers.QImagTime19.MainResults.QLanczosBound.QLanczosVariational
public import Qatlib.Papers.QImagTime19.MainResults.SourceModel

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open Qatlib.Papers.QImagTime19.MainResults

namespace Qatlib.Papers.QImagTime19.MainResults

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- The action `act A` of a matrix on a state is additive. -/
theorem act_add (A : Matrix ι ι ℂ) (ψ φ : State ι) :
    act A (ψ + φ) = act A ψ + act A φ := by
  simp [act, mulVec_add]

omit [DecidableEq ι] [Nonempty ι] in
/-- The action `act A` commutes with scalar multiplication. -/
theorem act_smul (A : Matrix ι ι ℂ) (c : ℂ) (ψ : State ι) :
    act A (c • ψ) = c • act A ψ := by
  simp [act, mulVec_smul]

omit [DecidableEq ι] [Nonempty ι] in
/-- The action `act A` preserves subtraction. -/
theorem act_sub (A : Matrix ι ι ℂ) (ψ φ : State ι) :
    act A (ψ - φ) = act A ψ - act A φ := by
  simp [act, mulVec_sub]

omit [DecidableEq ι] [Nonempty ι] in
/-- The action `act` is compatible with matrix multiplication: acting by `A * B`
is acting by `B` followed by acting by `A`. -/
theorem act_mul (A B : Matrix ι ι ℂ) (ψ : State ι) :
    act (A * B) ψ = act A (act B ψ) := by
  simp only [act, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv]
  rw [← Matrix.mulVec_mulVec]

omit [Nonempty ι] in
/-- The identity matrix acts trivially. -/
theorem act_one (ψ : State ι) : act (1 : Matrix ι ι ℂ) ψ = ψ := by
  simp [act]

/-- A unitary operator does not increase the norm of a state. -/
theorem norm_act_le {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (ψ : State ι) : ‖act U ψ‖ ≤ ‖ψ‖ := by
  have hU' : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
  have h := Matrix.l2_opNorm_mulVec U ψ
  rw [hU', one_mul] at h
  simpa [act, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv,
    PiLp.coe_symm_continuousLinearEquiv] using h

/-- A unitary operator preserves the norm of a state. -/
theorem norm_act_unitary {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (ψ : State ι) : ‖act U ψ‖ = ‖ψ‖ := by
  refine le_antisymm (norm_act_le hU ψ) ?_
  have hstar : star U ∈ Matrix.unitaryGroup ι ℂ := Unitary.star_mem hU
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  have hψ : ψ = act (star U) (act U ψ) := by
    rw [← act_mul, hUU, act_one]
  calc ‖ψ‖ = ‖act (star U) (act U ψ)‖ := congrArg norm hψ
    _ ≤ ‖act U ψ‖ := by simpa using norm_act_le hstar (act U ψ)

omit [DecidableEq ι] [Nonempty ι] in
/-- Renormalisation of a nonzero state has norm one. -/
theorem norm_normalize_eq_one {ψ : State ι} (h : ψ ≠ 0) : ‖normalize ψ‖ = 1 := by
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr h
  rw [Qatlib.Papers.QImagTime19.MainResults.normalize, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

omit [Nonempty ι] in
/-- An invertible operator maps a nonzero state to a nonzero state. -/
theorem act_ne_zero_of_isUnit {A : Matrix ι ι ℂ} (hA : IsUnit A) {ψ : State ι}
    (hψ : ψ ≠ 0) : act A ψ ≠ 0 := by
  intro h
  have hinj : Function.Injective fun v : ι → ℂ => A *ᵥ v :=
    Matrix.mulVec_injective_of_isUnit hA
  have h1 : A *ᵥ ((EuclideanSpace.equiv ι ℂ) ψ) = 0 := by
    have := congrArg (EuclideanSpace.equiv ι ℂ) h
    simpa [act] using this
  have hzero : A *ᵥ (0 : ι → ℂ) = 0 := Matrix.mulVec_zero A
  have h2 : (EuclideanSpace.equiv ι ℂ) ψ = 0 :=
    hinj (h1.trans hzero.symm)
  apply hψ
  have := congrArg (EuclideanSpace.equiv ι ℂ).symm h2
  simpa using this

omit [Nonempty ι] in
/-- One renormalised imaginary-time step of a normalised state has norm one. -/
theorem norm_imaginaryStep_eq_one {H : Matrix ι ι ℂ} {Δτ : ℝ} {ψ : State ι}
    (hψ : ‖ψ‖ = 1) : ‖imaginaryStep H Δτ ψ‖ = 1 := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix ι ι ℂ)
  apply norm_normalize_eq_one
  apply act_ne_zero_of_isUnit (NormedSpace.isUnit_exp _)
  rw [← norm_ne_zero_iff, hψ]
  norm_num

omit [Nonempty ι] in
/-- Every state of the Trotterised imaginary-time sequence is normalised when the
initial state is. -/
theorem trotterSeq_norm_eq_one {m : ℕ} [NeZero m] (H : Fin m → Matrix ι ι ℂ)
    (Δτ : ℝ) {ψ0 : State ι} (hψ0 : ‖ψ0‖ = 1) (s : ℕ) :
    ‖trotterSeq H Δτ ψ0 s‖ = 1 := by
  induction s with
  | zero => simpa [trotterSeq] using hψ0
  | succ s ih => simpa [trotterSeq] using norm_imaginaryStep_eq_one ih

omit [Nonempty ι] in
/-- Applying the identity unitary at every step leaves the state unchanged. -/
theorem qiteSeq_one (ψ0 : State ι) (s : ℕ) :
    qiteSeq (fun _ => (1 : Matrix ι ι ℂ)) ψ0 s = ψ0 := by
  induction s with
  | zero => rfl
  | succ s ih => simp [qiteSeq, act_one, ih]

omit [DecidableEq ι] [Nonempty ι] in
/-- **Telescoping estimate, Eq. (27).**  If two state sequences start at the same
state and each step of the second sequence is obtained from the corresponding
step of the first up to an error `δ`, then the accumulated error after `N` steps
is at most `N · δ`. -/
theorem telescoping_error_bound {Ψ Φ : ℕ → State ι} (N : ℕ) (δ : ℝ)
    (h0 : Φ 0 = Ψ 0)
    (hstep : ∀ s < N, ‖Φ (s + 1) - Ψ (s + 1)‖ ≤ ‖Φ s - Ψ s‖ + δ) :
    ‖Φ N - Ψ N‖ ≤ ‖Φ 0 - Ψ 0‖ + (N : ℝ) * δ := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    have hlast : ‖Φ (N + 1) - Ψ (N + 1)‖ ≤ ‖Φ N - Ψ N‖ + δ :=
      hstep N (Nat.lt_succ_self N)
    have ih' : ‖Φ N - Ψ N‖ ≤ ‖Φ 0 - Ψ 0‖ + (N : ℝ) * δ :=
      ih (fun s hs => hstep s (Nat.lt_trans hs (Nat.lt_succ_self N)))
    calc ‖Φ (N + 1) - Ψ (N + 1)‖
        ≤ ‖Φ N - Ψ N‖ + δ := hlast
      _ ≤ (‖Φ 0 - Ψ 0‖ + (N : ℝ) * δ) + δ := by linarith
      _ = ‖Φ 0 - Ψ 0‖ + ((N + 1 : ℕ) : ℝ) * δ := by push_cast; ring

omit [DecidableEq ι] [Nonempty ι] in
/-- With equal starting states and a total budget `N · δ ≤ ε`, the accumulated
error after `N` steps is at most `ε`. -/
theorem accumulated_error_le {Ψ Φ : ℕ → State ι} (N : ℕ) (δ ε : ℝ)
    (h0 : Φ 0 = Ψ 0)
    (hstep : ∀ s < N, ‖Φ (s + 1) - Ψ (s + 1)‖ ≤ ‖Φ s - Ψ s‖ + δ)
    (hbudget : (N : ℝ) * δ ≤ ε) :
    ‖Φ N - Ψ N‖ ≤ ε := by
  have h := telescoping_error_bound N δ h0 hstep
  have hzero : ‖Φ 0 - Ψ 0‖ = 0 := by rw [h0, sub_self, norm_zero]
  linarith

/-- The per-step error `δ = 2√2 e^{-ν/(2C)}` of Eq. (32) with `ν` the domain
width `qiteDomainWidth` of Eq. (34). -/
def qiteStepError (C : ℝ) (n m : ℕ) (ε : ℝ) : ℝ :=
  2 * Real.sqrt 2 * Real.exp (-(qiteDomainWidth C n m ε) / (2 * C))

/-- **Eq. (34) achieves the error `ε`.**  With the width
`ν = 2C ln(2√2 n m ε^{-1})`, the per-step error `2√2 e^{-ν/(2C)}` equals
`ε/(n m)`, hence `n·m` steps accumulate at most `ε`. -/
theorem qiteStepError_eq (C : ℝ) {n m : ℕ} {ε : ℝ} (hC : C ≠ 0) (hn : 0 < n)
    (hm : 0 < m) (hε : 0 < ε) :
    qiteStepError C n m ε = ε / ((n : ℝ) * (m : ℝ)) := by
  have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero two_ne_zero hC
  have harg : 0 < 2 * Real.sqrt 2 * (n : ℝ) * (m : ℝ) / ε := by positivity
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hν : -(2 * C * Real.log (2 * Real.sqrt 2 * (n : ℝ) * (m : ℝ) / ε)) / (2 * C)
      = -Real.log (2 * Real.sqrt 2 * (n : ℝ) * (m : ℝ) / ε) := by
    field_simp [h2C]
  unfold qiteStepError qiteDomainWidth
  rw [hν, Real.exp_neg, Real.exp_log harg]
  field_simp [hε.ne', hn'.ne', hm'.ne']

/-- The accumulated error budget of Theorem 1: `n m` steps of error
`2√2 e^{-ν/(2C)}` total at most `ε`. -/
theorem qite_error_budget (C : ℝ) {n m : ℕ} {ε : ℝ} (hC : C ≠ 0) (hn : 0 < n)
    (hm : 0 < m) (hε : 0 < ε) :
    ((n * m : ℕ) : ℝ) * qiteStepError C n m ε ≤ ε := by
  rw [qiteStepError_eq C hC hn hm hε]
  have hnm : ((n : ℝ) * (m : ℝ)) ≠ 0 := by positivity
  have hcast : ((n * m : ℕ) : ℝ) = (n : ℝ) * (m : ℝ) := by push_cast; ring
  rw [hcast]
  exact le_of_eq (mul_div_cancel₀ ε hnm)

/-- The qubit count of Theorem 1, Eq. (25), written in the literal paper form
`k (2C)^d ln^d(2√2 n m ε^{-1})` is the same real number as `k ν^d` with
`ν = 2C ln(2√2 n m ε^{-1})`. -/
theorem qiteQubitCount_paper_form (k : ℕ) (C : ℝ) (d n m : ℕ) (ε : ℝ) :
    (k : ℝ) * (qiteDomainWidth C n m ε) ^ d =
      (k : ℝ) * (2 * C) ^ d *
        (Real.log (2 * Real.sqrt 2 * (n : ℝ) * (m : ℝ) / ε)) ^ d := by
  rw [qiteDomainWidth, mul_pow]
  ring

end

end Qatlib.Papers.QImagTime19.MainResults
