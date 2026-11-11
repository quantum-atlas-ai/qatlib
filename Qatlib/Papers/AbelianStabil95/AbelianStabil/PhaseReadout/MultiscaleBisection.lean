/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseEstimateSubgoalQuan
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.PrecisionArithmetic
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.ReadoutParameters

/-!
# Controlled powers for multiscale phase estimation

`powerAccess` places powers of a matrix in blocks indexed by their exponents. `levelExponent`
selects the dyadic powers used in multiscale phase estimation, and `level_estimate` applies the
eigenphase sampling bound to the phase multiplied by `2 ^ j`. The development follows
[Kitaev1995].

## Main statements

* `powerAccess_level`: selects the block acting by `U ^ (2 ^ j)`.
* `level_estimate`: bounds the decoding failure probability at a dyadic level.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.KitaevReadout
open scoped BigOperators Classical

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A vector with eigenvalue `lam` for `U` has eigenvalue `lam ^ n` for `U ^ n`. -/
theorem pow_mul_eigenvector (U : Matrix I I ℂ) (ψ : QState I) (lam : ℂ) (n : ℕ)
    (hU : U *ᵥ ψ = lam • ψ) : (U ^ n) *ᵥ ψ = lam ^ n • ψ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hU, Matrix.mulVec_smul, ih, smul_smul]
    rw [mul_comm, pow_succ]

/-- The block diagonal matrix whose block indexed by `a` acts as `U ^ a`, representing the power
access used in [Kitaev, 1995, Lemma 10][Kitaev1995]. -/
def powerAccess (U : Matrix I I ℂ) (r : ℕ) :
    Matrix (Fin (r + 1) × I) (Fin (r + 1) × I) ℂ :=
  Matrix.of fun (a, i) (a', i') => if a = a' then (U ^ (a : ℕ)) i i' else 0

/-- On a basis control state indexed by `a`, `powerAccess U r` preserves that control and
applies `U ^ a` to the data state. -/
theorem powerAccess_apply (U : Matrix I I ℂ) (r : ℕ) (a : Fin (r + 1)) (ξ : QState I) :
    ApplyGate (powerAccess U r) (TensorState (Ket a) ξ)
      = TensorState (Ket a) (ApplyGate (U ^ (a : ℕ)) ξ) := by
  funext p
  obtain ⟨a', i'⟩ := p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, powerAccess, TensorState, Matrix.of_apply,
    Ket, Fintype.sum_prod_type]
  by_cases ha : a' = a
  · subst a'
    simp only [if_true, ite_mul, zero_mul]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.mulVec, dotProduct]
    · intro a'' _ ha''; simp [Ne.symm ha'']
    · intro h; exact absurd (Finset.mem_univ a) h
  · have h0 : ¬ (a = a') := fun h => ha h.symm
    simp [ha, h0]

/-- The dyadic exponent `2 ^ j` as an element of the power-access range for `j < l`. -/
def levelExponent (l j : ℕ) (hj : j < l) : Fin (bisectRange l + 1) :=
  ⟨2 ^ j, by
    have h : 2 ^ j < 2 ^ l := Nat.pow_lt_pow_right (by norm_num) hj
    have hle : bisectRange l + 1 = 2 ^ l := bisectRange_succ l
    omega⟩

/-- The natural-number value of the level exponent is `2 ^ j`. -/
@[simp] theorem levelExponent_val (l j : ℕ) (hj : j < l) :
    ((levelExponent l j hj : Fin (bisectRange l + 1)) : ℕ) = 2 ^ j := rfl

/-- Selecting `levelExponent l j hj` applies `U ^ (2 ^ j)` to the data and preserves the control
basis state, as used in [Kitaev, 1995, Lemma 10][Kitaev1995]. -/
theorem powerAccess_level (U : Matrix I I ℂ) (l j : ℕ) (hj : j < l) (ξ : QState I) :
    ApplyGate (powerAccess U (bisectRange l))
        (TensorState (Ket (levelExponent l j hj)) ξ)
      = TensorState (Ket (levelExponent l j hj)) (ApplyGate (U ^ (2 ^ j)) ξ) := by
  rw [powerAccess_apply, levelExponent_val]

/-- Raising `eigenPhase φ` to a natural power multiplies its phase by that exponent, as used in
[Kitaev1995]. -/
theorem eigenPhase_pow (φ : ℝ) (m : ℕ) :
    eigenPhase φ ^ m = eigenPhase ((m : ℝ) * φ) := by
  unfold eigenPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Under the stated precision, failure, and sample-count conditions, decoding the samples for
phase `2 ^ j * φ` fails to lie within `δ` modulo integers with probability at most `ε`. This
supplies a levelwise estimate for [Kitaev, 1995, Lemma 10][Kitaev1995]. -/
theorem level_estimate (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ) (j : ℕ)
    (hU : U *ᵥ ψ = eigenPhase φ • ψ) :
    ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε < 1 →
    ∀ s : ℕ, 36 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 ≤ s →
    (eigenphaseSampleLaw ((2 : ℝ) ^ j * φ) s).probEvent (L := 1)
        (fun ω => ¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - ((2 : ℝ) ^ j * φ) + m| ≤ δ)
      ≤ ε := by
  classical
  intro δ ε hδ hδ2 hε hε1 s hs
  have hUpow : (U ^ (2 ^ j)) *ᵥ ψ = eigenPhase ((2 : ℝ) ^ j * φ) • ψ := by
    have h := pow_mul_eigenvector U ψ (eigenPhase φ) (2 ^ j) hU
    rw [h, eigenPhase_pow]
    congr 1
    push_cast
    ring
  exact eigenphaseEstimateSubgoal δ ε hδ hδ2 hε hε1 I (U ^ (2 ^ j)) ψ
    ((2 : ℝ) ^ j * φ) hUpow s hs

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
