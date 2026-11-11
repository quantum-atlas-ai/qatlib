/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntTools

/-!
# Decoding arbitrary qudit resource vectors

This module computes the entries and Gram matrices of `quditResourceBranchKraus`. The entry
formula separates the inverse Fourier coefficient from a shifted resource amplitude; when the
first resource marginal is maximally mixed, every branch Gram matrix is `1 / n²` times the
identity.

These calculations supply the correction construction for the qudit teleportation protocol of
[BennettEtAl1993Teleportation].

## Main statements

* `quditResourceBranchKraus_entry`: explicit branch entries for an arbitrary resource vector.
* `quditResourceBranchKraus_gram`: uniform branch Gram matrices from a maximally mixed marginal.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators

/-- Computes a decoded resource branch entry as an inverse Fourier entry times the resource
amplitude at the shifted Alice index. -/
theorem quditResourceBranchKraus_entry (n : ℕ) [NeZero n]
    (R : QState (Fin n × Fin n)) (o : Fin n × Fin n) (k j : Fin n) :
    quditResourceBranchKraus n R o k j =
      (QFTMatrix n)ᴴ o.1 j * R (quditAdd n o.2 j, k) := by
  have hcol : (fun r => quditResourcePreparedFrame n R r j) =
      relabelState (quditRegisterEquiv n)
        (fun r : QuditTriple n => if r.1.1 = j then R (r.1.2,r.2) else 0) := rfl
  rw [quditResourceBranchKraus, matrix_mul_column, hcol, applyGate_relabelGate,
    applyGate_mul, quditSUMabInv_state]
  simp only [relabelState, Function.comp_apply, Equiv.symm_apply_apply]
  rw [quditHaInv_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- For fixed `b`, the map `quditAdd n b` is injective in nonzero dimension. -/
theorem quditAdd_left_injective (n : ℕ) [NeZero n] (b : Fin n) :
    Function.Injective (quditAdd n b) := by
  intro i j h
  have he := congrArg (ZMod.finEquiv n) h
  simp only [quditAdd, RingEquiv.apply_symm_apply] at he
  exact (ZMod.finEquiv n).injective (add_left_cancel he)

/-- Every entry of the adjoint qudit Fourier matrix has squared modulus `1 / n`. -/
theorem quditQFT_adjoint_norm_sq (n : ℕ) [NeZero n] (a j : Fin n) :
    star ((QFTMatrix n)ᴴ a j) * (QFTMatrix n)ᴴ a j = 1 / (n : ℂ) := by
  rw [quditQFT_adjoint_entry]
  have hc : star (ZMod.stdAddChar (-((ZMod.finEquiv n) a * (ZMod.finEquiv n) j))) *
      ZMod.stdAddChar (-((ZMod.finEquiv n) a * (ZMod.finEquiv n) j)) = (1 : ℂ) := by
    have h : ((Complex.normSq (ZMod.stdAddChar
        (-((ZMod.finEquiv n) a * (ZMod.finEquiv n) j))) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_stdAddChar]
      norm_num
    simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def] using h
  have hs : star (Real.sqrt (n : ℝ) : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by simp
  simp only [star_mul, star_inv₀, hs]
  calc
    _ = ((Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹) *
        (star (ZMod.stdAddChar _) * ZMod.stdAddChar _) := by ring
    _ = _ := by rw [hc, mul_one, qudit_sqrt_inv_sq]

/-- If the resource vector has maximally mixed first marginal, each decoded branch operator has
Gram matrix `1 / n²` times the identity. -/
theorem quditResourceBranchKraus_gram (n : ℕ) [NeZero n]
    (R : QState (Fin n × Fin n))
    (hR : PartialTrace (outerProduct R) = (1 / (n : ℂ)) • (1 : Operator n))
    (o : Fin n × Fin n) :
    (quditResourceBranchKraus n R o)ᴴ * quditResourceBranchKraus n R o =
      (1 / (n : ℂ)^2) • (1 : Operator n) := by
  ext i j
  have he : ((quditResourceBranchKraus n R o)ᴴ * quditResourceBranchKraus n R o) i j =
      (star ((QFTMatrix n)ᴴ o.1 i) * (QFTMatrix n)ᴴ o.1 j) *
        PartialTrace (outerProduct R) (quditAdd n o.2 j) (quditAdd n o.2 i) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, quditResourceBranchKraus_entry,
      star_mul, PartialTrace, outerProduct_apply, Finset.mul_sum, Complex.star_def]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, hR]
  by_cases hij : i = j
  · subst j
    rw [quditQFT_adjoint_norm_sq]
    simp [Matrix.smul_apply, smul_eq_mul, pow_two]
  · have ht : quditAdd n o.2 j ≠ quditAdd n o.2 i := by
      intro h
      exact hij ((quditAdd_left_injective n o.2 h).symm)
    simp [Matrix.smul_apply, Matrix.one_apply, ht, hij]

end Qatlib.Concepts.QuditTeleport.ResourceIff
