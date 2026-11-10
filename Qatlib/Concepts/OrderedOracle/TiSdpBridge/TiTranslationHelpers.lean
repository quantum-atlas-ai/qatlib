/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialHelpers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

theorem ti_apply_permutation {N : ℕ} (e : Fin N ≃ Fin N) (ψ : QState (Fin N)) (i : Fin N) :
    ApplyGate (permMatrix e) ψ i=ψ (e.symm i) := by
  simp only [ApplyGate,permMatrix,Matrix.mulVec,dotProduct,Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · simp
  · intro j _ hj
    have hne : i≠e j := by
      intro h
      have he := congrArg e.symm h
      simp only [Equiv.symm_apply_apply] at he
      exact hj he.symm
    simp [hne]
  · simp

theorem ti_character_predecessor (N : ℕ) [NeZero N] (i l : Fin N) :
    primRoot N^((((finShiftEquiv N).symm i).val:ℤ)*(l.val:ℤ)) =
      primRoot N^(-(l.val:ℤ))*primRoot N^((i.val:ℤ)*(l.val:ℤ)) := by
  have hN := NeZero.pos N
  have hr := primRoot_ne_zero N
  by_cases hi : i.val=0
  · have hp : ((finShiftEquiv N).symm i).val=N-1 := by
      change (i.val+(N-1))%N=N-1
      rw [hi,zero_add,Nat.mod_eq_of_lt (by omega)]
    rw [hp,hi,Nat.cast_zero,zero_mul,_root_.zpow_zero,mul_one]
    have he : ((N-1:ℕ):ℤ)*(l.val:ℤ)=(N:ℤ)*(l.val:ℤ)+-(l.val:ℤ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one]
      ring
    rw [he,_root_.zpow_add₀ hr,_root_.zpow_mul,
      primRoot_zpow_natCast_eq_one hN,_root_.one_zpow,one_mul]
  · have hp : ((finShiftEquiv N).symm i).val=i.val-1 := by
      change (i.val+(N-1))%N=i.val-1
      rw [show i.val+(N-1)=(i.val-1)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    rw [hp,Nat.cast_sub (by omega),Nat.cast_one]
    rw [← _root_.zpow_add₀ hr]
    congr 1
    ring

theorem ti_translation_fourier (n : ℕ) [NeZero n] :
    tiTranslation n * QFTMatrix (2*n) =
      QFTMatrix (2*n)*Matrix.diagonal (tiMomentumRoot n) := by
  ext i l
  change ApplyGate (permMatrix (finShiftEquiv (2*n)))
    (fun j => QFTMatrix (2*n) j l) i = _
  rw [ti_apply_permutation]
  simp only [Matrix.mul_diagonal,qftMatrix_apply]
  rw [ti_character_predecessor]
  unfold tiMomentumRoot
  ring

theorem ti_translation_fourier_conjugate (n : ℕ) [NeZero n] :
    tiTranslation n=QFTMatrix (2*n)*Matrix.diagonal (tiMomentumRoot n)*(QFTMatrix (2*n))ᴴ := by
  have hF := qftMatrix_unitary (by have := NeZero.pos n; omega : 0<2*n)
  have hFF : QFTMatrix (2*n)*(QFTMatrix (2*n))ᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hF)
  have he := congrArg (fun A => A*(QFTMatrix (2*n))ᴴ) (ti_translation_fourier n)
  (try dsimp only at he)
  rw [Matrix.mul_assoc,hFF,Matrix.mul_one] at he
  exact he

theorem ti_transition_commutes (n t : ℕ) [NeZero n] (a b : Fin n → ℂ) :
    tiTranslation n*tiPolynomialTransition n t a b =
      tiPolynomialTransition n t a b*tiTranslation n := by
  have hF := qftMatrix_unitary (by have := NeZero.pos n; omega : 0<2*n)
  have hFF : (QFTMatrix (2*n))ᴴ*QFTMatrix (2*n)=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hF)
  have hd : Matrix.diagonal (tiMomentumRoot n)*Matrix.diagonal (tiTransitionPhase n t a b) =
      Matrix.diagonal (tiTransitionPhase n t a b)*Matrix.diagonal (tiMomentumRoot n) := by
    rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    exact mul_comm _ _
  rw [ti_translation_fourier_conjugate,tiPolynomialTransition]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (QFTMatrix (2*n))ᴴ, hFF,Matrix.one_mul]
  rw [← Matrix.mul_assoc (QFTMatrix (2*n))ᴴ,hFF,Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal (tiMomentumRoot n)),
    ← Matrix.mul_assoc (Matrix.diagonal (tiTransitionPhase n t a b)),hd]

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
