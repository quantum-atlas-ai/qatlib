/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiReadoutHelpers

/-!
# Fourier characterization of translation-invariant unitaries

This module proves that unitary matrices commuting with cyclic translation act by phases in
Fourier coordinates. The symmetry comes from the invariant algorithms of [FarhiEtAl1999], while
[ChildsLandahlParrilo2007] provides the ordered-search polynomial context. The distinct values
of `tiMomentumRoot` make the translation spectrum simple.

`ti_commuting_diagonal` supplies the finite-dimensional algebraic step: a matrix commuting with
a diagonal matrix with distinct entries is diagonal. Applied in the Fourier basis, this yields
`ti_invariant_fourier_diagonal` and preservation of every Fourier-coordinate norm.
`ti_source_root_mode` also identifies each root of `z^n = (-1)^t` with a momentum mode of the
required parity.

## Main statements

- `ti_momentum_roots_injective` proves distinctness of the momentum roots.
- `ti_source_root_mode` realizes each relevant polynomial root as an active mode.
* `ti_invariant_fourier_diagonal` obtains unit-modulus Fourier phases from unitarity and
  translation commutation.
- `ti_invariant_fourier_norm` proves preservation of each Fourier-coordinate norm.

## References

- [Farhi et al., 1999][FarhiEtAl1999], invariant quantum algorithms for ordered search.
* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007], polynomial and semidefinite
  ordered-search methods.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.HspRecovery.CyclicRecovery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

/-- Proves that distinct indices in `Fin (2*n)` have distinct momentum roots when `n` is
nonzero. -/
theorem ti_momentum_roots_injective (n : ℕ) [NeZero n] :
    Function.Injective (tiMomentumRoot n) := by
  intro i j hij
  apply Fin.val_injective
  apply (isPrimitiveRoot_primRoot (by have := NeZero.pos n; omega : 2*n≠0)).pow_inj i.isLt j.isLt
  apply inv_injective
  simpa only [tiMomentumRoot,_root_.zpow_neg,zpow_natCast] using hij

/-- Shows that every complex root of `z^n = (-1)^t` is a momentum root at an index whose parity
equals that of `t`. -/
theorem ti_source_root_mode (n t : ℕ) [NeZero n] (z : ℂ)
    (hz : z^n=(-1:ℂ)^t) :
    ∃ l : Fin (2*n), tiMomentumRoot n l=z ∧ l.val%2=t%2 := by
  have hz2 : z^(2*n)=1 := by
    rw [show 2*n=n+n by omega,pow_add,hz,ti_parity_square]
  obtain ⟨i,hi,he⟩ :=
      (isPrimitiveRoot_primRoot (by have := NeZero.pos n; omega : 2*n≠0)).inv.eq_pow_of_pow_eq_one hz2
  let l : Fin (2*n) := ⟨i,hi⟩
  have hl : tiMomentumRoot n l=z := by
    simpa only [tiMomentumRoot,_root_.zpow_neg,zpow_natCast,inv_pow] using he
  refine ⟨l,hl,?_⟩
  have hp := ti_momentum_root_parity n l
  rw [hl,hz,neg_one_pow_eq_pow_mod_two t,neg_one_pow_eq_pow_mod_two l.val] at hp
  have ht : t%2=0 ∨ t%2=1 := by omega
  have hi' : l.val%2=0 ∨ l.val%2=1 := by omega
  rcases ht with ht | ht <;> rcases hi' with hi' | hi'
  · omega
  · norm_num [ht,hi'] at hp
  · norm_num [ht,hi'] at hp
  · omega

/-- Shows that a matrix commuting with a diagonal matrix whose diagonal entries are pairwise
distinct is itself diagonal. -/
theorem ti_commuting_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℂ) (hd : Function.Injective d) (V : Matrix I I ℂ)
    (hc : Matrix.diagonal d*V=V*Matrix.diagonal d) :
    V=Matrix.diagonal (fun i => V i i) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp
  · have he := congrArg (fun A : Matrix I I ℂ => A i j) hc
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he
    have hne : d i-d j≠0 := sub_ne_zero.mpr (fun h => hij (hd h))
    have hz : (d i-d j)*V i j=0 := by linear_combination he
    have hv := (mul_eq_zero.mp hz).resolve_left hne
    simp [hij,hv]

/-- Shows that a unitary matrix commuting with cyclic translation acts in Fourier coordinates by
a diagonal function whose values all have modulus one. -/
theorem ti_invariant_fourier_diagonal (n : ℕ) [NeZero n]
    (U : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hu : U ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ)
    (hc : tiTranslation n*U=U*tiTranslation n) :
    ∃ d : Fin (2*n) → ℂ, (∀ l,‖d l‖=1) ∧
      (QFTMatrix (2*n))ᴴ*U=Matrix.diagonal d*(QFTMatrix (2*n))ᴴ := by
  let F := QFTMatrix (2*n)
  let D := Matrix.diagonal (tiMomentumRoot n)
  let V := Fᴴ*U*F
  have hF := qftMatrix_unitary (by have := NeZero.pos n; omega : 0<2*n)
  have hFF : F*Fᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hF
  have hHF : Fᴴ*F=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hF
  have hFT : Fᴴ*tiTranslation n=D*Fᴴ := by
    rw [ti_translation_fourier_conjugate]
    change Fᴴ*(F*D*Fᴴ)=D*Fᴴ
    simp only [← Matrix.mul_assoc,hHF,Matrix.one_mul]
  have hTF : tiTranslation n*F=F*D := ti_translation_fourier n
  have hDV : D*V=V*D := by
    dsimp [V]
    calc
      D*(Fᴴ*U*F) = (D*Fᴴ)*U*F := by simp only [Matrix.mul_assoc]
      _ = (Fᴴ*tiTranslation n)*U*F := by rw [hFT]
      _ = Fᴴ*(tiTranslation n*U)*F := by simp only [Matrix.mul_assoc]
      _ = Fᴴ*(U*tiTranslation n)*F := by rw [hc]
      _ = Fᴴ*U*(tiTranslation n*F) := by simp only [Matrix.mul_assoc]
      _ = (Fᴴ*U*F)*D := by rw [hTF]; simp only [Matrix.mul_assoc]
  have hdiag : V=Matrix.diagonal (fun l => V l l) :=
    ti_commuting_diagonal _ (ti_momentum_roots_injective n) V hDV
  have hVH : V ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ := by
    exact (Matrix.unitaryGroup _ ℂ).mul_mem
      ((Matrix.unitaryGroup _ ℂ).mul_mem (qftMatrix_conjTranspose_unitary _ (by have := NeZero.pos n; omega)) hu) hF
  refine ⟨fun l => V l l,?_,?_⟩
  · intro l
    have he := Matrix.mem_unitaryGroup_iff'.mp hVH
    rw [hdiag,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal] at he
    have hl := congrArg (fun A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ => A l l) he
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq] at hl
    change star (V l l)*V l l=1 at hl
    simp only [Complex.star_def] at hl
    rw [← Complex.normSq_eq_conj_mul_self] at hl
    have hn : ‖V l l‖^2=1 := by
      have hr := congrArg Complex.re hl
      simpa only [Complex.ofReal_re,Complex.normSq_eq_norm_sq,Complex.one_re] using hr
    nlinarith [norm_nonneg (V l l)]
  · rw [← hdiag]
    dsimp [V]
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hFF,Matrix.mul_one]

/-- Proves that a unitary matrix commuting with cyclic translation preserves the norm of every
coordinate of the adjoint Fourier transform of any state. -/
theorem ti_invariant_fourier_norm (n : ℕ) [NeZero n]
    (U : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hu : U ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ)
    (hc : tiTranslation n*U=U*tiTranslation n)
    (ψ : QState (Fin (2*n))) (l : Fin (2*n)) :
    ‖ApplyGate (QFTMatrix (2*n))ᴴ (ApplyGate U ψ) l‖ =
      ‖ApplyGate (QFTMatrix (2*n))ᴴ ψ l‖ := by
  obtain ⟨d,hd,he⟩ := ti_invariant_fourier_diagonal n U hu hc
  unfold ApplyGate
  rw [Matrix.mulVec_mulVec,he,← Matrix.mulVec_mulVec,Matrix.mulVec_diagonal,norm_mul,hd,one_mul]

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
