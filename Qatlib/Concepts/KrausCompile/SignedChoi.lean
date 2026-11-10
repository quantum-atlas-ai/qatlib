/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped ComplexOrder Classical

namespace Qatlib.Concepts.KrausCompile.SignedChoi

theorem hp_preserves_adjoint {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hHP : ∀ X : Operator d, X.IsHermitian → (T X).IsHermitian) (X : Operator d) :
    T X.conjTranspose = (T X).conjTranspose := by
  have hplus : (X + X.conjTranspose).IsHermitian := isHermitian_add_transpose_self X
  have hminus : (Complex.I • (X - X.conjTranspose)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    simp only [Complex.star_def, Complex.conj_I]
    module
  have h1 : (T X).conjTranspose + (T X.conjTranspose).conjTranspose =
      T X + T X.conjTranspose := by
    simpa only [map_add, Matrix.conjTranspose_add] using (hHP _ hplus).eq
  have h2 := congrArg (fun M : Operator d => M) (hHP _ hminus).eq
  rw [map_smul, map_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub] at h2
  simp only [Complex.star_def, Complex.conj_I] at h2
  ext i j
  have h1ij := congrArg (fun M => M i j) h1
  have h2ij := congrArg (fun M => M i j) h2
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.conjTranspose_apply] at h1ij h2ij ⊢
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    -(1/2:ℂ) * h1ij - (Complex.I/2) * h2ij

theorem choi_hermitian {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hHP : ∀ X : Operator d, X.IsHermitian → (T X).IsHermitian) :
    (ChoiMatrix T).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨i,a⟩ ⟨j,b⟩
  have h := congrArg (fun M => M a b) (hp_preserves_adjoint T hHP (matrixUnit j i))
  simpa [ChoiMatrix, matrixUnit, Matrix.conjTranspose_single] using h.symm

theorem sign_mul_abs (x : ℝ) : (if 0 ≤ x then (1:ℝ) else -1) * |x| = x := by
  split_ifs with hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_neg (lt_of_not_ge hx)]

abbrev Active {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) := {i : I // hA.eigenvalues i ≠ 0}

theorem active_card_eq_rank {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) : Fintype.card (Active A hA) = A.rank :=
  hA.rank_eq_card_non_zero_eigs.symm

noncomputable def spectralSign {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (k : I) : ℂ :=
  if 0 ≤ hA.eigenvalues k then 1 else -1

noncomputable def spectralVector {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (k x : I) : ℂ :=
  (Real.sqrt |hA.eigenvalues k| : ℂ) * (hA.eigenvectorUnitary : Matrix I I ℂ) x k

theorem spectral_term {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (k x y : I) :
    spectralSign hA k * spectralVector hA k x * star (spectralVector hA k y) =
      (hA.eigenvectorUnitary : Matrix I I ℂ) x k * (hA.eigenvalues k : ℂ) *
        star ((hA.eigenvectorUnitary : Matrix I I ℂ) y k) := by
  have hsq : (Real.sqrt |hA.eigenvalues k| : ℂ) * (Real.sqrt |hA.eigenvalues k| : ℂ) =
      ((|hA.eigenvalues k| : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (abs_nonneg (hA.eigenvalues k))
  have hsgn : spectralSign hA k * ((|hA.eigenvalues k| : ℝ) : ℂ) = (hA.eigenvalues k : ℂ) := by
    unfold spectralSign
    split_ifs with hk
    · simp [abs_of_nonneg hk]
    · simp [abs_of_neg (lt_of_not_ge hk)]
  simp only [spectralVector, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (spectralSign hA k *
      ((Real.sqrt |hA.eigenvalues k| : ℂ) * (Real.sqrt |hA.eigenvalues k| : ℂ))) *
      (hA.eigenvectorUnitary : Matrix I I ℂ) x k *
      star ((hA.eigenvectorUnitary : Matrix I I ℂ) y k) := by
        simp only [Complex.star_def]
        ring
    _ = _ := by rw [hsq, hsgn]; simp only [Complex.star_def]; ring

theorem spectral_signed_entry {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (x y : I) :
    A x y = ∑ k : I, spectralSign hA k * spectralVector hA k x * star (spectralVector hA k y) := by
  have h := congrArg (fun M : Matrix I I ℂ => M x y) hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Function.comp_apply] at h
  rw [h]
  exact Finset.sum_congr rfl (fun k _ => (spectral_term hA k x y).symm)

theorem spectral_active_entry {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (x y : I) :
    A x y = ∑ k : Active A hA,
      spectralSign hA k.val * spectralVector hA k.val x * star (spectralVector hA k.val y) := by
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun k : I => hA.eigenvalues k ≠ 0)
    (fun k : I => spectralSign hA k * spectralVector hA k x * star (spectralVector hA k y))
  have hz : (∑ k : {k : I // ¬ hA.eigenvalues k ≠ 0},
      spectralSign hA k.val * spectralVector hA k.val x * star (spectralVector hA k.val y)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : hA.eigenvalues k.val = 0 := not_not.mp k.property
    simp [spectralVector, hk]
  rw [hz, add_zero] at hsum
  rw [spectral_signed_entry A hA x y, ← hsum]

noncomputable def activeKraus {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hC : (ChoiMatrix T).IsHermitian) (k : Active (ChoiMatrix T) hC) : Operator d :=
  fun a i => spectralVector hC k.val (i,a)

theorem active_signed_action {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hC : (ChoiMatrix T).IsHermitian) (X : Operator d) :
    T X = ∑ k : Active (ChoiMatrix T) hC,
      spectralSign hC k.val • (activeKraus T hC k * X * (activeKraus T hC k).conjTranspose) := by
  ext a b
  rw [apply_eq_choiSum, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, kraus_mul_apply]
  simp_rw [spectral_active_entry (ChoiMatrix T) hC, Finset.mul_sum]
  rw [sum3_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [activeKraus]
  ring

theorem active_signed_complete {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hC : (ChoiMatrix T).IsHermitian) (hTP : TracePreserving T) :
    (∑ k : Active (ChoiMatrix T) hC,
      spectralSign hC k.val • ((activeKraus T hC k).conjTranspose * activeKraus T hC k)) = 1 := by
  apply eq_one_of_trace_mul_eq_trace
  intro X
  rw [Finset.sum_mul, Matrix.trace_sum]
  calc
    _ = ∑ k : Active (ChoiMatrix T) hC,
        Matrix.trace (spectralSign hC k.val •
          (activeKraus T hC k * X * (activeKraus T hC k).conjTranspose)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_mul_assoc, Matrix.trace_smul, Matrix.trace_smul]
      exact congrArg (fun z : ℂ => spectralSign hC k.val • z)
        (Matrix.trace_mul_cycle (activeKraus T hC k) X (activeKraus T hC k).conjTranspose).symm
    _ = Matrix.trace (T X) := by rw [active_signed_action T hC X, Matrix.trace_sum]
    _ = Matrix.trace X := hTP X

theorem activeKraus_ne_zero {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hC : (ChoiMatrix T).IsHermitian) (k : Active (ChoiMatrix T) hC) :
    activeKraus T hC k ≠ 0 := by
  intro hz
  have hs : (Real.sqrt |hC.eigenvalues k.val| : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr k.property)).ne'
  have hcol (p : Fin d × Fin d) :
      (hC.eigenvectorUnitary : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) p k.val = 0 := by
    have h := congrArg (fun M : Operator d => M p.2 p.1) hz
    change (Real.sqrt |hC.eigenvalues k.val| : ℂ) *
      (hC.eigenvectorUnitary : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) p k.val = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hs
  have hu := congrArg (fun M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ => M k.val k.val)
    (Unitary.coe_star_mul_self hC.eigenvectorUnitary)
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    hcol, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at hu
  exact zero_ne_one hu

noncomputable def rankIndex {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hC : (ChoiMatrix T).IsHermitian) : Fin (ChoiMatrix T).rank ≃ Active (ChoiMatrix T) hC :=
  (finCongr hC.rank_eq_card_non_zero_eigs).trans (Fintype.equivFin _).symm

noncomputable def canonicalKraus {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hHP : ∀ X : Operator d, X.IsHermitian → (T X).IsHermitian)
    (i : Fin (ChoiMatrix T).rank) : Operator d :=
  activeKraus T (choi_hermitian T hHP) (rankIndex T (choi_hermitian T hHP) i)

noncomputable def canonicalSign {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hHP : ∀ X : Operator d, X.IsHermitian → (T X).IsHermitian)
    (i : Fin (ChoiMatrix T).rank) : ℂ :=
  spectralSign (choi_hermitian T hHP) (rankIndex T (choi_hermitian T hHP) i).val

theorem canonical_signed_representation {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d)
    (hHP : ∀ X : Operator d, X.IsHermitian → (T X).IsHermitian)
    (hTP : TracePreserving T) :
    (∀ i : Fin (ChoiMatrix T).rank, canonicalSign T hHP i = 1 ∨ canonicalSign T hHP i = -1) ∧
    (∀ i : Fin (ChoiMatrix T).rank, canonicalKraus T hHP i ≠ 0) ∧
    (∑ i : Fin (ChoiMatrix T).rank, canonicalSign T hHP i •
      ((canonicalKraus T hHP i).conjTranspose * canonicalKraus T hHP i)) = 1 ∧
    (∀ X : Operator d, T X = ∑ i : Fin (ChoiMatrix T).rank,
      canonicalSign T hHP i • (canonicalKraus T hHP i * X * (canonicalKraus T hHP i).conjTranspose)) := by
  let hC := choi_hermitian T hHP
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    unfold canonicalSign spectralSign
    split_ifs <;> simp
  · intro i
    exact activeKraus_ne_zero T hC _
  · change (∑ i : Fin (ChoiMatrix T).rank,
      spectralSign hC (rankIndex T hC i).val •
      ((activeKraus T hC (rankIndex T hC i)).conjTranspose * activeKraus T hC (rankIndex T hC i))) = 1
    rw [Equiv.sum_comp (e := rankIndex T hC)
      (g := fun k : Active (ChoiMatrix T) hC =>
        spectralSign hC k.val • ((activeKraus T hC k).conjTranspose * activeKraus T hC k))]
    exact active_signed_complete T hC hTP
  · intro X
    change T X = ∑ i : Fin (ChoiMatrix T).rank,
      spectralSign hC (rankIndex T hC i).val •
      (activeKraus T hC (rankIndex T hC i) * X * (activeKraus T hC (rankIndex T hC i)).conjTranspose)
    rw [Equiv.sum_comp (e := rankIndex T hC)
      (g := fun k : Active (ChoiMatrix T) hC =>
        spectralSign hC k.val • (activeKraus T hC k * X * (activeKraus T hC k).conjTranspose))]
    exact active_signed_action T hC X

end Qatlib.Concepts.KrausCompile.SignedChoi
