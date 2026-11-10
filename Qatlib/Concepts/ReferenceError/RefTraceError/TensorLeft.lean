/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixtureComposition
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Matrix

open scoped Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.ReferenceError.RefTraceError

@[simp] theorem tensorLeft_id {D R : ℕ} (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft LinearMap.id ρ = ρ := by
  ext x y
  simp [tensorLeft]

theorem tensorLeft_comp {D E F R : ℕ} (S : Operator E →ₗ[ℂ] Operator F)
    (T : Operator D →ₗ[ℂ] Operator E) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (S.comp T) ρ = tensorLeft S (tensorLeft T ρ) := by
  ext x y
  simp only [tensorLeft, LinearMap.comp_apply]

theorem tensorLeft_sum {J : Type} [Fintype J] {D E R : ℕ}
    (T : J → (Operator D →ₗ[ℂ] Operator E))
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (∑ j, T j) ρ = ∑ j, tensorLeft (T j) ρ := by
  ext x y
  simp [tensorLeft, Matrix.sum_apply, LinearMap.sum_apply]

theorem tensorLeft_smul {D E R : ℕ} (c : ℂ) (T : Operator D →ₗ[ℂ] Operator E)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (c • T) ρ = c • tensorLeft T ρ := by
  ext x y
  simp [tensorLeft, LinearMap.smul_apply]

theorem tensorLeft_sub {D E R : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft T (ρ - σ) = tensorLeft T ρ - tensorLeft T σ := by
  ext x y
  have harg : (fun i j : Fin D => (ρ - σ) (i, x.2) (j, y.2) : Matrix (Fin D) (Fin D) ℂ)
      = (fun i j => ρ (i, x.2) (j, y.2) : Matrix (Fin D) (Fin D) ℂ)
        - (fun i j => σ (i, x.2) (j, y.2) : Matrix (Fin D) (Fin D) ℂ) := by
    funext i j
    simp [Matrix.sub_apply]
  simp only [tensorLeft]
  rw [harg]
  have hlin : T ((fun i j => ρ (i, x.2) (j, y.2) : Matrix (Fin D) (Fin D) ℂ)
      - (fun i j => σ (i, x.2) (j, y.2) : Matrix (Fin D) (Fin D) ℂ))
      = T (fun i j => ρ (i, x.2) (j, y.2)) - T (fun i j => σ (i, x.2) (j, y.2)) :=
    map_sub _ _ _
  rw [hlin]
  simp [tensorLeft, Matrix.sub_apply]

private lemma sum_ite_weight {R : ℕ} (X : Fin R → ℂ) (s : Fin R) :
    ∑ t : Fin R, (if s = t then (1 : ℂ) else 0) * X t = X s := by
  simp [Finset.sum_ite_eq]

private lemma sum_pair_swap {ι : Type} [Fintype ι] (F : ι → ι → ℂ) :
    ∑ c, ∑ d, F c d = ∑ c, ∑ d, F d c := by
  calc ∑ c : ι, ∑ d : ι, F c d
      = ∑ p : ι × ι, F p.1 p.2 := (Fintype.sum_prod_type (fun p : ι × ι => F p.1 p.2)).symm
    _ = ∑ p : ι × ι, F p.2 p.1 := Equiv.sum_comp (Equiv.prodComm ι ι)
          (fun p : ι × ι => F p.2 p.1)
    _ = ∑ c : ι, ∑ d : ι, F d c :=
          Fintype.sum_prod_type (fun p : ι × ι => F p.2 p.1)

theorem tensorLeft_conjBranch {D R : ℕ} (M : Operator D)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (conjBranch M) ρ
      = TensorGate M (1 : Operator R) * ρ * (TensorGate M (1 : Operator R))ᴴ := by
  ext ⟨a, s⟩ ⟨b, t⟩
  have hL : tensorLeft (conjBranch M) ρ (a, s) (b, t)
      = ∑ c : Fin D, ∑ d : Fin D,
          M a c * ρ (c, s) (d, t) * (starRingEnd ℂ) (M b d) := by
    simp only [tensorLeft, conjBranch_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul]
    exact sum_pair_swap (fun x y : Fin D =>
      M a y * ρ (y, s) (x, t) * (starRingEnd ℂ) (M b x))
  have hentry : ∀ (x : Fin D) (y : Fin R),
      TensorGate M (1 : Operator R) (a, s) (x, y)
        = M a x * (if s = y then (1 : ℂ) else 0) := by
    intro x y
    rw [tensorGate_apply, Matrix.one_apply]
  have hblock : ∀ (c : Fin D) (s' : Fin R),
      (TensorGate M (1 : Operator R) * ρ) (a, s) (c, s')
        = ∑ d : Fin D, M a d * ρ (d, s) (c, s') := by
    intro c s'
    have hcollapse : ∀ x : Fin D,
        ∑ y : Fin R, M a x * (if s = y then (1 : ℂ) else 0) * ρ (x, y) (c, s')
          = M a x * ρ (x, s) (c, s') := by
      intro x
      rw [← sum_ite_weight (fun y => M a x * ρ (x, y) (c, s')) s]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => by rw [hentry x y],
      Finset.sum_congr rfl fun x _ => hcollapse x]
  have hconj : ∀ (c : Fin D) (s' : Fin R),
      (TensorGate M (1 : Operator R))ᴴ (c, s') (b, t)
        = (if t = s' then (1 : ℂ) else 0) * (starRingEnd ℂ) (M b c) := by
    intro c s'
    have h1 : (TensorGate M (1 : Operator R))ᴴ (c, s') (b, t)
        = (starRingEnd ℂ) (TensorGate M (1 : Operator R) (b, t) (c, s')) :=
      Matrix.conjTranspose_apply _ _ _
    have h2 : TensorGate M (1 : Operator R) (b, t) (c, s')
        = M b c * (if t = s' then (1 : ℂ) else 0) := by
      rw [tensorGate_apply, Matrix.one_apply]
    rw [h1, h2, map_mul]
    by_cases h : t = s' <;> simp [h]
  have hR : (TensorGate M (1 : Operator R) * ρ * (TensorGate M (1 : Operator R))ᴴ)
      (a, s) (b, t)
      = ∑ c : Fin D, ∑ d : Fin D,
          M a c * ρ (c, s) (d, t) * (starRingEnd ℂ) (M b d) := by
    calc (TensorGate M (1 : Operator R) * ρ * (TensorGate M (1 : Operator R))ᴴ)
          (a, s) (b, t)
        = ∑ u : Fin D × Fin R, (TensorGate M (1 : Operator R) * ρ) (a, s) u
            * ((TensorGate M (1 : Operator R))ᴴ) u (b, t) := Matrix.mul_apply
      _ = ∑ c : Fin D, (∑ d : Fin D, M a d * ρ (d, s) (c, t))
            * (starRingEnd ℂ) (M b c) := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← sum_ite_weight
              (fun s' => (∑ d : Fin D, M a d * ρ (d, s) (c, s'))
                * (starRingEnd ℂ) (M b c)) t]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hblock c y, hconj c y]
            ring
      _ = ∑ c : Fin D, ∑ d : Fin D,
            M a d * ρ (d, s) (c, t) * (starRingEnd ℂ) (M b c) :=
            Finset.sum_congr rfl fun c _ => Finset.sum_mul _ _ _
      _ = ∑ c : Fin D, ∑ d : Fin D,
            M a c * ρ (c, s) (d, t) * (starRingEnd ℂ) (M b d) :=
            sum_pair_swap (fun x y : Fin D =>
              M a y * ρ (y, s) (x, t) * (starRingEnd ℂ) (M b x))
  rw [hL, hR]

theorem tensorLeft_trace_map {D E R : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (hT : TracePreserving T) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix.trace (tensorLeft T ρ) = Matrix.trace ρ := by
  have hstep1 : Matrix.trace (tensorLeft T ρ)
      = ∑ a : Fin E, ∑ r : Fin R, T (fun i j => ρ (i, r) (j, r)) a a := by
    simp [Matrix.trace, tensorLeft, Fintype.sum_prod_type]
  have hstep2 : ∀ r : Fin R, ∑ a : Fin E, T (fun i j => ρ (i, r) (j, r)) a a
      = ∑ a : Fin D, ρ (a, r) (a, r) := fun r => hT _
  have hswap : ∑ a : Fin E, ∑ r : Fin R, T (fun i j => ρ (i, r) (j, r)) a a
      = ∑ r : Fin R, ∑ a : Fin E, T (fun i j => ρ (i, r) (j, r)) a a := Finset.sum_comm
  have hstep3 : (∑ r : Fin R, ∑ a : Fin D, ρ (a, r) (a, r)) = Matrix.trace ρ := by
    rw [show Matrix.trace ρ = ∑ p : Fin D × Fin R, ρ p p from rfl, Fintype.sum_prod_type,
      Finset.sum_comm]
  rw [hstep1, hswap, Finset.sum_congr rfl fun r _ => hstep2 r, hstep3]
end Qatlib.Concepts.ReferenceError.RefTraceError
