/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GradientOracle.C2GradientAlg

open scoped BigOperators

structure AffineModel (d : ℕ) where

  offset : ℝ

  grad : Fin d → ℝ

def AffineModel.eval {d : ℕ} (p : AffineModel d) (x : Fin d → ℝ) : ℝ :=
  p.offset + ∑ j, p.grad j * x j

def AffineModel.ofVec {d : ℕ} (v : Fin (d + 1) → ℝ) : AffineModel d :=
  ⟨v 0, fun j => v j.succ⟩

def evalLinearMap (d m : ℕ) (q : Fin m → (Fin d → ℝ)) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun v t := v 0 + ∑ j : Fin d, v j.succ * q t j
  map_add' a b := by
    funext t
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]
    simp only [RingHom.id_apply, mul_assoc]

theorem exists_nontrivial_kernel_vector
    (d m : ℕ) (hm : m < d + 1) (q : Fin m → (Fin d → ℝ)) :
    ∃ v : Fin (d + 1) → ℝ, v ≠ 0 ∧ evalLinearMap d m q v = 0 := by
  have hnotinj : ¬ Function.Injective (evalLinearMap d m q) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, Fintype.card_fin] at hle
    omega
  have hker : LinearMap.ker (evalLinearMap d m q) ≠ ⊥ := by
    intro h
    exact hnotinj ((LinearMap.ker_eq_bot).mp h)
  obtain ⟨v, hvmem, hvne⟩ := (Submodule.ne_bot_iff _).mp hker
  exact ⟨v, hvne, (LinearMap.mem_ker).mp hvmem⟩

theorem exists_nonzero_gradient_model_vanishing_on_queries
    (d m : ℕ) (hd : 1 ≤ d) (hm : m ≤ d) (q : Fin m → (Fin d → ℝ)) :
    ∃ p : AffineModel d, p.grad ≠ 0 ∧ ∀ t, p.eval (q t) = 0 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    refine ⟨⟨0, fun j => if j = ⟨0, hd⟩ then 1 else 0⟩, ?_, ?_⟩
    · intro hgrad
      have h := congrFun hgrad ⟨0, hd⟩
      simp at h
    · intro t
      exact Fin.elim0 t
  · obtain ⟨v, hvne, hv0⟩ :=
      exists_nontrivial_kernel_vector d m (by omega) q
    have hgradne : (fun j : Fin d => v j.succ) ≠ 0 := by
      intro hzero
      have hvzero0 : v 0 = 0 := by
        have ht0 := congrFun hv0 ⟨0, hmpos⟩
        have hzero' : ∀ j : Fin d, v j.succ = 0 := fun j => congrFun hzero j
        have hsum : (∑ j : Fin d, v j.succ * q ⟨0, hmpos⟩ j) = 0 := by
          simp [hzero']
        change v 0 + ∑ j : Fin d, v j.succ * q ⟨0, hmpos⟩ j = 0 at ht0
        rw [hsum] at ht0
        simpa using ht0
      apply hvne
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact hvzero0
      · exact congrFun hzero j
    refine ⟨AffineModel.ofVec v, ?_, ?_⟩
    · simpa [AffineModel.ofVec] using hgradne
    · intro t
      have ht := congrFun hv0 t
      simpa [AffineModel.eval, AffineModel.ofVec] using! ht

theorem affine_models_agree_with_distinct_gradients
    (d m : ℕ) (hd : 1 ≤ d) (hm : m ≤ d) (q : Fin m → (Fin d → ℝ)) :
    ∃ p p' : AffineModel d, p.grad ≠ p'.grad ∧
      ∀ t, p.eval (q t) = p'.eval (q t) := by
  obtain ⟨p, hgrad, hzero⟩ :=
    exists_nonzero_gradient_model_vanishing_on_queries d m hd hm q
  refine ⟨AffineModel.ofVec 0, p, ?_, ?_⟩
  · intro h
    exact hgrad (by simpa [AffineModel.ofVec] using! h.symm)
  · intro t
    rw [hzero t]
    simp [AffineModel.eval, AffineModel.ofVec]

theorem no_exact_gradient_from_le_d_queries
    (d m : ℕ) (hd : 1 ≤ d) (hm : m ≤ d)
    (q : Fin m → (Fin d → ℝ)) (out : (Fin m → ℝ) → (Fin d → ℝ)) :
    ∃ p : AffineModel d, out (fun t => p.eval (q t)) ≠ p.grad := by
  obtain ⟨p, p', hgrad, hagree⟩ :=
    affine_models_agree_with_distinct_gradients d m hd hm q
  by_contra h
  push Not at h
  have hfun : (fun t => p.eval (q t)) = (fun t => p'.eval (q t)) := by
    funext t
    exact hagree t
  have : p.grad = p'.grad := by
    rw [← h p, hfun, h p']
  exact hgrad this

structure AdaptivePointAlgorithm (d m : ℕ) where

  query : (t : Fin m) → (Fin t → ℝ) → (Fin d → ℝ)

  out : (Fin m → ℝ) → (Fin d → ℝ)

def transcriptPrefix {m : ℕ} (tr : Fin m → ℝ) (t : Fin m) : Fin t → ℝ :=
  fun i => tr ⟨i.val, lt_trans i.isLt t.isLt⟩

def AdaptivePointAlgorithm.IsRun {d m : ℕ} (A : AdaptivePointAlgorithm d m)
    (p : AffineModel d) (tr : Fin m → ℝ) : Prop :=
  ∀ t : Fin m, tr t = p.eval (A.query t (transcriptPrefix tr t))

theorem adaptive_no_exact_gradient
    (d m : ℕ) (hd : 1 ≤ d) (hm : m ≤ d)
    (A : AdaptivePointAlgorithm d m)
    (run : AffineModel d → Fin m → ℝ) (hRun : ∀ p, A.IsRun p (run p))
    (hDet : ∀ (p : AffineModel d) (tr tr' : Fin m → ℝ),
      A.IsRun p tr → A.IsRun p tr' → tr = tr') :
    ∃ p : AffineModel d, A.out (run p) ≠ p.grad := by
  let q : Fin m → (Fin d → ℝ) := fun t => A.query t (fun _ => 0)
  obtain ⟨p, hgrad, hzero⟩ :=
    exists_nonzero_gradient_model_vanishing_on_queries d m hd hm q
  let tr0 : Fin m → ℝ := fun _ => 0
  have hrunZero : A.IsRun (AffineModel.ofVec (0 : Fin (d + 1) → ℝ)) tr0 := by
    intro t
    simp [tr0, AffineModel.eval, AffineModel.ofVec]
  have hrunP : A.IsRun p tr0 := by
    intro t
    simpa [tr0, transcriptPrefix, q] using! (hzero t).symm
  have hZeroRun : run (AffineModel.ofVec (0 : Fin (d + 1) → ℝ)) = tr0 :=
    hDet _ _ _ (hRun _) hrunZero
  have hPRun : run p = tr0 := hDet _ _ _ (hRun p) hrunP
  by_contra h
  push Not at h
  have hOut : A.out (run (AffineModel.ofVec (0 : Fin (d + 1) → ℝ))) = A.out (run p) := by
    rw [hZeroRun, hPRun]
  have hZeroOut : A.out (run (AffineModel.ofVec (0 : Fin (d + 1) → ℝ))) = 0 := by
    simpa [AffineModel.ofVec] using! h (AffineModel.ofVec (0 : Fin (d + 1) → ℝ))
  have : p.grad = 0 := by
    rw [← h p, ← hOut]
    exact hZeroOut
  exact hgrad this

end Qatlib.Concepts.GradientOracle.C2GradientAlg
