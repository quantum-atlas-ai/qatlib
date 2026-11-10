/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.Sqrt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open scoped ComplexOrder

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open scoped BigOperators ComplexOrder
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

noncomputable def tiPolyEval {n : ℕ} (v : Fin n → ℂ) (z : ℂ) : ℂ := ∑ j, v j * z ^ (j : ℕ)

noncomputable def tiDirichletVec (n : ℕ) : Fin n → ℂ := fun _ => (Real.sqrt n)⁻¹

def tiTraceStep {n : ℕ} (t : ℕ) (Q Q' : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ j ∈ Finset.Ioo (0 : ℤ) ((n : ℤ)),
    genTrace Q j + (-1 : ℤ) ^ t * genTrace Q (j - (n : ℤ))
      = genTrace Q' j + (-1 : ℤ) ^ t * genTrace Q' (j - (n : ℤ))

def tiSDPFeasible (n k : ℕ) (ε : ℝ) [NeZero n] : Prop :=
  ∃ Q : ℕ → Matrix (Fin n) (Fin n) ℂ,
    (∀ t, (Q t).PosSemidef) ∧
    (∀ i j, Q 0 i j = (n : ℂ)⁻¹) ∧
    (∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) ∧
    (1 - ε ≤ (Q k 0 0).re) ∧
    (∀ t ∈ Finset.Icc 1 k, tiTraceStep t (Q t) (Q (t - 1)))

def tiSDPRootForm (n k : ℕ) (ε : ℝ) [NeZero n] : Prop :=
  ∃ Q : ℕ → Matrix (Fin n) (Fin n) ℂ,
    (∀ t, (Q t).PosSemidef) ∧
    (∀ i j, Q 0 i j = (n : ℂ)⁻¹) ∧
    (∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) ∧
    (1 - ε ≤ (Q k 0 0).re) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      matrixLaurent (Q t) z = matrixLaurent (Q (t - 1)) z)

def tiPolyConditions (n k : ℕ) (ε : ℝ) [NeZero n] : Prop :=
  ∃ p : ℕ → (Fin n → ℂ),
    p 0 = tiDirichletVec n ∧
    (∀ t ∈ Finset.Icc 1 k, ∑ j, Complex.normSq (p t j) = 1) ∧
    (∑ j, Complex.normSq (p 0 j) = 1) ∧
    (1 - ε ≤ Complex.normSq (p k 0)) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      ‖tiPolyEval (p t) z‖ = ‖tiPolyEval (p (t - 1)) z‖)

def exactTIProgram (n k : ℕ) [NeZero n] : Prop :=
  ∃ q : ℕ → (Fin n → ℝ),
    q 0 = fejerCoeffs n ∧
    (q k 0 = 1 ∧ ∀ j, (0 : Fin n) < j → q k j = 0) ∧
    (∀ t ∈ Finset.Icc 0 k, q t 0 = 1) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      laurentEval (q t) z = laurentEval (q (t - 1)) z) ∧
    (∀ t ∈ Finset.Icc 0 k, ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (laurentEval (q t) z).re)

theorem ti_initial_trace (n : ℕ) [NeZero n] (Q : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ i j, Q 0 i j = (n : ℂ)⁻¹) : (Q 0).trace = 1 := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, hQ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast NeZero.ne n : (n : ℂ) ≠ 0)

theorem ti_step_trace (n k : ℕ) [NeZero n] (Q : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ i j, Q 0 i j = (n : ℂ)⁻¹)
    (htr : ∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) (t : ℕ) (ht : t ∈ Finset.Icc 1 k) :
    (Q t).trace = (Q (t - 1)).trace := by
  rw [htr t ht]
  by_cases h1 : t = 1
  · subst t
    simpa using (ti_initial_trace n Q hQ).symm
  · symm
    apply htr
    simp only [Finset.mem_Icc] at ht ⊢
    omega

theorem lemma11_tiSDPFeasible_iff_rootForm (n k : ℕ) (ε : ℝ) [NeZero n] :
    tiSDPFeasible n k ε ↔ tiSDPRootForm n k ε := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  constructor
  · rintro ⟨Q, hps, hQ, htr, hfin, hstep⟩
    refine ⟨Q, hps, hQ, htr, hfin, ?_⟩
    intro t ht
    apply (matrixLaurent_root_matching_iff hn t (Q t) (Q (t - 1))).mpr
    refine ⟨ti_step_trace n k Q hQ htr t ht, ?_⟩
    intro j hj hjn
    have hm : (j : ℤ) ∈ Finset.Ioo (0 : ℤ) (n : ℤ) := by
      simp only [Finset.mem_Ioo]
      constructor <;> exact_mod_cast (by assumption)
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hstep t ht (j : ℤ) hm
  · rintro ⟨Q, hps, hQ, htr, hfin, hroot⟩
    refine ⟨Q, hps, hQ, htr, hfin, ?_⟩
    intro t ht j hj
    have hc := ((matrixLaurent_root_matching_iff hn t (Q t) (Q (t - 1))).mp (hroot t ht)).2
    simp only [Finset.mem_Ioo] at hj
    have hp : 0 < j.toNat := by omega
    have hlt : j.toNat < n := by omega
    have he : ((j.toNat : ℕ) : ℤ) = j := by omega
    simpa only [he, Int.cast_pow, Int.cast_neg, Int.cast_one] using hc j.toNat hp hlt

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
