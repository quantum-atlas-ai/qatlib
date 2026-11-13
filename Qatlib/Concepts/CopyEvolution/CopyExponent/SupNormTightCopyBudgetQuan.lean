/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.CopyExponent.SupNormTightCopyBudgetStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.StateDependentCopyPrecisionQuan
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm

/-!
# Explicit copy budget for trace-norm precision

`supNormTightCopyBudget` proves that a state-dependent ceiling budget gives error at most ε for
density operators. The proof combines the state-dependent precision theorem with a trace-norm
bound on density-operator differences, obtaining n ≤ 16t²/ε + 1.

The result supplies explicit constants for the copy scaling of density-matrix exponentiation
[LloydMohseniRebentrost2014].

## Main statements

* `traceNorm_tensor_one`: removes a one-dimensional identity factor from a trace norm.
* `supNormTightCopyBudget`: proves the budget, error, and resource-count specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent
open Matrix
open scoped ComplexOrder
set_option autoImplicit false

/-- Tensoring an operator with the one-dimensional identity preserves its trace norm. -/
theorem traceNorm_tensor_one (D : ℕ) (X : Operator D) :
    Matrix.traceNorm (TensorGate X (1:Operator 1)) = Matrix.traceNorm X := by
  let e : Fin D ≃ Fin D × Fin 1 :=
    { toFun := fun i => (i,0)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun p => by ext <;> simp [Subsingleton.elim p.2 0] }
  have he : TensorGate X (1:Operator 1) = Matrix.reindex e e X := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [tensorGate_apply, Matrix.reindex_apply, e,
      Subsingleton.elim a b]
  rw [he, diamond_traceNorm_reindex]

/-- Proves that the state-dependent ceiling budget achieves trace-norm error at most `ε`, has
resource tuple `(n, n, n, 0)`, and satisfies `n ≤ 16t²/ε + 1`. This supplies explicit
precision accounting for [LloydMohseniRebentrost2014]. -/
theorem supNormTightCopyBudget : SupNormTightCopyBudget := by
  intro D ρ σ t ε hρ hσ hε
  (try dsimp only)
  let a := 8*t^2*Matrix.traceNorm (ρ-σ)/ε
  let n := max 1 (Nat.ceil a)
  have hn : 0 < n := lt_of_lt_of_le (by decide) (le_max_left _ _)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hX : (TensorGate σ (1:Operator 1)).PosSemidef :=
    Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hσ.1 Matrix.PosSemidef.one
  have ht : Matrix.traceLeft (TensorGate σ (1:Operator 1)) = 1 := by
    ext i j
    simp only [Matrix.traceLeft, tensorGate_apply, ← Finset.sum_mul]
    change Matrix.trace σ * (1:Operator 1) i j = (1:Operator 1) i j
    rw [hσ.2, one_mul]
  have hf : Matrix.traceNorm (TensorGate σ (1:Operator 1)-
      TensorGate ρ (Matrix.traceLeft (TensorGate σ (1:Operator 1)))) =
      Matrix.traceNorm (ρ-σ) := by
    rw [ht, tensorGate_sub_left, traceNorm_tensor_one]
    rw [show σ-ρ = -(ρ-σ) by abel, Matrix.traceNorm_neg]
  have hg := copy_state_dependent_fresh_global_error D 1 ρ t n
    (TensorGate σ (1:Operator 1)) hρ hX hn
  rw [hf] at hg
  have htrace0 := Matrix.traceNorm_nonneg (ρ-σ)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have han : a ≤ (n:ℝ) := (Nat.le_ceil a).trans (by exact_mod_cast le_max_right 1 (Nat.ceil a))
  have hbound : 8*t^2/(n:ℝ)*Matrix.traceNorm (ρ-σ) ≤ ε := by
    have hh : 8*t^2*Matrix.traceNorm (ρ-σ) ≤ (n:ℝ)*ε :=
      (div_le_iff₀ hε).mp han
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnr).mpr
    simpa only [mul_comm] using hh
  have hnormρ : Matrix.traceNorm (TensorGate ρ (1:Operator 1)) = 1 := by
    rw [traceNorm_tensorGate ρ hρ.1 _ Matrix.PosSemidef.one,
      density_traceNorm_eq_one ρ hρ]
    norm_num [psd_traceNorm_eq_trace _ Matrix.PosSemidef.one, Matrix.trace]
  have hnormσ : Matrix.traceNorm (TensorGate σ (1:Operator 1)) = 1 := by
    rw [traceNorm_tensorGate σ hσ.1 _ Matrix.PosSemidef.one,
      density_traceNorm_eq_one σ hσ]
    norm_num [psd_traceNorm_eq_trace _ Matrix.PosSemidef.one, Matrix.trace]
  have hnorm : Matrix.traceNorm (ρ-σ) ≤ 2 := by
    have hh := traceNorm_sub_le (TensorGate ρ (1:Operator 1)) (TensorGate σ (1:Operator 1))
    rw [hnormρ, hnormσ, tensorGate_sub_left, traceNorm_tensor_one] at hh
    linarith
  have hab : a ≤ 16*t^2/ε := by
    dsimp [a]
    apply (div_le_div_iff_of_pos_right hε).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0≤8*t^2 by positivity)]
  have hceil : (Nat.ceil a : ℝ) ≤ a+1 := le_of_lt (Nat.ceil_lt_add_one ha0)
  have hnupper : (n:ℝ) ≤ 16*t^2/ε+1 := by
    dsimp [n]
    rw [Nat.cast_max]
    apply max_le
    · have hh : 0 ≤ 16*t^2/ε := by positivity
      linarith
    · linarith
  exact ⟨hg.trans hbound, by rw [freshCopyResourceCounts_eq, List.length_replicate], hnupper⟩
end Qatlib.Concepts.CopyEvolution.CopyExponent
