/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.BornLaw

/-!
# Positive context-overlap matrices

The overlap matrix of a finite family of contexts is the weighted sum of outer
products of their indicator vectors. Nonnegative context weights make this
matrix positive semidefinite. The same conclusion holds after multiplying the
two matrix indices by arbitrary real vertex weights.

These are Gram-matrix positivity arguments [Bhatia2007], used here in finite
measurement statistics; see [Watrous, *The Theory of Quantum Information*][Watrous2018]
for the quantum statistical setting.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]

/-- The weighted overlap of context indicators, expressed as a sum of rank-one
matrices; see [Bhatia, *Positive Definite Matrices*][Bhatia2007]. -/
def contextOverlap (C : K → Finset V) (q : K → ℝ) : Matrix V V ℝ :=
  fun i j => ∑ k,q k*(if i∈C k then 1 else 0)*(if j∈C k then 1 else 0)

/-- The overlap matrix formed by summing context indicator outer products with nonnegative
weights is positive semidefinite; this is the overlap Gram matrix used in [XuEtAl2026]. -/
theorem contextOverlap_psd (C : K → Finset V) (q : K → ℝ) (hq : ∀ k,0 ≤ q k) :
    (contextOverlap C q).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ (fun k _ =>
    (Matrix.posSemidef_vecMulVec_self_star (fun i : V => if i∈C k then (1:ℝ) else 0)).smul (hq k))
  convert h using 1
  ext i j
  simp [contextOverlap,Matrix.sum_apply,Matrix.vecMulVec_apply]

/-- Vertex weighting preserves positivity when the context weights are
nonnegative [Bhatia2007]. -/
theorem weighted_contextOverlap_psd (C : K → Finset V) (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (a : V → ℝ) :
    (Matrix.of (fun i j => a i*a j*contextOverlap C q i j)).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ (fun k _ =>
    (Matrix.posSemidef_vecMulVec_self_star (fun i : V => a i*(if i∈C k then (1:ℝ) else 0))).smul (hq k))
  convert h using 1
  ext i j
  simp only [contextOverlap,Finset.mul_sum,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
    star_trivial,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end Qatlib.Foundations.FiniteStats.BornEstimator
