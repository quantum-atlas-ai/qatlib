module

public import Qatlib.Papers.CommGibbsSamp14.GibbsStructure.QubitGibbs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Consumer checks for the commuting Gibbs sampler increment

The abstract gap and mixing theorems are instantiated on an explicit finite-temperature
two-level Gibbs state `p = (3/4, 1/4)` and on the two-site product state `p ⊗ p`, all on
non-degenerate finite types.
-/

open Qatlib.Papers.CommGibbsSamp14.GibbsStructure
open scoped InnerProductSpace

namespace QatlibTests.CommGibbsSamp14GibbsConsumer

noncomputable section

/-- The two-level Gibbs weight at inverse temperature `log 3` and energies `0, 1`. -/
def w34 : GibbsWeight (Fin 2) := qubitGibbsWeight (Real.log 3) ![0, 1]

/-- The ground state has Gibbs probability `3/4`. -/
theorem w34_weight_zero : w34.weight 0 = 3 / 4 := by
  norm_num [w34, qubitGibbsWeight, qubitWeight, Fin.sum_univ_two,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- The excited state has Gibbs probability `1/4`. -/
theorem w34_weight_one : w34.weight 1 = 1 / 4 := by
  norm_num [w34, qubitGibbsWeight, qubitWeight, Fin.sum_univ_two,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- The observable `f(0) = 1`, `f(1) = -1`, with Gibbs mean `1/2`. -/
def f0 : Fin 2 → ℝ := ![1, -1]

/-- The nonconstant observable has variance `3/4` in the Gibbs state. -/
theorem f0_variance :
    rhoInner w34 (f0 - qubitExpect w34 f0) (f0 - qubitExpect w34 f0) = 3 / 4 := by
  simp only [rhoInner, qubitExpect, Fin.sum_univ_two, f0, Pi.sub_apply]
  rw [w34_weight_zero, w34_weight_one]
  norm_num

/-- The squared `L²(ρ)` norm of the centred observable is `3/4`. -/
theorem f0_norm_sq :
    rhoNorm w34 (f0 - qubitExpect w34 f0) ^ 2 = 3 / 4 := by
  rw [rhoNorm_sq, rhoNormSq_def, f0_variance]

/-- Proposition 10 consumer: the concrete conditional expectation is unital, preserves the
Gibbs expectation and is a contraction. -/
theorem consumer_conditionalExpectation :
    qubitExpect w34 (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) ∧
      rhoInner w34 (qubitExpect w34 f0) (fun _ => (1 : ℝ)) =
        rhoInner w34 f0 (fun _ => (1 : ℝ)) ∧
      rhoInner w34 (qubitExpect w34 f0) (qubitExpect w34 f0) ≤ rhoInner w34 f0 f0 :=
  ⟨qubitExpect_unital w34, qubitExpect_state w34 f0,
    (qubitExpect_isOrthProj w34).contract f0⟩

/-- The single-site Dirichlet form attains the gap bound at positive variance. -/
theorem consumer_qubit_gap :
    rhoInner w34 f0 (-(qubitExpect w34 f0 - f0)) = 3 / 4 ∧
      rhoInner w34 f0 (-(qubitExpect w34 f0 - f0)) ≥
        1 * rhoInner w34 (f0 - qubitExpect w34 f0) (f0 - qubitExpect w34 f0) := by
  refine ⟨?_, qubit_spectralGap w34 f0⟩
  rw [qubit_dirichlet_identity, f0_variance]

/-- Exact exponential decay of the concrete single-site flow. -/
theorem consumer_qubit_flow (t : ℝ) :
    rhoNorm w34 (heatBathFlow w34 (qubitExpect w34) t f0 - qubitExpect w34 f0) =
      Real.exp (-t) * rhoNorm w34 (f0 - qubitExpect w34 f0) :=
  qubit_flow_decay w34 f0 t

/-- An observable of the two-site system that only depends on the first coordinate. -/
def pairState : Fin 2 × Fin 2 → ℝ := fun x => if x.1 = 0 then 1 else -1

/-- The two-site observable has positive variance relative to the full Gibbs mean. -/
theorem pairState_variance :
    rhoInner (productWeight w34)
      (pairState - (pairFamily w34).projList [false, true] pairState)
      (pairState - (pairFamily w34).projList [false, true] pairState) = 3 / 4 := by
  rw [pair_projList_eq_mean]
  simp only [rhoInner, productWeight, pairState, Pi.sub_apply, mul_one]
  simp only [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
  norm_num [w34_weight_zero, w34_weight_one]

/-- The two-site Dirichlet form controls the variance of a nonconstant observable. -/
theorem consumer_pair_gap :
    rhoInner (productWeight w34) pairState (-((pairFamily w34).gen [false, true] pairState)) ≥
      3 / 4 := by
  simpa only [one_mul, pairState_variance] using pair_spectralGap w34 pairState

/-- The single-site commuting family on `Fin 1`, used to instantiate the uniform gap
theorem. -/
def qubitFamily : CommutingFamily (Fin 1) (Fin 2) where
  weight := w34
  E _ := qubitExpect w34
  proj _ := qubitExpect_isOrthProj w34
  commute i j f := by
    fin_cases i
    fin_cases j
    rfl
  unital _ := qubitExpect_unital w34

/-- The uniform gap theorem at the concrete one-site lattice: the constant is extracted
outside the universal quantifiers and applied to a non-degenerate instance. -/
theorem consumer_uniform_gap :
    ∃ lam : ℝ, 0 < lam ∧
      rhoInner w34 f0 (-(qubitFamily.gen [0] f0)) ≥
        lam * rhoInner w34 (f0 - qubitFamily.projList [0] f0)
          (f0 - qubitFamily.projList [0] f0) := by
  obtain ⟨lam, hpos, h⟩ := exists_uniform_spectralGap
  exact ⟨lam, hpos,
    h 1 (by norm_num) [0] (by simp) (by simp) (Fin 2) qubitFamily f0⟩

/-- The uniform decay bound applies to the same nonconstant two-level observable. -/
theorem consumer_uniform_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 ≤ t →
      rhoNorm w34 (heatBathFlow w34 (qubitExpect w34) t f0 - qubitExpect w34 f0) ≤
        C * Real.exp (-t) * rhoNorm w34 (f0 - qubitExpect w34 f0) := by
  obtain ⟨C, hpos, h⟩ := exists_uniform_heatBath_decay
  exact ⟨C, hpos, fun t ht => h (Fin 2) w34 (qubitExpect w34) (qubitExpect_isOrthProj w34)
    t ht f0⟩

end

end QatlibTests.CommGibbsSamp14GibbsConsumer
