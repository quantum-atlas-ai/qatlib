module

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.RealSqrt
import Qatlib.Papers.SparseNetwork13.MainResults.Spectral.ContractProbe
import Qatlib.Papers.SparseNetwork13.MainResults.LowerBound.ParityNetwork
import Qatlib.Papers.SparseNetwork13.MainResults.Spectral.SpectralGapComparison

/-! Concrete consumers of the variational bounds, Euclidean energy, and parity network. -/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.SparseNetwork13.MainResults.Model
open Qatlib.Papers.SparseNetwork13.MainResults.Spectral.ContractProbe (pairMat pairOrth pairMin)
open Qatlib.Papers.SparseNetwork13.MainResults.LowerBound
open Qatlib.Papers.SparseNetwork13.MainResults.Spectral

namespace QatlibTests.SparseNetworkSpectralRegression

/-- Two distinct vertices joined by an edge of unit conductance. -/
private def unitEdge : ElecNetwork (Fin 2) (Fin 1) where
  tail _ := 0
  head _ := 1
  w _ := 1
  w_pos _ := by norm_num
  nonloop _ := by decide

/-- Both endpoints have weighted degree one. -/
private theorem degree_unitEdge (v : Fin 2) : weightedDegree unitEdge v = 1 := by
  fin_cases v <;> norm_num [weightedDegree, unitEdge, Fin.sum_univ_one]

/-- The normalized gap of the unit edge is exactly two. -/
private theorem normalized_gap_unitEdge : lambda2Normalized unitEdge = 2 := by
  have hm : normalizedLaplacian unitEdge = pairMat 1 := by
    ext u v
    fin_cases u <;> fin_cases v <;>
      norm_num [normalizedLaplacian, weightedDegree, laplacian, Matrix.mul_apply,
        Fin.sum_univ_one, incident, weightMatrix, unitEdge, pairMat]
  have ho : degreeOrthogonal unitEdge = pairOrth := by
    ext x
    simp [degreeOrthogonal, pairOrth, Fin.sum_univ_two, degree_unitEdge]
  rw [lambda2Normalized, hm, ho, pairMin, mul_one]

/-- A unit external current enters vertex zero and leaves vertex one. -/
private def balancedCurrent : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![1 / Real.sqrt 2, -1 / Real.sqrt 2]

/-- The current is balanced and has Euclidean norm one. -/
private theorem balanced_current_properties :
    (∑ v, balancedCurrent v) = 0 ∧ ‖balancedCurrent‖ ^ 2 = 1 := by
  constructor
  · simp [Fin.sum_univ_two, balancedCurrent, neg_div]
  · rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (1 / Real.sqrt 2) ^ 2 + (-1 / Real.sqrt 2) ^ 2 = 1
    norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

example : 2 ≤ lambda2 unitEdge := by
  rw [← normalized_gap_unitEdge]
  exact normalized_gap_le_combinatorial_gap unitEdge (fun v => (degree_unitEdge v).ge)

example : lambda2Normalized unitEdge ≤ 2 :=
  normalized_gap_le_two unitEdge (fun v => (degree_unitEdge v).symm ▸ zero_lt_one)

example : (2 : ℝ) / (1 + 2) ≤ lambda2NormalizedMod unitEdge 2 balancedCurrent.ofLp :=
  augmented_normalized_gap_bound unitEdge (fun v => (degree_unitEdge v).ge)
    (by norm_num) normalized_gap_unitEdge.ge balancedCurrent

example : (2 : ℝ) / 3 ≤ lambda2NormalizedMod unitEdge 2 balancedCurrent.ofLp := by
  exact augmented_normalized_gap_ge_third unitEdge (fun v => (degree_unitEdge v).ge)
    (by norm_num) normalized_gap_unitEdge.ge balancedCurrent

example : ‖modifiedLaplacian unitEdge 2 balancedCurrent.ofLp - laplacian unitEdge‖ = 4 := by
  rw [modified_laplacian_sub_norm unitEdge (by norm_num) balancedCurrent,
    balanced_current_properties.2]
  norm_num

example :
    normalizedModifiedLaplacian unitEdge 2 balancedCurrent.ofLp *ᵥ (fun _ => Real.sqrt 3) = 0 := by
  have hdegree (v : Fin 2) : 0 < weightedDegreeMod unitEdge 2 v := by
    norm_num [weightedDegreeMod, degree_unitEdge]
  have h := (augmented_normalized_degree_null unitEdge 2 hdegree balancedCurrent
    balanced_current_properties.1).2
  norm_num [weightedDegreeMod, degree_unitEdge] at h
  exact h

example (x : EuclideanSpace ℝ (Fin 2)) :
    x.ofLp ⬝ᵥ (laplacian unitEdge *ᵥ x.ofLp) = (x 0 - x 1) ^ 2 := by
  rw [laplacian_quadratic_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_one]
  change (Real.sqrt 1 * (x 0 - x 1)) ^ 2 = _
  rw [Real.sqrt_one, one_mul]

example : Fintype.card (ParityVertex 2) = 20 ∧ Fintype.card (ParityEdge 2) = 20 :=
  parity_network_card (n := 2) (by decide)

example :
    let G := parityNetwork (by decide : 0 < 2) ![true, false]
    ∃ e, G.tail e = .inr (2, false) ∧ G.head e = .inr (3, false) := by
  obtain ⟨_, _, _, _, _, _, he⟩ := parity_network_terminals (by decide : 0 < 2) ![true, false]
  exact he

example :
    let bits : Fin 2 → Bool := ![true, false]
    let G := parityNetwork (by decide : 0 < 2) bits
    Relation.ReflTransGen (fun a b => ∃ e, G.tail e = a ∧ G.head e = b)
      (.inl (0, false)) (.inl (Fin.last 2, true)) := by
  dsimp
  exact parity_network_short_walk (by decide) ![true, false] false (Fin.last 2)

example :
    let G := parityNetwork (by decide : 0 < 2) ![true, false]
    Relation.EqvGen (fun a b => ∃ e, G.tail e = a ∧ G.head e = b)
      (.inl (0, true)) (.inr (3, false)) :=
  parity_network_connected (by decide) ![true, false] (.inl (0, true)) (.inr (3, false))

#print axioms laplacian_quadratic_eq_norm_sq
#print axioms modified_laplacian_sub_norm
#print axioms normalized_gap_le_combinatorial_gap
#print axioms normalized_gap_le_two
#print axioms augmented_normalized_gap_bound
#print axioms augmented_normalized_gap_ge_third
#print axioms augmented_normalized_degree_null
#print axioms parity_network_card
#print axioms parity_network_terminals
#print axioms parity_network_short_walk
#print axioms parity_network_connected

end QatlibTests.SparseNetworkSpectralRegression
