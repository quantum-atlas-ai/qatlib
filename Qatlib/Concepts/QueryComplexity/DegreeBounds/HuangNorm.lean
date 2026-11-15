/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.Support
public import Archive.Sensitivity

@[expose] public section
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Two Boolean cube vertices are adjacent exactly when they differ in one coordinate. -/
theorem huang_adjacent_iff {n : ℕ} (x y : Fin n → Bool) :
    y ∈ Sensitivity.Q.adjacent x ↔ (Finset.univ.filter (fun i => x i ≠ y i)).card=1 := by
  classical
  constructor
  · rintro ⟨i,hi,hu⟩
    apply Finset.card_eq_one.mpr
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨fun hj => hu j hj, fun hji => hji ▸ hi⟩
  · intro h
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h
    refine ⟨i,?_,?_⟩
    · have hm : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by rw [hi]; simp
      simpa using hm
    · intro j hj
      have hm : j ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hj]
      rw [hi] at hm
      exact Finset.mem_singleton.mp hm

/-- Expands a coordinate of the Huang operator applied to a vector as a sum over the coordinate
basis. -/
private theorem huang_coordinate_expansion {n : ℕ} (q : Sensitivity.Q n)
    (y : Sensitivity.V n) :
    Sensitivity.ε q (Sensitivity.f n y)=∑ p : Sensitivity.Q n,
      Sensitivity.ε p y * Sensitivity.ε q (Sensitivity.f n (Sensitivity.e p)) := by
  classical
  let h := Sensitivity.dualBases_e_ε n
  have hy : y=∑ p : Sensitivity.Q n, Sensitivity.ε p y • Sensitivity.e p := by
    calc
      y = Module.DualBases.lc _ (h.coeffs y) := (h.lc_coeffs y).symm
      _ = _ := by
        rw [Module.DualBases.lc_def,Finsupp.linearCombination_apply,Finsupp.sum_fintype]
        · simp only [h.coeffs_apply]
        · intro i; simp
  conv_lhs => rw [hy]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- If a subset larger than half the cube has opposite function values on each internal edge,
the squared spectral sensitivity is at least the cube dimension. -/
theorem sensitivity_large_induced_cube_norm (m : ℕ) (g : (Fin (m+1) → Bool) → Bool)
    (H : Set (Sensitivity.Q (m+1))) (hH : H.toFinset.card ≥ 2^m+1)
    (hedge : ∀ x ∈ H, ∀ y ∈ H, y ∈ Sensitivity.Q.adjacent x → g x ≠ g y) :
    (m+1 : ℝ) ≤ spectralSensitivity g ^ 2 := by
  classical
  obtain ⟨y,⟨hyH,hyG⟩,hy0⟩ := Sensitivity.exists_eigenvalue H (by
    simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using hH)
  have hs : ∀ p, p ∉ H → Sensitivity.ε p y=0 := by
    intro p hp
    by_contra he
    exact hp ((Sensitivity.dualBases_e_ε (m+1)).mem_of_mem_span hyH p he)
  have heig := Sensitivity.f_image_g y (by simpa using hyG)
  let r : (Fin (m+1) → Bool) → ℝ := fun q =>
    ∑ p, if (Finset.univ.filter (fun i => q i ≠ p i)).card=1 ∧ g q ≠ g p
      then |Sensitivity.ε p y| else 0
  have hr : ∀ q, 0 ≤ r q := by
    intro q
    dsimp only [r]
    apply Finset.sum_nonneg
    intro p _
    split_ifs <;> positivity
  have hcoord : ∀ q, Real.sqrt (m+1) * |Sensitivity.ε q y| ≤ r q := by
    intro q
    by_cases hq : q ∈ H
    · calc
        _ = |Sensitivity.ε q (Sensitivity.f (m+1) y)| := by
          rw [heig,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
        _ = |∑ p : Sensitivity.Q (m+1),
            Sensitivity.ε p y * Sensitivity.ε q (Sensitivity.f (m+1) (Sensitivity.e p))| := by
          rw [huang_coordinate_expansion]
        _ ≤ ∑ p : Sensitivity.Q (m+1),
            |Sensitivity.ε p y * Sensitivity.ε q (Sensitivity.f (m+1) (Sensitivity.e p))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ r q := by
          apply Finset.sum_le_sum
          intro p _
          rw [abs_mul,Sensitivity.f_matrix p q]
          by_cases hp : p ∈ H
          · by_cases ha : p ∈ Sensitivity.Q.adjacent q
            · have hdiff := hedge q hq p hp ha
              have hcard := (huang_adjacent_iff q p).mp ha
              simp [ha,hcard,hdiff]
            · have hcard : ¬ (Finset.univ.filter (fun i => q i ≠ p i)).card=1 :=
                mt (huang_adjacent_iff q p).mpr ha
              simp [ha,hcard]
          · rw [hs p hp]
            simp
    · rw [hs q hq,abs_zero,mul_zero]
      exact hr q
  let w : QState (Fin (m+1) → Bool) := fun q => ((|Sensitivity.ε q y| : ℝ) : ℂ)
  have hw : 0 < ‖toEuclidean_fromVec w‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply hy0
    apply Sensitivity.epsilon_total
    intro p
    have he := congrArg (fun z : EuclideanSpace ℂ (Fin (m+1) → Bool) => z p) hz
    simpa only [toEuclidean_fromVec_apply,w,PiLp.zero_apply,Complex.ofReal_eq_zero,
      abs_eq_zero] using he
  have hAw : ∀ q, (sensAdjacency g *ᵥ w) q=(r q : ℂ) := by
    intro q
    simp only [Matrix.mulVec,dotProduct,r,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [sensAdjacency,w]
    split_ifs <;> simp
  have hsq : (m+1 : ℝ)*‖toEuclidean_fromVec w‖^2 ≤
      ‖toEuclidean_fromVec (sensAdjacency g *ᵥ w)‖^2 := by
    have h := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin (m+1) → Bool))) =>
      (sq_le_sq₀ (by positivity) (hr q)).mpr (hcoord q))
    simp only [mul_pow,← Finset.mul_sum,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m+1)] at h
    simpa only [norm_toEuclidean_fromVec_sq,w,hAw,Complex.norm_real,
      Real.norm_eq_abs,abs_abs,sq_abs] using h
  have hup := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (l2_norm_mulVec_fromVec_le (sensAdjacency g) w)
  rw [mul_pow] at hup
  have hfin := hsq.trans hup
  change (m+1 : ℝ)*‖toEuclidean_fromVec w‖^2 ≤
    spectralSensitivity g ^ 2 * ‖toEuclidean_fromVec w‖^2 at hfin
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hw)).mp hfin

end Qatlib.Concepts.QueryComplexity.DegreeBounds
