/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticNoncommutingLCHS
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ApproximationAlgorithms

/-!
# Finite Hamiltonian passage from a heat-kernel entry

A positive matrix entry of `staticNonunitaryEvolution` forces a substantial entry of a
Hamiltonian evolution at a finite quadrature node. The grid and cutoff estimates turn this into
a bounded evolution time; symmetry permits a nonnegative time with a Born success lower bound.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `heat_entry_forces_bounded_time`: produces a time with magnitude at most `33 * T / p`.
* `heat_entry_forces_born_success`: gives a nonnegative time with success at least `p ^ 2 / 16`.

## References

* [An et al., 2023][AnLiuLin2023]
-/

open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Concepts.LchsSimulation.StaticLchs.FinitePassage

/-- Every static LCHS grid node lies in the interval `[-K, K]` when the node count is positive. -/
theorem grid_abs_le (K N : ℕ) (hN : 0 < N) (j : Fin N) :
    |staticLchsGrid K N j| ≤ (K : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hj : (j.val : ℝ) ≤ N := by exact_mod_cast j.isLt.le
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · dsimp [staticLchsGrid]
    have hnon : 0 ≤ 2 * (K : ℝ) * j.val / N := by positivity
    linarith
  · dsimp [staticLchsGrid]
    have hm : (2 * (K : ℝ) * j.val) / N ≤ 2 * K := by
      rw [div_le_iff₀ hNr]
      nlinarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg _]
    linarith

/-- A real heat-evolution entry at least `p`, for `0 < p ≤ 1`, yields a finite LCHS node whose
Hamiltonian evolution entry has norm at least `p / 4`. -/
theorem heat_entry_forces_unitary_node {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (T p : ℝ) (hL : L.PosSemidef) (hT : 0 ≤ T)
    (hp : 0 < p) (hp1 : p ≤ 1) (target start : I)
    (hsignal : p ≤ (staticNonunitaryEvolution L 0 T target start).re) :
    ∃ j : Fin (staticLchsNodes L T (p / 2)),
      p / 4 ≤ ‖hamiltonianEvolution
        (staticLchsGrid (staticLchsCutoff (p / 2)) (staticLchsNodes L T (p / 2)) j • L)
        T target start‖ := by
  classical
  let K := staticLchsCutoff (p / 2)
  let N := staticLchsNodes L T (p / 2)
  let Q := staticLchsQuadrature L 0 T K N
  let U := fun j : Fin N => hamiltonianEvolution (staticLchsGrid K N j • L) T target start
  have hε : 0 < p / 2 := by linarith
  obtain ⟨hK, hN, hbudget⟩ := static_lchs_computed_quadrature_budget L T (p / 2) hT hε
  have hmass := (static_lchs_computed_coefficient_mass L T (p / 2) hT hε (by linarith)).2
  have herr : ‖Q - staticNonunitaryEvolution L 0 T‖ ≤ p / 2 := by
    exact (static_noncommuting_lchs_quadrature_error I L 0 T K N hL
      (by simp) hT hK hN).trans hbudget
  have he : ‖Q target start - staticNonunitaryEvolution L 0 T target start‖ ≤ p / 2 :=
    (norm_entry_le_l2_norm (Q - staticNonunitaryEvolution L 0 T) target start).trans herr
  have htri : ‖staticNonunitaryEvolution L 0 T target start‖ ≤
      ‖Q target start‖ + ‖Q target start - staticNonunitaryEvolution L 0 T target start‖ := by
    calc
      _ = ‖Q target start - (Q target start - staticNonunitaryEvolution L 0 T target start)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hsignal_norm :=
      (Complex.re_le_norm (staticNonunitaryEvolution L 0 T target start)).trans htri
  have hQ : p / 2 ≤ ‖Q target start‖ := by linarith
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖U j‖) hne
  have hsum : ‖Q target start‖ ≤ coefficientMass (staticLchsCoeff K N) * ‖U j‖ := by
    change ‖(staticLchsQuadrature L 0 T K N) target start‖ ≤ _
    simp only [staticLchsQuadrature, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, zero_add]
    calc
      _ ≤ ∑ i : Fin N, ‖staticLchsCoeff K N i * U i‖ := norm_sum_le _ _
      _ = ∑ i : Fin N, ‖staticLchsCoeff K N i‖ * ‖U i‖ := by simp only [norm_mul]
      _ ≤ ∑ i : Fin N, ‖staticLchsCoeff K N i‖ * ‖U j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hj i hi) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hprod : coefficientMass (staticLchsCoeff K N) * ‖U j‖ ≤ 2 * ‖U j‖ :=
    mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
  exact ⟨j, by dsimp only [U] at hsum hprod; linarith⟩

/-- Scaling a Hamiltonian by `a` is equivalent to scaling its evolution time by `a`. -/
theorem scalar_hamiltonian_time {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (a T : ℝ) :
    hamiltonianEvolution (a • L) T = hamiltonianEvolution L (a * T) := by
  unfold hamiltonianEvolution
  have he : (-Complex.I * (T : ℂ)) • (a • L) =
      (-Complex.I * ((a * T : ℝ) : ℂ)) • L := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [he]

/-- For positive `p`, the static LCHS cutoff at accuracy `p / 2` is at most `32 / p + 1`. -/
theorem cutoff_le (p : ℝ) (hp : 0 < p) :
    (staticLchsCutoff (p / 2) : ℝ) ≤ 32 / p + 1 := by
  have he : 16 / (p / 2) = 32 / p := by ring
  simp only [staticLchsCutoff, he, Nat.cast_max, Nat.cast_one]
  apply max_le
  · have h : 0 ≤ 32 / p := by positivity
    linarith
  · exact (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 32 / p)).le

/-- A heat-evolution entry at least `p`, for `0 < p ≤ 1`, yields a Hamiltonian evolution time of
magnitude at most `33 * T / p` with entry norm at least `p / 4`. -/
theorem heat_entry_forces_bounded_time {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (T p : ℝ) (hL : L.PosSemidef) (hT : 0 ≤ T)
    (hp : 0 < p) (hp1 : p ≤ 1) (target start : I)
    (hsignal : p ≤ (staticNonunitaryEvolution L 0 T target start).re) :
    ∃ τ : ℝ, |τ| ≤ 33 * T / p ∧ p / 4 ≤ ‖hamiltonianEvolution L τ target start‖ := by
  obtain ⟨j, hj⟩ := heat_entry_forces_unitary_node L T p hL hT hp hp1 target start hsignal
  let K := staticLchsCutoff (p / 2)
  let N := staticLchsNodes L T (p / 2)
  let a := staticLchsGrid K N j
  have hN : 0 < N := (static_lchs_computed_quadrature_budget L T (p / 2) hT (by linarith)).2.1
  refine ⟨a * T, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hT]
    calc
      |a| * T ≤ (K : ℝ) * T := mul_le_mul_of_nonneg_right (grid_abs_le K N hN j) hT
      _ ≤ (32 / p + 1) * T := mul_le_mul_of_nonneg_right (cutoff_le p hp) hT
      _ ≤ (33 / p) * T := by
        apply mul_le_mul_of_nonneg_right _ hT
        apply (le_div_iff₀ hp).mpr
        have he : (32 / p + 1) * p = 32 + p := by field_simp
        rw [he]
        linarith
      _ = 33 * T / p := by ring
  · rw [← scalar_hamiltonian_time]
    exact hj

/-- For a matrix that is both Hermitian and symmetric, reversing Hamiltonian evolution time
preserves the norm of each matrix entry. -/
theorem opposite_time_entry_norm {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (hH : L.IsHermitian) (hS : L.IsSymm) (t : ℝ) (a b : I) :
    ‖hamiltonianEvolution L (-t) a b‖ = ‖hamiltonianEvolution L t a b‖ := by
  have ha : hamiltonianEvolution L (-t) = (hamiltonianEvolution L t)ᴴ := by
    simp [hamiltonianEvolution, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hH.eq, RCLike.star_def]
  have hs : (hamiltonianEvolution L t).IsSymm := by
    unfold hamiltonianEvolution
    apply Matrix.IsSymm.exp
    change ((-Complex.I * (t : ℂ)) • L)ᵀ = _
    rw [Matrix.transpose_smul, hS.eq]
  rw [ha, Matrix.conjTranspose_apply, norm_star]
  exact congrArg norm (congrArg (fun M => M b a) hs.eq).symm

/-- For a symmetric positive semidefinite Hamiltonian and a heat entry at least `p`, there is a
time in `[0, 33 * T / p]` whose unitary evolution gives a normalized state with target Born
probability at least `p ^ 2 / 16`. -/
theorem heat_entry_forces_born_success {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (T p : ℝ) (hL : L.PosSemidef) (hS : L.IsSymm) (hT : 0 ≤ T)
    (hp : 0 < p) (hp1 : p ≤ 1) (target start : I)
    (hsignal : p ≤ (staticNonunitaryEvolution L 0 T target start).re) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 33 * T / p ∧
      hamiltonianEvolution L t ∈ Matrix.unitaryGroup I ℂ ∧
      Normalized (ApplyGate (hamiltonianEvolution L t) (Ket start)) ∧
      p ^ 2 / 16 ≤ MeasureProb (ApplyGate (hamiltonianEvolution L t) (Ket start)) {target} := by
  obtain ⟨τ, hτ, hpeak⟩ := heat_entry_forces_bounded_time L T p hL hT hp hp1 target start hsignal
  have hn : ‖hamiltonianEvolution L |τ| target start‖ = ‖hamiltonianEvolution L τ target start‖ := by
    by_cases h : 0 ≤ τ
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      exact opposite_time_entry_norm L hL.isHermitian hS τ target start
  have hu : hamiltonianEvolution L |τ| ∈ Matrix.unitaryGroup I ℂ :=
    hamiltonianEvolution_unitary hL.isHermitian _
  refine ⟨|τ|, abs_nonneg _, hτ, hu, normalized_applyGate hu (normalized_ket start), ?_⟩
  have he : MeasureProb (ApplyGate (hamiltonianEvolution L |τ|) (Ket start)) {target} =
      ‖hamiltonianEvolution L |τ| target start‖ ^ 2 := by
    simp only [MeasureProb, Finset.sum_singleton, BornProb, applyGate_eq_mulVec_ket]
  rw [he, hn]
  nlinarith [norm_nonneg (hamiltonianEvolution L τ target start)]

end Qatlib.Concepts.LchsSimulation.StaticLchs.FinitePassage
