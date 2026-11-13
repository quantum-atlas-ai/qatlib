/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Diagonal Gibbs distributions and Metropolis kernels

`diagonalGibbsDist` normalizes the finite Boltzmann weights and `thermalKernel` combines uniform
proposals with Metropolis acceptance. The resulting kernel is a transition matrix, reversible
and stationary for the Gibbs distribution.

For nonnegative inverse temperature and energies in `[0, R]`,
`diagonal_metropolis_derived_minorization` supplies an explicit Gibbs minorization factor `exp
(-β * R)`. See [TemmeEtAl2011] for background.

## Main statements

* `diagonal_metropolis_transition_reversible`: The uniform-proposal Metropolis kernel is
  stochastic, reversible, and stationary for the Gibbs distribution, with the stated
  off-diagonal entries.
* `diagonal_metropolis_derived_minorization`: For `β ≥ 0` and energies in `[0, R]`, the positive
  factor `exp (-β * R)` is at most one and minorizes every kernel row by the Gibbs distribution.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath

open Matrix

open scoped ComplexOrder

/-- The finite partition function obtained by summing the Boltzmann weights `exp (-β * E j)`. -/
noncomputable def diagonalGibbsPartition (D : ℕ) (E : Fin D → ℝ) (β : ℝ) : ℝ :=
  ∑ j : Fin D, Real.exp (-β*E j)

/-- The finite Gibbs partition function is strictly positive when the state space is nonempty. -/
theorem diagonalGibbsPartition_pos (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    0 < diagonalGibbsPartition D E β :=
  Finset.sum_pos' (fun _ _ => Real.exp_nonneg _)
    ⟨⟨0, hD⟩, Finset.mem_univ _, Real.exp_pos _⟩

/-- The finite probability distribution proportional to the Boltzmann weights `exp (-β * E i)`. -/
noncomputable def diagonalGibbsDist (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    FinDist (Fin D) where
  prob i := Real.exp (-β*E i) / diagonalGibbsPartition D E β
  nonneg i := div_nonneg (Real.exp_nonneg _) (le_of_lt (diagonalGibbsPartition_pos D hD E β))
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (diagonalGibbsPartition_pos D hD E β).ne'

/-- The diagonal operator whose diagonal entries are the finite Gibbs probabilities. -/
noncomputable def diagonalGibbsDensity (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    Operator D :=
  Matrix.diagonal fun i => ((diagonalGibbsDist D hD E β).prob i : ℂ)

/-- The Metropolis acceptance factor `min 1 (exp (-β * (E j - E i)))`. -/
noncomputable def thermalAcceptance {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) : ℝ :=
  min 1 (Real.exp (-β*(E j - E i)))

/-- Every Metropolis acceptance factor is strictly positive. -/
theorem thermalAcceptance_pos {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) :
    0 < thermalAcceptance E β i j :=
  lt_min_iff.mpr ⟨zero_lt_one, Real.exp_pos _⟩

/-- Every Metropolis acceptance factor is at most one. -/
theorem thermalAcceptance_le_one {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) :
    thermalAcceptance E β i j ≤ 1 :=
  min_le_left _ _

/-- The uniform-proposal Metropolis kernel, with its diagonal chosen to make each row sum to
one. -/
noncomputable def thermalKernel (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) : ℝ :=
  if i = j then 1 - ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j' / (D : ℝ)
  else thermalAcceptance E β i j / (D : ℝ)

/-- For distinct states, the Metropolis kernel entry is the acceptance factor divided by the
state-space size. -/
theorem thermalKernel_offdiag (D : ℕ) (E : Fin D → ℝ) (β : ℝ) {i j : Fin D} (hij : i ≠ j) :
    thermalKernel D E β i j = thermalAcceptance E β i j / (D : ℝ) :=
  ite_eq_right hij

/-- The Gibbs probability of a state is its Boltzmann weight divided by the partition function. -/
theorem diagonalGibbsDist_prob (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    (diagonalGibbsDist D hD E β).prob i
      = Real.exp (-β*E i)/diagonalGibbsPartition D E β := rfl

/-- The Gibbs density is the diagonal matrix of the Gibbs distribution's probabilities. -/
theorem diagonalGibbsDensity_eq (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    diagonalGibbsDensity D hD E β
      = Matrix.diagonal (fun i => ((diagonalGibbsDist D hD E β).prob i : ℂ)) := rfl

/-- Multiplying an exponential weight by a capped exponential ratio gives the minimum of the two
exponential weights. -/
private theorem exp_mul_min_comm (x y : ℝ) :
    Real.exp x * min 1 (Real.exp (y - x)) = min (Real.exp x) (Real.exp y) := by
  rcases le_or_gt (Real.exp (y - x)) 1 with h | h
  · have hxy : y ≤ x := by
      have h0 : Real.exp (y - x) ≤ Real.exp 0 := by simpa using h
      have := Real.exp_le_exp.mp h0
      linarith
    have hsum : x + (y - x) = y := by ring
    rw [min_eq_right h, ← Real.exp_add, hsum, min_eq_right (Real.exp_le_exp.mpr hxy)]
  · have hxy : x ≤ y := by
      have h0 : Real.exp 0 < Real.exp (y - x) := by simpa using h
      have := Real.exp_lt_exp.mp h0
      linarith
    rw [min_eq_left h.le, mul_one, min_eq_left (Real.exp_le_exp.mpr hxy)]

/-- The Metropolis acceptance factors satisfy detailed balance with the unnormalized Boltzmann
weights. -/
theorem thermalAcceptance_detailed {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) :
    Real.exp (-β*E i) * thermalAcceptance E β i j
      = Real.exp (-β*E j) * thermalAcceptance E β j i := by
  have hxy : (-β*E j : ℝ) - (-β*E i) = -β*(E j - E i) := by ring
  have hyx : (-β*E i : ℝ) - (-β*E j) = -β*(E i - E j) := by ring
  rw [thermalAcceptance, thermalAcceptance, ← hxy, ← hyx]
  rw [exp_mul_min_comm (-β*E i) (-β*E j), exp_mul_min_comm (-β*E j) (-β*E i), min_comm]

/-- Finite nonempty Gibbs weights are strictly positive and normalize to a diagonal density
operator. -/
theorem diagonal_gibbs_weight_density (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    (∀ i : Fin D, (diagonalGibbsDist D hD E β).prob i =
      Real.exp (-β*E i)/(∑ j : Fin D, Real.exp (-β*E j)) ∧
      0 < (diagonalGibbsDist D hD E β).prob i) ∧
    diagonalGibbsDensity D hD E β =
      Matrix.diagonal (fun i => ((diagonalGibbsDist D hD E β).prob i : ℂ)) ∧
    IsDensityOperator (diagonalGibbsDensity D hD E β) := by
  refine ⟨fun i => ⟨rfl, div_pos (Real.exp_pos _) (diagonalGibbsPartition_pos D hD E β)⟩,
    rfl, ⟨?_, ?_⟩⟩
  · exact Matrix.PosSemidef.diagonal fun i =>
      RCLike.ofReal_nonneg.mpr ((diagonalGibbsDist D hD E β).nonneg i)
  · rw [diagonalGibbsDensity, Matrix.trace_diagonal]
    exact_mod_cast (diagonalGibbsDist D hD E β).sum_one

/-- Each diagonal Metropolis kernel entry is at least the reciprocal of the nonzero state-space
size. -/
private theorem thermalKernel_diag_ge (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i : Fin D) : 1/(D : ℝ) ≤ thermalKernel D E β i i := by
  have hDpos : (0:ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hones : ∑ _ ∈ Finset.univ.erase i, (1:ℝ) = ((Finset.univ.erase i).card : ℝ) := by
    simp [Finset.sum_const]
  have hsum : ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j'
      ≤ ((Finset.univ.erase i).card : ℝ) := by
    calc ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j'
        ≤ ∑ _ ∈ Finset.univ.erase i, (1:ℝ) :=
          Finset.sum_le_sum fun j' _ => thermalAcceptance_le_one E β i j'
      _ = ((Finset.univ.erase i).card : ℝ) := hones
  have hcard : (Finset.univ.erase i).card = D - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hsum' : ((Finset.univ.erase i).card : ℝ) = ((D:ℝ)-1) := by
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
  have hfinal : ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j' / (D : ℝ)
      = (∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j')/(D : ℝ) :=
    (Finset.sum_div (Finset.univ.erase i) (fun j' => thermalAcceptance E β i j') (D : ℝ)).symm
  have hT : ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j' / (D : ℝ)
      ≤ ((D:ℝ)-1)/(D : ℝ) := by
    rw [hfinal, div_le_div_iff_of_pos_right hDpos]
    exact hsum.trans (le_of_eq hsum')
  have hid : (1:ℝ) - ((D:ℝ)-1)/(D : ℝ) - 1/(D : ℝ) = 0 := by field_simp; ring
  rw [thermalKernel, ite_eq_left rfl]
  linarith

/-- Every entry of the nonempty finite Metropolis kernel is nonnegative. -/
private theorem thermalKernel_nonneg (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i j : Fin D) : 0 ≤ thermalKernel D E β i j := by
  by_cases hij : i = j
  · subst j
    exact le_trans (div_nonneg zero_le_one (by exact_mod_cast hD.le))
      (thermalKernel_diag_ge D hD E β i)
  · rw [thermalKernel_offdiag D E β hij]
    exact div_nonneg (thermalAcceptance_pos E β i j).le (by exact_mod_cast hD.le)

/-- Every row of the nonempty finite Metropolis kernel sums to one. -/
private theorem thermalKernel_row_sum (D : ℕ) (_hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i : Fin D) : ∑ j : Fin D, thermalKernel D E β i j = 1 := by
  have hins : (Finset.univ : Finset (Fin D)) = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  have hni : i ∉ Finset.univ.erase i := Finset.notMem_erase i Finset.univ
  rw [hins, Finset.sum_insert hni]
  have hdiag : thermalKernel D E β i i
      = 1 - ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E β i j' / (D : ℝ) :=
    ite_eq_left rfl
  have hoff : ∀ j ∈ Finset.univ.erase i,
      thermalKernel D E β i j = thermalAcceptance E β i j / (D : ℝ) :=
    fun j hj => thermalKernel_offdiag D E β (Ne.symm (Finset.ne_of_mem_erase hj))
  rw [hdiag, Finset.sum_congr rfl hoff]
  linarith

/-- The finite Gibbs distribution and Metropolis kernel satisfy detailed balance. -/
private theorem thermal_kernel_detailed_balance (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β : ℝ) (i j : Fin D) :
    (diagonalGibbsDist D hD E β).prob i * thermalKernel D E β i j
      = (diagonalGibbsDist D hD E β).prob j * thermalKernel D E β j i := by
  by_cases hij : i = j
  · subst j; rfl
  have hZ : (diagonalGibbsPartition D E β) ≠ 0 := (diagonalGibbsPartition_pos D hD E β).ne'
  have hD' : ((D : ℝ)) ≠ 0 := by exact_mod_cast hD.ne'
  rw [diagonalGibbsDist_prob D hD E β i, diagonalGibbsDist_prob D hD E β j,
    thermalKernel_offdiag D E β hij, thermalKernel_offdiag D E β (Ne.symm hij)]
  have hL : (Real.exp (-β*E i)/diagonalGibbsPartition D E β)
      * (thermalAcceptance E β i j/(D:ℝ))
      = (Real.exp (-β*E i) * thermalAcceptance E β i j)
        /(diagonalGibbsPartition D E β*(D:ℝ)) := by
    field_simp
  have hR : (Real.exp (-β*E j)/diagonalGibbsPartition D E β)
      * (thermalAcceptance E β j i/(D:ℝ))
      = (Real.exp (-β*E j) * thermalAcceptance E β j i)
        /(diagonalGibbsPartition D E β*(D:ℝ)) := by
    field_simp
  rw [hL, hR, div_eq_div_iff (mul_ne_zero hZ hD') (mul_ne_zero hZ hD'),
    thermalAcceptance_detailed E β i j]

/-- The uniform-proposal Metropolis kernel is stochastic, reversible, and stationary for the
Gibbs distribution, with the stated off-diagonal entries. -/
theorem diagonal_metropolis_transition_reversible (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β : ℝ) :
    IsTransitionMatrix (thermalKernel D E β) ∧
    IsReversible (thermalKernel D E β) (diagonalGibbsDist D hD E β).prob ∧
    IsStationary (thermalKernel D E β) (diagonalGibbsDist D hD E β).prob ∧
    (∀ i j : Fin D, i≠j → thermalKernel D E β i j = thermalAcceptance E β i j/(D : ℝ)) := by
  refine ⟨⟨fun i j => thermalKernel_nonneg D hD E β i j,
      fun i => thermalKernel_row_sum D hD E β i⟩,
    fun i j => thermal_kernel_detailed_balance D hD E β i j, ?_,
    fun i j hij => thermalKernel_offdiag D E β hij⟩
  exact reversible_stationary ⟨fun i j => thermalKernel_nonneg D hD E β i j,
      fun i => thermalKernel_row_sum D hD E β i⟩
    ⟨(diagonalGibbsDist D hD E β).nonneg, (diagonalGibbsDist D hD E β).sum_one⟩
    fun i j => thermal_kernel_detailed_balance D hD E β i j

/-- For `β ≥ 0` and energies in `[0, R]`, the positive factor `exp (-β * R)` is at most one and
minorizes every kernel row by the Gibbs distribution. -/
theorem diagonal_metropolis_derived_minorization (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (β R : ℝ) (hβ : 0 ≤ β) (hR : 0 ≤ R) (hE : ∀ i, 0 ≤ E i ∧ E i ≤ R) :
    0 < Real.exp (-β*R) ∧ Real.exp (-β*R) ≤ 1 ∧
    (∀ i j : Fin D, Real.exp (-β*R)*(diagonalGibbsDist D hD E β).prob j
      ≤ thermalKernel D E β i j) := by
  have hZpos : 0 < diagonalGibbsPartition D E β := diagonalGibbsPartition_pos D hD E β
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD

  have hebnd : ∀ k : Fin D, Real.exp (-β*R) ≤ Real.exp (-β*E k)
      ∧ Real.exp (-β*E k) ≤ 1 := by
    intro k
    refine ⟨Real.exp_le_exp.mpr (by nlinarith [hβ, hR, (hE k).2]), ?_⟩
    have h1 : (-β:ℝ)*E k ≤ 0 := by nlinarith [hβ, (hE k).1]
    exact le_trans (Real.exp_le_exp.mpr h1) (by simp)

  have hZlb : (D : ℝ)*Real.exp (-β*R) ≤ diagonalGibbsPartition D E β := by
    have hsum : (D : ℝ)*Real.exp (-β*R) = ∑ k : Fin D, Real.exp (-β*R) := by
      simp [Finset.sum_const]
    rw [hsum]
    exact Finset.sum_le_sum fun k _ => (hebnd k).1

  have haccept : ∀ i j : Fin D, Real.exp (-β*E j) ≤ thermalAcceptance E β i j := by
    intro i j
    have hnonneg : (0:ℝ) ≤ β*E i := mul_nonneg hβ (hE i).1
    have harg : (-β:ℝ)*E j ≤ -β*(E j - E i) := by
      have hopen : -β*(E j - E i) = -β*E j + β*E i := by ring
      rw [hopen]
      linarith
    exact le_min ((hebnd j).2) (Real.exp_le_exp.mpr harg)
  have hR0 : (-β:ℝ)*R ≤ 0 := by nlinarith
  refine ⟨Real.exp_pos _, le_trans (Real.exp_le_exp.mpr hR0) (by simp), ?_⟩
  · intro i j
    have hDe : ∀ k : Fin D, (D : ℝ)*Real.exp (-β*R)*Real.exp (-β*E k)
        ≤ diagonalGibbsPartition D E β := by
      intro k
      calc (D : ℝ)*Real.exp (-β*R)*Real.exp (-β*E k)
          = Real.exp (-β*E k)*((D : ℝ)*Real.exp (-β*R)) := by ring
        _ ≤ 1*((D : ℝ)*Real.exp (-β*R)) := by
            refine mul_le_mul_of_nonneg_right ((hebnd k).2) ?_
            positivity
        _ = (D : ℝ)*Real.exp (-β*R) := by ring
        _ ≤ diagonalGibbsPartition D E β := hZlb
    by_cases hij : i = j
    · subst j
      rw [diagonalGibbsDist_prob D hD E β, mul_div_assoc', div_le_iff₀ hZpos]
      calc Real.exp (-β*R)*Real.exp (-β*E i)
          ≤ diagonalGibbsPartition D E β/(D : ℝ) := by
            rw [le_div_iff₀ hDpos]
            calc (Real.exp (-β*R)*Real.exp (-β*E i))*(D : ℝ)
                = (D : ℝ)*Real.exp (-β*R)*Real.exp (-β*E i) := by ring
              _ ≤ diagonalGibbsPartition D E β := hDe i
        _ ≤ thermalKernel D E β i i*diagonalGibbsPartition D E β := by
            have h1 : diagonalGibbsPartition D E β/(D : ℝ)
                = (1/(D : ℝ))*diagonalGibbsPartition D E β := by
              rw [div_eq_mul_one_div]
              ring
            rw [h1]
            exact mul_le_mul_of_nonneg_right (thermalKernel_diag_ge D hD E β i) hZpos.le
    · rw [diagonalGibbsDist_prob D hD E β, mul_div_assoc',
        thermalKernel_offdiag D E β hij, div_le_iff₀ hZpos, div_mul_eq_mul_div,
        le_div_iff₀ hDpos]
      have hkey : (D : ℝ)*Real.exp (-β*R)*Real.exp (-β*E j)
          ≤ thermalAcceptance E β i j*diagonalGibbsPartition D E β := by
        calc (D : ℝ)*Real.exp (-β*R)*Real.exp (-β*E j)
            ≤ (D : ℝ)*Real.exp (-β*R)*thermalAcceptance E β i j := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact haccept i j
          _ = thermalAcceptance E β i j*((D : ℝ)*Real.exp (-β*R)) := by ring
          _ ≤ thermalAcceptance E β i j*diagonalGibbsPartition D E β :=
              mul_le_mul_of_nonneg_left hZlb (thermalAcceptance_pos E β i j).le
      calc Real.exp (-β*R)*Real.exp (-β*E j)*(D : ℝ)
          = (D : ℝ)*Real.exp (-β*R)*Real.exp (-β*E j) := by ring
        _ ≤ thermalAcceptance E β i j*diagonalGibbsPartition D E β := hkey

end Qatlib.Concepts.GibbsMetropolis.RationalBath
