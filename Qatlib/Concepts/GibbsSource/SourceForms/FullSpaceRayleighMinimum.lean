/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapGeometry
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section


/-! # The attained finite-dimensional Rayleigh minimum

The topology on `ι → ℂ` is the ordinary finite product topology. Its default
norm is a supremum norm, so compactness is proved by coordinate bounds;
the Hilbert--Schmidt unit condition is never identified with that default
norm sphere. Nonemptiness is an explicit hypothesis at the generic level.
-/



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Full Norm Sq continuous for the stated finite source data. -/
theorem fullNormSq_continuous : Continuous (fullNormSq (ι := ι)) := by
  unfold fullNormSq dotProduct
  fun_prop

/-- Full Rayleigh continuous for the stated finite source data. -/
theorem fullRayleigh_continuous (M : Matrix ι ι ℂ) : Continuous (fullRayleigh M) := by
  unfold fullRayleigh Matrix.mulVec dotProduct
  fun_prop

/-- Full Star Dot continuous for the stated finite source data. -/
theorem fullStarDot_continuous (g : ι → ℂ) : Continuous (fun z => star g ⬝ᵥ z) := by
  unfold dotProduct
  fun_prop

/-- Full Unit Orthogonal is Closed for the stated finite source data. -/
theorem fullUnitOrthogonal_isClosed (g : ι → ℂ) : IsClosed (fullUnitOrthogonal g) := by
  change IsClosed ({z | fullNormSq z = 1} ∩ {z | star g ⬝ᵥ z = 0})
  exact (isClosed_eq fullNormSq_continuous continuous_const).inter
    (isClosed_eq (fullStarDot_continuous g) continuous_const)

/-- Full Unit Orthogonal is Compact for the stated finite source data. -/
theorem fullUnitOrthogonal_isCompact (g : ι → ℂ) : IsCompact (fullUnitOrthogonal g) := by
  classical
  apply (isCompact_closedBall (0 : ι → ℂ) 1).of_isClosed_subset
    (fullUnitOrthogonal_isClosed g)
  intro z hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hcoord : Complex.normSq (z i) ≤ 1 := by
    calc
      Complex.normSq (z i) ≤ ∑ j, Complex.normSq (z j) :=
        Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
      _ = 1 := (fullNormSq_eq_sum z).symm.trans hz.1
  have hs : ‖z i‖ ^ 2 ≤ 1 := by
    simpa only [Complex.sq_norm] using hcoord
  nlinarith [norm_nonneg (z i)]

/-- The exact infimum has an actual unit, Gibbs-orthogonal minimizing vector. -/
theorem fullRayleighGap_attained (M : Matrix ι ι ℂ) (g : ι → ℂ)
    (hS : (fullUnitOrthogonal g).Nonempty) :
    ∃ z ∈ fullUnitOrthogonal g,
      fullRayleighGap M g = fullRayleigh M z ∧
        ∀ w ∈ fullUnitOrthogonal g, fullRayleigh M z ≤ fullRayleigh M w := by
  exact (fullUnitOrthogonal_isCompact g).exists_sInf_image_eq_and_le hS
    (fullRayleigh_continuous M).continuousOn

/-- Full Rayleigh Gap le for the stated finite source data. -/
theorem fullRayleighGap_le (M : Matrix ι ι ℂ) (g z : ι → ℂ)
    (hz : z ∈ fullUnitOrthogonal g) : fullRayleighGap M g ≤ fullRayleigh M z := by
  exact csInf_le
    ((fullUnitOrthogonal_isCompact g).bddBelow_image (fullRayleigh_continuous M).continuousOn)
    (Set.mem_image_of_mem _ hz)

/-- Full Rayleigh Gap nonneg for the stated finite source data. -/
theorem fullRayleighGap_nonneg {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (g : ι → ℂ) (hS : (fullUnitOrthogonal g).Nonempty) :
    0 ≤ fullRayleighGap M g := by
  obtain ⟨z, _, he, _⟩ := fullRayleighGap_attained M g hS
  rw [he]
  exact fullRayleigh_nonneg hM z

/-- Full Rayleigh pos on unit Orthogonal for the stated finite source data. -/
theorem fullRayleigh_pos_on_unitOrthogonal {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (g : ι → ℂ) (hg : g ≠ 0)
    (hker : ∀ z, M *ᵥ z = 0 → ∃ c : ℂ, z = c • g)
    (z : ι → ℂ) (hz : z ∈ fullUnitOrthogonal g) :
    0 < fullRayleigh M z := by
  by_contra hn
  have hq : fullRayleigh M z = 0 :=
    le_antisymm (le_of_not_gt hn) (fullRayleigh_nonneg hM z)
  obtain ⟨c, hc⟩ := hker z ((fullRayleigh_eq_zero_iff hM z).mp hq)
  have hgn : (fullNormSq g : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fullNormSq_pos g hg)
  have ho := hz.2
  rw [hc, dotProduct_smul, fullStarDot_self_eq, smul_eq_mul] at ho
  have hc0 : c = 0 := (mul_eq_zero.mp ho).resolve_right hgn
  have hz0 : z = 0 := by simp [hc, hc0]
  have hnorm := hz.1
  rw [hz0, fullNormSq_zero] at hnorm
  norm_num at hnorm

/-- A PSD matrix with no Gibbs-orthogonal kernel has a strictly positive
attained Rayleigh minimum. -/
theorem fullRayleighGap_pos {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (g : ι → ℂ) (hg : g ≠ 0)
    (hker : ∀ z, M *ᵥ z = 0 → ∃ c : ℂ, z = c • g)
    (hS : (fullUnitOrthogonal g).Nonempty) :
    0 < fullRayleighGap M g := by
  obtain ⟨z, hz, he, _⟩ := fullRayleighGap_attained M g hS
  rw [he]
  exact fullRayleigh_pos_on_unitOrthogonal hM g hg hker z hz

end Qatlib.Concepts.GibbsSource.SourceForms
