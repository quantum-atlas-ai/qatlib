/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinEnergy
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Probability reduction for spin energy paths

A spin-energy continuum exceedance is covered by the data-box complement and finitely many grid
exceedances. The Gaussian localization estimate and interpolation marginal law yield an explicit
fixed-instance probability bound for the spin dynamics of [GohMuller2026]; continuity also
establishes measurability of the continuum event.

## Main statements

* `actual_spin_fixed_instance_reduction`: a continuum event is bounded by a Gaussian tail and a
  grid factor times one fixed-instance probability.
* `measurableSet_spin_continuum_energy`: spin-energy continuum threshold events are measurable.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Localization
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Modulus
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Grid
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinEnergy

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinProbability

/-- For positive `N` and `ε` and schedules in `[0, 1]`, a spin-energy exceedance at `c + ε` lies
outside the unit data box or produces a grid exceedance at `c`. -/
theorem actual_spin_grid_inclusion {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) (c : ℝ) :
    {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c+ε≤ spinEnergyPath M s T w τ} ⊆
      (dataBox r N 1 M)ᶜ ∪ ⋃ σ∈spinActualGrid r T N ε,{w | c≤ spinEnergyPath M s T w σ} := by
  intro w hw
  by_cases hb : w∈dataBox r N 1 M
  · obtain ⟨τ,hτ,hbig⟩ := hw
    obtain ⟨σ,hσ,hd⟩ := actual_spin_grid_approximation hN M s hs ε hε w hb τ hτ
    right
    apply Set.mem_iUnion.mpr ⟨σ,?_⟩
    apply Set.mem_iUnion.mpr ⟨hσ,?_⟩
    have hdist := abs_lt.mp hd
    change c≤ spinEnergyPath M s T w σ
    linarith [hdist.2]
  · exact Or.inl hb

/-- For positive `N` and `ε`, nonnegative `M`, and schedules in `[0, 1]`, the spin-energy
continuum exceedance probability is bounded by the explicit Gaussian localization tail plus
the spin-grid cardinality bound times the single-instance spin-energy exceedance
probability. See [GohMuller2026]. -/
theorem actual_spin_fixed_instance_reduction {r N T : ℕ} (hN : 0<N)
    (M : ℝ) (hM : 0≤M) (v : NNReal) (s : ℕ → ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) (c : ℝ) :
    jointLaw M v r N {w | ∃ τ∈Set.Icc (0:ℝ) 1,c+ε≤ spinEnergyPath M s T w τ}≤
      ENNReal.ofReal (4*(N:ℝ)^(r+1)*Real.exp (-(N:ℝ)^r/2))+
        ((Nat.ceil ((2*(1+2*(T:ℝ))*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1))))+2:ℕ):ENNReal)*
          ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
            {p | c≤ tensorEnergy p.1 (spinOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)} := by
  let P := jointLaw M v r N
  let Q := ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
    {p | c≤ tensorEnergy p.1 (spinOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)}
  have hinc := actual_spin_grid_inclusion (r:=r) hN M s hs ε hε c
  have hP := (measure_mono (μ:=P) hinc).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le (spinActualGrid r T N ε) _)))
  have hloc : P (dataBox r N 1 M)ᶜ≤
      ENNReal.ofReal (4*(N:ℝ)^(r+1)*Real.exp (-(N:ℝ)^r/2)) := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    have hv : -1/(2*(((N:NNReal)^r)⁻¹:ℝ))=-(N:ℝ)^r/2 := by
      simp only [NNReal.coe_natCast]
      have hn : (N:ℝ)≠0 := by positivity
      field_simp
    simpa only [one_pow,hv] using! actual_dataBox_tail (r:=r) (N:=N) M hM v 1 (by norm_num)
  have hsum : (∑ σ∈spinActualGrid r T N ε,P {w | c≤ spinEnergyPath M s T w σ})=
      (spinActualGrid r T N ε).card * Q := by
    calc
      _ = ∑ _σ∈spinActualGrid r T N ε,Q := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact actual_spin_energy_stationary M v s T σ
            (uniformGrid_mem (gridResolution_pos _ _) σ hσ) c
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  change P {w | ∃ τ∈Set.Icc (0:ℝ) 1,c+ε≤ spinEnergyPath M s T w τ}≤_
  refine hP.trans ?_
  change P (dataBox r N 1 M)ᶜ+(∑ σ∈spinActualGrid r T N ε,P {w | c≤ spinEnergyPath M s T w σ})≤_
  rw [hsum]
  exact add_le_add hloc
      (mul_le_mul_of_nonneg_right (by exact_mod_cast spinActualGrid_card r T N ε) (zero_le : 0≤Q))

/-- The spin energy path is jointly continuous in the sampled tensors, seed, and interpolation
parameter. -/
theorem continuous_spinEnergyPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    Continuous (fun p : Sample r N × ℝ => spinEnergyPath M s T p.1 p.2) := by
  have hJ : Continuous (fun p : Sample r N × ℝ => interpolate p.1.1.1 p.1.1.2 p.2) := by
    apply continuous_pi
    intro k
    unfold interpolate
    fun_prop
  exact (continuous_spinEnergy r N M s T).comp (hJ.prodMk (continuous_snd.comp continuous_fst))

/-- The set of samples whose spin energy reaches or exceeds `c` somewhere on `[0, 1]` is closed. -/
theorem isClosed_spin_continuum_energy {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (c : ℝ) :
    IsClosed {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c≤ spinEnergyPath M s T w τ} := by
  let I := Set.Icc (0:ℝ) 1
  letI : CompactSpace I := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  have hc : Continuous (fun p : Sample r N × I => spinEnergyPath M s T p.1 p.2) :=
    (continuous_spinEnergyPath M s T).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed {p : Sample r N × I | c≤ spinEnergyPath M s T p.1 p.2} :=
    isClosed_le continuous_const hc
  have hp := isClosedMap_fst_of_compactSpace _ hclosed
  have he : Prod.fst '' {p : Sample r N × I | c≤ spinEnergyPath M s T p.1 p.2}=
      {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c≤ spinEnergyPath M s T w τ} := by
    ext w
    constructor
    · rintro ⟨⟨w,τ⟩,hc,rfl⟩
      exact ⟨τ,τ.property,hc⟩
    · rintro ⟨τ,hτ,hc⟩
      exact ⟨(w,⟨τ,hτ⟩),hc,rfl⟩
  rw [he] at hp
  exact hp

/-- The set of samples whose spin energy reaches or exceeds `c` somewhere on `[0, 1]` is
measurable. -/
theorem measurableSet_spin_continuum_energy {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (c : ℝ) :
    MeasurableSet {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c≤ spinEnergyPath M s T w τ} :=
  (isClosed_spin_continuum_energy M s T c).measurableSet

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinProbability
