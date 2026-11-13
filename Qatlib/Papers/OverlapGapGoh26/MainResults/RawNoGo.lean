/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.GroundPath
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.Consumer
import Qatlib.Papers.OverlapGapGoh26.OgpBridge.SmallSpin
import Qatlib.Papers.OverlapGapGoh26.OgpBridge.MaximizingSpin

/-!
# Probability bounds for the raw cube energy obstruction

The module combines a continuous raw spin path, norm control, energy stability, ground energy
stability, and endpoint decorrelation with a density overlap gap assumption.
`actual_raw_good_events_obstruct` rules out simultaneous success and these path conditions;
`actual_raw_cube_nogo_bound` turns the resulting event inclusion into an explicit Gaussian
probability bound. This is the conditional raw dynamics obstruction associated with
[GohMuller2026].

## Main statements

* `actual_raw_good_events_obstruct`: For positive `r`, `N ≥ 2`, and the stated margin and
  overlap thresholds, the density overlap gap condition, bounded endpoint norms, uniform energy
  and maximum deviations below `μ/8`, small endpoint overlap, and initial success within `μ/8`
  cannot all hold.
* `actual_raw_success_subset`: Under the stated degree, dimension, and threshold conditions,
  initial cube success within `μ/8` forces failure of the input overlap gap or norm region, an
  energy or ground deviation, or an endpoint overlap deviation.
* `actual_raw_cube_nogo_bound`: For odd `r`, `N ≥ 2`, a schedule in `[0,1]`, `μ > 0`, and `0 <
  ν₁ < ν₂ < 1`, the raw cube success probability at margin `μ/8` is bounded by the displayed sum
  of model overlap gap failure, exponential norm tails, energy and ground fluctuations, and
  endpoint overlap terms.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators RealInnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.NormRegion
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.GroundPath
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Density
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.SmallSpin

namespace Qatlib.Papers.OverlapGapGoh26.MainResults.RawNoGo

/-- Interpolating the two negated source tensors equals the negated source tensor extracted from
the combined input path. -/
theorem cost_path {r N : ℕ} (x y : Input r N) (τ : ℝ) :
    interpolate (-(sourceTensor (tensorCoords x).ofLp)) (-(sourceTensor (tensorCoords y).ofLp)) τ=
      -(sourceTensor (tensorCoords (inputPath x y τ)).ofLp) := by
  rw [Qatlib.Papers.OverlapGapGoh26.OgpBridge.MaximizingSpin.interpolate_neg,source_tensor_path]

/-- For `N > 0`, if the raw energy density is within `μ` below the cube maximum along the input
path, then the negated tensor energy of the spin path is at most its cube minimum plus `Nμ`. -/
theorem cost_near_of_gap {r N : ℕ} (hN : 0< N) (s : ℕ→ℝ) (T : ℕ) (x y : Input r N)
    (τ μ : ℝ) (hgap : maximum (inputPath x y τ)-energy s T (inputPath x y τ)≤μ) :
    tensorEnergy (interpolate (-(sourceTensor (tensorCoords x).ofLp)) (-(sourceTensor (tensorCoords y).ofLp)) τ)
      (spinPath s T x y τ).ofLp≤
      cubeOpt (interpolate (-(sourceTensor (tensorCoords x).ofLp)) (-(sourceTensor (tensorCoords y).ofLp)) τ)+(N:ℝ)*μ := by
  have hn : (0:ℝ)< N := by exact_mod_cast hN
  rw [cost_path,tensor_energy_neg]
  rw [maximum_formula] at hgap
  change -cubeOpt (-(sourceTensor (tensorCoords (inputPath x y τ)).ofLp))/(N:ℝ)-
    tensorEnergy (sourceTensor (tensorCoords (inputPath x y τ)).ofLp) (spinPath s T x y τ).ofLp/(N:ℝ)≤μ at hgap
  have h := (div_le_iff₀ hn).mp (show
      (-cubeOpt (-(sourceTensor (tensorCoords (inputPath x y τ)).ofLp))-
        tensorEnergy (sourceTensor (tensorCoords (inputPath x y τ)).ofLp) (spinPath s T x y τ).ofLp)/(N:ℝ)≤μ by
      simpa only [sub_div] using! hgap)
  linarith

/-- For `N ≥ 2` and `0 < ν₁ < ν₂ < 1`, the density ensemble overlap gap condition on the negated
source tensors forces the cube maximum density along the path to be at least `μ`. -/
theorem maximum_ge_ogp_margin {r N : ℕ} (hN : 2≤ N) (x y : Input r N)
    (μ ν₁ ν₂ : ℝ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1)
    (hogp : densityEnsembleOGP (-(sourceTensor (tensorCoords x).ofLp)) (-(sourceTensor (tensorCoords y).ofLp)) μ ν₁ ν₂)
    (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) : μ≤ maximum (inputPath x y τ) := by
  have h := density_ogp_ground_bound hN _ _ μ ν₁ ν₂ hlo hgap hhi hogp τ hτ
  rw [cost_path] at h
  rw [maximum_formula,neg_div]
  linarith

/-- For positive `r`, `N`, and `K`, if `normScale x ≤ 2K` and the raw energy density is at least
`μ/2`, then the endpoint spin norm is at least `μ√N / (4K(r+1))`. -/
theorem actual_spin_norm_lower {r N T : ℕ} (hr : 0< r) (hN : 0< N) (s : ℕ→ℝ)
    (x : Input r N) (K μ : ℝ) (hK : 0< K) (hx : normScale x≤2*K)
    (hE : μ/2≤ energy s T x) :
    (μ/(4*K*((r+1:ℕ):ℝ)))*Real.sqrt (N:ℝ)≤‖Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x‖ := by
  have hn : (0:ℝ)< N := by exact_mod_cast hN
  have hsq : 0< Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hs := source_energy_spin_difference hr hN (tensorCoords x)
    (rawSpin s T (tensorCoords x) (seedCoords x)) 0 (rawSpin_cube s T _ _) (fun _ => by norm_num) (2*K) hx
  have hzero : tensorEnergy (sourceTensor (tensorCoords x).ofLp) (0 : Fin N→ℝ)=0 :=
    tensorEnergy_zero _
  simp only [WithLp.ofLp_zero,hzero,zero_div,sub_zero] at hs
  change |energy s T x|≤(2*K*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ))*
    ‖Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x‖ at hs
  have hh := hE.trans ((le_abs_self _).trans hs)
  have hh' := (le_div_iff₀ hsq).mp (show μ/2≤
      (2*K*((r+1:ℕ):ℝ)*‖Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x‖)/Real.sqrt (N:ℝ) by
      convert! hh using 1; ring)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0<4*K*((r+1:ℕ):ℝ))).mpr
  nlinarith

/-- The normalized spin radius `μ / (4 * normBound r * (r+1))` used in the raw path obstruction. -/
def normRadius (r : ℕ) (μ : ℝ) : ℝ := μ/(4*normBound r*((r+1:ℕ):ℝ))

/-- The endpoint overlap tolerance `ν * (normRadius r μ)^2`. -/
def overlapTolerance (r : ℕ) (μ ν : ℝ) : ℝ := ν*(normRadius r μ)^2

/-- A positive energy margin `μ` gives a strictly positive `normRadius r μ`. -/
theorem normRadius_pos (r : ℕ) (μ : ℝ) (hμ : 0<μ) : 0< normRadius r μ := by
  unfold normRadius
  exact div_pos hμ (mul_pos (mul_pos (by norm_num) (normBound_pos r)) (by positivity))

/-- Positive energy and overlap margins give a strictly positive `overlapTolerance r μ ν`. -/
theorem overlapTolerance_pos (r : ℕ) (μ ν : ℝ) (hμ : 0<μ) (hν : 0<ν) : 0< overlapTolerance r μ ν :=
  mul_pos hν (sq_pos_of_pos (normRadius_pos r μ hμ))

/-- For positive `r`, `N ≥ 2`, and the stated margin and overlap thresholds, the density overlap
gap condition, bounded endpoint norms, uniform energy and maximum deviations below `μ/8`,
small endpoint overlap, and initial success within `μ/8` cannot all hold. -/
theorem actual_raw_good_events_obstruct {r N T : ℕ} (hr : 0< r) (hN : 2≤ N)
    (s : ℕ→ℝ) (x y : Input r N) (μ ν₁ ν₂ : ℝ) (hμ : 0<μ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1)
    (hogp : densityEnsembleOGP (-(sourceTensor (tensorCoords x).ofLp)) (-(sourceTensor (tensorCoords y).ofLp)) μ ν₁ ν₂)
    (hregion : (x,y)∈pairRegion r N)
    (henergy : ∀ τ∈Set.Icc (0:ℝ) 1,|energyPath s T x y τ-energy s T x|<μ/8)
    (hground : ∀ τ∈Set.Icc (0:ℝ) 1,|maximum (inputPath x y τ)-maximum x|<μ/8)
    (hend : |Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.overlap s T (x,y)|< overlapTolerance r μ ν₁)
    (hsuccess : maximum x-energy s T x≤μ/8) : False := by
  have hn : 0< N := by omega
  have hn' : (0:ℝ)< N := by exact_mod_cast hn
  have hzero : (0:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hone : (1:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb : 0< normRadius r μ*Real.sqrt (N:ℝ) :=
      mul_pos (normRadius_pos r μ hμ) (Real.sqrt_pos.mpr hn')
  have hnear (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) : maximum (inputPath x y τ)-energy s T (inputPath x y τ)≤μ/2 := by
    have he := (abs_lt.mp (henergy τ hτ)).1
    have hg := (abs_lt.mp (hground τ hτ)).2
    change -(μ/8)< energy s T (inputPath x y τ)-energy s T x at he
    linarith
  have hnorm (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
      normRadius r μ*Real.sqrt (N:ℝ)≤‖spinPath s T x y τ‖ := by
    have hmax := maximum_ge_ogp_margin hN x y μ ν₁ ν₂ hlo hgap hhi hogp τ hτ
    have he : μ/2≤ energy s T (inputPath x y τ) := by have hg := hnear τ hτ; linarith
    exact actual_spin_norm_lower hr hn s (inputPath x y τ) (normBound r) μ (normBound_pos r)
      (normScale_inputPath x y (normBound r) hregion.1 hregion.2 τ hτ) he
  have hnz (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) : spinPath s T x y τ≠0 :=
    norm_ne_zero_iff.mp (ne_of_gt (hb.trans_le (hnorm τ hτ)))
  have hu : normRadius r μ*Real.sqrt (N:ℝ)≤‖Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x‖ := by
    simpa [spinPath,inputPath,Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin] using!
        hnorm 0 hzero
  have hv : normRadius r μ*Real.sqrt (N:ℝ)≤‖Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T y‖ := by
    simpa [spinPath,inputPath,Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin] using!
        hnorm 1 hone
  have hinner : |inner ℝ (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x)
      (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T y)|≤ overlapTolerance r μ ν₁*(N:ℝ) := by
    change |inner ℝ (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x)
      (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T y)/(N:ℝ)|< overlapTolerance r μ ν₁ at hend
    rw [abs_div,abs_of_pos hn'] at hend
    exact (div_le_iff₀ hn').mp hend.le
  have hscale : overlapTolerance r μ ν₁*(N:ℝ)=ν₁*(normRadius r μ*Real.sqrt (N:ℝ))^2 := by
    unfold overlapTolerance
    rw [mul_pow,Real.sq_sqrt hn'.le]
    ring
  have hd := decorrelation_to_normalized
    (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T x)
    (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin s T y)
    (normRadius r μ*Real.sqrt (N:ℝ)) (overlapTolerance r μ ν₁) ν₁ hb hlo.le hu hv hinner hscale.le
  have hdec : normalizedOverlap (spinPath s T x y 0) (spinPath s T x y 1)≤ν₁ := by
    simpa [spinPath,inputPath,Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.spin] using! hd
  obtain ⟨τ,hτ,hmidlo,hmidhi⟩ := actual_overlap_gap_crossing (spinPath s T x y)
    (continuous_spinPath s T x y).continuousOn hnz ν₁ ν₂ hgap hhi hdec
  have hraw := (density_ogp_iff_total hn _ _ μ ν₁ ν₂).mp hogp
  have hnear' (σ : ℝ) (hσ : σ∈Set.Icc (0:ℝ) 1) :
      maximum (inputPath x y σ)-energy s T (inputPath x y σ)≤μ := by have hh := hnear σ hσ; linarith
  have hbad := hraw 0 hzero τ hτ (spinPath s T x y 0) (spinPath s T x y τ)
    (fun i => abs_le.mp (spinPath_cube s T x y 0 i)) (fun i => abs_le.mp (spinPath_cube s T x y τ i))
    (cost_near_of_gap hn s T x y 0 μ (hnear' 0 hzero)) (cost_near_of_gap hn s T x y τ μ (hnear' τ hτ))
  rcases hbad with hbad|hbad <;> linarith

/-- The event that a tensor pair satisfies the density ensemble overlap gap condition with the
given energy margin and overlap thresholds. -/
def modelOgp (r N : ℕ) (μ ν₁ ν₂ : ℝ) : Set (Tensor (r+1) N×Tensor (r+1) N) :=
  {p | densityEnsembleOGP p.1 p.2 μ ν₁ ν₂}

/-- The event that the negated source tensors extracted from an input pair satisfy the density
ensemble overlap gap condition. -/
def inputOgp (r N : ℕ) (μ ν₁ ν₂ : ℝ) : Set (Input r N×Input r N) :=
  {w | densityEnsembleOGP (-(sourceTensor (tensorCoords w.1).ofLp)) (-(sourceTensor (tensorCoords w.2).ofLp)) μ ν₁ ν₂}

/-- The event that the cube maximum density minus the raw energy density is at most `a`. -/
def nearCube {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (a : ℝ) : Set (Input r N) :=
  {x | maximum x-energy s T x≤ a}

/-- The event that the raw energy density differs from its initial value by at least `a`
somewhere along the input interpolation interval. -/
def energyDeviation {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (a : ℝ) : Set (Input r N×Input r N) :=
  {w | ∃ τ∈Set.Icc (0:ℝ) 1,a≤|energyPath s T w.1 w.2 τ-energy s T w.1|}

/-- The event that the cube maximum density differs from its initial value by at least `a`
somewhere along the input interpolation interval. -/
def groundDeviation (r N : ℕ) (a : ℝ) : Set (Input r N×Input r N) :=
  {w | ∃ τ∈Set.Icc (0:ℝ) 1,a≤|maximum (inputPath w.1 w.2 τ)-maximum w.1|}

/-- The event that the absolute endpoint overlap is at least `a`. -/
def endpointDeviation {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (a : ℝ) : Set (Input r N×Input r N) :=
  {w | a≤|Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.overlap s T w|}

/-- Under the stated degree, dimension, and threshold conditions, initial cube success within
`μ/8` forces failure of the input overlap gap or norm region, an energy or ground deviation,
or an endpoint overlap deviation. -/
theorem actual_raw_success_subset {r N T : ℕ} (hr : 0< r) (hN : 2≤ N) (s : ℕ→ℝ)
    (μ ν₁ ν₂ : ℝ) (hμ : 0<μ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1) :
    Prod.fst⁻¹' nearCube (r:=r) (N:=N) s T (μ/8)⊆
      ((((inputOgp r N μ ν₁ ν₂)ᶜ∪(pairRegion r N)ᶜ)∪energyDeviation s T (μ/8))∪
        groundDeviation r N (μ/8))∪endpointDeviation s T (overlapTolerance r μ ν₁) := by
  intro w hw
  by_contra hnot
  simp only [Set.mem_union,Set.mem_compl_iff,not_or,not_not] at hnot
  exact actual_raw_good_events_obstruct hr hN s w.1 w.2 μ ν₁ ν₂ hμ hlo hgap hhi
    hnot.1.1.1.1 hnot.1.1.1.2
    (fun τ hτ => lt_of_not_ge (fun h => hnot.1.1.2 ⟨τ,hτ,h⟩))
    (fun τ hτ => lt_of_not_ge (fun h => hnot.1.2 ⟨τ,hτ,h⟩))
    (lt_of_not_ge hnot.2) hw

/-- For `N > 0`, the raw cube success event `nearCube s T a` is measurable. -/
theorem nearCube_measurable {r N : ℕ} (hN : 0< N) (s : ℕ→ℝ) (T : ℕ) (a : ℝ) :
    MeasurableSet (nearCube (r:=r) (N:=N) s T a) := by
  have hm : Continuous (maximum (r:=r) (N:=N)) :=
      ((ground_lipschitz hN).continuous.comp continuous_neg).neg
  exact measurableSet_le (hm.sub (contDiff_energy s T).continuous).measurable measurable_const

/-- The probability of input overlap gap failure for independent standard Gaussian inputs is at
most the corresponding failure probability for independent Gaussian tensors. -/
theorem inputOgp_failure_le (r N : ℕ) (μ ν₁ ν₂ : ℝ) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real (inputOgp r N μ ν₁ ν₂)ᶜ≤
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real (modelOgp r N μ ν₁ ν₂)ᶜ := by
  have hm := ((gaussian_tensor_neg_preserving r N).comp (actual_tensor_preserving r N)).prod
    ((gaussian_tensor_neg_preserving r N).comp (actual_tensor_preserving r N))
  have h := Measure.le_map_apply (μ:=(stdGaussian (Input r N)).prod (stdGaussian (Input r N)))
    hm.measurable.aemeasurable (modelOgp r N μ ν₁ ν₂)ᶜ
  rw [hm.map_eq] at h
  exact ENNReal.toReal_mono (by finiteness) h

/-- For odd `r`, `N ≥ 2`, a schedule in `[0,1]`, `μ > 0`, and `0 < ν₁ < ν₂ < 1`, the raw cube
success probability at margin `μ/8` is bounded by the displayed sum of model overlap gap
failure, exponential norm tails, energy and ground fluctuations, and endpoint overlap terms.
See [GohMuller2026]. -/
theorem actual_raw_cube_nogo_bound {r N T : ℕ} (hr : Odd r) (hN : 2≤ N) (s : ℕ→ℝ)
    (hs : ∀ j≤ T,s j∈Set.Icc (0:ℝ) 1) (μ ν₁ ν₂ : ℝ)
    (hμ : 0<μ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1) :
    (stdGaussian (Input r N)).real (nearCube s T (μ/8))≤
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real (modelOgp r N μ ν₁ ν₂)ᶜ+
        8*Real.exp (-(N:ℝ))+(2*rawVarianceConstant r T+Real.pi^2)/((N:ℝ)*(μ/8)^2)+
        Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.endpointConstant r T/
          ((N:ℝ)*(overlapTolerance r μ ν₁)^2) := by
  have hn : 0< N := by omega
  let P := (stdGaussian (Input r N)).prod (stdGaussian (Input r N))
  have hfirst := congrArg ENNReal.toReal ((measurePreserving_fst (μ:=stdGaussian (Input r N))
    (ν:=stdGaussian (Input r N))).measure_preimage (nearCube_measurable hn s T (μ/8)).nullMeasurableSet)
  have hsub :=
      measureReal_mono (μ:=P)
      (actual_raw_success_subset (r:=r) (N:=N) (T:=T) hr.pos hN s μ ν₁ ν₂ hμ hlo hgap hhi)
  have hu1 := measureReal_union_le (μ:=P) (inputOgp r N μ ν₁ ν₂)ᶜ (pairRegion r N)ᶜ
  have hu2 := (measureReal_union_le (μ:=P) ((inputOgp r N μ ν₁ ν₂)ᶜ∪(pairRegion r N)ᶜ) (energyDeviation s T (μ/8))).trans
    (add_le_add hu1 le_rfl)
  have hu3 := (measureReal_union_le (μ:=P) (((inputOgp r N μ ν₁ ν₂)ᶜ∪(pairRegion r N)ᶜ)∪energyDeviation s T (μ/8))
    (groundDeviation r N (μ/8))).trans (add_le_add hu2 le_rfl)
  have hu4 := (measureReal_union_le (μ:=P) ((((inputOgp r N μ ν₁ ν₂)ᶜ∪(pairRegion r N)ᶜ)∪energyDeviation s T (μ/8))∪
    groundDeviation r N (μ/8)) (endpointDeviation s T (overlapTolerance r μ ν₁))).trans (add_le_add hu3 le_rfl)
  have hsum := (hsub.trans hu4).trans (add_le_add
    (add_le_add (add_le_add (add_le_add (inputOgp_failure_le r N μ ν₁ ν₂) (pairRegion_failure hr.pos hn))
      (actual_raw_continuum_tail hr.pos hn s hs (μ/8) (by positivity)))
      (actual_maximum_continuum_tail hr.pos hn (μ/8) (by positivity)))
    (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.independent_endpoint_tail
      hr hn s hs (overlapTolerance r μ ν₁) (overlapTolerance_pos r μ ν₁ hμ hlo)))
  change P.real (Prod.fst⁻¹' nearCube s T (μ/8))=(stdGaussian (Input r N)).real
      (nearCube s T (μ/8)) at hfirst
  rw [hfirst] at hsum
  exact hsum.trans_eq (by ring)

end Qatlib.Papers.OverlapGapGoh26.MainResults.RawNoGo
