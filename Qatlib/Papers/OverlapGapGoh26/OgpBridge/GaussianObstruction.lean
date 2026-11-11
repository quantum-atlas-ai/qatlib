/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.OgpBridge.ContinuousPath

/-!
# Gaussian event bounds for the AMP path obstruction

`sourceIndependentDecorrelation` expresses an inner product bound for sufficiently low energy
cube vectors at two endpoint tensors. Combined with a path norm lower bound and the ensemble
overlap gap condition, it yields `source_gaussian_path_obstruction`; event inclusions then bound
uniform AMP success by the probabilities of failed hypotheses. The Gaussian ground mean supplies
the endpoint energy threshold used in the obstruction associated with [GohMuller2026].

## Main statements

* `source_gaussian_path_obstruction`: Under the ensemble overlap gap, endpoint energy and
  decorrelation conditions, a uniform path norm lower bound `b > 0`, and `δN ≤ ν₁b²`, some AMP
  path energy exceeds the interpolated cube minimum plus `μ`.
* `uniformNear_subset_failures`: Under the overlap threshold and norm scaling assumptions,
  uniform AMP energy proximity forces failure of the ensemble overlap gap, path norm, endpoint
  decorrelation, or endpoint energy condition.
* `gaussian_uniform_success_le_failures`: Under the overlap threshold and norm scaling
  assumptions, the `jointLaw` probability of uniform AMP success is at most the sum of the four
  hypothesis failure probabilities. See [GohMuller2026].

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian

/-- The minimum tensor energy over all real spin configurations obtained from Boolean vectors. -/
def binaryGround {q N : ℕ} (J : Tensor q N) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun z : Fin N → Bool => tensorEnergy J (fun i => if z i then 1 else -1))

/-- The Gaussian expectation of the binary ground energy divided by `N`. -/
def gaussianGroundMean (r N : ℕ) : ℝ :=
  ∫ J : Tensor (r+1) N, binaryGround J/(N:ℝ) ∂gaussianTensorLaw r N

/-- The condition that every pair of cube vectors with endpoint energies at most `N(1-δ) *
gaussianGroundMean r N` has absolute inner product at most `δN`. -/
def sourceIndependentDecorrelation {r N : ℕ} (A B : Tensor (r+1) N) (δ : ℝ) : Prop :=
  ∀ (u v : EuclideanSpace ℝ (Fin N)), u.ofLp ∈ hilbertCube N → v.ofLp ∈ hilbertCube N →
    tensorEnergy A u.ofLp ≤ (N:ℝ)*(1-δ)*gaussianGroundMean r N →
    tensorEnergy B v.ofLp ≤ (N:ℝ)*(1-δ)*gaussianGroundMean r N →
    |inner (𝕜:=ℝ) u v|≤δ*(N:ℝ)

/-- Under the ensemble overlap gap, endpoint energy and decorrelation conditions, a uniform path
norm lower bound `b > 0`, and `δN ≤ ν₁b²`, some AMP path energy exceeds the interpolated
cube minimum plus `μ`. See [GohMuller2026]. -/
theorem source_gaussian_path_obstruction {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (μ ν₁ ν₂ δ b : ℝ)
    (hogp : ensembleOGP A B μ ν₁ ν₂) (hgap : ν₁<ν₂) (hhigh : ν₂<1) (hν : 0≤ν₁)
    (hdec : sourceIndependentDecorrelation A B δ) (hb : 0<b)
    (hnorm : ∀ τ ∈ Set.Icc (0:ℝ) 1, b≤‖outputPath M s T A B seed τ‖)
    (hscale : δ*(N:ℝ)≤ν₁*b^2)
    (hEA : tensorEnergy A (outputPath M s T A B seed 0).ofLp≤(N:ℝ)*(1-δ)*gaussianGroundMean r N)
    (hEB : tensorEnergy B (outputPath M s T A B seed 1).ofLp≤(N:ℝ)*(1-δ)*gaussianGroundMean r N) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1, cubeOpt (interpolate A B τ)+μ <
      tensorEnergy (interpolate A B τ) (outputPath M s T A B seed τ).ofLp := by
  have hz : (0:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ho : (1:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hraw := hdec (outputPath M s T A B seed 0) (outputPath M s T A B seed 1)
    (fun i => outputPath_cube M s T A B seed 0 i)
    (fun i => outputPath_cube M s T A B seed 1 i) hEA hEB
  apply actual_amp_ogp_obstruction M s T A B seed μ ν₁ ν₂ hogp hgap hhigh
  · intro τ hτ
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hb (hnorm τ hτ)))
  · exact decorrelation_to_normalized _ _ b δ ν₁ hb hν (hnorm 0 hz) (hnorm 1 ho) hraw hscale

/-- The sample space of a tensor pair together with a seed vector. -/
abbrev Sample (r N : ℕ) := (Tensor (r+1) N × Tensor (r+1) N) × (Fin N → ℝ)

/-- The event that the AMP output energy stays at most `μ` above the interpolated cube minimum
at every parameter in `[0,1]`. -/
def uniformNearEvent {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (μ : ℝ) : Set (Sample r N) :=
  {w | ∀ τ ∈ Set.Icc (0:ℝ) 1, tensorEnergy (interpolate w.1.1 w.1.2 τ)
    (outputPath M s T w.1.1 w.1.2 w.2 τ).ofLp≤cubeOpt (interpolate w.1.1 w.1.2 τ)+μ}

/-- The sample event that the tensor pair satisfies the ensemble overlap gap condition. -/
def ogpEvent {r N : ℕ} (μ ν₁ ν₂ : ℝ) : Set (Sample r N) :=
  {w | ensembleOGP w.1.1 w.1.2 μ ν₁ ν₂}

/-- The event that the AMP output norm is at least `b` at every interpolation parameter in
`[0,1]`. -/
def normEvent {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (b : ℝ) : Set (Sample r N) :=
  {w | ∀ τ ∈ Set.Icc (0:ℝ) 1, b≤‖outputPath M s T w.1.1 w.1.2 w.2 τ‖}

/-- The sample event that the tensor pair satisfies `sourceIndependentDecorrelation` with
parameter `δ`. -/
def decorrelationEvent {r N : ℕ} (δ : ℝ) : Set (Sample r N) :=
  {w | sourceIndependentDecorrelation w.1.1 w.1.2 δ}

/-- The event that both AMP endpoint energies are at most `N(1-δ) * gaussianGroundMean r N` for
their respective tensors. -/
def endpointNearEvent {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (δ : ℝ) : Set (Sample r N) :=
  {w | tensorEnergy w.1.1 (outputPath M s T w.1.1 w.1.2 w.2 0).ofLp≤(N:ℝ)*(1-δ)*gaussianGroundMean r N ∧
    tensorEnergy w.1.2 (outputPath M s T w.1.1 w.1.2 w.2 1).ofLp≤(N:ℝ)*(1-δ)*gaussianGroundMean r N}

/-- Under the overlap threshold and norm scaling assumptions, uniform AMP energy proximity
forces failure of the ensemble overlap gap, path norm, endpoint decorrelation, or endpoint
energy condition. -/
theorem uniformNear_subset_failures {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (μ ν₁ ν₂ δ b : ℝ) (hgap : ν₁<ν₂) (hhigh : ν₂<1) (hν : 0≤ν₁) (hb : 0<b)
    (hscale : δ*(N:ℝ)≤ν₁*b^2) :
    uniformNearEvent (r:=r) (N:=N) M s T μ ⊆
      ((ogpEvent μ ν₁ ν₂)ᶜ ∪ (normEvent M s T b)ᶜ) ∪
        ((decorrelationEvent δ)ᶜ ∪ (endpointNearEvent M s T δ)ᶜ) := by
  intro w hw
  by_contra hn
  have ho : w∈ogpEvent μ ν₁ ν₂ := by simpa using (not_or.mp (not_or.mp hn).1).1
  have hno : w∈normEvent M s T b := by simpa using (not_or.mp (not_or.mp hn).1).2
  have hd : w∈decorrelationEvent δ := by simpa using (not_or.mp (not_or.mp hn).2).1
  have he : w∈endpointNearEvent M s T δ := by simpa using (not_or.mp (not_or.mp hn).2).2
  obtain ⟨τ,hτ,hbad⟩ := source_gaussian_path_obstruction M s T w.1.1 w.1.2 w.2 μ ν₁ ν₂ δ b
    ho hgap hhigh hν hd hb hno hscale he.1 he.2
  exact not_lt_of_ge (hw τ hτ) hbad

/-- Under the overlap threshold and norm scaling assumptions, the `jointLaw` probability of
uniform AMP success is at most the sum of the four hypothesis failure probabilities. See
[GohMuller2026]. -/
theorem gaussian_uniform_success_le_failures {r N : ℕ} (M : ℝ) (v : NNReal)
    (s : ℕ → ℝ) (T : ℕ) (μ ν₁ ν₂ δ b : ℝ)
    (hgap : ν₁<ν₂) (hhigh : ν₂<1) (hν : 0≤ν₁) (hb : 0<b) (hscale : δ*(N:ℝ)≤ν₁*b^2) :
    jointLaw M v r N (uniformNearEvent M s T μ)≤
      (jointLaw M v r N (ogpEvent μ ν₁ ν₂)ᶜ+jointLaw M v r N (normEvent M s T b)ᶜ)+
      (jointLaw M v r N (decorrelationEvent δ)ᶜ+jointLaw M v r N (endpointNearEvent M s T δ)ᶜ) := by
  apply (measure_mono (uniformNear_subset_failures M s T μ ν₁ ν₂ δ b hgap hhigh hν hb hscale)).trans
  exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
