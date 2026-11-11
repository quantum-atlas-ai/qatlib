/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.GridReduction
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.EntropyLimit
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.Comparison

/-!
# Subextensive repeated index energies

`remainderProbability` measures whether the repeated index energy reaches an extensive threshold
anywhere on the Hilbert cube. A polynomial grid and Gaussian tail estimates show that this
probability tends to zero, and the same conclusion follows for the difference between binary and
cube minimum energies. These limits supply the remainder control used in the analysis associated
with [GohMuller2026].

## Main statements

* `actual_remainder_subextensive`: For fixed `r` and `η > 0`, the probability that the repeated
  index energy reaches `ηN` in absolute value somewhere on the cube tends to zero.
* `actual_optimum_gap_subextensive`: For fixed `r` and `η > 0`, the probability that the binary
  ground energy exceeds the cube minimum by more than `ηN` tends to zero.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

/-- The Gaussian probability that some Hilbert cube vector has repeated index energy of absolute
value at least `ηN`. -/
def remainderProbability (r:ℕ) (η:ℝ) (N:ℕ) : ℝ :=
  (gaussianTensorLaw r N).real {A|∃u∈hilbertCube N,η*(N:ℝ)≤|tensorEnergy (repeated A) u|}

/-- For `N > 0`, the error expression for the mesh `N^(r+4)` simplifies to `2(r+1)/N²`. -/
theorem polynomial_mesh_error {r N:ℕ} (hN:0<N) :
    (N:ℝ)^(r+1)*(N:ℝ)*(r+1)*(2/((N:ℝ)^(r+4)))=2*(r+1)/(N:ℝ)^2 := by
  have hn:(N:ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [show r+4=(r+1)+3 by omega,pow_add]
  field_simp
  ring

/-- For fixed `r`, the polynomial mesh error `2(r+1)/N²` tends to zero as `N` tends to infinity. -/
theorem polynomial_mesh_zero (r:ℕ) :
    Tendsto (fun N:ℕ=>2*(r+1:ℝ)/(N:ℝ)^2) atTop (𝓝 0) := by
  have h:=(tendsto_const_div_atTop_nhds_zero_nat (2*(r+1:ℝ))).mul
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))
  convert! h using 1
  · funext N
    simp only [div_eq_mul_inv]
    ring
  · simp

/-- For fixed `r` and `η > 0`, the probability that the repeated index energy reaches `ηN` in
absolute value somewhere on the cube tends to zero. -/
theorem actual_remainder_subextensive (r:ℕ) (η:ℝ) (hη:0<η) :
    Tendsto (remainderProbability r η) atTop (𝓝 0) := by
  let c:ℝ:=η^2/(8*(r+1:ℝ)^2)
  have hc:0<c := by dsimp [c];positivity
  have hmeshsmall:∀ᶠ N:ℕ in atTop,2*(r+1:ℝ)/(N:ℝ)^2<η/2 :=
    (polynomial_mesh_zero r).eventually (eventually_lt_nhds (show (0:ℝ)<η/2 by linarith))
  have hb:∀ᶠ N:ℕ in atTop,remainderProbability r η N≤
      2*((N:ℝ)^(r+1)*Real.exp (-(1/2:ℝ)*(N:ℝ)^2))+
      2*((((N:ℝ)^(r+4)+1)^N)*Real.exp (-c*(N:ℝ)^2)) := by
    filter_upwards [hmeshsmall,eventually_ge_atTop 1] with N hsmall hN
    have hNpos:0<N := by omega
    have hn:(1:ℝ)≤N := by exact_mod_cast hN
    have hm:0<N^(r+4) := pow_pos hNpos _
    have hmesh:(N:ℝ)^(r+1)*(N:ℝ)*(r+1)*(2/((N^(r+4):ℕ):ℝ))≤η*(N:ℝ)/2 := by
      rw [Nat.cast_pow,polynomial_mesh_error hNpos]
      have hpos:η/2≤η*(N:ℝ)/2 := by nlinarith
      exact hsmall.le.trans hpos
    have h:=remainder_grid_tail hNpos hm η hη hmesh
    have he:-(η*(N:ℝ)/2)^2/(2*(r+1:ℝ)^2)= -c*(N:ℝ)^2 := by dsimp [c];field_simp;ring
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,he] at h
    exact h.trans_eq (by ring_nf)
  have hlim := ((polynomial_gaussian_tail_zero (r+1) (1/2) (by norm_num)).const_mul 2).add
    ((grid_entropy_tail_zero (r+4) c hc).const_mul 2)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N=>measureReal_nonneg)) hb
  simpa only [mul_zero,add_zero] using! hlim

/-- For fixed `r` and `η > 0`, the probability that the binary ground energy exceeds the cube
minimum by more than `ηN` tends to zero. -/
theorem actual_optimum_gap_subextensive (r:ℕ) (η:ℝ) (hη:0<η) :
    Tendsto (fun N:ℕ=>(gaussianTensorLaw r N).real
      {A|η*(N:ℝ)<binaryGround A-cubeOpt A}) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N=>measureReal_nonneg)) _
    (actual_remainder_subextensive r (η/2) (by linarith))
  apply Filter.Eventually.of_forall
  intro N
  have hs:{A:Tensor (r+1) N|η*(N:ℝ)<binaryGround A-cubeOpt A}⊆
      {A|∃u∈hilbertCube N,(η/2)*(N:ℝ)≤|tensorEnergy (repeated A) u|} := by
    have h:=optimum_gap_inclusion (q:=r+1) (N:=N) ((η/2)*(N:ℝ))
    have he:2*((η/2)*(N:ℝ))=η*(N:ℝ) := by ring
    rw [he] at h
    exact h
  exact measureReal_mono hs
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
