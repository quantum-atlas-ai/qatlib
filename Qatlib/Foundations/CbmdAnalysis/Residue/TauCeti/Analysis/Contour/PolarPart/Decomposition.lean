/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.HomologyCauchy
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.MeromorphicLaurent
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Polar-part decompositions over finite sets

This module packages finite polar sums and a holomorphic remainder in `PolarPartDecomposition`.
The construction `PolarPartDecomposition.ofMeromorphic` removes the chosen polar parts from a
function holomorphic off finitely many meromorphic points and fills in the removable remainder,
supplying decomposition data for the contour calculus supporting [WangEtAl2026].

## Main statements

* `PolarPartDecomposition.ofMeromorphic`: construction from local meromorphic data.
* `PolarPartDecomposition.intervalIntegral_deriv_smul_analyticRemainder_eq_zero`: vanishing of
  the analytic remainder integral.
* `PolarPartDecomposition.intervalIntegrable_polarPart_mul_deriv_truncated`: integrability of
  truncated polar contributions.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

open scoped Interval

/-- A decomposition of `f` off a finite set `S` into finite polar parts centered at its points
and a holomorphic remainder on `U`, with simple inverse-power coefficients equal to
residues. -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where

  order : S → ℕ

  coeff : (s : S) → Fin (order s) → ℂ

  polarPart : S → ℂ → ℂ

  polarPart_eq : ∀ (s : S) (z : ℂ),
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - (s : ℂ)) ^ (k.val + 1)

  residue_eq : ∀ s : S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0

  analyticRemainder : ℂ → ℂ

  analyticRemainder_differentiableOn : DifferentiableOn ℂ analyticRemainder U

  f_eq : ∀ z ∈ U \ (↑S : Set ℂ),
    f z = analyticRemainder z + ∑ s ∈ S.attach, polarPart s z

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- Selecting the zero-index polar coefficient in a finite sum gives the residue multiplied by
`c`. -/
theorem sum_ite_coeff_eq_residue_mul (decomp : PolarPartDecomposition f S U) (s : S) (c : ℂ) :
    (∑ k : Fin (decomp.order s), if k.val = 0 then decomp.coeff s k * c else 0)
      = residue f s * c := by
  classical
  rcases Nat.eq_zero_or_pos (decomp.order s) with h0 | h_pos
  · rw [Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega), decomp.residue_eq s,
      dif_neg (by omega), zero_mul]
  · have h_pick : ∀ k : Fin (decomp.order s),
        (if k.val = 0 then decomp.coeff s k * c else 0)
        = if k = ⟨0, h_pos⟩ then decomp.coeff s ⟨0, h_pos⟩ * c else 0 := fun k => by
      rcases eq_or_ne k ⟨0, h_pos⟩ with rfl | hk
      · simp
      · rw [if_neg fun h => hk (Fin.ext h), if_neg hk]
    rw [Finset.sum_congr rfl fun k _ => h_pick k, Finset.sum_ite_eq' Finset.univ,
      if_pos (Finset.mem_univ _), decomp.residue_eq s, dif_pos h_pos]

/-- The analytic remainder integrates to zero along a closed piecewise C¹ curve null-homologous
in the open set `U`. -/
theorem intervalIntegral_deriv_smul_analyticRemainder_eq_zero
    (decomp : PolarPartDecomposition f S U)
    (hU : IsOpen U) {γ : ℝ → ℂ} {a b : ℝ} (hγ_pc1 : IsPiecewiseC1On γ a b)
    (hγ : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t) = 0 :=
  homologyCauchyTheorem hU γ a b hγ_pc1 hγ hclosed decomp.analyticRemainder_differentiableOn hnull

end PolarPartDecomposition

/-- The sum of the chosen meromorphic polar parts over the finite set of centers. -/
def meromorphicPolarPartTotal {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, meromorphicPolarPartAt (hMero s.1 s.2) z

/-- Expands the total polar part as the sum over the attached finite set of centers. -/
theorem meromorphicPolarPartTotal_eq_sum {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) (z : ℂ) :
    meromorphicPolarPartTotal hMero z =
      ∑ s ∈ S.attach, meromorphicPolarPartAt (hMero s.1 s.2) z := by
  unfold meromorphicPolarPartTotal
  rfl

/-- The sum of polar parts centered at points other than `s` is analytic at `s`. -/
private theorem otherPolar_analyticAt {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) (s : ℂ) :
    AnalyticAt ℂ (fun z => ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
      meromorphicPolarPartAt (hMero s'.1 s'.2) z) s := by
  refine Finset.analyticAt_fun_sum _ fun s' hs' => ?_
  exact meromorphicPolarPartAt_analyticAt_of_ne (hMero s'.1 s'.2)
    ((Finset.mem_filter.mp hs').2).symm

/-- Near any selected center, subtracting the total polar part agrees on a punctured
neighborhood with a function analytic at that center. -/
private theorem exists_analyticAt_sub_polarPartTotal {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPolarPartTotal hMero z = g z := by
  refine ⟨fun z => meromorphicAnalyticPartAt (hMero s hs) z -
      ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
        meromorphicPolarPartAt (hMero s'.1 s'.2) z,
    (meromorphicAnalyticPartAt_analyticAt (hMero s hs)).sub
      (otherPolar_analyticAt hMero s), ?_⟩
  filter_upwards [eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt
    (hMero s hs)] with z hz
  rw [hz]
  suffices h_total : meromorphicPolarPartTotal hMero z =
      meromorphicPolarPartAt (hMero s hs) z +
        ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
          meromorphicPolarPartAt (hMero s'.1 s'.2) z by
    rw [h_total]
    ring
  unfold meromorphicPolarPartTotal
  rw [← Finset.sum_filter_add_sum_filter_not S.attach (fun s' => s'.1 = s)]
  congr 1
  rw [show S.attach.filter (fun s' => s'.1 = s) = {⟨s, hs⟩} from by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩]
  rw [Finset.sum_singleton]

/-- Away from the finite center set, filling the remainder at those centers by punctured limits
leaves it locally unchanged. -/
private theorem remainder_eventuallyEq_off {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {z : ℂ} (hz : z ∉ (↑S : Set ℂ)) :
    (fun w => if w ∈ (↑S : Set ℂ) then
        limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
      else f w - meromorphicPolarPartTotal hMero w) =ᶠ[𝓝 z]
      fun w => f w - meromorphicPolarPartTotal hMero w := by
  filter_upwards [(S.finite_toSet.isClosed.isOpen_compl).mem_nhds hz] with w hw
  rw [if_neg hw]

/-- A punctured neighborhood of any complex point eventually avoids every point of a fixed
finite set. -/
private theorem eventually_notMem_nhdsNE (S : Finset ℂ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ (↑S : Set ℂ) := by
  have hcl : IsClosed ((↑S \ {z} : Set ℂ)) := (S.finite_toSet.subset diff_subset).isClosed
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (hcl.isOpen_compl.mem_nhds (by simp)), self_mem_nhdsWithin] with w hwc hwne hwS
  exact hwc ⟨hwS, hwne⟩

/-- The remainder filled at the selected centers by punctured limits is complex differentiable
at each center. -/
private theorem remainder_differentiableAt_mem {f : ℂ → ℂ} {S : Finset ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {z : ℂ} (hzS : z ∈ (↑S : Set ℂ)) :
    DifferentiableAt ℂ (fun w => if w ∈ (↑S : Set ℂ) then
        limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
      else f w - meromorphicPolarPartTotal hMero w) z := by
  obtain ⟨g, hg_an, hg_eq⟩ := exists_analyticAt_sub_polarPartTotal hMero hzS
  have h1 : ∀ᶠ w in 𝓝[≠] z, (if w ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f w - meromorphicPolarPartTotal hMero w) = g w := by
    filter_upwards [eventually_notMem_nhdsNE S z, hg_eq] with w hwS hwg
    rw [if_neg hwS]
    exact hwg
  have h2 : (if z ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] z) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f z - meromorphicPolarPartTotal hMero z) = g z := by
    rw [if_pos hzS]
    refine Filter.Tendsto.limUnder_eq ?_
    refine Filter.Tendsto.congr' ?_
      (hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [hg_eq] with u hu using hu.symm
  have h_full : (fun w => if w ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] w) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f w - meromorphicPolarPartTotal hMero w) =ᶠ[𝓝 z] g := by
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure z, Filter.eventually_sup]
    exact ⟨h1, Filter.eventually_pure.mpr h2⟩
  exact h_full.differentiableAt_iff.mpr hg_an.differentiableAt

namespace PolarPartDecomposition

/-- Constructs a polar-part decomposition on an open set from holomorphicity off a finite set
and meromorphicity at its points. -/
noncomputable def ofMeromorphic {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ))) (hMero : ∀ s ∈ S, MeromorphicAt f s) :
    PolarPartDecomposition f S U where
  order s := meromorphicPolarOrderAt f s
  coeff s k := meromorphicPolarCoeffAt (hMero s s.2) k
  polarPart s z := meromorphicPolarPartAt (hMero s s.2) z
  polarPart_eq s z := meromorphicPolarPartAt_eq_sum (hMero s s.2) z
  residue_eq s := by
    rcases Nat.eq_zero_or_pos (meromorphicPolarOrderAt f s) with h0 | hpos
    · rw [dif_neg (by omega)]
      refine residue_eq_zero_of_meromorphicOrderAt_nonneg ?_
      have hle := neg_meromorphicPolarOrderAt_le f (s : ℂ)
      rw [h0] at hle
      simpa using hle
    · rw [dif_pos hpos]
      exact (meromorphicPolarCoeffAt_zero_eq_residue (hMero s s.2) hpos).symm
  analyticRemainder := fun z => if z ∈ (↑S : Set ℂ) then
      limUnder (𝓝[≠] z) (fun u => f u - meromorphicPolarPartTotal hMero u)
    else f z - meromorphicPolarPartTotal hMero z
  analyticRemainder_differentiableOn := by
    intro z hzU
    by_cases hzS : z ∈ (↑S : Set ℂ)
    · exact (remainder_differentiableAt_mem hMero hzS).differentiableWithinAt
    · have h_diff : DifferentiableAt ℂ
          (fun w => f w - meromorphicPolarPartTotal hMero w) z := by
        refine ((hf z ⟨hzU, hzS⟩).differentiableAt ?_).sub ?_
        · exact (hU.sdiff S.finite_toSet.isClosed).mem_nhds ⟨hzU, hzS⟩
        · refine DifferentiableAt.fun_sum fun s' _ => ?_
          exact (meromorphicPolarPartAt_analyticAt_of_ne (hMero s'.1 s'.2)
            (fun h => hzS (by rw [h]; exact Finset.mem_coe.mpr s'.2))).differentiableAt
      exact (h_diff.congr_of_eventuallyEq
        (remainder_eventuallyEq_off hMero hzS)).differentiableWithinAt
  f_eq z hz := by
    rw [if_neg hz.2]
    unfold meromorphicPolarPartTotal
    ring

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {hU : IsOpen U}
  {hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ))} {hMero : ∀ s ∈ S, MeromorphicAt f s}

/-- The decomposition constructed by `ofMeromorphic` uses `meromorphicPolarOrderAt` as its polar
order at each center. -/
@[simp] theorem ofMeromorphic_order (s : S) :
    (ofMeromorphic hU hf hMero).order s = meromorphicPolarOrderAt f s := by
  unfold ofMeromorphic
  rfl

/-- The coefficients of the decomposition constructed by `ofMeromorphic` agree with
`meromorphicPolarCoeffAt` after transporting the finite index. -/
@[simp] theorem ofMeromorphic_coeff (s : S) (k : Fin ((ofMeromorphic hU hf hMero).order s)) :
    (ofMeromorphic hU hf hMero).coeff s k =
      meromorphicPolarCoeffAt (hMero s s.2) (Fin.cast (ofMeromorphic_order s) k) := by
  unfold ofMeromorphic
  rfl

/-- The polar parts of the decomposition constructed by `ofMeromorphic` are the chosen
meromorphic polar parts. -/
@[simp] theorem ofMeromorphic_polarPart (s : S) (z : ℂ) :
    (ofMeromorphic hU hf hMero).polarPart s z = meromorphicPolarPartAt (hMero s s.2) z := by
  unfold ofMeromorphic
  rfl

/-- Away from the finite center set, the analytic remainder constructed by `ofMeromorphic`
equals `f` minus the total polar part. -/
theorem ofMeromorphic_analyticRemainder {z : ℂ} (hz : z ∉ (↑S : Set ℂ)) :
    (ofMeromorphic hU hf hMero).analyticRemainder z =
      f z - meromorphicPolarPartTotal hMero z := by
  unfold ofMeromorphic
  exact if_neg hz

/-- For a measurable curve with interval-integrable derivative, each polar part times the
derivative is interval integrable after any positive distance truncation. -/
theorem intervalIntegrable_polarPart_mul_deriv_truncated (decomp : PolarPartDecomposition f S U)
    (s : S) {γ : ℝ → ℂ} {a b : ℝ} (hγ_meas : Measurable γ)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ t - (s : ℂ)‖ > ε then decomp.polarPart s (γ t) * deriv γ t else 0)
      MeasureTheory.volume a b := by
  classical
  set M : ℝ := ∑ k : Fin (decomp.order s), ‖decomp.coeff s k‖ / ε ^ (k.val + 1) with hM_def
  have h_polar : Measurable fun t => decomp.polarPart s (γ t) := by
    have h_eq : (fun t => decomp.polarPart s (γ t)) = fun t =>
        ∑ k : Fin (decomp.order s), decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) :=
      funext fun t => decomp.polarPart_eq s (γ t)
    rw [h_eq]
    exact Finset.measurable_sum _ fun k _ =>
      (((hγ_meas.sub_const _).pow_const _).const_div _)
  refine intervalIntegrable_truncated_mul_deriv (f := decomp.polarPart s) (M := M) hderiv_int
    (aestronglyMeasurable_truncated hγ_meas.aemeasurable
      (h_polar.mul (measurable_deriv _)).aestronglyMeasurable) fun t h_far => ?_
  rw [decomp.polarPart_eq s (γ t), hM_def]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_div, norm_pow]
  gcongr

end PolarPartDecomposition

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
