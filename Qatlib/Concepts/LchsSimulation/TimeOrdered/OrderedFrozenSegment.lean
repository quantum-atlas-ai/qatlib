/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Frozen-segment bounds for ordered evolution

This module compares ordered Hamiltonian evolution on a segment with evolution under the
Hamiltonian frozen at its left endpoint. `orderedEvolution_congr_on_segment` localizes the
generator data, and `orderedSegmentClamp` lets the unitarity and error results use Hermitian
hypotheses only on the segment.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `orderedEvolution_frozen_segment_error`: bounds freezing error by the integrated Hamiltonian
  variation.
* `orderedEvolution_frozen_segment_error_on_segment`: uses Hermiticity only on the relevant time
  segment.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.LchsSimulation.TimeOrdered
open Matrix
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Freezing a continuous Hermitian Hamiltonian at the left endpoint gives operator error at
most the integral of `‖H u - H s‖` over the ordered segment. -/
theorem orderedEvolution_frozen_segment_error
    (H : ℝ → Matrix I I ℂ) (hcont : Continuous H)
    (hHerm : ∀ t, (H t).IsHermitian) {s t : ℝ} (hst : s ≤ t) :
    ‖orderedEvolution (fun u => Complex.I • H u) s t -
        HamiltonianEvolution (H s) (t - s)‖ ≤
      ∫ u in s..t, ‖H u - H s‖ := by
  let A := fun u => Complex.I • H u
  let B := -Complex.I • H s
  let V := fun u => orderedEvolution A u t
  let W := fun u : ℝ => NormedSpace.exp ((u - s) • B)
  let f := fun u => V u * W u
  let D := fun u => V u * (A u - A s) * W u
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hV (u : ℝ) : HasDerivAt V (V u * A u) u :=
    orderedEvolution_hasDerivAt_start A hA t u
  have hW (u : ℝ) : HasDerivAt W (-(A s * W u)) u := by
    have hd := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (u - s)).scomp u
      ((hasDerivAt_id u).sub_const s)
    change HasDerivAt W (1 • (B * W u)) u at hd
    simpa only [one_smul, B, A, neg_smul, neg_mul] using! hd
  have hWeq (u : ℝ) : W u = HamiltonianEvolution (H s) (u - s) := by
    unfold W B HamiltonianEvolution
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul]
    ring
  have hf (u : ℝ) : HasDerivAt f (D u) u := by
    convert! (hV u).mul (hW u) using 1
    dsimp only [D]
    noncomm_ring
  have hcV : Continuous V :=
    continuous_iff_continuousAt.mpr (fun u => (hV u).continuousAt)
  have hcW : Continuous W :=
    continuous_iff_continuousAt.mpr (fun u => (hW u).continuousAt)
  have hcD : Continuous D := (hcV.mul (hA.sub continuous_const)).mul hcW
  have hi : (∫ u in s..t, D u) = f t - f s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf u)
      (hcD.intervalIntegrable s t)
  have hend : f t - f s = W t - orderedEvolution A s t := by
    simp [f, V, W]
  have hnV (u : ℝ) : ‖V u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hcont hHerm u t)
  have hnW (u : ℝ) : ‖W u‖ ≤ 1 := by
    rw [hWeq]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hHerm s) _)
  have hb (u : ℝ) : ‖D u‖ ≤ ‖H u - H s‖ := by
    calc
      _ ≤ ‖V u‖ * ‖A u - A s‖ * ‖W u‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖A u - A s‖ * 1 := by
        gcongr <;> first | exact hnV u | exact hnW u
      _ = ‖H u - H s‖ := by
        dsimp only [A]
        rw [← smul_sub]
        simp [norm_smul]
  calc
    _ = ‖f t - f s‖ := by rw [hend, hWeq, norm_sub_rev]
    _ = ‖∫ u in s..t, D u‖ := congrArg norm hi.symm
    _ ≤ _ := intervalIntegral.norm_integral_le_of_norm_le hst
      (Filter.Eventually.of_forall (fun u _ => hb u))
      ((hcont.sub continuous_const).norm.intervalIntegrable s t)

/-- Generators that agree on `[s, t]` have the same ordered evolution from `s` to `t`. -/
theorem orderedEvolution_congr_on_segment
    (A B : ℝ → Matrix I I ℂ) {s t : ℝ} (hst : s ≤ t)
    (hAB : ∀ u ∈ Set.Icc s t, A u = B u) :
    orderedEvolution A s t = orderedEvolution B s t := by
  have hterm : ∀ n, ∀ v ∈ Set.Icc s t,
      orderedDysonTerm A s n v = orderedDysonTerm B s n v := by
    intro n
    induction n with
    | zero => intro v _; rfl
    | succ n ih =>
      intro v hv
      simp only [orderedDysonTerm]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hv.1] at hu
      have hut : u ∈ Set.Icc s t := ⟨hu.1, hu.2.trans hv.2⟩
      (try dsimp only)
      rw [hAB u hut, ih u hut]
  unfold orderedEvolution
  exact tsum_congr (fun n => hterm n t ⟨hst, le_rfl⟩)

/-- The real-valued clamp `max s (min t u)` onto an ordered time segment. -/
def orderedSegmentClamp (s t u : ℝ) : ℝ := max s (min t u)

/-- For `s ≤ t`, clamping any real number gives an element of `[s, t]`. -/
theorem orderedSegmentClamp_mem {s t : ℝ} (hst : s ≤ t) (u : ℝ) :
    orderedSegmentClamp s t u ∈ Set.Icc s t := by
  exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩

/-- Clamping a point already in `[s, t]` leaves it unchanged. -/
theorem orderedSegmentClamp_eq {s t u : ℝ} (hu : u ∈ Set.Icc s t) :
    orderedSegmentClamp s t u = u := by
  simp only [orderedSegmentClamp, min_eq_right hu.2, max_eq_right hu.1]

/-- A continuous Hamiltonian that is Hermitian on `[s, t]` has unitary ordered evolution from
`s` to `t`. -/
theorem orderedEvolution_unitary_on_segment
    (H : ℝ → Matrix I I ℂ) (hcont : Continuous H)
    {s t : ℝ} (hst : s ≤ t) (hHerm : ∀ u ∈ Set.Icc s t, (H u).IsHermitian) :
    orderedEvolution (fun u => Complex.I • H u) s t ∈ Matrix.unitaryGroup I ℂ := by
  let G := fun u => H (orderedSegmentClamp s t u)
  have hc : Continuous G := hcont.comp (continuous_const.max (continuous_const.min continuous_id))
  have hg : ∀ u, (G u).IsHermitian := fun u => hHerm _ (orderedSegmentClamp_mem hst u)
  have he : orderedEvolution (fun u => Complex.I • G u) s t =
      orderedEvolution (fun u => Complex.I • H u) s t :=
    orderedEvolution_congr_on_segment _ _ hst (by
      intro u hu
      simp only [G, orderedSegmentClamp_eq hu])
  rw [← he]
  exact ordered_evolution_hermitian_unitary I G hc hg s t

/-- For a continuous Hamiltonian Hermitian on `[s, t]`, freezing at `s` gives operator error at
most the integral of `‖H u - H s‖` on that segment. -/
theorem orderedEvolution_frozen_segment_error_on_segment
    (H : ℝ → Matrix I I ℂ) (hcont : Continuous H)
    {s t : ℝ} (hst : s ≤ t) (hHerm : ∀ u ∈ Set.Icc s t, (H u).IsHermitian) :
    ‖orderedEvolution (fun u => Complex.I • H u) s t -
        HamiltonianEvolution (H s) (t - s)‖ ≤ ∫ u in s..t, ‖H u - H s‖ := by
  let G := fun u => H (orderedSegmentClamp s t u)
  have hc : Continuous G := hcont.comp (continuous_const.max (continuous_const.min continuous_id))
  have hg : ∀ u, (G u).IsHermitian := fun u => hHerm _ (orderedSegmentClamp_mem hst u)
  have he : ∀ u ∈ Set.Icc s t, G u = H u := by
    intro u hu
    simp only [G, orderedSegmentClamp_eq hu]
  have hp := orderedEvolution_congr_on_segment
    (fun u => Complex.I • G u) (fun u => Complex.I • H u) hst (by
      intro u hu; (try dsimp only); rw [he u hu])
  have hint : (∫ u in s..t, ‖G u - G s‖) = ∫ u in s..t, ‖H u - H s‖ := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hst] at hu
    (try dsimp only)
    rw [he u hu, he s ⟨le_rfl, hst⟩]
  have h := orderedEvolution_frozen_segment_error G hc hg hst
  rw [hp, hint, he s ⟨le_rfl, hst⟩] at h
  exact h

end Qatlib.Concepts.LchsSimulation.TimeOrdered
