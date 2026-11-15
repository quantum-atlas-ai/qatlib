/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.DeflatedSchwarzAndFilterStat
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.ZeroMarginCanonicalComplementComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.BoundaryRootDeflationComp

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial
open scoped Classical BigOperators

/-- Two polynomials without closed disk zeros, with positive real values at zero and equal unit
circle moduli, are equal. -/
private theorem normalized_closed_disk_unique (R T : Polynomial ℂ)
    (hRr : 0 < (R.eval 0).re) (hRi : (R.eval 0).im = 0)
    (hRn : ∀ z : ℂ, ‖z‖ ≤ 1 → R.eval z ≠ 0)
    (hTr : 0 < (T.eval 0).re) (hTi : (T.eval 0).im = 0)
    (hTn : ∀ z : ℂ, ‖z‖ ≤ 1 → T.eval z ≠ 0)
    (hmod : ∀ z : ℂ, ‖z‖ = 1 → ‖R.eval z‖ = ‖T.eval z‖) : R = T := by
  have he : Set.EqOn R.eval T.eval (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    change R.eval z = T.eval z
    rw [polynomial_normalized_disk_schwarz R hRr hRi hRn z hz',
      polynomial_normalized_disk_schwarz T hTr hTi hTn z hz']
    congr 3
    funext θ
    rw [hmod _ (Complex.norm_exp_ofReal_mul_I θ)]
  have hec := he.closure R.continuous T.continuous
  rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)] at hec
  apply sub_eq_zero.mp
  apply polynomial_eq_zero_of_circle_norm_zero
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.le
  simp only [eval_sub, hec hz', sub_self, norm_zero]

/-- The boundary canonical complement is unique. -/
theorem boundaryCanonical_unique (P Q S : Polynomial ℂ) (d : ℕ)
    (hQ : BoundaryCanonical P Q d) (hS : BoundaryCanonical P S d) : S = Q := by
  by_cases hQ0 : Q = 0
  · have hs0 := (boundaryCanonical_zero_iff P S d hS).2
      ((boundaryCanonical_zero_iff P Q d hQ).1 hQ0)
    exact hs0.trans hQ0.symm
  have hS0 : S ≠ 0 := by
    intro hs
    exact hQ0 ((boundaryCanonical_zero_iff P Q d hQ).2
      ((boundaryCanonical_zero_iff P S d hS).1 hs))
  have hmod (z : ℂ) (hz : ‖z‖ = 1) : ‖Q.eval z‖ = ‖S.eval z‖ := by
    have hq := hQ.2.1 z hz
    have hs := hS.2.1 z hz
    nlinarith [norm_nonneg (Q.eval z), norm_nonneg (S.eval z)]
  have hmult (z : ℂ) (hz : ‖z‖ = 1) : Q.rootMultiplicity z = S.rootMultiplicity z :=
    le_antisymm (polynomial_circle_modulus_rootMultiplicity_le Q S hQ0 hS0 hmod z hz)
      (polynomial_circle_modulus_rootMultiplicity_le S Q hS0 hQ0
        (fun w hw => (hmod w hw).symm) z hz)
  have hroots : Q.roots.filter (fun z => ‖z‖ = 1) = S.roots.filter (fun z => ‖z‖ = 1) := by
    apply Multiset.ext.mpr
    intro z
    simp only [Multiset.count_filter]
    by_cases hz : ‖z‖ = 1
    · simp only [hz, ite_true, Polynomial.count_roots]
      exact hmult z hz
    · simp only [hz, ite_false]
  have hF : boundaryComplementFactor Q = boundaryComplementFactor S := by
    rw [boundaryComplementFactor_eq_roots_product,
      boundaryComplementFactor_eq_roots_product, hroots]
  let F := boundaryComplementFactor Q
  let R := boundaryComplementNormalizedQuotient Q
  let T := boundaryComplementNormalizedQuotient S
  let ζ := boundaryComplementQuotientPhase Q
  let ξ := boundaryComplementQuotientPhase S
  obtain ⟨hmQ, _, hfacQ, hζ, _, hr, hi, hn, _⟩ := boundaryRootDeflation P Q d hQ hQ0
  obtain ⟨_, _, hfacS, hξ, _, htr, hti, htn, _⟩ := boundaryRootDeflation P S d hS hS0
  have hfacS' : S = C ξ * F * T := by simpa only [← hF] using hfacS
  have hrt : ∀ z : ℂ, ‖z‖ = 1 → ‖R.eval z‖ = ‖T.eval z‖ := by
    apply polynomial_circle_continuous_extend F hmQ.ne_zero
      (fun z => ‖R.eval z‖) (fun z => ‖T.eval z‖) R.continuous.norm T.continuous.norm
    intro z hz hf
    have he := hmod z hz
    rw [hfacQ, hfacS', eval_mul, eval_mul, eval_mul, eval_mul, eval_C, eval_C,
      norm_mul, norm_mul, norm_mul, norm_mul, hζ, hξ, one_mul] at he
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hf) he
  have hRT : R = T := normalized_closed_disk_unique R T hr hi hn htr hti htn hrt
  obtain ⟨hqr, hqi, _⟩ := hQ.2.2.resolve_left hQ0
  obtain ⟨hsr, hsi, _⟩ := hS.2.2.resolve_left hS0
  have hzero_norm : ‖Q.eval 0‖ = ‖S.eval 0‖ := by
    have hq0eval : Q.eval 0 = ζ * F.eval 0 * R.eval 0 := by
      simpa only [eval_mul, eval_C] using congrArg (fun A : Polynomial ℂ => A.eval 0) hfacQ
    have hs0eval : S.eval 0 = ξ * F.eval 0 * T.eval 0 := by
      simpa only [eval_mul, eval_C] using congrArg (fun A : Polynomial ℂ => A.eval 0) hfacS'
    rw [hq0eval, hs0eval, norm_mul, norm_mul, norm_mul, norm_mul, hζ, hξ, one_mul, ← hRT]
  have hzero_eq : Q.eval 0 = S.eval 0 := by
    have hqn : ‖Q.eval 0‖ = (Q.eval 0).re := by
      rw [← Complex.re_add_im (Q.eval 0), hqi]; simp [abs_of_pos hqr]
    have hsn : ‖S.eval 0‖ = (S.eval 0).re := by
      rw [← Complex.re_add_im (S.eval 0), hsi]; simp [abs_of_pos hsr]
    apply Complex.ext
    · simpa only [hqn, hsn] using hzero_norm
    · rw [hqi, hsi]
  have hF0 : F.eval 0 ≠ 0 := by
    intro hf
    have he : Q.eval 0 = ζ * F.eval 0 * R.eval 0 := by
      simpa only [eval_mul, eval_C] using congrArg (fun A : Polynomial ℂ => A.eval 0) hfacQ
    rw [hf, mul_zero, zero_mul] at he
    have hqne := (hQ.2.2.resolve_left hQ0).2.2 0 (by simp)
    exact hqne he
  have hphase : ζ = ξ := by
    have he := hzero_eq
    rw [hfacQ, hfacS', eval_mul, eval_mul, eval_mul, eval_mul, eval_C, eval_C, ← hRT] at he
    exact mul_right_cancel₀ (mul_ne_zero hF0 (hn 0 (by simp))) (by simpa only [mul_assoc] using he)
  rw [hfacQ, hfacS', ← hRT, ← hphase]

/-- A unit circle bounded polynomial has a unique boundary canonical complement with the
deflated Schwarz representation and the stated unitary filter action. -/
theorem deflatedSchwarzAndFilter : DeflatedSchwarzAndFilter := by
  intro P d hp hb
  obtain ⟨Q, hc, _⟩ := zeroMarginCanonicalComplement P d hp hb
  refine ⟨Q, hc, fun S hs => boundaryCanonical_unique P Q S d hc hs, ?_, ?_⟩
  · intro hQ z hz
    obtain ⟨_, _, hf, _, _, hr, hi, hn, _⟩ := boundaryRootDeflation P Q d hc hQ
    have he := polynomial_normalized_disk_schwarz (boundaryComplementNormalizedQuotient Q)
      hr hi hn z hz
    calc
      Q.eval z = boundaryComplementQuotientPhase Q * (boundaryComplementFactor Q).eval z *
          (boundaryComplementNormalizedQuotient Q).eval z := by
        simpa only [eval_mul, eval_C] using congrArg (fun A : Polynomial ℂ => A.eval z) hf
      _ = _ := by rw [he]; rfl
  · intro z hz
    obtain ⟨hu, ho⟩ := circle_complement_actual_filter_consumer P Q z hz (hc.2.1 z hz)
    refine ⟨hu, ?_⟩
    have hket : Ket false = (fun b : Bool => if b then (0 : ℂ) else 1) := by
      funext b
      cases b <;> rfl
    simpa only [ApplyGate, hket] using ho

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
