/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
public import Mathlib.Analysis.Real.Pi.Bounds
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.CircleComplementConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial
open scoped Classical BigOperators

def BoundaryCanonical (P Q : Polynomial ℂ) (d : ℕ) : Prop :=
  Q.natDegree ≤ d ∧
  (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) ∧
  (Q = 0 ∨ (0 < (Q.eval 0).re ∧ (Q.eval 0).im = 0 ∧
    ∀ z : ℂ, ‖z‖ < 1 → Q.eval z ≠ 0))

def boundaryComplementRoots (Q : Polynomial ℂ) : Finset ℂ :=
  Q.roots.toFinset.filter fun z => ‖z‖ = 1

def boundaryComplementFactor (Q : Polynomial ℂ) : Polynomial ℂ :=
  ∏ z ∈ boundaryComplementRoots Q, (X-C z)^Q.rootMultiplicity z

def boundaryComplementQuotient (Q : Polynomial ℂ) : Polynomial ℂ :=
  Q /ₘ boundaryComplementFactor Q

def boundaryComplementNormalizedQuotient (Q : Polynomial ℂ) : Polynomial ℂ :=
  let R := boundaryComplementQuotient Q
  C ((‖R.eval 0‖ : ℂ)/R.eval 0)*R

def boundaryComplementQuotientPhase (Q : Polynomial ℂ) : ℂ :=
  let R := boundaryComplementQuotient Q
  R.eval 0/(‖R.eval 0‖ : ℂ)

def boundaryComplementProfile (Q : Polynomial ℂ) (z : ℂ) : ℝ :=
  ‖(boundaryComplementNormalizedQuotient Q).eval z‖^2

/-- On the unit circle, a linear factor and its reflected factor have equal norms. -/
private theorem boundary_reflected_factor_circle_norm (r z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - star r * z‖ = ‖z - r‖ := by
  have hzz : z * star z = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  calc
    ‖1 - star r * z‖ = ‖z * star (z - r)‖ := by
      congr 1
      rw [star_sub, mul_sub, hzz]
      ring
    _ = ‖z - r‖ := by rw [norm_mul, hz, norm_star, one_mul]

/-- The reflected linear factor is nonzero when both its root parameter and argument lie in the
open unit disk. -/
private theorem boundary_reflected_factor_ne_zero (r z : ℂ)
    (hr : ‖r‖ < 1) (hz : ‖z‖ < 1) : 1 - star r * z ≠ 0 := by
  intro he
  have he' : star r * z = 1 := by linear_combination -he
  have hh : ‖r‖ * ‖z‖ = 1 := by simpa [norm_mul] using congrArg norm he'
  have hle : ‖r‖ * ‖z‖ ≤ ‖r‖ := by nlinarith [norm_nonneg r]
  linarith

/-- Every nonzero complex polynomial admits a polynomial of no larger degree with no open disk
zeros and the same modulus on the unit circle. -/
theorem polynomial_outer_open_disk_factor (A : Polynomial ℂ) (ha0 : A ≠ 0) :
    ∃ B : Polynomial ℂ, B.natDegree ≤ A.natDegree ∧
      (∀ z : ℂ, ‖z‖ < 1 → B.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖B.eval z‖ = ‖A.eval z‖) := by
  generalize hd : A.natDegree = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hdeg : A.natDegree = 0
    · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
      have hane : a ≠ 0 := by simpa using ha0
      exact ⟨C a, by simp, fun _ _ => by simpa using hane, fun _ _ => rfl⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)))
    have hr' : A.IsRoot r := by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hr
    obtain ⟨g, hAg⟩ := Polynomial.dvd_iff_isRoot.mpr hr'
    have hg0 : g ≠ 0 := by intro h; simp [h] at hAg; exact ha0 hAg
    have hdegree : A.natDegree = 1 + g.natDegree := by
      rw [hAg, natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C]
    obtain ⟨B, hBd, hBn, hBc⟩ := ih g.natDegree (by omega) g hg0 rfl
    by_cases hrin : ‖r‖ < 1
    · let b : Polynomial ℂ := C 1 - C (star r) * X
      have hbd : b.natDegree ≤ 1 := by
        apply le_trans (natDegree_sub_le _ _)
        simp only [natDegree_C, max_le_iff, zero_le, true_and]
        exact (natDegree_mul_le).trans (by simp)
      refine ⟨b * B, ?_, ?_, ?_⟩
      · exact (natDegree_mul_le).trans (by omega)
      · intro z hz
        simp only [eval_mul]
        apply mul_ne_zero _ (hBn z hz)
        simpa [b] using boundary_reflected_factor_ne_zero r z hrin hz
      · intro z hz
        simp only [eval_mul, norm_mul]
        rw [hBc z hz, hAg, eval_mul, norm_mul]
        congr 1
        simpa [b] using boundary_reflected_factor_circle_norm r z hz
    · have hrout : 1 ≤ ‖r‖ := le_of_not_gt hrin
      refine ⟨(X - C r) * B, ?_, ?_, ?_⟩
      · have hh := natDegree_mul_le (p := X - C r) (q := B)
        rw [natDegree_X_sub_C] at hh
        omega
      · intro z hz
        simp only [eval_mul, eval_sub, eval_X, eval_C]
        apply mul_ne_zero _ (hBn z hz)
        intro he
        have hz' : z = r := sub_eq_zero.mp he
        rw [hz'] at hz
        linarith
      · intro z hz
        simp only [eval_mul, norm_mul]
        rw [hBc z hz, hAg, eval_mul, norm_mul]

/-- A complex polynomial whose norm vanishes on the entire unit circle is zero. -/
theorem polynomial_eq_zero_of_circle_norm_zero (Q : Polynomial ℂ)
    (hq : ∀ z : ℂ, ‖z‖ = 1 → ‖Q.eval z‖ = 0) : Q = 0 := by
  apply Polynomial.funext
  intro z
  have hb : ∀ w : ℂ, ‖w‖ = 1 → ‖Q.eval w‖ ≤ 0 := fun w hw => (hq w hw).le
  have hn : ‖Q.eval z‖ ≤ 0 := by
    by_cases hz : ‖z‖ ≤ 1
    · exact canonicalComplement_polynomial_disk_bound Q 0 hb z hz
    · simpa using canonicalComplement_polynomial_exterior_bound Q Q.natDegree 0
        le_rfl hb z (le_of_not_ge hz)
  simpa using norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- A boundary canonical complement is zero exactly when the original polynomial has modulus one
throughout the unit circle. -/
theorem boundaryCanonical_zero_iff (P Q : Polynomial ℂ) (d : ℕ)
    (hq : BoundaryCanonical P Q d) :
    Q = 0 ↔ ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ = 1 := by
  constructor
  · intro h z hz
    have hc := hq.2.1 z hz
    simp only [h, eval_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hc
    nlinarith [norm_nonneg (P.eval z)]
  · intro hp
    apply polynomial_eq_zero_of_circle_norm_zero
    intro z hz
    have hc := hq.2.1 z hz
    rw [hp z hz] at hc
    nlinarith [norm_nonneg (Q.eval z)]

/-- Every degree bounded polynomial with modulus at most one on the unit circle admits a
boundary canonical complement. -/
theorem boundaryCanonical_exists (P : Polynomial ℂ) (d : ℕ)
    (hp : P.natDegree ≤ d) (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : Polynomial ℂ, BoundaryCanonical P Q d := by
  obtain ⟨A, hAd, hAc⟩ := circle_complement_zero_margin_exists P d hp hb
  by_cases ha0 : A = 0
  · exact ⟨A, hAd, hAc, Or.inl ha0⟩
  obtain ⟨B, hBd, hBn, hBc⟩ := polynomial_outer_open_disk_factor A ha0
  have hb0 : B.eval 0 ≠ 0 := hBn 0 (by simp)
  let c : ℂ := (‖B.eval 0‖ : ℂ) / B.eval 0
  have hcn : ‖c‖ = 1 := by
    simp only [c, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hb0)
  have hc0 : c * B.eval 0 = (‖B.eval 0‖ : ℂ) := div_mul_cancel₀ _ hb0
  refine ⟨C c * B, (natDegree_mul_le).trans (by simpa using hBd.trans hAd), ?_, Or.inr ?_⟩
  · intro z hz
    simpa only [eval_mul, eval_C, norm_mul, hcn, one_mul, hBc z hz] using hAc z hz
  refine ⟨?_, ?_, ?_⟩
  · simp only [eval_mul, eval_C, hc0, Complex.ofReal_re]
    exact norm_pos_iff.mpr hb0
  · simp only [eval_mul, eval_C, hc0, Complex.ofReal_im]
  · intro z hz
    simp only [eval_mul, eval_C]
    exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [hcn]; norm_num)) (hBn z hz)

/-- The boundary complement factor is the product of the linear factors for the unit circle
roots, with multiplicity. -/
theorem boundaryComplementFactor_eq_roots_product (Q : Polynomial ℂ) :
    boundaryComplementFactor Q =
      ((Q.roots.filter fun z => ‖z‖ = 1).map fun z => X - C z).prod := by
  rw [Finset.prod_multiset_map_count, Multiset.toFinset_filter]
  unfold boundaryComplementFactor boundaryComplementRoots
  apply Finset.prod_congr rfl
  intro z hz
  rw [Multiset.count_filter, ite_eq_left (Finset.mem_filter.mp hz).2, Polynomial.count_roots]

/-- The boundary complement factor is monic. -/
theorem boundaryComplementFactor_monic (Q : Polynomial ℂ) :
    (boundaryComplementFactor Q).Monic := by
  rw [boundaryComplementFactor_eq_roots_product]
  exact monic_multisetProd_X_sub_C _

/-- The boundary complement factor divides the original complement polynomial. -/
theorem boundaryComplementFactor_dvd (Q : Polynomial ℂ) :
    boundaryComplementFactor Q ∣ Q := by
  rw [boundaryComplementFactor_eq_roots_product]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map (Multiset.filter_le _ _))).trans
    Q.prod_multiset_X_sub_C_dvd

/-- The boundary complement factor multiplied by its quotient recovers the complement
polynomial. -/
theorem boundaryComplementFactor_mul_quotient (Q : Polynomial ℂ) :
    boundaryComplementFactor Q * boundaryComplementQuotient Q = Q := by
  have hm := (Polynomial.modByMonic_eq_zero_iff_dvd
    (boundaryComplementFactor_monic Q)).mpr (boundaryComplementFactor_dvd Q)
  simpa only [hm, zero_add, boundaryComplementQuotient] using
    Polynomial.modByMonic_add_div Q (boundaryComplementFactor Q)

/-- The roots of the boundary complement factor are exactly the unit circle roots of the
complement, with multiplicity. -/
theorem boundaryComplementFactor_roots (Q : Polynomial ℂ) :
    (boundaryComplementFactor Q).roots = Q.roots.filter fun z => ‖z‖ = 1 := by
  rw [boundaryComplementFactor_eq_roots_product, Polynomial.roots_multiset_prod_X_sub_C]

/-- The boundary complement factor preserves the multiplicity of every unit circle root. -/
theorem boundaryComplementFactor_rootMultiplicity (Q : Polynomial ℂ) (z : ℂ)
    (hz : ‖z‖ = 1) :
    (boundaryComplementFactor Q).rootMultiplicity z = Q.rootMultiplicity z := by
  rw [← Polynomial.count_roots, boundaryComplementFactor_roots,
    Multiset.count_filter, ite_eq_left hz, Polynomial.count_roots]

/-- The quotient of a nonzero boundary canonical complement by its boundary root factor has no
zeros in the closed unit disk. -/
theorem boundaryComplementQuotient_closed_disk (P Q : Polynomial ℂ) (d : ℕ)
    (hc : BoundaryCanonical P Q d) (hQ : Q ≠ 0) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → (boundaryComplementQuotient Q).eval z ≠ 0 := by
  have he := boundaryComplementFactor_mul_quotient Q
  have hq : boundaryComplementQuotient Q ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact hQ he.symm
  have hn : ∀ z : ℂ, ‖z‖ < 1 → Q.eval z ≠ 0 := by
    rcases hc.2.2 with h | h
    · exact (hQ h).elim
    · exact h.2.2
  intro z hz hzero
  by_cases hzin : ‖z‖ < 1
  · apply hn z hzin
    rw [← he, eval_mul, hzero, mul_zero]
  · have hzc : ‖z‖ = 1 := le_antisymm hz (le_of_not_gt hzin)
    have hm := Polynomial.rootMultiplicity_mul (show
      boundaryComplementFactor Q * boundaryComplementQuotient Q ≠ 0 by rwa [he])
      (x := z)
    rw [he, boundaryComplementFactor_rootMultiplicity Q z hzc] at hm
    have hp := (Polynomial.rootMultiplicity_pos hq).2 hzero
    omega

/-- A polynomial with no zeros in the closed unit disk has a logarithm holomorphic in the open
disk and continuous on its closure. -/
private theorem boundary_polynomial_disk_log_exists (A : Polynomial ℂ)
    (ha : ∀ z : ℂ, ‖z‖ ≤ 1 → A.eval z ≠ 0) :
    ∃ H : ℂ → ℂ, DiffContOnCl ℂ H (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → Complex.exp (H z) = A.eval z) := by
  generalize hd : A.natDegree = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    have ha0 : A ≠ 0 := by intro h; have := ha 0 (by simp); simp [h] at this
    by_cases hdeg : A.natDegree = 0
    · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
      have hane : a ≠ 0 := by simpa using ha 0 (by simp)
      exact ⟨fun _ => Complex.log a, diffContOnCl_const,
        fun _ _ => by simpa using Complex.exp_log hane⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)))
    have hr' : A.IsRoot r := by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hr
    obtain ⟨g, hAg⟩ := Polynomial.dvd_iff_isRoot.mpr hr'
    have hg0 : g ≠ 0 := by intro h; simp [h] at hAg; exact ha0 hAg
    have hdegree : A.natDegree = 1+g.natDegree := by
      rw [hAg, natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C]
    have hgc : ∀ z : ℂ, ‖z‖ ≤ 1 → g.eval z ≠ 0 := by
      intro z hz hg
      apply ha z hz
      simp [hAg, hg]
    have hrnorm : 1 < ‖r‖ := lt_of_not_ge (fun h => ha r h hr')
    have hr0 : r ≠ 0 := by intro h; norm_num [h] at hrnorm
    obtain ⟨H, hHd, hHe⟩ := ih g.natDegree (by omega) g hgc rfl
    have hslit (z : ℂ) (hz : ‖z‖ ≤ 1) : 1-z/r ∈ Complex.slitPlane := by
      have hh : ‖-(z/r)‖ < 1 := by
        rw [norm_neg, norm_div, div_lt_one (by positivity)]
        exact hz.trans_lt hrnorm
      simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
    have hlog : DiffContOnCl ℂ (fun z : ℂ => Complex.log (1-z/r)) (Metric.ball 0 1) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.clog (by fun_prop)
      exact hslit z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    refine ⟨fun z => Complex.log (-r)+Complex.log (1-z/r)+H z,
      (diffContOnCl_const.add hlog).add hHd, ?_⟩
    intro z hz
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hr0),
      Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz)), hHe z hz, hAg,
      eval_mul, eval_sub, eval_X, eval_C]
    field_simp
    ring

set_option maxHeartbeats 800000 in

/-- A holomorphic disk function continuous on the closure and real at zero equals the Schwarz
circle average of its real part. -/
private theorem boundary_schwarz_circle_average (H : ℂ → ℂ)
    (hH : DiffContOnCl ℂ H (Metric.ball 0 1)) (hH0 : (H 0).im = 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Real.circleAverage (fun u : ℂ => (u+z)/(u-z)*(H u).re) 0 1 = H z := by
  let K : ℂ → ℂ := fun u => (u+z)/(u-z)
  let C : ℂ → ℂ := fun u => u/(u-z)
  have hzs : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hden (u : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1) : u-z ≠ 0 := by
    intro he
    have he' : u = z := sub_eq_zero.mp he
    have hu' : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hu
    rw [he'] at hu'
    linarith
  have hHc : ContinuousOn H (Metric.sphere (0 : ℂ) 1) := by
    apply hH.2.mono
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall
  have hKc : ContinuousOn K (Metric.sphere (0 : ℂ) 1) := by
    dsimp [K]
    fun_prop (disch := exact hden _ ‹_›)
  have hCc : ContinuousOn C (Metric.sphere (0 : ℂ) 1) := by
    dsimp [C]
    fun_prop (disch := exact hden _ ‹_›)
  have hiH : CircleIntegrable H 0 1 := hHc.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiC : CircleIntegrable (fun u => C u*H u) 0 1 :=
      (hCc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiK : CircleIntegrable (fun u => K u*H u) 0 1 :=
      (hKc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hKrc : ContinuousOn (fun u => ((K u).re : ℂ)) (Metric.sphere (0 : ℂ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hKc)
  have hiR : CircleIntegrable (fun u => (K u).re*H u) 0 1 :=
      (hKrc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiS : CircleIntegrable (fun u => star (K u)*H u) 0 1 :=
      (hKc.star.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hHabs : DiffContOnCl ℂ H (Metric.ball 0 |(1 : ℝ)|) := by
    simpa only [abs_one] using hH
  have hC : Real.circleAverage (fun u => C u*H u) 0 1 = H z := by
    simpa only [C, sub_zero, smul_eq_mul] using hHabs.circleAverage_smul_div
      (by simpa only [abs_one] using hzs)
  have hA : Real.circleAverage H 0 1 = H 0 := hHabs.circleAverage
  have hR : Real.circleAverage (fun u => (K u).re*H u) 0 1 = H z := by
    simpa [K, smul_eq_mul] using hH.circleAverage_re_herglotzRieszKernel_smul' hzs
  have hK : Real.circleAverage (fun u => K u*H u) 0 1 = 2*H z-H 0 := by
    calc
      _ = Real.circleAverage (fun u => (2 : ℂ) • (C u*H u)-H u) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro u hu
        have hu' : u ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [abs_one] using hu
        dsimp [K, C]
        change (u+z)/(u-z)*H u = 2*(u/(u-z)*H u)-H u
        field_simp [hden u hu']
        ring
      _ = 2*H z-H 0 := by
        rw [Real.circleAverage_fun_sub (f₁ := fun u => (2 : ℂ) • (C u*H u)) hiC.const_smul hiH,
          Real.circleAverage_fun_smul, hC, hA, smul_eq_mul]
  have hS : Real.circleAverage (fun u => star (K u)*H u) 0 1 = H 0 := by
    calc
      _ = Real.circleAverage (fun u => (2 : ℂ) • ((K u).re*H u)-K u*H u) 0 1 := by
        congr 1
        funext u
        simp only [smul_eq_mul]
        have hr : star (K u) = 2*(K u).re-K u := by
          apply Complex.ext <;> simp
          ring
        rw [hr]
        ring
      _ = H 0 := by
        rw [Real.circleAverage_fun_sub (f₁ := fun u => (2 : ℂ) • ((K u).re*H u)) hiR.const_smul hiK,
          Real.circleAverage_fun_smul, hR, hK, smul_eq_mul]
        ring
  have hT : Real.circleAverage (fun u => K u*star (H u)) 0 1 = H 0 := by
    have hh := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm hiS
    have h0 : star (H 0) = H 0 := by
      apply Complex.ext <;> simp [hH0]
    change Real.circleAverage (fun u => star (star (K u)*H u)) 0 1 =
      star (Real.circleAverage (fun u => star (K u)*H u) 0 1) at hh
    rw [hS, h0] at hh
    simpa only [star_mul, star_star, mul_comm] using hh
  calc
    _ = Real.circleAverage (fun u => (2 : ℂ)⁻¹ • (K u*H u+K u*star (H u))) 0 1 := by
      congr 1
      funext u
      change K u*(H u).re = (2 : ℂ)⁻¹*(K u*H u+K u*star (H u))
      have hr : ((H u).re : ℂ) = (2 : ℂ)⁻¹*(H u+star (H u)) := by
        apply Complex.ext <;> simp
        ring
      rw [hr]
      ring
    _ = H z := by
      have hiT : CircleIntegrable (fun u => K u*star (H u)) 0 1 :=
        (hKc.mul hHc.star).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
      rw [Real.circleAverage_fun_smul, Real.circleAverage_fun_add hiK hiT, hK, hT,
        smul_eq_mul]
      ring

/-- A polynomial with positive real value at zero and no closed disk zeros equals the
exponential of the Schwarz integral of its boundary log squared modulus. -/
theorem polynomial_normalized_disk_schwarz (Q : Polynomial ℂ)
    (hQr : 0 < (Q.eval 0).re) (hQi : (Q.eval 0).im = 0)
    (hQn : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) :
    ∀ z : ℂ, ‖z‖ < 1 → Q.eval z = Complex.exp
      ((1/(4*Real.pi) : ℝ) •
        (∫ θ : ℝ in 0..2*Real.pi,
          (Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
            ((Real.log (‖Q.eval (Complex.exp (θ*Complex.I))‖^2) : ℝ) : ℂ))) := by
  obtain ⟨H, hHd, hHe⟩ := boundary_polynomial_disk_log_exists Q hQn
  let c : ℂ := (Real.log (Q.eval 0).re : ℝ)
  have hQ0 : Q.eval 0 ≠ 0 := hQn 0 (by simp)
  have hc : Complex.exp c = Q.eval 0 := by
    simp only [c, ← Complex.ofReal_exp, Real.exp_log hQr]
    apply Complex.ext <;> simp [hQi]
  let L : ℂ → ℂ := fun z => H z+c-H 0
  have hLd : DiffContOnCl ℂ L (Metric.ball 0 1) :=
    (hHd.add diffContOnCl_const).sub diffContOnCl_const
  have hLe (z : ℂ) (hz : ‖z‖ ≤ 1) : Complex.exp (L z) = Q.eval z := by
    dsimp [L]
    rw [Complex.exp_sub, Complex.exp_add, hHe z hz, hc, hHe 0 (by simp)]
    exact mul_div_cancel_right₀ _ hQ0
  have hL0 : (L 0).im = 0 := by simp [L, c]
  have hLre (u : ℂ) (hu : ‖u‖ = 1) :
      (L u).re = (1/2 : ℝ)*Real.log (‖Q.eval u‖^2) := by
    have hl : Real.log ‖Q.eval u‖ = (L u).re := by
      rw [← hLe u hu.le, Complex.norm_exp, Real.log_exp]
    rw [Real.log_pow, hl]
    ring
  intro z hz
  rw [← hLe z hz.le]
  congr 1
  calc
    L z = Real.circleAverage (fun u : ℂ => (u+z)/(u-z)*(L u).re) 0 1 :=
      (boundary_schwarz_circle_average L hLd hL0 z hz).symm
    _ = (1/(4*Real.pi) : ℝ) •
        (∫ θ : ℝ in 0..2*Real.pi,
          (Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
          ((Real.log (‖Q.eval (Complex.exp (θ*Complex.I))‖^2) : ℝ) : ℂ)) := by
      rw [Real.circleAverage_def]
      have hf : (fun θ : ℝ => (circleMap 0 1 θ+z)/(circleMap 0 1 θ-z)*(L (circleMap 0 1 θ)).re) =
          (fun θ : ℝ => (1/2 : ℝ) •
            ((Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
              ((Real.log (‖Q.eval (Complex.exp (θ*Complex.I))‖^2) : ℝ) : ℂ))) := by
        funext θ
        simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
        rw [hLre _ (Complex.norm_exp_ofReal_mul_I θ)]
        simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat, Complex.real_smul]
        ring
      rw [hf, intervalIntegral.integral_smul, smul_smul]
      congr 1
      field_simp
      ring

open Filter
open scoped Topology

private def boundaryApproach (z : ℂ) (n : ℕ) : ℂ :=
  z * Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)

/-- The boundary approach sequence converges to its target point. -/
private theorem boundaryApproach_tendsto (z : ℂ) :
    Tendsto (boundaryApproach z) atTop (𝓝 z) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).ofReal.mul_const Complex.I
  have he := Complex.continuous_exp.continuousAt.tendsto.comp h
  change Tendsto (fun n : ℕ =>
    z * Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) atTop (𝓝 z)
  simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    using tendsto_const_nhds.mul he

/-- The boundary approach sequence stays on the unit circle when its target lies on that circle. -/
private theorem boundaryApproach_norm (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖boundaryApproach z n‖ = 1 := by
  rw [boundaryApproach, norm_mul, hz, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Every term of the boundary approach sequence differs from its unit circle target. -/
private theorem boundaryApproach_ne (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    boundaryApproach z n ≠ z := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  intro h
  have he : Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) = 1 :=
    mul_left_cancel₀ hz0 (by simpa [boundaryApproach] using h)
  have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hb : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hlo : -Real.pi < (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith [Real.pi_pos]
  have hhi : (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im ≤ Real.pi := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith [Real.pi_gt_three]
  have hlog := Complex.log_exp hlo hhi
  rw [he, Complex.log_one] at hlog
  have him := congrArg Complex.im hlog
  simp only [Complex.zero_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero] at him
  linarith

/-- For nonzero polynomials with equal unit circle modulus, each unit circle root multiplicity
of the first is at most that of the second. -/
theorem polynomial_circle_modulus_rootMultiplicity_le (Q S : Polynomial ℂ) (hQ : Q ≠ 0) (hS : S ≠ 0)
    (he : ∀ w : ℂ, ‖w‖ = 1 → ‖Q.eval w‖ = ‖S.eval w‖)
    (z : ℂ) (hz : ‖z‖ = 1) : Q.rootMultiplicity z ≤ S.rootMultiplicity z := by
  by_contra h
  have hlt : S.rootMultiplicity z < Q.rootMultiplicity z := Nat.lt_of_not_ge h
  obtain ⟨q, hq, hqnd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ z
  obtain ⟨s, hs, hsnd⟩ := S.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hS z
  have hs0 : s.eval z ≠ 0 := fun h => hsnd (Polynomial.dvd_iff_isRoot.mpr h)
  have hvalues (n : ℕ) : ‖s.eval (boundaryApproach z n)‖ =
      ‖boundaryApproach z n - z‖ ^ (Q.rootMultiplicity z - S.rootMultiplicity z) *
        ‖q.eval (boundaryApproach z n)‖ := by
    have hd : boundaryApproach z n - z ≠ 0 := sub_ne_zero.mpr (boundaryApproach_ne z hz n)
    have he' := he (boundaryApproach z n) (boundaryApproach_norm z hz n)
    rw [hq, hs, eval_mul, eval_mul, eval_pow, eval_pow, eval_sub, eval_X, eval_C,
      norm_mul, norm_mul, norm_pow, norm_pow] at he'
    have hsum : Q.rootMultiplicity z = S.rootMultiplicity z +
        (Q.rootMultiplicity z - S.rootMultiplicity z) := by omega
    rw [hsum, pow_add, mul_assoc] at he'
    exact (mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd)) he').symm
  have hlim := boundaryApproach_tendsto z
  have hls : Tendsto (fun n => ‖s.eval (boundaryApproach z n)‖) atTop (𝓝 ‖s.eval z‖) :=
    (s.continuous.norm.continuousAt.tendsto).comp hlim
  have hlq : Tendsto (fun n => ‖q.eval (boundaryApproach z n)‖) atTop (𝓝 ‖q.eval z‖) :=
    (q.continuous.norm.continuousAt.tendsto).comp hlim
  have hld := (hlim.sub_const z).norm.pow (Q.rootMultiplicity z - S.rootMultiplicity z)
  have hp : Q.rootMultiplicity z - S.rootMultiplicity z ≠ 0 := by omega
  have hzero : Tendsto (fun n => ‖boundaryApproach z n-z‖ ^
      (Q.rootMultiplicity z-S.rootMultiplicity z) * ‖q.eval (boundaryApproach z n)‖)
      atTop (𝓝 0) := by
    simpa [zero_pow hp] using hld.mul hlq
  have hr : ‖s.eval z‖ = 0 := tendsto_nhds_unique hls (by simpa only [← hvalues] using hzero)
  exact hs0 (norm_eq_zero.mp hr)

/-- Equality of two continuous real functions on the unit circle away from the zeros of a
nonzero polynomial extends to the whole circle. -/
theorem polynomial_circle_continuous_extend (F : Polynomial ℂ) (hF : F ≠ 0)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (he : ∀ z : ℂ, ‖z‖ = 1 → F.eval z ≠ 0 → f z = g z) :
    ∀ z : ℂ, ‖z‖ = 1 → f z = g z := by
  intro z hz
  obtain ⟨q, hq, hqnd⟩ := F.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hF z
  have hq0 : q.eval z ≠ 0 := fun h => hqnd (Polynomial.dvd_iff_isRoot.mpr h)
  have hlim := boundaryApproach_tendsto z
  have hqn : ∀ᶠ n : ℕ in atTop, q.eval (boundaryApproach z n) ≠ 0 :=
    hlim.eventually (q.continuous.continuousAt.eventually_ne hq0)
  have he' : ∀ᶠ n : ℕ in atTop, f (boundaryApproach z n) = g (boundaryApproach z n) := by
    filter_upwards [hqn] with n hn
    apply he _ (boundaryApproach_norm z hz n)
    rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (boundaryApproach_ne z hz n))) hn
  exact tendsto_nhds_unique ((hf.tendsto z).comp hlim)
    (((hg.tendsto z).comp hlim).congr' (by
      filter_upwards [he'] with n hn using hn.symm))

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
