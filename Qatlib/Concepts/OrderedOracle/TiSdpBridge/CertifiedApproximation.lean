/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.CertifiedApproximationDefs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open Matrix Polynomial Qatlib SignalProcessing

open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The local Chebyshev polynomial `cheb` equals `chebT`. -/
theorem cheb_eq_frozen (n : ℕ) : cheb n = Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebT n :=
    rfl

/-- The Chebyshev polynomials satisfy the standard three-term recursion. -/
theorem cheb_recursion (n : ℕ) :
    cheb (n + 2) = 2 * Polynomial.X * cheb (n + 1) - cheb n := by
  have h := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  simp only [cheb]
  have e1 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := Nat.cast_add n 2
  have e2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := Nat.cast_add n 1
  rw [e1, e2, h]

/-- Evaluating the degree-`n` Chebyshev polynomial at a cosine gives the cosine of the
multiplied angle. -/
theorem cheb_triangle (n : ℕ) (θ : ℝ) :
    (cheb n).eval (Real.cos θ) = Real.cos ((n : ℝ) * θ) := by
  have h := Polynomial.Chebyshev.T_real_cos θ (n : ℤ)
  simp only [cheb]
  rw [h]
  congr 1

/-- Chebyshev node evaluation has the stated cosine formula, and each valid node lies strictly
between negative one and one. -/
theorem cheb_node_value {N : ℕ} (hN : 0 < N) {j n : ℕ} (hj : j < N) :
    (cheb n).eval (chebNodeN N j) =
        Real.cos ((n : ℝ) * (2 * j + 1) * Real.pi / (2 * N)) ∧
      -1 < chebNodeN N j ∧ chebNodeN N j < 1 := by
  have htri := cheb_triangle n ((2 * j + 1) * Real.pi / (2 * N))
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : (0 : ℝ) < 2 * N := by positivity
  have hne : (2 : ℝ) * N ≠ 0 := ne_of_gt hpos
  have htheta0 : 0 < (2 * j + 1) * Real.pi / (2 * N) := by
    exact div_pos (mul_pos (by positivity) hpi) hpos
  have htheta1 : (2 * j + 1) * Real.pi / (2 * N) < Real.pi := by
    rw [div_lt_iff₀ hpos]
    have h1 : (2 * j + 1 : ℝ) < 2 * N := by
      exact_mod_cast (show 2 * j + 1 < 2 * N by omega)
    simpa [mul_comm] using! mul_lt_mul_of_pos_right h1 hpi
  refine ⟨?_, ?_, ?_⟩
  · simp only [chebNodeN]
    rw [htri]
    congr 1
    ring
  · simp only [chebNodeN]
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (x := (2 * j + 1) * Real.pi / (2 * N))
      (y := Real.pi) (by linarith [htheta0.le]) (by norm_num) htheta1
    rw [Real.cos_pi] at hcos
    exact hcos
  · simp only [chebNodeN]
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0)
      (y := (2 * j + 1) * Real.pi / (2 * N)) (by norm_num) htheta1.le htheta0
    rw [Real.cos_zero] at hcos
    exact hcos

/-- Casting integer `negOnePow` to the reals agrees with the corresponding natural power of
negative one. -/
private theorem negOnePow_natReal (n : ℕ) :
    (((n : ℤ).negOnePow : ℤ) : ℝ) = (-1 : ℝ) ^ n := by
  have h : ((n : ℤ).negOnePow : ℤ) = (-1 : ℤ) ^ n := Int.coe_negOnePow_natCast n
  rw [h]
  push_cast
  ring

/-- Every Chebyshev polynomial evaluates to one at the right endpoint. -/
theorem cheb_endpoint_right (n : ℕ) : (cheb n).eval 1 = 1 := by
  have h := Polynomial.Chebyshev.T_eval_one ℝ (n : ℤ)
  simp only [cheb]
  rw [h]

/-- At negative one, the degree-`n` Chebyshev polynomial evaluates to negative one to the power
`n`. -/
theorem cheb_endpoint_left (n : ℕ) : (cheb n).eval (-1) = (-1 : ℝ) ^ n := by
  have h := cheb_triangle n Real.pi
  calc
    (cheb n).eval (-1) = (cheb n).eval (Real.cos Real.pi) := by rw [Real.cos_pi]
    _ = Real.cos ((n : ℝ) * Real.pi) := h
    _ = (-1 : ℝ) ^ n := Real.cos_nat_mul_pi n

/-- A Chebyshev polynomial has the parity of its degree. -/
theorem cheb_parity (n : ℕ) (x : ℝ) :
    (cheb n).eval (-x) = (-1 : ℝ) ^ n * (cheb n).eval x := by
  have h := Polynomial.Chebyshev.T_eval_neg ℝ (n : ℤ) x
  simp only [cheb]
  rw [h, negOnePow_natReal]

/-- The natural degree of the degree-`n` Chebyshev polynomial is `n`. -/
theorem cheb_degree (n : ℕ) : (cheb n).natDegree = n := by
  have h := Polynomial.Chebyshev.natDegree_T ℝ (n : ℤ)
  simp only [cheb]
  rw [h]
  have h1 : ((n : ℤ).natAbs : ℕ) = n := by
    rw [Int.natAbs_eq_iff]
    exact Or.inl rfl
  exact h1

/-- Distinct valid Chebyshev node indices give distinct nodes. -/
theorem chebNodeN_injective {N : ℕ} (hN : 0 < N) {j k : ℕ} (hj : j < N) (hk : k < N)
    (hne : j ≠ k) : chebNodeN N j ≠ chebNodeN N k := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : (0 : ℝ) < 2 * N := by positivity
  have htheta (m : ℕ) (hm : m < N) :
      0 < (2 * m + 1) * Real.pi / (2 * N) ∧
        (2 * m + 1) * Real.pi / (2 * N) ≤ Real.pi := by
    constructor
    · exact div_pos (mul_pos (by positivity) hpi) hpos
    · rw [div_le_iff₀ hpos]
      have h1 : (2 * m + 1 : ℝ) ≤ 2 * N := by
        have : 2 * m + 1 ≤ 2 * N := by omega
        exact_mod_cast this
      simpa [mul_comm] using! mul_le_mul_of_nonneg_right h1 hpi.le
  by_cases hjk : j < k
  · have hlt : (2 * j + 1) * Real.pi / (2 * N) < (2 * k + 1) * Real.pi / (2 * N) := by
      rw [div_lt_iff₀ hpos]
      have h1 : (2 * j + 1 : ℝ) < 2 * k + 1 := by
        have : 2 * j + 1 < 2 * k + 1 := by omega
        exact_mod_cast this
      have hB : ((2 * k + 1) * Real.pi / (2 * N)) * (2 * N) = (2 * k + 1) * Real.pi := by
        rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      rw [hB]
      simpa [mul_comm] using! mul_lt_mul_of_pos_right h1 hpi
    have hcos : Real.cos ((2 * k + 1) * Real.pi / (2 * N)) <
        Real.cos ((2 * j + 1) * Real.pi / (2 * N)) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [(htheta j hj).1.le]) (htheta k hk).2 hlt
    intro hcon
    simp only [chebNodeN] at hcon
    exact absurd hcon.symm (ne_of_lt hcos)
  · have hkj : k < j := by omega
    have hlt : (2 * k + 1) * Real.pi / (2 * N) < (2 * j + 1) * Real.pi / (2 * N) := by
      rw [div_lt_iff₀ hpos]
      have h1 : (2 * k + 1 : ℝ) < 2 * j + 1 := by
        have : 2 * k + 1 < 2 * j + 1 := by omega
        exact_mod_cast this
      have hB : ((2 * j + 1) * Real.pi / (2 * N)) * (2 * N) = (2 * j + 1) * Real.pi := by
        rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      rw [hB]
      simpa [mul_comm] using! mul_lt_mul_of_pos_right h1 hpi
    have hcos : Real.cos ((2 * j + 1) * Real.pi / (2 * N)) <
        Real.cos ((2 * k + 1) * Real.pi / (2 * N)) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [(htheta k hk).1.le]) (htheta j hj).2 hlt
    intro hcon
    simp only [chebNodeN] at hcon
    exact absurd hcon (ne_of_lt hcos)

/-- The Chebyshev grid with one valid index removed has at most one fewer element. -/
theorem chebGridExcept_card {N : ℕ} {j : ℕ} (hj : j < N) :
    (chebGridExcept N j).card ≤ N - 1 := by
  have hmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
  have heq : chebGridExcept N j = (Finset.range N).erase j := by
    ext k
    simp [chebGridExcept, Finset.mem_erase, and_comm]
  rw [heq, Finset.card_erase_of_mem hmem, Finset.card_range]

/-- The Chebyshev Lagrange denominator is nonzero at a valid node index. -/
theorem chebLagrangeDen_ne_zero {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : j < N) :
    chebLagrangeDen N j ≠ 0 := by
  rw [chebLagrangeDen, Finset.prod_ne_zero_iff]
  intro k hk
  obtain ⟨hkN, hkj⟩ := Finset.mem_filter.mp hk
  have hk' : k < N := Finset.mem_range.mp hkN
  have hne : chebNodeN N j ≠ chebNodeN N k := chebNodeN_injective hN hj hk' (Ne.symm hkj)
  intro hzero
  have hcon : chebNodeN N j = chebNodeN N k := by linarith
  exact hne hcon

/-- The Chebyshev Lagrange numerator evaluates to its denominator at its own node and to zero at
other valid nodes. -/
theorem chebLagrangeNum_eval_node {N : ℕ} {j m : ℕ} (hm : m < N) :
    (chebLagrangeNum N j).eval (chebNodeN N m) =
      if j = m then chebLagrangeDen N j else 0 := by
  rw [chebLagrangeNum, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  by_cases hjm : j = m
  · simp only [ite_eq_left hjm]
    simp only [hjm.symm, chebLagrangeDen]
  · simp only [ite_eq_right hjm]
    have hmem : m ∈ chebGridExcept N j := by
      simp [chebGridExcept, hm, Ne.symm hjm]
    refine Finset.prod_eq_zero hmem ?_
    simp

/-- Polynomial evaluation commutes with a finite sum. -/
private theorem polynomial_eval_sum {ι : Type} [DecidableEq ι] (s : Finset ι)
    (g : ι → Polynomial ℝ) (x : ℝ) :
    (Finset.sum s g).eval x = Finset.sum s (fun j => (g j).eval x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Polynomial.eval_add, Finset.sum_insert ha]
    rw [ih]

/-- The Chebyshev interpolant agrees with the function at every valid interpolation node. -/
theorem chebInterpolantPoly_eval_node {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) {m : ℕ} (hm : m < N) :
    (chebInterpolantPoly N f).eval (chebNodeN N m) = f (chebNodeN N m) := by
  have hterm (j : ℕ) (hj : j < N) :
      (Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j).eval
          (chebNodeN N m) =
        if j = m then f (chebNodeN N j) else 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    rw [chebLagrangeNum_eval_node hm]
    split_ifs with hjm
    · rw [hjm]
      have hden := chebLagrangeDen_ne_zero hN (j := m) hm
      rw [div_mul_cancel₀ _ hden]
    · simp
  rw [chebInterpolantPoly]
  have heval : (Finset.sum (Finset.range N)
        (fun j => Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j)).eval
          (chebNodeN N m)
      = Finset.sum (Finset.range N)
        (fun j => (Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j).eval
          (chebNodeN N m)) :=
    polynomial_eval_sum (Finset.range N) _ (chebNodeN N m)
  rw [heval]
  rw [Finset.sum_eq_single m (by
        intro b hb hbm
        rw [hterm b (Finset.mem_range.mp hb)]
        simp only [ite_eq_right hbm]) (by
        intro h
        exact absurd (Finset.mem_range.mpr hm) h)]
  rw [hterm m hm]
  simp

/-- Each Chebyshev interpolation summand has degree at most one less than the node count. -/
private theorem chebInterpolantTerm_degree {N : ℕ} (f : ℝ → ℝ) {j : ℕ} (hj : j < N) :
    (Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j).natDegree
      ≤ N - 1 := by
  have hnum : (chebLagrangeNum N j).natDegree
      ≤ ∑ k ∈ chebGridExcept N j,
          (Polynomial.X - Polynomial.C (chebNodeN N k)).natDegree := by
    rw [chebLagrangeNum]
    exact Polynomial.natDegree_prod_le _ _
  calc
    (Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j).natDegree
        ≤ (Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j)).natDegree
            + (chebLagrangeNum N j).natDegree := Polynomial.natDegree_mul_le
    _ = (chebLagrangeNum N j).natDegree := by simp
    _ ≤ ∑ k ∈ chebGridExcept N j,
          (Polynomial.X - Polynomial.C (chebNodeN N k)).natDegree := hnum
    _ = (chebGridExcept N j).card := by simp
    _ ≤ N - 1 := chebGridExcept_card hj

/-- The Chebyshev interpolant has natural degree at most one less than the node count. -/
theorem chebInterpolantPoly_degree {N : ℕ} (f : ℝ → ℝ) :
    (chebInterpolantPoly N f).natDegree ≤ N - 1 := by
  calc
    (chebInterpolantPoly N f).natDegree
        ≤ Finset.fold max 0
            (natDegree ∘ fun j =>
              Polynomial.C (f (chebNodeN N j) / chebLagrangeDen N j) * chebLagrangeNum N j)
            (Finset.range N) := Polynomial.natDegree_sum_le _ _
    _ ≤ N - 1 := by
      rw [Finset.fold_max_le]
      constructor
      · omega
      · intro x hx
        exact chebInterpolantTerm_degree f (Finset.mem_range.mp hx)

/-- The Chebyshev parameter record has the stated node count and interpolation degree, differing
by one. -/
theorem chebParams_transport {N : ℕ} (hN : 0 < N) :
    (chebParams N hN).nodes = N ∧ (chebParams N hN).interpDegree = N - 1 ∧
      (chebParams N hN).interpDegree + 1 = (chebParams N hN).nodes := by
  refine ⟨rfl, rfl, (chebParams N hN).degree_eq⟩

/-- A polynomial approximation bound on the Hermitian spectrum transfers to the same matrix
functional-calculus error bound. -/
theorem hermitianFunction_polynomial_error_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) (p : Polynomial ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hpoint : ∀ i : Fin (Fintype.card I),
      ‖f (orderedHermitianValues hA i) - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ)‖ ≤ ε) :
    ‖hermitianFunction A hA f - aeval A (p.map Complex.ofRealHom)‖ ≤ ε := by
  have hpoly : hermitianFunction A hA (fun x => ((p.eval x : ℝ) : ℂ))
      = aeval A (p.map Complex.ofRealHom) :=
    hermitian_spectral_polynomial_evaluation I A hA p
  rw [← hpoly]
  have hsub : hermitianFunction A hA f - hermitianFunction A hA (fun x => ((p.eval x : ℝ) : ℂ))
      = Qatlib.Concepts.WalkSearch.Spectral.spectralDiagonal (orderedHermitianBasis hA)
          (fun i => f (orderedHermitianValues hA i)
            - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ)) := by
    unfold hermitianFunction Qatlib.Concepts.WalkSearch.Spectral.spectralDiagonal
    rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub]
  have hdiag : ‖Matrix.diagonal
      (fun i => f (orderedHermitianValues hA i)
        - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ))‖ ≤ ε := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hε).2 hpoint
  have hb : ‖Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA)‖ ≤ 1 :=
    Qatlib.Concepts.WalkSearch.Spectral.basisColumns_norm_le _
  have hb' : ‖(Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA))ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hb
  simp only [Qatlib.Concepts.WalkSearch.Spectral.spectralDiagonal]
  calc
    ‖Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA) *
        Matrix.diagonal
          (fun i => f (orderedHermitianValues hA i)
            - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ)) *
        (Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA))ᴴ‖
        ≤ ‖Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA) *
            Matrix.diagonal
              (fun i => f (orderedHermitianValues hA i)
                - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ))‖ *
            ‖(Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA))ᴴ‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA)‖ *
            ‖Matrix.diagonal
              (fun i => f (orderedHermitianValues hA i)
                - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ))‖) *
            ‖(Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA))ᴴ‖ := by
      have h1 := Matrix.l2_opNorm_mul
        (Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA))
        (Matrix.diagonal
          (fun i => f (orderedHermitianValues hA i)
            - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ)))
      exact mul_le_mul h1 (le_refl _) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (1 * ε) * 1 := by
      have h2 : ‖Qatlib.Concepts.WalkSearch.Spectral.basisColumns (orderedHermitianBasis hA)‖ *
          ‖Matrix.diagonal
            (fun i => f (orderedHermitianValues hA i)
              - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ))‖ ≤ 1 * ε :=
        mul_le_mul hb hdiag (norm_nonneg _) (by norm_num)
      exact mul_le_mul h2 hb' (norm_nonneg _) (by positivity)
    _ = ε := by ring

/-- A scalar error bound at all singular values transfers to the same odd singular-transform
error bound. -/
theorem oddSingularTransform_scalar_error_le {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq I] (A : Matrix O I ℂ) (f g : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hpoint : ∀ i : Fin (Fintype.card I),
      ‖f (matrixSingularValues A i) - g (matrixSingularValues A i)‖ ≤ ε) :
    ‖oddSingularTransform A f - oddSingularTransform A g‖ ≤ ε :=
  oddSingularTransform_error_le A f g hε hpoint

/-- The QSP response polynomial has parity determined by the phase-list length. -/
theorem response_parity_matches_cheb (base : ℂ) (zs : List ℂ) (x : ℂ) :
    (responseP base zs).eval (-x) = (-1 : ℂ) ^ zs.length * (responseP base zs).eval x :=
  (response_parity base zs x).1

/-- The response polynomial degree is at most the phase-list length. -/
theorem response_degree_le_query (base : ℂ) (zs : List ℂ) :
    (responseP base zs).natDegree ≤ zs.length := (response_degree base zs).1

/-- An odd QSVT phase sequence gives the stated singular-transform block encoding with one query
per phase and one additional gate. -/
theorem qsvt_access_and_error_transport {H I O : Type} [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O] {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I),
      ‖(responseP base zs).eval ((matrixSingularValues A i : ℝ) : ℂ)
        - f (matrixSingularValues A i)‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      Qatlib.Concepts.BlockEncoding.BlockEncoding (oddSingularTransform A f) (evaluate U cs) L R 1 ε ∧
        adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 :=
  qsvt_odd_counted_approximation h hb zs hzs hodd f hε happrox

/-- A length-`N` phase sequence and `N`-node Chebyshev interpolant obey their respective degree
budgets. -/
theorem cheb_qsp_degree_budget {N : ℕ} (f : ℝ → ℝ) (base : ℂ) (zs : List ℂ)
    (hzs : zs.length = N) :
    (chebInterpolantPoly N f).natDegree ≤ N - 1 ∧ (responseP base zs).natDegree ≤ N := by
  refine ⟨chebInterpolantPoly_degree f, ?_⟩
  have hdeg := response_degree_le_query base zs
  omega

/-- Cosines of distinct natural frequencies are orthogonal on the interval from zero to pi. -/
theorem cheb_orthogonality (m n : ℕ) (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..Real.pi, Real.cos ((m : ℝ) * x) * Real.cos ((n : ℝ) * x) = 0 := by
  simpa using!
      (Qatlib.Concepts.OrderedOracle.TiSdpBridge.clause1_with_admissible_sign_gap.2.2.1 m n hmn)

/-- Distinct Chebyshev polynomials are orthogonal after cosine substitution on the interval from
zero to pi. -/
theorem cheb_orthogonality_entry (m n : ℕ) (hmn : m ≠ n) :
    (∫ x in (0 : ℝ)..Real.pi, (cheb m).eval (Real.cos x) * (cheb n).eval (Real.cos x)) = 0 := by
  have h1 : ∀ θ : ℝ, (cheb m).eval (Real.cos θ) = Real.cos ((m : ℝ) * θ) := cheb_triangle m
  have h2 : ∀ θ : ℝ, (cheb n).eval (Real.cos θ) = Real.cos ((n : ℝ) * θ) := cheb_triangle n
  simp only [h1, h2]
  exact cheb_orthogonality m n hmn

/-- Uniform scalar approximation on the unit interval transfers to Hermitian functional calculus
when the spectrum lies there. -/
theorem hermitianFunction_uniform_error_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) (p : Polynomial ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hspec : ∀ i : Fin (Fintype.card I),
      orderedHermitianValues hA i ∈ Set.Icc (-1 : ℝ) 1)
    (hpoint : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      ‖f x - ((p.eval x : ℝ) : ℂ)‖ ≤ ε) :
    ‖hermitianFunction A hA f - aeval A (p.map Complex.ofRealHom)‖ ≤ ε :=
  hermitianFunction_polynomial_error_le A hA f p hε (fun i => hpoint _ (hspec i))

/-- A uniform Chebyshev interpolation error bounds the corresponding Hermitian matrix evaluation
error. -/
theorem cheb_interpolant_hermitian_error_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (fr : ℝ → ℝ) (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hspec : ∀ i : Fin (Fintype.card I),
      orderedHermitianValues hA i ∈ Set.Icc (-1 : ℝ) 1)
    (hpoint : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |fr x - (chebInterpolantPoly N fr).eval x| ≤ ε) :
    ‖hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ)) -
        aeval A ((chebInterpolantPoly N fr).map Complex.ofRealHom)‖ ≤ ε := by
  refine hermitianFunction_uniform_error_le A hA (fun x => ((fr x : ℝ) : ℂ))
    (chebInterpolantPoly N fr) hε hspec ?_
  intro x hx
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hpoint x hx

/-- Uniform approximation by an odd QSP response gives a singular-transform block encoding with
the stated query and gate counts. -/
theorem qsvt_uniform_error_and_budget {H I O : Type} [Fintype H] [Fintype I]
    [Fintype O] [DecidableEq H] [DecidableEq I] [DecidableEq O] {A : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(responseP base zs).eval (x : ℂ) - f x‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      Qatlib.Concepts.BlockEncoding.BlockEncoding (oddSingularTransform A f) (evaluate U cs) L R 1 ε ∧
        adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 :=
  qsvt_odd_counted_approximation h hb zs hzs hodd f hε (fun i => by
    have hs := encoded_singularValues_mem_unitInterval h i.val
    exact happrox _ hs)

/-- The Chebyshev interpolant and QSP response obey the stated degree bounds, together with a
counted approximate QSVT implementation. -/
theorem cheb_node_phase_query_budget {H I O : Type} [Fintype H] [Fintype I]
    [Fintype O] [DecidableEq H] [DecidableEq I] [DecidableEq O] {A : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(responseP base zs).eval (x : ℂ) - f x‖ ≤ ε) :
    (chebInterpolantPoly zs.length (fun x => (f x).re)).natDegree ≤ zs.length - 1 ∧
      (responseP base zs).natDegree ≤ zs.length ∧
        ∃ cs : List (AdjointStep H),
          Qatlib.Concepts.BlockEncoding.BlockEncoding (oddSingularTransform A f) (evaluate U cs) L R 1 ε ∧
            adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨chebInterpolantPoly_degree _, response_degree_le_query base zs, ?_⟩
  exact qsvt_uniform_error_and_budget h hb zs hzs hodd f hε happrox

/-- The rational Gram matrix is symmetric. -/
theorem ratGramMatrix_sym {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) :
    (ratGramMatrix A).transpose = ratGramMatrix A := by
  unfold ratGramMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Lifting the rational Gram matrix to the complex numbers gives the conjugate-transpose
product of the lifted matrix. -/
theorem ratGramMatrix_lift {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) :
    ratMatrixLift (ratGramMatrix A) = (ratMatrixLift A)ᴴ * (ratMatrixLift A) := by
  unfold ratGramMatrix ratMatrixLift
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
  push_cast
  simp only [Matrix.transpose_apply, ← Complex.ofReal_ratCast, Complex.star_def,
    Complex.conj_ofReal]

/-- The quadratic form of a rational Gram matrix is nonnegative. -/
theorem ratGramMatrix_quadratic_nonneg {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ)
    (x : Fin I → ℚ) :
    0 ≤ ∑ i, ∑ j, x i * (ratGramMatrix A) i j * x j := by
  have e1 : (∑ i, ∑ j, x i * (ratGramMatrix A) i j * x j)
      = ∑ i, ∑ j, ∑ k, (x i * (A k i * A k j)) * x j := by
    simp only [ratGramMatrix, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum Finset.univ _ _, Finset.sum_mul Finset.univ _ _]
  have e2 : (∑ i, ∑ j, ∑ k, (x i * (A k i * A k j)) * x j)
      = ∑ i, ∑ k, ∑ j, (x i * (A k i * A k j)) * x j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j k => (x i * (A k i * A k j)) * x j)
  have e3 : (∑ i, ∑ k, ∑ j, (x i * (A k i * A k j)) * x j)
      = ∑ k, ∑ i, ∑ j, (x i * (A k i * A k j)) * x j :=
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i k => ∑ j, (x i * (A k i * A k j)) * x j)
  have e4 : (∑ k, ∑ i, ∑ j, (x i * (A k i * A k j)) * x j)
      = ∑ k, (∑ i, x i * A k i) ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    calc
      (∑ i, ∑ j, (x i * (A k i * A k j)) * x j)
          = ∑ i, (x i * A k i) * (∑ j, A k j * x j) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum Finset.univ _ _]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
      _ = (∑ i, x i * A k i) * (∑ j, A k j * x j) := by
            rw [Finset.sum_mul Finset.univ _ _]
      _ = (∑ i, x i * A k i) ^ 2 := by
            have h2 : (∑ j, A k j * x j) = ∑ i, x i * A k i := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              ring
            rw [h2]
            ring
  rw [e1, e2, e3, e4]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The complex lift of a symmetric rational matrix is Hermitian. -/
theorem ratMatrixLift_isHermitian {D : ℕ} {A : Matrix (Fin D) (Fin D) ℚ} (hA : A.transpose = A) :
    (ratMatrixLift A).IsHermitian := by
  have hA' : ∀ i j, A j i = A i j := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℚ => M j i) hA
    have h2 : A i j = A j i := by simpa [Matrix.transpose_apply] using! h
    exact h2.symm
  ext i j
  simp only [Matrix.conjTranspose_apply, ratMatrixLift, Matrix.map_apply]
  rw [hA' i j]
  exact Complex.conj_ofReal _

noncomputable def ratMatrixReal {I : Type} [Fintype I] (A : Matrix I I ℚ) : Matrix I I ℝ :=
  A.map fun q => (q : ℝ)

noncomputable def ratRayleigh {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (v : EuclideanSpace ℝ I) : ℝ :=
  (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2

/-- The real lift of a symmetric rational matrix is Hermitian. -/
theorem ratMatrixReal_isHermitian {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) : (ratMatrixReal A).IsHermitian := by
  have hA' : ∀ i j, A j i = A i j := by
    intro i j
    have h := congrArg (fun M : Matrix I I ℚ => M j i) hA
    have h2 : A i j = A j i := by simpa [Matrix.transpose_apply] using! h
    exact h2.symm
  ext i j
  simp only [Matrix.conjTranspose_apply, ratMatrixReal, Matrix.map_apply, star_trivial]
  rw [hA' i j]

/-- The Euclidean linear map of a symmetric rational matrix's real lift is symmetric. -/
theorem ratMatrixReal_toEuclideanLin_isSymmetric {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) :
    (ratMatrixReal A).toEuclideanLin.IsSymmetric :=
  (Matrix.isSymmetric_toEuclideanLin_iff).mpr (ratMatrixReal_isHermitian hA)

noncomputable def ratSpecValues {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (hA : A.transpose = A) : Fin (Fintype.card I) → ℝ :=
  (ratMatrixReal_toEuclideanLin_isSymmetric hA).eigenvalues finrank_euclideanSpace

noncomputable def ratSpecBasis {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (hA : A.transpose = A) :
    OrthonormalBasis (Fin (Fintype.card I)) ℝ (EuclideanSpace ℝ I) :=
  (ratMatrixReal_toEuclideanLin_isSymmetric hA).eigenvectorBasis finrank_euclideanSpace

/-- The real lifted matrix acts diagonally in its spectral basis with entries `ratSpecValues`. -/
theorem ratSpec_eigenvector {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I)
    (j : Fin (Fintype.card I)) :
    ((ratSpecBasis A hA).repr ((ratMatrixReal A).toEuclideanLin v)).ofLp j
      = ratSpecValues A hA j * ((ratSpecBasis A hA).repr v).ofLp j := by
  have hj := (ratMatrixReal_toEuclideanLin_isSymmetric hA).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace v j
  exact hj

/-- The Rayleigh numerator equals the spectral sum of eigenvalues times squared basis
coordinates. -/
theorem ratSpec_rayleigh {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) :
    inner ℝ v ((ratMatrixReal A).toEuclideanLin v)
      = ∑ j, ratSpecValues A hA j * (ratSpecBasis A hA).repr v j ^ 2 := by
  rw [← (ratSpecBasis A hA).repr.inner_map_map v ((ratMatrixReal A).toEuclideanLin v)]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  rw [ratSpec_eigenvector hA v j]
  ring

/-- The squared norm equals the sum of squared coordinates in the rational matrix's real
spectral basis. -/
theorem ratSpec_norm_sq {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) :
    ‖v‖ ^ 2 = ∑ j, (ratSpecBasis A hA).repr v j ^ 2 := by
  rw [← (ratSpecBasis A hA).repr.norm_map v, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- A common denominator factors out of a finite weighted sum. -/
private theorem sum_mul_div {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ι → ℝ) (c : ℝ) :
    ∑ k, a k * (b k / c) = (∑ k, a k * b k) / c := by
  have h1 : ∑ k, a k * (b k / c) = ∑ k, (a k * b k) / c := by
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, ← Finset.sum_div]

noncomputable def ratSpecWeight {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (hA : A.transpose = A) (v : EuclideanSpace ℝ I)
    (k : Fin (Fintype.card I)) : ℝ :=
  (ratSpecBasis A hA).repr v k ^ 2 / ‖v‖ ^ 2

/-- Every rational spectral weight is nonnegative. -/
theorem ratSpecWeight_nonneg {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I)
    (k : Fin (Fintype.card I)) : 0 ≤ ratSpecWeight A hA v k := by
  unfold ratSpecWeight
  positivity

/-- The spectral weights of a nonzero vector sum to one. -/
theorem ratSpecWeight_sum_one {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) (hv : v ≠ 0) :
    ∑ k, ratSpecWeight A hA v k = 1 := by
  have hsq := ratSpec_norm_sq hA v
  unfold ratSpecWeight
  rw [← Finset.sum_div]
  rw [hsq]
  exact div_self (by
    rw [← hsq]
    positivity)

/-- The spectral-weighted eigenvalue sum equals the Rayleigh quotient. -/
theorem ratSpec_weighted_quotient {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) :
    ∑ k, ratSpecValues A hA k * ratSpecWeight A hA v k
      = (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2 := by
  rw [ratSpec_rayleigh hA v]
  unfold ratSpecWeight
  rw [sum_mul_div]

/-- The spectral-weighted squared deviation from the Rayleigh quotient equals the squared
relative residual norm. -/
theorem ratSpec_weighted_residual {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) (hv : v ≠ 0) :
    ∑ k, (ratSpecValues A hA k -
        (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) ^ 2 *
        ratSpecWeight A hA v k
      = (‖(ratMatrixReal A).toEuclideanLin v -
          ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖) ^ 2 := by
  set ρ : ℝ := (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2 with hρ
  have hres : ‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ ^ 2
      = ∑ j, (ratSpecValues A hA j - ρ) ^ 2 * (ratSpecBasis A hA).repr v j ^ 2 := by
    rw [← (ratSpecBasis A hA).repr.norm_map ((ratMatrixReal A).toEuclideanLin v - ρ • v),
      EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Finset.sum_congr rfl
    intro j _
    have h1 := ratSpec_eigenvector hA v j
    have h2 : (ratSpecBasis A hA).repr (ρ • v) j = ρ * (ratSpecBasis A hA).repr v j := by
      simp
    have hsub : (ratSpecBasis A hA).repr
          ((ratMatrixReal A).toEuclideanLin v - ρ • v)
        = (ratSpecBasis A hA).repr ((ratMatrixReal A).toEuclideanLin v)
          - (ratSpecBasis A hA).repr (ρ • v) := map_sub _ _ _
    have hone : ((ratSpecBasis A hA).repr ((ratMatrixReal A).toEuclideanLin v)
          - (ratSpecBasis A hA).repr (ρ • v)).ofLp j
        = ((ratSpecBasis A hA).repr ((ratMatrixReal A).toEuclideanLin v)).ofLp j
          - ((ratSpecBasis A hA).repr (ρ • v)).ofLp j := rfl
    rw [hsub, hone, h1, h2]
    ring
  have hnorm : ‖v‖ ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))
  unfold ratSpecWeight
  rw [sum_mul_div, ← hres]
  field_simp

/-- Some spectral value lies within the relative residual norm of the Rayleigh quotient of a
nonzero vector. -/
theorem ratSpec_value_enclosure {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) (hv : v ≠ 0) :
    ∃ j : Fin (Fintype.card I),
      |ratSpecValues A hA j -
          (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2|
        ≤ ‖(ratMatrixReal A).toEuclideanLin v -
            ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ := by
  set ρ : ℝ := (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2 with hρ
  set s : Finset ℝ := Finset.univ.image (fun j => |ratSpecValues A hA j - ρ|) with hs
  have hsne : s.Nonempty := by
    refine ⟨|ratSpecValues A hA ⟨0, Fintype.card_pos⟩ - ρ|, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, Fintype.card_pos⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj, hmj⟩ := Finset.mem_image.mp (Finset.min'_mem s hsne)
  have hle : ∀ k, s.min' hsne ≤ |ratSpecValues A hA k - ρ| := by
    intro k
    exact Finset.min'_le s (|ratSpecValues A hA k - ρ|)
      (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have hmn : 0 ≤ s.min' hsne := by
    rw [← hmj]
    exact abs_nonneg _
  have hkey : (s.min' hsne) ^ 2
      ≤ ∑ k, (ratSpecValues A hA k - ρ) ^ 2 * ratSpecWeight A hA v k := by
    calc
      (s.min' hsne) ^ 2 = ∑ k, (s.min' hsne) ^ 2 * ratSpecWeight A hA v k := by
        rw [← Finset.mul_sum, ratSpecWeight_sum_one hA v hv]
        ring
      _ ≤ ∑ k, (ratSpecValues A hA k - ρ) ^ 2 * ratSpecWeight A hA v k := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hsq : (ratSpecValues A hA k - ρ) ^ 2 ≥ (s.min' hsne) ^ 2 := by
          have h1 := hle k
          have habs : |ratSpecValues A hA k - ρ| ^ 2 = (ratSpecValues A hA k - ρ) ^ 2 := sq_abs _
          nlinarith [abs_nonneg (ratSpecValues A hA k - ρ)]
        have hw : 0 ≤ ratSpecWeight A hA v k := ratSpecWeight_nonneg hA v k
        nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hw]
  have hres := ratSpec_weighted_residual hA v hv
  refine ⟨j, ?_⟩
  rw [hmj]
  rw [hρ]
  have hsq : (s.min' hsne) ^ 2
      ≤ (‖(ratMatrixReal A).toEuclideanLin v -
          ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖) ^ 2 := by
    have hkey' : (s.min' hsne) ^ 2
        ≤ ∑ k, (ratSpecValues A hA k -
            ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2)) ^ 2 *
          ratSpecWeight A hA v k := by
      rw [hρ] at hkey
      exact hkey
    rw [← hres]
    exact hkey'
  have hmm : 0 ≤ ‖(ratMatrixReal A).toEuclideanLin v -
      ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ :=
    div_nonneg (norm_nonneg _) (norm_nonneg _)
  exact (sq_le_sq₀ hmn hmm).mp hsq

/-- Under the stated spectral separation, every value within the residual enclosure equals the
designated spectral value. -/
theorem ratSpec_value_uniqueness {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I)
    {g : ℝ} {j : Fin (Fintype.card I)}
    (hgap : ∀ k, ratSpecValues A hA k ≠ ratSpecValues A hA j →
      g ≤ |ratSpecValues A hA k -
        (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2|)
    (hgr : ‖(ratMatrixReal A).toEuclideanLin v -
        ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ < g) :
    ∀ k : Fin (Fintype.card I),
      |ratSpecValues A hA k -
          (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2| ≤
        ‖(ratMatrixReal A).toEuclideanLin v -
            ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ →
      ratSpecValues A hA k = ratSpecValues A hA j := by
  intro k hk
  by_contra hne
  have h1 := hgap k hne
  linarith

/-- A nonzero vector has a residual spectral enclosure, and the stated gap makes every enclosed
spectral value equal to the designated one. -/
theorem ratSpec_value_enclosure_with_gap {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) (hv : v ≠ 0)
    {g : ℝ} {j : Fin (Fintype.card I)}
    (hgap : ∀ k, ratSpecValues A hA k ≠ ratSpecValues A hA j →
      g ≤ |ratSpecValues A hA k -
        (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2|)
    (hgr : ‖(ratMatrixReal A).toEuclideanLin v -
        ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ < g) :
    ∃ k : Fin (Fintype.card I),
      |ratSpecValues A hA k -
          (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2| ≤
        ‖(ratMatrixReal A).toEuclideanLin v -
            ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ ∧
      ∀ k' : Fin (Fintype.card I),
        |ratSpecValues A hA k' -
            (inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2| ≤
          ‖(ratMatrixReal A).toEuclideanLin v -
              ((inner ℝ v ((ratMatrixReal A).toEuclideanLin v)) / ‖v‖ ^ 2) • v‖ / ‖v‖ →
          ratSpecValues A hA k' = ratSpecValues A hA j := by
  obtain ⟨k, hk⟩ := ratSpec_value_enclosure hA v hv
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  by_contra heq
  have h1 := hgap k' heq
  linarith

noncomputable def certifySpectralValue {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (_hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) (halfWidth : ℝ)
    (inputBits : ℕ) : CertifiedSpectralRun :=
  let ρ := ratRayleigh A v
  let r := ‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ / ‖v‖
  { verdict :=
      if r ≤ halfWidth then CertifiedSpectralVerdict.certified ρ halfWidth
      else CertifiedSpectralVerdict.stopped r
    bitTime := (D + 1) ^ 3 * (inputBits + 1)
    bitSpace := (D + 1) ^ 2 * (inputBits + 1) }

/-- The spectral-value certification returns a certified verdict when the relative residual is
within tolerance. -/
theorem certifySpectralValue_succeeds {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) {δ : ℝ} (_hδ : 0 ≤ δ)
    (inputBits : ℕ)
    (hr : ‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖ ≤ δ) :
    (certifySpectralValue A hA v δ inputBits).verdict = CertifiedSpectralVerdict.certified
      (ratRayleigh A v) δ := by
  simp [certifySpectralValue, hr]

/-- The spectral-value certification returns a stopped verdict when the relative residual
exceeds tolerance. -/
theorem certifySpectralValue_stops {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) {δ : ℝ} (_hδ : 0 ≤ δ)
    (inputBits : ℕ)
    (hr : δ < ‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖) :
    (certifySpectralValue A hA v δ inputBits).verdict = CertifiedSpectralVerdict.stopped
      (‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖) := by
  have hne : ¬ (‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖ ≤ δ) := by
    linarith
  simp [certifySpectralValue, hne]

/-- A successful residual bound certifies the existence of a spectral value within tolerance of
the Rayleigh quotient. -/
theorem certifySpectralValue_sound {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hv : v ≠ 0) [Nonempty (Fin D)]
    (hr : ‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖ ≤ δ) :
    ∃ j : Fin (Fintype.card (Fin D)),
      |ratSpecValues A hA j - ratRayleigh A v| ≤ δ := by
  obtain ⟨j, hj⟩ := ratSpec_value_enclosure hA v hv
  refine ⟨j, ?_⟩
  simpa only [ratRayleigh] using! hj.trans hr

noncomputable def certifySingularValue {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ)
    (v : EuclideanSpace ℝ (Fin I)) (halfWidth : ℝ) (inputBits : ℕ) : CertifiedSpectralRun :=
  let G := ratGramMatrix A
  let ρ := ratRayleigh G v
  let r := ‖(ratMatrixReal G).toEuclideanLin v - ρ • v‖ / ‖v‖
  { verdict :=
      if r ≤ halfWidth then CertifiedSpectralVerdict.certified ρ halfWidth
      else CertifiedSpectralVerdict.stopped r
    bitTime := (I + 1) ^ 3 * (O + 1) * (inputBits + 1)
    bitSpace := (I + 1) * (O + 1) * (inputBits + 1) }

/-- A Gram-matrix residual bound encloses a spectral value of the rational Gram matrix within
the stated tolerance. -/
theorem certifySingularValue_sound {O I : ℕ} (A : Matrix (Fin O) (Fin I) ℚ)
    (v : EuclideanSpace ℝ (Fin I)) {δ : ℝ} (_hδ : 0 ≤ δ) (hv : v ≠ 0)
    [Nonempty (Fin I)]
    (hr : ‖(ratMatrixReal (ratGramMatrix A)).toEuclideanLin v -
        ratRayleigh (ratGramMatrix A) v • v‖ / ‖v‖ ≤ δ) :
    ∃ j : Fin (Fintype.card (Fin I)),
      |ratSpecValues (ratGramMatrix A) (ratGramMatrix_sym A) j -
          ratRayleigh (ratGramMatrix A) v| ≤ δ := by
  obtain ⟨j, hj⟩ :=
    ratSpec_value_enclosure (ratGramMatrix_sym A) v hv
  refine ⟨j, ?_⟩
  simpa only [ratRayleigh] using! hj.trans hr

/-- Every indexed Hermitian spectral value has positive spectral multiplicity. -/
theorem spectralMultiplicity_pos {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (j : Fin (Fintype.card I)) :
    0 < spectralMultiplicity A hA j := by
  rw [spectralMultiplicity]
  refine Finset.card_pos.mpr ⟨j, ?_⟩
  simp

/-- The recorded spectral-run bit time satisfies the stated cubic dimension bound. -/
theorem spectralRun_bitTime_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ) (v : Fin D → ℚ)
    (inputBits : ℕ) :
    (spectralRun A v inputBits).bitTime ≤ (D + 1) ^ 3 * (inputBits + 1) := by
  rfl

/-- The recorded spectral-run bit space satisfies the stated quadratic dimension bound. -/
theorem spectralRun_bitSpace_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ) (v : Fin D → ℚ)
    (inputBits : ℕ) :
    (spectralRun A v inputBits).bitSpace ≤ (D + 1) ^ 2 * (inputBits + 1) := by
  rfl

/-- The polynomial spectral approximation is certified with the stated matrix error and
node-read count. -/
theorem funcEvalCost_certified {N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) (p : Polynomial ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (inputBits : ℕ) (εq : ℚ)
    (hpoint : ∀ i : Fin (Fintype.card I),
      ‖f (orderedHermitianValues hA i) - ((p.eval (orderedHermitianValues hA i) : ℝ) : ℂ)‖ ≤ ε) :
    ‖hermitianFunction A hA f - aeval A (p.map Complex.ofRealHom)‖ ≤ ε ∧
      (funcEvalCost N inputBits εq).nodeReads = N :=
  ⟨hermitianFunction_polynomial_error_le A hA f p hε hpoint, rfl⟩

/-- The coefficient-bit cost is monotone in node count, input bit count, and rational tolerance
bit length. -/
theorem funcEvalCost_coefficientBits_mono {N N' : ℕ} {inputBits inputBits' : ℕ} {ε ε' : ℚ}
    (hN : N ≤ N') (hI : inputBits ≤ inputBits') (hε : ratBitLength ε ≤ ratBitLength ε') :
    (funcEvalCost N inputBits ε).coefficientBits
      ≤ (funcEvalCost N' inputBits' ε').coefficientBits := by
  simp only [funcEvalCost]
  have h1 : (N + 1) * (inputBits + 1) ≤ (N' + 1) * (inputBits' + 1) :=
    Nat.mul_le_mul (Nat.succ_le_succ hN) (Nat.succ_le_succ hI)
  omega

/-- A triangular block with nonzero off-diagonal data is not normal. -/
theorem triBlock_not_normal {T : TriBlock} (hc : T.c ≠ (0, 0)) :
    (T.toMatrix)ᴴ * T.toMatrix ≠ T.toMatrix * (T.toMatrix)ᴴ := by
  intro hcon
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
    M ⟨0, by norm_num⟩ ⟨0, by norm_num⟩) hcon
  have hL : ((T.toMatrix)ᴴ * T.toMatrix) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
      = ((T.a : ℝ) : ℂ) ^ 2 := by
    rw [Matrix.mul_apply]
    simp only [TriBlock.toMatrix, Matrix.conjTranspose_apply]
    simp
    ring
  have hR : (T.toMatrix * (T.toMatrix)ᴴ) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
      = ((T.a : ℝ) : ℂ) ^ 2 + T.c.toComplex * (starRingEnd ℂ) T.c.toComplex := by
    rw [Matrix.mul_apply]
    simp only [TriBlock.toMatrix, Matrix.conjTranspose_apply]
    simp
    ring
  rw [hL, hR] at h00
  have hz : T.c.toComplex * (starRingEnd ℂ) T.c.toComplex = 0 := by
    have h'' : (0 : ℂ) = -(T.c.toComplex * (starRingEnd ℂ) T.c.toComplex) := by
      calc
        0 = (↑↑T.a : ℂ) ^ 2 - ((↑↑T.a : ℂ) ^ 2
            + T.c.toComplex * (starRingEnd ℂ) T.c.toComplex) := by
          symm
          rw [sub_eq_zero]
          exact h00
        _ = -(T.c.toComplex * (starRingEnd ℂ) T.c.toComplex) := by ring
    exact neg_eq_zero.mp h''.symm
  have hzc : T.c.toComplex = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · have h2 := congrArg (starRingEnd ℂ) h
      simpa using! h2
  have hcc : T.c = (0, 0) := by
    ext
    · have hre := congrArg Complex.re hzc
      simp [RatComplex.toComplex] at hre
      linarith
    · have him := congrArg Complex.im hzc
      simp [RatComplex.toComplex] at him
      linarith
  exact hc hcc

noncomputable def triBlockProjA (T : TriBlock) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i.val = 0 then
      (if j.val = 0 then (((T.a - T.b : ℚ) : ℝ) : ℂ) else T.c.toComplex) else 0

noncomputable def triBlockProjB (T : TriBlock) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i.val = 0 then
      (if j.val = 0 then 0 else -T.c.toComplex)
    else (if j.val = 1 then (((T.a - T.b : ℚ) : ℝ) : ℂ) else 0)

/-- The two unnormalized triangular-block projectors sum to the eigenvalue difference times the
identity. -/
theorem triBlock_proj_sum (T : TriBlock) :
    triBlockProjA T + triBlockProjB T = (((T.a - T.b : ℚ) : ℝ) : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triBlockProjA, triBlockProjB, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]

set_option linter.unnecessarySeqFocus false in

/-- The triangular block acts on each unnormalized projector by its corresponding diagonal
scalar. -/
theorem triBlock_proj_action (T : TriBlock) :
    T.toMatrix * triBlockProjA T = (((T.a : ℝ) : ℂ)) • triBlockProjA T ∧
      T.toMatrix * triBlockProjB T = (((T.b : ℝ) : ℂ)) • triBlockProjB T := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [TriBlock.toMatrix, triBlockProjA, triBlockProjB, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]; ring

/-- For values with a common sign and nonnegative weights, summing weighted absolute values
equals the absolute weighted sum. -/
private theorem abs_weighted_sum_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (w : ι → ℝ) (s : Finset ι) (hw : ∀ k, 0 ≤ w k)
    (hsame : ∀ k ∈ s, ∀ l ∈ s, f k * f l ≥ 0) :
    ∑ k ∈ s, |f k| * w k = |∑ k ∈ s, f k * w k| := by
  by_cases hex : ∃ k ∈ s, 0 < f k
  · obtain ⟨k₀, hk₀, hf₀⟩ := hex
    have hle : ∀ k ∈ s, 0 ≤ f k := by
      intro k hk
      have hprod := hsame k hk k₀ hk₀
      by_contra hcon
      have hneg : f k * f k₀ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hcon) hf₀
      linarith
    have h1 : ∑ k ∈ s, |f k| * w k = ∑ k ∈ s, f k * w k := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [abs_of_nonneg (hle k hk)]
    have h2 : 0 ≤ ∑ k ∈ s, f k * w k := by
      refine Finset.sum_nonneg (fun k hk => ?_)
      exact mul_nonneg (hle k hk) (hw k)
    rw [h1, abs_of_nonneg h2]
  · have hle : ∀ k ∈ s, f k ≤ 0 := by
      intro k hk
      by_contra hcon
      exact hex ⟨k, hk, lt_of_not_ge hcon⟩
    have h1 : ∑ k ∈ s, |f k| * w k = -∑ k ∈ s, f k * w k := by
      calc
        (∑ k ∈ s, |f k| * w k) = ∑ k ∈ s, (-(f k)) * w k := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [abs_of_nonpos (hle k hk)]
        _ = ∑ k ∈ s, -(f k * w k) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          ring
        _ = -∑ k ∈ s, f k * w k := by rw [Finset.sum_neg_distrib]
    have h2 : ∑ k ∈ s, f k * w k ≤ 0 := by
      refine Finset.sum_nonpos (fun k hk => ?_)
      exact mul_nonpos_of_nonpos_of_nonneg (hle k hk) (hw k)
    rw [h1, abs_of_nonpos h2]

/-- The spectral-weighted eigenvalue sum equals `ratRayleigh`. -/
theorem ratSpec_weighted_quotient_r {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) :
    ∑ k, ratSpecValues A hA k * ratSpecWeight A hA v k = ratRayleigh A v := by
  exact ratSpec_weighted_quotient hA v

/-- The spectral-weighted squared deviation from `ratRayleigh` equals the squared relative
residual norm. -/
theorem ratSpec_weighted_residual_r {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) (hv : v ≠ 0) :
    ∑ k, (ratSpecValues A hA k - ratRayleigh A v) ^ 2 * ratSpecWeight A hA v k
      = (‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖) ^ 2 := by
  exact ratSpec_weighted_residual hA v hv

/-- Under the gap and opposite-side separation assumptions, the designated eigenvalue error is
bounded by the squared relative residual divided by the gap. -/
theorem ratSpec_value_temple {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (v : EuclideanSpace ℝ I) (hv : v ≠ 0)
    {g : ℝ} {j : Fin (Fintype.card I)} (hg : 0 < g)
    (hgap : ∀ k : Fin (Fintype.card I), k ≠ j →
      g ≤ |ratSpecValues A hA k - ratRayleigh A v|)
    (hsep : ∀ k : Fin (Fintype.card I), k ≠ j →
      (ratSpecValues A hA k - ratRayleigh A v) *
        (ratSpecValues A hA j - ratRayleigh A v) < 0) :
    |ratSpecValues A hA j - ratRayleigh A v| ≤
      (‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖) ^ 2 / g := by
  set spec : Fin (Fintype.card I) → ℝ := ratSpecValues A hA with hspec
  set w : Fin (Fintype.card I) → ℝ := ratSpecWeight A hA v with hw
  set ρ : ℝ := ratRayleigh A v with hρ
  by_cases hj0 : spec j - ρ = 0
  · rw [hj0, abs_zero]
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  · have hw_nonneg : ∀ k, 0 ≤ w k := by
      intro k
      rw [hw]
      exact ratSpecWeight_nonneg hA v k
    have hw_sum : ∑ k, w k = 1 := by
      rw [hw]
      exact ratSpecWeight_sum_one hA v hv

    have hquot : ∑ k, spec k * w k = ρ := by
      rw [hspec, hw, hρ]
      exact ratSpec_weighted_quotient_r hA v
    have hres : ∑ k, (spec k - ρ) ^ 2 * w k =
        (‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ / ‖v‖) ^ 2 := by
      rw [hspec, hw, hρ]
      exact ratSpec_weighted_residual_r hA v hv

    have hE0 : ∑ k, (spec k - ρ) * w k = 0 := by
      have h1 : ∑ k, (spec k - ρ) * w k = (∑ k, spec k * w k) - ρ * (∑ k, w k) := by
        calc
          ∑ k, (spec k - ρ) * w k = ∑ k, (spec k * w k - ρ * w k) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            ring
          _ = (∑ k, spec k * w k) - ∑ k, ρ * w k := by
            rw [← Finset.sum_sub_distrib]
          _ = (∑ k, spec k * w k) - ρ * (∑ k, w k) := by rw [Finset.mul_sum]
      rw [h1, hquot, hw_sum]
      ring

    have hsplit (F : Fin (Fintype.card I) → ℝ) :
        ∑ k, F k = F j + ∑ k ∈ Finset.univ.erase j, F k := by
      have h := Finset.sum_erase_add Finset.univ F (Finset.mem_univ j)
      linarith

    have hsame : ∀ k ∈ Finset.univ.erase j, ∀ l ∈ Finset.univ.erase j,
        (spec k - ρ) * (spec l - ρ) ≥ 0 := by
      intro k hk l hl
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
      have hkt : (spec k - ρ) * (spec j - ρ) < 0 := hsep k hkj
      have hlt : (spec l - ρ) * (spec j - ρ) < 0 := hsep l hlj
      have ht2 : 0 < (spec j - ρ) ^ 2 := sq_pos_of_ne_zero hj0
      have hprod : 0 < ((spec k - ρ) * (spec l - ρ)) * ((spec j - ρ) ^ 2) := by
        have h := mul_pos_of_neg_of_neg hkt hlt
        rw [show ((spec k - ρ) * (spec j - ρ)) * ((spec l - ρ) * (spec j - ρ))
          = ((spec k - ρ) * (spec l - ρ)) * ((spec j - ρ) ^ 2) by ring] at h
        exact h
      have hpos : 0 < (spec k - ρ) * (spec l - ρ) := by
        by_contra hcon
        rcases lt_or_eq_of_le (le_of_not_gt hcon) with hneg | heq
        · have hbad : (spec k - ρ) * (spec l - ρ) * ((spec j - ρ) ^ 2) < 0 :=
            mul_neg_of_neg_of_pos hneg ht2
          linarith
        · rw [heq] at hprod
          exact absurd hprod (by simp)
      linarith

    have habs : ∑ k ∈ Finset.univ.erase j, |spec k - ρ| * w k = |spec j - ρ| * w j := by
      have h1 := abs_weighted_sum_eq (fun k => spec k - ρ) w (Finset.univ.erase j)
        (fun k => hw_nonneg k) hsame
      have h2 : ∑ k ∈ Finset.univ.erase j, (spec k - ρ) * w k = -(spec j - ρ) * w j := by
        have h3 := hsplit (fun k => (spec k - ρ) * w k)
        rw [hE0] at h3
        linarith
      rw [h1, h2, abs_mul, abs_neg, abs_of_nonneg (hw_nonneg j)]

    have hgap_bound : g * (∑ k ∈ Finset.univ.erase j, |spec k - ρ| * w k)
        ≤ ∑ k ∈ Finset.univ.erase j, (spec k - ρ) ^ 2 * w k := by
      have h1 : g * (∑ k ∈ Finset.univ.erase j, |spec k - ρ| * w k)
          = ∑ k ∈ Finset.univ.erase j, g * (|spec k - ρ| * w k) := by
        rw [Finset.mul_sum]
      rw [h1]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hg1 : g ≤ |spec k - ρ| := hgap k hkj
      have hkey : |spec k - ρ| ^ 2 ≥ g * |spec k - ρ| := by
        nlinarith [hg1, abs_nonneg (spec k - ρ)]
      calc
        g * (|spec k - ρ| * w k) = (g * |spec k - ρ|) * w k := by ring
        _ ≤ (|spec k - ρ| ^ 2) * w k :=
          mul_le_mul_of_nonneg_right hkey (hw_nonneg k)
        _ = ((spec k - ρ) ^ 2) * w k := by rw [sq_abs (spec k - ρ)]

    have hweight : g * (∑ k ∈ Finset.univ.erase j, w k)
        ≤ ∑ k ∈ Finset.univ.erase j, |spec k - ρ| * w k := by
      have h1 : g * (∑ k ∈ Finset.univ.erase j, w k)
          = ∑ k ∈ Finset.univ.erase j, g * w k := by
        rw [Finset.mul_sum]
      rw [h1]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hg1 : g ≤ |spec k - ρ| := hgap k hkj
      exact mul_le_mul_of_nonneg_right hg1 (hw_nonneg k)
    have hsum_erase : ∑ k ∈ Finset.univ.erase j, w k = 1 - w j := by
      have h3 := hsplit (fun k => w k)
      rw [hw_sum] at h3
      linarith
    have htwj : |spec j - ρ| * w j ≥ g * (1 - w j) := by
      have h1 := hweight
      rw [hsum_erase] at h1
      have h2 := habs
      linarith
    have hwj2 : w j * (|spec j - ρ| + g) ≥ g := by
      nlinarith [htwj]

    have hR : (‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ / ‖v‖) ^ 2 ≥ g * |spec j - ρ| := by
      have hsplitR := hsplit (fun k => (spec k - ρ) ^ 2 * w k)
      rw [← hres, hsplitR]
      calc
        (spec j - ρ) ^ 2 * w j + ∑ k ∈ Finset.univ.erase j, (spec k - ρ) ^ 2 * w k
            ≥ (spec j - ρ) ^ 2 * w j + g * (∑ k ∈ Finset.univ.erase j, |spec k - ρ| * w k) := by
          linarith
        _ = |spec j - ρ| ^ 2 * w j + g * (|spec j - ρ| * w j) := by
          rw [habs, sq_abs (spec j - ρ)]
        _ = |spec j - ρ| * w j * (|spec j - ρ| + g) := by ring
        _ ≥ |spec j - ρ| * g := by
          have hmul := mul_le_mul_of_nonneg_left hwj2 (abs_nonneg (spec j - ρ))
          calc
            |spec j - ρ| * w j * (|spec j - ρ| + g) = |spec j - ρ| * (w j * (|spec j - ρ| + g)) := by ring
            _ ≥ |spec j - ρ| * g := hmul
        _ = g * |spec j - ρ| := by ring
    rw [le_div_iff₀ hg]
    linarith

/-- The two normalized triangular-block spectral projectors sum to the identity. -/
theorem triBlockSpecProj_sum (T : TriBlock) :
    triBlockSpecProjA T + triBlockSpecProjB T = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triBlockSpecProjA, triBlockSpecProjB, Matrix.add_apply]

/-- The product of the first and second triangular-block spectral projectors is zero. -/
theorem triBlockSpecProj_mul (T : TriBlock) :
    triBlockSpecProjA T * triBlockSpecProjB T = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triBlockSpecProjA, triBlockSpecProjB, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.zero_apply]

/-- Both triangular-block spectral projectors are idempotent. -/
theorem triBlockSpecProj_idem (T : TriBlock) :
    triBlockSpecProjA T * triBlockSpecProjA T = triBlockSpecProjA T ∧
      triBlockSpecProjB T * triBlockSpecProjB T = triBlockSpecProjB T := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [triBlockSpecProjA, triBlockSpecProjB, Matrix.mul_apply, Fin.sum_univ_two]

/-- The triangular block acts on its normalized spectral projectors by the corresponding
eigenvalues. -/
theorem triBlockSpecProj_action (T : TriBlock) :
    T.toMatrix * triBlockSpecProjA T = (((T.a : ℝ) : ℂ)) • triBlockSpecProjA T ∧
      T.toMatrix * triBlockSpecProjB T = (((T.b : ℝ) : ℂ)) • triBlockSpecProjB T := by
  have hab : (((T.a - T.b : ℚ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro h
    have h1 : (T.a - T.b : ℚ) = 0 := by
      have h2 : ((T.a - T.b : ℚ) : ℝ) = 0 := by exact_mod_cast h
      exact_mod_cast h2
    exact sub_ne_zero.mpr T.ab_ne h1
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [TriBlock.toMatrix, triBlockSpecProjA, triBlockSpecProjB, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] at hab ⊢;
    field_simp [hab]; ring

/-- Both triangular-block spectral projector norms are bounded by `triBlockCondition`. -/
theorem triBlockSpecProj_norm_le (T : TriBlock) :
    ‖triBlockSpecProjA T‖ ≤ triBlockCondition T ∧
      ‖triBlockSpecProjB T‖ ≤ triBlockCondition T := by
  refine ⟨(spectral_operator_norm_le_frobenius _).trans
      (le_add_of_nonneg_right (spectralFrobenius_nonneg _)),
    (spectral_operator_norm_le_frobenius _).trans
      (le_add_of_nonneg_left (spectralFrobenius_nonneg _))⟩

/-- The norm of a weighted sum of the triangular-block spectral projectors is bounded by total
coefficient norm times `triBlockCondition`. -/
theorem triBlock_spectral_error_bound (T : TriBlock) (e_a e_b : ℂ) :
    ‖e_a • triBlockSpecProjA T + e_b • triBlockSpecProjB T‖
      ≤ (‖e_a‖ + ‖e_b‖) * triBlockCondition T := by
  have hA : ‖triBlockSpecProjA T‖ ≤ triBlockCondition T :=
    (triBlockSpecProj_norm_le T).1
  have hB : ‖triBlockSpecProjB T‖ ≤ triBlockCondition T :=
    (triBlockSpecProj_norm_le T).2
  calc
    ‖e_a • triBlockSpecProjA T + e_b • triBlockSpecProjB T‖
        ≤ ‖e_a • triBlockSpecProjA T‖ + ‖e_b • triBlockSpecProjB T‖ := norm_add_le _ _
    _ = ‖e_a‖ * ‖triBlockSpecProjA T‖ + ‖e_b‖ * ‖triBlockSpecProjB T‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ ‖e_a‖ * triBlockCondition T + ‖e_b‖ * triBlockCondition T := by
      exact add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
    _ = (‖e_a‖ + ‖e_b‖) * triBlockCondition T := by ring

noncomputable def triBlockShift (T : TriBlock) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  z • 1 - T.toMatrix

noncomputable def triBlockResolvent (T : TriBlock) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i.val = 0 then
      (if j.val = 0 then 1 / (z - ((T.a : ℝ) : ℂ))
       else T.c.toComplex / ((z - ((T.a : ℝ) : ℂ)) * (z - ((T.b : ℝ) : ℂ))))
    else (if j.val = 1 then 1 / (z - ((T.b : ℝ) : ℂ)) else 0)

/-- The triangular-block resolvent is a right inverse of the shifted block away from both
diagonal values. -/
theorem triBlockResolvent_inverse (T : TriBlock) {z : ℂ}
    (hza : z - ((T.a : ℝ) : ℂ) ≠ 0) (hzb : z - ((T.b : ℝ) : ℂ) ≠ 0) :
    triBlockShift T z * triBlockResolvent T z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triBlockShift, triBlockResolvent, TriBlock.toMatrix, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] at hza hzb ⊢ <;>
    field_simp [hza, hzb]; ring

/-- The triangular-block resolvent is a left inverse of the shifted block away from both
diagonal values. -/
theorem triBlockResolvent_inverse' (T : TriBlock) {z : ℂ}
    (hza : z - ((T.a : ℝ) : ℂ) ≠ 0) (hzb : z - ((T.b : ℝ) : ℂ) ≠ 0) :
    triBlockResolvent T z * triBlockShift T z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triBlockShift, triBlockResolvent, TriBlock.toMatrix, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] at hza hzb ⊢ <;>
    field_simp [hza, hzb]; ring

/-- The Chebyshev interpolant of the zero function is the zero polynomial. -/
theorem chebInterpolantPoly_zero (N : ℕ) :
    chebInterpolantPoly N (fun _ => (0 : ℝ)) = 0 := by
  simp [chebInterpolantPoly]

/-- Exact interpolation on the Hermitian spectrum yields exact functional evaluation with the
stated approximation, node count, and zero error record. -/
theorem chebFuncEval_exact {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (fr : ℝ → ℝ) (N : ℕ)
    (hpoint : ∀ i : Fin (Fintype.card I),
      |fr (orderedHermitianValues hA i) -
          (chebInterpolantPoly N fr).eval (orderedHermitianValues hA i)| ≤ 0) :
    ‖aeval A ((chebInterpolantPoly N fr).map Complex.ofRealHom) -
        hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))‖ ≤ 0 ∧
      (chebFuncEval A fr N 0 0 0).approx =
          aeval A ((chebInterpolantPoly N fr).map Complex.ofRealHom) ∧
      (chebFuncEval A fr N 0 0 0).nodeReads = N ∧
        (chebFuncEval A fr N 0 0 0).errorBound = 0 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  have h := hermitianFunction_polynomial_error_le A hA (fun x => ((fr x : ℝ) : ℂ))
    (chebInterpolantPoly N fr) (ε := 0) (by norm_num) ?_
  rw [norm_sub_rev]
  refine h
  intro i
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hpoint i

/-- A uniform Chebyshev approximation bound certifies the matrix evaluation error and the
recorded approximation, node count, and error bound. -/
theorem chebFuncEval_certified {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (fr : ℝ → ℝ) (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hspec : ∀ i : Fin (Fintype.card I),
      orderedHermitianValues hA i ∈ Set.Icc (-1 : ℝ) 1)
    (hpoint : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |fr x - (chebInterpolantPoly N fr).eval x| ≤ ε)
    (inputBits : ℕ) (εq : ℚ) :
    ‖aeval A ((chebInterpolantPoly N fr).map Complex.ofRealHom) -
        hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))‖ ≤ ε ∧
      (chebFuncEval A fr N inputBits εq ε).approx =
          aeval A ((chebInterpolantPoly N fr).map Complex.ofRealHom) ∧
      (chebFuncEval A fr N inputBits εq ε).nodeReads = N ∧
        (chebFuncEval A fr N inputBits εq ε).errorBound = ε := by
  refine ⟨?_, rfl, rfl, rfl⟩
  have h := cheb_interpolant_hermitian_error_le A hA fr N hε hspec hpoint
  rw [norm_sub_rev]
  exact h

/-- Distinct rational spectral basis vectors are orthogonal. -/
theorem ratSpecBasis_orthonormal {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (i j : Fin (Fintype.card I))
    (hij : i ≠ j) :
    inner ℝ (ratSpecBasis A hA i) (ratSpecBasis A hA j) = 0 :=
  (ratSpecBasis A hA).orthonormal.inner_eq_zero hij

/-- Every rational spectral basis vector has norm one. -/
theorem ratSpecBasis_norm {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (j : Fin (Fintype.card I)) :
    ‖ratSpecBasis A hA j‖ = 1 :=
  (ratSpecBasis A hA).norm_eq_one j

/-- The lifted matrix action on a spectral basis vector has the stated diagonal coordinate
representation. -/
theorem ratSpecBasis_residual {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℚ} (hA : A.transpose = A) (j k : Fin (Fintype.card I)) :
    ((ratSpecBasis A hA).repr ((ratMatrixReal A).toEuclideanLin (ratSpecBasis A hA j))).ofLp k
      = ratSpecValues A hA k *
        ((ratSpecBasis A hA).repr (ratSpecBasis A hA j)).ofLp k :=
  ratSpec_eigenvector hA (ratSpecBasis A hA j) k

/-- The spectral ledger records the supplied dimension, input bits, precision bits, and gap
bits. -/
theorem spectralLedger_accounting (D inputBits precisionBits gapBits : ℕ) :
    (spectralLedger D inputBits precisionBits gapBits).dim = D ∧
      (spectralLedger D inputBits precisionBits gapBits).inputBits = inputBits ∧
      (spectralLedger D inputBits precisionBits gapBits).precisionBits = precisionBits ∧
        (spectralLedger D inputBits precisionBits gapBits).gapBits = gapBits := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The spectral ledger bit time satisfies the stated cubic dimension and combined-bit bound. -/
theorem spectralLedger_bitTime_le (D inputBits precisionBits gapBits : ℕ) :
    (spectralLedger D inputBits precisionBits gapBits).bitTime
      ≤ (D + 1) ^ 3 * (inputBits + precisionBits + gapBits + 1) := by
  rfl

/-- The spectral ledger bit space satisfies the stated quadratic dimension and bit bound. -/
theorem spectralLedger_bitSpace_le (D inputBits precisionBits gapBits : ℕ) :
    (spectralLedger D inputBits precisionBits gapBits).bitSpace
      ≤ (D + 1) ^ 2 * (inputBits + precisionBits + 1) := by
  rfl

/-- The spectral ledger bit time is monotone in all four input budgets. -/
theorem spectralLedger_bitTime_mono {D D' inputBits inputBits' precisionBits precisionBits'
    gapBits gapBits' : ℕ} (hD : D ≤ D') (hI : inputBits ≤ inputBits')
    (hP : precisionBits ≤ precisionBits') (hG : gapBits ≤ gapBits') :
    (spectralLedger D inputBits precisionBits gapBits).bitTime
      ≤ (spectralLedger D' inputBits' precisionBits' gapBits').bitTime := by
  simp only [spectralLedger]
  have h1 : (D + 1) ^ 3 ≤ (D' + 1) ^ 3 := by
    exact Nat.pow_le_pow_left (Nat.succ_le_succ hD) 3
  have h2 : inputBits + precisionBits + gapBits + 1
      ≤ inputBits' + precisionBits' + gapBits' + 1 := by omega
  exact Nat.mul_le_mul h1 h2

/-- A positive-order Gauss-Legendre rule has weights summing to two and is exact through twice
the order minus one. -/
theorem gaussLegendre_rule_entry {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ node weight : Fin Q → ℝ,
      (∑ q, weight q = 2) ∧
        (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
          ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) := by
  obtain ⟨node, weight, hw, hexact, _hclosed⟩ :=
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.clause1_with_admissible_sign_gap.2.2.2.2.1 Q hQ
  exact ⟨node, weight, hw, hexact⟩

/-- A polynomial within the Gauss-Legendre degree budget is integrated exactly by a rule exact
throughout that budget. -/
theorem gauss_legendre_exact_of_degree_le {Q : ℕ} (hQ : 1 ≤ Q) (p : Polynomial ℝ)
    (hdeg : p.natDegree ≤ 2 * Q - 1) :
    ∃ node weight : Fin Q → ℝ,
      (∑ q, weight q = 2) ∧
        (∀ r : Polynomial ℝ, r.natDegree ≤ 2 * Q - 1 →
          ∫ x in (-1 : ℝ)..1, r.eval x = ∑ q, weight q * r.eval (node q)) ∧
        (∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) := by
  obtain ⟨node, weight, hw, hexact⟩ := gaussLegendre_rule_entry hQ
  exact ⟨node, weight, hw, hexact, hexact p hdeg⟩

/-- A Chebyshev interpolant with at most twice the quadrature order nodes is integrated exactly
by a suitable Gauss-Legendre rule. -/
theorem cheb_interpolant_gauss_legendre_exact {Q N : ℕ} (hQ : 1 ≤ Q) (hN : N ≤ 2 * Q)
    (f : ℝ → ℝ) :
    ∃ node weight : Fin Q → ℝ,
      (∑ q, weight q = 2) ∧
        (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
          ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
        (∫ x in (-1 : ℝ)..1, (chebInterpolantPoly N f).eval x =
          ∑ q, weight q * (chebInterpolantPoly N f).eval (node q)) := by
  obtain ⟨node, weight, hw, hexact, hexactP⟩ :=
    gauss_legendre_exact_of_degree_le hQ (chebInterpolantPoly N f)
      (le_trans (chebInterpolantPoly_degree f) (by omega))
  exact ⟨node, weight, hw, hexact, hexactP⟩

/-- A windowed reciprocal approximating polynomial admits an exact Gauss-Legendre rule with the
stated degree and approximation bounds. -/
theorem window_family_gauss_legendre_exact (ε δ : ℝ) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hδ : δ ≤ 1 / 2) :
    ∃ (Pw : Polynomial ℝ) (J k Q : ℕ) (node weight : Fin Q → ℝ),
      (∑ q, weight q = 2) ∧
        (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
          ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
        (Pw.natDegree ≤ 2 * J + 1 + 2 * 3 ^ k) ∧
        (∫ x in (-1 : ℝ)..1, Pw.eval x = ∑ q, weight q * Pw.eval (node q)) ∧
        (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ / 2) / x| ≤ ε) := by
  obtain ⟨Pw, J, k, _hJ, _hk, hdeg, _hpar, _hbnd, _h0, happ⟩ :=
    Qatlib.Concepts.QsvtCore.LinearSystems.windowed_reciprocal_exists ε δ hε hεδ hδ
  have hQ : 1 ≤ 2 * J + 2 * 3 ^ k + 1 := by omega
  obtain ⟨node, weight, hw, hexact, hexactP⟩ :=
    gauss_legendre_exact_of_degree_le hQ Pw (le_trans hdeg (by omega))
  exact ⟨Pw, J, k, 2 * J + 2 * 3 ^ k + 1, node, weight, hw, hexact, hdeg, hexactP, happ⟩

/-- Every sign polynomial admits a Gauss-Legendre rule integrating it exactly. -/
theorem sign_family_gauss_legendre_exact (k : ℕ) :
    ∃ (Q : ℕ) (node weight : Fin Q → ℝ),
      (∑ q, weight q = 2) ∧
        (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
          ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
        (∫ x in (-1 : ℝ)..1, (Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval x =
          ∑ q, weight q * (Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval (node q)) := by
  have hdeg : (Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).natDegree ≤ 2 * 3 ^ k - 1 := by
    rw [Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial_natDegree]
    omega
  obtain ⟨node, weight, hw, hexact, hexactP⟩ :=
    gauss_legendre_exact_of_degree_le (Q := 3 ^ k) (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (3:ℕ) ≠ 0)))
      (Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k) hdeg
  exact ⟨3 ^ k, node, weight, hw, hexact, hexactP⟩

/-- The near-optimal reciprocal polynomial admits a Gauss-Legendre rule integrating it exactly
under the stated parameter assumptions. -/
theorem reciprocal_family_gauss_legendre_exact (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε)
    (hε1 : ε < 1 / 2) :
    ∃ (Q : ℕ) (node weight : Fin Q → ℝ),
      (∑ q, weight q = 2) ∧
        (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
          ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
        (∫ x in (-1 : ℝ)..1, (Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalPolynomial κ ε).eval x =
          ∑ q, weight q * (Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalPolynomial κ ε).eval (node q)) := by
  obtain ⟨_hb, hJ2, hdeg, _hpar, _hz, _hbudget⟩ :=
    Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocal_family_degree_parity κ ε hκ hε hε1
  have hdeg' : (Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalPolynomial κ ε).natDegree ≤
      2 * (2 * Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε + 1) - 1 := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    have hle : 2 * Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε + 1 ≤
        2 * (2 * Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε + 1) - 1 := by omega
    exact hdeg.trans (WithBot.coe_le_coe.mpr hle)
  have hQ : 1 ≤ 2 * Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε + 1 := by
    omega
  obtain ⟨node, weight, hw, hexact, hexactP⟩ :=
    gauss_legendre_exact_of_degree_le (Q := 2 * Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε + 1)
      hQ (Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalPolynomial κ ε) hdeg'
  exact ⟨2 * Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε + 1, node, weight,
      hw, hexact, hexactP⟩

/-- Row padding preserves matrix entries whose row indices are within the original range. -/
theorem zeroPadRows_apply {O I D : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) {i : Fin D} (hi : i.val < O)
    (j : Fin I) : zeroPadRows A i j = A ⟨i.val, hi⟩ j := by
  unfold zeroPadRows
  rw [dite_eq_left hi]

/-- Column padding preserves matrix entries whose column indices are within the original range. -/
theorem zeroPadCols_apply {O I J : ℕ} (A : Matrix (Fin O) (Fin I) ℚ) {j : Fin J} (hj : j.val < I)
    (i : Fin O) : zeroPadCols A i j = A i ⟨j.val, hj⟩ := by
  unfold zeroPadCols
  rw [dite_eq_left hj]

/-- Padding with zero rows to a larger row count preserves the Gram matrix. -/
theorem zeroPadRows_gram_eq {O I D : ℕ} (hOD : O ≤ D) (A : Matrix (Fin O) (Fin I) ℚ) :
    ((zeroPadRows A : Matrix (Fin D) (Fin I) ℚ)ᵀ * (zeroPadRows A : Matrix (Fin D) (Fin I) ℚ))
      = Aᵀ * A := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hkey : ∀ k : Fin D,
      zeroPadRows A k i * zeroPadRows A k j =
        (if h : k.val < O then A ⟨k.val, h⟩ i * A ⟨k.val, h⟩ j else 0) := by
    intro k
    by_cases hk : k.val < O
    · simp [zeroPadRows, hk]
    · simp [zeroPadRows, hk]
  have h1 : (∑ k : Fin D, zeroPadRows A k i * zeroPadRows A k j)
      = ∑ k : Fin D, (if h : k.val < O then A ⟨k.val, h⟩ i * A ⟨k.val, h⟩ j else 0) :=
    Finset.sum_congr rfl (fun k _ => hkey k)
  have h2 : (∑ k : Fin D, (if h : k.val < O then A ⟨k.val, h⟩ i * A ⟨k.val, h⟩ j else 0))
      = ∑ k ∈ Finset.univ.filter (fun k : Fin D => k.val < O),
          (if h : k.val < O then A ⟨k.val, h⟩ i * A ⟨k.val, h⟩ j else 0) :=
    (Finset.sum_subset (s₁ := Finset.univ.filter (fun k : Fin D => k.val < O))
      (s₂ := (Finset.univ : Finset (Fin D)))
      (Finset.filter_subset _ _) (by
        intro k _ hk
        have hk' : ¬ (k.val < O) := by
          intro hc
          exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        rw [dite_eq_right hk'])).symm
  have h3 : (∑ k ∈ Finset.univ.filter (fun k : Fin D => k.val < O),
          (if h : k.val < O then A ⟨k.val, h⟩ i * A ⟨k.val, h⟩ j else 0))
      = ∑ k : Fin O, A k i * A k j := by
    refine Finset.sum_bij (s := Finset.univ.filter (fun k : Fin D => k.val < O))
      (t := (Finset.univ : Finset (Fin O))) (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_univ _
    · intro a₁ ha₁ a₂ ha₂ heq
      have hv : a₁.val = a₂.val := (Fin.mk.inj_iff).mp heq
      exact Fin.val_injective hv
    · intro b hb
      refine ⟨⟨b.val, lt_of_lt_of_le b.isLt hOD⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩
    · intro a ha
      have ha' : a.val < O := (Finset.mem_filter.mp ha).2
      rw [dite_eq_left ha']
  exact h1.trans (h2.trans h3)

/-- The original-index corner of the column-padded Gram matrix equals the original Gram matrix. -/
theorem zeroPadCols_gram_apply {O I J : ℕ} (A : Matrix (Fin O) (Fin I) ℚ)
    {i j : Fin J} (hi : i.val < I) (hj : j.val < I) :
    ((zeroPadCols A)ᵀ * (zeroPadCols A)) i j = (Aᵀ * A) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [zeroPadCols, hi, hj]

/-- A Gram-matrix entry in a padded column index row is zero. -/
theorem zeroPadCols_gram_zero {O I J : ℕ} (A : Matrix (Fin O) (Fin I) ℚ)
    {i j : Fin J} (hi : I ≤ i.val) :
    ((zeroPadCols A)ᵀ * (zeroPadCols A)) i j = 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  simp [zeroPadCols, hi]

/-- Every row of the column-padded Gram matrix indexed beyond the original columns is zero. -/
theorem zeroPadCols_gram_kernel {O I J : ℕ} (A : Matrix (Fin O) (Fin I) ℚ)
    {k : Fin J} (hk : I ≤ k.val) (j : Fin J) :
    ((zeroPadCols A)ᵀ * (zeroPadCols A)) k j = 0 :=
  zeroPadCols_gram_zero A hk

/-- The spectral ledger time and space budgets are monotone when the row dimension increases. -/
theorem zeroPadRows_ledger_mono {O D inputBits precisionBits gapBits : ℕ} (hOD : O ≤ D) :
    (spectralLedger O inputBits precisionBits gapBits).bitTime ≤
        (spectralLedger D inputBits precisionBits gapBits).bitTime ∧
      (spectralLedger O inputBits precisionBits gapBits).bitSpace ≤
        (spectralLedger D inputBits precisionBits gapBits).bitSpace := by
  have hp3 : (O + 1) ^ 3 ≤ (D + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hp2 : (O + 1) ^ 2 ≤ (D + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  simp only [spectralLedger]
  constructor
  · exact Nat.mul_le_mul_right _ hp3
  · exact Nat.mul_le_mul_right _ hp2

noncomputable def ratResidual {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ) (v : EuclideanSpace ℝ (Fin D))
    (ρ : ℝ) : EuclideanSpace ℝ (Fin D) :=
  (ratMatrixReal A).toEuclideanLin v - ρ • v

/-- The matrix `ratProjector v` is symmetric. -/
theorem ratProjector_sym {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) :
    (ratProjector v).transpose = ratProjector v := by
  ext i j
  simp [ratProjector, mul_comm]

/-- For a nonzero vector, `ratProjector v` is idempotent. -/
theorem ratProjector_idem {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) (hv : v ≠ 0) :
    ratProjector v * ratProjector v = ratProjector v := by
  ext i j
  simp only [Matrix.mul_apply]
  have hs : (∑ k, v k ^ 2) ≠ 0 := by
    rw [← EuclideanSpace.real_norm_sq_eq v]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  calc (∑ k, ratProjector v i k * ratProjector v k j)
      = ∑ k, (v i * v j) * (v k ^ 2) / (∑ k, v k ^ 2) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        unfold ratProjector
        field_simp
    _ = (v i * v j) * (∑ k, v k ^ 2) / (∑ k, v k ^ 2) ^ 2 := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
    _ = v i * v j / (∑ k, v k ^ 2) := by field_simp
    _ = ratProjector v i j := rfl

/-- Each projector error entry is the corresponding residual component times a vector coordinate
divided by its squared norm sum. -/
theorem ratProjector_residual {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : EuclideanSpace ℝ (Fin D)) (ρ : ℝ) (i j : Fin D) :
    ((ratMatrixReal A) * (ratProjector v) - ρ • (ratProjector v)) i j =
      ratResidual A v ρ i * v j / (∑ k, v k ^ 2) := by
  have hmul : ∀ (M : Matrix (Fin D) (Fin D) ℝ) (w : EuclideanSpace ℝ (Fin D)) (i : Fin D),
      (M.toEuclideanLin w) i = ∑ j, M i j * w j := by
    intro M w i; rfl
  unfold ratResidual
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, PiLp.sub_apply,
    PiLp.smul_apply]
  rw [hmul]
  simp only [ratMatrixReal, Matrix.map_apply]
  unfold ratProjector
  have h1 : (∑ x, (A i x : ℝ) * (v x * v j / (∑ k, v k ^ 2)))
      = (∑ x, (A i x : ℝ) * v x) * v j / (∑ k, v k ^ 2) := by
    have h2 : ∀ x : Fin D, (A i x : ℝ) * (v x * v j / (∑ k, v k ^ 2))
        = ((A i x : ℝ) * v x) * (v j / (∑ k, v k ^ 2)) := by
      intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => h2 x)]
    rw [← Finset.sum_mul]
    ring
  rw [h1]
  ring

/-- The projector error matrix equals the normalized outer product of the residual and the
vector. -/
theorem ratProjector_error_matrix {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : EuclideanSpace ℝ (Fin D)) (ρ : ℝ) :
    (ratMatrixReal A) * (ratProjector v) - ρ • (ratProjector v)
      = (fun i j => ratResidual A v ρ i * v j / (∑ k, v k ^ 2)) := by
  ext i j
  exact ratProjector_residual A v ρ i j

/-- Applying the projector error matrix to its defining nonzero vector recovers the residual
vector. -/
theorem ratProjector_residual_vector {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : EuclideanSpace ℝ (Fin D)) (ρ : ℝ) (hv : v ≠ 0) :
    ((ratMatrixReal A) * (ratProjector v) - ρ • (ratProjector v)).toEuclideanLin v
      = (ratMatrixReal A).toEuclideanLin v - ρ • v := by
  have hmul : ∀ (M : Matrix (Fin D) (Fin D) ℝ) (w : EuclideanSpace ℝ (Fin D)) (i : Fin D),
      (M.toEuclideanLin w) i = ∑ j, M i j * w j := by
    intro M w i; rfl
  rw [ratProjector_error_matrix]
  ext i
  rw [hmul]
  have hR : ((ratMatrixReal A).toEuclideanLin v - ρ • v) i = ratResidual A v ρ i := by
    simp only [ratResidual, PiLp.sub_apply, PiLp.smul_apply]
  rw [hR]
  have hs : (∑ k, v k ^ 2) ≠ 0 := by
    rw [← EuclideanSpace.real_norm_sq_eq v]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have h2 : ∀ j : Fin D, (ratResidual A v ρ i * v j / (∑ k, v k ^ 2)) * v j
      = ratResidual A v ρ i * (v j ^ 2) / (∑ k, v k ^ 2) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => h2 j)]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  field_simp

/-- The projector error acts on any vector by the stated inner-product multiple of the residual. -/
theorem ratProjector_error_action {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : EuclideanSpace ℝ (Fin D)) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin D)) :
    ((ratMatrixReal A) * (ratProjector v) - ρ • (ratProjector v)).toEuclideanLin x
      = (inner ℝ v x / (∑ k, v k ^ 2)) • ratResidual A v ρ := by
  have hmul : ∀ (M : Matrix (Fin D) (Fin D) ℝ) (w : EuclideanSpace ℝ (Fin D)) (i : Fin D),
      (M.toEuclideanLin w) i = ∑ j, M i j * w j := by
    intro M w i; rfl
  rw [ratProjector_error_matrix]
  ext i
  rw [hmul]
  have hinner : inner ℝ v x = ∑ j, v j * x j := by
    simp [PiLp.inner_apply, mul_comm]
  have h2 : ∀ j : Fin D,
      (ratResidual A v ρ i * v j / (∑ k, v k ^ 2)) * x j
        = (ratResidual A v ρ i / (∑ k, v k ^ 2)) * (v j * x j) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => h2 j)]
  rw [← Finset.mul_sum, hinner]
  simp only [PiLp.smul_apply]
  ring

/-- The projector error norm is at most the relative residual norm of its defining nonzero
vector. -/
theorem ratProjector_error_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (v : EuclideanSpace ℝ (Fin D)) (ρ : ℝ) (hv : v ≠ 0) :
    ‖(ratMatrixReal A) * (ratProjector v) - ρ • (ratProjector v)‖ ≤
      ‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ / ‖v‖ := by
  have hs : (∑ k, v k ^ 2) ≠ 0 := by
    rw [← EuclideanSpace.real_norm_sq_eq v]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  have hsv : 0 < ∑ k, v k ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq v]
    positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  show ‖((ratMatrixReal A) * (ratProjector v) - ρ • (ratProjector v)).toEuclideanLin x‖
    ≤ (‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ / ‖v‖) * ‖x‖
  rw [ratProjector_error_action]
  rw [norm_smul]
  have hcs : |inner ℝ v x| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
  have hinner : inner ℝ v x = ∑ j, v j * x j := by
    simp [PiLp.inner_apply, mul_comm]
  have hscale : ‖inner ℝ v x / (∑ k, v k ^ 2)‖
      = |inner ℝ v x| / (∑ k, v k ^ 2) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hsv]
  rw [hscale]
  rw [← EuclideanSpace.real_norm_sq_eq v]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hkey : |inner ℝ v x| / ‖v‖ ^ 2 ≤ ‖x‖ / ‖v‖ := by
    have hvn : ‖v‖ ≠ 0 := ne_of_gt hvpos
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖v‖ ^ 2)]
    have h3 : (‖x‖ / ‖v‖) * ‖v‖ ^ 2 = ‖x‖ * ‖v‖ := by field_simp
    rw [h3]
    simpa [mul_comm] using! hcs
  calc (|inner ℝ v x| / ‖v‖ ^ 2) * ‖ratResidual A v ρ‖
      ≤ (‖x‖ / ‖v‖) * ‖ratResidual A v ρ‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
    _ = (‖ratResidual A v ρ‖ / ‖v‖) * ‖x‖ := by ring

noncomputable def certifySpectralProjection {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (_hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) (inputBits : ℕ) :
    SpectralProjectionRun D :=
  let ρ := ratRayleigh A v
  let r := ‖(ratMatrixReal A).toEuclideanLin v - ρ • v‖ / ‖v‖
  { projector := ratProjector v
    quotient := ρ
    errorBound := r
    bitTime := (D + 1) ^ 3 * (inputBits + 1)
    bitSpace := (D + 1) ^ 2 * (inputBits + 1) }

/-- The certified spectral projection records the relative Rayleigh residual as its error bound. -/
theorem certifySpectralProjection_errorBound_eq {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) (inputBits : ℕ) :
    (certifySpectralProjection A hA v inputBits).errorBound =
      ‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖ := rfl

/-- The certified spectral projection error bound is nonnegative. -/
theorem certifySpectralProjection_errorBound_nonneg {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) (inputBits : ℕ) :
    0 ≤ (certifySpectralProjection A hA v inputBits).errorBound := by
  rw [certifySpectralProjection_errorBound_eq]
  positivity

/-- The spectral projection residual criterion encloses some spectral value within the requested
Rayleigh tolerance. -/
theorem certifySpectralProjection_sound {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hv : v ≠ 0) [Nonempty (Fin D)]
    (hr : ‖(ratMatrixReal A).toEuclideanLin v - ratRayleigh A v • v‖ / ‖v‖ ≤ δ) :
    ∃ j : Fin (Fintype.card (Fin D)),
      |ratSpecValues A hA j - ratRayleigh A v| ≤ δ := by
  obtain ⟨j, hj⟩ := ratSpec_value_enclosure hA v hv
  refine ⟨j, ?_⟩
  simpa only [ratRayleigh] using! hj.trans hr

/-- The certified projection error bound controls the norm of the Rayleigh projector residual
matrix. -/
theorem certifySpectralProjection_error_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℚ)
    (hA : A.transpose = A) (v : EuclideanSpace ℝ (Fin D)) (hv : v ≠ 0)
    (inputBits : ℕ) :
    ‖(ratMatrixReal A) * (ratProjector v) - ratRayleigh A v • (ratProjector v)‖
      ≤ (certifySpectralProjection A hA v inputBits).errorBound := by
  exact ratProjector_error_le A v (ratRayleigh A v) hv

/-- When the smaller matrix rank is zero, Chebyshev evaluation satisfies the stated
approximation-plus-rank-weighted perturbation bound. -/
theorem chebFuncEval_ranklog_stability {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (fr : ℝ → ℝ) (N : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hf : Qatlib.Concepts.SketchSpectral.MatrixFunctions.hermitianPairScalarLipschitz A hA B hB
      (fun x => ((fr x : ℝ) : ℂ)) L)
    (hr : min A.rank B.rank = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hspec : ∀ i : Fin (Fintype.card I),
      orderedHermitianValues hA i ∈ Set.Icc (-1 : ℝ) 1)
    (hpoint : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |fr x - (chebInterpolantPoly N fr).eval x| ≤ ε)
    (inputBits : ℕ) (εq : ℚ) :
    ‖(chebFuncEval A fr N inputBits εq ε).approx
        - hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ))‖ ≤
      ε + Qatlib.Concepts.SketchSpectral.MatrixFunctions.hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ := by
  have hcert := chebFuncEval_certified A hA fr N hε hspec hpoint inputBits εq
  have hstab := Qatlib.Concepts.SketchSpectral.MatrixFunctions.hermitianFunction_operator_stability_min_rank_zero
    A B hA hB hr (fun x => ((fr x : ℝ) : ℂ)) L hL hf
  have htri : ‖(chebFuncEval A fr N inputBits εq ε).approx
        - hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ))‖ ≤
      ‖(chebFuncEval A fr N inputBits εq ε).approx
        - hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))‖
        + ‖hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))
        - hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ))‖ := by
    have h := dist_triangle (chebFuncEval A fr N inputBits εq ε).approx
      (hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ)))
      (hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ)))
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
    exact h
  have h1 : ‖(chebFuncEval A fr N inputBits εq ε).approx
        - hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))‖ ≤ ε := by
    rw [hcert.2.1]
    exact hcert.1
  calc ‖(chebFuncEval A fr N inputBits εq ε).approx
        - hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ))‖
      ≤ ‖(chebFuncEval A fr N inputBits εq ε).approx
        - hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))‖
        + ‖hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))
        - hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ))‖ := htri
    _ ≤ ε + ‖hermitianFunction A hA (fun x => ((fr x : ℝ) : ℂ))
        - hermitianFunction B hB (fun x => ((fr x : ℝ) : ℂ))‖ := by linarith
    _ ≤ ε + Qatlib.Concepts.SketchSpectral.MatrixFunctions.hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ := by
      linarith [hstab]

/-- Away from the first diagonal value, the triangular block has a resolvent certificate with
the stated half-distance radius. -/
theorem triBlock_resolvent_certificate (T : TriBlock) {z : ℂ}
    (hza : z - ((T.a : ℝ) : ℂ) ≠ 0) :
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.ResolventCertificate (T.toMatrix) z
      (‖z - ((T.a : ℝ) : ℂ)‖ / 2) := by
  constructor
  · have hpos : 0 < ‖z - ((T.a : ℝ) : ℂ)‖ := norm_pos_iff.mpr hza
    exact div_pos hpos (by norm_num)
  · have hlower : ‖z - ((T.a : ℝ) : ℂ)‖ ≤ ‖triBlockShift T z‖ := by
      have hunit : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        simp [EuclideanSpace.single]
      have hcol : ∀ i : Fin 2,
          (triBlockShift T z).toEuclideanLin
              (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) i
            = (triBlockShift T z) i 0 := by
        intro i
        have h1 : (triBlockShift T z).toEuclideanLin
              (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) i
            = ∑ j, (triBlockShift T z) i j
                * (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) j := rfl
        rw [h1]
        fin_cases i <;> simp [EuclideanSpace.single]
      have hn : ‖(triBlockShift T z).toEuclideanLin
              (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2))‖
          = ‖z - ((T.a : ℝ) : ℂ)‖ := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
        simp only [hcol]
        have h00 : (triBlockShift T z) 0 0 = z - ((T.a : ℝ) : ℂ) := by
          simp [triBlockShift, Matrix.sub_apply, Matrix.smul_apply, TriBlock.toMatrix]
        have h10 : (triBlockShift T z) 1 0 = 0 := by
          simp [triBlockShift, Matrix.sub_apply, Matrix.smul_apply, TriBlock.toMatrix]
        rw [h00, h10]
        have hz : ‖z - ((T.a : ℝ) : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2
            = ‖z - ((T.a : ℝ) : ℂ)‖ ^ 2 := by simp
        rw [hz, Real.sqrt_sq_eq_abs]
        simp
      have hle0 := Matrix.l2_opNorm_mulVec (triBlockShift T z)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2))
      have hle : ‖(triBlockShift T z).toEuclideanLin
              (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2))‖
          ≤ ‖triBlockShift T z‖ * ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
              : EuclideanSpace ℂ (Fin 2))‖ := by
        rwa [show (EuclideanSpace.equiv (Fin 2) ℂ).symm
              (triBlockShift T z
                *ᵥ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2)))
            = (triBlockShift T z).toEuclideanLin
                (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) from rfl] at hle0
      rw [hn] at hle
      rw [hunit] at hle
      simpa using! hle
    have hnn : 0 ≤ ‖z - ((T.a : ℝ) : ℂ)‖ := norm_nonneg _
    have hshift : triBlockShift T z = z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - T.toMatrix := rfl
    rw [hshift] at hlower
    linarith

/-- The stated entrywise bound yields a Schur multiplier bound for the triangular-block
resolvent radius. -/
theorem triBlock_schur_multiplier_bounded (T : TriBlock) {z : ℂ}
    (hza : z - ((T.a : ℝ) : ℂ) ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ 2 / ‖z - ((T.a : ℝ) : ℂ)‖) :
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.SchurMultiplierBounded B
      ((2 : ℝ) / (‖z - ((T.a : ℝ) : ℂ)‖ / 2)) := by
  have hcert := triBlock_resolvent_certificate T hza
  have hne : ‖z - ((T.a : ℝ) : ℂ)‖ ≠ 0 := by
    exact ne_of_gt (norm_pos_iff.mpr hza)
  refine Qatlib.Concepts.OrderedOracle.TiSdpBridge.clause55_schurMultiplierBridge 2 (T.toMatrix) z
    (‖z - ((T.a : ℝ) : ℂ)‖ / 2) hcert B ?_
  intro i j
  have hone : 1 / (‖z - ((T.a : ℝ) : ℂ)‖ / 2) = 2 / ‖z - ((T.a : ℝ) : ℂ)‖ := by
    field_simp
  rw [hone]
  exact hB i j

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
