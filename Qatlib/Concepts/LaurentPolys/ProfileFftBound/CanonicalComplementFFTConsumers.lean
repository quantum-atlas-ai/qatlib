/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.CircleComplementConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.BoundaryCanon Qatlib.Concepts.LaurentPolys.CircleComplement

namespace Qatlib.Concepts.LaurentPolys.ProfileFftBound
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def radixTwoPositiveFourier (m : ℕ) (f : Fin (2^m) → ℂ) :
    ((Fin (2^m) → ℂ) × ℕ × ℕ) :=
  let t := radixTwoFourier m (fun j => star (f j))
  (fun j => star (t.1 j), t.2)

/-- The positive radix two Fourier transform computes the positive exponential sum with
`m*2^m/2` multiplications and `m*2^m` additions. -/
theorem radixTwoPositiveFourier_semantics_cost (m : ℕ) (f : Fin (2^m) → ℂ) :
    (∀ j : Fin (2^m), (radixTwoPositiveFourier m f).1 j =
      ∑ l : Fin (2^m), f l*
        Complex.exp ((2*Real.pi*j.val*l.val/(2^m : ℕ) : ℝ)*Complex.I)) ∧
    (radixTwoPositiveFourier m f).2.1 = m*2^m/2 ∧
    (radixTwoPositiveFourier m f).2.2 = m*2^m := by
  refine ⟨?_, radixTwoFourier_cost m (fun j => star (f j))⟩
  intro j
  change star ((radixTwoFourier m (fun l => star (f l))).1 j) = _
  rw [radixTwoFourier_semantics, star_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [star_mul, star_star]
  rw [mul_comm (star _) (f l)]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  push_cast
  ring

def radixTwoNormalisedFourier (m : ℕ) (f : Fin (2^m) → ℂ) :
    ((Fin (2^m) → ℂ) × ℕ × ℕ) :=
  let t := radixTwoFourier m f
  (fun j => (2^m : ℂ)⁻¹*t.1 j, t.2.1+2^m, t.2.2)

/-- The normalized radix two Fourier transform computes the negative exponential sum divided by
the grid size, with the stated multiplication and addition counts. -/
theorem radixTwoNormalisedFourier_semantics_cost (m : ℕ) (f : Fin (2^m) → ℂ) :
    (∀ j : Fin (2^m), (radixTwoNormalisedFourier m f).1 j =
      (2^m : ℂ)⁻¹ * ∑ l : Fin (2^m),
        f l*Complex.exp ((-2*Real.pi*j.val*l.val/(2^m : ℕ) : ℝ)*Complex.I)) ∧
    (radixTwoNormalisedFourier m f).2.1 = m*2^m/2+2^m ∧
    (radixTwoNormalisedFourier m f).2.2 = m*2^m := by
  obtain ⟨hm, ha⟩ := radixTwoFourier_cost m f
  refine ⟨?_, ?_, ha⟩
  · intro j
    change (2^m : ℂ)⁻¹*(radixTwoFourier m f).1 j = _
    rw [radixTwoFourier_semantics]
  · change (radixTwoFourier m f).2.1+2^m = _
    rw [hm]

/-- The radix two Fourier output equals the sum weighted by negative powers of the grid root of
unity. -/
theorem radixTwoFourier_root_semantics (m : ℕ) (f : Fin (2^m) → ℂ)
    (j : Fin (2^m)) :
    (radixTwoFourier m f).1 j =
      ∑ l : Fin (2^m), f l*
        (Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I))^(-(j.val*l.val : ℤ)) := by
  rw [radixTwoFourier_semantics]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- The positive radix two Fourier output equals the sum weighted by positive powers of the grid
root of unity. -/
theorem radixTwoPositiveFourier_root_semantics (m : ℕ) (f : Fin (2^m) → ℂ)
    (j : Fin (2^m)) :
    (radixTwoPositiveFourier m f).1 j =
      ∑ l : Fin (2^m), f l*
        (Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I))^(j.val*l.val) := by
  rw [(radixTwoPositiveFourier_semantics_cost m f).1]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Gram matrix of the circle completion is the identity scaled by the sum of squared
polynomial evaluation norms. -/
theorem circleCompletion_gram (P Q : Polynomial ℂ) (z : ℂ) :
    (circleCompletion P Q z)ᴴ*circleCompletion P Q z =
      ((‖P.eval z‖^2+‖Q.eval z‖^2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  have hn : P.eval z*star (P.eval z)+Q.eval z*star (Q.eval z) =
      ((‖P.eval z‖^2+‖Q.eval z‖^2 : ℝ) : ℂ) := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply,
      circleCompletion, Bool.false_eq_true, ite_false, ite_true, star_neg, star_star,
      Matrix.one_apply, Bool.true_eq_false, mul_neg, Matrix.smul_apply, smul_eq_mul]
  · linear_combination hn
  · ring
  · ring
  · linear_combination hn

/-- The circle completion unitarity defect norm equals the circle residual. -/
theorem circleCompletion_unitarity_defect_eq_residual (P Q : Polynomial ℂ) (z : ℂ) :
    ‖(circleCompletion P Q z)ᴴ*circleCompletion P Q z-1‖ = circleResidual P Q z := by
  rw [circleCompletion_gram]
  have he : (((‖P.eval z‖^2+‖Q.eval z‖^2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ))-1 =
      (((‖P.eval z‖^2+‖Q.eval z‖^2-1 : ℝ) : ℂ)) • (1 : Matrix Bool Bool ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  rw [he, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- A polynomial with a positive unit circle margin has a normalized complement without closed
disk zeros whose circle completion is unitary and produces the stated evaluation amplitudes. -/
theorem canonical_complement_exact_filter_consumer (P : Polynomial ℂ) (d : ℕ) (δ : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ d ∧ 0 < (Q.eval 0).re ∧ (Q.eval 0).im = 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 →
        circleCompletion P Q z ∈ Matrix.unitaryGroup Bool ℂ ∧
        (circleCompletion P Q z).mulVec (fun b : Bool => if b then 0 else 1) =
          (fun b : Bool => if b then Q.eval z else P.eval z) ∧
        ‖(circleCompletion P Q z)ᴴ*circleCompletion P Q z-1‖ = 0) := by
  obtain ⟨Q, hQd, hQr, hQi, hQn, hQc, _⟩ :=
    canonical_complement_schwarz_representation P d δ hp hδ hδ1 hP
  refine ⟨Q, hQd, hQr, hQi, hQn, ?_⟩
  intro z hz
  obtain ⟨hu, ho⟩ := circle_complement_actual_filter_consumer P Q z hz (hQc z hz)
  refine ⟨hu, ho, ?_⟩
  rw [circleCompletion_unitarity_defect_eq_residual]
  simp only [circleResidual, hQc z hz, sub_self, abs_zero]

structure CanonicalComplementFourierRun (m : ℕ) where
  coefficients : Fin (2^m) → ℂ
  gridValues : Fin (2^m) → ℂ
  multiplications : ℕ
  additions : ℕ
  logarithms : ℕ
  exponentials : ℕ

def canonicalComplementFourierRun (P : Polynomial ℂ) (d m : ℕ) :
    CanonicalComplementFourierRun m :=
  let ω := Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I)
  let first := radixTwoNormalisedFourier m
    (fun j => ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ))
  let second := radixTwoPositiveFourier m
    (fun j => if j.val = 0 then (2 : ℂ)⁻¹*first.1 j
      else if j.val ≤ 2^m/2 then first.1 j else 0)
  let third := radixTwoNormalisedFourier m (fun j => Complex.exp (second.1 j))
  let fourth := radixTwoPositiveFourier m
    (fun j => if j.val ≤ d then third.1 j else 0)
  ⟨third.1, fourth.1,
    first.2.1+second.2.1+third.2.1+fourth.2.1+1,
    first.2.2+second.2.2+third.2.2+fourth.2.2, 2^m, 2^m⟩

/-- Gives the exact multiplication, addition, logarithm, and exponential counts for the
canonical complement Fourier run. -/
theorem canonicalComplementFourierRun_cost (P : Polynomial ℂ) (d m : ℕ) :
    (canonicalComplementFourierRun P d m).multiplications =
      4*(m*2^m/2)+2*2^m+1 ∧
    (canonicalComplementFourierRun P d m).additions = 4*m*2^m ∧
    (canonicalComplementFourierRun P d m).logarithms = 2^m ∧
    (canonicalComplementFourierRun P d m).exponentials = 2^m := by
  unfold canonicalComplementFourierRun
  simp only [radixTwoNormalisedFourier_semantics_cost,
    radixTwoPositiveFourier_semantics_cost]
  constructor
  · ring
  constructor
  · ring
  trivial

/-- A finite half spectrum sum equals half its constant coefficient plus the positive frequency
sum through the midpoint. -/
private theorem sum_half_spectrum (N : ℕ) (hN : 0 < N)
    (a : ℕ → ℂ) (ω : ℂ) (j : ℕ) :
    (∑ l : Fin N, (if l.val = 0 then (2 : ℂ)⁻¹*a l.val
      else if l.val ≤ N/2 then a l.val else 0)*ω^(l.val*j)) =
      (2 : ℂ)⁻¹*a 0 +
        ∑ l ∈ Finset.range (N/2+1), if l=0 then 0 else a l*ω^(l*j) := by
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
    (if l = 0 then (2 : ℂ)⁻¹*a l else if l ≤ N/2 then a l else 0)*ω^(l*j)) N]
  have hK : N/2+1 ≤ N := by omega
  calc
    _ = ∑ l ∈ Finset.range (N/2+1),
        (if l = 0 then (2 : ℂ)⁻¹*a l else if l ≤ N/2 then a l else 0)*ω^(l*j) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hK)
      intro l _ hl
      have hk : ¬l ≤ N/2 := by simp only [Finset.mem_range] at hl; omega
      have h0 : l ≠ 0 := by omega
      simp [h0, hk]
    _ = ∑ l ∈ Finset.range (N/2+1),
        ((if l=0 then (2 : ℂ)⁻¹*a 0 else 0) +
          (if l=0 then 0 else a l*ω^(l*j))) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hk : l ≤ N/2 := by simp only [Finset.mem_range] at hl; omega
      by_cases h0 : l=0 <;> simp [h0, hk]
    _ = _ := by simp only [Finset.sum_add_distrib]; simp

/-- The canonical complement Fourier run coefficients equal the stated discrete Fourier
transform of exponentiated half spectrum log data. -/
theorem canonicalComplementFourierRun_coefficients (P : Polynomial ℂ) (d m : ℕ)
    (n : Fin (2^m)) :
    let N : ℕ := 2^m
    let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
    let a := fun k : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ)*ω^(-(k*j.val : ℤ))
    (canonicalComplementFourierRun P d m).coefficients n =
      (N : ℂ)⁻¹ * ∑ j : Fin N,
        Complex.exp ((2 : ℂ)⁻¹*a 0 +
          ∑ l ∈ Finset.range (N/2+1), if l=0 then 0 else a l*ω^(l*j.val))*
          ω^(-(n.val*j.val : ℤ)) := by
  (try dsimp only)
  let ω := Complex.exp ((2*Real.pi/(2^m : ℝ) : ℝ)*Complex.I)
  let samples := fun j : Fin (2^m) =>
    ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ)
  let a := fun k : ℕ => (2^m : ℂ)⁻¹*∑ j : Fin (2^m),
    samples j*ω^(-(k*j.val : ℤ))
  have ha (k : Fin (2^m)) :
      (radixTwoNormalisedFourier m samples).1 k = a k.val := by
    change (2^m : ℂ)⁻¹*(radixTwoFourier m samples).1 k = _
    rw [radixTwoFourier_root_semantics]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rfl
  change (2^m : ℂ)⁻¹*(radixTwoFourier m _).1 n = _
  rw [radixTwoFourier_root_semantics]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  rw [radixTwoPositiveFourier_root_semantics]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  change (∑ l : Fin (2^m),
    (if l.val=0 then (2 : ℂ)⁻¹*(radixTwoNormalisedFourier m samples).1 l
      else if l.val ≤ 2^m/2 then (radixTwoNormalisedFourier m samples).1 l else 0)*
        ω^(j.val*l.val)) =
    (2 : ℂ)⁻¹*a 0 + ∑ l ∈ Finset.range (2^m/2+1),
      if l=0 then 0 else a l*ω^(l*j.val)
  simp_rw [ha]
  simpa only [mul_comm j.val] using! sum_half_spectrum (2^m) (by positivity) a ω j.val

def canonicalComplementFourierPolynomial (P : Polynomial ℂ) (d m : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (d+1), Polynomial.monomial n
    ((canonicalComplementFourierRun P d m).coefficients
      ⟨n % 2^m, Nat.mod_lt _ (by positivity)⟩)

/-- The canonical complement Fourier polynomial has natural degree at most `d`. -/
theorem canonicalComplementFourierPolynomial_natDegree (P : Polynomial ℂ) (d m : ℕ) :
    (canonicalComplementFourierPolynomial P d m).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_monomial_le _).trans (by
    simp only [Finset.mem_range] at hn; omega)

/-- Each coefficient through degree `d` of the Fourier polynomial equals the corresponding run
coefficient indexed modulo the grid size. -/
theorem canonicalComplementFourierPolynomial_coeff (P : Polynomial ℂ) (d m n : ℕ)
    (hn : n ≤ d) :
    (canonicalComplementFourierPolynomial P d m).coeff n =
      (canonicalComplementFourierRun P d m).coefficients
        ⟨n % 2^m, Nat.mod_lt _ (by positivity)⟩ := by
  simp [canonicalComplementFourierPolynomial, Polynomial.coeff_monomial, hn]

/-- A grid sum truncated at degree `d` equals the corresponding finite sum over natural
coefficient indices when `d` is smaller than the grid size. -/
private theorem sum_truncated_spectrum (N : ℕ) (hN : 0 < N) (d : ℕ)
    (hd : d < N) (a : Fin N → ℂ) (ω : ℂ) (j : ℕ) :
    (∑ l : Fin N, (if l.val ≤ d then a l else 0)*ω^(j*l.val)) =
      ∑ l ∈ Finset.range (d+1),
        a ⟨l % N, Nat.mod_lt _ hN⟩*ω^(l*j) := by
  calc
    _ = ∑ l : Fin N, (if l.val ≤ d then
          a ⟨l.val % N, Nat.mod_lt _ hN⟩ else 0)*ω^(l.val*j) := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [Nat.mod_eq_of_lt l.isLt, Fin.eta, mul_comm j]
    _ = ∑ l ∈ Finset.range N,
        (if l ≤ d then a ⟨l % N, Nat.mod_lt _ hN⟩ else 0)*ω^(l*j) :=
      Fin.sum_univ_eq_sum_range (fun l : ℕ =>
        (if l ≤ d then a ⟨l % N, Nat.mod_lt _ hN⟩ else 0)*ω^(l*j)) N
    _ = ∑ l ∈ Finset.range (d+1),
        (if l ≤ d then a ⟨l % N, Nat.mod_lt _ hN⟩ else 0)*ω^(l*j) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro l _ hl
      have hl' : ¬l ≤ d := by simp only [Finset.mem_range] at hl; omega
      simp [hl']
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hl' : l ≤ d := by simp only [Finset.mem_range] at hl; omega
      simp only [ite_eq_left hl']

/-- When the grid has at least `d+1` points, the run grid values are evaluations of the Fourier
polynomial at the grid roots. -/
theorem canonicalComplementFourierRun_gridValues (P : Polynomial ℂ) (d m : ℕ)
    (hd : d+1 ≤ 2^m) (j : Fin (2^m)) :
    let ω := Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I)
    (canonicalComplementFourierRun P d m).gridValues j =
      (canonicalComplementFourierPolynomial P d m).eval (ω^j.val) := by
  (try dsimp only)
  change (radixTwoPositiveFourier m
    (fun l => if l.val ≤ d then (canonicalComplementFourierRun P d m).coefficients l
      else 0)).1 j = _
  rw [radixTwoPositiveFourier_root_semantics]
  rw [sum_truncated_spectrum (2^m) (by positivity) d (by omega)]
  simp only [canonicalComplementFourierPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [← pow_mul, Nat.mul_comm n]

/-- Approximating the downscaled complement coefficients within `ε/(16*(d+1))` gives residual
and circle completion unitarity defect below `ε` for the original input polynomial. -/
theorem canonicalComplement_downscale_coefficient_consumer (P₀ Q Q' : Polynomial ℂ) (d : ℕ) (ε : ℝ)
    (hQd : Q.natDegree ≤ d) (hQ'd : Q'.natDegree ≤ d)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1)
    (hc : ∀ z : ℂ, ‖z‖ = 1 →
      ‖((((1-ε/4 : ℝ) : ℂ) • P₀).eval z)‖^2+‖Q.eval z‖^2 = 1)
    (hcoeff : ∀ n : ℕ, n ≤ d → ‖Q.coeff n-Q'.coeff n‖ ≤ ε/(16*(d+1))) :
    (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q' z < ε) ∧
    (∀ z : ℂ, ‖z‖ = 1 →
      ‖(circleCompletion P₀ Q' z)ᴴ*circleCompletion P₀ Q' z-1‖ < ε) := by
  let P : Polynomial ℂ := ((1-ε/4 : ℝ) : ℂ) • P₀
  have hden : (0 : ℝ) < (d+1) := by positivity
  have hQsum : (∑ n ∈ Q.support ∪ Q'.support, ‖Q.coeff n-Q'.coeff n‖) ≤ ε/16 := by
    have hsub : Q.support ∪ Q'.support ⊆ Finset.range (d+1) := by
      intro n hn
      rcases Finset.mem_union.mp hn with hn | hn
      · exact Finset.mem_range.mpr (by have := (le_natDegree_of_mem_supp n hn).trans hQd; omega)
      · exact Finset.mem_range.mpr (by have := (le_natDegree_of_mem_supp n hn).trans hQ'd; omega)
    calc
      _ ≤ ∑ n ∈ Finset.range (d+1), ‖Q.coeff n-Q'.coeff n‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ _n ∈ Finset.range (d+1), ε/(16*(d+1)) :=
        Finset.sum_le_sum (fun n hn => hcoeff n (by simp only [Finset.mem_range] at hn; omega))
      _ = ε/16 := by simp; field_simp
  have hres (z : ℂ) (hz : ‖z‖ = 1) : circleResidual P₀ Q' z < ε := by
    have hb := circle_complement_coefficient_residual_certificate P Q P Q' (ε/16)
      (by positivity) (by simp; positivity) hQsum hc z hz
    have hscale : ‖P.eval z‖ = (1-ε/4)*‖P₀.eval z‖ := by
      simp only [P, Polynomial.eval_smul, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1-ε/4)]
    have hnorm : ‖P₀.eval z‖^2 ≤ 1 := by
      nlinarith [hP z hz, norm_nonneg (P₀.eval z)]
    have hf0 : 0 ≤ 1-(1-ε/4)^2 := by
      nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ 1-ε/4) (by linarith : 1-ε/4 ≤ 1)]
    have hf1 : 1-(1-ε/4)^2 ≤ ε/2 := by nlinarith [sq_nonneg ε]
    have hgap : |‖P₀.eval z‖^2-‖P.eval z‖^2| ≤ ε/2 := by
      have he : ‖P₀.eval z‖^2-‖P.eval z‖^2 =
          (1-(1-ε/4)^2)*‖P₀.eval z‖^2 := by rw [hscale]; ring
      rw [he, abs_of_nonneg (mul_nonneg hf0 (sq_nonneg _))]
      simpa only [mul_one] using! mul_le_mul hf1 hnorm (sq_nonneg _) (by positivity : 0 ≤ ε/2)
    calc
      _ = |(‖P.eval z‖^2+‖Q'.eval z‖^2-1)+(‖P₀.eval z‖^2-‖P.eval z‖^2)| := by
        change |‖P₀.eval z‖^2+‖Q'.eval z‖^2-1| = _
        congr 1
        ring
      _ ≤ |‖P.eval z‖^2+‖Q'.eval z‖^2-1|+|‖P₀.eval z‖^2-‖P.eval z‖^2| := abs_add_le _ _
      _ ≤ 4*(ε/16)+2*(ε/16)^2+ε/2 := add_le_add hb hgap
      _ < ε := by nlinarith [mul_lt_mul_of_pos_left hε1 hε]
  refine ⟨hres, ?_⟩
  intro z hz
  rw [circleCompletion_unitarity_defect_eq_residual]
  exact hres z hz

/-- Under the stated grid threshold, the downscaled Fourier construction has degree at most `d`
and uniform residual and unitarity defect below `ε`. -/
theorem scaled_complement_same_fft_uniform_residual :
∀ (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ), 0 < d → P₀.natDegree ≤ d →
      0 < ε → ε < 1 → (∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1) →
      let P := (1-ε/4 : ℂ) • P₀
      let N := 2^m
      let δ := ε/4
      let η := ε/(16*(d+1))
      let ρ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
      1 ≤ m → d+1 ≤ N →
      (Nat.ceil (2/Real.log ρ * Real.log (8*Real.log (1/δ)/(ρ-1)/η)) : ℕ) ≤ N →
      let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ) * Complex.I)
      let a := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
        ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(n*j.val : ℤ))
      let q := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
        Complex.exp ((2 : ℂ)⁻¹*a 0 +
          ∑ l ∈ Finset.range (N/2+1), if l=0 then 0 else a l*ω^(l*j.val)) *
          ω^(-(n*j.val : ℤ))
      let Q := ∑ n ∈ Finset.range (d+1), Polynomial.monomial n (q n)
      Q.natDegree ≤ d ∧
      (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q z < ε) ∧
      (∀ z : ℂ, ‖z‖ = 1 →
        ‖(circleCompletion P₀ Q z)ᴴ*circleCompletion P₀ Q z-1‖ < ε) := by
  intro P₀ d m ε hd hPd hε hε1 hP₀
  (try dsimp only)
  intro hm hgrid hthreshold
  let P : Polynomial ℂ := (1-ε/4 : ℂ) • P₀
  let N := 2^m
  let δ : ℝ := ε/4
  let η : ℝ := ε/(16*(d+1))
  let ρ : ℝ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
  let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
  let a := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
    ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(n*j.val : ℤ))
  let q := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
    Complex.exp ((2 : ℂ)⁻¹*a 0 +
      ∑ l ∈ Finset.range (N/2+1), if l=0 then 0 else a l*ω^(l*j.val)) * ω^(-(n*j.val : ℤ))
  let Q' : Polynomial ℂ := ∑ n ∈ Finset.range (d+1), Polynomial.monomial n (q n)
  change Q'.natDegree ≤ d ∧
    (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q' z < ε) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ‖(circleCompletion P₀ Q' z)ᴴ*circleCompletion P₀ Q' z-1‖ < ε)
  have hscalar : (1-ε/4 : ℂ) = ((1-ε/4 : ℝ) : ℂ) := by push_cast; rfl
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hη1 : η < 1 := by
    dsimp [η]
    rw [div_lt_one (by positivity)]
    nlinarith
  have hPdeg : P.natDegree ≤ d := (Polynomial.natDegree_smul_le _ _).trans hPd
  have hP (z : ℂ) (hz : ‖z‖ = 1) : ‖P.eval z‖ ≤ 1-δ := by
    dsimp only [P]
    rw [hscalar, Polynomial.eval_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1-ε/4)]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hP₀ z hz)
      (by linarith : 0 ≤ 1-ε/4)
  obtain ⟨Q, hQd, hQr, hQi, hQn, hQc, _⟩ :=
    canonical_complement_schwarz_representation P d δ hPdeg hδ hδ1 hP
  have hbase : 1 < (1/(1-δ) : ℝ) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1-δ)]
    linarith
  have hρ : 1 < ρ := Real.one_lt_rpow hbase (by positivity)
  have hρbase : ρ ≤ 1/(1-δ) := by
    calc
      _ ≤ (1/(1-δ) : ℝ)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase.le (by rw [div_le_one (by positivity)]; exact hdreal)
      _ = _ := Real.rpow_one _
  have hρ2 : ρ < 2 := hρbase.trans_lt (by
    rw [div_lt_iff₀ (by linarith : 0 < 1-δ)]
    dsimp [δ]
    linarith)
  have hlog : 1-δ ≤ Real.log (1/δ) := by
    simpa only [one_div, inv_inv] using! Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδ)
  have harg : 2 ≤ 8*Real.log (1/δ)/(ρ-1)/η := by
    rw [le_div_iff₀ hη, le_div_iff₀ (by linarith : 0 < ρ-1)]
    have hprod : η*(ρ-1) < 1 := by
      have hh := mul_lt_mul_of_pos_left (by linarith : ρ-1 < 1) hη
      nlinarith
    have hδquarter : δ < 1/4 := by dsimp [δ]; linarith
    nlinarith
  have hnew : (Nat.ceil (2/Real.log (min 2 ρ) *
      Real.log (max 2 (8*Real.log (1/δ)/(min 2 ρ-1)/η))) : ℕ) ≤ N := by
    rw [min_eq_right hρ2.le, max_eq_right harg]
    exact hthreshold
  have hacc := canonical_complement_discrete_fourier_accuracy P Q d m δ η hd hPdeg hQd
    hδ hδ1 hη hη1 hP hQr hQi hQn hQc hm hgrid hnew
  have hsame : Q' = canonicalComplementFourierPolynomial P d m := by
    dsimp only [Q', canonicalComplementFourierPolynomial]
    apply Finset.sum_congr rfl
    intro n hn
    apply congrArg (Polynomial.monomial n)
    have hnn : n < 2^m := by have := Finset.mem_range.mp hn; omega
    have hh := canonicalComplementFourierRun_coefficients P d m
      ⟨n % 2^m, Nat.mod_lt _ (by positivity)⟩
    simpa only [Nat.mod_eq_of_lt hnn] using! hh.symm
  have hQ'd : Q'.natDegree ≤ d := by
    rw [hsame]; exact canonicalComplementFourierPolynomial_natDegree P d m
  have hcoef (n : ℕ) (hn : n ≤ d) : Q'.coeff n = q n := by
    simp [Q', Polynomial.coeff_monomial, hn]
  refine ⟨hQ'd, ?_⟩
  apply canonicalComplement_downscale_coefficient_consumer P₀ Q Q' d ε hQd hQ'd hε hε1 hP₀
  · simpa only [P, hscalar] using! hQc
  · intro n hn
    rw [hcoef n hn]
    exact (hacc n hn).le

structure CanonicalComplementAlgorithmTwoRun (m : ℕ) where
  coefficients : Fin (2^m) → ℂ
  gridValues : Fin (2^m) → ℂ
  multiplications : ℕ
  additions : ℕ
  logarithms : ℕ
  exponentials : ℕ

noncomputable def canonicalComplementAlgorithmTwoRun (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    CanonicalComplementAlgorithmTwoRun m :=
  let scaled : Fin (2^m) → ℂ := fun l =>
    if l.val ≤ d then ((1-ε/4 : ℝ) : ℂ) * P₀.coeff l.val else 0
  let first := radixTwoPositiveFourier m scaled
  let second := radixTwoNormalisedFourier m
    (fun j => ((Real.log (1-‖first.1 j‖^2) : ℝ) : ℂ))
  let third := radixTwoPositiveFourier m
    (fun j => if j.val = 0 then (2 : ℂ)⁻¹*second.1 j
      else if j.val ≤ 2^m/2 then second.1 j else 0)
  let fourth := radixTwoNormalisedFourier m (fun j => Complex.exp (third.1 j))
  let fifth := radixTwoPositiveFourier m
    (fun j => if j.val ≤ d then fourth.1 j else 0)
  ⟨fourth.1, fifth.1,
    first.2.1+second.2.1+third.2.1+fourth.2.1+fifth.2.1+1+(d+1),
    first.2.2+second.2.2+third.2.2+fourth.2.2+fifth.2.2, 2^m, 2^m⟩

/-- Gives the exact multiplication, addition, logarithm, and exponential counts for Algorithm 2. -/
theorem canonicalComplementAlgorithmTwoRun_cost (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications =
      5*(m*2^m/2)+2*2^m+1+(d+1) ∧
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).additions = 5*m*2^m ∧
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).logarithms = 2^m ∧
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).exponentials = 2^m := by
  unfold canonicalComplementAlgorithmTwoRun
  simp only [radixTwoNormalisedFourier_semantics_cost,
    radixTwoPositiveFourier_semantics_cost]
  constructor
  · ring
  constructor
  · ring
  trivial

/-- On a grid with at least `d+1` points, Algorithm 2 has the stated exact multiplication,
addition, logarithm, and exponential counts. -/
theorem canonicalComplementAlgorithmTwoRun_cost_of_valid_grid
    (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    d+1 ≤ 2^m →
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications =
        5*(m*2^m/2)+2*2^m+1+(d+1) ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).additions = 5*m*2^m ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).logarithms = 2^m ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).exponentials = 2^m := by
  intro _
  exact canonicalComplementAlgorithmTwoRun_cost P₀ d m ε

/-- The natural logarithm of two lies between one half and one. -/
private theorem log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (x := (2:ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  · rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
    have h := Real.add_one_le_exp (1:ℝ)
    linarith

set_option maxHeartbeats 800000 in

/-- For positive `d` and tolerance between zero and one, the Fourier grid threshold is at most
`128*(d/ε)*(1+Real.log (d/ε))`. -/
theorem canonical_complement_fft_threshold_bound :
    ∀ (d : ℕ) (ε : ℝ), 0 < d → 0 < ε → ε < 1 →
      let δ : ℝ := ε/4
      let η : ℝ := ε/(16*(d+1))
      let ρ : ℝ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
      2/Real.log ρ * Real.log (8*Real.log (1/δ)/(ρ-1)/η) ≤
        128*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε)) := by
  intro d ε hd hε hε1
  (try dsimp only)
  set δ : ℝ := ε/4 with hδ
  set η : ℝ := ε/(16*(d+1)) with hη
  set ρ : ℝ := (1/(1-δ))^(1/(d : ℝ) : ℝ) with hρ
  set D : ℝ := (d : ℝ)/ε with hD
  set L : ℝ := 1 + Real.log D with hL
  set X : ℝ := 8*Real.log (1/δ)/(ρ-1)/η with hX
  have : NeZero (ε:ℝ) := ⟨by linarith⟩
  have hdreal : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdposR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hDpos : (0:ℝ) < D := by rw [hD]; positivity
  have hD1 : (1:ℝ) ≤ D := by rw [hD]; exact (le_div_iff₀ hε).2 (by linarith)
  have hlogD : (0:ℝ) ≤ Real.log D := Real.log_nonneg hD1
  have hL1 : (1:ℝ) ≤ L := by rw [hL]; linarith
  have hδpos : (0:ℝ) < δ := by rw [hδ]; linarith
  have hηpos : (0:ℝ) < η := by rw [hη]; positivity
  have hApos : (0:ℝ) < 1/(1-δ) := by
    rw [hδ]
    have : (0:ℝ) < 1-ε/4 := by linarith
    positivity
  have hA1 : (1:ℝ) < 1/(1-δ) := by
    have h1δ : (0:ℝ) < 1-δ := by rw [hδ]; linarith
    rw [lt_div_iff₀ h1δ]
    linarith
  have hρ1 : (1:ℝ) < ρ := by
    rw [hρ]
    exact Real.one_lt_rpow hA1 (by positivity)
  have hlogρpos : (0:ℝ) < Real.log ρ := by rw [hρ]; exact Real.log_pos hρ1
  have hrhompos : (0:ℝ) < ρ-1 := by linarith
  have hbase : (δ:ℝ) ≤ Real.log (1/(1-δ)) := by
    have hq : (0:ℝ) < 1-δ := by rw [hδ]; linarith
    have : NeZero (1-δ:ℝ) := ⟨by linarith⟩
    have h1 := Real.log_le_sub_one_of_pos hq
    have h2 : Real.log (1/(1-δ)) = -Real.log (1-δ) := by
      rw [one_div, Real.log_inv (1-δ)]
    linarith
  have hlogρD : ((1/(4*D):ℝ)) ≤ Real.log ρ := by
    have hmul := mul_le_mul_of_nonneg_left hbase hdposR.le
    have hmul' : (δ:ℝ) ≤ Real.log (1/(1-δ)) := by
      calc (δ:ℝ) = (d:ℝ)⁻¹ * ((d:ℝ) * δ) := by field_simp
        _ ≤ (d:ℝ)⁻¹ * ((d:ℝ) * Real.log (1/(1-δ))) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = Real.log (1/(1-δ)) := by field_simp
    have hkey : (1/(d:ℝ) : ℝ) * (δ:ℝ) = 1/(4*D) := by
      rw [hδ, hD]
      field_simp
    rw [hρ, Real.log_rpow hApos]
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left hmul' (by positivity)
  have hρm1 : Real.log ρ ≤ ρ-1 := by
    have h1 := Real.add_one_le_exp (Real.log ρ)
    have h2 : Real.exp (Real.log ρ) = ρ := Real.exp_log (by linarith)
    linarith
  have htwo : (2/Real.log ρ:ℝ) ≤ 8*D := by
    have h1 : (2/Real.log ρ:ℝ) ≤ 2/(1/(4*D)) := by
      rw [div_le_div_iff₀ hlogρpos (by positivity : (0:ℝ) < 1/(4*D))]
      nlinarith [hlogρD]
    have h2 : (2/(1/(4*D)) : ℝ) = 8*D := by field_simp; ring
    linarith
  have hinvρD : ((1/(ρ-1):ℝ) : ℝ) ≤ 4*D := by
    calc
      (1/(ρ-1):ℝ) ≤ 1/Real.log ρ := by
        rw [div_le_div_iff₀ hrhompos hlogρpos]
        nlinarith
      _ ≤ 4*D := by
        rw [div_le_iff₀ hlogρpos]
        have hk : (1:ℝ) ≤ 4*D * Real.log ρ := by
          have hstep := (div_le_iff₀ (by positivity : (0:ℝ) < 4*D)).mp hlogρD
          rw [show Real.log ρ * (4*D) = 4*D * Real.log ρ by ring] at hstep
          exact hstep
        exact hk
  have hy0 : (0:ℝ) ≤ Real.log (1/ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    linarith
  have hlog1δpos : (0:ℝ) < Real.log (1/δ) := by
    have h1 : (1:ℝ) < 1/δ := by rw [lt_div_iff₀ hδpos]; linarith
    exact Real.log_pos h1
  have hlog1δ : (Real.log (1/δ):ℝ) ≤ 2 + Real.log (1/ε) := by
    have h1 : (1/δ:ℝ) = 4/ε := by rw [hδ]; field_simp
    have h3 : Real.log (4/ε) = Real.log 4 + Real.log (1/ε) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by positivity : (1/ε:ℝ) ≠ 0)]
      field_simp
    have h4 : (Real.log 4:ℝ) ≤ 2 := by
      have h5 : Real.log 4 = 2 * Real.log 2 := by
        calc Real.log 4 = Real.log (2*2) := by norm_num
          _ = Real.log 2 + Real.log 2 := by
            rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
          _ = 2 * Real.log 2 := by ring
      linarith [log_two_bounds.2]
    rw [h1, h3]
    linarith
  have hlog1εD : (Real.log (1/ε):ℝ) ≤ Real.log D := by
    have h1 : (0:ℝ) < 1/ε := by positivity
    have h2 : (1/ε:ℝ) ≤ D := by
      rw [hD, div_le_div_iff₀ hε hε]
      nlinarith [hdreal]
    rw [hD]
    exact Real.log_le_log h1 h2
  have hinvηD : ((1/η:ℝ) : ℝ) ≤ 32*D := by
    have hk : (16*(d+1):ℕ) ≤ 32*d := by omega
    have hk' : ((16*(d+1):ℕ) : ℝ) ≤ 32*(d:ℝ) := by exact_mod_cast hk
    calc
      (1/η:ℝ) = ((16*(d+1):ℕ) : ℝ)/ε := by
        rw [hη, one_div, inv_div, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
      _ ≤ (32*(d:ℝ) : ℝ)/ε := by
        rw [div_le_div_iff₀ hε hε]
        nlinarith
      _ = 32*D := by rw [hD]; ring
  have hXpos : (0:ℝ) < X := by rw [hX]; positivity
  have hXbound : (X:ℝ) ≤ 1024 * (D^2 * (2 + Real.log (1/ε))) := by
    rw [hX]
    have h1R : (1:ℝ) ≤ 4*D*(ρ-1) := (div_le_iff₀ hrhompos).1 hinvρD
    have hηD : (1:ℝ) ≤ 32*D*η := (div_le_iff₀ hηpos).1 hinvηD
    have h1 : (8*Real.log (1/δ)/(ρ-1) : ℝ) ≤ 8*(2+Real.log (1/ε))*(4*D) := by
      rw [div_le_iff₀ hrhompos]
      nlinarith
    have h2 : (8*Real.log (1/δ)/(ρ-1)/η : ℝ) ≤ 8*(2+Real.log (1/ε))*(4*D)*(32*D) := by
      rw [div_le_iff₀ hηpos]
      calc 8*Real.log (1/δ)/(ρ-1) ≤ 8*(2+Real.log (1/ε))*(4*D) := h1
        _ ≤ (8*(2+Real.log (1/ε))*(4*D)) * (32*D*η) := by
          have hnonneg : (0:ℝ) ≤ 8*(2+Real.log (1/ε))*(4*D) := by positivity
          have hstep := mul_le_mul_of_nonneg_left hηD hnonneg
          linarith
        _ = 8*(2+Real.log (1/ε))*(4*D)*(32*D)*η := by ring
    convert! h2 using 1; ring

  have hlogX : (Real.log X:ℝ) ≤ 14*L := by
    have h1 : (Real.log X:ℝ) ≤ Real.log 1024 + 2*Real.log D + Real.log (2 + Real.log (1/ε)) := by
      have hb := Real.log_le_log hXpos hXbound
      have heq : Real.log (1024 * (D^2 * (2 + Real.log (1/ε))))
          = Real.log 1024 + 2*Real.log D + Real.log (2 + Real.log (1/ε)) := by
        rw [Real.log_mul (x := (1024:ℝ)) (y := D^2 * (2 + Real.log (1/ε)))
          (by norm_num) (by positivity),
          Real.log_mul (x := D^2) (y := 2 + Real.log (1/ε))
          (by positivity) (by positivity),
          Real.log_pow D 2]
        ring
      rw [heq] at hb
      exact hb
    have h1024 : (Real.log 1024:ℝ) ≤ 10 := by
      have h' : Real.log 1024 = 10 * Real.log 2 := by
        rw [show (1024:ℝ) = 2^10 by norm_num, Real.log_pow 2 10]
        norm_num
      linarith [log_two_bounds.2]
    have hlog2y : (Real.log (2+Real.log (1/ε)):ℝ) ≤ 1 + Real.log (1/ε) := by
      have h1 : (0:ℝ) < 2+Real.log (1/ε) := by linarith
      have h2 : (2+Real.log (1/ε):ℝ) ≤ 2*(1+Real.log (1/ε)) := by
        have hy : (0:ℝ) ≤ Real.log (1/ε) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ hε]
          linarith
        linarith
      have h3 := Real.log_le_log h1 h2
      rw [Real.log_mul (x := (2:ℝ)) (y := 1 + Real.log (1/ε)) (by norm_num) (by positivity)] at h3
      have h4 : (Real.log (1+Real.log (1/ε)):ℝ) ≤ Real.log (1/ε) := by
        have h5 := Real.log_le_sub_one_of_pos (x := 1 + Real.log (1/ε)) (by linarith)
        linarith
      linarith [log_two_bounds.2]
    linarith
  calc
    2/Real.log ρ * Real.log X ≤ 2/Real.log ρ * (14*L) := by
      exact mul_le_mul_of_nonneg_left hlogX (by positivity)
    _ ≤ (8*D) * (14*L) := by
      exact mul_le_mul_of_nonneg_right htwo (by linarith)
    _ ≤ 128*D*L := by nlinarith

/-- The positive Fourier transform of the padded downscaled input coefficients gives the
downscaled polynomial values at the grid roots. -/
private theorem algorithm_two_input_fft (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ)
    (hp : P₀.natDegree ≤ d) (hN : d+1 ≤ 2^m) (j : Fin (2^m)) :
    (radixTwoPositiveFourier m (fun l : Fin (2^m)=>
      if l.val ≤ d then ((1-ε/4 : ℝ) : ℂ)*P₀.coeff l.val else 0)).1 j=
      ((((1-ε/4 : ℝ) : ℂ) • P₀).eval
        ((Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I))^j.val)) := by
  let c : ℂ:=((1-ε/4 : ℝ) : ℂ)
  let ω : ℂ:=Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I)
  have hmask (l : Fin (2^m)) : (if l.val ≤ d then c*P₀.coeff l.val else 0)=c*P₀.coeff l.val := by
    split_ifs with hl
    · rfl
    · have hz : P₀.coeff l.val=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hz]
  rw [radixTwoPositiveFourier_root_semantics]
  change (∑ l : Fin (2^m),(if l.val ≤ d then c*P₀.coeff l.val else 0)*ω^(j.val*l.val))=(c • P₀).eval (ω^j.val)
  simp_rw [hmask]
  rw [Polynomial.eval_smul,Polynomial.eval_eq_sum_range' (show P₀.natDegree < 2^m by omega)]
  simp only [smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ=>c*P₀.coeff l*ω^(j.val*l)) (2^m),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_mul]
  ring

/-- On a sufficiently large grid, Algorithm 2 coefficients equal those of the canonical Fourier
run on the downscaled polynomial. -/
theorem canonicalComplementAlgorithmTwoRun_coefficients_corrected (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ)
    (hp : P₀.natDegree ≤ d) (hN : d+1 ≤ 2^m) (n : Fin (2^m)) :
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).coefficients n=
      (canonicalComplementFourierRun (((1-ε/4 : ℝ) : ℂ) • P₀) d m).coefficients n := by
  have hs : (radixTwoPositiveFourier m (fun l : Fin (2^m)=>
      if l.val ≤ d then ((1-ε/4 : ℝ) : ℂ)*P₀.coeff l.val else 0)).1=
      fun j=>(((1-ε/4 : ℝ) : ℂ) • P₀).eval
        ((Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I))^j.val) :=
    funext (algorithm_two_input_fft P₀ d m ε hp hN)
  unfold canonicalComplementAlgorithmTwoRun canonicalComplementFourierRun
  (try dsimp only)
  rw [hs]

/-- On a sufficiently large grid, Algorithm 2 grid values equal evaluations of the canonical
Fourier polynomial for the downscaled input. -/
theorem canonicalComplementAlgorithmTwoRun_gridValues_corrected (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ)
    (hp : P₀.natDegree ≤ d) (hN : d+1 ≤ 2^m) (j : Fin (2^m)) :
    (canonicalComplementAlgorithmTwoRun P₀ d m ε).gridValues j=
      (canonicalComplementFourierPolynomial (((1-ε/4 : ℝ) : ℂ) • P₀) d m).eval
        ((Complex.exp ((2*Real.pi/(2^m : ℕ) : ℝ)*Complex.I))^j.val) := by
  have hc : (canonicalComplementAlgorithmTwoRun P₀ d m ε).coefficients=
      (canonicalComplementFourierRun (((1-ε/4 : ℝ) : ℂ) • P₀) d m).coefficients :=
    funext (canonicalComplementAlgorithmTwoRun_coefficients_corrected P₀ d m ε hp hN)
  change (radixTwoPositiveFourier m (fun l=>if l.val ≤ d then
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).coefficients l else 0)).1 j=_
  rw [hc]
  exact canonicalComplementFourierRun_gridValues _ d m hN j

/-- Every positive natural number is covered by a power of two at most twice that number. -/
private theorem algorithm_two_power_cover (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ,n ≤ 2^m ∧ 2^m ≤ 2*n := by
  have hex : ∃ m : ℕ,n ≤ 2^m := ⟨n,Nat.lt_two_pow_self.le⟩
  let m:=Nat.find hex
  refine ⟨m,Nat.find_spec hex,?_⟩
  by_cases hm : m=0
  · simp only [hm,pow_zero]
    omega
  · obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hm
    have hp : ¬n ≤ 2^k := Nat.find_min hex (by change k < m;omega)
    rw [hk,pow_succ]
    omega

/-- On a sufficiently large grid, the polynomial reconstructed from Algorithm 2 coefficients
equals the canonical Fourier polynomial of the downscaled input. -/
private theorem algorithm_two_poly (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ)
    (hp : P₀.natDegree ≤ d) (hN : d+1 ≤ 2^m) :
    (∑ n ∈ Finset.range (d+1),Polynomial.monomial n
      ((canonicalComplementAlgorithmTwoRun P₀ d m ε).coefficients
        ⟨n % 2^m,Nat.mod_lt _ (by positivity)⟩))=
      canonicalComplementFourierPolynomial (((1-ε/4 : ℝ) : ℂ) • P₀) d m := by
  unfold canonicalComplementFourierPolynomial
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (Polynomial.monomial n)
    (canonicalComplementAlgorithmTwoRun_coefficients_corrected P₀ d m ε hp hN _)

/-- Under the stated input and grid assumptions, Algorithm 2 produces a degree bounded
complement with residual and circle completion unitarity defect below `ε`. -/
private theorem algorithm_two_accuracy (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ)
    (hd : 0 < d) (hp : P₀.natDegree ≤ d) (hε : 0 < ε) (hε1 : ε < 1)
    (hP : ∀ z : ℂ,‖z‖=1 → ‖P₀.eval z‖ ≤ 1) (hm : 1 ≤ m) (hN : d+1 ≤ 2^m)
    (ht : (Nat.ceil (2/Real.log ((1/(1-ε/4))^(1/(d : ℝ) : ℝ))*
      Real.log (8*Real.log (1/(ε/4))/((1/(1-ε/4))^(1/(d : ℝ) : ℝ)-1)/(ε/(16*(d+1))))) : ℕ) ≤ 2^m) :
    let Q:=canonicalComplementFourierPolynomial (((1-ε/4 : ℝ) : ℂ) • P₀) d m
    Q.natDegree ≤ d ∧ (∀ z : ℂ,‖z‖=1 → circleResidual P₀ Q z < ε) ∧
      (∀ z : ℂ,‖z‖=1 → ‖(circleCompletion P₀ Q z)ᴴ*circleCompletion P₀ Q z-1‖ < ε) := by
  let P : Polynomial ℂ:=((1-ε/4 : ℝ) : ℂ) • P₀
  let N:=2^m
  let ω:=Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
  let a:=fun n : ℕ=>(N : ℂ)⁻¹*∑ j : Fin N,
    ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ)*ω^(-(n*j.val : ℤ))
  let q:=fun n : ℕ=>(N : ℂ)⁻¹*∑ j : Fin N,
    Complex.exp ((2 : ℂ)⁻¹*a 0+∑ l∈Finset.range (N/2+1),if l=0 then 0 else a l*ω^(l*j.val))*
      ω^(-(n*j.val : ℤ))
  have hscalar : (1-ε/4 : ℂ)=((1-ε/4 : ℝ) : ℂ) := by push_cast;rfl
  have hb:=scaled_complement_same_fft_uniform_residual P₀ d m ε hd hp hε hε1 hP hm hN ht
  simp only [hscalar] at hb
  change (∑ n∈Finset.range (d+1),Polynomial.monomial n (q n)).natDegree ≤ d ∧
    (∀ z : ℂ,‖z‖=1 → circleResidual P₀ (∑ n∈Finset.range (d+1),Polynomial.monomial n (q n)) z < ε) ∧
    (∀ z : ℂ,‖z‖=1 → ‖(circleCompletion P₀ (∑ n∈Finset.range (d+1),Polynomial.monomial n (q n)) z)ᴴ*
      circleCompletion P₀ (∑ n∈Finset.range (d+1),Polynomial.monomial n (q n)) z-1‖ < ε) at hb
  have hsame : (∑ n∈Finset.range (d+1),Polynomial.monomial n (q n))=canonicalComplementFourierPolynomial P d m := by
    unfold canonicalComplementFourierPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    apply congrArg (Polynomial.monomial n)
    have hnN : n < 2^m := by have hh:=Finset.mem_range.mp hn;omega
    have he:=canonicalComplementFourierRun_coefficients P d m ⟨n % 2^m,Nat.mod_lt _ (by positivity)⟩
    simpa only [Nat.mod_eq_of_lt hnN] using! he.symm
  rw [hsame] at hb
  exact hb

set_option maxHeartbeats 1500000 in

/-- Algorithm 2 admits a grid and degree bounded approximate complement satisfying the stated
grid size, residual, unitarity defect, and total operation bounds. -/
theorem canonical_complement_algorithm_two_total_cost :
    ∀ (P₀ : Polynomial ℂ) (d : ℕ) (ε : ℝ), 0 < d → P₀.natDegree ≤ d →
      0 < ε → ε < 1 → (∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1) →
      ∃ (m : ℕ) (Q : Polynomial ℂ),
        1 ≤ m ∧ d+1 ≤ 2^m ∧ (2^m : ℝ) ≤ 512*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε)) ∧
        Q = canonicalComplementFourierPolynomial (((1-ε/4 : ℝ) : ℂ) • P₀) d m ∧
        Q.natDegree ≤ d ∧
        (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q z < ε) ∧
        (∀ z : ℂ, ‖z‖ = 1 →
          ‖(circleCompletion P₀ Q z)ᴴ*circleCompletion P₀ Q z-1‖ < ε) ∧
        (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications ≤
          32768*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε))^2 ∧
        (canonicalComplementAlgorithmTwoRun P₀ d m ε).additions ≤
          32768*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε))^2 ∧
        (canonicalComplementAlgorithmTwoRun P₀ d m ε).logarithms = 2^m ∧
        (canonicalComplementAlgorithmTwoRun P₀ d m ε).exponentials = 2^m := by
  intro P₀ d ε hd hp hε hε1 hP
  let D : ℝ:=(d : ℝ)/ε
  let L : ℝ:=1+Real.log D
  let U : ℝ:=128*D*L
  let n : ℕ:=d+1+Nat.ceil U
  have hDpos : 0 < D := by dsimp [D];positivity
  have hD1 : 1 ≤ D := by
    dsimp [D]
    rw [le_div_iff₀ hε]
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdD : (d : ℝ) ≤ D := by
    dsimp [D]
    rw [le_div_iff₀ hε]
    have hdr : (0 : ℝ) ≤ d := by positivity
    nlinarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hL1 : 1 ≤ L := by dsimp [L];linarith
  have hLpos : 0 < L := by linarith
  have hU0 : 0 ≤ U := by dsimp [U];positivity
  have hnpos : 0 < n := by dsimp [n];omega
  obtain ⟨m,hnm,hmn⟩:=algorithm_two_power_cover n hnpos
  have hgrid : d+1 ≤ 2^m := by dsimp [n] at hnm;omega
  have hm : 1 ≤ m := by
    by_contra hh
    have hm0 : m=0 := by omega
    simp only [hm0,pow_zero] at hgrid
    omega
  have hceil : ((Nat.ceil U : ℕ) : ℝ) ≤ U+1 := (Nat.ceil_lt_add_one hU0).le
  have hnreal : (n : ℝ) ≤ 131*D*L := by
    dsimp [n,U] at hceil ⊢
    push_cast
    have hDL : D ≤ D*L := by nlinarith
    nlinarith
  have hNupper : ((2^m : ℕ) : ℝ) ≤ 262*D*L := by
    have hh : ((2^m : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hmn
    nlinarith
  have hN512 : ((2^m : ℕ) : ℝ) ≤ 512*D*L := by nlinarith
  have hUle : U ≤ (n : ℝ) := by
    dsimp [n]
    push_cast
    have hc:=Nat.le_ceil U
    linarith
  have hthreshold :
      (Nat.ceil (2/Real.log ((1/(1-ε/4))^(1/(d : ℝ) : ℝ))*
        Real.log (8*Real.log (1/(ε/4))/((1/(1-ε/4))^(1/(d : ℝ) : ℝ)-1)/(ε/(16*(d+1))))) : ℕ) ≤ 2^m := by
    apply Nat.ceil_le.mpr
    have ht:=canonical_complement_fft_threshold_bound d ε hd hε hε1
    have hc : (n : ℝ) ≤ ((2^m : ℕ) : ℝ) := by exact_mod_cast hnm
    exact ht.trans (hUle.trans hc)
  have hNpos : (0 : ℝ) < ((2^m : ℕ) : ℝ) := by positivity
  have hlogN : Real.log (((2^m : ℕ) : ℝ))=(m : ℝ)*Real.log 2 := by
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have hlog262 : Real.log 262 ≤ (9 : ℝ) := by
    calc
      _ ≤ Real.log (2^9 : ℝ) := Real.log_le_log (by norm_num) (by norm_num)
      _ ≤ _ := by rw [Real.log_pow];norm_num;nlinarith only [log_two_bounds.2]
  have hlogL : Real.log L ≤ L-1 := Real.log_le_sub_one_of_pos hLpos
  have hlogupper:=Real.log_le_log hNpos hNupper
  rw [Real.log_mul (by positivity : (262 : ℝ)*D≠0) (ne_of_gt hLpos),
    Real.log_mul (by norm_num : (262 : ℝ)≠0) (ne_of_gt hDpos),hlogN] at hlogupper
  have hmreal : (m : ℝ) ≤ 22*L := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hlower : (m : ℝ)/2 ≤ (m : ℝ)*Real.log 2 := by nlinarith [log_two_bounds.1]
    have hLeq : L=1+Real.log D := rfl
    nlinarith
  let Q : Polynomial ℂ:=∑ k∈Finset.range (d+1),Polynomial.monomial k
    ((canonicalComplementAlgorithmTwoRun P₀ d m ε).coefficients ⟨k % 2^m,Nat.mod_lt _ (by positivity)⟩)
  have hQsame : Q=canonicalComplementFourierPolynomial (((1-ε/4 : ℝ) : ℂ) • P₀) d m :=
    algorithm_two_poly P₀ d m ε hp hgrid
  have hacc:=algorithm_two_accuracy P₀ d m ε hd hp hε hε1 hP hm hgrid hthreshold
  rw [← hQsame] at hacc
  have hc:=canonicalComplementAlgorithmTwoRun_cost_of_valid_grid P₀ d m ε hgrid
  have hadd : ((5*m*2^m : ℕ) : ℝ) ≤ 28820*D*L^2 := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    have hh:=mul_le_mul hmreal hNupper (by positivity : (0 : ℝ) ≤ ((2^m : ℕ) : ℝ))
        (by positivity : 0 ≤ 22*L)
    nlinarith only [hh]
  have hL2 : L ≤ L^2 := by nlinarith only [hL1]
  have hLsq : D*L ≤ D*L^2 := mul_le_mul_of_nonneg_left hL2 hDpos.le
  have hDsq : D ≤ D*L^2 := by
    have hs : (1 : ℝ) ≤ L^2 := by nlinarith only [hL1]
    simpa using! mul_le_mul_of_nonneg_left hs hDpos.le
  have hfloor : ((m*2^m/2 : ℕ) : ℝ) ≤ ((m*2^m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_le_self (m*2^m) 2)
  have hmult : ((5*(m*2^m/2)+2*2^m+1+(d+1) : ℕ) : ℝ) ≤ 32768*D*L^2 := by
    have hh : ((5*(m*2^m/2)+2*2^m+1+(d+1) : ℕ) : ℝ) ≤
        ((5*m*2^m : ℕ) : ℝ)+2*((2^m : ℕ) : ℝ)+1+((d+1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hfloor ⊢
      nlinarith only [hfloor]
    have hdr : ((d+1 : ℕ) : ℝ) ≤ 2*D := by push_cast;nlinarith
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hh hadd hNupper hdr ⊢
    nlinarith only [hh,hadd,hNupper,hdr,hD1,hLsq,hDsq]
  refine ⟨m,Q,hm,hgrid,(by simpa only [Nat.cast_pow,Nat.cast_ofNat] using! hN512),hQsame,hacc.1,hacc.2.1,hacc.2.2,?_,?_,hc.2.2.1,hc.2.2.2⟩
  · rw [hc.1]
    exact hmult
  · rw [hc.2.1]
    have hh : 28820*D*L^2 ≤ 32768*D*L^2 := by nlinarith
    exact hadd.trans hh

private def algorithm_two_counter_P : Polynomial ℂ:=C (1/200 : ℂ)+C (Complex.I/200)*X

/-- The counterexample polynomial evaluates to `(1+Complex.I*z)/200`. -/
private theorem algorithm_two_counter_eval (z : ℂ) : algorithm_two_counter_P.eval z=(1+Complex.I*z)/200 := by
  simp [algorithm_two_counter_P]
  ring

/-- The counterexample polynomial has natural degree at most one. -/
private theorem algorithm_two_counter_degree : algorithm_two_counter_P.natDegree ≤ 1 := by
  unfold algorithm_two_counter_P
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · exact (Polynomial.natDegree_mul_le).trans (by simp)

/-- The counterexample polynomial has unit circle modulus at most one hundredth. -/
private theorem algorithm_two_counter_margin :
    ∀ z : ℂ,‖z‖=1 → ‖algorithm_two_counter_P.eval z‖ ≤ 1-(99/100 : ℝ) := by
  intro z hz
  rw [algorithm_two_counter_eval,norm_div,show ‖(200 : ℂ)‖=(200 : ℝ) from by norm_num]
  have hn : ‖1+Complex.I*z‖ ≤ (2 : ℝ) := by
    calc
      _ ≤ ‖(1 : ℂ)‖+‖Complex.I*z‖ := norm_add_le _ _
      _ = _ := by norm_num [hz]
  exact (div_le_div_of_nonneg_right hn (by norm_num)).trans_eq (by norm_num)

/-- The counterexample polynomial vanishes at `Complex.I`, equals one hundredth at its negative,
and has equal squared moduli at one and minus one. -/
private theorem algorithm_two_counter_values :
    algorithm_two_counter_P.eval Complex.I=0 ∧
      algorithm_two_counter_P.eval (-Complex.I)=(1/100 : ℂ) ∧
      ‖algorithm_two_counter_P.eval 1‖^2=‖algorithm_two_counter_P.eval (-1)‖^2 := by
  constructor
  · norm_num [algorithm_two_counter_eval,Complex.I_mul_I]
  constructor
  · norm_num [algorithm_two_counter_eval,Complex.I_mul_I]
  · norm_num [algorithm_two_counter_P,Complex.sq_norm,Complex.normSq]

/-- The two point grid root exponential equals minus one. -/
private theorem algorithm_two_counter_root : Complex.exp ((2*Real.pi/2 : ℝ)*Complex.I)=(-1 : ℂ) := by
  rw [show (2*Real.pi/2 : ℝ)=Real.pi by ring,Complex.exp_pi_mul_I]

/-- The two point radix two Fourier transform returns the sum and difference of its input
values. -/
private theorem algorithm_two_counter_DFT (f : Fin 2 → ℂ) (j : Fin 2) :
    (radixTwoFourier 1 f).1 j=if j.val=0 then f 0+f 1 else f 0-f 1 := by
  rw [radixTwoFourier_root_semantics]
  simp only [show (2^1 : ℕ)=2 by norm_num,Nat.cast_ofNat,algorithm_two_counter_root]
  change (∑ x : Fin 2,f x*(-1)^(-(j.val*x.val : ℤ)))=_
  rw [Fin.sum_univ_two]
  by_cases h0 : j.val=0
  · simp [h0]
  · have h1 : j.val=1 := by omega
    simp [h1]
    ring

/-- The two point positive radix two Fourier transform returns the sum and difference of its
input values. -/
private theorem algorithm_two_counter_positive_DFT (f : Fin 2 → ℂ) (j : Fin 2) :
    (radixTwoPositiveFourier 1 f).1 j=if j.val=0 then f 0+f 1 else f 0-f 1 := by
  rw [radixTwoPositiveFourier_root_semantics]
  simp only [show (2^1 : ℕ)=2 by norm_num,Nat.cast_ofNat,algorithm_two_counter_root]
  change (∑ x : Fin 2,f x*(-1)^(j.val*x.val))=_
  rw [Fin.sum_univ_two]
  by_cases h0 : j.val=0
  · simp [h0]
  · have h1 : j.val=1 := by omega
    simp [h1]
    ring

/-- The two point normalized radix two Fourier transform returns half the sum and half the
difference of its input values. -/
private theorem algorithm_two_counter_normalised_DFT (f : Fin 2 → ℂ) (j : Fin 2) :
    (radixTwoNormalisedFourier 1 f).1 j=(2 : ℂ)⁻¹*(if j.val=0 then f 0+f 1 else f 0-f 1) := by
  change (2^1 : ℂ)⁻¹*(radixTwoFourier 1 f).1 j=_
  rw [algorithm_two_counter_DFT]
  norm_num

/-- The linear coefficient computed for the counterexample by the two point canonical Fourier
run is zero. -/
private theorem algorithm_two_counter_coefficient :
    (canonicalComplementFourierRun algorithm_two_counter_P 1 1).coefficients ⟨1,by norm_num⟩=0 := by
  let ω : ℂ:=Complex.exp ((2*Real.pi/(2^1 : ℕ) : ℝ)*Complex.I)
  let S : Fin 2 → ℂ:=fun j=>((Real.log (1-‖algorithm_two_counter_P.eval (ω^j.val)‖^2) : ℝ) : ℂ)
  let A : Fin 2 → ℂ:=(radixTwoNormalisedFourier 1 S).1
  let T : Fin 2 → ℂ:=fun j=>if j.val=0 then (2 : ℂ)⁻¹*A j else if j.val ≤ 1 then A j else 0
  have hω : ω=-1 := by exact algorithm_two_counter_root
  have hS : S 1=S 0 := by simp [S,hω,algorithm_two_counter_values.2.2]
  have hA0 : A 0=S 0 := by
    dsimp only [A]
    rw [algorithm_two_counter_normalised_DFT,hS]
    norm_num
    ring
  have hA1 : A 1=0 := by
    dsimp only [A]
    rw [algorithm_two_counter_normalised_DFT,hS]
    norm_num
  have hT0 : T 0=(2 : ℂ)⁻¹*S 0 := by simp [T,hA0]
  have hT1 : T 1=0 := by simp [T,hA1]
  have hE0 : (radixTwoPositiveFourier 1 T).1 0=(2 : ℂ)⁻¹*S 0 := by
    rw [algorithm_two_counter_positive_DFT]
    simp [hT0,hT1]
  have hE1 : (radixTwoPositiveFourier 1 T).1 1=(2 : ℂ)⁻¹*S 0 := by
    rw [algorithm_two_counter_positive_DFT]
    simp [hT0,hT1]
  change (radixTwoNormalisedFourier 1 (fun j=>Complex.exp ((radixTwoPositiveFourier 1 T).1 j))).1 ⟨1,by norm_num⟩=0
  rw [algorithm_two_counter_normalised_DFT]
  simp [hE0,hE1]

/-- Every complement of degree at most one for the counterexample has linear coefficient norm
strictly greater than one forty thousandth. -/
private theorem algorithm_two_counter_linear_lower (Q : Polynomial ℂ) (hQ : Q.natDegree ≤ 1)
    (hc : ∀ z : ℂ,‖z‖=1 → ‖algorithm_two_counter_P.eval z‖^2+‖Q.eval z‖^2=1) :
    (1/40000 : ℝ) < ‖Q.coeff 1‖ := by
  have heval (z : ℂ) : Q.eval z=Q.coeff 0+Q.coeff 1*z := by
    rw [Polynomial.eval_eq_sum_range' (show Q.natDegree < 2 by omega)]
    norm_num [Finset.sum_range_succ]
  have hi:=hc Complex.I (by simp)
  have hm:=hc (-Complex.I) (by simp)
  rw [algorithm_two_counter_values.1] at hi
  rw [algorithm_two_counter_values.2.1] at hm
  simp only [norm_zero,zero_pow (by decide : (2 : ℕ)≠0),zero_add] at hi
  norm_num at hm
  have hni : ‖Q.eval Complex.I‖=1 := by nlinarith only [hi,norm_nonneg (Q.eval Complex.I)]
  have hnm : ‖Q.eval (-Complex.I)‖ ≤ 1 := by nlinarith only [hm,norm_nonneg (Q.eval (-Complex.I))]
  have he : Q.eval Complex.I-Q.eval (-Complex.I)=2*Q.coeff 1*Complex.I := by rw [heval,heval];ring
  have hnd : ‖Q.eval Complex.I-Q.eval (-Complex.I)‖=2*‖Q.coeff 1‖ := by
    rw [he,norm_mul,norm_mul,Complex.norm_I]
    norm_num
  have hd : 1-‖Q.eval (-Complex.I)‖ ≤ 2*‖Q.coeff 1‖ := by
    calc
      _ = ‖Q.eval Complex.I‖-‖Q.eval (-Complex.I)‖ := by rw [hni]
      _ ≤ |‖Q.eval Complex.I‖-‖Q.eval (-Complex.I)‖| := le_abs_self _
      _ ≤ ‖Q.eval Complex.I-Q.eval (-Complex.I)‖ := abs_norm_sub_norm_le _ _
      _ = _ := hnd
  have hh:=mul_le_mul hd (show 1+‖Q.eval (-Complex.I)‖ ≤ (2 : ℝ) by linarith)
    (show 0 ≤ 1+‖Q.eval (-Complex.I)‖ by positivity)
    (show 0 ≤ 2*‖Q.coeff 1‖ by positivity)
  have hl : (1/40000 : ℝ) ≤ ‖Q.coeff 1‖ := by nlinarith only [hh,hm]
  have hnq : 0 < 2*‖Q.coeff 1‖ := by linarith
  have hnmlt : ‖Q.eval (-Complex.I)‖ < 1 := by nlinarith only [hm,norm_nonneg (Q.eval (-Complex.I))]
  have hfirst:=mul_le_mul_of_nonneg_right hd (show 0 ≤ 1+‖Q.eval (-Complex.I)‖ by positivity)
  have hsecond:=mul_lt_mul_of_pos_left (show 1+‖Q.eval (-Complex.I)‖ < (2 : ℝ) by linarith) hnq
  have hstrict:=hfirst.trans_lt hsecond
  nlinarith only [hstrict,hm]

/-- The original Fourier threshold for the specified counterexample parameters is at most two. -/
private theorem algorithm_two_counter_threshold :
    (Nat.ceil (2/Real.log ((1/(1-(99/100 : ℝ)))^(1/(1 : ℝ) : ℝ))*
      Real.log (8*Real.log (1/(99/100 : ℝ))/((1/(1-(99/100 : ℝ)))^(1/(1 : ℝ) : ℝ)-1)/(1/100000 : ℝ))) : ℕ) ≤ 2 := by
  norm_num only [one_div,Real.rpow_one,inv_inv,one_mul] at ⊢
  let A : ℝ:=8*Real.log (100/99)/99/(1/100000)
  have hlog : Real.log (100/99) ≤ (1/99 : ℝ) := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100/99)
    linarith
  have hlpos : 0 < Real.log (100/99) := Real.log_pos (by norm_num)
  have hApos : 0 < A := by dsimp [A];positivity
  have hAbound : A ≤ (100 : ℝ) := by
    dsimp [A]
    have hh:=div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 8)) (by norm_num : (0 : ℝ) ≤ 99))
      (by norm_num : (0 : ℝ) ≤ 1/100000)
    norm_num at hh
    linarith
  have hp : 0 < Real.log 100 := Real.log_pos (by norm_num)
  have hlogs:=Real.log_le_log hApos hAbound
  have ht : 2/Real.log 100*Real.log A ≤ (2 : ℝ) := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hp]
    linarith
  apply Nat.ceil_le.mpr
  convert! ht using 1

set_option maxHeartbeats 1500000 in

/-- There exist normalized complementary polynomials satisfying the original grid threshold for
which the computed Fourier coefficients fail the claimed error bound. -/
theorem canonical_complement_original_threshold_counterexample :
    ∃ (P Q : Polynomial ℂ) (d m : ℕ) (δ ε : ℝ),
      0 < d ∧ P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
      0 < δ ∧ δ < 1 ∧ 0 < ε ∧ ε < 1 ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) ∧
      0 < (Q.eval 0).re ∧ (Q.eval 0).im = 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) ∧
      1 ≤ m ∧ d+1 ≤ 2^m ∧
      (Nat.ceil (2/Real.log ((1/(1-δ))^(1/(d : ℝ) : ℝ)) *
        Real.log (8*Real.log (1/δ)/(((1/(1-δ))^(1/(d : ℝ) : ℝ))-1)/ε)) : ℕ) ≤ 2^m ∧
      (let N : ℕ := 2^m
       let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
       let a : ℕ → ℂ := fun n => (N : ℂ)⁻¹ * ∑ j : Fin N,
         ((Real.log (1-‖P.eval (ω^j.val)‖^2 : ℝ) : ℂ) * ω^(-(n*j.val : ℤ)))
       let q : ℕ → ℂ := fun n => (N : ℂ)⁻¹ * ∑ j : Fin N,
         Complex.exp ((2 : ℂ)⁻¹*a 0 +
           ∑ l ∈ Finset.range (N/2+1), if l = 0 then 0 else a l*ω^(l*j.val)) *
           ω^(-(n*j.val : ℤ))
       ¬ ∀ n : ℕ, n ≤ d → ‖Q.coeff n - q n‖ < ε) := by
  obtain ⟨Q,hQ,hQr,hQi,hQn,hQc,_⟩:=canonical_complement_schwarz_representation
    algorithm_two_counter_P 1 (99/100) algorithm_two_counter_degree (by norm_num) (by norm_num)
    algorithm_two_counter_margin
  refine ⟨algorithm_two_counter_P,Q,1,1,99/100,1/100000,by norm_num,
    algorithm_two_counter_degree,hQ,by norm_num,by norm_num,by norm_num,by norm_num,
    algorithm_two_counter_margin,hQr,hQi,hQn,hQc,by norm_num,by norm_num,?_,?_⟩
  · simpa only [Nat.cast_one,pow_one] using! algorithm_two_counter_threshold
  · (try dsimp only)
    intro hh
    have he:=hh 1 (by norm_num)
    have hf:=canonicalComplementFourierRun_coefficients algorithm_two_counter_P 1 1 ⟨1,by norm_num⟩
    dsimp only at hf
    rw [← hf,algorithm_two_counter_coefficient,sub_zero] at he
    have hl:=algorithm_two_counter_linear_lower Q hQ hQc
    norm_num at he
    linarith

end Qatlib.Concepts.LaurentPolys.ProfileFftBound
