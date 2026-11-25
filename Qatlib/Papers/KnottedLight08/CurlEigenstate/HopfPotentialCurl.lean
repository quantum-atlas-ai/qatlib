/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialTime
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKModeDivergence

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The curl of the integrated Hopf potential

The regular dipole derivatives have a common integrable frequency
bound in a neighborhood of each Cartesian point. The curl of the
integrated positive-frequency potential therefore retains the mode
eigenvalue multiplication inside the integral.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set
open Qatlib.Papers.KnotLight13.TorusFamily (Spacetime coordinateValue coordinateSection
  coordinateSection_at spaceTimePartial cartesianCurl cartesianDivergence)
open Qatlib.Papers.KnottedLight08.HopfField (ranadaField ranadaE_im ranadaB)
open scoped Topology BigOperators

/-- The absolute value of the damping and phase is real exponential decay. -/
private theorem norm_hopfDamping (t k : ℝ) :
    ‖Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ))‖ = Real.exp (-k) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.add_re]

/-- The derivative of one positive-frequency potential component
with respect to one spatial coordinate. -/
private noncomputable def hopfPotentialPartialDensity (s : Spacetime) (i j : Fin 3) (k : ℝ) : ℂ :=
  Complex.I / (2 * (Real.pi : ℂ)) *
    (Complex.exp (-(1 + Complex.I * (s.2.2.2 : ℂ)) * (k : ℂ)) * hopfDipolePartial k s i j) /
      (k : ℂ)

/-- A Cartesian section of the potential density has the exact
derivative supplied by the regular mode. -/
private theorem hasDerivAt_hopfPotentialDensity_space (s : Spacetime) (i j : Fin 3)
    (k a : ℝ) :
    HasDerivAt (fun u => let p := coordinateSection s i.castSucc u
      hopfPotentialDensity p.1 p.2.1 p.2.2.1 p.2.2.2 j k)
      (hopfPotentialPartialDensity (coordinateSection s i.castSucc a) i j k) a := by
  let S := fun u => coordinateSection s i.castSucc u
  have hS (u : ℝ) : coordinateSection (S a) i.castSucc u = S u := by
    fin_cases i <;> simp [S, coordinateSection, Fin.castSucc]
  have hV : coordinateValue (S a) i.castSucc = a := by
    fin_cases i <;> simp [S, coordinateSection, coordinateValue, Fin.castSucc]
  have hT (u : ℝ) : (S u).2.2.2 = s.2.2.2 := by
    fin_cases i <;> simp [S, coordinateSection, Fin.castSucc]
  have hM : HasDerivAt (fun u => hopfDipoleMode k (S u).1 (S u).2.1 (S u).2.2.1 j)
      (hopfDipolePartial k (S a) i j) a := by
    simpa only [hS, hV] using hasDerivAt_hopfDipoleMode_section k (S a) i j
  let c := Complex.I / (2 * (Real.pi : ℂ))
  let e := Complex.exp (-(1 + Complex.I * (s.2.2.2 : ℂ)) * (k : ℂ))
  change HasDerivAt (fun u => hopfPotentialDensity (S u).1 (S u).2.1 (S u).2.2.1 (S u).2.2.2 j k)
    (hopfPotentialPartialDensity (S a) i j k) a
  simp only [hopfPotentialDensity, hopfPotentialPartialDensity, hT]
  simpa only [c, e, mul_assoc] using (hM.const_mul (c * e)).div_const (k : ℂ)

/-- For fixed Cartesian point the derivative density is measurable in frequency. -/
private theorem measurable_hopfPotentialPartialDensity (s : Spacetime) (i j : Fin 3) :
    Measurable (hopfPotentialPartialDensity s i j) := by
  have he : Continuous (fun k : ℝ => Complex.exp (-(1 + Complex.I *
      (s.2.2.2 : ℂ)) * (k : ℂ))) := by fun_prop
  exact ((he.measurable.mul (measurable_hopfDipolePartial s i j)).const_mul
    (Complex.I / (2 * (Real.pi : ℂ)))).div Complex.continuous_ofReal.measurable

/-- The reciprocal frequency in the potential cancels the linear
frequency factor in the derivative bound. -/
private theorem norm_hopfPotentialPartialDensity_le {k : ℝ} (hk : 0 < k)
    (s : Spacetime) (i j : Fin 3) :
    ‖hopfPotentialPartialDensity s i j k‖ ≤
      ‖Complex.I / (2 * (Real.pi : ℂ))‖ * (Real.exp (-k) * (1 + k) ^ 6) *
        hopfDipolePartialWeight s i j := by
  rw [hopfPotentialPartialDensity, norm_div, norm_mul, norm_mul, norm_hopfDamping,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  apply (div_le_iff₀ hk).2
  calc
    _ ≤ ‖Complex.I / (2 * (Real.pi : ℂ))‖ *
          (Real.exp (-k) * (k * (1 + k) ^ 6 * hopfDipolePartialWeight s i j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_hopfDipolePartial_le hk.le s i j) (Real.exp_pos _).le)
        (norm_nonneg _)
    _ = _ := by ring

/-- The damped polynomial bounding the derivative is integrable on positive frequencies. -/
private theorem integrableOn_hopfDerivativeWeight :
    IntegrableOn (fun k : ℝ => Real.exp (-k) * (1 + k) ^ 6) (Ioi 0) := by
  have hM (n : ℕ) : IntegrableOn (fun k : ℝ => Real.exp (-k) * k ^ n) (Ioi 0) := by
    have h := (integrableOn_hopf_laplace_moment (a := 1) (by norm_num) n).norm
    refine IntegrableOn.congr_fun h (fun k hk => ?_) measurableSet_Ioi
    simp [norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mem_Ioi.mp hk), mul_comm]
  have hSum : IntegrableOn (fun k : ℝ => ∑ n ∈ Finset.range 7,
      (Nat.choose 6 n : ℝ) * (Real.exp (-k) * k ^ n)) (Ioi 0) :=
    integrable_finsetSum _ (fun n _ => (hM n).const_mul _)
  refine hSum.congr_fun (fun k _ => ?_) measurableSet_Ioi
  rw [add_comm (1 : ℝ) k, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [one_pow, mul_one]
  ring

/-- Each spatial derivative of the integrated potential can be
computed inside the frequency integral. -/
private theorem hasDerivAt_hopfPositivePotential_space (s : Spacetime) (i j : Fin 3) :
    IntegrableOn (hopfPotentialPartialDensity s i j) (Ioi 0) ∧
      HasDerivAt (fun u => let p := coordinateSection s i.castSucc u
        hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2 j)
        (∫ k in Ioi (0 : ℝ), hopfPotentialPartialDensity s i j k) (coordinateValue s i.castSucc) := by
  let x := coordinateValue s i.castSucc
  let S := fun u => coordinateSection s i.castSucc u
  let W := fun u => hopfDipolePartialWeight (S u) i j
  let c := ‖Complex.I / (2 * (Real.pi : ℂ))‖
  let M := fun k : ℝ => c * (Real.exp (-k) * (1 + k) ^ 6) * (W x + 1)
  let V := {u : ℝ | W u < W x + 1}
  let F := fun u k => hopfPotentialDensity (S u).1 (S u).2.1 (S u).2.2.1 (S u).2.2.2 j k
  let D := fun u k => hopfPotentialPartialDensity (S u) i j k
  have hx : S x = s := coordinateSection_at s i.castSucc
  have hS : Continuous S := by
    fin_cases i <;> simp [S, coordinateSection, Fin.castSucc, continuous_const] <;> exact continuous_id
  have hW : Continuous W := (continuous_hopfDipolePartialWeight i j).comp hS
  have hV : V ∈ 𝓝 x := (tendsto_order.1 hW.continuousAt.tendsto).2 _ (by dsimp [W]; linarith)
  have hM : IntegrableOn M (Ioi 0) :=
    (integrableOn_hopfDerivativeWeight.const_mul c).mul_const _
  have hF (u : ℝ) : IntegrableOn (F u) (Ioi 0) :=
    integrableOn_hopfPotentialDensity (S u).1 (S u).2.1 (S u).2.2.1 (S u).2.2.2 j
  have hD :
      IntegrableOn (D x) (Ioi 0) ∧
        HasDerivAt (fun u => ∫ k in Ioi (0 : ℝ), F u k) (∫ k in Ioi (0 : ℝ), D x k) x := by
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D) hV
      (Eventually.of_forall fun u => (hF u).aestronglyMeasurable) (hF x)
      (measurable_hopfPotentialPartialDensity (S x) i j).aestronglyMeasurable ?_ hM
      (Eventually.of_forall fun k u _ => hasDerivAt_hopfPotentialDensity_space s i j k u)
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun k hk u hu => ?_
    have hk' : 0 < k := hk
    refine (norm_hopfPotentialPartialDensity_le hk' (S u) i j).trans ?_
    exact mul_le_mul_of_nonneg_left (show W u ≤ W x + 1 from le_of_lt hu) (by positivity)
  have hDx : D x = hopfPotentialPartialDensity s i j := by simp only [D, hx]
  rw [hDx] at hD
  simpa only [F, S, x, hopfPositivePotential] using hD

/-- The Cartesian curl is the signed difference of the corresponding section derivatives. -/
private def curlOfSections (P : Fin 3 → Fin 3 → ℂ) (j : Fin 3) : ℂ :=
  ![P 1 2 - P 2 1, P 2 0 - P 0 2, P 0 1 - P 1 0] j

/-- The curl multiplier on the potential derivative density cancels
the reciprocal frequency, leaving the positive-frequency field density. -/
private theorem curlOfSections_hopfPotentialPartialDensity (s : Spacetime) (j : Fin 3)
    {k : ℝ} (hk : k ≠ 0) :
    curlOfSections (fun i l => hopfPotentialPartialDensity s i l k) j =
      Complex.I * ((1 / (2 * (Real.pi : ℂ))) *
        (Complex.exp (-(1 + Complex.I * (s.2.2.2 : ℂ)) * (k : ℂ)) *
          hopfDipoleMode k s.1 s.2.1 s.2.2.1 j)) := by
  have hp (i l : Fin 3) := spaceTimePartial_hopfDipoleMode k s i l
  have hx (l : Fin 3) := hp 0 l
  have hy (l : Fin 3) := hp 1 l
  have hz (l : Fin 3) := hp 2 l
  simp only [show (0 : Fin 3).castSucc = 0 by decide,
    show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
  have hc : curlOfSections (hopfDipolePartial k s) j =
      (k : ℂ) * hopfDipoleMode k s.1 s.2.1 s.2.2.1 j := by
    rw [← cartesianCurl_hopfDipoleMode k s j]
    fin_cases j <;> simp [curlOfSections, cartesianCurl, hx, hy, hz]
  have hK : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  calc
    _ = Complex.I / (2 * (Real.pi : ℂ)) *
        (Complex.exp (-(1 + Complex.I * (s.2.2.2 : ℂ)) * (k : ℂ)) *
          curlOfSections (hopfDipolePartial k s) j) / (k : ℂ) := by
      fin_cases j <;> simp [curlOfSections, hopfPotentialPartialDensity] <;> ring
    _ = _ := by
      rw [hc]
      field_simp [hK]

/-- The curl of the positive-frequency Hopf potential equals
the actual Rañada complex field times the imaginary unit. -/
theorem cartesianCurl_hopfPositivePotential (s : Spacetime) (j : Fin 3) :
    cartesianCurl (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2) s j =
      Complex.I * ranadaField s.1 s.2.1 s.2.2.1 s.2.2.2 j := by
  have hp (i l : Fin 3) :
      spaceTimePartial (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2 l) s i.castSucc =
        ∫ k in Ioi (0 : ℝ), hopfPotentialPartialDensity s i l k :=
    (hasDerivAt_hopfPositivePotential_space s i l).2.deriv
  have hx (l : Fin 3) := hp 0 l
  have hy (l : Fin 3) := hp 1 l
  have hz (l : Fin 3) := hp 2 l
  simp only [show (0 : Fin 3).castSucc = 0 by decide,
    show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
  have hInt (i l : Fin 3) := (hasDerivAt_hopfPositivePotential_space s i l).1
  have hf := (ranadaField_eq_hopf_dipole_superposition s.1 s.2.1 s.2.2.1 s.2.2.2 j).2
  calc
    _ = ∫ k in Ioi (0 : ℝ), curlOfSections (fun i l => hopfPotentialPartialDensity s i l k) j := by
      fin_cases j
      · simpa [cartesianCurl, curlOfSections, hy, hz] using
          (integral_sub (hInt 1 2) (hInt 2 1)).symm
      · simpa [cartesianCurl, curlOfSections, hz, hx] using
          (integral_sub (hInt 2 0) (hInt 0 2)).symm
      · simpa [cartesianCurl, curlOfSections, hx, hy] using
          (integral_sub (hInt 0 1) (hInt 1 0)).symm
    _ = _ := by
      rw [setIntegral_congr_fun measurableSet_Ioi
        (fun _ hk => curlOfSections_hopfPotentialPartialDensity s j hk.ne')]
      simp only [integral_const_mul, ← hf]

/-- A spatial derivative of the real potential is twice the real
part of the corresponding positive-frequency derivative. -/
private theorem spaceTimePartial_hopfVectorPotential (s : Spacetime) (i l : Fin 3) :
    spaceTimePartial (fun p => (hopfVectorPotential p.1 p.2.1 p.2.2.1 p.2.2.2 l : ℂ)) s i.castSucc =
      ((2 * (spaceTimePartial (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2 l)
        s i.castSucc).re : ℝ) : ℂ) := by
  let x := coordinateValue s i.castSucc
  have h := (hasDerivAt_hopfPositivePotential_space s i l).2
  have hr := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h).const_mul (2 : ℝ)).ofReal_comp
  have hd : spaceTimePartial (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2 l) s i.castSucc =
      ∫ k in Ioi (0 : ℝ), hopfPotentialPartialDensity s i l k := h.deriv
  rw [hd]
  simpa only [hopfVectorPotential, Function.comp_apply, spaceTimePartial, Complex.reCLM_apply, x]
    using hr.deriv

/-- Taking both conjugate frequencies in the potential recovers
the article-normalized magnetic field from its Cartesian curl. -/
theorem cartesianCurl_hopfVectorPotential (s : Spacetime) (j : Fin 3) :
    cartesianCurl (fun p l => (hopfVectorPotential p.1 p.2.1 p.2.2.1 p.2.2.2 l : ℂ)) s j =
      ((-2 * (ranadaB s.1 s.2.1 s.2.2.1 s.2.2.2 j).re : ℝ) : ℂ) := by
  let A := fun p : Spacetime => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2
  have hp (i l : Fin 3) :
      spaceTimePartial (fun p => (hopfVectorPotential p.1 p.2.1 p.2.2.1 p.2.2.2 l : ℂ)) s i.castSucc =
        ((2 * (spaceTimePartial (fun p => A p l) s i.castSucc).re : ℝ) : ℂ) :=
    spaceTimePartial_hopfVectorPotential s i l
  have hx (l : Fin 3) := hp 0 l
  have hy (l : Fin 3) := hp 1 l
  have hz (l : Fin 3) := hp 2 l
  simp only [show (0 : Fin 3).castSucc = 0 by decide,
    show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
  calc
    _ = ((2 * (cartesianCurl A s j).re : ℝ) : ℂ) := by
      fin_cases j <;> simp [cartesianCurl, hx, hy, hz, Complex.sub_re] <;> ring
    _ = _ := by
      change ((2 * (cartesianCurl (fun p => hopfPositivePotential p.1 p.2.1
        p.2.2.1 p.2.2.2) s j).re : ℝ) : ℂ) = _
      rw [cartesianCurl_hopfPositivePotential]
      simp [ranadaField, Complex.mul_re, Complex.add_im, Complex.mul_im, ranadaE_im]

/-- The divergence of the positive-frequency potential integrates
the vanishing divergence of each regular CK mode. -/
theorem cartesianDivergence_hopfPositivePotential (s : Spacetime) :
    cartesianDivergence (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2) s = 0 := by
  let D := fun i : Fin 3 => hopfPotentialPartialDensity s i i
  have hI (i : Fin 3) : Integrable (D i) (volume.restrict (Ioi (0 : ℝ))) :=
    (hasDerivAt_hopfPositivePotential_space s i i).1
  have hp (i : Fin 3) :
      spaceTimePartial (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2 i) s i.castSucc =
        ∫ k in Ioi (0 : ℝ), D i k := (hasDerivAt_hopfPositivePotential_space s i i).2.deriv
  have hx := hp 0
  have hy := hp 1
  have hz := hp 2
  simp only [show (0 : Fin 3).castSucc = 0 by decide,
    show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
  have hsum (k : ℝ) : D 0 k + D 1 k + D 2 k = 0 := by
    let E := Complex.exp (-(1 + Complex.I * (s.2.2.2 : ℂ)) * (k : ℂ))
    let c := Complex.I / (2 * (Real.pi : ℂ))
    calc
      _ = c * (E * (hopfDipolePartial k s 0 0 + hopfDipolePartial k s 1 1 +
          hopfDipolePartial k s 2 2)) / (k : ℂ) := by
        dsimp only [D, hopfPotentialPartialDensity, c, E]
        ring
      _ = 0 := by rw [sum_hopfDipolePartial_diagonal_eq_zero, mul_zero, mul_zero, zero_div]
  calc
    _ = ∫ k in Ioi (0 : ℝ), D 0 k + D 1 k + D 2 k := by
      simp only [cartesianDivergence, hx, hy, hz]
      simpa only [Pi.add_apply, integral_add (hI 0) (hI 1)] using
        (integral_add ((hI 0).add (hI 1)) (hI 2)).symm
    _ = 0 := by simp only [hsum, integral_zero]

/-- The real published Hopf vector potential satisfies the
Coulomb gauge at every Cartesian point and real time. -/
theorem cartesianDivergence_hopfVectorPotential (s : Spacetime) :
    cartesianDivergence (fun p l => (hopfVectorPotential p.1 p.2.1 p.2.2.1 p.2.2.2 l : ℂ)) s = 0 := by
  let A := fun p : Spacetime => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2
  have hx := spaceTimePartial_hopfVectorPotential s 0 0
  have hy := spaceTimePartial_hopfVectorPotential s 1 1
  have hz := spaceTimePartial_hopfVectorPotential s 2 2
  simp only [show (0 : Fin 3).castSucc = 0 by decide,
    show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
  calc
    _ = ((2 * (cartesianDivergence A s).re : ℝ) : ℂ) := by
      simp [cartesianDivergence, hx, hy, hz, A, Complex.add_re]
      ring
    _ = 0 := by simp only [A, cartesianDivergence_hopfPositivePotential,
      Complex.zero_re, mul_zero, Complex.ofReal_zero]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
