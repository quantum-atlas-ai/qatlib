/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRadialSection
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularMode

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Spatial derivatives of the regular CK dipole

The product rule applies at every Cartesian point to the regular
radial coefficients and the angular polynomials.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter
open Qatlib.Papers.KnotLight13.TorusFamily (Spacetime coordinateValue coordinateSection
  coordinateSection_at spaceTimePartial cartesianCurl)
open scoped Topology

/-- Spatial derivatives of the linear CK angular vector. -/
def ckAngularD (i j : Fin 3) : ℂ :=
  (![![0, 0, -(1 : ℂ)], ![0, 0, -Complex.I], ![1, Complex.I, 0]] : Fin 3 → Fin 3 → ℂ) i j

/-- Spatial derivatives of the quadratic CK curl angular vector. -/
def ckCurlAngularD (x y z : ℝ) (i j : Fin 3) : ℂ :=
  (![![-(y : ℂ), 2 * (x : ℂ) + Complex.I * (y : ℂ), Complex.I * (z : ℂ)],
    ![-(x : ℂ) - 2 * Complex.I * (y : ℂ), Complex.I * (x : ℂ), -(z : ℂ)],
    ![-2 * Complex.I * (z : ℂ), 2 * (z : ℂ), Complex.I * (x : ℂ) - (y : ℂ)]] :
    Fin 3 → Fin 3 → ℂ) i j

/-- The angular vector along each spatial coordinate has its exact polynomial derivative. -/
private theorem hasDerivAt_ckAngular_section (s : Spacetime) (i j : Fin 3) :
    HasDerivAt (fun u => let p := coordinateSection s i.castSucc u
      ckAngular p.1 p.2.1 p.2.2.1 j) (ckAngularD i j) (coordinateValue s i.castSucc) := by
  fin_cases i
  · simpa [ckAngularD, coordinateSection, coordinateValue, Fin.castSucc] using
      hasDerivAt_angular_x s.1 s.2.1 s.2.2.1 j
  · simpa [ckAngularD, coordinateSection, coordinateValue, Fin.castSucc] using
      hasDerivAt_angular_y s.1 s.2.1 s.2.2.1 j
  · simpa [ckAngularD, coordinateSection, coordinateValue, Fin.castSucc] using
      hasDerivAt_angular_z s.1 s.2.1 s.2.2.1 j

/-- The curl angular vector along each spatial coordinate has its exact polynomial derivative. -/
private theorem hasDerivAt_ckCurlAngular_section (s : Spacetime) (i j : Fin 3) :
    HasDerivAt (fun u => let p := coordinateSection s i.castSucc u
      ckCurlAngular p.1 p.2.1 p.2.2.1 j) (ckCurlAngularD s.1 s.2.1 s.2.2.1 i j)
      (coordinateValue s i.castSucc) := by
  fin_cases i
  · simpa [ckCurlAngularD, coordinateSection, coordinateValue, Fin.castSucc] using
      hasDerivAt_curlAngular_x s.1 s.2.1 s.2.2.1 j
  · simpa [ckCurlAngularD, coordinateSection, coordinateValue, Fin.castSucc] using
      hasDerivAt_curlAngular_y s.1 s.2.1 s.2.2.1 j
  · simpa [ckCurlAngularD, coordinateSection, coordinateValue, Fin.castSucc] using
      hasDerivAt_curlAngular_z s.1 s.2.1 s.2.2.1 j

/-- The exact Cartesian section derivative of the extended CK dipole. -/
noncomputable def hopfDipolePartial (k : ℝ) (s : Spacetime) (i j : Fin 3) : ℂ :=
  let r := ckRadius s.1 s.2.1 s.2.2.1
  let u := k * r
  let q := coordinateValue s i.castSucc
  let d₃ := deriv ckRadialThree u * (k * (q / r))
  let d₅ := deriv ckRadialFive u * (k * (q / r))
  ((k ^ 4 * d₃ : ℝ) : ℂ) * ckAngular s.1 s.2.1 s.2.2.1 j +
    ((k ^ 4 * ckRadialThree u : ℝ) : ℂ) * ckAngularD i j +
    ((k ^ 5 * d₅ : ℝ) : ℂ) * ckCurlAngular s.1 s.2.1 s.2.2.1 j +
    ((k ^ 5 * ckRadialFive u : ℝ) : ℂ) * ckCurlAngularD s.1 s.2.1 s.2.2.1 i j +
    ((k ^ 3 * d₃ : ℝ) : ℂ) * ckConstantCurl j

/-- Differentiating the regular CK dipole along any spatial section
gives the stated derivative, including at the origin. -/
theorem hasDerivAt_hopfDipoleMode_section (k : ℝ) (s : Spacetime) (i j : Fin 3) :
    HasDerivAt (fun u => let p := coordinateSection s i.castSucc u
      hopfDipoleMode k p.1 p.2.1 p.2.2.1 j) (hopfDipolePartial k s i j)
      (coordinateValue s i.castSucc) := by
  have hd₃ (u : ℝ) : HasDerivAt ckRadialThree (deriv ckRadialThree u) u :=
    (hasDerivAt_ckRadialThree u).congr_deriv (hasDerivAt_ckRadialThree u).deriv.symm
  have hd₅ (u : ℝ) : HasDerivAt ckRadialFive (deriv ckRadialFive u) u :=
    (hasDerivAt_ckRadialFive u).congr_deriv (hasDerivAt_ckRadialFive u).deriv.symm
  have h₃ := hasDerivAt_ckRadialSection hd₃ (by rw [(hasDerivAt_ckRadialThree 0).deriv]; simp) k s i
  have h₅ := hasDerivAt_ckRadialSection hd₅ (by rw [(hasDerivAt_ckRadialFive 0).deriv]; simp) k s i
  have hA := hasDerivAt_ckAngular_section s i j
  have hB := hasDerivAt_ckCurlAngular_section s i j
  have hC := hasDerivAt_const (coordinateValue s i.castSucc) (ckConstantCurl j)
  have h := ((((h₃.const_mul (k ^ 4)).ofReal_comp.mul hA).add
    ((h₅.const_mul (k ^ 5)).ofReal_comp.mul hB)).add
    ((h₃.const_mul (k ^ 3)).ofReal_comp.mul hC))
  simp_rw [hopfDipoleMode_eq_regular]
  refine h.congr_deriv ?_
  simp only [hopfDipolePartial, coordinateSection_at, mul_zero, add_zero]
  push_cast
  ring

/-- At each fixed position the spatial derivative of the CK mode
is measurable as a function of frequency. -/
theorem measurable_hopfDipolePartial (s : Spacetime) (i j : Fin 3) :
    Measurable (fun k => hopfDipolePartial k s i j) := by
  let r := ckRadius s.1 s.2.1 s.2.2.1
  let q := coordinateValue s i.castSucc
  have hKr : Continuous (fun k : ℝ => k * r) := continuous_id.mul_const _
  have hKq : Continuous (fun k : ℝ => k * (q / r)) := continuous_id.mul_const _
  have h₃ : Continuous (fun k : ℝ => ckRadialThree (k * r)) :=
    continuous_ckRadialThree.comp hKr
  have h₅ : Continuous (fun k : ℝ => ckRadialFive (k * r)) :=
    continuous_ckRadialFive.comp hKr
  have hd₃ : Measurable (fun k => deriv ckRadialThree (k * r) * (k * (q / r))) :=
    ((measurable_deriv ckRadialThree).comp hKr.measurable).mul hKq.measurable
  have hd₅ : Measurable (fun k => deriv ckRadialFive (k * r) * (k * (q / r))) :=
    ((measurable_deriv ckRadialFive).comp hKr.measurable).mul hKq.measurable
  have hPart (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) (a : ℂ) :
      Measurable (fun k : ℝ => ((k ^ n * f k : ℝ) : ℂ) * a) :=
    (Complex.continuous_ofReal.measurable.comp ((measurable_id.pow_const n).mul hf)).mul_const a
  exact ((((hPart 4 hd₃ _).add (hPart 4 h₃.measurable _)).add
    (hPart 5 hd₅ _)).add (hPart 5 h₅.measurable _)).add (hPart 3 hd₃ _)

/-- The angular weight in the frequency bound for a spatial
derivative, which is locally bounded in the spatial coordinates. -/
noncomputable def hopfDipolePartialWeight (s : Spacetime) (i j : Fin 3) : ℝ :=
  let q := |coordinateValue s i.castSucc|
  q * ‖ckAngular s.1 s.2.1 s.2.2.1 j‖ + ‖ckAngularD i j‖ +
    q * ‖ckCurlAngular s.1 s.2.1 s.2.2.1 j‖ + ‖ckCurlAngularD s.1 s.2.1 s.2.2.1 i j‖ +
    q * ‖ckConstantCurl j‖

/-- The angular weight varies continuously with the Cartesian point. -/
theorem continuous_hopfDipolePartialWeight (i j : Fin 3) :
    Continuous (fun s => hopfDipolePartialWeight s i j) := by
  have hq : Continuous (fun s : Spacetime => |coordinateValue s i.castSucc|) := by
    fin_cases i <;> simp [coordinateValue, Fin.castSucc] <;> fun_prop
  have hA : Continuous (fun s : Spacetime => ‖ckAngular s.1 s.2.1 s.2.2.1 j‖) := by
    fin_cases j <;> simp only [ckAngular] <;> fun_prop
  have hB : Continuous (fun s : Spacetime => ‖ckCurlAngular s.1 s.2.1 s.2.2.1 j‖) := by
    fin_cases j <;> simp only [ckCurlAngular] <;> fun_prop
  have hdB : Continuous (fun s : Spacetime => ‖ckCurlAngularD s.1 s.2.1 s.2.2.1 i j‖) := by
    fin_cases i <;> fin_cases j <;> simp only [ckCurlAngularD] <;> fun_prop
  have hD : Continuous (fun _ : Spacetime => ‖ckAngularD i j‖) := continuous_const
  have hC : Continuous (fun _ : Spacetime => ‖ckConstantCurl j‖) := continuous_const
  exact ((((hq.mul hA).add hD).add (hq.mul hB)).add hdB).add (hq.mul hC)

/-- For positive frequencies the regular mode derivative is bounded
by the product of a frequency polynomial and its angular weight. -/
theorem norm_hopfDipolePartial_le {k : ℝ} (hk : 0 ≤ k) (s : Spacetime) (i j : Fin 3) :
    ‖hopfDipolePartial k s i j‖ ≤ k * (1 + k) ^ 6 * hopfDipolePartialWeight s i j := by
  let r := ckRadius s.1 s.2.1 s.2.2.1
  let q := coordinateValue s i.castSucc
  let d₃ := deriv ckRadialThree (k * r) * (k * (q / r))
  let d₅ := deriv ckRadialFive (k * r) * (k * (q / r))
  let M := k * (1 + k) ^ 6
  have hD₃ : |d₃| ≤ k ^ 2 * |q| :=
    (abs_ckRadialSection_le abs_deriv_ckRadialThree_le k s i).trans
      (mul_le_of_le_one_right (by positivity) (by norm_num))
  have hD₅ : |d₅| ≤ k ^ 2 * |q| :=
    (abs_ckRadialSection_le abs_deriv_ckRadialFive_le k s i).trans
      (mul_le_of_le_one_right (by positivity) (by norm_num))
  have hpow (n : ℕ) (hn : n ≤ 6) : k ^ (n + 1) ≤ M := by
    change k ^ (n + 1) ≤ k * (1 + k) ^ 6
    rw [pow_succ, mul_comm k]
    exact mul_le_mul_of_nonneg_right
      ((pow_le_pow_left₀ hk (by linarith : k ≤ 1 + k) n).trans
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + k) hn)) hk
  have hNorm (n : ℕ) (a : ℝ) (z : ℂ) :
      ‖((k ^ n * a : ℝ) : ℂ) * z‖ = k ^ n * |a| * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hk _)]
  have hPlain (n : ℕ) (hn : n ≤ 6) (a : ℝ) (ha : |a| ≤ 1) (z : ℂ) :
      ‖((k ^ (n + 1) * a : ℝ) : ℂ) * z‖ ≤ M * ‖z‖ := by
    rw [hNorm]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_right (pow_nonneg hk _) ha).trans (hpow n hn)) (norm_nonneg _)
  have hDer (n : ℕ) (hn : n + 1 ≤ 6) (d : ℝ) (hd : |d| ≤ k ^ 2 * |q|) (z : ℂ) :
      ‖((k ^ n * d : ℝ) : ℂ) * z‖ ≤ M * (|q| * ‖z‖) := by
    rw [hNorm]
    calc
      _ ≤ k ^ n * (k ^ 2 * |q|) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (pow_nonneg hk _))
          (norm_nonneg _)
      _ = k ^ (n + 1 + 1) * (|q| * ‖z‖) := by
        rw [show n + 1 + 1 = n + 2 by omega, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hpow (n + 1) hn) (by positivity)
  have h₃ : |ckRadialThree (k * r)| ≤ 1 := (abs_ckRadialThree_le _).trans (by norm_num)
  have h₅ : |ckRadialFive (k * r)| ≤ 1 := (abs_ckRadialFive_le _).trans (by norm_num)
  have hAdd {z w : ℂ} {a b : ℝ} (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ b) :
      ‖z + w‖ ≤ a + b := (norm_add_le z w).trans (add_le_add hz hw)
  refine (hAdd (hAdd (hAdd (hAdd (hDer 4 (by decide) d₃ hD₃ _) (hPlain 3 (by decide) _ h₃ _))
    (hDer 5 (by decide) d₅ hD₅ _)) (hPlain 4 (by decide) _ h₅ _))
    (hDer 3 (by decide) d₃ hD₃ _)).trans_eq ?_
  dsimp only [M, q, hopfDipolePartialWeight]
  ring

/-- Each spatial partial of the extended CK mode is the explicit
regular derivative. -/
theorem spaceTimePartial_hopfDipoleMode (k : ℝ) (s : Spacetime) (i j : Fin 3) :
    spaceTimePartial (fun p => hopfDipoleMode k p.1 p.2.1 p.2.2.1 j) s i.castSucc =
      hopfDipolePartial k s i j :=
  (hasDerivAt_hopfDipoleMode_section k s i j).deriv

/-- The continuous CK dipole remains a positive curl eigenstate at
the spatial origin, where the derivative of its linear angular factor
supplies the entire curl. -/
theorem cartesianCurl_hopfDipoleMode (k : ℝ) (s : Spacetime) (j : Fin 3) :
    cartesianCurl (fun p => hopfDipoleMode k p.1 p.2.1 p.2.2.1) s j =
      (k : ℂ) * hopfDipoleMode k s.1 s.2.1 s.2.2.1 j := by
  by_cases hR : ckRadius s.1 s.2.1 s.2.2.1 = 0
  · rcases s with ⟨x, y, z, t⟩
    obtain ⟨rfl, rfl, rfl⟩ := ckRadius_zero_coords hR
    have hP (i l : Fin 3) :
        hopfDipolePartial k (0, 0, 0, t) i l = ((k ^ 4 / 3 : ℝ) : ℂ) * ckAngularD i l := by
      have hB : ckCurlAngularD 0 0 0 i l = 0 := by
        fin_cases i <;> fin_cases l <;> simp [ckCurlAngularD]
      simp [hopfDipolePartial, ckRadius, ckRadialThree, hB, div_eq_mul_inv]
    have hp (i l : Fin 3) :
        spaceTimePartial (fun p => hopfDipoleMode k p.1 p.2.1 p.2.2.1 l)
          (0, 0, 0, t) i.castSucc = ((k ^ 4 / 3 : ℝ) : ℂ) * ckAngularD i l :=
      (spaceTimePartial_hopfDipoleMode k _ i l).trans (hP i l)
    have hx (l : Fin 3) := hp 0 l
    have hy (l : Fin 3) := hp 1 l
    have hz (l : Fin 3) := hp 2 l
    simp only [show (0 : Fin 3).castSucc = 0 by decide,
      show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
    rw [show hopfDipoleMode k 0 0 0 j = (k : ℂ) ^ 3 / 3 * ckConstantCurl j by
      rw [hopfDipoleMode, ite_eq_left hR]]
    fin_cases j <;>
      simp [cartesianCurl, hx, hy, hz, ckAngularD, ckConstantCurl] <;> ring
  · have hp (i l : Fin 3) :
        spaceTimePartial (fun p => hopfDipoleMode k p.1 p.2.1 p.2.2.1 l) s i.castSucc =
          spaceTimePartial (fun p => ckBeltramiPlus k p l) s i.castSucc := by
      let r := fun u : ℝ => let p := coordinateSection s i.castSucc u
        ckRadius p.1 p.2.1 p.2.2.1
      have hc : Continuous r := by
        fin_cases i <;> simp only [r, coordinateSection, Fin.castSucc] <;> simp <;>
          unfold ckRadius <;> fun_prop
      have hn : r (coordinateValue s i.castSucc) ≠ 0 := by
        simpa only [r, coordinateSection_at] using hR
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hc.continuousAt.eventually_ne hn] with u hu
      dsimp only [r] at hu
      simp only [hopfDipoleMode, ite_eq_right hu, ckBeltramiPlus,
        ckMultipoleField, ckCurlMultipoleField]
    have hx (l : Fin 3) := hp 0 l
    have hy (l : Fin 3) := hp 1 l
    have hz (l : Fin 3) := hp 2 l
    simp only [show (0 : Fin 3).castSucc = 0 by decide,
      show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
    calc
      _ = cartesianCurl (ckBeltramiPlus k) s j := by
        fin_cases j <;> simp [cartesianCurl, hx, hy, hz]
      _ = _ := by
        rw [cartesianCurl_ckBeltramiPlus k s hR]
        simp only [hopfDipoleMode, ite_eq_right hR, ckBeltramiPlus,
          ckMultipoleField, ckCurlMultipoleField]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
