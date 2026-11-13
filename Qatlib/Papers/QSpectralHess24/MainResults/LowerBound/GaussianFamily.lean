/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSpectralHess24.MainResults.Core.OracleModel
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Gaussian Test Family for Quantum Hessian Estimation Lower Bounds

This module formalizes Lemmas 6.4 and 6.5 of Zhang and Shao on the `d^2`-element
Gaussian test family `f_{j,k}(x) = ε x_j x_k exp(-c ‖x‖^2 / 2)` used in the quantum
query lower bound for Hessian estimation, proving the global quadratic sum bound
`∑_{j,k} f_{j,k}(x)^2 ≤ 4 ε^2 / (e^2 c^2)`, the multi-index derivative bound
`|∂^α f_{j,k}(0)| ≤ c^t t^{t/2}` (`t = |α|`), and the exact Hessian identity
`H_{f_{j,k}}(0) = c (E_{jk} + E_{kj})`.

## Main definitions

* `gaussianFamily`: Gaussian test function `f_{j,k}(x) = ε x_j x_k exp(-c ∑_i x_i^2 / 2)`.
* `gaussianFamilyIndex`: index type `Fin d × Fin d` of the `d^2` family members.

## Main statements

* `gaussianFamily_index_card`: Lemma 6.4, cardinality `d^2` of the Gaussian test family.
* `gaussianFamily_sum_sq_eq`, `gaussianFamily_sum_sq_le`: Lemma 6.4, `∑_{j,k} f_{j,k}(x)^2 ≤ 4 ε^2 / (e^2 c^2)`.
* `gaussianFamily_deriv_bound`: Lemma 6.5, origin derivative bound and Hessian `c (E_{jk} + E_{kj})`.

## References

* [Zhang and Shao, 2024][ZhangShao2024SpectralHess], Section 6, Lemmas 6.4 and 6.5, pp. 29--30.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib
open Matrix
open scoped BigOperators
open scoped ContDiff

open Qatlib.Papers.QSpectralHess24.MainResults.Core

namespace Qatlib.Papers.QSpectralHess24.MainResults.LowerBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The Gaussian test function `f_{j,k}(x) = ε x_j x_k e^{−c‖x‖²/2}` of Lemma 6.4. -/
noncomputable def gaussianFamily {d : ℕ} (ε c : ℝ) (j k : Fin d) (x : Fin d → ℝ) : ℝ :=
  ε * x j * x k * Real.exp (-(c * ∑ i, (x i) ^ 2) / 2)

/-- The `d²` members of the test family, indexed by the pair `(j,k)`. -/
noncomputable def gaussianFamilyIndex (d : ℕ) : Type := Fin d × Fin d

instance (d : ℕ) : Fintype (gaussianFamilyIndex d) := by
  unfold gaussianFamilyIndex; infer_instance

instance (d : ℕ) : DecidableEq (gaussianFamilyIndex d) := by
  unfold gaussianFamilyIndex; infer_instance

/-- **c025 / Lemma 6.4 (arXiv:2407.03833v2, p.29).**
Let `d ∈ ℕ`, `ε, c ∈ ℝ₊` and `f_*(x) = 0`, `f_{j,k}(x) = ε x_j x_k e^{−c‖x‖²/2}`.
The family `𝓕 = {f_{j,k} : j,k ∈ [d]}` has `d²` members and for all `x ∈ ℝ^d`,
`Σ_{j,k ∈ [d]} |f_{j,k}(x) − f_*(x)|² ≤ 4ε²/(e²c²)`.

Original proof: `Σ_{j,k} (ε x_j x_k e^{−c‖x‖²/2})² = ε² (Σ_i x_i²)² e^{−c‖x‖²}`, and
with `z := c‖x‖²` one has `z² e^{−z} ≤ 4/e²` (from `z e^{−z} ≤ 1/e` applied to
`z/2`), giving the bound.

**Status.** Fully proved: `gaussianFamily_sum_sq_le` proves the numerical bound and
`gaussianFamilyIndex_card` the cardinality `d²`. -/
theorem gaussianFamily_index_card (d : ℕ) : Fintype.card (gaussianFamilyIndex d) = d ^ 2 := by
  change Fintype.card (Fin d × Fin d) = d ^ 2
  rw [Fintype.card_prod, Fintype.card_fin, sq]

/-- The squared-exponential identity behind Lemma 6.4:
`Σ_{j,k} f_{j,k}(x)^2 = ε² (Σ_i x_i²)² e^{−c Σ_i x_i²}`. -/
theorem gaussianFamily_sum_sq_eq {d : ℕ} (ε c : ℝ) (x : Fin d → ℝ) :
    ∑ p : gaussianFamilyIndex d, (gaussianFamily ε c p.1 p.2 x) ^ 2 =
      ε ^ 2 * (∑ i, (x i) ^ 2) ^ 2 * Real.exp (-(c * ∑ i, (x i) ^ 2)) := by
  have hexp_sq : ∀ t : ℝ, (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    intro t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hterm : ∀ j k : Fin d,
      (gaussianFamily ε c j k x) ^ 2 =
        ε ^ 2 * (x j) ^ 2 * (x k) ^ 2 * Real.exp (-(c * ∑ i, (x i) ^ 2)) := by
    intro j k
    unfold gaussianFamily
    simp only [mul_pow, hexp_sq]
    rw [show 2 * (-(c * ∑ i, (x i) ^ 2) / 2) = -(c * ∑ i, (x i) ^ 2) from by ring]
  have hprod : (∑ p : gaussianFamilyIndex d, (gaussianFamily ε c p.1 p.2 x) ^ 2) =
      ∑ j : Fin d, ∑ k : Fin d, (gaussianFamily ε c j k x) ^ 2 := by
    change (∑ p : Fin d × Fin d, (gaussianFamily ε c p.1 p.2 x) ^ 2) = _
    rw [Fintype.sum_prod_type]
  rw [hprod]
  simp only [hterm]
  set E : ℝ := Real.exp (-(c * ∑ i, (x i) ^ 2)) with hE
  set T : ℝ := ∑ k : Fin d, (x k) ^ 2 with hT
  have hstepA : ∀ j : Fin d, (∑ k : Fin d, ε ^ 2 * (x j) ^ 2 * (x k) ^ 2 * E) =
      ∑ k : Fin d, (ε ^ 2 * (x j) ^ 2 * E) * (x k) ^ 2 := by
    intro j
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hstepB : ∀ j : Fin d, (∑ k : Fin d, (ε ^ 2 * (x j) ^ 2 * E) * (x k) ^ 2) =
      (ε ^ 2 * (x j) ^ 2 * E) * T := by
    intro j
    rw [Finset.mul_sum]
  have hstepC : (∑ j : Fin d, (ε ^ 2 * (x j) ^ 2 * E) * T) = ε ^ 2 * E * T * T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTT : (∑ i : Fin d, (x i) ^ 2) ^ 2 = T * T := by
    rw [sq, ← hT]
  rw [hTT]
  simp only [hstepA, hstepB, hstepC]
  ring

/-- **c025 / Lemma 6.4, numerical bound.** For `c > 0` and `ε ≥ 0`,
`Σ_{j,k} |f_{j,k}(x) − f_*(x)|² ≤ 4ε²/(e²c²)` with `f_* = 0`. -/
theorem gaussianFamily_sum_sq_le {d : ℕ} (ε c : ℝ) (hc : 0 < c) (hε : 0 ≤ ε)
    (x : Fin d → ℝ) :
    ∑ p : gaussianFamilyIndex d, (gaussianFamily ε c p.1 p.2 x) ^ 2 ≤
      4 * ε ^ 2 / (Real.exp 1) ^ 2 / c ^ 2 := by
  rw [gaussianFamily_sum_sq_eq]
  set S : ℝ := ∑ i, (x i) ^ 2 with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  -- the scalar inequality `z² e^{−z} ≤ 4/e²` for `z = c S`
  have hexp_sq : ∀ t : ℝ, (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    intro t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hbase : (c * S / 2) * Real.exp (-(c * S / 2)) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one (c * S / 2)
  have hbase2 : c * S * Real.exp (-(c * S / 2)) ≤ 2 * Real.exp (-1) := by
    nlinarith [Real.exp_pos (-(c * S / 2))]
  have hsquare : (c * S * Real.exp (-(c * S / 2))) ^ 2 ≤ (2 * Real.exp (-1)) ^ 2 := by
    rw [sq, sq]
    exact mul_self_le_mul_self
      (mul_nonneg (mul_nonneg (le_of_lt hc) hSnn) (le_of_lt (Real.exp_pos _))) hbase2
  have hlhs : (c * S * Real.exp (-(c * S / 2))) ^ 2 = (c * S) ^ 2 * Real.exp (-(c * S)) := by
    simp only [mul_pow, hexp_sq]
    rw [show 2 * (-(c * S / 2)) = -(c * S) from by ring]
  have hrhs : (2 * Real.exp (-1)) ^ 2 = 4 * ((Real.exp 1)⁻¹) ^ 2 := by
    rw [mul_pow, Real.exp_neg]
    ring
  rw [hlhs, hrhs] at hsquare
  -- divide by `c ^ 2`
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hfin : (c * S) ^ 2 * Real.exp (-(c * S)) / c ^ 2 ≤
      4 * ((Real.exp 1)⁻¹) ^ 2 / c ^ 2 :=
    div_le_div_of_nonneg_right hsquare (le_of_lt hc2)
  have hconv : ε ^ 2 * S ^ 2 * Real.exp (-(c * S)) =
      ε ^ 2 * ((c * S) ^ 2 * Real.exp (-(c * S)) / c ^ 2) := by
    field_simp
  rw [hconv]
  have hε2 : 0 ≤ ε ^ 2 := pow_nonneg hε 2
  have hstep : ε ^ 2 * ((c * S) ^ 2 * Real.exp (-(c * S)) / c ^ 2) ≤
      ε ^ 2 * (4 * ((Real.exp 1)⁻¹) ^ 2 / c ^ 2) :=
    mul_le_mul_of_nonneg_left hfin hε2
  refine hstep.trans (le_of_eq ?_)
  rw [inv_pow]
  field_simp

private noncomputable def gaussianFactor (c : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  u ^ r * Real.exp (-(c / 2) * u ^ 2)

private lemma nat_lt_infty (n : ℕ) : (n : ℕ∞ω) < ∞ :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)

private lemma gaussianFactor_smooth (c : ℝ) (r : ℕ) :
    ContDiff ℝ ∞ (gaussianFactor c r) := by
  exact (contDiff_id.pow r).mul
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.pow 2)))

private lemma separable_smooth {d : ℕ} (a : ℝ) (ψ : Fin d → ℝ → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (fun x : Fin d → ℝ => a * ∏ i, ψ i (x i)) := by
  exact contDiff_const.mul
    (contDiff_prod fun i _ => (hψ i).comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) i))

private lemma separable_fderiv {d : ℕ} (a : ℝ) (ψ : Fin d → ℝ → ℝ)
    (hψ : ∀ i, Differentiable ℝ (ψ i)) (x : Fin d → ℝ) (i₀ : Fin d) :
    fderiv ℝ (fun y : Fin d → ℝ => a * ∏ i, ψ i (y i)) x (Pi.single i₀ 1) =
      a * ∏ i, (if i = i₀ then deriv (ψ i) else ψ i) (x i) := by
  have hd := (HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun i (y : Fin d → ℝ) => ψ i (y i))
    (fun i _ => ((hψ i (x i)).hasDerivAt.hasFDerivAt.comp x
      (hasFDerivAt_apply i x)))).const_mul a
  rw [hd.fderiv]
  simp only [_root_.smul_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i₀]
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    congr 1
    rw [mul_comm]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

private lemma separable_iteratedFDeriv {d : ℕ} (a : ℝ) (ψ : Fin d → ℝ → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (L : List (Fin d)) (x : Fin d → ℝ) :
    iteratedFDeriv ℝ L.length (fun y : Fin d → ℝ => a * ∏ i, ψ i (y i)) x
        (fun s => Pi.single (L.get s) 1) =
      a * ∏ i, iteratedDeriv (L.count i) (ψ i) (x i) := by
  induction L generalizing x with
  | nil => simp
  | cons i L ih =>
    simp only [List.length_cons]
    rw [((separable_smooth a ψ hψ).differentiable_iteratedFDeriv
        (nat_lt_infty L.length) x).iteratedFDeriv_succ_apply_left']
    have ht : (fun y => iteratedFDeriv ℝ L.length
        (fun z : Fin d → ℝ => a * ∏ i, ψ i (z i)) y
        (Fin.tail (fun s : Fin (L.length + 1) =>
          (Pi.single ((i :: L).get s) (1 : ℝ) : Fin d → ℝ)))) =
        fun y => a * ∏ q, iteratedDeriv (L.count q) (ψ q) (y q) := by
      funext y
      exact ih y
    rw [ht, separable_fderiv a (fun q => iteratedDeriv (L.count q) (ψ q))
      (fun q => (hψ q).differentiable_iteratedDeriv (L.count q) (nat_lt_infty _))]
    congr 1
    apply Finset.prod_congr rfl
    intro q _
    by_cases hq : q = i
    · subst q
      simp [iteratedDeriv_succ]
    · simp [hq, Ne.symm hq]

private lemma iteratedDeriv_mul_coordinate_aux (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ∀ u : ℝ, iteratedDeriv (m + 1) (fun x => x * f x) u =
      (m + 1 : ℝ) * iteratedDeriv m f u + u * iteratedDeriv (m + 1) f u := by
  induction m with
  | zero =>
    intro u
    rw [iteratedDeriv_one, iteratedDeriv_zero, iteratedDeriv_one]
    have hd := (hasDerivAt_id' u).mul ((hf.differentiable (by decide)).differentiableAt.hasDerivAt)
    exact hd.deriv.trans (by ring)
  | succ m ih =>
    intro u
    rw [iteratedDeriv_succ, funext ih]
    have hd1 : HasDerivAt (fun x => (m + 1 : ℝ) * iteratedDeriv m f x)
        ((m + 1 : ℝ) * iteratedDeriv (m + 1) f u) u := by
      rw [iteratedDeriv_succ]
      exact ((hf.differentiable_iteratedDeriv m
        (nat_lt_infty m)).differentiableAt.hasDerivAt).const_mul (m + 1 : ℝ)
    have hd2 : HasDerivAt (fun x => x * iteratedDeriv (m + 1) f x)
        (1 * iteratedDeriv (m + 1) f u + u * iteratedDeriv (m + 2) f u) u := by
      rw [show iteratedDeriv (m + 2) f u = deriv (iteratedDeriv (m + 1) f) u from
        congrFun iteratedDeriv_succ u]
      exact (hasDerivAt_id' u).mul ((hf.differentiable_iteratedDeriv (m + 1)
        (nat_lt_infty (m + 1))).differentiableAt.hasDerivAt)
    exact (hd1.add hd2).deriv.trans (by push_cast; ring)

private lemma iteratedDeriv_mul_coordinate (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    iteratedDeriv (m + 1) (fun u => u * f u) 0 =
      (m + 1 : ℝ) * iteratedDeriv m f 0 := by
  simpa using iteratedDeriv_mul_coordinate_aux f hf m 0

private lemma gaussianFactor_deriv (c u : ℝ) :
    deriv (gaussianFactor c 0) u = -c * gaussianFactor c 1 u := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-(c / 2) * x ^ 2)) _ u :=
    (((hasDerivAt_id' u).pow 2).const_mul (-(c / 2))).exp
  have he : gaussianFactor c 0 = fun x => Real.exp (-(c / 2) * x ^ 2) := by
    funext x
    simp [gaussianFactor]
  rw [he]
  exact h.deriv.trans (by simp [gaussianFactor]; ring)

private lemma gaussianFactor_coordinate (c : ℝ) (r : ℕ) :
    gaussianFactor c (r + 1) = fun u => u * gaussianFactor c r u := by
  funext u
  simp [gaussianFactor, pow_succ, mul_comm, mul_assoc]

private lemma gaussianFactor_step (c : ℝ) (m : ℕ) :
    iteratedDeriv (m + 2) (gaussianFactor c 0) 0 =
      -c * (m + 1 : ℝ) * iteratedDeriv m (gaussianFactor c 0) 0 := by
  rw [show m + 2 = (m + 1) + 1 from rfl, iteratedDeriv_succ',
    show deriv (gaussianFactor c 0) = fun u => -c * gaussianFactor c 1 u from
      funext (gaussianFactor_deriv c), iteratedDeriv_const_mul_field,
    gaussianFactor_coordinate c 0,
    iteratedDeriv_mul_coordinate _ (gaussianFactor_smooth c 0)]
  ring

private lemma gaussianFactor_one (c : ℝ) (m : ℕ) :
    iteratedDeriv (m + 1) (gaussianFactor c 1) 0 =
      (m + 1 : ℝ) * iteratedDeriv m (gaussianFactor c 0) 0 := by
  rw [gaussianFactor_coordinate c 0,
    iteratedDeriv_mul_coordinate _ (gaussianFactor_smooth c 0)]

private lemma gaussianFactor_two (c : ℝ) (m : ℕ) :
    iteratedDeriv (m + 2) (gaussianFactor c 2) 0 =
      (m + 2 : ℝ) * (m + 1 : ℝ) * iteratedDeriv m (gaussianFactor c 0) 0 := by
  rw [show m + 2 = (m + 1) + 1 from rfl, gaussianFactor_coordinate c 1,
    iteratedDeriv_mul_coordinate _ (gaussianFactor_smooth c 1), gaussianFactor_one]
  push_cast
  ring

private def oddProduct : ℕ → ℝ
  | 0 => 1
  | l + 1 => (2 * l + 1 : ℝ) * oddProduct l

private lemma oddProduct_sq (l : ℕ) :
    oddProduct l ^ 2 ≤ (2 * l : ℝ) ^ (2 * l) := by
  induction l with
  | zero => norm_num [oddProduct]
  | succ l ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : (2 * l : ℝ) ^ (2 * l) ≤ (2 * (l + 1) : ℝ) ^ (2 * l) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hq : (2 * l + 1 : ℝ) ^ 2 ≤ (2 * (l + 1) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      oddProduct (l + 1) ^ 2 = (2 * l + 1 : ℝ) ^ 2 * oddProduct l ^ 2 := by
        rw [oddProduct, mul_pow]
      _ ≤ (2 * (l + 1) : ℝ) ^ 2 * (2 * (l + 1) : ℝ) ^ (2 * l) :=
        mul_le_mul hq (ih.trans hp) (sq_nonneg _) (by positivity)
      _ = (2 * (l + 1) : ℝ) ^ (2 * (l + 1)) := by
        rw [← pow_add]
        congr 1
        omega

private lemma oddProduct_sq_odd (l : ℕ) :
    oddProduct (l + 1) ^ 2 ≤ (2 * l + 1 : ℝ) ^ (2 * l + 1) := by
  induction l with
  | zero => norm_num [oddProduct]
  | succ l ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : (2 * l + 1 : ℝ) ^ (2 * l + 1) ≤
        (2 * (l + 1) + 1 : ℝ) ^ (2 * l + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      oddProduct (l + 1 + 1) ^ 2 =
          (2 * (l + 1) + 1 : ℝ) ^ 2 * oddProduct (l + 1) ^ 2 := by
        rw [oddProduct, mul_pow]
        push_cast
        rfl
      _ ≤ (2 * (l + 1) + 1 : ℝ) ^ 2 * (2 * (l + 1) + 1 : ℝ) ^ (2 * l + 1) :=
        mul_le_mul_of_nonneg_left (ih.trans hp) (sq_nonneg _)
      _ = (2 * (l + 1) + 1 : ℝ) ^ (2 * (l + 1) + 1) := by
        rw [← pow_add]
        congr 1
        omega

private lemma oddProduct_sq_even (l : ℕ) :
    oddProduct (l + 1) ^ 2 ≤ (2 * l + 2 : ℝ) ^ (2 * l) := by
  induction l with
  | zero => norm_num [oddProduct]
  | succ l ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : (2 * l + 2 : ℝ) ^ (2 * l) ≤ (2 * (l + 1) + 2 : ℝ) ^ (2 * l) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hq : (2 * (l + 1) + 1 : ℝ) ^ 2 ≤ (2 * (l + 1) + 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      oddProduct (l + 1 + 1) ^ 2 =
          (2 * (l + 1) + 1 : ℝ) ^ 2 * oddProduct (l + 1) ^ 2 := by
        rw [oddProduct, mul_pow]
        push_cast
        rfl
      _ ≤ (2 * (l + 1) + 2 : ℝ) ^ 2 * (2 * (l + 1) + 2 : ℝ) ^ (2 * l) :=
        mul_le_mul hq (ih.trans hp) (sq_nonneg _) (by positivity)
      _ = (2 * (l + 1) + 2 : ℝ) ^ (2 * (l + 1)) := by
        rw [← pow_add]
        congr 1
        omega

private lemma gaussianFactor_even (c : ℝ) (l : ℕ) :
    iteratedDeriv (2 * l) (gaussianFactor c 0) 0 = (-c) ^ l * oddProduct l := by
  induction l with
  | zero => simp [gaussianFactor, oddProduct]
  | succ l ih =>
    rw [show 2 * (l + 1) = 2 * l + 2 from by omega, gaussianFactor_step, ih,
      oddProduct, pow_succ]
    push_cast
    ring

private lemma gaussianFactor_odd (c : ℝ) (l : ℕ) :
    iteratedDeriv (2 * l + 1) (gaussianFactor c 0) 0 = 0 := by
  induction l with
  | zero => simp [iteratedDeriv_succ', gaussianFactor_deriv, gaussianFactor]
  | succ l ih =>
    rw [show 2 * (l + 1) + 1 = (2 * l + 1) + 2 from by omega,
      gaussianFactor_step, ih, mul_zero]

private lemma gaussianFactor_low (c : ℝ) (r m : ℕ) (hm : m < r) :
    r ≤ 2 → iteratedDeriv m (gaussianFactor c r) 0 = 0 := by
  intro hr
  interval_cases r <;> interval_cases m
  · simp [gaussianFactor]
  · simp [gaussianFactor]
  · rw [gaussianFactor_coordinate c 1,
      iteratedDeriv_mul_coordinate _ (gaussianFactor_smooth c 1) 0]
    simp [gaussianFactor]

private lemma gaussianFactor_sq_bound (c : ℝ) (hc : 1 ≤ c) (r m : ℕ)
    (hr : r ≤ 2) (hm : r ≤ m) :
    (iteratedDeriv m (gaussianFactor c r) 0) ^ 2 ≤
      (c ^ (m - r)) ^ 2 * (m : ℝ) ^ m := by
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hcp (l n : ℕ) (hln : l ≤ n) : (c ^ l) ^ 2 ≤ (c ^ n) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg hc0 _) (pow_le_pow_right₀ hc hln) 2
  have hnegpow (l : ℕ) : ((-c) ^ l) ^ 2 = (c ^ l) ^ 2 := by
    induction l with
    | zero => simp
    | succ l ih =>
      calc
        ((-c) ^ (l + 1)) ^ 2 = ((-c) ^ l) ^ 2 * (-c) ^ 2 := by ring
        _ = (c ^ l) ^ 2 * c ^ 2 := by rw [ih]; ring
        _ = (c ^ (l + 1)) ^ 2 := by ring
  have hn : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by omega
  interval_cases r
  · rcases hn with he | ho
    · rw [he, gaussianFactor_even, mul_pow, hnegpow, Nat.sub_zero]
      exact mul_le_mul (hcp _ _ (by omega)) (by exact_mod_cast oddProduct_sq (m / 2))
        (sq_nonneg _) (sq_nonneg _)
    · rw [ho, gaussianFactor_odd, zero_pow (by decide)]
      positivity
  · rcases hn with he | ho
    · obtain ⟨l, hl⟩ : ∃ l, m / 2 = l + 1 := ⟨m / 2 - 1, by omega⟩
      rw [he, hl, show 2 * (l + 1) = (2 * l + 1) + 1 from by omega,
        gaussianFactor_one, gaussianFactor_odd, mul_zero, zero_pow (by decide)]
      positivity
    · rw [ho, gaussianFactor_one, gaussianFactor_even]
      have hid : ((2 * (m / 2) : ℕ) + 1 : ℝ) *
          ((-c) ^ (m / 2) * oddProduct (m / 2)) =
          (-c) ^ (m / 2) * oddProduct (m / 2 + 1) := by
        rw [oddProduct]
        push_cast
        ring
      rw [hid, mul_pow, hnegpow]
      exact mul_le_mul (hcp _ _ (by omega))
        (by exact_mod_cast oddProduct_sq_odd (m / 2)) (sq_nonneg _) (sq_nonneg _)
  · rcases hn with he | ho
    · obtain ⟨l, hl⟩ : ∃ l, m / 2 = l + 1 := ⟨m / 2 - 1, by omega⟩
      rw [he, hl, show 2 * (l + 1) = 2 * l + 2 from by omega,
        gaussianFactor_two, gaussianFactor_even]
      have hid : ((2 * l : ℕ) + 2 : ℝ) * ((2 * l : ℕ) + 1 : ℝ) *
          ((-c) ^ l * oddProduct l) =
          (-c) ^ l * ((2 * l + 2 : ℝ) * oddProduct (l + 1)) := by
        rw [oddProduct]
        push_cast
        ring
      rw [hid, mul_pow, hnegpow]
      have hp : ((2 * l + 2 : ℝ) * oddProduct (l + 1)) ^ 2 ≤
          ((2 * l + 2 : ℕ) : ℝ) ^ (2 * l + 2) := by
        push_cast
        rw [mul_pow, show 2 * l + 2 = 2 + 2 * l from by omega, pow_add]
        exact mul_le_mul_of_nonneg_left (oddProduct_sq_even l) (sq_nonneg _)
      exact mul_le_mul (hcp _ _ (by omega)) hp (sq_nonneg _) (sq_nonneg _)
    · obtain ⟨l, hl⟩ : ∃ l, m / 2 = l + 1 := ⟨m / 2 - 1, by omega⟩
      rw [ho, hl, show 2 * (l + 1) + 1 = (2 * l + 1) + 2 from by omega,
        gaussianFactor_two, gaussianFactor_odd, mul_zero, zero_pow (by decide)]
      positivity

private def coordinateDegree {d : ℕ} (j k i : Fin d) : ℕ :=
  (if i = j then 1 else 0) + (if i = k then 1 else 0)

private lemma coordinateDegree_le {d : ℕ} (j k i : Fin d) :
    coordinateDegree j k i ≤ 2 := by
  unfold coordinateDegree
  split_ifs <;> omega

private lemma coordinateDegree_sum {d : ℕ} (j k : Fin d) :
    ∑ i, coordinateDegree j k i = 2 := by
  simp [coordinateDegree, Finset.sum_add_distrib]

private lemma gaussianFamily_separable {d : ℕ} (c : ℝ) (j k : Fin d) :
    gaussianFamily c c j k =
      fun x => c * ∏ i, gaussianFactor c (coordinateDegree j k i) (x i) := by
  funext x
  have hp : ∀ i, x i ^ coordinateDegree j k i =
      (if i = j then x j else 1) * (if i = k then x k else 1) := by
    intro i
    unfold coordinateDegree
    split_ifs <;> simp_all
    ring
  have he : (∏ i, Real.exp (-(c / 2) * (x i) ^ 2)) =
      Real.exp (-(c * ∑ i, (x i) ^ 2) / 2) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    congr 1
    ring
  simp only [gaussianFactor, Finset.prod_mul_distrib, hp]
  rw [Finset.prod_ite_eq', Finset.prod_ite_eq', he]
  simp [gaussianFamily, mul_assoc]

private lemma list_sum_count {d : ℕ} (L : List (Fin d)) :
    ∑ i, L.count i = L.length := by
  induction L with
  | nil => simp
  | cons i L ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

private lemma real_prod_le_prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hga : 0 ≤ g a := hfa.trans (hfg a (Finset.mem_insert_self a s))
    have hfs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi))) hfs hga

private lemma gaussianFamily_partial_sq {d : ℕ} (c : ℝ) (hc : 1 ≤ c)
    (j k : Fin d) (L : List (Fin d)) :
    (partialDeriv (gaussianFamily c c j k) L) ^ 2 ≤
      (c ^ L.length) ^ 2 * (L.length : ℝ) ^ L.length := by
  rw [gaussianFamily_separable, partialDeriv,
    separable_iteratedFDeriv c _ (fun i => gaussianFactor_smooth c (coordinateDegree j k i))]
  simp only [Pi.zero_apply, mul_pow, ← Finset.prod_pow]
  by_cases hz : ∃ i, L.count i < coordinateDegree j k i
  · obtain ⟨i, hi⟩ := hz
    have hzero : iteratedDeriv (L.count i) (gaussianFactor c (coordinateDegree j k i)) 0 = 0 :=
      gaussianFactor_low c _ _ hi (coordinateDegree_le j k i)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hzero]; norm_num), mul_zero]
    positivity
  · have hm : ∀ i, coordinateDegree j k i ≤ L.count i := by
      simpa using hz
    have hp : (∏ i, (iteratedDeriv (L.count i)
        (gaussianFactor c (coordinateDegree j k i)) 0) ^ 2) ≤
        ∏ i, ((c ^ (L.count i - coordinateDegree j k i)) ^ 2 *
          (L.length : ℝ) ^ L.count i) := by
      apply real_prod_le_prod Finset.univ _ _ (fun i _ => sq_nonneg _)
      intro i _
      exact (gaussianFactor_sq_bound c hc _ _ (coordinateDegree_le j k i) (hm i)).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _)
            (by exact_mod_cast List.count_le_length (a := i) (l := L)) _)
          (sq_nonneg _))
    have hs : (∑ i, (L.count i - coordinateDegree j k i)) + 2 = L.length := by
      rw [← coordinateDegree_sum j k, ← Finset.sum_add_distrib]
      simpa only [Nat.sub_add_cancel (hm _)] using list_sum_count L
    have hcp : c ^ 2 * (c ^ (∑ i, (L.count i - coordinateDegree j k i))) ^ 2 ≤
        (c ^ L.length) ^ 2 := by
      rw [← mul_pow, ← pow_succ']
      exact pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ hc (by omega)) 2
    calc
      c ^ 2 * ∏ i, (iteratedDeriv (L.count i)
          (gaussianFactor c (coordinateDegree j k i)) 0) ^ 2 ≤
          c ^ 2 * ∏ i, ((c ^ (L.count i - coordinateDegree j k i)) ^ 2 *
            (L.length : ℝ) ^ L.count i) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = c ^ 2 * (c ^ (∑ i, (L.count i - coordinateDegree j k i))) ^ 2 *
          (L.length : ℝ) ^ L.length := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow,
          Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, list_sum_count, mul_assoc]
      _ ≤ (c ^ L.length) ^ 2 * (L.length : ℝ) ^ L.length :=
        mul_le_mul_of_nonneg_right hcp (by positivity)

private lemma list_count_pair {d : ℕ} (a b i : Fin d) :
    [a, b].count i = (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
  simp only [List.count_cons, List.count_nil, zero_add, beq_iff_eq]
  by_cases hia : i = a <;> by_cases hib : i = b
  · subst hia; subst hib; simp
  · subst hia; simp [hib, Ne.symm hib]
  · subst hib; simp [hia, Ne.symm hia]
  · simp [hia, hib, Ne.symm hia, Ne.symm hib]

private lemma gaussianFactor_diag_zero (c : ℝ) (r : ℕ) (hr : r ≤ 2) :
    iteratedDeriv r (gaussianFactor c r) 0 = if r = 2 then 2 else 1 := by
  interval_cases r
  · simp [gaussianFactor]
  · rw [gaussianFactor_one c 0]
    simp [gaussianFactor]
  · rw [gaussianFactor_two c 0]
    simp [gaussianFactor]

/-- **c026 / Lemma 6.5 (arXiv:2407.03833v2, p.30).**
Let `d, t ∈ ℕ`, `1 ≤ c ∈ ℝ₊` and `x ∈ ℝ^d`. Then
`f_{j,k}(x) = c x_j x_k e^{−c‖x‖²/2}` satisfies
`|∂^α f_{j,k}(0)| ≤ c^t t^{t/2}` for every multi-index `α` with `|α| = t`, and
`H_{f_{j,k}}(0) = c(E_{jk} + E_{kj})`, where `E_{jk}` is the `(0,1)`-matrix whose only
nonzero entry is the `(j,k)`-th one.

Original proof: factor `f_{j,k}(x) = √c x_j e^{−cx_j²/2} · √c x_k e^{−cx_k²/2} ·
Π_{i≠j,k} e^{−cx_i²/2}` and use the Taylor series of `e^{−cx²/2}` together with
`(2ℓ)!/ℓ! ≤ (2ℓ)^ℓ` and `(2ℓ+1)!/ℓ! ≤ (2ℓ+1)^{ℓ+1/2}`, plus `(√c)^ℓ ≤ c^ℓ`.

**Lean gap.** The product factorisation and the factorial estimates
(`Nat.factorial`-ratio bounds) are not formalised; the Hessian computation
`H_{f_{j,k}}(0) = c(E_{jk} + E_{kj})` needs a second-derivative calculation for the
Gaussian factors. The derivative is modelled with `Core.partialDeriv` (`iteratedFDeriv`
along the coordinate directions of `α`).
**Reusable deps.** `Core.partialDeriv`, `Core.hessian`, `Core.elementaryMatrix`,
`gaussianFamily`, `gaussianFamily_sum_sq_le`.
**Next tactics.** Prove `iteratedFDeriv` of a product via `iteratedFDerivWithin_prod`
style lemmas, bound the factorial ratios with `Nat.factorial_le_pow` and
`Nat.pow_le_pow_left`, then `simp [gaussianFamily, hessian]` for the Hessian. -/
theorem gaussianFamily_deriv_bound {d : ℕ} (c : ℝ) (hc : 1 ≤ c) (j k : Fin d)
    (α : List (Fin d)) :
    |partialDeriv (gaussianFamily c c j k) α| ≤
        c ^ α.length * Real.rpow (α.length : ℝ) ((α.length : ℝ) / 2) ∧
      hessian (gaussianFamily c c j k) =
        fun a b => c * (elementaryMatrix d j k a b + elementaryMatrix d k j a b) := by
  constructor
  · have hsq := gaussianFamily_partial_sq c hc j k α
    have hc0 : 0 ≤ c := le_trans (by norm_num) hc
    have hrpow_sq : (Real.rpow (α.length : ℝ) ((α.length : ℝ) / 2)) ^ 2 =
        (α.length : ℝ) ^ α.length := by
      rcases eq_or_ne α.length 0 with ht0 | ht0
      · simp [ht0]
      · change (((α.length : ℝ) ^ ((α.length : ℝ) / 2)) ^ (2 : ℕ)) = _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        simp [Real.rpow_natCast]
    have hrhs_nonneg :
        0 ≤ c ^ α.length * Real.rpow (α.length : ℝ) ((α.length : ℝ) / 2) :=
      mul_nonneg (pow_nonneg hc0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsq' : (partialDeriv (gaussianFamily c c j k) α) ^ 2 ≤
        (c ^ α.length * Real.rpow (α.length : ℝ) ((α.length : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, hrpow_sq]
      exact hsq
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq' hrhs_nonneg)
  · funext a b
    let ψ₀ : Fin d → ℝ → ℝ := fun i => gaussianFactor c (coordinateDegree j k i)
    have hψ₀ : ∀ i, ContDiff ℝ ∞ (ψ₀ i) := fun i => gaussianFactor_smooth c _
    let ψ₁ : Fin d → ℝ → ℝ := fun i => if i = b then deriv (ψ₀ i) else ψ₀ i
    have hψ₁ : ∀ i, Differentiable ℝ (ψ₁ i) := by
      intro i
      dsimp [ψ₁]
      split_ifs
      · simpa only [iteratedDeriv_one] using
          (hψ₀ i).differentiable_iteratedDeriv 1 (nat_lt_infty 1)
      · exact (hψ₀ i).differentiable (by decide)
    have hf1 : (fun x => (fderiv ℝ (gaussianFamily c c j k) x) (Pi.single b 1)) =
        fun x => c * ∏ i, ψ₁ i (x i) := by
      funext x
      rw [gaussianFamily_separable]
      exact separable_fderiv c ψ₀ (fun i => (hψ₀ i).differentiable (by decide)) x b
    have hhess : hessian (gaussianFamily c c j k) a b =
        c * ∏ i, iteratedDeriv ([a, b].count i) (ψ₀ i) 0 := by
      change (fderiv ℝ (fun x => (fderiv ℝ (gaussianFamily c c j k) x) (Pi.single b 1)) 0)
        (Pi.single a 1) = _
      rw [hf1, separable_fderiv c ψ₁ hψ₁ 0 a]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      dsimp [ψ₁]
      rw [list_count_pair]
      by_cases hia : i = a <;> by_cases hib : i = b
      · subst hia; subst hib; simp [iteratedDeriv_succ]
      · subst hia; simp [hib]
      · subst hib; simp [hia]
      · simp [hia, hib]
    rw [hhess]
    congr 1
    by_cases hmatch : (a = j ∧ b = k) ∨ (a = k ∧ b = j)
    · have hcnt : ∀ i, [a, b].count i = coordinateDegree j k i := by
        intro i
        rw [list_count_pair, coordinateDegree]
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · omega
      have hprod : (∏ i, iteratedDeriv ([a, b].count i) (ψ₀ i) 0) =
          ∏ i, (if coordinateDegree j k i = 2 then (2 : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hcnt i]
        exact gaussianFactor_diag_zero c _ (coordinateDegree_le j k i)
      rw [hprod]
      by_cases hjk : j = k
      · subst k
        have hab : a = j ∧ b = j := by simpa using hmatch
        rcases hab with ⟨ha, hb⟩
        rw [ha, hb, Finset.prod_eq_single j]
        · norm_num [coordinateDegree, elementaryMatrix]
        · intro i _ hij
          simp [coordinateDegree, hij]
        · simp
      · have hnone : ∀ i, coordinateDegree j k i ≠ 2 := by
          intro i
          unfold coordinateDegree
          split_ifs with h1 h2
          · exact False.elim (hjk (h1.symm.trans h2))
          · decide
          · decide
          · decide
        rw [Finset.prod_eq_one (fun i _ => by simp [hnone i])]
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [elementaryMatrix, hjk]
        · simp [elementaryMatrix, hjk, Ne.symm hjk]
    · have hex : ∃ i, [a, b].count i < coordinateDegree j k i := by
        by_contra hall
        push Not at hall
        have hsum_eq : ∑ i, coordinateDegree j k i = ∑ i, [a, b].count i := by
          rw [coordinateDegree_sum, list_sum_count]
          rfl
        have heq : ∀ i ∈ (Finset.univ : Finset (Fin d)),
            coordinateDegree j k i = [a, b].count i :=
          (Finset.sum_eq_sum_iff_of_le fun i _ => hall i).mp hsum_eq
        have hj := heq j (Finset.mem_univ j)
        have hk := heq k (Finset.mem_univ k)
        rw [list_count_pair, coordinateDegree] at hj hk
        by_cases hjk : j = k
        · subst k
          have hab : a = j ∧ b = j := by
            by_cases hja : j = a <;> by_cases hjb : j = b
            · exact ⟨hja.symm, hjb.symm⟩
            · subst hja; simp [hjb] at hj
            · subst hjb; simp [hja] at hj
            · simp [hja, hjb] at hj
          exact hmatch (Or.inl hab)
        · have hja : j = a ∨ j = b := by
            by_cases h1 : j = a <;> by_cases h2 : j = b
            · exact Or.inl h1
            · exact Or.inl h1
            · exact Or.inr h2
            · simp only [eq_self, hjk, h1, h2, ↓reduceIte] at hj; omega
          have hka : k = a ∨ k = b := by
            by_cases h1 : k = a <;> by_cases h2 : k = b
            · exact Or.inl h1
            · exact Or.inl h1
            · exact Or.inr h2
            · simp only [eq_self, Ne.symm hjk, h1, h2, ↓reduceIte] at hk; omega
          rcases hja with rfl | rfl <;> rcases hka with h1 | h2
          · exact False.elim (hjk h1.symm)
          · exact hmatch (Or.inl ⟨rfl, h2.symm⟩)
          · exact hmatch (Or.inr ⟨h1.symm, rfl⟩)
          · exact False.elim (hjk h2.symm)
      obtain ⟨i, hi⟩ := hex
      have hzero : iteratedDeriv ([a, b].count i) (ψ₀ i) 0 = 0 :=
        gaussianFactor_low c _ _ hi (coordinateDegree_le j k i)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
      have h1 : ¬(a = j ∧ b = k) := fun h => hmatch (Or.inl h)
      have h2 : ¬(a = k ∧ b = j) := fun h => hmatch (Or.inr h)
      simp [elementaryMatrix, h1, h2]

end Qatlib.Papers.QSpectralHess24.MainResults.LowerBound
