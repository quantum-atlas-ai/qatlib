/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.DysonCoefficients
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.DysonExpansion

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled BCHCommMass BCHMassProducts BCHPerturbation DysonCoefficients
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
set_option warningAsError false

theorem shift_hasSum {E : Type} [NormedAddCommGroup E] (f : ℕ → E) (x : E)
    (hf : HasSum f x) (l : ℕ) : HasSum (fun k => if l ≤ k then f (k - l) else 0) x := by
  let g := fun k => if l ≤ k then f (k - l) else 0
  have hzero : ∑ k ∈ Finset.range l, g k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact if_neg (by have := Finset.mem_range.mp hk; omega)
  have hs : HasSum (fun k => g (k + l)) x := by
    convert! hf using 1
    funext k
    dsimp only [g]
    rw [if_pos (by omega), Nat.add_sub_cancel]
  have h := (hasSum_nat_add_iff l).mp hs
  simpa only [hzero, add_zero] using! h

variable {I : Type} [Fintype I] [DecidableEq I]

def orderCoefficient (xs : List (Matrix I I ℂ)) (t : ℝ) (p k : ℕ) : Matrix I I ℂ :=
  ∑ j ∈ Finset.range (p - 1),
    if j + 1 ≤ k then powerCoefficient xs t (j + 1) (k - (j + 1)) else 0

def orderProfile (xs : List (Matrix I I ℂ)) (t : ℝ) (p k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (p - 1),
    if j + 1 ≤ k then massProfile xs t (j + 1) (k - (j + 1)) / ((j + 1).factorial : ℝ) else 0

theorem orderCoefficient_zero (xs : List (Matrix I I ℂ)) (t : ℝ) (p : ℕ) :
    orderCoefficient xs t p 0 = 0 := by
  unfold orderCoefficient
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (by omega)

theorem orderCoefficient_norm (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (t : ℝ) (p k : ℕ) : ‖orderCoefficient xs t p k‖ ≤ orderProfile xs t p k := by
  unfold orderCoefficient orderProfile
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j + 1 ≤ k
  · simp only [if_pos hj]
    exact powerCoefficient_norm xs hxs t (j + 1) (k - (j + 1))
  · simp only [if_neg hj, norm_zero, le_refl]

theorem shifted_depth_hasSum (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : ℕ) (hq : 0 < q)
    (t : ℝ) (ht : |t| ≤ r) (l : ℕ) :
    HasSum (fun k => (1 / (q : ℝ) ^ (2 * k)) •
      (if l ≤ k then powerCoefficient xs t l (k - l) else 0))
      (PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs q t) l 1) := by
  have hs := shift_hasSum _ _ (depth_hasSum xs hxs r J hc q hq t ht l) l
  convert! hs using 1
  funext k
  by_cases hk : l ≤ k
  · simp only [if_pos hk, Nat.sub_add_cancel hk]
  · simp only [if_neg hk, smul_zero]

theorem prefix_hasSum (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : ℕ) (hq : 0 < q)
    (t : ℝ) (ht : |t| ≤ r) (p : ℕ) :
    HasSum (fun k => (1 / (q : ℝ) ^ (2 * k)) • orderCoefficient xs t p k)
      (∑ j ∈ Finset.range (p - 1),
        PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs q t) (j + 1) 1) := by
  have h := hasSum_sum (s := Finset.range (p - 1))
    (fun j _ => shifted_depth_hasSum xs hxs r J hc q hq t ht (j + 1))
  simpa only [orderCoefficient, Finset.smul_sum] using! h

theorem positive_hasSum (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : ℕ) (hq : 0 < q)
    (t : ℝ) (ht : |t| ≤ r) (p : ℕ) :
    HasSum (fun k => (1 / (q : ℝ) ^ (2 * (k + 1))) • orderCoefficient xs t p (k + 1))
      (∑ j ∈ Finset.range (p - 1),
        PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs q t) (j + 1) 1) := by
  apply (hasSum_nat_add_iff
    (f := fun k => (1 / (q : ℝ) ^ (2 * k)) • orderCoefficient xs t p k) 1).mpr
  simpa only [Finset.sum_range_one, orderCoefficient_zero, smul_zero, add_zero] using!
    prefix_hasSum xs hxs r J hc q hq t ht p

theorem repetition_series (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : ℕ) (hq : 0 < q)
    (t : ℝ) (ht : |t| ≤ r) (p : ℕ) (hp : 0 < p) :
    let A := t • ((-Complex.I) • xs.sum)
    let B := perturbation xs q t
    suzukiExponentialWord (recursiveSuzukiGenerators (xs.map (fun X => (-Complex.I) • X)) 0)
      (t / q) ^ q = NormedSpace.exp A +
        (∑' k, (1 / (q : ℝ) ^ (2 * (k + 1))) • orderCoefficient xs t p (k + 1)) +
          PerturbationDyson.remainder A B p 1 ∧
      ‖PerturbationDyson.remainder A B p 1‖ ≤
        (∑' n, massProfile xs t p n) / ((q : ℝ) ^ (2 * p) * (p.factorial : ℝ)) := by
  have h := BCHPerturbation.repetition_expansion xs hxs r J hc q hq t ht p hp
  have hs := (positive_hasSum xs hxs r J hc q hq t ht p).tsum_eq
  (try dsimp only)
  constructor
  · calc
      _ = _ := h.1
      _ = _ := by rw [hs]
  · exact remainder_profile_bound xs hxs r J hc q hq t ht p hp

end Qatlib.Papers.CommutLCHS26.MainResults.DysonExpansion
