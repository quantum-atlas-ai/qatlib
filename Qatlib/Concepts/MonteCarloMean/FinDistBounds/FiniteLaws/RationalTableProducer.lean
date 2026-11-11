/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalNormalization
import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteLaws
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.RationalLikelihoodTransport

/-!
# Producing normalized rational probability tables

Entrywise rational approximations to a finite law are normalized into legal probability tables.
The theorem `produce` combines normalization success, total variation accuracy, output width
bounds, and an arithmetic gate cap. The statistical interpretation of total variation is
standard; see [Watrous2018].

## Main statements

* `raw_total_positive`: entrywise error with m·eps < 1 forces positive total raw mass.
* `table_tv`: normalization gives total variation error at most m·eps.
* `produce`: a legal accurate table exists with explicit width and cost bounds.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.RationalTableProducer

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FinitePrecision.ComputableInput
open BitRational BitRational.FiniteSelection BitRational.RationalNormalization
open FiniteInformationDivergence FiniteRationalLikelihood
open scoped BigOperators

variable {m : ℕ}

/-- Entrywise error at most `eps` across `m` outcomes gives total raw L1 error at most m·eps. -/
theorem raw_l1 (a : Vector ℚ m) (actual : FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ i : Fin m, |(a[i.val] : ℝ) - actual.prob i| ≤ eps) :
    (∑ i : Fin m, |(a[i.val] : ℝ) - actual.prob i|) ≤ (m : ℝ) * eps := by
  calc
    _ ≤ ∑ _i : Fin m, eps := Finset.sum_le_sum fun i _ => herr i
    _ = _ := by simp

/-- A raw table within entrywise error `eps` of a probability law has positive total mass when
m·eps < 1. -/
theorem raw_total_positive (a : Vector ℚ m) (actual : FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ i : Fin m, |(a[i.val] : ℝ) - actual.prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1) : 0 < ∑ i : Fin m, a[i.val] := by
  have h := (FiniteWeights.mass_error (fun i : Fin m => (a[i.val] : ℝ))
    actual.prob actual.sum_one).trans (raw_l1 a actual eps herr)
  have hl := (abs_le.mp h).1
  have hp : 0 < ∑ i : Fin m, (a[i.val] : ℝ) := by linarith
  exact_mod_cast hp

/-- Successful normalization of a nonnegative table with positive total mass yields nonnegative
entries summing to one. -/
theorem table_legality (a : Vector ℚ m) (r : Result m) (hr : normalize a = some r)
    (ha : ∀ i : Fin m, 0 ≤ a[i.val]) (hZ : 0 < ∑ i : Fin m, a[i.val]) :
    (∀ i : Fin m, 0 ≤ r.values[i.val]) ∧ (∑ i : Fin m, r.values[i.val]) = 1 := by
  constructor
  · intro i
    rw [normalize_value a r hr i]
    exact div_nonneg (ha i) hZ.le
  · simp_rw [normalize_value a r hr]
    rw [← Finset.sum_div, div_self hZ.ne']

/-- For nonnegative input with m·eps < 1, the normalized rational law is within total variation
m·eps of the actual law. -/
theorem table_tv (a : Vector ℚ m) (r : Result m) (hr : normalize a = some r)
    (ha : ∀ i : Fin m, 0 ≤ a[i.val]) (actual : FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ i : Fin m, |(a[i.val] : ℝ) - actual.prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1)
    (hn : ∀ i : Fin m, 0 ≤ r.values[i.val]) (hs : ∑ i : Fin m, r.values[i.val] = 1) :
    tv actual (distribution (fun i : Fin m => r.values[i.val]) hn hs) ≤ (m : ℝ) * eps := by
  have hZ := raw_total_positive a actual eps herr hsmall
  have hZR : 0 < ∑ i : Fin m, (a[i.val] : ℝ) := by exact_mod_cast hZ
  have hnn (i : Fin m) : (0 : ℝ) ≤ (a[i.val] : ℝ) := by exact_mod_cast ha i
  have hl := FiniteWeights.normalized_l1 (fun i : Fin m => (a[i.val] : ℝ))
    actual.prob hnn actual.sum_one hZR
  have he (i : Fin m) : |actual.prob i - (r.values[i.val] : ℝ)| =
      |(a[i.val] : ℝ) / (∑ j : Fin m, (a[j.val] : ℝ)) - actual.prob i| := by
    rw [normalize_value a r hr i]
    simp only [Rat.cast_div, Rat.cast_sum]
    exact abs_sub_comm _ _
  change (∑ i : Fin m, |actual.prob i - (r.values[i.val] : ℝ)|) / 2 ≤ _
  simp_rw [he]
  have hraw := raw_l1 a actual eps herr
  linarith

/-- Nonnegative entrywise approximations with m·eps < 1 produce a normalized rational law with
total variation error at most m·eps and the stated width and gate bounds. -/
theorem produce (a : Vector ℚ m) (ha : ∀ i : Fin m, 0 ≤ a[i.val])
    (actual : FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ i : Fin m, |(a[i.val] : ℝ) - actual.prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1) (B : ℕ) (hB : ∀ i : Fin m, width a[i.val] ≤ B) :
    ∃ (r : Result m) (_hr : normalize a = some r)
      (hn : ∀ i : Fin m, 0 ≤ r.values[i.val]) (hs : ∑ i : Fin m, r.values[i.val] = 1),
      tv actual (distribution (fun i : Fin m => r.values[i.val]) hn hs) ≤ (m : ℝ) * eps ∧
      (∀ i : Fin m, width r.values[i.val] ≤ B + (1 + m * (B + 1))) ∧
      r.gates ≤ m * (binomialRatAddGateCap (1 + m * (B + 1)) +
        binomialRatOpGateCap (B + (1 + m * (B + 1)))) := by
  have hZ := raw_total_positive a actual eps herr hsmall
  cases hr : normalize a with
  | none =>
    have hz := (normalize_none_iff a).mp hr
    linarith
  | some r =>
    obtain ⟨hn, hs⟩ := table_legality a r hr ha hZ
    have hb := normalize_bounds a r hr B hB
    exact ⟨r, rfl, hn, hs, table_tv a r hr ha actual eps herr hsmall hn hs, hb.1, hb.2⟩

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.RationalTableProducer
