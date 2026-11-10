/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.LinearMixing.MixingCore
import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.StationaryAndFamily
import Mathlib.Data.Int.Interval
set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Filter

noncomputable section

open scoped Topology BigOperators

def siteWindow (t : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(t : ℤ)) (t : ℤ)).filter
    (fun n => |(n : ℝ)| ≤ (t : ℝ) / Real.sqrt 2)

def uniformMass (t : ℕ) (n : ℤ) : ℝ := by
  classical
  exact if n ∈ siteWindow t then 1 / (siteWindow t).card else 0

def walkTVDistance (t : ℕ) : ℝ :=
  (1 / 2) *
    ∑ n ∈ siteWindow t, |probMass n t - 1 / (siteWindow t).card|

theorem hadamard_walk_linear_mixing_of_height (t : ℕ)
    (hcard : 0 < (siteWindow t).card)
    (hp_nonneg : ∀ n ∈ siteWindow t, 0 ≤ probMass n t)
    (hp_sum : ∑ n ∈ siteWindow t, probMass n t = 1)
    {c M : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (hMc : c ≤ M)
    (hheight : ∀ n ∈ siteWindow t, probMass n t ≤ 1 / ((siteWindow t).card : ℝ))
    (G : Finset ℤ) (hGsub : ∀ n ∈ G, n ∈ siteWindow t)
    (hGmass : ∀ n ∈ G, c / ((siteWindow t).card : ℝ) ≤ probMass n t)
    (hGlo : ∀ n ∈ siteWindow t, n ∉ G → probMass n t ≤ c / ((siteWindow t).card : ℝ))
    (hmassG : M ≤ ∑ n ∈ G, probMass n t) :
    walkTVDistance t ≤ 1 - ((M - c) / (1 - c)) * c :=
  mixing_of_height_mass (siteWindow t) (fun n => probMass n t) hcard hp_nonneg hp_sum
    hc hc1 hMc hheight G hGsub hGmass hGlo hmassG

theorem mixing_delta_lt_one {c M : ℝ} (hc : 0 < c) (hcM : c < M) (hM1 : M < 1) :
    1 - ((M - c) / (1 - c)) * c < 1 := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hβc : 0 < ((M - c) / (1 - c)) * c := by
    apply mul_pos (div_pos (by linarith) h1c) hc
  linarith

end

end Qatlib.Papers.QWalkLine00.MainResults
