/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.StatDistance
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

theorem stationary_of_reversible (M : MC n) (π : Dim n → ℝ)
    (hst : IsStochastic M) (hrev : IsReversible M π) (j : Dim n) :
    ∑ i, M i j * π i = π j := by
  calc ∑ i, M i j * π i = ∑ i, M j i * π j :=
        Finset.sum_congr rfl (fun i _ => hrev.2 i j)
    _ = ∑ i, π j * M j i := Finset.sum_congr rfl (fun i _ => by ring)
    _ = π j * ∑ i, M j i := by rw [Finset.mul_sum]
    _ = π j * 1 := by rw [hst j]
    _ = π j := mul_one _

theorem stationary_of_stronglySamplable (M : MC n) (π : Dim n → ℝ)
    (h : StronglySamplable M π) (j : Dim n) :
    ∑ i, M i j * π i = π j :=
  stationary_of_reversible M π h.stochastic h.reversible j

theorem slowlyVarying_overlap_pos {T : ℕ} (π : Fin (T + 1) → Dim n → ℝ)
    (h : SlowlyVarying π) (t : Fin T) :
    0 < ∑ i : Dim n, Real.sqrt (π (Fin.castSucc t) i * π t.succ i) := by
  obtain ⟨c, k, hc, hle⟩ := h t
  have hcpos : (0:ℝ) < (c : ℝ) * ((n : ℝ) + 1) ^ k := by positivity
  have hpos : (0:ℝ) < 1 / ((c : ℝ) * ((n : ℝ) + 1) ^ k) := by positivity
  linarith

theorem overlap_le_one_prob (p q : Dim n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, Real.sqrt (p i * q i) ≤ 1 :=
  StatDistance.overlap_le_one p q hp hq hp1 hq1

theorem one_sub_tv_le_overlap_prob (p q : Dim n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    1 - (1 / 2) * ∑ i, |p i - q i| ≤ ∑ i, Real.sqrt (p i * q i) :=
  StatDistance.one_sub_tv_le_overlap p q hp hq hp1 hq1

end Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling
