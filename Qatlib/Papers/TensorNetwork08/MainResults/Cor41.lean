/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Circuit
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor41

open Qatlib.Papers.TensorNetwork08.MainResults.Circuit
open Qatlib.Foundations.TableAccess.ReversibleTable

theorem fig6_gate_unitary {n : ℕ} (a : Fin n) :
    permMatrix (cnotFun a) ∈ Matrix.unitaryGroup (Reg n × Bool) ℂ :=
  permMatrix_unitary (cnotFun_involutive a)

theorem fig6_value_mem_unit {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (a : Fin n)
    (hQ : ∑ s : Reg n, ‖Q s (zeroReg n)‖ ^ 2 = 1) :
    0 ≤ p0 Q a ∧ p0 Q a ≤ 1 :=
  ⟨p0_nonneg Q a, p0_le_one a hQ⟩

theorem corollary4_1_promise_decision
    (Δ p0 r : ℝ) (hΔ : 0 < Δ) (happ : |Δ * p0 - r| < Δ / 6) :
    (2 / 3 ≤ p0 → Δ / 2 < r) ∧ (p0 ≤ 1 / 3 → r < Δ / 2) := by
  obtain ⟨hlow, hhigh⟩ := abs_lt.1 happ
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem corollary4_1_decides
    (Δ p0 r : ℝ) (hΔ : 0 < Δ) (happ : |Δ * p0 - r| < Δ / 6)
    (hpromise : p0 ≤ 1 / 3 ∨ 2 / 3 ≤ p0) :
    (r > Δ / 2 ∧ 2 / 3 ≤ p0) ∨ (r ≤ Δ / 2 ∧ p0 ≤ 1 / 3) := by
  obtain ⟨hyes, hno⟩ := corollary4_1_promise_decision Δ p0 r hΔ happ
  rcases hpromise with h | h
  · right
    exact ⟨le_of_lt (hno h), h⟩
  · left
    exact ⟨hyes h, h⟩

end Qatlib.Papers.TensorNetwork08.MainResults.Cor41
