/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.FourierModel.FiberGenerator

/-!
# Strength-time rescaling of heat evolution

The heat fiber evolution is unchanged when both generator matrices are multiplied by `ε²` and
evolution time is divided by `ε²`, provided `ε` is nonzero. `actual_strength_time` records this
exact identity for the resource rescaling discussed in [JinLiu2024].

## Main statements

* `actual_strength_time`: simultaneous generator and time rescaling preserves the evolution.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.ParabolicPDE24.Resources
open Qatlib.Papers.ParabolicPDE24.FourierDefs
open Qatlib.Concepts.ChannelTheory.Naimark.EtaProjection

/-- For nonzero `ε`, scaling both heat generator matrices by `ε²` and replacing time `T` by `T /
ε²` leaves the lifted evolution unchanged. See [JinLiu2024]. -/
theorem actual_strength_time {E : Type} [Fintype E] [DecidableEq E]
    (k ε ω T : ℝ) (hε : ε≠0) (η : E→ℝ) :
    evolution ((ε^2:ℝ) •heatA₁ ε ω) ((ε^2:ℝ) •heatA₂ k ε) η (T/ε^2)=
      evolution (heatA₁ ε ω) (heatA₂ k ε) η T := by
  have hc : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hε
  unfold evolution
  congr 1
  ext p q
  simp only [hamiltonian,Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  split_ifs
  · push_cast
    field_simp [hc]
  · simp
end Qatlib.Papers.ParabolicPDE24.Resources
