/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateTables.GrayUniversal.GrayCodeSynthesis

/-!
# Single-address phase synthesis

`grayPhase_table` synthesizes a unit-modulus phase at one computational-basis address of a
nonempty register. It embeds the phase in a diagonal two-level block on an adjacent address pair
and applies the Gray adjacent-pair construction.

The resulting word acts correctly on every state with an explicit quadratic length bound, using
the controlled-gate synthesis framework of [BarencoEtAl1995].

## Main statements

* `grayPhase_table`: constructs a legal phase word of length at most `256 * (k + 1)^2 + 2 * k`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal
open Matrix
open scoped Classical BigOperators

/-- A scalar `z` satisfying `star z * z = 1` can be applied at a single register address by a
legal reflection word of length at most `256 * (k + 1)^2 + 2 * k`. The compiled word agrees
with the single-address phase matrix on every state. -/
theorem grayPhase_table {k : ℕ} (x : Reg (k+1)) (z : ℂ) (hz : star z*z = 1) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ 256*(k+1)^2+2*k ∧ ∀ ψ : QState (Reg (k+1)),
        Run 1 (reflectionCompile gs) ψ = twoLevelMatrix (.phase x z) *ᵥ ψ := by
  let t := Fin.last k
  let y := Function.update x t (!(x t))
  have ht : x t ≠ y t := by simp [y]
  have hother : ∀ w, w ≠ t → x w = y w := by
    intro w hw
    simp [y,hw]
  have hxy : x ≠ y := fun he => ht (congrFun he t)
  let B : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 1 else z)
  have hB : B ∈ unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    change (starRingEnd ℂ) z*z = 1 at hz
    ext a b
    cases a <;> cases b <;> simp [B,Matrix.mul_apply,hz]
  obtain ⟨gs,hgs,hlen,hr⟩ := grayAdjacentPair_table x y t ht hother B hB
  have hmat : twoLevelMatrix (.pair x y B) = twoLevelMatrix (.phase x z) := by
    ext u v
    by_cases hux : u = x <;> by_cases huy : u = y <;>
      by_cases hvx : v = x <;> by_cases hvy : v = y <;>
      by_cases huv : u = v <;> simp_all [twoLevelMatrix,B]
  exact ⟨gs,hgs,hlen,fun ψ => (hr ψ).trans (congrArg (fun A => A *ᵥ ψ) hmat)⟩

end Qatlib.Concepts.GateTables.GrayUniversal
