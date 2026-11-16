/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
public import Qatlib.Foundations.PureStateMath.Tensor
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A genuine zero-query source word for constant classical output

Demand: MinorClosed10 Lemma4.1, the historical promise with no marked
items. A concrete known unitary swaps the none payload with the fixed
output and makes no oracle calls. No final query-cost bound is a premise.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix
namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools.ConstantCost
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
variable {E : Type}

/-- The actual clean basis coordinate with false tag and one workspace coordinate. -/
def cleanBasis (n q : ℕ) (z : Option E) : SourceSpace n q (Option E) 1 :=
  ((0,0),((false,z),0))

variable [DecidableEq E]

/-- Exchange the empty payload and one prescribed output, fixing all other payloads. -/
def flipOut (e : E) (z : Option E) : Option E :=
  if z = none then some e else if z = some e then none else z

/-- The actual payload exchange is an involution. -/
theorem flipTwice (e : E) (z : Option E) : flipOut e (flipOut e z) = z := by
  by_cases hz : z = none
  · subst z
    simp [flipOut]
  · by_cases he : z = some e
    · subst z
      simp [flipOut]
    · simp [flipOut, hz, he]

/-- The actual nested tensor clean state is the corresponding single computational basis ket. -/
theorem cleanKet (n q : ℕ) (z : Option E) :
    sourceClean n q 1 (by decide) false (Ket z) = Ket (cleanBasis n q z) := by
  simp [sourceClean, cleanBasis, tensorState_ket_ket]

variable [Fintype E]

/-- The real source-function model computes a fixed output with a legal known unitary and zero oracle calls. -/
theorem zeroCalls {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (e : E) (f : X → E) (hf : ∀ x, f x = e) :
    sourceFunctionQ input f = 0 := by
  let σ : SourceSpace n q (Option E) 1 → SourceSpace n q (Option E) 1 :=
    fun p => (p.1, ((p.2.1.1, flipOut e p.2.1.2), p.2.2))
  have hs : Function.Involutive σ := by
    rintro ⟨a, ⟨⟨tag,z⟩,w⟩⟩
    change (a,((tag,flipOut e (flipOut e z)),w)) = (a,((tag,z),w))
    rw [flipTwice]
  let U := permMatrix σ
  let C : SourceWord (SourceSpace n q (Option E) 1) := [.inl U]
  have hlegal : sourceWordLegal C := by
    intro a ha
    have he : a = .inl U := List.mem_singleton.mp ha
    subst a
    exact permMatrix_unitary hs
  have hout (x : X) : sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q 1 (by decide) false (Ket none) = Ket (cleanBasis n q (some e)) := by
    rw [cleanKet]
    have he := applyGate_permMatrix_ket hs (cleanBasis n q (none : Option E))
    simpa [sourceWordMatrix, C, U, ApplyGate, σ, cleanBasis, flipOut] using he
  apply le_antisymm
  · unfold sourceFunctionQ
    apply sInf_le
    refine ⟨1, by decide, C, ?_, hlegal, ?_⟩
    · simp [C, sourceWordCalls]
    · intro x
      rw [hout]
      norm_num [MeasureProb, bornProb_ket, cleanBasis, hf x]
  · exact zero_le

end Qatlib.Concepts.GramQueryCore.LowerBoundTools.ConstantCost
