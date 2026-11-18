/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingCoreDefs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

/-!
# Errors modulo CSS stabilizers

These classes distinguish equal logical action from merely equal syndrome.
They concern Pauli labels; equality of arbitrary Pauli matrices on a codespace
may additionally involve a global phase.
-/

namespace Qatlib.Concepts.ErrorCorrection.ErrorClasses

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open scoped Matrix

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]

/-- The product of the two stabilizer row spaces in the existing Pauli label type. -/
noncomputable def stabilizerSpace (c : CssData ι κX κZ) :
    Submodule (ZMod 2) (PauliLabel ι) :=
  (LinearMap.range (Matrix.mulVecLin c.hXᵀ)).prod
    (LinearMap.range (Matrix.mulVecLin c.hZᵀ))

/-- Membership in the structured submodule is the public stabilizer-label predicate. -/
theorem mem_space (c : CssData ι κX κZ) (e : PauliLabel ι) :
    e ∈ stabilizerSpace c ↔ IsStabilizerLabel c e := Iff.rfl

/-- Two errors are equivalent when their difference is a stabilizer label. -/
noncomputable def ErrorEquiv (c : CssData ι κX κZ) (e f : PauliLabel ι) : Prop :=
  e - f ∈ stabilizerSpace c

/-- The explicit error relation agrees with equality in the stabilizer quotient. -/
theorem quotient_eq (c : CssData ι κX κZ) (e f : PauliLabel ι) :
    (Submodule.Quotient.mk e : PauliLabel ι ⧸ stabilizerSpace c) =
      Submodule.Quotient.mk f ↔ ErrorEquiv c e f :=
  Submodule.Quotient.eq (stabilizerSpace c)

/-- Stabilizer error equivalence is an equivalence relation. -/
theorem error_equiv (c : CssData ι κX κZ) : Equivalence (ErrorEquiv c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact (quotient_eq c e e).mp rfl
  · intro e f h
    exact (quotient_eq c f e).mp ((quotient_eq c e f).mpr h).symm
  · intro e f g h₁ h₂
    exact (quotient_eq c e g).mp
      (((quotient_eq c e f).mpr h₁).trans ((quotient_eq c f g).mpr h₂))

end Qatlib.Concepts.ErrorCorrection.ErrorClasses
