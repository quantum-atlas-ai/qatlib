/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

set_option backward.isDefEq.respectTransparency false

/-!
# QMA2Sep26 — shared vocabulary for the paper-layer statements

This file fixes the finite-dimensional vocabulary used by the paper-layer
theorems of *A quantum oracle separation between QMA(2) and QMA*
(Bostanci–Grewal–Haferkamp–Huang–Hwang–Natarajan–Nirkhe, arXiv:2609.02865v1).

This module contains definitions and elementary tensor and product-value lemmas.
Sibling files prove product-value algebra and specify conditional verifier
interfaces. No oracle separation or query implementation is proved here.

## The four-register model

The paper studies the antisymmetric/symmetric projectors on four systems under
the bipartition `(12 | 34)`.  We index the `4` elementary `d`-dimensional
registers by `Fin 4 → Fin d`; a state on them is a `QState (Fin 4 → Fin d)`
(amplitudes over the computational basis `v : Fin 4 → Fin d`, i.e.
`v 0, v 1, v 2, v 3` are the basis labels of registers `1,2,3,4`).
-/

namespace Qatlib.Papers.QMA2Sep26.MainResults

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath

noncomputable section

variable {d : ℕ}

/-! ## The bipartition `(12 | 34)` -/

/-- Registers `1,2` of the `(12 | 34)` split map into the four-register index
positions `0,1` (the left block `A`). -/
def leftReg : Fin 2 → Fin 4 := Fin.castAdd 2

/-- Registers `3,4` of the `(12 | 34)` split map into the four-register index
positions `2,3` (the right block `B`). -/
def rightReg : Fin 2 → Fin 4 := Fin.natAdd 2

/-- Embed a product state `|α⟩_{12} ⊗ |β⟩_{34}` into the four-register space:
`(tensorPair α β) v = α (v ∘ leftReg) · β (v ∘ rightReg)`. -/
def tensorPair (α β : QState (Fin 2 → Fin d)) : QState (Fin 4 → Fin d) :=
  fun v => α (fun i => v (leftReg i)) * β (fun i => v (rightReg i))

/-- The defining equation of `tensorPair`: it evaluates to the product of the
two two-register amplitudes. -/
@[simp] theorem tensorPair_apply (α β : QState (Fin 2 → Fin d)) (v : Fin 4 → Fin d) :
    tensorPair α β v = α (fun i => v (leftReg i)) * β (fun i => v (rightReg i)) := rfl

/-! ## Register permutations and the symmetric / antisymmetric projectors -/

/-- The register permutation `R_π` on `(C^d)^{⊗4}` as a matrix, using the
convention `(R_π ψ)(u) = ψ(u ∘ π)` (permuting the four register labels). -/
def permMatrix (π : Equiv.Perm (Fin 4)) :
    Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
  Matrix.of fun u v => if v = (fun k => u (π k)) then 1 else 0

/-- The sign of a permutation of four registers, valued in `ℂ`. -/
def permSignC (π : Equiv.Perm (Fin 4)) : ℂ :=
  (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ)

/-- The four-copy **antisymmetric** projector
`Π_d^- = Π_anti^{d,4} = (1/4!) Σ_{π ∈ S₄} sgn(π) R_π` (Definition 3.3, Eq. (4),
with `k = 4`). -/
def antisymProjector (d : ℕ) : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
  (1 / 24 : ℂ) • ∑ π : Equiv.Perm (Fin 4), permSignC π • permMatrix (d := d) π

/-- The four-copy **symmetric** projector
`Π_d^+ = Π_sym^{d,4} = (1/4!) Σ_{π ∈ S₄} R_π` (Definition 3.4, Eq. (5),
with `k = 4`). -/
def symProjector (d : ℕ) : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
  (1 / 24 : ℂ) • ∑ π : Equiv.Perm (Fin 4), permMatrix (d := d) π

/-! ## Quadratic forms and the product value -/

/-- The quadratic form `⟨ψ|P|ψ⟩` of a matrix `P` at a state `ψ`, as a complex
number (`⟨ψ| = star ψ`, `|Pψ⟩ = P *ᵥ ψ`). -/
def quadForm {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℂ) (ψ : QState X) : ℂ :=
  dotProduct (star ψ) (P *ᵥ ψ)

/-- The real part `Re⟨ψ|P|ψ⟩`.  For Hermitian positive-semidefinite `P` this is
the Born probability of the event `P` on `|ψ⟩`. -/
def realQuadForm {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℂ) (ψ : QState X) : ℝ :=
  (quadForm P ψ).re

/-- The **product value** `hSep(P)` of Definition 3.1 specialized to the
bipartition `(12 | 34)`: the supremum of `Re⟨α|⟨β| P |α⟩|β⟩` over all normalized
product states `|α⟩|β⟩`. -/
def productValue (P : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ) : ℝ :=
  sSup { x : ℝ | ∃ α β : QState (Fin 2 → Fin d),
    Normalized α ∧ Normalized β ∧ x = realQuadForm P (tensorPair α β) }

/-- The pointwise (universal) form of the product-value bound: every normalized
product state has quadratic form at most `c`.  This is equivalent to
`productValue P ≤ c` once `productValue` is known to be attained/bounded. -/
def productValueBound (P : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ) (c : ℝ) : Prop :=
  ∀ α β : QState (Fin 2 → Fin d), Normalized α → Normalized β →
    realQuadForm P (tensorPair α β) ≤ c

/-- Membership of a value in the product-value range. -/
theorem realQuadForm_mem_productValue_range
    {P : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ}
    {α β : QState (Fin 2 → Fin d)} (hα : Normalized α) (hβ : Normalized β) :
    realQuadForm P (tensorPair α β) ∈
      { x : ℝ | ∃ α β : QState (Fin 2 → Fin d),
        Normalized α ∧ Normalized β ∧ x = realQuadForm P (tensorPair α β) } :=
  ⟨α, β, hα, hβ, rfl⟩

/-! ## Cycle counts and permutation traces

The proof of Lemma 4.2 uses `tr R_ρ = d^{C(ρ)}`, where `C(ρ)` is the number of
cycles of `ρ` (including fixed points).  For `ρ : Perm (Fin n)` the total number
of cycles is `n - (number of moved points) + (number of nontrivial cycles)`.
-/

/-- The total number of cycles of `ρ : Perm (Fin n)`, counting fixed points as
length-one cycles: `C(ρ) = (n - Σ cycleType) + |cycleType|`. -/
def totalCycles {n : ℕ} (ρ : Equiv.Perm (Fin n)) : ℕ :=
  n - ρ.cycleType.sum + ρ.cycleType.card

/-- The sign of a permutation of `n` points, valued in `ℂ` (general `n`, for the
`t`-fold tensor-power register permutations). -/
def permSignC' {n : ℕ} (ρ : Equiv.Perm (Fin n)) : ℂ :=
  (((Equiv.Perm.sign ρ : ℤˣ) : ℤ) : ℂ)

/-- `IsEvenPerm ξ` says `ξ` is an even permutation (`sign ξ = 1`). -/
def IsEvenPerm {n : ℕ} (ξ : Equiv.Perm (Fin n)) : Prop := Equiv.Perm.sign ξ = 1

end

end Qatlib.Papers.QMA2Sep26.MainResults
