/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
import Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhaseIsometry
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin

set_option backward.isDefEq.respectTransparency false

/-!
# Known Count Permutation

Equal actual address multiplicities construct a known permutation of copy slots.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.KnownCountPermutation
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase

/-- Equal actual address multiplicities construct a known permutation of copy slots. -/
def slotPermutation {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a) : Equiv.Perm (Fin Q) :=
  Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (h a))

/-- The constructed slot permutation matches the literal addresses without reading any unknown spin. -/
theorem slotPermutation_labels {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a) (j : Fin Q) :
    y (slotPermutation x y h j)=x j := Equiv.ofFiberEquiv_map _ _

/-- The physical spin-basis permutation depends only on known address slots and their multiplicities. -/
def spinPermutation {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a) :
    Equiv.Perm (Fin Q → Bool) :=
  Equiv.piCongrLeft' (fun _ : Fin Q => Bool) (slotPermutation x y h)

/-- The actual matrix is isometric on the entire spin register, not just the selected tensor family. -/
theorem spinPermutation_isometry {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a) :
    ((spinPermutation x y h).permMatrix ℂ).conjTranspose*(spinPermutation x y h).permMatrix ℂ=1 :=
  permutation_isometry (spinPermutation x y h)

/-- One fixed known-label permutation transports every actual unknown spin tensor amplitude. -/
theorem spinPermutation_apply {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a)
    (u : A → Bool → ℂ) (s : Fin Q → Bool) :
    (((spinPermutation x y h).permMatrix ℂ)*ᵥ
      (fun t : Fin Q → Bool => copyAmplitude u Q (fun j => (y j,t j)))) s=
        copyAmplitude u Q (fun j => (x j,s j)) := by
  rw [Matrix.permMatrix_mulVec]
  change (∏ j : Fin Q,u (y j) (s ((slotPermutation x y h).symm j)))=
    ∏ j : Fin Q,u (x j) (s j)
  have hp := Equiv.prod_comp (slotPermutation x y h)
    (fun j : Fin Q => u (y j) (s ((slotPermutation x y h).symm j)))
  rw [←hp]
  simp only [Equiv.symm_apply_apply,slotPermutation_labels]

end Qatlib.Concepts.SpinorSampling.NativeRecords.KnownCountPermutation
