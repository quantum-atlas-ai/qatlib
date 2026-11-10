/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.QueryConvert

variable {I : Type*} [Fintype I] [DecidableEq I]

def flipBit (c b : Bool) : Bool := c != b

theorem flipBit_involutive (c : Bool) : Function.Involutive (flipBit c) := by
  intro b
  cases c <;> cases b <;> rfl

def oracleFlip (x : I → Bool) (p : I × Bool) : I × Bool :=
  (p.1, flipBit (x p.1) p.2)

theorem oracleFlip_involutive (x : I → Bool) : Function.Involutive (oracleFlip x) := by
  intro p
  obtain ⟨i, b⟩ := p
  show (i, flipBit (x i) (flipBit (x i) b)) = (i, b)
  rw [flipBit_involutive]

def oracleHamiltonian (x : I → Bool) : Matrix (I × Bool) (I × Bool) ℂ :=
  permMatrix (oracleFlip x)

theorem oracleHamiltonian_apply (x : I → Bool) (p q : I × Bool) :
    oracleHamiltonian x p q = if p = oracleFlip x q then 1 else 0 := rfl

theorem oracleHamiltonian_mulVec_ket (x : I → Bool) (i : I) (b : Bool) :
    oracleHamiltonian x *ᵥ Ket (i, b) = Ket (i, flipBit (x i) b) := by
  have h := applyGate_permMatrix_ket (oracleFlip_involutive x) (i, b)
  simpa using! h

theorem oracleHamiltonian_mulVec (x : I → Bool) (ψ : QState (I × Bool)) :
    oracleHamiltonian x *ᵥ ψ = fun p => ψ (oracleFlip x p) := by
  funext p
  exact applyGate_permMatrix (oracleFlip_involutive x) ψ p

theorem oracleHamiltonian_isHermitian (x : I → Bool) :
    (oracleHamiltonian x).IsHermitian :=
  permMatrix_conjTranspose (oracleFlip_involutive x)

theorem oracleHamiltonian_mul_self (x : I → Bool) :
    oracleHamiltonian x * oracleHamiltonian x = 1 :=
  permMatrix_mul_self (oracleFlip_involutive x)

theorem oracleHamiltonian_unitary (x : I → Bool) :
    oracleHamiltonian x ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  permMatrix_unitary (oracleFlip_involutive x)

theorem inner_oracleHamiltonian (x : I → Bool) (ψ φ : QState (I × Bool)) :
    Inner (oracleHamiltonian x *ᵥ ψ) (oracleHamiltonian x *ᵥ φ) = Inner ψ φ :=
  inner_applyGate (oracleHamiltonian_unitary x) ψ φ

theorem oracleHamiltonian_edge (x : I → Bool) (i : I) (b : Bool) :
    oracleHamiltonian x (i, flipBit (x i) b) (i, b) = 1 := by
  rw [oracleHamiltonian_apply]
  have h : (i, flipBit (x i) b) = oracleFlip x (i, b) := rfl
  rw [h, if_pos rfl]

end Qatlib.Papers.ContDiscWalk08.QueryConvert
