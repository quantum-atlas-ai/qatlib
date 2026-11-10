/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorDiff
import Qatlib.Papers.OverlapGapGoh26.Resources.IndependentFaults
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.Resources.ParityGadget

abbrev Basis := Bool×Bool×Bool×Bool

def spin (b : Bool) : ℝ := if b then -1 else 1

def coordinates (b : Basis) : Fin 4 → ℝ := ![spin b.1,spin b.2.1,spin b.2.2.1,spin b.2.2.2]

def parityZ (b : Basis) : ℝ := spin b.1*spin b.2.1*spin b.2.2.1*spin b.2.2.2

theorem actual_quartic_energy (J : ℝ) (b : Basis) :
    tensorEnergy (Pi.single (id : Fin 4 → Fin 4) J) (coordinates b)=J*parityZ b := by
  rw [tensorEnergy_single]
  simp [coordinates,parityZ,Fin.prod_univ_succ,mul_assoc]

inductive Gate where
  | cnot : Fin 3 → Gate
  | phase : ℝ → Gate

def cnotBasis (i : Fin 3) (b : Basis) : Basis :=
  (b.1,b.2.1,b.2.2.1,b.2.2.2 ^^ (if i=0 then b.1 else if i=1 then b.2.1 else b.2.2.1))

def phaseFactor (θ : ℝ) (z : ℝ) : ℂ := Complex.exp (-Complex.I*(θ:ℂ)*(z:ℂ))

def runGate : Gate → (Basis → ℂ) → Basis → ℂ
  | Gate.cnot i,ψ => fun b => ψ (cnotBasis i b)
  | Gate.phase θ,ψ => fun b => phaseFactor θ (spin b.2.2.2)*ψ b

def word (θ : ℝ) : List Gate :=
  [.cnot 0,.cnot 1,.cnot 2,.phase θ,.cnot 2,.cnot 1,.cnot 0]

def runWord : List Gate → (Basis → ℂ) → Basis → ℂ
  | [],ψ => ψ
  | g::gs,ψ => runWord gs (runGate g ψ)

theorem actual_parity_word (θ : ℝ) (ψ : Basis → ℂ) :
    runWord (word θ) ψ=fun b => phaseFactor θ (parityZ b)*ψ b := by
  funext b
  rcases b with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [runWord,word,runGate,cnotBasis,spin,parityZ,phaseFactor]

theorem phaseFactor_norm (θ z : ℝ) : ‖phaseFactor θ z‖=1 := by
  simp [phaseFactor,Complex.norm_exp]

theorem actual_word_born_mass (θ : ℝ) (ψ : Basis → ℂ) :
    (∑ b : Basis,‖runWord (word θ) ψ b‖^2)=∑ b : Basis,‖ψ b‖^2 := by
  rw [actual_parity_word]
  simp only [norm_mul,phaseFactor_norm,one_mul]

theorem actual_cost_phase (γ J : ℝ) (b : Basis) :
    phaseFactor γ ((1+tensorEnergy (Pi.single (id : Fin 4 → Fin 4) J) (coordinates b))/2)=
      phaseFactor (γ/2) 1*phaseFactor (γ*J/2) (parityZ b) := by
  rw [actual_quartic_energy]
  unfold phaseFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def twoQCount (w : List Gate) : ℕ :=
    (w.map (fun g => match g with | .cnot _ => 1 | .phase _ => 0)).sum

theorem actual_word_twoQCount (θ : ℝ) : twoQCount (word θ)=6 := rfl

theorem actual_word_no_fault (e θ : ℝ) (he : e≤1) :
    Faults.independentLaw e (twoQCount (word θ)) {x | ∀ i,x i=false}=ENNReal.ofReal ((1-e)^6) := by
  simpa only [actual_word_twoQCount] using
      Faults.actual_no_fault_probability e he (twoQCount (word θ))

end Qatlib.Papers.OverlapGapGoh26.Resources.ParityGadget
