/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorDiff
import Qatlib.Papers.OverlapGapGoh26.Resources.IndependentFaults

/-!
# A four qubit parity phase gadget

`word` computes four bit parity into the last bit with three CNOTs, applies a phase, and
reverses the CNOTs. `actual_parity_word` proves the resulting amplitude action, while the
remaining results establish preservation of Born mass, the quartic cost phase factorization, and
a six CNOT count with its independent no fault measure. This formalizes the parity gadget in the
resource estimate of [GohMuller2026].

## Main statements

* `actual_parity_word`: Executing the parity gadget multiplies each basis amplitude by
  `phaseFactor θ (parityZ b)`.
* `actual_cost_phase`: The phase for the quartic cost `(1 + tensorEnergy)/2` factors as the
  constant phase `phaseFactor (γ/2) 1` times the parity phase `phaseFactor (γ*J/2) (parityZ b)`.
* `actual_word_no_fault`: For `e ≤ 1`, the independent fault measure assigns mass
  `ENNReal.ofReal ((1-e)^6)` to the event with no faults in the parity gadget's six CNOTs.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.Resources.ParityGadget

/-- The computational basis indexed by four Boolean bits. -/
abbrev Basis := Bool×Bool×Bool×Bool

/-- The real spin value `1` for false and `-1` for true. -/
def spin (b : Bool) : ℝ := if b then -1 else 1

/-- The four real spin coordinates of a computational basis state. -/
def coordinates (b : Basis) : Fin 4 → ℝ := ![spin b.1,spin b.2.1,spin b.2.2.1,spin b.2.2.2]

/-- The product of the four computational basis spin values. -/
def parityZ (b : Basis) : ℝ := spin b.1*spin b.2.1*spin b.2.2.1*spin b.2.2.2

/-- The tensor with sole coefficient `J` at the identity index tuple has energy `J * parityZ b`
at the basis spin coordinates. -/
theorem actual_quartic_energy (J : ℝ) (b : Basis) :
    tensorEnergy (Pi.single (id : Fin 4 → Fin 4) J) (coordinates b)=J*parityZ b := by
  rw [tensorEnergy_single]
  simp [coordinates,parityZ,Fin.prod_univ_succ,mul_assoc]

/-- The gate instructions consisting of a CNOT from one of the first three bits to the last bit,
or a phase on the last bit. -/
inductive Gate where
  | cnot : Fin 3 → Gate
  | phase : ℝ → Gate

/-- The basis permutation that toggles the last bit when control bit `i` is true. -/
def cnotBasis (i : Fin 3) (b : Basis) : Basis :=
  (b.1,b.2.1,b.2.2.1,b.2.2.2 ^^ (if i=0 then b.1 else if i=1 then b.2.1 else b.2.2.1))

/-- The complex phase `exp(-iθz)` for real angle `θ` and value `z`. -/
def phaseFactor (θ : ℝ) (z : ℝ) : ℂ := Complex.exp (-Complex.I*(θ:ℂ)*(z:ℂ))

/-- The action of a gate instruction on basis amplitudes, by a CNOT basis permutation or
multiplication by the last bit phase. -/
def runGate : Gate → (Basis → ℂ) → Basis → ℂ
  | Gate.cnot i,ψ => fun b => ψ (cnotBasis i b)
  | Gate.phase θ,ψ => fun b => phaseFactor θ (spin b.2.2.2)*ψ b

/-- The parity gadget consisting of three CNOTs, a phase of angle `θ`, and the three CNOTs in
reverse order. -/
def word (θ : ℝ) : List Gate :=
  [.cnot 0,.cnot 1,.cnot 2,.phase θ,.cnot 2,.cnot 1,.cnot 0]

/-- The action on amplitudes obtained by executing a list of gate instructions in order. -/
def runWord : List Gate → (Basis → ℂ) → Basis → ℂ
  | [],ψ => ψ
  | g::gs,ψ => runWord gs (runGate g ψ)

/-- Executing the parity gadget multiplies each basis amplitude by `phaseFactor θ (parityZ b)`.
See [GohMuller2026]. -/
theorem actual_parity_word (θ : ℝ) (ψ : Basis → ℂ) :
    runWord (word θ) ψ=fun b => phaseFactor θ (parityZ b)*ψ b := by
  funext b
  rcases b with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [runWord,word,runGate,cnotBasis,spin,parityZ,phaseFactor]

/-- Every phase factor `exp(-iθz)` with real `θ` and `z` has norm one. -/
theorem phaseFactor_norm (θ z : ℝ) : ‖phaseFactor θ z‖=1 := by
  simp [phaseFactor,Complex.norm_exp]

/-- The parity gadget preserves the sum of squared norms of all basis amplitudes. See
[GohMuller2026]. -/
theorem actual_word_born_mass (θ : ℝ) (ψ : Basis → ℂ) :
    (∑ b : Basis,‖runWord (word θ) ψ b‖^2)=∑ b : Basis,‖ψ b‖^2 := by
  rw [actual_parity_word]
  simp only [norm_mul,phaseFactor_norm,one_mul]

/-- The phase for the quartic cost `(1 + tensorEnergy)/2` factors as the constant phase
`phaseFactor (γ/2) 1` times the parity phase `phaseFactor (γ*J/2) (parityZ b)`. See
[GohMuller2026]. -/
theorem actual_cost_phase (γ J : ℝ) (b : Basis) :
    phaseFactor γ ((1+tensorEnergy (Pi.single (id : Fin 4 → Fin 4) J) (coordinates b))/2)=
      phaseFactor (γ/2) 1*phaseFactor (γ*J/2) (parityZ b) := by
  rw [actual_quartic_energy]
  unfold phaseFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The number of CNOT instructions in a gate word, counting each phase instruction as zero. -/
def twoQCount (w : List Gate) : ℕ :=
    (w.map (fun g => match g with | .cnot _ => 1 | .phase _ => 0)).sum

/-- The parity gadget contains exactly six CNOT instructions. See [GohMuller2026]. -/
theorem actual_word_twoQCount (θ : ℝ) : twoQCount (word θ)=6 := rfl

/-- For `e ≤ 1`, the independent fault measure assigns mass `ENNReal.ofReal ((1-e)^6)` to the
event with no faults in the parity gadget's six CNOTs. See [GohMuller2026]. -/
theorem actual_word_no_fault (e θ : ℝ) (he : e≤1) :
    Faults.independentLaw e (twoQCount (word θ)) {x | ∀ i,x i=false}=ENNReal.ofReal ((1-e)^6) := by
  simpa only [actual_word_twoQCount] using
      Faults.actual_no_fault_probability e he (twoQCount (word θ))

end Qatlib.Papers.OverlapGapGoh26.Resources.ParityGadget
