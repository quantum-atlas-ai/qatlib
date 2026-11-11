/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.TwoParticleAntisym
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Onsite double-occupation phase circuits

The occupation basis has two spin wires per site. `word` applies a diagonal phase at each listed
site precisely when both spin occupations are present; `word_evolution` identifies its action
with the onsite Hamiltonian evolution and `full_pass_resources` counts the gates in a complete
pass.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `gate_local`: The site phase gate equals its two-wire matrix entry when the configurations
  agree outside the site, and is zero otherwise.
* `word_evolution`: The onsite circuit implements exactly the Hamiltonian evolution of the
  diagonal onsite energy.
* `full_pass_resources`: Applying the onsite gate once at each of the `m` sites gives a unitary
  circuit with no queries and exactly `m` gates.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

/-- The occupation basis with one Boolean wire for each site and spin label. -/
abbrev Basis (m : ℕ) := (Fin m × Bool) → Bool

/-- The site and spin wire set contains exactly `2 * m` wires. [AbramsLloyd1997] -/
theorem wire_count (m : ℕ) : Fintype.card (Fin m × Bool) = 2*m := by simp; omega

/-- The phase `exp(-iθ)` when both Boolean occupations are true, and `1` otherwise. -/
def scalar (θ : ℝ) (b c : Bool) : ℂ :=
  if b && c then Complex.exp (-Complex.I * θ) else 1

/-- The diagonal two-wire phase matrix determined by `scalar`. -/
def localPhase (θ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal (fun z => scalar θ z.1 z.2)

/-- The diagonal phase gate acting on the two spin occupations at site `i`. -/
def gate {m : ℕ} (i : Fin m) (θ : ℝ) : Matrix (Basis m) (Basis m) ℂ :=
  Matrix.diagonal (fun x => scalar θ (x (i,false)) (x (i,true)))

/-- Two occupation configurations agree on all wires whose site differs from `i`. -/
def Outside {m : ℕ} (i : Fin m) (x y : Basis m) : Prop :=
  ∀ k : Fin m × Bool, k.1 ≠ i → x k = y k

/-- The site phase gate equals its two-wire matrix entry when the configurations agree outside
the site, and is zero otherwise. [AbramsLloyd1997] -/
theorem gate_local {m : ℕ} (i : Fin m) (θ : ℝ) (x y : Basis m) :
    gate i θ x y = if Outside i x y then
      localPhase θ (x (i,false),x (i,true)) (y (i,false),y (i,true)) else 0 := by
  by_cases h : x = y
  · subst y
    simp [gate,localPhase,Outside]
  · by_cases ho : Outside i x y
    · have hp : (x (i,false),x (i,true)) ≠ (y (i,false),y (i,true)) := by
        intro hp
        apply h
        funext k
        rcases k with ⟨j,b⟩
        by_cases hj : j=i
        · subst j
          cases b
          · exact congrArg Prod.fst hp
          · exact congrArg Prod.snd hp
        · exact ho (j,b) hj
      simp [gate,localPhase,h,ho,hp]
    · simp [gate,h,ho]

/-- Every double-occupation phase scalar has squared norm one. -/
theorem scalar_normSq (θ : ℝ) (b c : Bool) : Complex.normSq (scalar θ b c)=1 := by
  have he : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  simp only [neg_mul] at he
  cases b <;> cases c <;> simp [scalar,Complex.normSq_eq_norm_sq,he]

/-- A finite diagonal matrix whose entries have squared norm one is unitary. -/
theorem diagonal_unitary {J : Type} [Fintype J] [DecidableEq J]
    (f : J → ℂ) (hf : ∀ x,Complex.normSq (f x)=1) :
    Matrix.diagonal f ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  have h : (fun i => (star f) i * f i) = (fun _ => (1 : ℂ)) := by
    funext i
    rw [Pi.star_apply,show star (f i)=(starRingEnd ℂ) (f i) from rfl,
      ← Complex.normSq_eq_conj_mul_self,hf i]
    rfl
  rw [h,Matrix.diagonal_one]

/-- The two-wire double-occupation phase matrix is unitary. [AbramsLloyd1997] -/
theorem localPhase_unitary (θ : ℝ) :
    localPhase θ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  diagonal_unitary _ (fun z => scalar_normSq θ z.1 z.2)

/-- The phase gate at a single site is unitary on the full occupation basis. -/
theorem gate_unitary {m : ℕ} (i : Fin m) (θ : ℝ) :
    gate i θ ∈ Matrix.unitaryGroup (Basis m) ℂ :=
  diagonal_unitary _ (fun x => scalar_normSq θ (x (i,false)) (x (i,true)))

/-- Applying the site gate multiplies each amplitude by the phase determined by the two
occupations at that site. -/
theorem gate_apply {m : ℕ} (i : Fin m) (θ : ℝ) (ψ : QState (Basis m)) (x : Basis m) :
    ApplyGate (gate i θ) ψ x = scalar θ (x (i,false)) (x (i,true))*ψ x := by
  simp [gate,ApplyGate,Matrix.mulVec_diagonal]

/-- The circuit applying one onsite phase gate for each site in the list, with angle `time * V
i`. -/
def word {m : ℕ} (sites : List (Fin m)) (V : Fin m → ℝ) (time : ℝ) : Circuit (Basis m) :=
  sites.map fun i => .gate (gate i (time * V i))

/-- The onsite circuit is unitary, has no queries, and has one gate for each listed site. -/
theorem word_resources {m : ℕ} (sites : List (Fin m)) (V : Fin m → ℝ) (time : ℝ) :
    IsUnitaryCircuit (word sites V time) ∧ QueryCount (word sites V time)=0 ∧
      GateCount (word sites V time)=sites.length := by
  refine ⟨?_,?_,?_⟩
  · intro U hU
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hU
    cases hi
    exact gate_unitary _ _
  · induction sites with
    | nil => rfl
    | cons i sites ih => exact ih
  · induction sites with
    | nil => rfl
    | cons i sites ih => exact congrArg (·+1) ih

/-- The sum of the onsite potentials at doubly occupied sites in the given list, with
repetitions counted. -/
def energy {m : ℕ} (sites : List (Fin m)) (V : Fin m → ℝ) (x : Basis m) : ℝ :=
  (sites.map fun i => if x (i,false) && x (i,true) then V i else 0).sum

/-- Running the onsite circuit multiplies each amplitude by `exp(-i * time * energy sites V x)`. -/
theorem word_apply {m : ℕ} (sites : List (Fin m)) (V : Fin m → ℝ) (time : ℝ)
    (ψ : QState (Basis m)) (x : Basis m) :
    Run 1 (word sites V time) ψ x =
      Complex.exp (-Complex.I * (time * energy sites V x)) * ψ x := by
  induction sites generalizing ψ with
  | nil => simp [word,energy]
  | cons i sites ih =>
    change Run 1 (word sites V time) (ApplyGate (gate i (time*V i)) ψ) x = _
    rw [ih,gate_apply]
    simp only [energy,List.map_cons,List.sum_cons]
    by_cases hi : x (i,false) = true ∧ x (i,true) = true
    · simp only [scalar,Bool.and_eq_true]
      rw [if_pos hi,if_pos hi]
      rw [← mul_assoc,← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp [scalar,hi]

/-- The diagonal onsite Hamiltonian whose entries are the occupation energies. -/
def hamiltonian {m : ℕ} (sites : List (Fin m)) (V : Fin m → ℝ) :
    Matrix (Basis m) (Basis m) ℂ := Matrix.diagonal (fun x => (energy sites V x : ℂ))

/-- The onsite circuit implements exactly the Hamiltonian evolution of the diagonal onsite
energy. [AbramsLloyd1997] -/
theorem word_evolution {m : ℕ} (sites : List (Fin m)) (V : Fin m → ℝ) (time : ℝ)
    (ψ : QState (Basis m)) :
    Run 1 (word sites V time) ψ =
      ApplyGate (HamiltonianEvolution (hamiltonian sites V) time) ψ := by
  funext x
  rw [word_apply]
  unfold HamiltonianEvolution hamiltonian
  rw [← Matrix.diagonal_smul,Matrix.exp_diagonal,Pi.exp_def]
  simp only [Pi.smul_apply,smul_eq_mul,← Complex.exp_eq_exp_ℂ]
  simp only [ApplyGate,Matrix.mulVec_diagonal]
  congr 2
  ring

/-- Applying the onsite gate once at each of the `m` sites gives a unitary circuit with no
queries and exactly `m` gates. [AbramsLloyd1997] -/
theorem full_pass_resources (m : ℕ) (V : Fin m → ℝ) (time : ℝ) :
    IsUnitaryCircuit (word (Finset.univ.toList) V time) ∧
    QueryCount (word (Finset.univ.toList) V time)=0 ∧
    GateCount (word (Finset.univ.toList) V time)=m := by
  simpa using word_resources (Finset.univ.toList) V time

/-- The energy of a complete pass is the sum of `V i` over all doubly occupied sites.
[AbramsLloyd1997] -/
theorem full_pass_energy (m : ℕ) (V : Fin m → ℝ) (x : Basis m) :
    energy (Finset.univ.toList) V x =
      ∑ i : Fin m, if x (i,false) && x (i,true) then V i else 0 := by
  simp [energy]

end Qatlib.Papers.ManyBodyFermi97.MainResults.OnsiteWord
