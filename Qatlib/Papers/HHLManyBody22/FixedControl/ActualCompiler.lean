/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.GreedyFixing
import Qatlib.Papers.HHLManyBody22.FixedControl.MultiQubitFixing

/-!
# Compiling controlled instructions on fixed clock sectors

`compileFixed` specializes a sequence of controlled matrix instructions using a list of fixed
clock values. It removes instructions with false controls, replaces instructions with true
controls by bare matrix actions, and retains instructions whose controls are unspecified.

The compiled word is exact on every clock assignment satisfying the choices and has length at
most the original word. `greedy_compiled_sector` applies this result to the event returned by
greedy clock fixing. See [BaskaranEtAl2023].

## Main statements

* `compileFixed_exact_on_sector`: On a clock assignment satisfying all choices, the compiled
  word acts exactly as the original controlled word.
* `compileFixed_length`: Compiling fixed controls never increases the instruction word length.
* `greedy_compiled_sector`: On any assignment in the event returned by greedy fixing,
  compilation using its choices preserves the original controlled word's action.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.HHLManyBody22.FixedControl
open Matrix
open Qatlib.Papers.HHLManyBody22.GreedyFixing
variable {n : ℕ} {I : Type} [Fintype I]

/-- The first Boolean value assigned to clock index `i` by the list of choices, or `none` if no
choice mentions it. -/
def chosenValue : List (Fin n×Bool)→Fin n→Option Bool
  | [],_ => none
  | c::cs,i => if c.1=i then some c.2 else chosenValue cs i

/-- If a clock assignment satisfies every listed choice, each value returned by `chosenValue`
agrees with that assignment. -/
theorem chosenValue_sound (cs : List (Fin n×Bool)) (x : ClockBits n)
    (hx : ∀c∈cs,x c.1=c.2) (i : Fin n) (b : Bool) (hb : chosenValue cs i=some b) :
    x i=b := by
  induction cs with
  | nil => simp [chosenValue] at hb
  | cons c cs ih =>
    simp only [chosenValue] at hb
    split_ifs at hb with hi
    · cases Option.some.inj hb
      exact hi ▸ hx c (by simp)
    · exact ih (fun d hd => hx d (by simp [hd])) hb

/-- A matrix instruction that is either controlled by one clock bit or applied without a
control. -/
inductive FixedInstruction (n : ℕ) (I : Type) where
  | controlled : Fin n→Matrix I I ℂ→FixedInstruction n I
  | bare : Matrix I I ℂ→FixedInstruction n I

/-- The action of an instruction on a state at a fixed clock assignment. -/
def instructionAt (g : FixedInstruction n I) (x : ClockBits n) (φ : I→ℂ) : I→ℂ :=
  match g with
  | .controlled i U => if x i then U*ᵥφ else φ
  | .bare U => U*ᵥφ

/-- Sequential execution of a list of fixed instructions at a clock assignment. -/
def instructionWordAt : List (FixedInstruction n I)→ClockBits n→(I→ℂ)→(I→ℂ)
  | [],_,φ => φ
  | g::gs,x,φ => instructionWordAt gs x (instructionAt g x φ)

/-- The instruction word obtained by removing false fixed controls, removing true fixed controls
from their gates, and retaining unspecified controls. -/
def compileFixed (cs : List (Fin n×Bool)) :
    List (Fin n×Matrix I I ℂ)→List (FixedInstruction n I)
  | [] => []
  | (i,U)::gs => match chosenValue cs i with
    | none => .controlled i U::compileFixed cs gs
    | some false => compileFixed cs gs
    | some true => .bare U::compileFixed cs gs

/-- The instruction word that keeps every supplied gate controlled by its original clock index. -/
def originalControlledWord (gs : List (Fin n×Matrix I I ℂ)) : List (FixedInstruction n I) :=
  gs.map (fun g => .controlled g.1 g.2)

/-- On a clock assignment satisfying all choices, the compiled word acts exactly as the original
controlled word. -/
theorem compileFixed_exact_on_sector (cs : List (Fin n×Bool))
    (gs : List (Fin n×Matrix I I ℂ)) (x : ClockBits n)
    (hx : ∀c∈cs,x c.1=c.2) (φ : I→ℂ) :
    instructionWordAt (compileFixed cs gs) x φ=
      instructionWordAt (originalControlledWord gs) x φ := by
  induction gs generalizing φ with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,U⟩ := g
    unfold compileFixed
    cases hb : chosenValue cs i with
    | none => simpa only [hb,instructionWordAt,originalControlledWord,List.map_cons] using
        (ih (instructionAt (.controlled i U) x φ))
    | some b =>
      have hxi := chosenValue_sound cs x hx i b hb
      cases b <;> simp only [instructionWordAt,originalControlledWord,List.map_cons,
        instructionAt,hxi,Bool.false_eq_true,if_false,if_true]
      · exact ih φ
      · exact ih (U*ᵥφ)

omit [Fintype I] in

/-- Compiling fixed controls never increases the instruction word length. See
[BaskaranEtAl2023]. -/
theorem compileFixed_length (cs : List (Fin n×Bool))
    (gs : List (Fin n×Matrix I I ℂ)) : (compileFixed cs gs).length≤gs.length := by
  induction gs with
  | nil => simp [compileFixed]
  | cons g gs ih =>
    obtain ⟨i,U⟩ := g
    unfold compileFixed
    cases hb : chosenValue cs i with
    | none => simpa only [List.length_cons] using Nat.succ_le_succ ih
    | some b => cases b <;> simp only [List.length_cons] <;> omega

/-- On any assignment in the event returned by greedy fixing, compilation using its choices
preserves the original controlled word's action. See [BaskaranEtAl2023]. -/
theorem greedy_compiled_sector {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (gs : List (Fin n×Matrix I I ℂ)) (x : ClockBits n)
    (hx : x∈(greedyFix w threshold n Finset.univ Finset.univ).event) (φ : I→ℂ) :
    instructionWordAt (compileFixed (greedyFix w threshold n Finset.univ Finset.univ).choices gs) x φ=
      instructionWordAt (originalControlledWord gs) x φ := by
  exact compileFixed_exact_on_sector _ gs x ((greedyFix_event _ _ _ _ _ _).mp hx).2 φ

end Qatlib.Papers.HHLManyBody22.FixedControl
