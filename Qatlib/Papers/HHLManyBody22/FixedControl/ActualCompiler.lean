/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.GreedyFixing
import Qatlib.Papers.HHLManyBody22.FixedControl.MultiQubitFixing
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.HHLManyBody22.FixedControl
open Matrix
open Qatlib.Papers.HHLManyBody22.GreedyFixing
variable {n : ℕ} {I : Type} [Fintype I]

def chosenValue : List (Fin n×Bool)→Fin n→Option Bool
  | [],_ => none
  | c::cs,i => if c.1=i then some c.2 else chosenValue cs i

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

inductive FixedInstruction (n : ℕ) (I : Type) where
  | controlled : Fin n→Matrix I I ℂ→FixedInstruction n I
  | bare : Matrix I I ℂ→FixedInstruction n I

def instructionAt (g : FixedInstruction n I) (x : ClockBits n) (φ : I→ℂ) : I→ℂ :=
  match g with
  | .controlled i U => if x i then U*ᵥφ else φ
  | .bare U => U*ᵥφ

def instructionWordAt : List (FixedInstruction n I)→ClockBits n→(I→ℂ)→(I→ℂ)
  | [],_,φ => φ
  | g::gs,x,φ => instructionWordAt gs x (instructionAt g x φ)

def compileFixed (cs : List (Fin n×Bool)) :
    List (Fin n×Matrix I I ℂ)→List (FixedInstruction n I)
  | [] => []
  | (i,U)::gs => match chosenValue cs i with
    | none => .controlled i U::compileFixed cs gs
    | some false => compileFixed cs gs
    | some true => .bare U::compileFixed cs gs

def originalControlledWord (gs : List (Fin n×Matrix I I ℂ)) : List (FixedInstruction n I) :=
  gs.map (fun g => .controlled g.1 g.2)

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

theorem greedy_compiled_sector {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (gs : List (Fin n×Matrix I I ℂ)) (x : ClockBits n)
    (hx : x∈(greedyFix w threshold n Finset.univ Finset.univ).event) (φ : I→ℂ) :
    instructionWordAt (compileFixed (greedyFix w threshold n Finset.univ Finset.univ).choices gs) x φ=
      instructionWordAt (originalControlledWord gs) x φ := by
  exact compileFixed_exact_on_sector _ gs x ((greedyFix_event _ _ _ _ _ _).mp hx).2 φ

end Qatlib.Papers.HHLManyBody22.FixedControl
