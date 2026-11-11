/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnownWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightProgram

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.RiskEstimation.PolyRotation
/-! Typed source constructors for the already derived MCX, predicate/Circle
and pivot-move words. Compilation is exact list equality for the forward
program; the native inverse will only require full operator equality. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnown
open Qatlib Matrix
open scoped Classical

/-- Construction for flip Ops in the native known builders model. -/
def flipOps {N : ℕ} (xs : List (Fin N)) : List (Gate N) := xs.map Gate.x
/-- Construction for move Ops in the native known builders model. -/
def moveOps {N : ℕ} (pivot : Fin N) (xs : List (Fin N)) : List (Gate N) := xs.map (Gate.cx pivot)
/-- Construction for ccx Ops in the native known builders model. -/
def ccxOps {N : ℕ} (ts : List (CcxTriple N)) : List (Gate N) :=
  ts.map (fun t => .ccx t.1 t.2.1 t.2.2)

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem flipOps_compile {N : ℕ} (xs : List (Fin N)) : wordCompile (flipOps xs)=nativeFlipWord xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change [.inl (x,PauliX)]++wordCompile (flipOps xs)=.inl (x,PauliX)::nativeFlipWord xs
    rw [ih]
    rfl

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem moveOps_compile {N : ℕ} (pivot : Fin N) (xs : List (Fin N)) :
    wordCompile (moveOps pivot xs)=nativePivotMoves pivot xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change [.inr (pivot,x)]++wordCompile (moveOps pivot xs)=.inr (pivot,x)::nativePivotMoves pivot xs
    rw [ih]
    rfl

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem ccxOps_compile {N : ℕ} (ts : List (CcxTriple N)) : wordCompile (ccxOps ts)=ccxTriplesCompile ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change toffoliLocalSteps t.1 t.2.1 t.2.2++wordCompile (ccxOps ts)=
      toffoliLocalSteps t.1 t.2.1 t.2.2++ccxTriplesCompile ts
    rw [ih]

/-- Construction for positive Ops in the native known builders model. -/
def positiveOps {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N)) : List (Gate N) :=
  match cs with
  | [] => [.x t]
  | [a] => [.cx a t]
  | [a,b] => [.ccx a b t]
  | a::b::c::rest =>
    ccxOps (nativeAndLadder (a::b::c::rest).dropLast ws) ++
      [.ccx (subsetFlagWireCorrected (a::b::c::rest).dropLast t ws)
        ((a::b::c::rest).getLast (by simp)) t] ++
      ccxOps (nativeAndLadder (a::b::c::rest).dropLast ws).reverse

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem positiveOps_compile {N : ℕ} (cs : List (Fin N)) (t : Fin N) (ws : List (Fin N)) :
    wordCompile (positiveOps cs t ws)=nativePositiveMcx cs t ws := by
  cases cs with
  | nil => rfl
  | cons a cs =>
    cases cs with
    | nil => rfl
    | cons b cs =>
      cases cs with
      | nil => rfl
      | cons c rest =>
        change wordCompile (_++_++_)=nativePrefixMcx _ _ _ _
        rw [wordCompile_append, wordCompile_append, ccxOps_compile, ccxOps_compile]
        rfl

/-- Construction for signed Ops in the native known builders model. -/
def signedOps {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N) (ws : List (Fin N)) : List (Gate N) :=
  flipOps (nativeNegativeWires pattern) ++ positiveOps (pattern.map Prod.fst) t ws ++
    flipOps (nativeNegativeWires pattern).reverse

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem signedOps_compile {N : ℕ} (pattern : List (Fin N × Bool)) (t : Fin N) (ws : List (Fin N)) :
    wordCompile (signedOps pattern t ws)=nativeSignedMcx pattern t ws := by
  rw [signedOps, wordCompile_append, wordCompile_append, flipOps_compile, positiveOps_compile, flipOps_compile]
  rfl

/-- Construction for predicate Circle Ops in the native known builders model. -/
def predicateCircleOps {N : ℕ} (pattern : List (Fin N × Bool)) (work pivot : Fin N)
    (pool : List (Fin N)) (r : Circle) : List (Gate N) :=
  signedOps pattern work pool ++ [.cry work pivot r] ++ signedOps pattern work pool

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem predicateCircleOps_compile {N : ℕ} (pattern : List (Fin N × Bool)) (work pivot : Fin N)
    (pool : List (Fin N)) (r : Circle) :
    wordCompile (predicateCircleOps pattern work pivot pool r)=nativePredicateCircleWord pattern work pivot pool r := by
  rw [predicateCircleOps, wordCompile_append, wordCompile_append, signedOps_compile]
  rfl

/-- Construction for pair Ops in the native known builders model. -/
def pairOps {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N) (pool targets : List (Fin N))
    (r : Circle) : List (Gate N) :=
  moveOps pivot targets ++ predicateCircleOps (nativeZeroPattern controls) work pivot pool r ++
    moveOps pivot targets.reverse

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem pairOps_compile {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle) :
    wordCompile (pairOps controls work pivot pool targets r)=nativeTwoLevelWord controls work pivot pool targets r := by
  rw [pairOps, wordCompile_append, wordCompile_append, moveOps_compile, predicateCircleOps_compile, moveOps_compile]
  rfl

/-- Construction for middle Ops in the native known builders model. -/
def middleOps {N : ℕ} (labels : List (Fin N)) (work seed : Fin N) (pool : List (Fin N)) : List (Gate N) :=
  signedOps (nativeZeroPattern labels) work pool ++ [.z work] ++
    signedOps (nativeZeroPattern labels) work pool ++ [.z seed]

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem middleOps_compile {N : ℕ} (labels : List (Fin N)) (work seed : Fin N) (pool : List (Fin N)) :
    wordCompile (middleOps labels work seed pool)=nativeOriginWord labels work seed pool := by
  simp only [middleOps, wordCompile_append, signedOps_compile]
  rfl

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnown
