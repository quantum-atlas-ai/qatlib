/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # The historical product oracle returns unaddressed component values

Fixed source1012.2112v1 Section5. A query addresses one product component.
The old product definition instead returns all components at the selected
base input, ignoring the component part of the query. This exact two-copy
example records a model discrepancy, not a counterexample to Theorem20.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SymmetryAdv10.MainResults.ProductAudit
open Qatlib.Papers.SymmetryAdv10.MainResults

/-- The exact historical product instance, including its tuple-valued output. -/
abbrev oldProduct (P : Problem) (k : ℕ) : Problem where
  F := Fin k → P.F
  Hom := Fin k × P.Hom
  Out := Fin k → P.Out
  Tgt := Fin k → P.Tgt
  funMap := fun f x => fun i => P.funMap (f i) x.2
  target := fun f t => ∏ i, P.target (f i) (t i)

/-- A real binary oracle with a normalized one-dimensional target. -/
abbrev binaryProblem : Problem where
  F := Fin 2
  Hom := Unit
  Out := Fin 2
  Tgt := Unit
  funMap := fun f _ => f
  target := fun _ _ => 1

/-- The first component is unchanged between these actual two-copy inputs. -/
theorem addressedEqual : (fun _ : Fin 2 => (0 : Fin 2)) 0=
    (fun i : Fin 2 => i) 0 := rfl

/-- Nevertheless the old oracle output reveals a different unaddressed component. -/
theorem leaksOther :
    (oldProduct binaryProblem 2).funMap (fun _ => 0) (0,())≠
      (oldProduct binaryProblem 2).funMap (fun i => i) (0,()) := by
  intro h
  have he:=congrFun h (1 : Fin 2)
  norm_num [oldProduct,binaryProblem] at he

/-- Swapping the addressed component leaves the entire old reply unchanged. -/
theorem ignoresAddress (f : Fin 2 → Fin 2) :
    (oldProduct binaryProblem 2).funMap f (0,())=
      (oldProduct binaryProblem 2).funMap f (1,()) := rfl

end Qatlib.Papers.SymmetryAdv10.MainResults.ProductAudit
