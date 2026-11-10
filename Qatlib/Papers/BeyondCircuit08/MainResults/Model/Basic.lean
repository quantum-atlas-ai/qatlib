/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Model

abbrev Symbol := Bool

def hasAdjacentStar {L : ℕ} (s : Fin L → Symbol) : Bool :=
  (List.range L).any fun i =>
    if h : i + 1 < L then s ⟨i, Nat.lt_of_succ_lt h⟩ && s ⟨i + 1, h⟩ else false

def QStr (L : ℕ) : Type := {s : Fin L → Symbol // hasAdjacentStar s = false}

instance (L : ℕ) : Fintype (QStr L) := by
  unfold QStr; infer_instance

instance (L : ℕ) : DecidableEq (QStr L) := by
  unfold QStr; infer_instance

def IsStarStar {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = true

def IsStarP {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = false

def IsPStar {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = false ∧ s ⟨n, Nat.lt_succ_self n⟩ = true

def IsPP {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = false ∧ s ⟨n, Nat.lt_succ_self n⟩ = false

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsStarStar (n := n) s) :=
  fun s => by unfold IsStarStar; infer_instance

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsStarP (n := n) s) :=
  fun s => by unfold IsStarP; infer_instance

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsPStar (n := n) s) :=
  fun s => by unfold IsPStar; infer_instance

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsPP (n := n) s) :=
  fun s => by unfold IsPP; infer_instance

def StarStarBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsStarStar (n := n) s.1}

def StarPBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsStarP (n := n) s.1}

def PStarBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsPStar (n := n) s.1}

def PPBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsPP (n := n) s.1}

instance (n : ℕ) : Fintype (StarStarBasis n) := by unfold StarStarBasis; infer_instance
instance (n : ℕ) : DecidableEq (StarStarBasis n) := by unfold StarStarBasis; infer_instance
instance (n : ℕ) : Fintype (StarPBasis n) := by unfold StarPBasis; infer_instance
instance (n : ℕ) : DecidableEq (StarPBasis n) := by unfold StarPBasis; infer_instance
instance (n : ℕ) : Fintype (PStarBasis n) := by unfold PStarBasis; infer_instance
instance (n : ℕ) : DecidableEq (PStarBasis n) := by unfold PStarBasis; infer_instance
instance (n : ℕ) : Fintype (PPBasis n) := by unfold PPBasis; infer_instance
instance (n : ℕ) : DecidableEq (PPBasis n) := by unfold PPBasis; infer_instance

def goldenTau : ℝ := 2 / (1 + Real.sqrt 5)

def fibA : ℂ := Complex.exp ((-(3 * Real.pi / 5) : ℝ) * Complex.I)

def fiba : ℂ := -(fibA ^ 4)

def fibb : ℂ := fibA ^ 8

def fibc : ℂ := fibA ^ 8 * (goldenTau : ℂ) ^ 2 - fibA ^ 4 * (goldenTau : ℂ)

def tauThreeHalves : ℂ := ((Real.sqrt goldenTau : ℝ) : ℂ) * (goldenTau : ℂ)

def fibd : ℂ := fibA ^ 8 * tauThreeHalves + fibA ^ 4 * tauThreeHalves

def fibe : ℂ := fibA ^ 8 * (goldenTau : ℂ) - fibA ^ 4 * (goldenTau : ℂ) ^ 2

def fibRepEntry (n : ℕ) (c : Fin (n - 1)) (t s : Fin (n + 1) → Symbol) : ℂ :=
  let mid : Fin (n + 1) := ⟨c.1 + 1, by omega⟩
  let lv : Symbol := s ⟨c.1, by omega⟩
  let rv : Symbol := s ⟨c.1 + 2, by omega⟩
  let mv : Symbol := s mid
  if t = s then
    (if lv = false ∧ rv = false then (if mv = true then fibc else fibe)
     else if lv = true ∧ rv = true then fibb else fiba)
  else if t = Function.update s mid (!mv) then
    (if lv = false ∧ rv = false then fibd else 0)
  else 0

def blockGen {n : ℕ} (B : Type) [Fintype B] [DecidableEq B]
    (toFun : B → Fin (n + 1) → Symbol) (c : Fin (n - 1)) : Matrix B B ℂ :=
  fun t s => fibRepEntry n c (toFun t) (toFun s)

def starStarGen (n : ℕ) (c : Fin (n - 1)) : Matrix (StarStarBasis n) (StarStarBasis n) ℂ :=
  blockGen (StarStarBasis n) (fun s => s.1.1) c

def starPGen (n : ℕ) (c : Fin (n - 1)) : Matrix (StarPBasis n) (StarPBasis n) ℂ :=
  blockGen (StarPBasis n) (fun s => s.1.1) c

def pStarGen (n : ℕ) (c : Fin (n - 1)) : Matrix (PStarBasis n) (PStarBasis n) ℂ :=
  blockGen (PStarBasis n) (fun s => s.1.1) c

def ppGen (n : ℕ) (c : Fin (n - 1)) : Matrix (PPBasis n) (PPBasis n) ℂ :=
  blockGen (PPBasis n) (fun s => s.1.1) c

def BraidWord (n : ℕ) : Type := List (Fin (n - 1) × Bool)

def crossingCount {n : ℕ} (w : BraidWord n) : ℕ := w.length

def evalWord {M : Type} [Monoid M] [Inv M] {n : ℕ}
    (gen : Fin (n - 1) → M) (w : BraidWord n) : M :=
  (w.map fun g => if g.2 then gen g.1 else (gen g.1)⁻¹).prod

def normalizeGen {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Complex.sqrt M.det)⁻¹ • M

def IsSUOn (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup ι ℂ ∧ U.det = 1

def PhaseDenseOn (ι : Type) [Fintype ι] [DecidableEq ι] (G : Set (Matrix ι ι ℂ)) : Prop :=
  ∀ U : Matrix ι ι ℂ, IsSUOn ι U → ∀ ε : ℝ, 0 < ε →
    ∃ M ∈ G, ∃ θ : ℝ, ‖(Complex.exp (θ * Complex.I)) • M - U‖ ≤ ε

end Qatlib.Papers.BeyondCircuit08.MainResults.Model
