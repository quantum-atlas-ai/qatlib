/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryThreeSourceAE
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections

open Matrix
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord
open scoped Classical

variable {H K : Type}

def forwardFlag (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H → ℕ
  | .gate _ => 0
  | .forward t => if t = s then 1 else 0
  | .backward _ => 0

def backwardFlag (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H → ℕ
  | .gate _ => 0
  | .forward _ => 0
  | .backward t => if t = s then 1 else 0

def forwardCount
    (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) : ℕ := (w.map (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag s)).sum
def backwardCount
    (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) : ℕ := (w.map (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag s)).sum

@[simp] theorem forwardCount_append (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (u v : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (u ++ v) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s u + Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s v := by
  simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount]

@[simp] theorem backwardCount_append (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (u v : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (u ++ v) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s u + Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s v := by
  simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount]

@[simp] theorem forwardFlag_adjoint (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (c : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointStep c) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag s c := by cases c <;> rfl

@[simp] theorem backwardFlag_adjoint (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (c : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointStep c) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag s c := by cases c <;> rfl

theorem forwardCount_adjoint (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord w) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s w := by
  simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord, List.map_map, Function.comp_def, List.map_reverse]

theorem backwardCount_adjoint (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord w) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s w := by
  simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord, List.map_map, Function.comp_def, List.map_reverse]

@[simp] theorem forwardFlag_lift (F : Matrix H H ℂ → Matrix K K ℂ) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (c : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.liftStep F c) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag s c := by cases c <;> rfl

@[simp] theorem backwardFlag_lift (F : Matrix H H ℂ → Matrix K K ℂ) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (c : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.liftStep F c) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag s c := by cases c <;> rfl

theorem forwardCount_lift (F : Matrix H H ℂ → Matrix K K ℂ) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.liftWord F w) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s w := by
  simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.liftWord, List.map_map, Function.comp_def]

theorem backwardCount_lift (F : Matrix H H ℂ → Matrix K K ℂ) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.liftWord F w) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s w := by
  simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.liftWord, List.map_map, Function.comp_def]

theorem queryCount_directions (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s w = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s w + Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp_all [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryFlag, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag,
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag] <;> omega

section PhysicalWords
variable [Fintype H] [DecidableEq H]

theorem forwardCount_tensor (J : Type) [Fintype J] [DecidableEq J]
    (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord J w) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s w :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_lift _ s w

theorem backwardCount_tensor (J : Type) [Fintype J] [DecidableEq J]
    (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (w : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.tensorWord J w) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s w :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_lift _ s w

theorem grover_directions (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions Aword seed S) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword := by
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleGrover.instructions, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_append, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_append,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_adjoint, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_adjoint, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_tensor, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_tensor]
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.queryCount_directions, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount]
  simp [Nat.add_comm]

theorem substitute_balanced (body : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (outer : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) (hbal : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s body = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s body) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount outer * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s body ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute body outer) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount outer * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s body := by
  induction outer with
  | nil => simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
  | cons c cs ih =>
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.substitute_cons, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_append, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_append,
      ih.1, ih.2]
    cases c with
    | gate V => simp [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount,
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardFlag, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardFlag, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
    | forward => simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]; constructor <;> ring
    | backward =>
      simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleSubstitution.expand, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_adjoint,
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_adjoint, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
      constructor <;> rw [hbal] <;> ring

theorem ae_directions (M : ℕ) (hM : 0 < M) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) =
      M * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword + (M-1) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S) =
      M * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword + (M-1) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword := by
  have houter : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer (H := H) M) = M - 1 := by
    have hc :=
        (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.counted_offgrid_qpe_clean_flag M hM (1 : Matrix H H ℂ) (0 : Qatlib.Foundations.PureStateMath.QState H)).2
    have hr :=
        Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_counts
        (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit (I := H) M)
    exact hr.1.trans hc.1
  have hg :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.grover_directions Aword seed S s
  have hbF : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword := by
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_tensor, hg.1]
  have hbB : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword := by
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_tensor, hg.2]
  have hbal : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S) := hbF.trans hbB.symm
  have hsub := Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.substitute_balanced (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.body M Aword seed S)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.outer M) s hbal
  have hm : M = (M-1) + 1 := by omega
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.qpeWord,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_append, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_append, hsub.1, hsub.2, houter, hbF, hbB,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.initWord, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_tensor, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_tensor,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.queryCount_directions]
  have hmf : M * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword = (M-1) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword + Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword := by
    conv_lhs => rw [hm]
    simp [Nat.add_mul]
  have hmb : M * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword = (M-1) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword + Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword := by
    conv_lhs => rw [hm]
    simp [Nat.add_mul]
  rw [hmf, hmb]
  constructor <;> ring

theorem ae_inverse_directions (M : ℕ) (hM : 0 < M) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (s : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S)) =
      M * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword + (M-1) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.adjointWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions M Aword seed S)) =
      M * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount s Aword + (M-1) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount s Aword := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.forwardCount_adjoint, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.backwardCount_adjoint]
  exact ⟨(Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.ae_directions M hM Aword seed S s).2, (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections.ae_directions M hM Aword seed S s).1⟩

end PhysicalWords
end Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleDirections
