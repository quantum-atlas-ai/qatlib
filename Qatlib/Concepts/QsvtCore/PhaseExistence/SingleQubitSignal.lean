/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
set_option warningAsError false

open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

noncomputable section

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

noncomputable def signalRotation (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Complex.I * Real.sqrt (1 - x ^ 2);
     Complex.I * Real.sqrt (1 - x ^ 2), (x : ℂ)]

noncomputable def signalReflection (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Real.sqrt (1 - x ^ 2);
     Real.sqrt (1 - x ^ 2), -(x : ℂ)]

noncomputable def zPhaseGate (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![z, star z]

noncomputable def reflectionWord (x : ℝ) (Φ : List ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Φ.foldr (fun φ M => zPhaseGate (anglePhase φ) * signalReflection x * M) 1

noncomputable def signalStep (x : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := M * signalRotation x * zPhaseGate z

noncomputable def signalWord (x : ℝ) (z0 : ℂ) (zs : List ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  zs.foldl (signalStep x) (zPhaseGate z0)

noncomputable def eq3PairStep (w : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (C w * (X * pq.1 - (1 - X ^ 2) * pq.2), C (star w) * (pq.1 + X * pq.2))

noncomputable def eq3Fold (pq : Polynomial ℂ × Polynomial ℂ) (z : ℂ) :
    Polynomial ℂ × Polynomial ℂ := eq3PairStep z pq

noncomputable def eq3Pair (z0 : ℂ) (zs : List ℂ) : Polynomial ℂ × Polynomial ℂ :=
  zs.foldl eq3Fold (C z0, 0)

@[simp] theorem reflectionWord_nil (x : ℝ) : reflectionWord x [] = 1 := rfl

@[simp] theorem reflectionWord_cons (x : ℝ) (φ : ℝ) (Φ : List ℝ) :
    reflectionWord x (φ :: Φ) =
      zPhaseGate (anglePhase φ) * signalReflection x * reflectionWord x Φ := rfl

@[simp] theorem signalWord_nil (x : ℝ) (z0 : ℂ) : signalWord x z0 [] = zPhaseGate z0 := rfl

private theorem foldl_snoc_word (M : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) (zs : List ℂ) (x : ℝ) :
    (zs ++ [w]).foldl (signalStep x) M =
      zs.foldl (signalStep x) M * signalRotation x * zPhaseGate w := by
  induction zs generalizing M with
  | nil => rfl
  | cons z zs ih =>
    rw [List.cons_append, List.foldl_cons, List.foldl_cons, ih]

@[simp] theorem signalWord_snoc (x : ℝ) (z0 w : ℂ) (zs : List ℂ) :
    signalWord x z0 (zs ++ [w]) =
      signalWord x z0 zs * signalRotation x * zPhaseGate w :=
    foldl_snoc_word _ _ _ _

@[simp] theorem eq3Pair_nil (z0 : ℂ) : eq3Pair z0 [] = (C z0, 0) := rfl

private theorem foldl_snoc_pair (init : Polynomial ℂ × Polynomial ℂ) (w : ℂ) (zs : List ℂ) :
    (zs ++ [w]).foldl eq3Fold init = eq3PairStep w (zs.foldl eq3Fold init) := by
  induction zs generalizing init with
  | nil => rfl
  | cons z zs ih =>
    rw [List.cons_append, List.foldl_cons, List.foldl_cons, ih]

@[simp] theorem eq3Pair_snoc (z0 w : ℂ) (zs : List ℂ) :
    eq3Pair z0 (zs ++ [w]) = eq3PairStep w (eq3Pair z0 zs) :=
    foldl_snoc_pair _ _ _

noncomputable def chebyshevAngles : ℕ → List ℝ
  | 0 => []
  | d + 1 => ((1 - ((d + 1 : ℕ) : ℝ)) * (Real.pi / 2)) :: List.replicate d (Real.pi / 2)

end Qatlib.Concepts.QsvtCore.PhaseExistence
