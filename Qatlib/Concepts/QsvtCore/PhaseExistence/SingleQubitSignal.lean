/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT

/-!
# Single-qubit signal and reflection words

`signalRotation`, `signalReflection`, and `zPhaseGate` define the two-dimensional matrix
primitives used in quantum signal processing. The module builds their ordered words and the
polynomial recurrence `eq3Pair`, and supplies recurrence identities for appending phases. See
[GilyenSuLowWiebe2019].

## Main statements

* `signalWord` and `reflectionWord`: ordered products of signal and phase matrices.
* `eq3Pair_snoc`: the polynomial pair recurrence for an appended phase.
* `chebyshevAngles`: a phase-angle list indexed by the target degree.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

noncomputable section

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The two-dimensional signal matrix with diagonal entries `x` and off-diagonal entries `I *
sqrt (1 - x^2)`. -/
noncomputable def signalRotation (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Complex.I * Real.sqrt (1 - x ^ 2);
     Complex.I * Real.sqrt (1 - x ^ 2), (x : ℂ)]

/-- The two-dimensional real signal matrix with diagonal entries `x` and `-x` and off-diagonal
entries `sqrt (1 - x^2)`, as in [Gilyén et al., Definition 7][GilyenSuLowWiebe2019]. -/
noncomputable def signalReflection (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Real.sqrt (1 - x ^ 2);
     Real.sqrt (1 - x ^ 2), -(x : ℂ)]

/-- The diagonal matrix with entries `z` and its complex conjugate. -/
noncomputable def zPhaseGate (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![z, star z]

/-- The ordered product of phase gates followed by signal reflections, folded from the right
over the angle list. -/
noncomputable def reflectionWord (x : ℝ) (Φ : List ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Φ.foldr (fun φ M => zPhaseGate (anglePhase φ) * signalReflection x * M) 1

/-- Append a signal rotation and a phase gate to a two-dimensional matrix by right
multiplication. -/
noncomputable def signalStep (x : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := M * signalRotation x * zPhaseGate z

/-- The signal word obtained by folding `signalStep` from the initial phase gate `zPhaseGate
z0`. -/
noncomputable def signalWord (x : ℝ) (z0 : ℂ) (zs : List ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  zs.foldl (signalStep x) (zPhaseGate z0)

/-- The polynomial pair update `(w * (X * P - (1 - X^2) * Q), star w * (P + X * Q))`, with
scalars embedded as constant polynomials. -/
noncomputable def eq3PairStep (w : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (C w * (X * pq.1 - (1 - X ^ 2) * pq.2), C (star w) * (pq.1 + X * pq.2))

/-- The fold operation applying `eq3PairStep` to a polynomial pair and the next scalar. -/
noncomputable def eq3Fold (pq : Polynomial ℂ × Polynomial ℂ) (z : ℂ) :
    Polynomial ℂ × Polynomial ℂ := eq3PairStep z pq

/-- The polynomial response pair obtained by folding the phase list from `(C z0, 0)`. -/
noncomputable def eq3Pair (z0 : ℂ) (zs : List ℂ) : Polynomial ℂ × Polynomial ℂ :=
  zs.foldl eq3Fold (C z0, 0)

/-- The reflection word of an empty angle list is the identity matrix. -/
@[simp] theorem reflectionWord_nil (x : ℝ) : reflectionWord x [] = 1 := rfl

/-- Prepending an angle to a reflection word prepends its phase gate and signal reflection. -/
@[simp] theorem reflectionWord_cons (x : ℝ) (φ : ℝ) (Φ : List ℝ) :
    reflectionWord x (φ :: Φ) =
      zPhaseGate (anglePhase φ) * signalReflection x * reflectionWord x Φ := rfl

/-- The signal word of an empty list is its initial phase gate. -/
@[simp] theorem signalWord_nil (x : ℝ) (z0 : ℂ) : signalWord x z0 [] = zPhaseGate z0 := rfl

/-- Appending a scalar to the fold defining a signal word appends its signal rotation and phase
gate. -/
private theorem foldl_snoc_word (M : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) (zs : List ℂ) (x : ℝ) :
    (zs ++ [w]).foldl (signalStep x) M =
      zs.foldl (signalStep x) M * signalRotation x * zPhaseGate w := by
  induction zs generalizing M with
  | nil => rfl
  | cons z zs ih =>
    rw [List.cons_append, List.foldl_cons, List.foldl_cons, ih]

/-- Appending a scalar to the phase list right-multiplies the signal word by the signal rotation
and the new phase gate. -/
@[simp] theorem signalWord_snoc (x : ℝ) (z0 w : ℂ) (zs : List ℂ) :
    signalWord x z0 (zs ++ [w]) =
      signalWord x z0 zs * signalRotation x * zPhaseGate w :=
    foldl_snoc_word _ _ _ _

/-- The polynomial pair for an empty phase list is `(C z0, 0)`. -/
@[simp] theorem eq3Pair_nil (z0 : ℂ) : eq3Pair z0 [] = (C z0, 0) := rfl

/-- Appending a scalar to a polynomial-pair fold applies one `eq3PairStep` to the previous fold
result. -/
private theorem foldl_snoc_pair (init : Polynomial ℂ × Polynomial ℂ) (w : ℂ) (zs : List ℂ) :
    (zs ++ [w]).foldl eq3Fold init = eq3PairStep w (zs.foldl eq3Fold init) := by
  induction zs generalizing init with
  | nil => rfl
  | cons z zs ih =>
    rw [List.cons_append, List.foldl_cons, List.foldl_cons, ih]

/-- The polynomial pair for a phase list with an appended scalar is obtained by one
`eq3PairStep`. -/
@[simp] theorem eq3Pair_snoc (z0 w : ℂ) (zs : List ℂ) :
    eq3Pair z0 (zs ++ [w]) = eq3PairStep w (eq3Pair z0 zs) :=
    foldl_snoc_pair _ _ _

/-- The empty angle list at degree zero and, at positive degree `d + 1`, the angle `(1 - (d +
1)) * π / 2` followed by `d` copies of `π / 2`. -/
noncomputable def chebyshevAngles : ℕ → List ℝ
  | 0 => []
  | d + 1 => ((1 - ((d + 1 : ℕ) : ℝ)) * (Real.pi / 2)) :: List.replicate d (Real.pi / 2)

end Qatlib.Concepts.QsvtCore.PhaseExistence
