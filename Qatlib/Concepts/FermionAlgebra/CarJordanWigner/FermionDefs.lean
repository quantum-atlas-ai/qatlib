/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.FermionAlgebra.CarJordanWigner

open Matrix

set_option autoImplicit false

def jwSign {n : ℕ} (i : Fin n) (x : Reg n) : ℂ :=
  (-1 : ℂ) ^ (∑ j : Fin i, if x (Fin.castLE (Nat.le_of_lt i.isLt) j) then 1 else 0)

def annihilation {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => if x i ∧ y = Function.update x i false then jwSign i x else 0

def creation {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => if ¬ x i ∧ y = Function.update x i true then jwSign i y else 0

def numberOp {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => if x = y ∧ x i then 1 else 0

def parityOp {n : ℕ} : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => if x = y then (-1 : ℂ) ^ (∑ i, if x i then 1 else 0) else 0

noncomputable def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliX + Complex.I • pauliY)

noncomputable def jwPauliWord {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => ∏ j : Fin n,
    if j < i then (if y j = x j then (if x j then -1 else 1 : ℂ) else 0)
    else if i < j then (if y j = x j then 1 else 0)
    else sigmaMinus (boolEquivFin2 (y j)) (boolEquivFin2 (x j))

def fermionPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
    if i < j then some (i, j) else none

noncomputable def hubbardJWTerms {n : ℕ} (t μ U : ℂ) : List (ℂ × Matrix (Reg n) (Reg n) ℂ) :=
  ((List.finRange n).map fun i : Fin n => (μ, numberOp i))
  ++ ((fermionPairs n).map fun p : Fin n × Fin n => (U, numberOp p.1 * numberOp p.2))
  ++ ((fermionPairs n).map fun p : Fin n × Fin n =>
        (t, creation p.1 * annihilation p.2 + creation p.2 * annihilation p.1))

def majorana {n : ℕ} (a : Fin (2 * n)) : Matrix (Reg n) (Reg n) ℂ :=
  have hk : a.val / 2 < n := by omega
  if a.val % 2 = 0 then
    creation ⟨a.val / 2, hk⟩ + annihilation ⟨a.val / 2, hk⟩
  else
    Complex.I • (annihilation ⟨a.val / 2, hk⟩ - creation ⟨a.val / 2, hk⟩)

noncomputable def covarianceMatrix {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b =>
    Complex.re ((Complex.I / 2) * Matrix.trace
      (Mᴴ * (majorana a * majorana b - majorana b * majorana a) * M))

noncomputable def quadraticGenerator {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  A 0 0 • (creation i * annihilation i) + A 0 1 • (creation i * annihilation j)
    + A 1 0 • (creation j * annihilation i) + A 1 1 • (creation j * annihilation j)

noncomputable def matchGate {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  NormedSpace.exp (quadraticGenerator i j A)

end Qatlib.Concepts.FermionAlgebra.CarJordanWigner
