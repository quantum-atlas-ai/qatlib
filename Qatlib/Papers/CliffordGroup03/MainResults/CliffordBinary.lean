/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CliffordGroup03.MainResults.Definitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

namespace Qatlib.Papers.CliffordGroup03.MainResults

def dvec {n : ℕ} (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) : BV (2 * n) :=
  diagVec (Cᵀ * Umat n * C)

def thm1_b2 {n : ℕ} (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (b1 : BV (2 * n)) :
    BV (2 * n) :=
  C.mulVec b1

def thm1_delta2 {n : ℕ} (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2))
    (b1 : BV (2 * n)) (δ1 : ZMod 2) : ZMod 2 :=
  booleanDot (dvec C) b1 + δ1

def thm1_eps2 {n : ℕ} (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h : BV (2 * n))
    (b1 : BV (2 * n)) (δ1 ε1 : ZMod 2) : ZMod 2 :=
  (let d := dvec C
   let Cb := CbarMat C d
   ε1 + extDot (hbar h) (evec b1 δ1) +
     quadForm (lowsOpt (Cbᵀ * Ubar n * Cb)) (evec b1 δ1))

def compH {n : ℕ} (C1 C2 : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2))
    (h1 h2 : BV (2 * n)) : BV (2 * n) :=
  fun i =>
    (let d1 := dvec C1
     let d2 := dvec C2
     let Cb1 := CbarMat C1 d1
     let Cb2 := CbarMat C2 d2
     hbar h1 (some i) +
       (Matrix.mulVec Cb1ᵀ (hbar h2)) (some i) +
       diagVecOpt (Cb1ᵀ * lowsOpt (Cb2ᵀ * Ubar n * Cb2) * Cb1) (some i))

def invC {n : ℕ} (C1 : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Pmat n * C1ᵀ * Pmat n

def invd {n : ℕ} (C1 : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) : BV (2 * n) :=
  (invC C1)ᵀ.mulVec (dvec C1)

def invH {n : ℕ} (C1 : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h1 : BV (2 * n)) :
    BV (2 * n) :=
  fun i =>
    (let d1 := dvec C1
     let Cb := CbarMat C1 d1
     let Cbi := CbarMat (invC C1) (invd C1)
     (Matrix.mulVec Cbiᵀ (hbar h1)) (some i) +
       diagVecOpt (Cbiᵀ * lowsOpt (Cbᵀ * Ubar n * Cb) * Cbi) (some i))

theorem conj_mul {n : ℕ} (Q M N : Matrix (Reg n) (Reg n) ℂ) (hQ : Qᴴ * Q = 1) :
    Q * (M * N) * Qᴴ = (Q * M * Qᴴ) * (Q * N * Qᴴ) := by
  symm
  rw [Matrix.mul_assoc (Q * M) Qᴴ (Q * N * Qᴴ),
      ← Matrix.mul_assoc Qᴴ (Q * N) Qᴴ,
      ← Matrix.mul_assoc Qᴴ Q N, hQ, Matrix.one_mul,
      Matrix.mul_assoc Q M (N * Qᴴ),
      Matrix.mul_assoc Q (M * N) Qᴴ,
      Matrix.mul_assoc M N Qᴴ]

def source_theorem_one_conjugation {n : ℕ}
    (Q : Matrix (Reg n) (Reg n) ℂ)
    (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h : BV (2 * n))
    (b1 : BV (2 * n)) (δ1 ε1 : ZMod 2) : Prop :=
  RepresentsClifford Q C h →
    Q * (((Complex.I ^ δ1.val : ℂ) * ((-1 : ℂ) ^ ε1.val)) • tau (splitVec b1)) * Qᴴ
      = ((Complex.I ^ (thm1_delta2 C b1 δ1).val : ℂ) *
          ((-1 : ℂ) ^ (thm1_eps2 C h b1 δ1 ε1).val)) •
          tau (splitVec (thm1_b2 C b1))

def source_theorem_two_composition {n : ℕ}
    (Q1 Q2 : Matrix (Reg n) (Reg n) ℂ)
    (C1 C2 : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h1 h2 : BV (2 * n)) : Prop :=
  RepresentsClifford Q1 C1 h1 → RepresentsClifford Q2 C2 h2 →
    RepresentsClifford (Q2 * Q1) (C2 * C1) (compH C1 C2 h1 h2)

def source_theorem_three_inverse {n : ℕ}
    (Q1 : Matrix (Reg n) (Reg n) ℂ)
    (C1 : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h1 : BV (2 * n)) : Prop :=
  RepresentsClifford Q1 C1 h1 → Q1 * Q1ᴴ = 1 → Symplectic n C1 →
    RepresentsClifford Q1ᴴ (invC C1) (invH C1 h1)

end Qatlib.Papers.CliffordGroup03.MainResults
