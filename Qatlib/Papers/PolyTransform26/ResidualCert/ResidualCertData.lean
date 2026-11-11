/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra.NCResponseData
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Residual representation and certificate data

The structure `ResidualData` records a finite residual representation of a noncommutative
polynomial. The extension `ResidualCert` imposes the constant and tail-coefficient identities
and nilpotence at a specified word length, and exposes the resulting transition, response, and
collection data. The residual-certificate setting follows [ShenEtAl2026].

## Main statements

* `ResidualCert`: A residual representation equipped with the constant and tail-coefficient
  identities and vanishing of all residual matrix products of length `D`.
* `ResidualCert.responseH`: The word-indexed residual coefficients of a certificate, viewed as
  its response vectors.

## References

* [Shen et al., 2026][ShenEtAl2026]
-/

open Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

namespace Qatlib.Papers.PolyTransform26.ResidualCert

open Matrix

/-- Data specifying the residual dimension, truncation length, initial vector, residual
matrices, constant coefficient, collection rows, and noncommutative polynomial. -/
structure ResidualData (J : Type) [Fintype J] where
  r : ℕ
  D : ℕ
  a0 : EuclideanSpace ℂ (Fin r)
  Ares : J → Matrix (Fin r) (Fin r) ℂ
  cConst : ℂ
  pRow : J → Fin r → ℂ
  q : NCPoly J

variable {J : Type} [Fintype J]

/-- The word-indexed residual vector obtained from `a0` by successively applying the matrices
for the word's letters. -/
noncomputable def residualCoeff {r : ℕ} (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) : List J → EuclideanSpace ℂ (Fin r)
  | [] => a0
  | j :: w => (Ares j).toEuclideanLin (residualCoeff a0 Ares w)

/-- The ordered product of the residual matrices along a word, with the empty word giving the
identity. -/
noncomputable def matrixWord {r : ℕ} (Ares : J → Matrix (Fin r) (Fin r) ℂ) :
    List J → Matrix (Fin r) (Fin r) ℂ
  | [] => 1
  | j :: w => Ares j * matrixWord Ares w

/-- A residual representation equipped with the constant and tail-coefficient identities and
vanishing of all residual matrix products of length `D`. -/
structure ResidualCert (J : Type) [Fintype J] extends ResidualData J where
  q_const : q [] = cConst
  q_tail : ∀ j w, q (j :: w) = ∑ t : Fin r, pRow j t * residualCoeff a0 Ares w t
  nilpotent : ∀ w : List J, w.length = D → matrixWord Ares w = 0

/-- The residual matrices of a certificate, viewed as its response transition matrices. -/
def ResidualCert.responseT (cert : ResidualCert J) : J → Matrix (Fin cert.r) (Fin cert.r) ℂ :=
  cert.Ares

/-- The word-indexed residual coefficients of a certificate, viewed as its response vectors. -/
noncomputable def ResidualCert.responseH (cert : ResidualCert J) :
    List J → EuclideanSpace ℂ (Fin cert.r) :=
  residualCoeff cert.a0 cert.Ares

/-- The collection rows of a residual certificate. -/
def ResidualCert.responseC (cert : ResidualCert J) : J → Fin cert.r → ℂ :=
  cert.pRow

end Qatlib.Papers.PolyTransform26.ResidualCert
