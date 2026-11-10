/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra.NCResponseData
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
open Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

namespace Qatlib.Papers.PolyTransform26.ResidualCert

open Matrix

structure ResidualData (J : Type) [Fintype J] where
  r : ℕ
  D : ℕ
  a0 : EuclideanSpace ℂ (Fin r)
  Ares : J → Matrix (Fin r) (Fin r) ℂ
  cConst : ℂ
  pRow : J → Fin r → ℂ
  q : NCPoly J

variable {J : Type} [Fintype J]

noncomputable def residualCoeff {r : ℕ} (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) : List J → EuclideanSpace ℂ (Fin r)
  | [] => a0
  | j :: w => (Ares j).toEuclideanLin (residualCoeff a0 Ares w)

noncomputable def matrixWord {r : ℕ} (Ares : J → Matrix (Fin r) (Fin r) ℂ) :
    List J → Matrix (Fin r) (Fin r) ℂ
  | [] => 1
  | j :: w => Ares j * matrixWord Ares w

structure ResidualCert (J : Type) [Fintype J] extends ResidualData J where
  q_const : q [] = cConst
  q_tail : ∀ j w, q (j :: w) = ∑ t : Fin r, pRow j t * residualCoeff a0 Ares w t
  nilpotent : ∀ w : List J, w.length = D → matrixWord Ares w = 0

def ResidualCert.responseT (cert : ResidualCert J) : J → Matrix (Fin cert.r) (Fin cert.r) ℂ :=
  cert.Ares

noncomputable def ResidualCert.responseH (cert : ResidualCert J) :
    List J → EuclideanSpace ℂ (Fin cert.r) :=
  residualCoeff cert.a0 cert.Ares

def ResidualCert.responseC (cert : ResidualCert J) : J → Fin cert.r → ℂ :=
  cert.pRow

end Qatlib.Papers.PolyTransform26.ResidualCert
