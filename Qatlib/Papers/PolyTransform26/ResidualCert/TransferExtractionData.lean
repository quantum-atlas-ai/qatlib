/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyTransform26.ResidualCert.ResidualCertData
set_option warningAsError false

namespace Qatlib.Papers.PolyTransform26.ResidualCert
open Matrix
variable {X Y J : Type} [Fintype X]

noncomputable def compactSuccessorInput {r : ℕ} (F : J → Matrix Y X ℂ)
    (Q : Matrix X (Fin r) ℂ) : Matrix (Y ⊕ Unit) (Unit ⊕ (J × Fin r)) ℂ :=
  fun i k => match i,k with
  | Sum.inl y,Sum.inr (j,t) => (F j*Q) y t
  | Sum.inr _,Sum.inl _ => 1
  | _,_ => 0

noncomputable def compactSuccessorOutput {r : ℕ} (Q : Matrix X (Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (pRow : J → Fin r → ℂ) : Matrix (X ⊕ Unit) (Unit ⊕ (J × Fin r)) ℂ :=
  fun i k => match i,k with
  | Sum.inl x,Sum.inl _ => Q.mulVec a0 x
  | Sum.inl x,Sum.inr (j,t) => (Q*Ares j) x t
  | Sum.inr _,Sum.inl _ => d
  | Sum.inr _,Sum.inr (j,t) => pRow j t

noncomputable def compactResponse {r : ℕ} (Q : Matrix X (Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (w : List J) : EuclideanSpace ℂ X :=
  Q.toEuclideanLin (residualCoeff a0 Ares w)

end Qatlib.Papers.PolyTransform26.ResidualCert
