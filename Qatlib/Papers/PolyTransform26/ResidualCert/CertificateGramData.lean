/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyTransform26.ResidualCert.TransferExtractionData
import Mathlib.LinearAlgebra.Matrix.Kronecker
set_option warningAsError false

namespace Qatlib.Papers.PolyTransform26.ResidualCert
open Matrix
open scoped Kronecker
variable {A B R J M : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype M]
  [DecidableEq B] [DecidableEq M]

noncomputable def certificateStackedFactor (K : Matrix M (B × R) ℂ) : Matrix (B × M) R ℂ :=
  fun p t => K p.2 (p.1,t)

noncomputable def certificateGramPullback (T : Matrix (B × R) (B × R) ℂ) (G : Matrix B B ℂ) : Matrix R R ℂ :=
  fun s t => ∑ a, ∑ b, G a b*T (a,s) (b,t)

noncomputable def certificateResidualColumns (a0 : R → ℂ) (Ares : J → Matrix R R ℂ) :
    Matrix R (Unit ⊕ (J × R)) ℂ :=
  fun s k => match k with
  | Sum.inl _ => a0 s
  | Sum.inr (j,t) => Ares j s t

noncomputable def certificateOutputRow (d : ℂ) (p : J → R → ℂ) : Matrix Unit (Unit ⊕ (J × R)) ℂ :=
  fun _ k => match k with
  | Sum.inl _ => d
  | Sum.inr (j,t) => p j t

noncomputable def certificateQueryGram (F : J → Matrix A B ℂ) (T : Matrix (B × R) (B × R) ℂ) :
    Matrix (Unit ⊕ (J × R)) (Unit ⊕ (J × R)) ℂ :=
  fun i k => match i,k with
  | Sum.inr (j,s),Sum.inr (l,t) => certificateGramPullback T ((F j)ᴴ*F l) s t
  | _,_ => 0

noncomputable def certificateExternalRow : Matrix Unit (Unit ⊕ (J × R)) ℂ :=
  fun _ k => match k with
  | Sum.inl _ => 1
  | Sum.inr _ => 0

noncomputable def compactSourceCertificate {r : ℕ} (F : J → Matrix A B ℂ)
    (T : Matrix (B × Fin r) (B × Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (p : J → Fin r → ℂ) :
    Matrix (Unit ⊕ (J × Fin r)) (Unit ⊕ (J × Fin r)) ℂ :=
  (certificateExternalRow (J := J) (R := Fin r))ᴴ*certificateExternalRow + certificateQueryGram F T -
    (certificateResidualColumns a0 Ares)ᴴ*certificateGramPullback T (1 : Matrix B B ℂ)*certificateResidualColumns a0 Ares -
    (certificateOutputRow d p)ᴴ*certificateOutputRow d p

end Qatlib.Papers.PolyTransform26.ResidualCert
