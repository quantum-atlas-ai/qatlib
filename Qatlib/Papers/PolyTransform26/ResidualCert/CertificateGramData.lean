/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyTransform26.ResidualCert.TransferExtractionData
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Arrays for residual-certificate Gram calculations

These definitions organize residual coordinates into stacked factors, coefficient columns, and
output rows. The matrix `compactSourceCertificate` is the difference between the input Gram
contributions and the residual and scalar output Gram contributions. The residual-certificate
setting follows [ShenEtAl2026].

## Main statements

* `certificateGramPullback`: The matrix with entries given by summing `G a b * T (a, s) (b, t)`
  over the two external indices.
* `compactSourceCertificate`: The external and query Gram contributions minus the weighted
  residual-column Gram contribution and the output-row Gram matrix.

## References

* [Shen et al., 2026][ShenEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Papers.PolyTransform26.ResidualCert
open Matrix
open scoped Kronecker
variable {A B R J M : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype M]
  [DecidableEq B] [DecidableEq M]

/-- The reshaping of `K` whose entry at row `(b, m)` and column `t` is `K m (b, t)`. -/
noncomputable def certificateStackedFactor (K : Matrix M (B × R) ℂ) : Matrix (B × M) R ℂ :=
  fun p t => K p.2 (p.1,t)

/-- The matrix with entries given by summing `G a b * T (a, s) (b, t)` over the two external
indices. -/
noncomputable def certificateGramPullback (T : Matrix (B × R) (B × R) ℂ) (G : Matrix B B ℂ) : Matrix R R ℂ :=
  fun s t => ∑ a, ∑ b, G a b*T (a,s) (b,t)

/-- The matrix whose external column is `a0` and whose column labeled by `(j, t)` is column `t`
of `Ares j`. -/
noncomputable def certificateResidualColumns (a0 : R → ℂ) (Ares : J → Matrix R R ℂ) :
    Matrix R (Unit ⊕ (J × R)) ℂ :=
  fun s k => match k with
  | Sum.inl _ => a0 s
  | Sum.inr (j,t) => Ares j s t

/-- The row with external entry `d` and entries `p j t` at labels `(j, t)`. -/
noncomputable def certificateOutputRow (d : ℂ) (p : J → R → ℂ) : Matrix Unit (Unit ⊕ (J × R)) ℂ :=
  fun _ k => match k with
  | Sum.inl _ => d
  | Sum.inr (j,t) => p j t

/-- The matrix with `(j, l)` residual blocks given by the pullback of `T` along `(F j)ᴴ * F l`,
and zero entries involving the external column. -/
noncomputable def certificateQueryGram (F : J → Matrix A B ℂ) (T : Matrix (B × R) (B × R) ℂ) :
    Matrix (Unit ⊕ (J × R)) (Unit ⊕ (J × R)) ℂ :=
  fun i k => match i,k with
  | Sum.inr (j,s),Sum.inr (l,t) => certificateGramPullback T ((F j)ᴴ*F l) s t
  | _,_ => 0

/-- The row equal to one on the external column and zero on every residual column. -/
noncomputable def certificateExternalRow : Matrix Unit (Unit ⊕ (J × R)) ℂ :=
  fun _ k => match k with
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- The external and query Gram contributions minus the weighted residual-column Gram
contribution and the output-row Gram matrix. -/
noncomputable def compactSourceCertificate {r : ℕ} (F : J → Matrix A B ℂ)
    (T : Matrix (B × Fin r) (B × Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (p : J → Fin r → ℂ) :
    Matrix (Unit ⊕ (J × Fin r)) (Unit ⊕ (J × Fin r)) ℂ :=
  (certificateExternalRow (J := J) (R := Fin r))ᴴ*certificateExternalRow + certificateQueryGram F T -
    (certificateResidualColumns a0 Ares)ᴴ*certificateGramPullback T (1 : Matrix B B ℂ)*certificateResidualColumns a0 Ares -
    (certificateOutputRow d p)ᴴ*certificateOutputRow d p

end Qatlib.Papers.PolyTransform26.ResidualCert
