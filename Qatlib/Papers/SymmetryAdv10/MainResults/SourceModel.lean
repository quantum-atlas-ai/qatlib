/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Hadamard
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for Ambainis--Magnin--Roetteler--Roland, arXiv:1012.2112v1

Fixed paper version: arXiv:1012.2112v1 (2010-12-09), title
"Symmetry-assisted adversaries for quantum state generation".

This module fixes the *vocabulary* of the paper's adversary framework so that
each Claim (Lemma 3, Lemma 8, ..., Theorem 29) can be stated against the same
objects:

* a quantum state generation problem `Problem` with input alphabet `Hom`, oracle
  function type `F`, output alphabet `Out`, and target state amplitudes
  `target f : Tgt → ℂ` (Definition of Section 2.1, p. 5);
* the target Gram matrix `targetGram` and the paper's `ρ⊙`
  (`Definition 9`, p. 8);
* junk matrices: Gram matrices of unit vectors (non-coherent case) and the
  all-ones matrix (coherent case), `Definition 9`, p. 8;
* adversary matrices `Γ` with `Γ|δ⟩ = |δ⟩` (`Definition 5`, p. 6), additive
  (`−I ⪯ Γ ⪯ I`) and multiplicative (`Γ ⪰ I`) variants;
* the Hadamard-product restriction `Γ_x = Γ ∘ D_x` of `Definition 6`, p. 7;
* the progress function `W = tr[Γρ]` and the constants
  `C(ε) = √ε + 2√(ε(1−ε))` (Theorem 10, p. 9),
  `K̃(Γ̃,λ̃,ε) = (1−λ̃)(√(1−ε) − √η)²` (Theorem 12, p. 10) and
  `K(Γ,λ,ε) = 1 + (λ−1)(√(1−ε) − √η)²` (Theorem 14, p. 11);
* the paper's bound functionals `ADV±`, `ADṼ`, `MADV^{(λ)}`, `MADV`
  (`Definition 15`, p. 12), as suprema over the corresponding matrix families.

The definitions are deliberately phrased with finite types and complex
matrices, matching the paper's finite-dimensional setting.  The query
complexity `Q_ε` itself is *not* defined here: modelling arbitrary quantum
circuits is outside this paper block, and the lower-bound theorems are stated
in their progress-function form (see `HybridBound`), or as statements about the
bound functionals (see `AdvComparison`).
-/

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.SymmetryAdv10.MainResults

noncomputable section

/-- A quantum state generation problem (Section 2.1, p. 5; Definition 9, p. 8).

* `F` is the set of oracle functions,
* `Hom` is the input alphabet `Σ_I`,
* `Out` is the output alphabet `Σ_O`,
* `Tgt` indexes the target register in which `|P(f)⟩` lives,
* `funMap f x = f(x)`,
* `target f : Tgt → ℂ` are the amplitudes of `|P(f)⟩`. -/
structure Problem where
  F : Type
  [instFintypeF : Fintype F]
  [instDecEqF : DecidableEq F]
  Hom : Type
  [instFintypeHom : Fintype Hom]
  [instDecEqHom : DecidableEq Hom]
  Out : Type
  [instFintypeOut : Fintype Out]
  [instDecEqOut : DecidableEq Out]
  Tgt : Type
  [instFintypeTgt : Fintype Tgt]
  funMap : F → Hom → Out
  target : F → Tgt → ℂ

attribute [instance] Problem.instFintypeF Problem.instDecEqF Problem.instFintypeHom
  Problem.instDecEqHom Problem.instFintypeOut Problem.instDecEqOut Problem.instFintypeTgt

namespace Problem

variable (P : Problem)

/-- The target Gram matrix `G(f,g) = ⟨P(f)|P(g)⟩`. -/
def targetGram : Matrix P.F P.F ℂ :=
  fun f g => ∑ t : P.Tgt, star (P.target f t) * P.target g t

/-- The paper's `ρ⊙ = |F|⁻¹ ∑_{f,f'} ⟨ψ_f|ψ_f'⟩ |f'⟩⟨f|` (Definition 9, p. 8).
Its entry in row `a`, column `b` is `|F|⁻¹ ⟨ψ_b|ψ_a⟩`. -/
def rhoDot : Matrix P.F P.F ℂ :=
  fun a b => ((Fintype.card P.F : ℂ))⁻¹ * P.targetGram b a

/-- Gram matrices of unit vectors: the non-coherent junk matrices of
Definition 9, p. 8 (equivalently: positive semidefinite with unit diagonal). -/
def IsNoncoherentJunk (M : Matrix P.F P.F ℂ) : Prop :=
  M.PosSemidef ∧ ∀ f, M f f = 1

/-- The coherent junk matrix: the all-ones matrix of Definition 9, p. 8. -/
def allOnesJunk : Matrix P.F P.F ℂ := fun _ _ => 1

/-- The uniform superposition `|δ⟩ = |F|^{-1/2} ∑_f |f⟩`. -/
def deltaVec : P.F → ℂ :=
  fun _ => ((Real.sqrt (Fintype.card P.F : ℝ) : ℂ))⁻¹

/-- Adversary matrix (Definition 5, p. 6): Hermitian and fixing `|δ⟩`. -/
def IsAdversaryMatrix (Γ : Matrix P.F P.F ℂ) : Prop :=
  Γ.IsHermitian ∧ Γ.mulVec P.deltaVec = P.deltaVec

/-- Additive adversary matrix (Definition 5, p. 6): `−I ⪯ Γ ⪯ I`. -/
def IsAdditiveAdversary (Γ : Matrix P.F P.F ℂ) : Prop :=
  P.IsAdversaryMatrix Γ ∧ (1 - Γ).PosSemidef ∧ (1 + Γ).PosSemidef

/-- Multiplicative adversary matrix (Definition 5, p. 6): `Γ ⪰ I`. -/
def IsMultiplicativeAdversary (Γ : Matrix P.F P.F ℂ) : Prop :=
  P.IsAdversaryMatrix Γ ∧ (Γ - 1).PosSemidef

/-- The `(0,1)`-matrix `D_x` of Definition 6, p. 7: entry in row `g`, column
`f` is `δ_{f(x), g(x)}`. -/
def D (x : P.Hom) : Matrix P.F P.F ℂ :=
  fun g f => if P.funMap f x = P.funMap g x then 1 else 0

/-- `Γ_x = Γ ∘ D_x` (Definition 6, p. 7). -/
def GammaX (Γ : Matrix P.F P.F ℂ) (x : P.Hom) : Matrix P.F P.F ℂ :=
  Matrix.hadamard Γ (P.D x)

/-- The progress function `W = tr[Γρ]` (Definition 5, p. 6), as a real number. -/
def progress (Γ ρ : Matrix P.F P.F ℂ) : ℝ := (Γ * ρ).trace.re

/-- The additive-adversary constant `C(ε) = √ε + 2√(ε(1−ε))` (Theorem 10, p. 9). -/
def additiveC (ε : ℝ) : ℝ := Real.sqrt ε + 2 * Real.sqrt (ε * (1 - ε))

/-- The hybrid kernel `K̃(Γ̃,λ̃,ε) = (1−λ̃)(√(1−ε) − √η)²`
(Theorem 12, p. 10). -/
def hybridK (lam eps eta : ℝ) : ℝ :=
  (1 - lam) * (Real.sqrt (1 - eps) - Real.sqrt eta) ^ 2

/-- The multiplicative kernel `K(Γ,λ,ε) = 1 + (λ−1)(√(1−ε) − √η)²`
(Theorem 14, p. 11). -/
def multK (lam eps eta : ℝ) : ℝ :=
  1 + (lam - 1) * (Real.sqrt (1 - eps) - Real.sqrt eta) ^ 2

/-- `max_x ‖Γ_x − Γ‖`, the denominator of the additive and hybrid bounds. -/
def maxGammaDiff (Γ : Matrix P.F P.F ℂ) : ℝ :=
  sSup (Set.range (fun x : P.Hom => ‖P.GammaX Γ x - Γ‖))

/-- `max_x ‖Γ_x^{1/2} Γ^{-1/2}‖²`, the first multiplicative denominator. -/
def maxSqrtDiffLeft (Γ : Matrix P.F P.F ℂ) : ℝ :=
  sSup (Set.range (fun x : P.Hom =>
    ‖CFC.sqrt (P.GammaX Γ x) * (CFC.sqrt Γ)⁻¹‖ ^ 2))

/-- `max_x ‖Γ^{1/2} Γ_x^{-1/2}‖²`, the second multiplicative denominator. -/
def maxSqrtDiffRight (Γ : Matrix P.F P.F ℂ) : ℝ :=
  sSup (Set.range (fun x : P.Hom =>
    ‖CFC.sqrt Γ * (CFC.sqrt (P.GammaX Γ x))⁻¹‖ ^ 2))

/-- The junk overlap of a projector `Π_bad` on the bad subspace:
`sup_M tr[Π_bad (ρ⊙ ∘ M)]`, taken over the junk matrices of Definition 9. -/
def badOverlap (Pibad : Matrix P.F P.F ℂ) : ℝ :=
  sSup {v : ℝ | ∃ M : Matrix P.F P.F ℂ,
    P.IsNoncoherentJunk M ∧ v = (Pibad * Matrix.hadamard P.rhoDot M).trace.re}

/-- The additive adversary bound `ADV±_ε(P)` of Definition 15, p. 12. -/
def advPlus (ε : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ Γ : Matrix P.F P.F ℂ,
    P.IsAdditiveAdversary Γ ∧
    (∀ M : Matrix P.F P.F ℂ, P.IsNoncoherentJunk M →
      (Γ * Matrix.hadamard P.rhoDot M).trace = 0) ∧
    v = (1 - additiveC ε) / P.maxGammaDiff Γ}

/-- The hybrid adversary bound `ADṼ_ε(P)` of Definition 15, p. 12, with the
junk overlap `η` of the bad subspace left as the supremum `badOverlap`. -/
def advHat (ε : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (Γ Pibad : Matrix P.F P.F ℂ) (lam : ℝ),
    P.IsAdditiveAdversary Γ ∧ lam < 1 ∧
    v = hybridK lam ε (P.badOverlap Pibad) / P.maxGammaDiff Γ}

/-- The multiplicative adversary bound at fixed `λ`,
`MADV^{(λ)}_ε(P)` of Definition 15, p. 12. -/
def madvLambda (ε lam : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ Γ : Matrix P.F P.F ℂ,
    P.IsMultiplicativeAdversary Γ ∧
    v = Real.log (multK lam ε (P.badOverlap 1)) /
      Real.log (max (P.maxSqrtDiffLeft Γ) (P.maxSqrtDiffRight Γ))}

/-- The multiplicative adversary bound `MADV_ε(P) = sup_{λ>1} MADV^{(λ)}_ε(P)`
of Definition 15, p. 12. -/
def madv (ε : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ lam : ℝ, 1 < lam ∧ v = P.madvLambda ε lam}

end Problem

end

end Qatlib.Papers.SymmetryAdv10.MainResults
