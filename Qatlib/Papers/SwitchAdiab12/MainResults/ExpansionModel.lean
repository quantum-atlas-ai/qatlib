/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.Module.Basic

@[expose] public section


/-! # Preserved legacy analytic interface
These closed definitions preserve the old contract for review. They do not
establish the source spectral calculus, smoothness, or adiabatic bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SwitchAdiab12.MainResults.ExpansionModel

/-- The coefficient sequence of the Nenciu expansion together with the
Hamiltonian family and its spectral data.  `A` is the ambient complex normed
algebra of bounded operators. -/
structure ExpansionData (A : Type*) [NormedRing A] [NormedAlgebra ℂ A] where
  /-- the Hamiltonian family `H(s)`. -/
  H : ℝ → A
  /-- the instantaneous spectral projection `P(s)`. -/
  P : ℝ → A
  /-- the eigenvalue branch `E_g(s)` (notation of Section III). -/
  Eeig : ℝ → ℝ
  /-- the minimal gap `g`. -/
  g : ℝ
  /-- the coefficients `B_n(s)` of the expansion (I.7). -/
  B : ℕ → ℝ → A

namespace ExpansionData

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- `P(s)` is a projection for every `s`. -/
def IsProjection (D : ExpansionData A) : Prop :=
  ∀ s : ℝ, D.P s * D.P s = D.P s

/-- The Gevrey hypothesis of Definition I.3, with the class parameters `C, R`
fixed (paper p. 5): `Ḣ` is supported in `[0,1]` and
`‖d^k H/ds^k‖ ≤ C R^k k^{αk}` for `k ≥ 1`. -/
def IsGevrey (D : ExpansionData A) (α C R : ℝ) : Prop :=
  0 < C ∧ 0 < R ∧
    Function.support (fun s => deriv D.H s) ⊆ Set.Icc (0 : ℝ) 1 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDeriv k D.H s‖ ≤ C * R ^ k * (k : ℝ) ^ (α * k)

/-- The contour resolvent bound (III.4), with the paper's convention
`1/g ≥ 1`: on the circle of radius `g/2` around `E_g(s)` the resolvent of
`H(s)` exists and has norm at most `2/g`. -/
def ResolventBound (D : ExpansionData A) : Prop :=
  0 < D.g ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ,
    ‖z - (D.Eeig s : ℂ)‖ = D.g / 2 →
      ∃ Rz : A,
        (D.H s - z • (1 : A)) * Rz = 1 ∧
          Rz * (D.H s - z • (1 : A)) = 1 ∧ ‖Rz‖ ≤ 2 / D.g

/-- The defining hierarchy of the expansion: `B_0 = P`, the differential
relations (II.2a) `i Ḃ_j = [H, B_{j+1}]`, and the projection relations
(II.2b) `B_j = Σ_{m=0}^{j} B_m B_{j-m}`. -/
def SolvesHierarchy (D : ExpansionData A) : Prop :=
  D.B 0 = D.P ∧
    (∀ (j : ℕ) (s : ℝ),
      HasDerivAt (D.B j)
        ((-Complex.I) •
          (D.H s * D.B (j + 1) s - D.B (j + 1) s * D.H s)) s) ∧
      ∀ (j : ℕ) (s : ℝ),
        D.B j s = ∑ m ∈ Finset.range (j + 1), D.B m s * D.B (j - m) s

end ExpansionData

open ExpansionData

end Qatlib.Papers.SwitchAdiab12.MainResults.ExpansionModel
