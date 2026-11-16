/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section


/-! # Preserved legacy analytic interface
These closed definitions preserve the old contract for review. They do not
establish the source spectral calculus, smoothness, or adiabatic bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SwitchAdiab12.MainResults.SwitchModel

open scoped ComplexOrder

/-- The data of a switching adiabatic family: the Hamiltonian path `H`, the
instantaneous eigenprojection `P`, the eigenvalue `E`, the minimal gap `g`,
the initial state `ψ_I` and the rescaled Schrödinger solution `ψ τ s`. -/
structure SwitchAdiabaticData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- `τ`-independent Hamiltonian family `H(s)`. -/
  H : ℝ → E →L[ℂ] E
  /-- instantaneous spectral projection on the eigenvalue branch of interest. -/
  P : ℝ → E →L[ℂ] E
  /-- the eigenvalue branch `E(s)`. -/
  Eeig : ℝ → ℝ
  /-- the minimal gap `g = min_{s ∈ [0,1]} g(s)`. -/
  g : ℝ
  /-- the initial ground state `ψ_I`. -/
  psiI : E
  /-- the rescaled solution `ψ_τ(s)` of (I.1). -/
  psi : ℝ → ℝ → E

namespace SwitchAdiabaticData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `P(s)` is an orthogonal projection for every `s`: idempotent and
contractive (in a Hilbert space this is equivalent to being the orthogonal
projection onto its range). -/
def IsOrthogonalProjection (D : SwitchAdiabaticData E) : Prop :=
  (∀ s : ℝ, D.P s * D.P s = D.P s) ∧ (∀ s : ℝ, ‖D.P s‖ ≤ 1)

/-- Assumption I.1 (minimal gap), paper p. 4: `P(s)` is the eigenprojection
for the eigenvalue `E(s)`, and the rest of the spectrum is separated from
`E(s)` by the gap `g > 0`. -/
def HasGap (D : SwitchAdiabaticData E) : Prop :=
  0 < D.g ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
    D.H s * D.P s = ((D.Eeig s : ℂ)) • D.P s ∧
      ∀ x : E,
        D.g * ‖x - D.P s x‖ ≤ ‖(D.H s - (D.Eeig s : ℂ) • 1) (x - D.P s x)‖

/-- Definition I.3 (Gevrey class `G^α(R)`), paper p. 5: the derivative of `H`
is supported in `[0,1]` and `‖d^k H/ds^k‖ ≤ C R^k k^{α k}` for `k ≥ 1`. -/
def IsGevrey (D : SwitchAdiabaticData E) (α : ℝ) : Prop :=
  ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
    Function.support (fun s => deriv D.H s) ⊆ Set.Icc (0 : ℝ) 1 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDeriv k D.H s‖ ≤ C * R ^ k * (k : ℝ) ^ (α * k)

/-- The rescaled Schrödinger equation (I.1), paper p. 2:
`i ψ̇_τ(s) = τ H(s) ψ_τ(s)`, equivalently `ψ̇_τ(s) = -i τ H(s) ψ_τ(s)`,
with the initial condition `ψ_τ(0) = ψ_I`. -/
def SolvesSchrodinger (D : SwitchAdiabaticData E) : Prop :=
  ∀ τ : ℝ, (∀ s : ℝ,
      HasDerivAt (fun r => D.psi τ r)
        ((-Complex.I * (τ : ℂ)) • D.H s (D.psi τ s)) s) ∧
    D.psi τ 0 = D.psiI

/-- `ψ_I` is the (unit) ground state of `H_I = H(0)`. -/
def InitialGround (D : SwitchAdiabaticData E) : Prop :=
  D.P 0 D.psiI = D.psiI ∧ ‖D.psiI‖ = 1

end SwitchAdiabaticData

open SwitchAdiabaticData


/-- The legacy gap predicate permits the zero projection onto a non-eigenvalue. -/
def jumpData (g : ℝ) : SwitchAdiabaticData ℂ where
  H := fun _ => 0
  P := fun s => if s = 0 then 1 else 0
  Eeig := fun s => if s = 0 then 0 else 1
  g := g
  psiI := 1
  psi := fun _ _ => 1

/-- The discontinuous projection still satisfies both legacy algebraic conditions. -/
theorem jumpProj (g : ℝ) : (jumpData g).IsOrthogonalProjection := by
  constructor
  · intro s
    by_cases hs : s = 0 <;> simp [jumpData, hs]
  · intro s
    by_cases hs : s = 0 <;> simp [jumpData, hs]

/-- Every positive gap at most one satisfies the old bound, even after the jump. -/
theorem jumpGap (g : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) :
    (jumpData g).HasGap := by
  refine ⟨hg, ?_⟩
  intro s _
  by_cases hs : s = 0
  · simp [jumpData, hs]
  · constructor
    · simp [jumpData, hs]
    · intro x
      simpa [jumpData, hs] using mul_le_mul_of_nonneg_right hg1 (norm_nonneg x)

/-- The Hamiltonian is actually constant and meets every legacy Gevrey predicate. -/
theorem jumpGev (g α : ℝ) : (jumpData g).IsGevrey α := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
  · simp [jumpData]
  · intro k hk s _
    change ‖iteratedDeriv k (fun _ : ℝ => (0 : ℂ →L[ℂ] ℂ)) s‖ ≤
      (1 : ℝ) * 1 ^ k * (k : ℝ) ^ (α * (k : ℝ))
    rw [iteratedDeriv_const, ite_eq_right (by omega : k ≠ 0)]
    simpa only [norm_zero, one_pow, one_mul] using
      Real.rpow_nonneg (Nat.cast_nonneg k) (α * (k : ℝ))

/-- The constant state is an actual solution of the zero-Hamiltonian equation. -/
theorem jumpSolves (g : ℝ) : (jumpData g).SolvesSchrodinger := by
  intro τ
  constructor
  · intro s
    simpa [jumpData] using (hasDerivAt_const s (1 : ℂ))
  · rfl

/-- The initial state is unit length and belongs to the initial projection. -/
theorem jumpInitial (g : ℝ) : (jumpData g).InitialGround := by
  simp [SwitchAdiabaticData.InitialGround, jumpData]

/-- At s=1 the projection range is zero and the error is exactly one for every time. -/
theorem jumpError (g τ : ℝ) :
    Metric.infDist ((jumpData g).psi τ 1) (Set.range ((jumpData g).P 1)) = 1 := by
  simp [jumpData, Metric.infDist_singleton]

/-- All literal legacy promises hold while its error conclusion fails at s=1. -/
theorem jumpWitness (g α τ : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) :
    (jumpData g).IsOrthogonalProjection ∧ (jumpData g).HasGap ∧
    (jumpData g).IsGevrey α ∧ (jumpData g).SolvesSchrodinger ∧
    (jumpData g).InitialGround ∧
    ¬ Metric.infDist ((jumpData g).psi τ 1) (Set.range ((jumpData g).P 1)) ≤ (1/2 : ℝ) := by
  refine ⟨jumpProj g, jumpGap g hg hg1, jumpGev g α, jumpSolves g, jumpInitial g, ?_⟩
  rw [jumpError]
  norm_num

end Qatlib.Papers.SwitchAdiab12.MainResults.SwitchModel
