/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabPEPS15 — shared source model

Source: "Rapid adiabatic preparation of injective PEPS and Gibbs states",
fixed arXiv:1508.00570 (v2, 12 Nov 2015).  PDF at
`assets/1508.00570.pdf`, text at `assets/1508.00570.txt`.

This module fixes the vocabulary shared by the claim modules of paper
`AdiabPEPS15`.  It does not prove any source claim; it only states the
objects that the source's Theorems 1, 8–10, 14 and Lemmas 2–7, 12–13 are
phrased in terms of:

* a finite-dimensional Hilbert space `ℂ^d` with the paper's **Euclidean**
  vector norm (`euclidNorm`) and its (conjugate-linear in the first slot)
  inner product `inner`;
* `Parallel` — the paper's "`v` is parallel to `w`" (a complex multiple);
* the **Gevrey bounds** of Eq. (14) and (35) (`gevreyOp`, `gevreyShift`);
* the **adiabatic-expansion constants** `A₁, A₂, A₃` of Eq. (55);
* the **Hamiltonian path** as a Hermitian matrix function together with the
  derivative data used in the Gevrey hypotheses;
* the **cluster expansion** objects `H_Ω`, `f_μ`, and the Möbius transforms
  `f̂` / `fˇ` of Eqs. (93)–(96).

Boundary: every analytic inequality (a bound on a derivative of a state or
operator, a spectral-gap estimate, a Lieb–Robinson or cluster-expansion
estimate) is stated over this model, with the source's hypotheses as explicit
Lean hypotheses.  The model does not claim that the finite-sum Möbius
combinatorics *alone* implies the operator-valued cluster bound; those are
separate claims and are handled in their own modules.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace Qatlib.Papers.AdiabPEPS15.MainResults

variable {d : ℕ}

/-! ## §1 Hilbert-space primitives (Euclidean norm, inner product, parallelism) -/

/-- The paper's vector norm: the Euclidean (`ℓ²`) norm on `ℂ^d`.  The source
uses the Euclidean norm for vectors and the operator norm for operators
(Supplemental Material, paragraph below Eq. (13)); this is the vector half. -/
def euclidNorm (v : Fin d → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The Hilbert-space inner product `⟨u, v⟩ = ∑ᵢ conj(uᵢ) · vᵢ`, conjugate
linear in the *first* argument, as used for the phase condition
`⟨φ̇, φ⟩ = 0` below Eq. (13). -/
def inner (u v : Fin d → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- `u` and `v` are orthogonal: `⟨u, v⟩ = 0`. -/
def Orth (u v : Fin d → ℂ) : Prop := inner u v = 0

/-- `v` is *parallel* to `w`: `v = λ • w` for some complex `λ`.  This is the
relation used throughout Lemmas 2 and 6 ("`φ⁽ᵏ⁾(s₀)` is parallel to
`φ(s₀)`"). -/
def Parallel (v w : Fin d → ℂ) : Prop := ∃ c : ℂ, v = c • w

/-- `[k!]^{1+α}` — the factorial factor appearing in Eq. (14). -/
def factPow (k : ℕ) (α : ℝ) : ℝ := (Nat.factorial k : ℝ) ^ (1 + α)

/-- The Gevrey majorant of Eq. (14): `K · cᵏ · [k!]^{1+α} / (k+1)²`. -/
def gevreyOp (K c α : ℝ) (k : ℕ) : ℝ :=
  K * c ^ k * factPow k α / ((k : ℝ) + 1) ^ 2

/-- The shifted Gevrey majorant of Eq. (35): for derivative order `k` and
shift `p`, `C · eᵏ · [(k+p)!]^{1+α} / (k+p+1)²`. -/
def gevreyShift (C e : ℝ) (α : ℝ) (p k : ℕ) : ℝ :=
  C * e ^ k * factPow (k + p) α / (((k + p : ℕ) : ℝ) + 1) ^ 2

/-- `f` has all derivatives of order `≥ 1` vanishing at `s₀`.  This is the
endpoint hypothesis of Theorem 1 ("all derivatives of G vanish at `0` and at
`1`") and of Lemma 2. -/
def DerivativesVanishAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (s₀ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → iteratedDeriv k f s₀ = 0

/-! ## §2 Adiabatic-expansion constants of Eq. (55) -/

/-- `4π²/3`, the constant that Lemma 3 supplies at every convolution step. -/
def kernelConst : ℝ := 4 * Real.pi ^ 2 / 3

/-- `A₁ = 8π²/3` of Eq. (55). -/
def A1 : ℝ := 8 * Real.pi ^ 2 / 3

/-- `A₃ = 2c (K/Δ) (4π²/3)²` of Eq. (55). -/
def A3 (c K Δ : ℝ) : ℝ := 2 * c * (K / Δ) * (4 * Real.pi ^ 2 / 3) ^ 2

/-- `A₂ = 4c² (K²/Δ³) (4π²/3)⁵` of Eq. (55). -/
def A2 (c K Δ : ℝ) : ℝ := 4 * c ^ 2 * (K ^ 2 / Δ ^ 3) * (4 * Real.pi ^ 2 / 3) ^ 5

/-! ## §3 The Hamiltonian path and its spectral data

The source works throughout with a smooth path `s ↦ G(s)` of Hermitian
operators on `ℂ^d`, its instantaneous ground state `φ(s)` (energy normalised
to `0`), and the minimal spectral gap `Δ` over the path.  We keep the objects
as separate function arguments and the structural facts as hypotheses, so that
each claim's module can instantiate them exactly as the source does. -/

/-- The paper's structural bundle for the adiabatic path: `G` is a Hermitian
path with ground state `φ`, unit ground-state norm, ground energy `0`, and a
uniform spectral gap `Δ` on the orthogonal complement of `φ`.  The phase of
`φ` is fixed by `⟨φ̇, φ⟩ = 0`. -/
structure AdiabaticPath (d : ℕ) where
  /-- The Hamiltonian path `G(s)`. -/
  G : ℝ → Matrix (Fin d) (Fin d) ℂ
  /-- The instantaneous ground state `φ(s)`. -/
  φ : ℝ → Fin d → ℂ
  /-- The minimal gap `Δ`. -/
  Δ : ℝ
  gap_pos : 0 < Δ
  hermitian : ∀ s, Matrix.IsHermitian (G s)
  ground : ∀ s, G s *ᵥ φ s = 0
  unit : ∀ s, euclidNorm (φ s) = 1
  /-- Uniform gap: `‖G v‖ ≥ Δ ‖v‖` for every `v ⊥ φ(s)`. -/
  gap : ∀ s (v : Fin d → ℂ), Orth v (φ s) → Δ * euclidNorm v ≤ euclidNorm (G s *ᵥ v)
  /-- Fixed phase: `⟨φ̇, φ⟩ = 0`. -/
  phase : ∀ s, inner (iteratedDeriv 1 φ s) (φ s) = 0

/-! ## §4 Cluster expansion of Eqs. (91)–(96) -/

variable {ι : Type*} [DecidableEq ι]

/-- `H_Ω = ∑_{λ ∈ Ω} h_λ` of §"Cluster expansion". -/
def Hsum (h : ι → Matrix (Fin d) (Fin d) ℂ) (Ω : Finset ι) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ a ∈ Ω, h a

/-- The non-local parent-Hamiltonian term `f_μ(Ω) = e^{βH_Ω} P_μ e^{-2βH_Ω}
P_μ e^{βH_Ω}` of Eq. (91) and §"Cluster expansion". -/
def fμ (h : ι → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (β : ℝ) (Ω : Finset ι) : Matrix (Fin d) (Fin d) ℂ :=
  NormedSpace.exp (β • Hsum h Ω) * P * NormedSpace.exp ((-2 * β) • Hsum h Ω) * P *
    NormedSpace.exp (β • Hsum h Ω)

/-- The Möbius transform `ř` of Eq. (94): `fˇ(Ω) = ∑_{Θ ⊆ Ω} (-1)^{|Ω\Θ|} f(Θ)`.
-/
def mobiusCheck (f : Finset ι → Matrix (Fin d) (Fin d) ℂ) (Ω : Finset ι) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ Θ ∈ Ω.powerset, ((-1 : ℂ) ^ (Ω.card - Θ.card)) • f Θ

/-- The Möbius transform `f̂` of Eq. (93): `f̂(Ω) = ∑_{Θ ⊆ Ω} f(Θ)`. -/
def mobiusHat (f : Finset ι → Matrix (Fin d) (Fin d) ℂ) (Ω : Finset ι) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ Θ ∈ Ω.powerset, f Θ

/-- The cluster term `fˇ_μ(Ω)` of Eq. (96). -/
def fCheck (h : ι → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (β : ℝ) (Ω : Finset ι) : Matrix (Fin d) (Fin d) ℂ :=
  mobiusCheck (fμ h P β) Ω

/-- The doubled Möbius sum of Eq. (98): for disjoint `Ω, Θ`,
`∑_{Ω' ⊆ Ω} ∑_{Θ' ⊆ Θ} (-1)^{|Ω\Ω'|}(-1)^{|Θ\Θ'|} f(Ω' ∪ Θ')`. -/
def doubleMobius (f : Finset ι → Matrix (Fin d) (Fin d) ℂ) (Ω Θ : Finset ι) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ Ω' ∈ Ω.powerset, ∑ Θ' ∈ Θ.powerset,
    (((-1 : ℂ) ^ (Ω.card - Ω'.card)) * ((-1 : ℂ) ^ (Θ.card - Θ'.card))) • f (Ω' ∪ Θ')

/-- The RHS `(e^{4β} - 1)^{|Ω|}` of the cluster norm bound Eq. (99). -/
def clusterBound (β : ℝ) (n : ℕ) : ℝ := (Real.exp (4 * β) - 1) ^ n

/-- The source's spectral-gap condition `G² ≥ Δ G` for a Hamiltonian `G`,
expressed through the Hilbert-space quadratic form: for every `v`,
`Δ ⟨v, G v⟩ ≤ ⟨G v, G v⟩`.  For a Hermitian positive-semidefinite `G` whose
kernel is its ground space, this is equivalent to "the spectral gap of `G` is
at least `Δ`" (eigenvalues `0` and `≥ Δ`).  Used by Theorems 9 and 14. -/
def GapGE (G : Matrix (Fin d) (Fin d) ℂ) (Δ : ℝ) : Prop :=
  Matrix.IsHermitian G ∧
    ∀ v : Fin d → ℂ, Δ * (inner v (G *ᵥ v)).re ≤ (inner (G *ᵥ v) (G *ᵥ v)).re

/-- The Euclidean norm of a vector differs from the library `ℓ²`-style `Pi`
norm only in bookkeeping; here we record the elementary `euclidNorm` unfolding
fact used by downstream claims. -/
theorem euclidNorm_def (v : Fin d → ℂ) : euclidNorm v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := rfl

/-- `Parallel v 0` holds only for `v = 0`. -/
theorem parallel_zero {v : Fin d → ℂ} (h : Parallel v 0) : v = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc, smul_zero]

/-- Parallelism is preserved by a zero scalar: the zero vector is parallel to
every vector.  This is the degenerate case used when a coefficient vanishes. -/
theorem parallel_zero_left (w : Fin d → ℂ) : Parallel 0 w := ⟨0, by simp⟩

end Qatlib.Papers.AdiabPEPS15.MainResults
