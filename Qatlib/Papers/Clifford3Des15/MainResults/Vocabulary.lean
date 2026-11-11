/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.TwirlChannel
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — shared vocabulary (paper layer)

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

This module fixes, in one place, the objects that the paper's Section 2 introduces
and that the claims in `MainResults` refer to.  Complex Euclidean spaces are
modelled by the house `Operator d = Matrix (Fin d) (Fin d) ℂ` (the paper's
`L(X)` for `X = ℂ^d`), and the `k`-fold register `L(X^{⊗k})` is modelled by
`Operator (d ^ k)`.  A `k`-fold Haar twirl `T_k` is the house `HaarTwirl H`
(`H : HaarUnitaryMeasure D`) and a finite-ensemble twirl `Ψ_{E,k}` is the
weighted conjugation average `ensembleTwirl E` defined below.

Everything here is definitional; the mathematical content (the paper's
Propositions, Lemmas and Theorems) lives in the sibling files.  Nothing in
`Foundations`/`Concepts` is redefined: the Haar measure (`HaarUnitaryMeasure`,
`HaarTwirl`), unitarity (`IsUnitaryMatrix`), and finite-group twirls
(`FamilyTwirl`) are imported from
`QuantumAlgorithm.Foundations.ChannelTheory.TwirlChannel`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Classical

namespace Qatlib.Papers.Clifford3Des15.MainResults

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ChannelTheory.TwirlChannel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

variable {ι : Type} [Fintype ι]

/-! ## Finite unitary ensembles and their twirl channels (§2.4) -/

/-- A finite unitary ensemble over `X = ℂ^d` (paper §2.4): index set `ι`,
probability weights `α : ι → ℝ`, and a member unitary `U i : L(X)`. -/
structure Ensemble (ι : Type) [Fintype ι] (d : ℕ) where
  /-- Probability weight of each member. -/
  wt : ι → ℝ
  /-- The operator carried by each member. -/
  op : ι → Operator d
  /-- Weights are nonnegative. -/
  wt_nonneg : ∀ i, 0 ≤ wt i
  /-- The weights form a probability vector. -/
  wt_sum_one : (∑ i, wt i) = 1
  /-- Every member is unitary. -/
  op_unitary : ∀ i, IsUnitaryMatrix (op i)

/-- The weighted twirl channel `Ψ_{E,k}` of an ensemble `E` (paper eq. (21)) on a
fixed register of dimension `d` (`= dim X^{⊗k}`): `X ↦ ∑_i α_i U_i X U_i†`. -/
def ensembleTwirl {d : ℕ} (E : Ensemble ι d) : Operator d →ₗ[ℂ] Operator d :=
  ∑ i, ((E.wt i : ℂ)) • conjBranch (E.op i)

/-- Unfolding `ensembleTwirl` on an operator: `Ψ_{E,k}(X) = ∑_i α_i U_i X U_i†`. -/
theorem ensembleTwirl_apply {d : ℕ} (E : Ensemble ι d) (X : Operator d) :
    ensembleTwirl E X
      = ∑ i, ((E.wt i : ℂ)) • (E.op i * X * (E.op i).conjTranspose) := by
  simp only [ensembleTwirl, LinearMap.sum_apply, LinearMap.smul_apply, conjBranch_apply]

/-- Definition 1 (k-design, eq. (21)/(28)): the finite ensemble `E` is a unitary
`k`-design on a register of dimension `D` (`D = dim X^{⊗k}`) iff its `k`-fold twirl
`Ψ_{E,k}` equals the `k`-fold Haar twirl `T_k = HaarTwirl H` on every operator. -/
def IsUnitaryDesign {d : ℕ} (H : HaarUnitaryMeasure d) (E : Ensemble ι d) : Prop :=
  ∀ X : Operator d, ensembleTwirl E X = HaarTwirl H X

/-! ## Linearity of the Haar twirl `T_k`

These are the entrywise Bochner-integral linearity facts that let us push `T_k`
through a finite ensemble average; they are what Proposition 1 (c005) uses. -/

/-- The Haar twirl of the zero operator is zero. -/
theorem haarTwirl_zero {D : ℕ} (H : HaarUnitaryMeasure D) :
    HaarTwirl H (0 : Operator D) = 0 := by
  ext i j
  show MeasureTheory.integral H.μ (fun A : Operator D => (A * (0 : Operator D) * A.conjTranspose) i j)
    = 0
  have hz : (fun A : Operator D => (A * (0 : Operator D) * A.conjTranspose) i j)
      = fun _ => (0 : ℂ) := by
    funext A; simp
  rw [hz, MeasureTheory.integral_zero]

/-- The Haar twirl is additive. -/
theorem haarTwirl_add {D : ℕ} (H : HaarUnitaryMeasure D) (ρ σ : Operator D) :
    HaarTwirl H (ρ + σ) = HaarTwirl H ρ + HaarTwirl H σ := by
  ext i j
  show MeasureTheory.integral H.μ (fun A : Operator D => (A * (ρ + σ) * A.conjTranspose) i j)
    = MeasureTheory.integral H.μ (fun A : Operator D => (A * ρ * A.conjTranspose) i j)
      + MeasureTheory.integral H.μ (fun A : Operator D => (A * σ * A.conjTranspose) i j)
  have hpt : (fun A : Operator D => (A * (ρ + σ) * A.conjTranspose) i j)
      = fun A => (A * ρ * A.conjTranspose) i j + (A * σ * A.conjTranspose) i j := by
    funext A
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  rw [hpt]
  exact MeasureTheory.integral_add (haar_conjEntry_integrable H ρ i j)
    (haar_conjEntry_integrable H σ i j)

/-- The Haar twirl is complex-homogeneous. -/
theorem haarTwirl_smul {D : ℕ} (H : HaarUnitaryMeasure D) (c : ℂ) (ρ : Operator D) :
    HaarTwirl H (c • ρ) = c • HaarTwirl H ρ := by
  ext i j
  show MeasureTheory.integral H.μ (fun A : Operator D => (A * (c • ρ) * A.conjTranspose) i j)
    = c * MeasureTheory.integral H.μ (fun A : Operator D => (A * ρ * A.conjTranspose) i j)
  have hpt : (fun A : Operator D => (A * (c • ρ) * A.conjTranspose) i j)
      = fun A => c * ((A * ρ * A.conjTranspose) i j) := by
    funext A
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [hpt, MeasureTheory.integral_const_mul]

/-- The Haar twirl is additive over a finite sum of scalar-weighted operators.
(The `[Fintype ι]` section instance is unused here; the finite set `s` is given
explicitly.) -/
theorem haarTwirl_finset_sum {D : ℕ} (H : HaarUnitaryMeasure D) (s : Finset ι)
    (c : ι → ℂ) (ρ : ι → Operator D) :
    HaarTwirl H (∑ i ∈ s, c i • ρ i) = ∑ i ∈ s, c i • HaarTwirl H (ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [haarTwirl_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, haarTwirl_add, haarTwirl_smul, ih]

/-! ## Permutation operators on the `k`-fold register (§2.2)

The paper's `W_π ∈ L(X^{⊗k})` (eq. (9)) for `π ∈ S_k`.  We model it as the
`0/1` permutation matrix on `Fin (d ^ k) ≃ (Fin k → Fin d)` obtained by
permuting the `k` register coordinates. -/

/-- Enumerate the `k`-fold register `X^{⊗k}`: `(Fin k → Fin d) ≃ Fin (d ^ k)`. -/
def regEquiv (d k : ℕ) : (Fin k → Fin d) ≃ Fin (d ^ k) := finFunctionFinEquiv

/-- The permutation operator `W_π ∈ L(X^{⊗k})` (paper eq. (9)): the `0/1`
matrix sending basis index `v` to `v ∘ π`. -/
def permOp (d k : ℕ) (π : Equiv.Perm (Fin k)) : Operator (d ^ k) :=
  Matrix.of fun i j => if (regEquiv d k).symm j = (regEquiv d k).symm i ∘ π then 1 else 0

/-! ## Pauli group data and Pauli mixing (§2.1, §2.5) -/

/-- `U` sends the Pauli element `p` to `q` by conjugation (paper eq. (7)):
`U p U† = q`. -/
def conjugatesTo {d : ℕ} (U p q : Operator d) : Prop := U * p * U.conjTranspose = q

/-- The Pauli group (modulo phase) on `n` qudits as a finite set `P` of non-identity
operators, together with the commutation-value function `F` (paper eq. (3)):
`p1 p2 = ω^{F(p1,p2)} p2 p1`.  For qubits `F` takes values in `{0,1}`
(commuting / anti-commuting); for qudits in `[d]`. -/
structure PauliSystem (d : ℕ) where
  /-- Non-identity Pauli operators (phase-free representatives). -/
  P : Finset (Operator d)
  /-- Commutation value `F(p1,p2)` of eq. (3)/(4). -/
  F : Operator d → Operator d → ℕ
  /-- The identity is not counted among the non-identity Pauli elements. -/
  one_not_mem : (1 : Operator d) ∉ P
  /-- Every Pauli representative is unitary. -/
  mem_unitary : ∀ p ∈ P, IsUnitaryMatrix p

/-- The Pauli class `H_ℓ` of ordered pairs with `q1 ≠ q2` and `F(q1,q2) = ℓ`
(paper eqs. (30)-(32)). -/
def Hclass {d : ℕ} (F : Operator d → Operator d → ℕ) (ℓ : ℕ)
    (P : Finset (Operator d)) : Finset (Operator d × Operator d) := by
  classical
  exact (P.product P).filter (fun pr => pr.1 ≠ pr.2 ∧ F pr.1 pr.2 = ℓ)

/-- Weight of the sub-ensemble of `E` whose members satisfy `s` (paper eq. (27)):
`∑_{(α,U) ∈ E_s} α`. -/
def subWeight {d : ℕ} (E : Ensemble ι d) (s : ι → Prop) [DecidablePred s] : ℝ :=
  ∑ i ∈ Finset.univ.filter s, E.wt i

/-- Definition 2 (Pauli-invariant, eq. (26)): `E` is closed under right
multiplication by Pauli elements with equal weight (global phases quotiented). -/
def PauliInvariant {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d) : Prop :=
  ∀ p ∈ S.P, ∀ i : ι, ∃ j : ι, E.wt j = E.wt i ∧ E.op j = E.op i * p

/-- Definition 3 (Pauli mixing, eq. (29)): for every `p,q ∈ P`, the sub-ensemble
mapping `p` to `q` has total weight `1 / |P|`. -/
def PauliMixing {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d) : Prop := by
  classical
  exact ∀ p ∈ S.P, ∀ q ∈ S.P,
    subWeight E (fun i => conjugatesTo (E.op i) p q) = (S.P.card : ℝ)⁻¹

/-- Definition 4 (Pauli 2-mixing, eq. (35)): for every ordered pair `(p1,p2)` of
distinct Pauli elements and every `(q1,q2)` in the matching class `H_{F(p1,p2)}`,
the sub-ensemble mapping `(p1,p2)` to `(q1,q2)` has total weight `1 / |H|`. -/
def PauliTwoMixing {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d) : Prop := by
  classical
  exact ∀ p1 ∈ S.P, ∀ p2 ∈ S.P, p1 ≠ p2 →
    ∀ q1 q2, (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P →
      subWeight E (fun i => conjugatesTo (E.op i) p1 q1 ∧ conjugatesTo (E.op i) p2 q2)
        = ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹

/-! ## Clifford group and uniform ensembles (§2.1, §2.4) -/

/-- `C` is the (generalized) Clifford group of the Pauli system `S`: exactly the
unitaries normalizing `S.P` (paper eqs. (5)-(6)). -/
def IsCliffordGroup {d : ℕ} (C : Finset (Operator d)) (S : PauliSystem d) : Prop :=
  (∀ c ∈ C, IsUnitaryMatrix c ∧ ∀ p ∈ S.P, ∃ q ∈ S.P, conjugatesTo c p q) ∧
    (∀ c, IsUnitaryMatrix c → (∀ p ∈ S.P, ∃ q ∈ S.P, conjugatesTo c p q) → c ∈ C)

/-- `E` is the uniform ensemble over `S` (each element of `S` exactly once, equal
weights `|S|⁻¹`) — the paper's "uniform ensemble over the Clifford group". -/
def IsUniformOver {d : ℕ} (E : Ensemble ι d) (S : Finset (Operator d)) : Prop :=
  (∀ i, E.op i ∈ S) ∧ (∀ x ∈ S, ∃ i, E.op i = x) ∧
    (∀ i, E.wt i = (S.card : ℝ)⁻¹)

end Qatlib.Papers.Clifford3Des15.MainResults
