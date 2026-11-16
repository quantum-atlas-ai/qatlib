/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

@[expose] public section


/-! Archived matrix-map vocabulary and its definitional properties. These definitions do not assert Sinkhorn convergence or operator-scaling theorems. -/

set_option autoImplicit false
noncomputable section

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
open Matrix Filter

namespace Qatlib.Papers.MatrixScaling16.MainResults.Source

/-- The ambient matrix algebra `M_d` of the paper, with `d = n`. -/
abbrev M (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

/-- A `ℂ`-linear endomorphism of the matrix algebra, i.e. a linear map `M_n → M_n`. -/
abbrev LinearEnd (n : ℕ) : Type := M n →ₗ[ℂ] M n

/-- A positive linear map `M_n → M_n`, the paper's `E : M_d → M_d`. -/
abbrev PMap (n : ℕ) : Type := PositiveLinearMap ℂ (M n) (M n)

/-- `P` is an orthogonal projection: Hermitian and idempotent. -/
def IsOrthProj {n : ℕ} (P : M n) : Prop := Pᴴ = P ∧ P * P = P

/-! ## The trace dual `E*` -/

/-- The trace/Heisenberg dual of a linear endomorphism, the paper's `E*`.

It is characterised by `tr(E A * B) = tr(A * E* B)` for all `A, B`, and is
given entrywise by `(E* B)_{lk} = tr(E(E_{kl}) * B)` where `E_{kl}` is the
matrix unit.  For a positive map `E`, `E*` is the adjoint in the Hilbert
Schmidt inner product, exactly as in the paper. -/
def traceDual {n : ℕ} (E : LinearEnd n) : LinearEnd n where
  toFun B := Matrix.of fun l k => (E (Matrix.single k l 1) * B).trace
  map_add' B C := by
    ext l k
    simp only [Matrix.of_apply, Matrix.mul_add, Matrix.trace_add, Matrix.add_apply]
  map_smul' c B := by
    ext l k
    simp only [Matrix.of_apply, Matrix.mul_smul, Matrix.trace_smul, Matrix.smul_apply,
      RingHom.id_apply, smul_eq_mul]

/-- The map `B ↦ Cout * E (Cinᴴ * B * Cin) * Coutᴴ`, the rescaling of `E` that
underlies a matrix scaling and Definition D.1. -/
def rescale {n : ℕ} (E : LinearEnd n) (Cout Cin : M n) : LinearEnd n where
  toFun B := Cout * E (Cinᴴ * B * Cin) * Coutᴴ
  map_add' B C := by
    simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c B := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, map_smul]

/-- The matrix scaling of Definition 9.3 / equation (39): `B ↦ Y† E (X B X†) Y`. -/
def scaledMap {n : ℕ} (E : LinearEnd n) (X Y : M n) : LinearEnd n :=
  rescale E Yᴴ X

/-- The map underlying the Sinkhorn update `B ↦ S * E B * S` for a Hermitian `S`. -/
def squeeze {n : ℕ} (S : M n) (E : LinearEnd n) : LinearEnd n where
  toFun B := S * E B * S
  map_add' B C := by simp only [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, map_smul]

/-! ## Basic predicates of the paper -/

/-- `E` is unital: `E(1) = 1`. -/
def IsUnital {n : ℕ} (E : LinearEnd n) : Prop := E 1 = 1

/-- `E` is trace preserving: `E*(1) = 1`. -/
def IsTracePreserving {n : ℕ} (E : LinearEnd n) : Prop := traceDual E 1 = 1

/-- `E` is doubly stochastic (Definition 9.3): unital and trace preserving. -/
def IsDoublyStochastic {n : ℕ} (E : LinearEnd n) : Prop := E 1 = 1 ∧ traceDual E 1 = 1

/-- `E` is scalable to a doubly stochastic map (Definition 9.3): there are
matrices `X, Y` such that `Y† E (X · X†) Y` is doubly stochastic. -/
def IsScalableTo {n : ℕ} (E : LinearEnd n) : Prop :=
  ∃ X Y : M n, IsDoublyStochastic (scaledMap E X Y)

/-- The paper's irreducibility (Definition 9.1): the only orthogonal projection
`P` with `E(P M P) ⊆ P M P` is the identity. -/
def Irreducible {n : ℕ} (E : LinearEnd n) : Prop :=
  ∀ P : M n, IsOrthProj P → P ≠ 0 →
    (∀ A : M n, P * E (P * A * P) * P = E (P * A * P)) → P = 1

/-- The paper's full indecomposability (Definition 9.1): for any two nonzero
orthogonal projections `P, Q` of the same rank with `E(P M P) ⊆ Q M Q`, one has
`P = Q = 1`. -/
def FullyIndecomposable {n : ℕ} (E : LinearEnd n) : Prop :=
  ∀ P Q : M n, IsOrthProj P → IsOrthProj Q → P ≠ 0 → Q ≠ 0 →
    P.rank = Q.rank →
    (∀ A : M n, Q * E (P * A * P) * Q = E (P * A * P)) → P = 1 ∧ Q = 1

/-- `E` is fully indecomposable as a *map*, spelled in the form used by
Lemma 9.12 and Theorem 9.4, i.e. Definition 9.1's condition. -/
abbrev FullIndecomp {n : ℕ} : LinearEnd n → Prop := FullyIndecomposable

/-- A positive linear map (in the sense of the paper): it maps positive
semidefinite matrices to positive semidefinite matrices. -/
def IsPositiveMap {n : ℕ} (E : LinearEnd n) : Prop :=
  ∀ A : M n, A.PosSemidef → (E A).PosSemidef

/-- `E` is rank non-decreasing (Definition 9.2, equation (38)). -/
def RankNonDecreasing {n : ℕ} (E : LinearEnd n) : Prop :=
  ∀ A : M n, A.PosSemidef → A.rank ≤ (E A).rank

/-- `E` is positivity improving (Definition 9.1): positive definite matrices are
mapped to positive definite matrices. -/
def PositivityImproving {n : ℕ} (E : LinearEnd n) : Prop :=
  ∀ A : M n, A.PosDef → (E A).PosDef

/-- `E` is doubly stochastic in the sense of Appendix D's `DS` functional: used
to state that a fixed point under normalisation is doubly stochastic. -/
def IsFixedPointUpToNormalisation {n : ℕ} (E : LinearEnd n) (A : M n) : Prop :=
  A.PosDef ∧ traceDual E ((E A)⁻¹) = A⁻¹

/-! ## Capacity, mixed discriminant, Menon operator -/

/-- The capacity `Cap(E)` of Definition 9.7 / equation (44):
`inf { det(E X) | X > 0, det X = 1 }`. -/
def cap {n : ℕ} (E : LinearEnd n) : ℝ :=
  sInf { t : ℝ | ∃ X : M n, X.PosDef ∧ X.det = 1 ∧ t = (E X).det.re }

/-- The mixed discriminant of Definition C.3 / equation (71), written in the
equivalent permutation form
`M(A_1,...,A_n) = ∑_{σ} det( A_{σ(1)} e_1, ..., A_{σ(n)} e_n )`,
which is the coefficient of `x_1 ⋯ x_n` in `det(∑ x_i A_i)`. -/
def mixedDiscriminant {n : ℕ} (A : Fin n → M n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), Matrix.det (fun i j => A (σ j) i j)

/-- The minimal mixed discriminant `M̃(A)` of Definition C.5 / equation (72). -/
def minimalMixedDiscriminant {n : ℕ} (A : Fin n → M n) : ℝ :=
  sInf { t : ℝ | ∃ i j : Fin n, i ≠ j ∧ t = (mixedDiscriminant A).re }

/-- The tuple `A_{E,U}` of Definition C.2 / equation (70): the diagonal action
of a unitary `U`, given by the matrices `E(u_i u_i†)` for the rows `u_i` of `U`. -/
def decoherenceTuple {n : ℕ} (E : LinearEnd n) (U : M n) : Fin n → M n :=
  fun i => E (Matrix.of fun a b => U i a * star (U i b))

/-- The Menon operator `T_pos` of Definition 9.13:
`T_pos := D ∘ E* ∘ D ∘ E`, i.e. `T_pos(A) = ( E*((E A)⁻¹) )⁻¹`. -/
def menon {n : ℕ} (E : LinearEnd n) (A : M n) : M n :=
  (traceDual E ((E A)⁻¹))⁻¹

/-- The capacity `Cap(A_{E,U})` attached to a tuple of positive definite
matrices, as in Lemma 9.9. -/
def tupleCap {n : ℕ} (A : Fin n → M n) : ℝ :=
  sInf { t : ℝ | ∃ γ : Fin n → ℝ, (∀ i, 0 < γ i) ∧ (∏ i, γ i = 1) ∧
    t = (Matrix.det (∑ i, (γ i : ℂ) • A i)).re }

/-- The convex potential `f_A` of equation (46):
`f_A(ξ) = ln det(e^{ξ_1} A_1 + ... + e^{ξ_n} A_n)`. -/
def fA {n : ℕ} (A : Fin n → M n) (ξ : Fin n → ℝ) : ℝ :=
  Real.log (Matrix.det (∑ i, ((Real.exp (ξ i) : ℂ)) • A i)).re

/-! ## Error functional, Hilbert metric, contraction ratio, Δ -/

/-- The error functional `DS` of equation (40):
`DS(E) = tr((E 1 - 1)^2) + tr((E* 1 - 1)^2)`. -/
def dsError {n : ℕ} (E : LinearEnd n) : ℝ :=
  ((E 1 - 1) * (E 1 - 1)).trace.re + ((traceDual E 1 - 1) * (traceDual E 1 - 1)).trace.re

/-- The Hilbert projective metric `d_H` on positive definite matrices, equation
(67): `d_H(A,B) = log(M(A,B)) - log(m(A,B))` with `M = inf{t | A ≤ t B}` and
`m = sup{t | t B ≤ A}`. -/
def hilbertMetric {n : ℕ} (A B : M n) : ℝ :=
  Real.log (sInf { t : ℝ | 0 < t ∧ A ≤ t • B }) -
    Real.log (sSup { t : ℝ | 0 < t ∧ t • B ≤ A })

/-- The contraction ratio `γ^{1/2}(E)` of equation (68). -/
def contractionRatio {n : ℕ} (E : LinearEnd n) : ℝ :=
  sSup { r : ℝ | ∃ A B : M n, A.PosDef ∧ B.PosDef ∧ A ≠ B ∧
    r = hilbertMetric (E A) (E B) / hilbertMetric A B }

/-- The metric `Δ` on scalable maps of Definition 9.19 / equation (54). -/
def delta {n : ℕ} (E T : LinearEnd n) : ℝ :=
  sInf { r : ℝ | ∃ X Y : M n, scaledMap E X Y = T ∧
    r = hilbertMetric X 1 + hilbertMetric Y 1 }

/-! ## Appendix D: locally scalable functionals -/

/-- A locally scalable functional of Definition D.1 / equation (73). -/
def LocallyScalable {n : ℕ} (φ : LinearEnd n → ℝ) : Prop :=
  ∀ (E : LinearEnd n) (C1 C2 : M n),
    φ (rescale E C1 C2) = (C1 * C1ᴴ).det.re * (C2 * C2ᴴ).det.re * φ E

/-- A bounded locally scalable functional of Definition D.1. -/
def BoundedLocallyScalable {n : ℕ} (φ : LinearEnd n → ℝ) : Prop :=
  LocallyScalable φ ∧ ∃ f : ℝ → ℝ, ∀ E : LinearEnd n, |φ E| ≤ f ((E 1).trace.re)

/-! ## The Sinkhorn iteration of equations (41)-(42) -/

/-- A choice of Hermitian square root for positive semidefinite matrices, as used
by the Sinkhorn updates `E(1)^{1/2}`. -/
structure SqrtChoice (n : ℕ) where
  /-- The chosen square root. -/
  sqrt : M n → M n
  /-- The chosen square root of a positive semidefinite matrix is Hermitian. -/
  sqrt_hermitian : ∀ A : M n, A.PosSemidef → (sqrt A)ᴴ = sqrt A
  /-- The chosen square root squares back to the matrix. -/
  sqrt_mul_self : ∀ A : M n, A.PosSemidef → sqrt A * sqrt A = A

/-- One half-iteration of the Sinkhorn procedure, equation (41):
`E ↦ E(1)^{1/2} E(·) E(1)^{1/2}`. -/
def sinkhornHalf {n : ℕ} (sc : SqrtChoice n) (E : LinearEnd n) : LinearEnd n :=
  squeeze (sc.sqrt (E 1)) E

/-- One full Sinkhorn step of equations (41)-(42): first the unitalising update
(41), then the trace-normalising update (42) via `E*`. -/
def sinkhornStep {n : ℕ} (sc : SqrtChoice n) (E : LinearEnd n) : LinearEnd n :=
  squeeze (sc.sqrt (traceDual (sinkhornHalf sc E) 1)) (sinkhornHalf sc E)

/-- The Sinkhorn iterates `E^{(k)} = E_{2k}` of equations (41)-(42). -/
def sinkhornIter {n : ℕ} (sc : SqrtChoice n) : ℕ → LinearEnd n → LinearEnd n
  | 0, E => E
  | k + 1, E => sinkhornStep sc (sinkhornIter sc k E)


/-! ## Direct sums, unitaries, and the objects of individual claims -/

/-- The compression `B ↦ P * E (P * B * P) * P` of `E` to the range of the
projection `P`. -/
def compress {n : ℕ} (E : LinearEnd n) (P : M n) : LinearEnd n where
  toFun B := P * E (P * B * P) * P
  map_add' B C := by simp only [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, map_smul]

/-- `U` is a unitary matrix. -/
def IsUnitary {n : ℕ} (U : M n) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- Conjugation of a map by a unitary, `B ↦ U * E B * U†`. -/
def conjUnitary {n : ℕ} (U : M n) (E : LinearEnd n) : LinearEnd n := rescale E U 1

/-- `E` is, up to a unitary, a direct sum of fully indecomposable maps
(Theorem 9.4): there is a unitary `U` and a family of pairwise orthogonal
projections `P_i` summing to the identity, each invariant under `U E U†`, such
that every compressed map is fully indecomposable. -/
def IsDirectSumFullyIndecomposable {n : ℕ} (E : LinearEnd n) : Prop :=
  ∃ (U : M n) (m : ℕ) (P : Fin m → M n),
    IsUnitary U ∧
    (∀ i, IsOrthProj (P i)) ∧
    (∑ i, P i = 1) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧
    (∀ (i : Fin m) (A : M n),
      P i * conjUnitary U E (P i * A * P i) * P i = conjUnitary U E (P i * A * P i)) ∧
    (∀ i, FullyIndecomposable (compress (conjUnitary U E) (P i)))

/-- The scaling of Lemma 9.14: `B ↦ Y⁻¹ E (X B X†) Y⁻†`. -/
def scaledMapInv {n : ℕ} (E : LinearEnd n) (X Y : M n) : LinearEnd n where
  toFun B := Y⁻¹ * E (X * B * Xᴴ) * (Y⁻¹)ᴴ
  map_add' B C := by simp only [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, map_smul]

/-- `T_pos` has a positive definite, trace-one fixed point (Lemma 9.14). -/
def HasPositiveEigenvector {n : ℕ} (E : LinearEnd n) : Prop :=
  ∃ ρ : M n, ρ.PosDef ∧ ρ.trace.re = 1 ∧ menon E ρ = ρ

/-- `T` is a scaling of `E` to a doubly stochastic map (Definition 9.3). -/
def IsScalingOf {n : ℕ} (E T : LinearEnd n) : Prop :=
  ∃ X Y : M n, T = scaledMap E X Y ∧ IsDoublyStochastic T

/-- `T` is *the* unique scaling of `E` to a doubly stochastic map. -/
def IsUniqueScalingOf {n : ℕ} (E T : LinearEnd n) : Prop :=
  IsScalingOf E T ∧ ∀ T', IsScalingOf E T' → T' = T

/-- `T` is the doubly stochastic scaling limit of the Sinkhorn iteration. -/
def IsSinkhornLimit {n : ℕ} (sc : SqrtChoice n) (E T : LinearEnd n) : Prop :=
  IsDoublyStochastic T ∧ Tendsto (fun k : ℕ => delta (sinkhornIter sc k E) T) atTop (nhds 0)

/-! ## Definitional unfolding lemmas (proved) -/

/-- Definition 9.3 (fixed arXiv:1609.06349): `T` is a scaling of `E` to a
doubly stochastic map iff it has the form `Y E (X · X†) Y†` and is doubly
stochastic.  Definitional unfolding. -/
theorem isScalingOf_iff {n : ℕ} (E T : LinearEnd n) :
    IsScalingOf E T ↔ ∃ X Y : M n, T = scaledMap E X Y ∧ IsDoublyStochastic T :=
  Iff.rfl

/-- Definition 9.3 (fixed arXiv:1609.06349): uniqueness of the doubly
stochastic scaling.  Definitional unfolding. -/
theorem isUniqueScalingOf_iff {n : ℕ} (E T : LinearEnd n) :
    IsUniqueScalingOf E T ↔
      IsScalingOf E T ∧ ∀ T', IsScalingOf E T' → T' = T :=
  Iff.rfl

/-- Definition 9.3 (fixed arXiv:1609.06349): `E` is scalable iff some
`Y E (X · X†) Y†` is doubly stochastic.  Definitional unfolding. -/
theorem isScalableTo_iff {n : ℕ} (E : LinearEnd n) :
    IsScalableTo E ↔ ∃ X Y : M n, IsDoublyStochastic (scaledMap E X Y) :=
  Iff.rfl

/-- Proposition 9.20 setup (fixed arXiv:1609.06349): `T` is the Sinkhorn limit
of `E` iff it is doubly stochastic and the `delta`-distance of the iteration to
`T` tends to zero.  Definitional unfolding. -/
theorem isSinkhornLimit_iff {n : ℕ} (sc : SqrtChoice n) (E T : LinearEnd n) :
    IsSinkhornLimit sc E T ↔
      IsDoublyStochastic T ∧
        Tendsto (fun k : ℕ => delta (sinkhornIter sc k E) T) atTop (nhds 0) :=
  Iff.rfl

/-- Lemma 9.14 setup (fixed arXiv:1609.06349): `T_pos` has a positive
eigenvector iff there is a positive definite trace-one `ρ` fixed by `menon E`.
Definitional unfolding. -/
theorem hasPositiveEigenvector_iff {n : ℕ} (E : LinearEnd n) :
    HasPositiveEigenvector E ↔
      ∃ ρ : M n, ρ.PosDef ∧ ρ.trace.re = 1 ∧ menon E ρ = ρ :=
  Iff.rfl

/-- Positivity of a map (the hypothesis of Theorem 9.4 and Lemmas 9.9–9.12):
semidefinite matrices are sent to semidefinite matrices.  Definitional
unfolding. -/
theorem isPositiveMap_iff {n : ℕ} (E : LinearEnd n) :
    IsPositiveMap E ↔ ∀ A : M n, A.PosSemidef → (E A).PosSemidef :=
  Iff.rfl

/-- Definition D.1 (fixed arXiv:1609.06349): a functional is locally scalable
iff it scales by the determinant factors under `rescale`.  Definitional
unfolding. -/
theorem locallyScalable_iff {n : ℕ} (φ : LinearEnd n → ℝ) :
    LocallyScalable φ ↔
      ∀ (E : LinearEnd n) (C1 C2 : M n),
        φ (rescale E C1 C2) =
          (C1 * C1ᴴ).det.re * (C2 * C2ᴴ).det.re * φ E :=
  Iff.rfl

/-- Definition D.1 (fixed arXiv:1609.06349): bounded local scalability.
Definitional unfolding. -/
theorem boundedLocallyScalable_iff {n : ℕ} (φ : LinearEnd n → ℝ) :
    BoundedLocallyScalable φ ↔
      LocallyScalable φ ∧ ∃ f : ℝ → ℝ, ∀ E : LinearEnd n, |φ E| ≤ f ((E 1).trace.re) :=
  Iff.rfl

/-- The identity matrix is unitary. -/
theorem isUnitary_one {n : ℕ} : IsUnitary (1 : M n) := by
  constructor <;> simp

/-- The adjoint of a unitary matrix is unitary. -/
theorem isUnitary_adjoint {n : ℕ} {U : M n} (hU : IsUnitary U) : IsUnitary Uᴴ := by
  refine ⟨?_, ?_⟩
  · simpa using hU.2
  · simpa using hU.1


end Qatlib.Papers.MatrixScaling16.MainResults.Source
