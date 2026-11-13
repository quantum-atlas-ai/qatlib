/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Choi matrices and finite Kraus representations

This module proves the equivalence between complete positivity, positivity of the Choi matrix,
and a Kraus representation with at most the product of the input and output dimensions many
terms [Choi1975]. For a given Kraus representation, it also characterizes trace preservation by
the completeness relation.

The results include zero-dimensional cases, conversion to bundled quantum channels, and
comparison with Physlib's matrix-map conventions. The qubit transpose map provides a
trace-preserving map that is not completely positive.

## Main statements

* `clause2_conj1`: complete positivity is equivalent to Choi positivity.
* `clause2_conj2`: complete positivity is equivalent to a bounded finite Kraus representation.
* `tracePreserving_iff_krausComplete`: trace preservation is equivalent to Kraus completeness.
* `transposeMap_two_not_completelyPositive`: qubit transposition fails complete positivity.

## References

* [Choi, 1975][Choi1975]
* [Kraus, 1971][Kraus1971]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical ComplexOrder BigOperators

variable {D E : ℕ}

namespace Qatlib.Concepts.ChannelTheory.Stinespring

/-- A matrix unit has entry one exactly at its specified row and column, and zero at every other
entry. -/
theorem matrixUnit_apply {n : ℕ} (i j a b : Fin n) :
    matrixUnit (D := n) i j a b = if i = a ∧ j = b then (1 : ℂ) else 0 := rfl

/-- Every finite operator is the sum of its entries times the corresponding matrix units. -/
theorem matrix_eq_sum_matrixUnit (A : Operator D) :
    A = ∑ i : Fin D, ∑ j : Fin D, A i j • matrixUnit (D := D) i j := by
  classical
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [matrixUnit, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Each entry of `T A` is the sum of the entries of `A` weighted by the corresponding Choi
matrix entries. -/
theorem apply_eq_choiSum (T : Operator D →ₗ[ℂ] Operator E) (A : Operator D) (a b : Fin E) :
    T A a b = ∑ i : Fin D, ∑ j : Fin D, A i j * ChoiMatrix T (i, a) (j, b) := by
  conv_lhs => rw [matrix_eq_sum_matrixUnit A]
  simp only [map_sum, Matrix.sum_apply, map_smul]
  rfl

/-- Pairing `X` with the matrix unit at `(i, j)` under the trace extracts the entry `X j i`. -/
theorem trace_mul_matrixUnit {n : ℕ} (X : Operator n) (i j : Fin n) :
    Matrix.trace (X * matrixUnit i j) = X j i := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, matrixUnit_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · exact if_pos (And.intro rfl rfl)
    · intro b _ hb
      exact if_neg (fun h => hb h.2.symm)
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (fun h => hl h.1.symm)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A finite operator is zero if its trace pairing with every operator is zero. -/
theorem eq_zero_of_trace_mul_eq_zero {n : ℕ} {X : Operator n}
    (h : ∀ A : Operator n, Matrix.trace (X * A) = 0) : X = 0 := by
  classical
  ext i j
  rw [← trace_mul_matrixUnit X j i, h (matrixUnit j i), Matrix.zero_apply]

/-- Multiplication by a matrix equal to the identity leaves the trace unchanged. -/
theorem trace_mul_eq_trace_of_eq_one {n : ℕ} {M : Operator n} (hM : M = 1)
    (A : Operator n) : Matrix.trace (M * A) = Matrix.trace A := by
  rw [hM, one_mul]

/-- A finite operator is the identity if left multiplication by it preserves the trace of every
operator. -/
theorem eq_one_of_trace_mul_eq_trace {n : ℕ} {M : Operator n}
    (h : ∀ A : Operator n, Matrix.trace (M * A) = Matrix.trace A) : M = 1 := by
  classical
  have hz : M - 1 = 0 := by
    apply eq_zero_of_trace_mul_eq_zero
    intro A
    have h1 := h A
    have h2 : Matrix.trace ((M - 1) * A) = Matrix.trace (M * A) - Matrix.trace A := by
      rw [sub_mul, one_mul, Matrix.trace_sub]
    rw [h2, h1, sub_self]
  exact sub_eq_zero.mp hz

/-- Every finite positive semidefinite complex matrix factors as `V * Vᴴ` for a square matrix
`V`. -/
theorem psd_eq_mul_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ V : Matrix ι ι ℂ, A = V * V.conjTranspose := by
  classical
  set U : Matrix ι ι ℂ := (hA.1.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set S : Matrix ι ι ℂ :=
    diagonal fun i => (Real.sqrt (hA.1.eigenvalues i) : ℂ) with hS
  have hspec : A = U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * U.conjTranspose := by
    have h := hA.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    rw [hU]
    exact h
  refine ⟨U * S, ?_⟩
  have hSS : S * S = diagonal fun i => (hA.1.eigenvalues i : ℂ) := by
    rw [hS, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (Matrix.PosSemidef.eigenvalues_nonneg hA i)
  have hSconj : S.conjTranspose = S := by
    rw [hS, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  rw [hspec]
  calc U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * U.conjTranspose
      = U * (S * S) * U.conjTranspose := by rw [hSS]
    _ = U * S * (U * S).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, hSconj, mul_assoc]

/-- The family of `D * E` Kraus matrices obtained by reshaping the columns of a matrix indexed
by input-output pairs. -/
noncomputable def krausOfFactor {D E : ℕ} (V : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Fin (D * E) → Matrix (Fin E) (Fin D) ℂ :=
  fun k a i => V (i, a) (finProdFinEquiv.symm k)

/-- Summing reshaped Kraus entry products over `Fin (D * E)` equals summing the corresponding
factor entries over input-output pairs. -/
theorem krausOfFactor_sum_eq {D E : ℕ}
    (V : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (a b i j) :
    ∑ k : Fin (D * E), krausOfFactor V k a i * star (krausOfFactor V k b j)
      = ∑ p : Fin D × Fin E, V (i, a) p * star (V (j, b) p) := by
  have h := Equiv.sum_comp (e := (finProdFinEquiv (m := D) (n := E)).symm)
    (g := fun p : Fin D × Fin E => V (i, a) p * star (V (j, b) p))
  exact h

/-- Each entry of `V * Vᴴ` is the sum of the corresponding entry products of the Kraus matrices
reshaped from `V`. -/
theorem choi_eq_sum_krausOfFactor {D E : ℕ}
    (V : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (i j : Fin D) (a b : Fin E) :
    (V * V.conjTranspose) (i, a) (j, b)
      = ∑ k : Fin (D * E), krausOfFactor V k a i * star (krausOfFactor V k b j) := by
  rw [krausOfFactor_sum_eq]
  rfl

/-- The order of the outermost and innermost sums in a finite triple sum may be exchanged. -/
theorem sum3_comm {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid δ] (f : α → β → γ → δ) :
    ∑ x : α, ∑ y : β, ∑ z : γ, f x y z = ∑ z : γ, ∑ y : β, ∑ x : α, f x y z := by
  classical
  have s1 : (∑ x : α, ∑ y : β, ∑ z : γ, f x y z)
      = (∑ y : β, ∑ x : α, ∑ z : γ, f x y z) := Finset.sum_comm
  have s2 : (∑ y : β, ∑ x : α, ∑ z : γ, f x y z)
      = (∑ y : β, ∑ z : γ, ∑ x : α, f x y z) := by
    congr 1
    funext y
    exact Finset.sum_comm
  have s3 : (∑ y : β, ∑ z : γ, ∑ x : α, f x y z)
      = (∑ z : γ, ∑ y : β, ∑ x : α, f x y z) := Finset.sum_comm
  rw [s1, s2, s3]

/-- A factorization of the Choi matrix as `V * Vᴴ` yields a Kraus representation using
`krausOfFactor V`. -/
theorem krausForm_of_choi_eq {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    {V : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (h : ChoiMatrix T = V * V.conjTranspose) :
    KrausForm T (krausOfFactor V) := by
  intro A
  ext a b
  rw [apply_eq_choiSum]
  have key : ∀ i j : Fin D, ChoiMatrix T (i, a) (j, b)
      = ∑ k : Fin (D * E), krausOfFactor V k a i * star (krausOfFactor V k b j) := by
    intro i j
    rw [h]
    exact choi_eq_sum_krausOfFactor V i j a b
  have hL : (∑ i : Fin D, ∑ j : Fin D, A i j * ChoiMatrix T (i, a) (j, b))
      = ∑ i : Fin D, ∑ j : Fin D, ∑ k : Fin (D * E),
          krausOfFactor V k a i * A i j * star (krausOfFactor V k b j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [key i j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hR : (∑ k : Fin (D * E), krausOfFactor V k * A * (krausOfFactor V k).conjTranspose) a b
      = ∑ k : Fin (D * E), ∑ j : Fin D, ∑ i : Fin D,
          krausOfFactor V k a i * A i j * star (krausOfFactor V k b j) := by
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_apply]
    show (∑ y : Fin D, (krausOfFactor V k * A) a y * star (krausOfFactor V k b y)) = _
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [hL, sum3_comm, hR]

/-- A complex-linear map represented by a finite Kraus family is completely positive. -/
theorem completelyPositive_of_krausForm {D E : ℕ} {n : ℕ}
    {K : Fin n → Matrix (Fin E) (Fin D) ℂ} {T : Operator D →ₗ[ℂ] Operator E}
    (hK : KrausForm T K) : CompletelyPositive T := by
  have hEq : T = krausMap K := by
    apply LinearMap.ext
    intro A
    have h1 : krausMap K A = ∑ k, K k * A * (K k).conjTranspose := by
      simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]
    rw [h1]
    exact hK A
  rw [hEq]
  unfold krausMap
  exact CompletelyPositive.sum fun k _ => completelyPositive_conjBranch (K k)

/-- The trace of a Kraus sum equals the trace pairing of the input with the sum of the Kraus
adjoint products. -/
theorem trace_krausForm {D E : ℕ} {n : ℕ} (K : Fin n → Matrix (Fin E) (Fin D) ℂ)
    (A : Operator D) :
    Matrix.trace (∑ k, K k * A * (K k).conjTranspose)
      = Matrix.trace ((∑ k, (K k).conjTranspose * K k) * A) := by
  rw [Matrix.trace_sum]
  conv_rhs => rw [Finset.sum_mul, Matrix.trace_sum]
  congr 1
  funext k
  exact Matrix.trace_mul_cycle _ _ _

/-- For a given Kraus representation, trace preservation is equivalent to the Kraus completeness
relation [Kraus1971]. -/
theorem tracePreserving_iff_krausComplete {D E : ℕ} {n : ℕ}
    {K : Fin n → Matrix (Fin E) (Fin D) ℂ} {T : Operator D →ₗ[ℂ] Operator E}
    (hK : KrausForm T K) : TracePreserving T ↔ KrausComplete K := by
  constructor
  · intro hTP
    have h : ∀ A : Operator D,
        Matrix.trace ((∑ k, (K k).conjTranspose * K k) * A) = Matrix.trace A := by
      intro A
      rw [← trace_krausForm K A, ← hK A]
      exact hTP A
    exact eq_one_of_trace_mul_eq_trace h
  · intro hC A
    rw [hK A, trace_krausForm, hC, one_mul]

/-- The Kraus operators of a trace-preserving map satisfy the completeness relation. -/
theorem krausComplete_of_tracePreserving {D E : ℕ} {n : ℕ}
    {K : Fin n → Matrix (Fin E) (Fin D) ℂ} {T : Operator D →ₗ[ℂ] Operator E}
    (hK : KrausForm T K) (hTP : TracePreserving T) : KrausComplete K :=
  (tracePreserving_iff_krausComplete hK).mp hTP

/-- A map with a complete Kraus representation preserves the trace. -/
theorem tracePreserving_of_krausComplete {D E : ℕ} {n : ℕ}
    {K : Fin n → Matrix (Fin E) (Fin D) ℂ} {T : Operator D →ₗ[ℂ] Operator E}
    (hK : KrausForm T K) (hC : KrausComplete K) : TracePreserving T :=
  (tracePreserving_iff_krausComplete hK).mpr hC

/-- The unnormalized maximally entangled outer-product matrix on two copies of `Fin D`. -/
noncomputable def omegaMatrix (D : ℕ) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0

/-- The unnormalized maximally entangled matrix `omegaMatrix D` is positive semidefinite. -/
theorem omegaMatrix_posSemidef (D : ℕ) : (omegaMatrix D).PosSemidef := by
  classical
  let W : Matrix (Fin 1) (Fin D × Fin D) ℂ :=
    fun _ x => (if x.1 = x.2 then 1 else 0 : ℂ)
  have h : omegaMatrix D = W.conjTranspose * W := by
    ext x y
    simp only [omegaMatrix, Matrix.mul_apply, W]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2 <;> simp [hx, hy]
    · intro b _ hb
      exact absurd (Subsingleton.elim b 0) hb
    · intro h0
      exact absurd (Finset.mem_univ (0 : Fin 1)) h0
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self W

/-- The Choi matrix is the dimension-`D` amplification of `T` applied to `omegaMatrix D`. -/
theorem choiMatrix_eq_amplification (T : Operator D →ₗ[ℂ] Operator E) :
    ChoiMatrix T = ChannelAmplification T D (omegaMatrix D) := by
  ext x y
  simp only [ChoiMatrix, ChannelAmplification, omegaMatrix, matrixUnit, Matrix.single]
  rfl

/-- A completely positive map has a positive semidefinite Choi matrix. -/
theorem choi_posSemidef_of_completelyPositive {D E : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (hT : CompletelyPositive T) : (ChoiMatrix T).PosSemidef := by
  rw [choiMatrix_eq_amplification]
  exact hT D (omegaMatrix D) (omegaMatrix_posSemidef D)

/-- A map with a positive semidefinite Choi matrix possesses a Kraus representation with at most
`D * E` terms. -/
theorem kraus_exists_of_choi_posSemidef {D E : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (h : (ChoiMatrix T).PosSemidef) :
    ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ), KrausForm T K ∧ n ≤ D * E := by
  obtain ⟨V, hV⟩ := psd_eq_mul_conjTranspose (ι := Fin D × Fin E) (ChoiMatrix T) h
  exact ⟨D * E, krausOfFactor V, krausForm_of_choi_eq T hV, le_refl _⟩

/-- Every complex-linear map from the zero-dimensional operator space is completely positive. -/
theorem completelyPositive_of_input_zero {D E : ℕ} (hD : D = 0)
    (T : Operator D →ₗ[ℂ] Operator E) : CompletelyPositive T := by
  subst hD
  intro r A hA
  have hin : ∀ x y : Fin r × Fin E, (fun i j : Fin 0 => A (x.1, i) (y.1, j)) = 0 := by
    intro x y
    ext i j
    exact Fin.elim0 i
  have hzero : ChannelAmplification T r A = 0 := by
    ext x y
    have hin' : (fun i j : Fin 0 => A (x.1, i) (y.1, j)) = (0 : Operator 0) := hin x y
    simp [ChannelAmplification, hin']
  rw [hzero]
  exact Matrix.PosSemidef.zero

/-- Every complex-linear map from the zero-dimensional operator space preserves the trace. -/
theorem tracePreserving_of_input_zero {D E : ℕ} (hD : D = 0)
    (T : Operator D →ₗ[ℂ] Operator E) : TracePreserving T := by
  subst hD
  intro A
  have hA : A = 0 := Subsingleton.elim A 0
  rw [hA, map_zero]
  simp

/-- A map into the zero-dimensional operator space preserves the trace exactly when its input
dimension is zero. -/
theorem tracePreserving_iff_input_zero_of_output_zero {D E : ℕ} (hE : E = 0)
    (T : Operator D →ₗ[ℂ] Operator E) : TracePreserving T ↔ D = 0 := by
  subst hE
  constructor
  · intro h
    by_contra hD
    have h1 : Matrix.trace (T (1 : Operator D)) = Matrix.trace (1 : Operator D) := h 1
    have h2 : Matrix.trace (T (1 : Operator D)) = 0 := by simp
    have h3 : Matrix.trace (1 : Operator D) = (D : ℂ) := by simp
    rw [h2, h3] at h1
    exact hD (Nat.cast_eq_zero.mp h1.symm)
  · intro hD
    exact tracePreserving_of_input_zero hD T

/-- A complex-linear map is the underlying map of a `QuantumChannel` exactly when it is
completely positive and trace preserving. -/
theorem quantumChannel_iff_cp_tp {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (∃ Q : QuantumChannel D E, Q.map = T) ↔ CompletelyPositive T ∧ TracePreserving T := by
  constructor
  · rintro ⟨Q, hQ⟩
    subst hQ
    exact ⟨Q.completelyPositive, Q.tracePreserving⟩
  · rintro ⟨hCP, hTP⟩
    exact ⟨⟨T, hCP, hTP⟩, rfl⟩

/-- Qatlib's complete positivity predicate is equivalent to Physlib's
`MatrixMap.IsCompletelyPositive` predicate. -/
theorem completelyPositive_iff_physlibMap {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    CompletelyPositive T ↔ MatrixMap.IsCompletelyPositive T :=
  Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib T

/-- Qatlib's trace preservation predicate is equivalent to Physlib's
`MatrixMap.IsTracePreserving` predicate. -/
theorem tracePreserving_iff_physlibMap {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    TracePreserving T ↔ MatrixMap.IsTracePreserving T :=
  Qatlib.Concepts.ChannelTheory.Stinespring.tracePreserving_iff_physlib T

/-- Physlib's Choi matrix is Qatlib's Choi matrix with the input-output product indices swapped. -/
theorem choiMatrix_physlib_eq_submatrix {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    MatrixMap.choi_matrix T = (ChoiMatrix T).submatrix Prod.swap Prod.swap := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

/-- Qatlib's and Physlib's Choi matrices are positive semidefinite under exactly the same
conditions. -/
theorem choi_posSemidef_iff_physlib {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (ChoiMatrix T).PosSemidef ↔ (MatrixMap.choi_matrix T).PosSemidef := by
  rw [choiMatrix_physlib_eq_submatrix]
  constructor
  · intro h
    exact h.submatrix Prod.swap
  · intro h
    have hswap : ((ChoiMatrix T).submatrix Prod.swap Prod.swap).submatrix Prod.swap Prod.swap
        = ChoiMatrix T := by
      ext x y
      rfl
    rw [← hswap]
    exact h.submatrix Prod.swap

/-- The map `krausMap K` has Kraus representation `K`. -/
theorem krausForm_krausMap {D E : ℕ} {n : ℕ} (K : Fin n → Matrix (Fin E) (Fin D) ℂ) :
    KrausForm (krausMap K) K := by
  intro A
  simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]

/-- The bundled quantum channel constructed from a finite Kraus family satisfying completeness. -/
noncomputable def krausChannel {D E : ℕ} {n : ℕ}
    (K : Fin n → Matrix (Fin E) (Fin D) ℂ) (hC : KrausComplete K) : QuantumChannel D E where
  map := krausMap K
  completelyPositive := completelyPositive_of_krausForm (krausForm_krausMap K)
  tracePreserving := tracePreserving_of_krausComplete (krausForm_krausMap K) hC

/-- A finite-dimensional complex-linear map is completely positive exactly when its Choi matrix
is positive semidefinite [Choi1975]. -/
theorem clause2_conj1 {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    CompletelyPositive T ↔ (ChoiMatrix T).PosSemidef := by
  constructor
  · exact choi_posSemidef_of_completelyPositive
  · intro h
    obtain ⟨V, hV⟩ := psd_eq_mul_conjTranspose (ι := Fin D × Fin E) (ChoiMatrix T) h
    exact completelyPositive_of_krausForm (krausForm_of_choi_eq T hV)

/-- A finite-dimensional complex-linear map is completely positive exactly when it possesses a
Kraus representation with at most `D * E` terms [Choi1975]. -/
theorem clause2_conj2 {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    CompletelyPositive T ↔
      ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ), KrausForm T K ∧ n ≤ D * E := by
  constructor
  · intro h
    exact kraus_exists_of_choi_posSemidef (choi_posSemidef_of_completelyPositive h)
  · rintro ⟨n, K, hK, _⟩
    exact completelyPositive_of_krausForm hK

/-- The existence of a complete Kraus representation with at most `D * E` terms implies trace
preservation. -/
theorem clause2_conj4_mpr {D E : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (h : ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ),
      KrausForm T K ∧ KrausComplete K ∧ n ≤ D * E) : TracePreserving T := by
  obtain ⟨n, K, hK, hC, _⟩ := h
  exact tracePreserving_of_krausComplete hK hC

/-- Every bundled quantum channel has a positive semidefinite Choi matrix and a complete Kraus
representation with at most `D * E` terms. -/
theorem clause2_conj11 {D E : ℕ} (Q : QuantumChannel D E) :
    (ChoiMatrix Q.map).PosSemidef ∧
      ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ),
        KrausForm Q.map K ∧ KrausComplete K ∧ n ≤ D * E := by
  refine ⟨choi_posSemidef_of_completelyPositive Q.completelyPositive, ?_⟩
  obtain ⟨n, K, hK, hn⟩ :=
    kraus_exists_of_choi_posSemidef (choi_posSemidef_of_completelyPositive Q.completelyPositive)
  exact ⟨n, K, hK, krausComplete_of_tracePreserving hK Q.tracePreserving, hn⟩

/-- Every complete finite Kraus family defines a bundled quantum channel with that Kraus
representation and with Physlib complete positivity and trace preservation. -/
theorem clause2_conj12 {D E : ℕ} :
    ∀ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ), KrausComplete K →
      ∃ Q : QuantumChannel D E,
        KrausForm Q.map K ∧
        MatrixMap.IsCompletelyPositive Q.map ∧ MatrixMap.IsTracePreserving Q.map := by
  intro n K hC
  refine ⟨krausChannel K hC, ?_, ?_, ?_⟩
  · simpa [krausChannel] using krausForm_krausMap K
  · exact (completelyPositive_iff_physlibMap (krausMap K)).mp
      (completelyPositive_of_krausForm (krausForm_krausMap K))
  · exact (tracePreserving_iff_physlibMap (krausMap K)).mp
      (tracePreserving_of_krausComplete (krausForm_krausMap K) hC)

/-- Matrix transposition as a complex-linear endomorphism of the operator space. -/
noncomputable def transposeMap (D : ℕ) : Operator D →ₗ[ℂ] Operator D :=
  (Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ).toLinearMap

/-- Applying `transposeMap D` to an operator returns its transpose. -/
theorem transposeMap_apply {D : ℕ} (A : Operator D) :
    transposeMap D A = A.transpose := rfl

/-- Matrix transposition preserves the trace in every finite dimension. -/
theorem transposeMap_tracePreserving (D : ℕ) : TracePreserving (transposeMap D) := by
  intro A
  show Matrix.trace (A.transpose) = Matrix.trace A
  simp [Matrix.trace]

/-- The antisymmetric two-qubit vector with coefficients one at `(0, 1)` and minus one at `(1,
0)`. -/
noncomputable def wAnti : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- Swapping the two indices negates the vector `wAnti`. -/
theorem wAnti_swap : ∀ p : Fin 2 × Fin 2, wAnti p.swap = - wAnti p := by
  intro ⟨i, a⟩
  fin_cases i <;> fin_cases a <;> simp [wAnti, Prod.swap]

/-- The Choi matrix of transposition has entry one exactly when the input-output indices are
paired in the swapped order. -/
theorem choi_transposeMap_apply {D : ℕ} (x y : Fin D × Fin D) :
    ChoiMatrix (transposeMap D) x y = if x.1 = y.2 ∧ y.1 = x.2 then (1 : ℂ) else 0 := by
  have h : ∀ (a b c d : Fin D),
      matrixUnit (D := D) a b c d = if a = c ∧ b = d then (1 : ℂ) else 0 := by
    intro a b c d
    exact matrixUnit_apply a b c d
  by_cases h1 : x.1 = y.2 <;> by_cases h2 : y.1 = x.2 <;>
    simp [ChoiMatrix, transposeMap, h, h1, h2, ne_comm, eq_comm]

/-- The quadratic form of the qubit transpose Choi matrix at `wAnti` equals `-2`. -/
theorem transposeMap_two_quadratic :
    star wAnti ⬝ᵥ (ChoiMatrix (transposeMap 2) *ᵥ wAnti) = (-2 : ℂ) := by
  have hmv : ∀ x : Fin 2 × Fin 2,
      (ChoiMatrix (transposeMap 2) *ᵥ wAnti) x = wAnti x.swap := by
    intro ⟨i, a⟩
    fin_cases i <;> fin_cases a <;>
      simp [Matrix.mulVec_eq_sum, choi_transposeMap_apply, wAnti, Prod.swap,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  have hsum : ∑ p : Fin 2 × Fin 2, star (wAnti p) * wAnti p = (2 : ℂ) := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    simp [wAnti]
    norm_num
  simp only [dotProduct]
  simp only [hmv, Pi.star_apply, wAnti_swap, mul_neg]
  rw [Finset.sum_neg_distrib, hsum]

/-- The transpose map on qubit operators is not completely positive. -/
theorem transposeMap_two_not_completelyPositive :
    ¬ CompletelyPositive (transposeMap 2) := by
  intro hCP
  have hpsd : (ChoiMatrix (transposeMap 2)).PosSemidef :=
    choi_posSemidef_of_completelyPositive hCP
  have hq := hpsd.re_dotProduct_nonneg wAnti
  rw [transposeMap_two_quadratic] at hq
  norm_num at hq
end Qatlib.Concepts.ChannelTheory.Stinespring
