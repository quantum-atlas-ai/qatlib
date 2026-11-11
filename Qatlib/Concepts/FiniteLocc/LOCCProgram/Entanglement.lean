/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Concepts.FiniteLocc.LOCCProgram.PositiveBranchDecomposition
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessingTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.CollapsedMessageGuessingTele
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Finite bipartite entanglement and local protocols

This module develops finite-dimensional bipartite entanglement through coefficient matrices,
Gram spectra, and Schmidt decompositions. It proves the product-state rank criterion,
establishes the Bell-state properties, and relates separability defined by product vectors to
separability defined by product density operators; see [Wilde2017] and [Nielsen1999].

Nonnegative combinations of product density operators are preserved by local Kraus branches and
complete finite local protocols. The module also proves preservation of trace and the unaffected
marginal, positivity of the partial transpose for separable states, and nonseparability of the
singlet projector.

## Main statements

* `exists_schmidtData`: construct a Schmidt expansion with norm, marginal, and rank identities.
* `g1`: collect Schmidt, product-state, Bell-state, and dimension-boundary results.
* `g3`: collect local-protocol preservation, messaging, and communication-charge results.
* `isSeparableState_iff_isSeparableMixed`: equate the two finite convex-decomposition
  definitions.
* `bell_singlet_not_isSeparableState`: the singlet projector is not separable.

## References

* [Wilde, 2017][Wilde2017]
* [Nielsen, 1999][Nielsen1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge


namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Matrix
open scoped ComplexOrder Kronecker

variable {D E : ℕ}

/-- The property of being a finite nonnegative linear combination of tensor products of density
operators, without a normalization condition on the weights. -/
def IsSeparableSub (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Operator D) (τ : Fin n → Operator E),
    (∀ i, 0 ≤ p i) ∧ (∀ i, IsDensityOperator (σ i)) ∧ (∀ i, IsDensityOperator (τ i)) ∧
      ρ = ∑ i, (p i : ℂ) • TensorGate (σ i) (τ i)

/-- The zero bipartite operator is a nonnegative combination of product density operators. -/
theorem isSeparableSub_zero :
    IsSeparableSub (0 : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) := by
  refine ⟨0, 0, 0, 0, by simp, by simp, by simp, ?_⟩
  simp

/-- The sum of two nonnegative combinations of product density operators has the same property. -/
theorem isSeparableSub_add {ρ σ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hρ : IsSeparableSub ρ) (hσ : IsSeparableSub σ) : IsSeparableSub (ρ + σ) := by
  obtain ⟨n, p, a, b, hp, ha, hb, he⟩ := hρ
  obtain ⟨m, q, u, v, hq, hu, hv, hf⟩ := hσ
  refine ⟨n + m, fun k => Sum.elim p q ((@finSumFinEquiv n m).symm k),
    fun k => Sum.elim a u ((@finSumFinEquiv n m).symm k),
    fun k => Sum.elim b v ((@finSumFinEquiv n m).symm k), ?_, ?_, ?_, ?_⟩
  · intro k
    beta_reduce
    rcases hk : (@finSumFinEquiv n m).symm k with i | j
    · show 0 ≤ p i; exact hp i
    · show 0 ≤ q j; exact hq j
  · intro k
    beta_reduce
    rcases hk : (@finSumFinEquiv n m).symm k with i | j
    · show IsDensityOperator (a i); exact ha i
    · show IsDensityOperator (u j); exact hu j
  · intro k
    beta_reduce
    rcases hk : (@finSumFinEquiv n m).symm k with i | j
    · show IsDensityOperator (b i); exact hb i
    · show IsDensityOperator (v j); exact hv j
  · have hsplit : (∑ k : Fin (n + m),
          ((Sum.elim p q ((@finSumFinEquiv n m).symm k) : ℝ) : ℂ) •
            TensorGate (Sum.elim a u ((@finSumFinEquiv n m).symm k))
              (Sum.elim b v ((@finSumFinEquiv n m).symm k)))
        = (∑ x : Fin n ⊕ Fin m,
          ((Sum.elim p q x : ℝ) : ℂ) • TensorGate (Sum.elim a u x) (Sum.elim b v x)) :=
      Equiv.sum_comp (@finSumFinEquiv n m).symm
        (fun x : Fin n ⊕ Fin m =>
          ((Sum.elim p q x : ℝ) : ℂ) • TensorGate (Sum.elim a u x) (Sum.elim b v x))
    rw [hsplit, Fintype.sum_sum_type, he, hf]
    refine congrArg₂ _ ?_ ?_ <;>
      refine Finset.sum_congr rfl fun i _ => by simp [Sum.elim_inl, Sum.elim_inr]

/-- A finite sum of nonnegative combinations of product density operators has the same property. -/
theorem isSeparableSub_sum : ∀ (n : ℕ) (ρs : Fin n → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ),
    (∀ i, IsSeparableSub (ρs i)) → IsSeparableSub (∑ i, ρs i) := by
  intro n
  induction n with
  | zero =>
      intro ρs h
      simpa using isSeparableSub_zero
  | succ n ih =>
      intro ρs h
      rw [Fin.sum_univ_succ]
      exact isSeparableSub_add (h 0) (ih (fun i => ρs i.succ) (fun i => h i.succ))

/-- A separable mixed state is a nonnegative combination of product density operators. -/
theorem isSeparableSub_of_isSeparableMixed {ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (h : IsSeparableMixed ρ) : IsSeparableSub ρ := by
  obtain ⟨n, p, σ, τ, hp, _, hσ, hτ, he⟩ := h
  exact ⟨n, p, σ, τ, hp, hσ, hτ, he⟩

/-- The trace of a real scalar multiple of a tensor product of density operators equals that
scalar, viewed in `ℂ`. -/
private theorem trace_smul_tensorGate (p : ℝ) (σ : Operator D) (τ : Operator E)
    (hσ : IsDensityOperator σ) (hτ : IsDensityOperator τ) :
    Matrix.trace ((p : ℂ) • TensorGate σ τ) = (p : ℂ) := by
  show Matrix.trace ((p : ℂ) • (σ ⊗ₖ τ)) = (p : ℂ)
  rw [Matrix.trace_smul, Matrix.trace_kronecker]
  have h1 : Matrix.trace σ = 1 := hσ.2
  have h2 : Matrix.trace τ = 1 := hτ.2
  simp [h1, h2]

/-- A separable mixed state has trace one. -/
theorem trace_of_isSeparableMixed {ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (h : IsSeparableMixed ρ) : Matrix.trace ρ = 1 := by
  obtain ⟨n, p, σ, τ, _, hsum, hσ, hτ, he⟩ := h
  conv_lhs => rw [he]
  rw [Matrix.trace_sum]
  simp_rw [trace_smul_tensorGate _ _ _ (hσ _) (hτ _)]
  rw [← Complex.ofReal_sum, hsum]
  simp

/-- A nonnegative combination of product density operators with trace one is a separable mixed
state. -/
theorem isSeparableMixed_of_isSeparableSub {ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (h : IsSeparableSub ρ) (htr : Matrix.trace ρ = 1) : IsSeparableMixed ρ := by
  obtain ⟨n, p, σ, τ, hp, hσ, hτ, he⟩ := h
  refine ⟨n, p, σ, τ, hp, ?_, hσ, hτ, he⟩
  have hcomplex : (∑ i, (p i : ℂ)) = (1 : ℂ) := by
    have key : (∑ i, (p i : ℂ)) = Matrix.trace ρ := by
      conv_rhs => rw [he, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun i _ => (trace_smul_tensorGate _ _ _ (hσ i) (hτ i)).symm
    rw [key, htr]
  rw [← Complex.ofReal_sum] at hcomplex
  exact_mod_cast hcomplex

/-- A Kraus conjugation of a density operator is a nonnegative scalar multiple of a density
operator, given a density operator to use when the branch is zero. -/
theorem exists_density_smul (K σ : Operator D) (hσ : IsDensityOperator σ)
    (placeholder : Operator D) (hph : IsDensityOperator placeholder) :
    ∃ (c : ℝ) (σ' : Operator D),
      0 ≤ c ∧ IsDensityOperator σ' ∧ K * σ * K.conjTranspose = (c : ℂ) • σ' := by
  have hS : (K * σ * K.conjTranspose).PosSemidef :=
    hσ.1.mul_mul_conjTranspose_same K
  by_cases hz : K * σ * K.conjTranspose = 0
  · exact ⟨0, placeholder, le_refl _, hph, by simp [hz]⟩
  · have hne : Matrix.trace (K * σ * K.conjTranspose) ≠ 0 := fun h =>
      hz (hS.trace_eq_zero_iff.mp h)
    have hsum : Matrix.trace (K * σ * K.conjTranspose)
        = ∑ i, ((hS.isHermitian.eigenvalues i : ℝ) : ℂ) :=
      hS.isHermitian.trace_eq_sum_eigenvalues
    have hre : 0 ≤ (Matrix.trace (K * σ * K.conjTranspose)).re := by
      rw [hsum, Complex.re_sum]
      exact Finset.sum_nonneg fun i _ => hS.eigenvalues_nonneg i
    have hreal : Matrix.trace (K * σ * K.conjTranspose)
        = ((Matrix.trace (K * σ * K.conjTranspose)).re : ℂ) := by
      rw [hsum, Complex.re_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_re]
    have hc : 0 < (Matrix.trace (K * σ * K.conjTranspose)).re := by
      rcases lt_or_eq_of_le hre with h | h
      · exact h
      · refine absurd ?_ hne
        rw [hreal]
        exact_mod_cast h.symm
    have hre0 : ((Matrix.trace (K * σ * K.conjTranspose)).re : ℂ) ≠ 0 := by
      exact_mod_cast hc.ne'
    refine ⟨(Matrix.trace (K * σ * K.conjTranspose)).re,
      ((Matrix.trace (K * σ * K.conjTranspose)).re : ℂ)⁻¹ • (K * σ * K.conjTranspose),
      hre, ?_, ?_⟩
    · refine ⟨hS.smul (by exact_mod_cast inv_nonneg.mpr hc.le), ?_⟩
      rw [Matrix.trace_smul, hreal, smul_eq_mul]
      exact inv_mul_cancel₀ hre0
    · rw [smul_smul, mul_inv_cancel₀ hre0, one_smul]

/-- Conjugation by a Kraus operator on the first subsystem preserves nonnegative combinations of
product density operators. -/
theorem isSeparableSub_tensorLeft_kraus (K : Operator D)
    {ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ} (h : IsSeparableSub ρ) :
    IsSeparableSub
      (TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E)).conjTranspose) := by
  obtain ⟨n, p, σ, τ, hp, hσ, hτ, he⟩ := h
  by_cases hn : n = 0
  · subst hn
    have he0 : ρ = 0 := by rw [he]; simp
    subst he0
    simpa using (isSeparableSub_zero (D := D) (E := E))
  · have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hrew : TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E)).conjTranspose
        = ∑ i, (p i : ℂ) • TensorGate (K * σ i * K.conjTranspose) (τ i) := by
      conv_lhs => rw [he]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : TensorGate K (1 : Operator E) * ((p i : ℂ) • TensorGate (σ i) (τ i))
          * (TensorGate K (1 : Operator E)).conjTranspose
          = (p i : ℂ) • (TensorGate K (1 : Operator E) * TensorGate (σ i) (τ i)
              * (TensorGate K (1 : Operator E)).conjTranspose) := by
        rw [mul_smul_comm, smul_mul_assoc]
      rw [h1]
      have h2 : TensorGate K (1 : Operator E) * TensorGate (σ i) (τ i)
          * (TensorGate K (1 : Operator E)).conjTranspose
          = TensorGate (K * σ i * K.conjTranspose) (τ i) := by
        rw [tensorGate_conjTranspose, Matrix.conjTranspose_one]
        rw [Matrix.mul_assoc, tensorGate_mul, tensorGate_mul]
        rw [← Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
      rw [h2]
    choose c σ' hc hσ' hk using fun i =>
      exists_density_smul K (σ i) (hσ i) (σ i0) (hσ i0)
    have hkey : ∀ i, TensorGate (K * σ i * K.conjTranspose) (τ i)
        = ((c i : ℝ) : ℂ) • TensorGate (σ' i) (τ i) := by
      intro i
      rw [hk i]
      exact Matrix.smul_kronecker _ _ _
    rw [hrew]
    simp_rw [hkey, smul_smul]
    refine ⟨n, fun i => p i * c i, σ', τ, ?_, hσ', hτ, ?_⟩
    · intro i
      exact mul_nonneg (hp i) (hc i)
    · simp_rw [Complex.ofReal_mul]

/-- Conjugation by a Kraus operator on the second subsystem preserves nonnegative combinations
of product density operators. -/
theorem isSeparableSub_tensorRight_kraus (K : Operator E)
    {ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ} (h : IsSeparableSub ρ) :
    IsSeparableSub
      (TensorGate (1 : Operator D) K * ρ * (TensorGate (1 : Operator D) K).conjTranspose) := by
  obtain ⟨n, p, σ, τ, hp, hσ, hτ, he⟩ := h
  by_cases hn : n = 0
  · subst hn
    have he0 : ρ = 0 := by rw [he]; simp
    subst he0
    simpa using (isSeparableSub_zero (D := D) (E := E))
  · have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hrew : TensorGate (1 : Operator D) K * ρ * (TensorGate (1 : Operator D) K).conjTranspose
        = ∑ i, (p i : ℂ) • TensorGate (σ i) (K * τ i * K.conjTranspose) := by
      conv_lhs => rw [he]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : TensorGate (1 : Operator D) K * ((p i : ℂ) • TensorGate (σ i) (τ i))
          * (TensorGate (1 : Operator D) K).conjTranspose
          = (p i : ℂ) • (TensorGate (1 : Operator D) K * TensorGate (σ i) (τ i)
              * (TensorGate (1 : Operator D) K).conjTranspose) := by
        rw [mul_smul_comm, smul_mul_assoc]
      rw [h1]
      have h2 : TensorGate (1 : Operator D) K * TensorGate (σ i) (τ i)
          * (TensorGate (1 : Operator D) K).conjTranspose
          = TensorGate (σ i) (K * τ i * K.conjTranspose) := by
        rw [tensorGate_conjTranspose, Matrix.conjTranspose_one]
        rw [Matrix.mul_assoc, tensorGate_mul, tensorGate_mul]
        rw [Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc]
      rw [h2]
    choose c τ' hc hτ' hk using fun i =>
      exists_density_smul K (τ i) (hτ i) (τ i0) (hτ i0)
    have hkey : ∀ i, TensorGate (σ i) (K * τ i * K.conjTranspose)
        = ((c i : ℝ) : ℂ) • TensorGate (σ i) (τ' i) := by
      intro i
      rw [hk i]
      exact Matrix.kronecker_smul _ _ _
    rw [hrew]
    simp_rw [hkey, smul_smul]
    refine ⟨n, fun i => p i * c i, σ, τ', ?_, hσ, hτ', ?_⟩
    · intro i
      exact mul_nonneg (hp i) (hc i)
    · simp_rw [Complex.ofReal_mul]

/-- A finite sum in the first argument of `TensorGate` can be moved outside the tensor product. -/
theorem sum_tensorLeft {n : ℕ} (a : Fin n → Operator D) (B : Operator E) :
    (∑ i, TensorGate (a i) B) = TensorGate (∑ i, a i) B := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  simp [Matrix.sum_apply, tensorGate_apply, Finset.sum_mul]

/-- A finite sum in the second argument of `TensorGate` can be moved outside the tensor product. -/
theorem sum_tensorRight {n : ℕ} (A : Operator D) (b : Fin n → Operator E) :
    (∑ i, TensorGate A (b i)) = TensorGate A (∑ i, b i) := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  simp [Matrix.sum_apply, tensorGate_apply, Finset.mul_sum]

/-- The trace of a first-subsystem Kraus conjugation equals the trace of multiplication by its
local effect operator. -/
theorem trace_tensorLeft_sandwich (K : Operator D)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix.trace (TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E))ᴴ)
      = Matrix.trace (TensorGate (K.conjTranspose * K) (1 : Operator E) * ρ) := by
  rw [Matrix.trace_mul_cycle]
  congr 1
  rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul, Matrix.mul_one]

/-- The trace of a second-subsystem Kraus conjugation equals the trace of multiplication by its
local effect operator. -/
theorem trace_tensorRight_sandwich (K : Operator E)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix.trace (TensorGate (1 : Operator D) K * ρ * (TensorGate (1 : Operator D) K)ᴴ)
      = Matrix.trace (TensorGate (1 : Operator D) (K.conjTranspose * K) * ρ) := by
  rw [Matrix.trace_mul_cycle]
  congr 1
  rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul, Matrix.one_mul]

/-- The sum of branch traces of a complete first-subsystem Kraus family equals the input trace. -/
theorem trace_tensorLeft_instrument {n : ℕ} (ks : Fin n → Operator D)
    (hks : ∑ i, (ks i)ᴴ * ks i = 1)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    ∑ i, Matrix.trace (TensorGate (ks i) (1 : Operator E) * ρ *
      (TensorGate (ks i) (1 : Operator E))ᴴ) = Matrix.trace ρ := by
  simp_rw [trace_tensorLeft_sandwich]
  have hsum : ∑ i, TensorGate ((ks i)ᴴ * ks i) (1 : Operator E)
      = TensorGate (1 : Operator D) (1 : Operator E) := by
    conv_rhs => rw [← hks]
    exact sum_tensorLeft _ _
  calc
    ∑ i, Matrix.trace (TensorGate ((ks i)ᴴ * ks i) (1 : Operator E) * ρ)
        = Matrix.trace ((∑ i, TensorGate ((ks i)ᴴ * ks i) (1 : Operator E)) * ρ) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace (TensorGate (1 : Operator D) (1 : Operator E) * ρ) := by rw [hsum]
    _ = Matrix.trace ρ := by rw [tensorGate_one, one_mul]

/-- The sum of branch traces of a complete second-subsystem Kraus family equals the input trace. -/
theorem trace_tensorRight_instrument {n : ℕ} (ks : Fin n → Operator E)
    (hks : ∑ i, (ks i)ᴴ * ks i = 1)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    ∑ i, Matrix.trace (TensorGate (1 : Operator D) (ks i) * ρ *
      (TensorGate (1 : Operator D) (ks i))ᴴ) = Matrix.trace ρ := by
  simp_rw [trace_tensorRight_sandwich]
  have hsum : ∑ i, TensorGate (1 : Operator D) ((ks i)ᴴ * ks i)
      = TensorGate (1 : Operator D) (1 : Operator E) := by
    conv_rhs => rw [← hks]
    exact sum_tensorRight _ _
  calc
    ∑ i, Matrix.trace (TensorGate (1 : Operator D) ((ks i)ᴴ * ks i) * ρ)
        = Matrix.trace ((∑ i, TensorGate (1 : Operator D) ((ks i)ᴴ * ks i)) * ρ) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace (TensorGate (1 : Operator D) (1 : Operator E) * ρ) := by rw [hsum]
    _ = Matrix.trace ρ := by rw [tensorGate_one, one_mul]

/-- The channel of a complete finite local protocol preserves trace. -/
theorem trace_loccChannel (P : LoccProtocol D E) :
    LoccComplete P → ∀ ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ,
      Matrix.trace (LoccChannel P ρ) = Matrix.trace ρ := by
  induction P with
  | halt =>
      rintro _ ρ
      rfl
  | stepA n ks next ih =>
      rintro ⟨hks, hnext⟩ ρ
      show Matrix.trace (∑ i, LoccChannel (next i) _)
        = Matrix.trace ρ
      rw [Matrix.trace_sum]
      conv_rhs => rw [← trace_tensorLeft_instrument ks hks ρ]
      exact Finset.sum_congr rfl fun i _ => ih i (hnext i) _
  | stepB n ks next ih =>
      rintro ⟨hks, hnext⟩ ρ
      show Matrix.trace (∑ i, LoccChannel (next i) _)
        = Matrix.trace ρ
      rw [Matrix.trace_sum]
      conv_rhs => rw [← trace_tensorRight_instrument ks hks ρ]
      exact Finset.sum_congr rfl fun i _ => ih i (hnext i) _

/-- The channel of a complete finite local protocol preserves nonnegative combinations of
product density operators. -/
theorem isSeparableSub_loccChannel (P : LoccProtocol D E) :
    LoccComplete P → ∀ ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ,
      IsSeparableSub ρ → IsSeparableSub (LoccChannel P ρ) := by
  induction P with
  | halt =>
      rintro _ ρ h
      simpa using! h
  | stepA n ks next ih =>
      rintro ⟨hks, hnext⟩ ρ h
      show IsSeparableSub (∑ i, _)
      apply isSeparableSub_sum
      intro i
      exact ih i (hnext i) _ (isSeparableSub_tensorLeft_kraus (ks i) h)
  | stepB n ks next ih =>
      rintro ⟨hks, hnext⟩ ρ h
      show IsSeparableSub (∑ i, _)
      apply isSeparableSub_sum
      intro i
      exact ih i (hnext i) _ (isSeparableSub_tensorRight_kraus (ks i) h)

/-- Summing a complete instrument on the second subsystem leaves the first reduced operator
unchanged. -/
theorem partialTrace_right_instrument {n : ℕ} (ks : Fin n → Operator E)
    (hks : ∑ i, (ks i)ᴴ * ks i = 1)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (∑ i, TensorGate (1 : Operator D) (ks i) * ρ *
        (TensorGate (1 : Operator D) (ks i))ᴴ) = PartialTrace ρ := by
  conv_lhs => rw [partialTrace_sum]
  have hsum : (∑ i, PartialTrace (TensorGate (1 : Operator D) (ks i) * ρ *
        (TensorGate (1 : Operator D) (ks i))ᴴ))
      = ∑ i, PartialTrace (ρ * TensorGate (1 : Operator D) ((ks i)ᴴ * ks i)) := by
    refine Finset.sum_congr rfl fun i _ => partialTrace_discard_sandwich D E (ks i) ρ
  rw [hsum]
  have key : PartialTrace ρ
      = ∑ i, PartialTrace (ρ * TensorGate (1 : Operator D) ((ks i)ᴴ * ks i)) := by
    conv_lhs => rw [← Matrix.mul_one ρ, ← tensorGate_one]
    conv_lhs => rw [← hks]
    rw [← sum_tensorRight (1 : Operator D) (fun i => (ks i)ᴴ * ks i), Matrix.mul_sum,
      partialTrace_sum]
  rw [← key]

/-- Complete finite local protocols preserve separable mixed states and trace, and complete
second-subsystem instruments preserve the first marginal. This also bundles the two
message-guessing properties and the two-bit charge of a four-outcome first-party step; see
[Wilde2017] for quantum instruments. -/
theorem g3 :

  (∀ (D E : ℕ) (P : LoccProtocol D E), LoccComplete P →
    ∀ ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ,
      IsSeparableMixed ρ → IsSeparableMixed (LoccChannel P ρ)) ∧

  (∀ (D E : ℕ) (P : LoccProtocol D E), LoccComplete P →
    ∀ ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ,
      Matrix.trace (LoccChannel P ρ) = Matrix.trace ρ) ∧

  (∀ (D E n : ℕ) (ks : Fin n → Operator E),
    (∑ i, (ks i)ᴴ * ks i = 1) →
    ∀ ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ,
      PartialTrace (∑ i, TensorGate (1 : Operator D) (ks i) * ρ *
          (TensorGate (1 : Operator D) (ks i))ᴴ) = PartialTrace ρ) ∧

  (Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessing ∧
    Qatlib.Concepts.QuditTeleport.MessagingBounds.CollapsedMessageGuessing) ∧

  (∀ (D E : ℕ) (ks : Fin 4 → Operator D) (next : Fin 4 → LoccProtocol D E),
    LoccBits (LoccProtocol.stepA 4 ks next) =
      2 + Finset.univ.sup fun i => LoccBits (next i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D E P hP ρ hρ
    exact isSeparableMixed_of_isSeparableSub
      (isSeparableSub_loccChannel P hP ρ (isSeparableSub_of_isSeparableMixed hρ))
      (by rw [trace_loccChannel P hP ρ]; exact trace_of_isSeparableMixed hρ)
  · intro D E P hP ρ
    exact trace_loccChannel P hP ρ
  · intro D E n ks hks ρ
    exact partialTrace_right_instrument ks hks ρ
  · exact ⟨Qatlib.Concepts.QuditTeleport.MessagingBounds.prearrivalMessageGuessing,
      Qatlib.Concepts.QuditTeleport.MessagingBounds.collapsedMessageGuessing⟩
  · intro D E ks next
    show Nat.ceil (Real.log ((4 : ℕ) : ℝ) / Real.log 2)
        + Finset.univ.sup (fun i => LoccBits (next i))
      = 2 + Finset.univ.sup (fun i => LoccBits (next i))
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
      rw [show ((4 : ℕ) : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hdiv : Real.log ((4 : ℕ) : ℝ) / Real.log 2 = 2 := by
      rw [h4]
      exact mul_div_cancel_right₀ _ hlog2
    rw [hdiv]
    simp

/-- The product of a bipartite coefficient matrix with its conjugate transpose. -/
noncomputable def gramMatrix (ψ : QState (Fin D × Fin E)) : Matrix (Fin D) (Fin D) ℂ :=
  bipartiteMatrix ψ * (bipartiteMatrix ψ).conjTranspose

/-- The Gram matrix of a bipartite pure state is positive semidefinite. -/
theorem gramMatrix_posSemidef (ψ : QState (Fin D × Fin E)) : (gramMatrix ψ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose (bipartiteMatrix ψ)

/-- The Gram matrix of a bipartite pure state is Hermitian. -/
theorem gramMatrix_isHermitian (ψ : QState (Fin D × Fin E)) : (gramMatrix ψ).IsHermitian :=
  (gramMatrix_posSemidef ψ).isHermitian

/-- The indexed vector of the orthonormal eigenvector basis of the Gram matrix. -/
noncomputable def schmidtU (ψ : QState (Fin D × Fin E)) (j : Fin D) : QState (Fin D) :=
  ⇑((gramMatrix_isHermitian ψ).eigenvectorBasis j)

/-- The indexed real eigenvalue of the Gram matrix. -/
noncomputable def schmidtΛ (ψ : QState (Fin D × Fin E)) (j : Fin D) : ℝ :=
  (gramMatrix_isHermitian ψ).eigenvalues j

/-- The unitary matrix whose columns are the chosen Gram eigenvectors. -/
private noncomputable def gramUnitary (ψ : QState (Fin D × Fin E)) : Matrix (Fin D) (Fin D) ℂ :=
  (gramMatrix_isHermitian ψ).eigenvectorUnitary

/-- The coordinates of a chosen Schmidt eigenvector form the corresponding column of
`gramUnitary`. -/
theorem schmidtU_eq_gramUnitary (ψ : QState (Fin D × Fin E)) (i j : Fin D) :
    schmidtU ψ j i = gramUnitary ψ i j := by
  rfl

/-- Multiplying `gramUnitary` on the left by its conjugate transpose gives the identity. -/
private theorem gramUnitary_star_mul (ψ : QState (Fin D × Fin E)) :
    (gramUnitary ψ).conjTranspose * gramUnitary ψ = 1 := by
  have h := (gramMatrix_isHermitian ψ).eigenvectorUnitary.property
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

/-- Multiplying `gramUnitary` on the right by its conjugate transpose gives the identity. -/
private theorem gramUnitary_mul_star (ψ : QState (Fin D × Fin E)) :
    gramUnitary ψ * (gramUnitary ψ).conjTranspose = 1 := by
  have h := (gramMatrix_isHermitian ψ).eigenvectorUnitary.property
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
  exact h

/-- The chosen Gram eigenvectors are orthonormal. -/
theorem schmidtU_inner (ψ : QState (Fin D × Fin E)) (j j' : Fin D) :
    Qatlib.Foundations.PureStateMath.Inner (schmidtU ψ j) (schmidtU ψ j') = if j = j' then 1 else 0 := by
  rw [inner_apply]
  have hsum : (∑ i, (starRingEnd ℂ) (schmidtU ψ j i) * schmidtU ψ j' i)
      = ((gramUnitary ψ).conjTranspose * gramUnitary ψ) j j' := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [schmidtU_eq_gramUnitary, schmidtU_eq_gramUnitary]
    rfl
  rw [hsum, gramUnitary_star_mul, Matrix.one_apply]

/-- The sum of the outer products of the chosen Gram eigenvectors is the identity. -/
theorem sum_outerProduct_schmidtU (ψ : QState (Fin D × Fin E)) :
    ∑ j, outerProduct (schmidtU ψ j) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, outerProduct_apply]
  have hsum : (∑ j, schmidtU ψ j a * (starRingEnd ℂ) (schmidtU ψ j b))
      = (gramUnitary ψ * (gramUnitary ψ).conjTranspose) a b := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [schmidtU_eq_gramUnitary, schmidtU_eq_gramUnitary]
    rfl
  rw [hsum, gramUnitary_mul_star, Matrix.one_apply]

/-- Each chosen Gram eigenvector has eigenvalue `schmidtΛ`. -/
theorem schmidtU_mulVec (ψ : QState (Fin D × Fin E)) (j : Fin D) :
    gramMatrix ψ *ᵥ schmidtU ψ j = ((schmidtΛ ψ j : ℝ) : ℂ) • schmidtU ψ j := by
  simpa only [RCLike.real_smul_eq_coe_smul, schmidtΛ, schmidtU] using!
    (gramMatrix_isHermitian ψ).mulVec_eigenvectorBasis j

/-- Every Gram eigenvalue is nonnegative. -/
theorem schmidtΛ_nonneg (ψ : QState (Fin D × Fin E)) (j : Fin D) : 0 ≤ schmidtΛ ψ j := by
  exact (gramMatrix_posSemidef ψ).eigenvalues_nonneg j

/-- The Gram matrix equals the sum of its eigenvalues times the outer products of its chosen
eigenvectors. -/
theorem gramMatrix_eq_sum (ψ : QState (Fin D × Fin E)) :
    gramMatrix ψ = ∑ j, ((schmidtΛ ψ j : ℝ) : ℂ) • outerProduct (schmidtU ψ j) := by
  have h1 : gramMatrix ψ = gramMatrix ψ * (∑ j, outerProduct (schmidtU ψ j)) := by
    rw [sum_outerProduct_schmidtU, Matrix.mul_one]
  conv_lhs => rw [h1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext a b
  simp only [Matrix.mul_apply, outerProduct_apply]
  have hvec : (∑ k, gramMatrix ψ a k * (schmidtU ψ j k * (starRingEnd ℂ) (schmidtU ψ j b)))
      = (gramMatrix ψ *ᵥ schmidtU ψ j) a * (starRingEnd ℂ) (schmidtU ψ j b) := by
    have hform : (gramMatrix ψ *ᵥ schmidtU ψ j) a
        = ∑ k, gramMatrix ψ a k * schmidtU ψ j k := rfl
    rw [hform, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hvec, schmidtU_mulVec]
  show ((schmidtΛ ψ j : ℝ) : ℂ) * schmidtU ψ j a * (starRingEnd ℂ) (schmidtU ψ j b)
    = ((schmidtΛ ψ j : ℝ) : ℂ) * (schmidtU ψ j a * (starRingEnd ℂ) (schmidtU ψ j b))
  ring

/-- The trace of the Gram matrix equals the squared norm sum of the bipartite vector. -/
theorem trace_gramMatrix (ψ : QState (Fin D × Fin E)) :
    Matrix.trace (gramMatrix ψ) = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
  have h : Matrix.trace (gramMatrix ψ)
      = ∑ i : Fin D, ∑ j : Fin E, bipartiteMatrix ψ i j * (starRingEnd ℂ) (bipartiteMatrix ψ i j) := by
    rw [gramMatrix, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun j _ => by rfl
  rw [h]
  have h2 : (∑ i : Fin D, ∑ j : Fin E,
        bipartiteMatrix ψ i j * (starRingEnd ℂ) (bipartiteMatrix ψ i j))
      = ((∑ i : Fin D × Fin E, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have hz : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      intro z
      have hz' := Complex.mul_conj z
      rw [Complex.normSq_eq_norm_sq] at hz'
      simpa only [Complex.star_def] using hz'
    rw [bipartiteMatrix, Matrix.of_apply]
    exact hz _
  rw [h2]

/-- The finite set of indices with nonzero Gram eigenvalue. -/
noncomputable def schmidtSupport (ψ : QState (Fin D × Fin E)) : Finset (Fin D) :=
  Finset.univ.filter fun j => schmidtΛ ψ j ≠ 0

/-- The number of nonzero Gram eigenvalues equals the Schmidt rank. -/
theorem card_schmidtSupport (ψ : QState (Fin D × Fin E)) :
    (schmidtSupport ψ).card = schmidtRank ψ := by
  have hrank : (gramMatrix ψ).rank = schmidtRank ψ := by
    rw [gramMatrix, schmidtRank, Matrix.rank_self_mul_conjTranspose]
  have heig : (gramMatrix ψ).rank = Fintype.card {j // schmidtΛ ψ j ≠ 0} := by
    exact (gramMatrix_isHermitian ψ).rank_eq_card_non_zero_eigs
  have hcard : Fintype.card {j // schmidtΛ ψ j ≠ 0} = (schmidtSupport ψ).card := by
    rw [Fintype.card_subtype, schmidtSupport]
  calc
    (schmidtSupport ψ).card = Fintype.card {j // schmidtΛ ψ j ≠ 0} := hcard.symm
    _ = (gramMatrix ψ).rank := heig.symm
    _ = schmidtRank ψ := hrank

/-- A scalar multiplying a tensor state can be absorbed into its first factor. -/
theorem schmidtU_smul_tensor (c : ℂ) (u : QState (Fin D)) (v : QState (Fin E)) :
    c • TensorState u v = TensorState (c • u) v := by
  funext p
  obtain ⟨i, j⟩ := p
  simp [TensorState, smul_eq_mul]
  ring

/-- The inner product of a finite complex vector with itself is zero exactly when the vector is
zero. -/
theorem inner_self_eq_zero_iff {I : Type*} [Fintype I] (φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner φ φ = 0 ↔ φ = 0 := by
  classical
  constructor
  · intro h
    have h1 : ((∑ i, ‖φ i‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum, ← inner_self φ]
      exact h
    have hre : (∑ i, ‖φ i‖ ^ 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h1
    funext i
    have hi : ‖φ i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun (j : I) _ => sq_nonneg (‖φ j‖))).mp hre i
        (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    subst h
    simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct]

/-- The inner product is complex linear in its second argument. -/
theorem inner_smul_right {I : Type*} [Fintype I] (φ ψ : QState I) (c : ℂ) :
    Qatlib.Foundations.PureStateMath.Inner φ (c • ψ) = c * Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.smul_apply, smul_eq_mul]
  have h : (∑ i, star φ i * (c * ψ i)) = ∑ i, c * (star φ i * ψ i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h, ← Finset.mul_sum]

/-- The vector obtained by applying the adjoint coefficient matrix to a chosen Gram eigenvector. -/
noncomputable def schmidtW (ψ : QState (Fin D × Fin E)) (j : Fin D) : QState (Fin E) :=
  (bipartiteMatrix ψ).conjTranspose *ᵥ schmidtU ψ j

/-- The inner product of two adjoint matrix images equals the inner product with the
corresponding Gram action. -/
theorem inner_conjTranspose_mulVec (A : Matrix (Fin D) (Fin E) ℂ) (φ ψ : QState (Fin D)) :
    Qatlib.Foundations.PureStateMath.Inner (A.conjTranspose *ᵥ φ) (A.conjTranspose *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner φ ((A * A.conjTranspose) *ᵥ ψ) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- The adjoint images of distinct Gram eigenvectors are orthogonal, and each squared norm
equals its Gram eigenvalue. -/
theorem schmidtW_inner (ψ : QState (Fin D × Fin E)) (j j' : Fin D) :
    Qatlib.Foundations.PureStateMath.Inner (schmidtW ψ j) (schmidtW ψ j')
      = if j = j' then ((schmidtΛ ψ j : ℝ) : ℂ) else 0 := by
  rw [schmidtW, schmidtW, inner_conjTranspose_mulVec]
  show Qatlib.Foundations.PureStateMath.Inner (schmidtU ψ j)
      (gramMatrix ψ *ᵥ schmidtU ψ j') = _
  rw [schmidtU_mulVec, inner_smul_right]
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, schmidtU_inner, if_pos rfl, mul_one]
  · rw [if_neg h, schmidtU_inner, if_neg h, mul_zero]

/-- Conjugating a coordinate of an adjoint matrix-vector product gives the sum of matrix entries
times conjugated vector entries. -/
private theorem starRingEnd_conjTranspose_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) (v : I → ℂ) (j : J) :
    (starRingEnd ℂ) ((M.conjTranspose *ᵥ v) j)
      = ∑ b : I, M b j * (starRingEnd ℂ) (v b) := by
  show (starRingEnd ℂ) (∑ b : I, M.conjTranspose j b * v b)
    = ∑ b : I, M b j * (starRingEnd ℂ) (v b)
  simp only [Matrix.conjTranspose_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [map_mul, starRingEnd_apply, star_star]

/-- Every finite bipartite vector has a Schmidt expansion with nonnegative coefficients and
orthonormal factors. The expansion recovers its squared norm, first reduced operator, and
Schmidt rank. -/
theorem exists_schmidtData (ψ : QState (Fin D × Fin E)) :
    ∃ (r : ℕ) (c : Fin r → ℝ) (u : Fin r → QState (Fin D)) (v : Fin r → QState (Fin E)),
      (∀ i, 0 ≤ c i) ∧
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (v i) (v j) = if i = j then 1 else 0) ∧
      (ψ = ∑ i, (c i : ℂ) • TensorState (u i) (v i)) ∧
      (∑ i, c i * c i = ∑ i, ‖ψ i‖ ^ 2) ∧
      (PartialTrace (outerProduct ψ) = ∑ i, ((c i * c i : ℝ) : ℂ) • outerProduct (u i)) ∧
      (schmidtRank ψ = {i : Fin r | c i ≠ 0}.ncard) := by
  classical
  set S : Finset (Fin D) := schmidtSupport ψ with hSdef
  set r : ℕ := S.card with hrdef
  set e : S ≃ Fin r := Finset.equivFinOfCardEq (show S.card = r from rfl) with hedef
  have hmemL : ∀ k : Fin r, schmidtΛ ψ ((e.symm k : S)) ≠ 0 := by
    intro k
    have h : ((e.symm k : S) : Fin D) ∈ Finset.univ.filter (fun j => schmidtΛ ψ j ≠ 0) :=
      (e.symm k).property
    exact (Finset.mem_filter.mp h).2
  have heinj : ∀ k k' : Fin r, ((e.symm k : S) : Fin D) = ((e.symm k' : S) : Fin D) → k = k' := by
    intro k k' h
    have h1 : (e.symm k : S) = (e.symm k' : S) := Subtype.coe_injective h
    exact e.symm.injective h1
  set cfun : Fin r → ℝ := fun k => Real.sqrt (schmidtΛ ψ ((e.symm k : S)))
  set ufun : Fin r → QState (Fin D) := fun k => schmidtU ψ ((e.symm k : S))
  set vfun : Fin r → QState (Fin E) :=
    fun k j => (starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j)
      / ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)
  have hcnz : ∀ k : Fin r, ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ) ≠ 0 := by
    intro k
    exact_mod_cast (Real.sqrt_ne_zero (schmidtΛ_nonneg ψ _)).mpr (hmemL k)

  have hzero : ∀ t : Fin D, ¬ t ∈ S → (bipartiteMatrix ψ).conjTranspose *ᵥ schmidtU ψ t = 0 := by
    intro t ht
    have hLam : schmidtΛ ψ t = 0 := by
      by_contra hne
      apply ht
      show t ∈ schmidtSupport ψ
      simp only [schmidtSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hne
    have hself : Qatlib.Foundations.PureStateMath.Inner (schmidtW ψ t) (schmidtW ψ t) = 0 := by
      rw [schmidtW_inner, if_pos rfl, hLam]
      simp
    exact (inner_self_eq_zero_iff (schmidtW ψ t)).mp hself

  have hcomplete : ∀ (i : Fin D) (j : Fin E),
      (∑ t : Fin D, schmidtU ψ t i
          * (starRingEnd ℂ) (schmidtW ψ t j)) = bipartiteMatrix ψ i j := by
    intro i j
    simp_rw [schmidtW, starRingEnd_conjTranspose_mulVec]
    have hswap : (∑ t : Fin D, schmidtU ψ t i
          * (∑ b : Fin D, bipartiteMatrix ψ b j * (starRingEnd ℂ) (schmidtU ψ t b)))
        = ∑ b : Fin D, bipartiteMatrix ψ b j
            * (∑ t : Fin D, schmidtU ψ t i * (starRingEnd ℂ) (schmidtU ψ t b)) := by
      have h1 : (∑ t : Fin D, schmidtU ψ t i
            * (∑ b : Fin D, bipartiteMatrix ψ b j * (starRingEnd ℂ) (schmidtU ψ t b)))
          = ∑ t : Fin D, ∑ b : Fin D, schmidtU ψ t i
              * (bipartiteMatrix ψ b j * (starRingEnd ℂ) (schmidtU ψ t b)) :=
        Finset.sum_congr rfl fun t _ => Finset.mul_sum _ _ _
      rw [h1]
      have h2 : (∑ t : Fin D, ∑ b : Fin D, schmidtU ψ t i
            * (bipartiteMatrix ψ b j * (starRingEnd ℂ) (schmidtU ψ t b)))
          = ∑ b : Fin D, ∑ t : Fin D, schmidtU ψ t i
              * (bipartiteMatrix ψ b j * (starRingEnd ℂ) (schmidtU ψ t b)) :=
        Finset.sum_comm
      rw [h2]
      refine Finset.sum_congr rfl fun b _ => ?_
      have h3 : (∑ t : Fin D, schmidtU ψ t i
            * (bipartiteMatrix ψ b j * (starRingEnd ℂ) (schmidtU ψ t b)))
          = ∑ t : Fin D, bipartiteMatrix ψ b j
              * (schmidtU ψ t i * (starRingEnd ℂ) (schmidtU ψ t b)) :=
        Finset.sum_congr rfl fun t _ => by ring
      rw [h3]
      exact (Finset.mul_sum _ _ _).symm
    rw [hswap]
    have huu : ∀ b : Fin D, (∑ t : Fin D, schmidtU ψ t i * (starRingEnd ℂ) (schmidtU ψ t b))
        = (gramUnitary ψ * (gramUnitary ψ).conjTranspose) i b := by
      intro b
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [schmidtU_eq_gramUnitary, schmidtU_eq_gramUnitary]
      rfl
    simp_rw [huu]
    have h1 : (∑ b : Fin D, bipartiteMatrix ψ b j
          * (gramUnitary ψ * (gramUnitary ψ).conjTranspose) i b)
        = (∑ b : Fin D, (gramUnitary ψ * (gramUnitary ψ).conjTranspose) i b
          * bipartiteMatrix ψ b j) :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [h1, ← Matrix.mul_apply, gramUnitary_mul_star, Matrix.one_mul]
  refine ⟨r, cfun, ufun, vfun, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact Real.sqrt_nonneg _
  · have hU : ∀ a b : Fin r, Qatlib.Foundations.PureStateMath.Inner (ufun a) (ufun b) = if a = b then 1 else 0 := by
      intro a b
      show Qatlib.Foundations.PureStateMath.Inner (schmidtU ψ ((e.symm a : S))) (schmidtU ψ ((e.symm b : S)))
        = if a = b then 1 else 0
      rw [schmidtU_inner]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hab, if_neg (fun hcon => hab (heinj a b hcon))]
    exact hU
  · have hcross : ∀ a b : Fin r,
        (∑ j : Fin E, schmidtW ψ ((e.symm a : S)) j
            * (starRingEnd ℂ) (schmidtW ψ ((e.symm b : S)) j))
        = if a = b then ((cfun a * cfun a : ℝ) : ℂ) else 0 := by
      intro a b
      have hconj : (∑ j : Fin E, schmidtW ψ ((e.symm a : S)) j
            * (starRingEnd ℂ) (schmidtW ψ ((e.symm b : S)) j))
          = (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner (schmidtW ψ ((e.symm a : S)))
              (schmidtW ψ ((e.symm b : S)))) := by
        rw [inner_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul, Complex.conj_conj]
      rw [hconj, schmidtW_inner]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl]
        rw [show (cfun a * cfun a : ℝ) = schmidtΛ ψ ((e.symm a : S)) from
          Real.mul_self_sqrt (schmidtΛ_nonneg ψ _)]
        exact Complex.conj_ofReal _
      · rw [if_neg hab, if_neg (fun hcon => hab (heinj a b hcon)), map_zero]
    intro k k'
    have hleaf : ∀ j : Fin E,
        (starRingEnd ℂ) (vfun k j) * vfun k' j
          = (((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)⁻¹
              * ((Real.sqrt (schmidtΛ ψ ((e.symm k' : S))) : ℝ) : ℂ)⁻¹)
            * (schmidtW ψ ((e.symm k : S)) j
                * (starRingEnd ℂ) (schmidtW ψ ((e.symm k' : S)) j)) := by
      intro j
      show (starRingEnd ℂ) ((starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j)
            / ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ))
          * ((starRingEnd ℂ) (schmidtW ψ ((e.symm k' : S)) j)
            / ((Real.sqrt (schmidtΛ ψ ((e.symm k' : S))) : ℝ) : ℂ))
          = (((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)⁻¹
              * ((Real.sqrt (schmidtΛ ψ ((e.symm k' : S))) : ℝ) : ℂ)⁻¹)
            * (schmidtW ψ ((e.symm k : S)) j
                * (starRingEnd ℂ) (schmidtW ψ ((e.symm k' : S)) j))
      simp only [div_eq_mul_inv, map_mul, map_inv₀, Complex.conj_conj, Complex.conj_ofReal]
      ring
    rw [inner_apply]
    have hsum : (∑ j : Fin E, (starRingEnd ℂ) (vfun k j) * vfun k' j)
        = (((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)⁻¹
            * ((Real.sqrt (schmidtΛ ψ ((e.symm k' : S))) : ℝ) : ℂ)⁻¹)
          * (∑ j : Fin E, schmidtW ψ ((e.symm k : S)) j
              * (starRingEnd ℂ) (schmidtW ψ ((e.symm k' : S)) j)) := by
      have h1 : (∑ j : Fin E, (starRingEnd ℂ) (vfun k j) * vfun k' j)
          = ∑ j : Fin E, (((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)⁻¹
              * ((Real.sqrt (schmidtΛ ψ ((e.symm k' : S))) : ℝ) : ℂ)⁻¹)
            * (schmidtW ψ ((e.symm k : S)) j
                * (starRingEnd ℂ) (schmidtW ψ ((e.symm k' : S)) j)) :=
        Finset.sum_congr rfl fun j _ => hleaf j
      rw [h1]
      exact (Finset.mul_sum _ _ _).symm
    rw [hsum, hcross k k']
    by_cases h : k = k'
    · subst h
      rw [if_pos rfl, if_pos rfl]
      have hsq : (cfun k * cfun k : ℝ) = schmidtΛ ψ ((e.symm k : S)) :=
        Real.mul_self_sqrt (schmidtΛ_nonneg ψ _)
      have hAA : ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)
          * ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)
          = ((schmidtΛ ψ ((e.symm k : S)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (schmidtΛ_nonneg ψ _)]
      rw [hsq, ← hAA]
      field_simp [hcnz k]
    · rw [if_neg h, if_neg h, mul_zero]
  · funext p
    obtain ⟨i, j⟩ := p
    have hpt : (∑ k : Fin r, (cfun k : ℂ) • TensorState (ufun k) (vfun k)) (i, j)
        = ∑ k : Fin r, schmidtU ψ ((e.symm k : S)) i
            * (starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      show ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)
          * (schmidtU ψ ((e.symm k : S)) i
            * ((starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j)
              / ((Real.sqrt (schmidtΛ ψ ((e.symm k : S))) : ℝ) : ℂ)))
        = schmidtU ψ ((e.symm k : S)) i * (starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j)
      field_simp [hcnz k]
    rw [hpt]
    have hsplit : (∑ k : Fin r, schmidtU ψ ((e.symm k : S)) i
          * (starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j))
        = ∑ t ∈ S, schmidtU ψ t i * (starRingEnd ℂ) (schmidtW ψ t j) :=
      (Fintype.sum_equiv e.symm
          (fun k : Fin r => schmidtU ψ ((e.symm k : S)) i
            * (starRingEnd ℂ) (schmidtW ψ ((e.symm k : S)) j))
          (fun t : S => schmidtU ψ t i * (starRingEnd ℂ) (schmidtW ψ t j)) (fun _ => rfl)).trans
        (Finset.sum_coe_sort S
          (fun t => schmidtU ψ t i * (starRingEnd ℂ) (schmidtW ψ t j)))
    rw [hsplit]
    have hfull : (∑ t ∈ S, schmidtU ψ t i * (starRingEnd ℂ) (schmidtW ψ t j))
        = ∑ t : Fin D, schmidtU ψ t i * (starRingEnd ℂ) (schmidtW ψ t j) := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun t _ ht => ?_)
      rw [schmidtW, hzero t ht]
      simp
    rw [hfull, hcomplete]
    rfl
  · have hsum1 : (∑ k : Fin r, cfun k * cfun k) = ∑ t ∈ S, schmidtΛ ψ t := by
      rw [Fintype.sum_equiv e.symm (fun k : Fin r => cfun k * cfun k)
          (fun t : S => schmidtΛ ψ t)
          (fun k => Real.mul_self_sqrt (schmidtΛ_nonneg ψ ((e.symm k : S)))),
        Finset.sum_coe_sort]
    rw [hsum1]
    have hsum2 : (∑ t ∈ S, schmidtΛ ψ t) = ∑ t : Fin D, schmidtΛ ψ t := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun t _ ht => ?_)
      have hLam : schmidtΛ ψ t = 0 := by
        by_contra hne
        apply ht
        show t ∈ schmidtSupport ψ
        simp only [schmidtSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne
      rw [hLam]
    rw [hsum2]
    have htrace : ((∑ t : Fin D, schmidtΛ ψ t : ℝ) : ℂ) = Matrix.trace (gramMatrix ψ) := by
      rw [Complex.ofReal_sum]
      exact (gramMatrix_isHermitian ψ).trace_eq_sum_eigenvalues.symm
    have hre : (∑ t : Fin D, schmidtΛ ψ t : ℝ) = ∑ i, ‖ψ i‖ ^ 2 := by
      have h := congrArg Complex.re htrace
      rw [trace_gramMatrix] at h
      simp only [Complex.ofReal_re] at h
      exact h
    rw [hre]
  · ext a b
    have hL : PartialTrace (outerProduct ψ) a b
        = ∑ j : Fin E, bipartiteMatrix ψ a j * (starRingEnd ℂ) (bipartiteMatrix ψ b j) := by
      show (∑ j : Fin E, outerProduct ψ (a, j) (b, j)) = _
      simp only [outerProduct_apply, bipartiteMatrix, Matrix.of_apply]
    rw [hL]
    have hgram : (∑ j : Fin E, bipartiteMatrix ψ a j * (starRingEnd ℂ) (bipartiteMatrix ψ b j))
        = gramMatrix ψ a b := rfl
    rw [hgram, gramMatrix_eq_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hpt : ∀ t : Fin D,
        ((schmidtΛ ψ t : ℝ) : ℂ) * outerProduct (schmidtU ψ t) a b
          = schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ) * (starRingEnd ℂ) (schmidtU ψ t b) := by
      intro t
      rw [outerProduct_apply]
      ring
    simp_rw [hpt]
    have hsplit : (∑ t : Fin D, schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ)
          * (starRingEnd ℂ) (schmidtU ψ t b))
        = ∑ t ∈ S, schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ)
            * (starRingEnd ℂ) (schmidtU ψ t b) := by
      refine Eq.symm ?_
      refine Finset.sum_subset (Finset.subset_univ _) (fun t _ ht => ?_)
      have hLam : schmidtΛ ψ t = 0 := by
        by_contra hne
        apply ht
        show t ∈ schmidtSupport ψ
        simp only [schmidtSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne
      rw [hLam]
      simp
    rw [hsplit]
    have hsumS : (∑ t ∈ S, schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ)
          * (starRingEnd ℂ) (schmidtU ψ t b))
        = ∑ k : Fin r, ((cfun k * cfun k : ℝ) : ℂ)
            * outerProduct (ufun k) a b := by
      have himg : (∑ k : Fin r, schmidtU ψ ((e.symm k : S)) a
            * ((schmidtΛ ψ ((e.symm k : S)) : ℝ) : ℂ)
            * (starRingEnd ℂ) (schmidtU ψ ((e.symm k : S)) b))
          = ∑ t ∈ S, schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ)
              * (starRingEnd ℂ) (schmidtU ψ t b) :=
        (Fintype.sum_equiv e.symm
          (fun k : Fin r => schmidtU ψ ((e.symm k : S)) a
            * ((schmidtΛ ψ ((e.symm k : S)) : ℝ) : ℂ)
            * (starRingEnd ℂ) (schmidtU ψ ((e.symm k : S)) b))
          (fun t : S => schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ)
            * (starRingEnd ℂ) (schmidtU ψ t b)) (fun _ => rfl)).trans
          (Finset.sum_coe_sort S
            (fun t => schmidtU ψ t a * ((schmidtΛ ψ t : ℝ) : ℂ)
              * (starRingEnd ℂ) (schmidtU ψ t b)))
      rw [← himg]
      refine Finset.sum_congr rfl fun k _ => ?_
      show schmidtU ψ ((e.symm k : S)) a * ((schmidtΛ ψ ((e.symm k : S)) : ℝ) : ℂ)
            * (starRingEnd ℂ) (schmidtU ψ ((e.symm k : S)) b)
          = ((cfun k * cfun k : ℝ) : ℂ) * outerProduct (ufun k) a b
      rw [outerProduct_apply]
      have hsq : (cfun k * cfun k : ℝ) = schmidtΛ ψ ((e.symm k : S)) :=
        Real.mul_self_sqrt (schmidtΛ_nonneg ψ _)
      rw [hsq]
      ring
    rw [hsumS]
  · rw [← card_schmidtSupport, ← hSdef, ← hrdef]
    have hall : ∀ k : Fin r, cfun k ≠ 0 := by
      intro k
      have := hmemL k
      show Real.sqrt (schmidtΛ ψ ((e.symm k : S))) ≠ 0
      exact (Real.sqrt_ne_zero (schmidtΛ_nonneg ψ _)).mpr this
    have heq : {i : Fin r | cfun i ≠ 0} = (Set.univ : Set (Fin r)) :=
      Set.eq_univ_of_forall hall
    rw [heq, Set.ncard_univ]
    simp

/-- A bipartite vector is a product state exactly when its Schmidt rank is at most one. -/
private theorem isProductState_iff_schmidtRank {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    IsProductState ψ ↔ schmidtRank ψ ≤ 1 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    have hmat : bipartiteMatrix (TensorState a b) = Matrix.vecMulVec a b := by
      ext i j
      rfl
    rw [schmidtRank, hmat]
    exact Matrix.rank_vecMulVec_le _ _
  · intro hrank
    obtain ⟨r, c, u, v, _, _, _, hsum, _, _, hrank'⟩ := exists_schmidtData ψ
    rw [hrank'] at hrank
    have hle : ({i : Fin r | c i ≠ 0} : Set (Fin r)).ncard ≤ 1 := hrank
    rw [Set.ncard_le_one_iff] at hle
    by_cases hz : ∃ i : Fin r, c i ≠ 0
    · obtain ⟨i0, hi0⟩ := hz
      have huniq : ∀ j : Fin r, c j ≠ 0 → j = i0 := by
        intro j hj
        exact hle (a := j) (b := i0) hj hi0
      have hsingle : (∑ i : Fin r, (c i : ℂ) • TensorState (u i) (v i))
          = (c i0 : ℂ) • TensorState (u i0) (v i0) := by
        refine Finset.sum_eq_single i0 (fun i _ hi => ?_) (fun hi => absurd (Finset.mem_univ i0) hi)
        have hci : c i = 0 := by
          by_contra hc
          exact hi (huniq i hc)
        rw [hci]
        simp
      refine ⟨(c i0 : ℂ) • u i0, v i0, ?_⟩
      rw [← schmidtU_smul_tensor, ← hsingle, hsum]
    · have hz' : ∀ i : Fin r, c i = 0 := by
        intro i
        by_contra hc
        exact hz ⟨i, hc⟩
      have hzero : ψ = 0 := by
        rw [hsum]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [hz']
      refine ⟨0, 0, ?_⟩
      rw [hzero]
      funext p
      obtain ⟨i, j⟩ := p
      simp [TensorState]

/-- Every vector in the Boolean-indexed Bell family is normalized. -/
private theorem bell_norm (s : Bool × Bool) : Normalized (bell s) := by
  fin_cases s
  all_goals
    unfold Normalized
    simp only [bell, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_smul, neg_smul]
    simp only [Pi.add_apply, Pi.neg_apply, ket_apply]
  all_goals simp
  all_goals norm_num

/-- The first reduced operator of each Bell vector is one half of the identity. -/
private theorem bell_marginal (s : Bool × Bool) :
    PartialTrace (outerProduct (bell s)) = (1 / 2 : ℂ) • (1 : Operator 2) := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j
  all_goals
    simp only [PartialTrace, outerProduct_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Fin.sum_univ_two, bell, Pi.smul_apply,
      ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_smul, neg_smul, Pi.add_apply, Pi.neg_apply, ket_apply]
  all_goals simp
  all_goals norm_num
  all_goals
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv, h2]
    norm_num

/-- The coefficient matrix of each Bell vector has nonzero determinant. -/
private theorem bell_det (s : Bool × Bool) : (bipartiteMatrix (bell s)).det ≠ 0 := by
  fin_cases s
  all_goals
    rw [Matrix.det_fin_two]
    simp only [bipartiteMatrix, Matrix.of_apply, bell, Pi.smul_apply, smul_eq_mul,
      ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_smul, neg_smul, Pi.add_apply, Pi.neg_apply, ket_apply]
  all_goals simp

/-- Each Bell vector has Schmidt rank two. -/
private theorem bell_schmidtRank (s : Bool × Bool) : schmidtRank (bell s) = 2 := by
  have hunit : IsUnit (bipartiteMatrix (bell s)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (bell_det s))
  rw [schmidtRank, Matrix.rank_of_isUnit _ hunit]
  norm_num

/-- Each Bell vector is normalized and entangled. -/
private theorem bell_entangled (s : Bool × Bool) : IsEntangled (bell s) := by
  refine ⟨bell_norm s, ?_⟩
  intro h
  have hle : schmidtRank (bell s) ≤ 1 := (isProductState_iff_schmidtRank _).mp h
  rw [bell_schmidtRank s] at hle
  norm_num at hle

/-- Normalized bipartite vectors possess Schmidt decompositions with normalized squared
coefficients, the stated marginal, and the stated rank count, as in [Wilde, Theorem
3.8.1][Wilde2017]. This also establishes the product-state rank criterion, the Bell-state
properties, and the zero- and one-dimensional boundary cases; see [Nielsen1999]. -/
theorem g1 :

  (∀ (D E : ℕ) (ψ : QState (Fin D × Fin E)), Normalized ψ →
    ∃ (r : ℕ) (c : Fin r → ℝ) (u : Fin r → QState (Fin D)) (v : Fin r → QState (Fin E)),
      (∀ i, 0 ≤ c i) ∧
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (v i) (v j) = if i = j then 1 else 0) ∧
      (ψ = ∑ i, (c i : ℂ) • TensorState (u i) (v i)) ∧
      (∑ i, c i * c i = 1) ∧
      (PartialTrace (outerProduct ψ) = ∑ i, ((c i * c i : ℝ) : ℂ) • outerProduct (u i)) ∧
      (schmidtRank ψ = {i : Fin r | c i ≠ 0}.ncard)) ∧

  (∀ (D E : ℕ) (ψ : QState (Fin D × Fin E)),
    (IsProductState ψ ↔ schmidtRank ψ ≤ 1)) ∧

  (∀ s : Bool × Bool,
    Normalized (bell s) ∧ IsEntangled (bell s) ∧
    (PartialTrace (outerProduct (bell s)) = (1 / 2 : ℂ) • (1 : Operator 2))) ∧

  (∀ (D E : ℕ), D = 0 ∨ E = 0 → ∀ ψ : QState (Fin D × Fin E), ¬ Normalized ψ) ∧

  (∀ ψ : QState (Fin 1 × Fin 1), Normalized ψ → IsProductState ψ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D E ψ hψ
    obtain ⟨r, c, u, v, h1, h2, h3, h4, h5, h6, h7⟩ := exists_schmidtData ψ
    exact ⟨r, c, u, v, h1, h2, h3, h4, by rw [h5]; exact hψ, h6, h7⟩
  · intro D E ψ
    exact isProductState_iff_schmidtRank ψ
  · intro s
    exact ⟨bell_norm s, bell_entangled s, bell_marginal s⟩
  · intro D E h ψ hN
    have hN' : ∑ i : Fin D × Fin E, ‖ψ i‖ ^ 2 = 1 := hN
    cases h with
    | inl hD =>
      subst hD
      haveI : IsEmpty (Fin 0 × Fin E) := ⟨fun p => Fin.elim0 p.1⟩
      rw [Finset.sum_of_isEmpty] at hN'
      exact absurd hN' zero_ne_one
    | inr hE =>
      subst hE
      haveI : IsEmpty (Fin D × Fin 0) := ⟨fun p => Fin.elim0 p.2⟩
      rw [Finset.sum_of_isEmpty] at hN'
      exact absurd hN' zero_ne_one
  · intro ψ _
    refine ⟨fun _ => ψ (0, 0), fun _ => (1 : ℂ), ?_⟩
    funext p
    obtain ⟨i, j⟩ := p
    show ψ (i, j) = TensorState (fun _ => ψ (0, 0)) (fun _ => (1 : ℂ)) (i, j)
    rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
    simp [TensorState]

/-- The outer product of a tensor state is the tensor product of the two outer products. -/
theorem outerProduct_tensorState (a : QState (Fin D)) (b : QState (Fin E)) :
    outerProduct (TensorState a b) = TensorGate (outerProduct a) (outerProduct b) := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [outerProduct_apply, tensorGate_apply, tensorState_apply, map_mul]
  ring

/-- Complex conjugation of an inner product interchanges its arguments. -/
theorem star_inner {I : Type*} [Fintype I] [DecidableEq I] (a b : QState I) :
    (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner a b) = Qatlib.Foundations.PureStateMath.Inner b a := by
  rw [inner_apply, inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

/-- The outer product of a normalized vector is a density operator. -/
theorem isDensityOperator_outerProduct {d : ℕ} (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    IsDensityOperator (outerProduct ψ) := by
  refine ⟨?_, ?_⟩
  · refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · ext i j
      simp [outerProduct, Matrix.conjTranspose_apply]
      ring
    · intro x
      have hform : star x ⬝ᵥ (outerProduct ψ *ᵥ x)
          = (Qatlib.Foundations.PureStateMath.Inner ψ x) * (Qatlib.Foundations.PureStateMath.Inner x ψ) := by
        rw [outerProduct_mulVec, dotProduct_smul, smul_eq_mul]
        rfl
      rw [hform, ← star_inner x ψ, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact Complex.zero_le_real.mpr (sq_nonneg ‖Qatlib.Foundations.PureStateMath.Inner x ψ‖)
  · have htr : Matrix.trace (outerProduct ψ) = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.diag_apply, outerProduct_apply, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    rw [htr, ← inner_self]
    exact (normalized_iff_inner_self ψ).mp hψ

/-- The outer products of a Hermitian matrix's orthonormal eigenvector basis sum to the
identity. -/
theorem sum_outerProduct_eigenvectorBasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : ∑ j, outerProduct ⇑(hA.eigenvectorBasis j) = 1 := by
  set u : Matrix.unitaryGroup (Fin d) ℂ := hA.eigenvectorUnitary with hudecl
  have huu : (u : Matrix (Fin d) (Fin d) ℂ) * (u : Matrix (Fin d) (Fin d) ℂ).conjTranspose = 1 := by
    have h := u.property
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  ext a b
  simp only [Matrix.sum_apply, outerProduct_apply]
  have hsum : (∑ j, ⇑(hA.eigenvectorBasis j) a * (starRingEnd ℂ) (⇑(hA.eigenvectorBasis j) b))
      = ((u : Matrix (Fin d) (Fin d) ℂ) * (u : Matrix (Fin d) (Fin d) ℂ).conjTranspose) a b := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hA.eigenvectorUnitary_apply a j, ← hA.eigenvectorUnitary_apply b j]
    rfl
  rw [hsum, huu, Matrix.one_apply]

/-- The eigenvalues of a positive semidefinite trace-one matrix sum to one. -/
theorem sum_eigenvalues_eq_one {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (htr : Matrix.trace A = 1) : ∑ j, hA.1.eigenvalues j = 1 := by
  have h := hA.1.trace_eq_sum_eigenvalues
  rw [htr] at h
  have hre : ((∑ j, hA.1.eigenvalues j : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    exact h.symm
  exact_mod_cast hre

/-- Each vector in the chosen eigenvector basis of a Hermitian matrix is normalized. -/
theorem normalized_eigenvectorBasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (j : Fin d) : Normalized ⇑(hA.eigenvectorBasis j) := by
  have hnorm : ‖(hA.eigenvectorBasis j : EuclideanSpace ℂ (Fin d))‖ = 1 :=
    hA.eigenvectorBasis.orthonormal.1 j
  have hsq := EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis j : EuclideanSpace ℂ (Fin d))
  rw [hnorm] at hsq
  simpa [Normalized] using hsq.symm

/-- Every finite-dimensional density operator is a convex combination of normalized pure-state
projectors. -/
theorem exists_pure_decomposition {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : IsDensityOperator σ) :
    ∃ (c : Fin d → ℝ) (u : Fin d → QState (Fin d)),
      (∀ i, 0 ≤ c i) ∧ (∑ i, c i = 1) ∧ (∀ i, Normalized (u i)) ∧
        σ = ∑ i, (c i : ℂ) • outerProduct (u i) := by
  classical
  refine ⟨fun j => hσ.1.isHermitian.eigenvalues j,
    fun j => ⇑(hσ.1.isHermitian.eigenvectorBasis j), ?_, ?_, ?_, ?_⟩
  · intro i
    exact hσ.1.eigenvalues_nonneg i
  · exact sum_eigenvalues_eq_one σ hσ.1 hσ.2
  · intro i
    exact normalized_eigenvectorBasis σ hσ.1.isHermitian i
  · have hmul : ∀ j, σ *ᵥ ⇑(hσ.1.isHermitian.eigenvectorBasis j)
        = ((hσ.1.isHermitian.eigenvalues j : ℝ) : ℂ) • ⇑(hσ.1.isHermitian.eigenvectorBasis j) := by
      intro j
      rw [hσ.1.isHermitian.mulVec_eigenvectorBasis j, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    have hcomplete : (∑ j, outerProduct ⇑(hσ.1.isHermitian.eigenvectorBasis j)) = 1 :=
      sum_outerProduct_eigenvectorBasis σ hσ.1.isHermitian
    have h1 : σ = σ * (∑ j, outerProduct ⇑(hσ.1.isHermitian.eigenvectorBasis j)) := by
      rw [hcomplete, Matrix.mul_one]
    conv_lhs => rw [h1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext a b
    simp only [Matrix.mul_apply, outerProduct_apply, Matrix.smul_apply, smul_eq_mul]
    have hvec : (∑ k, σ a k * (⇑(hσ.1.isHermitian.eigenvectorBasis j) k
          * (starRingEnd ℂ) (⇑(hσ.1.isHermitian.eigenvectorBasis j) b)))
        = (σ *ᵥ ⇑(hσ.1.isHermitian.eigenvectorBasis j)) a
            * (starRingEnd ℂ) (⇑(hσ.1.isHermitian.eigenvectorBasis j) b) := by
      have hform : (σ *ᵥ ⇑(hσ.1.isHermitian.eigenvectorBasis j)) a
          = ∑ k, σ a k * ⇑(hσ.1.isHermitian.eigenvectorBasis j) k := rfl
      rw [hform, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hvec, hmul j, Pi.smul_apply, smul_eq_mul]
    ring

/-- Partial transpose swaps the second subsystem indices of a matrix entry. -/
theorem partialTranspose_apply (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (p q : Fin D × Fin E) : PartialTranspose A p q = A (p.1, q.2) (q.1, p.2) := rfl

/-- Partial transpose preserves addition. -/
theorem partialTranspose_add (A B : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTranspose (A + B) = PartialTranspose A + PartialTranspose B := by
  ext p q
  simp [partialTranspose_apply]

/-- Partial transpose commutes with complex scalar multiplication. -/
theorem partialTranspose_smul (c : ℂ) (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTranspose (c • A) = c • PartialTranspose A := by
  ext p q
  simp [partialTranspose_apply]

/-- Partial transpose commutes with a finite sum. -/
theorem partialTranspose_sum {n : ℕ} (f : Fin n → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTranspose (∑ i, f i) = ∑ i, PartialTranspose (f i) := by
  ext p q
  simp only [partialTranspose_apply, Matrix.sum_apply]

/-- Applying partial transpose twice recovers the original operator. -/
theorem partialTranspose_partialTranspose (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTranspose (PartialTranspose A) = A := by
  ext p q
  obtain ⟨i₁, j₁⟩ := p
  obtain ⟨i₂, j₂⟩ := q
  simp only [partialTranspose_apply]

/-- Partial transpose of a tensor product transposes its second factor. -/
theorem partialTranspose_tensorGate (σ : Operator D) (τ : Operator E) :
    PartialTranspose (TensorGate σ τ) = TensorGate σ τ.transpose := by
  ext p q
  obtain ⟨i₁, j₁⟩ := p
  obtain ⟨i₂, j₂⟩ := q
  simp [partialTranspose_apply, tensorGate_apply, Matrix.transpose_apply]

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_sum {n : ℕ} {ι : Type*} [Fintype ι] (f : Fin n → Matrix ι ι ℂ)
    (h : ∀ i, (f i).PosSemidef) : (∑ i, f i).PosSemidef := by
  classical
  apply Finset.sum_induction (p := fun A : Matrix ι ι ℂ => A.PosSemidef)
  · intro a b ha hb
    exact ha.add hb
  · exact Matrix.PosSemidef.zero
  · intro i _
    exact h i

/-- The tensor product of two positive semidefinite operators is positive semidefinite. -/
theorem tensorGate_posSemidef {σ : Operator D} {τ : Operator E}
    (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) : (TensorGate σ τ).PosSemidef := by
  show (σ ⊗ₖ τ).PosSemidef
  exact hσ.kronecker hτ

/-- Scalars in both tensor factors combine into their product. -/
theorem tensorGate_smul_smul (c d : ℂ) (A : Operator D) (B : Operator E) :
    TensorGate (c • A) (d • B) = (c * d) • TensorGate A B := by
  show (c • A) ⊗ₖ (d • B) = _
  rw [smul_kronecker, kronecker_smul, smul_smul]
  rfl

/-- Multiplication by a nonnegative real scalar preserves positive semidefiniteness. -/
theorem posSemidef_smul_ofReal {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c)
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) : (((c : ℝ) : ℂ) • A).PosSemidef :=
  hA.smul (Complex.zero_le_real.mpr hc)

/-- Convex decompositions into normalized product projectors and into product density operators
define the same separability property. -/
theorem isSeparableState_iff_isSeparableMixed
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    IsSeparableState ρ ↔ IsSeparableMixed ρ := by
  constructor
  · rintro ⟨n, p, a, b, hp, hsum, ha, hb, he⟩
    refine ⟨n, p, fun i => outerProduct (a i), fun i => outerProduct (b i), hp, hsum, ?_, ?_, ?_⟩
    · intro i
      exact isDensityOperator_outerProduct (a i) (ha i)
    · intro i
      exact isDensityOperator_outerProduct (b i) (hb i)
    · rw [he]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [outerProduct_tensorState]
  · rintro ⟨n, p, σ, τ, hp, hsum, hσ, hτ, he⟩
    choose c u hc hcu hsu hdeu using fun i => exists_pure_decomposition (σ i) (hσ i)
    choose d v hd hdv hsv hdev using fun i => exists_pure_decomposition (τ i) (hτ i)
    have hts : ∀ i, TensorGate (σ i) (τ i)
        = ∑ k : Fin D, ∑ l : Fin E,
          (((c i k * d i l : ℝ) : ℂ)) • outerProduct (TensorState (u i k) (v i l)) := by
      intro i
      rw [hdeu i, hdev i]
      rw [← sum_tensorLeft (fun k => ((c i k : ℝ) : ℂ) • outerProduct (u i k))
          (∑ l, ((d i l : ℝ) : ℂ) • outerProduct (v i l))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← sum_tensorRight (((c i k : ℝ) : ℂ) • outerProduct (u i k))
          (fun l => ((d i l : ℝ) : ℂ) • outerProduct (v i l))]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [tensorGate_smul_smul, outerProduct_tensorState, ← Complex.ofReal_mul]
    have hkey : ρ = ∑ i : Fin n, ∑ k : Fin D, ∑ l : Fin E,
        (((p i * c i k * d i l : ℝ) : ℂ)) • outerProduct (TensorState (u i k) (v i l)) := by
      rw [he]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hts i]
      simp_rw [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [show ((p i : ℂ) * ((c i k * d i l : ℝ) : ℂ)) = (((p i * c i k * d i l : ℝ) : ℂ)) by
        push_cast; ring]

    have hre : (∑ x : Fin n × Fin D × Fin E,
          (((p x.1 * c x.1 x.2.1 * d x.1 x.2.2 : ℝ) : ℂ)) •
            outerProduct (TensorState (u x.1 x.2.1) (v x.1 x.2.2)))
        = ∑ i : Fin n, ∑ k : Fin D, ∑ l : Fin E,
          (((p i * c i k * d i l : ℝ) : ℂ)) • outerProduct (TensorState (u i k) (v i l)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
    have hsum3 : (∑ x : Fin n × Fin D × Fin E, p x.1 * c x.1 x.2.1 * d x.1 x.2.2) = 1 := by
      have haux : ∀ i : Fin n, (∑ y : Fin D × Fin E, p i * c i y.1 * d i y.2) = p i := by
        intro i
        rw [Fintype.sum_prod_type]
        have haux2 : ∀ k : Fin D, (∑ l : Fin E, p i * c i k * d i l) = p i * c i k := by
          intro k
          rw [show (∑ l : Fin E, p i * c i k * d i l) = ∑ l : Fin E, (p i * c i k) * d i l from
            Finset.sum_congr rfl fun l _ => by ring]
          rw [← Finset.mul_sum, hdv i, mul_one]
        simp_rw [haux2]
        rw [← Finset.mul_sum, hcu i, mul_one]
      rw [Fintype.sum_prod_type]
      simp_rw [haux]
      exact hsum
    set e := Fintype.equivFin (Fin n × Fin D × Fin E) with heq
    refine ⟨Fintype.card (Fin n × Fin D × Fin E),
      fun j => p (e.symm j).1 * c (e.symm j).1 (e.symm j).2.1 * d (e.symm j).1 (e.symm j).2.2,
      fun j => u (e.symm j).1 (e.symm j).2.1,
      fun j => v (e.symm j).1 (e.symm j).2.2, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      exact mul_nonneg (mul_nonneg (hp _) (hc _ _)) (hd _ _)
    · have hre2 : (∑ j : Fin (Fintype.card (Fin n × Fin D × Fin E)),
            (p (e.symm j).1 * c (e.symm j).1 (e.symm j).2.1 * d (e.symm j).1 (e.symm j).2.2))
          = ∑ x : Fin n × Fin D × Fin E, (p x.1 * c x.1 x.2.1 * d x.1 x.2.2) :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      rw [hre2]
      exact hsum3
    · intro j
      exact hsu _ _
    · intro j
      exact hsv _ _
    · rw [hkey]
      have hre3 : (∑ j : Fin (Fintype.card (Fin n × Fin D × Fin E)),
            (((p (e.symm j).1 * c (e.symm j).1 (e.symm j).2.1
                * d (e.symm j).1 (e.symm j).2.2 : ℝ) : ℂ)) •
              outerProduct (TensorState (u (e.symm j).1 (e.symm j).2.1)
                (v (e.symm j).1 (e.symm j).2.2)))
          = ∑ x : Fin n × Fin D × Fin E,
            (((p x.1 * c x.1 x.2.1 * d x.1 x.2.2 : ℝ) : ℂ)) •
              outerProduct (TensorState (u x.1 x.2.1) (v x.1 x.2.2)) :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      have hgoal : (∑ j : Fin (Fintype.card (Fin n × Fin D × Fin E)),
            (((p (e.symm j).1 * c (e.symm j).1 (e.symm j).2.1
                * d (e.symm j).1 (e.symm j).2.2 : ℝ) : ℂ)) •
              outerProduct (TensorState (u (e.symm j).1 (e.symm j).2.1)
                (v (e.symm j).1 (e.symm j).2.2)))
          = ∑ i : Fin n, ∑ k : Fin D, ∑ l : Fin E,
            (((p i * c i k * d i l : ℝ) : ℂ)) • outerProduct (TensorState (u i k) (v i l)) := by
        rw [hre3, hre]
      exact hgoal.symm

/-- The partial transpose of a separable state is positive semidefinite. -/
theorem partialTranspose_posSemidef_of_isSeparableState
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : IsSeparableState ρ) :
    (PartialTranspose ρ).PosSemidef := by
  obtain ⟨n, p, σ, τ, hp, _, hσ, hτ, he⟩ :=
    (isSeparableState_iff_isSeparableMixed ρ).mp hρ
  have hpt : ∀ i, PartialTranspose ((p i : ℂ) • TensorGate (σ i) (τ i))
      = ((p i : ℝ) : ℂ) • TensorGate (σ i) (τ i).transpose := by
    intro i
    rw [partialTranspose_smul, partialTranspose_tensorGate]
  rw [he, partialTranspose_sum]
  simp_rw [hpt]
  exact posSemidef_sum _ fun i =>
    posSemidef_smul_ofReal _ (hp i) _
      (tensorGate_posSemidef (hσ i).1 (hτ i).1.transpose)

/-- A scalar in the first argument of the inner product is conjugated when moved outside. -/
theorem inner_smul_left {I : Type*} [Fintype I] (φ ψ : QState I) (c : ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (c • φ) ψ = (starRingEnd ℂ) c * Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  classical
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply, mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

/-- The inner product preserves addition in its first argument. -/
theorem inner_add_left {I : Type*} [Fintype I] (φ χ ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (φ + χ) ψ = Qatlib.Foundations.PureStateMath.Inner φ ψ + Qatlib.Foundations.PureStateMath.Inner χ ψ := by
  classical
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, map_add, add_mul, starRingEnd_apply]
  exact Finset.sum_add_distrib

/-- The inner product preserves addition in its second argument. -/
theorem inner_add_right {I : Type*} [Fintype I] (φ ψ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner φ (ψ + χ) = Qatlib.Foundations.PureStateMath.Inner φ ψ + Qatlib.Foundations.PureStateMath.Inner φ χ := by
  classical
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, mul_add, starRingEnd_apply]
  exact Finset.sum_add_distrib

/-- The inner product preserves subtraction in its second argument. -/
theorem inner_sub_right {I : Type*} [Fintype I] (φ ψ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner φ (ψ - χ) = Qatlib.Foundations.PureStateMath.Inner φ ψ - Qatlib.Foundations.PureStateMath.Inner φ χ := by
  classical
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, mul_sub, starRingEnd_apply]
  exact Finset.sum_sub_distrib (s := (Finset.univ : Finset I)) _ _

/-- The inner product preserves subtraction in its first argument. -/
theorem inner_sub_left {I : Type*} [Fintype I] (φ χ ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (φ - χ) ψ = Qatlib.Foundations.PureStateMath.Inner φ ψ - Qatlib.Foundations.PureStateMath.Inner χ ψ := by
  classical
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, map_sub, sub_mul, starRingEnd_apply]
  exact Finset.sum_sub_distrib (s := (Finset.univ : Finset I)) _ _

/-- A normalized tensor product can be represented by two normalized factors with the same
tensor product. -/
theorem exists_normalized_tensor_factors {D E : ℕ} (a : QState (Fin D)) (b : QState (Fin E))
    (h : Normalized (TensorState a b)) :
    ∃ (a' : QState (Fin D)) (b' : QState (Fin E)),
      Normalized a' ∧ Normalized b' ∧ TensorState a' b' = TensorState a b := by
  classical
  set ra : ℝ := ∑ i, ‖a i‖ ^ 2 with hrade
  set rb : ℝ := ∑ j, ‖b j‖ ^ 2 with hrbe
  have h1 : (∑ q : Fin D × Fin E, ‖TensorState a b q‖ ^ 2)
      = (∑ i, ‖a i‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    have h2 : ∀ i : Fin D, (∑ j : Fin E, ‖TensorState a b (i, j)‖ ^ 2) = ‖a i‖ ^ 2 * (∑ j, ‖b j‖ ^ 2) := by
      intro i
      have h3 : ∀ j : Fin E, ‖TensorState a b (i, j)‖ ^ 2 = ‖a i‖ ^ 2 * ‖b j‖ ^ 2 := by
        intro j
        simp [TensorState, mul_pow]
      simp_rw [h3]
      rw [← Finset.mul_sum]
    simp_rw [h2]
    rw [← Finset.sum_mul]
  have hprod : ra * rb = 1 := by
    rw [hrade, hrbe, ← h1]
    exact h
  have hra : 0 < ra := by
    by_contra hn
    have hz : ra = 0 := le_antisymm (not_lt.mp hn)
      (Finset.sum_nonneg fun i _ => sq_nonneg ‖a i‖)
    rw [hz, zero_mul] at hprod
    exact zero_ne_one hprod
  have hrb : 0 < rb := by
    by_contra hn
    have hz : rb = 0 := le_antisymm (not_lt.mp hn)
      (Finset.sum_nonneg fun j _ => sq_nonneg ‖b j‖)
    rw [hz, mul_zero] at hprod
    exact zero_ne_one hprod
  refine ⟨(((Real.sqrt ra)⁻¹ : ℝ) : ℂ) • a, (((Real.sqrt rb)⁻¹ : ℝ) : ℂ) • b, ?_, ?_, ?_⟩
  · show ∑ i, ‖(((Real.sqrt ra)⁻¹ : ℝ) : ℂ) * a i‖ ^ 2 = 1
    have hs : ∀ i, ‖(((Real.sqrt ra)⁻¹ : ℝ) : ℂ) * a i‖ ^ 2
        = (((Real.sqrt ra)⁻¹ : ℝ) ^ 2) * ‖a i‖ ^ 2 := by
      intro i
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_eq_norm_sq]
      ring
    simp_rw [hs]
    rw [← Finset.mul_sum]
    have hsq : (Real.sqrt ra)⁻¹ ^ 2 = ra⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hra)]
    rw [hsq, hrade, inv_mul_cancel₀ hra.ne']
  · show ∑ j, ‖(((Real.sqrt rb)⁻¹ : ℝ) : ℂ) * b j‖ ^ 2 = 1
    have hs : ∀ j, ‖(((Real.sqrt rb)⁻¹ : ℝ) : ℂ) * b j‖ ^ 2
        = (((Real.sqrt rb)⁻¹ : ℝ) ^ 2) * ‖b j‖ ^ 2 := by
      intro j
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_eq_norm_sq]
      ring
    simp_rw [hs]
    rw [← Finset.mul_sum]
    have hsq : (Real.sqrt rb)⁻¹ ^ 2 = rb⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hrb)]
    rw [hsq, hrbe, inv_mul_cancel₀ hrb.ne']
  · funext q
    obtain ⟨i, j⟩ := q
    have hscal : ((((Real.sqrt ra)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt rb)⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, ← mul_inv, ← Real.sqrt_mul (le_of_lt hra) rb,
        hprod, Real.sqrt_one, inv_one, Complex.ofReal_one]
    show (((((Real.sqrt ra)⁻¹ : ℝ) : ℂ)) * a i) * (((((Real.sqrt rb)⁻¹ : ℝ) : ℂ)) * b j) = a i * b j
    rw [show (((((Real.sqrt ra)⁻¹ : ℝ) : ℂ)) * a i) * (((((Real.sqrt rb)⁻¹ : ℝ) : ℂ)) * b j)
        = (((((Real.sqrt ra)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt rb)⁻¹ : ℝ) : ℂ))) * (a i * b j) by ring,
      hscal, one_mul]

/-- Matrix-vector multiplication commutes with a finite sum of matrices. -/
theorem sum_mulVec {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (v : n → ℂ) : ((∑ i, A i) *ᵥ v) = ∑ i, A i *ᵥ v := by
  funext p
  rw [Finset.sum_apply]
  have hleft : ((∑ i, A i) *ᵥ v) p = ∑ q, (∑ i, A i) p q * v q := rfl
  have hright : (∑ c, (A c *ᵥ v) p) = ∑ i, ∑ q, A i p q * v q := rfl
  rw [hleft, hright]
  have hAP : ∀ q, (∑ i, A i) p q = ∑ i, A i p q := fun q =>
    Matrix.sum_apply p q Finset.univ A
  simp_rw [hAP, Finset.sum_mul]
  exact Finset.sum_comm

/-- The projector onto a normalized bipartite vector is separable exactly when the vector is a
product state. -/
theorem isSeparableState_outerProduct_iff_isProductState
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    IsSeparableState (outerProduct ψ) ↔ IsProductState ψ := by
  constructor
  · intro h
    obtain ⟨n, p, a, b, hp, hsum, ha, hb, he⟩ := h
    have hnormw : ∀ i, Normalized (TensorState (a i) (b i)) := fun i =>
      normalized_tensorState (ha i) (hb i)
    have hex : ∃ i : Fin n, p i ≠ 0 := by
      by_contra hn
      have hall : ∀ i : Fin n, p i = 0 := by
        intro i
        by_contra hi
        exact hn ⟨i, hi⟩
      have hz : (∑ i, p i) = 0 := Finset.sum_eq_zero (fun i _ => hall i)
      rw [hz] at hsum
      exact zero_ne_one hsum
    obtain ⟨i0, hi0⟩ := hex
    have hkey : ∀ (v : QState (Fin D × Fin E)) (i : Fin n),
        Qatlib.Foundations.PureStateMath.Inner ψ v = 0 → p i * ‖Qatlib.Foundations.PureStateMath.Inner (TensorState (a i) (b i)) v‖ ^ 2 = 0 := by
      intro v i hv
      have hzero : star v ⬝ᵥ (outerProduct ψ *ᵥ v) = 0 := by
        rw [outerProduct_mulVec, hv, zero_smul, dotProduct_zero]
      have hexp : star v ⬝ᵥ (outerProduct ψ *ᵥ v)
          = ((∑ k, p k * ‖Qatlib.Foundations.PureStateMath.Inner (TensorState (a k) (b k)) v‖ ^ 2 : ℝ) : ℂ) := by
        rw [he, sum_mulVec, dotProduct_sum, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hterm : star v ⬝ᵥ (((p k : ℂ) • outerProduct (TensorState (a k) (b k))) *ᵥ v)
            = ((p k * ‖Qatlib.Foundations.PureStateMath.Inner (TensorState (a k) (b k)) v‖ ^ 2 : ℝ) : ℂ) := by
          rw [smul_mulVec, outerProduct_mulVec, dotProduct_smul, dotProduct_smul]
          simp only [smul_eq_mul]
          show (p k : ℂ) * (Qatlib.Foundations.PureStateMath.Inner (TensorState (a k) (b k)) v
              * Qatlib.Foundations.PureStateMath.Inner v (TensorState (a k) (b k)))
            = ((p k * ‖Qatlib.Foundations.PureStateMath.Inner (TensorState (a k) (b k)) v‖ ^ 2 : ℝ) : ℂ)
          rw [← star_inner (TensorState (a k) (b k)) v, Complex.mul_conj,
            Complex.normSq_eq_norm_sq]
          push_cast
          ring
        exact hterm
      rw [hexp, Complex.ofReal_eq_zero] at hzero
      have hnn : ∀ k : Fin n, 0 ≤ p k * ‖Qatlib.Foundations.PureStateMath.Inner (TensorState (a k) (b k)) v‖ ^ 2 := fun k =>
        mul_nonneg (hp k) (sq_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hzero i (Finset.mem_univ i)
    have horth : ∀ v : QState (Fin D × Fin E), Qatlib.Foundations.PureStateMath.Inner ψ v = 0 →
        Qatlib.Foundations.PureStateMath.Inner (TensorState (a i0) (b i0)) v = 0 := by
      intro v hv
      have hzz :
          p i0 * ‖Qatlib.Foundations.PureStateMath.Inner
          (TensorState (a i0) (b i0)) v‖ ^ 2 = 0 := hkey v i0 hv
      have hp0 : p i0 ≠ 0 := hi0
      have hzz2 : ‖Qatlib.Foundations.PureStateMath.Inner (TensorState (a i0) (b i0)) v‖ ^ 2 = 0 := by
        rw [mul_comm] at hzz
        exact eq_zero_of_ne_zero_of_mul_right_eq_zero hp0 hzz
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzz2)
    set w : QState (Fin D × Fin E) := TensorState (a i0) (b i0) with hwd
    set c : ℂ := Qatlib.Foundations.PureStateMath.Inner ψ w with hcd
    have hpsi : Qatlib.Foundations.PureStateMath.Inner ψ ψ = 1 :=
        (normalized_iff_inner_self ψ).mp hψ
    have hww : Qatlib.Foundations.PureStateMath.Inner w w = 1 := (normalized_iff_inner_self w).mp (by
      rw [hwd]; exact hnormw i0)
    have hvz : ∀ v : QState (Fin D × Fin E), Qatlib.Foundations.PureStateMath.Inner ψ v = 0 → Qatlib.Foundations.PureStateMath.Inner w v = 0 := by
      intro v hv
      exact horth v hv
    have hpsiV : Qatlib.Foundations.PureStateMath.Inner ψ (w - c • ψ) = 0 := by
      rw [inner_sub_right, inner_smul_right, hcd, hpsi, mul_one, sub_self]
    have hinnerV : Qatlib.Foundations.PureStateMath.Inner (w - c • ψ) ψ = 0 := by
      rw [inner_sub_left, inner_smul_left, hcd, hpsi, mul_one, star_inner ψ w, sub_self]
    have hwwV : Qatlib.Foundations.PureStateMath.Inner w (w - c • ψ) = 0 :=
        hvz (w - c • ψ) hpsiV
    have hnormV : Qatlib.Foundations.PureStateMath.Inner (w - c • ψ) (w - c • ψ) = 0 := by
      rw [inner_sub_right, inner_smul_right, hinnerV, mul_zero, sub_zero]
      rw [inner_sub_left, inner_smul_left, hww, ← hcd]
      have hall : 1 - (starRingEnd ℂ) c * c = 0 := by
        rw [mul_comm]
        rw [inner_sub_right, inner_smul_right, hww, ← star_inner ψ w, ← hcd] at hwwV
        exact hwwV
      exact hall
    have hv : w - c • ψ = 0 := (inner_self_eq_zero_iff (w - c • ψ)).mp hnormV
    have hcne : c ≠ 0 := by
      intro hcz
      rw [hcz, zero_smul, sub_zero] at hv
      have hz : Qatlib.Foundations.PureStateMath.Inner (0 : QState (Fin D × Fin E)) (0 : QState (Fin D × Fin E)) = 0 :=
        dotProduct_zero _
      rw [hv] at hww
      rw [hz] at hww
      exact zero_ne_one hww
    refine ⟨c⁻¹ • a i0, b i0, ?_⟩
    have hwψ : w = c • ψ := sub_eq_zero.mp hv
    have hfinal : c⁻¹ • w = ψ := by
      rw [hwψ, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [← hfinal, hwd, schmidtU_smul_tensor]
  · rintro ⟨a, b, rfl⟩
    obtain ⟨a', b', ha', hb', he⟩ := exists_normalized_tensor_factors a b hψ
    refine ⟨1, fun _ => (1 : ℝ), fun _ => a', fun _ => b', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact zero_le_one
    · simp
    · intro i
      exact ha'
    · intro i
      exact hb'
    · rw [← he]
      simp

/-- The tensor product distributes over addition in its first argument. -/
theorem tensorGate_add_left (A A' : Operator D) (B : Operator E) :
    TensorGate (A + A') B = TensorGate A B + TensorGate A' B := by
  show (A + A') ⊗ₖ B = _
  rw [add_kronecker]
  rfl

/-- Summing a list of first-subsystem Kraus conjugations preserves nonnegative combinations of
product density operators. -/
theorem isSeparableSub_listSum_kraus (ks : List (Operator D))
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (h : IsSeparableSub ρ) :
    IsSeparableSub ((ks.map fun K => TensorGate K (1 : Operator E) * ρ *
      (TensorGate K (1 : Operator E)).conjTranspose).sum) := by
  induction ks with
  | nil => simpa using isSeparableSub_zero
  | cons K ks ih =>
    rw [List.map_cons, List.sum_cons]
    exact isSeparableSub_add (isSeparableSub_tensorLeft_kraus K h) ih

/-- The trace of a list sum of first-subsystem Kraus branches equals the trace against the sum
of their effect operators. -/
theorem trace_tensorLeft_listSum (ks : List (Operator D))
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix.trace ((ks.map fun K => TensorGate K (1 : Operator E) * ρ *
      (TensorGate K (1 : Operator E)).conjTranspose).sum)
    = Matrix.trace (TensorGate ((ks.map fun K => K.conjTranspose * K).sum) (1 : Operator E) * ρ) := by
  induction ks with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have hz : (TensorGate (0 : Operator D) (1 : Operator E)) = 0 := by
      show (0 : Operator D) ⊗ₖ (1 : Operator E) = 0
      simp
    rw [hz, zero_mul, Matrix.trace_zero]
  | cons K ks ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Matrix.trace_add]
    rw [trace_tensorLeft_sandwich, ih]
    rw [← Matrix.trace_add, ← Matrix.add_mul]
    rw [← tensorGate_add_left]

/-- A complete list of first-subsystem Kraus operators preserves trace after summing its
branches. -/
theorem trace_listSum_kraus (ks : List (Operator D)) (hks : IsKrausList ks)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix.trace ((ks.map fun K => TensorGate K (1 : Operator E) * ρ *
      (TensorGate K (1 : Operator E)).conjTranspose).sum) = Matrix.trace ρ := by
  have hks' : (ks.map fun K => K.conjTranspose * K).sum = 1 := hks
  rw [trace_tensorLeft_listSum, hks', tensorGate_one, one_mul]

/-- Applying a complete list of first-subsystem Kraus operators preserves separable states. -/
theorem isSeparableState_applyFirstKraus (ks : List (Operator D)) (hks : IsKrausList ks)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : IsSeparableState ρ) :
    IsSeparableState (ApplyFirstKraus ks ρ) := by
  have hmixed : IsSeparableMixed ρ := (isSeparableState_iff_isSeparableMixed ρ).mp hρ
  have hsub : IsSeparableSub ρ := isSeparableSub_of_isSeparableMixed hmixed
  have hsub' : IsSeparableSub (ApplyFirstKraus ks ρ) := by
    show IsSeparableSub ((ks.map fun K => TensorGate K (1 : Operator E) * ρ *
      (TensorGate K (1 : Operator E)).conjTranspose).sum)
    exact isSeparableSub_listSum_kraus ks ρ hsub
  have htr : Matrix.trace (ApplyFirstKraus ks ρ) = 1 := by
    show Matrix.trace ((ks.map fun K => TensorGate K (1 : Operator E) * ρ *
      (TensorGate K (1 : Operator E)).conjTranspose).sum) = 1
    rw [trace_listSum_kraus ks hks ρ, trace_of_isSeparableMixed hmixed]
  exact (isSeparableState_iff_isSeparableMixed (ApplyFirstKraus ks ρ)).mpr
    (isSeparableMixed_of_isSeparableSub hsub' htr)

/-- The entries of the singlet projector's partial transpose are products of singlet amplitudes
with the second indices exchanged. -/
theorem singlet_partialTranspose_apply (p q : Fin 2 × Fin 2) :
    PartialTranspose (outerProduct (bell (true, true))) p q
      = (bell (true, true)) (p.1, q.2) * (starRingEnd ℂ) ((bell (true, true)) (q.1, p.2)) := by
  rw [partialTranspose_apply, outerProduct_apply]

/-- The singlet has amplitudes `1 / √2` at `(0, 1)`, `-1 / √2` at `(1, 0)`, and zero elsewhere. -/
theorem bell_singlet_amplitude (x y : Fin 2) :
    (bell (true, true)) (x, y)
      = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) *
          (if (x, y) = ((0 : Fin 2), (1 : Fin 2)) then (1 : ℂ)
           else if (x, y) = ((1 : Fin 2), (0 : Fin 2)) then -1 else 0) := by
  fin_cases x <;> fin_cases y <;> simp [bell, ket_apply]

/-- On the basis indices `(0, 0)` and `(1, 1)`, the singlet's partial transpose has zero
diagonal entries and off-diagonal entries `-1 / 2`. -/
theorem singlet_partialTranspose_corners :
    PartialTranspose (outerProduct (bell (true, true))) (0, 0) (0, 0) = (0 : ℂ) ∧
    PartialTranspose (outerProduct (bell (true, true))) (0, 0) (1, 1) = (-1 / 2 : ℂ) ∧
    PartialTranspose (outerProduct (bell (true, true))) (1, 1) (0, 0) = (-1 / 2 : ℂ) ∧
    PartialTranspose (outerProduct (bell (true, true))) (1, 1) (1, 1) = (0 : ℂ) := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hinv : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv, h2]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [singlet_partialTranspose_apply, bell_singlet_amplitude, hinv]

/-- The sesquilinear pairing of basis vectors through a matrix extracts its corresponding entry. -/
theorem star_ket_dotProduct_mulVec_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i j : ι) : star (Qatlib.Foundations.PureStateMath.Ket i) ⬝ᵥ (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) = M i j := by
  have hv : ∀ p, (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) p = M p j := by
    intro p
    show (∑ q, M p q * Qatlib.Foundations.PureStateMath.Ket j q) = M p j
    rw [Finset.sum_eq_single j]
    · rw [ket_self, mul_one]
    · intro b _ hb
      rw [ket_ne hb, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  show ∑ p, (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Ket i p) *
      (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) p = M i j
  simp_rw [hv]
  rw [Finset.sum_eq_single i]
  · rw [ket_self]
    simp
  · intro b _ hb
    rw [ket_ne hb]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The quadratic form of the singlet's partial transpose on the sum of the `(0, 0)` and `(1,
1)` basis vectors equals `-1`. -/
theorem singlet_partialTranspose_form :
    star (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2 × Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1, 1)) ⬝ᵥ
        (PartialTranspose (outerProduct (bell (true, true))) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2 × Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1, 1)))
      = (-1 : ℂ) := by
  have hM := singlet_partialTranspose_corners
  simp only [mulVec_add, star_add, add_dotProduct, dotProduct_add,
    star_ket_dotProduct_mulVec_ket]
  simp only [show (0 : Fin 2 × Fin 2) = ((0 : Fin 2), (0 : Fin 2)) from rfl]
  rw [hM.1, hM.2.1, hM.2.2.1, hM.2.2.2]
  ring

/-- The singlet projector has a partial transpose that is not positive semidefinite. -/
theorem bell_singlet_partialTranspose_not_posSemidef :
    ¬ (PartialTranspose (outerProduct (bell (true, true)))).PosSemidef := by
  intro h
  have hnn := h.dotProduct_mulVec_nonneg
    (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2 × Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1, 1))
  rw [singlet_partialTranspose_form] at hnn
  have hreal : (0 : ℝ) ≤ -1 := (Complex.nonneg_iff.mp hnn).1
  linarith

/-- The singlet projector is not separable. -/
theorem bell_singlet_not_isSeparableState :
    ¬ IsSeparableState (outerProduct (bell (true, true))) := by
  intro h
  exact bell_singlet_partialTranspose_not_posSemidef
    (partialTranspose_posSemidef_of_isSeparableState _ h)

end Qatlib.Concepts.FiniteLocc.LOCCProgram
