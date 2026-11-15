/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbFormsAux
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Lemma33AlgorithmToTensorQuan
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.FactorizationBoundsTensorCbNormQuan
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Theorem13AlgorithmToFormStat

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

/-- The complex norm of a coerced real number equals its absolute value. -/
private theorem cbNorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  rw [show ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm, h1, Real.sqrt_sq (abs_nonneg r)]

section Aux

variable {κ : Type} [Fintype κ] {s : ℕ}

/-- The permutation group on `Fin s` has cardinality `Nat.factorial s`. -/
private theorem card_perm_fin (s : ℕ) : Fintype.card (Equiv.Perm (Fin s)) = Nat.factorial s := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- The sum of a constant over permutations of `Fin s` equals the constant times `Nat.factorial
s`. -/
private theorem sum_perm_const_real (s : ℕ) (c : ℝ) :
    ∑ _ : Equiv.Perm (Fin s), c = (Nat.factorial s : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_perm_fin]
  simp

/-- Right composition with a fixed permutation is bijective on the permutation group. -/
private theorem perm_trans_right_bijective (π : Equiv.Perm (Fin s)) :
    Function.Bijective fun σ : Equiv.Perm (Fin s) => σ.trans π := by
  constructor
  · intro a b hab
    simp only [] at hab
    have h : (a.trans π).trans π.symm = (b.trans π).trans π.symm := by rw [hab]
    rwa [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl,
      Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
  · intro τ
    refine ⟨τ.trans π.symm, ?_⟩
    show (τ.trans π.symm).trans π = τ
    rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]

/-- Precomposition with a permutation is bijective on index functions. -/
private theorem comp_perm_bijective (σ : Equiv.Perm (Fin s)) :
    Function.Bijective fun i : Fin s → κ => i ∘ σ := by
  constructor
  · intro a b hab
    simp only [] at hab
    have h : (a ∘ σ) ∘ σ.symm = (b ∘ σ) ∘ σ.symm := by rw [hab]
    have hc : ∀ f : Fin s → κ, (f ∘ σ) ∘ σ.symm = f := by
      intro f
      ext x
      simp
    rwa [hc a, hc b] at h
  · intro i
    refine ⟨i ∘ σ.symm, ?_⟩
    show (i ∘ σ.symm) ∘ σ = i
    ext x
    simp

/-- Averaging a tensor over all permutations produces a symmetric tensor. -/
private theorem isSymmTensor_symm (T : RealTensor κ s) :
    IsSymmTensor (fun i => (Nat.factorial s : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin s), permTensor T σ i) := by
  intro π
  funext i
  show (Nat.factorial s : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin s), T ((i ∘ π) ∘ σ)
      = (Nat.factorial s : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin s), T (i ∘ τ)
  rw [Fintype.sum_bijective (fun σ : Equiv.Perm (Fin s) => σ.trans π) (perm_trans_right_bijective π)
    (fun σ => T ((i ∘ π) ∘ σ)) (fun τ => T (i ∘ τ)) (fun _ => rfl)]

/-- Permuting tensor slots preserves the associated form value on a repeated input. -/
private theorem formValue_permTensor (T : RealTensor κ s) (σ : Equiv.Perm (Fin s)) (y : κ → ℝ) :
    formValue (permTensor T σ) y = formValue T y := by
  show ∑ i : Fin s → κ, T (i ∘ σ) * ∏ j, y (i j) = ∑ i : Fin s → κ, T i * ∏ j, y (i j)
  rw [Fintype.sum_bijective (fun i => i ∘ σ) (comp_perm_bijective σ)
    (fun i => T (i ∘ σ) * ∏ j, y (i j))
    (fun u => T u * ∏ j, y (u (σ.symm j)))
    (fun i => by
      refine congrArg (fun P => T (i ∘ σ) * P) (Finset.prod_congr rfl fun j _ => ?_)
      simp)]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg (fun P => T u * P) (Equiv.prod_comp σ.symm fun j => y (u j))

/-- Symmetrizing a tensor by averaging over permutations preserves its form value. -/
private theorem formValue_symm (T : RealTensor κ s) (y : κ → ℝ) :
    formValue (fun i => (Nat.factorial s : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin s), permTensor T σ i) y
      = formValue T y := by
  show ∑ i : Fin s → κ,
      ((Nat.factorial s : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin s), T (i ∘ σ)) * ∏ j, y (i j)
      = formValue T y
  have step1 : ∀ i : Fin s → κ,
      ((Nat.factorial s : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin s), T (i ∘ σ)) * ∏ j, y (i j)
        = (Nat.factorial s : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin s), T (i ∘ σ) * ∏ j, y (i j) := by
    intro i
    rw [mul_assoc, Finset.sum_mul]
  have step2 : ∀ σ : Equiv.Perm (Fin s),
      (∑ i : Fin s → κ, T (i ∘ σ) * ∏ j, y (i j)) = formValue T y :=
    fun σ => formValue_permTensor T σ y
  rw [Finset.sum_congr rfl fun i _ => step1 i, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun σ _ => step2 σ, sum_perm_const_real,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_pos s).ne'), one_mul]

/-- Evaluating a real tensor on repeated real inputs coerced to the complex numbers gives the
coerced real form value. -/
private theorem tensorEval_ofReal (T : RealTensor κ s) (y : κ → ℝ) :
    tensorEval T (fun _ k => (y k : ℂ)) = ((formValue T y : ℝ) : ℂ) := by
  rw [tensorEval, formValue, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.ofReal_mul, Complex.ofReal_prod]

/-- The real Boolean sign vector coerces entrywise to `signVecC`. -/
private theorem signVecC_eq_ofReal {n : ℕ} (x : Fin n → Bool) (k : Fin n ⊕ Fin n) :
    ((signVecR x k : ℝ) : ℂ) = signVecC x k := by
  cases k with
  | inl i => cases hx : x i <;> simp [signVecR, signVecC, hx]
  | inr i => simp [signVecR, signVecC]

/-- Every tensor completely bounded norm is nonnegative. -/
private theorem tensorCbNorm_nonneg (T : RealTensor κ s) : 0 ≤ tensorCbNorm T := by
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨d, A, hA, rfl⟩ := hr
  exact norm_nonneg _

/-- The matrix-evaluation norms defining `tensorCbNorm` form a set bounded above. -/
private theorem tensorCbNorm_bddAbove (T : RealTensor κ s) :
    BddAbove {r : ℝ | ∃ (d : ℕ) (A : Fin s → κ → Matrix (Fin d) (Fin d) ℂ),
      (∀ j i, ‖A j i‖ ≤ 1) ∧
        r = ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖} := by
  refine ⟨∑ i : Fin s → κ, |T i|, ?_⟩
  rintro r ⟨d, A, hA, rfl⟩
  calc ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖
      ≤ ∑ i : Fin s → κ, ‖(T i : ℂ) • matProdFin s (fun j => A j (i j))‖ :=
        norm_sum_le Finset.univ _
    _ ≤ ∑ i : Fin s → κ, |T i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ‖(T i : ℂ) • matProdFin s (fun j => A j (i j))‖
            = ‖(T i : ℂ)‖ * ‖matProdFin s (fun j => A j (i j))‖ := norm_smul _ _
          _ ≤ ‖(T i : ℂ)‖ * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              refine le_trans (l2_opNorm_matProdFin_le (fun j => A j (i j))) ?_
              calc (∏ j, ‖A j (i j)‖) ≤ ∏ j : Fin s, (1 : ℝ) :=
                    Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => hA j (i j)
                _ = 1 := by simp
          _ = |T i| := by rw [mul_one, cbNorm_ofReal]

/-- Scaling a tensor by a real scalar increases its completely bounded norm by at most the
scalar's absolute value factor. -/
private theorem tensorCbNorm_constMul_le (c : ℝ) (T : RealTensor κ s) :
    tensorCbNorm (fun i => c * T i) ≤ |c| * tensorCbNorm T := by
  have hbdd := tensorCbNorm_bddAbove T
  refine csSup_le ?_ fun r hr => ?_
  · exact ⟨_, 1, fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ),
      fun _ _ => norm_zero.trans_le zero_le_one, rfl⟩
  · obtain ⟨d, A, hA, rfl⟩ := hr
    show ‖∑ i : Fin s → κ, ((c * T i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j))‖
        ≤ |c| * tensorCbNorm T
    have hsmul : ∑ i : Fin s → κ, ((c * T i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j))
        = ((c : ℝ) : ℂ) • ∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j)) := by
      have hterm : ∀ i : Fin s → κ,
          ((c * T i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j))
            = ((c : ℝ) : ℂ) • ((T i : ℂ) • matProdFin s (fun j => A j (i j))) := by
        intro i
        rw [Complex.ofReal_mul, smul_smul]
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.smul_sum]
    rw [hsmul, norm_smul, cbNorm_ofReal]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    exact le_csSup hbdd ⟨d, A, hA, rfl⟩

end Aux

/-- For positive input size, a sign algorithm with `t` queries yields a symmetric real tensor of
order twice `t` with form completely bounded norm at most one and the same bias. -/
theorem theorem1_3AlgorithmToForm : Theorem1_3AlgorithmToForm := by
  intro n hn t β h
  obtain ⟨T, hTfac, hTβ⟩ := lemma3_3AlgorithmToTensor n hn t β h
  have hTle : tensorCbNorm T ≤ 1 := factorizationBoundsTensorCbNorm _ _ _ hTfac
  refine ⟨fun i => (Nat.factorial (2 * t) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (2 * t)), permTensor T σ i,
    isSymmTensor_symm T, ?_, ?_⟩
  · set S : RealTensor (Fin n ⊕ Fin n) (2 * t) :=
      fun i => (Nat.factorial (2 * t) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (2 * t)), permTensor T σ i
      with hS
    have hdec : ∀ i : Fin (2 * t) → (Fin n ⊕ Fin n),
        S i = ∑ σ : Equiv.Perm (Fin (2 * t)), (Nat.factorial (2 * t) : ℝ)⁻¹ * T (i ∘ σ) := by
      intro i
      simp only [hS]
      rw [Finset.mul_sum]
      simp only [permTensor]
    have hbdd : BddBelow {c : ℝ |
        ∃ D : Equiv.Perm (Fin (2 * t)) → RealTensor (Fin n ⊕ Fin n) (2 * t),
          (∀ i : Fin (2 * t) → (Fin n ⊕ Fin n), S i = ∑ σ : Equiv.Perm (Fin (2 * t)), D σ (i ∘ σ)) ∧
            c = ∑ σ : Equiv.Perm (Fin (2 * t)), tensorCbNorm (D σ)} := by
      refine ⟨0, ?_⟩
      rintro c ⟨D, -, rfl⟩
      exact Finset.sum_nonneg fun σ _ => tensorCbNorm_nonneg _
    have hle2 : (∑ σ : Equiv.Perm (Fin (2 * t)),
          tensorCbNorm ((fun _ i => (Nat.factorial (2 * t) : ℝ)⁻¹ * T i) σ)) ≤ 1 := by
      have hterm : ∀ σ : Equiv.Perm (Fin (2 * t)),
          tensorCbNorm ((fun _ i => (Nat.factorial (2 * t) : ℝ)⁻¹ * T i) σ)
            ≤ (Nat.factorial (2 * t) : ℝ)⁻¹ * tensorCbNorm T := by
        intro σ
        have h := tensorCbNorm_constMul_le ((Nat.factorial (2 * t) : ℝ)⁻¹) T
        have hF : (0 : ℝ) < (Nat.factorial (2 * t)) := by exact_mod_cast Nat.factorial_pos _
        rwa [abs_of_nonneg (inv_pos.mpr hF).le] at h
      calc ∑ σ : Equiv.Perm (Fin (2 * t)),
            tensorCbNorm ((fun _ i => (Nat.factorial (2 * t) : ℝ)⁻¹ * T i) σ)
          ≤ ∑ σ : Equiv.Perm (Fin (2 * t)), (Nat.factorial (2 * t) : ℝ)⁻¹ * tensorCbNorm T :=
              Finset.sum_le_sum fun σ _ => hterm σ
        _ ≤ ∑ σ : Equiv.Perm (Fin (2 * t)), (Nat.factorial (2 * t) : ℝ)⁻¹ * 1 :=
              Finset.sum_le_sum fun σ _ =>
                mul_le_mul_of_nonneg_left hTle (by positivity)
        _ = 1 := by
              rw [Finset.sum_congr rfl fun σ _ => mul_one _, sum_perm_const_real,
                mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne')]
    exact le_trans
      (csInf_le hbdd ⟨fun _ i => (Nat.factorial (2 * t) : ℝ)⁻¹ * T i, hdec, rfl⟩) hle2
  · intro x
    have h1 : formBias (fun i => (Nat.factorial (2 * t) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (2 * t)), permTensor T σ i) x = formValue T (signVecR x) :=
      formValue_symm T (signVecR x)
    have hpt : (fun _ : Fin (2 * t) => fun k => ((signVecR x k : ℝ) : ℂ))
        = fun _ => signVecC x := by
      funext _ k
      exact signVecC_eq_ofReal x k
    have h2 : ((formValue T (signVecR x) : ℝ) : ℂ) = (β x : ℂ) := by
      rw [← tensorEval_ofReal T (signVecR x), hpt]
      exact hTβ x
    rw [h1]
    exact Complex.ofReal_inj.mp h2

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
