/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.LinearAlgebra.Matrix.PosDef
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermLinOpt04.MainResults.Model

abbrev Fock (n : ℕ) := Matrix (Reg n) (Reg n) ℂ

noncomputable def gen {n : ℕ} (a : Fin (2 * n)) : Fock n := majorana a

noncomputable def tensorSquare {n : ℕ} (X : Fock n) :
    Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ := fun y x => X y.1 x.1 * X y.2 x.2

noncomputable def Lambda (n : ℕ) : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
  ∑ a : Fin (2 * n), tensorSquare (gen a)

noncomputable def IsEvenOp {n : ℕ} (X : Fock n) : Prop :=
  (parityOp : Fock n) * X * parityOp = X

noncomputable def IsOddOp {n : ℕ} (X : Fock n) : Prop :=
  (parityOp : Fock n) * X * parityOp = -X

noncomputable def IsParityPreserving {n : ℕ} (E : Fock n →ₗ[ℂ] Fock n) : Prop :=
  (∀ X, IsEvenOp X → IsEvenOp (E X)) ∧ (∀ X, IsOddOp X → IsOddOp (E X))

noncomputable def IsRealOrthogonal {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  Rᵀ * R = 1 ∧ R * Rᵀ = 1

noncomputable def IsCanonicalWith {n : ℕ} (V : Fock n)
    (R : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Prop :=
  V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ∀ a : Fin (2 * n), V * gen a * Vᴴ = ∑ b, (R a b : ℂ) • gen b

noncomputable def IsPositiveOperator {n : ℕ} (X : Fock n) : Prop := X.PosSemidef

noncomputable def IsPureState {n : ℕ} (X : Fock n) : Prop := X * X = X

noncomputable def IsInCorrelationBall {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ((1 : Matrix (Fin m) (Fin m) ℂ) - Mᴴ * M).PosSemidef

noncomputable def pfaffianList {ι : Type*} [DecidableEq ι] (M : ι → ι → ℂ) :
    List ι → ℂ
  | [] => 1
  | [_] => 0
  | a :: rest =>
      ∑ j : Fin rest.length,
        (-1 : ℂ) ^ (j : ℕ) * M a (rest.get j) * pfaffianList M (rest.eraseIdx j)
termination_by l => l.length
decreasing_by
  simp_wf
  have := List.length_eraseIdx_add_one (l := rest) (i := (j : ℕ)) j.isLt
  omega

noncomputable def pfaffianSub {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (S : Finset (Fin (2 * n))) : ℂ :=
  pfaffianList (fun a b => M a b) (S.sort (· ≤ ·))

noncomputable def monomial {n : ℕ} (S : Finset (Fin (2 * n))) : Fock n :=
  ((S.sort (· ≤ ·)).map (fun a => gen a)).prod

noncomputable def gaussianOp {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (C : ℂ) : Fock n :=
  C • ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => Even S.card)),
        (Complex.I ^ (S.card / 2) * pfaffianSub M S) • monomial S

noncomputable def IsGaussianOperator {n : ℕ} (X : Fock n) : Prop :=
  (∃ (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ), X = gaussianOp M C) ∨
    ∃ Xm : ℕ → Fock n,
      (∀ m, ∃ (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ), Xm m = gaussianOp M C) ∧
        Filter.Tendsto Xm Filter.atTop (nhds X)

noncomputable def IsGaussianState {n : ℕ} (ρ : Fock n)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop :=
  (∀ a b, M a b = -(M b a)) ∧ (∀ a b, (M a b).im = 0) ∧
    ρ = gaussianOp M (((2 : ℂ) ^ n)⁻¹)

noncomputable def correlation {n : ℕ} (X : Fock n) (a b : Fin (2 * n)) : ℂ :=
  (Complex.I / 2) * Matrix.trace (X * (gen a * gen b - gen b * gen a))

noncomputable def IsCorrelationMatrixOf {n : ℕ} (X : Fock n)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop := ∀ a b, M a b = correlation X a b

noncomputable def evenIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨2 * (j : ℕ), by omega⟩

noncomputable def oddIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨2 * (j : ℕ) + 1, by omega⟩

noncomputable def productState {n : ℕ} (lam : Fin n → ℝ) : Fock n :=
  (((2 : ℂ) ^ n)⁻¹) •
    ((List.finRange n).map (fun j =>
      (1 : Fock n) + (Complex.I * (lam j : ℂ)) •
        (gen (evenIdx j) * gen (oddIdx j)))).prod

noncomputable def linearForm {n : ℕ} (T : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (a : Fin (2 * n)) : Fock n := ∑ b : Fin (2 * n), T a b • gen b

noncomputable def wedgeList {n : ℕ} (l : List (Fock n)) : Fock n :=
  ((Nat.factorial l.length : ℂ))⁻¹ •
    ∑ σ : Equiv.Perm (Fin l.length),
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
        (List.ofFn (fun a : Fin l.length => l.get (σ a))).prod

noncomputable def gaussianFormOp {n : ℕ} (k : ℕ) (hk : 2 * k ≤ 2 * n)
    (T : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Fock n :=
  C • (wedgeList (List.ofFn (fun a : Fin (2 * k) => linearForm T (Fin.castLE hk a)))) *
    (∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin (2 * n)) =>
        (∀ a ∈ S, 2 * k ≤ (a : ℕ)) ∧ Even S.card)),
      (Complex.I ^ (S.card / 2) * pfaffianSub M S) •
        wedgeList ((S.sort (· ≤ ·)).map (fun a => linearForm T a)))

noncomputable def K (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun a b =>
    if (a : ℕ) = 0 ∧ (b : ℕ) = 1 then 1
    else if (a : ℕ) = 1 ∧ (b : ℕ) = 0 then -1 else 0

@[simp] theorem pfaffianList_nil {ι : Type*} [DecidableEq ι] (M : ι → ι → ℂ) :
    pfaffianList M [] = 1 := by simp [pfaffianList]

@[simp] theorem pfaffianSub_empty {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    pfaffianSub M ∅ = 1 := by
  simp [pfaffianSub]

@[simp] theorem monomial_empty {n : ℕ} : monomial (∅ : Finset (Fin (2 * n))) = 1 := by
  simp [monomial]

theorem gaussianOp_smul {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (a C : ℂ) :
    gaussianOp M (a * C) = a • gaussianOp M C := by
  simp only [gaussianOp, smul_smul]

theorem pfaffianList_zero_of_ne_nil {ι : Type*} [DecidableEq ι] {l : List ι}
    (h : l ≠ []) : pfaffianList (fun _ _ => (0 : ℂ)) l = 0 := by
  match l with
  | [] => exact absurd rfl h
  | [_] => simp only [pfaffianList]
  | a :: b :: t =>
      simp only [pfaffianList]
      apply Finset.sum_eq_zero
      intro j _
      simp

theorem pfaffianSub_zero_of_ne_empty {n : ℕ} {S : Finset (Fin (2 * n))} (h : S ≠ ∅) :
    pfaffianSub (0 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) S = 0 := by
  unfold pfaffianSub
  apply pfaffianList_zero_of_ne_nil
  intro hn
  apply h
  have hlen : S.card = 0 := by
    have := Finset.length_sort (s := S) (· ≤ ·)
    rw [← this, hn]
    rfl
  exact Finset.card_eq_zero.mp hlen

theorem gaussianOp_zero {n : ℕ} (C : ℂ) :
    gaussianOp (0 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) C = C • (1 : Fock n) := by
  unfold gaussianOp
  rw [Finset.sum_eq_single (∅ : Finset (Fin (2 * n)))]
  · simp
  · intro S hS hne
    have hSz : pfaffianSub (0 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) S = 0 :=
      pfaffianSub_zero_of_ne_empty hne
    simp [hSz]
  · intro hmem
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩) hmem

theorem isGaussianOperator_of_eq {n : ℕ} {X : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} {C : ℂ} (h : X = gaussianOp M C) :
    IsGaussianOperator X := Or.inl ⟨M, C, h⟩

end Qatlib.Papers.FermLinOpt04.MainResults.Model
