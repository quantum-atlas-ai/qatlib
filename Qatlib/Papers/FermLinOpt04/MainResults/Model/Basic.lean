/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Fock-space Gaussian operator definitions

This module builds the matrix model `Fock` from Majorana generators, defines parity and
correlation predicates, and constructs Gaussian operators through Pfaffian-weighted even
monomials. `IsGaussianOperator` also includes sequential limits of these expansions, while
`IsGaussianState` specifies a normalized expansion with a real antisymmetric parameter matrix.

The auxiliary constructions include ordered product operators, antisymmetrized products, and the
general expression `gaussianFormOp`. These results formalize the indicated identities from
[Bravyi2005Fermionic].

## Main statements

* `gaussianOp`: defines the Pfaffian expansion.
* `IsGaussianOperator`: includes expansions and their sequential limits.
* `gaussianOp_zero`: evaluates the expansion with zero matrix parameter.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermLinOpt04.MainResults.Model

/-- The algebra of complex matrices on the `n`-mode occupation-basis register. -/
abbrev Fock (n : ℕ) := Matrix (Reg n) (Reg n) ℂ

/-- The Majorana generator with index `a` in the Fock-space matrix model. -/
noncomputable def gen {n : ℕ} (a : Fin (2 * n)) : Fock n := majorana a

/-- The tensor square of `X`, with entries given by products of the corresponding entries of
`X`. -/
noncomputable def tensorSquare {n : ℕ} (X : Fock n) :
    Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ := fun y x => X y.1 x.1 * X y.2 x.2

/-- The sum of the tensor squares of all `2 * n` Majorana generators. -/
noncomputable def Lambda (n : ℕ) : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
  ∑ a : Fin (2 * n), tensorSquare (gen a)

/-- The condition that conjugation by `parityOp` fixes `X`. -/
noncomputable def IsEvenOp {n : ℕ} (X : Fock n) : Prop :=
  (parityOp : Fock n) * X * parityOp = X

/-- The condition that conjugation by `parityOp` sends `X` to `-X`. -/
noncomputable def IsOddOp {n : ℕ} (X : Fock n) : Prop :=
  (parityOp : Fock n) * X * parityOp = -X

/-- The condition that a linear map sends even operators to even operators and odd operators to
odd operators. -/
noncomputable def IsParityPreserving {n : ℕ} (E : Fock n →ₗ[ℂ] Fock n) : Prop :=
  (∀ X, IsEvenOp X → IsEvenOp (E X)) ∧ (∀ X, IsOddOp X → IsOddOp (E X))

/-- The condition that a real matrix has its transpose as a two-sided inverse. -/
noncomputable def IsRealOrthogonal {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  Rᵀ * R = 1 ∧ R * Rᵀ = 1

/-- The condition that `V` is unitary and conjugates each Majorana generator to the real linear
combination specified by the corresponding row of `R`. -/
noncomputable def IsCanonicalWith {n : ℕ} (V : Fock n)
    (R : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Prop :=
  V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ∀ a : Fin (2 * n), V * gen a * Vᴴ = ∑ b, (R a b : ℂ) • gen b

/-- The condition that the Fock-space matrix `X` is positive semidefinite. -/
noncomputable def IsPositiveOperator {n : ℕ} (X : Fock n) : Prop := X.PosSemidef

/-- The idempotence condition `X * X = X`. -/
noncomputable def IsPureState {n : ℕ} (X : Fock n) : Prop := X * X = X

/-- The condition that `1 - Mᴴ * M` is positive semidefinite. -/
noncomputable def IsInCorrelationBall {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ((1 : Matrix (Fin m) (Fin m) ℂ) - Mᴴ * M).PosSemidef

/-- The recursive Pfaffian expression on an ordered list, expanded by pairing its first entry
with each later entry. -/
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

/-- The Pfaffian expression for the submatrix indexed by `S`, with indices taken in increasing
order. -/
noncomputable def pfaffianSub {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (S : Finset (Fin (2 * n))) : ℂ :=
  pfaffianList (fun a b => M a b) (S.sort (· ≤ ·))

/-- The ordered product of the Majorana generators indexed by `S`, in increasing order. -/
noncomputable def monomial {n : ℕ} (S : Finset (Fin (2 * n))) : Fock n :=
  ((S.sort (· ≤ ·)).map (fun a => gen a)).prod

/-- The scalar `C` times the sum of even Majorana monomials weighted by `I^(S.card / 2) *
pfaffianSub M S`. -/
noncomputable def gaussianOp {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (C : ℂ) : Fock n :=
  C • ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => Even S.card)),
        (Complex.I ^ (S.card / 2) * pfaffianSub M S) • monomial S

/-- The condition that `X` is a Gaussian Pfaffian expansion or a sequential limit of such
expansions. -/
noncomputable def IsGaussianOperator {n : ℕ} (X : Fock n) : Prop :=
  (∃ (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ), X = gaussianOp M C) ∨
    ∃ Xm : ℕ → Fock n,
      (∀ m, ∃ (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ), Xm m = gaussianOp M C) ∧
        Filter.Tendsto Xm Filter.atTop (nhds X)

/-- The condition that `M` is real and antisymmetric and `ρ` equals its Gaussian expansion with
coefficient `2^(-n)`. -/
noncomputable def IsGaussianState {n : ℕ} (ρ : Fock n)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop :=
  (∀ a b, M a b = -(M b a)) ∧ (∀ a b, (M a b).im = 0) ∧
    ρ = gaussianOp M (((2 : ℂ) ^ n)⁻¹)

/-- The correlation entry `(I / 2) * trace (X * (gen a * gen b - gen b * gen a))`. -/
noncomputable def correlation {n : ℕ} (X : Fock n) (a b : Fin (2 * n)) : ℂ :=
  (Complex.I / 2) * Matrix.trace (X * (gen a * gen b - gen b * gen a))

/-- The condition that every entry of `M` equals the corresponding correlation of `X`. -/
noncomputable def IsCorrelationMatrixOf {n : ℕ} (X : Fock n)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop := ∀ a b, M a b = correlation X a b

/-- The Majorana index `2 * j` associated with mode `j`. -/
noncomputable def evenIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨2 * (j : ℕ), by omega⟩

/-- The Majorana index `2 * j + 1` associated with mode `j`. -/
noncomputable def oddIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨2 * (j : ℕ) + 1, by omega⟩

/-- The ordered product of `1 + I * lam j * gen (evenIdx j) * gen (oddIdx j)`, scaled by
`2^(-n)`. -/
noncomputable def productState {n : ℕ} (lam : Fin n → ℝ) : Fock n :=
  (((2 : ℂ) ^ n)⁻¹) •
    ((List.finRange n).map (fun j =>
      (1 : Fock n) + (Complex.I * (lam j : ℂ)) •
        (gen (evenIdx j) * gen (oddIdx j)))).prod

/-- The linear combination of Majorana generators specified by row `a` of `T`. -/
noncomputable def linearForm {n : ℕ} (T : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (a : Fin (2 * n)) : Fock n := ∑ b : Fin (2 * n), T a b • gen b

/-- The signed sum of all permuted products of the list entries, divided by the factorial of the
list length. -/
noncomputable def wedgeList {n : ℕ} (l : List (Fock n)) : Fock n :=
  ((Nat.factorial l.length : ℂ))⁻¹ •
    ∑ σ : Equiv.Perm (Fin l.length),
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
        (List.ofFn (fun a : Fin l.length => l.get (σ a))).prod

/-- The scalar-weighted product of the antisymmetrized first `2 * k` transformed generators and
a Pfaffian expansion over even subsets of the remaining indices. -/
noncomputable def gaussianFormOp {n : ℕ} (k : ℕ) (hk : 2 * k ≤ 2 * n)
    (T : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Fock n :=
  C • (wedgeList (List.ofFn (fun a : Fin (2 * k) => linearForm T (Fin.castLE hk a)))) *
    (∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin (2 * n)) =>
        (∀ a ∈ S, 2 * k ≤ (a : ℕ)) ∧ Even S.card)),
      (Complex.I ^ (S.card / 2) * pfaffianSub M S) •
        wedgeList ((S.sort (· ≤ ·)).map (fun a => linearForm T a)))

/-- The matrix with entries one at `(0, 1)`, negative one at `(1, 0)`, and zero elsewhere. -/
noncomputable def K (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun a b =>
    if (a : ℕ) = 0 ∧ (b : ℕ) = 1 then 1
    else if (a : ℕ) = 1 ∧ (b : ℕ) = 0 then -1 else 0

/-- The recursive Pfaffian expression on the empty list is one. -/
@[simp] theorem pfaffianList_nil {ι : Type*} [DecidableEq ι] (M : ι → ι → ℂ) :
    pfaffianList M [] = 1 := by simp [pfaffianList]

/-- The Pfaffian of the submatrix on the empty index set is one. -/
@[simp] theorem pfaffianSub_empty {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    pfaffianSub M ∅ = 1 := by
  simp [pfaffianSub]

/-- The Majorana monomial on the empty index set is the identity. -/
@[simp] theorem monomial_empty {n : ℕ} : monomial (∅ : Finset (Fin (2 * n))) = 1 := by
  simp [monomial]

/-- Multiplying the coefficient of a Gaussian expansion by `a` scales the resulting operator by
`a`. -/
theorem gaussianOp_smul {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (a C : ℂ) :
    gaussianOp M (a * C) = a • gaussianOp M C := by
  simp only [gaussianOp, smul_smul]

/-- The Pfaffian expression for the zero matrix vanishes on any nonempty list. -/
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

/-- The Pfaffian of a zero-matrix submatrix vanishes for every nonempty index set. -/
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

/-- The Gaussian expansion with zero matrix parameter is `C` times the identity. -/
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

/-- An operator equal to a Gaussian Pfaffian expansion satisfies `IsGaussianOperator`. -/
theorem isGaussianOperator_of_eq {n : ℕ} {X : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} {C : ℂ} (h : X = gaussianOp M C) :
    IsGaussianOperator X := Or.inl ⟨M, C, h⟩

end Qatlib.Papers.FermLinOpt04.MainResults.Model
