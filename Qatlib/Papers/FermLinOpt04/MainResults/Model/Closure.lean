/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermLinOpt04.MainResults.Model

theorem tensorSquare_mul {n : ℕ} (A B : Fock n) :
    tensorSquare (A * B) = tensorSquare A * tensorSquare B := by
  ext ⟨y1, y2⟩ ⟨x1, x2⟩
  simp only [tensorSquare, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  ring

theorem tensorSquare_one {n : ℕ} : tensorSquare (1 : Fock n) = 1 := by
  ext ⟨y1, y2⟩ ⟨x1, x2⟩
  rw [tensorSquare, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h1 : y1 = x1 <;> by_cases h2 : y2 = x2 <;> simp [h1, h2, Prod.ext_iff]

theorem tensorSquare_smul {n : ℕ} (c : ℂ) (A : Fock n) :
    tensorSquare (c • A) = (c * c) • tensorSquare A := by
  ext ⟨y1, y2⟩ ⟨x1, x2⟩
  simp only [tensorSquare, Matrix.smul_apply, smul_eq_mul]
  ring

theorem tensorSquare_zero {n : ℕ} : tensorSquare (0 : Fock n) = 0 := by
  ext ⟨y1, y2⟩ ⟨x1, x2⟩
  simp [tensorSquare]

theorem lambdaCommute_mul {n : ℕ} {X Y : Fock n}
    (hX : lambdaCommute X) (hY : lambdaCommute Y) : lambdaCommute (X * Y) := by
  show Lambda n * tensorSquare (X * Y) = tensorSquare (X * Y) * Lambda n
  rw [tensorSquare_mul]
  have hX' : Lambda n * tensorSquare X = tensorSquare X * Lambda n := hX
  have hY' : Lambda n * tensorSquare Y = tensorSquare Y * Lambda n := hY
  calc Lambda n * (tensorSquare X * tensorSquare Y)
      = Lambda n * tensorSquare X * tensorSquare Y := by rw [Matrix.mul_assoc]
    _ = tensorSquare X * Lambda n * tensorSquare Y := by rw [hX']
    _ = tensorSquare X * (Lambda n * tensorSquare Y) := by rw [Matrix.mul_assoc]
    _ = tensorSquare X * (tensorSquare Y * Lambda n) := by rw [hY']
    _ = tensorSquare X * tensorSquare Y * Lambda n := by rw [Matrix.mul_assoc]

theorem lambdaCommute_one {n : ℕ} : lambdaCommute (1 : Fock n) := by
  show Lambda n * tensorSquare 1 = tensorSquare 1 * Lambda n
  rw [tensorSquare_one, Matrix.mul_one, Matrix.one_mul]

theorem parityOp_sq {n : ℕ} : (parityOp : Fock n) * parityOp = 1 :=
  (g1 n).2.2.2.1.1

theorem parityOp_annihilation {n : ℕ} (i : Fin n) :
    (parityOp : Fock n) * annihilation i = -(annihilation i * parityOp) :=
  ((g1 n).2.2.2.1.2 i).1

theorem parityOp_creation {n : ℕ} (i : Fin n) :
    (parityOp : Fock n) * creation i = -(creation i * parityOp) :=
  ((g1 n).2.2.2.1.2 i).2 i

theorem parityOp_annihilation_conj {n : ℕ} (i : Fin n) :
    (parityOp : Fock n) * annihilation i * parityOp = -annihilation i := by
  rw [parityOp_annihilation, neg_mul, Matrix.mul_assoc, parityOp_sq, Matrix.mul_one]

theorem parityOp_creation_conj {n : ℕ} (i : Fin n) :
    (parityOp : Fock n) * creation i * parityOp = -creation i := by
  rw [parityOp_creation, neg_mul, Matrix.mul_assoc, parityOp_sq, Matrix.mul_one]

private theorem parity_mid {n : ℕ} (X Y : Fock n) :
    (parityOp : Fock n) * (X * Y) * parityOp
      = (parityOp * X * parityOp) * (parityOp * Y * parityOp) := by
  have hP : (parityOp : Fock n) * parityOp = 1 := parityOp_sq
  have h1 : (parityOp : Fock n) * X * parityOp * (parityOp * Y * parityOp)
      = (parityOp * X) * (Y * parityOp) := by
    calc (parityOp : Fock n) * X * parityOp * (parityOp * Y * parityOp)
        = (parityOp * X) * (parityOp * (parityOp * (Y * parityOp))) := by
          simp only [Matrix.mul_assoc]
      _ = (parityOp * X) * ((parityOp * parityOp) * (Y * parityOp)) := by
          rw [← Matrix.mul_assoc (parityOp) (parityOp) (Y * parityOp)]
      _ = (parityOp * X) * (Y * parityOp) := by rw [hP, Matrix.one_mul]
  calc (parityOp : Fock n) * (X * Y) * parityOp
      = (parityOp * X) * (Y * parityOp) := by simp only [Matrix.mul_assoc]
    _ = (parityOp * X * parityOp) * (parityOp * Y * parityOp) := h1.symm

theorem IsEvenOp.add {n : ℕ} {X Y : Fock n} (hX : IsEvenOp X) (hY : IsEvenOp Y) :
    IsEvenOp (X + Y) := by
  show (parityOp : Fock n) * (X + Y) * parityOp = X + Y
  have hX' : (parityOp : Fock n) * X * parityOp = X := hX
  have hY' : (parityOp : Fock n) * Y * parityOp = Y := hY
  rw [Matrix.mul_add, Matrix.add_mul, hX', hY']

theorem IsEvenOp.neg {n : ℕ} {X : Fock n} (hX : IsEvenOp X) : IsEvenOp (-X) := by
  show (parityOp : Fock n) * (-X) * parityOp = -X
  have hX' : (parityOp : Fock n) * X * parityOp = X := hX
  rw [Matrix.mul_neg, Matrix.neg_mul, hX']

theorem IsEvenOp.smul {n : ℕ} (c : ℂ) {X : Fock n} (hX : IsEvenOp X) :
    IsEvenOp (c • X) := by
  show (parityOp : Fock n) * (c • X) * parityOp = c • X
  have hX' : (parityOp : Fock n) * X * parityOp = X := hX
  rw [Matrix.mul_smul, Matrix.smul_mul, hX']

theorem IsEvenOp.zero {n : ℕ} : IsEvenOp (0 : Fock n) := by
  show (parityOp : Fock n) * (0 : Fock n) * parityOp = 0
  simp

theorem IsEvenOp.one {n : ℕ} : IsEvenOp (1 : Fock n) := by
  show (parityOp : Fock n) * (1 : Fock n) * parityOp = 1
  rw [Matrix.mul_one, parityOp_sq]

theorem IsEvenOp.mul {n : ℕ} {X Y : Fock n} (hX : IsEvenOp X) (hY : IsEvenOp Y) :
    IsEvenOp (X * Y) := by
  show (parityOp : Fock n) * (X * Y) * parityOp = X * Y
  have hX' : (parityOp : Fock n) * X * parityOp = X := hX
  have hY' : (parityOp : Fock n) * Y * parityOp = Y := hY
  rw [parity_mid, hX', hY']

theorem IsOddOp.mul_odd {n : ℕ} {X Y : Fock n} (hX : IsOddOp X) (hY : IsOddOp Y) :
    IsEvenOp (X * Y) := by
  show (parityOp : Fock n) * (X * Y) * parityOp = X * Y
  have hX' : (parityOp : Fock n) * X * parityOp = -X := hX
  have hY' : (parityOp : Fock n) * Y * parityOp = -Y := hY
  rw [parity_mid, hX', hY', neg_mul_neg]

theorem IsOddOp.mul_even {n : ℕ} {X Y : Fock n} (hX : IsOddOp X) (hY : IsEvenOp Y) :
    IsOddOp (X * Y) := by
  show (parityOp : Fock n) * (X * Y) * parityOp = -(X * Y)
  have hX' : (parityOp : Fock n) * X * parityOp = -X := hX
  have hY' : (parityOp : Fock n) * Y * parityOp = Y := hY
  rw [parity_mid, hX', hY', neg_mul]

theorem IsEvenOp.mul_odd {n : ℕ} {X Y : Fock n} (hX : IsEvenOp X) (hY : IsOddOp Y) :
    IsOddOp (X * Y) := by
  show (parityOp : Fock n) * (X * Y) * parityOp = -(X * Y)
  have hX' : (parityOp : Fock n) * X * parityOp = X := hX
  have hY' : (parityOp : Fock n) * Y * parityOp = -Y := hY
  rw [parity_mid, hX', hY', mul_neg]

theorem IsEvenOp.sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fock n)
    (h : ∀ i ∈ s, IsEvenOp (f i)) : IsEvenOp (s.sum f) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using! IsEvenOp.zero
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact IsEvenOp.add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem isOddOp_majorana {n : ℕ} (a : Fin (2 * n)) : IsOddOp (majorana a) := by
  unfold IsOddOp
  simp only [majorana]
  split
  · rw [Matrix.mul_add, Matrix.add_mul, parityOp_creation_conj, parityOp_annihilation_conj,
      neg_add]
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      parityOp_annihilation_conj, parityOp_creation_conj]
    module

theorem IsOddOp.gen {n : ℕ} (a : Fin (2 * n)) : IsOddOp (gen a) :=
  isOddOp_majorana a

theorem parity_prod {n : ℕ} (l : List (Fock n)) (h : ∀ X ∈ l, IsOddOp X) :
    (Even l.length → IsEvenOp l.prod) ∧ (Odd l.length → IsOddOp l.prod) := by
  induction l with
  | nil =>
      refine ⟨fun _ => ?_, fun hodd => ?_⟩
      · simpa using! IsEvenOp.one
      · simp at hodd
  | cons x xs ih =>
      obtain ⟨ihE, ihO⟩ := ih (fun X hX => h X (List.mem_cons_of_mem x hX))
      have hx : IsOddOp x := h x (List.mem_cons_self ..)
      refine ⟨fun he => ?_, fun ho => ?_⟩
      · rw [List.prod_cons]
        have hlen : Odd xs.length := by
          rw [List.length_cons] at he
          obtain ⟨k, hk⟩ := he
          exact ⟨k - 1, by omega⟩
        exact IsOddOp.mul_odd hx (ihO hlen)
      · rw [List.prod_cons]
        have hlen : Even xs.length := by
          rw [List.length_cons] at ho
          obtain ⟨k, hk⟩ := ho
          exact ⟨k, by omega⟩
        exact IsOddOp.mul_even hx (ihE hlen)

theorem isEvenOp_monomial {n : ℕ} (S : Finset (Fin (2 * n))) (h : Even S.card) :
    IsEvenOp (monomial S) := by
  show IsEvenOp (((S.sort (· ≤ ·)).map (fun a => gen a)).prod)
  refine (parity_prod _ ?_).1 ?_
  · intro X hX
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hX
    exact IsOddOp.gen a
  · rw [List.length_map, Finset.length_sort]
    exact h

theorem isEvenOp_gaussianOp {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ) :
    IsEvenOp (gaussianOp M C) := by
  show IsEvenOp (C • (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => Even S.card)).sum
    (fun S => (Complex.I ^ (S.card / 2) * pfaffianSub M S) • monomial S))
  refine IsEvenOp.smul C ?_
  refine IsEvenOp.sum (Finset.univ.filter (fun S : Finset (Fin (2 * n)) => Even S.card))
    (fun S => (Complex.I ^ (S.card / 2) * pfaffianSub M S) • monomial S) ?_
  intro S hS
  exact IsEvenOp.smul _ (isEvenOp_monomial S (Finset.mem_filter.mp hS).2)

theorem isEvenOp_of_isGaussianOperator {n : ℕ} {X : Fock n}
    (h : IsGaussianOperator X) : IsEvenOp X := by
  rcases h with ⟨M, C, rfl⟩ | ⟨Xm, hXm, hlim⟩
  · exact isEvenOp_gaussianOp M C
  · show (parityOp : Fock n) * X * parityOp = X
    have hXmEven : ∀ m, (parityOp : Fock n) * Xm m * parityOp = Xm m := by
      intro m
      obtain ⟨M, C, hMC⟩ := hXm m
      rw [hMC]
      exact isEvenOp_gaussianOp M C
    have h1 : Filter.Tendsto (fun m => (parityOp : Fock n) * Xm m * parityOp)
        Filter.atTop (nhds ((parityOp : Fock n) * X * parityOp)) :=
      ((tendsto_const_nhds (x := (parityOp : Fock n))).mul hlim).mul
        (tendsto_const_nhds (x := (parityOp : Fock n)))
    have htend : Filter.Tendsto (fun m => (parityOp : Fock n) * Xm m * parityOp - Xm m)
        Filter.atTop (nhds ((parityOp : Fock n) * X * parityOp - X)) := h1.sub hlim
    have hzero : (fun m => (parityOp : Fock n) * Xm m * parityOp - Xm m) = fun _ => 0 := by
      funext m
      rw [hXmEven m, sub_self]
    rw [hzero] at htend
    have huniq : (0 : Fock n) = (parityOp : Fock n) * X * parityOp - X :=
      tendsto_const_nhds_iff.mp htend
    exact sub_eq_zero.mp huniq.symm

theorem charMul {n : ℕ} {X Y : Fock n}
    (hX : IsEvenOp X ∧ lambdaCommute X) (hY : IsEvenOp Y ∧ lambdaCommute Y) :
    IsEvenOp (X * Y) ∧ lambdaCommute (X * Y) :=
  ⟨IsEvenOp.mul hX.1 hY.1, lambdaCommute_mul hX.2 hY.2⟩

theorem gaussianOperator_mul_of_char {n : ℕ} {X Y : Fock n}
    (hchar : ∀ Z : Fock n, IsGaussianOperator Z ↔ (IsEvenOp Z ∧ lambdaCommute Z))
    (hX : IsGaussianOperator X) (hY : IsGaussianOperator Y) :
    IsGaussianOperator (X * Y) :=
  (hchar (X * Y)).mpr (charMul ((hchar X).mp hX) ((hchar Y).mp hY))

end Qatlib.Papers.FermLinOpt04.MainResults.Model
