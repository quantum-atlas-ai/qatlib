/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationProofs

/-!
# Open-boundary MPS overlaps and examples

This module identifies `mpsAmplitude` with the zero-to-zero matrix entry of `word`, then
evaluates `transferWord` as an open-boundary inner product and squared norm. It also
characterizes a zero squared norm by vanishing of every physical-word amplitude.

Explicit complex, Bell, zero, and diagonal examples check conjugation and distinguish open from
periodic boundary contractions. These constructions use the matrix product state setting of
[PerezGarciaEtAl2007].

## Main statements

* `mpsAmplitude_eq_word`: Open-boundary amplitudes are zero-to-zero ordered-product entries.
* `transferWord_inner`: Mixed-transfer contraction equals the sum of conjugate amplitude
  products.
* `normSq_sum_eq_zero_iff`: The squared norm vanishes exactly when every amplitude vanishes.
* `open_overlap_and_consumers`: The identities and boundary examples are assembled, including a
  counterexample to the stated evaluator specification.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open scoped Kronecker

/-- An entry of an ordered product of `m + 1` matrices is the sum over all `m` internal indices
of the products of the corresponding matrix entries. -/
private theorem ofFn_prod_apply {D : ℕ} :
    ∀ (m : ℕ) (M : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ) (a b : Fin D),
    (List.ofFn M).prod a b
      = ∑ α : Fin m → Fin D, ∏ i : Fin (m + 1),
        M i (Fin.cons (α := fun _ => Fin D) a α i) (Fin.snoc (α := fun _ => Fin D) α b i) := by
  intro m
  induction m with
  | zero =>
      intro M a b
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_zero, List.prod_nil, Matrix.mul_one]
      rw [Finset.sum_eq_single (Fin.elim0 (α := Fin D))]
      · rw [Fin.prod_univ_one]
        rfl
      · intro c _ hc
        exact absurd (funext fun i => i.elim0 : c = Fin.elim0) hc
      · intro h
        exact absurd (Finset.mem_univ Fin.elim0) h
  | succ m ih =>
      intro M a b
      rw [peel M, Matrix.mul_apply]
      simp only [ih (fun i => M i.succ)]
      simp only [Finset.mul_sum]
      rw [← (Fintype.sum_prod_type (fun p : Fin D × (Fin m → Fin D) =>
        M 0 a p.1 * ∏ i : Fin (m + 1),
        M i.succ (Fin.cons (α := fun _ => Fin D) p.1 p.2 i)
          (Fin.snoc (α := fun _ => Fin D) p.2 b i)))]
      refine Fintype.sum_equiv (Fin.consEquiv fun _ => Fin D)
        (fun p => M 0 a p.1 * ∏ i : Fin (m + 1),
          M i.succ (Fin.cons (α := fun _ => Fin D) p.1 p.2 i)
            (Fin.snoc (α := fun _ => Fin D) p.2 b i))
        (fun α => ∏ i : Fin (m + 2),
          M i (Fin.cons (α := fun _ => Fin D) a α i)
            (Fin.snoc (α := fun _ => Fin D) α b i)) ?_
      intro p
      show M 0 a p.1 * ∏ i : Fin (m + 1),
          M i.succ (Fin.cons (α := fun _ => Fin D) p.1 p.2 i)
            (Fin.snoc (α := fun _ => Fin D) p.2 b i)
        = ∏ i : Fin (m + 1 + 1),
          M i (Fin.cons (α := fun _ => Fin D) a
            (Fin.cons (α := fun _ => Fin D) p.1 p.2) i)
            (Fin.snoc (α := fun _ => Fin D) (Fin.cons (α := fun _ => Fin D) p.1 p.2) b i)
      rw [Fin.prod_univ_succ (fun i => M i
        (Fin.cons (α := fun _ => Fin D) a (Fin.cons (α := fun _ => Fin D) p.1 p.2) i)
        (Fin.snoc (α := fun _ => Fin D) (Fin.cons (α := fun _ => Fin D) p.1 p.2) b i))]
      have hsnoc : Fin.snoc (Fin.cons (α := fun _ => Fin D) p.1 p.2) b
          = Fin.cons (α := fun _ => Fin D) p.1 (Fin.snoc (α := fun _ => Fin D) p.2 b) :=
        (Fin.cons_snoc_eq_snoc_cons p.1 p.2 b).symm
      rw [hsnoc]
      simp only [Fin.cons_zero, Fin.cons_succ]

/-- The left bond-index function is the internal-index word prefixed by the zero boundary index. -/
private theorem mpsLeftIdx_eq_cons {D : ℕ} [NeZero D] {m : ℕ} (α : Fin m → Fin D)
    (i : Fin (m + 1)) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx (n := m + 1) α i
      = Fin.cons (α := fun _ => Fin D) (0 : Fin D) α i := by
  induction i using Fin.cases with
  | zero => simp [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx]
  | succ j =>
      rw [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx, Fin.cons_succ,
        if_neg (by rw [Fin.val_succ]; omega),
        dif_pos (by rw [Fin.val_succ, Nat.succ_sub_one]; have := j.isLt; omega)]
      exact congrArg α (Fin.ext (by simp [Fin.val_succ]))

/-- The right bond-index function is the internal-index word suffixed by the zero boundary
index. -/
private theorem mpsRightIdx_eq_snoc {D : ℕ} [NeZero D] {m : ℕ} (α : Fin m → Fin D)
    (i : Fin (m + 1)) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx (n := m + 1) α i
      = Fin.snoc (α := fun _ => Fin D) α (0 : Fin D) i := by
  by_cases h : (i : ℕ) < m
  · rw [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx, dif_pos (by omega)]
    conv_rhs => rw [← Fin.castSucc_castLT i h, Fin.snoc_castSucc]
    rfl
  · have hval : (i : ℕ) = m := by have := i.isLt; omega
    rw [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx, dif_neg (by omega), Fin.eq_last_of_not_lt h,
      Fin.snoc_last]

/-- The open-boundary MPS amplitude equals the zero-to-zero entry of the ordered matrix product
for the physical word. -/
theorem mpsAmplitude_eq_word {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x = word A x 0 0 := by
  cases n with
  | zero =>
      rw [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude]
      show (∑ α : Fin 0 → Fin D, ∏ i : Fin 0,
        A i (x i) (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx α i) (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx α i))
        = word A x 0 0
      rw [Finset.sum_eq_single (Fin.elim0 (α := Fin D))]
      · simp [word]
      · intro c _ hc
        exact absurd (funext fun i => i.elim0 : c = Fin.elim0) hc
      · intro h
        exact absurd (Finset.mem_univ Fin.elim0) h
  | succ m =>
      rw [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude]
      show (∑ α : Fin m → Fin D, ∏ i : Fin (m + 1),
        A i (x i) (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx (n := m + 1) α i)
          (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx (n := m + 1) α i)) = word A x 0 0
      have hbody : ∀ α : Fin m → Fin D,
          (∏ i, A i (x i) (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx (n := m + 1) α i)
              (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx (n := m + 1) α i))
          = ∏ i, A i (x i) (Fin.cons (α := fun _ => Fin D) (0 : Fin D) α i)
              (Fin.snoc (α := fun _ => Fin D) α (0 : Fin D) i) :=
        fun α => Finset.prod_congr rfl fun i _ => by
          rw [mpsLeftIdx_eq_cons, mpsRightIdx_eq_snoc]
      simp only [hbody]
      show (∑ α : Fin m → Fin D, ∏ i : Fin (m + 1),
          A i (x i) (Fin.cons (α := fun _ => Fin D) (0 : Fin D) α i)
            (Fin.snoc (α := fun _ => Fin D) α (0 : Fin D) i)) = word A x 0 0
      rw [← ofFn_prod_apply m (fun i => A i (x i)) 0 0]
      rfl

/-- The zero-boundary entry of the mixed-transfer product equals the sum of conjugated
amplitudes of `A` times amplitudes of `B`. -/
theorem transferWord_inner {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    transferWord A B (0, 0) (0, 0)
      = ∑ x : Fin n → Fin d, star (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x)
          * Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude B x := by
  rw [transferWord_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.kronecker_apply, Matrix.map_apply, mpsAmplitude_eq_word, mpsAmplitude_eq_word]
  rfl

/-- The zero-boundary self-transfer entry equals the complex embedding of the sum of squared
amplitude norms. -/
theorem transferWord_norm {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    transferWord A A (0, 0) (0, 0)
      = Complex.ofReal (∑ x : Fin n → Fin d, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x)) := by
  rw [transferWord_inner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Complex.normSq_eq_conj_mul_self (z := Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x)).symm

/-- The sum of squared MPS amplitude norms is zero if and only if every physical-word amplitude
is zero. -/
theorem normSq_sum_eq_zero_iff {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (∑ x : Fin n → Fin d, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x) = 0)
      ↔ ∀ x : Fin n → Fin d, Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x = 0 := by
  constructor
  · intro h x
    have hx := Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => Complex.normSq_nonneg _) |>.mp h x (Finset.mem_univ x)
    exact Complex.normSq_eq_zero.mp hx
  · intro h
    exact Finset.sum_eq_zero fun x _ => by rw [h x, Complex.normSq_zero]

/-- The squared complex norm of a natural power equals the corresponding power of the squared
norm. -/
private theorem normSq_pow (z : ℂ) : ∀ n : ℕ, Complex.normSq (z ^ n) = Complex.normSq z ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

/-- Every physical-word amplitude of `plusISite n` equals `(1 + Complex.I) ^ n`. -/
private theorem plusI_amp (n : ℕ) (x : Fin n → Fin 1) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude (plusISite n) x = (1 + Complex.I) ^ n := by
  rw [show plusISite n = (fun _ _ => Matrix.of fun _ _ => (1 + Complex.I : ℂ)) from rfl,
    Qatlib.Concepts.TensorNetwork.GaugeInvariance.mpsAmplitude_product, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The sum of squared amplitude norms for `plusISite n` is `2 ^ n`. -/
theorem plusI_norm_sum (n : ℕ) :
    (∑ x : Fin n → Fin 1, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude (plusISite n) x))
      = (2 : ℝ) ^ n := by
  have key : ∀ b : Fin n → Fin 1, b = (fun _ => (0 : Fin 1)) :=
    fun b => funext fun i => Subsingleton.elim _ _
  rw [Finset.sum_eq_single (fun _ => (0 : Fin 1))]
  · rw [plusI_amp, normSq_pow,
      show Complex.normSq (1 + Complex.I) = 2 by norm_num [Complex.normSq]]
  · intro b _ hb
    exact absurd (key b) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The zero-boundary self-transfer entry for `plusISite n` is the complex embedding of `2 ^ n`. -/
theorem plusI_transfer (n : ℕ) :
    transferWord (plusISite n) (plusISite n) (0, 0) (0, 0)
      = Complex.ofReal ((2 : ℝ) ^ n) := by
  rw [transferWord_norm, plusI_norm_sum]

/-- The two-site Bell tensor has amplitude one on equal physical symbols and zero on unequal
symbols. -/
private theorem bell_amp_cons (a b : Fin 2) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude bellSite (Fin.cons (α := fun _ => Fin 2) a (fun _ => b))
      = if a = b then (1 : ℂ) else 0 := by
  rw [Qatlib.Concepts.TensorNetwork.GaugeInvariance.mpsAmplitude_two_site]
  fin_cases a <;> fin_cases b <;> simp [bellSite]

/-- The equivalence between a pair of binary symbols and a binary word of length two. -/
private def pairWordEquiv : Fin 2 × Fin 2 ≃ (Fin 2 → Fin 2) where
  toFun p := Fin.cons (α := fun _ => Fin 2) p.1 (fun _ => p.2)
  invFun x := (x 0, x ⟨1, by omega⟩)
  left_inv p := by
    show (Fin.cons (α := fun _ => Fin 2) p.1 (fun _ => p.2) 0,
      Fin.cons (α := fun _ => Fin 2) p.1 (fun _ => p.2) ⟨1, by omega⟩) = (p.1, p.2)
    rw [Prod.mk.injEq, Fin.cons_zero]
    exact ⟨rfl, Fin.cons_succ (α := fun _ => Fin 2) p.1 (fun _ => p.2) ⟨0, Nat.zero_lt_one⟩⟩
  right_inv x := by
    funext i
    match i with
    | ⟨0, _⟩ => exact Fin.cons_zero _ _
    | ⟨1, _⟩ =>
        exact Fin.cons_succ (α := fun _ => Fin 2) (x 0) (fun _ => x ⟨1, by omega⟩)
          ⟨0, Nat.zero_lt_one⟩

/-- The unnormalized Bell tensor has total squared amplitude norm two. -/
theorem bell_norm_sum :
    (∑ x : Fin 2 → Fin 2, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude bellSite x)) = 2 := by
  rw [← Fintype.sum_equiv pairWordEquiv
    (fun p => Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude bellSite (pairWordEquiv p)))
    (fun x => Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude bellSite x)) (fun _ => rfl)]
  have key : ∀ p : Fin 2 × Fin 2,
      Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude bellSite (pairWordEquiv p))
        = if p.1 = p.2 then (1 : ℝ) else 0 := by
    intro p
    have hx : pairWordEquiv p = Fin.cons (α := fun _ => Fin 2) p.1 (fun _ => p.2) := rfl
    rw [hx, bell_amp_cons]
    by_cases h : p.1 = p.2 <;> simp [h]
  simp only [key, Fintype.sum_prod_type]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num

/-- The zero-boundary self-transfer entry of the Bell tensor equals two. -/
theorem bell_transfer :
    transferWord bellSite bellSite (0, 0) (0, 0) = Complex.ofReal 2 := by
  rw [transferWord_norm, bell_norm_sum]

/-- The amplitude of `phiSite` is the product of the indicators that each physical symbol is
zero. -/
private theorem phi_amp (x : Fin 2 → Fin 2) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude phiSite x = ∏ i, (if (x i).val = 0 then (1 : ℂ) else 0) := by
  rw [show phiSite = (fun _ j => Matrix.of fun _ _ => if j.val = 0 then (1 : ℂ) else 0) from rfl,
    Qatlib.Concepts.TensorNetwork.GaugeInvariance.mpsAmplitude_product]

/-- The amplitude of `psiSite` is the product of the indicators that each physical symbol is
one. -/
private theorem psi_amp (x : Fin 2 → Fin 2) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude psiSite x = ∏ i, (if (x i).val = 1 then (1 : ℂ) else 0) := by
  rw [show psiSite = (fun _ j => Matrix.of fun _ _ => if j.val = 1 then (1 : ℂ) else 0) from rfl,
    Qatlib.Concepts.TensorNetwork.GaugeInvariance.mpsAmplitude_product]

/-- The zero-boundary mixed-transfer overlap of `phiSite` with `psiSite` is zero. -/
theorem phi_psi_cross : transferWord phiSite psiSite (0, 0) (0, 0) = 0 := by
  rw [transferWord_inner]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [phi_amp, psi_amp]
  by_cases hx0 : (x 0).val = 0
  · have h1 : ¬((x 0).val = 1) := by have := (x 0).isLt; omega
    have hψ : (∏ i, if (x i).val = 1 then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 2)) (by rw [if_neg h1])
    rw [hψ, mul_zero]
  · have hφ : (∏ i, if (x i).val = 0 then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 2)) (by rw [if_neg hx0])
    rw [hφ, star_zero, zero_mul]

/-- The zero-boundary overlap of the scalar imaginary-unit tensor with the scalar identity
tensor is `-Complex.I`. -/
theorem i_one_transfer : transferWord iSite oneSite (0, 0) (0, 0) = -Complex.I := by
  rw [transferWord_inner]
  have key : ∀ b : Fin 1 → Fin 1, b = (fun _ => (0 : Fin 1)) :=
    fun b => funext fun i => Subsingleton.elim _ _
  rw [Finset.sum_eq_single (fun _ => (0 : Fin 1))]
  · rw [show iSite = (fun _ _ => Matrix.of fun _ _ => (Complex.I : ℂ)) from rfl,
      show oneSite = (fun _ _ => Matrix.of fun _ _ => (1 : ℂ)) from rfl,
      Qatlib.Concepts.TensorNetwork.GaugeInvariance.mpsAmplitude_product, Qatlib.Concepts.TensorNetwork.GaugeInvariance.mpsAmplitude_product]
    simp only [Fin.prod_univ_one]
    simp [Complex.conj_I]
  · intro b _ hb
    exact absurd (key b) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- An identically zero tensor family of positive length has zero total squared amplitude norm. -/
theorem zero_site_norm_sum (n' d' D' : ℕ) (hn : 0 < n') [NeZero D'] :
    (∑ x : Fin n' → Fin d', Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude (zeroSite n' d' D') x))
      = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
  have h0 : word (zeroSite (m + 1) d' D') x = 0 := by
    show (List.ofFn fun i : Fin (m + 1) => (0 : Matrix (Fin D') (Fin D') ℂ)).prod = 0
    rw [peel, zero_mul]
  rw [mpsAmplitude_eq_word, h0, Matrix.zero_apply, Complex.normSq_zero]

/-- The zero-boundary self-transfer contraction of the auxiliary tensor `g14rA4` is zero. -/
theorem clause14Aux_transfer :
    transferWord Qatlib.Concepts.TensorNetwork.GaugeInvariance.g14rA4 Qatlib.Concepts.TensorNetwork.GaugeInvariance.g14rA4 (0, 0) (0, 0) = 0 := by
  rw [transferWord_inner]
  exact Qatlib.Concepts.TensorNetwork.GaugeInvariance.clause14Aux_amp_pair_sum

/-- The open-boundary amplitude of `diagSite` equals one. -/
theorem diag_open (x : Fin 1 → Fin 1) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude diagSite x = 1 := by
  rw [mpsAmplitude_eq_word]
  show (List.ofFn fun i : Fin 1 => diagSite i (x i)).prod 0 0 = 1
  rw [peel, List.ofFn_zero, List.prod_nil, Matrix.mul_one]
  simp [diagSite]

/-- The periodic amplitude of `diagSite` equals three. -/
theorem diag_periodic (x : Fin 1 → Fin 1) :
    Qatlib.Concepts.MpsAdaptation.MpsTransfer.periodicMpsAmplitude diagSite x = 3 := by
  rw [Qatlib.Concepts.MpsAdaptation.MpsTransfer.periodicMpsAmplitude]
  have hbody : ∀ f : Fin 1 → Fin 2,
      (∏ i : Fin 1, diagSite i (x i) (f i)
          (f ⟨((i : ℕ) + 1) % 1, Nat.mod_lt _ (NeZero.pos 1)⟩))
      = diagSite 0 (x 0) (Qatlib.Concepts.TensorNetwork.GaugeInvariance.equivSingle21 f) (Qatlib.Concepts.TensorNetwork.GaugeInvariance.equivSingle21 f) := by
    intro f
    rw [Fin.prod_univ_one]
    rfl
  rw [Fintype.sum_equiv Qatlib.Concepts.TensorNetwork.GaugeInvariance.equivSingle21
    (fun f => ∏ i : Fin 1, diagSite i (x i) (f i)
      (f ⟨((i : ℕ) + 1) % 1, Nat.mod_lt _ (NeZero.pos 1)⟩))
    (fun k => diagSite 0 (x 0) k k) hbody]
  rw [Fin.sum_univ_two]
  norm_num [diagSite]

/-- The open-boundary product, overlap, and norm identities hold together with empty cases and
explicit tensor examples. The auxiliary example refutes the stated universal
correctness-and-cost specification for `mpsInnerEvalWithCount`. -/
theorem open_overlap_and_consumers :
    (∀ (n d D : ℕ) [NeZero D],
      ∀ (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      (∀ x : Fin n → Fin d, Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x = word A x 0 0)
      ∧ (transferWord A B (0, 0) (0, 0)
          = ∑ x : Fin n → Fin d,
            star (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x) * Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude B x)
      ∧ (transferWord A A (0, 0) (0, 0)
          = Complex.ofReal (∑ x : Fin n → Fin d,
              Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x))
        ∧ ((∑ x : Fin n → Fin d, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x) = 0)
            ↔ ∀ x : Fin n → Fin d, Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x = 0)))
    ∧ (∀ (d D : ℕ) [NeZero D], ∀ (A : Fin 0 → Fin d → Matrix (Fin D) (Fin D) ℂ),
        (∀ x : Fin 0 → Fin d, Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x = 1)
        ∧ (∑ x : Fin 0 → Fin d, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x)) = 1)
    ∧ (∀ (n D : ℕ) [NeZero D], 0 < n →
        ∀ (A B : Fin n → Fin 0 → Matrix (Fin D) (Fin D) ℂ),
        (∑ x : Fin n → Fin 0, Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x)) = 0
        ∧ (∑ x : Fin n → Fin 0,
            star (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude A x) * Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude B x) = 0
        ∧ transferWord A B (0, 0) (0, 0) = 0)
    ∧ ((∀ n' : ℕ,
          (∑ x : Fin n' → Fin 1,
              Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude (plusISite n') x)) = (2 : ℝ) ^ n'
        ∧ transferWord (plusISite n') (plusISite n') (0, 0) (0, 0)
            = Complex.ofReal ((2 : ℝ) ^ n'))
      ∧ ((∑ x : Fin 2 → Fin 2,
            Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude bellSite x)) = 2
        ∧ transferWord bellSite bellSite (0, 0) (0, 0) = Complex.ofReal 2)
      ∧ transferWord phiSite psiSite (0, 0) (0, 0) = 0
      ∧ transferWord iSite oneSite (0, 0) (0, 0) = -Complex.I
      ∧ (∀ (n' d' D' : ℕ), 0 < n' → ∀ [NeZero D'],
          (∑ x : Fin n' → Fin d',
              Complex.normSq (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude (zeroSite n' d' D') x)) = 0)
      ∧ (transferWord Qatlib.Concepts.TensorNetwork.GaugeInvariance.g14rA4 Qatlib.Concepts.TensorNetwork.GaugeInvariance.g14rA4 (0, 0) (0, 0) = 0
        ∧ (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsInnerEvalWithCount (n := 2) (d := 1) (D := 2)
            Qatlib.Concepts.TensorNetwork.GaugeInvariance.g14rA4 Qatlib.Concepts.TensorNetwork.GaugeInvariance.g14rA4).1 = 1
        ∧ ¬ (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
            (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
            (@Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsInnerEvalWithCount n d D hn hD A B).1
              = ∑ x, (starRingEnd ℂ) (@Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude n d D hD A x)
                * @Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude n d D hD B x
            ∧ (@Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsInnerEvalWithCount n d D hn hD A B).2
              ≤ Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsInnerOpCount n d D))
      ∧ (∀ x : Fin 1 → Fin 1,
          Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude diagSite x = 1
          ∧ Qatlib.Concepts.MpsAdaptation.MpsTransfer.periodicMpsAmplitude diagSite x = 3)) := by
  refine ⟨fun _ _ _ _ A B => ⟨fun x => mpsAmplitude_eq_word A x, transferWord_inner A B,
    transferWord_norm A, normSq_sum_eq_zero_iff A⟩, ?_, ?_, ?_⟩
  · intro d D _ A
    refine ⟨fun x => by simp [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude], ?_⟩
    rw [Finset.sum_eq_single (Fin.elim0 (α := Fin d))]
    · simp [Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsAmplitude]
    · intro c _ hc
      exact absurd (funext fun i => i.elim0 : c = Fin.elim0) hc
    · intro h
      exact absurd (Finset.mem_univ Fin.elim0) h
  · intro n D _ hn A B
    exact ⟨Finset.sum_eq_zero fun x _ => (x ⟨0, hn⟩).elim0,
      Finset.sum_eq_zero fun x _ => (x ⟨0, hn⟩).elim0, by
        rw [(transferWord_empty_phys hn A B).1]; simp⟩
  · exact ⟨fun n' => ⟨plusI_norm_sum n', plusI_transfer n'⟩,
    ⟨bell_norm_sum, bell_transfer⟩, phi_psi_cross, i_one_transfer,
    fun _ _ _ hn _ => zero_site_norm_sum _ _ _ hn,
    ⟨clause14Aux_transfer, Qatlib.Concepts.TensorNetwork.GaugeInvariance.clause14Aux_mpsInnerEvalCount_fst,
      Qatlib.Concepts.TensorNetwork.GaugeInvariance.clause3_clause4_counter⟩,
    fun x => ⟨diag_open x, diag_periodic x⟩⟩

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
