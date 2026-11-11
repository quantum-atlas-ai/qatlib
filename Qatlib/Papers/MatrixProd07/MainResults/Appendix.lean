/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Word span growth and appendix propositions

`wordSpan` is the span of products of a fixed length in a family of bond matrices. When one
generator is invertible, dimensions are nondecreasing, equality propagates, and
`proposition2_C1_bound` bounds a spanning length by `D ^ 2`.

The module also defines `Conjecture2`, a normalized W state, locality predicates, and
propositions expressing a W state bond bound and a bond dimension dichotomy. These constructions
are associated with [PerezGarciaEtAl2007].

## Main statements

* `wordSpan_stabilizes`: propagates equality of consecutive word span dimensions.
* `proposition2_C1_bound`: a spanning length bound with an invertible generator.
* `theorem20_dichotomy`: proposition expressing the bond dimension alternative.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.Appendix

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open Module
open scoped BigOperators ComplexConjugate

/-- The space of complex amplitude functions on configurations of `N` sites of local dimension
`d`. -/
abbrev Ket (N d : ℕ) := (Fin N → Fin d) → ℂ

/-- The complex linear span of all length `r` products of the matrices `A`. -/
noncomputable def wordSpan {d D : ℕ} (A : Fin d → BM D) (r : ℕ) : Submodule ℂ (BM D) :=
  Submodule.span ℂ (Set.range (wordProd A r))

/-- Folding right multiplication from `X` equals `X` times the same fold starting from the
identity. -/
lemma foldl_mul_eq {d D : ℕ} (A : Fin d → BM D) (l : List (Fin d)) (X : BM D) :
    l.foldl (fun M i => M * A i) X = X * l.foldl (fun M i => M * A i) 1 := by
  induction l generalizing X with
  | nil => simp
  | cons a t ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (X * A a), ih (1 * A a), one_mul,
        Matrix.mul_assoc]

/-- The product associated with the empty word is the identity matrix. -/
lemma wordProd_zero {d D : ℕ} (A : Fin d → BM D) (w : Fin 0 → Fin d) :
    wordProd A 0 w = 1 := by
  simp [wordProd]

/-- Prepending a letter multiplies the remaining word product on the left by its matrix. -/
lemma wordProd_cons {d D : ℕ} (A : Fin d → BM D) (r : ℕ) (j : Fin d) (w : Fin r → Fin d) :
    wordProd A (r + 1) (Fin.cons j w) = A j * wordProd A r w := by
  unfold wordProd
  rw [List.ofFn_cons, List.foldl_cons, one_mul, foldl_mul_eq]

/-- Appending a letter multiplies the preceding word product on the right by its matrix. -/
lemma wordProd_snoc {d D : ℕ} (A : Fin d → BM D) (r : ℕ) (w : Fin r → Fin d) (j : Fin d) :
    wordProd A (r + 1) (Fin.snoc w j) = wordProd A r w * A j := by
  unfold wordProd
  have h : List.ofFn (Fin.snoc w j) = List.ofFn w ++ [j] := by
    rw [Fin.snoc_eq_append, List.ofFn_fin_append, List.ofFn_cons]
    simp
  rw [h, List.foldl_concat]

/-- The span of length zero word products is the span of the identity matrix. -/
lemma wordSpan_zero {d D : ℕ} (A : Fin d → BM D) :
    wordSpan A 0 = Submodule.span ℂ ({1} : Set (BM D)) := by
  unfold wordSpan
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    simp [wordProd_zero A w]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨fun i => i.elim0, by rw [wordProd_zero]; exact hx.symm⟩

/-- For positive bond dimension, the span of length zero word products has complex dimension
one. -/
lemma wordSpan_zero_finrank {d D : ℕ} (A : Fin d → BM D) (hD : 0 < D) :
    finrank ℂ (wordSpan A 0) = 1 := by
  rw [wordSpan_zero]
  have h1 : (1 : BM D) ≠ 0 := by
    intro h
    have h00 : (1 : ℂ) = 0 := by
      simpa using congrFun (congrFun h ⟨0, hD⟩) ⟨0, hD⟩
    exact one_ne_zero h00
  exact finrank_span_singleton h1

/-- The complex linear map given by right multiplication by `M`. -/
def mulRightLin {D : ℕ} (M : BM D) : BM D →ₗ[ℂ] BM D where
  toFun X := X * M
  map_add' X Y := Matrix.add_mul X Y M
  map_smul' c X := Matrix.smul_mul c X M

/-- The complex linear map given by left multiplication by `M`. -/
def mulLeftLin {D : ℕ} (M : BM D) : BM D →ₗ[ℂ] BM D where
  toFun X := M * X
  map_add' X Y := Matrix.mul_add M X Y
  map_smul' c X := Matrix.mul_smul M c X

/-- Right multiplication by an invertible matrix is injective. -/
lemma mulRight_injective {D : ℕ} {M : BM D} (hM : IsUnit M) :
    Function.Injective (mulRightLin M) :=
  hM.mul_left_injective

/-- Right multiplication by `A 0` sends the length `r` word span into the length `r + 1` word
span. -/
lemma map_mulRight_le_wordSpan_succ {d D : ℕ} [NeZero d] (A : Fin d → BM D) (r : ℕ) :
    Submodule.map (mulRightLin (A 0)) (wordSpan A r) ≤ wordSpan A (r + 1) := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  show mulRightLin (A 0) (wordProd A r w) ∈ wordSpan A (r + 1)
  rw [show mulRightLin (A 0) (wordProd A r w) = wordProd A (r + 1) (Fin.snoc w 0) from by
        simp [mulRightLin, wordProd_snoc]]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- Left multiplication by any generator sends the length `r` word span into the length `r + 1`
word span. -/
lemma map_mulLeft_le_wordSpan_succ {d D : ℕ} (A : Fin d → BM D) (r : ℕ) (j : Fin d) :
    Submodule.map (mulLeftLin (A j)) (wordSpan A r) ≤ wordSpan A (r + 1) := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  show mulLeftLin (A j) (wordProd A r w) ∈ wordSpan A (r + 1)
  rw [show mulLeftLin (A j) (wordProd A r w) = wordProd A (r + 1) (Fin.cons j w) from by
        simp [mulLeftLin, wordProd_cons]]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- If `A 0` is invertible, right multiplication by it preserves the dimension of each word
span. -/
lemma finrank_map_mulRight {d D : ℕ} [NeZero d] (A : Fin d → BM D) (h0 : IsUnit (A 0))
    (r : ℕ) :
    finrank ℂ (Submodule.map (mulRightLin (A 0)) (wordSpan A r))
      = finrank ℂ (wordSpan A r) := by
  have hinj : Function.Injective (mulRightLin (A 0)) := mulRight_injective h0
  have hinj' : Function.Injective
      ((mulRightLin (A 0)).comp (wordSpan A r).subtype) :=
    hinj.comp Subtype.val_injective
  have hmap : Submodule.map (mulRightLin (A 0)) (wordSpan A r)
      = LinearMap.range ((mulRightLin (A 0)).comp (wordSpan A r).subtype) := by
    ext x
    rw [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [hmap, LinearMap.finrank_range_of_inj hinj']

/-- If `A 0` is invertible, the dimension of the word span cannot decrease at the next length. -/
lemma finrank_le_succ {d D : ℕ} [NeZero d] (A : Fin d → BM D) (h0 : IsUnit (A 0)) (r : ℕ) :
    finrank ℂ (wordSpan A r) ≤ finrank ℂ (wordSpan A (r + 1)) := by
  calc finrank ℂ (wordSpan A r)
      = finrank ℂ (Submodule.map (mulRightLin (A 0)) (wordSpan A r)) :=
        (finrank_map_mulRight A h0 r).symm
    _ ≤ finrank ℂ (wordSpan A (r + 1)) :=
        Submodule.finrank_mono (map_mulRight_le_wordSpan_succ A r)

/-- If `A 0` is invertible, word span dimensions are nondecreasing with word length. -/
lemma finrank_mono_of_le {d D : ℕ} [NeZero d] (A : Fin d → BM D) (h0 : IsUnit (A 0))
    {a b : ℕ} (h : a ≤ b) :
    finrank ℂ (wordSpan A a) ≤ finrank ℂ (wordSpan A b) := by
  induction b generalizing a with
  | zero =>
      have haz : a = 0 := Nat.le_zero.mp h
      subst haz
      exact le_rfl
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq
        exact le_rfl
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (finrank_le_succ A h0 b)

/-- If the next word span equals the image under right multiplication by `A 0`, the following
word span is contained in the corresponding next image. -/
lemma wordSpan_succ_succ_le {d D : ℕ} [NeZero d] (A : Fin d → BM D) (r : ℕ)
    (h : wordSpan A (r + 1) = Submodule.map (mulRightLin (A 0)) (wordSpan A r)) :
    wordSpan A (r + 2) ≤ Submodule.map (mulRightLin (A 0)) (wordSpan A (r + 1)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, rfl⟩
  have hv : wordProd A (r + 2) v = A (v 0) * wordProd A (r + 1) (Fin.tail v) := by
    conv_lhs => rw [← Fin.cons_self_tail v]
    exact wordProd_cons A (r + 1) (v 0) (Fin.tail v)
  rw [hv]
  have hY : wordProd A (r + 1) (Fin.tail v) ∈ wordSpan A (r + 1) :=
    Submodule.subset_span ⟨_, rfl⟩
  rw [h] at hY
  obtain ⟨X, hX, hXeq⟩ := Submodule.mem_map.mp hY
  rw [← hXeq]
  refine Submodule.mem_map.mpr ⟨A (v 0) * X, ?_, ?_⟩
  · exact map_mulLeft_le_wordSpan_succ A r (v 0) (Submodule.mem_map.mpr ⟨X, hX, rfl⟩)
  · show (A (v 0) * X) * A 0 = A (v 0) * (X * A 0)
    rw [Matrix.mul_assoc]

/-- With `A 0` invertible, equality of two consecutive word span dimensions propagates to all
later lengths, together with the right multiplication image formula. -/
lemma wordSpan_stabilizes {d D : ℕ} [NeZero d] (A : Fin d → BM D) (h0 : IsUnit (A 0))
    {r : ℕ} (hr : finrank ℂ (wordSpan A (r + 1)) = finrank ℂ (wordSpan A r)) :
    ∀ t, wordSpan A (r + t + 1) = Submodule.map (mulRightLin (A 0)) (wordSpan A (r + t))
      ∧ finrank ℂ (wordSpan A (r + t + 1)) = finrank ℂ (wordSpan A r) := by
  intro t
  induction t with
  | zero =>
      have hbase : wordSpan A (r + 1) = Submodule.map (mulRightLin (A 0)) (wordSpan A r) := by
        refine (Submodule.eq_of_le_of_finrank_eq (map_mulRight_le_wordSpan_succ A r) ?_).symm
        rw [finrank_map_mulRight A h0 r, hr]
      refine ⟨?_, ?_⟩
      · simpa using hbase
      · rw [show finrank ℂ (wordSpan A (r + 0 + 1)) = finrank ℂ (wordSpan A (r + 1)) from rfl,
          hbase, finrank_map_mulRight A h0 r]
  | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hle : wordSpan A (r + (t + 1) + 1) ≤
          Submodule.map (mulRightLin (A 0)) (wordSpan A (r + (t + 1))) :=
        wordSpan_succ_succ_le A (r + t) ih1
      have hge : Submodule.map (mulRightLin (A 0)) (wordSpan A (r + (t + 1))) ≤
          wordSpan A (r + (t + 1) + 1) :=
        map_mulRight_le_wordSpan_succ A (r + (t + 1))
      refine ⟨le_antisymm hle hge, ?_⟩
      rw [le_antisymm hle hge, finrank_map_mulRight A h0 (r + (t + 1))]
      exact ih2

/-- If some word span is the full matrix space and `A 0` is invertible, equality of consecutive
dimensions at `r` forces the length `r` span to be full. -/
lemma wordSpan_eq_top_of_stable {d D : ℕ} [NeZero d] (A : Fin d → BM D)
    (h0 : IsUnit (A 0)) {L₀ : ℕ} (hL₀ : wordSpan A L₀ = ⊤) {r : ℕ}
    (hr : finrank ℂ (wordSpan A (r + 1)) = finrank ℂ (wordSpan A r)) :
    wordSpan A r = ⊤ := by
  by_cases h : r < L₀
  · obtain ⟨-, ih2⟩ := wordSpan_stabilizes A h0 hr (L₀ - r - 1)
    have hidx : r + (L₀ - r - 1) + 1 = L₀ := by omega
    rw [hidx, hL₀, finrank_top] at ih2
    exact Submodule.eq_top_of_finrank_eq ih2.symm
  · have h1 : finrank ℂ (wordSpan A r) ≤ finrank ℂ (BM D) := Submodule.finrank_le _
    have h2 : finrank ℂ (BM D) ≤ finrank ℂ (wordSpan A r) := by
      have hmono : finrank ℂ (wordSpan A L₀) ≤ finrank ℂ (wordSpan A r) :=
        finrank_mono_of_le A h0 (Nat.le_of_not_lt h)
      rwa [hL₀, finrank_top] at hmono
    exact Submodule.eq_top_of_finrank_eq (le_antisymm h1 h2)

/-- If `A 0` is invertible and some word length spans the full matrix space, then length `D ^ 2`
already spans it. See [PerezGarciaEtAl2007]. -/
theorem proposition2_C1_bound {d D : ℕ} [NeZero d] (A : Fin d → BM D)
    (h0 : IsUnit (A 0)) (hC1 : C1 A) : C1At A (D ^ 2) := by
  change wordSpan A (D ^ 2) = ⊤
  obtain ⟨L₀, hL₀⟩ := hC1
  have htop : wordSpan A L₀ = ⊤ := hL₀
  have hN : finrank ℂ (BM D) = D * D := by
    show Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) = D * D
    rw [Module.finrank_matrix]
    simp
  have hupper : ∀ r, finrank ℂ (wordSpan A r) ≤ D * D := by
    intro r
    have h1 : finrank ℂ (wordSpan A r) ≤ finrank ℂ (BM D) := Submodule.finrank_le _
    rwa [hN] at h1
  have key : finrank ℂ (wordSpan A (D ^ 2)) = D * D := by
    rcases lt_or_ge (finrank ℂ (wordSpan A (D ^ 2))) (D * D) with hlt | hge
    · exfalso
      have hD : D ≠ 0 := by
        rintro rfl
        simp at hlt
      have hstrict : ∀ r, r < D ^ 2 →
          finrank ℂ (wordSpan A r) < finrank ℂ (wordSpan A (r + 1)) := by
        intro r hr
        rcases lt_or_eq_of_le (finrank_le_succ A h0 r) with hlt' | heq
        · exact hlt'
        · exfalso
          have htopr : wordSpan A r = ⊤ := wordSpan_eq_top_of_stable A h0 htop heq.symm
          have hmono : finrank ℂ (wordSpan A r) ≤ finrank ℂ (wordSpan A (D ^ 2)) :=
            finrank_mono_of_le A h0 (le_of_lt hr)
          rw [htopr, finrank_top, hN] at hmono
          omega
      have hlin : ∀ k, k ≤ D ^ 2 →
          finrank ℂ (wordSpan A 0) + k ≤ finrank ℂ (wordSpan A k) := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
            intro hk
            have hk' : k < D ^ 2 := Nat.lt_of_succ_le hk
            have h1 : finrank ℂ (wordSpan A 0) + k ≤ finrank ℂ (wordSpan A k) :=
              ih (le_of_lt hk')
            have h2 : finrank ℂ (wordSpan A k) + 1 ≤ finrank ℂ (wordSpan A (k + 1)) :=
              Nat.succ_le_of_lt (hstrict k hk')
            calc finrank ℂ (wordSpan A 0) + (k + 1)
                = finrank ℂ (wordSpan A 0) + k + 1 := by omega
              _ ≤ finrank ℂ (wordSpan A k) + 1 := Nat.add_le_add_right h1 1
              _ ≤ finrank ℂ (wordSpan A (k + 1)) := h2
      have hDpos : 0 < D := Nat.pos_of_ne_zero hD
      have hf0 : finrank ℂ (wordSpan A 0) = 1 := wordSpan_zero_finrank A hDpos
      have hlin' := hlin (D ^ 2) le_rfl
      rw [hf0] at hlin'
      have hpow : D ^ 2 = D * D := Nat.pow_two D
      omega
    · exact le_antisymm (hupper _) hge
  have hfinal : finrank ℂ (wordSpan A (D ^ 2)) = finrank ℂ (BM D) := by
    rw [key, hN]
  exact Submodule.eq_top_of_finrank_eq hfinal

/-- The proposition that a universal positive integer `C` makes length `C * D ^ 2` products span
the matrix space for every family satisfying `TICanonicalForm`. -/
def Conjecture2 : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (d D : ℕ), NeZero d → ∀ A : Fin d → BM D,
    TICanonicalForm A → C1At A (C * D ^ 2)

/-- The amplitude function supported on configurations with exactly one entry equal to one, with
amplitude `1 / sqrt N`. -/
noncomputable def WState (N : ℕ) : Ket N 2 :=
  fun x => if (Finset.univ.filter fun k : Fin N => x k = 1).card = 1 then
      (1 : ℂ) / (Real.sqrt N : ℂ)
    else 0

/-- The proposition that `D` is bounded below by a positive constant times `N ^ (1 / 3)`,
parameterized by the conjectural bound and a canonical representation of the W state. -/
def corollary1_w_state  (_hC2 : Conjecture2) {N D : ℕ} (hN : 3 ≤ N) [NeZero D]
    (A : Fin 2 → BM D) (_hcanon : TICanonicalForm A)
    (_hrep : ∀ x, @tiAmplitude N 2 D (⟨by omega⟩ : NeZero N) ‹NeZero D› A x = WState N x) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c * (N : ℝ) ^ (1 / 3 : ℝ) ≤ (D : ℝ)

/-- The complex inner product on amplitude functions, conjugate linear in its first argument. -/
def inner {N d : ℕ} (φ ψ : Ket N d) : ℂ := ∑ x, starRingEnd ℂ (φ x) * ψ x

/-- The cyclic window of length `L` beginning at `i` in a chain of length `N`, taken to be empty
when `N = 0`. -/
def window (N L i : ℕ) : Finset (Fin N) :=
  if 0 < N then
    Finset.univ.filter (fun j : Fin N => ∃ t : Fin L, j.val = (i + t.val) % N)
  else ∅

/-- The condition that `(T φ) x` vanishes whenever `φ` vanishes on every configuration agreeing
with `x` outside `S`. -/
def DependsOnlyOn {N d : ℕ} (S : Finset (Fin N)) (T : Ket N d →ₗ[ℂ] Ket N d) : Prop :=
  ∀ (φ : Ket N d) (x : Fin N → Fin d),
    (∀ y : Fin N → Fin d, (∀ i, i ∉ S → y i = x i) → φ y = 0) → (T φ) x = 0

/-- The condition that `H` annihilates `ψ`, has nonnegative real quadratic form, and decomposes
into terms with nonnegative real quadratic forms satisfying `DependsOnlyOn` on cyclic
windows. -/
def IsLocalTIFrustrationFree {N d : ℕ} (L : ℕ) (H : Ket N d →ₗ[ℂ] Ket N d) (ψ : Ket N d) : Prop :=
  H ψ = 0 ∧ (∀ φ, 0 ≤ (inner φ (H φ)).re) ∧
    ∃ terms : Fin N → Ket N d →ₗ[ℂ] Ket N d,
      H = ∑ i, terms i ∧
        (∀ i, DependsOnlyOn (window N L i.val) (terms i)) ∧
        (∀ (i : Fin N) (φ : Ket N d), 0 ≤ (inner φ (terms i φ)).re)

/-- The proposition that the bond dimensions are uniformly bounded or exceed arbitrarily large
positive multiples of the cube root of the chain length, parameterized by the stated
canonical and local ground state data. -/
def theorem20_dichotomy  (_hC2 : Conjecture2) {d : ℕ} [NeZero d] {L : ℕ}
    (D : ℕ → ℕ) (hDnz : ∀ n, NeZero (D n))
    (A : (n : ℕ) → Fin d → BM (D n))
    (H : (n : ℕ) → Ket (n + 1) d →ₗ[ℂ] Ket (n + 1) d)
    (_hFF : ∀ n, IsLocalTIFrustrationFree L (H n)
      (fun x => @tiAmplitude (n + 1) d (D n) (⟨Nat.succ_ne_zero n⟩ : NeZero (n + 1))
        (hDnz n) (A n) x))
    (_hcanon : ∀ n, TICanonicalForm (A n)) : Prop :=
  (∃ D₀ : ℕ, ∀ n, D n ≤ D₀) ∨
      (∀ c : ℝ, 0 < c → ∃ n : ℕ, c * ((n : ℝ) + 1) ^ (1 / 3 : ℝ) ≤ (D n : ℝ))
end Qatlib.Papers.MatrixProd07.MainResults.Appendix
