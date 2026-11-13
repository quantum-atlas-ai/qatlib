/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgGraph15.MainResults.SourceSpanPrograms
import Mathlib.Analysis.Complex.Norm
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

set_option backward.isDefEq.respectTransparency false

/-!
# Span Program `P₁` for Graph Bipartiteness

This module formalizes the correctness and witness-size analysis of the span
program `P₁` for graph bipartiteness in Section 3 (Algorithm 1, Eqs. (1)-(3))
of Āriņš.

## Main statements

* `bipTarget_not_mem_of_isBipartite`: on any bipartite graph `G`, the target
  vector does not lie in the span of the available program vectors.
* `negNorm_bipColWit_le` and `negNorm_bipColWit_le_twelve`: `O(n ^ 3)` negative
  witness size bounds for the 2-coloring witness `bipColWit` (Eq. (2)).
* `bipTarget_mem_span_of_not_isBipartite`: on any non-bipartite graph `G`, the
  target vector lies in the span of the available program vectors.
* `bip_posWitness_norm_le_two`: on any non-bipartite graph `G`, there exists a
  positive witness of squared norm at most `2`, obtained by averaging rotations
  of a shortest odd cycle (Eq. (1)).
* `bip_witnessSize_bound`: `O(n √n)` combined witness-size bound (Eq. (3)).

## References

* [Arins, 2015][Arins2015], Section 3, Algorithm 1, Eqs. (1)-(3).
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Finset

namespace Qatlib.Papers.SpanProgGraph15.MainResults

/-! ## Pairing against basis vectors -/

/-- Complex conjugation fixes real scalars coerced to `ℂ`. -/
theorem star_ofReal (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- Pairing `⟨u|·⟩` against a scaled computational basis vector `Pi.single i c`. -/
theorem pair_single {H : Type} [Fintype H] [DecidableEq H] (u : H → ℂ) (i : H) (c : ℂ) :
    pair u (Pi.single i c) = star (u i) * c := by
  unfold pair
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Pairing against `P₁`'s special target basis vector `|0⟩`. -/
theorem pair_bipZero {n : ℕ} (u : BipBasis n → ℂ) :
    pair u (bipZero n) = star (u (Sum.inl ())) := by
  simp [bipZero, pair_single]

/-! ## The 2-coloring negative witness -/

/-- The `±1` sign associated with a Boolean vertex color. -/
def colSign {n : ℕ} (s : Fin n → Bool) (v : Fin n) : ℝ := if s v then -1 else 1

/-- Every color sign squares to `1`. -/
theorem colSign_sq {n : ℕ} (s : Fin n → Bool) (v : Fin n) :
    colSign s v * colSign s v = 1 := by
  unfold colSign
  split <;> norm_num

/-- Every color sign is nonzero. -/
theorem colSign_ne_zero {n : ℕ} (s : Fin n → Bool) (v : Fin n) : colSign s v ≠ 0 := by
  unfold colSign
  split <;> norm_num

/-- Distinct Boolean colors receive opposite signs. -/
theorem colSign_eq_neg {n : ℕ} {s : Fin n → Bool} {u v : Fin n} (h : s u ≠ s v) :
    colSign s u = - colSign s v := by
  unfold colSign
  cases hu : s u <;> cases hv : s v <;> simp_all

/-- Negative witness attached to a Boolean 2-coloring `s`: `1` on `|0⟩`,
`-(colSign s k * colSign s v)` on `|v_{k,b}⟩` when `b = s v`, and `0` elsewhere. -/
def bipColWit {n : ℕ} (s : Fin n → Bool) : BipBasis n → ℂ
  | Sum.inl () => 1
  | Sum.inr (v, b, k) => ((if b = s v then -(colSign s k * colSign s v) else 0 : ℝ) : ℂ)

/-- The coloring witness pairs to `1` with `|0⟩`. -/
theorem pair_bipColWit_zero {n : ℕ} (s : Fin n → Bool) :
    pair (bipColWit s) (bipZero n) = 1 := by
  rw [pair_bipZero]
  simp [bipColWit]

/-- Every free block vector pairs to `0` with the coloring witness. -/
theorem pair_bipColWit_free {n : ℕ} (s : Fin n → Bool) (k : Fin n) :
    pair (bipColWit s) (bipFree n k) = 0 := by
  simp only [bipFree, bipZero, bipBasisVec]
  rw [pair_add, pair_add, pair_single, pair_single, pair_single]
  cases hk : s k <;> simp [bipColWit, colSign, hk]

/-- Any `0`-parity edge vector between oppositely colored vertices pairs to `0`
with `bipColWit s`. -/
theorem pair_bipColWit_edge0 {n : ℕ} {s : Fin n → Bool} {k : Fin n} {u v : Fin n}
    (h : s u ≠ s v) : pair (bipColWit s) (bipEdge0 n k u v) = 0 := by
  simp only [bipEdge0, bipBasisVec]
  rw [pair_add, pair_single, pair_single]
  unfold bipColWit colSign
  cases hu : s u <;> cases hv : s v <;> simp_all

/-- Any `1`-parity edge vector between oppositely colored vertices pairs to `0`
with `bipColWit s`. -/
theorem pair_bipColWit_edge1 {n : ℕ} {s : Fin n → Bool} {k : Fin n} {u v : Fin n}
    (h : s u ≠ s v) : pair (bipColWit s) (bipEdge1 n k u v) = 0 := by
  simp only [bipEdge1, bipBasisVec]
  rw [pair_add, pair_single, pair_single]
  unfold bipColWit colSign
  cases hu : s u <;> cases hv : s v <;> simp_all

/-- `bipColWit s` is a valid negative witness whenever `s` properly 2-colors `G`. -/
theorem bipColWit_isNeg {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) :
    NegWitnessData (bipGenVec n) (bipGenAvail n G) (bipTarget n) (bipColWit s) := by
  refine ⟨pair_bipColWit_zero s, ?_⟩
  intro i hi
  rcases i with k | ⟨k, b, u, v⟩
  · exact pair_bipColWit_free s k
  · cases b
    · exact pair_bipColWit_edge0 (k := k) (u := u) (v := v) (hs u v hi)
    · exact pair_bipColWit_edge1 (k := k) (u := u) (v := v) (hs u v hi)

/-- On any bipartite graph `G`, the target `bipTarget n` is outside `bipSpan n G`. -/
theorem bipTarget_not_mem_of_isBipartite {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsBipartite) : bipTarget n ∉ bipSpan n G := by
  obtain ⟨C⟩ := hG
  refine not_mem_span_of_negWitness (bipColWit_isNeg G (fun v => decide (C v = 0)) ?_)
  intro u v huv
  exact (by
    have hne : C u ≠ C v := C.valid huv
    have key : ∀ x y : Fin 2, x ≠ y → decide (x = 0) ≠ decide (y = 0) := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    exact key (C u) (C v) hne)

/-! ## Negative witness size (Eq. (2)) -/

/-- Every program vector pairs with `bipColWit s` to norm at most `2`. -/
theorem norm_pair_bipColWit_gen_le {n : ℕ} (s : Fin n → Bool) (i : BipGen n) :
    ‖pair (bipColWit s) (bipGenVec n i)‖ ≤ 2 := by
  rcases i with k | ⟨k, b, u, v⟩
  · rw [bipGenVec, pair_bipColWit_free]
    norm_num
  · simp only [bipGenVec]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      simp only [bipEdge0, bipBasisVec]
      rw [pair_add, pair_single, pair_single]
      cases hu : s u <;> cases hv : s v <;>
        simp [bipColWit, colSign, hu, hv, star_ofReal, Complex.norm_real, Real.norm_eq_abs] <;>
        split <;> norm_num
    · simp only [ite_true]
      simp only [bipEdge1, bipBasisVec]
      rw [pair_add, pair_single, pair_single]
      cases hu : s u <;> cases hv : s v <;>
        simp [bipColWit, colSign, hu, hv, star_ofReal, Complex.norm_real, Real.norm_eq_abs] <;>
        split <;> norm_num

/-- Negative witness size bound `negNorm ≤ 4 * (n + 2 * n ^ 3)` (Eq. (2)). -/
theorem negNorm_bipColWit_le {n : ℕ} (s : Fin n → Bool) :
    negNorm (bipGenVec n) (bipColWit s) ≤ 4 * (n + 2 * n ^ 3 : ℝ) := by
  have hb : (Fintype.card (BipGen n) : ℝ) = ((n : ℝ) + 2 * (n : ℝ) ^ 3) := by
    rw [card_bipGen]
    push_cast
    ring
  calc negNorm (bipGenVec n) (bipColWit s)
      = ∑ i, ‖pair (bipColWit s) (bipGenVec n i)‖ ^ 2 := rfl
    _ ≤ ∑ _i : BipGen n, (4 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := norm_pair_bipColWit_gen_le s i
        have h2 : (0 : ℝ) ≤ ‖pair (bipColWit s) (bipGenVec n i)‖ := norm_nonneg _
        nlinarith
    _ = 4 * (Fintype.card (BipGen n) : ℝ) := by
        simp [Finset.sum_const, mul_comm]
    _ = 4 * ((n : ℝ) + 2 * (n : ℝ) ^ 3) := by rw [hb]

/-- Homogeneous `O(n ^ 3)` negative witness size bound for `n ≥ 1`. -/
theorem negNorm_bipColWit_le_twelve {n : ℕ} (hn : 1 ≤ n) (s : Fin n → Bool) :
    negNorm (bipGenVec n) (bipColWit s) ≤ 12 * (n : ℝ) ^ 3 := by
  refine le_trans (negNorm_bipColWit_le s) ?_
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-! ## Positive witness size (Eq. (1)) -/

private theorem bip_shortest_odd_walk {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬ G.IsBipartite) :
    ∃ (u : Fin n) (w : G.Walk u u), Odd w.length ∧
      Function.Injective (fun i : Fin w.length => w.getVert i.val) := by
  have hex : ∃ d : ℕ, Odd d ∧ ∃ (u : Fin n) (w : G.Walk u u), w.length = d := by
    have h := mt SimpleGraph.two_colorable_iff_forall_loop_even.mpr hG
    push Not at h
    obtain ⟨u, w, hw⟩ := h
    exact ⟨w.length, Nat.not_even_iff_odd.mp hw, u, w, rfl⟩
  obtain ⟨ho, u, w, hw⟩ := Nat.find_spec hex
  have hmin (x : Fin n) (p : G.Walk x x) (hp : p.length < w.length) :
      Even p.length := by
    apply Nat.not_odd_iff_even.mp
    intro hodd
    exact Nat.find_min hex (hw ▸ hp) ⟨hodd, x, p, rfl⟩
  refine ⟨u, w, hw ▸ ho, ?_⟩
  have hne (i j : Fin w.length) (hij : i.val < j.val)
      (heq : w.getVert i.val = w.getVert j.val) : False := by
    let mid : G.Walk (w.getVert i.val) (w.getVert i.val) :=
      ((w.drop i.val).take (j.val - i.val)).copy rfl
      (by rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij.le]; exact heq.symm)
    let outer := (w.drop j.val).append ((w.take i.val).copy rfl heq)
    have hm : mid.length = j.val - i.val := by
      simp [mid]
    have hout : outer.length = w.length - j.val + i.val := by
      simp [outer]
    have h₁ := hmin _ mid (by rw [hm]; omega)
    have h₂ := hmin _ outer (by rw [hout]; omega)
    have heven : Even w.length := by
      convert h₁.add h₂ using 1
      rw [hm, hout]
      omega
    exact (Nat.not_even_iff_odd.mpr (hw ▸ ho)) heven
  intro i j hij
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hne i j hlt hij
  · exact hne j i hgt hij.symm

open Fin.NatCast

private theorem bip_cycle_telescope {n d : ℕ} [NeZero d]
    (v : Fin d → Fin n) (r : Fin d) (m : ℕ) :
    bipFree n (v r) +
        ∑ t ∈ Finset.range m, ((-1 : ℂ) ^ (t + 1)) •
          bipGenVec n (Sum.inr (v r, decide (t % 2 = 1),
            (v (r + (t : Fin d)), v (r + ((t + 1 : ℕ) : Fin d))))) =
      bipZero n + bipBasisVec n (v r) true (v r) +
        ((-1 : ℂ) ^ m) •
          bipBasisVec n (v (r + (m : Fin d))) (decide (m % 2 = 1)) (v r) := by
  induction m with
  | zero => simp [bipFree, add_comm, add_left_comm]
  | succ m ih =>
    have he : bipGenVec n (Sum.inr (v r, decide (m % 2 = 1),
        (v (r + (m : Fin d)), v (r + ((m + 1 : ℕ) : Fin d))))) =
        bipBasisVec n (v (r + (m : Fin d))) (decide (m % 2 = 1)) (v r) +
          bipBasisVec n (v (r + ((m + 1 : ℕ) : Fin d)))
            (decide ((m + 1) % 2 = 1)) (v r) := by
      have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases hm with hm | hm <;>
        simp [bipGenVec, bipEdge0, bipEdge1, hm, Nat.add_mod]
    rw [Finset.sum_range_succ, ← add_assoc, ih, he]
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

private theorem bip_cycle_witness {n d : ℕ} [NeZero d] {G : SimpleGraph (Fin n)}
    (ho : Odd d) (v : Fin d → Fin n) (hv : Function.Injective v)
    (ha : ∀ t : Fin d, G.Adj (v t) (v (t + 1))) :
    ∃ c : BipGen n → ℂ,
      PosWitnessData (bipGenVec n) (bipGenAvail n G) (bipTarget n) c ∧ posNorm c ≤ 2 := by
  let f : Fin d ⊕ (Fin d × Fin d) → BipGen n
    | Sum.inl r => Sum.inl (v r)
    | Sum.inr (r, t) => Sum.inr (v r, decide (t.val % 2 = 1),
        (v (r + t), v (r + (t + 1))))
  have hf : Function.Injective f := by
    intro x y h
    rcases x with r | ⟨r, t⟩ <;> rcases y with s | ⟨s, u⟩
    · exact congrArg Sum.inl (hv (Sum.inl.inj h))
    · simp [f] at h
    · simp [f] at h
    · simp only [f, Sum.inr.injEq, Prod.mk.injEq] at h
      have hrs := hv h.1
      subst s
      have htu : t = u := add_left_cancel (hv h.2.2.1)
      subst u
      rfl
  let q : ℂ := (d : ℂ)⁻¹
  let a : Fin d ⊕ (Fin d × Fin d) → ℂ
    | Sum.inl _ => q
    | Sum.inr (_, t) => q * (-1) ^ (t.val + 1)
  let c : BipGen n → ℂ := Function.extend f a 0
  have hc (j : Fin d ⊕ (Fin d × Fin d)) : c (f j) = a j :=
    hf.extend_apply a 0 j
  have hz (i : BipGen n) (hi : i ∉ Set.range f) : c i = 0 :=
    Function.extend_apply' (f := f) a (0 : BipGen n → ℂ) i hi
  have htel (r : Fin d) :
      bipFree n (v r) + ∑ t : Fin d, ((-1 : ℂ) ^ (t.val + 1)) •
        bipGenVec n (f (Sum.inr (r, t))) = bipTarget n := by
    have ht := bip_cycle_telescope v r d
    rw [← Fin.sum_univ_eq_sum_range] at ht
    simpa [f, bipTarget, Fin.cast_val_eq_self, ho.neg_one_pow, Nat.odd_iff.mp ho,
      Nat.cast_add, add_assoc] using ht
  have hcomb : (∑ j, a j • bipGenVec n (f j)) = bipTarget n := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [a, f, bipGenVec]
    have heq : (∑ r : Fin d, q • bipFree n (v r)) +
        (∑ r : Fin d, ∑ t : Fin d, (q * (-1 : ℂ) ^ (t.val + 1)) •
          bipGenVec n (f (Sum.inr (r, t)))) =
        ∑ r : Fin d, q • (bipFree n (v r) +
          ∑ t : Fin d, ((-1 : ℂ) ^ (t.val + 1)) •
            bipGenVec n (f (Sum.inr (r, t)))) := by
      simp only [smul_add, Finset.smul_sum, mul_smul, Finset.sum_add_distrib]
    change (∑ r : Fin d, q • bipFree n (v r)) +
      (∑ r : Fin d, ∑ t : Fin d, (q * (-1 : ℂ) ^ (t.val + 1)) •
        bipGenVec n (f (Sum.inr (r, t)))) = _
    rw [heq]
    simp only [htel, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    simp [q, NeZero.ne d]
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases hir : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hir
      rcases j with r | ⟨r, t⟩
      · trivial
      · simpa [f, bipGenAvail, add_assoc] using ha (r + t)
    · exact (hi (hz i hir)).elim
  · rw [← hcomb]
    exact (Fintype.sum_of_injective f hf _ _
      (fun i hi => by rw [hz i hi]; simp) (fun j => by rw [hc j])).symm
  · have hn (j : Fin d ⊕ (Fin d × Fin d)) : ‖a j‖ ^ 2 = ((d : ℝ)⁻¹) ^ 2 := by
      rcases j with r | ⟨r, t⟩ <;> simp [a, q, norm_pow]
    have hs : posNorm c = ∑ j, ‖a j‖ ^ 2 := by
      exact (Fintype.sum_of_injective f hf _ _
        (fun i hi => by rw [hz i hi]; simp) (fun j => by rw [hc j])).symm
    rw [hs]
    simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    push_cast
    field_simp
    nlinarith

/-- On any non-bipartite graph `G`, there exists a positive witness of squared
norm at most `2` (Eq. (1)). -/
theorem bip_posWitness_norm_le_two {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬ G.IsBipartite) :
    ∃ c : BipGen n → ℂ,
      PosWitnessData (bipGenVec n) (bipGenAvail n G) (bipTarget n) c ∧ posNorm c ≤ 2 := by
  obtain ⟨u, w, ho, hv⟩ := bip_shortest_odd_walk hG
  have hd : 0 < w.length := by obtain ⟨a, ha⟩ := ho; omega
  let : NeZero w.length := ⟨by omega⟩
  refine bip_cycle_witness ho (fun t : Fin w.length => w.getVert t.val) hv ?_
  intro t
  have ht := w.adj_getVert_succ t.isLt
  have he : t + 1 = ((t.val + 1 : ℕ) : Fin w.length) := by simp
  rw [he]
  change G.Adj (w.getVert t.val) (w.getVert ((t.val + 1) % w.length))
  by_cases h : t.val + 1 < w.length
  · simpa [Nat.mod_eq_of_lt h] using ht
  · have heq : t.val + 1 = w.length := by omega
    simpa [heq] using ht

/-- On any non-bipartite graph `G`, the target `bipTarget n` lies in `bipSpan n G`. -/
theorem bipTarget_mem_span_of_not_isBipartite {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬ G.IsBipartite) : bipTarget n ∈ bipSpan n G := by
  obtain ⟨c, hc, _⟩ := bip_posWitness_norm_le_two hG
  exact mem_span_of_posWitness hc

/-! ## Combined witness size (Eq. (3)) -/

/-- Combining the negative witness bound of Eq. (2) with the positive witness
bound of Eq. (1) yields `√(4 * (n + 2 * n ^ 3) * 2) ≤ 5 * n * √n` (Eq. (3)). -/
theorem bip_witnessSize_bound {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (4 * ((n : ℝ) + 2 * (n : ℝ) ^ 3) * 2) ≤ 5 * (n : ℝ) * Real.sqrt n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrew : 4 * ((n : ℝ) + 2 * (n : ℝ) ^ 3) * 2 = 8 * ((n : ℝ) + 2 * (n : ℝ) ^ 3) := by
    ring
  rw [hrew]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hsq : (5 * (n : ℝ) * Real.sqrt n) ^ 2 = 25 * (n : ℝ) ^ 3 := by
      have h : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith
    rw [hsq]
    have hn2 : (1 : ℝ) ≤ (n : ℝ) * n := by nlinarith
    nlinarith

end Qatlib.Papers.SpanProgGraph15.MainResults
