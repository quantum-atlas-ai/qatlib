/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KikuchiMaxCut26.MainResults.Proposition22
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option backward.isDefEq.respectTransparency false

/-!
# Sharp Laplacian Eigenvalue Bound for Kikuchi Graphs

This module proves Theorem 3.1: for any graph `G` on `n` vertices with `m` edges,
any level `0 ≤ k ≤ n`, and any sign `b ∈ {-1, 1}`, the largest eigenvalue of
the Kikuchi Laplacian family `L_{b,G}^{(k)} = D_G^{(k)} + b A_G^{(k)}` satisfies
`λ_max(L_{b,G}^{(k)}) ≤ m + k`.

## Main statements

* `signedLaplacian_isSymm`, `signedLaplacian_isHermitian`: symmetry and Hermiticity of `L_{b,G}^{(k)}`.
* `signedLaplacian_neg_one`, `signedLaplacian_one`: specialization to `L_G^{(k)}` and `Q_G^{(k)}`.
* `theorem_3_1`: sharp upper bound `lamMax (signedLaplacian G k b) _ ≤ edgeCount G + k`.

## References

* [Bakshi et al., 2026][BakshiEtAl2026Kikuchi], Theorem 3.1, pp. 3--6.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KikuchiMaxCut26.MainResults

variable {n : ℕ}

/-- The one-parameter family `L_{b,G}^{(k)} = D_G^{(k)} + b A_G^{(k)}` is symmetric for every real `b`. -/
theorem signedLaplacian_isSymm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (b : ℝ) : (signedLaplacian G k b).IsSymm := by
  classical
  simp only [signedLaplacian, degMatrix, adjMatrix]
  exact ((kikuchiGraph G k).isSymm_degMatrix ℝ).add
    (((kikuchiGraph G k).isSymm_adjMatrix).smul b)

/-- The family `L_{b,G}^{(k)}` is Hermitian for every real `b`. -/
theorem signedLaplacian_isHermitian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (b : ℝ) : (signedLaplacian G k b).IsHermitian :=
  signedLaplacian_isSymm G k b

/-- `L_{-1,G}^{(k)} = L_G^{(k)}`, the signed Laplacian. -/
theorem signedLaplacian_neg_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    signedLaplacian G k (-1) = lapMatrix G k := by
  classical
  simp [signedLaplacian, lapMatrix, degMatrix, adjMatrix, SimpleGraph.lapMatrix,
    sub_eq_add_neg]

/-- `L_{1,G}^{(k)} = Q_G^{(k)}`, the signless Laplacian. -/
theorem signedLaplacian_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    signedLaplacian G k 1 = signlessMatrix G k := by
  classical
  simp [signedLaplacian, signlessMatrix, one_smul]

/-! The auxiliary operators act on all subsets.  Deleting vertices therefore does not
change the ambient vector space. -/

private def swapSet {V : Type*} [DecidableEq V] (i j : V) : Finset V ≃ Finset V :=
  (Equiv.swap i j).finsetCongr

private lemma mem_swapSet {V : Type*} [DecidableEq V] (i j v : V) (S : Finset V) :
    v ∈ swapSet i j S ↔ Equiv.swap i j v ∈ S := by
  change v ∈ S.map (Equiv.swap i j).toEmbedding ↔ _
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨Equiv.swap i j v, h, by simp⟩

private lemma swapSet_insert {V : Type*} [DecidableEq V] (i j v : V) (S : Finset V) :
    swapSet i j (insert v S) = insert (Equiv.swap i j v) (swapSet i j S) := by
  exact Finset.map_insert _ _ _

private lemma swapSet_self {V : Type*} [DecidableEq V] (i j : V) (S : Finset V)
    (h : i ∈ S ↔ j ∈ S) : swapSet i j S = S := by
  ext v
  rw [mem_swapSet]
  by_cases hi : v = i
  · subst v; simpa using h.symm
  by_cases hj : v = j
  · subst v; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hi hj]

private lemma swapSet_swapSet {V : Type*} [DecidableEq V] (i j : V) (S : Finset V) :
    swapSet i j (swapSet i j S) = S := by
  ext v
  simp only [mem_swapSet, Equiv.swap_apply_self]

private lemma swapSet_symm {V : Type*} [DecidableEq V] (i j : V) :
    swapSet i j = swapSet j i := by
  simp only [swapSet, Equiv.swap_comm]

private def edgeOp {V : Type*} [DecidableEq V] (b : ℝ) (i j : V)
    (x : Finset V → ℝ) (S : Finset V) : ℝ :=
  if (i ∈ S ∧ j ∉ S) ∨ (j ∈ S ∧ i ∉ S) then x S + b * x (swapSet i j S) else 0

private def gradient {V : Type*} [DecidableEq V] (b : ℝ) (i j : V)
    (x : Finset V → ℝ) (S : Finset V) : ℝ :=
  if i ∉ S ∧ j ∉ S then x (insert i S) + b * x (insert j S) else 0

private lemma edgeOp_symm {V : Type*} [DecidableEq V] (b : ℝ) (i j : V)
    (x : Finset V → ℝ) : edgeOp b i j x = edgeOp b j i x := by
  funext S
  simp only [edgeOp, swapSet_symm i j, or_comm]

private lemma gradient_symm {V : Type*} [DecidableEq V] (b : ℝ) (hb : b ^ 2 = 1) (i j : V)
    (x : Finset V → ℝ) : gradient b j i x = fun S => b * gradient b i j x S := by
  funext S
  by_cases h : i ∉ S ∧ j ∉ S
  · simp only [gradient, h.1, h.2, not_false_eq_true, and_self, ite_true]
    linear_combination -x (insert j S) * hb
  · have h' : ¬ (j ∉ S ∧ i ∉ S) := by tauto
    simp [gradient, h, h']

private lemma gradient_edge_self {V : Type*} [DecidableEq V] (b : ℝ) (hb : b ^ 2 = 1)
    (i j : V) (hij : i ≠ j)
    (x : Finset V → ℝ) (S : Finset V) :
    gradient b i j (edgeOp b i j x) S = 2 * gradient b i j x S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [gradient, hi]
  · simp [gradient, hi]
  · simp [gradient, hj]
  · have hs := swapSet_self i j S (by simp [hi, hj])
    simp [gradient, edgeOp, hi, hj, hij, hij.symm, swapSet_insert, hs]
    linear_combination x (insert i S) * hb

private lemma gradient_edge_disjoint {V : Type*} [DecidableEq V] (b : ℝ) (i j u v : V)
    (hiu : i ≠ u) (hiv : i ≠ v) (hju : j ≠ u) (hjv : j ≠ v)
    (x : Finset V → ℝ) (S : Finset V) :
    gradient b i j (edgeOp b u v x) S = edgeOp b u v (gradient b i j x) S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [gradient, edgeOp, hi, hj, hu, hv, hiu, hiv, hju, hjv,
      hiu.symm, hiv.symm, hju.symm, hjv.symm, mem_swapSet, swapSet_insert,
      Equiv.swap_apply_of_ne_of_ne] <;> ring

private lemma gradient_edge_incident {V : Type*} [DecidableEq V] (b : ℝ) (hb : b ^ 2 = 1)
    (i j w : V)
    (hij : i ≠ j) (hiw : i ≠ w) (hjw : j ≠ w)
    (x : Finset V → ℝ) (S : Finset V) :
    gradient b i j (edgeOp b i w x) S = gradient b i w x (swapSet j w S) := by
  have hset : ∀ T : Finset V, i ∉ T → j ∉ T → w ∈ T →
      insert i (swapSet j w T) = swapSet i w (insert j T) ∧
        insert w (swapSet j w T) = insert j T := by
    intro T hi hj hw
    constructor <;> ext z <;>
      by_cases hzi : z = i <;> by_cases hzj : z = j <;> by_cases hzw : z = w <;>
      simp_all [mem_swapSet, Equiv.swap_apply_def]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> by_cases hw : w ∈ S
  all_goals try simp [gradient, edgeOp, hi, hj, hw, hij, hiw, hjw,
    hij.symm, hiw.symm, hjw.symm, mem_swapSet, swapSet_insert,
    Equiv.swap_apply_of_ne_of_ne]
  · obtain ⟨h1, h2⟩ := hset S hi hj hw
    simp only [h1, h2, swapSet_insert, Equiv.swap_apply_of_ne_of_ne hij.symm hjw,
      ]
    linear_combination x (insert j (swapSet i w S)) * hb
  · have hs := swapSet_self j w S (by simp [hj, hw])
    have hs' := swapSet_self i w S (by simp [hi, hw])
    rw [hs, hs']

private def subsetOp {V : Type*} [Fintype V] [DecidableEq V] (b : ℝ) (G : SimpleGraph V)
    (x : Finset V → ℝ) (S : Finset V) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ i, ∑ j, if G.Adj i j then edgeOp b i j x S else 0

private def deletedGraph {V : Type*} (G : SimpleGraph V) (i j : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ≠ i ∧ u ≠ j ∧ v ≠ i ∧ v ≠ j
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩⟩
  loopless := ⟨fun u h => G.irrefl h.1⟩

private lemma swapSet_card {V : Type*} [DecidableEq V] (i j : V) (S : Finset V) :
    (swapSet i j S).card = S.card := by
  exact Finset.card_map _

private lemma swapSet_sdiff {V : Type*} [DecidableEq V] (i j : V) (S : Finset V)
    (hi : i ∈ S) (hj : j ∉ S) :
    S \ swapSet i j S = {i} ∧ swapSet i j S \ S = {j} := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  constructor <;> ext z <;> by_cases hzi : z = i <;> by_cases hzj : z = j <;>
    simp_all [mem_swapSet, Equiv.swap_apply_def]

private lemma swapSet_of_sdiff {V : Type*} [DecidableEq V] (i j : V) (S T : Finset V)
    (h1 : S \ T = {i}) (h2 : T \ S = {j}) :
    i ∈ S ∧ j ∉ S ∧ swapSet i j S = T := by
  have hi : i ∈ S ∧ i ∉ T := by simpa only [Finset.mem_sdiff] using
    (show i ∈ S \ T by rw [h1]; exact Finset.mem_singleton_self _)
  have hj : j ∈ T ∧ j ∉ S := by simpa only [Finset.mem_sdiff] using
    (show j ∈ T \ S by rw [h2]; exact Finset.mem_singleton_self _)
  refine ⟨hi.1, hj.2, ?_⟩
  ext z
  by_cases hzi : z = i
  · subst z; simp [mem_swapSet, hi.2, hj.2]
  by_cases hzj : z = j
  · subst z; simp [mem_swapSet, hi.1, hj.1]
  have hz1 : ¬ (z ∈ S ∧ z ∉ T) := by
    rw [← Finset.mem_sdiff, h1, Finset.mem_singleton]; exact hzi
  have hz2 : ¬ (z ∈ T ∧ z ∉ S) := by
    rw [← Finset.mem_sdiff, h2, Finset.mem_singleton]; exact hzj
  rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hzi hzj]
  tauto

private def crossingPairs {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S

private lemma mem_crossingPairs {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (p : V × V) :
    p ∈ crossingPairs G S ↔ G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S := by
  classical
  simp [crossingPairs]

private lemma subsetOp_crossing {V : Type*} [Fintype V] [DecidableEq V]
    (b : ℝ) (G : SimpleGraph V) (x : Finset V → ℝ) (S : Finset V) :
    subsetOp b G x S = ∑ p ∈ crossingPairs G S, (x S + b * x (swapSet p.1 p.2 S)) := by
  classical
  let f : V → V → ℝ := fun i j =>
    if G.Adj i j ∧ i ∈ S ∧ j ∉ S then x S + b * x (swapSet i j S) else 0
  have hs (i j : V) : (if G.Adj i j then edgeOp b i j x S else 0) = f i j + f j i := by
    by_cases hg : G.Adj i j <;> by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [f, edgeOp, hg, G.adj_comm j i, hi, hj, swapSet_symm i j]
  unfold subsetOp
  simp_rw [hs, Finset.sum_add_distrib]
  have hc : (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := Finset.sum_comm
  rw [hc]
  have hf : (∑ i, ∑ j, f i j) =
      ∑ p ∈ crossingPairs G S, (x S + b * x (swapSet p.1 p.2 S)) := by
    simp [crossingPairs, Finset.sum_filter, Fintype.sum_prod_type, f]
  rw [hf]
  simp only [Finset.sum_add_distrib]
  ring

private def extK {V : Type*} [DecidableEq V] {k : ℕ} (x : KSub V k → ℝ)
    (S : Finset V) : ℝ := if h : S.card = k then x ⟨S, h⟩ else 0

private lemma extK_apply {V : Type*} [DecidableEq V] {k : ℕ} (x : KSub V k → ℝ)
    (S : KSub V k) : extK x S = x S := by simp [extK, S.2]

private lemma subsetOp_mulVec (b : ℝ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (x : KSub (Fin n) k → ℝ) (S : KSub (Fin n) k) :
    subsetOp b G (extK x) S = (signedLaplacian G k b *ᵥ x) S := by
  classical
  rw [subsetOp_crossing]
  have hs : (∑ p ∈ crossingPairs G S.1,
      (extK x S.1 + b * extK x (swapSet p.1 p.2 S.1))) =
      ∑ T ∈ (kikuchiGraph G k).neighborFinset S, (x S + b * x T) := by
    refine Finset.sum_bij
      (fun p _ => (⟨swapSet p.1 p.2 S.1, (swapSet_card _ _ _).trans S.2⟩ : KSub (Fin n) k))
      ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hg, hi, hj⟩ := (mem_crossingPairs G S.1 p).mp hp
      exact ((kikuchiGraph G k).mem_neighborFinset S _).mpr
        ⟨p.1, p.2, hg, (swapSet_sdiff _ _ _ hi hj).1, (swapSet_sdiff _ _ _ hi hj).2⟩
    · intro p hp q hq heq
      obtain ⟨_, hi, hj⟩ := (mem_crossingPairs G S.1 p).mp hp
      obtain ⟨_, hu, hv⟩ := (mem_crossingPairs G S.1 q).mp hq
      have he := congrArg Subtype.val heq
      dsimp only at he
      have h1 := (swapSet_sdiff _ _ _ hi hj).1
      have h2 := (swapSet_sdiff _ _ _ hi hj).2
      rw [he, (swapSet_sdiff _ _ _ hu hv).1] at h1
      rw [he, (swapSet_sdiff _ _ _ hu hv).2] at h2
      exact Prod.ext (Finset.singleton_injective h1).symm (Finset.singleton_injective h2).symm
    · intro T hT
      obtain ⟨i, j, hg, h1, h2⟩ := ((kikuchiGraph G k).mem_neighborFinset S T).mp hT
      obtain ⟨hi, hj, he⟩ := swapSet_of_sdiff i j S.1 T.1 h1 h2
      refine ⟨(i, j), (mem_crossingPairs G S.1 (i, j)).mpr ⟨hg, hi, hj⟩, ?_⟩
      exact Subtype.ext he
    · intro p _
      rw [extK_apply]
      congr 1
      rw [extK, dite_eq_left ((swapSet_card _ _ _).trans S.2)]
  rw [hs, Finset.sum_add_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul, ← Finset.mul_sum]
  simp [signedLaplacian, degMatrix, adjMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    SimpleGraph.degMatrix_mulVec_apply]

private def kInner {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x y : Finset V → ℝ) : ℝ := ∑ S : KSub V k, x S * y S

private def kNormSq {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x : Finset V → ℝ) : ℝ := kInner k x x

private lemma kNormSq_nonneg {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x : Finset V → ℝ) : 0 ≤ kNormSq k x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

private lemma kInner_add {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x y z : Finset V → ℝ) :
    kInner k x (fun S => y S + z S) = kInner k x y + kInner k x z := by
  simp [kInner, mul_add, Finset.sum_add_distrib]

private lemma kInner_mul {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x y : Finset V → ℝ) (c : ℝ) :
    kInner k x (fun S => c * y S) = c * kInner k x y := by
  simp [kInner, Finset.mul_sum, mul_left_comm]

private lemma kInner_sum {V I : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x : Finset V → ℝ) (s : Finset I) (y : I → Finset V → ℝ) :
    kInner k x (fun S => ∑ i ∈ s, y i S) = ∑ i ∈ s, kInner k x (y i) := by
  simp only [kInner, Finset.mul_sum]
  exact Finset.sum_comm

private lemma kInner_le_norms {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (x y : Finset V → ℝ) : 2 * kInner k x y ≤ kNormSq k x + kNormSq k y := by
  simp only [kNormSq, kInner, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun S _ => by nlinarith [sq_nonneg (x S - y S)]

private def swapK {V : Type*} [DecidableEq V] (i j : V) (k : ℕ) : KSub V k ≃ KSub V k where
  toFun S := ⟨swapSet i j S, (swapSet_card _ _ _).trans S.2⟩
  invFun S := ⟨swapSet i j S, (swapSet_card _ _ _).trans S.2⟩
  left_inv S := Subtype.ext (swapSet_swapSet i j S)
  right_inv S := Subtype.ext (swapSet_swapSet i j S)

private lemma kNormSq_swap {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (i j : V) (x : Finset V → ℝ) :
    kNormSq k (fun S => x (swapSet i j S)) = kNormSq k x := by
  exact Equiv.sum_comp (swapK i j k) (fun S => x S.1 * x S.1)

private lemma kNormSq_mul {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (c : ℝ) (x : Finset V → ℝ) :
    kNormSq k (fun S => c * x S) = c ^ 2 * kNormSq k x := by
  simp only [kNormSq, kInner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

private lemma kNormSq_gradient_symm {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (b : ℝ) (hb : b ^ 2 = 1) (i j : V) (x : Finset V → ℝ) :
    kNormSq k (gradient b j i x) = kNormSq k (gradient b i j x) := by
  rw [gradient_symm b hb, kNormSq_mul, hb, one_mul]

private lemma kInner_subsetOp (b : ℝ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (x : Finset (Fin n) → ℝ) :
    kInner k x (subsetOp b G x) =
      (fun S : KSub (Fin n) k => x S) ⬝ᵥ
        (signedLaplacian G k b *ᵥ fun S : KSub (Fin n) k => x S) := by
  have he (S : Finset (Fin n)) (hS : S.card = k) :
      subsetOp b G x S = subsetOp b G (extK (fun T : KSub (Fin n) k => x T)) S := by
    rw [subsetOp_crossing, subsetOp_crossing]
    apply Finset.sum_congr rfl
    intro p _
    simp [extK, hS, swapSet_card]
  unfold kInner dotProduct
  apply Finset.sum_congr rfl
  intro S _
  rw [he S S.2, subsetOp_mulVec b G k _ S]

private def adjPairs (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p => G.Adj p.1 p.2

private def otherNbrs (G : SimpleGraph (Fin n)) (i j : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w => G.Adj i w ∧ w ≠ j

private lemma sum_adjPairs_partition (G : SimpleGraph (Fin n)) {i j : Fin n}
    (hij : G.Adj i j) (f : Fin n → Fin n → ℝ) (hf : ∀ u v, f v u = f u v) :
    (∑ p ∈ adjPairs G, f p.1 p.2) =
      2 * f i j + (∑ p ∈ adjPairs (deletedGraph G i j), f p.1 p.2) +
      2 * (∑ w ∈ otherNbrs G i j, f i w) +
      2 * (∑ w ∈ otherNbrs G j i, f j w) := by
  classical
  have hne := G.ne_of_adj hij
  have hp (u v : Fin n) :
      (if G.Adj u v then f u v else 0) =
        (if u = i ∧ v = j then f i j else 0) +
        (if u = j ∧ v = i then f j i else 0) +
        (if (deletedGraph G i j).Adj u v then f u v else 0) +
        (if u = i ∧ G.Adj i v ∧ v ≠ j then f i v else 0) +
        (if v = i ∧ G.Adj i u ∧ u ≠ j then f u i else 0) +
        (if u = j ∧ G.Adj j v ∧ v ≠ i then f j v else 0) +
        (if v = j ∧ G.Adj j u ∧ u ≠ i then f u j else 0) := by
    by_cases hui : u = i <;> by_cases huj : u = j <;>
      by_cases hvi : v = i <;> by_cases hvj : v = j <;>
      simp_all [deletedGraph, G.adj_comm]
  simp only [adjPairs, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [hp, Finset.sum_add_distrib]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  simp_rw [hf]
  simp only [otherNbrs, Finset.sum_filter, ite_and]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private lemma gradient_subsetOp_sum (b : ℝ) (G : SimpleGraph (Fin n))
    (i j : Fin n) (x : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    gradient b i j (subsetOp b G x) S =
      (1 / 2 : ℝ) * ∑ p ∈ adjPairs G, gradient b i j (edgeOp b p.1 p.2 x) S := by
  classical
  by_cases h : i ∉ S ∧ j ∉ S
  · simp only [gradient, h.1, h.2, not_false_eq_true, and_self, ite_true,
      subsetOp, adjPairs, Finset.sum_filter,
      Fintype.sum_prod_type]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  · simp [gradient, h]

private lemma gradient_subsetOp (b : ℝ) (hb : b ^ 2 = 1) (G : SimpleGraph (Fin n))
    {i j : Fin n} (hadj : G.Adj i j) (x : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) :
    gradient b i j (subsetOp b G x) S =
      2 * gradient b i j x S +
      subsetOp b (deletedGraph G i j) (gradient b i j x) S +
      (∑ w ∈ otherNbrs G i j, gradient b i w x (swapSet j w S)) +
      (∑ w ∈ otherNbrs G j i, b * gradient b j w x (swapSet i w S)) := by
  classical
  rw [gradient_subsetOp_sum, sum_adjPairs_partition G hadj
    (fun u v => gradient b i j (edgeOp b u v x) S)
    (fun u v => congrArg (fun z => gradient b i j z S) (edgeOp_symm b v u x))]
  rw [gradient_edge_self b hb i j (G.ne_of_adj hadj)]
  have hd : (∑ p ∈ adjPairs (deletedGraph G i j),
      gradient b i j (edgeOp b p.1 p.2 x) S) =
      2 * subsetOp b (deletedGraph G i j) (gradient b i j x) S := by
    have he : (∑ p ∈ adjPairs (deletedGraph G i j),
        gradient b i j (edgeOp b p.1 p.2 x) S) =
        ∑ p ∈ adjPairs (deletedGraph G i j), edgeOp b p.1 p.2 (gradient b i j x) S := by
      apply Finset.sum_congr rfl
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      exact gradient_edge_disjoint b i j p.1 p.2 h.2.1.symm h.2.2.2.1.symm
        h.2.2.1.symm h.2.2.2.2.symm x S
    rw [he]
    simp [subsetOp, adjPairs, Finset.sum_filter, Fintype.sum_prod_type]
  rw [hd]
  have hi : (∑ w ∈ otherNbrs G i j, gradient b i j (edgeOp b i w x) S) =
      ∑ w ∈ otherNbrs G i j, gradient b i w x (swapSet j w S) := by
    apply Finset.sum_congr rfl
    intro w hw
    have h := (Finset.mem_filter.mp hw).2
    exact gradient_edge_incident b hb i j w (G.ne_of_adj hadj)
      (G.ne_of_adj h.1) h.2.symm x S
  have hj : (∑ w ∈ otherNbrs G j i, gradient b i j (edgeOp b j w x) S) =
      ∑ w ∈ otherNbrs G j i, b * gradient b j w x (swapSet i w S) := by
    apply Finset.sum_congr rfl
    intro w hw
    have h := (Finset.mem_filter.mp hw).2
    rw [gradient_symm b hb j i]
    exact congrArg (b * ·) (gradient_edge_incident b hb j i w
      (G.ne_of_adj hadj).symm (G.ne_of_adj h.1) h.2.symm x S)
  rw [hi, hj]
  ring

private lemma card_adjPairs (G : SimpleGraph (Fin n)) :
    (adjPairs G).card = 2 * @edgeCount n G (Classical.decRel G.Adj) := by
  classical
  calc
    (adjPairs G).card = ∑ i, (G.neighborFinset i).card := by
      simp only [adjPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp
    _ = 2 * G.edgeFinset.card := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        G.sum_degrees_eq_twice_card_edges

private lemma edgeCount_partition (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {i j : Fin n} (hadj : G.Adj i j) :
    (edgeCount G : ℝ) = 1 +
      (@edgeCount n (deletedGraph G i j) (Classical.decRel _) : ℝ) +
      ((otherNbrs G i j).card : ℝ) + ((otherNbrs G j i).card : ℝ) := by
  classical
  have h := sum_adjPairs_partition G hadj (fun _ _ => 1) (fun _ _ => rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [card_adjPairs G, card_adjPairs (deletedGraph G i j)] at h
  push_cast at h
  have he : (Classical.decRel G.Adj) = (inferInstance : DecidableRel G.Adj) :=
    Subsingleton.elim _ _
  rw [he] at h
  linarith

private lemma sum_insert_crossing (G : SimpleGraph (Fin n)) (k : ℕ)
    (f : Finset (Fin n) → Fin n → Fin n → ℝ) :
    (∑ R : KSub (Fin n) k, ∑ p ∈ adjPairs G,
      if p.1 ∉ R.1 ∧ p.2 ∉ R.1 then f (insert p.1 R.1) p.1 p.2 else 0) =
      ∑ S : KSub (Fin n) (k + 1), ∑ p ∈ crossingPairs G S.1, f S.1 p.1 p.2 := by
  classical
  let t₁ := (Finset.univ : Finset (KSub (Fin n) k × Fin n × Fin n)).filter
    fun q => G.Adj q.2.1 q.2.2 ∧ q.2.1 ∉ q.1.1 ∧ q.2.2 ∉ q.1.1
  let t₂ := (Finset.univ : Finset (KSub (Fin n) (k + 1) × Fin n × Fin n)).filter
    fun q => G.Adj q.2.1 q.2.2 ∧ q.2.1 ∈ q.1.1 ∧ q.2.2 ∉ q.1.1
  have ht : (∑ q ∈ t₁, f (insert q.2.1 q.1.1) q.2.1 q.2.2) =
      ∑ q ∈ t₂, f q.1.1 q.2.1 q.2.2 := by
    refine Finset.sum_bij (fun q hq =>
      (⟨insert q.2.1 q.1.1, by
        have h := (Finset.mem_filter.mp hq).2
        rw [Finset.card_insert_of_notMem h.2.1, q.1.2]⟩, q.2)) ?_ ?_ ?_ ?_
    · intro q hq
      have h := (Finset.mem_filter.mp hq).2
      simp only [t₂, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨h.1, Finset.mem_insert_self _ _, ?_⟩
      simp only [Finset.mem_insert]
      exact not_or.mpr ⟨(G.ne_of_adj h.1).symm, h.2.2⟩
    · intro q hq r hr he
      have hq' := (Finset.mem_filter.mp hq).2
      have hr' := (Finset.mem_filter.mp hr).2
      have hp : q.2 = r.2 :=
        congrArg (fun z : KSub (Fin n) (k + 1) × Fin n × Fin n => z.2) he
      have hs : insert q.2.1 q.1.1 = insert r.2.1 r.1.1 :=
        congrArg (fun z => z.1.1) he
      rw [hp] at hs
      have he' := congrArg (fun z => z.erase r.2.1) hs
      rw [Finset.erase_insert (hp ▸ hq'.2.1), Finset.erase_insert hr'.2.1] at he'
      exact Prod.ext (Subtype.ext he') hp
    · intro q hq
      have h := (Finset.mem_filter.mp hq).2
      let R : KSub (Fin n) k := ⟨q.1.1.erase q.2.1, by
        rw [Finset.card_erase_of_mem h.2.1, q.1.2]
        omega⟩
      refine ⟨(R, q.2), ?_, ?_⟩
      · simp only [t₁, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h.1, Finset.notMem_erase _ _, fun hz => h.2.2 (Finset.mem_of_mem_erase hz)⟩
      · apply Prod.ext
        · exact Subtype.ext (Finset.insert_erase h.2.1)
        · rfl
    · intro q _
      rfl
  simpa only [t₁, t₂, adjPairs, crossingPairs, Finset.sum_filter,
    Fintype.sum_prod_type, ite_and] using ht

private lemma sum_crossing_swap (G : SimpleGraph (Fin n)) (k : ℕ)
    (f : Finset (Fin n) → Fin n → Fin n → ℝ) :
    (∑ S : KSub (Fin n) k, ∑ p ∈ crossingPairs G S.1,
      f (swapSet p.1 p.2 S.1) p.2 p.1) =
      ∑ S : KSub (Fin n) k, ∑ p ∈ crossingPairs G S.1, f S.1 p.1 p.2 := by
  classical
  let t := (Finset.univ : Finset (KSub (Fin n) k × Fin n × Fin n)).filter
    fun q => G.Adj q.2.1 q.2.2 ∧ q.2.1 ∈ q.1.1 ∧ q.2.2 ∉ q.1.1
  have hm (q : KSub (Fin n) k × Fin n × Fin n) (hq : q ∈ t) :
      (swapK q.2.1 q.2.2 k q.1, q.2.2, q.2.1) ∈ t := by
    have h := (Finset.mem_filter.mp hq).2
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, swapK,
      Equiv.coe_fn_mk, mem_swapSet, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact ⟨h.1.symm, h.2.1, h.2.2⟩
  have hs (q : KSub (Fin n) k × Fin n × Fin n) :
      (swapK q.2.2 q.2.1 k (swapK q.2.1 q.2.2 k q.1), q.2.1, q.2.2) = q := by
    apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun e => e (swapSet q.2.1 q.2.2 q.1.1))
        (swapSet_symm q.2.2 q.2.1)).trans (swapSet_swapSet _ _ _)
    · rfl
  have ht : (∑ q ∈ t, f (swapSet q.2.1 q.2.2 q.1.1) q.2.2 q.2.1) =
      ∑ q ∈ t, f q.1.1 q.2.1 q.2.2 := by
    refine Finset.sum_bij (fun q _ => (swapK q.2.1 q.2.2 k q.1, q.2.2, q.2.1))
      hm ?_ ?_ (fun _ _ => rfl)
    · intro q _ r _ he
      have he' := congrArg (fun z : KSub (Fin n) k × Fin n × Fin n =>
        (swapK z.2.1 z.2.2 k z.1, z.2.2, z.2.1)) he
      simpa only [hs] using he'
    · intro q hq
      exact ⟨_, hm q hq, hs q⟩
  simpa only [t, crossingPairs, Finset.sum_filter, Fintype.sum_prod_type] using ht

private lemma sum_kNormSq_gradient_eq (b : ℝ) (hb : b ^ 2 = 1)
    (G : SimpleGraph (Fin n)) (k : ℕ) (x : Finset (Fin n) → ℝ) :
    (∑ p ∈ adjPairs G, kNormSq k (gradient b p.1 p.2 x)) =
      2 * kInner (k + 1) x (subsetOp b G x) := by
  classical
  let f := fun S i j => x S * (x S + b * x (swapSet i j S))
  have he : (∑ p ∈ adjPairs G, kNormSq k (gradient b p.1 p.2 x)) =
      ∑ S : KSub (Fin n) (k + 1), ∑ p ∈ crossingPairs G S.1,
        (x S.1 + b * x (swapSet p.1 p.2 S.1)) ^ 2 := by
    rw [← sum_insert_crossing G k
      (fun S i j => (x S + b * x (swapSet i j S)) ^ 2)]
    simp only [kNormSq, kInner]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro R _
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 ∉ R.1 ∧ p.2 ∉ R.1
    · have hs := swapSet_self p.1 p.2 R.1 (by simp [h.1, h.2])
      simp only [gradient, h.1, h.2, not_false_eq_true, and_self, ite_true,
        swapSet_insert, Equiv.swap_apply_left, hs, pow_two]
    · simp only [gradient, h, ite_false, mul_zero]
  rw [he]
  have hp (S : Finset (Fin n)) (i j : Fin n) :
      (x S + b * x (swapSet i j S)) ^ 2 = f S i j + f (swapSet i j S) j i := by
    dsimp [f]
    rw [swapSet_symm j i, swapSet_swapSet]
    linear_combination (x (swapSet i j S)) ^ 2 * hb
  simp_rw [hp, Finset.sum_add_distrib]
  rw [sum_crossing_swap]
  have hf : (∑ S : KSub (Fin n) (k + 1), ∑ p ∈ crossingPairs G S.1,
      f S.1 p.1 p.2) = kInner (k + 1) x (subsetOp b G x) := by
    simp only [kInner, subsetOp_crossing, Finset.mul_sum, f]
  rw [hf]
  ring

private lemma sum_otherNbrs_left (G : SimpleGraph (Fin n))
    (g : Fin n → Fin n → ℝ) :
    (∑ p ∈ adjPairs G, ∑ w ∈ otherNbrs G p.1 p.2, g p.1 w) =
      ∑ p ∈ adjPairs G, ((otherNbrs G p.1 p.2).card : ℝ) * g p.1 p.2 := by
  classical
  let t := (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    fun q => G.Adj q.1 q.2.1 ∧ G.Adj q.1 q.2.2 ∧ q.2.2 ≠ q.2.1
  have hm (q : Fin n × Fin n × Fin n) (hq : q ∈ t) : (q.1, q.2.2, q.2.1) ∈ t := by
    have h := (Finset.mem_filter.mp hq).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.1, h.1, h.2.2.symm⟩
  have ht : (∑ q ∈ t, g q.1 q.2.2) = ∑ q ∈ t, g q.1 q.2.1 := by
    refine Finset.sum_bij (fun q _ => (q.1, q.2.2, q.2.1)) hm ?_ ?_ (fun _ _ => rfl)
    · intro q _ r _ he
      exact congrArg (fun z : Fin n × Fin n × Fin n => (z.1, z.2.2, z.2.1)) he
    · intro q hq
      exact ⟨_, hm q hq, rfl⟩
  have hc (i j : Fin n) : ((otherNbrs G i j).card : ℝ) * g i j =
      ∑ w ∈ otherNbrs G i j, g i j := by simp
  simp_rw [hc]
  simpa only [t, adjPairs, otherNbrs, Finset.sum_filter, Fintype.sum_prod_type,
    ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero] using ht

private lemma sum_otherNbrs_right (G : SimpleGraph (Fin n))
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, g j i = g i j) :
    (∑ p ∈ adjPairs G, ∑ w ∈ otherNbrs G p.2 p.1, g p.2 w) =
      ∑ p ∈ adjPairs G, ((otherNbrs G p.2 p.1).card : ℝ) * g p.1 p.2 := by
  classical
  have hs (f : Fin n → Fin n → ℝ) :
      (∑ p ∈ adjPairs G, f p.2 p.1) = ∑ p ∈ adjPairs G, f p.1 p.2 := by
    simp only [adjPairs, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  rw [hs (fun i j => ∑ w ∈ otherNbrs G i j, g i w), sum_otherNbrs_left]
  symm
  calc
    (∑ p ∈ adjPairs G, ((otherNbrs G p.2 p.1).card : ℝ) * g p.1 p.2) =
        ∑ p ∈ adjPairs G, ((otherNbrs G p.2 p.1).card : ℝ) * g p.2 p.1 := by
      simp only [hg]
    _ = _ := hs (fun i j => ((otherNbrs G i j).card : ℝ) * g i j)

private lemma exists_lamMax_eigenpair {k : ℕ} (A : Matrix (KSub (Fin n) k) (KSub (Fin n) k) ℝ)
    (hA : A.IsHermitian) (hcard : Fintype.card (KSub (Fin n) k) ≠ 0) :
    ∃ u : KSub (Fin n) k → ℝ, u ⬝ᵥ u = 1 ∧ A *ᵥ u = lamMax A hA • u := by
  classical
  open scoped RealInnerProductSpace in
  let i₀ := (eigEquiv (KSub (Fin n) k)) ⟨0, Nat.pos_of_ne_zero hcard⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis i₀), ?_, ?_⟩
  · have hn := hA.eigenvectorBasis.orthonormal.1 i₀
    have hi : inner ℝ (hA.eigenvectorBasis i₀) (hA.eigenvectorBasis i₀) = 1 := by
      rw [real_inner_self_eq_norm_sq, hn]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
    simpa [star_trivial] using hi
  · have he : hA.eigenvalues i₀ = lamMax A hA := by
      rw [lamMax_eq A hA hcard, eigenvalues_eq_eigenvalues₀_comp]
      simp [i₀]
    simpa only [he] using hA.mulVec_eigenvectorBasis i₀

private lemma sum_gradient_inner_le (b : ℝ) (hb : b ^ 2 = 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (ih : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      lamMax (signedLaplacian H k b) (signedLaplacian_isHermitian H k b) ≤
        (edgeCount H : ℝ) + (k : ℝ))
    (x : Finset (Fin n) → ℝ) :
    (∑ p ∈ adjPairs G, kInner k (gradient b p.1 p.2 x)
      (gradient b p.1 p.2 (subsetOp b G x))) ≤
      ((edgeCount G : ℝ) + (k : ℝ) + 1) *
        ∑ p ∈ adjPairs G, kNormSq k (gradient b p.1 p.2 x) := by
  classical
  let N := fun i j => kNormSq k (gradient b i j x)
  let E := fun i j => kInner k (gradient b i j x)
    (gradient b i j (subsetOp b G x))
  have hp (p : Fin n × Fin n) (hp : p ∈ adjPairs G) :
      2 * E p.1 p.2 ≤
        2 * ((edgeCount G : ℝ) + (k : ℝ) + 1) * N p.1 p.2 +
        ((∑ w ∈ otherNbrs G p.1 p.2, N p.1 w) -
          ((otherNbrs G p.1 p.2).card : ℝ) * N p.1 p.2) +
        ((∑ w ∈ otherNbrs G p.2 p.1, N p.2 w) -
          ((otherNbrs G p.2 p.1).card : ℝ) * N p.1 p.2) := by
    have hadj : G.Adj p.1 p.2 := by simpa [adjPairs] using hp
    let H := deletedGraph G p.1 p.2
    let _ : DecidableRel H.Adj := Classical.decRel _
    let y := gradient b p.1 p.2 x
    have hD : kInner k y (subsetOp b H y) ≤
        ((edgeCount H : ℝ) + (k : ℝ)) * N p.1 p.2 := by
      calc
        kInner k y (subsetOp b H y) ≤
            lamMax (signedLaplacian H k b) (signedLaplacian_isHermitian H k b) *
              N p.1 p.2 := by
          rw [kInner_subsetOp]
          exact dotProduct_mulVec_le_lamMax _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (ih H) (kNormSq_nonneg k y)
    have hI (w : Fin n) :
        2 * kInner k y (fun S => gradient b p.1 w x (swapSet p.2 w S)) ≤
          N p.1 p.2 + N p.1 w := by
      simpa only [kNormSq_swap] using
        kInner_le_norms k y (fun S => gradient b p.1 w x (swapSet p.2 w S))
    have hJ (w : Fin n) :
        2 * kInner k y (fun S => b * gradient b p.2 w x (swapSet p.1 w S)) ≤
          N p.1 p.2 + N p.2 w := by
      simpa only [kNormSq_mul, kNormSq_swap, hb, one_mul] using
        kInner_le_norms k y (fun S => b * gradient b p.2 w x (swapSet p.1 w S))
    have hIs := Finset.sum_le_sum (s := otherNbrs G p.1 p.2) (fun w _ => hI w)
    have hJs := Finset.sum_le_sum (s := otherNbrs G p.2 p.1) (fun w _ => hJ w)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul] at hIs hJs
    have he : E p.1 p.2 = 2 * N p.1 p.2 + kInner k y (subsetOp b H y) +
        (∑ w ∈ otherNbrs G p.1 p.2,
          kInner k y (fun S => gradient b p.1 w x (swapSet p.2 w S))) +
        (∑ w ∈ otherNbrs G p.2 p.1,
          kInner k y (fun S => b * gradient b p.2 w x (swapSet p.1 w S))) := by
      have hg := funext (gradient_subsetOp b hb G hadj x)
      dsimp only [E]
      rw [hg, kInner_add, kInner_add, kInner_add, kInner_mul,
        kInner_sum, kInner_sum]
      rfl
    have hc := edgeCount_partition G hadj
    change (edgeCount G : ℝ) = 1 + (edgeCount H : ℝ) +
      ((otherNbrs G p.1 p.2).card : ℝ) + ((otherNbrs G p.2 p.1).card : ℝ) at hc
    rw [hc]
    nlinarith only [he, hD, hIs, hJs]
  have hs := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [sum_otherNbrs_left G N,
    sum_otherNbrs_right G N (fun i j => kNormSq_gradient_symm k b hb i j x)] at hs
  dsimp only [E, N] at hs
  linarith

private lemma theorem_3_1_aux (k : ℕ) (b : ℝ) (hb : b ^ 2 = 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    lamMax (signedLaplacian G k b) (signedLaplacian_isHermitian G k b) ≤
      (edgeCount G : ℝ) + (k : ℝ) := by
  induction k generalizing G with
  | zero =>
    by_cases hcard : Fintype.card (KSub (Fin n) 0) = 0
    · simp only [lamMax, hcard, dite_true]
      positivity
    · obtain ⟨u, hu1, huA⟩ :=
        exists_lamMax_eigenpair (signedLaplacian G 0 b) (signedLaplacian_isHermitian G 0 b) hcard
      have hquad : kInner 0 (extK u) (subsetOp b G (extK u)) =
          lamMax (signedLaplacian G 0 b) (signedLaplacian_isHermitian G 0 b) := by
        rw [kInner_subsetOp b G 0 (extK u)]
        have hex : (fun S : KSub (Fin n) 0 => extK u S) = u := funext (extK_apply u)
        rw [hex, huA, dotProduct_smul, hu1, smul_eq_mul, mul_one]
      have hzero : kInner 0 (extK u) (subsetOp b G (extK u)) = 0 := by
        unfold kInner
        apply Finset.sum_eq_zero
        intro S _
        have hS : S.1 = ∅ := Finset.card_eq_zero.mp S.2
        rw [subsetOp_crossing, hS]
        have hc : crossingPairs G (∅ : Finset (Fin n)) = ∅ := by
          ext p
          simp [mem_crossingPairs]
        rw [hc, Finset.sum_empty, mul_zero]
      have hlam0 : lamMax (signedLaplacian G 0 b) (signedLaplacian_isHermitian G 0 b) = 0 :=
        hquad.symm.trans hzero
      rw [hlam0]
      positivity
  | succ k ih =>
    by_cases hcard : Fintype.card (KSub (Fin n) (k + 1)) = 0
    · simp only [lamMax, hcard, dite_true]
      positivity
    · let A := signedLaplacian G (k + 1) b
      let hA := signedLaplacian_isHermitian G (k + 1) b
      let μ := lamMax A hA
      obtain ⟨u, hu1, huA⟩ := exists_lamMax_eigenpair A hA hcard
      let x : Finset (Fin n) → ℝ := extK u
      have hx_sub (T : Finset (Fin n)) (hT : T.card = k + 1) :
          subsetOp b G x T = μ * x T := by
        let Tk : KSub (Fin n) (k + 1) := ⟨T, hT⟩
        have hm := subsetOp_mulVec b G (k + 1) u Tk
        change subsetOp b G x T = (A *ᵥ u) Tk at hm
        rw [hm, huA, Pi.smul_apply, smul_eq_mul]
        congr 1
        exact (extK_apply u Tk).symm
      have hgrad_sub (i j : Fin n) (R : KSub (Fin n) k) :
          gradient b i j (subsetOp b G x) R.1 = μ * gradient b i j x R.1 := by
        by_cases hR : i ∉ R.1 ∧ j ∉ R.1
        · have hci : (insert i R.1).card = k + 1 := by
            rw [Finset.card_insert_of_notMem hR.1, R.2]
          have hcj : (insert j R.1).card = k + 1 := by
            rw [Finset.card_insert_of_notMem hR.2, R.2]
          simp only [gradient, hR.1, hR.2, not_false_eq_true, and_self, ite_true,
            hx_sub _ hci, hx_sub _ hcj]
          ring
        · simp [gradient, hR]
      have hinner_eq (p : Fin n × Fin n) :
          kInner k (gradient b p.1 p.2 x) (gradient b p.1 p.2 (subsetOp b G x)) =
            μ * kNormSq k (gradient b p.1 p.2 x) := by
        simp only [kInner, kNormSq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R _
        rw [hgrad_sub p.1 p.2 R]
        ring
      have hquad : kInner (k + 1) x (subsetOp b G x) = μ := by
        rw [kInner_subsetOp b G (k + 1) x]
        have hex : (fun S : KSub (Fin n) (k + 1) => x S) = u := funext (extK_apply u)
        rw [hex, huA, dotProduct_smul, hu1, smul_eq_mul, mul_one]
      have hsum_norm : (∑ p ∈ adjPairs G, kNormSq k (gradient b p.1 p.2 x)) = 2 * μ := by
        rw [sum_kNormSq_gradient_eq b hb G k x, hquad]
      have hle := sum_gradient_inner_le b hb G k (fun H _ => ih H) x
      simp_rw [hinner_eq, ← Finset.mul_sum, hsum_norm] at hle
      by_cases hμ : μ ≤ 0
      · have hpos : (0 : ℝ) ≤ (edgeCount G : ℝ) + ((k + 1 : ℕ) : ℝ) := by positivity
        exact hμ.trans hpos
      · push Not at hμ
        push_cast
        nlinarith

/-- **Theorem 3.1**: for any graph `G` on `n` vertices with `m = edgeCount G` edges,
any `k ≤ n`, and any `b ∈ {-1, 1}`, `λ_max(L_{b,G}^{(k)}) ≤ m + k`. -/
theorem theorem_3_1 (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (hk : k ≤ n)
    (b : ℝ) (hb : b = -1 ∨ b = 1) :
    lamMax (signedLaplacian G k b) (signedLaplacian_isHermitian G k b) ≤
      (edgeCount G : ℝ) + (k : ℝ) := by
  refine (And.left ⟨?_, hk⟩)
  have hb2 : b ^ 2 = 1 := by
    rcases hb with rfl | rfl <;> norm_num
  exact theorem_3_1_aux k b hb2 G

end Qatlib.Papers.KikuchiMaxCut26.MainResults
