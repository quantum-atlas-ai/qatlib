/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.WalkTypeTransportStat
import Qatlib.Concepts.WalkFind.UniqueCollision.SearchReadoutAux
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonDiffusionAux

/-!
# Transport between Johnson-walk state spaces

The module relates the full Johnson walk on subset-element states to its reduced type-space
matrices. It counts type fibers, proves orthonormality of the normalized type vectors, and
transports both diffusion half-steps and the marked phase flip.

`jwTypeLift` extends the basis-vector transport identities to arbitrary reduced vectors, powers
of the walk, and the complete iteration matrix. See [Ambainis2007ElementDistinctness] for the
mathematical background.

## Main statements

* `jwWalkBig_type_transport`: transport on type basis vectors.
* `walkTypeTransport_answer`: the type-transport proposition.
* `jwRunMat_typeLift`: transport of complete iterations.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

/-- A state has type `(k, false)` exactly when its subset contains the marked set `I`, assuming
`I.card = k`. -/
theorem jwTypeOf_marked_iff {k N r : ℕ} (I : Finset (Fin N)) (hI : I.card = k)
    (p : JRState N r) : jwTypeOf I p = (k, false) ↔ I ⊆ p.1.1 := by
  constructor
  · intro h
    have hc := congrArg Prod.fst h
    change (p.1.1.filter fun x => decide (x ∈ I)).card = k at hc
    have hs : (p.1.1.filter fun x => decide (x ∈ I)) ⊆ I := by
      intro x hx
      simpa using (Finset.mem_filter.mp hx).2
    have he := Finset.eq_of_subset_of_card_le hs (by omega)
    rw [← he]
    exact Finset.filter_subset _ _
  · intro h
    have he : (p.1.1.filter fun x => decide (x ∈ I)) = I := by
      ext x
      simp only [Finset.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hx => ⟨h hx, hx⟩⟩
    have hnot : p.1.2 ∉ I := fun hx => p.2.2 (h hx)
    unfold jwTypeOf
    apply Prod.ext
    · change (p.1.1.filter fun x => decide (x ∈ I)).card = k
      rw [he, hI]
    · simp [hnot]

/-- The full marked phase flip negates the type vector exactly for type `(k, false)` and fixes
the other type vectors. -/
theorem jwFlipBig_type (k N r : ℕ) (I : Finset (Fin N)) (hI : I.card = k)
    (jt : Fin (2 * k + 1)) :
    jwFlipBig k N r I *ᵥ jwPsiBigAt k N r I jt =
      (if jwPsiCoord k jt = (k, false) then (-1 : ℂ) else 1) •
        jwPsiBigAt k N r I jt := by
  rw [jwFlipBig_mulVec]
  ext p
  by_cases ht : jwTypeOf I p = jwPsiCoord k jt
  · have hmark : I ⊆ p.1.1 ↔ jwPsiCoord k jt = (k, false) := by
      rw [← ht, jwTypeOf_marked_iff I hI p]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [hmark]
  · simp [jwPsiBigAt, jwPsiBig, ht]

/-- The unique index whose `jwPsiCoord` is `(k, false)` is the final index. -/
private theorem good_coord_unique (k : ℕ) (i : Fin (2 * k + 1))
    (h : jwPsiCoord k i = (k, false)) : i = Fin.last (2 * k) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change i.val / 2 = k at h1
  have h2' : i.val % 2 ≠ 1 := by simpa [jwPsiCoord] using h2
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- The reduced marked flip is diagonal, with sign −1 on type `(k, false)` and sign 1 elsewhere. -/
theorem jwFlipTilde_eq_diagonal (k : ℕ) :
    jwFlipTilde k = Matrix.diagonal
      (fun i => if jwPsiCoord k i = (k, false) then (-1 : ℂ) else 1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jwFlipTilde]
  · have hb : ¬ (jwPsiCoord k i = (k, false) ∧ jwPsiCoord k j = (k, false)) := by
      rintro ⟨hi, hj⟩
      exact hij ((good_coord_unique k i hi).trans (good_coord_unique k j hj).symm)
    simp [jwFlipTilde, hb, hij]

/-- The full marked phase flip acts on type vectors with coefficients given by `jwFlipTilde`. -/
theorem jwFlipBig_type_transport (k N r : ℕ) (I : Finset (Fin N)) (hI : I.card = k)
    (jt : Fin (2 * k + 1)) :
    jwFlipBig k N r I *ᵥ jwPsiBigAt k N r I jt =
      ∑ i : Fin (2 * k + 1), jwFlipTilde k i jt • jwPsiBigAt k N r I i := by
  rw [jwFlipBig_type k N r I hI jt, jwFlipTilde_eq_diagonal]
  simp [Matrix.diagonal_apply, ite_smul]

/-- The equivalence inserting the distinguished outside element into the subset, with inverse
given by erasing the distinguished inside element. -/
def jwInsertEquiv (N r : ℕ) : JRState N r ≃ JRState' N r where
  toFun q := ⟨(insert q.1.2 q.1.1,q.1.2), by
    constructor
    · rw [Finset.card_insert_of_notMem q.2.2,q.2.1]
    · exact Finset.mem_insert_self _ _⟩
  invFun p := ⟨(p.1.1.erase p.1.2,p.1.2), by
    constructor
    · rw [Finset.card_erase_of_mem p.2.2,p.2.1]; omega
    · exact Finset.notMem_erase _ _⟩
  left_inv q := by
    apply Subtype.ext
    simp only [Finset.erase_insert q.2.2]
  right_inv p := by
    apply Subtype.ext
    simp only [Finset.insert_erase p.2.2]

/-- The embedding matrix is the permutation matrix of `jwInsertEquiv`. -/
theorem jwEmbedMat_equiv (N r : ℕ) (p : JRState' N r) (q : JRState N r) :
    jwEmbedMat N r p q = if p = jwInsertEquiv N r q then 1 else 0 := by
  have he : p = jwInsertEquiv N r q ↔ p.1 = (q.1.1 ∪ {q.1.2},q.1.2) := by
    rw [Subtype.ext_iff]
    simp only [jwInsertEquiv, Equiv.coe_fn_mk, Finset.union_singleton]
  simp only [jwEmbedMat, Matrix.of_apply, he]

/-- The dropping matrix is the permutation matrix of the inverse of `jwInsertEquiv`. -/
theorem jwDropMat_equiv (N r : ℕ) (q : JRState N r) (p : JRState' N r) :
    jwDropMat N r q p = if q = (jwInsertEquiv N r).symm p then 1 else 0 := by
  have he : q = (jwInsertEquiv N r).symm p ↔ q.1 = (p.1.1.erase p.1.2,p.1.2) := by
    rw [Subtype.ext_iff]
    rfl
  simp only [jwDropMat, Matrix.of_apply, he]

/-- Applying the embedding matrix evaluates the input at the inverse image under
`jwInsertEquiv`. -/
theorem jwEmbedMat_mulVec (N r : ℕ) (v : JRState N r → ℂ) (p : JRState' N r) :
    (jwEmbedMat N r *ᵥ v) p = v ((jwInsertEquiv N r).symm p) := by
  simp only [Matrix.mulVec, dotProduct, jwEmbedMat_equiv, ite_mul, one_mul, zero_mul]
  have he (q : JRState N r) : p = jwInsertEquiv N r q ↔ (jwInsertEquiv N r).symm p = q := by
    exact (jwInsertEquiv N r).symm_apply_eq.symm
  simp only [he, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Applying the dropping matrix evaluates the input at its image under `jwInsertEquiv`. -/
theorem jwDropMat_mulVec (N r : ℕ) (v : JRState' N r → ℂ) (q : JRState N r) :
    (jwDropMat N r *ᵥ v) q = v (jwInsertEquiv N r q) := by
  simp only [Matrix.mulVec, dotProduct, jwDropMat_equiv, ite_mul, one_mul, zero_mul]
  have he (p : JRState' N r) : q = (jwInsertEquiv N r).symm p ↔ jwInsertEquiv N r q = p := by
    exact (jwInsertEquiv N r).apply_eq_iff_eq_symm_apply.symm
  simp only [he, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Dropping after embedding gives the identity matrix on `JRState`. -/
theorem jwDropMat_mul_embed (N r : ℕ) : jwDropMat N r * jwEmbedMat N r = 1 := by
  apply Matrix.ext
  intro p q
  change (jwDropMat N r *ᵥ (fun t => jwEmbedMat N r t q)) p = _
  rw [jwDropMat_mulVec, jwEmbedMat_equiv]
  simp [Matrix.one_apply]

/-- The dropping matrix is the conjugate transpose of the embedding matrix. -/
theorem jwDropMat_eq_embed_adjoint (N r : ℕ) : jwDropMat N r = (jwEmbedMat N r)ᴴ := by
  ext q p
  have he : q = (jwInsertEquiv N r).symm p ↔ p = jwInsertEquiv N r q := by
    rw [eq_comm]
    exact (jwInsertEquiv N r).symm_apply_eq
  simp [jwDropMat_equiv, Matrix.conjTranspose_apply, jwEmbedMat_equiv, he]

/-- Embedding after dropping gives the identity matrix on `JRState'`. -/
theorem jwEmbedMat_mul_drop (N r : ℕ) : jwEmbedMat N r * jwDropMat N r = 1 := by
  ext p q
  change (jwEmbedMat N r *ᵥ (fun t => jwDropMat N r t q)) p = _
  rw [jwEmbedMat_mulVec, jwDropMat_equiv]
  simp [Matrix.one_apply]

/-- The embedding matrix preserves constant vectors. -/
theorem jwEmbedMat_constant (N r : ℕ) (z : ℂ) :
    jwEmbedMat N r *ᵥ (fun _ => z) = fun _ => z := by
  funext p
  exact jwEmbedMat_mulVec N r (fun _ => z) p

/-- The dropping matrix preserves constant vectors. -/
theorem jwDropMat_constant (N r : ℕ) (z : ℂ) :
    jwDropMat N r *ᵥ (fun _ => z) = fun _ => z := by
  funext p
  exact jwDropMat_mulVec N r (fun _ => z) p

/-- The fiber of states with a fixed subset in `JRState N r` has cardinality `N - r`. -/
theorem jwOutsideFiber_card (N r : ℕ) (p : JRState N r) :
    Fintype.card {q : JRState N r // p.1.1 = q.1.1} = N-r := by
  let e : {q : JRState N r // p.1.1 = q.1.1} ≃ {y : Fin N // y ∉ p.1.1} :=
    { toFun := fun q => ⟨q.1.1.2, by simpa only [← q.2] using q.1.2.2⟩
      invFun := fun y => ⟨⟨(p.1.1,y.1),p.2.1,y.2⟩,rfl⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext q.2 rfl
      right_inv := by intro y; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl]
  simp [Fintype.card_coe, p.2.1]

/-- The fiber of states with a fixed subset in `JRState' N r` has cardinality `r + 1`. -/
theorem jwInsideFiber_card (N r : ℕ) (p : JRState' N r) :
    Fintype.card {q : JRState' N r // p.1.1 = q.1.1} = r+1 := by
  let e : {q : JRState' N r // p.1.1 = q.1.1} ≃ {y : Fin N // y ∈ p.1.1} :=
    { toFun := fun q => ⟨q.1.1.2, by simpa only [← q.2] using q.1.2.2⟩
      invFun := fun y => ⟨⟨(p.1.1,y.1),p.2.1,y.2⟩,rfl⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext q.2 rfl
      right_inv := by intro y; rfl }
  rw [Fintype.card_congr e]
  simpa using p.2.1

/-- Diffusion on fibers of common positive cardinality `d` fixes every constant vector. -/
private theorem fiberDiffusion_constant {α β : Type} [Fintype α] [DecidableEq α]
    [DecidableEq β] (f : α → β) (d : ℕ) (hd : 0 < d)
    (hc : ∀ p, Fintype.card {q // f p = f q} = d) (z : ℂ) :
    (Matrix.of fun p q => (2 / (d : ℂ)) * (if f p = f q then 1 else 0) -
      (if p = q then 1 else 0)) *ᵥ (fun _ => z) = fun _ => z := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hsum : (∑ q, (if f p = f q then (1 : ℂ) else 0) * z) = (d : ℂ) * z := by
    rw [← Finset.sum_mul, Finset.sum_boole]
    rw [← Fintype.card_subtype, hc p]
  rw [hsum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  field_simp
  ring

/-- For `r < N`, the first full-space diffusion fixes constant vectors. -/
theorem jwBigDiff1_constant (N r : ℕ) (hr : r < N) (z : ℂ) :
    jwBigDiff1 N r *ᵥ (fun _ => z) = fun _ => z := by
  have he : jwBigDiff1 N r = Matrix.of (fun p q : JRState N r =>
      (2 / ((N-r : ℕ) : ℂ)) * (if p.1.1 = q.1.1 then 1 else 0) -
        (if p = q then 1 else 0)) := by
    ext p q
    have hpq : p = q ↔ p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    by_cases hs : p.1.1 = q.1.1
    · simp [jwBigDiff1, hs, hpq]
    · simp [jwBigDiff1, hs, hpq]
  rw [he]
  exact fiberDiffusion_constant (fun p : JRState N r => p.1.1) (N-r) (by omega)
    (jwOutsideFiber_card N r) z

/-- The second full-space diffusion fixes constant vectors. -/
theorem jwBigDiff2_constant (N r : ℕ) (z : ℂ) :
    jwBigDiff2 N r *ᵥ (fun _ => z) = fun _ => z := by
  have he : jwBigDiff2 N r = Matrix.of (fun p q : JRState' N r =>
      (2 / ((r+1 : ℕ) : ℂ)) * (if p.1.1 = q.1.1 then 1 else 0) -
        (if p = q then 1 else 0)) := by
    ext p q
    have hpq : p = q ↔ p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    by_cases hs : p.1.1 = q.1.1
    · simp [jwBigDiff2, hs, hpq]
    · simp [jwBigDiff2, hs, hpq]
  rw [he]
  exact fiberDiffusion_constant (fun p : JRState' N r => p.1.1) (r+1) (by omega)
    (jwInsideFiber_card N r) z

/-- For `r < N`, the full Johnson walk fixes its start vector. -/
theorem jwWalkBig_start_fixed (N r : ℕ) (hr : r < N) :
    jwWalkBig N r *ᵥ jwStartBig N r = jwStartBig N r := by
  unfold jwWalkBig jwStartBig
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    jwBigDiff1_constant N r hr, jwEmbedMat_constant, jwBigDiff2_constant,
    jwDropMat_constant]

/-- The number of subset-element states in `JRState N r` is `Nat.choose N r * (N - r)`. -/
theorem jrState_card (N r : ℕ) :
    Fintype.card (JRState N r) = Nat.choose N r * (N-r) := by
  let e : JRState N r ≃
      (Σ S : {S : Finset (Fin N) // S.card = r}, {y : Fin N // y ∉ S.1}) :=
    { toFun := fun p => ⟨⟨p.1.1,p.2.1⟩,⟨p.1.2,p.2.2⟩⟩
      invFun := fun p => ⟨(p.1.1,p.2.1),p.1.2,p.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have hc (S : {S : Finset (Fin N) // S.card = r}) :
      Fintype.card {y : Fin N // y ∉ S.1} = N-r := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_coe,S.2]
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_finset_len,Fintype.card_fin,Nat.cast_id]

/-- For `r < N`, the sum of squared coordinate norms of the full start vector is 1. -/
theorem jwStartBig_normSq (N r : ℕ) (hr : r < N) :
    (∑ p : JRState N r, ‖jwStartBig N r p‖^2) = 1 := by
  have hc : 0 < Fintype.card (JRState N r) := by
    rw [jrState_card]
    exact Nat.mul_pos (Nat.choose_pos (le_of_lt hr)) (by omega)
  have hcR : (0 : ℝ) < Fintype.card (JRState N r) := by exact_mod_cast hc
  simp only [jwStartBig,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_one,
    abs_of_nonneg (Real.sqrt_nonneg _),div_pow,one_pow,
    Real.sq_sqrt (le_of_lt hcR),Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_one_div_cancel (ne_of_gt hcR)

/-- Distinct reduced indices have distinct Johnson-walk type coordinates. -/
theorem jwPsiCoord_injective (k : ℕ) : Function.Injective (jwPsiCoord k) := by
  intro i j h
  have hdiv := congrArg Prod.fst h
  have hmod := congrArg Prod.snd h
  change i.val/2 = j.val/2 at hdiv
  have hmod' : (i.val%2 == 1) = (j.val%2 == 1) := hmod
  apply Fin.ext
  by_cases hi : i.val%2 = 1
  · have hj : j.val%2 = 1 := by simpa [hi] using hmod'.symm
    omega
  · have hj : j.val%2 ≠ 1 := by simpa [hi] using hmod'.symm
    omega

/-- Type vectors with distinct reduced indices are orthogonal. -/
theorem jwPsiBigAt_orthogonal (k N r : ℕ) (I : Finset (Fin N))
    (i j : Fin (2*k+1)) (hij : i ≠ j) :
    (∑ p : JRState N r, star (jwPsiBigAt k N r I i p) * jwPsiBigAt k N r I j p) = 0 := by
  have hcoord : jwPsiCoord k i ≠ jwPsiCoord k j := fun h => hij (jwPsiCoord_injective k h)
  apply Finset.sum_eq_zero
  intro p _
  by_cases hi : jwTypeOf I p = jwPsiCoord k i
  · have hj : jwTypeOf I p ≠ jwPsiCoord k j := fun h => hcoord (hi.symm.trans h)
    simp [jwPsiBigAt,jwPsiBig,hj]
  · simp [jwPsiBigAt,jwPsiBig,hi]

/-- When `I.card = k`, the good-state vector is the type vector at the final index. -/
theorem jwGoodVec_eq_typeLast (k N r : ℕ) (I : Finset (Fin N)) (hI : I.card = k) :
    jwGoodVec k N r I = jwPsiBigAt k N r I (Fin.last (2*k)) := by
  funext p
  have hcoord : jwPsiCoord k (Fin.last (2*k)) = (k,false) := by
    simp [jwPsiCoord]
  simp only [jwGoodVec,jwPsiBigAt,hcoord,jwPsiBig,
    jwTypeOf_marked_iff I hI p,decide_eq_true_eq]

/-- The number of subsets of `I` with cardinality `j` is `Nat.choose I.card j`. -/
private theorem subsetCard_count {N : ℕ} (I : Finset (Fin N)) (j : ℕ) :
    Fintype.card {A : Finset (Fin N) // A ⊆ I ∧ A.card = j} = Nat.choose I.card j := by
  have he : (Finset.univ.filter fun A : Finset (Fin N) => A ⊆ I ∧ A.card = j) =
      I.powersetCard j := by ext A; simp
  rw [Fintype.subtype_card, he, Finset.card_powersetCard]

/-- For `j ≤ r`, the number of `r`-element subsets intersecting `I` in exactly `j` elements is
`Nat.choose I.card j * Nat.choose (N - I.card) (r - j)`. -/
private theorem intersectionSet_count {N r j : ℕ} (I : Finset (Fin N)) (hjr : j ≤ r) :
    Fintype.card {S : Finset (Fin N) // S.card = r ∧ (S ∩ I).card = j} =
      Nat.choose I.card j * Nat.choose (N - I.card) (r-j) := by
  let e : {S : Finset (Fin N) // S.card = r ∧ (S ∩ I).card = j} ≃
      {A : Finset (Fin N) // A ⊆ I ∧ A.card = j} ×
      {B : Finset (Fin N) // B ⊆ Iᶜ ∧ B.card = r-j} :=
    { toFun := fun S =>
        (⟨S.1 ∩ I, Finset.inter_subset_right, S.2.2⟩,
         ⟨S.1 \ I, by intro x hx; simpa using (Finset.mem_sdiff.mp hx).2,
           by rw [Finset.card_sdiff, Finset.inter_comm, S.2.1, S.2.2]⟩)
      invFun := fun P => ⟨P.1.1 ∪ P.2.1, by
        have hd : Disjoint P.1.1 P.2.1 := by
          apply Finset.disjoint_left.mpr
          intro x ha hb
          have hai := P.1.2.1 ha
          have hbi := P.2.2.1 hb
          simp [hai] at hbi
        constructor
        · rw [Finset.card_union_of_disjoint hd, P.1.2.2, P.2.2.2]
          omega
        · have he : (P.1.1 ∪ P.2.1) ∩ I = P.1.1 := by
            ext x
            have ha : x ∈ P.1.1 → x ∈ I := fun hx => P.1.2.1 hx
            have hb : x ∈ P.2.1 → x ∈ Iᶜ := fun hx => P.2.2.1 hx
            simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl] at *
            tauto
          rw [he, P.1.2.2]⟩
      left_inv := by
        intro S
        apply Subtype.ext
        ext x; simp; tauto
      right_inv := by
        intro P
        apply Prod.ext <;> apply Subtype.ext
        · ext x
          have ha : x ∈ P.1.1 → x ∈ I := fun hx => P.1.2.1 hx
          have hb : x ∈ P.2.1 → x ∈ Iᶜ := fun hx => P.2.2.1 hx
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl] at *
          tauto
        · ext x
          have ha : x ∈ P.1.1 → x ∈ I := fun hx => P.1.2.1 hx
          have hb : x ∈ P.2.1 → x ∈ Iᶜ := fun hx => P.2.2.1 hx
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl] at *
          tauto }
  rw [Fintype.card_congr e, Fintype.card_prod, subsetCard_count, subsetCard_count]
  simp [Finset.card_compl]

/-- Counts the elements outside an `r`-element subset according to whether they belong to `I`. -/
theorem jwOutsideTypeFiber_card (N r : ℕ) (I : Finset (Fin N))
    (S : Finset (Fin N)) (hS : S.card = r) (l : Bool) :
    Fintype.card {y : Fin N // y ∉ S ∧ decide (y ∈ I) = l} =
      if l then I.card - (S ∩ I).card else N-r-(I.card-(S ∩ I).card) := by
  have htrue : (Finset.univ.filter fun y : Fin N => y ∉ S ∧ decide (y ∈ I) = true) =
      I \ S := by ext y; simp [and_comm]
  have hfalse : (Finset.univ.filter fun y : Fin N => y ∉ S ∧ decide (y ∈ I) = false) =
      (S ∪ I)ᶜ := by ext y; simp
  cases l
  · rw [Fintype.subtype_card, hfalse, Finset.card_compl, Fintype.card_fin]
    simp only [Bool.false_eq_true, ite_false]
    have h := Finset.card_union_add_card_inter S I
    rw [hS] at h
    have hle := Finset.card_le_card (Finset.inter_subset_right : S ∩ I ⊆ I)
    omega
  · rw [Fintype.subtype_card, htrue, Finset.card_sdiff]
    simp

/-- When `I.card = k` and `j ≤ r`, the number of full states of type `(j, l)` equals `jwCnt k N
r j l`. -/
theorem jwTypeFiber_card (k N r j : ℕ) (I : Finset (Fin N)) (hI : I.card = k)
    (hjr : j ≤ r) (l : Bool) :
    Fintype.card {p : JRState N r // jwTypeOf I p = (j,l)} = jwCnt k N r j l := by
  have hf (S : Finset (Fin N)) :
      (S.filter fun x => decide (x ∈ I)) = S ∩ I := by ext x; simp
  let e : {p : JRState N r // jwTypeOf I p = (j,l)} ≃
      (Σ S : {S : Finset (Fin N) // S.card = r ∧ (S ∩ I).card = j},
        {y : Fin N // y ∉ S.1 ∧ decide (y ∈ I) = l}) :=
    { toFun := fun p =>
        ⟨⟨p.1.1.1, p.1.2.1, by
          have h := congrArg Prod.fst p.2
          simpa [jwTypeOf, hf] using! h⟩,
          ⟨p.1.1.2,p.1.2.2,congrArg Prod.snd p.2⟩⟩
      invFun := fun p => ⟨⟨(p.1.1,p.2.1),p.1.2.1,p.2.2.1⟩,by
        apply Prod.ext
        · simpa [jwTypeOf,hf] using! p.1.2.2
        · exact p.2.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have hc (S : {S : Finset (Fin N) // S.card = r ∧ (S ∩ I).card = j}) :
      Fintype.card {y : Fin N // y ∉ S.1 ∧ decide (y ∈ I) = l} =
        if l then k-j else N-r-(k-j) := by
    simpa [hI, S.2.2] using jwOutsideTypeFiber_card N r I S.1 S.2.1 l
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [intersectionSet_count I hjr, hI]
  rfl

/-- Under `k ≤ r` and `k < N - r`, every reduced type coordinate has strictly positive
population. -/
theorem jwCnt_coord_pos (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (i : Fin (2*k+1)) : 0 < jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 := by
  have hi := i.isLt
  have hj : i.val/2 ≤ k := by omega
  have hjr : i.val/2 ≤ r := le_trans hj hkr
  have hb : r-i.val/2 ≤ N-k := by omega
  unfold jwCnt jwPsiCoord
  apply Nat.mul_pos (Nat.mul_pos (Nat.choose_pos hj) (Nat.choose_pos hb))
  split_ifs with h
  · have hm : i.val%2 = 1 := by simpa using h
    omega
  · omega

/-- Under the stated population conditions and `I.card = k`, each normalized type vector has
squared norm 1. -/
theorem jwPsiBigAt_normSq (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (i : Fin (2*k+1)) :
    (∑ p : JRState N r, ‖jwPsiBigAt k N r I i p‖^2) = 1 := by
  let c := jwPsiCoord k i
  have hj : c.1 ≤ r := by dsimp [c,jwPsiCoord]; have hi := i.isLt; omega
  have hc : 0 < (jwCnt k N r c.1 c.2 : ℝ) := by
    exact_mod_cast jwCnt_coord_pos k N r hkr hkNr i
  have he : ∀ p : JRState N r,
      ‖jwPsiBigAt k N r I i p‖^2 =
        if jwTypeOf I p = c then 1/(jwCnt k N r c.1 c.2 : ℝ) else 0 := by
    intro p
    by_cases hp : jwTypeOf I p = c
    · simp [jwPsiBigAt,jwPsiBig,show jwPsiCoord k i = c from rfl,hp,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (le_of_lt hc)]
    · simp [jwPsiBigAt,jwPsiBig,show jwPsiCoord k i = c from rfl,hp]
  simp_rw [he]
  have hcard : (Finset.univ.filter fun p : JRState N r => jwTypeOf I p = c).card =
      jwCnt k N r c.1 c.2 := by
    simpa [Fintype.subtype_card] using jwTypeFiber_card k N r c.1 I hI hj c.2
  rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,hcard]
  exact mul_one_div_cancel (ne_of_gt hc)

/-- Under the stated population conditions, the type vectors form an orthonormal family. -/
theorem jwPsiBigAt_inner (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (i j : Fin (2*k+1)) :
    (∑ p : JRState N r, star (jwPsiBigAt k N r I i p) * jwPsiBigAt k N r I j p) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true,Complex.star_def,← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq,← Complex.ofReal_sum]
    rw [jwPsiBigAt_normSq k N r hkr hkNr I hI]
    rfl
  · rw [if_neg hij]
    exact jwPsiBigAt_orthogonal k N r I i j hij

/-- When `I.card = k`, every full state has a type represented by a reduced coordinate. -/
theorem jwTypeOf_exists_coord (k N r : ℕ) (I : Finset (Fin N)) (hI : I.card = k)
    (p : JRState N r) : ∃ i : Fin (2*k+1), jwTypeOf I p = jwPsiCoord k i := by
  let j := (p.1.1 ∩ I).card
  have hf : (p.1.1.filter fun x => decide (x ∈ I)) = p.1.1 ∩ I := by ext x; simp
  have hj : j ≤ k := by
    simpa [j,hI] using Finset.card_le_card (Finset.inter_subset_right : p.1.1 ∩ I ⊆ I)
  by_cases hp : p.1.2 ∈ I
  · have hy : p.1.2 ∈ I \ p.1.1 := Finset.mem_sdiff.mpr ⟨hp,p.2.2⟩
    have hc : 0 < (I \ p.1.1).card := Finset.card_pos.mpr ⟨p.1.2,hy⟩
    rw [Finset.card_sdiff,hI] at hc
    have hjk : j < k := by dsimp [j] at *; omega
    refine ⟨⟨2*j+1,by omega⟩,?_⟩
    simp only [jwTypeOf,hf]
    simp [jwPsiCoord,hp,j,Nat.add_div,Nat.add_mod]
  · refine ⟨⟨2*j,by omega⟩,?_⟩
    simp only [jwTypeOf,hf]
    simp [jwPsiCoord,hp,j]

/-- Under the stated population conditions, decomposes the full start vector in the normalized
type vectors with coefficients from `jwStart` divided by the square root of the full state
count. -/
theorem jwStartBig_decompose_card (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) :
    jwStartBig N r = ∑ i : Fin (2*k+1),
      (jwStart k N r i / (Real.sqrt (Fintype.card (JRState N r) : ℝ) : ℂ)) •
        jwPsiBigAt k N r I i := by
  funext p
  obtain ⟨i,hi⟩ := jwTypeOf_exists_coord k N r I hI p
  have hs : (Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by
      exact_mod_cast jwCnt_coord_pos k N r hkr hkNr i))
  rw [Finset.sum_apply,Finset.sum_eq_single i]
  · simp only [Pi.smul_apply,smul_eq_mul,jwStart,jwPsiBigAt,jwPsiBig,hi,
      Prod.mk.eta,ite_true,jwStartBig,Complex.ofReal_div,Complex.ofReal_one]
    field_simp
  · intro j _ hji
    have hj : jwTypeOf I p ≠ jwPsiCoord k j := by
      intro h
      exact hji (jwPsiCoord_injective k (h.symm.trans hi))
    simp [jwPsiBigAt,jwPsiBig,hj]
  · simp

/-- The first full diffusion averages over the fixed-subset fiber with factor `2 / (N - r)` and
subtracts the input coordinate. -/
theorem jwBigDiff1_apply (N r : ℕ) (v : JRState N r → ℂ) (p : JRState N r) :
    (jwBigDiff1 N r *ᵥ v) p =
      (2 / ((N-r : ℕ) : ℂ)) * (∑ q : JRState N r, if p.1.1 = q.1.1 then v q else 0) - v p := by
  have he : jwBigDiff1 N r = Matrix.of (fun p q : JRState N r =>
      (2 / ((N-r : ℕ) : ℂ)) * (if p.1.1 = q.1.1 then 1 else 0) -
        (if p = q then 1 else 0)) := by
    ext p q
    have hpq : p = q ↔ p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    by_cases hs : p.1.1 = q.1.1
    · simp [jwBigDiff1, hs, hpq]
    · simp [jwBigDiff1, hs, hpq]
  rw [he]
  simp only [Matrix.mulVec,dotProduct,Matrix.of_apply,sub_mul,Finset.sum_sub_distrib,
    mul_assoc,← Finset.mul_sum,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,if_true]

/-- Counts full states with a prescribed type and the same subset as a fixed state. -/
theorem jwFixedOutsideType_card (N r : ℕ) (I : Finset (Fin N)) (p : JRState N r)
    (j : ℕ) (l : Bool) :
    Fintype.card {q : JRState N r // p.1.1 = q.1.1 ∧ jwTypeOf I q = (j,l)} =
      if (p.1.1 ∩ I).card = j then
        (if l then I.card-j else N-r-(I.card-j)) else 0 := by
  have hf (S : Finset (Fin N)) :
      (S.filter fun x => decide (x ∈ I)) = S ∩ I := by ext x; simp
  by_cases hj : (p.1.1 ∩ I).card = j
  · rw [if_pos hj]
    let e : {q : JRState N r // p.1.1 = q.1.1 ∧ jwTypeOf I q = (j,l)} ≃
        {y : Fin N // y ∉ p.1.1 ∧ decide (y ∈ I) = l} :=
      { toFun := fun q => ⟨q.1.1.2,by simpa only [q.2.1] using q.1.2.2,
          congrArg Prod.snd q.2.2⟩
        invFun := fun y => ⟨⟨(p.1.1,y.1),p.2.1,y.2.1⟩,rfl,by
          apply Prod.ext
          · simpa only [jwTypeOf,hf] using hj
          · exact y.2.2⟩
        left_inv := by
          intro q
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext q.2.1 rfl
        right_inv := by intro y; rfl }
    rw [Fintype.card_congr e]
    simpa [hj] using jwOutsideTypeFiber_card N r I p.1.1 p.2.1 l
  · rw [if_neg hj]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun q => ?_⟩
    have h := congrArg Prod.fst q.2.2
    have hj' : (q.1.1.1 ∩ I).card = j := by simpa only [jwTypeOf,hf] using h
    exact hj (q.2.1 ▸ hj')

/-- Computes the first full diffusion on a type vector using the number of outside elements of
each Boolean type. -/
theorem jwBigDiff1_type_apply (k N r j : ℕ) (I : Finset (Fin N)) (hI : I.card = k)
    (l : Bool) (p : JRState N r) :
    (jwBigDiff1 N r *ᵥ jwPsiBig k N r I j l) p =
      (2 / ((N-r : ℕ) : ℂ)) *
        (if (p.1.1 ∩ I).card = j then
          ((if l then k-j else N-r-(k-j) : ℕ) : ℂ) else 0) *
        ((1 / Real.sqrt (jwCnt k N r j l : ℝ) : ℝ) : ℂ) -
      jwPsiBig k N r I j l p := by
  rw [jwBigDiff1_apply]
  have he (q : JRState N r) :
      (if p.1.1 = q.1.1 then jwPsiBig k N r I j l q else 0) =
        if p.1.1 = q.1.1 ∧ jwTypeOf I q = (j,l) then
          ((1 / Real.sqrt (jwCnt k N r j l : ℝ) : ℝ) : ℂ) else 0 := by
    by_cases hs : p.1.1 = q.1.1 <;> by_cases ht : jwTypeOf I q = (j,l) <;>
      simp [jwPsiBig,hs,ht]
  simp_rw [he]
  rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun q : JRState N r =>
      p.1.1 = q.1.1 ∧ jwTypeOf I q = (j,l)).card =
        if (p.1.1 ∩ I).card = j then (if l then k-j else N-r-(k-j)) else 0 := by
    simpa [Fintype.subtype_card,hI] using jwFixedOutsideType_card N r I p j l
  rw [hcard]
  push_cast
  split_ifs <;> ring

/-- Taking the inner product with a normalized type vector extracts its coefficient from a
type-vector linear combination, under the stated population conditions. -/
theorem jwPsiBigAt_inner_sum (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k)
    (v : Fin (2*k+1) → ℂ) (i : Fin (2*k+1)) :
    (∑ p : JRState N r, star (jwPsiBigAt k N r I i p) *
      (∑ j : Fin (2*k+1), v j • jwPsiBigAt k N r I j) p) = v i := by
  calc
    _ = ∑ j : Fin (2*k+1), v j *
        (∑ p : JRState N r, star (jwPsiBigAt k N r I i p) * jwPsiBigAt k N r I j p) := by
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = v i := by
      simp_rw [jwPsiBigAt_inner k N r hkr hkNr I hI]
      simp

/-- The first reduced half-step has `jwD2` entries within equal intersection-count types and
zero entries between different counts. -/
theorem jwStep1_entry_types (k N r : ℕ) (i j : Fin (2*k+1)) :
    jwStep1 k N r i j =
      if (jwPsiCoord k i).1 = (jwPsiCoord k j).1 then
        jwD2 ((k-(jwPsiCoord k j).1 : ℝ)/(N-r))
          (jwPsiCoord k i).2 (jwPsiCoord k j).2 else 0 := by
  by_cases hi : i.val%2 = 1
  · have hdiv : (i.val+1)/2 = i.val/2+1 := by omega
    simp [jwStep1,jwPhiCoord,jwPsiCoord,hi,hdiv]
  · have hdiv : (i.val+1)/2 = i.val/2 := by omega
    have hz : i.val%2 = 0 := by omega
    simp [jwStep1,jwPhiCoord,jwPsiCoord,hz,hdiv]

/-- Evaluates a linear combination of type vectors at a state of a specified type as its
coefficient divided by the square root of that type's population. -/
theorem jwPsiBigAt_sum_apply (k N r : ℕ) (I : Finset (Fin N))
    (v : Fin (2*k+1) → ℂ) (p : JRState N r) (i : Fin (2*k+1))
    (hi : jwTypeOf I p = jwPsiCoord k i) :
    (∑ j : Fin (2*k+1), v j • jwPsiBigAt k N r I j) p =
      v i * ((1 / Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℝ) : ℂ) := by
  rw [Finset.sum_apply,Finset.sum_eq_single i]
  · simp [jwPsiBigAt,jwPsiBig,hi]
  · intro j _ hji
    have hj : jwTypeOf I p ≠ jwPsiCoord k j := by
      intro h
      exact hji (jwPsiCoord_injective k (h.symm.trans hi))
    simp [jwPsiBigAt,jwPsiBig,hj]
  · simp

/-- The type of an inserted state, consisting of its subset's intersection cardinality with `I`
and the distinguished element's membership in `I`. -/
def jwTypeOfInserted {N r : ℕ} (I : Finset (Fin N)) (p : JRState' N r) : ℕ × Bool :=
  ((p.1.1 ∩ I).card,decide (p.1.2 ∈ I))

/-- Inserting the distinguished element increases the intersection count by one exactly when
that element belongs to `I`, and preserves its Boolean membership label. -/
theorem jwTypeOfInserted_insert (N r : ℕ) (I : Finset (Fin N)) (p : JRState N r) :
    jwTypeOfInserted I (jwInsertEquiv N r p) =
      ((jwTypeOf I p).1 + if (jwTypeOf I p).2 then 1 else 0,(jwTypeOf I p).2) := by
  have hf : (p.1.1.filter fun x => decide (x ∈ I)) = p.1.1 ∩ I := by ext x; simp
  by_cases hp : p.1.2 ∈ I
  · have he : (insert p.1.2 p.1.1) ∩ I = insert p.1.2 (p.1.1 ∩ I) := by ext x; simp [hp]
    have hnot : p.1.2 ∉ p.1.1 ∩ I := by simp [p.2.2]
    simp only [jwTypeOfInserted,jwInsertEquiv,Equiv.coe_fn_mk,jwTypeOf,hf]
    simp [hp,he,Finset.card_insert_of_notMem hnot]
  · have he : (insert p.1.2 p.1.1) ∩ I = p.1.1 ∩ I := by ext x; simp [hp]
    simp only [jwTypeOfInserted,jwInsertEquiv,Equiv.coe_fn_mk,jwTypeOf,hf]
    simp [hp,he]

/-- The inserted coordinate `jwPhiCoord` is obtained from `jwPsiCoord` by adding the Boolean
membership indicator to the count. -/
theorem jwPhiCoord_eq_psi (k : ℕ) (i : Fin (2*k+1)) :
    jwPhiCoord k i = ((jwPsiCoord k i).1 + if (jwPsiCoord k i).2 then 1 else 0,
      (jwPsiCoord k i).2) := by
  apply Prod.ext
  · by_cases h : i.val%2 = 1
    · simp only [jwPhiCoord,jwPsiCoord,h,beq_self_eq_true,ite_true]
      omega
    · have hz : i.val%2 = 0 := by omega
      simp only [jwPhiCoord,jwPsiCoord,hz]
      norm_num
      omega
  · rfl

/-- A state's inserted type equals `jwPhiCoord k i` exactly when its original type equals
`jwPsiCoord k i`. -/
theorem jwInsert_type_iff (k N r : ℕ) (I : Finset (Fin N)) (p : JRState N r)
    (i : Fin (2*k+1)) :
    jwTypeOfInserted I (jwInsertEquiv N r p) = jwPhiCoord k i ↔
      jwTypeOf I p = jwPsiCoord k i := by
  rw [jwTypeOfInserted_insert,jwPhiCoord_eq_psi]
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨h1,h2⟩
    rw [h2] at h1
    exact ⟨Nat.add_right_cancel h1,h2⟩
  · rintro ⟨h1,h2⟩
    simp [h1,h2]

/-- The embedded type vector is supported on its corresponding inserted type and has amplitude
equal to the reciprocal square root of its original type population. -/
theorem jwEmbedMat_type_apply (k N r : ℕ) (I : Finset (Fin N))
    (i : Fin (2*k+1)) (p : JRState' N r) :
    (jwEmbedMat N r *ᵥ jwPsiBigAt k N r I i) p =
      if jwTypeOfInserted I p = jwPhiCoord k i then
        ((1 / Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℝ) : ℂ) else 0 := by
  rw [jwEmbedMat_mulVec]
  have ht := jwInsert_type_iff k N r I ((jwInsertEquiv N r).symm p) i
  rw [Equiv.apply_symm_apply] at ht
  simp only [jwPsiBigAt,jwPsiBig]
  simp only [Prod.mk.eta,← ht]

/-- Counts the elements inside an `(r + 1)`-element subset according to whether they belong to
`I`. -/
theorem jwInsideTypeFiber_card (N r : ℕ) (I : Finset (Fin N))
    (T : Finset (Fin N)) (hT : T.card = r+1) (l : Bool) :
    Fintype.card {y : Fin N // y ∈ T ∧ decide (y ∈ I) = l} =
      if l then (T ∩ I).card else r+1-(T ∩ I).card := by
  have htrue : (Finset.univ.filter fun y : Fin N => y ∈ T ∧ decide (y ∈ I) = true) =
      T ∩ I := by ext y; simp
  have hfalse : (Finset.univ.filter fun y : Fin N => y ∈ T ∧ decide (y ∈ I) = false) =
      T \ I := by ext y; simp
  cases l
  · rw [Fintype.subtype_card,hfalse,Finset.card_sdiff,hT,Finset.inter_comm]
    rfl
  · rw [Fintype.subtype_card,htrue]
    rfl

/-- The second full diffusion averages over the fixed-subset fiber with factor `2 / (r + 1)` and
subtracts the input coordinate. -/
theorem jwBigDiff2_apply (N r : ℕ) (v : JRState' N r → ℂ) (p : JRState' N r) :
    (jwBigDiff2 N r *ᵥ v) p =
      (2 / ((r+1 : ℕ) : ℂ)) * (∑ q : JRState' N r, if p.1.1 = q.1.1 then v q else 0) - v p := by
  have he : jwBigDiff2 N r = Matrix.of (fun p q : JRState' N r =>
      (2 / ((r+1 : ℕ) : ℂ)) * (if p.1.1 = q.1.1 then 1 else 0) -
        (if p = q then 1 else 0)) := by
    ext p q
    have hpq : p = q ↔ p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    by_cases hs : p.1.1 = q.1.1
    · simp [jwBigDiff2, hs, hpq]
    · simp [jwBigDiff2, hs, hpq]
  rw [he]
  simp only [Matrix.mulVec,dotProduct,Matrix.of_apply,sub_mul,Finset.sum_sub_distrib,
    mul_assoc,← Finset.mul_sum,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,if_true]

/-- Under the stated population conditions, the first full diffusion acts on type vectors with
coefficients given by `jwStep1`. -/
theorem jwBigDiff1_type_transport (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (jt : Fin (2*k+1)) :
    jwBigDiff1 N r *ᵥ jwPsiBigAt k N r I jt =
      ∑ i : Fin (2*k+1), jwStep1 k N r i jt • jwPsiBigAt k N r I i := by
  funext p
  obtain ⟨i,hi⟩ := jwTypeOf_exists_coord k N r I hI p
  rw [jwPsiBigAt_sum_apply k N r I _ p i hi,jwStep1_entry_types]
  change (jwBigDiff1 N r *ᵥ jwPsiBig k N r I (jwPsiCoord k jt).1 (jwPsiCoord k jt).2) p = _
  rw [jwBigDiff1_type_apply k N r (jwPsiCoord k jt).1 I hI]
  have hf : (p.1.1.filter fun x => decide (x ∈ I)) = p.1.1 ∩ I := by ext x; simp
  have hpi : (p.1.1 ∩ I).card = (jwPsiCoord k i).1 := by
    simpa only [jwTypeOf,hf] using congrArg Prod.fst hi
  by_cases hj : (jwPsiCoord k i).1 = (jwPsiCoord k jt).1
  · rw [if_pos hj]
    by_cases hjk : (jwPsiCoord k jt).1 = k
    · have ht : jwPsiCoord k jt = (k,false) := by
        apply Prod.ext hjk
        have hb : jt.val%2 ≠ 1 := by have ht := jt.isLt; change jt.val/2 = k at hjk; omega
        simp [jwPsiCoord,hb]
      have hi' : jwPsiCoord k i = (k,false) := by
        apply Prod.ext (hj.trans hjk)
        have hb : i.val%2 ≠ 1 := by
          have ht := i.isLt
          have hd : i.val/2 = k := hj.trans hjk
          omega
        simp [jwPsiCoord,hb]
      have hd : (((N-r : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : N-r ≠ 0)
      simp only [ht,hi',hpi]
      simp [jwD2,jwPsiBig,hi,hi']
      field_simp
      ring
    · let j := (jwPsiCoord k jt).1
      have hjlt : j < k := by
        have ht := jt.isLt
        dsimp [j,jwPsiCoord] at *
        omega
      let C : ℝ := (Nat.choose k j * Nat.choose (N-k) (r-j) : ℕ)
      let a : ℝ := (N-r-(k-j) : ℕ)
      let b : ℝ := (k-j : ℕ)
      have hC : 0 < C := by
        dsimp [C]
        exact_mod_cast Nat.mul_pos (Nat.choose_pos (le_of_lt hjlt)) (Nat.choose_pos (by omega))
      have ha : 0 < a := by dsimp [a]; exact_mod_cast (by omega : 0 < N-r-(k-j))
      have hb : 0 < b := by dsimp [b]; exact_mod_cast (by omega : 0 < k-j)
      have hab : a+b = ((N-r : ℕ) : ℝ) := by
        dsimp [a,b]
        rw [← Nat.cast_add]
        congr 1
        omega
      have he : (k-j : ℝ)/(N-r) = b/(a+b) := by
        rw [hab]
        dsimp [b]
        rw [Nat.cast_sub (le_of_lt hjlt),Nat.cast_sub (by omega : r ≤ N)]
      have hc (l : Bool) : (jwCnt k N r j l : ℝ) = C*(if l then b else a) := by
        cases l <;> simp [jwCnt,C,a,b,Nat.cast_mul]
      have hn := jwD2_fiber_normalized C a b hC ha hb
        (jwPsiCoord k i).2 (jwPsiCoord k jt).2
      rw [← hc (jwPsiCoord k i).2,← hc (jwPsiCoord k jt).2,← he,hab] at hn
      have htype : jwTypeOf I p = ((jwPsiCoord k jt).1,(jwPsiCoord k jt).2) ↔
          (jwPsiCoord k i).2 = (jwPsiCoord k jt).2 := by rw [hi]; simp [Prod.ext_iff,hj]
      rw [hpi,if_pos hj,jwPsiBig,if_congr htype rfl rfl,hj]

      convert hn.symm using 1
      all_goals dsimp only [a,b,j]
      all_goals split_ifs <;> push_cast <;> ring
  · have htype : jwTypeOf I p ≠ ((jwPsiCoord k jt).1,(jwPsiCoord k jt).2) := by
      intro h
      exact hj ((congrArg Prod.fst hi).symm.trans (congrArg Prod.fst h))
    simp [hpi,hj,jwPsiBig,htype]

/-- Counts inserted states with a prescribed type and the same subset as a fixed inserted state. -/
theorem jwFixedInsideType_card (N r : ℕ) (I : Finset (Fin N)) (p : JRState' N r)
    (j : ℕ) (l : Bool) :
    Fintype.card {q : JRState' N r // p.1.1 = q.1.1 ∧ jwTypeOfInserted I q = (j,l)} =
      if (p.1.1 ∩ I).card = j then (if l then j else r+1-j) else 0 := by
  by_cases hj : (p.1.1 ∩ I).card = j
  · rw [if_pos hj]
    let e : {q : JRState' N r // p.1.1 = q.1.1 ∧ jwTypeOfInserted I q = (j,l)} ≃
        {y : Fin N // y ∈ p.1.1 ∧ decide (y ∈ I) = l} :=
      { toFun := fun q => ⟨q.1.1.2,by simpa only [q.2.1] using q.1.2.2,
          congrArg Prod.snd q.2.2⟩
        invFun := fun y => ⟨⟨(p.1.1,y.1),p.2.1,y.2.1⟩,rfl,by
          exact Prod.ext hj y.2.2⟩
        left_inv := by
          intro q
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext q.2.1 rfl
        right_inv := by intro y; rfl }
    rw [Fintype.card_congr e]
    simpa [hj] using jwInsideTypeFiber_card N r I p.1.1 p.2.1 l
  · rw [if_neg hj]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun q => ?_⟩
    have hj' : (q.1.1.1 ∩ I).card = j := congrArg Prod.fst q.2.2
    exact hj (q.2.1 ▸ hj')

/-- The second reduced half-step has `jwD2` entries within equal inserted intersection counts
and zero entries between different counts. -/
theorem jwStep2_entry_types (k r : ℕ) (i j : Fin (2*k+1)) :
    jwStep2 k r i j =
      if (jwPhiCoord k i).1 = (jwPhiCoord k j).1 then
        jwD2 ((jwPhiCoord k j).1/(r+1))
          (jwPhiCoord k i).2 (jwPhiCoord k j).2 else 0 := by
  by_cases hi : i.val%2 = 1 <;> by_cases hj : j.val%2 = 1
  · have hdi : (i.val+1)/2 = i.val/2+1 := by omega
    simp [jwStep2,jwPsiCoord,jwPhiCoord,hi,hj,hdi]
  · have hdi : (i.val+1)/2 = i.val/2+1 := by omega
    have hzj : j.val%2 = 0 := by omega
    simp [jwStep2,jwPsiCoord,jwPhiCoord,hi,hzj,hdi]
  · have hdi : (i.val+1)/2 = i.val/2 := by omega
    have hzi : i.val%2 = 0 := by omega
    simp [jwStep2,jwPsiCoord,jwPhiCoord,hzi,hj,hdi,jwD2]
  · have hdi : (i.val+1)/2 = i.val/2 := by omega
    have hzi : i.val%2 = 0 := by omega
    have hzj : j.val%2 = 0 := by omega
    simp [jwStep2,jwPsiCoord,jwPhiCoord,hzi,hzj,hdi]

/-- Computes the second full diffusion on an embedded type vector from the inserted-type fiber
count and its normalization. -/
theorem jwBigDiff2_embed_type_apply (k N r : ℕ) (I : Finset (Fin N))
    (i : Fin (2*k+1)) (p : JRState' N r) :
    (jwBigDiff2 N r *ᵥ (jwEmbedMat N r *ᵥ jwPsiBigAt k N r I i)) p =
      (2 / ((r+1 : ℕ) : ℂ)) *
        (if (p.1.1 ∩ I).card = (jwPhiCoord k i).1 then
          ((if (jwPhiCoord k i).2 then (jwPhiCoord k i).1 else r+1-(jwPhiCoord k i).1 : ℕ) : ℂ) else 0) *
        ((1 / Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℝ) : ℂ) -
      (jwEmbedMat N r *ᵥ jwPsiBigAt k N r I i) p := by
  rw [jwBigDiff2_apply]
  have he (q : JRState' N r) :
      (if p.1.1 = q.1.1 then (jwEmbedMat N r *ᵥ jwPsiBigAt k N r I i) q else 0) =
        if p.1.1 = q.1.1 ∧ jwTypeOfInserted I q = jwPhiCoord k i then
          ((1 / Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℂ) : ℂ) else 0 := by
    rw [jwEmbedMat_type_apply]
    by_cases hs : p.1.1 = q.1.1 <;> by_cases ht : jwTypeOfInserted I q = jwPhiCoord k i <;>
      simp [hs,ht]
  simp_rw [he]
  rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun q : JRState' N r =>
      p.1.1 = q.1.1 ∧ jwTypeOfInserted I q = jwPhiCoord k i).card =
        if (p.1.1 ∩ I).card = (jwPhiCoord k i).1 then
          (if (jwPhiCoord k i).2 then (jwPhiCoord k i).1 else r+1-(jwPhiCoord k i).1) else 0 := by
    simpa [Fintype.subtype_card] using
        jwFixedInsideType_card N r I p (jwPhiCoord k i).1 (jwPhiCoord k i).2
  rw [hcard]
  push_cast
  split_ifs <;> ring

/-- Under the stated population conditions, expresses a type population using inserted
intersection counts, two binomial coefficients, and the appropriate inside-element count. -/
theorem jwCnt_phi_population (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (i : Fin (2*k+1)) :
    jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 =
      Nat.choose k (jwPhiCoord k i).1 * Nat.choose (N-k) (r+1-(jwPhiCoord k i).1) *
        (if (jwPhiCoord k i).2 then (jwPhiCoord k i).1 else r+1-(jwPhiCoord k i).1) := by
  have hφ : (jwPhiCoord k i).1 ≤ k := by have hi := i.isLt; dsimp [jwPhiCoord]; omega
  have he := congrArg Prod.fst (jwPhiCoord_eq_psi k i)
  have hb : (jwPhiCoord k i).2 = (jwPsiCoord k i).2 := rfl
  by_cases h : (jwPsiCoord k i).2 = true
  · have hpos : 1 ≤ (jwPhiCoord k i).1 := by simp only [h,if_true] at he; omega
    have hj : (jwPsiCoord k i).1 = (jwPhiCoord k i).1-1 := by simp only [h,if_true] at he; omega
    rw [h,hj,jwCnt_inserted_true k N r (jwPhiCoord k i).1 hpos (by omega) hφ]
    simp [hb,h]
  · have hfalse : (jwPsiCoord k i).2 = false := Bool.eq_false_iff.mpr h
    have hj : (jwPsiCoord k i).1 = (jwPhiCoord k i).1 := by simpa [hfalse] using he.symm
    rw [hfalse,hj,jwCnt_inserted_false k N r (jwPhiCoord k i).1 (by omega) hφ (le_of_lt hkNr)]
    simp [hb,hfalse]

/-- Under the stated population conditions, embedding, applying the second full diffusion, and
dropping acts on type vectors with coefficients given by `jwStep2`. -/
theorem jwBigDiff2_type_transport (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (jt : Fin (2*k+1)) :
    jwDropMat N r *ᵥ (jwBigDiff2 N r *ᵥ (jwEmbedMat N r *ᵥ jwPsiBigAt k N r I jt)) =
      ∑ i : Fin (2*k+1), jwStep2 k r i jt • jwPsiBigAt k N r I i := by
  funext p
  obtain ⟨i,hi⟩ := jwTypeOf_exists_coord k N r I hI p
  rw [jwDropMat_mulVec,jwPsiBigAt_sum_apply k N r I _ p i hi,jwStep2_entry_types,
    jwBigDiff2_embed_type_apply,jwEmbedMat_type_apply]
  have hin : jwTypeOfInserted I (jwInsertEquiv N r p) = jwPhiCoord k i :=
    (jwInsert_type_iff k N r I p i).mpr hi
  have hpi : ((jwInsertEquiv N r p).1.1 ∩ I).card = (jwPhiCoord k i).1 :=
    congrArg Prod.fst hin
  by_cases hj : (jwPhiCoord k i).1 = (jwPhiCoord k jt).1
  · rw [if_pos hj]
    by_cases hj0 : (jwPhiCoord k jt).1 = 0
    · have ht : jwPhiCoord k jt = (0,false) := by
        apply Prod.ext hj0
        have hb : jt.val%2 ≠ 1 := by
          have hd : (jt.val+1)/2 = 0 := hj0
          omega
        simp [jwPhiCoord,hb]
      have hi' : jwPhiCoord k i = (0,false) := by
        apply Prod.ext (hj.trans hj0)
        have hb : i.val%2 ≠ 1 := by
          have hd : (i.val+1)/2 = 0 := hj.trans hj0
          omega
        simp [jwPhiCoord,hb]
      have he (t : Fin (2*k+1)) (ht : jwPhiCoord k t = (0,false)) :
          jwPsiCoord k t = (0,false) := by
        have hφ := jwPhiCoord_eq_psi k t
        have h1 := congrArg Prod.fst ht
        have h2 := congrArg Prod.snd ht
        apply Prod.ext
        · dsimp [jwPhiCoord,jwPsiCoord] at *
          omega
        · exact h2
      have hd : ((r+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : r+1 ≠ 0)
      simp only [ht,hi',he jt ht,he i hi',hin,hpi]
      simp [jwD2]
      field_simp
      ring
    · let j := (jwPhiCoord k jt).1
      have hjpos : 1 ≤ j := by dsimp [j]; omega
      have hjk : j ≤ k := by have ht := jt.isLt; dsimp [j,jwPhiCoord]; omega
      let C : ℝ := (Nat.choose k j * Nat.choose (N-k) (r+1-j) : ℕ)
      let a : ℝ := (r+1-j : ℕ)
      let b : ℝ := (j : ℕ)
      have hC : 0 < C := by
        dsimp [C]
        exact_mod_cast Nat.mul_pos (Nat.choose_pos hjk) (Nat.choose_pos (by omega))
      have ha : 0 < a := by dsimp [a]; exact_mod_cast (by omega : 0 < r+1-j)
      have hb : 0 < b := by dsimp [b]; exact_mod_cast (by omega : 0 < j)
      have hab : a+b = ((r+1 : ℕ) : ℝ) := by
        dsimp [a,b]
        rw [← Nat.cast_add]
        congr 1
        omega
      have he : (j : ℝ)/(r+1) = b/(a+b) := by rw [hab]; simp [b]
      have hc (t : Fin (2*k+1)) (ht : (jwPhiCoord k t).1 = j) :
          (jwCnt k N r (jwPsiCoord k t).1 (jwPsiCoord k t).2 : ℝ) =
            C*(if (jwPhiCoord k t).2 then b else a) := by
        rw [jwCnt_phi_population k N r hkr hkNr t,ht]
        cases hbit : (jwPhiCoord k t).2 <;> simp [C,a,b,Nat.cast_mul]
      have hn := jwD2_fiber_normalized C a b hC ha hb
        (jwPhiCoord k i).2 (jwPhiCoord k jt).2
      rw [← hc i hj,← hc jt rfl,← he,hab] at hn
      have htype : jwTypeOfInserted I (jwInsertEquiv N r p) = jwPhiCoord k jt ↔
          (jwPhiCoord k i).2 = (jwPhiCoord k jt).2 := by rw [hin]; simp [Prod.ext_iff,hj]
      simp only [hpi,if_pos hj]
      simp only [htype]
      convert hn.symm using 1
      all_goals dsimp only [a,b,j]
      all_goals split_ifs <;> push_cast <;> ring
  · have htype : jwTypeOfInserted I (jwInsertEquiv N r p) ≠ jwPhiCoord k jt := by
      intro h
      exact hj ((congrArg Prod.fst hin).symm.trans (congrArg Prod.fst h))
    simp [hpi,hj,htype]

/-- Under the stated population conditions, the full Johnson walk acts on type vectors with
coefficients given by `jwWalk`. -/
theorem jwWalkBig_type_transport (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (jt : Fin (2*k+1)) :
    jwWalkBig N r *ᵥ jwPsiBigAt k N r I jt =
      ∑ i : Fin (2*k+1), jwWalk k N r i jt • jwPsiBigAt k N r I i := by
  rw [jwWalkBig,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    jwBigDiff1_type_transport k N r hkr hkNr I hI]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul]
  simp_rw [jwBigDiff2_type_transport k N r hkr hkNr I hI]
  simp only [Finset.smul_sum,smul_smul,jwWalk,Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- Establishes transport of the full walk and marked flip to the reduced type space in
`WalkTypeTransport`. See [Ambainis2007ElementDistinctness]. -/
theorem walkTypeTransport_answer : WalkTypeTransport := by
  intro k N r _ hkr hkNr I hI
  exact ⟨jwWalkBig_type_transport k N r hkr hkNr I hI,
    jwFlipBig_type_transport k N r I hI⟩

/-- The linear combination of full type vectors with coefficients given by a reduced coordinate
vector. -/
noncomputable def jwTypeLift (k N r : ℕ) (I : Finset (Fin N))
    (v : Fin (2*k+1) → ℂ) : JRState N r → ℂ :=
  ∑ i : Fin (2*k+1), v i • jwPsiBigAt k N r I i

/-- An operator identity on each vector of a finite family extends to every linear combination
with coefficients transformed by the corresponding coefficient matrix. -/
private theorem matrix_typeLift_transport {n m : Type} [Fintype n] [Fintype m]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (P : n → m → ℂ)
    (h : ∀ j, A *ᵥ P j = ∑ i, B i j • P i) (v : n → ℂ) :
    A *ᵥ (∑ i, v i • P i) = ∑ i, (B *ᵥ v) i • P i := by
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul]
  simp_rw [h]
  simp only [Finset.smul_sum,smul_smul,Matrix.mulVec,dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- Under the stated population conditions, applying the full Johnson walk to a lifted vector
equals lifting the reduced walk's action. -/
theorem jwWalkBig_typeLift (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (v : Fin (2*k+1) → ℂ) :
    jwWalkBig N r *ᵥ jwTypeLift k N r I v =
      jwTypeLift k N r I (jwWalk k N r *ᵥ v) :=
  matrix_typeLift_transport _ _ _ (jwWalkBig_type_transport k N r hkr hkNr I hI) v

/-- When `I.card = k`, applying the full marked flip to a lifted vector equals lifting the
reduced marked flip's action. -/
theorem jwFlipBig_typeLift (k N r : ℕ) (I : Finset (Fin N)) (hI : I.card = k)
    (v : Fin (2*k+1) → ℂ) :
    jwFlipBig k N r I *ᵥ jwTypeLift k N r I v =
      jwTypeLift k N r I (jwFlipTilde k *ᵥ v) :=
  matrix_typeLift_transport _ _ _ (jwFlipBig_type_transport k N r I hI) v

/-- Under the stated population conditions, every power of the full Johnson walk intertwines
with the same power of the reduced walk through `jwTypeLift`. -/
theorem jwWalkBig_pow_typeLift (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (t : ℕ) (v : Fin (2*k+1) → ℂ) :
    jwWalkBig N r ^ t *ᵥ jwTypeLift k N r I v =
      jwTypeLift k N r I (jwWalk k N r ^ t *ᵥ v) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ',pow_succ',← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,ih,
      jwWalkBig_typeLift k N r hkr hkNr I hI]

/-- Under the stated population conditions, the full iteration matrix intertwines with repeated
reduced walk powers and marked flips through `jwTypeLift`. -/
theorem jwRunMat_typeLift (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (t1 t2 : ℕ) (v : Fin (2*k+1) → ℂ) :
    jwRunMat k N r t1 t2 I *ᵥ jwTypeLift k N r I v =
      jwTypeLift k N r I ((jwWalk k N r ^ t2 * jwFlipTilde k) ^ t1 *ᵥ v) := by
  unfold jwRunMat
  induction t1 with
  | zero => simp
  | succ t ih =>
    rw [pow_succ',pow_succ',← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,ih,
      ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
      jwFlipBig_typeLift k N r I hI,jwWalkBig_pow_typeLift k N r hkr hkNr I hI]

end Qatlib.Concepts.WalkFind.WalkSpectrum
