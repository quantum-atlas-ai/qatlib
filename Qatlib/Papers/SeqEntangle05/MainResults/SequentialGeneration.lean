/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace

namespace Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration

open Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs

def BlockFactorization (D : ℕ) : Prop :=
  ∀ B : Block D, ∃ (V : IsometryMatrix D) (M : Matrix (Fin D) (Fin D) ℂ),
    IsIsometry V ∧ ∀ i, B i = isoBlock V i * M

theorem orthonormal_sum_inner_smul_of_mem_span
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) {x : E}
    (hx : x ∈ Submodule.span 𝕜 (Set.range v)) :
    ∑ i, ⟪v i, x⟫_𝕜 • v i = x := by
  classical
  have hmain : ∀ y ∈ Submodule.span 𝕜 (Set.range v),
      ∑ i, ⟪v i, y⟫_𝕜 • v i = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [Finset.sum_eq_single i]
        · rw [orthonormal_iff_ite.mp hv i i, if_pos rfl, one_smul]
        · intro j _ hji
          rw [orthonormal_iff_ite.mp hv j i, if_neg hji, zero_smul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
    | zero => simp
    | add a b _ _ iha ihb =>
        have hsum : (∑ i, ⟪v i, a + b⟫_𝕜 • v i)
            = (∑ i, ⟪v i, a⟫_𝕜 • v i) + (∑ i, ⟪v i, b⟫_𝕜 • v i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [inner_add_right, add_smul]
        rw [hsum, iha, ihb]
    | smul c a _ iha =>
        have hstep : (∑ i, ⟪v i, c • a⟫_𝕜 • v i) = c • (∑ i, ⟪v i, a⟫_𝕜 • v i) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [inner_smul_right, mul_smul]
        rw [hstep, iha]
  exact hmain x hx

theorem blockFactorization (D : ℕ) : BlockFactorization D := by
  classical
  intro B
  let A : Matrix (Fin D × Fin 2) (Fin D) ℂ := fun p β => B p.2 p.1 β
  let E := EuclideanSpace ℂ (Fin D × Fin 2)
  let col : Fin D → E := fun β => WithLp.toLp 2 (fun p => A p β)
  let W : Submodule ℂ E := Submodule.span ℂ (Set.range col)
  let r : ℕ := Module.finrank ℂ W
  let bW : OrthonormalBasis (Fin r) ℂ W := stdOrthonormalBasis ℂ W
  have hWle : r ≤ D := by
    have h := finrank_range_le_card (R := ℂ) col
    have hr : r = Set.finrank ℂ (Set.range col) := rfl
    rw [hr]
    simpa using h
  have hEdim : Module.finrank ℂ E = Fintype.card (Fin D × Fin 2) := finrank_euclideanSpace
  let idx : Set (Fin (Module.finrank ℂ E)) := {i | i.val < r}
  let v : Fin (Module.finrank ℂ E) → E := fun i =>
    if h : i.val < r then (bW ⟨i.val, h⟩ : E) else 0
  have hv : Orthonormal ℂ (idx.restrict v) := by
    let e : idx → Fin r := fun i => ⟨i.val, i.prop⟩
    have he : Function.Injective e := by
      intro a b hab
      have hval : (e a).val = (e b).val := congrArg (fun x : Fin r => x.val) hab
      exact Subtype.ext (Fin.ext hval)
    have hbase : Orthonormal ℂ (fun i : Fin r => ((bW i : W) : E)) :=
      bW.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hcomp : Orthonormal ℂ (fun i : idx => ((bW (e i) : W) : E)) := hbase.comp e he
    have hfun : (idx.restrict v) = (fun i : idx => ((bW (e i) : W) : E)) := by
      funext i
      simp only [Set.restrict, v, e]
      exact dif_pos i.prop
    rw [hfun]
    exact hcomp
  obtain ⟨b', hb'⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℂ) (E := E) (ι := Fin (Module.finrank ℂ E)) (v := v) (s := idx)
    (by simp) hv
  have hDfin : D ≤ Module.finrank ℂ E := by
    rw [hEdim]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  let emb : Fin D → Fin (Module.finrank ℂ E) := fun β => ⟨β.val, lt_of_lt_of_le β.isLt hDfin⟩
  have hemb : Function.Injective emb := by
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin (Module.finrank ℂ E) => x.val) hab)
  let Wv : Submodule ℂ E := Submodule.span ℂ (Set.range (fun β => b' (emb β)))
  have horth : Orthonormal ℂ (fun β : Fin D => b' (emb β)) := b'.orthonormal.comp emb hemb
  have hbWin : ∀ i : Fin r, (bW i : E) ∈ Wv := by
    intro i
    have hiD : i.val < D := lt_of_lt_of_le i.isLt hWle
    refine Submodule.subset_span ⟨⟨i.val, hiD⟩, ?_⟩
    have hidx : emb ⟨i.val, hiD⟩ ∈ idx := by
      show (emb ⟨i.val, hiD⟩).val < r
      exact i.isLt
    have heq := hb' (emb ⟨i.val, hiD⟩) hidx
    show b' (emb ⟨i.val, hiD⟩) = (bW i : E)
    rw [heq]
    simp only [v]
    rw [dif_pos i.isLt]
  have hAsub : ∀ β : Fin D, col β ∈ Wv := by
    intro β
    have hxW : col β ∈ W := Submodule.subset_span ⟨β, rfl⟩
    have hexp : (∑ i : Fin r, ⟪((bW i : W) : E), col β⟫_ℂ • ((bW i : W) : E)) = col β := by
      have h := congrArg (Subtype.val) (bW.sum_repr' (⟨col β, hxW⟩ : W))
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul, Submodule.coe_inner] at h
      simpa using h
    rw [← hexp]
    refine Submodule.sum_mem (p := Wv) ?_
    intro i _
    exact Submodule.smul_mem _ _ (hbWin i)
  let Vm : Matrix (Fin D × Fin 2) (Fin D) ℂ := fun p β => WithLp.ofLp (b' (emb β)) p
  let M : Matrix (Fin D) (Fin D) ℂ := fun γ β => ⟪b' (emb γ), col β⟫_ℂ
  refine ⟨Vm, M, ?_, ?_⟩
  · show Matrix.conjTranspose Vm * Vm = 1
    ext γ γ'
    rw [Matrix.mul_apply]
    have hinner : ⟪b' (emb γ), b' (emb γ')⟫_ℂ
        = ∑ p, WithLp.ofLp (b' (emb γ')) p * star (WithLp.ofLp (b' (emb γ)) p) :=
      EuclideanSpace.inner_eq_star_dotProduct _ _
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply, Vm]
    rw [show (∑ p : Fin D × Fin 2,
          star (WithLp.ofLp (b' (emb γ)) p) * WithLp.ofLp (b' (emb γ')) p)
        = ∑ p, WithLp.ofLp (b' (emb γ')) p * star (WithLp.ofLp (b' (emb γ)) p) from
      Finset.sum_congr rfl (fun p _ => mul_comm _ _)]
    rw [← hinner, orthonormal_iff_ite.mp horth γ γ']
  · intro i
    ext α β
    simp only [isoBlock, Matrix.mul_apply, Vm, M]
    have hmem := hAsub β
    have hf := orthonormal_sum_inner_smul_of_mem_span horth hmem
    have hev := congrArg (fun z : E => WithLp.ofLp z (α, i)) hf
    have hev' : (∑ x, ⟪b' (emb x), col β⟫_ℂ • b' (emb x)).ofLp (α, i)
        = (col β).ofLp (α, i) := hev
    have hL : B i α β = WithLp.ofLp (col β) (α, i) := by
      simp [col, A]
    rw [hL, ← hev']
    have hsplit : (∑ x, ⟪b' (emb x), col β⟫_ℂ • b' (emb x)).ofLp
        = ∑ x, (⟪b' (emb x), col β⟫_ℂ • b' (emb x)).ofLp :=
      map_sum (WithLp.linearEquiv 2 ℂ ((Fin D × Fin 2) → ℂ)).toLinearMap _ Finset.univ
    have hcongr : (∑ x, ⟪b' (emb x), col β⟫_ℂ • b' (emb x)).ofLp (α, i)
        = (∑ x, (⟪b' (emb x), col β⟫_ℂ • b' (emb x)).ofLp) (α, i) :=
      congrFun hsplit (α, i)
    rw [hcongr, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro γ _
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem factorList {D : ℕ} (hfactor : BlockFactorization D)
    (C : Matrix (Fin D) (Fin D) ℂ) (pl : List (Block D)) :
    ∃ (Vs : List (IsometryMatrix D)) (M : Matrix (Fin D) (Fin D) ℂ),
      Vs.length = pl.length ∧ (∀ V ∈ Vs, IsIsometry V) ∧
      ∀ (is : List (Fin 2)), is.length = pl.length →
        C * prodBlocks pl is = prodBlocks (Vs.map isoBlockFamily) is * M := by
  induction pl generalizing C with
  | nil =>
      refine ⟨[], C, by simp, by simp, ?_⟩
      intro is his
      have his' : is = [] := by simpa using his
      subst his'
      simp
  | cons A As ih =>
      obtain ⟨V, M0, hV, hfac⟩ := hfactor (fun i => C * A i)
      obtain ⟨Vs, M, hlen, hiso, his⟩ := ih M0
      refine ⟨V :: Vs, M, by simp [hlen], ?_, ?_⟩
      · intro W hW
        rcases List.mem_cons.mp hW with rfl | hW
        · exact hV
        · exact hiso W hW
      · intro is hislen
        cases is with
        | nil => simp at hislen
        | cons i is' =>
            have hlen' : is'.length = As.length := by simpa using hislen
            simp only [prodBlocks_cons, List.map_cons]
            rw [← Matrix.mul_assoc, hfac i, Matrix.mul_assoc, his is' hlen']
            simp only [isoBlockFamily, Matrix.mul_assoc]

theorem isMPS_seqGenerable {D n : ℕ} (hfactor : BlockFactorization D)
    {ψ : (Fin n → Fin 2) → ℂ} (h : IsMPS D n ψ) : SeqGenerable D n ψ := by
  obtain ⟨A, φI, φF, hψ⟩ := h
  obtain ⟨Vs, M, hlen, hiso, his⟩ :=
    factorList hfactor (1 : Matrix (Fin D) (Fin D) ℂ) (List.ofFn A)
  have hlenA : (List.ofFn A).length = n := by simp
  have hVn : Vs.length = n := by rw [hlen, hlenA]
  subst hVn
  refine ⟨Vs.get, M *ᵥ φI, φF, ?_, ?_⟩
  · intro k
    exact hiso (Vs.get k) (List.get_mem Vs k)
  · intro bits
    have hlenbits : (List.ofFn bits).length = (List.ofFn A).length := by simp
    have hkey := his (List.ofFn bits) hlenbits
    rw [one_mul] at hkey
    rw [hψ bits]
    have hmap : List.ofFn (fun k => isoBlockFamily (Vs.get k)) = Vs.map isoBlockFamily := by
      rw [List.ofFn_comp', List.ofFn_get]
    simp only [mpsAmplitude, blockProd, hmap]
    rw [Matrix.mulVec_mulVec, hkey]

theorem isMPS_iff_seqGenerable {D n : ℕ} (hfactor : BlockFactorization D)
    {ψ : (Fin n → Fin 2) → ℂ} : IsMPS D n ψ ↔ SeqGenerable D n ψ :=
  ⟨isMPS_seqGenerable hfactor, seqGenerable_isMPS⟩

theorem isMPS_seqGenerable_uncond {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : IsMPS D n ψ) : SeqGenerable D n ψ :=
  isMPS_seqGenerable (blockFactorization D) h

theorem isMPS_iff_seqGenerable_uncond {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ} :
    IsMPS D n ψ ↔ SeqGenerable D n ψ :=
  isMPS_iff_seqGenerable (blockFactorization D)

end Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration
