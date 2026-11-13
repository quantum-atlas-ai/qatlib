/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Multinomial
import Qatlib.Papers.LatticeProd19.MainResults.SourceModel
import Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus.Corollary1

set_option backward.isDefEq.respectTransparency false

/-!
# Mixed Partial Differentiation Rule for Abbreviated Adjoint Sequences

This module proves Proposition 2: the mixed partial derivative with respect to
`(τ_1, ..., τ_m)` of a composed sequence of exponential-adjoint blocks `Ad^{γ_i}_{τ_i}`
and commutator blocks `ad^{δ_i}` expands as the product of multinomial sums over
ordered compositions `v_{i,1} + ⋯ + v_{i,γ_i} = w_i`.

## Main statements

* `foldOps`, `block`, `abbrevAd`: abbreviated adjoint operator sequence.
* `diffBlock`, `diffBlockFull`, `Comp`, `rhsAd`, `mixedDeriv`: multinomial derivative expansion.
* `proposition2_abbreviated_adjoint_rule`: `mixedDeriv w (fun τ => abbrevAd γ δ X Y τ Z) τ = rhsAd γ δ X Y w τ Z`.

## References

* [Childs and Su, 2019][ChildsSu2019], Proposition 2, Eqs. (42)--(45), pp. 7--8.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus

open Qatlib.Papers.LatticeProd19.MainResults.SourceModel

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- Fold a list of endomorphisms, leftmost outermost: `foldOps [f, g] Z = f (g Z)`. -/
def foldOps (fs : List (𝔸 → 𝔸)) (Z : 𝔸) : 𝔸 :=
  fs.foldr (fun f acc => f acc) Z

/-- One block `Ad_{τ X_1} ⋯ Ad_{τ X_γ} ad_{Y_1} ⋯ ad_{Y_δ}` of the sequence. -/
def block {γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸) (τ : ℝ) : 𝔸 → 𝔸 :=
  fun Z =>
    foldOps (List.ofFn (fun j : Fin γ => AdExp (X j) τ))
      (foldOps (List.ofFn (fun j : Fin δ => ad (Y j))) Z)

/-- The abbreviated adjoint representation evaluated at `τ : Fin m → ℝ` and applied to `Z`. -/
def abbrevAd {m : ℕ} (γ δ : Fin m → ℕ)
    (X : (i : Fin m) → Fin (γ i) → 𝔸)
    (Y : (i : Fin m) → Fin (δ i) → 𝔸)
    (τ : Fin m → ℝ) (Z : 𝔸) : 𝔸 :=
  foldOps (List.ofFn (fun i : Fin m => block (X i) (Y i) (τ i))) Z

/-- The differentiated block `(Ad_τ ad^{v_1}) ⋯ (Ad_τ ad^{v_γ})`. -/
def diffBlock {γ : ℕ} (X : Fin γ → 𝔸) (τ : ℝ) (v : Fin γ → ℕ) : 𝔸 → 𝔸 :=
  fun Z =>
    foldOps (List.ofFn (fun j : Fin γ =>
      fun W => AdExp (X j) τ (adPow (X j) (v j) W))) Z

/-- The differentiated block followed by the `ad^{δ}` part. -/
def diffBlockFull {γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸) (τ : ℝ)
    (v : Fin γ → ℕ) : 𝔸 → 𝔸 :=
  fun Z => diffBlock X τ v (foldOps (List.ofFn (fun j : Fin δ => ad (Y j))) Z)

/-- Ordered compositions of `w` into `γ` nonnegative parts. -/
abbrev Comp (γ w : ℕ) : Type :=
  {v : Fin γ → Fin (w + 1) // ∑ j : Fin γ, ((v j : Fin (w + 1)) : ℕ) = w}

/-- The multinomial sum for the mixed derivative of order `w : Fin m → ℕ`. -/
def rhsAd {m : ℕ} (γ δ : Fin m → ℕ)
    (X : (i : Fin m) → Fin (γ i) → 𝔸)
    (Y : (i : Fin m) → Fin (δ i) → 𝔸)
    (w : Fin m → ℕ) (τ : Fin m → ℝ) (Z : 𝔸) : 𝔸 :=
  ∑ v : (i : Fin m) → Comp (γ i) (w i),
    (∏ i : Fin m,
        ((Nat.multinomial Finset.univ (fun j : Fin (γ i) => ((v i).val j : ℕ)) : ℕ) : ℝ)) •
      foldOps (List.ofFn (fun i : Fin m =>
        diffBlockFull (X i) (Y i) (τ i) (fun j : Fin (γ i) => ((v i).val j : ℕ)))) Z

/-- Mixed partial derivative of a function of `m` real variables in coordinate order `0, ..., m - 1`. -/
def mixedDeriv {m : ℕ} (w : Fin m → ℕ) (F : (Fin m → ℝ) → 𝔸) :
    (Fin m → ℝ) → 𝔸 :=
  (List.ofFn (fun i : Fin m => i)).foldr
    (fun i G => fun τ =>
      iteratedDeriv (w i) (fun s : ℝ => G (Function.update τ i s)) (τ i)) F

private def adLinear (X : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ContinuousLinearMap.mul ℝ 𝔸 X - (ContinuousLinearMap.mul ℝ 𝔸).flip X

private def adjLinear (X : 𝔸) (t : ℝ) : 𝔸 →L[ℝ] 𝔸 :=
  ((ContinuousLinearMap.mul ℝ 𝔸).flip (expm (-X) t)).comp
    (ContinuousLinearMap.mul ℝ 𝔸 (expm X t))

private def powLinear (X : 𝔸) : ℕ → 𝔸 →L[ℝ] 𝔸
  | 0 => ContinuousLinearMap.id ℝ 𝔸
  | k + 1 => (adLinear X).comp (powLinear X k)

omit [CompleteSpace 𝔸] in
private theorem powLinear_apply (X : 𝔸) (k : ℕ) (W : 𝔸) :
    powLinear X k W = adPow X k W := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ad X (powLinear X k W) = (ad X)^[k + 1] W
    rw [Function.iterate_succ_apply', ih]
    rfl

private def foldLinear (fs : List (𝔸 →L[ℝ] 𝔸)) : 𝔸 →L[ℝ] 𝔸 :=
  fs.foldr ContinuousLinearMap.comp (ContinuousLinearMap.id ℝ 𝔸)

omit [CompleteSpace 𝔸] in
private theorem foldLinear_apply (fs : List (𝔸 →L[ℝ] 𝔸)) (W : 𝔸) :
    foldLinear fs W = foldOps (fs.map (fun (L : 𝔸 →L[ℝ] 𝔸) => (L : 𝔸 → 𝔸))) W := by
  induction fs with
  | nil => rfl
  | cons L fs ih => exact congrArg L ih

omit [CompleteSpace 𝔸] in
private theorem deriv_linear (L : 𝔸 →L[ℝ] 𝔸) (g : ℝ → 𝔸)
    (hg : ContDiff ℝ ⊤ g) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun s => L (g s)) t = L (iteratedDeriv n g t) := by
  simpa only [iteratedDeriv_eq_iteratedFDeriv, Function.comp_def,
    ContinuousLinearMap.compContinuousMultilinearMap_coe] using
    congrArg (fun f => f (fun _ => (1 : ℝ)))
      (L.iteratedFDeriv_comp_left hg.contDiffAt (i := n) (by simp))

private theorem smooth_expm (X : 𝔸) : ContDiff ℝ ⊤ (expm X) := by
  have h : ContDiff ℂ ⊤ (fun z : ℂ => NormedSpace.exp (z • X)) :=
    (contDiff_iff_contDiffAt.mpr (fun z : 𝔸 =>
      (NormedSpace.exp_analytic (𝕂 := ℂ) z).contDiffAt)).comp
        (contDiff_id.smul contDiff_const)
  exact h.restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff

private theorem smooth_adj (X : 𝔸) (g : ℝ → 𝔸) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ (fun s => AdExp X s (g s)) :=
  ((smooth_expm X).mul hg).mul (smooth_expm (-X))

private theorem smooth_fold {n : ℕ} (X : Fin n → 𝔸) (W : 𝔸) :
    ContDiff ℝ ⊤ (fun s => foldOps (List.ofFn (fun j => AdExp (X j) s)) W) := by
  induction n with
  | zero => simpa [foldOps] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => W))
  | succ n ih =>
    simpa [List.ofFn_succ, foldOps] using
      smooth_adj (X 0) _ (ih (fun j => X j.succ))

private def compJoin {n w : ℕ} (k : Fin (w + 1)) (v : Comp n (w - k)) :
    Comp (n + 1) w :=
  ⟨Fin.cons k (fun j => ⟨v.val j, lt_of_lt_of_le (v.val j).isLt
    (Nat.succ_le_succ (Nat.sub_le w k))⟩), by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [v.property, Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)]⟩

private def compSplit {n w : ℕ} (v : Comp (n + 1) w) :
    (k : Fin (w + 1)) × Comp n (w - k) :=
  ⟨v.val 0, ⟨fun j => ⟨v.val j.succ, by
    have hs := v.property
    rw [Fin.sum_univ_succ] at hs
    have hj := Finset.single_le_sum (fun i _ => Nat.zero_le (v.val i.succ : ℕ))
      (Finset.mem_univ j)
    omega⟩, by
      have hs := v.property
      rw [Fin.sum_univ_succ] at hs
      dsimp
      omega⟩⟩

private def compEquiv (n w : ℕ) :
    ((k : Fin (w + 1)) × Comp n (w - k)) ≃ Comp (n + 1) w where
  toFun p := compJoin p.1 p.2
  invFun := compSplit
  left_inv p := by
    rcases p with ⟨k, v⟩
    apply Sigma.ext rfl
    rfl
  right_inv v := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

private theorem multinomial_succ {n : ℕ} (v : Fin (n + 1) → ℕ) :
    Nat.multinomial Finset.univ v =
      (∑ j, v j).choose (v 0) * Nat.multinomial Finset.univ (fun j : Fin n => v j.succ) := by
  have h : (Finset.univ : Finset (Fin (n + 1))) =
      Finset.cons 0 (Finset.univ.map (Fin.succEmb n)) (by simp) := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  conv_lhs => rw [h, Nat.multinomial_cons]
  have hm : Nat.multinomial (Finset.univ.map (Fin.succEmb n)) v =
      Nat.multinomial Finset.univ (fun j : Fin n => v j.succ) := by
    simp [Nat.multinomial]
  rw [hm, Fin.sum_univ_succ]
  simp

private theorem iteratedDeriv_block_const {n : ℕ} (X : Fin n → 𝔸)
    (W : 𝔸) (w : ℕ) (t : ℝ) :
    iteratedDeriv w (fun s => foldOps (List.ofFn (fun j => AdExp (X j) s)) W) t =
      ∑ v : Comp n w,
        (Nat.multinomial Finset.univ (fun j => (v.val j : ℕ)) : ℝ) •
          diffBlock X t (fun j => (v.val j : ℕ)) W := by
  induction n generalizing w with
  | zero =>
    cases w with
    | zero =>
      let v : Comp 0 0 := ⟨Fin.elim0, by simp⟩
      have : Unique (Comp 0 0) := ⟨⟨v⟩, fun a => Subtype.ext (funext (fun j => Fin.elim0 j))⟩
      simp [foldOps, diffBlock, Nat.multinomial]
    | succ w =>
      have : IsEmpty (Comp 0 (w + 1)) := ⟨fun v => by simpa using v.property⟩
      simp [foldOps, iteratedDeriv_const]
  | succ n ih =>
    have hc : iteratedDeriv w (fun s => AdExp (X 0) s
        (foldOps (List.ofFn (fun j : Fin n => AdExp (X j.succ) s)) W)) t =
        ∑ k ∈ Finset.range (w + 1), (w.choose k : ℝ) •
          AdExp (X 0) t (adPow (X 0) k
            (iteratedDeriv (w - k) (fun s =>
              foldOps (List.ofFn (fun j : Fin n => AdExp (X j.succ) s)) W) t)) := by
      cases w with
      | zero => simp
      | succ w => exact corollary1_higher_order_rule _ _ (smooth_fold _ _) _ (by omega) _
    conv_lhs => simp only [List.ofFn_succ, foldOps, List.foldr_cons]
    change iteratedDeriv w (fun s => AdExp (X 0) s
      (foldOps (List.ofFn (fun j : Fin n => AdExp (X j.succ) s)) W)) t = _
    rw [hc]
    simp_rw [ih]
    have hlin (k : ℕ) (U : 𝔸) :
        AdExp (X 0) t (adPow (X 0) k U) =
          ((adjLinear (X 0) t).comp (powLinear (X 0) k)) U := by
      simp [adjLinear, powLinear_apply, AdExp]
    simp_rw [hlin, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [← Fin.sum_univ_eq_sum_range]
    let f (p : (k : Fin (w + 1)) × Comp n (w - k)) : 𝔸 :=
      ((w.choose p.1 : ℝ) *
        (Nat.multinomial Finset.univ (fun j => (p.2.val j : ℕ)) : ℝ)) •
        ((adjLinear (X 0) t).comp (powLinear (X 0) p.1))
          (diffBlock (fun j => X j.succ) t (fun j => (p.2.val j : ℕ)) W)
    change (∑ k, ∑ v, f ⟨k, v⟩) = _
    rw [← Fintype.sum_sigma f]
    refine Fintype.sum_equiv (compEquiv n w) _ _ (fun p => ?_)
    rcases p with ⟨k, v⟩
    dsimp [compEquiv]
    rw [multinomial_succ, (compJoin k v).property, Nat.cast_mul]
    simp [f, diffBlock, List.ofFn_succ, foldOps, compJoin, adjLinear, powLinear_apply, AdExp]

private def blockLinear {γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸)
    (t : ℝ) : 𝔸 →L[ℝ] 𝔸 :=
  (foldLinear (List.ofFn (fun j => adjLinear (X j) t))).comp
    (foldLinear (List.ofFn (fun j => adLinear (Y j))))

omit [CompleteSpace 𝔸] in
private theorem blockLinear_apply {γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸)
    (t : ℝ) (W : 𝔸) : blockLinear X Y t W = block X Y t W := by
  simp only [blockLinear, ContinuousLinearMap.comp_apply, foldLinear_apply, List.map_ofFn]
  rfl

private def fullLinear {γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸)
    (t : ℝ) (v : Fin γ → ℕ) : 𝔸 →L[ℝ] 𝔸 :=
  (foldLinear (List.ofFn (fun j => (adjLinear (X j) t).comp (powLinear (X j) (v j))))).comp
    (foldLinear (List.ofFn (fun j => adLinear (Y j))))

omit [CompleteSpace 𝔸] in
private theorem fullLinear_apply {γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸)
    (t : ℝ) (v : Fin γ → ℕ) (W : 𝔸) :
    fullLinear X Y t v W = diffBlockFull X Y t v W := by
  simp only [fullLinear, ContinuousLinearMap.comp_apply, foldLinear_apply, List.map_ofFn]
  have h (j : Fin γ) :
      ((adjLinear (X j) t).comp (powLinear (X j) (v j)) : 𝔸 → 𝔸) =
        fun W => AdExp (X j) t (adPow (X j) (v j) W) := by
    funext W
    simp [adjLinear, powLinear_apply, AdExp]
  simp only [Function.comp_def, h]
  rfl

omit [CompleteSpace 𝔸] in
private theorem smooth_parameter {m : ℕ} (F : (Fin m → ℝ) → ℝ → 𝔸)
    (hF : ContDiff ℝ ⊤ (Function.uncurry F)) (n : ℕ) :
    ContDiff ℝ ⊤ (Function.uncurry (fun τ => iteratedDeriv n (F τ))) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    have hh : ContDiff ℝ ⊤ (fun p : (((Fin m → ℝ) × ℝ) × ℝ) =>
        iteratedDeriv n (F p.1.1) p.2) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have h := (ContDiff.fderiv (n := ⊤) (f := fun p : (Fin m → ℝ) × ℝ =>
        fun s => iteratedDeriv n (F p.1) s) hh contDiff_snd (by simp)).clm_apply
          (contDiff_const (c := (1 : ℝ)))
    simpa only [Function.uncurry_def, iteratedDeriv_succ, deriv] using h

omit [CompleteSpace 𝔸] in
private theorem smooth_coordinate {m : ℕ} (F : (Fin m → ℝ) → 𝔸)
    (hF : ContDiff ℝ ⊤ F) (i : Fin m) (n : ℕ) :
    ContDiff ℝ ⊤ (fun τ => iteratedDeriv n (fun s => F (Function.update τ i s)) (τ i)) := by
  have hu : ContDiff ℝ ⊤ (fun p : (Fin m → ℝ) × ℝ => Function.update p.1 i p.2) := by
    apply contDiff_pi.mpr
    intro j
    by_cases hj : j = i
    · subst j; simpa using (contDiff_snd : ContDiff ℝ ⊤ (fun p : (Fin m → ℝ) × ℝ => p.2))
    · simpa only [Function.update_of_ne hj, Function.comp_def] using
        (contDiff_apply ℝ (fun _ : Fin m => ℝ) j).comp
        (contDiff_fst : ContDiff ℝ ⊤ (fun p : (Fin m → ℝ) × ℝ => p.1))
  exact (smooth_parameter (fun τ s => F (Function.update τ i s)) (hF.comp hu) n).comp
    (contDiff_id.prodMk (contDiff_apply ℝ (fun _ : Fin m => ℝ) i))

private def partialFold {m : ℕ} (w : Fin m → ℕ) (is : List (Fin m))
    (F : (Fin m → ℝ) → 𝔸) : (Fin m → ℝ) → 𝔸 :=
  is.foldr (fun i G τ => iteratedDeriv (w i) (fun s => G (Function.update τ i s)) (τ i)) F

omit [CompleteSpace 𝔸] in
private theorem smooth_partialFold {m : ℕ} (w : Fin m → ℕ) (is : List (Fin m))
    (F : (Fin m → ℝ) → 𝔸) (hF : ContDiff ℝ ⊤ F) :
    ContDiff ℝ ⊤ (partialFold w is F) := by
  induction is with
  | nil => exact hF
  | cons i is ih => exact smooth_coordinate _ ih i (w i)

omit [CompleteSpace 𝔸] in
private theorem separate_tail {m : ℕ} (w : Fin (m + 1) → ℕ) (is : List (Fin m))
    (L : ℝ → 𝔸 →L[ℝ] 𝔸) (G : (Fin m → ℝ) → 𝔸) (hG : ContDiff ℝ ⊤ G)
    (τ : Fin (m + 1) → ℝ) :
    partialFold w (is.map Fin.succ) (fun σ => L (σ 0) (G (fun j => σ j.succ))) τ =
      L (τ 0) (partialFold (fun j => w j.succ) is G (fun j => τ j.succ)) := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    change iteratedDeriv (w i.succ) (fun s =>
      partialFold w (is.map Fin.succ) _ (Function.update τ i.succ s)) (τ i.succ) = _
    simp_rw [ih]
    have hu (s : ℝ) : (fun j => Function.update τ i.succ s j.succ) =
        Function.update (fun j => τ j.succ) i s := by
      funext j
      by_cases h : j = i <;> simp [h, Fin.succ_inj]
    simp_rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, hu]
    exact deriv_linear (L (τ 0)) _
      ((smooth_partialFold _ is G hG).comp (contDiff_update ⊤ _ i)) _ _

private theorem smooth_block {m γ δ : ℕ} (X : Fin γ → 𝔸) (Y : Fin δ → 𝔸)
    (u : (Fin m → ℝ) → ℝ) (V : (Fin m → ℝ) → 𝔸)
    (hu : ContDiff ℝ ⊤ u) (hV : ContDiff ℝ ⊤ V) :
    ContDiff ℝ ⊤ (fun τ => block X Y (u τ) (V τ)) := by
  induction γ with
  | zero =>
    have h : (fun j => (adLinear (Y j) : 𝔸 → 𝔸)) = (fun j => ad (Y j)) := rfl
    simpa only [Function.comp_def, foldLinear_apply, List.map_ofFn,
      h, block, List.ofFn_zero, foldOps, List.foldr_nil] using
      (foldLinear (List.ofFn (fun j => adLinear (Y j)))).contDiff.comp hV
  | succ γ ih =>
    have ht := ih (fun j => X j.succ)
    simpa only [Function.comp_def, block, List.ofFn_succ, foldOps, List.foldr_cons, AdExp] using
      (((smooth_expm (X 0)).comp hu).mul ht).mul ((smooth_expm (-X 0)).comp hu)

private theorem smooth_abbrev {m : ℕ} (γ δ : Fin m → ℕ)
    (X : (i : Fin m) → Fin (γ i) → 𝔸) (Y : (i : Fin m) → Fin (δ i) → 𝔸)
    (Z : 𝔸) : ContDiff ℝ ⊤ (fun τ => abbrevAd γ δ X Y τ Z) := by
  induction m with
  | zero => simpa [abbrevAd, foldOps] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : Fin 0 → ℝ => Z))
  | succ m ih =>
    have ht := (ih (fun i => γ i.succ) (fun i => δ i.succ)
      (fun i => X i.succ) (fun i => Y i.succ)).comp
        (contDiff_pi.mpr (fun j => contDiff_apply ℝ (fun _ : Fin (m + 1) => ℝ) j.succ))
    simpa only [Function.comp_def, abbrevAd, List.ofFn_succ, foldOps, List.foldr_cons] using
      smooth_block (X 0) (Y 0) _ _
        (contDiff_apply ℝ (fun _ : Fin (m + 1) => ℝ) 0) ht

omit [CompleteSpace 𝔸] in
private theorem rhs_succ {m : ℕ} (γ δ : Fin (m + 1) → ℕ)
    (X : (i : Fin (m + 1)) → Fin (γ i) → 𝔸)
    (Y : (i : Fin (m + 1)) → Fin (δ i) → 𝔸)
    (Z : 𝔸) (w : Fin (m + 1) → ℕ) (τ : Fin (m + 1) → ℝ) :
    rhsAd γ δ X Y w τ Z =
      ∑ v : Comp (γ 0) (w 0),
        (Nat.multinomial Finset.univ (fun j => (v.val j : ℕ)) : ℝ) •
          diffBlockFull (X 0) (Y 0) (τ 0) (fun j => (v.val j : ℕ))
            (rhsAd (fun i => γ i.succ) (fun i => δ i.succ)
              (fun i => X i.succ) (fun i => Y i.succ)
              (fun i => w i.succ) (fun i => τ i.succ) Z) := by
  classical
  simp only [rhsAd, ← fullLinear_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [← (Fin.consEquiv (fun i => Comp (γ i) (w i))).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro vs _
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    List.ofFn_succ, foldOps, List.foldr_cons, fullLinear_apply]

/-- **Proposition 2**: the mixed partial derivative of the abbreviated adjoint
representation equals the multinomial sum of differentiated blocks. -/
theorem proposition2_abbreviated_adjoint_rule
    {m : ℕ} (γ δ : Fin m → ℕ)
    (X : (i : Fin m) → Fin (γ i) → 𝔸)
    (Y : (i : Fin m) → Fin (δ i) → 𝔸)
    (Z : 𝔸) (w : Fin m → ℕ) (τ : Fin m → ℝ) :
    mixedDeriv w (fun τ => abbrevAd γ δ X Y τ Z) τ =
      rhsAd γ δ X Y w τ Z := by
  classical
  induction m with
  | zero =>
    let : Unique ((i : Fin 0) → Comp (γ i) (w i)) :=
      ⟨⟨fun i => Fin.elim0 i⟩, fun v => funext (fun i => Fin.elim0 i)⟩
    simp [mixedDeriv, abbrevAd, rhsAd, foldOps]
  | succ m ih =>
    have ht (s : ℝ) :
        partialFold w ((List.ofFn (fun i : Fin m => i)).map Fin.succ)
          (fun σ => abbrevAd γ δ X Y σ Z) (Function.update τ 0 s) =
        blockLinear (X 0) (Y 0) s
          (rhsAd (fun i => γ i.succ) (fun i => δ i.succ)
            (fun i => X i.succ) (fun i => Y i.succ)
            (fun i => w i.succ) (fun i => τ i.succ) Z) := by
      have hb : (fun σ => abbrevAd γ δ X Y σ Z) =
          (fun σ => blockLinear (X 0) (Y 0) (σ 0)
            (abbrevAd (fun i => γ i.succ) (fun i => δ i.succ)
              (fun i => X i.succ) (fun i => Y i.succ) (fun i => σ i.succ) Z)) := by
        funext σ
        simp [abbrevAd, List.ofFn_succ, foldOps, blockLinear_apply]
      rw [hb, separate_tail w _ (blockLinear (X 0) (Y 0)) _
        (smooth_abbrev _ _ _ _ Z)]
      simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _),
        mixedDeriv, partialFold] using
        congrArg (blockLinear (X 0) (Y 0) s)
          (ih (fun i => γ i.succ) (fun i => δ i.succ)
            (fun i => X i.succ) (fun i => Y i.succ) (fun i => w i.succ)
            (fun i => τ i.succ))
    change partialFold w (List.ofFn (fun i : Fin (m + 1) => i)) _ τ = _
    rw [show List.ofFn (fun i : Fin (m + 1) => i) =
        0 :: (List.ofFn (fun i : Fin m => i)).map Fin.succ by
      simpa only [List.map_ofFn, Function.comp_def] using
        (List.ofFn_succ (f := fun i : Fin (m + 1) => i))]
    change iteratedDeriv (w 0) (fun s =>
      partialFold w ((List.ofFn (fun i : Fin m => i)).map Fin.succ)
        (fun σ => abbrevAd γ δ X Y σ Z) (Function.update τ 0 s)) (τ 0) = _
    simp_rw [ht, blockLinear_apply]
    simp only [block]
    rw [iteratedDeriv_block_const]
    exact (rhs_succ γ δ X Y Z w τ).symm

end Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus
