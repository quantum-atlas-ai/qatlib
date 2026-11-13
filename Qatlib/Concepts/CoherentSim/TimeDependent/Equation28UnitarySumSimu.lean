/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28UnitarySumStat
import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28Simu

/-!
# Positive unitary sums for time dependent segments

This module proves `equation28UnitarySum` by expressing grid increments and their ordered
products as finite sums of unitaries with nonnegative coefficients. The coefficient weight lies
between one and the truncated exponential series in `Λ * τ`.

The mathematical context is discussed in [BerryEtAl2015Taylor].

## Main statements

* `HasUnitarySum`: A finite positive unitary representation with a specified total coefficient
  weight.
* `equation28UnitarySum`: The unitary representation and coefficient bounds for the grid
  segment.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.CoherentSim.TimeDependent
open Matrix
open scoped Classical BigOperators

/-- The matrix `A` is a finite sum of unitary matrices with nonnegative real coefficients whose
sum is `w`. -/
private def HasUnitarySum {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (w : ℝ) : Prop :=
  ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (β : D → ℝ) (V : D → Matrix I I ℂ),
    (∀ d, 0 ≤ β d) ∧ (∀ d, V d ∈ Matrix.unitaryGroup I ℂ) ∧
      A = ∑ d, (β d : ℂ) • V d ∧ ∑ d, β d = w

/-- The zero matrix has a positive unitary representation of total weight zero. -/
private theorem unitarySum_zero {I : Type} [Fintype I] [DecidableEq I] :
    HasUnitarySum (0 : Matrix I I ℂ) 0 := by
  refine ⟨Empty, inferInstance, inferInstance, (fun d => nomatch d), (fun d => nomatch d), ?_⟩
  simp

/-- The identity matrix has a positive unitary representation of total weight one. -/
private theorem unitarySum_one {I : Type} [Fintype I] [DecidableEq I] :
    HasUnitarySum (1 : Matrix I I ℂ) 1 := by
  refine ⟨Unit, inferInstance, inferInstance, (fun _ => 1), (fun _ => 1), ?_⟩
  simp

/-- Adding positive unitary representations adds their total coefficient weights. -/
private theorem unitarySum_add {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} {a b : ℝ} (hA : HasUnitarySum A a) (hB : HasUnitarySum B b) :
    HasUnitarySum (A+B) (a+b) := by
  obtain ⟨D,hD,dD,β,V,hβ,hV,he,hw⟩ := hA
  obtain ⟨E,hE,dE,γ,W,hγ,hW,hf,hz⟩ := hB
  letI := hD
  letI := dD
  letI := hE
  letI := dE
  refine ⟨D ⊕ E, inferInstance, inferInstance, Sum.elim β γ, Sum.elim V W, ?_, ?_, ?_, ?_⟩
  · intro d; cases d with | inl d => exact hβ d | inr e => exact hγ e
  · intro d; cases d with | inl d => exact hV d | inr e => exact hW e
  · rw [Fintype.sum_sum_type]
    change A+B = (∑ d, (β d : ℂ) • V d) + (∑ e, (γ e : ℂ) • W e)
    rw [← he, ← hf]
  · simp [Fintype.sum_sum_type, hw, hz]

/-- Multiplying positive unitary representations multiplies their total coefficient weights. -/
private theorem unitarySum_mul {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} {a b : ℝ} (hA : HasUnitarySum A a) (hB : HasUnitarySum B b) :
    HasUnitarySum (A*B) (a*b) := by
  obtain ⟨D,hD,dD,β,V,hβ,hV,he,hw⟩ := hA
  obtain ⟨E,hE,dE,γ,W,hγ,hW,hf,hz⟩ := hB
  letI := hD
  letI := dD
  letI := hE
  letI := dE
  refine ⟨D × E, inferInstance, inferInstance, (fun d => β d.1 * γ d.2),
    (fun d => V d.1 * W d.2), ?_, ?_, ?_, ?_⟩
  · intro d; exact mul_nonneg (hβ _) (hγ _)
  · intro d; exact (Matrix.unitaryGroup I ℂ).mul_mem (hV _) (hW _)
  · rw [he,hf,Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.ofReal_mul]
  · rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hw, hz]

/-- If every matrix in a list has a positive unitary representation of weight at most a
nonnegative `q`, the list product has such a representation of weight at most `q ^
l.length`. -/
private theorem unitarySum_list_prod {I : Type} [Fintype I] [DecidableEq I]
    (q : ℝ) (hq : 0 ≤ q) (l : List (Matrix I I ℂ)) :
    (∀ A ∈ l, ∃ w, 0 ≤ w ∧ w ≤ q ∧ HasUnitarySum A w) →
      ∃ w, 0 ≤ w ∧ w ≤ q^l.length ∧ HasUnitarySum l.prod w := by
  induction l with
  | nil => intro _; exact ⟨1, by norm_num, by simp, unitarySum_one⟩
  | cons A l ih =>
    intro h
    obtain ⟨a,ha,haq,hA⟩ := h A (by simp)
    obtain ⟨b,hb,hbq,hB⟩ := ih (fun B hB => h B (by simp [hB]))
    refine ⟨a*b, mul_nonneg ha hb, ?_, unitarySum_mul hA hB⟩
    simpa [pow_succ, mul_comm] using! mul_le_mul haq hbq hb hq

/-- If every matrix in a list has a positive unitary representation of weight at most `C`, their
sum has such a representation of nonnegative weight at most `l.length * C`. -/
private theorem unitarySum_list_sum {I : Type} [Fintype I] [DecidableEq I]
    (C : ℝ) (l : List (Matrix I I ℂ)) :
    (∀ A ∈ l, ∃ w, 0 ≤ w ∧ w ≤ C ∧ HasUnitarySum A w) →
      ∃ w, 0 ≤ w ∧ w ≤ (l.length : ℝ)*C ∧ HasUnitarySum l.sum w := by
  induction l with
  | nil => intro _; exact ⟨0, le_rfl, by simp, unitarySum_zero⟩
  | cons A l ih =>
    intro h
    obtain ⟨a,ha,haC,hA⟩ := h A (by simp)
    obtain ⟨b,hb,hbC,hB⟩ := ih (fun B hB => h B (by simp [hB]))
    refine ⟨a+b, add_nonneg ha hb, ?_, unitarySum_add hA hB⟩
    simpa [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, add_comm] using!
        add_le_add haC hbC

/-- A finite sum of matrices with positive unitary representations has a representation whose
nonnegative total weight is bounded by the sum of the individual weight bounds. -/
private theorem unitarySum_finset_sum {I : Type} [Fintype I] [DecidableEq I]
    {D : Type*} [DecidableEq D] (A : D → Matrix I I ℂ) (C : D → ℝ) (s : Finset D) :
    (∀ d ∈ s, ∃ w, 0 ≤ w ∧ w ≤ C d ∧ HasUnitarySum (A d) w) →
      ∃ w, 0 ≤ w ∧ w ≤ ∑ d ∈ s, C d ∧ HasUnitarySum (∑ d ∈ s, A d) w := by
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨0, le_rfl, by simp, by simpa using! (unitarySum_zero (I := I))⟩
  | @insert d s hd ih =>
    intro h
    obtain ⟨a,ha,haC,hA⟩ := h d (by simp)
    obtain ⟨b,hb,hbC,hB⟩ := ih (fun e he => h e (by simp [he]))
    refine ⟨a+b, add_nonneg ha hb, ?_, ?_⟩
    · simpa [Finset.sum_insert hd] using! add_le_add haC hbC
    · simpa [Finset.sum_insert hd] using! unitarySum_add hA hB

/-- Multiplication by the scalar −i preserves membership in the matrix unitary group. -/
private theorem negativeI_unitary {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (-Complex.I) • U ∈ Matrix.unitaryGroup I ℂ := by
  have hu := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, hu, smul_smul]
  simp

/-- For nonnegative `h` and coefficients `α`, the increment −ih times their unitary sum has a
positive unitary representation of weight `h * ∑ ℓ, α ℓ`. -/
private theorem increment_unitarySum {I : Type} [Fintype I] [DecidableEq I]
    (L : ℕ) (α : Fin L → ℝ) (V : Fin L → Matrix I I ℂ) (h : ℝ)
    (hV : ∀ ℓ, V ℓ ∈ Matrix.unitaryGroup I ℂ) (hα : ∀ ℓ, 0 ≤ α ℓ) (hh : 0 ≤ h) :
    HasUnitarySum (-((h : ℂ)) • (Complex.I • (∑ ℓ, (α ℓ : ℂ) • V ℓ))) (h*∑ ℓ, α ℓ) := by
  refine ⟨Fin L, inferInstance, inferInstance, (fun ℓ => h*α ℓ),
    (fun ℓ => (-Complex.I) • V ℓ), ?_, ?_, ?_, ?_⟩
  · intro ℓ; exact mul_nonneg hh (hα _)
  · intro ℓ; exact negativeI_unitary (hV _)
  · rw [Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    simp only [Complex.ofReal_mul, smul_smul]
    congr 1
    ring
  · rw [← Finset.mul_sum]

/-- The grid segment has a positive unitary representation with total weight between one and the
order-`K` exponential sum in `Λ * τ`, when the Hamiltonian has the stated positive unitary
decomposition [BerryEtAl2015Taylor]. -/
theorem equation28UnitarySum : Equation28UnitarySum := by
  intro I _ _ L α Hl H τ Λ M K hU hα hH hΛ hM ht
  let l := gridIncrements H τ M
  let q := Λ*τ/M
  have hΛ0 : 0 ≤ Λ := (Finset.sum_nonneg (fun ℓ _ => hα ℓ 0)).trans (hΛ 0 ⟨le_rfl,ht⟩)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hlen : l.length = M := by simp [l,gridIncrements]
  have hinc : ∀ A ∈ l, ∃ w, 0 ≤ w ∧ w ≤ q ∧ HasUnitarySum A w := by
    intro A hA
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hA)
    have hj : (j.val : ℝ) ≤ M := by exact_mod_cast j.isLt.le
    have hu : τ*(j.val : ℝ)/M ∈ Set.Icc 0 τ := by
      refine ⟨by positivity, ?_⟩
      calc
        _ ≤ τ*(M : ℝ)/M := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj ht)
          (Nat.cast_nonneg _)
        _ = τ := by field_simp
    refine ⟨(τ/M)*∑ ℓ, α ℓ (τ*(j.val : ℝ)/M),
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun ℓ _ => hα ℓ _)), ?_, ?_⟩
    · calc
        _ ≤ (τ/M)*Λ := mul_le_mul_of_nonneg_left (hΛ _ hu) (by positivity)
        _ = q := by dsimp [q]; ring
    · rw [hH _ hu]
      exact increment_unitarySum L _ Hl (τ/M) hU (fun ℓ => hα ℓ _) (by positivity)
  have hlayer (k : ℕ) : ∃ w, 0 ≤ w ∧
      w ≤ (Λ*τ)^k/(k.factorial : ℝ) ∧
      HasUnitarySum (((l.sublistsLen k).map List.prod).sum) w := by
    obtain ⟨w,hw,hb,hrep⟩ := unitarySum_list_sum (q^k) ((l.sublistsLen k).map List.prod) (by
      intro A hA
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hA
      obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hu
      simpa [hlen] using! unitarySum_list_prod q hq u (fun B hB => hinc B (hsub.subset hB)))
    refine ⟨w,hw,hb.trans ?_,hrep⟩
    simpa [List.length_map, List.length_sublistsLen,hlen,q] using!
      equation28_choose_weight_bound M k (Λ*τ) hM (by positivity)
  obtain ⟨w,hw,hb,hrep⟩ := unitarySum_finset_sum
    (fun k => ((l.sublistsLen (k+1)).map List.prod).sum)
    (fun k => (Λ*τ)^(k+1)/((k+1).factorial : ℝ)) (Finset.range K) (fun k _ => hlayer (k+1))
  have hp : equation28Segment H τ M K =
      1 + ∑ k ∈ Finset.range K, ((l.sublistsLen (k+1)).map List.prod).sum := by
    rw [equation28Segment, Finset.sum_range_succ']
    simp [l,add_comm]
  have hr : HasUnitarySum (equation28Segment H τ M K) (1+w) := by
    rw [hp]
    exact unitarySum_add unitarySum_one hrep
  obtain ⟨D,hD,dD,β,V,hβ,hV,he,hweight⟩ := hr
  letI := hD
  letI := dD
  refine ⟨D,hD,dD,β,V,hβ,hV,he,?_,?_⟩
  · rw [hweight]; linarith
  · rw [hweight, Finset.sum_range_succ']
    simpa [add_comm] using! add_le_add_left hb 1

end Qatlib.Concepts.CoherentSim.TimeDependent
