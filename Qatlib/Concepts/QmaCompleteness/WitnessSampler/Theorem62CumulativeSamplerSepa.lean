/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Theorem62CumulativeSamplerStat
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Lemma61HybridSamplerCoreSepa

/-!
# Cumulative witness-sampler bound

This module proves `theorem6_2CumulativeSampler` from the hybrid query-mass bound. It controls
transition mass into fresh elements of `S`, iterates this estimate over sampling histories, and
averages over the family of witness states.

The proof also verifies that `hardcodeS` removes all first-oracle queries while preserving the
second-oracle query count. Its query-analysis ingredients use the hybrid method of
[BennettEtAl1997].

## Main statements

* `theorem6_2CumulativeSampler`: cumulative success is at least `1 / (2 ^ q : ℝ) * (1 / (36 * (t
  : ℝ) ^ 2)) ^ v`, together with the hardcoded query-count identities.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

set_option autoImplicit false

open Matrix

section G4

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The measurement mass `MeasureProb φ A` of any finite event `A` is nonnegative for every
vector `φ`. -/
private theorem measureProb_nonneg {I : Type} [Fintype I] (φ : QState I) (A : Finset I) :
    (0 : ℝ) ≤ MeasureProb φ A :=
  Finset.sum_nonneg fun i _ => sq_nonneg (‖φ i‖)

/-- For finite events `A ⊆ B`, the measurement masses satisfy `MeasureProb φ A ≤ MeasureProb φ
B` for every vector `φ`. -/
private theorem measureProb_mono {I : Type} [Fintype I] (φ : QState I)
    (A B : Finset I) (hAB : A ⊆ B) : MeasureProb φ A ≤ MeasureProb φ B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB
    (fun i _ _ => sq_nonneg (‖φ i‖))

/-- The sum of a pointwise nonnegative real function `f` over any list `L` is nonnegative. -/
private theorem list_map_sum_nonneg' {α : Type} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (L : List α) : (0 : ℝ) ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; linarith [hf a, ih]

omit [DecidableEq W] in

/-- The controlled fiber measurement mass `controlFiberMass n S Δ W φ` is nonnegative for every
vector `φ`. -/
private theorem controlFiberMass_nonneg' (S Δ : Reg n → Bool)
    (φ : QState (ForrSpace n W)) : (0 : ℝ) ≤ controlFiberMass n S Δ W φ :=
  measureProb_nonneg φ _

/-- Summing the list sum of `f φ x` over `x` in a finite set `T` equals the list sum over `φ` of
the finite sums over `T`. -/
private theorem sum_swap {I : Type} (L : List I) (f : I → Reg n → ℝ) (T : Finset (Reg n)) :
    (∑ x ∈ T, (L.map (fun φ => f φ x)).sum) = (L.map (fun φ => ∑ x ∈ T, f φ x)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, Finset.sum_add_distrib]

/-- If every element of `hist` satisfies `S`, then every string selected by its membership
predicate `regOfList n hist` also satisfies `S`. -/
private theorem regOfList_subset (hist : List (Reg n)) (S : Reg n → Bool)
    (hsub : ∀ x ∈ hist, S x) : ∀ x, regOfList n hist x → S x := by
  intro x hx
  by_cases hxh : x ∈ hist
  · exact hsub x hxh
  · exact absurd (of_decide_eq_true hx) hxh

omit [DecidableEq W] in

/-- The sum of `sQueryBornMass n W φ x` over addresses `x` in `T` equals the measurement mass of
all basis states whose first oracle address lies in `T`. -/
private theorem sum_sQueryBornMass (φ : QState (ForrSpace n W)) (T : Finset (Reg n)) :
    (∑ x ∈ T, sQueryBornMass n W φ x)
      = MeasureProb φ (Finset.univ.filter fun p : ForrSpace n W => p.1.1 ∈ T) := by
  classical
  unfold sQueryBornMass MeasureProb
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq]

/-- The transition mass `directTransitionMass n W S U C ψ hist x` is nonnegative for every
circuit, vector, history, and address. -/
private theorem directTransitionMass_nonneg (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) (hist : List (Reg n))
    (x : Reg n) : (0 : ℝ) ≤ directTransitionMass n W S U C ψ hist x := by
  unfold directTransitionMass
  refine mul_nonneg (one_div_nonneg.mpr (by positivity)) ?_
  exact list_map_sum_nonneg' _ (fun φ => measureProb_nonneg φ _) _

/-- The recursive success mass `cumDirectSuccess n W S U C ψ v hist` is nonnegative for every
number of remaining samples `v` and history `hist`. -/
private theorem cumDirectSuccess_nonneg (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) :
    ∀ (v : ℕ) (hist : List (Reg n)), (0 : ℝ) ≤ cumDirectSuccess n W S U C ψ v hist := by
  intro v
  induction v with
  | zero => intro hist; exact zero_le_one
  | succ v ih =>
    intro hist
    refine Finset.sum_nonneg fun x _ => ?_
    refine mul_nonneg ?_ (ih _)
    by_cases hx : S x ∧ x ∉ hist
    · rw [ite_eq_left hx]
      exact directTransitionMass_nonneg S U C ψ hist x
    · simp [hx]

/-- If `TOQueryCountS C ≤ t` and the summed controlled fiber mass along the history oracle
execution divided by `t` is at least `1 / (36 * t ^ 2)`, then the total
`directTransitionMass` of unseen addresses satisfying `S` is at least the same bound. -/
private theorem transition_sum_ge (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) (hist : List (Reg n))
    (t : ℕ) (hcount : TOQueryCountS C ≤ t)
    (hbound : (1 / (t : ℝ)) *
        ((sQueryStates (forrPhaseOracleS n (regOfList n hist) W)
          (forrPhaseOracleU n U W) C ψ).map
          (controlFiberMass n S (regOfList n hist) W)).sum ≥
        1 / (36 * (t : ℝ) ^ 2)) :
    (∑ x : Reg n,
        (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0))
      ≥ 1 / (36 * (t : ℝ) ^ 2) := by
  classical
  set c := 1 / (36 * (t : ℝ) ^ 2) with hcdef
  set T : Finset (Reg n) := Finset.univ.filter fun x => S x ∧ x ∉ hist with hT
  set traj := sQueryStates (forrPhaseOracleS n (regOfList n hist) W)
    (forrPhaseOracleU n U W) C ψ with htraj

  have hfilter : (∑ x : Reg n,
      (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0))
      = ∑ x ∈ T, directTransitionMass n W S U C ψ hist x := by
    rw [Finset.sum_filter]
  rw [hfilter]

  have hswap : (∑ x ∈ T, directTransitionMass n W S U C ψ hist x)
      = (1 / (TOQueryCountS C : ℝ)) *
        (traj.map (fun φ => ∑ x ∈ T, sQueryBornMass n W φ x)).sum := by
    unfold directTransitionMass
    rw [← Finset.mul_sum, ← sum_swap]
  rw [hswap]

  have hterm : ∀ φ : QState (ForrSpace n W),
      (∑ x ∈ T, sQueryBornMass n W φ x)
        ≥ controlFiberMass n S (regOfList n hist) W φ := by
    intro φ
    rw [sum_sQueryBornMass]
    refine measureProb_mono φ _ _ ?_
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ p, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ p.1.1, hp.2.2.1,
      fun hmem => hp.2.2.2 (decide_eq_true hmem)⟩

  have hmasst : (t : ℝ) * c
      ≤ (traj.map (controlFiberMass n S (regOfList n hist) W)).sum := by
    rcases Nat.eq_zero_or_pos t with ht0 | htp
    · rw [ht0]
      have hnn : (0 : ℝ) ≤ (traj.map (controlFiberMass n S (regOfList n hist) W)).sum :=
        list_map_sum_nonneg' _ (fun φ => controlFiberMass_nonneg' S _ φ) _
      simpa using hnn
    · have htp' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htp
      have heq : (1 / (t : ℝ)) *
          ((traj.map (controlFiberMass n S (regOfList n hist) W)).sum)
          = ((traj.map (controlFiberMass n S (regOfList n hist) W)).sum) / (t : ℝ) := by
        rw [one_div, inv_mul_eq_div]
      have htden : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htp
      rw [heq, ge_iff_le, le_div_iff₀ htden] at hbound
      linarith

  have hgen : ∀ (L : List (QState (ForrSpace n W))) (f g : QState (ForrSpace n W) → ℝ),
      (∀ φ, g φ ≤ f φ) → (L.map g).sum ≤ (L.map f).sum := by
    intro L f g hfg
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons]; linarith [hfg a, ih]
  have hmono : ((traj.map (controlFiberMass n S (regOfList n hist) W)).sum)
      ≤ (traj.map (fun φ => ∑ x ∈ T, sQueryBornMass n W φ x)).sum :=
    hgen _ _ _ hterm
  rcases Nat.eq_zero_or_pos (TOQueryCountS C) with hk0 | hkp
  · have hlen : traj.length = 0 := by
      have h := sQueryStates_length (forrPhaseOracleS n (regOfList n hist) W)
        (forrPhaseOracleU n U W) C ψ
      simpa [hk0] using h
    have hempty : traj = [] := List.length_eq_zero_iff.mp hlen
    rw [hempty] at hbound ⊢
    simp only [List.map_nil, List.sum_nil, mul_zero] at hbound ⊢
    rcases Nat.eq_zero_or_pos t with ht0 | htp
    · have hc0 : c = 0 := by rw [hcdef, ht0]; norm_num
      rw [hc0]
    · have hposc : (0 : ℝ) < c := by rw [hcdef]; positivity
      exact absurd hbound (by nlinarith)
  · have hkp' : (0 : ℝ) < (TOQueryCountS C : ℝ) := by exact_mod_cast hkp
    have htk : (TOQueryCountS C : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcount
    have hbig : (traj.map (fun φ => ∑ x ∈ T, sQueryBornMass n W φ x)).sum
        ≥ (t : ℝ) * c := hmasst.trans hmono
    have h1 : (1 / (TOQueryCountS C : ℝ)) *
        (traj.map (fun φ => ∑ x ∈ T, sQueryBornMass n W φ x)).sum
        ≥ (1 / (TOQueryCountS C : ℝ)) * ((t : ℝ) * c) :=
      mul_le_mul_of_nonneg_left hbig (by positivity)
    have h2 : (1 / (TOQueryCountS C : ℝ)) * ((t : ℝ) * c) ≥ c := by
      have h3 : (1 / (TOQueryCountS C : ℝ)) * (TOQueryCountS C : ℝ) = 1 := by
        field_simp
      have hcnn : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
      have htk' : (1 / (TOQueryCountS C : ℝ)) * ((TOQueryCountS C : ℝ) * c)
          ≤ (1 / (TOQueryCountS C : ℝ)) * ((t : ℝ) * c) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [htk, hcnn]
      have h4 : (1 / (TOQueryCountS C : ℝ)) * ((TOQueryCountS C : ℝ) * c) = c := by
        rw [← mul_assoc, h3, one_mul]
      exact h4.symm.trans_le htk'
    exact h2.trans h1

/-- If `TOQueryCountS C ≤ t` and every distinct history in `S` of length at most `v` has summed
controlled fiber mass divided by `t` at least `1 / (36 * t ^ 2)`, then `cumDirectSuccess`
for `v'` further samples is at least `(1 / (36 * t ^ 2)) ^ v'` whenever the distinct
starting history lies in `S` and its length plus `v'` is at most `v`. -/
private theorem cumDirectSuccess_ge (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (t v : ℕ) (hcount : TOQueryCountS C ≤ t)
    (hper : ∀ hist : List (Reg n), hist.Nodup → (∀ x ∈ hist, S x) → hist.length ≤ v →
      (1 / (t : ℝ)) *
          ((sQueryStates (forrPhaseOracleS n (regOfList n hist) W)
            (forrPhaseOracleU n U W) C ψ).map
            (controlFiberMass n S (regOfList n hist) W)).sum ≥
          1 / (36 * (t : ℝ) ^ 2)) :
    ∀ (v' : ℕ) (hist : List (Reg n)), hist.Nodup → (∀ x ∈ hist, S x) →
      hist.length + v' ≤ v →
      cumDirectSuccess n W S U C ψ v' hist ≥ (1 / (36 * (t : ℝ) ^ 2)) ^ v' := by
  intro v'
  induction v' with
  | zero =>
    intro hist _ _ _
    simp [cumDirectSuccess]
  | succ v' ih =>
    intro hist hnodup hsub hlen
    have hperx : ∀ x : Reg n,
        (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0) *
            cumDirectSuccess n W S U C ψ v' (x :: hist)
          ≥ (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0) *
              (1 / (36 * (t : ℝ) ^ 2)) ^ v' := by
      intro x
      by_cases hx : S x ∧ x ∉ hist
      · have h1 : (0 : ℝ) ≤ directTransitionMass n W S U C ψ hist x :=
          directTransitionMass_nonneg S U C ψ hist x
        rw [ite_eq_left hx]
        refine mul_le_mul_of_nonneg_left ?_ h1
        refine ih (x :: hist) (List.nodup_cons.mpr ⟨hx.2, hnodup⟩) ?_ ?_
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hx.1
          · exact hsub y hy'
        · have hlc : (x :: hist).length = hist.length + 1 := rfl
          omega
      · simp [hx]
    have h1 : (∑ x : Reg n, (if S x ∧ x ∉ hist then
          directTransitionMass n W S U C ψ hist x else 0) *
          (1 / (36 * (t : ℝ) ^ 2)) ^ v')
        ≤ cumDirectSuccess n W S U C ψ (v' + 1) hist :=
      Finset.sum_le_sum fun x _ => hperx x
    have h2 : (1 / (36 * (t : ℝ) ^ 2)) ^ (v' + 1)
        ≤ (∑ x : Reg n, (if S x ∧ x ∉ hist then
          directTransitionMass n W S U C ψ hist x else 0) *
          (1 / (36 * (t : ℝ) ^ 2)) ^ v') := by
      rw [← Finset.sum_mul, pow_succ']
      have hc0 : (0 : ℝ) ≤ 1 / (36 * (t : ℝ) ^ 2) := by positivity
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hc0 v')
      have hlenv : hist.length ≤ v := by omega
      exact transition_sum_ge S U C ψ hist t hcount (hper hist hnodup hsub hlenv)
    exact h2.trans h1

/-- Replacing every first oracle query by the fixed gate `oΔ` using `hardcodeS` leaves zero
first oracle queries. -/
private theorem hardcodeS_countS {I : Type} (oΔ : Matrix I I ℂ) (C : TOCircuit I) :
    TOQueryCountS (hardcodeS oΔ C) = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' => show TOQueryCountS (hardcodeS oΔ C) = 0; exact ih
    | queryS => show TOQueryCountS (hardcodeS oΔ C) = 0; exact ih
    | queryU => show TOQueryCountS (hardcodeS oΔ C) = 0; exact ih

/-- Replacing first oracle queries by fixed gates using `hardcodeS` preserves the number
`TOQueryCountU C` of second oracle queries. -/
private theorem hardcodeS_countU {I : Type} (oΔ : Matrix I I ℂ) (C : TOCircuit I) :
    TOQueryCountU (hardcodeS oΔ C) = TOQueryCountU C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' => show TOQueryCountU (hardcodeS oΔ C) = TOQueryCountU C; exact ih
    | queryS => show TOQueryCountU (hardcodeS oΔ C) = TOQueryCountU C; exact ih
    | queryU =>
      show TOQueryCountU (hardcodeS oΔ C) + 1 = TOQueryCountU C + 1
      rw [ih]

set_option maxHeartbeats 1000000 in

/-- Establishes `Theorem6_2CumulativeSampler`: under its normalization, query bounds, and
acceptance gap hypotheses, cumulative sampling succeeds with mass at least `1 / (2 ^ q) * (1
/ (36 * t ^ 2)) ^ v`, and hardcoding each history oracle removes first oracle queries while
preserving second oracle queries. -/
theorem theorem6_2CumulativeSampler : Theorem6_2CumulativeSampler := by
  intro n q t v W _ _ S U C ψfam E hC hnorm hcountS hcountU hsmall hgood
  obtain ⟨w₀, hw₀⟩ := hgood
  classical
  have hper : ∀ hist : List (Reg n), hist.Nodup → (∀ x ∈ hist, S x) → hist.length ≤ v →
      (1 / (t : ℝ)) *
          ((sQueryStates (forrPhaseOracleS n (regOfList n hist) W)
            (forrPhaseOracleU n U W) C (ψfam w₀)).map
            (controlFiberMass n S (regOfList n hist) W)).sum ≥
          1 / (36 * (t : ℝ) ^ 2) := by
    intro hist hnodup hsub hlen
    exact lemma6_1HybridSamplerCore (n := n) (W := W) (S := S) (Δ := regOfList n hist)
      (U := U) (t := t) (C := C) (ψ := ψfam w₀) (E := E) hC (hnorm w₀)
      (regOfList_subset hist S hsub) hcountS hw₀ (hsmall hist hnodup hsub hlen w₀)
  have htree := cumDirectSuccess_ge S U C (ψfam w₀) t v hcountS hper v []
    List.nodup_nil (by simp) (by simp)
  have hmix : cumulativeSamplerSuccess n q W S U C ψfam v
      ≥ (1 / (Fintype.card (Fin q → Bool) : ℝ))
        * (1 / (36 * (t : ℝ) ^ 2)) ^ v := by
    unfold cumulativeSamplerSuccess
    refine le_trans (mul_le_mul_of_nonneg_left htree (by positivity)) ?_
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun w _ => cumDirectSuccess_nonneg S U C (ψfam w) v [])
        (Finset.mem_univ w₀)) (by positivity)
  have hcard : (Fintype.card (Fin q → Bool) : ℝ) = (2 : ℝ) ^ q := by
    rw [Fintype.card_pi_const, Fintype.card_bool]
    push_cast
    rfl
  refine ⟨?_, fun hist => ⟨hardcodeS_countS _ C, hardcodeS_countU _ C⟩⟩
  rw [hcard] at hmix
  exact hmix

end G4

end Qatlib.Concepts.QmaCompleteness.WitnessSampler
