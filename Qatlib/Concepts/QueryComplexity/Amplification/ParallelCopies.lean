/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.PiTensorState
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Circuits on individual tensor factors

This module defines `FactorGate`, `FactorCircuit`, and `SeqCopiesCircuit` for executing circuits
on selected tensor factors. It proves unitarity and exact gate and query counts; for circuits
with zero queries, execution acts independently on the designated factors, supplying the
repeated circuit construction used for amplification in [BennettEtAl1997].

## Main statements

* `applyGate_factorGate_piTensorState`: a factor gate updates one state factor.
* `gateCount_seqCopiesCircuit`: sequential copies multiply the gate count by the copy count.
* `run_seqCopiesCircuit_piTensorState`: circuits with zero queries execute independently on all
  factors.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.QueryComplexity.Amplification

open Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

section Factor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix acting as `U` on tensor factor `j` and as the identity on all other factors. -/
noncomputable def FactorGate (j : ι) (U : Matrix I I ℂ) : Matrix (ι → I) (ι → I) ℂ :=
  Matrix.of fun f g => if (∀ l, l ≠ j → f l = g l) then U (f j) (g j) else 0

/-- Lift every gate of a circuit to factor `j` while retaining each query step. -/
noncomputable def FactorCircuit (j : ι) : Circuit I → Circuit (ι → I)
  | [] => []
  | Step.gate U :: C => Step.gate (FactorGate j U) :: FactorCircuit j C
  | Step.query :: C => Step.query :: FactorCircuit j C

/-- Lifting an empty circuit to one tensor factor gives the empty circuit. -/
@[simp] theorem factorCircuit_nil (j : ι) : FactorCircuit j ([] : Circuit I) = [] := rfl

/-- Lifting a leading gate uses `FactorGate` on that gate and lifts the remaining circuit. -/
@[simp] theorem factorCircuit_gate (j : ι) (U : Matrix I I ℂ) (C : Circuit I) :
    FactorCircuit j (Step.gate U :: C) =
      Step.gate (FactorGate j U) :: FactorCircuit j C := rfl

/-- Lifting a leading query retains the query and lifts the remaining circuit. -/
@[simp] theorem factorCircuit_query (j : ι) (C : Circuit I) :
    FactorCircuit j (Step.query :: C) = Step.query :: FactorCircuit j C := rfl

/-- A factor gate has entry `U (f j) (g j)` when the two indices agree away from `j`, and zero
otherwise. -/
private theorem factorGate_apply (j : ι) (U : Matrix I I ℂ) (f g : ι → I) :
    FactorGate j U f g = if (∀ l, l ≠ j → f l = g l) then U (f j) (g j) else 0 := rfl

/-- Lifting the identity matrix to a tensor factor gives the identity matrix. -/
private theorem factorGate_one (j : ι) : FactorGate j (1 : Matrix I I ℂ) = 1 := by
  ext f g
  simp only [factorGate_apply, Matrix.one_apply]
  by_cases hfg : f = g
  · subst hfg
    simp
  · rw [if_neg hfg]
    by_cases hfj : f j = g j
    · refine if_neg ?_
      intro hcond
      apply hfg
      funext l
      by_cases hl : l = j
      · subst hl
        exact hfj
      · exact hcond l hl
    · rw [if_neg hfj, ite_self]

/-- Lifting a matrix to a tensor factor commutes with conjugate transposition. -/
private theorem factorGate_conjTranspose (j : ι) (U : Matrix I I ℂ) :
    (FactorGate j U)ᴴ = FactorGate j Uᴴ := by
  ext f g
  by_cases h : ∀ l, l ≠ j → g l = f l
  · simp only [factorGate_apply, Matrix.conjTranspose_apply, if_pos h]
    rw [if_pos fun l hl => (h l hl).symm]
  · simp only [factorGate_apply, Matrix.conjTranspose_apply, if_neg h, star_zero]
    rw [if_neg fun hc => h fun l hl => (hc l hl).symm]

/-- Summing over functions agreeing with `f` away from `j` reduces to summing over updates of
`f` at `j`. -/
private theorem sum_factor (j : ι) (f : ι → I) (F : (ι → I) → ℂ) :
    ∑ g : ι → I, (if (∀ l, l ≠ j → f l = g l) then F g else 0)
      = ∑ a : I, F (Function.update f j a) := by
  have hinj : ∀ a b : I, Function.update f j a = Function.update f j b → a = b := by
    intro a b hab
    have h := congrFun hab j
    rwa [Function.update_self, Function.update_self] at h
  have hzero : ∀ g ∈ (Finset.univ : Finset (ι → I)),
      g ∉ Finset.univ.image (fun a => Function.update f j a) →
      (if (∀ l, l ≠ j → f l = g l) then F g else 0) = 0 := by
    intro g _ hg
    refine if_neg (fun hcond => hg ?_)
    have hupd : Function.update f j (g j) = g := by
      funext l
      by_cases hl : l = j
      · subst hl
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hl (g j) f]
        exact hcond l hl
    rw [← hupd]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (g j))
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
    Finset.sum_image (fun a _ b _ hab => hinj a b hab)]
  exact Finset.sum_congr rfl fun a _ =>
    if_pos fun l hl => (Function.update_of_ne hl a f).symm

/-- Lifting matrices to a tensor factor preserves multiplication. -/
private theorem factorGate_mul (j : ι) (U V : Matrix I I ℂ) :
    FactorGate j U * FactorGate j V = FactorGate j (U * V) := by
  ext f g
  simp only [factorGate_apply, Matrix.mul_apply]
  by_cases h : ∀ l, l ≠ j → f l = g l
  · rw [if_pos h]
    have hterm : ∀ g' : ι → I,
        (if (∀ l, l ≠ j → f l = g' l) then U (f j) (g' j) else 0)
            * (if (∀ l, l ≠ j → g' l = g l) then V (g' j) (g j) else 0)
        = if (∀ l, l ≠ j → f l = g' l) then U (f j) (g' j) * V (g' j) (g j) else 0 := by
      intro g'
      by_cases h₁ : ∀ l, l ≠ j → f l = g' l
      · simp only [if_pos h₁, if_pos fun l hl => (h₁ l hl).symm.trans (h l hl)]
      · simp only [if_neg h₁, zero_mul]
    rw [Finset.sum_congr rfl fun g' _ => hterm g',
      sum_factor j f fun g' => U (f j) (g' j) * V (g' j) (g j)]
    exact Finset.sum_congr rfl fun a _ => by rw [Function.update_self]
  · rw [if_neg h]
    have hterm : ∀ g' : ι → I,
        (if (∀ l, l ≠ j → f l = g' l) then U (f j) (g' j) else 0)
            * (if (∀ l, l ≠ j → g' l = g l) then V (g' j) (g j) else 0) = 0 := by
      intro g'
      by_cases h₁ : ∀ l, l ≠ j → f l = g' l
      · rw [if_pos h₁, if_neg ?_, mul_zero]
        intro hc
        exact h fun l hl => (h₁ l hl).trans (hc l hl)
      · rw [if_neg h₁, zero_mul]
    simp [hterm]

/-- Lifting a unitary matrix to one tensor factor gives a unitary matrix. -/
theorem factorGate_unitary (j : ι) {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    FactorGate j U ∈ Matrix.unitaryGroup (ι → I) ℂ := by
  have hU' : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, factorGate_conjTranspose,
    factorGate_mul, hU', factorGate_one]

/-- A product evaluated after updating coordinate `j` splits into the updated factor and the
product over all remaining coordinates. -/
private theorem prod_update_split_left (j : ι) (ψ : ι → QState I) (ω : ι → I) (a : I) :
    ∏ k, ψ k (Function.update ω j a k) = ψ j a * ∏ k ∈ Finset.univ.erase j, ψ k (ω k) := by
  have h := Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun k => ψ k (Function.update ω j a k)) (Finset.mem_univ j)
  rw [← h]
  try simp only []
  rw [Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun k hk => ?_)
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1 a ω]

/-- Updating state factor `j` splits its tensor amplitude into the new factor amplitude and the
product over the other factors. -/
private theorem prod_update_split_right (j : ι) (ψ : ι → QState I) (χ : QState I) (ω : ι → I) :
    ∏ k, Function.update ψ j χ k (ω k) = χ (ω j) * ∏ k ∈ Finset.univ.erase j, ψ k (ω k) := by
  have h := Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun k => Function.update ψ j χ k (ω k)) (Finset.mem_univ j)
  rw [← h]
  try simp only []
  rw [Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun k hk => ?_)
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1 χ ψ]

/-- Applying a factor gate to a tensor state replaces exactly the selected state factor by its
image under the original gate. -/
theorem applyGate_factorGate_piTensorState (j : ι) (U : Matrix I I ℂ) (ψ : ι → QState I) :
    ApplyGate (FactorGate j U) (PiTensorState ψ)
      = PiTensorState (Function.update ψ j (ApplyGate U (ψ j))) := by
  funext ω
  have key := sum_factor j ω fun g => U (ω j) (g j) * ∏ k, ψ k (g k)
  simp only [ApplyGate, Matrix.mulVec, dotProduct, factorGate_apply, ite_mul, zero_mul,
    piTensorState_apply] at key ⊢
  rw [key]
  simp only [Function.update_self]
  have hsplit : ∑ a : I, U (ω j) a * ∏ k, ψ k (Function.update ω j a k)
      = (∑ a : I, U (ω j) a * ψ j a) * ∏ k ∈ Finset.univ.erase j, ψ k (ω k) := by
    rw [Finset.sum_congr rfl fun a _ => by rw [prod_update_split_left j ψ ω a]]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
  rw [hsplit, prod_update_split_right j ψ (U *ᵥ ψ j) ω]
  rfl

/-- Lifting a unitary circuit to one tensor factor gives a unitary circuit. -/
theorem isUnitaryCircuit_factorCircuit (j : ι) {C : Circuit I} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (FactorCircuit j C) := by
  revert hC
  induction C with
  | nil => intro hC; exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      intro hC
      rw [factorCircuit_gate, isUnitaryCircuit_gate]
      exact ⟨factorGate_unitary j ((isUnitaryCircuit_gate U C).mp hC).1,
        ih ((isUnitaryCircuit_gate U C).mp hC).2⟩
    | query =>
      intro hC
      rw [factorCircuit_query, isUnitaryCircuit_query]
      exact ih ((isUnitaryCircuit_query C).mp hC)

/-- Lifting a circuit to a tensor factor preserves its gate count. -/
theorem gateCount_factorCircuit (j : ι) (C : Circuit I) :
    GateCount (FactorCircuit j C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

/-- Lifting a circuit to a tensor factor preserves its query count. -/
theorem queryCount_factorCircuit (j : ι) (C : Circuit I) :
    QueryCount (FactorCircuit j C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

/-- For a circuit with zero queries, running its factor lift with the identity oracle applies
the original circuit only to the selected tensor factor. -/
private theorem run_factorCircuit_one (j : ι) (C : Circuit I) (hC0 : QueryCount C = 0) :
    ∀ ψ : ι → QState I, Run (1 : Matrix (ι → I) (ι → I) ℂ) (FactorCircuit j C) (PiTensorState ψ)
      = PiTensorState (Function.update ψ j (Run 1 C (ψ j))) := by
  revert hC0
  induction C with
  | nil =>
    intro hC0 ψ
    have hupd : Function.update ψ j (Run 1 ([] : Circuit I) (ψ j)) = ψ := by
      funext l
      simp only [run_nil, Function.update_apply]
      by_cases hl : l = j <;> simp [hl]
    rw [hupd]
    rfl
  | cons s C ih =>
    intro hC0 ψ
    cases s with
    | gate U =>
      rw [factorCircuit_gate, run_gate, run_gate, applyGate_factorGate_piTensorState,
        ih (by simpa only [queryCount_gate] using hC0), Function.update_self,
        Function.update_idem]
    | query => simp at hC0

/-- For a circuit with zero queries, running its factor lift with any oracle applies the
original identity oracle execution only to the selected tensor factor. -/
theorem run_factorCircuit_piTensorState (j : ι) (C : Circuit I) (hC0 : QueryCount C = 0)
    (O : Matrix (ι → I) (ι → I) ℂ) (ψ : ι → QState I) :
    Run O (FactorCircuit j C) (PiTensorState ψ)
      = PiTensorState (Function.update ψ j (Run 1 C (ψ j))) := by
  rw [run_eq_of_queryCount_eq_zero O 1 (FactorCircuit j C)
    (by rw [queryCount_factorCircuit]; exact hC0) (PiTensorState ψ)]
  exact run_factorCircuit_one j C hC0 ψ

/-- Concatenating the factor lifts of a unitary circuit over any list of factors gives a unitary
circuit. -/
private theorem isUnitaryCircuit_flatMap_factorCircuit {C : Circuit I}
    (hC : IsUnitaryCircuit C) :
    ∀ L : List ι, IsUnitaryCircuit (L.flatMap fun j => FactorCircuit j C) := by
  intro L
  induction L with
  | nil => exact isUnitaryCircuit_nil
  | cons j₀ L ih =>
    simp only [List.flatMap_cons]
    rw [isUnitaryCircuit_append]
    exact ⟨isUnitaryCircuit_factorCircuit j₀ hC, ih⟩

/-- The gate count of the concatenated factor lifts equals the list length times the original
gate count. -/
private theorem gateCount_flatMap_factorCircuit (C : Circuit I) :
    ∀ L : List ι, GateCount (L.flatMap fun j => FactorCircuit j C) = L.length * GateCount C := by
  intro L
  induction L with
  | nil => simp
  | cons j₀ L ih =>
    simp only [List.flatMap_cons, gateCount_append, ih, gateCount_factorCircuit,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- The query count of the concatenated factor lifts equals the list length times the original
query count. -/
private theorem queryCount_flatMap_factorCircuit (C : Circuit I) :
    ∀ L : List ι, QueryCount (L.flatMap fun j => FactorCircuit j C) = L.length * QueryCount C := by
  intro L
  induction L with
  | nil => simp
  | cons j₀ L ih =>
    simp only [List.flatMap_cons, queryCount_append, ih, queryCount_factorCircuit,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- For a circuit with zero queries and a list without duplicates, the concatenated factor lifts
apply the original circuit exactly to the listed tensor factors. -/
private theorem run_flatMap_factorCircuit (C : Circuit I) (hC0 : QueryCount C = 0) :
    ∀ (L : List ι), L.Nodup → ∀ (ψ : ι → QState I),
      Run (1 : Matrix (ι → I) (ι → I) ℂ) (L.flatMap fun j => FactorCircuit j C)
          (PiTensorState ψ)
        = PiTensorState (fun j => if j ∈ L then Run 1 C (ψ j) else ψ j) := by
  intro L
  induction L with
  | nil => intro _ ψ; simp
  | cons j₀ L ih =>
    intro hnd ψ
    obtain ⟨hj₀, hL⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons]
    rw [run_append, run_factorCircuit_piTensorState j₀ C hC0 1 ψ, ih hL]
    refine congrArg PiTensorState ?_
    funext j
    by_cases hj : j = j₀
    · subst hj
      rw [Function.update_self]
      simp [hj₀]
    · rw [Function.update_of_ne hj (Run 1 C (ψ j₀)) ψ]
      by_cases hjL : j ∈ L
      · rw [if_pos hjL, if_pos (List.mem_cons_of_mem _ hjL)]
      · rw [if_neg hjL, if_neg ?_]
        intro hc
        rcases List.mem_cons.mp hc with h | h
        · exact hj h
        · exact hjL h

end Factor

/-- The circuit obtained by executing one factor lift of `C` for each of `k` tensor factors in
order. -/
noncomputable def SeqCopiesCircuit (k : ℕ) (C : Circuit I) : Circuit (Fin k → I) :=
  (List.finRange k).flatMap fun j => FactorCircuit j C

/-- Sequential copies of a unitary circuit form a unitary circuit. -/
theorem isUnitaryCircuit_seqCopiesCircuit (k : ℕ) {C : Circuit I} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (SeqCopiesCircuit k C) := by
  simp only [SeqCopiesCircuit]
  exact isUnitaryCircuit_flatMap_factorCircuit hC (List.finRange k)

/-- The gate count of `k` sequential copies is `k` times the original gate count. -/
theorem gateCount_seqCopiesCircuit (k : ℕ) (C : Circuit I) :
    GateCount (SeqCopiesCircuit k C) = k * GateCount C := by
  simp only [SeqCopiesCircuit, gateCount_flatMap_factorCircuit, List.length_finRange]

/-- The query count of `k` sequential copies is `k` times the original query count. -/
theorem queryCount_seqCopiesCircuit (k : ℕ) (C : Circuit I) :
    QueryCount (SeqCopiesCircuit k C) = k * QueryCount C := by
  simp only [SeqCopiesCircuit, queryCount_flatMap_factorCircuit, List.length_finRange]

/-- For a circuit with zero queries, executing `k` sequential copies with any oracle applies the
original identity oracle execution to every tensor factor. -/
theorem run_seqCopiesCircuit_piTensorState (k : ℕ) (C : Circuit I) (hC0 : QueryCount C = 0)
    (O : Matrix (Fin k → I) (Fin k → I) ℂ) (ψ : Fin k → QState I) :
    Run O (SeqCopiesCircuit k C) (PiTensorState ψ) = PiTensorState (fun j => Run 1 C (ψ j)) := by
  rw [run_eq_of_queryCount_eq_zero O 1 (SeqCopiesCircuit k C)
    (by rw [queryCount_seqCopiesCircuit, hC0, mul_zero]) (PiTensorState ψ)]
  simp only [SeqCopiesCircuit]
  rw [run_flatMap_factorCircuit C hC0 (List.finRange k) (List.nodup_finRange k) ψ]
  refine congrArg PiTensorState ?_
  funext j
  simp [List.mem_finRange]

end Qatlib.Concepts.QueryComplexity.Amplification
