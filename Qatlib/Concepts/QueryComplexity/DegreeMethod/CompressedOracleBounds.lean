/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.CompressedOracleBoundsDefs

/-!
# Compressed database bounds for bit oracle circuits

This module relates the compressed database execution `databaseXorRun` to ordinary bit oracle
execution averaged over Bernoulli inputs. The connection uses Hadamard conversion between bit
and phase queries, as described in [NielsenChuang2010], and gives exact full-state, marginal,
and event probability formulas.

The compressed oracle changes records only at the queried address. Consequently the database
support is bounded by the query count, and binomial moments of its record count satisfy explicit
bounds.

## Main statements

* `databaseXor_fullstate`: decompressed amplitudes factor into a Bernoulli amplitude and an
  ordinary oracle amplitude.
* `databaseXor_event`: database event probabilities equal Bernoulli averages.
* `databaseXor_support`: databases larger than the query budget have zero amplitude.
* `databaseXor_moment`: bounds binomial moments of the number of records.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped BigOperators

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- Running the lifted bit-to-phase compiled circuit with the compressed oracle equals running
the original lifted circuit with `databaseXorOracle`. -/
theorem run_databaseXor_compiled (p : ℝ) (C : Circuit ((I × Bool) × W))
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    Run (compressedOracle p) (tensorLiftCircuit (bitToPhaseCircuitSameInput C)) v =
      Run (databaseXorOracle p) (tensorLiftCircuit C) v := by
  induction C generalizing v with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [bitToPhaseCircuitSameInput, List.flatMap_cons, bitToPhaseStep,
        List.cons_append, List.nil_append, tensorLiftCircuit, List.map_cons,
        tensorLiftStep, run_gate]
      exact ih _
    | query =>
      simp only [bitToPhaseCircuitSameInput, List.flatMap_cons, bitToPhaseStep,
        List.cons_append, List.nil_append, tensorLiftCircuit, List.map_cons,
        tensorLiftStep, run_gate, run_query]
      rw [← applyGate_mul, ← applyGate_mul]
      exact ih _

/-- The compressed database bit oracle execution equals `compressedRunState` of the bit-to-phase
compiled circuit. -/
theorem databaseXorRun_eq_compiled (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) :
    databaseXorRun p C ψ = compressedRunState p (bitToPhaseCircuitSameInput C) ψ :=
  (run_databaseXor_compiled p C _).symm

/-- For `p ∈ [0, 1]`, decompression identifies the database bit oracle execution with the joint
phase oracle execution of the compiled circuit from a Bernoulli database state. -/
theorem decompressedXorRun_eq_joint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    decompressedXorRun p C ψ =
      Run jointPhaseOracle (tensorLiftCircuit (bitToPhaseCircuitSameInput C))
        (TensorState ψ (bernoulliState p)) := by
  have hF : decompressGate (I := I) p * (decompressGate p)ᴴ = 1 := by
    have hU : decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact decompressGate_unitary p hp0 hp1
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU
  rw [decompressedXorRun, databaseXorRun_eq_compiled, compressedRunState,
    compressed_run_from_empty p hp0 hp1, ← applyGate_mul, tensorGate_mul,
    Matrix.one_mul, hF, tensorGate_one, applyGate_one]

/-- For `p ∈ [0, 1]`, each decompressed joint amplitude is the Bernoulli input amplitude times
the ordinary bit oracle circuit amplitude for that input. -/
theorem databaseXor_fullstate (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q : (I × Bool) × W) (x : I → Bool) :
    decompressedXorRun p C ψ (q, x) =
      bernoulliState p x * Run (workspaceBitOracle x) C ψ q := by
  rw [decompressedXorRun_eq_joint p hp0 hp1, joint_run_expansion,
    run_bitToPhaseCircuitSameInput]

/-- For `p ∈ [0, 1]`, the reduced algorithm matrix is the Bernoulli-weighted sum of outer
products of the ordinary bit oracle output states. -/
theorem databaseXor_marginal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q q' : (I × Bool) × W) :
    databaseXorMarginal p C ψ q q' =
      ∑ x : I → Bool, bernoulliPmf p x * Run (workspaceBitOracle x) C ψ q *
        star (Run (workspaceBitOracle x) C ψ q') := by
  simp only [databaseXorMarginal, databaseXorRun_eq_compiled]
  simpa only [run_bitToPhaseCircuitSameInput] using!
    compressed_marginal p hp0 hp1 (bitToPhaseCircuitSameInput C) ψ q q'

/-- Bit-to-phase compilation preserves query count and adds two gates per query. -/
theorem databaseXor_compilation_cost (C : Circuit ((I × Bool) × W)) :
    QueryCount (bitToPhaseCircuitSameInput C) = QueryCount C ∧
      GateCount (bitToPhaseCircuitSameInput C) = GateCount C + 2 * QueryCount C :=
  ⟨bitToPhaseCircuitSameInput_queryCount C, bitToPhaseCircuitSameInput_gateCount C⟩

/-- Lifting the bit-to-phase compiled circuit preserves the original query count and adds two
gates per query to the original gate count. -/
theorem databaseXor_joint_cost (C : Circuit ((I × Bool) × W)) :
    QueryCount (tensorLiftCircuit (bitToPhaseCircuitSameInput C)) = QueryCount C ∧
      GateCount (tensorLiftCircuit (bitToPhaseCircuitSameInput C)) =
        GateCount C + 2 * QueryCount C := by
  have hl (D : Circuit ((I × Bool) × W)) :
      QueryCount (tensorLiftCircuit D) = QueryCount D ∧
        GateCount (tensorLiftCircuit D) = GateCount D := by
    induction D with
    | nil => exact ⟨rfl, rfl⟩
    | cons s D ih =>
      cases s with
      | gate U => exact ⟨ih.1, congrArg (· + 1) ih.2⟩
      | query => exact ⟨congrArg (· + 1) ih.1, ih.2⟩
  obtain ⟨hq, hg⟩ := hl (bitToPhaseCircuitSameInput C)
  rw [bitToPhaseCircuitSameInput_queryCount] at hq
  rw [bitToPhaseCircuitSameInput_gateCount] at hg
  exact ⟨hq, hg⟩

/-- For `p ∈ [0, 1]`, a circuit with at most `t` queries has zero compressed amplitude on
databases with more than `t` records. -/
theorem databaseXor_support (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) (t : ℕ)
    (ht : QueryCount C ≤ t) (q : (I × Bool) × W) (d : I → Bool)
    (hd : t < databaseCard d) : databaseXorRun p C ψ (q, d) = 0 := by
  rw [databaseXorRun_eq_compiled]
  exact database_support_bound p hp0 hp1 _ ψ t
    (by simpa only [bitToPhaseCircuitSameInput_queryCount] using! ht) q d hd

/-- Summing compressed joint Born probabilities over databases gives the Bernoulli average of
ordinary bit oracle Born probabilities. -/
theorem databaseXor_born_marginal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q : (I × Bool) × W) :
    (∑ d : I → Bool, BornProb (databaseXorRun p C ψ) (q, d)) =
      ∑ x : I → Bool, bernoulliPmf p x * BornProb (Run (workspaceBitOracle x) C ψ) q := by
  have h := congrArg Complex.re (databaseXor_marginal p hp0 hp1 C ψ q q)
  simp only [databaseXorMarginal, Complex.re_sum] at h
  simpa only [BornProb, mul_assoc, Complex.mul_conj, Complex.star_def,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re] using! h

/-- For `p ∈ [0, 1]`, the compressed execution probability of an algorithm event equals the
Bernoulli average of its ordinary bit oracle execution probabilities. -/
theorem databaseXor_event (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (S : Finset ((I × Bool) × W)) :
    MeasureProb (databaseXorRun p C ψ) (S ×ˢ Finset.univ) =
      ∑ x : I → Bool, bernoulliPmf p x * MeasureProb (Run (workspaceBitOracle x) C ψ) S := by
  simp only [MeasureProb, Finset.sum_product]
  simp_rw [databaseXor_born_marginal p hp0 hp1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm

/-- For `p ∈ [0, 1]`, compressed database execution of a unitary circuit from a normalized
algorithm state is normalized. -/
theorem databaseXor_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) :
    Normalized (databaseXorRun p C ψ) := by
  have hbit (x : I → Bool) :
      Normalized (Run (workspaceBitOracle (W := W) x) C ψ) :=
    normalized_run _ (tensorGate_unitary (bitOracleOn_unitary x) (Submonoid.one_mem _))
      C hC hψ
  have h := databaseXor_event p hp0 hp1 C ψ Finset.univ
  rw [Finset.univ_product_univ] at h
  simp_rw [measureProb_univ (hbit _), mul_one] at h
  have hmass : (∑ x : I → Bool, bernoulliPmf p x) = 1 := by
    unfold bernoulliPmf
    have hs := Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
      (fun (_ : I) (b : Bool) => if b then p else 1 - p)
    simpa using! hs.symm
  exact h.trans hmass

/-- Applying `U` tensored with the identity acts on each fixed second-register slice by `U`. -/
private theorem tensor_one_slice {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (U : Matrix A A ℂ) (v : QState (A × B)) (a : A) (b : B) :
    ApplyGate (TensorGate U (1 : Matrix B B ℂ)) v (a, b) =
      ApplyGate U (fun k => v (k, b)) a := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, tensorGate_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite]

/-- The database target Hadamard acts by summing over the Boolean response register while fixing
the address, workspace, and database. -/
theorem databaseTargetHadamard_apply (v : QState (((I × Bool) × W) × (I → Bool)))
    (j : I) (b : Bool) (w : W) (d : I → Bool) :
    ApplyGate databaseTargetHadamard v (((j, b), w), d) =
      ∑ c : Bool, Hadamard b c * v (((j, c), w), d) := by
  rw [databaseTargetHadamard, tensor_one_slice, controlHadamard, tensor_one_slice]
  simp [ApplyGate, Matrix.mulVec, dotProduct, tensorGate_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul]

/-- The compressed oracle acts within each fixed algorithm basis slice by a sum over database
indices. -/
private theorem compressedOracle_apply_slice (p : ℝ)
    (v : QState (((I × Bool) × W) × (I → Bool))) (q : (I × Bool) × W) (d : I → Bool) :
    ApplyGate (compressedOracle p) v (q, d) =
      ∑ e : I → Bool, compressedOracle p (q, d) (q, e) * v (q, e) := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_single q
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro e _
    rw [compressed_oracle_offdiag p q r d e (Ne.symm hr), zero_mul]
  · simp

/-- The action of the database bit oracle expands as a target Hadamard, compressed oracle
action, and target Hadamard. -/
theorem databaseXorOracle_apply (p : ℝ) (v : QState (((I × Bool) × W) × (I → Bool)))
    (j : I) (b : Bool) (w : W) (d : I → Bool) :
    ApplyGate (databaseXorOracle p) v (((j, b), w), d) =
      ∑ c : Bool, Hadamard b c *
        (∑ e : I → Bool, compressedOracle p (((j, c), w), d) (((j, c), w), e) *
          (∑ a : Bool, Hadamard c a * v (((j, a), w), e))) := by
  simp only [databaseXorOracle, applyGate_mul, databaseTargetHadamard_apply,
    compressedOracle_apply_slice]

/-- For `p ∈ [0, 1]`, each fixed-address database bit oracle entry is a Hadamard sum of the
identity branch and the local compressed query branch. -/
theorem databaseXorOracle_entry (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d e : I → Bool) :
    databaseXorOracle p (((j, b), w), d) (((j, a), w), e) =
      ∑ c : Bool, Hadamard b c *
        (if c then
          if ∀ k, k ≠ j → d k = e k then compressedQueryEntry p (d j) (e j) else 0
        else if d = e then 1 else 0) * Hadamard c a := by
  have h := databaseXorOracle_apply p (Ket (((j, a), w), e)) j b w d
  have hk : ApplyGate (databaseXorOracle p) (Ket (((j, a), w), e)) (((j, b), w), d) =
      databaseXorOracle p (((j, b), w), d) (((j, a), w), e) := by
    simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite]
  rw [hk] at h
  have hket (c : Bool) (f : I → Bool) :
      (∑ a' : Bool, Hadamard c a' * Ket (((j, a), w), e) (((j, a'), w), f)) =
        if f = e then Hadamard c a else 0 := by
    by_cases hf : f = e
    · subst f
      simp [Ket, Prod.mk.injEq, mul_ite]
    · simp [Ket, Prod.mk.injEq, hf]
  simp_rw [hket] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq'] at h
  simpa only [compressed_oracle_entry p hp0 hp1, Finset.mem_univ, ite_true, mul_assoc] using! h

/-- A database bit oracle matrix entry vanishes when its address or workspace indices differ. -/
theorem databaseXorOracle_offblock (p : ℝ) (j k : I) (b a : Bool) (w v : W)
    (d e : I → Bool) (h : j ≠ k ∨ w ≠ v) :
    databaseXorOracle p (((j, b), w), d) (((k, a), v), e) = 0 := by
  have hket (a' : Bool) (f : I → Bool) : Ket (((k, a), v), e) (((j, a'), w), f) = 0 := by
    rcases h with hj | hw <;> simp [Ket, Prod.mk.injEq, *]
  have he := databaseXorOracle_apply p (Ket (((k, a), v), e)) j b w d
  simp only [hket, mul_zero, Finset.sum_const_zero] at he
  simpa only [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using! he

/-- For `p ∈ [0, 1]`, a nonzero database bit oracle entry preserves every database coordinate
other than the queried address. -/
theorem databaseXorOracle_locality (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : databaseXorOracle p (((j, b), w), d) (((j, a), w), e) ≠ 0) :
    ∀ k, k ≠ j → d k = e k := by
  by_contra hn
  have hde : d ≠ e := by intro he; subst e; exact hn (fun _ _ => rfl)
  apply h
  rw [databaseXorOracle_entry p hp0 hp1]
  apply Finset.sum_eq_zero
  intro c _
  cases c <;> simp [hn, hde]

/-- For `p ∈ [0, 1]`, a nonzero database bit oracle transition increases the record count by at
most one. -/
theorem databaseXorOracle_card_step (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : databaseXorOracle p (((j, b), w), d) (((j, a), w), e) ≠ 0) :
    databaseCard d ≤ databaseCard e + 1 := by
  have hl := databaseXorOracle_locality p hp0 hp1 j b a w d e h
  have hs : databaseSupport d ⊆ insert j (databaseSupport e) := by
    intro k hk
    by_cases hkj : k = j
    · simp [hkj]
    · apply Finset.mem_insert_of_mem
      simpa only [databaseSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        hl k hkj] using! hk
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- For a normalized unitary execution with at most `t` queries, the expected value of
`Nat.choose (databaseCard d) k` is at most `Nat.choose t k * (2 * Real.sqrt (p * (1 - p))) ^
k` when `p ∈ [0, 1]`. -/
theorem databaseXor_moment (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ)
    (k t : ℕ) (ht : QueryCount C ≤ t) :
    (∑ q : (I × Bool) × W, ∑ d : I → Bool,
      (Nat.choose (databaseCard d) k : ℝ) * ‖databaseXorRun p C ψ (q, d)‖ ^ 2) ≤
        (Nat.choose t k : ℝ) * (2 * Real.sqrt (p * (1 - p))) ^ k := by
  simp only [databaseXorRun_eq_compiled]
  exact database_moment_bound p hp0 hp1 _
    ((bitToPhaseCircuitSameInput_isUnitaryCircuit C).mpr hC) ψ hψ k t
    (by simpa only [bitToPhaseCircuitSameInput_queryCount] using! ht)

omit [DecidableEq I] in

/-- A database has at least two records exactly when it records at two distinct addresses. -/
theorem databaseHasRecords_two_iff (d : I → Bool) :
    databaseHasRecords 2 d ↔
      ∃ j k : I, j ≠ k ∧ databaseRecordsAt j d ∧ databaseRecordsAt k d := by
  change 2 ≤ (databaseSupport d).card ↔ _
  constructor
  · intro h
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (show 1 < (databaseSupport d).card by omega)
    exact ⟨j, k, hjk, (Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hk).2⟩
  · rintro ⟨j, k, hjk, hj, hk⟩
    have hc := Finset.one_lt_card.mpr
      ⟨j, (by simpa [databaseSupport] using! hj : j ∈ databaseSupport d),
        k, (by simpa [databaseSupport] using! hk : k ∈ databaseSupport d), hjk⟩
    omega

/-- For `p ∈ [0, 1]`, two consecutive database bit oracle queries restore the algorithm state
tensored with the empty database basis state. -/
theorem databaseXorRun_two_queries (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : QState ((I × Bool) × W)) :
    databaseXorRun p [Step.query, Step.query] ψ = TensorState ψ (Ket (fun _ => false)) := by
  have hh : decompressedXorRun p [Step.query, Step.query] ψ =
      decompressedXorRun p [] ψ := by
    funext qx
    obtain ⟨q, x⟩ := qx
    rw [databaseXor_fullstate p hp0 hp1, databaseXor_fullstate p hp0 hp1]
    simp only [run_query, run_nil, ← applyGate_mul, workspaceBitOracle,
      tensorGate_mul, bitOracleOn_mul_self, Matrix.one_mul, tensorGate_one, applyGate_one]
  have hd := congrArg (ApplyGate (TensorGate
    (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ)) hh
  simpa only [decompressedXorRun, ← applyGate_mul, tensorGate_mul, Matrix.one_mul,
    decompressGate_unitary p hp0 hp1, tensorGate_one, applyGate_one] using! hd

end Qatlib.Concepts.QueryComplexity.DegreeMethod
