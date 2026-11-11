/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircApprox95.MainResults.QuantitativeNet
import Qatlib.Papers.QCircApprox95.MainResults.ProblemCounting
import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Tactic

/-!
# Gate word covers and problem counts

Local gate placement preserves operator norms and differences. A telescoping product estimate
turns finite covers of the gate set into covers of fixed-length circuits and their basis-state
outputs.

The resulting covers bound the numbers of decision and guessing problems represented by these
circuits, with a concrete decision bound obtained from a quantitative unitary net. See
[Knill1995].

## Main statements

* `repBy_covered_by_words`: approximates a length-b circuit by a word in the gate cover.
* `decision_net_count`: bounds the number of decision problems by the number of cover words.
* `guess_net_count`: adds the output ambiguity factor for guessing problems.

## References

* [Knill, 1995][Knill1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Kronecker
open Qatlib.Concepts.LocalCircuits.LocalGateCosts
open Qatlib.Foundations.BornMetrics.FiniteStats
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.QCircApprox95.MainResults

/-- Placing a local matrix difference on the selected wires equals the difference of the placed
matrices. -/
theorem placeLocalGate_sub {n : ℕ} (S : Finset (Fin n))
    (V W : Matrix (Reg S.card) (Reg S.card) ℂ) :
    placeLocalGate S (V - W) = placeLocalGate S V - placeLocalGate S W := by
  ext i j
  obtain ⟨x, rfl⟩ : ∃ x, bitVecEquiv n x = i :=
    ⟨(bitVecEquiv n).symm i, (bitVecEquiv n).apply_symm_apply i⟩
  obtain ⟨y, rfl⟩ : ∃ y, bitVecEquiv n y = j :=
    ⟨(bitVecEquiv n).symm j, (bitVecEquiv n).apply_symm_apply j⟩
  rw [Matrix.sub_apply, placeLocalGate_apply, placeLocalGate_apply, placeLocalGate_apply]
  by_cases h : outside S x = outside S y <;> simp [h, Matrix.sub_apply]

/-- Placing a local gate on the selected wires preserves its operator norm. -/
theorem placeLocalGate_l2_norm {n : ℕ} (S : Finset (Fin n))
    (V : Matrix (Reg S.card) (Reg S.card) ℂ) :
    ‖placeLocalGate S V‖ = ‖V‖ := by
  unfold placeLocalGate
  rw [l2_norm_relabelGate]
  change ‖relabelGate (split S).symm
    (V ⊗ₖ (1 : Matrix (Outside n S) (Outside n S) ℂ))‖ = ‖V‖
  rw [l2_norm_relabelGate]
  haveI : Nonempty (Outside n S) := ⟨fun _ => false⟩
  rw [Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_kronecker,
    Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_one_eq, mul_one]

/-- The operator-norm distance between two placed local matrices equals their original
operator-norm distance. -/
theorem placeLocalGate_l2_sub {n : ℕ} (S : Finset (Fin n))
    (V W : Matrix (Reg S.card) (Reg S.card) ℂ) :
    ‖placeLocalGate S V - placeLocalGate S W‖ = ‖V - W‖ := by
  rw [← placeLocalGate_sub, placeLocalGate_l2_norm]

/-- For paired lists of unitary matrices with each pair at distance at most a nonnegative `ε`,
the products are at distance at most the list length times `ε`. -/
theorem pair_list_prod_close {N : ℕ} (l : List (Matrix (Fin N) (Fin N) ℂ ×
      Matrix (Fin N) (Fin N) ℂ))
    (hunit1 : ∀ p ∈ l, p.1 ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hunit2 : ∀ p ∈ l, p.2 ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ p ∈ l, ‖p.1 - p.2‖ ≤ ε) :
    ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ ≤ (l.length : ℝ) * ε := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    have hp1 : ‖p.1 - p.2‖ ≤ ε := h p (by simp)
    have hp2 : p.2 ∈ Matrix.unitaryGroup (Fin N) ℂ := hunit2 p (by simp)
    have htail : ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ ≤ (l.length : ℝ) * ε :=
      ih (fun q hq => hunit1 q (List.mem_cons_of_mem _ hq))
        (fun q hq => hunit2 q (List.mem_cons_of_mem _ hq))
        (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hcu2 : ‖p.2‖ ≤ 1 :=
      Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hp2
    have hPfst : ‖(l.map Prod.fst).prod‖ ≤ 1 := by
      apply Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_list_prod_le_one
      intro a ha
      rcases List.mem_map.mp ha with ⟨q, hq, rfl⟩
      exact Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one
        (hunit1 q (List.mem_cons_of_mem _ hq))
    calc ‖p.1 * (l.map Prod.fst).prod - p.2 * (l.map Prod.snd).prod‖
        ≤ ‖p.1 - p.2‖ * ‖(l.map Prod.fst).prod‖ +
            ‖p.2‖ * ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ :=
          Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_rect_mul_sub_mul_le
            p.1 p.2 (l.map Prod.fst).prod (l.map Prod.snd).prod
      _ ≤ ε * 1 + 1 * ((l.length : ℝ) * ε) := by
          apply add_le_add
          · calc ‖p.1 - p.2‖ * ‖(l.map Prod.fst).prod‖
                ≤ ε * ‖(l.map Prod.fst).prod‖ :=
                  mul_le_mul_of_nonneg_right hp1 (norm_nonneg _)
              _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hPfst hε
          · calc ‖p.2‖ * ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖
                ≤ 1 * ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖ :=
                  mul_le_mul_of_nonneg_right hcu2 (norm_nonneg _)
              _ ≤ 1 * ((l.length : ℝ) * ε) :=
                  mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = (l.length : ℝ) * ε + ε := by ring

/-- A circuit in `repBy g n b` has a length-`b` approximation using the unitary cover `C`, with
operator-norm error at most `b * δ`. This supplies the word cover used in Theorems 5.1 and
5.3 of [Knill1995]. -/
theorem repBy_covered_by_words {g n b : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (C : Finset (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
    (hgunit : ∀ G ∈ gateSet g n, G ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hC : ∀ G ∈ gateSet g n, ∃ c ∈ C, ‖G - c‖ ≤ δ)
    (hCu : ∀ c ∈ C, c ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∀ U ∈ repBy g n b, ∃ cs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      cs.length = b ∧ (∀ c ∈ cs, c ∈ C) ∧ ‖U - cs.prod‖ ≤ (b : ℝ) * δ := by
  classical
  intro U hU
  obtain ⟨word, hlen, hlegal, rfl⟩ := hU

  let choose_c : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ →
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    fun G => if h : G ∈ gateSet g n then Classical.choose (hC G h) else G
  have choose_mem : ∀ G (hG : G ∈ gateSet g n), choose_c G ∈ C := by
    intro G hG
    simp only [choose_c, dif_pos hG]
    exact (Classical.choose_spec (hC G hG)).1
  have choose_close : ∀ G (hG : G ∈ gateSet g n), ‖G - choose_c G‖ ≤ δ := by
    intro G hG
    simp only [choose_c, dif_pos hG]
    exact (Classical.choose_spec (hC G hG)).2
  let pairs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ×
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
    word.map (fun G => (G, choose_c G))
  let cs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := word.map choose_c
  have hfst : pairs.map Prod.fst = word := by
    simp only [pairs, List.map_map]
    change List.map id word = word
    exact List.map_id word
  have hsnd : pairs.map Prod.snd = cs := by
    simp only [cs, pairs, List.map_map]
    change List.map choose_c word = List.map choose_c word
    rfl
  have hpairs_close : ∀ p ∈ pairs, ‖p.1 - p.2‖ ≤ δ := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨G, hG, rfl⟩ := hp
    exact choose_close G (hlegal G hG)
  have hpairs_unitary1 : ∀ p ∈ pairs, p.1 ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨G, hG, rfl⟩ := hp
    exact hgunit G (hlegal G hG)
  have hpairs_unitary2 : ∀ p ∈ pairs, p.2 ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨G, hG, rfl⟩ := hp
    exact hCu (choose_c G) (choose_mem G (hlegal G hG))
  have hcs_mem : ∀ c ∈ cs, c ∈ C := by
    intro c hc
    rw [show cs = pairs.map Prod.snd from hsnd.symm] at hc
    rw [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    rw [List.mem_map] at hp
    obtain ⟨G, hG, rfl⟩ := hp
    exact choose_mem G (hlegal G hG)
  refine ⟨cs, ?_, hcs_mem, ?_⟩
  · simp only [cs, List.length_map]; exact hlen
  · have hplen : pairs.length = b := by simp [pairs, hlen]
    rw [← hfst, ← hsnd]
    simpa [hplen] using
      pair_list_prod_close pairs hpairs_unitary1 hpairs_unitary2 hδ hpairs_close

/-- The same length-`b` cover word approximates every basis-state output of a represented
circuit within `b * δ` in Euclidean norm. This is the state cover used in the counting
arguments of [Knill1995]. -/
theorem repBy_states_covered {g n b : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (C : Finset (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
    (hgunit : ∀ G ∈ gateSet g n, G ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hC : ∀ G ∈ gateSet g n, ∃ c ∈ C, ‖G - c‖ ≤ δ)
    (hCu : ∀ c ∈ C, c ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ∀ U ∈ repBy g n b, ∃ cs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      cs.length = b ∧ (∀ c ∈ cs, c ∈ C) ∧
      ∀ x : Fin (2 ^ n),
        l2norm (U *ᵥ ket x - cs.prod *ᵥ ket x) ≤ (b : ℝ) * δ := by
  intro U hU
  obtain ⟨cs, hlen, hmem, hclose⟩ :=
    repBy_covered_by_words hδ C hgunit hC hCu U hU
  refine ⟨cs, hlen, hmem, fun x => ?_⟩
  have hsub : U *ᵥ ket x - cs.prod *ᵥ ket x = (U - cs.prod) *ᵥ ket x := by
    rw [Matrix.sub_mulVec]
  rw [hsub]
  calc l2norm ((U - cs.prod) *ᵥ ket x)
      ≤ ‖U - cs.prod‖ * l2norm (ket x) :=
        Qatlib.Foundations.BornMetrics.FiniteStats.l2norm_mulVec_le _ _
    _ = ‖U - cs.prod‖ * 1 := by
        rw [Qatlib.Foundations.BornMetrics.FiniteStats.l2norm_ket]
    _ = ‖U - cs.prod‖ := by ring
    _ ≤ (b : ℝ) * δ := hclose

/-- If `2 * (b * δ) < 1 / q`, a finite family of decision problems represented by length-`b`
circuits has cardinality at most `C.card ^ b`, under the stated unitary covering
assumptions. See Theorem 5.1 of [Knill1995]. -/
theorem decision_net_count {g n b : ℕ} {q δ : ℝ}
    (hq : 0 < q) (hδ0 : 0 ≤ δ) (hsmall : 2 * ((b : ℝ) * δ) < 1 / q)
    (C : Finset (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
    (hgunit : ∀ G ∈ gateSet g n, G ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hC : ∀ G ∈ gateSet g n, ∃ c ∈ C, ‖G - c‖ ≤ δ)
    (hCu : ∀ c ∈ C, c ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (p : Fin (2 ^ n) → Fin 2)
    (F : Finset (Fin (2 ^ n) → Fin 2))
    (hF : ∀ f ∈ F, ∃ U ∈ repBy g n b,
      decides p q (fun x => U *ᵥ ket x) f) :
    (F.card : ℝ) ≤ (C.card : ℝ) ^ b := by
  classical

  have hrhs : (1 : ℝ) / q = 2 * (1 / (2 * q)) := by
    field_simp
  rw [hrhs] at hsmall
  have hquarter : (b : ℝ) * δ < 1 / (2 * q) := by linarith
  set δ' : ℝ := ((b : ℝ) * δ + 1 / (2 * q)) / 2 with hδ'def
  have hlt : (b : ℝ) * δ < δ' := by rw [hδ'def]; linarith
  have h2δ' : 2 * δ' < 1 / q := by rw [hδ'def]; linarith
  let c : (Fin b → ↥C) → Fin (2 ^ n) → Fin (2 ^ n) → ℂ :=
    fun i x =>
      (List.ofFn (fun j : Fin b =>
        ((i j : ↥C) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))).prod *ᵥ ket x
  have hcount : F.card ≤ Fintype.card (Fin b → ↥C) := by
    apply decision_card_le_indexed p hq h2δ' c F
    intro f hf
    obtain ⟨U, hU, hdec⟩ := hF f hf
    obtain ⟨cs, hlen, hmem, hclose⟩ :=
      repBy_states_covered hδ0 C hgunit hC hCu U hU
    let i : Fin b → ↥C :=
      fun j => ⟨cs.get (Fin.cast hlen.symm j), hmem _ (List.get_mem _ _)⟩
    have hcs : (List.ofFn (fun j : Fin b =>
        ((i j : ↥C) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))) = cs := by
      have hcongr := List.ofFn_congr hlen (List.get cs)
      rw [List.ofFn_get] at hcongr
      simpa [i] using hcongr.symm
    refine ⟨fun x => U *ᵥ ket x, ?_, hdec, i, ?_⟩
    · exact unitary_column_mass (repBy_unitary hU)
    · intro x
      have hx := hclose x
      have hx' : l2norm (U *ᵥ ket x - cs.prod *ᵥ ket x) < δ' := lt_of_le_of_lt hx hlt
      simpa [c, hcs] using hx'
  calc (F.card : ℝ) ≤ (Fintype.card (Fin b → ↥C) : ℝ) := by exact_mod_cast hcount
    _ = (C.card : ℝ) ^ b := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
        push_cast
        ring

/-- For `n ≥ 1` and `0 < δ ≤ 1 / 2`, the stated decision gap bounds the number of represented
problems by `(2 / δ) ^ (b * 2 ^ (4 * n))`. This is a concrete net-based count associated
with Theorem 5.1 of [Knill1995]. -/
theorem decision_net_count_concrete (n g b : ℕ) (hn : 1 ≤ n) {q δ : ℝ}
    (hq : 0 < q) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsmall : 2 * ((b : ℝ) * δ) < 1 / q)
    (p : Fin (2 ^ n) → Fin 2)
    (F : Finset (Fin (2 ^ n) → Fin 2))
    (hF : ∀ f ∈ F, ∃ U ∈ repBy g n b,
      decides p q (fun x => U *ᵥ ket x) f) :
    (F.card : ℝ) ≤ (2 / δ) ^ (b * 2 ^ (4 * n)) := by
  obtain ⟨s, hsU, hcover, hcard⟩ := quantitative_unitary_net n hn hδ0 hδ
  have hgunit : ∀ G ∈ gateSet g n, G ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
    fun G hG => gateSet_unitary hG
  have hCcover : ∀ G ∈ gateSet g n, ∃ c ∈ s, ‖G - c‖ ≤ δ := by
    intro G hG
    exact hcover G (hgunit G hG)
  have hCu : ∀ c ∈ s, c ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    intro c hc
    exact hsU hc
  have hb := decision_net_count (g := g) (n := n) (b := b) hq hδ0.le hsmall
    s hgunit hCcover hCu p F hF
  refine hb.trans ?_
  calc (s.card : ℝ) ^ b ≤ ((2 / δ) ^ (2 ^ (4 * n))) ^ b :=
        pow_le_pow_left₀ (by positivity) hcard b
    _ = (2 / δ) ^ (b * 2 ^ (4 * n)) := by
        rw [← pow_mul, mul_comm]

/-- The product of a list of unitary matrices is unitary. -/
theorem list_prod_unitary {N : ℕ} (l : List (Matrix (Fin N) (Fin N) ℂ))
    (h : ∀ c ∈ l, c ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    l.prod ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons a l ih =>
    rw [List.prod_cons]
    exact Submonoid.mul_mem _ (h a (by simp))
      (ih (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- If `b * δ < 1 / (2 * Real.sqrt q)`, the stated unitary gate cover bounds the number of
represented guessing problems by `C.card ^ b * (4 * q) ^ (2 ^ n)`. See Theorem 5.3 of
[Knill1995]. -/
theorem guess_net_count {g n b A : ℕ} {q δ : ℝ}
    (hq : 0 < q) (hδ0 : 0 ≤ δ) (hsmall : (b : ℝ) * δ < 1 / (2 * Real.sqrt q))
    (C : Finset (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
    (hgunit : ∀ G ∈ gateSet g n, G ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hC : ∀ G ∈ gateSet g n, ∃ c ∈ C, ‖G - c‖ ≤ δ)
    (hCu : ∀ c ∈ C, c ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (p : Fin (2 ^ n) → Fin A)
    (F : Finset (Fin (2 ^ n) → Fin A))
    (hF : ∀ f ∈ F, ∃ U ∈ repBy g n b,
      guesses p q (fun x => U *ᵥ ket x) f) :
    (F.card : ℝ) ≤ (C.card : ℝ) ^ b * (4 * q) ^ (2 ^ n) := by
  classical

  set δ' : ℝ := ((b : ℝ) * δ + 1 / (2 * Real.sqrt q)) / 2 with hδ'def
  have hlt : (b : ℝ) * δ < δ' := by rw [hδ'def]; linarith
  have h2δ' : δ' < 1 / (2 * Real.sqrt q) := by rw [hδ'def]; linarith
  let c : (Fin b → ↥C) → Fin (2 ^ n) → Fin (2 ^ n) → ℂ :=
    fun i x =>
      (List.ofFn (fun j : Fin b =>
        ((i j : ↥C) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))).prod *ᵥ ket x
  have hc : ∀ i x, ∑ k, ‖c i x k‖ ^ 2 = 1 := by
    intro i x
    have hlist : ∀ G ∈ (List.ofFn (fun j : Fin b =>
        ((i j : ↥C) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))),
        G ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
      rw [List.forall_mem_ofFn_iff]
      intro j
      exact hCu _ (i j).2
    exact unitary_column_mass (list_prod_unitary _ hlist) x
  have hcount : (F.card : ℝ) ≤
      (Fintype.card (Fin b → ↥C) : ℝ) * (4 * q) ^ (2 ^ n) := by
    have h := guess_card_le_indexed (N := 2 ^ n) (A := A) (τ := Fin b → ↥C)
      p hq h2δ' c hc F ?_
    · simpa using h
    · intro f hf
      obtain ⟨U, hU, hdec⟩ := hF f hf
      obtain ⟨cs, hlen, hmem, hclose⟩ :=
        repBy_states_covered hδ0 C hgunit hC hCu U hU
      let i : Fin b → ↥C :=
        fun j => ⟨cs.get (Fin.cast hlen.symm j), hmem _ (List.get_mem _ _)⟩
      have hcs : (List.ofFn (fun j : Fin b =>
          ((i j : ↥C) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))) = cs := by
        have hcongr := List.ofFn_congr hlen (List.get cs)
        rw [List.ofFn_get] at hcongr
        simpa [i] using hcongr.symm
      refine ⟨fun x => U *ᵥ ket x, unitary_column_mass (repBy_unitary hU), hdec, i, ?_⟩
      intro x
      have hx := hclose x
      have hx' : l2norm (U *ᵥ ket x - cs.prod *ᵥ ket x) < δ' := lt_of_le_of_lt hx hlt
      simpa [c, hcs] using hx'
  have hcard_eq : (Fintype.card (Fin b → ↥C) : ℝ) = (C.card : ℝ) ^ b := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    push_cast
    ring
  calc (F.card : ℝ) ≤ (Fintype.card (Fin b → ↥C) : ℝ) * (4 * q) ^ (2 ^ n) := hcount
    _ = (C.card : ℝ) ^ b * (4 * q) ^ (2 ^ n) := by rw [hcard_eq]

end Qatlib.Papers.QCircApprox95.MainResults
