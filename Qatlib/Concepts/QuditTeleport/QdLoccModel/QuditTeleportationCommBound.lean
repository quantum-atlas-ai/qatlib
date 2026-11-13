/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Mathlib.Combinatorics.Pigeonhole

/-!
# Qudit message guessing and communication bounds

The results bound `qdBestGuessMass` and `qdDecodeMass` for finite outcome encodings, including
uniform qudit outcomes and collapsed messages. Counting Boolean lists relates injective message
encodings to `qdCommCost`.

The theorems also collect explicit protocol recovery and encoding properties, resource
characterizations, and repeated-coding reliability for the combined teleportation theorem. These
results develop resource and communication properties of teleportation
[BennettEtAl1993Teleportation].

## Main statements

* `clause4_clause3`: A normalized nonnegative outcome law has a message value with weight at
  least the reciprocal of the image size; any collapsed pair contributes its combined weight to
  one message guess.
* `clause4_clause4`: For uniform qudit outcomes, injective, noninjective, and constant encodings
  satisfy the stated optimal fixed-message guessing bounds, while any decoder succeeds with
  weight at most the image size divided by `n²`.
* `qdCommCost_of_card`: An injective message encoding and at least `n²` outcomes imply `n² ≤ 2 ^
  (qdCommCost P + 1)`.
* `clause4_clause6`: The standard qudit protocol has corrected branch weight `1 / n²`, identity
  total output, and injective decodable messages of length `2 * Nat.clog 2 n`
  [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

/-- The maximum fold of a real list is at least its initial seed. -/
theorem list_foldl_max_seed_le : ∀ (l : List ℝ) (b : ℝ), b ≤ l.foldl max b := by
  intro l
  induction l with
  | nil => intro b; exact le_rfl
  | cons hd tl ih =>
    intro b
    show b ≤ List.foldl max (max b hd) tl
    exact le_trans (le_max_left b hd) (ih (max b hd))

/-- Every member of a real list is at most the maximum fold with any initial seed. -/
theorem list_foldl_max_le_of_mem : ∀ (l : List ℝ) (b : ℝ) (x : ℝ), x ∈ l →
    x ≤ l.foldl max b := by
  intro l
  induction l with
  | nil => intro b x hx; exact absurd hx (by simp)
  | cons hd tl ih =>
    intro b x hx
    rcases List.mem_cons.mp hx with h | hx
    · rw [h]
      simp only [List.foldl_cons]
      exact le_trans (le_max_right b hd) (list_foldl_max_seed_le tl (max b hd))
    · simp only [List.foldl_cons]
      exact ih (max b hd) x hx

/-- If the seed and every list element are bounded above by `r`, their maximum fold is also
bounded by `r`. -/
theorem list_foldl_max_le_upper : ∀ (l : List ℝ) (b r : ℝ), (∀ x ∈ l, x ≤ r) → b ≤ r →
    l.foldl max b ≤ r := by
  intro l
  induction l with
  | nil => intro b r _ hb; exact hb
  | cons hd tl ih =>
    intro b r hall hb
    simp only [List.foldl_cons]
    exact ih (max b hd) r (fun x hx => hall x (by simp [hx]))
      (max_le hb (hall hd (by simp)))

/-- The weight of any fixed message guess is at most `qdBestGuessMass`. -/
theorem qdGuessMass_le_best {κ σ : Type} [Fintype κ] [Fintype σ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) (g : σ) :
    qdGuessMass p m g ≤ qdBestGuessMass p m := by
  unfold qdBestGuessMass
  refine list_foldl_max_le_of_mem _ 0 _ ?_
  exact List.mem_map_of_mem (f := qdGuessMass p m) (by simp)

/-- If every fixed-message guess has weight at most a nonnegative `r`, then `qdBestGuessMass` is
at most `r`. -/
theorem qdBestGuessMass_le_of_forall {κ σ : Type} [Fintype κ] [Fintype σ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) {r : ℝ} (hr : 0 ≤ r)
    (hall : ∀ g : σ, qdGuessMass p m g ≤ r) :
    qdBestGuessMass p m ≤ r := by
  unfold qdBestGuessMass
  refine list_foldl_max_le_upper _ 0 r ?_ hr
  intro x hx
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
  exact hall g

/-- For uniform qudit outcomes, a decoder's success weight is the number of correctly decoded
outcomes divided by `n²`. -/
theorem qdDecodeMass_uniform (n : ℕ) {σ : Type} [DecidableEq (Fin n × Fin n)] [DecidableEq σ]
    (m : Fin n × Fin n → σ) (g : σ → Fin n × Fin n) :
    qdDecodeMass (qdUniform n) m g =
      ((Finset.univ.filter (fun k => g (m k) = k)).card : ℕ) / ((n * n : ℕ) : ℝ) := by
  simp only [qdDecodeMass, qdUniform]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- For a perfect protocol with a normalized pure resource and unitary corrections, message
consistency makes equal-message corrections induce the same conjugation map. -/
theorem clause4_clause2_msgConsistent :
    ∀ (n : ℕ) (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ)
      (U : κ → Operator n) (Ψ : QState (Fin n × Fin n)),
    Normalized Ψ → QdLoccUnitaryCorr P U → QdLoccPerfect P (outerProduct Ψ) →
    (QdLoccMsgConsistent P → ∀ k k' : κ, P.msgCode k = P.msgCode k' →
      QdSameConjugation n (U k) (U k')) := by
  intro n κ _ P U Ψ _ hU _ hc k k' hm
  exact qdMsgConsistent_sameConjugation P U hU hc hm

/-- An outcome count of at least `n²` implies `n² ≤ 2 ^ qdMessageBits κ`. -/
theorem clause4_clause2_counting_reduce (n : ℕ) (κ : Type) [Fintype κ]
    (hcard : n * n ≤ Fintype.card κ) :
    n * n ≤ 2 ^ qdMessageBits κ :=
  Nat.le_trans hcard (qdCard_le_pow_messageBits κ)

/-- A normalized nonnegative outcome law has a message value with weight at least the reciprocal
of the image size; any collapsed pair contributes its combined weight to one message guess. -/
theorem clause4_clause3 : ∀ (κ σ : Type) (_hκ : Fintype κ) (_hd : DecidableEq σ) (p : κ → ℝ),
    (∀ k, 0 ≤ p k) → ∑ k, p k = 1 → ∀ m : κ → σ,
    (∃ g : σ,
      1 / ((Fintype.card (Set.range m) : ℕ) : ℝ) ≤ qdGuessMass p m g) ∧
    (∀ a b : κ, a ≠ b → m a = m b →
      ∃ g : σ, p a + p b ≤ qdGuessMass p m g) := by
  intro κ σ _ _ p hp hsum m
  constructor
  · have hkne : Nonempty κ := by
      by_contra hc
      haveI : IsEmpty κ := not_nonempty_iff.mp hc
      have h0 : ∑ k, p k = 0 := by
        rw [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0] at hsum
      exact zero_ne_one hsum
    obtain k₀ := Classical.choice hkne
    have hne : (Finset.univ.image m).Nonempty :=
      ⟨m k₀, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hcard : (Finset.univ.image m).card = Fintype.card (Set.range m) := by
      rw [← Set.toFinset_card (Set.range m), Set.toFinset_range m]
    have hpos : 0 < Fintype.card (Set.range m) :=
      Fintype.card_pos_iff.mpr ⟨⟨m k₀, ⟨k₀, rfl⟩⟩⟩
    have hNne : ((Fintype.card (Set.range m) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    have hbb : (Finset.univ.image m).card •
        (1 / ((Fintype.card (Set.range m) : ℕ) : ℝ)) ≤ ∑ k, p k := by
      rw [hcard, hsum, nsmul_eq_mul, mul_div_cancel₀ _ hNne]
    obtain ⟨g, _, hge⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (f := m) (s := Finset.univ) (t := Finset.univ.image m) (w := p)
      (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hne hbb
    exact ⟨g, hge⟩
  · intro a b hab hmab
    refine ⟨m a, ?_⟩
    show p a + p b ≤ ∑ k ∈ Finset.univ.filter (fun k => m k = m a), p k
    have hab' : a ≠ b := hab
    have hsub : Finset.cons a (Finset.cons b ∅ (by simp)) (by simp [hab']) ⊆
        Finset.univ.filter (fun k => m k = m a) := by
      intro x hx
      simp only [Finset.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · simp
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmab.symm⟩
      · exact absurd hx (by simp)
    calc p a + p b
        = ∑ x ∈ Finset.cons a (Finset.cons b ∅ (by simp)) (by simp [hab']), p x := by
          rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_empty]
          ring
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k => m k = m a), p k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hp k)

/-- For uniform qudit outcomes, injective, noninjective, and constant encodings satisfy the
stated optimal fixed-message guessing bounds, while any decoder succeeds with weight at most
the image size divided by `n²`. -/
theorem clause4_clause4 : ∀ (n : ℕ) (_hn : NeZero n) (σ : Type) (_hσ : Fintype σ) (_hd : DecidableEq σ)
    (m : Fin n × Fin n → σ),
    (Function.Injective m →
      qdBestGuessMass (qdUniform n) m = 1 / ((n * n : ℕ) : ℝ)) ∧
    (¬ Function.Injective m →
      2 / ((n * n : ℕ) : ℝ) ≤ qdBestGuessMass (qdUniform n) m ∧
        qdBestGuessMass (qdUniform n) m ≤ 1) ∧
    ((∃ c : σ, ∀ o : Fin n × Fin n, m o = c) →
      qdBestGuessMass (qdUniform n) m = 1) ∧
    (∀ g : σ → Fin n × Fin n,
      qdDecodeMass (qdUniform n) m g ≤
        ((Fintype.card (Set.range m) : ℕ) : ℝ) / ((n * n : ℕ) : ℝ)) := by
  intro n hn σ _ _ m
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn2pos : 0 < ((n * n : ℕ) : ℝ) := by
    have : 0 < (n * n : ℕ) := Nat.mul_pos hn0 hn0
    exact_mod_cast this
  have hn2ne : ((n * n : ℕ) : ℝ) ≠ 0 := ne_of_gt hn2pos

  have huniv : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
    simp [Fintype.card_prod]
  have hcard_le : ∀ g : σ,
      (Finset.univ.filter (fun k => m k = g)).card ≤ n * n := by
    intro g
    calc (Finset.univ.filter (fun k => m k = g)).card
          ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = n * n := huniv
  have hbest_le_one : qdBestGuessMass (qdUniform n) m ≤ 1 := by
    refine qdBestGuessMass_le_of_forall (qdUniform n) m (by norm_num) ?_
    intro g
    rw [qdGuessMass_uniform n m g]
    exact (div_le_one hn2pos).mpr (by exact_mod_cast hcard_le g)
  obtain o₀ : Fin n × Fin n := (⟨0, hn0⟩, ⟨0, hn0⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hinj
    have hfiber1 : (Finset.univ.filter (fun k => m k = m o₀)).card = 1 := by
      apply Nat.le_antisymm
      · refine Finset.card_le_one.mpr ?_
        intro x hx y hy
        have hx' : m x = m o₀ := (Finset.mem_filter.mp hx).2
        have hy' : m y = m o₀ := (Finset.mem_filter.mp hy).2
        exact hinj (hx'.trans hy'.symm)
      · have hsub : insert o₀ (∅ : Finset (Fin n × Fin n)) ⊆
            Finset.univ.filter (fun k => m k = m o₀) := by
          intro x hx
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · simp
          · exact absurd hx (by simp)
        have hc1 : (insert o₀ (∅ : Finset (Fin n × Fin n))).card = 1 := by simp
        calc (1:ℕ) = (insert o₀ (∅ : Finset (Fin n × Fin n))).card := hc1.symm
          _ ≤ (Finset.univ.filter (fun k => m k = m o₀)).card := Finset.card_le_card hsub
    have hge : (1:ℝ)/((n * n : ℕ) : ℝ) ≤ qdBestGuessMass (qdUniform n) m := by
      have h := qdGuessMass_le_best (qdUniform n) m (m o₀)
      rwa [qdGuessMass_uniform n m (m o₀), hfiber1, Nat.cast_one] at h
    refine le_antisymm ?_ hge
    refine qdBestGuessMass_le_of_forall (qdUniform n) m
      (show (0:ℝ) ≤ 1 / ((n * n : ℕ) : ℝ) by positivity) ?_
    intro g
    have hc1 : (Finset.univ.filter (fun k => m k = g)).card ≤ 1 :=
      Finset.card_le_one.mpr (by
        intro x hx y hy
        exact hinj ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
    rw [qdGuessMass_uniform n m g, div_le_div_iff₀ hn2pos hn2pos]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc1) hn2pos.le
  · intro hninj
    obtain ⟨a, b, hmeq, hne⟩ := Function.not_injective_iff.mp hninj
    have hsub : insert a (insert b (∅ : Finset (Fin n × Fin n))) ⊆
        Finset.univ.filter (fun k => m k = m a) := by
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · simp
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmeq.symm⟩
      · exact absurd hx (by simp)
    have hc2 : (insert a (insert b (∅ : Finset (Fin n × Fin n)))).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]),
        Finset.card_insert_of_notMem (by simp), Finset.card_empty]
    have h2 : (2:ℕ) ≤ (Finset.univ.filter (fun k => m k = m a)).card := by
      calc (2:ℕ) = (insert a (insert b (∅ : Finset (Fin n × Fin n)))).card := hc2.symm
        _ ≤ (Finset.univ.filter (fun k => m k = m a)).card := Finset.card_le_card hsub
    refine ⟨?_, hbest_le_one⟩
    have hge := qdGuessMass_le_best (qdUniform n) m (m a)
    rw [qdGuessMass_uniform n m (m a)] at hge
    calc 2 / ((n * n : ℕ) : ℝ)
        ≤ ((Finset.univ.filter (fun k => m k = m a)).card : ℕ) / ((n * n : ℕ) : ℝ) := by
          rw [div_le_div_iff₀ hn2pos hn2pos]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hn2pos.le
      _ ≤ qdBestGuessMass (qdUniform n) m := hge
  · rintro ⟨c, hc⟩
    have hfil : Finset.univ.filter (fun k => m k = c) = (Finset.univ : Finset (Fin n × Fin n)) :=
      Finset.filter_eq_self.mpr (fun k _ => hc k)
    have hcn : (Finset.univ.filter (fun k => m k = c)).card = n * n := by
      rw [hfil, huniv]
    have hge : (1:ℝ) ≤ qdBestGuessMass (qdUniform n) m := by
      have h := qdGuessMass_le_best (qdUniform n) m c
      rw [qdGuessMass_uniform n m c, hcn, div_self hn2ne] at h
      exact h
    exact le_antisymm hbest_le_one hge
  · intro g
    rw [qdDecodeMass_uniform n m g, div_le_div_iff₀ hn2pos hn2pos]
    have hinj : Function.Injective
        (fun k : {k : Fin n × Fin n // k ∈ Finset.univ.filter (fun k => g (m k) = k)} =>
          (⟨m k, ⟨k, rfl⟩⟩ : Set.range m)) := by
      intro a b hab
      have ha : g (m a) = a := (Finset.mem_filter.mp a.2).2
      have hb : g (m b) = b := (Finset.mem_filter.mp b.2).2
      have hm : m a = m b := congrArg Subtype.val hab
      exact Subtype.ext (ha.symm.trans (hm ▸ hb))
    have hle : (Finset.univ.filter (fun k => g (m k) = k)).card ≤
        Fintype.card (Set.range m) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_le_of_injective _ hinj
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hn2pos.le

/-- The standard qudit protocol has corrected branch weight `1 / n²`, identity total output, and
injective decodable messages of length `2 * Nat.clog 2 n` [BennettEtAl1993Teleportation]. -/
theorem clause4_clause6 : ∀ (n : ℕ) (h : NeZero n),
    (∀ (rho : Operator n) (o : Fin n × Fin n),
      @quditActualBranchCore n h o rho = (1 / (n : ℂ) ^ 2) • rho) ∧
    (∀ rho : Operator n, (@quditCorrectedInstrument n h).forget.map rho = rho) ∧
    (∀ o : Fin n × Fin n,
      (quditMessage n (Nat.clog 2 n) o).length = 2 * Nat.clog 2 n ∧
        quditDecodeMessage n (Nat.clog 2 n) (quditMessage n (Nat.clog 2 n) o)
          = some o) ∧
    Function.Injective (quditMessage n (Nat.clog 2 n)) ∧
    n ≤ 2 ^ Nat.clog 2 n := by
  intro n h
  haveI h' := h
  obtain ⟨hmsg, hinj, _, hle⟩ :=
    qudit_actual_fixed_width_message n (Nat.clog 2 n) (Nat.le_pow_clog (by decide) n)
  refine ⟨fun rho o => quditActualBranchCore_uniform n o rho, ?_, hmsg, hinj, hle⟩
  intro rho
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply]
  simp only [quditCorrectedInstrument_branch, ← Finset.sum_smul,
    qudit_uniform_scalar_sum, one_smul]

/-- The qudit resource marginal converse, maximal-entanglement characterization, resource
sufficiency, pure-resource form, and redundant-coding reliability contracts all hold. -/
theorem clause4_clause7 : (QuditResourceMarginalConverse ∧ QuditMaxEntCharacterization ∧
    QuditMaxEntResourceTeleportation ∧ QuditPureResourceMaxEntForm ∧
    RedundantCodingReliability) :=
  ⟨quditResourceMarginalConverse, quditMaxEntCharacterization,
    quditMaxEntResourceTeleportation, quditPureResourceMaxEntForm,
    redundantCodingReliability⟩
open Matrix

/-- The sum of the powers `2 ^ i` for `i < n` is `2 ^ n - 1`. -/
theorem sum_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.pow_succ]
    rcases n with _ | n
    · simp
    · have h1 : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
      omega

/-- A finite set contains at most `2 ^ m` Boolean lists of length `m`. -/
private theorem boolListLen_card_le (m : ℕ) (s : Finset (List Bool)) :
    (s.filter (fun l => l.length = m)).card ≤ 2 ^ m := by
  have hlen : ∀ l ∈ s.filter (fun l => l.length = m), l.length = m :=
    fun l hl => (Finset.mem_filter.mp hl).2
  let f : {x : List Bool // x ∈ s.filter (fun l => l.length = m)} → (Fin m → Bool) :=
    fun l i => l.val.get ⟨i, by rw [hlen l.val l.property]; exact i.2⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    refine List.ext_get ?_ ?_
    · rw [hlen a.1 a.2, hlen b.1 b.2]
    · intro n h1 h2
      have hf := congrFun h ⟨n, by rw [← hlen a.1 a.2]; exact h1⟩
      simpa [f] using hf
  have h1 := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe] at h1
  have h2 : Fintype.card (Fin m → Bool) = 2 ^ m := by
    rw [Fintype.card_pi]
    simp [Finset.prod_const, Fintype.card_bool]
  rw [h2] at h1
  exact h1

/-- A finite set of Boolean lists whose lengths are at most `c` has cardinality at most `2 ^ (c
+ 1)`. -/
theorem boolLists_card_le (c : ℕ) (s : Finset (List Bool)) (hall : ∀ l ∈ s, l.length ≤ c) :
    s.card ≤ 2 ^ (c + 1) := by
  have heq : s = (Finset.range (c + 1)).biUnion
      (fun m => s.filter (fun l => l.length = m)) := by
    ext l
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hl
      exact ⟨l.length, ⟨Nat.lt_succ_of_le (hall l hl), hl, rfl⟩⟩
    · rintro ⟨m, _, hl, _⟩
      exact hl
  have hdisj : Set.PairwiseDisjoint (Finset.range (c + 1) : Set ℕ)
      (fun m => s.filter (fun l => l.length = m)) := by
    intro m hm n hn hmn
    show Disjoint (s.filter (fun l => l.length = m)) (s.filter (fun l => l.length = n))
    rw [Finset.disjoint_left]
    intro x hx hnx
    simp only [Finset.mem_filter] at hx hnx
    exact hmn (hx.2.symm.trans hnx.2)
  rw [heq, Finset.card_biUnion hdisj]
  have hsum : ∑ m ∈ Finset.range (c + 1),
      (s.filter (fun l => l.length = m)).card ≤ ∑ m ∈ Finset.range (c + 1), 2 ^ m :=
    Finset.sum_le_sum (fun m _ => boolListLen_card_le m s)
  have hgeo : ∑ m ∈ Finset.range (c + 1), 2 ^ m = 2 ^ (c + 1) - 1 := sum_two_pow _
  have hpow : 0 < 2 ^ (c + 1) := Nat.two_pow_pos _
  omega

/-- If a protocol's message encoding is injective, its number of outcomes is at most `2 ^
(qdCommCost P + 1)`. -/
theorem qdCommCost_card_le {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (hinj : Function.Injective P.msgCode) :
    Fintype.card κ ≤ 2 ^ (qdCommCost P + 1) := by
  have hcard : Fintype.card κ = (Finset.univ.image P.msgCode).card := by
    rw [Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ]
  have hall : ∀ l ∈ Finset.univ.image P.msgCode, l.length ≤ qdCommCost P := by
    intro l hl
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact qdMsgCodeLength_le P k
  rw [hcard]
  exact boolLists_card_le (qdCommCost P) _ hall

/-- An injective message encoding and at least `n²` outcomes imply `n² ≤ 2 ^ (qdCommCost P +
1)`. -/
theorem qdCommCost_of_card {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (hcard : n * n ≤ Fintype.card κ) (hinj : Function.Injective P.msgCode) :
    n * n ≤ 2 ^ (qdCommCost P + 1) :=
  Nat.le_trans hcard (qdCommCost_card_le P hinj)
end Qatlib.Concepts.QuditTeleport.QdLoccModel
