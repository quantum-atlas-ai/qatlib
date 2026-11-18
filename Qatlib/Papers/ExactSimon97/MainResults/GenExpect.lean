/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommHSP98.MainResults.AbelianGen
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators Classical

/-!
# Section 2 of [BrassardHoyer1997]: expected number of uniform subgroup samples

The source observes that independent uniform samples of a finite group `H` generate `H`
after at most `2 log₂ |H|` samples in expectation, for two reasons: a proper generated
subgroup is escaped by the next sample with probability at least one half, and a strict
subgroup chain in `H` has length at most `log₂ |H|`.

This module formalizes, for finite Abelian `H` (the setting of the exact Simon
algorithm, where strong Fourier sampling supplies independent uniform annihilator
labels):

* `growthProbHalf`, `card_double_of_lt`, `stallProb_le_half`: a proper subgroup holds
  at most half of the elements, so the next uniform sample stays inside with
  probability at most `1/2` (reason one, in cardinality and single-sample form).
* `chain_card_ge`, `chain_le_log`: each strict inclusion doubles the cardinality, so a
  strictly increasing chain of `t+1` subgroups inside `H` forces `t ≤ log₂ |H|`
  (reason two).
* `failProb_le`: the generation-failure probability of `k` samples is at most
  `(|H| − 1) · (1/2)^k`.
* `expectedPartial_le`: the truncated tail sum of failure probabilities is at most
  `⌈log₂|H|⌉ + (|H| − 1)·(1/2)^(⌈log₂|H|⌉ − 1)`; by the tail-sum formula this bounds
  the expected number of samples `E[T] = Σ_{k≥0} P(T > k)`.
* `expectedSmall_le`, `expected_le_two_log`: the bound is at most `2·log₂|H|` for
  every `|H| ≥ 2`, the constant stated in the source.
-/

namespace Qatlib.Papers.ExactSimon97.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Papers.NoncommHSP98.MainResults

variable {G : Type} [AddCommGroup G] [Fintype G]

section ReasonOne

/-- Reason one, cardinality form: a proper subgroup of a finite Abelian group contains
at most half of the elements, so a uniform sample escapes it with probability at least
one half. -/
theorem growthProbHalf (K : AddSubgroup G) (hK : K < ⊤) :
    2 * Fintype.card ↥K ≤ Fintype.card G :=
  asp_proper_subgroup_card_half K hK

/-- A proper subgroup `K < M` has at most half the cardinality of `M`, so each strict
inclusion in a subgroup chain doubles the cardinality. -/
theorem card_double_of_lt {K M : AddSubgroup G} (h : K < M) :
    2 * Fintype.card ↥K ≤ Fintype.card ↥M := by
  have hne : K.addSubgroupOf M ≠ ⊤ := fun heq =>
    h.2 (AddSubgroup.addSubgroupOf_eq_top.mp heq)
  have hcard := asp_proper_subgroup_card_half (K.addSubgroupOf M)
    (lt_of_le_of_ne le_top hne)
  have hcardK : Fintype.card ↥(K.addSubgroupOf M) = Fintype.card ↥K :=
    Fintype.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h.le).toEquiv
  rwa [hcardK] at hcard

end ReasonOne

section ReasonTwo

/-- A strictly increasing initial segment of subgroups reaches cardinality at least
`2^t` after `t` strict inclusions, because each inclusion doubles the order. -/
theorem chain_card_ge (K : ℕ → AddSubgroup G) (t : ℕ)
    (hmono : ∀ s, s < t → K s < K (s + 1)) :
    2 ^ t ≤ Fintype.card ↥(K t) := by
  induction t with
  | zero =>
    have hpos : 0 < Fintype.card ↥(K 0) :=
      Fintype.card_pos_iff.mpr ⟨⟨0, AddSubgroup.zero_mem _⟩⟩
    omega
  | succ t ih =>
    have hd := card_double_of_lt (hmono t (by omega))
    have ih2 := ih (fun s hs => hmono s (by omega))
    calc 2 ^ (t + 1) = 2 ^ t * 2 := pow_succ _ _
      _ ≤ Fintype.card ↥(K t) * 2 := Nat.mul_le_mul_right _ ih2
      _ = 2 * Fintype.card ↥(K t) := mul_comm _ _
      _ ≤ Fintype.card ↥(K (t + 1)) := hd

/-- Reason two: a strictly increasing chain of `t+1` distinct subgroups inside `H`
forces `t ≤ log₂ |H|`, since `2^t ≤ |K t| ≤ |H|`. -/
theorem chain_le_log (K : ℕ → AddSubgroup G) (t : ℕ)
    (hmono : ∀ s, s < t → K s < K (s + 1))
    (H' : AddSubgroup G) (hKH : ∀ s, s ≤ t → K s ≤ H') :
    t ≤ Nat.log 2 (Fintype.card ↥H') := by
  have h1 : 2 ^ t ≤ Fintype.card ↥(K t) := chain_card_ge K t hmono
  have h2 : Fintype.card ↥(K t) ≤ Fintype.card ↥H' :=
    Fintype.card_le_of_injective
      (fun (x : ↥(K t)) => (⟨(x : G), hKH t (le_refl t) x.2⟩ : ↥H'))
      (fun a b hab => Subtype.ext (congrArg (fun y : ↥H' => (y : G)) hab))
  have hpos : 0 < Fintype.card ↥H' :=
    Fintype.card_pos_iff.mpr ⟨⟨0, AddSubgroup.zero_mem _⟩⟩
  exact Nat.le_log_iff_pow_le (by decide : 1 < 2) (Nat.ne_of_gt hpos) |>.mpr
    (le_trans h1 h2)

end ReasonTwo

section SingleSample

variable [DecidableEq G]

/-- The probability that one uniform sample of `H` stays inside a proper subgroup `K`
is exactly the normalized cardinality `|K|/|H|`, which is at most `1/2`. -/
theorem stallProb_le_half (H K : AddSubgroup G) (hKH : K ≤ H) (hK : K < H) :
    FinDist.probEvent (L := 1) (unifOnSub H) (fun ω => (ω 0 : G) ∈ K) ≤ 1 / 2 := by
  classical
  have h0 : 0 < Fintype.card ↥H :=
    Fintype.card_pos_iff.mpr ⟨⟨0, AddSubgroup.zero_mem _⟩⟩
  have hpos : (0 : ℝ) < (Fintype.card ↥H : ℝ) := by exact_mod_cast h0
  have hcard : (Finset.univ.filter (fun g => g ∈ K) : Finset G).card =
      Fintype.card ↥K := by
    have himg : (Finset.univ.filter (fun g => g ∈ K) : Finset G) =
        (Finset.univ.image (Subtype.val : ↥K → G)) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hg
        exact ⟨⟨g, hg⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact x.2
    rw [himg, Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
  have hterm : ∀ g ∈ (Finset.univ.filter (fun g => g ∈ K) : Finset G),
      (unifOnSub H).prob g = 1 / (Fintype.card ↥H : ℝ) := by
    intro g hg
    simp [unifOnSub, hKH ((Finset.mem_filter.mp hg).2)]
  have hprod : ∀ ω : Fin 1 → G, (unifOnSub H).probOf (L := 1) ω =
      (unifOnSub H).prob (ω 0) := by
    intro ω
    unfold FinDist.probOf
    simp
  unfold FinDist.probEvent
  rw [Finset.sum_congr rfl (fun ω _ => hprod ω)]
  have hmap : (∑ ω ∈ Finset.univ.filter (fun ω : Fin 1 → G => (ω 0 : G) ∈ K),
        (unifOnSub H).prob (ω 0)) =
      ∑ g ∈ (Finset.univ.filter (fun g => g ∈ K) : Finset G),
        (unifOnSub H).prob g := by
    have himg : (Finset.univ.filter (fun g => g ∈ K) : Finset G) =
        (Finset.univ.filter (fun ω : Fin 1 → G => (ω 0 : G) ∈ K)).image
          (fun ω => (ω 0 : G)) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hg
        exact ⟨fun _ => g, by simpa using hg, rfl⟩
      · rintro ⟨ω, hω, rfl⟩
        exact hω
    have hinj : Set.InjOn (fun ω : Fin 1 → G => (ω 0 : G))
        (Finset.univ.filter (fun ω : Fin 1 → G => (ω 0 : G) ∈ K)) := by
      intro a _ b _ hab
      funext i
      fin_cases i
      exact hab
    rw [himg, Finset.sum_image hinj]
  rw [hmap, Finset.sum_congr rfl hterm, sum_one_div, hcard, div_le_iff₀ hpos]
  have hcast : (2 : ℝ) * (Fintype.card ↥K : ℝ) ≤ (Fintype.card ↥H : ℝ) := by
    exact_mod_cast card_double_of_lt hK
  linarith

end SingleSample

section TailSum

variable [DecidableEq G]

/-- The generation-failure probability of `k` independent uniform samples of `H`. -/
noncomputable def failProbAt (H : AddSubgroup G) (k : ℕ) : ℝ :=
  FinDist.probEvent (L := k) (unifOnSub H)
    (fun hs => AddSubgroup.closure (Set.range hs) ≠ H)

omit [DecidableEq G] in
/-- Sample-record events have probability at most one. -/
theorem probEvent_le_one {X : Type*} [Fintype X] {L : ℕ} (p : FinDist X)
    (E : (Fin L → X) → Prop) [DecidablePred E] : p.probEvent E ≤ 1 := by
  classical
  have hnn : ∀ ω : Fin L → X, 0 ≤ p.probOf ω := fun ω =>
    Finset.prod_nonneg (fun i _ => p.nonneg _)
  have h1 : (∑ ω ∈ Finset.univ.filter E, p.probOf ω) ≤ (∑ ω : Fin L → X, p.probOf ω) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => hnn ω)
  unfold FinDist.probEvent
  rw [probOfTotal p] at h1
  exact h1

omit [DecidableEq G] in
/-- The partial geometric tail of one halves satisfies
`Σ_{j<d} (1/2)^(L+j) ≤ (1/2)^(L-1)` for `L ≥ 1`. -/
theorem geomTail_le : ∀ (d L : ℕ), 1 ≤ L →
    ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (L + j) ≤ (1 / 2 : ℝ) ^ (L - 1) := by
  intro d
  induction d with
  | zero => intro L _; simp
  | succ d ih =>
    intro L hL
    rw [Finset.sum_range_succ']
    have hshift : ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (L + (j + 1)) =
        ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ ((L + 1) + j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      congr 1
      omega
    have ih2 := ih (L + 1) (by omega)
    rw [hshift]
    rw [show L + 1 - 1 = L from by omega] at ih2
    have hcalc : (1 / 2 : ℝ) ^ L + (1 / 2 : ℝ) ^ L = (1 / 2 : ℝ) ^ (L - 1) := by
      have h2 : (1 / 2 : ℝ) ^ (L - 1) * (1 / 2) = (1 / 2 : ℝ) ^ L := by
        rw [← pow_succ, show L - 1 + 1 = L from by omega]
      have hposL1 : (0 : ℝ) < (1 / 2 : ℝ) ^ (L - 1) := pow_pos (by norm_num) _
      nlinarith [h2, hposL1]
    simp only [Nat.add_zero]
    linarith

omit [DecidableEq G] in
/-- If `2^t ≤ c` then `log₂ c ≥ t`. -/
theorem log2_ge_of_pow_le {c t : ℕ} (h : 2 ^ t ≤ c) : (t : ℝ) ≤ Real.logb 2 (c : ℝ) := by
  have hmono : Real.logb 2 ((2 : ℝ) ^ t) ≤ Real.logb 2 (c : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (by exact_mod_cast h)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hmono
  exact hmono

omit [DecidableEq G] in
/-- If `2^r ≤ c^q` with `q ≠ 0` then `log₂ c ≥ r/q`; integer-power comparison form for
rational lower bounds on `log₂ c`. -/
theorem log2_lower_pow {c q r : ℕ} (hq : q ≠ 0) (h : 2 ^ r ≤ c ^ q) :
    (r : ℝ) / (q : ℝ) ≤ Real.logb 2 (c : ℝ) := by
  have h1 : (r : ℝ) ≤ Real.logb 2 ((c ^ q : ℕ) : ℝ) := log2_ge_of_pow_le h
  have h2 : Real.logb 2 ((c ^ q : ℕ) : ℝ) = Real.logb 2 ((c : ℝ) ^ (q : ℕ)) := by
    push_cast
    rfl
  rw [h2, Real.logb_pow] at h1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hq)
  have hcancel : (r : ℝ) / (q : ℝ) * (q : ℝ) = (r : ℝ) := by field_simp
  rcases lt_or_ge (Real.logb 2 (c : ℝ)) ((r : ℝ) / (q : ℝ)) with hlt | hle
  · exfalso
    have hmul : Real.logb 2 (c : ℝ) * (q : ℝ) < (r : ℝ) / (q : ℝ) * (q : ℝ) :=
      mul_lt_mul_of_pos_right hlt hqpos
    rw [hcancel] at hmul
    linarith
  · exact hle

omit [DecidableEq G] in
/-- The ceiling of `log₂ c` for `c ≥ 2`, characterized by `2^(L-1) < c ≤ 2^L`. -/
def ceilLog2 (c : ℕ) : ℕ := Nat.log 2 (2 * c - 1)

omit [DecidableEq G] in
/-- Specification of the ceiling of `log₂ c` for `c ≥ 2`: the defining two-sided
power bound `2^(L-1) < c ≤ 2^L` and positivity of `L`. -/
theorem ceilLog2_specs {c : ℕ} (hc : 2 ≤ c) :
    2 ^ (ceilLog2 c - 1) < c ∧ c ≤ 2 ^ (ceilLog2 c) ∧ 1 ≤ ceilLog2 c := by
  have h1 : (2 : ℕ) ^ Nat.log 2 (2 * c - 1) ≤ 2 * c - 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 * c - 1 < (2 : ℕ) ^ (Nat.log 2 (2 * c - 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  have hLpos : 1 ≤ ceilLog2 c := by
    have h1 : (1 : ℕ) < 2 := by decide
    have h2 : (2 : ℕ) ≤ 2 * c - 1 := by omega
    exact Nat.log_pos_iff.mpr ⟨h2, h1⟩
  refine ⟨?_, ?_, hLpos⟩
  · have hexp : (2 : ℕ) ^ ceilLog2 c = (2 : ℕ) ^ (ceilLog2 c - 1) * 2 := by
      rw [← pow_succ, show ceilLog2 c - 1 + 1 = ceilLog2 c by omega]
    have h1' : (2 : ℕ) ^ (ceilLog2 c - 1) * 2 ≤ 2 * c - 1 := by rwa [← hexp]
    omega
  · have hexp2 : (2 : ℕ) ^ (ceilLog2 c + 1) = (2 : ℕ) ^ ceilLog2 c * 2 := pow_succ _ _
    have h2' : 2 * c - 1 < (2 : ℕ) ^ ceilLog2 c * 2 := by rwa [← hexp2]
    omega

/-- The generation-failure probability of `k` uniform samples is at most
`(|H| − 1)·(1/2)^k`, sharpening the strict bound of `genFail_lt` by one. -/
theorem failProb_le (H : AddSubgroup G) (k : ℕ) :
    failProbAt H k ≤ ((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hnear : ∀ L : Finset ↥H,
      |∑ g ∈ L, (unifOnSub H).prob (g : G) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ 0 := by
    intro L
    rw [unifOnSub_exact H L, sub_self, abs_zero]
  obtain ⟨maxs, -, -, hcount, hbound⟩ :=
    nearUniformGenerationSubgoal k G H (unifOnSub H) 0 (le_refl 0) hnear
  simp only [mul_zero, add_zero, zero_add] at hbound
  have hcast : (maxs.card : ℝ) ≤ ((Fintype.card ↥H - 1 : ℕ) : ℝ) := by
    have hle : maxs.card ≤ Fintype.card ↥H - 1 := by omega
    exact_mod_cast hle
  exact le_trans hbound (mul_le_mul_of_nonneg_right hcast (by positivity))

/-- The truncated tail sum of generation-failure probabilities is at most
`⌈log₂|H|⌉ + (|H|−1)·(1/2)^(⌈log₂|H|⌉ − 1)`; by the tail-sum formula this bounds the
expected number `E[T] = Σ_{k≥0} P(T > k)` of uniform samples needed to generate `H`. -/
theorem expectedPartial_le (H : AddSubgroup G)
    (hH : 2 ≤ Fintype.card ↥H) (K' : ℕ) :
    ∑ k ∈ Finset.range K', failProbAt H k ≤
      (ceilLog2 (Fintype.card ↥H) : ℝ) +
        ((Fintype.card ↥H : ℝ) - 1) * (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) := by
  classical
  obtain ⟨hlow, hhigh, hLpos⟩ := ceilLog2_specs hH
  have hsplit : Finset.range K' =
      (Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H))) ∪
        Finset.Ico (ceilLog2 (Fintype.card ↥H)) K' := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_inter]
    constructor
    · intro hk
      by_cases h : k < ceilLog2 (Fintype.card ↥H)
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨by omega, hk⟩
    · rintro (⟨hk, _⟩ | ⟨_, hk⟩)
      · exact hk
      · exact hk
  have hdisj : Disjoint (Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H)))
      (Finset.Ico (ceilLog2 (Fintype.card ↥H)) K') :=
    Finset.disjoint_iff_ne.mpr
      (fun a ha b hb => by
        simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_Ico] at ha hb
        omega)
  rw [hsplit, Finset.sum_union hdisj]
  have hsum1 : ∑ k ∈ Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H)),
      failProbAt H k ≤ (ceilLog2 (Fintype.card ↥H) : ℝ) := by
    calc ∑ k ∈ Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H)),
          failProbAt H k
        ≤ ∑ _k ∈ Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H)), (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => probEvent_le_one _ _)
      _ = ((Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H))).card : ℝ) := by
          rw [Finset.sum_const, Nat.smul_one_eq_cast]
      _ ≤ (ceilLog2 (Fintype.card ↥H) : ℝ) := by
          have hsub : (Finset.range K' ∩ Finset.range (ceilLog2 (Fintype.card ↥H))) ⊆
              Finset.range (ceilLog2 (Fintype.card ↥H)) := Finset.inter_subset_right
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_range] at hcard
          exact_mod_cast hcard
  have hnorm : ((Fintype.card ↥H - 1 : ℕ) : ℝ) =
      ((Fintype.card ↥H : ℝ) - 1) := by
    have h1 : (1 : ℕ) ≤ Fintype.card ↥H := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hsum2 : ∑ k ∈ Finset.Ico (ceilLog2 (Fintype.card ↥H)) K', failProbAt H k ≤
      ((Fintype.card ↥H : ℝ) - 1) * (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) := by
    have hle : ∀ k ∈ Finset.Ico (ceilLog2 (Fintype.card ↥H)) K',
        failProbAt H k ≤ ((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k :=
      fun k _ => failProb_le H k
    calc ∑ k ∈ Finset.Ico (ceilLog2 (Fintype.card ↥H)) K', failProbAt H k
        ≤ ∑ k ∈ Finset.Ico (ceilLog2 (Fintype.card ↥H)) K',
            ((Fintype.card ↥H - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k :=
          Finset.sum_le_sum hle
      _ = ((Fintype.card ↥H - 1 : ℕ) : ℝ) *
            ∑ k ∈ Finset.Ico (ceilLog2 (Fintype.card ↥H)) K', (1 / 2 : ℝ) ^ k :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ((Fintype.card ↥H - 1 : ℕ) : ℝ) *
            (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (Fintype.card ↥H - 1))
          rw [Finset.sum_Ico_eq_sum_range (f := fun k => (1 / 2 : ℝ) ^ k)
              (ceilLog2 (Fintype.card ↥H)) K']
          exact geomTail_le _ _ hLpos
      _ = ((Fintype.card ↥H : ℝ) - 1) * (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) := by
          rw [hnorm]
  linarith

/-- Small-cardinality arithmetic for the expectation bound: for `2 ≤ c ≤ 8` the
truncated tail-sum bound at `L = ceilLog2 c` is at most `2·log₂ c`, by exact
computation of the seven possible values. -/
theorem expectedSmall_le (c : ℕ) (hc2 : 2 ≤ c) (hc8 : c ≤ 8) :
    (ceilLog2 c : ℝ) + ((c : ℝ) - 1) * (1 / 2 : ℝ) ^ (ceilLog2 c - 1) ≤
      2 * Real.logb 2 (c : ℝ) := by
  interval_cases c
  · have hLv : ceilLog2 2 = 1 := by decide
    have hlog : Real.logb 2 ((2 : ℕ) : ℝ) = 1 :=
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)
    rw [hLv, hlog]
    norm_num
  · have hLv : ceilLog2 3 = 2 := by decide
    have hlog : ((3 : ℝ)) / ((2 : ℝ)) ≤ Real.logb 2 ((3 : ℕ) : ℝ) :=
      log2_lower_pow (by decide) (by decide : (2 : ℕ) ^ 3 ≤ (3 : ℕ) ^ 2)
    rw [hLv]
    norm_num
    linarith
  · have hLv : ceilLog2 4 = 2 := by decide
    have hlog : Real.logb 2 ((4 : ℕ) : ℝ) = 2 := by
      have h4 : ((4 : ℕ) : ℝ) = ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      rw [h4, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    rw [hLv, hlog]
    norm_num
  · have hLv : ceilLog2 5 = 3 := by decide
    have hlog : ((9 : ℝ)) / ((4 : ℝ)) ≤ Real.logb 2 ((5 : ℕ) : ℝ) :=
      log2_lower_pow (by decide) (by decide : (2 : ℕ) ^ 9 ≤ (5 : ℕ) ^ 4)
    rw [hLv]
    norm_num
    linarith
  · have hLv : ceilLog2 6 = 3 := by decide
    have hlog : ((9 : ℝ)) / ((4 : ℝ)) ≤ Real.logb 2 ((6 : ℕ) : ℝ) :=
      log2_lower_pow (by decide) (by decide : (2 : ℕ) ^ 9 ≤ (6 : ℕ) ^ 4)
    rw [hLv]
    norm_num
    linarith
  · have hLv : ceilLog2 7 = 3 := by decide
    have hlog : ((9 : ℝ)) / ((4 : ℝ)) ≤ Real.logb 2 ((7 : ℕ) : ℝ) :=
      log2_lower_pow (by decide) (by decide : (2 : ℕ) ^ 9 ≤ (7 : ℕ) ^ 4)
    rw [hLv]
    norm_num
    linarith
  · have hLv : ceilLog2 8 = 3 := by decide
    have hlog : Real.logb 2 ((8 : ℕ) : ℝ) = 3 := by
      have h8 : ((8 : ℕ) : ℝ) = ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
      rw [h8, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    rw [hLv, hlog]
    norm_num

/-- The expected number of uniform samples needed to generate `H` is at most
`2·log₂|H|` for every `|H| ≥ 2`: the truncated tail sums satisfy the bound uniformly
in the truncation `K'`. -/
theorem expected_le_two_log (H : AddSubgroup G)
    (hH : 2 ≤ Fintype.card ↥H) (K' : ℕ) :
    ∑ k ∈ Finset.range K', failProbAt H k ≤
      2 * Real.logb 2 (Fintype.card ↥H : ℝ) := by
  classical
  have hmain := expectedPartial_le H hH K'
  obtain ⟨hlow, hhigh, hLpos⟩ := ceilLog2_specs hH
  rcases Nat.lt_or_ge (Fintype.card ↥H) 9 with hsmall | hbig
  · have hsm := expectedSmall_le (Fintype.card ↥H) hH (by omega)
    exact le_trans hmain hsm
  · have hprod : ((Fintype.card ↥H : ℝ) - 1) *
        (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) ≤ 2 := by
      have h2Lm1pos : (0 : ℝ) < (2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) := by
        positivity
      have h2Lpos : (0 : ℝ) < (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) := by positivity
      have hpowL : (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) =
          (2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) * 2 := by
        rw [← mul_comm, ← pow_succ', show (ceilLog2 (Fintype.card ↥H) - 1) + 1
            = ceilLog2 (Fintype.card ↥H) by omega]
      have hkey : (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) *
          (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) = 2 := by
        rw [halfPowInv, hpowL, ← mul_assoc,
          inv_mul_cancel₀ h2Lm1pos.ne', one_mul]
      have hstep : ((Fintype.card ↥H : ℝ) - 1) *
          (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) *
          (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) =
          ((Fintype.card ↥H : ℝ) - 1) * 2 := by rw [mul_assoc, hkey]
      have hclt : (Fintype.card ↥H : ℝ) ≤
          (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) := by exact_mod_cast hhigh
      have hbound : ((Fintype.card ↥H : ℝ) - 1) *
          (1 / 2 : ℝ) ^ (ceilLog2 (Fintype.card ↥H) - 1) *
          (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) ≤
          2 * (2 : ℝ) ^ ceilLog2 (Fintype.card ↥H) := by
        rw [hstep]
        linarith
      exact le_of_mul_le_mul_right hbound h2Lpos
    have hlogb : ((ceilLog2 (Fintype.card ↥H) : ℕ) : ℝ) - 1 ≤
        Real.logb 2 (Fintype.card ↥H : ℝ) := by
      have hle : (2 : ℕ) ^ (ceilLog2 (Fintype.card ↥H) - 1) ≤ Fintype.card ↥H :=
        Nat.le_of_lt hlow
      have h1 := log2_ge_of_pow_le hle
      have h2 : ((ceilLog2 (Fintype.card ↥H) - 1 : ℕ) : ℝ) =
          ((ceilLog2 (Fintype.card ↥H) : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hLpos, Nat.cast_one]
      rw [h2] at h1
      exact h1
    have hlogb3 : (3 : ℝ) ≤ Real.logb 2 (Fintype.card ↥H : ℝ) :=
      log2_ge_of_pow_le (by omega : (2 : ℕ) ^ 3 ≤ Fintype.card ↥H)
    have hLcast : ((ceilLog2 (Fintype.card ↥H) : ℕ) : ℝ) =
        ((ceilLog2 (Fintype.card ↥H) : ℕ) : ℝ) - 1 + 1 := by ring
    linarith

end TailSum

end Qatlib.Papers.ExactSimon97.MainResults
