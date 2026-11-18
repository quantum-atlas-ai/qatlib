/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
public import Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The general uniform informative-query bound (Section III, first slice)

Fixed source quant-ph/9706062v2, Section III (the classical algorithm
attributed to M. Sipser in the paragraph beginning "We can think of decision
trees as associated with functions that impose constraints").  The source
recognizes the hidden word by *trials*: it queries words whose already
identified prefix agrees with the hidden word until the level predicate
returns the informative answer, which certifies the next hidden bit ("First
try various inputs until you find an example `x_1…x_{n-1}` such that `f_{n-1}`
is 1 on this input.  Then you know that `w_1 = x_1`", and onwards from each
known prefix).  This module proves the general uniform success bound behind
those trials for the whole family at once — every word length, every stage,
every hidden word — together with the information-theoretic depth floor that
any such classical tree must pay on the uniform candidate family:

* `IsUniformQueryStage`: the general uniform informative-query predicate — a
  finite query space with a Boolean answer function, a marker answer and a
  decoded bit, such that every marker answer certifies the decoded bit and at
  least a quarter of the uniform query space returns the marker;
* `cylinderCard`: the two-coordinate cylinder counting lemma, the general
  engine isolated from the level predicate: any event containing the
  two-bit forcing cylinder carries at least a quarter of the uniform mass;
* `prefixFixedCard`, `informQuarterTwo`, `informQuarter`, `informQuarterRat`:
  the uniform success mass of a level-predicate stage — at least one quarter
  of the correct-prefix queries are informative, for every stage with at
  least two free positions;
* `levelPredStage`: the level-predicate stage satisfies
  `IsUniformQueryStage`;
* `uniformDepthGe`, `uniformCostGe`: on the uniform hidden-word family, any
  classical adaptive tree with Boolean answers that exactly recovers every
  word of length `n` — for any oracle and any query addressing — has
  worst-case depth (resp. per-input actual query count) at least `n`.

Boundaries (deliberately not covered here): the global adaptive recovery
process (the stage-by-stage state machine with its random-trial stopping);
the expected-query budget such as `≤ 4(n-1) + 2`; the endpoint stages with
fewer than two free positions, which belong to the two-evaluation decision
of `Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred.twoEval_iff`; and any equivalence between the staged evaluation
and the full-word predicate.  The depth and cost bounds are counting floors
for an arbitrary one-bit oracle, not the source's upper-bound algorithm, and
nothing here claims the source's global classical algorithm as closed.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.DecisionTrees97.UniformQueryBound

open Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred
open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

/-! ### The general uniform informative-query predicate -/

/-- The general uniform informative-query predicate: `f` is a Boolean answer
function on a finite query space `Ω`, `marker` is the informative answer, and
`guess q` is the bit the algorithm reads off a query `q` when trying to learn
`target`.  The stage is uniformly informative when every marker answer
certifies the decoded bit, and at least a quarter of the uniform query space
returns the marker — the two facts the source's trial-based recovery needs at
every stage.  Nothing in the predicate mentions level predicates, word
lengths or a specific instance. -/
structure IsUniformQueryStage {Ω : Type} [Fintype Ω] (f : Ω → Bool)
    (marker : Bool) (guess : Ω → Bool) (target : Bool) : Prop where
  /-- Soundness of the marker: an informative answer certifies the decoded
  bit. -/
  certifies : ∀ q : Ω, f q = marker → guess q = target
  /-- Uniform success mass: at least a quarter of the uniform query space
  returns the marker answer. -/
  quarter : Fintype.card Ω ≤ 4 * (Finset.univ.filter fun q => f q = marker).card

/-! ### The two-coordinate cylinder counting engine -/

/-- Prefixing two fixed bits is injective on free tails: the double tail is
a left inverse. -/
theorem consCons_injective {n : ℕ} (c d : Bool) :
    Function.Injective
      (fun u : Fin n → Bool => Fin.cons c (Fin.cons d u) :
        (Fin n → Bool) → (Fin (n + 2) → Bool)) := by
  have hinv : Function.LeftInverse
      (fun t : Fin (n + 2) → Bool => Fin.tail (Fin.tail t))
      (fun u : Fin n → Bool => Fin.cons c (Fin.cons d u) :
        (Fin n → Bool) → (Fin (n + 2) → Bool)) := by
    intro u
    simp
  exact hinv.injective

/-- The two-coordinate cylinder in the free-tail space — tails whose first
two bits take prescribed values — carries exactly a quarter of the uniform
mass of `Fin (n + 2) → Bool`.  This is the general counting engine behind the
uniform informative-query bound: any event that contains such a cylinder
holds on at least a quarter of the uniform tail space. -/
theorem cylinderCard (n : ℕ) (c d : Bool) :
    (Finset.univ.filter fun t : Fin (n + 2) → Bool =>
        t 0 = c ∧ t 1 = d).card = 2 ^ n := by
  have himg : (Finset.univ.filter fun t : Fin (n + 2) → Bool =>
        t 0 = c ∧ t 1 = d) =
      Finset.univ.image
        (fun u : Fin n → Bool => Fin.cons c (Fin.cons d u) :
          (Fin n → Bool) → (Fin (n + 2) → Bool)) := by
    refine Finset.ext fun t => ?_
    constructor
    · intro h
      obtain ⟨_, ht0, ht1⟩ := Finset.mem_filter.mp h
      refine Finset.mem_image.2 ⟨Fin.tail (Fin.tail t), Finset.mem_univ _, ?_⟩
      have h0 := Fin.cons_self_tail t
      have h0' := Fin.cons_self_tail (Fin.tail t)
      have hA : Fin.cons (t 1) (Fin.tail (Fin.tail t)) = Fin.tail t := by
        have e : (Fin.tail t) 0 = t 1 :=
          (Fin.cons_one (t 0) (Fin.tail t)).symm.trans (congrFun h0 1)
        rw [← e]
        exact h0'
      calc Fin.cons c (Fin.cons d (Fin.tail (Fin.tail t)))
          = Fin.cons (t 0) (Fin.cons (t 1) (Fin.tail (Fin.tail t))) := by
            rw [ht0, ht1]
        _ = Fin.cons (t 0) (Fin.tail t) := by rw [hA]
        _ = t := h0
    · intro h
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
      · simp only [Fin.cons_zero]
      · simp only [Fin.cons_one, Fin.cons_zero]
  rw [himg, Finset.card_image_of_injOn
    (fun a _ b _ h => consCons_injective c d h), Finset.card_univ]
  simp

/-! ### The uniform success mass of a level-predicate stage -/

/-- The correct-prefix query space has exactly `2 ^ r` elements: the prefix
extension map bijects the free-tail space with it. -/
theorem prefixFixedCard (k r : ℕ) (w : Fin (k + r) → Bool) :
    (prefixFixed k r w).card = 2 ^ r := by
  have himg : prefixFixed k r w = Finset.univ.image (extend k r w) := by
    refine Finset.ext fun x => ?_
    rw [mem_prefixFixed]
    constructor
    · intro hagree
      exact Finset.mem_image.2 ⟨suf k r x, Finset.mem_univ _,
        extend_suf k r w x hagree⟩
    · intro h
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h
      exact mem_prefixFixed.mp (extend_mem k r w t)
  rw [himg, Finset.card_image_of_injOn (fun a _ b _ h => extend_inj k r w h),
    Finset.card_univ]
  simp

/-- The uniform success mass of a level-predicate stage with `n + 2` free
positions: at least a quarter of the correct-prefix queries return the
informative answer.  The bound is uniform over the whole family — every word
length, every stage `k` and every hidden word `w` — and generalizes the
concrete two-level forcing event `lvlAuxF_force`, which supplies the forcing
cylinder inside the informative set. -/
theorem informQuarterTwo (k n : ℕ) (w : Fin (k + (n + 2)) → Bool) :
    (prefixFixed k (n + 2) w).card ≤ 4 * (informativeSet k (n + 2) w).card := by
  obtain ⟨c, hc⟩ : ∃ c : Bool, c = w ⟨k, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Bool, d = !(w ⟨k + 1, by omega⟩) := ⟨_, rfl⟩
  have hne : ∀ b : Bool, b ≠ !b := by decide
  have hxk : ∀ t : Fin (n + 2) → Bool,
      (extend k (n + 2) w t) ⟨k, by omega⟩ = t 0 := by
    intro t
    have h := congrFun (suf_of_extend k (n + 2) w t) 0
    simpa [suf] using h
  have hxk1 : ∀ t : Fin (n + 2) → Bool,
      (extend k (n + 2) w t) ⟨k + 1, by omega⟩ = t 1 := by
    intro t
    have h := congrFun (suf_of_extend k (n + 2) w t) 1
    simpa [suf] using h
  have hmem : ∀ u : Fin n → Bool,
      extend k (n + 2) w (Fin.cons c (Fin.cons d u))
        ∈ informativeSet k (n + 2) w := by
    intro u
    simp only [informativeSet, Finset.mem_filter]
    refine ⟨extend_mem k (n + 2) w _, ?_⟩
    refine lvlAuxF_force k n (flagAt k) w _ ?_ ?_
    · rw [hxk]
      simp only [Fin.cons_zero]
      exact hc.symm
    · rw [hxk1]
      simp only [Fin.cons_one, Fin.cons_zero]
      rw [hd]
      exact hne _
  have himg : (Finset.univ.image
      fun u : Fin n → Bool => extend k (n + 2) w (Fin.cons c (Fin.cons d u))) ⊆
      informativeSet k (n + 2) w := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmem u
  have hcard : 2 ^ n ≤ (informativeSet k (n + 2) w).card := by
    refine le_trans ?_ (Finset.card_le_card himg)
    rw [Finset.card_image_of_injOn
      (f := fun u : Fin n → Bool => extend k (n + 2) w (Fin.cons c (Fin.cons d u)))
      (s := (Finset.univ : Finset (Fin n → Bool)))
      (fun a _ b _ h => consCons_injective c d (extend_inj k (n + 2) w h)),
      Finset.card_univ]
    simp
  rw [prefixFixedCard]
  have hpow : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add, Nat.pow_two]; ring
  rw [hpow]
  exact Nat.mul_le_mul_left 4 hcard

/-- The uniform success bound for a stage with `r` remaining positions,
`2 ≤ r`: at least a quarter of the correct-prefix queries are informative.
Two free positions are exactly what the two-level forcing event needs; the
final single-bit endpoint is the two-evaluation decision of
`Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred.twoEval_iff`, not this bound. -/
theorem informQuarter (k r : ℕ) (hr : 2 ≤ r) (w : Fin (k + r) → Bool) :
    (prefixFixed k r w).card ≤ 4 * (informativeSet k r w).card := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n + 2 := ⟨r - 2, by omega⟩
  exact informQuarterTwo k n w

/-- Fraction form of the uniform success bound: under the uniform measure on
the correct-prefix query space, an answer is informative with probability at
least `1/4`. -/
theorem informQuarterRat (k r : ℕ) (hr : 2 ≤ r) (w : Fin (k + r) → Bool) :
    (1 / 4 : ℚ) ≤ (informativeSet k r w).card / (prefixFixed k r w).card := by
  have h := informQuarter k r hr w
  have hpos : (0 : ℚ) < (prefixFixed k r w).card := by
    rw [prefixFixedCard]
    positivity
  rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 4) hpos]
  have h' : ((prefixFixed k r w).card : ℚ)
      ≤ 4 * (informativeSet k r w).card := by exact_mod_cast h
  norm_num
  linarith

/-- The level-predicate stage of the source's trial algorithm satisfies the
general uniform informative-query predicate: the query space is the set of
correct-prefix words, the answer is the level predicate evaluated from the
known prefix, the marker is the parity-flipped flag, and the decoded bit is
the queried word's bit at the next unknown position, identified via
`identBit`. -/
theorem levelPredStage (k n : ℕ) (w : Fin (k + (n + 2)) → Bool) :
    IsUniformQueryStage
      (fun q : {x : Fin (k + (n + 2)) → Bool // x ∈ prefixFixed k (n + 2) w} =>
        lvlAuxF (flagAt k) (suf k (n + 2) w) (suf k (n + 2) q.1))
      (!(flagAt k))
      (fun q => q.1 ⟨k, by omega⟩)
      (w ⟨k, by omega⟩) := by
  constructor
  · intro q h
    exact (identBit k (n + 1) (flagAt k) w q.1 h).symm
  · have himg : (Finset.univ.filter
        (fun q : {x : Fin (k + (n + 2)) → Bool // x ∈ prefixFixed k (n + 2) w} =>
          lvlAuxF (flagAt k) (suf k (n + 2) w) (suf k (n + 2) q.1)
            = !(flagAt k))).image
        Subtype.val = informativeSet k (n + 2) w := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        informativeSet]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.2, hq⟩
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    have hc : (Finset.univ.filter
        (fun q : {x : Fin (k + (n + 2)) → Bool // x ∈ prefixFixed k (n + 2) w} =>
          lvlAuxF (flagAt k) (suf k (n + 2) w) (suf k (n + 2) q.1)
            = !(flagAt k))).card
        = (informativeSet k (n + 2) w).card := by
      calc (Finset.univ.filter _).card
          = ((Finset.univ.filter _).image Subtype.val).card := by
            rw [Finset.card_image_of_injOn
              (f := (Subtype.val : {x : Fin (k + (n + 2)) → Bool //
                  x ∈ prefixFixed k (n + 2) w} → (Fin (k + (n + 2)) → Bool)))
              (fun a _ b _ h => Subtype.ext h)]
        _ = (informativeSet k (n + 2) w).card := by rw [himg]
    rw [hc, Fintype.card_coe]
    exact informQuarterTwo k n w

/-! ### Depth floors on the uniform hidden-word family -/

/-- Information-theoretic depth floor on the uniform hidden-word family: any
classical adaptive tree with Boolean answers that exactly recovers every
hidden word of length `n` — for any oracle and any query addressing — has
worst-case query depth at least `n`.  This is the general lower-bound
instance for the uniform family, a counting floor complementary to the
source's trial algorithm; it is not the source's upper-bound algorithm and
involves no random-walk dynamics. -/
theorem uniformDepthGe (n : ℕ) {I : Type} (oracle : (Fin n → Bool) → I → Bool)
    (tree : QueryTree I Bool (Fin n → Bool))
    (hcorrect : ∀ w, (run (oracle w) tree).1 = w) :
    n ≤ depth tree := by
  have h := exact_recovery_card oracle tree hcorrect
  have hc : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  rw [hc] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-- Actual-count form of the same floor: if every hidden word of length `n`
is recovered exactly using at most `M` actual queries, then `n ≤ M`. -/
theorem uniformCostGe (n : ℕ) {I : Type} (oracle : (Fin n → Bool) → I → Bool)
    (tree : QueryTree I Bool (Fin n → Bool)) (M : ℕ)
    (hcorrect : ∀ w, (run (oracle w) tree).1 = w)
    (hcost : ∀ w, (run (oracle w) tree).2 ≤ M) :
    n ≤ M := by
  have h := actual_exact_recovery_card oracle tree M hcorrect hcost
  have hc : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hb : Fintype.card Bool = 2 := by simp
  rw [hc, hb] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

end Qatlib.Papers.DecisionTrees97.UniformQueryBound
