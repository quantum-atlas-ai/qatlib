/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QPatternMatch14.MainResults.Model.Instances
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! Literal weak-model constructions and counterexamples.
These records inspect the entire input for free; they have no oracle-cost credit. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QPatternMatch14.MainResults
open Qatlib.Papers.QPatternMatch14.MainResults.Model

abbrev CheckInput (m : ℕ) (A : Type*) := DStr 1 m A × DStr 1 m A
noncomputable def disagreeCount {m : ℕ} {A : Type*} [DecidableEq A]
    (inp : CheckInput m A) : ℕ :=
  Fintype.card { x : Coord 1 m // inp.1 x ≠ inp.2 x }

def detectionPromise {d n m : ℕ} {A : Type*} [DecidableEq A] (hmn : m ≤ n)
    (γ : ℝ) (inp : PatternInput d n m A) : Prop :=
  ∀ s, ¬ matchesAt hmn inp.T inp.P s → γ ≤ mismatchFraction hmn inp.T inp.P s

/-- The legacy interface allows a point mass on an arbitrary input-dependent answer at zero cost. -/
def freeAlg {I A : Type*} [Fintype A] (pick : I → A) : QueryAlgorithm I A where
  cost _ := 0
  outProb i a := by classical exact if a = pick i then 1 else 0
  nonneg i a := by classical split <;> norm_num
  sum_one i := by classical simp

/-- The free-record witness assigns zero queries independently of its answer rule. -/
theorem freeCost {I A : Type*} [Fintype A] (pick : I → A) (i : I) :
    (freeAlg pick).cost i = 0 := rfl

/-- A free exact selector is a bounded-error algorithm in the legacy interface. -/
theorem freeCorrect {I A : Type*} [Fintype A] (pick : I → A)
    (spec : I → A → Prop) (i : I) (h : spec i (pick i)) :
    successMass (freeAlg pick) spec i = 1 := by
  classical
  simp [successMass, freeAlg, h]

/-- Choice of a matching offset or `none` reads the full text and pattern for free. -/
def patternPick {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A) :
    Option (Coord d (n - m + 1)) := by
  classical
  exact if h : ∃ s, matchesAt hmn inp.T inp.P s then some h.choose else none

/-- The pointwise choice satisfies the complete old pattern specification. -/
theorem patternPickOk {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A) :
    patternSpec hmn inp (patternPick hmn inp) := by
  classical
  unfold patternPick
  split_ifs with h
  · exact h.choose_spec
  · exact fun s hs => h ⟨s, hs⟩

/-- A zero-cost exact pattern solver exists because the old output and cost fields are uncoupled. -/
theorem freePattern {d n m : ℕ} {A : Type*} (hmn : m ≤ n) :
    ∃ Alg : QueryAlgorithm (PatternInput d n m A) (Option (Coord d (n - m + 1))),
      (∀ inp, Alg.cost inp = 0) ∧
      (∀ inp, successMass Alg (patternSpec hmn) inp = 1) :=
  ⟨freeAlg (patternPick hmn), fun _ => rfl,
    fun inp => freeCorrect _ _ inp (patternPickOk hmn inp)⟩

/-- A zero-cost exact detector refutes every strictly positive lower bound in this interface. -/
def detectPick {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A) : Bool := by
  classical
  exact if ∃ s, matchesAt hmn inp.T inp.P s then true else false

/-- The detector's success is one on every input, independent of all promises. -/
theorem detectCorrect {d n m : ℕ} {A : Type*} (hmn : m ≤ n) :
    boundedError (freeAlg (detectPick (d := d) (A := A) hmn)) (patternDetectionSpec hmn) := by
  intro inp
  have hx : patternDetectionSpec hmn inp (detectPick hmn inp) := by
    classical
    unfold detectPick
    split_ifs with h
    · exact h
    · exact fun s hs => h ⟨s, hs⟩
  rw [freeCorrect _ _ inp hx]
  norm_num

/-- No promised input can make a positive expression less than this exact detector's zero cost. -/
theorem lowerFailure {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (b : ℝ) (hb : 0 < b)
    (promise : PatternInput d n m A → Prop) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ Alg : QueryAlgorithm (PatternInput d n m A) Bool,
      boundedError Alg (patternDetectionSpec hmn) →
        ∃ inp, promise inp ∧ c * b ≤ (Alg.cost inp : ℝ) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨inp, _, hcost⟩ := h (freeAlg (detectPick hmn)) (detectCorrect hmn)
  exact (not_le_of_gt (mul_pos hc hb)) (by simpa [freeAlg] using hcost)

/-- The explicit positive scales of the first two lower bounds already fail at size one. -/
theorem lowerScales :
    lemma10QuantumBound 1 1 1 1 = 1 ∧ lemma10ClassicalBound 1 1 1 1 = 1 ∧
      injectiveBound 1 1 1 1 = 3 := by
  norm_num [lemma10QuantumBound, lemma10ClassicalBound, injectiveBound]

/-- The quantum half of the old Lemma 10 is false in the free-record interface. -/
theorem refuteLemma10 :
    ¬ (∃ cq : ℝ, 0 < cq ∧
      ∀ Alg : QueryAlgorithm (PatternInput 1 1 1 Bool) Bool,
        boundedError Alg (patternDetectionSpec (by omega)) →
          ∃ inp : PatternInput 1 1 1 Bool, detectionPromise (by omega) 1 inp ∧
            cq * lemma10QuantumBound 1 1 1 1 ≤ (Alg.cost inp : ℝ)) := by
  apply lowerFailure
  norm_num [lemma10QuantumBound]

/-- The old injective lower bound is false at one site over a two-symbol alphabet. -/
theorem refuteLemma11 :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ Alg : ClassicalAlgorithm (PatternInput 1 1 1 Bool) Bool,
        boundedError Alg (patternDetectionSpec (by omega)) →
          ∃ inp : PatternInput 1 1 1 Bool,
            Function.Injective inp.T ∧ Function.Injective inp.P ∧
            detectionPromise (by omega) 1 inp ∧
            c * injectiveBound 1 1 1 1 ≤ (Alg.cost inp : ℝ)) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨inp, _, _, _, hcost⟩ := h (freeAlg (detectPick (by omega))) (detectCorrect (by omega))
  norm_num [freeAlg, injectiveBound] at hcost
  linarith

/-- The random-function lower-bound expression is positive at a concrete admissible size. -/
theorem refuteProp13 :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ Alg : ClassicalAlgorithm (PatternInput 2 2 1 Bool) Bool,
        boundedError Alg (patternDetectionSpec (by omega)) →
          ∃ inp : PatternInput 2 2 1 Bool,
            c * proposition13Bound 2 2 1 2 ≤ (Alg.cost inp : ℝ)) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨inp, hcost⟩ := h (freeAlg (detectPick (by omega))) (detectCorrect (by omega))
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [freeAlg, proposition13Bound, Real.logb, hlog] at hcost
  linarith

/-- A zero-cost exact check satisfies the literal upper-bound obligation. -/
theorem source_lemma3 {m : ℕ} {A : Type*} [_fa : Fintype A] [DecidableEq A]
    (hm : 0 < m) {γ : ℝ} (hγ0 : 0 < γ) (_hγ1 : γ ≤ 1) :
    ∃ Check : QueryAlgorithm (CheckInput m A) Bool, ∃ C : ℝ, 0 < C ∧
      (∀ inp : CheckInput m A, (Check.cost inp : ℝ) ≤ C / Real.sqrt γ) ∧
      (∀ inp : CheckInput m A, inp.1 = inp.2 →
        successMass Check (fun _ b => b = true) inp = 1) ∧
      (∀ inp : CheckInput m A, γ * (m : ℝ) ≤ (disagreeCount inp : ℝ) →
        (2 / 3 : ℝ) ≤ successMass Check (fun _ b => b = false) inp) := by
  classical
  let pick : CheckInput m A → Bool := fun inp => if inp.1 = inp.2 then true else false
  refine ⟨freeAlg pick, 1, by norm_num, ?_, ?_, ?_⟩
  · intro inp
    rw [freeCost, Nat.cast_zero]
    positivity
  · intro inp heq
    apply freeCorrect
    dsimp [pick]
    exact ite_eq_left heq
  · intro inp hdis
    have hne : inp.1 ≠ inp.2 := by
      intro heq
      have hz : disagreeCount inp = 0 := by simp [disagreeCount, heq]
      rw [hz] at hdis
      have hp : 0 < γ * (m : ℝ) := mul_pos hγ0 (by exact_mod_cast hm)
      exact (not_le_of_gt hp) (by simpa using hdis)
    have hs : successMass (freeAlg pick) (fun _ b => b = false) inp = 1 := by
      apply freeCorrect
      dsimp [pick]
      exact ite_eq_right hne
    rw [hs]
    norm_num

/-- Natural-size logarithms are nonnegative, including the library convention at zero. -/
theorem natLogNonneg (m : ℕ) : 0 ≤ Real.log (m : ℝ) := by
  rcases m with _ | m
  · simp
  · apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)

/-- The exact old Theorem 2 is a free-record existential, with no operational query credit. -/
theorem source_theorem2 {d n m : ℕ} {A : Type*} [_fa : Fintype A] [DecidableEq A]
    [_na : Nonempty A] (hmn : m ≤ n) {ν : ℕ} (hνT : ν ≤ n) (hνP : ν ≤ m)
    {γ : ℝ} (_hγ : 0 < γ) :
    ∃ Alg : QueryAlgorithm (PatternInput d n m A) (Option (Coord d (n - m + 1))),
      ∃ C : ℝ, 0 < C ∧
        ∀ inp : PatternInput d n m A, theorem2Promise hmn ν hνT hνP γ inp →
          (Alg.cost inp : ℝ) ≤
            C * theorem2QueryBound (d : ℝ) (n : ℝ) (m : ℝ) (ν : ℝ) γ ∧
          (2 / 3 : ℝ) ≤ successMass Alg (patternSpec hmn) inp := by
  refine ⟨freeAlg (patternPick hmn), 1, by norm_num, ?_⟩
  intro inp _
  constructor
  · rw [freeCost, Nat.cast_zero]
    rw [one_mul]
    have he : 0 ≤ expLogTerm (d : ℝ) (m : ℝ) := by
      unfold expLogTerm
      exact Real.rpow_nonneg (by norm_num) _
    unfold theorem2QueryBound
    exact mul_nonneg
      (Real.rpow_nonneg
        (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)) he)
          (Nat.cast_nonneg m)) _)
      (add_nonneg
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg ν) _)
          (natLogNonneg m)) he)
        (div_nonneg zero_le_one (Real.sqrt_nonneg γ)))
  · rw [freeCorrect _ _ inp (patternPickOk hmn inp)]
    norm_num

/-- The old average-case theorem omits the random law and admits a free exact selector. -/
theorem source_theorem1 {d n m : ℕ} {A : Type*} [_fa : Fintype A] [DecidableEq A]
    [_na : Nonempty A] (hmn : m ≤ n) (_hm : 0 < m) (_hd : 0 < d) :
    ∃ Alg : QueryAlgorithm (PatternInput d n m A) (Option (Coord d (n - m + 1))),
      ∃ C : ℝ, 0 < C ∧
        ∀ inp : PatternInput d n m A, theorem1Good hmn inp →
          (Alg.cost inp : ℝ) ≤ C * theorem1QueryBound (d : ℝ) (n : ℝ) (m : ℝ) ∧
          (2 / 3 : ℝ) ≤ successMass Alg (patternSpec hmn) inp := by
  refine ⟨freeAlg (patternPick hmn), 1, by norm_num, ?_⟩
  intro inp _
  constructor
  · rw [freeCost, Nat.cast_zero]
    rw [one_mul]
    unfold theorem1QueryBound
    exact mul_nonneg
      (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)) _)
      (Real.rpow_nonneg (by norm_num) _)
  · rw [freeCorrect _ _ inp (patternPickOk hmn inp)]
    norm_num

/-- The old Proposition 8 likewise has a free exact witness on every input. -/
theorem source_proposition8 {d n m : ℕ} {A : Type*} [_fa : Fintype A] [DecidableEq A]
    [_na : Nonempty A] (hmn : m ≤ n) (_hm : 0 < m) {ν : ℕ} (hνT : ν ≤ n) :
    ∃ Alg : QueryAlgorithm (PatternInput d n m A) (Option (Coord d (n - m + 1))),
      ∃ C : ℝ, 0 < C ∧
        ∀ inp : PatternInput d n m A, proposition8Good hmn ν hνT inp →
          (Alg.cost inp : ℝ) ≤
            C * proposition8QueryBound (d : ℝ) (n : ℝ) (m : ℝ) ∧
          (2 / 3 : ℝ) ≤ successMass Alg (patternSpec hmn) inp := by
  refine ⟨freeAlg (patternPick hmn), 1, by norm_num, ?_⟩
  intro inp _
  constructor
  · rw [freeCost, Nat.cast_zero]
    rw [one_mul]
    unfold proposition8QueryBound
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)) _)
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (natLogNonneg m) _))
      (natLogNonneg n)
  · rw [freeCorrect _ _ inp (patternPickOk hmn inp)]
    norm_num

/-- The exact old classical upper-bound target is true in the free-record model. -/
theorem source_theorem12 {d n m : ℕ} {A : Type*} [_fa : Fintype A] [_da : DecidableEq A]
    [_na : Nonempty A] (hmn : m ≤ n) {γ : ℝ} (hγ : 0 < γ) (_hγ1 : γ ≤ 1) :
    ∃ Alg : ClassicalAlgorithm (PatternInput d n m A) (Option (Coord d (n - m + 1))),
      ∃ C : ℝ, 0 < C ∧
        ∀ inp : PatternInput d n m A,
          Function.Injective inp.T → Function.Injective inp.P →
            (Alg.cost inp : ℝ) ≤
              C * injectiveBound (d : ℝ) (n : ℝ) (m : ℝ) γ ∧
            (2 / 3 : ℝ) ≤ successMass Alg (patternSpec hmn) inp := by
  refine ⟨freeAlg (patternPick hmn), 1, by norm_num, ?_⟩
  intro inp _ _
  constructor
  · rw [freeCost, Nat.cast_zero]
    rw [one_mul]
    unfold injectiveBound
    exact add_nonneg
      (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)) _))
      (div_nonneg zero_le_one hγ.le)
  · rw [freeCorrect _ _ inp (patternPickOk hmn inp)]
    norm_num

/-- The old match-only output can also inspect the full input for free. -/
def offsetPick {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A) :
    Coord d (n - m + 1) := by
  classical
  exact if h : ∃ s, matchesAt hmn inp.T inp.P s then h.choose else fun _ => 0

/-- A promised existing match makes the free chosen offset correct. -/
theorem offsetPickOk {d n m : ℕ} {A : Type*} (hmn : m ≤ n) (inp : PatternInput d n m A)
    (h : ∃ s, matchesAt hmn inp.T inp.P s) :
    matchesAt hmn inp.T inp.P (offsetPick hmn inp) := by
  classical
  simpa [offsetPick, h] using h.choose_spec

/-- The exact old Theorem 5 is proved without granting source query-complexity credit. -/
theorem source_theorem5 {d n m : ℕ} {A : Type*} [_fa : Fintype A] [DecidableEq A]
    [_na : Nonempty A] (hmn : m ≤ n) {ν : ℕ} (hνT : ν ≤ n) (hνP : ν ≤ m) :
    ∃ Alg : QueryAlgorithm (PatternInput d n m A) (Coord d (n - m + 1)),
      ∃ C : ℝ, 0 < C ∧
        ∀ inp : PatternInput d n m A, theorem5Promise hmn ν hνT hνP inp →
          (Alg.cost inp : ℝ) ≤
            C * theorem5QueryBound (d : ℝ) (n : ℝ) (m : ℝ) (ν : ℝ) ∧
          (2 / 3 : ℝ) ≤
            successMass Alg (fun inp s => matchesAt hmn inp.T inp.P s) inp := by
  refine ⟨freeAlg (offsetPick hmn), 1, by norm_num, ?_⟩
  intro inp hp
  constructor
  · rw [freeCost, Nat.cast_zero]
    rw [one_mul]
    unfold theorem5QueryBound
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)) _)
          (Real.rpow_nonneg (Nat.cast_nonneg ν) _))
        (Real.rpow_nonneg (natLogNonneg m) _))
      (Real.rpow_nonneg (by norm_num) _)
  · rw [freeCorrect _ _ inp (offsetPickOk hmn inp hp.2.2.2)]
    norm_num

def brokenShift : HiddenShiftInput 1 1 (Fin 3) where
  f x := ⟨(x 0).val, by have := (x 0).isLt; omega⟩
  g x := ⟨2 * (x 0).val, by have := (x 0).isLt; omega⟩
  s _ := 0

/-- The literal noisy promise admits a concrete pair with no exact cyclic shift. -/
theorem brokenPromise : theorem4Promise brokenShift := by
  refine ⟨by decide, by decide, 1, by norm_num, ?_⟩
  have hc : Fintype.card {x : Coord 1 (2 ^ 1) //
      brokenShift.g x ≠ brokenShift.f (addCoord 1 brokenShift.s x)} = 1 := by decide
  norm_num [hiddenShiftMismatchFraction, hc, expLogTerm, Real.logb]

/-- No shift exactly relates the two injective functions in this admitted instance. -/
theorem brokenNoShift :
    ∀ s : Coord 1 (2 ^ 1), ¬ ∀ x, brokenShift.g x = brokenShift.f (addCoord 1 s x) := by
  decide

/-- Every alleged output distribution has zero success on this promised instance. -/
theorem brokenSuccess (Alg : QueryAlgorithm (HiddenShiftInput 1 1 (Fin 3)) (Coord 1 (2 ^ 1))) :
    successMass Alg (fun inp s => ∀ x, inp.g x = inp.f (addCoord 1 s x)) brokenShift = 0 := by
  classical
  unfold successMass
  rw [Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro s _
  split_ifs with h
  · exact (brokenNoShift s h).elim
  · rfl

/-- The complete old Theorem 4 target is false at positive dimension and register size. -/
theorem refuteTheorem4 :
    ¬ (∃ Alg : QueryAlgorithm (HiddenShiftInput 1 1 (Fin 3)) (Coord 1 (2 ^ 1)),
      ∃ C : ℝ, 0 < C ∧
        ∀ inp : HiddenShiftInput 1 1 (Fin 3), theorem4Promise inp →
          (Alg.cost inp : ℝ) ≤ C * theorem4QueryBound 1 1 ∧
          (2 / 3 : ℝ) ≤
            successMass Alg (fun inp s => ∀ x, inp.g x = inp.f (addCoord 1 s x)) inp) := by
  rintro ⟨Alg, C, _, h⟩
  have hx := (h brokenShift brokenPromise).2
  rw [brokenSuccess] at hx
  norm_num at hx

end Qatlib.Papers.QPatternMatch14.MainResults
