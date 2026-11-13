/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.AmplificationHilbert
import Qatlib.Papers.ExactSimon97.MainResults.Amplification
import Qatlib.Papers.ExactSimon97.MainResults.ShrinkCoherent

/-!
# State formulas for exact amplitude amplification

This module expresses a phase update directly in terms of complex state amplitudes and their
good and bad components. Equal good and bad masses eliminate all bad amplitudes; coordinate
balance then yields support on nonzero vectors of a binary subspace. These constructions support
the results of [BrassardHoyer1997].

## Main statements

* `lemma8_general_output`: computes both components of the phase-updated state.
* `theorem4_coordinate_amplification`: restricts the updated support to a chosen coordinate-one
  fiber.
* `cosetBlock_good_half`: proves that balanced coset blocks have good mass one half.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Classical
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

variable {I : Type} [Fintype I]

/-- The finite Hermitian inner product `∑ i, star (f i) * g i`. -/
def hInner (f g : I → ℂ) : ℂ := ∑ i, star (f i) * g i

/-- The sum of squared amplitude magnitudes on indices marked true by `χ`, expressed as a
complex number. -/
def goodMass (χ : I → Bool) (ψ : I → ℂ) : ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => χ i = true), star (ψ i) * ψ i

/-- The sum of squared amplitude magnitudes on indices marked false by `χ`, expressed as a
complex number. -/
def badMass (χ : I → Bool) (ψ : I → ℂ) : ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => χ i = false), star (ψ i) * ψ i

/-- Multiply the amplitudes marked by `χ` by `Complex.I`, leaving the other amplitudes
unchanged. -/
def phaseGood (χ : I → Bool) (ψ : I → ℂ) : I → ℂ :=
  fun i => if χ i then Complex.I * ψ i else ψ i

/-- The state update `w + (Complex.I - 1) * ⟨Ψ, w⟩ * Ψ`, without a normalization assumption. -/
def zeroReflState (Ψ w : I → ℂ) : I → ℂ :=
  fun i => (Complex.I - 1) * hInner Ψ w * Ψ i + w i

/-- The restriction of a state to indices marked true by `χ`. -/
def goodPart (χ : I → Bool) (ψ : I → ℂ) : I → ℂ := fun i => if χ i then ψ i else 0

/-- The restriction of a state to indices marked false by `χ`. -/
def badPart (χ : I → Bool) (ψ : I → ℂ) : I → ℂ := fun i => if χ i then 0 else ψ i

/-- Every element of `ZMod 2` is zero or one. -/
theorem zmod2_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The sums over the true and false fibers of a Boolean predicate add to the full sum. -/
theorem sum_split_filter (χ : I → Bool) (f : I → ℂ) :
    (∑ i ∈ Finset.univ.filter (fun i => χ i = true), f i) +
        (∑ i ∈ Finset.univ.filter (fun i => χ i = false), f i) = ∑ i, f i := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset I))
    (p := fun i => χ i = true) (f := f)
  have hcompl : (Finset.univ.filter (fun i => ¬ (χ i = true))) =
      (Finset.univ.filter (fun i => χ i = false)) := by
    apply Finset.filter_congr
    intro i _
    cases χ i <;> simp
  rw [hcompl] at h
  simpa using h

/-- The inner product with the phase-marked state is `Complex.I * goodMass χ ψ + badMass χ ψ`. -/
theorem hInner_phaseGood (χ : I → Bool) (ψ : I → ℂ) :
    hInner ψ (phaseGood χ ψ) = Complex.I * goodMass χ ψ + badMass χ ψ := by
  classical
  unfold hInner phaseGood goodMass badMass
  have hterm : ∀ i : I,
      star (ψ i) * (if χ i then Complex.I * ψ i else ψ i) =
        if χ i then Complex.I * (star (ψ i) * ψ i) else star (ψ i) * ψ i := by
    intro i
    cases χ i <;> simp [mul_assoc, mul_comm]
  simp_rw [hterm]
  rw [← sum_split_filter (χ := χ)
    (f := fun i => if χ i then Complex.I * (star (ψ i) * ψ i) else star (ψ i) * ψ i)]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [if_pos hi.2]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [if_neg (by simpa using hi.2)]

/-- If good and bad masses sum to one, each good amplitude is multiplied by `2 * Complex.I * (1
- goodMass χ ψ) - 1` by the combined update. -/
theorem phase_component_good (χ : I → Bool) (ψ : I → ℂ)
    (h : goodMass χ ψ + badMass χ ψ = 1) :
    ∀ i, χ i = true →
      zeroReflState ψ (phaseGood χ ψ) i =
        (2 * Complex.I * (1 - goodMass χ ψ) - 1) * ψ i := by
  intro i hi
  have hI2 : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
  have hb : badMass χ ψ = 1 - goodMass χ ψ := by linear_combination h
  unfold zeroReflState
  rw [hInner_phaseGood, hb]
  have hph : phaseGood χ ψ i = Complex.I * ψ i := by simp [phaseGood, hi]
  rw [hph]
  ring_nf
  rw [hI2]
  ring

/-- If good and bad masses sum to one, each bad amplitude is multiplied by `Complex.I * (1 - 2 *
goodMass χ ψ)` by the combined update. -/
theorem phase_component_bad (χ : I → Bool) (ψ : I → ℂ)
    (h : goodMass χ ψ + badMass χ ψ = 1) :
    ∀ i, χ i = false →
      zeroReflState ψ (phaseGood χ ψ) i =
        (Complex.I * (1 - 2 * goodMass χ ψ)) * ψ i := by
  intro i hi
  have hI2 : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
  have hb : badMass χ ψ = 1 - goodMass χ ψ := by linear_combination h
  unfold zeroReflState
  rw [hInner_phaseGood, hb]
  have hph : phaseGood χ ψ i = ψ i := by simp [phaseGood, hi]
  rw [hph]
  ring_nf
  rw [hI2]
  ring

/-- When good and bad masses sum to one, the phase-updated state is the stated linear
combination of its good and bad parts. See [BrassardHoyer1997]. -/
theorem lemma8_general_output (χ : I → Bool) (ψ : I → ℂ)
    (h : goodMass χ ψ + badMass χ ψ = 1) :
    zeroReflState ψ (phaseGood χ ψ) =
      fun i => (2 * Complex.I * (1 - goodMass χ ψ) - 1) * goodPart χ ψ i +
        (Complex.I * (1 - 2 * goodMass χ ψ)) * badPart χ ψ i := by
  funext i
  by_cases hi : χ i = true
  · rw [phase_component_good χ ψ h i hi]
    simp only [goodPart, badPart, hi, if_true]
    ring
  · have hf : χ i = false := by cases hχ : χ i <;> simp_all
    rw [phase_component_bad χ ψ h i hf]
    simp only [goodPart, badPart, hf, Bool.false_eq_true, if_false]
    ring

/-- When both masses equal one half, every bad amplitude vanishes after the combined phase
update. See [BrassardHoyer1997]. -/
theorem lemma8_state_at_half (χ : I → Bool) (ψ : I → ℂ)
    (hg : goodMass χ ψ = 1 / 2) (hb : badMass χ ψ = 1 / 2) :
    ∀ i, χ i = false → zeroReflState ψ (phaseGood χ ψ) i = 0 := by
  intro i hi
  have hsum : goodMass χ ψ + badMass χ ψ = 1 := by rw [hg, hb]; norm_num
  rw [phase_component_bad χ ψ hsum i hi, hg]
  norm_num

/-- If `Ψ` and `w` are supported on a predicate `S`, their rank-one phase update is also
supported on `S`. -/
theorem zeroReflState_support {S : I → Prop} (Ψ w : I → ℂ)
    (hΨ : ∀ i, Ψ i ≠ 0 → S i) (hw : ∀ i, w i ≠ 0 → S i) :
    ∀ i, zeroReflState Ψ w i ≠ 0 → S i := by
  intro i hi
  unfold zeroReflState at hi
  by_cases h0 : Ψ i = 0
  · have : (Complex.I - 1) * hInner Ψ w * Ψ i + w i = w i := by simp [h0]
    rw [this] at hi
    exact hw i hi
  · exact hΨ i h0

omit [Fintype I] in

/-- Multiplying selected amplitudes by `Complex.I` preserves any given support predicate. -/
theorem phaseGood_support {S : I → Prop} (χ : I → Bool) (ψ : I → ℂ)
    (h : ∀ i, ψ i ≠ 0 → S i) : ∀ i, phaseGood χ ψ i ≠ 0 → S i := by
  intro i hi
  by_cases hc : χ i = true
  · have hval : phaseGood χ ψ i = Complex.I * ψ i := by simp [phaseGood, hc]
    rw [hval] at hi
    refine h i ?_
    intro hz
    rw [hz, mul_zero] at hi
    exact hi rfl
  · have hf : χ i = false := by cases hχ : χ i <;> simp_all
    have hval : phaseGood χ ψ i = ψ i := by simp [phaseGood, hf]
    rw [hval] at hi
    exact h i hi

/-- The Boolean predicate marking states whose first-register coordinate `i` is one. -/
def coordGood {n : ℕ} {S : Type} (i : Fin n) (p : BoolVec n × S) : Bool :=
  decide (p.1 i = 1)

/-- The predicate `coordGood i` is true exactly when the first register has coordinate `i` equal
to one. -/
@[simp] theorem coordGood_eq_true {n : ℕ} {S : Type} (i : Fin n) (p : BoolVec n × S) :
    coordGood i p = true ↔ p.1 i = 1 := by
  simp [coordGood]

/-- For a state supported on `K` with equal good and bad masses, the combined update is
supported on vectors of `K` whose chosen coordinate is one. See [BrassardHoyer1997]. -/
theorem theorem4_coordinate_amplification {n : ℕ} {S : Type} [Fintype S]
    (ψ : BoolVec n × S → ℂ) (K : Submodule (ZMod 2) (BoolVec n)) (i : Fin n)
    (hsupp : ∀ p, ψ p ≠ 0 → p.1 ∈ K)
    (hg : goodMass (coordGood (S := S) i) ψ = 1 / 2)
    (hb : badMass (coordGood (S := S) i) ψ = 1 / 2) :
    ∀ p, zeroReflState ψ (phaseGood (coordGood (S := S) i) ψ) p ≠ 0 →
      p.1 ∈ K ∧ p.1 i = 1 := by
  intro p hp
  have hK : p.1 ∈ K :=
    zeroReflState_support (S := fun q : BoolVec n × S => q.1 ∈ K)
      ψ (phaseGood (coordGood (S := S) i) ψ) hsupp
      (phaseGood_support (coordGood (S := S) i) ψ hsupp) p hp
  refine ⟨hK, ?_⟩
  by_contra hne
  have hfalse : coordGood (S := S) i p = false := by
    by_cases h : p.1 i = 1
    · exact absurd h hne
    · simp [coordGood, h]
  exact hp (lemma8_state_at_half (coordGood (S := S) i) ψ hg hb p hfalse)

/-- For a state supported on `K` with equal good and bad masses, the combined update is
supported on nonzero vectors of `K`. See [BrassardHoyer1997]. -/
theorem theorem4_coordinate_nonzero {n : ℕ} {S : Type} [Fintype S]
    (ψ : BoolVec n × S → ℂ) (K : Submodule (ZMod 2) (BoolVec n)) (i : Fin n)
    (hsupp : ∀ p, ψ p ≠ 0 → p.1 ∈ K)
    (hg : goodMass (coordGood (S := S) i) ψ = 1 / 2)
    (hb : badMass (coordGood (S := S) i) ψ = 1 / 2) :
    ∀ p, zeroReflState ψ (phaseGood (coordGood (S := S) i) ψ) p ≠ 0 →
      p.1 ∈ K ∧ p.1 ≠ 0 := by
  intro p hp
  obtain ⟨hK, hi⟩ := theorem4_coordinate_amplification ψ K i hsupp hg hb p hp
  refine ⟨hK, ?_⟩
  intro hzero
  rw [hzero] at hi
  simp at hi

/-- A nonzero binary submodule contains a vector with some coordinate equal to one. See
[BrassardHoyer1997]. -/
theorem exists_one_of_ne_bot {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n))
    (hK : K ≠ ⊥) : ∃ (i : Fin n) (k : BoolVec n), k ∈ K ∧ k i = 1 := by
  by_contra h
  push Not at h
  apply hK
  ext x
  simp only [Submodule.mem_bot]
  constructor
  · intro hx
    funext i
    rcases zmod2_zero_or_one (x i) with h0 | h1
    · exact h0
    · exact absurd h1 (h i x hx)
  · intro hx
    rw [hx]
    exact K.zero_mem

/-- A binary submodule all of whose vectors have every coordinate zero is the zero submodule.
See [BrassardHoyer1997]. -/
theorem eq_bot_of_forall_zero {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n))
    (h : ∀ (i : Fin n) (k : BoolVec n), k ∈ K → k i = 0) : K = ⊥ := by
  ext x
  simp only [Submodule.mem_bot]
  constructor
  · intro hx
    funext i
    exact h i x hx
  · intro hx
    rw [hx]
    exact K.zero_mem

/-- The state supported on `K` with block amplitudes `c s * normFactor K * charFun (t s) x`. -/
def cosetBlockState {n : ℕ} {S : Type} [Fintype S]
    (K : Submodule (ZMod 2) (BoolVec n)) (t : S → BoolVec n) (c : S → ℂ) :
    BoolVec n × S → ℂ :=
  fun p => if p.1 ∈ K then c p.2 * normFactor K * charFun (t p.2) p.1 else 0

/-- On vectors belonging to `K`, `cosetBlockState` evaluates to its defining normalized
character amplitude. -/
theorem cosetBlockState_apply {n : ℕ} {S : Type} [Fintype S]
    (K : Submodule (ZMod 2) (BoolVec n)) (t : S → BoolVec n) (c : S → ℂ)
    (p : BoolVec n × S) (hp : p.1 ∈ K) :
    cosetBlockState K t c p = c p.2 * normFactor K * charFun (t p.2) p.1 := by
  simp [cosetBlockState, hp]

/-- The squared magnitude of the normalization factor is the reciprocal of the submodule
cardinality. -/
theorem star_normFactor_mul {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) :
    star (normFactor K) * normFactor K = ((Nat.card K : ℂ))⁻¹ := by
  have hpos : (0 : ℝ) < (Nat.card K : ℝ) := by
    haveI : Nonempty K := ⟨0⟩
    exact_mod_cast Nat.card_pos
  have hsq : Real.sqrt (Nat.card K : ℝ) * Real.sqrt (Nat.card K : ℝ) =
      (Nat.card K : ℝ) := Real.mul_self_sqrt (le_of_lt hpos)
  unfold normFactor
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv]
  have hc : ((Real.sqrt (Nat.card K : ℝ) : ℂ) * (Real.sqrt (Nat.card K : ℝ) : ℂ)) =
      ((Nat.card K : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]
  rw [hc]
  norm_num

/-- Every Boolean character value has squared magnitude one. -/
theorem star_charFun_mul {n : ℕ} (a x : BoolVec n) :
    star (charFun a x) * charFun a x = 1 := by
  unfold charFun
  rcases zmod2_zero_or_one (dot a x) with h | h
  · rw [h]
    simp
  · rw [h, stdAddChar_one_zmod2]
    norm_num

/-- The squared magnitude of a scaled normalized character amplitude equals `star c * c` times
the squared normalization factor. -/
theorem star_block_mul {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n))
    (t : BoolVec n) (c : ℂ) (x : BoolVec n) :
    star (c * normFactor K * charFun t x) * (c * normFactor K * charFun t x) =
      star c * c * (star (normFactor K) * normFactor K) := by
  calc star (c * normFactor K * charFun t x) * (c * normFactor K * charFun t x)
      = (star c * c) * (star (normFactor K) * normFactor K) *
          (star (charFun t x) * charFun t x) := by
        rw [star_mul, star_mul]
        ring
    _ = star c * c * (star (normFactor K) * normFactor K) := by
        rw [star_charFun_mul, mul_one]

/-- The cardinality of a binary submodule is nonzero when viewed as a complex number. -/
theorem natCard_ne_zero {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) :
    (Nat.card K : ℂ) ≠ 0 := by
  haveI : Nonempty K := ⟨0⟩
  have h : Nat.card K ≠ 0 := Nat.card_pos.ne'
  exact_mod_cast h

/-- If coordinate `i` takes the value one on `K`, twice the size of its one fiber equals the
cardinality of `K`. -/
theorem bitOne_card_mul_two {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) (i : Fin n)
    (hfib : ∃ k ∈ K, k i = 1) :
    (bitOne K i).card * 2 = Nat.card K := by
  classical
  have hKcard : Nat.card K =
      (Finset.univ.filter (fun k : BoolVec n => k ∈ K)).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hsplit : Finset.univ.filter (fun k : BoolVec n => k ∈ K) =
      bitZero K i ∪ bitOne K i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, bitZero,
      bitOne]
    constructor
    · intro hk
      rcases zmod2_zero_or_one (k i) with h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩)
      · exact hk
      · exact hk
  have hdisj : Disjoint (bitZero K i) (bitOne K i) := by
    rw [Finset.disjoint_left]
    intro k h0 h1
    simp only [bitZero, bitOne, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    rw [h0.2] at h1
    exact absurd h1.2 (by decide)
  obtain ⟨g0, hg0K, hg0i⟩ := hfib
  have hb := coordinate_balance K g0 hg0K i hg0i
  rw [hKcard, hsplit, Finset.card_union_of_disjoint hdisj, hb]
  omega

/-- If coordinate `i` is nonzero on `K`, the normalized character state's mass on its one fiber
is one half. See [BrassardHoyer1997]. -/
theorem fiberMass_half {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) (t : BoolVec n)
    (i : Fin n) (hfib : ∃ k ∈ K, k i = 1) :
    (∑ k ∈ bitOne K i, star (normFactor K * charFun t k) *
        (normFactor K * charFun t k)) = 1 / 2 := by
  classical
  have hterm : ∀ k : BoolVec n,
      star (normFactor K * charFun t k) * (normFactor K * charFun t k) =
        star (normFactor K) * normFactor K := by
    intro k
    have h := star_block_mul K t (1 : ℂ) k
    simpa using h
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_const, nsmul_eq_mul,
    star_normFactor_mul]
  have hmul := bitOne_card_mul_two K i hfib
  have h2 : ((bitOne K i).card : ℂ) * 2 = (Nat.card K : ℂ) := by
    rw [← hmul]
    push_cast
    ring
  have hcard := natCard_ne_zero K
  field_simp
  rw [← h2]

/-- If the block coefficients have total squared magnitude one and coordinate `i` is nonzero on
`K`, the good mass of the coset-block state is one half. See [BrassardHoyer1997]. -/
theorem cosetBlock_good_half {n : ℕ} {S : Type} [Fintype S]
    (K : Submodule (ZMod 2) (BoolVec n)) (t : S → BoolVec n) (c : S → ℂ)
    (hc : ∑ s, star (c s) * c s = 1) (i : Fin n)
    (hfib : ∃ k ∈ K, k i = 1) :
    goodMass (coordGood (S := S) i) (cosetBlockState K t c) = 1 / 2 := by
  classical
  unfold goodMass
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hstep : ∀ x : BoolVec n,
      (∑ s : S, (if coordGood (S := S) i (x, s) = true
          then star (cosetBlockState K t c (x, s)) * cosetBlockState K t c (x, s)
          else 0)) =
        (if x ∈ K ∧ x i = 1 then
          (∑ s : S, star (c s) * c s) * (star (normFactor K) * normFactor K)
          else 0) := by
    intro x
    by_cases hx : x ∈ K ∧ x i = 1
    · have hxtrue : ∀ s : S, coordGood (S := S) i (x, s) = true := by
        intro s
        simp [coordGood, hx.2]
      have hbody : ∀ s : S,
          (if coordGood (S := S) i (x, s) = true
              then star (cosetBlockState K t c (x, s)) * cosetBlockState K t c (x, s)
              else 0) =
            star (c s) * c s * (star (normFactor K) * normFactor K) := by
        intro s
        rw [hxtrue s, if_pos rfl]
        rw [cosetBlockState_apply K t c (x, s) hx.1]
        exact star_block_mul K (t s) (c s) x
      rw [Finset.sum_congr rfl (fun s _ => hbody s), ← Finset.sum_mul, hc, one_mul, if_pos hx]
    · have hzero : (∑ s : S, (if coordGood (S := S) i (x, s) = true
            then star (cosetBlockState K t c (x, s)) * cosetBlockState K t c (x, s)
            else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        by_cases hxK : x ∈ K
        · have hxi : x i ≠ 1 := fun h => hx ⟨hxK, h⟩
          have hcf : coordGood (S := S) i (x, s) = false := by
            simp [coordGood, hxi]
          rw [hcf]
          simp
        · have hblk : cosetBlockState K t c (x, s) = 0 := by
            simp [cosetBlockState, hxK]
          rw [hblk]
          simp
      rw [hzero, if_neg hx]
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter (fun x : BoolVec n => x ∈ K ∧ x i = 1)) = bitOne K i := by
    rfl
  rw [hfilter, Finset.sum_const, hc, star_normFactor_mul, one_mul, nsmul_eq_mul]
  have hmul := bitOne_card_mul_two K i hfib
  have hcm : ((bitOne K i).card : ℂ) * 2 = (Nat.card K : ℂ) := by
    rw [← hmul]
    push_cast
    ring
  have hcard := natCard_ne_zero K
  field_simp
  rw [← hcm]

end Qatlib.Papers.ExactSimon97.MainResults
