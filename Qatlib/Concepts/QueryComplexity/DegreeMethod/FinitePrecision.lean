/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
import Mathlib.Data.Nat.Bitwise

/-!
# Finite-precision contract checks and counterexamples

This module proves basic consequences of finite approximation inputs and explicit access
contracts, and checks the finite-precision arithmetic and compilation requirements defined in
`FinitePrecisionCoreDefs`. It establishes refutations of several requirements as currently
formulated: indistinguishable encoded inputs can demand incompatible outputs, and some stated
clock or space bounds are smaller than the input they must cover.

Supporting constructions include injective numeric encodings, deterministic halting uniqueness,
tape-script execution, and a finite-state machine that writes a fixed word. Classical and
quantum computation provide background for these machine and finite-precision models
[KitaevShenVyalyi2002]; the counterexamples here concern the specific local contract
definitions.

## Main statements

* `finiteInputBoundary`, `premisesExplicit`, and `accessRestrictionPreserved` establish the
  stated input and access conditions.
* `backendSound_refutable`, `clause3Body_refutable`, and `clause44Body_refutable` refute the
  corresponding arithmetic and consumer packages.
* `constOut_halts` and `certifiesConst` construct certified finite inputs for rational
  constants.
* `tm0Compiled_contract_ambiguity` refutes uniform compilation when contract implementations are
  absent from the encoded input.
* `tm0Compiled_space_le_input` supplies the input-space lower bound used to refute the
  postprocessing consumers and `clause45Body_refutable` refutes the final compilation package.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002], *Classical and Quantum Computation*,
  for background.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib


namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs

/-- If the configuration reached at time `t` has no next step, the machine trajectory is `none`
at time `t + 1`. -/
theorem bitMachineAfter_succ_of_stop {Λ : Type} [Inhabited Λ]
    (M : Turing.TM0.Machine (Option Bool) Λ) (input : List (Option Bool)) {t : ℕ}
    {cfg : Turing.TM0.Cfg (Option Bool) Λ}
    (hr : BitMachineAfter M input t = some cfg) (hs : Turing.TM0.step M cfg = none) :
    BitMachineAfter M input (t + 1) = none := by
  simp [BitMachineAfter, hr, hs]

/-- Once the machine trajectory is `none`, it remains `none` at the next time step. -/
theorem bitMachineAfter_none_succ {Λ : Type} [Inhabited Λ]
    (M : Turing.TM0.Machine (Option Bool) Λ) (input : List (Option Bool)) {t : ℕ}
    (hr : BitMachineAfter M input t = none) :
    BitMachineAfter M input (t + 1) = none := by
  simp [BitMachineAfter, hr]

/-- If the machine trajectory is `none` at time `t`, it is `none` at every time `s` with `t ≤
s`. -/
theorem bitMachineAfter_none_of_le {Λ : Type} [Inhabited Λ]
    (M : Turing.TM0.Machine (Option Bool) Λ) (input : List (Option Bool)) {t s : ℕ}
    (h : t ≤ s) (hr : BitMachineAfter M input t = none) :
    BitMachineAfter M input s = none := by
  induction h with
  | refl => exact hr
  | step _ ih => exact bitMachineAfter_none_succ M input ih

/-- Two halting configurations reached by the same machine on the same input are equal, even
when their recorded times initially differ. -/
theorem bitMachineAfter_halt_unique {Λ : Type} [Inhabited Λ]
    (M : Turing.TM0.Machine (Option Bool) Λ) (input : List (Option Bool)) {t s : ℕ}
    {cfgT cfgS : Turing.TM0.Cfg (Option Bool) Λ}
    (hT : BitMachineAfter M input t = some cfgT) (sT : Turing.TM0.step M cfgT = none)
    (hS : BitMachineAfter M input s = some cfgS) (sS : Turing.TM0.step M cfgS = none) :
    cfgT = cfgS := by
  have hts : t = s := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hstop : BitMachineHaltsAt M input t := ⟨cfgT, hT, sT⟩
      have h1 : BitMachineAfter M input (t + 1) = none :=
        Qatlib.Concepts.ClassicalTape.TapeCompilation.bitMachineAfter_succ_of_halts hstop
      have hnone : BitMachineAfter M input s = none :=
        bitMachineAfter_none_of_le M input (Nat.succ_le_of_lt hlt) h1
      simp [hnone] at hS
    · have hstop : BitMachineHaltsAt M input s := ⟨cfgS, hS, sS⟩
      have h1 : BitMachineAfter M input (s + 1) = none :=
        Qatlib.Concepts.ClassicalTape.TapeCompilation.bitMachineAfter_succ_of_halts hstop
      have hnone : BitMachineAfter M input t = none :=
        bitMachineAfter_none_of_le M input (Nat.succ_le_of_lt hgt) h1
      simp [hnone] at hT
  subst hts
  exact Option.some.inj (hT.symm.trans hS)

/-- At an index within the Boolean word, `tapeAt` returns the corresponding bit wrapped in
`some`. -/
theorem tapeAt_eq_some {l : List Bool} {i : ℕ} (hi : i < l.length) :
    tapeAt l i = some l[i] := by
  have hi' : i < (l.map some).length := by simpa using hi
  show (l.map some).getD i none = some l[i]
  rw [List.getD_eq_getElem (l.map some) none hi']
  simp only [List.getElem_map]

/-- At an index at or beyond the word's length, `tapeAt` returns the blank symbol `none`. -/
theorem tapeAt_eq_none {l : List Bool} {i : ℕ} (hi : l.length ≤ i) :
    tapeAt l i = none := by
  have hi' : (l.map some).length ≤ i := by simpa using hi
  show (l.map some).getD i none = none
  rw [List.getD_eq_default (l.map some) none hi']

/-- Boolean words are equal if their blank-padded tape representations agree at every
natural-number index. -/
theorem tapeAt_ext {l l' : List Bool} (h : ∀ i, tapeAt l i = tapeAt l' i) : l = l' := by
  by_contra hne
  have hlen : l.length = l'.length := by
    by_contra hlen'
    rcases Nat.lt_or_gt_of_ne hlen' with hlt | hgt
    · have := h l.length
      rw [tapeAt_eq_none (le_refl _), tapeAt_eq_some hlt] at this
      exact Option.some_ne_none _ this.symm
    · have := h l'.length
      rw [tapeAt_eq_none (le_refl _), tapeAt_eq_some hgt] at this
      exact Option.some_ne_none _ this
  apply hne
  refine List.ext_getElem hlen ?_
  intro i hi hi'
  have hii := h i
  rw [tapeAt_eq_some hi, tapeAt_eq_some hi'] at hii
  exact Option.some.inj hii

/-- Establishes that finite real inputs are exactly computably approximable reals, with the
analogous componentwise description for complex inputs. In particular, a real lacking a
computable approximation is excluded. -/
theorem finiteInputBoundary : FiniteInputBoundary := by
  refine ⟨fun x => Iff.rfl, fun z => Iff.rfl, ?_⟩
  intro x h hx
  exact h hx

/-- Expands the arithmetic preconditions: division and logarithm require their stated dyadic
lower bounds, square root requires a nonnegative argument, and the remaining operations have
no additional premise. -/
theorem premisesExplicit : PremisesExplicit := by
  intro op x y gap
  cases op <;> exact Iff.rfl

/-- Refutes `BackendSound be C D` for every backend and every choice of cost constants. The same
rational input approximates two pairs of real addends whose required dyadic outputs cannot
agree. -/
theorem backendSound_refutable (be : ArithBackend) (C D : ℕ) : ¬ BackendSound be C D := by
  intro h

  have hA := h ArithOp.add (1/8 : ℝ) (1/8 : ℝ) 0 1 (3/8 : ℚ) (3/8 : ℚ)
    (by exact True.intro) (by norm_num) (by norm_num)
  have hB := h ArithOp.add (5/8 : ℝ) (5/8 : ℝ) 0 1 (3/8 : ℚ) (3/8 : ℚ)
    (by exact True.intro) (by norm_num) (by norm_num)
  obtain ⟨tA, mA, cfgA, hrA, hsA, htA, hrdA, -, -, -⟩ := hA
  obtain ⟨tB, mB, cfgB, hrB, hsB, htB, hrdB, -, -, -⟩ := hB

  have hcfg : cfgA = cfgB :=
    bitMachineAfter_halt_unique (be.run ArithOp.add)
      (ArithOpInput ArithOp.add 1 0 (3/8) (3/8)) hrA hsA hrB hsB
  subst hcfg

  have hrdA' : |(mA : ℝ) / 2 - 1 / 4| ≤ 1 / 2 := by
    have := hrdA
    simp only [RoundedDyadic, dyadicVal, ArithOpValue] at this
    norm_num at this
    exact this
  have hrdB' : |(mB : ℝ) / 2 - 5 / 4| ≤ 1 / 2 := by
    have := hrdB
    simp only [RoundedDyadic, dyadicVal, ArithOpValue] at this
    norm_num at this
    exact this
  have mA_mem : mA = 0 ∨ mA = 1 := by
    rw [abs_le] at hrdA'
    have e1 : (-1 : ℝ) ≤ 2 * (mA : ℝ) := by linarith
    have e2 : 2 * (mA : ℝ) ≤ 3 := by linarith
    have i1 : (-1 : ℤ) ≤ 2 * mA := by exact_mod_cast e1
    have i2 : 2 * mA ≤ 3 := by exact_mod_cast e2
    omega
  have mB_mem : mB = 2 ∨ mB = 3 := by
    rw [abs_le] at hrdB'
    have e1 : (3 : ℝ) ≤ 2 * (mB : ℝ) := by linarith
    have e2 : 2 * (mB : ℝ) ≤ 7 := by linarith
    have i1 : (3 : ℤ) ≤ 2 * mB := by exact_mod_cast e1
    have i2 : 2 * mB ≤ 7 := by exact_mod_cast e2
    omega

  have htapes : ∀ i : ℕ,
      tapeAt (ratBits ((mA : ℚ) / 2)) i = tapeAt (ratBits ((mB : ℚ) / 2)) i := by
    intro i
    have eA := htA i
    have eB := htB i
    have k2 : ((2 : ℚ) ^ (1 : ℕ)) = 2 := by norm_num
    rw [k2] at eA eB
    exact eA.symm.trans eB

  have hdiv1 : ((1 : ℤ) : ℚ) / 2 = Rat.divInt 1 2 := by
    rw [Rat.div_def', Rat.num_intCast, Rat.den_intCast]; norm_num
  have hdiv3 : ((3 : ℤ) : ℚ) / 2 = Rat.divInt 3 2 := by
    rw [Rat.div_def', Rat.num_intCast, Rat.den_intCast]; norm_num
  rcases mA_mem with hA0 | hA1 <;> rcases mB_mem with hB2 | hB3
  · rw [hA0, hB2, show ((0 : ℤ) : ℚ) / 2 = 0 by norm_num,
      show ((2 : ℤ) : ℚ) / 2 = 1 by norm_num] at htapes
    exact absurd (htapes 1) (by decide)
  · rw [hA0, hB3, show ((0 : ℤ) : ℚ) / 2 = 0 by norm_num, hdiv3] at htapes
    exact absurd (htapes 1) (by decide)
  · rw [hA1, hB2, hdiv1, show ((2 : ℤ) : ℚ) / 2 = 1 by norm_num] at htapes
    exact absurd (htapes 7) (by decide)
  · rw [hA1, hB3, hdiv1, hdiv3] at htapes
    exact absurd (htapes 2) (by decide)

/-- Combines the finite-input boundary and explicit arithmetic premises with the existence of an
arithmetic backend satisfying `BackendSound` for some cost constants. -/
def clause3Body : Prop :=
  FiniteInputBoundary ∧
  PremisesExplicit ∧
  ∃ (be : ArithBackend) (C D : ℕ), BackendSound be C D

/-- Refutes `clause3Body` using the impossibility of its `BackendSound` requirement. -/
theorem clause3Body_refutable : ¬ clause3Body := by
  rintro ⟨_, _, be, C, D, h⟩
  exact backendSound_refutable be C D h

/-- Every numerical parameter has one of the four declared kinds: phase, rotation, preparation
coefficient, or spectral gap. -/
theorem numericalKindsComplete : NumericalKindsComplete := by
  intro p
  cases p.kind with
  | phase => exact Or.inl rfl
  | rotation => exact Or.inr (Or.inl rfl)
  | prepareCoeff => exact Or.inr (Or.inr (Or.inl rfl))
  | spectralGap => exact Or.inr (Or.inr (Or.inr rfl))

/-- Extracts the lower bound charging input-reading cost from a `BackendCostOk` certificate. -/
theorem inputReadCostCharged : InputReadCostCharged := by
  intro inst k t C D h
  exact h.1

/-- A real certified by a numerical parameter's finite approximation machine is computably
approximable. -/
theorem noExactRealOracle : NoExactRealOracle := by
  intro inst i p x _ hp
  exact ⟨p.name, hp⟩

/-- Refutes `RationalHHLConsumer r` for every backend run. The one-entry instance with zero gap
and precision requires at least fourteen reading steps while its clock bound permits at most
one. -/
theorem rationalHHLConsumer_refutable (r : BackendRun) : ¬ RationalHHLConsumer r := by
  intro h

  obtain ⟨t, q, cfg, hr, hs, ht, hacc, hcost, hclock⟩ :=
    h 1 0 0 (fun _ => (1 : ℚ)) (fun _ => (1 : ℚ)) 1 1 1
      (by norm_num) (by norm_num) (by norm_num)

  have hcost' : 14 ≤ t := by
    have h1 : (ratBits (1 : ℚ)).length = 7 := by decide
    simpa [Fin.sum_univ_one, List.length_append, h1] using hcost

  have hclock' : t ≤ 1 := by simpa using hclock
  omega

/-- Refutes `RationalLCUConsumer r` for every backend run. A single coefficient equal to one at
zero precision requires at least seven reading steps while its clock bound permits at most
one. -/
theorem rationalLCUConsumer_refutable (r : BackendRun) : ¬ RationalLCUConsumer r := by
  intro h

  obtain ⟨t, q, cfg, hr, hs, ht, hacc, hcost, hclock⟩ :=
    h 1 0 (fun _ => (1 : ℚ)) 1 1 (by norm_num) (by norm_num) (by norm_num)

  have hcost' : 7 ≤ t := by
    have h1 : (ratBits (1 : ℚ)).length = 7 := by decide
    simpa [Fin.sum_univ_one, h1] using hcost

  have hclock' : t ≤ 1 := by simpa using hclock
  omega

/-- Counts the initial consecutive `true` bits, stopping at the first `false` bit or the end of
the list. -/
def countLeadingTrue : List Bool → ℕ
  | true :: rest => countLeadingTrue rest + 1
  | _ => 0

/-- Prepending `k` copies of `true` increases `countLeadingTrue` by exactly `k`. -/
theorem countLeadingTrue_replicate_true (k : ℕ) (l : List Bool) :
    countLeadingTrue (List.replicate k true ++ l) = k + countLeadingTrue l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, countLeadingTrue, ih]
    omega

/-- The number of leading `true` bits in `natBits n` is the length of the binary digit list
`n.bits`. -/
theorem countLeadingTrue_natBits (n : ℕ) :
    countLeadingTrue (natBits n) = n.bits.length := by
  show countLeadingTrue ((List.replicate n.bits.length true ++ [false]) ++ n.bits) = _
  rw [List.append_assoc, countLeadingTrue_replicate_true]
  rfl

/-- Appending `natBits y` does not change the leading-`true` count of `natBits x`, which is
`x.bits.length`. -/
theorem countLeadingTrue_natBits_append (x y : ℕ) :
    countLeadingTrue (natBits x ++ natBits y) = x.bits.length := by
  show countLeadingTrue
      (((List.replicate x.bits.length true ++ [false]) ++ x.bits) ++ natBits y) = _
  rw [List.append_assoc, List.append_assoc, countLeadingTrue_replicate_true]
  rfl

/-- The self-delimiting encoding `natBits n` has length `2 * n.bits.length + 1`. -/
theorem natBits_length (n : ℕ) : (natBits n).length = 2 * n.bits.length + 1 := by
  simp [natBits, List.length_append, List.length_replicate]
  omega

/-- The binary digit representation `Nat.bits` is injective. -/
theorem bits_injective : Function.Injective Nat.bits := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

/-- Equality of the Boolean tests for negativity implies that the two integers are negative
under exactly the same condition. -/
theorem sign_iff_of_decide {a b : ℤ} (h : decide (a < 0) = decide (b < 0)) :
    (a < 0) ↔ (b < 0) := by
  constructor <;> intro h'
  · apply of_decide_eq_true
    rw [← h]
    exact decide_eq_true h'
  · apply of_decide_eq_true
    rw [h]
    exact decide_eq_true h'

/-- The self-delimiting natural-number encoding `natBits` is injective. -/
theorem natBits_injective : Function.Injective natBits := by
  intro a b h
  have hlen : (natBits a).length = (natBits b).length := congrArg List.length h
  have hk : a.bits.length = b.bits.length := by
    rw [natBits_length, natBits_length] at hlen
    omega
  have hbits : a.bits = b.bits := by
    have ha : natBits a = (List.replicate a.bits.length true ++ [false]) ++ a.bits := rfl
    have hb : natBits b = (List.replicate a.bits.length true ++ [false]) ++ b.bits := by
      have h0 : natBits b = (List.replicate b.bits.length true ++ [false]) ++ b.bits := rfl
      rw [h0, ← hk]
    rw [ha, hb] at h
    exact List.append_cancel_left h
  exact bits_injective hbits

/-- The signed integer encoding `intBits` is injective. -/
theorem intBits_injective : Function.Injective intBits := by
  intro a b h
  have hsign : decide (a < 0) = decide (b < 0) := List.cons.inj h |>.1
  have habs : natBits a.natAbs = natBits b.natAbs := List.cons.inj h |>.2
  have hab : a.natAbs = b.natAbs := natBits_injective habs
  have hlt : (a < 0) ↔ (b < 0) := sign_iff_of_decide hsign
  by_cases ha : a < 0
  · have hb : b < 0 := hlt.1 ha
    have e1 : ((a.natAbs : ℕ) : ℤ) = -a := by
      have := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -a from by omega)
      rw [Int.natAbs_neg] at this
      omega
    have e2 : ((b.natAbs : ℕ) : ℤ) = -b := by
      have := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -b from by omega)
      rw [Int.natAbs_neg] at this
      omega
    rw [← neg_inj, ← e1, ← e2, hab]
  · have hb : ¬ b < 0 := fun h' => ha (hlt.2 h')
    have e1 : ((a.natAbs : ℕ) : ℤ) = a := Int.natAbs_of_nonneg (by omega)
    have e2 : ((b.natAbs : ℕ) : ℤ) = b := Int.natAbs_of_nonneg (by omega)
    rw [← e1, ← e2, hab]

/-- The rational encoding `ratBits` is injective, as its sign and self-delimiting numerator and
denominator encodings determine the rational. -/
theorem ratBits_injective : Function.Injective ratBits := by
  intro a b h
  have hsign : decide (a.num < 0) = decide (b.num < 0) := List.cons.inj h |>.1
  have hrest : natBits a.num.natAbs ++ natBits a.den = natBits b.num.natAbs ++ natBits b.den :=
    List.cons.inj h |>.2
  have hk : a.num.natAbs.bits.length = b.num.natAbs.bits.length := by
    have := congrArg countLeadingTrue hrest
    rwa [countLeadingTrue_natBits_append, countLeadingTrue_natBits_append] at this

  have hnum : natBits a.num.natAbs = natBits b.num.natAbs := by
    have la := natBits_length a.num.natAbs
    have lb := natBits_length b.num.natAbs
    have takeA : (natBits a.num.natAbs ++ natBits a.den).take (2 * a.num.natAbs.bits.length + 1)
        = natBits a.num.natAbs := by
      rw [List.take_append_of_le_length (show 2 * a.num.natAbs.bits.length + 1 ≤
          (natBits a.num.natAbs).length by omega)]
      exact List.take_of_length_le (show (natBits a.num.natAbs).length ≤
        2 * a.num.natAbs.bits.length + 1 by omega)
    have takeB : (natBits b.num.natAbs ++ natBits b.den).take (2 * b.num.natAbs.bits.length + 1)
        = natBits b.num.natAbs := by
      rw [List.take_append_of_le_length (show 2 * b.num.natAbs.bits.length + 1 ≤
          (natBits b.num.natAbs).length by omega)]
      exact List.take_of_length_le (show (natBits b.num.natAbs).length ≤
        2 * b.num.natAbs.bits.length + 1 by omega)
    rw [← takeA, ← takeB, hrest, hk]
  have hden : natBits a.den = natBits b.den :=
    List.append_cancel_left (by rw [← hrest, hnum])
  have hnum' : a.num = b.num := by
    have habs : a.num.natAbs = b.num.natAbs := natBits_injective hnum
    have hlt : (a.num < 0) ↔ (b.num < 0) := sign_iff_of_decide hsign
    by_cases ha : a.num < 0
    · have hb : b.num < 0 := hlt.1 ha
      have e1 : ((a.num.natAbs : ℕ) : ℤ) = -a.num := by
        have := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -a.num from by omega)
        rw [Int.natAbs_neg] at this
        omega
      have e2 : ((b.num.natAbs : ℕ) : ℤ) = -b.num := by
        have := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -b.num from by omega)
        rw [Int.natAbs_neg] at this
        omega
      rw [← neg_inj, ← e1, ← e2, habs]
    · have hb : ¬ b.num < 0 := fun h' => ha (hlt.2 h')
      have e1 : ((a.num.natAbs : ℕ) : ℤ) = a.num := Int.natAbs_of_nonneg (by omega)
      have e2 : ((b.num.natAbs : ℕ) : ℤ) = b.num := Int.natAbs_of_nonneg (by omega)
      rw [← e1, ← e2, habs]
  exact Rat.ext hnum' (natBits_injective hden)

/-- Applies a single TM0 movement or write instruction directly to a tape. -/
def stmtApply : Turing.TM0.Stmt (Option Bool) → Turing.Tape (Option Bool) →
    Turing.Tape (Option Bool)
  | .move d, T => T.move d
  | .write a, T => T.write a

/-- Executes a list of TM0 tape instructions in order by folding `stmtApply` from the initial
tape. -/
def scriptApply (script : List (Turing.TM0.Stmt (Option Bool)))
    (T : Turing.Tape (Option Bool)) : Turing.Tape (Option Bool) :=
  script.foldl (fun T s => stmtApply s T) T

/-- Executing the empty tape script leaves the tape unchanged. -/
theorem scriptApply_nil (T : Turing.Tape (Option Bool)) : scriptApply [] T = T := rfl

/-- Executing a nonempty script applies its first instruction and then executes the remaining
instructions. -/
theorem scriptApply_cons (s : Turing.TM0.Stmt (Option Bool))
    (ss : List (Turing.TM0.Stmt (Option Bool))) (T : Turing.Tape (Option Bool)) :
    scriptApply (s :: ss) T = scriptApply ss (stmtApply s T) := rfl

/-- Executing concatenated scripts is equivalent to executing the first script and then the
second. -/
theorem scriptApply_append (s₁ s₂ : List (Turing.TM0.Stmt (Option Bool)))
    (T : Turing.Tape (Option Bool)) :
    scriptApply (s₁ ++ s₂) T = scriptApply s₂ (scriptApply s₁ T) := by
  induction s₁ generalizing T with
  | nil => rfl
  | cons s ss ih =>
    rw [List.cons_append, scriptApply_cons, scriptApply_cons, ih]

/-- Moving right on a tape built by `mk₂` transfers the current cell to the front of the left
list and removes it from the right list. Empty lists supply the blank default through
`headI`. -/
theorem move_right_mk₂ (Lv Rv : List (Option Bool)) :
    (Turing.Tape.mk₂ Lv Rv).move Turing.Dir.right =
      Turing.Tape.mk₂ (Rv.headI :: Lv) Rv.tail := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.move, Turing.ListBlank.head_mk,
    Turing.ListBlank.cons_mk, Turing.ListBlank.tail_mk]

/-- Moving left on a tape built by `mk₂` uses the head of the left list as the new current cell
and places the former current cell immediately to its right. -/
theorem move_left_mk₂ (Lv Rv : List (Option Bool)) :
    (Turing.Tape.mk₂ Lv Rv).move Turing.Dir.left =
      Turing.Tape.mk₂ Lv.tail (Lv.headI :: Rv.headI :: Rv.tail) := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.move, Turing.ListBlank.head_mk,
    Turing.ListBlank.cons_mk, Turing.ListBlank.tail_mk]

/-- Writing a symbol on a tape built by `mk₂` replaces the head of the right list while
preserving the left list and the remaining right cells. -/
theorem write_mk₂ (Lv Rv : List (Option Bool)) (b : Option Bool) :
    (Turing.Tape.mk₂ Lv Rv).write b = Turing.Tape.mk₂ Lv (b :: Rv.tail) := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]

/-- The current-and-right portion of `Turing.Tape.mk₂ Lv Rv` is the blank-padded list
represented by `Rv`. -/
theorem right₀_mk₂ (Lv Rv : List (Option Bool)) :
    (Turing.Tape.mk₂ Lv Rv).right₀ = Turing.ListBlank.mk Rv := by
  show (Turing.Tape.mk' (Turing.ListBlank.mk Lv) (Turing.ListBlank.mk Rv)).right₀ =
    Turing.ListBlank.mk Rv
  rw [Turing.Tape.mk'_right₀]

/-- A tape whose current-and-right cells contain the encoded bits of `w` satisfies `RatOnTape`
for `w`, independently of its control state and left cells. -/
theorem ratOnTape_mk₂ {Λ : Type} [Inhabited Λ] (st : Λ) (xs : List (Option Bool))
    (w : ℚ) :
    RatOnTape ⟨st, Turing.Tape.mk₂ xs ((ratBits w).map some)⟩ w := by
  intro i
  rw [right₀_mk₂, Turing.ListBlank.nth_mk]
  show ((ratBits w).map some).getI i = tapeAt (ratBits w) i
  rfl

/-- Builds a script that writes a fixed Boolean word to blank current-and-right cells and
returns the head to its starting position. The empty word uses no instructions. -/
def constOutScript : List Bool → List (Turing.TM0.Stmt (Option Bool))
  | [] => []
  | [b] => [Turing.TM0.Stmt.write (some b)]
  | b :: b' :: rest =>
      Turing.TM0.Stmt.write (some b) :: Turing.TM0.Stmt.move Turing.Dir.right ::
        constOutScript (b' :: rest) ++ [Turing.TM0.Stmt.move Turing.Dir.left]

/-- Executing `constOutScript W` with blank current-and-right cells writes `W` there, preserves
the left cells, and restores the original head position. -/
theorem scriptApply_constOutScript (W : List Bool) :
    ∀ (Lv : List (Option Bool)),
      scriptApply (constOutScript W) (Turing.Tape.mk₂ Lv []) =
        Turing.Tape.mk₂ Lv ((W.map some)) := by
  induction W with
  | nil => intro Lv; rfl
  | cons b W ih =>
    rcases W with _ | ⟨b', rest⟩
    · intro Lv
      show scriptApply [Turing.TM0.Stmt.write (some b)] (Turing.Tape.mk₂ Lv []) =
        Turing.Tape.mk₂ Lv [some b]
      rfl
    · intro Lv
      have hform : constOutScript (b :: b' :: rest) =
          (Turing.TM0.Stmt.write (some b) :: Turing.TM0.Stmt.move Turing.Dir.right ::
            constOutScript (b' :: rest)) ++ [Turing.TM0.Stmt.move Turing.Dir.left] := rfl
      rw [hform, scriptApply_append]
      show scriptApply [Turing.TM0.Stmt.move Turing.Dir.left]
          (scriptApply
            (Turing.TM0.Stmt.write (some b) :: Turing.TM0.Stmt.move Turing.Dir.right ::
              constOutScript (b' :: rest))
            (Turing.Tape.mk₂ Lv [])) = _
      rw [scriptApply_cons, scriptApply_cons]
      show scriptApply [Turing.TM0.Stmt.move Turing.Dir.left]
          (scriptApply (constOutScript (b' :: rest))
            (Turing.Tape.mk₂ (some b :: Lv) [])) = _
      rw [ih]
      show scriptApply [Turing.TM0.Stmt.move Turing.Dir.left]
          (Turing.Tape.mk₂ (some b :: Lv) (List.map some (b' :: rest))) = _
      rw [scriptApply_cons, scriptApply_nil]
      show (Turing.Tape.mk₂ (some b :: Lv) (List.map some (b' :: rest))).move
          Turing.Dir.left = _
      rw [move_left_mk₂]
      rfl

/-- Constructs a finite-state TM0 machine that scans right to the first blank, runs
`constOutScript W`, and halts. State zero performs the scan, the following states execute
the script, and the final state stops. -/
def constOutMachine (W : List Bool) :
    Turing.TM0.Machine (Option Bool) (Fin ((constOutScript W).length + 2)) :=
  fun s g =>
    if _hs : s.val = 0 then
      match g with
      | some _ => some (⟨0, by omega⟩, Turing.TM0.Stmt.move Turing.Dir.right)
      | none => some (⟨1, by omega⟩, Turing.TM0.Stmt.write g)
    else if _hscript : s.val ≤ (constOutScript W).length then
      some ((if _hlast : s.val = (constOutScript W).length then
          ⟨(constOutScript W).length + 1, by omega⟩
        else ⟨s.val + 1, by omega⟩),
        (constOutScript W).getD (s.val - 1) (Turing.TM0.Stmt.write none))
    else
      none

/-- In state zero, `constOutMachine W` moves right past a nonblank bit. On a blank it writes
that blank unchanged and enters state one. -/
theorem constOutMachine_scan (W : List Bool) (g : Option Bool) :
    constOutMachine W ⟨0, by omega⟩ g =
      match g with
      | some _ => some (⟨0, by omega⟩, Turing.TM0.Stmt.move Turing.Dir.right)
      | none => some (⟨1, by omega⟩, Turing.TM0.Stmt.write g) := rfl

/-- In script state `i + 1`, the constant-output machine executes instruction `i` and advances
to the next state, using the final halting state after the last instruction. -/
theorem constOutMachine_script (W : List Bool) {i : ℕ}
    (hi : i < (constOutScript W).length) (g : Option Bool) :
    constOutMachine W ⟨i + 1, by omega⟩ g =
      some ((if i + 1 = (constOutScript W).length then
          ⟨(constOutScript W).length + 1, by omega⟩
        else ⟨i + 2, by omega⟩),
        (constOutScript W).getD i (Turing.TM0.Stmt.write none)) := by
  have h0 : ¬ (i + 1 : ℕ) = 0 := by omega
  have hi' : (i + 1 : ℕ) ≤ (constOutScript W).length := by omega
  simp [constOutMachine, h0, hi']

/-- The final state of `constOutMachine W` has no outgoing transition, regardless of the current
tape symbol. -/
theorem constOutMachine_halt (W : List Bool) (g : Option Bool) :
    constOutMachine W ⟨(constOutScript W).length + 1, by omega⟩ g = none := by
  have h0 : ¬ ((constOutScript W).length + 1 : ℕ) = 0 := by omega
  have h1 : ¬ ((constOutScript W).length + 1 : ℕ) ≤ (constOutScript W).length := by omega
  simp [constOutMachine, h0, h1]

/-- A machine transition returning state `q'` and instruction `st` yields the configuration with
state `q'` and tape `stmtApply st T`. -/
theorem step_of_eq {m : ℕ} [Inhabited (Fin m)]
    (M : Turing.TM0.Machine (Option Bool) (Fin m)) (q : Fin m)
    (T : Turing.Tape (Option Bool)) {q' : Fin m} {st : Turing.TM0.Stmt (Option Bool)}
    (h : M q T.1 = some (q', st)) :
    Turing.TM0.step M ⟨q, T⟩ = some ⟨q', stmtApply st T⟩ := by
  simp only [Turing.TM0.step]
  rw [h]
  cases st with
  | move d => rfl
  | write g => rfl

/-- If the machine has no transition for the current state and tape symbol, the configuration
has no next TM0 step. -/
theorem step_none_of_eq {m : ℕ} [Inhabited (Fin m)]
    (M : Turing.TM0.Machine (Option Bool) (Fin m)) (q : Fin m)
    (T : Turing.Tape (Option Bool)) (h : M q T.1 = none) :
    Turing.TM0.step M ⟨q, T⟩ = none := by
  simp only [Turing.TM0.step]
  rw [h]
  rfl

/-- On input `natBits k`, the constant-output machine reaches its halting state after `(natBits
k).length + 1 + (constOutScript W).length` steps. Its head then points to the start of the
output region containing `W`, with the original input preserved to the left. -/
theorem constOut_halts (W : List Bool) (k : ℕ) :
    BitMachineAfter (constOutMachine W) ((natBits k).map some)
        ((natBits k).length + 1 + (constOutScript W).length) =
      some ⟨⟨(constOutScript W).length + 1, by omega⟩,
        Turing.Tape.mk₂ ((natBits k).map some).reverse (W.map some)⟩ ∧
      Turing.TM0.step (constOutMachine W)
          ⟨⟨(constOutScript W).length + 1, by omega⟩,
            Turing.Tape.mk₂ ((natBits k).map some).reverse (W.map some)⟩ = none := by
  have hscan : ∀ j ≤ (natBits k).length,
      BitMachineAfter (constOutMachine W) ((natBits k).map some) j =
        some ⟨⟨0, by omega⟩,
          Turing.Tape.mk₂ (((natBits k).take j).map some |>.reverse)
            ((natBits k).drop j |>.map some)⟩ := by
    intro j
    induction j with
    | zero =>
      intro _
      show BitMachineAfter (constOutMachine W) ((natBits k).map some) 0 = some _
      rfl
    | succ j ih =>
      intro hj
      have hj' : j < (natBits k).length := by omega
      have hdropj : (natBits k).drop j = (natBits k)[j] :: (natBits k).drop (j + 1) :=
        List.drop_eq_getElem_cons hj'
      have hhead : (Turing.Tape.mk₂ (((natBits k).take j).map some |>.reverse)
          ((natBits k).drop j |>.map some)).1 = some (natBits k)[j] := by
        show ((natBits k).drop j |>.map some).headI = _
        rw [hdropj, List.map_cons]
        rfl
      have hcall : constOutMachine W ⟨0, by omega⟩
          ((Turing.Tape.mk₂ (((natBits k).take j).map some |>.reverse)
            ((natBits k).drop j |>.map some)).1) =
          some (⟨0, by omega⟩, Turing.TM0.Stmt.move Turing.Dir.right) := by
        rw [hhead, constOutMachine_scan]
      have htape : (Turing.Tape.mk₂ (((natBits k).take j).map some |>.reverse)
            ((natBits k).drop j |>.map some)).move Turing.Dir.right =
          Turing.Tape.mk₂ (((natBits k).take (j + 1)).map some |>.reverse)
            ((natBits k).drop (j + 1) |>.map some) := by
        rw [move_right_mk₂, hdropj, List.map_cons, List.tail_cons]
        rw [List.take_succ_eq_append_getElem hj', List.map_append, List.reverse_append]
        rfl
      have hstep : Turing.TM0.step (constOutMachine W)
          ⟨⟨0, by omega⟩,
            Turing.Tape.mk₂ (((natBits k).take j).map some |>.reverse)
              ((natBits k).drop j |>.map some)⟩ =
          some ⟨⟨0, by omega⟩,
            Turing.Tape.mk₂ (((natBits k).take (j + 1)).map some |>.reverse)
              ((natBits k).drop (j + 1) |>.map some)⟩ := by
        rw [step_of_eq (constOutMachine W) _ _ hcall]
        exact congrArg (fun T : Turing.Tape (Option Bool) =>
          (some (⟨⟨0, by omega⟩, T⟩) :
            Option (Turing.TM0.Cfg (Option Bool) (Fin ((constOutScript W).length + 2))))) htape
      have h1 : BitMachineAfter (constOutMachine W) ((natBits k).map some) (j + 1) =
          (BitMachineAfter (constOutMachine W) ((natBits k).map some) j).bind
            (Turing.TM0.step (constOutMachine W)) := rfl
      rw [h1, ih (by omega), Option.bind_some, hstep]
  have hlast := hscan (natBits k).length (le_refl _)
  have hdrop : (natBits k).drop (natBits k).length = [] := List.drop_length
  have htake : (natBits k).take (natBits k).length = natBits k := List.take_of_length_le (le_refl _)
  have hblank : Turing.Tape.mk₂ (((natBits k).take (natBits k).length).map some |>.reverse)
        (((natBits k).drop (natBits k).length).map some) =
      Turing.Tape.mk₂ ((natBits k).map some).reverse [] := by
    rw [htake, hdrop]
    rfl

  have hswitch : Turing.TM0.step (constOutMachine W)
      ⟨⟨0, by omega⟩,
        Turing.Tape.mk₂ ((natBits k).map some).reverse []⟩ =
      some ⟨⟨1, by omega⟩, Turing.Tape.mk₂ ((natBits k).map some).reverse []⟩ := by
    have hhead : (Turing.Tape.mk₂ ((natBits k).map some).reverse ([] : List (Option Bool))).1
        = (none : Option Bool) := rfl
    have hcall : constOutMachine W ⟨0, by omega⟩
        ((Turing.Tape.mk₂ ((natBits k).map some).reverse ([] : List (Option Bool))).1) =
        some (⟨1, by omega⟩, Turing.TM0.Stmt.write (none : Option Bool)) := by
      rw [hhead, constOutMachine_scan]
    rw [step_of_eq (constOutMachine W) _ _ hcall]
    rfl
  have hscript : ∀ i (hi : i ≤ (constOutScript W).length),
      BitMachineAfter (constOutMachine W) ((natBits k).map some) ((natBits k).length + 1 + i) =
        some ⟨⟨i + 1, by omega⟩,
          scriptApply ((constOutScript W).take i)
            (Turing.Tape.mk₂ ((natBits k).map some).reverse [])⟩ := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 : BitMachineAfter (constOutMachine W) ((natBits k).map some)
          ((natBits k).length + 1) =
          (BitMachineAfter (constOutMachine W) ((natBits k).map some) ((natBits k).length)).bind
            (Turing.TM0.step (constOutMachine W)) := rfl
      rw [h0, hlast, hblank, Option.bind_some, hswitch]
      rfl
    | succ i ih =>
      intro hi
      have hi' : i < (constOutScript W).length := by omega
      have h1 : BitMachineAfter (constOutMachine W) ((natBits k).map some)
          ((natBits k).length + 1 + (i + 1)) =
          (BitMachineAfter (constOutMachine W) ((natBits k).map some)
            ((natBits k).length + 1 + i)).bind (Turing.TM0.step (constOutMachine W)) := rfl
      rw [h1, ih (by omega), Option.bind_some]
      have hget : ((constOutScript W).take (i + 1)) =
          ((constOutScript W).take i) ++ [(constOutScript W)[i]] := by
        rw [List.take_succ_eq_append_getElem hi']
      have hstep : Turing.TM0.step (constOutMachine W)
          ⟨⟨i + 1, by omega⟩,
            scriptApply ((constOutScript W).take i)
              (Turing.Tape.mk₂ ((natBits k).map some).reverse [])⟩ =
          some ⟨⟨i + 2, by omega⟩,
            stmtApply ((constOutScript W)[i])
              (scriptApply ((constOutScript W).take i)
                (Turing.Tape.mk₂ ((natBits k).map some).reverse []))⟩ := by
        have hcall : constOutMachine W ⟨i + 1, by omega⟩
            ((scriptApply ((constOutScript W).take i)
              (Turing.Tape.mk₂ ((natBits k).map some).reverse [])).1) =
            some ((if i + 1 = (constOutScript W).length then
                  ⟨(constOutScript W).length + 1, by omega⟩
                else ⟨i + 2, by omega⟩),
              (constOutScript W).getD i (Turing.TM0.Stmt.write none)) :=
          constOutMachine_script W hi' _
        rw [step_of_eq (constOutMachine W) _ _ hcall]
        have hgetd : (constOutScript W).getD i (Turing.TM0.Stmt.write none) = (constOutScript W)[i] :=
          List.getD_eq_getElem _ _ hi'
        rw [hgetd]
        split_ifs with hlast'
        · have heq : (⟨(constOutScript W).length + 1, by omega⟩ :
            Fin ((constOutScript W).length + 2)) = ⟨i + 2, by omega⟩ := by
            apply Fin.eq_of_val_eq
            show (constOutScript W).length + 1 = i + 2
            omega
          rw [heq]
        · rfl
      rw [hstep, hget, scriptApply_append]
      rfl
  have hfinal := hscript (constOutScript W).length (le_refl _)
  have htakeScript : ((constOutScript W).take (constOutScript W).length) = constOutScript W :=
    List.take_of_length_le (le_refl _)
  refine ⟨?_, ?_⟩
  · rw [hfinal, htakeScript, scriptApply_constOutScript]
  · exact step_none_of_eq (constOutMachine W) _ _ (constOutMachine_halt W _)

/-- Packages the constant-output machine for `W` as a `FiniteRealInput`, with declared size zero
and state bound `(constOutScript W).length + 1`. -/
def constOutInput (W : List Bool) : FiniteRealInput where
  states := (constOutScript W).length + 1
  approx := constOutMachine W
  size := 0

/-- The finite input that always outputs `ratBits q` certifies the real value of the rational
`q` at every requested precision. -/
theorem certifiesConst (q : ℚ) :
    CertifiesApproximation (constOutInput (ratBits q)) (q : ℝ) := by
  intro k
  obtain ⟨hrun, hstop⟩ := constOut_halts (ratBits q) k
  refine ⟨(natBits k).length + 1 + (constOutScript (ratBits q)).length, q, _, hrun, hstop,
    ratOnTape_mk₂ _ ((natBits k).map some).reverse q, ?_⟩
  show |((q : ℚ) : ℝ) - (q : ℝ)| ≤ ((2 : ℝ)⁻¹) ^ k
  rw [sub_self, abs_zero]
  exact pow_nonneg (by norm_num) k

/-- Refutes `OffGridQPEConsumer r` for every backend run. Two certified constant inputs of
declared size zero produce the same machine input but demand incompatible approximations to
zero and two. -/
theorem offGridQPEConsumer_refutable (r : BackendRun) : ¬ OffGridQPEConsumer r := by
  intro h

  have h0 := h 16 (by norm_num) (constOutInput (ratBits 0)) ((0 : ℚ) : ℝ) 0 (0 : ℚ)
    (certifiesConst 0) (by norm_num)
  have h2 := h 16 (by norm_num) (constOutInput (ratBits 2)) ((2 : ℚ) : ℝ) 0 (0 : ℚ)
    (certifiesConst 2) (by norm_num)
  obtain ⟨t0, q0, cfg0, hr0, hs0, hrat0, hacc0, -, -⟩ := h0
  obtain ⟨t2, q2, cfg2, hr2, hs2, hrat2, hacc2, -, -⟩ := h2

  have hcfg : cfg0 = cfg2 :=
    bitMachineAfter_halt_unique r.machine
      ((natBits 16 ++ natBits 0 ++ ratBits 0 ++ natBits 0).map some) hr0 hs0 hr2 hs2
  subst hcfg

  have hq : q0 = q2 := by
    apply ratBits_injective
    apply tapeAt_ext
    intro i
    exact (hrat0 i).symm.trans (hrat2 i)
  subst hq

  have hwin : (2 : ℝ) * Real.pi / (16 : ℝ) + ((0 : ℚ) : ℝ) * ((2 : ℝ)⁻¹) ^ (0 : ℕ) ≤ 1 / 2 := by
    have hpow : ((2 : ℝ)⁻¹) ^ (0 : ℕ) = 1 := pow_zero _
    rw [hpow, mul_one, Rat.cast_zero, add_zero]
    have h16 : (0 : ℝ) < 16 := by norm_num
    rw [div_le_iff₀ h16]
    have h : (2 : ℝ) * Real.pi ≤ 8 := by linarith [Real.pi_le_four]
    have heq : (1 / 2 : ℝ) * 16 = 8 := by norm_num
    linarith
  have h0s : |((q0 : ℚ) : ℝ) - ((0 : ℚ) : ℝ)| ≤ 1 / 2 := le_trans hacc0 hwin
  have h2s : |((q0 : ℚ) : ℝ) - ((2 : ℚ) : ℝ)| ≤ 1 / 2 := le_trans hacc2 hwin
  rw [abs_le] at h0s h2s
  push_cast at h0s h2s
  norm_num at h0s h2s
  linarith

/-- Combines numerical-kind completeness, a precision chooser with realization, cost, and error
guarantees, the QPE, HHL, and LCU consumer requirements, input-reading charges, and
computable-input restrictions. -/
def clause44Body : Prop :=
  NumericalKindsComplete ∧
  (∃ (chooser : PrecisionChoice) (C D : ℕ),
    ∀ (inst : SameWordInstance),
      ∃ (r : BackendRun) (t : ℕ),
        RunRealizes r inst (chooser (paramsOf inst)) ∧
        BackendCostOk inst (chooser (paramsOf inst)) t C D ∧
        (0 < inst.ε → amplifiedWordError inst (chooser (paramsOf inst)) ≤ inst.ε)) ∧
  (∃ r : BackendRun, OffGridQPEConsumer r) ∧
  (∃ r : BackendRun, RationalHHLConsumer r) ∧
  (∃ r : BackendRun, RationalLCUConsumer r) ∧
  InputReadCostCharged ∧
  NoExactRealOracle

/-- Refutes `clause44Body` because its required rational HHL consumer cannot exist. -/
theorem clause44Body_refutable : ¬ clause44Body := by
  rintro ⟨_, _, _, ⟨r, hr⟩, _, _⟩
  exact rationalHHLConsumer_refutable r hr

/-- Every oracle instruction in a legal program under a well-formed contract uses a supplied
access form with an available implementation. -/
theorem accessRestrictionPreserved : AccessRestrictionPreserved := by
  intro w L p c hwf hleg s hs
  cases s with
  | oracle slot form addr val =>
    have hsup : c.supplied slot form = true := hleg _ hs
    exact ⟨hsup, by rw [hwf slot form]; exact hsup⟩
  | fairCoin dst => trivial
  | arith code ws => trivial
  | emit src => trivial

/-- Defines a one-register, one-slot program that queries slot zero in forward form and emits
the resulting register value. -/
def clause45AmbProgram : ProbProgram 1 1 :=
  { steps := [ProbInstr.oracle 0 .forward 0 0, ProbInstr.emit 0] }

/-- Defines a one-slot access contract supplying every access form, with each implementation
returning the fixed natural number `v`. -/
def clause45AmbContract (v : ℕ) : AccessContract 1 where
  supplied := fun _ _ => true
  impl := fun _ _ => some (fun _ => v)

/-- The constant-valued ambiguity contract is well formed for every `v`. -/
theorem clause45Amb_wellFormed (v : ℕ) : (clause45AmbContract v).WellFormed := by
  intro s f
  rfl

/-- The ambiguity program is legal under every constant-valued ambiguity contract. -/
theorem clause45Amb_legal (v : ℕ) : clause45AmbProgram.LegalFor (clause45AmbContract v) := by
  intro s hs
  have hs' : s = ProbInstr.oracle 0 .forward 0 0 ∨ s = ProbInstr.emit 0 := by
    simpa [clause45AmbProgram] using hs
  rcases hs' with rfl | rfl
  · show (clause45AmbContract v).supplied 0 .forward = true
    rfl
  · trivial

/-- Under the constant-zero contract and an empty coin record, the ambiguity program outputs
`[0]`. -/
theorem clause45Amb_runProb_zero :
    (runProb (clause45AmbContract 0) clause45AmbProgram []).out = [0] := by
  rfl

/-- Under the constant-one contract and an empty coin record, the ambiguity program outputs
`[1]`. -/
theorem clause45Amb_runProb_one :
    (runProb (clause45AmbContract 1) clause45AmbProgram []).out = [1] := by
  rfl

/-- Refutes the existence of fixed TM0 and TM2 compilers satisfying the stated compilation,
probability-law, and polynomial cost guarantees for every well-formed legal contract. The
same encoded program and coin record require different TM0 outputs under the constant-zero
and constant-one contracts. -/
theorem tm0Compiled_contract_ambiguity :
    ¬ (∃ (comp0 : ProbTM0Compiler) (comp2 : ProbTM2Compiler) (C D : ℕ),
      ∀ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L),
        c.WellFormed →
        p.LegalFor c →
        ∃ (clock space : ℕ),
          TM0Compiled comp0 c p clock space ∧
          TM2Compiled comp2 c p clock space ∧
          TM0LawPreserved comp0 c p clock ∧
          TM2LawPreserved comp2 c p clock ∧
          clock ≤ C * (1 + (probProgramBits p).length + p.coins) ^ D + C ∧
          space ≤ C * (1 + (probProgramBits p).length + p.coins) ^ D + C) := by
  rintro ⟨comp0, comp2, C, D, hall⟩
  obtain ⟨clock0, space0, hcomp0, -, -, -, -⟩ := hall 1 1 clause45AmbProgram (clause45AmbContract 0)
    (clause45Amb_wellFormed 0) (clause45Amb_legal 0)
  obtain ⟨clock1, space1, hcomp1, -, -, -, -⟩ := hall 1 1 clause45AmbProgram (clause45AmbContract 1)
    (clause45Amb_wellFormed 1) (clause45Amb_legal 1)
  obtain ⟨t0, cfg0, hr0, hs0, -, -, htape0⟩ := hcomp0 [] rfl
  obtain ⟨t1, cfg1, hr1, hs1, -, -, htape1⟩ := hcomp1 [] rfl

  have hcfg : cfg0 = cfg1 :=
    bitMachineAfter_halt_unique comp0.machine
      ((probProgramBits clause45AmbProgram ++ ([] : List Bool)).map some) hr0 hs0 hr1 hs1
  subst hcfg
  rw [clause45Amb_runProb_zero] at htape0
  rw [clause45Amb_runProb_one] at htape1

  have e : tapeAt (natBits 0) 0 = tapeAt (natBits 1) 0 :=
    (htape0 0).symm.trans (htape1 0)
  exact absurd e (by decide)

/-- The self-delimiting encoding `natBits n` is nonempty for every natural number `n`. -/
theorem natBits_ne_nil (n : ℕ) : natBits n ≠ [] := by
  simp [natBits]

/-- Concatenating the `natBits` encodings of a list of natural numbers produces at least as many
bits as there are list entries. -/
theorem flatMap_natBits_length (ns : List ℕ) :
    ns.length ≤ (ns.flatMap natBits).length := by
  induction ns with
  | nil => simp
  | cons x l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have h1 : 1 ≤ (natBits x).length :=
      List.length_pos_iff_ne_nil.2 (natBits_ne_nil x)
    omega

/-- Every encoded probabilistic program has at least four bits, accounting for its four
mandatory natural-number header fields. -/
theorem probProgramBits_length {w L : ℕ} (p : ProbProgram w L) :
    4 ≤ (probProgramBits p).length := by
  have h : 4 ≤ ([w, L, p.steps.length, p.coins] ++
      p.steps.flatMap probInstrFields).length := by simp
  have h2 := flatMap_natBits_length
    ([w, L, p.steps.length, p.coins] ++ p.steps.flatMap probInstrFields)
  exact le_trans h h2

/-- The nonblank-cell count of a blank-padded list represented by `xs` is `blankCells xs`. -/
theorem blankUsedCells_mk (xs : List (Option Bool)) :
    blankUsedCells (Turing.ListBlank.mk xs) = blankCells xs :=
  rfl

/-- Filtering out blank symbols from `l.map some` leaves the list unchanged. -/
theorem filter_some (l : List Bool) :
    (l.map some).filter (fun x => x ≠ none) = l.map some := by
  refine List.filter_eq_self.2 ?_
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
  simp

/-- Embedding a Boolean word with `some` gives exactly one nonblank cell per bit. -/
theorem blankCells_map_some (l : List Bool) :
    blankCells (l.map some) = l.length := by
  unfold blankCells
  rw [filter_some, List.length_map]

/-- The space of an initial tape built from `xs` is one current cell plus the number of nonblank
cells in `xs.tail`. -/
theorem tapeSpace_mk₁ (xs : List (Option Bool)) :
    tapeSpace (Turing.Tape.mk₁ xs) = 1 + blankCells xs.tail := by
  unfold tapeSpace
  have hl : (Turing.Tape.mk₁ xs).left = Turing.ListBlank.mk [] := rfl
  have hr : (Turing.Tape.mk₁ xs).right = Turing.ListBlank.mk xs.tail := rfl
  rw [hl, hr, blankUsedCells_mk, blankUsedCells_mk]
  simp [blankCells]

/-- The initial tape for a Boolean word has space `max l.length 1`, counting the current cell
even when the word is empty. -/
theorem tapeSpace_mk₁_map_some (l : List Bool) :
    tapeSpace (Turing.Tape.mk₁ (l.map some)) = max l.length 1 := by
  cases l with
  | nil => simp [tapeSpace_mk₁, blankCells]
  | cons a l =>
    rw [tapeSpace_mk₁, List.map_cons, List.tail_cons, blankCells_map_some,
      List.length_cons]
    omega

/-- A left fold taking maxima bounds both its initial accumulator and every value `f v`
contributed by an element of the folded list. -/
theorem le_foldl_max (f : ℕ → ℕ) :
    ∀ (a : ℕ) (l : List ℕ),
      a ≤ l.foldl (fun acc s => max acc (f s)) a ∧
        ∀ v ∈ l, f v ≤ l.foldl (fun acc s => max acc (f s)) a := by
  intro a l
  induction l generalizing a with
  | nil => exact ⟨le_refl _, fun v hv => absurd hv List.not_mem_nil⟩
  | cons x l ih =>
    have hfold : (x :: l).foldl (fun acc s => max acc (f s)) a
        = l.foldl (fun acc s => max acc (f s)) (max a (f x)) := rfl
    rw [hfold]
    obtain ⟨hge, hmem⟩ := ih (max a (f x))
    refine ⟨le_trans (le_max_left a (f x)) hge, ?_⟩
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact le_trans (le_max_right a (f _)) hge
    · exact hmem v hv

/-- The peak tape space through any time `t` is at least the space occupied by the initial input
tape. -/
theorem peakSpaceAfter_ge_init {Λ : Type} [Inhabited Λ]
    (M : Turing.TM0.Machine (Option Bool) Λ) :
    ∀ (input : List (Option Bool)) (t : ℕ),
      tapeSpace (Turing.Tape.mk₁ input) ≤ peakSpaceAfter M input t := by
  intro input t
  have hmem : (0 : ℕ) ∈ List.range (t + 1) := List.mem_range.2 (Nat.succ_pos t)
  obtain ⟨_, hle⟩ := le_foldl_max (fun s => (BitMachineAfter M input s).elim 0 cfgSpace)
    0 (List.range (t + 1))
  have := hle 0 hmem
  simpa [peakSpaceAfter, BitMachineAfter, cfgSpace] using! this

/-- Any `TM0Compiled` space bound covers the full encoded program length plus the number of coin
bits in its input. -/
theorem tm0Compiled_space_le_input (comp0 : ProbTM0Compiler) {w L : ℕ}
    (c : AccessContract L) (p : ProbProgram w L) (clock space : ℕ)
    (h : TM0Compiled comp0 c p clock space) :
    (probProgramBits p).length + p.coins ≤ space := by
  obtain ⟨t, cfg, hr, hs, _, hpeak, _⟩ :=
    h (List.replicate p.coins false) (by simp)
  have hinit : tapeSpace (Turing.Tape.mk₁
        ((probProgramBits p ++ List.replicate p.coins false).map some)) ≤ space :=
    le_trans (peakSpaceAfter_ge_init comp0.machine _ t) hpeak
  have hlen := tapeSpace_mk₁_map_some
    (probProgramBits p ++ List.replicate p.coins false)
  have hcalc : (probProgramBits p ++ List.replicate p.coins false).length
      = (probProgramBits p).length + p.coins := by
    simp [List.length_replicate]
  have h4 : 1 ≤ (probProgramBits p).length + p.coins := by
    have := probProgramBits_length p
    omega
  rw [hcalc, max_eq_left h4] at hlen
  omega

/-- Refutes `QFTPostprocessConsumer comp0` for every TM0 compiler. At zero input width, its
space bound is one, whereas any encoded program already occupies at least four cells. -/
theorem qftPostprocessConsumer_refutable (comp0 : ProbTM0Compiler) :
    ¬ QFTPostprocessConsumer comp0 := by
  intro h
  obtain ⟨w, L, p, c, clock, space, -, -, hcomp, -, -, hclock, hspace⟩ :=
    h 0 (fun i => i.elim0)
  have hspace' : space ≤ 1 := by simpa using hspace
  have hsize : (probProgramBits p).length + p.coins ≤ space :=
    tm0Compiled_space_le_input comp0 c p clock space hcomp
  have hlen := probProgramBits_length p
  omega

/-- Refutes `SimonPostprocessConsumer comp0` for every TM0 compiler. The instance with zero rows
and columns allows only one space unit, below the mandatory encoded-program input size. -/
theorem simonPostprocessConsumer_refutable (comp0 : ProbTM0Compiler) :
    ¬ SimonPostprocessConsumer comp0 := by
  intro h
  obtain ⟨w, L, p, c, clock, space, -, -, hcomp, -, -, hclock, hspace⟩ :=
    h 0 0 (fun i => i.elim0) (fun i => i.elim0)
  have hspace' : space ≤ 1 := by simpa using hspace
  have hsize : (probProgramBits p).length + p.coins ≤ space :=
    tm0Compiled_space_le_input comp0 c p clock space hcomp
  have hlen := probProgramBits_length p
  omega

/-- A nonzero natural number has a nonempty binary digit list. -/
theorem bits_ne_nil_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.bits ≠ [] := by
  intro h
  apply hn
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h, Nat.zero_bits]

/-- Every self-delimiting natural-number encoding has length at least one. -/
theorem natBits_length_pos (n : ℕ) : 1 ≤ (natBits n).length := by
  rw [natBits_length]
  omega

/-- Tests whether a probabilistic instruction is an `emit` instruction. -/
def isEmit {w L : ℕ} : ProbInstr w L → Bool
  | .emit _ => true
  | _ => false

/-- A probabilistic instruction increases the output-list length by one exactly when it is an
`emit` instruction. -/
theorem probStep_out_length {w L : ℕ} (c : AccessContract L) (s : ProbState w)
    (i : ProbInstr w L) :
    (probStep c s i).out.length = s.out.length + (if isEmit i then 1 else 0) := by
  cases i with
  | fairCoin dst =>
    cases hc : s.coins with
    | nil => simp [probStep, isEmit, hc]
    | cons b rest => simp [probStep, isEmit, hc]
  | oracle slot form addr val =>
    cases hc : c.impl slot form with
    | none => simp [probStep, isEmit, hc]
    | some g => simp [probStep, isEmit, hc]
  | arith code ws => simp [probStep, isEmit]
  | emit src => simp [probStep, isEmit]

/-- Executing an instruction list adds exactly its number of `emit` instructions to the initial
output-list length. -/
theorem foldl_probStep_out_length {w L : ℕ} (c : AccessContract L) (s : ProbState w)
    (is : List (ProbInstr w L)) :
    (is.foldl (probStep c) s).out.length = s.out.length + (is.filter isEmit).length := by
  induction is generalizing s with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, probStep_out_length, List.filter_cons]
    cases hx : isEmit x <;> simp [hx] <;> omega

/-- The output length of a probabilistic program equals the number of `emit` instructions,
independently of the access contract and coin record. -/
theorem runProb_out_length {w L : ℕ} (c : AccessContract L) (p : ProbProgram w L)
    (record : List Bool) :
    (runProb c p record).out.length = (p.steps.filter isEmit).length := by
  have h := foldl_probStep_out_length c
    (show ProbState w from { regs := fun _ => 0, coins := record, out := [] }) p.steps
  simpa [runProb] using h

/-- Refutes `ShorPostprocessConsumer comp0` for every TM0 compiler. The zero-argument
modular-exponentiation instance must emit a value, forcing at least six encoded program bits
while its space bound allows at most four. -/
theorem shorPostprocessConsumer_refutable (comp0 : ProbTM0Compiler) :
    ¬ ShorPostprocessConsumer comp0 := by
  intro h
  obtain ⟨hmodexp, -⟩ := h
  obtain ⟨w, L, p, c, clock, space, hcoins, -, -, hcomp, -, hout, -, hspace⟩ :=
    hmodexp 0 0 0
  have hout1 : (runProb c p (List.replicate p.coins false)).out = [1] := by
    rw [hout _ (by simp), pow_zero, Nat.mod_zero]
  have hemit : (p.steps.filter isEmit).length = 1 := by
    rw [← runProb_out_length c p (List.replicate p.coins false), hout1]
    simp
  have hsteps : 1 ≤ p.steps.length :=
    List.length_pos_iff_ne_nil.2 (fun he => by simp [he] at hemit)
  have hbits : 3 ≤ (natBits p.steps.length).length := by
    rw [natBits_length]
    have hne : p.steps.length ≠ 0 := by omega
    have hpos : 1 ≤ p.steps.length.bits.length :=
      List.length_pos_iff_ne_nil.2 (bits_ne_nil_of_ne_zero hne)
    omega
  have hfour : 6 ≤ ([w, L, p.steps.length, p.coins].flatMap natBits).length := by
    have h1 : 1 ≤ (natBits w).length := natBits_length_pos w
    have h2 : 1 ≤ (natBits L).length := natBits_length_pos L
    have h4 : 1 ≤ (natBits p.coins).length := natBits_length_pos p.coins
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    omega
  have hlen : 6 ≤ (probProgramBits p).length := by
    show 6 ≤ (([w, L, p.steps.length, p.coins] ++
      p.steps.flatMap probInstrFields).flatMap natBits).length
    rw [List.flatMap_append, List.length_append]
    exact le_trans hfour (Nat.le_add_right _ _)
  have hspace' : space ≤ 4 := by
    have h0 : (natBits 0).length = 1 := by
      rw [natBits_length, Nat.zero_bits]
      simp
    rw [h0] at hspace
    omega
  have hsize := tm0Compiled_space_le_input comp0 c p clock space hcomp
  rw [hcoins] at hsize
  omega

/-- Combines uniform TM0 and TM2 compilation with probability-law preservation and polynomial
time and space bounds, the Shor, Simon, and QFT postprocessing consumers, and preservation
of access restrictions. -/
def clause45Body : Prop :=
  (∃ (comp0 : ProbTM0Compiler) (comp2 : ProbTM2Compiler) (C D : ℕ),
    ∀ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L),
      c.WellFormed →
      p.LegalFor c →
      ∃ (clock space : ℕ),
        TM0Compiled comp0 c p clock space ∧
        TM2Compiled comp2 c p clock space ∧
        TM0LawPreserved comp0 c p clock ∧
        TM2LawPreserved comp2 c p clock ∧
        clock ≤ C * (1 + (probProgramBits p).length + p.coins) ^ D + C ∧
        space ≤ C * (1 + (probProgramBits p).length + p.coins) ^ D + C) ∧
  (∃ comp0 : ProbTM0Compiler, ShorPostprocessConsumer comp0) ∧
  (∃ comp0 : ProbTM0Compiler, SimonPostprocessConsumer comp0) ∧
  (∃ comp0 : ProbTM0Compiler, QFTPostprocessConsumer comp0) ∧
  AccessRestrictionPreserved

/-- Refutes `clause45Body` using the contract ambiguity that prevents its uniform compilation
requirement. -/
theorem clause45Body_refutable : ¬ clause45Body := by
  rintro ⟨hall, _, _, _, _⟩
  exact tm0Compiled_contract_ambiguity hall

end Qatlib.Concepts.QueryComplexity.DegreeMethod
