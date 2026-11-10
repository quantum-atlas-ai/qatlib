/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionEffective
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator
open Qatlib.Concepts.ScaledSqrt.SqrtBounds
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain

open Qatlib
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue natBits framed Runs ComputesAt)
open Turing

namespace output2

def ratEnc (r : ℚ) : RatEnc := ⟨r.num, r.den, r.den_pos⟩

@[simp] theorem ratEnc_toRat (r : ℚ) : (ratEnc r).toRat = r := by
  simp [ratEnc, RatEnc.toRat, Rat.num_div_den]

def sqrtInterval (q S : ℚ) (k : ℕ) : ℚ × ℚ :=
  let b := Qatlib.Concepts.ScaledSqrt.SqrtBounds.bracket q S k
  (b.1, b.2.1)

def sqrtLo (q S : ℚ) (k : ℕ) : ℚ := (sqrtInterval q S k).1

def sqrtHi (q S : ℚ) (k : ℕ) : ℚ := (sqrtInterval q S k).2

def bracketEnc (q S : ℚ) (k : ℕ) : RatEnc × RatEnc :=
  (ratEnc (sqrtLo q S k), ratEnc (sqrtHi q S k))

theorem sqrtInterval_certified (q S : ℚ) (k : ℕ) (hS : 0 < S) (hq : 0 ≤ q)
    (hSq : q ≤ S * S) :
    0 ≤ sqrtLo q S k ∧ sqrtLo q S k ≤ sqrtHi q S k ∧ sqrtHi q S k ≤ S ∧
      (sqrtLo q S k) ^ 2 ≤ q ∧ q ≤ (sqrtHi q S k) ^ 2 ∧
      sqrtHi q S k - sqrtLo q S k = S / (2 : ℚ) ^ k ∧
      ((sqrtLo q S k : ℚ) : ℝ) ≤ Real.sqrt (q : ℝ) ∧
      Real.sqrt (q : ℝ) ≤ ((sqrtHi q S k : ℚ) : ℝ) := by
  have h := Qatlib.Concepts.ScaledSqrt.SqrtBounds.g1 q S k hS hq hSq
  dsimp only [sqrtInterval, sqrtLo, sqrtHi]
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩

theorem bracketEnc_decodes (q S : ℚ) (k : ℕ) :
    (bracketEnc q S k).1.toRat = sqrtLo q S k ∧
      (bracketEnc q S k).2.toRat = sqrtHi q S k := by
  exact ⟨ratEnc_toRat _, ratEnc_toRat _⟩

def encRatWord (r : ℚ) : Bits :=
  (if 0 ≤ r then [false] else [true]) ++
    framed (natBits r.num.natAbs) ++ framed (natBits r.den)

def bracketWord (q S : ℚ) (k : ℕ) : Bits :=
  encRatWord (sqrtLo q S k) ++ encRatWord (sqrtHi q S k)

theorem bracketWord_eq (q S : ℚ) (k : ℕ) :
    bracketWord q S k =
      encRatWord (bracketEnc q S k).1.toRat ++
        encRatWord (bracketEnc q S k).2.toRat := by
  simp [bracketWord, bracketEnc]

def widthPrecision (S : ℚ) (b : ℕ) : ℕ := b + Nat.log2 S.num.natAbs + 1

theorem widthPrecision_spec (S : ℚ) (hS : 0 < S) (b : ℕ) :
    S / (2 : ℚ) ^ widthPrecision S b ≤ 1 / (2 : ℚ) ^ b := by
  have hnum_pos : 0 < S.num := Rat.num_pos.mpr hS
  have hnum_nonneg : (0 : ℚ) ≤ (S.num : ℚ) := by exact_mod_cast hnum_pos.le
  have hnum_cast : ((S.num.natAbs : ℕ) : ℚ) = (S.num : ℚ) := by
    have h : ((S.num.natAbs : ℕ) : ℤ) = S.num := Int.natAbs_of_nonneg hnum_pos.le
    have hq := congrArg (fun t : ℤ => (t : ℚ)) h
    simpa using! hq
  have hden_one : (1 : ℚ) ≤ S.den := by exact_mod_cast S.den_pos
  have hS_eq : S = (S.num : ℚ) / (S.den : ℚ) := by
    rw [Rat.num_div_den]
  have hle_num : S ≤ (S.num.natAbs : ℚ) := by
    have hdiv : (S.num : ℚ) / (S.den : ℚ) ≤ (S.num : ℚ) / 1 :=
      div_le_div_of_nonneg_left hnum_nonneg (by norm_num) hden_one
    calc
      S = (S.num : ℚ) / (S.den : ℚ) := hS_eq
      _ ≤ (S.num : ℚ) / 1 := hdiv
      _ = (S.num : ℚ) := by ring
      _ = (S.num.natAbs : ℚ) := hnum_cast.symm
  have hlt : (S.num.natAbs : ℕ) < 2 ^ (Nat.log2 S.num.natAbs + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (S.num.natAbs)
    simpa [Nat.log2_eq_log_two] using! h
  have hbound : S ≤ (2 : ℚ) ^ (Nat.log2 S.num.natAbs + 1) := by
    refine hle_num.trans ?_
    exact_mod_cast hlt.le
  have hsplit : S / (2 : ℚ) ^ (b + Nat.log2 S.num.natAbs + 1)
      = (S / (2 : ℚ) ^ (Nat.log2 S.num.natAbs + 1)) / (2 : ℚ) ^ b := by
    rw [pow_add]
    ring
  rw [show widthPrecision S b = b + Nat.log2 S.num.natAbs + 1 from rfl, hsplit]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [div_le_one (by positivity)]
  exact hbound

theorem precision_term_is_needed :
    ¬ ((2 : ℚ) / (2 : ℚ) ^ 0 ≤ 1 / (2 : ℚ) ^ 0) ∧
      (2 : ℚ) / (2 : ℚ) ^ 1 ≤ 1 / (2 : ℚ) ^ 0 := by
  norm_num

def bisectStep (q : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  let m := (p.1 + p.2) / 2
  if m * m ≤ q then (m, p.2) else (p.1, m)

theorem rationalSqrtBracket_pair_eq_iterate (q : ℚ) (k : ℕ) :
    ((Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q k).1,
        (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q k).2.1)
      = (bisectStep q)^[k] (0, 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep :
        ((Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q (k + 1)).1,
            (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q (k + 1)).2.1)
          = bisectStep q
              ((Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q k).1,
                (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q k).2.1) := by
      simp only [Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket, bisectStep]
      split_ifs <;> rfl
    rw [hstep, ih, Function.iterate_succ_apply']

theorem sqrtInterval_eq_scale (q S : ℚ) (k : ℕ) :
    sqrtInterval q S k =
      (S * (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).1,
        S * (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).2.1) := by
  rfl

theorem bracket_machine_of_step (step : Bits → Bits) (tf sf : Bits → ℕ)
    (hstep : ComputesAt step tf sf) (init : Bits) (q S : ℚ) (k : ℕ)
    (hiter : (step^[k]) init = bracketWord q S k) :
    ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
      Runs M (natBits k ++ framed init) (bracketWord q S k)
        (C * (1 + (natBits k ++ framed init).length + k +
          (bracketWord q S k).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step tf k init +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length k init) ^ 2)
        (C * (1 + (natBits k ++ framed init).length + k +
          (bracketWord q S k).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step sf k init +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length k init) ^ 2) := by
  obtain ⟨qm, M, C, hC, hM⟩ :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.uniform_iterates step tf sf hstep
  refine ⟨qm, M, C, hC, ?_⟩
  have h := hM k init
  rw [hiter] at h
  exact h

theorem bracket_machine_width (step : Bits → Bits) (tf sf : Bits → ℕ)
    (hstep : ComputesAt step tf sf) (init : Bits) (q S : ℚ) (hS : 0 < S)
    (hq : 0 ≤ q) (hSq : q ≤ S * S) (b : ℕ)
    (hiter : (step^[widthPrecision S b]) init =
      bracketWord q S (widthPrecision S b)) :
    ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
      Runs M (natBits (widthPrecision S b) ++ framed init)
        (bracketWord q S (widthPrecision S b))
        (C * (1 + (natBits (widthPrecision S b) ++ framed init).length +
          widthPrecision S b + (bracketWord q S (widthPrecision S b)).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step tf
            (widthPrecision S b) init +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length
            (widthPrecision S b) init) ^ 2)
        (C * (1 + (natBits (widthPrecision S b) ++ framed init).length +
          widthPrecision S b + (bracketWord q S (widthPrecision S b)).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step sf
            (widthPrecision S b) init +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length
            (widthPrecision S b) init) ^ 2) ∧
      sqrtHi q S (widthPrecision S b) - sqrtLo q S (widthPrecision S b)
        ≤ 1 / (2 : ℚ) ^ b := by
  obtain ⟨qm, M, C, hC, hRuns⟩ :=
    bracket_machine_of_step step tf sf hstep init q S (widthPrecision S b) hiter
  refine ⟨qm, M, C, hC, hRuns, ?_⟩
  have hwidth := (sqrtInterval_certified q S (widthPrecision S b) hS hq hSq).2.2.2.2.2.1
  rw [hwidth]
  exact widthPrecision_spec S hS b

def readFramedNat (w : Bits) : Option (ℕ × Bits) :=
  match Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat w with
  | none => none
  | some (len, rest) =>
      if len ≤ rest.length then
        match Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat (rest.take len) with
        | none => none
        | some (v, rest') =>
            if rest'.length = 0 then some (v, rest.drop len) else none
      else none

theorem take_append_length (l rest : Bits) :
    (l ++ rest).take l.length = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem drop_append_length (l rest : Bits) :
    (l ++ rest).drop l.length = rest := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem readFramedNat_natBits (n : ℕ) (rest : Bits) :
    readFramedNat (framed (natBits n) ++ rest) = some (n, rest) := by
  have hread : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat (framed (natBits n) ++ rest)
      = some ((natBits n).length, natBits n ++ rest) := by
    rw [framed, List.append_assoc]
    exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat_complete _ _
  have hinner : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat (natBits n) = some (n, []) := by
    simpa using! Qatlib.Concepts.BitWordCompiler.CanonicalCodec.readNat_complete n ([] : Bits)
  unfold readFramedNat
  rw [hread]
  (try dsimp only)
  rw [if_pos (show (natBits n).length ≤ (natBits n ++ rest).length by simp)]
  rw [take_append_length]
  rw [hinner]
  (try dsimp only)
  simp only [List.length_nil]
  simp only [if_true]
  simp

def decRat (w : Bits) : Option (ℚ × Bits) :=
  match w with
  | [] => none
  | b :: t =>
      match readFramedNat t with
      | none => none
      | some (n, r1) =>
          match readFramedNat r1 with
          | none => none
          | some (d, r2) =>
              if d = 0 then none
              else some ((if b then -((n : ℚ) / (d : ℚ)) else (n : ℚ) / (d : ℚ)), r2)

theorem num_nonneg_of_nonneg (r : ℚ) (h : 0 ≤ r) : (0 : ℚ) ≤ (r.num : ℚ) := by
  have hdiv : (0 : ℚ) ≤ (r.num : ℚ) / (r.den : ℚ) := by
    rwa [Rat.num_div_den]
  have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  by_contra hneg
  have hlt : (r.num : ℚ) < 0 := lt_of_not_ge hneg
  have : (r.num : ℚ) / (r.den : ℚ) < 0 := div_neg_of_neg_of_pos hlt hd
  linarith

theorem num_nonpos_of_neg (r : ℚ) (h : ¬ 0 ≤ r) : (r.num : ℚ) ≤ 0 := by
  have hr : r < 0 := lt_of_not_ge h
  have hdiv : (r.num : ℚ) / (r.den : ℚ) < 0 := by
    rw [Rat.num_div_den]; exact hr
  have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  have hmul : (r.num : ℚ) = ((r.num : ℚ) / (r.den : ℚ)) * (r.den : ℚ) := by
    field_simp [r.den_pos.ne']
  have hneg : (r.num : ℚ) < 0 := by
    rw [hmul]
    exact mul_neg_of_neg_of_pos hdiv hd
  exact le_of_lt hneg

theorem cast_natAbs_num_of_nonneg (r : ℚ) (h : 0 ≤ r) :
    ((r.num.natAbs : ℚ)) = (r.num : ℚ) := by
  have hnum : (0 : ℤ) ≤ r.num := by exact_mod_cast num_nonneg_of_nonneg r h
  have hcast : ((r.num.natAbs : ℕ) : ℤ) = r.num := Int.natAbs_of_nonneg hnum
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hcast
  simpa using! hq

theorem neg_cast_natAbs_num_of_neg (r : ℚ) (h : ¬ 0 ≤ r) :
    -(((r.num.natAbs : ℚ))) = (r.num : ℚ) := by
  have hnum : r.num ≤ 0 := by exact_mod_cast num_nonpos_of_neg r h
  have hcast : ((r.num.natAbs : ℕ) : ℤ) = -r.num := Int.ofNat_natAbs_of_nonpos hnum
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hcast
  have hq' : ((r.num.natAbs : ℚ)) = -((r.num : ℤ) : ℚ) := by simpa using! hq
  rw [hq']
  ring

theorem decRat_encRatWord (r : ℚ) (rest : Bits) :
    decRat (encRatWord r ++ rest) = some (r, rest) := by
  unfold encRatWord
  by_cases h : 0 ≤ r
  · rw [if_pos h]
    simp [decRat, readFramedNat_natBits, List.append_assoc, r.den_pos.ne']
    rw [abs_of_nonneg (num_nonneg_of_nonneg r h), Rat.num_div_den]
  · rw [if_neg h]
    simp [decRat, readFramedNat_natBits, List.append_assoc, r.den_pos.ne']
    rw [abs_of_nonpos (num_nonpos_of_neg r h)]
    rw [show -((-(r.num : ℚ)) / (r.den : ℚ)) = r from by
      rw [← neg_div, neg_neg, Rat.num_div_den]]

def stateWord (q S lo hi : ℚ) : Bits :=
  encRatWord q ++ (encRatWord S ++ (encRatWord lo ++ encRatWord hi))

def readState (w : Bits) : Option (ℚ × ℚ × ℚ × ℚ × Bits) :=
  match decRat w with
  | none => none
  | some (q, r1) =>
      match decRat r1 with
      | none => none
      | some (S, r2) =>
          match decRat r2 with
          | none => none
          | some (lo, r3) =>
              match decRat r3 with
              | none => none
              | some (hi, r4) => some (q, S, lo, hi, r4)

theorem readState_stateWord (q S lo hi : ℚ) (rest : Bits) :
    readState (stateWord q S lo hi ++ rest) = some (q, S, lo, hi, rest) := by
  simp only [stateWord, readState, decRat_encRatWord, List.append_assoc]

def wordStep (w : Bits) : Bits :=
  match readState w with
  | none => w
  | some (q, S, lo, hi, rest) =>
      let p := bisectStep q (lo, hi)
      stateWord q S p.1 p.2 ++ rest

theorem wordStep_stateWord (q S lo hi : ℚ) (rest : Bits) :
    wordStep (stateWord q S lo hi ++ rest)
      = stateWord q S (bisectStep q (lo, hi)).1 (bisectStep q (lo, hi)).2 ++ rest := by
  simp only [wordStep, readState_stateWord]

theorem bisectStep_scaled (q S : ℚ) (hS : 0 < S) (p : ℚ × ℚ) :
    (S * (bisectStep (q / (S * S)) p).1, S * (bisectStep (q / (S * S)) p).2)
      = bisectStep (S * S * (q / (S * S))) (S * p.1, S * p.2) := by
  unfold bisectStep
  have hSq : (0 : ℚ) < S * S := mul_pos hS hS
  have hq : S * S * (q / (S * S)) = q := by field_simp [hS.ne']
  have hmid : (S * p.1 + S * p.2) / 2 = S * ((p.1 + p.2) / 2) := by ring
  by_cases h : ((p.1 + p.2) / 2) * ((p.1 + p.2) / 2) ≤ q / (S * S)
  · have h' : ((S * p.1 + S * p.2) / 2) * ((S * p.1 + S * p.2) / 2)
        ≤ S * S * (q / (S * S)) := by
      rw [hmid]
      have hmul : (S * ((p.1 + p.2) / 2)) * (S * ((p.1 + p.2) / 2))
          = (S * S) * (((p.1 + p.2) / 2) * ((p.1 + p.2) / 2)) := by ring
      rw [hmul]
      exact mul_le_mul_of_nonneg_left h hSq.le
    rw [if_pos h, if_pos h', hmid]
  · have h' : ¬ ((S * p.1 + S * p.2) / 2) * ((S * p.1 + S * p.2) / 2)
        ≤ S * S * (q / (S * S)) := by
      intro hc
      apply h
      rw [hmid] at hc
      have hmul : (S * ((p.1 + p.2) / 2)) * (S * ((p.1 + p.2) / 2))
          = (S * S) * (((p.1 + p.2) / 2) * ((p.1 + p.2) / 2)) := by ring
      rw [hmul] at hc
      exact (mul_le_mul_iff_of_pos_left hSq).mp hc
    rw [if_neg h, if_neg h', hmid]

theorem bisectStep_iterate_scaled (q S : ℚ) (hS : 0 < S) (k : ℕ) :
    (bisectStep q)^[k] (0, S) = sqrtInterval q S k := by
  have hq : S * S * (q / (S * S)) = q := by field_simp [hS.ne']
  have hmain : (bisectStep (S * S * (q / (S * S))))^[k] (S * 0, S * 1)
      = (S * ((bisectStep (q / (S * S)))^[k] (0, 1)).1,
          S * ((bisectStep (q / (S * S)))^[k] (0, 1)).2) := by
    induction k with
    | zero => simp [Function.iterate_zero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ← bisectStep_scaled q S hS,
        Function.iterate_succ_apply']
  rw [hq] at hmain
  have hinit : (S * 0, S * 1) = (0, S) := by simp
  rw [hinit] at hmain
  rw [hmain, sqrtInterval_eq_scale]
  rw [show (bisectStep (q / (S * S)))^[k] (0, 1)
      = ((Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).1,
          (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).2.1) from
    (rationalSqrtBracket_pair_eq_iterate (q / (S * S)) k).symm]

theorem wordStep_iterate (q S : ℚ) (hS : 0 < S) (k : ℕ) (rest : Bits) :
    (wordStep^[k]) (stateWord q S 0 S ++ rest)
      = stateWord q S (sqrtLo q S k) (sqrtHi q S k) ++ rest := by
  induction k with
  | zero =>
    have h0 : sqrtInterval q S 0 = (0, S) := by
      simp [sqrtInterval, Qatlib.Concepts.ScaledSqrt.SqrtBounds.bracket,
        Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket]
    simp only [Function.iterate_zero, sqrtLo, sqrtHi, h0]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, wordStep_stateWord]
    have hpair : bisectStep q (sqrtLo q S k, sqrtHi q S k)
        = (sqrtLo q S (k + 1), sqrtHi q S (k + 1)) := by
      have h1 := bisectStep_iterate_scaled q S hS (k + 1)
      rw [Function.iterate_succ_apply', bisectStep_iterate_scaled q S hS k] at h1
      simpa [sqrtLo, sqrtHi, sqrtInterval] using! h1
    rw [hpair]

theorem bracket_machine_word (tf sf : Bits → ℕ)
    (hstep : ComputesAt wordStep tf sf) (q S : ℚ) (hS : 0 < S) (k : ℕ) :
    ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
      Runs M (natBits k ++ framed (stateWord q S 0 S))
        (stateWord q S (sqrtLo q S k) (sqrtHi q S k))
        (C * (1 + (natBits k ++ framed (stateWord q S 0 S)).length + k +
          (stateWord q S (sqrtLo q S k) (sqrtHi q S k)).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep tf k (stateWord q S 0 S) +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length k
            (stateWord q S 0 S)) ^ 2)
        (C * (1 + (natBits k ++ framed (stateWord q S 0 S)).length + k +
          (stateWord q S (sqrtLo q S k) (sqrtHi q S k)).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep sf k (stateWord q S 0 S) +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length k
            (stateWord q S 0 S)) ^ 2) := by
  obtain ⟨qm, M, C, hC, hM⟩ :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.uniform_iterates wordStep tf sf hstep
  refine ⟨qm, M, C, hC, ?_⟩
  have h := hM k (stateWord q S 0 S)
  have hi := wordStep_iterate q S hS k []
  rw [List.append_nil] at hi
  rw [hi] at h
  simpa only [List.append_nil] using! h

theorem stateWord_suffix (q S lo hi : ℚ) :
    stateWord q S lo hi =
      encRatWord q ++ (encRatWord S ++ (encRatWord lo ++ encRatWord hi)) := rfl

theorem stateWord_suffix_bracketWord (q S : ℚ) (k : ℕ) :
    stateWord q S (sqrtLo q S k) (sqrtHi q S k)
      = encRatWord q ++ (encRatWord S ++ bracketWord q S k) := by
  simp [stateWord, bracketWord]

theorem bracket_machine_word_width (tf sf : Bits → ℕ)
    (hstep : ComputesAt wordStep tf sf) (q S : ℚ) (hS : 0 < S)
    (hq : 0 ≤ q) (hSq : q ≤ S * S) (b : ℕ) :
    ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
      Runs M (natBits (widthPrecision S b) ++ framed (stateWord q S 0 S))
        (stateWord q S (sqrtLo q S (widthPrecision S b))
          (sqrtHi q S (widthPrecision S b)))
        (C * (1 + (natBits (widthPrecision S b) ++
            framed (stateWord q S 0 S)).length + widthPrecision S b +
          (stateWord q S (sqrtLo q S (widthPrecision S b))
            (sqrtHi q S (widthPrecision S b))).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep tf
            (widthPrecision S b) (stateWord q S 0 S) +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length
            (widthPrecision S b) (stateWord q S 0 S)) ^ 2)
        (C * (1 + (natBits (widthPrecision S b) ++
            framed (stateWord q S 0 S)).length + widthPrecision S b +
          (stateWord q S (sqrtLo q S (widthPrecision S b))
            (sqrtHi q S (widthPrecision S b))).length +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep sf
            (widthPrecision S b) (stateWord q S 0 S) +
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length
            (widthPrecision S b) (stateWord q S 0 S)) ^ 2) ∧
      sqrtHi q S (widthPrecision S b) - sqrtLo q S (widthPrecision S b)
        ≤ 1 / (2 : ℚ) ^ b := by
  obtain ⟨qm, M, C, hC, hRuns⟩ :=
    bracket_machine_word tf sf hstep q S hS (widthPrecision S b)
  refine ⟨qm, M, C, hC, hRuns, ?_⟩
  have hwidth := (sqrtInterval_certified q S (widthPrecision S b) hS hq hSq).2.2.2.2.2.1
  rw [hwidth]
  exact widthPrecision_spec S hS b

theorem frontier1 :
    (∀ (q S : ℚ) (k : ℕ), 0 < S → 0 ≤ q → q ≤ S * S →
      (bracketEnc q S k).1.toRat = sqrtLo q S k ∧
        (bracketEnc q S k).2.toRat = sqrtHi q S k ∧
        0 ≤ sqrtLo q S k ∧ sqrtLo q S k ≤ sqrtHi q S k ∧ sqrtHi q S k ≤ S ∧
        (sqrtLo q S k) ^ 2 ≤ q ∧ q ≤ (sqrtHi q S k) ^ 2 ∧
        sqrtHi q S k - sqrtLo q S k = S / (2 : ℚ) ^ k ∧
        ((sqrtLo q S k : ℚ) : ℝ) ≤ Real.sqrt (q : ℝ) ∧
        Real.sqrt (q : ℝ) ≤ ((sqrtHi q S k : ℚ) : ℝ)) ∧
    (∀ (S : ℚ) (b : ℕ), 0 < S →
      S / (2 : ℚ) ^ widthPrecision S b ≤ 1 / (2 : ℚ) ^ b) ∧
    (∀ (q : ℚ) (k : ℕ),
      ((Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q k).1,
          (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket q k).2.1)
        = (bisectStep q)^[k] (0, 1)) ∧
    (∀ (step : Bits → Bits) (tf sf : Bits → ℕ), ComputesAt step tf sf →
      ∀ (init : Bits) (q S : ℚ) (k : ℕ), (step^[k]) init = bracketWord q S k →
        ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
          Runs M (natBits k ++ framed init) (bracketWord q S k)
            (C * (1 + (natBits k ++ framed init).length + k +
              (bracketWord q S k).length +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step tf k init +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length k init) ^ 2)
            (C * (1 + (natBits k ++ framed init).length + k +
              (bracketWord q S k).length +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step sf k init +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length k init) ^ 2)) ∧
    (∀ (step : Bits → Bits) (tf sf : Bits → ℕ), ComputesAt step tf sf →
      ∀ (init : Bits) (q S : ℚ), 0 < S → 0 ≤ q → q ≤ S * S → ∀ b : ℕ,
        (step^[widthPrecision S b]) init = bracketWord q S (widthPrecision S b) →
        ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
          Runs M (natBits (widthPrecision S b) ++ framed init)
            (bracketWord q S (widthPrecision S b))
            (C * (1 + (natBits (widthPrecision S b) ++ framed init).length +
              widthPrecision S b + (bracketWord q S (widthPrecision S b)).length +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step tf
                (widthPrecision S b) init +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length
                (widthPrecision S b) init) ^ 2)
            (C * (1 + (natBits (widthPrecision S b) ++ framed init).length +
              widthPrecision S b + (bracketWord q S (widthPrecision S b)).length +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step sf
                (widthPrecision S b) init +
              Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum step List.length
                (widthPrecision S b) init) ^ 2) ∧
          sqrtHi q S (widthPrecision S b) - sqrtLo q S (widthPrecision S b)
            ≤ 1 / (2 : ℚ) ^ b) ∧
    (∀ (r : ℚ) (rest : Bits), decRat (encRatWord r ++ rest) = some (r, rest)) ∧
    (∀ (q S lo hi : ℚ) (rest : Bits),
      readState (stateWord q S lo hi ++ rest) = some (q, S, lo, hi, rest)) ∧
    (∀ (q S : ℚ), 0 < S → ∀ (k : ℕ) (rest : Bits),
      (wordStep^[k]) (stateWord q S 0 S ++ rest)
        = stateWord q S (sqrtLo q S k) (sqrtHi q S k) ++ rest) ∧
    (∀ (tf sf : Bits → ℕ), ComputesAt wordStep tf sf → ∀ (q S : ℚ), 0 < S → ∀ k : ℕ,
      ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
        Runs M (natBits k ++ framed (stateWord q S 0 S))
          (stateWord q S (sqrtLo q S k) (sqrtHi q S k))
          (C * (1 + (natBits k ++ framed (stateWord q S 0 S)).length + k +
            (stateWord q S (sqrtLo q S k) (sqrtHi q S k)).length +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep tf k (stateWord q S 0 S) +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length k
              (stateWord q S 0 S)) ^ 2)
          (C * (1 + (natBits k ++ framed (stateWord q S 0 S)).length + k +
            (stateWord q S (sqrtLo q S k) (sqrtHi q S k)).length +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep sf k (stateWord q S 0 S) +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length k
              (stateWord q S 0 S)) ^ 2)) ∧
    (∀ (tf sf : Bits → ℕ), ComputesAt wordStep tf sf → ∀ (q S : ℚ), 0 < S → 0 ≤ q →
      q ≤ S * S → ∀ b : ℕ,
      ∃ (qm : ℕ) (M : TM0.Machine (Option Bool) (Fin (qm + 1))) (C : ℕ), 0 < C ∧
        Runs M (natBits (widthPrecision S b) ++ framed (stateWord q S 0 S))
          (stateWord q S (sqrtLo q S (widthPrecision S b))
            (sqrtHi q S (widthPrecision S b)))
          (C * (1 + (natBits (widthPrecision S b) ++
              framed (stateWord q S 0 S)).length + widthPrecision S b +
            (stateWord q S (sqrtLo q S (widthPrecision S b))
              (sqrtHi q S (widthPrecision S b))).length +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep tf
              (widthPrecision S b) (stateWord q S 0 S) +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length
              (widthPrecision S b) (stateWord q S 0 S)) ^ 2)
          (C * (1 + (natBits (widthPrecision S b) ++
              framed (stateWord q S 0 S)).length + widthPrecision S b +
            (stateWord q S (sqrtLo q S (widthPrecision S b))
              (sqrtHi q S (widthPrecision S b))).length +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep sf
              (widthPrecision S b) (stateWord q S 0 S) +
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum wordStep List.length
              (widthPrecision S b) (stateWord q S 0 S)) ^ 2) ∧
        sqrtHi q S (widthPrecision S b) - sqrtLo q S (widthPrecision S b)
          ≤ 1 / (2 : ℚ) ^ b) ∧
    (∀ (q S : ℚ) (k : ℕ),
      stateWord q S (sqrtLo q S k) (sqrtHi q S k)
        = encRatWord q ++ (encRatWord S ++ bracketWord q S k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q S k hS hq hSq
    obtain ⟨hdec1, hdec2⟩ := bracketEnc_decodes q S k
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sqrtInterval_certified q S k hS hq hSq
    exact ⟨hdec1, hdec2, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · intro S b hS
    exact widthPrecision_spec S hS b
  · intro q k
    exact rationalSqrtBracket_pair_eq_iterate q k
  · intro step tf sf hstep init q S k hiter
    exact bracket_machine_of_step step tf sf hstep init q S k hiter
  · intro step tf sf hstep init q S hS hq hSq b hiter
    exact bracket_machine_width step tf sf hstep init q S hS hq hSq b hiter
  · intro r rest
    exact decRat_encRatWord r rest
  · intro q S lo hi rest
    exact readState_stateWord q S lo hi rest
  · intro q S hS k rest
    exact wordStep_iterate q S hS k rest
  · intro tf sf hstep q S hS k
    exact bracket_machine_word tf sf hstep q S hS k
  · intro tf sf hstep q S hS hq hSq b
    exact bracket_machine_word_width tf sf hstep q S hS hq hSq b
  · intro q S k
    exact stateWord_suffix_bracketWord q S k

def sqNum (q S : ℚ) : ℕ := q.num.natAbs * S.den * S.den

def sqDen (q S : ℚ) : ℕ := q.den * S.num.natAbs * S.num.natAbs

theorem sqDen_pos (q S : ℚ) (hS : 0 < S) : 0 < sqDen q S := by
  have hd : 0 < q.den := q.den_pos
  have hn : 0 < S.num.natAbs := by
    have hpos : 0 < S.num := Rat.num_pos.mpr hS
    exact Int.natAbs_pos.mpr hpos.ne'
  unfold sqDen
  exact Nat.mul_pos (Nat.mul_pos hd hn) hn

theorem sqNum_div_sqDen (q S : ℚ) (hq : 0 ≤ q) (hS : 0 < S) :
    (sqNum q S : ℚ) / (sqDen q S : ℚ) = q / (S * S) := by
  have hqn : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := cast_natAbs_num_of_nonneg q hq
  have hSn : ((S.num.natAbs : ℕ) : ℚ) = (S.num : ℚ) := cast_natAbs_num_of_nonneg S hS.le
  have hP : (sqNum q S : ℚ) = (q.num : ℚ) * (S.den : ℚ) * (S.den : ℚ) := by
    unfold sqNum
    push_cast
    rw [hqn]
  have hD : (sqDen q S : ℚ) = (q.den : ℚ) * (S.num : ℚ) * (S.num : ℚ) := by
    unfold sqDen
    push_cast
    rw [hSn]
  rw [hP, hD]
  conv_rhs => rw [← Rat.num_div_den q, ← Rat.num_div_den S]
  have hqd : ((q.den : ℕ) : ℚ) ≠ 0 := by
    have h : (0 : ℕ) < q.den := q.den_pos
    exact_mod_cast h.ne'
  have hSd : ((S.den : ℕ) : ℚ) ≠ 0 := by
    have h : (0 : ℕ) < S.den := S.den_pos
    exact_mod_cast h.ne'
  have hSn0 : (S.num : ℚ) ≠ 0 := by
    have h : (0 : ℤ) < S.num := Rat.num_pos.mpr hS
    have h2 : (0 : ℚ) < (S.num : ℚ) := by exact_mod_cast h
    exact h2.ne'
  field_simp

def intStep (P Q j a : ℕ) : ℕ :=
  if (2 * a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P then 2 * a + 1 else 2 * a

theorem intStep_eq (P Q j a : ℕ) :
    intStep P Q j a
      = 2 * a + (if (2 * a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P then 1 else 0) := by
  unfold intStep
  split_ifs <;> omega

def intBisectFrom (P Q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, a => a
  | n + 1, j, a => intStep P Q (j + n) (intBisectFrom P Q n j a)

def intBisect (P Q k : ℕ) : ℕ := intBisectFrom P Q k 0 0

theorem test_iff (P Q j a : ℕ) (hQ : 0 < Q) :
    ((2 * (a : ℚ) + 1) / 2 ^ (j + 1)) * ((2 * (a : ℚ) + 1) / 2 ^ (j + 1))
        ≤ (P : ℚ) / (Q : ℚ) ↔
      (2 * a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P := by
  have hQq : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
  have hp : (0 : ℚ) < (2 : ℚ) ^ (2 * (j + 1)) := by positivity
  have hkey : ((2 * (a : ℚ) + 1) / 2 ^ (j + 1)) * ((2 * (a : ℚ) + 1) / 2 ^ (j + 1))
      = (2 * (a : ℚ) + 1) ^ 2 / (2 : ℚ) ^ (2 * (j + 1)) := by
    rw [div_mul_div_comm, ← pow_add,
      show j + 1 + (j + 1) = 2 * (j + 1) by omega]
    ring
  rw [hkey, div_le_div_iff₀ hp hQq]
  constructor
  · intro h
    have h' : (((2 * a + 1) ^ 2 * Q : ℕ) : ℚ) ≤ ((2 ^ (2 * (j + 1)) * P : ℕ) : ℚ) := by
      push_cast
      calc ((2 : ℚ) * (a : ℚ) + 1) ^ 2 * (Q : ℚ)
          = (2 * (a : ℚ) + 1) ^ 2 * (Q : ℚ) := by ring
        _ ≤ (P : ℚ) * (2 : ℚ) ^ (2 * (j + 1)) := h
        _ = (2 : ℚ) ^ (2 * (j + 1)) * (P : ℚ) := by ring
    exact_mod_cast h'
  · intro h
    have h' : (((2 * a + 1) ^ 2 * Q : ℕ) : ℚ) ≤ ((2 ^ (2 * (j + 1)) * P : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at h'
    calc (2 * (a : ℚ) + 1) ^ 2 * (Q : ℚ)
        = ((2 : ℚ) * (a : ℚ) + 1) ^ 2 * (Q : ℚ) := by ring
      _ ≤ (2 : ℚ) ^ (2 * (j + 1)) * (P : ℚ) := h'
      _ = (P : ℚ) * (2 : ℚ) ^ (2 * (j + 1)) := by ring

theorem bisectStep_apply (X lo hi m : ℚ) (hm : m = (lo + hi) / 2) :
    bisectStep X (lo, hi) = if m * m ≤ X then (m, hi) else (lo, m) := by
  subst hm
  rfl

theorem bisectStep_pair (P Q j a : ℕ) (hQ : 0 < Q) :
    bisectStep ((P : ℚ) / (Q : ℚ))
        (((a : ℚ) / 2 ^ j), (((a : ℚ) + 1) / 2 ^ j)) =
      ((((intStep P Q j a : ℕ) : ℚ) / 2 ^ (j + 1)),
        ((((intStep P Q j a : ℕ) : ℚ) + 1) / 2 ^ (j + 1))) := by
  have hpow : ((2 : ℚ) ^ (j + 1)) = 2 * (2 : ℚ) ^ j := by
    rw [pow_succ]
    ring
  have hpj : ((2 : ℚ) ^ j) ≠ 0 := by positivity
  have hmid : (2 * (a : ℚ) + 1) / 2 ^ (j + 1)
      = (((a : ℚ) / 2 ^ j) + (((a : ℚ) + 1) / 2 ^ j)) / 2 := by
    rw [hpow]
    field_simp
    ring
  rw [bisectStep_apply _ _ _ _ hmid]
  by_cases h : (2 * a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P
  · have hq : ((2 * (a : ℚ) + 1) / 2 ^ (j + 1)) * ((2 * (a : ℚ) + 1) / 2 ^ (j + 1))
        ≤ (P : ℚ) / (Q : ℚ) := (test_iff P Q j a hQ).mpr h
    rw [if_pos hq]
    simp only [intStep, if_pos h]
    have hc2 : (((2 * a + 1 : ℕ)) : ℚ) = 2 * (a : ℚ) + 1 := by push_cast; ring
    have hfac : (((a : ℚ) + 1)) / 2 ^ j = (2 * (a : ℚ) + 1 + 1) / 2 ^ (j + 1) := by
      rw [hpow]
      field_simp
      ring
    rw [hc2, hfac]
  · have hq : ¬ ((2 * (a : ℚ) + 1) / 2 ^ (j + 1)) * ((2 * (a : ℚ) + 1) / 2 ^ (j + 1))
        ≤ (P : ℚ) / (Q : ℚ) := by
      intro hc
      exact h ((test_iff P Q j a hQ).mp hc)
    rw [if_neg hq]
    simp only [intStep, if_neg h]
    have hc2 : (((2 * a : ℕ)) : ℚ) = 2 * (a : ℚ) := by push_cast; ring
    have hfac : (a : ℚ) / 2 ^ j = (2 * (a : ℚ)) / 2 ^ (j + 1) := by
      rw [hpow]
      field_simp
    rw [hc2, hfac]

theorem bisectStep_iterate_int (P Q : ℕ) (hQ : 0 < Q) (n j a : ℕ) :
    (bisectStep ((P : ℚ) / (Q : ℚ)))^[n]
        (((a : ℚ) / 2 ^ j), (((a : ℚ) + 1) / 2 ^ j)) =
      (((intBisectFrom P Q n j a : ℕ) : ℚ) / 2 ^ (j + n),
        ((((intBisectFrom P Q n j a : ℕ) : ℚ) + 1) / 2 ^ (j + n))) := by
  induction n generalizing j a with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih j a,
      bisectStep_pair P Q (j + n) (intBisectFrom P Q n j a) hQ,
      show j + n + 1 = j + (n + 1) by omega]
    rfl

theorem bisectStep_iterate_int_zero (P Q : ℕ) (hQ : 0 < Q) (k : ℕ) :
    (bisectStep ((P : ℚ) / (Q : ℚ)))^[k] (0, 1) =
      (((intBisect P Q k : ℕ) : ℚ) / 2 ^ k,
        ((((intBisect P Q k : ℕ) : ℚ) + 1) / 2 ^ k)) := by
  have h := bisectStep_iterate_int P Q hQ k 0 0
  simpa [intBisect] using! h

theorem sqrtInterval_intBisect (q S : ℚ) (hq : 0 ≤ q) (hS : 0 < S) (k : ℕ) :
    sqrtInterval q S k =
      (S * (((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) / 2 ^ k),
        S * ((((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) + 1) / 2 ^ k)) := by
  have hQpos : 0 < sqDen q S := sqDen_pos q S hS
  have hpair : ((Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).1,
      (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).2.1) =
      (((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) / 2 ^ k,
        ((((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) + 1) / 2 ^ k)) := by
    rw [rationalSqrtBracket_pair_eq_iterate, ← sqNum_div_sqDen q S hq hS]
    exact bisectStep_iterate_int_zero (sqNum q S) (sqDen q S) hQpos k
  rw [sqrtInterval_eq_scale,
    show (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).1
        = ((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) / 2 ^ k from
      congrArg Prod.fst hpair,
    show (Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q / (S * S)) k).2.1
        = (((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) + 1) / 2 ^ k from
      congrArg Prod.snd hpair]

theorem sqrtLo_eq_intBisect (q S : ℚ) (hq : 0 ≤ q) (hS : 0 < S) (k : ℕ) :
    sqrtLo q S k = S * (((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) / 2 ^ k) := by
  have h := sqrtInterval_intBisect q S hq hS k
  exact congrArg Prod.fst h

theorem sqrtHi_eq_intBisect (q S : ℚ) (hq : 0 ≤ q) (hS : 0 < S) (k : ℕ) :
    sqrtHi q S k =
      S * ((((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) + 1) / 2 ^ k) := by
  have h := sqrtInterval_intBisect q S hq hS k
  exact congrArg Prod.snd h

theorem intBisectFrom_lt (P Q : ℕ) :
    ∀ (n j a : ℕ), a < 2 ^ j → intBisectFrom P Q n j a < 2 ^ (j + n) := by
  intro n
  induction n with
  | zero => intro j a ha; simpa [intBisectFrom] using! ha
  | succ n ih =>
    intro j a ha
    rw [show intBisectFrom P Q (n + 1) j a
        = intStep P Q (j + n) (intBisectFrom P Q n j a) from rfl]
    have hprev : intBisectFrom P Q n j a < 2 ^ (j + n) := ih j a ha
    have h2 : 2 ^ (j + (n + 1)) = 2 * 2 ^ (j + n) := by
      rw [show j + (n + 1) = (j + n) + 1 by omega, pow_succ]
      ring
    unfold intStep
    split_ifs <;> omega

theorem intBisect_lt (P Q k : ℕ) : intBisect P Q k < 2 ^ k := by
  have h := intBisectFrom_lt P Q k 0 0 (by norm_num)
  rw [Nat.zero_add] at h
  exact h

theorem intStep_invariant (P Q j a : ℕ)
    (hlo : a ^ 2 * Q ≤ 2 ^ (2 * j) * P) (hhi : 2 ^ (2 * j) * P ≤ (a + 1) ^ 2 * Q) :
    (intStep P Q j a) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P ∧
      2 ^ (2 * (j + 1)) * P ≤ (intStep P Q j a + 1) ^ 2 * Q := by
  have hpow : 2 ^ (2 * (j + 1)) = 4 * 2 ^ (2 * j) := by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    norm_num
    ring
  unfold intStep
  split_ifs with h
  · refine ⟨h, ?_⟩
    rw [hpow]
    nlinarith
  · have hnot : 2 ^ (2 * (j + 1)) * P < (2 * a + 1) ^ 2 * Q := Nat.lt_of_not_le h
    refine ⟨?_, ?_⟩
    · rw [hpow]
      nlinarith
    · rw [hpow] at hnot ⊢
      exact le_of_lt hnot

theorem intBisectFrom_invariant (P Q : ℕ) :
    ∀ (n j a : ℕ), a ^ 2 * Q ≤ 2 ^ (2 * j) * P → 2 ^ (2 * j) * P ≤ (a + 1) ^ 2 * Q →
      (intBisectFrom P Q n j a) ^ 2 * Q ≤ 2 ^ (2 * (j + n)) * P ∧
        2 ^ (2 * (j + n)) * P ≤ (intBisectFrom P Q n j a + 1) ^ 2 * Q := by
  intro n
  induction n with
  | zero =>
    intro j a hlo hhi
    simpa [intBisectFrom] using! ⟨hlo, hhi⟩
  | succ n ih =>
    intro j a hlo hhi
    rw [show intBisectFrom P Q (n + 1) j a
        = intStep P Q (j + n) (intBisectFrom P Q n j a) from rfl]
    have hprev := ih j a hlo hhi
    have hnext := intStep_invariant P Q (j + n) (intBisectFrom P Q n j a) hprev.1 hprev.2
    rw [show 2 * (j + (n + 1)) = 2 * ((j + n) + 1) by omega]
    exact hnext

theorem intBisect_invariant (P Q : ℕ) (hPQ : P ≤ Q) (k : ℕ) :
    (intBisect P Q k) ^ 2 * Q ≤ 2 ^ (2 * k) * P ∧
      2 ^ (2 * k) * P ≤ (intBisect P Q k + 1) ^ 2 * Q := by
  have hlo : (0 : ℕ) ^ 2 * Q ≤ 2 ^ (2 * 0) * P := by simp
  have hhi : 2 ^ (2 * 0) * P ≤ (0 + 1) ^ 2 * Q := by
    have h1 : 2 ^ (2 * 0) * P = P := by
      rw [show 2 * 0 = 0 by norm_num, pow_zero]
      ring
    have h2 : (0 + 1) ^ 2 * Q = Q := by norm_num
    rw [h1, h2]
    exact hPQ
  have h := intBisectFrom_invariant P Q k 0 0 hlo hhi
  rw [Nat.zero_add] at h
  exact h

theorem frontier3 :
    (∀ (q S : ℚ), 0 ≤ q → 0 < S → (sqNum q S : ℚ) / (sqDen q S : ℚ) = q / (S * S) ∧
      ∀ k : ℕ,
        sqrtLo q S k = S * (((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) / 2 ^ k) ∧
        sqrtHi q S k =
          S * ((((intBisect (sqNum q S) (sqDen q S) k : ℕ) : ℚ) + 1) / 2 ^ k)) ∧
    (∀ (P Q : ℕ), 0 < Q → P ≤ Q → ∀ k : ℕ,
      (intBisect P Q k) ^ 2 * Q ≤ 2 ^ (2 * k) * P ∧
        2 ^ (2 * k) * P ≤ (intBisect P Q k + 1) ^ 2 * Q) ∧
    (∀ (P Q k : ℕ), intBisect P Q k < 2 ^ k) ∧
    (∀ (P Q j a : ℕ), 0 < Q →
      ((((2 * (a : ℚ) + 1) / 2 ^ (j + 1)) * ((2 * (a : ℚ) + 1) / 2 ^ (j + 1))
          ≤ (P : ℚ) / (Q : ℚ)) ↔
        ((2 * a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P))) ∧
    (∀ (P Q : ℕ), 0 < Q → ∀ (n j a : ℕ),
      a ^ 2 * Q ≤ 2 ^ (2 * j) * P → 2 ^ (2 * j) * P ≤ (a + 1) ^ 2 * Q →
        (intBisectFrom P Q n j a) ^ 2 * Q ≤ 2 ^ (2 * (j + n)) * P ∧
          2 ^ (2 * (j + n)) * P ≤ (intBisectFrom P Q n j a + 1) ^ 2 * Q) ∧
    (∀ (P Q j a : ℕ),
      intStep P Q j a
        = 2 * a + (if (2 * a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P then 1 else 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q S hq hS
    exact ⟨sqNum_div_sqDen q S hq hS, fun k => ⟨sqrtLo_eq_intBisect q S hq hS k,
      sqrtHi_eq_intBisect q S hq hS k⟩⟩
  · intro P Q hQ hPQ k
    exact intBisect_invariant P Q hPQ k
  · intro P Q k
    exact intBisect_lt P Q k
  · intro P Q j a
    exact test_iff P Q j a
  · intro P Q hQ n j a hlo hhi
    exact intBisectFrom_invariant P Q n j a hlo hhi
  · intro P Q j a
    exact intStep_eq P Q j a

def dblNat (x : ℕ) : ℕ := x + x

def quadNat (x : ℕ) : ℕ := dblNat (dblNat x)

theorem dblNat_eq (x : ℕ) : dblNat x = 2 * x := by unfold dblNat; ring

theorem quadNat_eq (x : ℕ) : quadNat x = 4 * x := by
  unfold quadNat dblNat
  ring

theorem dblNat_shiftLeft (n : ℕ) :
    dblNat n = binaryValue (shiftLeft n.bits 1) := by
  rw [dblNat_eq, shiftLeft_value,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  norm_num

theorem quadNat_shiftLeft (n : ℕ) :
    quadNat n = binaryValue (shiftLeft (shiftLeft n.bits 1) 1) := by
  rw [quadNat_eq, shiftLeft_value, shiftLeft_value,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  ring

structure IncrState where

  a : ℕ

  sq : ℕ

  lin : ℕ

  rhs : ℕ
  deriving DecidableEq, Repr

def incrTrial (Q : ℕ) (s : IncrState) : ℕ := quadNat s.sq + quadNat s.lin + Q

def incrBit (Q : ℕ) (s : IncrState) : ℕ := if incrTrial Q s ≤ s.rhs then 1 else 0

def incrStep (Q : ℕ) (s : IncrState) : IncrState :=
  if incrBit Q s = 1 then
    { a := dblNat s.a + 1
      sq := incrTrial Q s
      lin := dblNat s.lin + Q
      rhs := quadNat s.rhs }
  else
    { a := dblNat s.a
      sq := quadNat s.sq
      lin := dblNat s.lin
      rhs := quadNat s.rhs }

def incrInit (P : ℕ) : IncrState := ⟨0, 0, 0, quadNat P⟩

def incrIterate (Q : ℕ) : ℕ → IncrState → IncrState
  | 0, s => s
  | n + 1, s => incrStep Q (incrIterate Q n s)

theorem incrTrial_eq (Q : ℕ) (s : IncrState)
    (hsq : s.sq = s.a ^ 2 * Q) (hlin : s.lin = s.a * Q) :
    incrTrial Q s = (2 * s.a + 1) ^ 2 * Q := by
  unfold incrTrial quadNat dblNat
  rw [hsq, hlin]
  ring

theorem incrBit_eq_one_iff (Q : ℕ) (s : IncrState) :
    incrBit Q s = 1 ↔ incrTrial Q s ≤ s.rhs := by
  unfold incrBit
  split_ifs <;> simp_all

theorem incrBit_ne_one_iff (Q : ℕ) (s : IncrState) :
    incrBit Q s ≠ 1 ↔ ¬ incrTrial Q s ≤ s.rhs := by
  rw [ne_eq, incrBit_eq_one_iff]

theorem incrStep_a (P Q j : ℕ) (s : IncrState)
    (hsq : s.sq = s.a ^ 2 * Q) (hlin : s.lin = s.a * Q)
    (hrhs : s.rhs = 2 ^ (2 * (j + 1)) * P) :
    (incrStep Q s).a = intStep P Q j s.a := by
  rw [intStep_eq]
  by_cases h : incrBit Q s = 1
  · have hc : incrTrial Q s ≤ s.rhs := (incrBit_eq_one_iff Q s).mp h
    have hcond : (2 * s.a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P := by
      rwa [incrTrial_eq Q s hsq hlin, hrhs] at hc
    simp only [incrStep, if_pos h, dblNat_eq, if_pos hcond]
  · have hc : ¬ incrTrial Q s ≤ s.rhs := (incrBit_ne_one_iff Q s).mp h
    have hcond : ¬ (2 * s.a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P := by
      rwa [incrTrial_eq Q s hsq hlin, hrhs] at hc
    simp only [incrStep, if_neg h, dblNat_eq, if_neg hcond, Nat.add_zero]

theorem incrStep_invariant (Q : ℕ) (s : IncrState)
    (hsq : s.sq = s.a ^ 2 * Q) (hlin : s.lin = s.a * Q) :
    (incrStep Q s).sq = (incrStep Q s).a ^ 2 * Q ∧
      (incrStep Q s).lin = (incrStep Q s).a * Q := by
  by_cases h : incrBit Q s = 1
  · have htr : incrTrial Q s = (2 * s.a + 1) ^ 2 * Q := incrTrial_eq Q s hsq hlin
    constructor
    · simp only [incrStep, if_pos h, htr, dblNat_eq]
    · simp only [incrStep, if_pos h, hlin, dblNat_eq]
      ring
  · constructor
    · simp only [incrStep, if_neg h, hsq, quadNat_eq, dblNat_eq]
      ring
    · simp only [incrStep, if_neg h, hlin, dblNat_eq]
      ring

theorem incrStep_rhs (P Q j : ℕ) (s : IncrState)
    (hrhs : s.rhs = 2 ^ (2 * (j + 1)) * P) :
    (incrStep Q s).rhs = 2 ^ (2 * ((j + 1) + 1)) * P := by
  have h4 : (2 : ℕ) ^ (2 * ((j + 1) + 1)) = 4 * 2 ^ (2 * (j + 1)) := by
    rw [show 2 * ((j + 1) + 1) = 2 * (j + 1) + 2 by omega, pow_add]
    ring
  have hfield : (incrStep Q s).rhs = quadNat s.rhs := by
    unfold incrStep
    split_ifs <;> rfl
  calc (incrStep Q s).rhs = quadNat s.rhs := hfield
    _ = 4 * s.rhs := quadNat_eq s.rhs
    _ = 4 * (2 ^ (2 * (j + 1)) * P) := by rw [hrhs]
    _ = (4 * 2 ^ (2 * (j + 1))) * P := by rw [Nat.mul_assoc]
    _ = 2 ^ (2 * ((j + 1) + 1)) * P := by rw [h4]

theorem incrIterate_spec (P Q j : ℕ) (s : IncrState)
    (hsq : s.sq = s.a ^ 2 * Q) (hlin : s.lin = s.a * Q)
    (hrhs : s.rhs = 2 ^ (2 * (j + 1)) * P) :
    ∀ n : ℕ,
      (incrIterate Q n s).a = intBisectFrom P Q n j s.a ∧
      (incrIterate Q n s).sq = (incrIterate Q n s).a ^ 2 * Q ∧
      (incrIterate Q n s).lin = (incrIterate Q n s).a * Q ∧
      (incrIterate Q n s).rhs = 2 ^ (2 * (j + n + 1)) * P := by
  intro n
  induction n with
  | zero =>
      refine ⟨rfl, hsq, hlin, ?_⟩
      show s.rhs = 2 ^ (2 * (j + 0 + 1)) * P
      rw [hrhs, show j + 0 + 1 = j + 1 by omega]
  | succ n ih =>
      obtain ⟨ha, hsq', hlin', hrhs'⟩ := ih
      have hstep_a := incrStep_a P Q (j + n) (incrIterate Q n s) hsq' hlin' hrhs'
      have hstep_inv := incrStep_invariant Q (incrIterate Q n s) hsq' hlin'
      have hstep_rhs := incrStep_rhs P Q (j + n) (incrIterate Q n s) hrhs'
      refine ⟨?_, hstep_inv.1, hstep_inv.2, ?_⟩
      · show (incrStep Q (incrIterate Q n s)).a = intBisectFrom P Q (n + 1) j s.a
        rw [hstep_a, ha]
        rfl
      · show (incrStep Q (incrIterate Q n s)).rhs = 2 ^ (2 * (j + (n + 1) + 1)) * P
        rw [hstep_rhs]
        congr 1

theorem incrIterate_intBisect (P Q k : ℕ) :
    (incrIterate Q k (incrInit P)).a = intBisect P Q k := by
  have hsq : (incrInit P).sq = (incrInit P).a ^ 2 * Q := by simp [incrInit]
  have hlin : (incrInit P).lin = (incrInit P).a * Q := by simp [incrInit]
  have hrhs : (incrInit P).rhs = 2 ^ (2 * (0 + 1)) * P := by
    simp [incrInit, quadNat_eq]
  have h := incrIterate_spec P Q 0 (incrInit P) hsq hlin hrhs k
  simpa [intBisect] using! h.1

theorem incrIterate_invariant (P Q k : ℕ) :
    (incrIterate Q k (incrInit P)).sq = (incrIterate Q k (incrInit P)).a ^ 2 * Q ∧
    (incrIterate Q k (incrInit P)).lin = (incrIterate Q k (incrInit P)).a * Q ∧
    (incrIterate Q k (incrInit P)).rhs = 2 ^ (2 * (k + 1)) * P := by
  have hsq : (incrInit P).sq = (incrInit P).a ^ 2 * Q := by simp [incrInit]
  have hlin : (incrInit P).lin = (incrInit P).a * Q := by simp [incrInit]
  have hrhs : (incrInit P).rhs = 2 ^ (2 * (0 + 1)) * P := by
    simp [incrInit, quadNat_eq]
  have h := incrIterate_spec P Q 0 (incrInit P) hsq hlin hrhs k
  refine ⟨h.2.1, h.2.2.1, ?_⟩
  rw [h.2.2.2, show 0 + k + 1 = k + 1 by omega]

theorem incrIterate_bracket (P Q k : ℕ) (hPQ : P ≤ Q) :
    (incrIterate Q k (incrInit P)).a ^ 2 * Q ≤ 2 ^ (2 * k) * P ∧
      2 ^ (2 * k) * P ≤ ((incrIterate Q k (incrInit P)).a + 1) ^ 2 * Q := by
  have h := intBisect_invariant P Q hPQ k
  rw [incrIterate_intBisect P Q k]
  exact h

def incrTrialBits (Q : ℕ) (s : IncrState) : Bits :=
  bitAdd (bitAdd (shiftLeft s.sq.bits 2) (shiftLeft s.lin.bits 2)) Q.bits

theorem incrTrialBits_value (Q : ℕ) (s : IncrState) :
    binaryValue (incrTrialBits Q s) = incrTrial Q s := by
  unfold incrTrialBits incrTrial quadNat dblNat
  rw [bitAdd_value, bitAdd_value, shiftLeft_value, shiftLeft_value,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  ring

def incrABits (Q : ℕ) (s : IncrState) : Bits :=
  bitAdd (shiftLeft s.a.bits 1) (if incrBit Q s = 1 then [true] else [])

theorem incrABits_value (Q : ℕ) (s : IncrState) :
    binaryValue (incrABits Q s) = (incrStep Q s).a := by
  unfold incrABits
  rw [bitAdd_value, shiftLeft_value,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  by_cases h : incrBit Q s = 1
  · rw [if_pos h]
    simp only [binaryValue_singleton, bitNat, if_true]
    simp only [incrStep, if_pos h, dblNat_eq]
    norm_num
  · rw [if_neg h]
    simp only [binaryValue_nil, incrStep, if_neg h, dblNat_eq, Nat.add_zero]
    norm_num

def incrLinBits (Q : ℕ) (s : IncrState) : Bits :=
  bitAdd (shiftLeft s.lin.bits 1) (if incrBit Q s = 1 then Q.bits else [])

theorem incrLinBits_value (Q : ℕ) (s : IncrState) :
    binaryValue (incrLinBits Q s) = (incrStep Q s).lin := by
  unfold incrLinBits
  by_cases h : incrBit Q s = 1
  · rw [if_pos h]
    rw [bitAdd_value, shiftLeft_value,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    simp only [incrStep, if_pos h, dblNat_eq]
    ring
  · rw [if_neg h]
    rw [bitAdd_value, shiftLeft_value,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    simp only [binaryValue_nil, incrStep, if_neg h, dblNat_eq, Nat.add_zero]
    norm_num

theorem frontier4 :
    (∀ (Q : ℕ) (s : IncrState), incrTrial Q s = quadNat s.sq + quadNat s.lin + Q) ∧
    (∀ (P Q k : ℕ), (incrIterate Q k (incrInit P)).a = intBisect P Q k) ∧
    (∀ (P Q k : ℕ),
      (incrIterate Q k (incrInit P)).sq = (incrIterate Q k (incrInit P)).a ^ 2 * Q ∧
      (incrIterate Q k (incrInit P)).lin = (incrIterate Q k (incrInit P)).a * Q ∧
      (incrIterate Q k (incrInit P)).rhs = 2 ^ (2 * (k + 1)) * P) ∧
    (∀ (P Q k : ℕ), P ≤ Q →
      (incrIterate Q k (incrInit P)).a ^ 2 * Q ≤ 2 ^ (2 * k) * P ∧
      2 ^ (2 * k) * P ≤ ((incrIterate Q k (incrInit P)).a + 1) ^ 2 * Q) ∧
    (∀ (P Q j : ℕ) (s : IncrState), s.sq = s.a ^ 2 * Q → s.lin = s.a * Q →
      s.rhs = 2 ^ (2 * (j + 1)) * P → (incrStep Q s).a = intStep P Q j s.a) ∧
    (∀ (Q : ℕ) (s : IncrState), binaryValue (incrTrialBits Q s) = incrTrial Q s) ∧
    (∀ (Q : ℕ) (s : IncrState), binaryValue (incrABits Q s) = (incrStep Q s).a) ∧
    (∀ (Q : ℕ) (s : IncrState), binaryValue (incrLinBits Q s) = (incrStep Q s).lin) := by
  refine ⟨fun Q s => rfl, incrIterate_intBisect, incrIterate_invariant,
    incrIterate_bracket, incrStep_a, incrTrialBits_value, incrABits_value,
    incrLinBits_value⟩

namespace TrialAdd

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def bitOf : Option Bool → ℕ
  | none => 0
  | some b => if b then 1 else 0

def stepSum (c : ℕ) (a b d : Bits) : ℕ := bitOf a.head? + bitOf b.head? + bitOf d.head? + c

theorem bitOf_le_one (o : Option Bool) : bitOf o ≤ 1 := by
  cases o with
  | none => simp [bitOf]
  | some b => cases b <;> simp [bitOf]

theorem length_tail (l : Bits) : l.tail.length = l.length - 1 := List.length_tail

theorem measure_decrease (c : ℕ) (a b d : Bits)
    (h : ¬ (a = [] ∧ b = [] ∧ d = [] ∧ c = 0)) :
    2 * (a.tail.length + b.tail.length + d.tail.length) + stepSum c a b d / 2 <
      2 * (a.length + b.length + d.length) + c := by
  have hta : a.tail.length ≤ a.length := by rw [length_tail]; cases a <;> simp
  have htb : b.tail.length ≤ b.length := by rw [length_tail]; cases b <;> simp
  have htd : d.tail.length ≤ d.length := by rw [length_tail]; cases d <;> simp
  have ht : bitOf a.head? + bitOf b.head? + bitOf d.head? ≤ 3 := by
    have h1 := bitOf_le_one a.head?
    have h2 := bitOf_le_one b.head?
    have h3 := bitOf_le_one d.head?
    omega
  have hs : stepSum c a b d / 2 ≤ c + 1 := by unfold stepSum; omega
  by_cases ha : a = []
  · by_cases hb : b = []
    · by_cases hd : d = []
      · subst ha hb hd
        simp only [List.head?_nil, bitOf, stepSum, List.tail_nil, List.length_nil,
          Nat.zero_add] at hs ⊢
        have hcpos : 0 < c := by
          by_contra hh
          have hc0 : c = 0 := by omega
          exact h ⟨rfl, rfl, rfl, hc0⟩
        have := Nat.div_lt_self hcpos (by norm_num : 1 < 2)
        omega
      · have hd' : d.tail.length + 1 = d.length := by
          rw [length_tail]; cases d with
          | nil => exact absurd rfl hd
          | cons x xs => simp
        omega
    · have hb' : b.tail.length + 1 = b.length := by
        rw [length_tail]; cases b with
        | nil => exact absurd rfl hb
        | cons x xs => simp
      omega
  · have ha' : a.tail.length + 1 = a.length := by
      rw [length_tail]; cases a with
      | nil => exact absurd rfl ha
      | cons x xs => simp
    omega

structure Local where
  oa : Option Bool
  ob : Option Bool
  od : Option Bool
  c0 : Bool
  c1 : Bool
deriving DecidableEq, Fintype

instance : Inhabited Local := ⟨⟨none, none, none, false, false⟩⟩

def carryVal (v : Local) : ℕ := (if v.c0 then 1 else 0) + 2 * (if v.c1 then 1 else 0)

def Local.total (v : Local) : ℕ := bitOf v.oa + bitOf v.ob + bitOf v.od + carryVal v

def Local.outBit (v : Local) : Bool := decide (Local.total v % 2 = 1)

def Local.nextC0 (v : Local) : Bool := decide (Local.total v / 2 % 2 = 1)

def Local.nextC1 (v : Local) : Bool := decide (Local.total v / 2 / 2 = 1)

def Local.stalled (v : Local) : Bool :=
  v.oa.isNone && v.ob.isNone && v.od.isNone && decide (Local.total v = 0)

def enc (c : ℕ) : Bool × Bool := (decide (c % 2 = 1), decide (c / 2 = 1))

def dec (p : Bool × Bool) : ℕ := (if p.1 then 1 else 0) + 2 * (if p.2 then 1 else 0)

theorem dec_enc {c : ℕ} (hc : c ≤ 2) : dec (enc c) = c := by
  unfold dec enc
  interval_cases c <;> rfl

theorem carryVal_enc {c : ℕ} (hc : c ≤ 2) (oa ob od : Option Bool) :
    carryVal ⟨oa, ob, od, (enc c).1, (enc c).2⟩ = c := by
  simp only [carryVal, enc, decide_eq_true_eq]
  interval_cases c <;> rfl

def store (os a b d : Bits) : Fin 4 → Bits :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then d else os

@[simp] theorem store_zero (os a b d : Bits) : store os a b d 0 = a := by simp [store]

@[simp] theorem store_one (os a b d : Bits) : store os a b d 1 = b := by simp [store]

@[simp] theorem store_two (os a b d : Bits) : store os a b d 2 = d := by simp [store]

@[simp] theorem store_three (os a b d : Bits) : store os a b d 3 = os := by simp [store]

theorem store_update_zero (os a b d a' : Bits) :
    Function.update (store os a b d) 0 a' = store os a' b d := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_one (os a b d b' : Bits) :
    Function.update (store os a b d) 1 b' = store os a b' d := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_two (os a b d d' : Bits) :
    Function.update (store os a b d) 2 d' = store os a b d' := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_three (os a b d os' : Bits) :
    Function.update (store os a b d) 3 os' = store os' a b d := by
  funext i; fin_cases i <;> simp [store]

inductive Label | shift | step | done deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.step⟩

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Local
  | .shift =>
    .push 0 (fun _ => false)
      (.push 0 (fun _ => false)
        (.push 1 (fun _ => false)
          (.push 1 (fun _ => false)
            (.load (fun _ => ⟨none, none, none, false, false⟩)
              (.goto (fun _ => .step))))))
  | .step =>
    .pop 0 (fun v b => { v with oa := b })
      (.pop 1 (fun v b => { v with ob := b })
        (.pop 2 (fun v b => { v with od := b })
          (.branch (fun v => v.stalled) .halt
            (.push 3 (fun v => v.outBit)
              (.load (fun v => ⟨none, none, none, v.nextC0, v.nextC1⟩)
                (.goto (fun _ => .step)))))))
  | .done => .halt

def cfg (c : ℕ) (os a b d : Bits) : TM2.Cfg (fun _ : Fin 4 => Bool) Label Local :=
  ⟨some .step, ⟨none, none, none, (enc c).1, (enc c).2⟩, store os a b d⟩

def startCfg (a b d : Bits) : TM2.Cfg (fun _ : Fin 4 => Bool) Label Local :=
  ⟨some .shift, ⟨none, none, none, false, false⟩, store [] a b d⟩

theorem shift_step (a b d : Bits) :
    TM2.step program (startCfg a b d) =
      some (cfg 0 [] (false :: false :: a) (false :: false :: b) d) := by
  have henc : (enc 0).1 = false ∧ (enc 0).2 = false := by
    constructor <;> simp [enc]
  obtain ⟨h1, h2⟩ := henc
  simp only [startCfg, cfg, TM2.step, program, TM2.stepAux, store_update_zero,
    store_update_one, store_zero, store_one, h1, h2]

def total (c : ℕ) (a b d : Bits) : ℕ := bitOf a.head? + bitOf b.head? + bitOf d.head? + c

theorem stalled_iff (c : ℕ) (a b d : Bits) (hc : c ≤ 2) :
    Local.stalled ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩ = true ↔
      (a = [] ∧ b = [] ∧ d = [] ∧ c = 0) := by
  have hc0 : carryVal ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩ = c :=
    carryVal_enc hc _ _ _
  constructor
  · intro h
    simp only [Local.stalled, Bool.and_eq_true, Option.isNone_iff_eq_none,
      List.head?_eq_none_iff, decide_eq_true_eq, Local.total, hc0] at h
    obtain ⟨⟨⟨ha, hb⟩, hd⟩, htot⟩ := h
    refine ⟨ha, hb, hd, ?_⟩
    rw [ha, hb, hd] at htot
    simpa [Local.total, bitOf, carryVal, enc] using! htot
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [Local.stalled, Local.total, bitOf, carryVal, enc]

theorem step_cfg (c : ℕ) (os a b d : Bits) (hc : c ≤ 2) :
    TM2.step program (cfg c os a b d) =
      some (if a = [] ∧ b = [] ∧ d = [] ∧ c = 0 then
          ⟨none, ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩,
            store os a.tail b.tail d.tail⟩
        else
          ⟨some .step,
            ⟨none, none, none, decide (total c a b d / 2 % 2 = 1),
              decide (total c a b d / 2 / 2 = 1)⟩,
            store (decide (total c a b d % 2 = 1) :: os) a.tail b.tail d.tail⟩) := by
  unfold cfg
  by_cases h : a = [] ∧ b = [] ∧ d = [] ∧ c = 0
  · rw [if_pos h]
    have hs : Local.stalled ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩ = true :=
      (stalled_iff c a b d hc).mpr h
    simp only [TM2.step, program, TM2.stepAux, store_update_zero, store_update_one,
      store_update_two, store_zero, store_one, store_two, hs, cond]
  · rw [if_neg h]
    have hs : Local.stalled ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩ = false := by
      cases hh : Local.stalled ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩
      · rfl
      · exact absurd ((stalled_iff c a b d hc).mp hh) h
    have hc0 : carryVal ⟨a.head?, b.head?, d.head?, (enc c).1, (enc c).2⟩ = c :=
      carryVal_enc hc _ _ _
    simp only [TM2.step, program, TM2.stepAux, store_update_zero, store_update_one,
      store_update_two, store_update_three, store_zero, store_one, store_two,
      store_three, hs, cond_false, Local.nextC0, Local.nextC1,
      Local.outBit, Local.total, hc0, total]

def outWord (c : ℕ) (os a b d : Bits) : Bits :=
  if a = [] ∧ b = [] ∧ d = [] ∧ c = 0 then os
  else outWord (stepSum c a b d / 2)
    (decide (stepSum c a b d % 2 = 1) :: os) a.tail b.tail d.tail
termination_by 2 * (a.length + b.length + d.length) + c
decreasing_by exact measure_decrease c a b d ‹¬ (a = [] ∧ b = [] ∧ d = [] ∧ c = 0)›

def fuel (c : ℕ) (a b d : Bits) : ℕ :=
  if a = [] ∧ b = [] ∧ d = [] ∧ c = 0 then 1
  else 1 + fuel (stepSum c a b d / 2) a.tail b.tail d.tail
termination_by 2 * (a.length + b.length + d.length) + c
decreasing_by exact measure_decrease c a b d ‹¬ (a = [] ∧ b = [] ∧ d = [] ∧ c = 0)›

theorem binaryValue_head_tail (l : Bits) :
    binaryValue l = bitOf l.head? + 2 * binaryValue l.tail := by
  cases l with
  | nil => simp [bitOf]
  | cons b bs =>
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.ParseFramed.binaryValue_cons]
    simp [bitOf]
    omega

theorem bitOf_decide_mod (s : ℕ) : bitOf (some (decide (s % 2 = 1))) = s % 2 := by
  have h2 : s % 2 = 0 ∨ s % 2 = 1 := Nat.mod_two_eq_zero_or_one s
  rcases h2 with h | h <;> simp [bitOf, h]

def emit (c : ℕ) (a b d : Bits) : Bits :=
  if a = [] ∧ b = [] ∧ d = [] ∧ c = 0 then []
  else decide (stepSum c a b d % 2 = 1) :: emit (stepSum c a b d / 2) a.tail b.tail d.tail
termination_by 2 * (a.length + b.length + d.length) + c
decreasing_by exact measure_decrease c a b d ‹¬ (a = [] ∧ b = [] ∧ d = [] ∧ c = 0)›

theorem emit_value (c : ℕ) (a b d : Bits) :
    binaryValue (emit c a b d) = binaryValue a + binaryValue b + binaryValue d + c := by
  induction c, a, b, d using emit.induct with
  | case1 c a b d h =>
    rw [emit.eq_def, if_pos h]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp
  | case2 c a b d h ih =>
    rw [emit.eq_def, if_neg h]
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.ParseFramed.binaryValue_cons, ih]
    set s := stepSum c a b d with hsdef
    have hbit := bitOf_decide_mod s
    have ha := binaryValue_head_tail a
    have hb := binaryValue_head_tail b
    have hd := binaryValue_head_tail d
    have hmod : s % 2 + 2 * (s / 2) = s := Nat.mod_add_div s 2
    have hsum : s = bitOf a.head? + bitOf b.head? + bitOf d.head? + c := rfl
    have hif : (if decide (s % 2 = 1) = true then 1 else 0) = s % 2 := by
      simpa [bitOf] using! hbit
    rw [hif]
    omega

theorem outWord_eq (c : ℕ) (os a b d : Bits) :
    outWord c os a b d = (emit c a b d).reverse ++ os := by
  induction c, os, a, b, d using outWord.induct with
  | case1 c os a b d h =>
    rw [outWord.eq_def, if_pos h, emit.eq_def, if_pos h]
    simp
  | case2 c os a b d h ih =>
    have hem : emit c a b d =
        decide (stepSum c a b d % 2 = 1) ::
          emit (stepSum c a b d / 2) a.tail b.tail d.tail := by
      rw [emit.eq_def, if_neg h]
    rw [outWord.eq_def, if_neg h, ih, hem, List.reverse_cons, List.append_assoc,
      List.singleton_append]

theorem fuel_le (c : ℕ) (a b d : Bits) :
    fuel c a b d ≤ 2 * (a.length + b.length + d.length) + c + 1 := by
  induction c, a, b, d using fuel.induct with
  | case1 c a b d h =>
    rw [fuel.eq_def, if_pos h]
    omega
  | case2 c a b d h ih =>
    rw [fuel.eq_def, if_neg h]
    have hdec := measure_decrease c a b d h
    omega

theorem enc_zero_one : (enc 0).1 = false := by simp [enc]

theorem enc_zero_two : (enc 0).2 = false := by simp [enc]

theorem sum_le_five {c : ℕ} (hc : c ≤ 2) (a b d : Bits) :
    stepSum c a b d ≤ 5 := by
  have h1 := bitOf_le_one a.head?
  have h2 := bitOf_le_one b.head?
  have h3 := bitOf_le_one d.head?
  unfold stepSum
  omega

theorem run_fuel (c : ℕ) (os a b d : Bits) (hc : c ≤ 2) :
    stackRun program (fuel c a b d) (cfg c os a b d) =
      some ⟨none, ⟨none, none, none, false, false⟩,
        store (outWord c os a b d) [] [] []⟩ := by
  revert os
  induction c, a, b, d using fuel.induct with
  | case1 c a b d h =>
    intro os
    obtain ⟨ha, hb, hd, hc0⟩ := h
    subst ha hb hd hc0
    have hfuel : fuel 0 [] [] [] = 1 := by rw [fuel.eq_def, if_pos ⟨rfl, rfl, rfl, rfl⟩]
    have hout : outWord 0 os [] [] [] = os := by
      rw [outWord.eq_def, if_pos ⟨rfl, rfl, rfl, rfl⟩]
    have hstep := step_cfg 0 os [] [] [] (by norm_num)
    rw [if_pos ⟨rfl, rfl, rfl, rfl⟩] at hstep
    simp only [List.head?_nil, List.tail_nil] at hstep
    rw [hfuel, hout]
    simp only [stackRun, hstep, Option.bind_some, enc_zero_one, enc_zero_two]
  | case2 c a b d h ih =>
    intro os
    have hfuel : fuel c a b d = 1 + fuel (stepSum c a b d / 2) a.tail b.tail d.tail := by
      rw [fuel.eq_def, if_neg h]
    have hc' : stepSum c a b d / 2 ≤ 2 := by
      have := sum_le_five hc a b d
      omega
    have hstep := step_cfg c os a b d hc
    rw [if_neg h] at hstep
    have hout : outWord c os a b d =
        outWord (stepSum c a b d / 2)
          (decide (stepSum c a b d % 2 = 1) :: os) a.tail b.tail d.tail := by
      rw [outWord.eq_def, if_neg h]
    rw [hfuel, hout, Nat.one_add, stackRun, hstep, Option.bind_some]
    exact ih hc' (decide (stepSum c a b d % 2 = 1) :: os)

theorem program_nodes_le : programNodes program ≤ 6 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l with
  | shift =>
    simp only [program]
    repeat' rw [stackNodes]
    omega
  | step =>
    simp only [program]
    repeat' rw [stackNodes]
    omega
  | done => simp [program, stackNodes]

theorem sweep_factor_le : sweepFactor program ≤ 85 := by
  have h := program_nodes_le
  unfold sweepFactor
  nlinarith

def totalTicks (a b d : Bits) : ℕ := 1 + fuel 0 (false :: false :: a) (false :: false :: b) d

theorem stackRun_start (a b d : Bits) :
    stackRun program (totalTicks a b d) (startCfg a b d) =
      some ⟨none, ⟨none, none, none, false, false⟩,
        store (outWord 0 [] (false :: false :: a) (false :: false :: b) d) [] [] []⟩ := by
  have h := run_fuel 0 [] (false :: false :: a) (false :: false :: b) d (by norm_num)
  unfold totalTicks
  rw [Nat.add_comm, stackRun, shift_step, Option.bind_some]
  exact h

theorem initial_height (a b d : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d).stk ≤ a.length + b.length + d.length := by
  unfold Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight startCfg store
  apply Finset.sup_le
  intro i _
  fin_cases i <;> simp <;> omega

theorem shifted_length (a b d : Bits) :
    (false :: false :: a).length + (false :: false :: b).length + d.length
      = a.length + b.length + d.length + 4 := by
  simp only [List.length_cons]
  omega

theorem totalTicks_le (a b d : Bits) :
    totalTicks a b d ≤ 2 * (a.length + b.length + d.length + 4) + 2 := by
  have h := fuel_le 0 (false :: false :: a) (false :: false :: b) d
  rw [shifted_length] at h
  unfold totalTicks
  omega

theorem machine_bounds (a b d : Bits) :
    stackRunClock program (totalTicks a b d) (startCfg a b d)
        ≤ 20000 * (a.length + b.length + d.length + 4) ^ 2 ∧
      stackRunMaxClock program (totalTicks a b d) (startCfg a b d)
        ≤ 3000 * (a.length + b.length + d.length + 4) ∧
      stackRunMaxHeight program (totalTicks a b d) (startCfg a b d)
        ≤ 25 * (a.length + b.length + d.length + 4) := by
  let L := a.length + b.length + d.length + 4
  have hn := totalTicks_le a b d
  have hh := initial_height a b d
  have hnodes := program_nodes_le
  have hsweep := sweep_factor_le
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hbase : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d).stk +
      totalTicks a b d * programNodes program + 1 ≤ 25 * L := by
    have hmul : totalTicks a b d * programNodes program ≤ (2*L+2) * 6 :=
      Nat.mul_le_mul hn hnodes
    have hlen : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d).stk ≤ L := by
      dsimp [L]; omega
    omega
  have hL2 : L ≤ L ^ 2 := by nlinarith
  constructor
  · have hprod : totalTicks a b d * sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d).stk + totalTicks a b d * programNodes program + 1)
        ≤ ((2*L+2) * 85) * (25 * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul hn hsweep) hbase
    have hfin : ((2*L+2) * 85) * (25 * L) ≤ 20000 * L ^ 2 := by nlinarith
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le program _ _).trans
      (hprod.trans hfin)
  constructor
  · have hmul : sweepFactor program * (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d).stk +
        totalTicks a b d * programNodes program + 1) ≤ 85 * (25 * L) :=
      Nat.mul_le_mul hsweep hbase
    have hfin : 85 * (25 * L) ≤ 3000 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le program _ _).trans
      (hmul.trans hfin)
  · have hmul : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d).stk +
        totalTicks a b d * programNodes program ≤ L + (2*L+2) * 6 :=
      Nat.add_le_add (by dsimp [L]; omega) (Nat.mul_le_mul hn hnodes)
    have hfin : L + (2*L+2) * 6 ≤ 25 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxHeight_le program _ _).trans
      (hmul.trans hfin)

theorem shift_value (x : Bits) : binaryValue (false :: false :: x) = 4 * binaryValue x := by
  rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.ParseFramed.binaryValue_cons,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.ParseFramed.binaryValue_cons]
  simp only [Bool.false_eq_true, if_false]
  ring

theorem emit_shift_value (a b d : Bits) :
    binaryValue (emit 0 (false :: false :: a) (false :: false :: b) d)
      = 4 * binaryValue a + 4 * binaryValue b + binaryValue d := by
  rw [emit_value, shift_value, shift_value]
  ring

theorem machine_incrTrial (Q : ℕ) (s : IncrState) :
    binaryValue (emit 0 (false :: false :: s.sq.bits) (false :: false :: s.lin.bits) Q.bits)
      = incrTrial Q s := by
  rw [emit_shift_value,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  unfold incrTrial quadNat dblNat
  ring

theorem trialProgram (a b d : Bits) :
    ∃ ticks, stackRun program ticks (startCfg a b d) =
        some ⟨none, ⟨none, none, none, false, false⟩,
          store (outWord 0 [] (false :: false :: a) (false :: false :: b) d) [] [] []⟩ ∧
      ticks = totalTicks a b d ∧
      binaryValue (emit 0 (false :: false :: a) (false :: false :: b) d)
        = 4 * binaryValue a + 4 * binaryValue b + binaryValue d ∧
      stackRunClock program ticks (startCfg a b d)
        ≤ 20000 * (a.length + b.length + d.length + 4) ^ 2 ∧
      stackRunMaxClock program ticks (startCfg a b d)
        ≤ 3000 * (a.length + b.length + d.length + 4) ∧
      stackRunMaxHeight program ticks (startCfg a b d)
        ≤ 25 * (a.length + b.length + d.length + 4) := by
  obtain ⟨hclock, hmax, hheight⟩ := machine_bounds a b d
  exact ⟨totalTicks a b d, stackRun_start a b d, rfl, emit_shift_value a b d,
    hclock, hmax, hheight⟩

end TrialAdd

namespace TrialCompare

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def carryOf (c0 c1 : Bool) : ℕ := (if c0 then 1 else 0) + 2 * (if c1 then 1 else 0)

theorem carryOf_le_three (c0 c1 : Bool) : carryOf c0 c1 ≤ 3 := by
  unfold carryOf
  cases c0 <;> cases c1 <;> simp

theorem carryOf_eq_zero {c0 c1 : Bool} : carryOf c0 c1 = 0 ↔ c0 = false ∧ c1 = false := by
  unfold carryOf
  cases c0 <;> cases c1 <;> simp

def carryBit0 (t : ℕ) : Bool :=
  if t / 2 = 0 then false else if t / 2 = 1 then true else false

def carryBit1 (t : ℕ) : Bool :=
  if t / 2 = 0 then false else if t / 2 = 1 then false else true

theorem carryOf_bits (t : ℕ) : carryOf (carryBit0 t) (carryBit1 t) = min (t / 2) 2 := by
  unfold carryBit0 carryBit1 carryOf
  rcases Nat.lt_or_ge 2 (t / 2) with h | h
  · have h2 : 2 ≤ t / 2 := le_of_lt h
    have h0 : t / 2 ≠ 0 := by omega
    have h1 : t / 2 ≠ 1 := by omega
    simp [h0, h1, Nat.min_eq_right h2]
  · interval_cases h' : t / 2 <;> simp

def borrowBit (r d w : ℕ) : Bool := decide (r < d + w)

structure CState where

  a : Bits

  b : Bits

  d : Bits

  r : Bits

  c0 : Bool

  c1 : Bool

  w : Bool
deriving DecidableEq, Repr

def CState.cval (st : CState) : ℕ := carryOf st.c0 st.c1

def CState.total (st : CState) : ℕ :=
  TrialAdd.bitOf st.a.head? + TrialAdd.bitOf st.b.head? + TrialAdd.bitOf st.d.head? +
    carryOf st.c0 st.c1

def CState.value (st : CState) : ℕ :=
  binaryValue st.a + binaryValue st.b + binaryValue st.d + CState.cval st

def CState.bit (st : CState) : ℕ := CState.total st % 2

def CState.wval (st : CState) : ℕ := if st.w then 1 else 0

def CState.nextW (st : CState) : Bool :=
  borrowBit (TrialAdd.bitOf st.r.head?) (CState.total st % 2) (CState.wval st)

def CState.nextCarry (st : CState) : Bool × Bool :=
  (carryBit0 (CState.total st), carryBit1 (CState.total st))

def CState.step (st : CState) : CState :=
  ⟨st.a.tail, st.b.tail, st.d.tail, st.r.tail, (CState.nextCarry st).1,
    (CState.nextCarry st).2, CState.nextW st⟩

abbrev CState.halted (st : CState) : Prop :=
  st.a = [] ∧ st.b = [] ∧ st.d = [] ∧ st.r = [] ∧ st.c0 = false ∧ st.c1 = false

def CState.measure (st : CState) : ℕ :=
  2 * (st.a.length + st.b.length + st.d.length + st.r.length) + CState.cval st

theorem CState.bit_le_one (st : CState) : CState.bit st ≤ 1 := by
  rcases Nat.mod_two_eq_zero_or_one (CState.total st) with h | h <;> simp [CState.bit, h]

theorem CState.wval_le_one (st : CState) : CState.wval st ≤ 1 := by
  unfold CState.wval
  split_ifs <;> omega

theorem CState.cval_step_val (st : CState) :
    CState.cval (CState.step st) = min (CState.total st / 2) 2 := by
  show carryOf (carryBit0 (CState.total st)) (carryBit1 (CState.total st)) = _
  exact carryOf_bits (CState.total st)

theorem CState.cval_step_le_two (st : CState) : CState.cval (CState.step st) ≤ 2 := by
  rw [CState.cval_step_val]
  exact Nat.min_le_right _ _

theorem CState.cval_step_le (st : CState) : CState.cval (CState.step st) ≤ CState.cval st + 1 := by
  have h1 := TrialAdd.bitOf_le_one st.a.head?
  have h2 := TrialAdd.bitOf_le_one st.b.head?
  have h3 := TrialAdd.bitOf_le_one st.d.head?
  have h4 := carryOf_le_three st.c0 st.c1
  rw [CState.cval_step_val]
  unfold CState.total CState.cval at *
  omega

theorem CState.cval_step_eq (st : CState) (h : CState.cval st ≤ 2) :
    CState.cval (CState.step st) = CState.total st / 2 := by
  have h1 := TrialAdd.bitOf_le_one st.a.head?
  have h2 := TrialAdd.bitOf_le_one st.b.head?
  have h3 := TrialAdd.bitOf_le_one st.d.head?
  rw [CState.cval_step_val]
  unfold CState.total CState.cval at *
  omega

theorem length_tail_lt {l : Bits} (h : l ≠ []) : l.tail.length < l.length := by
  rw [TrialAdd.length_tail]
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => simp

theorem length_tail_le (l : Bits) : l.tail.length ≤ l.length := by
  rw [TrialAdd.length_tail]
  exact Nat.sub_le _ _

theorem CState.measure_step (st : CState) (h : ¬ CState.halted st) :
    (CState.step st).measure < st.measure := by
  unfold CState.halted at h
  show 2 * (st.a.tail.length + st.b.tail.length + st.d.tail.length + st.r.tail.length) +
      CState.cval (CState.step st) <
    2 * (st.a.length + st.b.length + st.d.length + st.r.length) + CState.cval st
  by_cases hnil : st.a = [] ∧ st.b = [] ∧ st.d = [] ∧ st.r = []
  · obtain ⟨ha, hb, hd, hr⟩ := hnil
    have hzero : CState.cval st ≠ 0 := by
      intro h0
      exact h ⟨ha, hb, hd, hr, (carryOf_eq_zero.mp h0).1, (carryOf_eq_zero.mp h0).2⟩
    have htotal : CState.total st = CState.cval st := by
      unfold CState.total CState.cval
      simp only [ha, hb, hd, List.head?_nil, TrialAdd.bitOf, Nat.zero_add]
    have hstep : CState.cval (CState.step st) = min (CState.cval st / 2) 2 := by
      rw [CState.cval_step_val, htotal]
    have hlt : min (CState.cval st / 2) 2 < CState.cval st := by
      have hpos : 0 < CState.cval st := Nat.pos_of_ne_zero hzero
      have hdiv : CState.cval st / 2 < CState.cval st := Nat.div_lt_self hpos (by norm_num)
      omega
    have hlen : st.a.tail.length + st.b.tail.length + st.d.tail.length + st.r.tail.length = 0 := by
      simp only [ha, hb, hd, hr, List.tail_nil, List.length_nil, Nat.add_zero]
    have hlen0 : st.a.length + st.b.length + st.d.length + st.r.length = 0 := by
      simp only [ha, hb, hd, hr, List.length_nil, Nat.add_zero]
    omega
  · have hstrict : st.a.tail.length + st.b.tail.length + st.d.tail.length + st.r.tail.length <
        st.a.length + st.b.length + st.d.length + st.r.length := by
      have hle1 : st.a.tail.length ≤ st.a.length := length_tail_le st.a
      have hle2 : st.b.tail.length ≤ st.b.length := length_tail_le st.b
      have hle3 : st.d.tail.length ≤ st.d.length := length_tail_le st.d
      have hle4 : st.r.tail.length ≤ st.r.length := length_tail_le st.r
      by_contra hcon
      push Not at hcon
      have e1 : st.a.tail.length = st.a.length := by omega
      have e2 : st.b.tail.length = st.b.length := by omega
      have e3 : st.d.tail.length = st.d.length := by omega
      have e4 : st.r.tail.length = st.r.length := by omega
      have ha : st.a = [] := by
        by_contra hh; have := length_tail_lt hh; omega
      have hb : st.b = [] := by
        by_contra hh; have := length_tail_lt hh; omega
      have hd : st.d = [] := by
        by_contra hh; have := length_tail_lt hh; omega
      have hr : st.r = [] := by
        by_contra hh; have := length_tail_lt hh; omega
      exact hnil ⟨ha, hb, hd, hr⟩
    have hc := CState.cval_step_le st
    omega

def CState.run (st : CState) : CState :=
  if CState.halted st then st else CState.run (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

def fuel (st : CState) : ℕ :=
  if CState.halted st then 1 else 1 + fuel (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

theorem fuel_le (st : CState) :
    fuel st ≤ 2 * (st.a.length + st.b.length + st.d.length + st.r.length) +
      CState.cval st + 1 := by
  induction st using fuel.induct with
  | case1 st h =>
    rw [fuel.eq_def, if_pos h]
    omega
  | case2 st h ih =>
    rw [fuel.eq_def, if_neg h]
    have hdec : 2 * ((CState.step st).a.length + (CState.step st).b.length +
        (CState.step st).d.length + (CState.step st).r.length) + CState.cval (CState.step st) <
        2 * (st.a.length + st.b.length + st.d.length + st.r.length) + CState.cval st :=
      CState.measure_step st h
    omega

theorem CState.value_step_aux (st : CState) :
    CState.value st = CState.bit st + 2 * (binaryValue st.a.tail + binaryValue st.b.tail +
      binaryValue st.d.tail + CState.total st / 2) := by
  have hmod := Nat.mod_add_div (CState.total st) 2
  simp only [CState.value, CState.bit, CState.cval, CState.total] at hmod ⊢
  rw [TrialAdd.binaryValue_head_tail st.a, TrialAdd.binaryValue_head_tail st.b,
    TrialAdd.binaryValue_head_tail st.d]
  generalize hm : (TrialAdd.bitOf st.a.head? + TrialAdd.bitOf st.b.head? +
    TrialAdd.bitOf st.d.head? + carryOf st.c0 st.c1) % 2 = m at hmod ⊢
  generalize hq : (TrialAdd.bitOf st.a.head? + TrialAdd.bitOf st.b.head? +
    TrialAdd.bitOf st.d.head? + carryOf st.c0 st.c1) / 2 = q at hmod ⊢
  omega

theorem CState.value_step (st : CState) (h : CState.cval st ≤ 2) :
    CState.value st = CState.bit st + 2 * CState.value (CState.step st) := by
  have hc : CState.cval (CState.step st) = CState.total st / 2 := CState.cval_step_eq st h
  rw [CState.value_step_aux]
  unfold CState.value
  rw [hc]
  rfl

theorem CState.wval_step (st : CState) :
    CState.wval (CState.step st) =
      (if TrialAdd.bitOf st.r.head? < CState.bit st + CState.wval st then 1 else 0) := by
  simp only [CState.wval, CState.nextW, CState.bit, borrowBit, CState.step]
  by_cases h : TrialAdd.bitOf st.r.head? < CState.total st % 2 + (if st.w then 1 else 0) <;>
    simp [h]

theorem CState.step_le_iff (st : CState) (h : CState.cval st ≤ 2) :
    CState.value st + CState.wval st ≤ binaryValue st.r ↔
      CState.value (CState.step st) + CState.wval (CState.step st) ≤
        binaryValue (CState.step st).r := by
  have hv := CState.value_step st h
  have hw := CState.wval_step st
  have hr : binaryValue st.r = TrialAdd.bitOf st.r.head? + 2 * binaryValue st.r.tail :=
    TrialAdd.binaryValue_head_tail st.r
  have hbit : CState.bit st ≤ 1 := CState.bit_le_one st
  have hwv : CState.wval st ≤ 1 := CState.wval_le_one st
  have hr1 : TrialAdd.bitOf st.r.head? ≤ 1 := TrialAdd.bitOf_le_one _
  have hstepr : binaryValue (CState.step st).r = binaryValue st.r.tail := rfl
  rw [hv, hw, hr, hstepr]
  by_cases hlt : TrialAdd.bitOf st.r.head? < CState.bit st + CState.wval st
  · rw [if_pos hlt]
    constructor <;> intro hgoal <;> omega
  · rw [if_neg hlt]
    constructor <;> intro hgoal <;> omega

theorem CState.run_spec (st : CState) (h : CState.cval st ≤ 2) :
    (CState.run st).halted ∧
      ((CState.run st).w = false ↔ CState.value st + CState.wval st ≤ binaryValue st.r) := by
  revert h
  induction st using CState.run.induct with
  | case1 st hh =>
    intro h
    rw [CState.run.eq_def, if_pos hh]
    refine ⟨hh, ?_⟩
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    have hvalue : CState.value st = 0 := by
      simp only [CState.value, CState.cval, ha, hb, hd, hc0, hc1, binaryValue_nil, carryOf,
        Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
    rw [hvalue, hr]
    show st.w = false ↔ 0 + (if st.w then 1 else 0) ≤ 0
    by_cases hw : st.w <;> simp [hw]
  | case2 st hh ih =>
    intro h
    rw [CState.run.eq_def, if_neg hh]
    obtain ⟨hh', hspec⟩ := ih (CState.cval_step_le_two st)
    refine ⟨hh', ?_⟩
    rw [hspec]
    exact (CState.step_le_iff st h).symm

inductive Label | shift | step | done deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.step⟩

structure Local where

  oa : Option Bool

  ob : Option Bool

  od : Option Bool

  orr : Option Bool

  c0 : Bool

  c1 : Bool

  w : Bool
deriving DecidableEq

instance : Inhabited Local := ⟨⟨none, none, none, false, false, false, false⟩⟩

def Local.total (v : Local) : ℕ :=
  TrialAdd.bitOf v.oa + TrialAdd.bitOf v.ob + TrialAdd.bitOf v.od + carryOf v.c0 v.c1

def Local.next (v : Local) : Local :=
  ⟨none, none, none, none, carryBit0 (Local.total v), carryBit1 (Local.total v),
    borrowBit (TrialAdd.bitOf v.orr) (Local.total v % 2) (if v.w then 1 else 0)⟩

def Local.stalled (v : Local) : Bool :=
  v.oa.isNone && v.ob.isNone && v.od.isNone && v.orr.isNone && decide (Local.total v = 0)

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Local
  | .shift =>
    .push 0 (fun _ => false)
      (.push 0 (fun _ => false)
        (.push 1 (fun _ => false)
          (.push 1 (fun _ => false)
            (.load (fun _ => ⟨none, none, none, none, false, false, false⟩)
              (.goto (fun _ => .step))))))
  | .step =>
    .pop 0 (fun v b => { v with oa := b })
      (.pop 1 (fun v b => { v with ob := b })
        (.pop 2 (fun v b => { v with od := b })
          (.pop 3 (fun v b => { v with orr := b })
            (.branch (fun v => v.stalled) (.goto (fun _ => .done))
              (.load Local.next (.goto (fun _ => .step)))))))
  | .done =>
    .push 4 (fun v => !v.w)
      (.load (fun _ => ⟨none, none, none, false, false, false, false⟩) .halt)

def store (os a b d r : Bits) : Fin 5 → Bits :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then d else if i = 3 then r else os

@[simp] theorem store_zero (os a b d r : Bits) : store os a b d r 0 = a := by simp [store]

@[simp] theorem store_one (os a b d r : Bits) : store os a b d r 1 = b := by simp [store]

@[simp] theorem store_two (os a b d r : Bits) : store os a b d r 2 = d := by simp [store]

@[simp] theorem store_three (os a b d r : Bits) : store os a b d r 3 = r := by simp [store]

@[simp] theorem store_four (os a b d r : Bits) : store os a b d r 4 = os := by simp [store]

theorem store_update_zero (os a b d r a' : Bits) :
    Function.update (store os a b d r) 0 a' = store os a' b d r := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_one (os a b d r b' : Bits) :
    Function.update (store os a b d r) 1 b' = store os a b' d r := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_two (os a b d r d' : Bits) :
    Function.update (store os a b d r) 2 d' = store os a b d' r := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_three (os a b d r r' : Bits) :
    Function.update (store os a b d r) 3 r' = store os a b d r' := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_four (os a b d r os' : Bits) :
    Function.update (store os a b d r) 4 os' = store os' a b d r := by
  funext i; fin_cases i <;> simp [store]

def cfg (st : CState) (os : Bits) : TM2.Cfg (fun _ : Fin 5 => Bool) Label Local :=
  ⟨some .step, ⟨none, none, none, none, st.c0, st.c1, st.w⟩, store os st.a st.b st.d st.r⟩

def shiftCfg (a b d r : Bits) : TM2.Cfg (fun _ : Fin 5 => Bool) Label Local :=
  ⟨some .shift, ⟨none, none, none, false, false, false, false⟩, store [] a b d r⟩

def startCfg (a b d r : Bits) : TM2.Cfg (fun _ : Fin 5 => Bool) Label Local :=
  shiftCfg a b d r

theorem bool_eq_false {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp_all

theorem stalled_iff (st : CState) :
    Local.stalled ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩ = true ↔
      CState.halted st := by
  have htotal : Local.total ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩ =
      CState.total st := rfl
  unfold Local.stalled CState.halted
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.head?_eq_none_iff,
    decide_eq_true_eq, htotal]
  constructor
  · rintro ⟨⟨⟨⟨ha, hb⟩, hd⟩, hr⟩, htot⟩
    have hcarry : carryOf st.c0 st.c1 = 0 := by
      have hsplit : CState.total st = carryOf st.c0 st.c1 := by
        unfold CState.total
        simp only [ha, hb, hd, List.head?_nil, TrialAdd.bitOf, Nat.zero_add]
      omega
    exact ⟨ha, hb, hd, hr, (carryOf_eq_zero.mp hcarry).1, (carryOf_eq_zero.mp hcarry).2⟩
  · rintro ⟨ha, hb, hd, hr, hc0, hc1⟩
    refine ⟨⟨⟨⟨ha, hb⟩, hd⟩, hr⟩, ?_⟩
    unfold CState.total
    simp only [ha, hb, hd, List.head?_nil, TrialAdd.bitOf, Nat.zero_add, hc0, hc1,
      carryOf, Bool.false_eq_true, if_false]

theorem shift_step (a b d r : Bits) :
    TM2.step program (shiftCfg a b d r) =
      some (cfg ⟨false :: false :: a, false :: false :: b, d, r, false, false, false⟩ []) := by
  simp only [TM2.step, program, shiftCfg, TM2.stepAux, cfg, store_zero, store_one,
    store_update_zero, store_update_one]

theorem step_cfg (st : CState) (os : Bits) :
    TM2.step program (cfg st os) =
      some (if CState.halted st then
          ⟨some .done, ⟨none, none, none, none, st.c0, st.c1, st.w⟩,
            store os st.a.tail st.b.tail st.d.tail st.r.tail⟩
        else cfg (CState.step st) os) := by
  unfold cfg
  by_cases h : CState.halted st
  · have hs : Local.stalled ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩
        = true := (stalled_iff st).mpr h
    rw [if_pos h]
    simp only [TM2.step, program, TM2.stepAux, store_update_zero, store_update_one,
      store_update_two, store_update_three, store_zero, store_one, store_two,
      store_three, hs, cond]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := h
    simp only [ha, hb, hd, hr, List.tail_nil, List.head?_nil, hc0, hc1]
  · have hfalse : Local.stalled ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1,
        st.w⟩ = false := bool_eq_false (fun hh => h ((stalled_iff st).mp hh))
    rw [if_neg h]
    simp only [TM2.step, program, TM2.stepAux, store_update_zero, store_update_one,
      store_update_two, store_update_three, store_zero, store_one, store_two,
      store_three, hfalse, cond_false]
    rfl

theorem run_fuel (st : CState) (os : Bits) :
    stackRun program (fuel st) (cfg st os) =
      some ⟨some .done,
        ⟨none, none, none, none, (CState.run st).c0, (CState.run st).c1, (CState.run st).w⟩,
        store os [] [] [] []⟩ := by
  revert os
  induction st using fuel.induct with
  | case1 st h =>
    intro os
    rw [fuel.eq_def, if_pos h]
    have hrun : CState.run st = st := by rw [CState.run.eq_def, if_pos h]
    rw [hrun]
    simp only [stackRun, step_cfg st os, if_pos h, Option.bind_some]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := h
    simp only [ha, hb, hd, hr, List.tail_nil]
  | case2 st h ih =>
    intro os
    rw [fuel.eq_def, if_neg h]
    have hrun : CState.run st = CState.run (CState.step st) := by
      rw [CState.run.eq_def, if_neg h]
    rw [hrun, Nat.one_add, stackRun, step_cfg st os, if_neg h]
    simp only [Option.bind_some]
    exact ih os

theorem done_step (c0 c1 w : Bool) (os : Bits) :
    TM2.step program
        ⟨some .done, ⟨none, none, none, none, c0, c1, w⟩, store os [] [] [] []⟩ =
      some ⟨none, ⟨none, none, none, false, false, false, false⟩,
        store ((!w) :: os) [] [] [] []⟩ := by
  cases w <;>
    simp only [program, TM2.step, TM2.stepAux, store_update_four, store_four, Bool.not_false,
      Bool.not_true]

def totalTicks (a b d r : Bits) : ℕ :=
  1 + (fuel ⟨false :: false :: a, false :: false :: b, d, r, false, false, false⟩ + 1)

theorem shift_run (a b d r : Bits) :
    stackRun program 1 (shiftCfg a b d r) =
      some (cfg ⟨false :: false :: a, false :: false :: b, d, r, false, false, false⟩ []) := by
  simp only [stackRun, shift_step, Option.bind_some]

theorem done_run (c0 c1 w : Bool) (os : Bits) :
    stackRun program 1 ⟨some .done, ⟨none, none, none, none, c0, c1, w⟩, store os [] [] [] []⟩ =
      some ⟨none, ⟨none, none, none, false, false, false, false⟩,
        store ((!w) :: os) [] [] [] []⟩ := by
  simp only [stackRun, done_step, Option.bind_some]

theorem stackRun_start (a b d r : Bits) :
    stackRun program (totalTicks a b d r) (startCfg a b d r) =
      some ⟨none, ⟨none, none, none, false, false, false, false⟩,
        store ((!((CState.run ⟨false :: false :: a, false :: false :: b, d, r, false, false,
          false⟩).w)) :: []) [] [] [] []⟩ := by
  have hloop := run_fuel ⟨false :: false :: a, false :: false :: b, d, r, false, false, false⟩ []
  have hout := done_run (CState.run ⟨false :: false :: a, false :: false :: b, d, r, false, false,
    false⟩).c0 (CState.run ⟨false :: false :: a, false :: false :: b, d, r, false, false,
    false⟩).c1 (CState.run ⟨false :: false :: a, false :: false :: b, d, r, false, false,
    false⟩).w []
  unfold totalTicks
  rw [run_add, show startCfg a b d r = shiftCfg a b d r from rfl, shift_run]
  simp only [Option.bind_some]
  rw [run_add, hloop]
  simp only [Option.bind_some]
  exact hout

theorem fuel_start_le (a b d r : Bits) :
    totalTicks a b d r ≤ 2 * (a.length + b.length + d.length + r.length + 4) + 3 := by
  have h := fuel_le ⟨false :: false :: a, false :: false :: b, d, r, false, false, false⟩
  have hlen : (false :: false :: a).length + (false :: false :: b).length +
      d.length + r.length = a.length + b.length + d.length + r.length + 4 := by
    simp only [List.length_cons]
    omega
  rw [hlen] at h
  unfold CState.cval at h
  simp only [carryOf, Bool.false_eq_true, if_false, Nat.zero_add] at h
  unfold totalTicks
  omega

theorem program_nodes_le : programNodes program ≤ 4 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l with
  | shift =>
    simp only [program]
    repeat' rw [stackNodes]
    try omega
  | step =>
    simp only [program]
    repeat' rw [stackNodes]
    try omega
  | done =>
    simp only [program]
    repeat' rw [stackNodes]
    try omega

theorem sweep_factor_le : sweepFactor program ≤ 41 := by
  have h := program_nodes_le
  unfold sweepFactor
  nlinarith

theorem initial_height (a b d r : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d r).stk ≤
      a.length + b.length + d.length + r.length := by
  unfold startCfg shiftCfg store Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro i _
  fin_cases i <;> simp <;> omega

theorem machine_bounds (a b d r : Bits) :
    stackRunClock program (totalTicks a b d r) (startCfg a b d r)
        ≤ 20000 * (a.length + b.length + d.length + r.length + 4) ^ 2 ∧
      stackRunMaxClock program (totalTicks a b d r) (startCfg a b d r)
        ≤ 3000 * (a.length + b.length + d.length + r.length + 4) ∧
      stackRunMaxHeight program (totalTicks a b d r) (startCfg a b d r)
        ≤ 25 * (a.length + b.length + d.length + r.length + 4) := by
  let L := a.length + b.length + d.length + r.length + 4
  have hn := fuel_start_le a b d r
  have hh := initial_height a b d r
  have hnodes := program_nodes_le
  have hsweep := sweep_factor_le
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hbase : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d r).stk +
      totalTicks a b d r * programNodes program + 1 ≤ 25 * L := by
    have hmul : totalTicks a b d r * programNodes program ≤ (2 * L + 3) * 4 :=
      Nat.mul_le_mul hn hnodes
    have hlen : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d r).stk ≤ L := by
      dsimp [L]; omega
    omega
  constructor
  · have hprod : totalTicks a b d r * sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d r).stk +
          totalTicks a b d r * programNodes program + 1)
        ≤ ((2 * L + 3) * 41) * (25 * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul hn hsweep) hbase
    have hfin : ((2 * L + 3) * 41) * (25 * L) ≤ 20000 * L ^ 2 := by nlinarith
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le program _ _).trans
      (hprod.trans hfin)
  constructor
  · have hmul : sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d r).stk +
          totalTicks a b d r * programNodes program + 1) ≤ 41 * (25 * L) :=
      Nat.mul_le_mul hsweep hbase
    have hfin : 41 * (25 * L) ≤ 3000 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le program _ _).trans
      (hmul.trans hfin)
  · have hmul : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg a b d r).stk +
        totalTicks a b d r * programNodes program ≤ L + (2 * L + 3) * 4 :=
      Nat.add_le_add (by dsimp [L]; omega) (Nat.mul_le_mul hn hnodes)
    have hfin : L + (2 * L + 3) * 4 ≤ 25 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxHeight_le program _ _).trans
      (hmul.trans hfin)

theorem compare_receipt (a b d r : Bits) :
    ∃ ticks, stackRun program ticks (startCfg a b d r) =
        some ⟨none, ⟨none, none, none, false, false, false, false⟩,
          store ((!((CState.run ⟨false :: false :: a, false :: false :: b, d, r, false, false,
            false⟩).w)) :: []) [] [] [] []⟩ ∧
      ticks = totalTicks a b d r ∧
      stackRunClock program ticks (startCfg a b d r)
        ≤ 20000 * (a.length + b.length + d.length + r.length + 4) ^ 2 ∧
      stackRunMaxClock program ticks (startCfg a b d r)
        ≤ 3000 * (a.length + b.length + d.length + r.length + 4) ∧
      stackRunMaxHeight program ticks (startCfg a b d r)
        ≤ 25 * (a.length + b.length + d.length + r.length + 4) := by
  obtain ⟨hclock, hmax, hheight⟩ := machine_bounds a b d r
  exact ⟨totalTicks a b d r, stackRun_start a b d r, rfl, hclock, hmax, hheight⟩

theorem machine_incrBit (Q : ℕ) (s : IncrState) :
    (!((CState.run ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits, Q.bits,
      s.rhs.bits, false, false, false⟩).w)) = decide (incrBit Q s = 1) := by
  have hspec := CState.run_spec ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits,
    Q.bits, s.rhs.bits, false, false, false⟩ (by simp [CState.cval, carryOf])
  have hval : CState.value ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits,
      Q.bits, s.rhs.bits, false, false, false⟩ = incrTrial Q s := by
    unfold CState.value CState.cval incrTrial quadNat dblNat
    rw [TrialAdd.shift_value, TrialAdd.shift_value,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    simp only [carryOf, Bool.false_eq_true, if_false, Nat.zero_add]
    ring
  have hrval : binaryValue s.rhs.bits = s.rhs :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits s.rhs
  have hw0 : CState.wval ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits, Q.bits,
      s.rhs.bits, false, false, false⟩ = 0 := rfl
  by_cases h : incrBit Q s = 1
  · have hle : incrTrial Q s ≤ s.rhs := (incrBit_eq_one_iff Q s).mp h
    have hw : (CState.run ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits, Q.bits,
        s.rhs.bits, false, false, false⟩).w = false :=
      hspec.2.mpr (by rw [hval, hrval, hw0]; simpa using! hle)
    simp [h, hw]
  · have hle : ¬ incrTrial Q s ≤ s.rhs := (incrBit_ne_one_iff Q s).mp h
    have hw : (CState.run ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits, Q.bits,
        s.rhs.bits, false, false, false⟩).w = true := by
      by_cases hh : (CState.run ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits,
          Q.bits, s.rhs.bits, false, false, false⟩).w = true
      · exact hh
      · have hf : (CState.run ⟨false :: false :: s.sq.bits, false :: false :: s.lin.bits,
            Q.bits, s.rhs.bits, false, false, false⟩).w = false := bool_eq_false (by simpa using! hh)
        exact absurd (by have := hspec.2.mp hf; rwa [hval, hrval, hw0] at this) hle
    simp [h, hw]

end TrialCompare

namespace TrialEmit

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open TrialCompare (CState fuel)

def emitT (st : CState) : Bits :=
  if CState.halted st then []
  else decide (CState.total st % 2 = 1) :: emitT (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

def emitS (st : CState) : Bits :=
  if CState.halted st then []
  else st.a.head?.getD false :: emitS (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

def emitL (st : CState) : Bits :=
  if CState.halted st then []
  else st.b.head?.getD false :: emitL (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

def emitQ (st : CState) : Bits :=
  if CState.halted st then []
  else st.d.head?.getD false :: emitQ (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

def emitR (st : CState) : Bits :=
  if CState.halted st then []
  else st.r.head?.getD false :: emitR (CState.step st)
termination_by CState.measure st
decreasing_by exact CState.measure_step st ‹¬ CState.halted st›

def emitQ2 (st : CState) : Bits := false :: emitQ st

def emitR4 (st : CState) : Bits := false :: false :: emitR st

theorem bitOf_getD (o : Option Bool) : TrialAdd.bitOf o = bitNat (o.getD false) := by
  cases o with
  | none => rfl
  | some b => cases b <;> rfl

theorem emitT_value (st : CState) (h : CState.cval st ≤ 2) :
    binaryValue (emitT st) = CState.value st := by
  revert h
  induction st using emitT.induct with
  | case1 st hh =>
    intro h
    rw [emitT.eq_def, if_pos hh]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp only [CState.value, CState.cval, ha, hb, hd, hc0, hc1, binaryValue_nil,
      TrialCompare.carryOf, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
  | case2 st hh ih =>
    intro h
    rw [emitT.eq_def, if_neg hh, binaryValue_cons',
      ih (CState.cval_step_le_two st), CState.value_step st h]
    have hbit : bitNat (decide (CState.total st % 2 = 1)) = CState.bit st := by
      unfold CState.bit
      rcases Nat.mod_two_eq_zero_or_one (CState.total st) with h2 | h2 <;> simp [bitNat, h2]
    rw [hbit]
    ring

theorem emitS_value (st : CState) : binaryValue (emitS st) = binaryValue st.a := by
  induction st using emitS.induct with
  | case1 st hh =>
    rw [emitS.eq_def, if_pos hh]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp [ha]
  | case2 st hh ih =>
    rw [emitS.eq_def, if_neg hh, binaryValue_cons', ih,
      TrialAdd.binaryValue_head_tail st.a, bitOf_getD]
    show 2 * binaryValue (CState.step st).a + bitNat ((List.head? st.a).getD false) = _
    rw [show (CState.step st).a = st.a.tail from rfl]
    omega

theorem emitL_value (st : CState) : binaryValue (emitL st) = binaryValue st.b := by
  induction st using emitL.induct with
  | case1 st hh =>
    rw [emitL.eq_def, if_pos hh]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp [hb]
  | case2 st hh ih =>
    rw [emitL.eq_def, if_neg hh, binaryValue_cons', ih,
      TrialAdd.binaryValue_head_tail st.b, bitOf_getD]
    show 2 * binaryValue (CState.step st).b + bitNat ((List.head? st.b).getD false) = _
    rw [show (CState.step st).b = st.b.tail from rfl]
    omega

theorem emitQ_value (st : CState) : binaryValue (emitQ st) = binaryValue st.d := by
  induction st using emitQ.induct with
  | case1 st hh =>
    rw [emitQ.eq_def, if_pos hh]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp [hd]
  | case2 st hh ih =>
    rw [emitQ.eq_def, if_neg hh, binaryValue_cons', ih,
      TrialAdd.binaryValue_head_tail st.d, bitOf_getD]
    show 2 * binaryValue (CState.step st).d + bitNat ((List.head? st.d).getD false) = _
    rw [show (CState.step st).d = st.d.tail from rfl]
    omega

theorem emitR_value (st : CState) : binaryValue (emitR st) = binaryValue st.r := by
  induction st using emitR.induct with
  | case1 st hh =>
    rw [emitR.eq_def, if_pos hh]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp [hr]
  | case2 st hh ih =>
    rw [emitR.eq_def, if_neg hh, binaryValue_cons', ih,
      TrialAdd.binaryValue_head_tail st.r, bitOf_getD]
    show 2 * binaryValue (CState.step st).r + bitNat ((List.head? st.r).getD false) = _
    rw [show (CState.step st).r = st.r.tail from rfl]
    omega

theorem emitQ2_value (st : CState) : binaryValue (emitQ2 st) = 2 * binaryValue st.d := by
  unfold emitQ2
  rw [binaryValue_cons', emitQ_value]
  simp [bitNat]

theorem emitR4_value (st : CState) : binaryValue (emitR4 st) = 4 * binaryValue st.r := by
  unfold emitR4
  rw [binaryValue_cons', binaryValue_cons', emitR_value]
  simp [bitNat]
  ring

structure Out where

  aa : Bits

  t : Bits

  s : Bits

  l : Bits

  q2 : Bits

  r : Bits

  qc : Bits

  cmp : Bits

def store (sq lin q rhs aa t s l q2 r qc cm : Bits) : Fin 12 → Bits :=
  fun i =>
    if i = 0 then sq else if i = 1 then lin else if i = 2 then q else
    if i = 3 then rhs else if i = 4 then aa else if i = 5 then t else
    if i = 6 then s else if i = 7 then l else if i = 8 then q2 else
    if i = 9 then r else if i = 10 then qc else cm

@[simp] theorem store_zero (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 0 = sq := by simp [store]

@[simp] theorem store_one (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 1 = lin := by simp [store]

@[simp] theorem store_two (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 2 = q := by simp [store]

@[simp] theorem store_three (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 3 = rhs := by simp [store]

@[simp] theorem store_four (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 4 = aa := by simp [store]

@[simp] theorem store_five (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 5 = t := by simp [store]

@[simp] theorem store_six (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 6 = s := by simp [store]

@[simp] theorem store_seven (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 7 = l := by simp [store]

@[simp] theorem store_eight (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 8 = q2 := by simp [store]

@[simp] theorem store_nine (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 9 = r := by simp [store]

@[simp] theorem store_ten (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 10 = qc := by simp [store]

@[simp] theorem store_eleven (sq lin q rhs aa t s l q2 r qc cm : Bits) :
    store sq lin q rhs aa t s l q2 r qc cm 11 = cm := by simp [store]

theorem store_update_zero (sq lin q rhs aa t s l q2 r qc cm sq' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 0 sq' =
      store sq' lin q rhs aa t s l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_one (sq lin q rhs aa t s l q2 r qc cm lin' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 1 lin' =
      store sq lin' q rhs aa t s l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_two (sq lin q rhs aa t s l q2 r qc cm q' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 2 q' =
      store sq lin q' rhs aa t s l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_three (sq lin q rhs aa t s l q2 r qc cm rhs' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 3 rhs' =
      store sq lin q rhs' aa t s l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_four (sq lin q rhs aa t s l q2 r qc cm aa' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 4 aa' =
      store sq lin q rhs aa' t s l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_five (sq lin q rhs aa t s l q2 r qc cm t' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 5 t' =
      store sq lin q rhs aa t' s l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_six (sq lin q rhs aa t s l q2 r qc cm s' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 6 s' =
      store sq lin q rhs aa t s' l q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_seven (sq lin q rhs aa t s l q2 r qc cm l' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 7 l' =
      store sq lin q rhs aa t s l' q2 r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_eight (sq lin q rhs aa t s l q2 r qc cm q2' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 8 q2' =
      store sq lin q rhs aa t s l q2' r qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_nine (sq lin q rhs aa t s l q2 r qc cm r' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 9 r' =
      store sq lin q rhs aa t s l q2 r' qc cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_ten (sq lin q rhs aa t s l q2 r qc cm qc' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 10 qc' =
      store sq lin q rhs aa t s l q2 r qc' cm := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_eleven (sq lin q rhs aa t s l q2 r qc cm cm' : Bits) :
    Function.update (store sq lin q rhs aa t s l q2 r qc cm) 11 cm' =
      store sq lin q rhs aa t s l q2 r qc cm' := by
  funext i; fin_cases i <;> simp [store]

def apply (st : CState) (o : Out) : Out :=
  ⟨o.aa, (emitT st).reverse ++ o.t, (emitS st).reverse ++ o.s, (emitL st).reverse ++ o.l,
    (emitQ st).reverse ++ o.q2, (emitR st).reverse ++ o.r, (emitQ st).reverse ++ o.qc,
    o.cmp⟩

def stepOut (st : CState) (o : Out) : Out :=
  ⟨o.aa, decide (CState.total st % 2 = 1) :: o.t,
    st.a.head?.getD false :: o.s, st.b.head?.getD false :: o.l,
    st.d.head?.getD false :: o.q2, st.r.head?.getD false :: o.r,
    st.d.head?.getD false :: o.qc, o.cmp⟩

inductive Label | shift | step | done deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.step⟩

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local
  | .shift =>
    .push 0 (fun _ => false) (.push 0 (fun _ => false)
      (.push 1 (fun _ => false) (.push 8 (fun _ => false)
        (.push 9 (fun _ => false) (.push 9 (fun _ => false)
          (.load (fun _ => ⟨none, none, none, none, false, false, false⟩)
            (.goto (fun _ => .step))))))))
  | .step =>
    .pop 0 (fun v b => { v with oa := b })
      (.pop 1 (fun v b => { v with ob := b })
        (.pop 2 (fun v b => { v with od := b })
          (.pop 3 (fun v b => { v with orr := b })
            (.branch (fun v => v.stalled) (.goto (fun _ => .done))
              (.push 5 (fun v => decide (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.total v % 2 = 1))
                (.push 6 (fun v => v.oa.getD false)
                  (.push 7 (fun v => v.ob.getD false)
                    (.push 8 (fun v => v.od.getD false)
                      (.push 9 (fun v => v.orr.getD false)
                        (.push 10 (fun v => v.od.getD false)
                          (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.next (.goto (fun _ => .step)))))))))))))
  | .done =>
    .push 4 (fun v => !v.w)
      (.push 11 (fun v => !v.w)
        (.load (fun _ => ⟨none, none, none, none, false, false, false⟩) .halt))

def cfg (st : CState) (o : Out) : TM2.Cfg (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  ⟨some .step, ⟨none, none, none, none, st.c0, st.c1, st.w⟩,
    store st.a st.b st.d st.r o.aa o.t o.s o.l o.q2 o.r o.qc o.cmp⟩

def startCfg (sq lin q rhs aa : Bits) : TM2.Cfg (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  ⟨some .shift, ⟨none, none, none, none, false, false, false⟩,
    store sq lin q rhs aa [] [] [] [] [] [] []⟩

def st0 (sq lin2 q rhs : Bits) : CState :=
  ⟨false :: false :: sq, false :: lin2, q, rhs, false, false, false⟩

def o0 (aa : Bits) : Out := ⟨aa, [], [], [], [false], [false, false], [], []⟩

theorem shift_step (sq lin q rhs aa : Bits) :
    TM2.step program (startCfg sq lin q rhs aa) =
      some (cfg (st0 sq lin q rhs) (o0 aa)) := by
  simp only [TM2.step, program, startCfg, cfg, st0, o0, TM2.stepAux, store_update_zero,
    store_update_one, store_update_eight, store_update_nine, store_zero, store_one,
    store_eight, store_nine]

theorem step_cfg (st : CState) (o : Out) :
    TM2.step program (cfg st o) =
      some (if CState.halted st then
          ⟨some .done, ⟨none, none, none, none, st.c0, st.c1, st.w⟩,
            store st.a.tail st.b.tail st.d.tail st.r.tail o.aa o.t o.s o.l o.q2 o.r o.qc
              o.cmp⟩
        else cfg (CState.step st) (stepOut st o)) := by
  unfold cfg
  by_cases h : CState.halted st
  · have hs : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.stalled
        ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩ = true :=
      (TrialCompare.stalled_iff st).mpr h
    rw [if_pos h]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := h
    simp only [TM2.step, program, TM2.stepAux, store_update_zero, store_update_one,
      store_update_two, store_update_three, store_zero, store_one, store_two, store_three,
      hs, cond]
    simp only [ha, hb, hd, hr, List.tail_nil, List.head?_nil, hc0, hc1]
  · have hfalse : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.stalled
        ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩ = false :=
      TrialCompare.bool_eq_false (fun hh => h ((TrialCompare.stalled_iff st).mp hh))
    rw [if_neg h]
    simp only [TM2.step, program, TM2.stepAux, store_update_zero, store_update_one,
      store_update_two, store_update_three, store_update_five, store_update_six,
      store_update_seven, store_update_eight, store_update_nine, store_update_ten,
      store_zero, store_one, store_two, store_three, store_five, store_six, store_seven,
      store_eight, store_nine, store_ten, hfalse, cond_false, stepOut, Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.next,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.total, CState.total, CState.step]
    rfl

theorem done_step (c0 c1 w : Bool) (o : Out) :
    TM2.step program
        ⟨some .done, ⟨none, none, none, none, c0, c1, w⟩,
          store [] [] [] [] o.aa o.t o.s o.l o.q2 o.r o.qc o.cmp⟩ =
      some ⟨none, ⟨none, none, none, none, false, false, false⟩,
        store [] [] [] [] ((!w) :: o.aa) o.t o.s o.l o.q2 o.r o.qc ((!w) :: o.cmp)⟩ := by
  cases w <;>
    simp only [program, TM2.step, TM2.stepAux, store_update_four, store_update_eleven,
      store_four, store_eleven, Bool.not_false, Bool.not_true]

theorem apply_step (st : CState) (o : Out) (h : ¬ CState.halted st) :
    apply st o = apply (CState.step st) (stepOut st o) := by
  unfold apply stepOut
  rw [emitT.eq_def, if_neg h, emitS.eq_def, if_neg h, emitL.eq_def, if_neg h,
    emitQ.eq_def, if_neg h, emitR.eq_def, if_neg h]
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem apply_halted (st : CState) (o : Out) (h : CState.halted st) : apply st o = o := by
  unfold apply
  rw [emitT.eq_def, if_pos h, emitS.eq_def, if_pos h, emitL.eq_def, if_pos h,
    emitQ.eq_def, if_pos h, emitR.eq_def, if_pos h]
  simp only [List.reverse_nil, List.nil_append]

theorem run_fuel (st : CState) (o : Out) (hc : CState.cval st ≤ 2) :
    stackRun program (fuel st) (cfg st o) =
      some ⟨some .done,
        ⟨none, none, none, none, (CState.run st).c0, (CState.run st).c1, (CState.run st).w⟩,
        store (CState.run st).a (CState.run st).b (CState.run st).d (CState.run st).r
          o.aa (apply st o).t (apply st o).s (apply st o).l (apply st o).q2 (apply st o).r
          (apply st o).qc (apply st o).cmp⟩ := by
  revert o hc
  induction st using TrialCompare.fuel.induct with
  | case1 st hh =>
    intro o hc
    rw [fuel.eq_def, if_pos hh]
    have hrun : CState.run st = st := by rw [CState.run.eq_def, if_pos hh]
    rw [hrun, apply_halted st o hh]
    simp only [stackRun, step_cfg st o, if_pos hh, Option.bind_some]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp only [ha, hb, hd, hr, List.tail_nil]
  | case2 st hh ih =>
    intro o hc
    rw [fuel.eq_def, if_neg hh]
    have hrun : CState.run st = CState.run (CState.step st) := by
      rw [CState.run.eq_def, if_neg hh]
    have happ : apply st o = apply (CState.step st) (stepOut st o) := apply_step st o hh
    rw [hrun, happ, Nat.one_add, stackRun, step_cfg st o, if_neg hh]
    simp only [Option.bind_some]
    exact ih (stepOut st o) (CState.cval_step_le_two st)

def totalTicks (sq lin q rhs : Bits) : ℕ :=
  1 + (fuel (st0 sq lin q rhs) + 1)

theorem shift_run (sq lin q rhs aa : Bits) :
    stackRun program 1 (startCfg sq lin q rhs aa) =
      some (cfg (st0 sq lin q rhs) (o0 aa)) := by
  simp only [stackRun, shift_step, Option.bind_some]

def doneOut (st : CState) (o : Out) : Out :=
  ⟨(!st.w) :: o.aa, o.t, o.s, o.l, o.q2, o.r, o.qc, (!st.w) :: o.cmp⟩

def runOut (sq lin q rhs aa : Bits) : Out :=
  doneOut (CState.run (st0 sq lin q rhs)) (apply (st0 sq lin q rhs) (o0 aa))

theorem start_halted_holds (sq lin q rhs : Bits) :
    CState.cval (st0 sq lin q rhs) ≤ 2 := by
  simp [st0, CState.cval, TrialCompare.carryOf]

theorem run_fuel_halted (sq lin q rhs : Bits) (o : Out) :
    stackRun program (fuel (st0 sq lin q rhs)) (cfg (st0 sq lin q rhs) o) =
      some ⟨some .done,
        ⟨none, none, none, none, (CState.run (st0 sq lin q rhs)).c0,
          (CState.run (st0 sq lin q rhs)).c1, (CState.run (st0 sq lin q rhs)).w⟩,
        store [] [] [] []
          o.aa (apply (st0 sq lin q rhs) o).t (apply (st0 sq lin q rhs) o).s
          (apply (st0 sq lin q rhs) o).l (apply (st0 sq lin q rhs) o).q2
          (apply (st0 sq lin q rhs) o).r (apply (st0 sq lin q rhs) o).qc
          (apply (st0 sq lin q rhs) o).cmp⟩ := by
  have h := run_fuel (st0 sq lin q rhs) o (start_halted_holds sq lin q rhs)
  obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ :=
    (CState.run_spec (st0 sq lin q rhs) (start_halted_holds sq lin q rhs)).1
  rw [h, ha, hb, hd, hr]

theorem stackRun_start (sq lin q rhs aa : Bits) :
    stackRun program (totalTicks sq lin q rhs) (startCfg sq lin q rhs aa) =
      some ⟨none, ⟨none, none, none, none, false, false, false⟩,
        store [] [] [] [] (runOut sq lin q rhs aa).aa (runOut sq lin q rhs aa).t
          (runOut sq lin q rhs aa).s (runOut sq lin q rhs aa).l (runOut sq lin q rhs aa).q2
          (runOut sq lin q rhs aa).r (runOut sq lin q rhs aa).qc
          (runOut sq lin q rhs aa).cmp⟩ := by
  have hloop := run_fuel_halted sq lin q rhs (o0 aa)
  have hdone := done_step (CState.run (st0 sq lin q rhs)).c0 (CState.run (st0 sq lin q rhs)).c1
    (CState.run (st0 sq lin q rhs)).w (apply (st0 sq lin q rhs) (o0 aa))
  unfold totalTicks
  rw [run_add, shift_run]
  simp only [Option.bind_some]
  rw [run_add, hloop]
  simp only [Option.bind_some]
  exact hdone

theorem fuel_start_le (sq lin q rhs : Bits) :
    totalTicks sq lin q rhs ≤ 2 * (sq.length + lin.length + q.length + rhs.length + 4) + 3 := by
  have h := TrialCompare.fuel_le (st0 sq lin q rhs)
  unfold totalTicks
  simp only [st0] at h ⊢
  have hlen : (false :: false :: sq).length + (false :: lin).length + q.length + rhs.length =
      sq.length + lin.length + q.length + rhs.length + 3 := by
    simp only [List.length_cons]
    omega
  rw [hlen] at h
  unfold CState.cval at h
  simp only [TrialCompare.carryOf, Bool.false_eq_true, if_false, Nat.zero_add] at h
  omega

theorem program_nodes_le : programNodes program ≤ 10 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l with
  | shift =>
    simp only [program]
    repeat' rw [stackNodes]
    omega
  | step =>
    simp only [program]
    repeat' rw [stackNodes]
    omega
  | done =>
    simp only [program]
    repeat' rw [stackNodes]
    omega

theorem sweep_factor_le : sweepFactor program ≤ 221 := by
  have h := program_nodes_le
  unfold sweepFactor
  nlinarith

theorem initial_height (sq lin q rhs aa : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg sq lin q rhs aa).stk ≤
      sq.length + lin.length + q.length + rhs.length + aa.length := by
  unfold startCfg store Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro i _
  fin_cases i <;> simp <;> omega

theorem machine_bounds (sq lin q rhs aa : Bits) :
    stackRunClock program (totalTicks sq lin q rhs) (startCfg sq lin q rhs aa)
        ≤ 20000 * (sq.length + lin.length + q.length + rhs.length + aa.length + 4) ^ 2 ∧
      stackRunMaxClock program (totalTicks sq lin q rhs) (startCfg sq lin q rhs aa)
        ≤ 7000 * (sq.length + lin.length + q.length + rhs.length + aa.length + 4) ∧
      stackRunMaxHeight program (totalTicks sq lin q rhs) (startCfg sq lin q rhs aa)
        ≤ 30 * (sq.length + lin.length + q.length + rhs.length + aa.length + 4) := by
  let L := sq.length + lin.length + q.length + rhs.length + aa.length + 4
  have hn := fuel_start_le sq lin q rhs
  have hn' : totalTicks sq lin q rhs ≤ 2 * L + 3 := by dsimp [L]; omega
  have hh := initial_height sq lin q rhs aa
  have hnodes := program_nodes_le
  have hsweep := sweep_factor_le
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hbase : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg sq lin q rhs aa).stk +
      totalTicks sq lin q rhs * programNodes program + 1 ≤ 30 * L := by
    have hmul : totalTicks sq lin q rhs * programNodes program ≤ (2 * L + 3) * 10 :=
      Nat.mul_le_mul hn' hnodes
    have hlen : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg sq lin q rhs aa).stk ≤ L := by
      dsimp [L]; omega
    omega
  constructor
  · have hprod : totalTicks sq lin q rhs * sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg sq lin q rhs aa).stk +
          totalTicks sq lin q rhs * programNodes program + 1)
        ≤ ((2 * L + 3) * 221) * (30 * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul hn' hsweep) hbase
    have hfin : ((2 * L + 3) * 221) * (30 * L) ≤ 20000 * L ^ 2 := by nlinarith
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le program _ _).trans
      (hprod.trans hfin)
  constructor
  · have hmul : sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg sq lin q rhs aa).stk +
          totalTicks sq lin q rhs * programNodes program + 1) ≤ 221 * (30 * L) :=
      Nat.mul_le_mul hsweep hbase
    have hfin : 221 * (30 * L) ≤ 7000 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le program _ _).trans
      (hmul.trans hfin)
  · have hmul : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg sq lin q rhs aa).stk +
        totalTicks sq lin q rhs * programNodes program ≤ L + (2 * L + 3) * 10 :=
      Nat.add_le_add (by dsimp [L]; omega) (Nat.mul_le_mul hn' hnodes)
    have hfin : L + (2 * L + 3) * 10 ≤ 30 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxHeight_le program _ _).trans
      (hmul.trans hfin)

structure MState where

  a : ℕ

  sq : ℕ

  lin2 : ℕ

  rhs : ℕ
deriving DecidableEq, Repr

def mTrial (Q : ℕ) (s : MState) : ℕ := 4 * s.sq + 2 * s.lin2 + Q

def mBit (Q : ℕ) (s : MState) : ℕ := if mTrial Q s ≤ s.rhs then 1 else 0

def mStep (Q : ℕ) (s : MState) : MState :=
  if mBit Q s = 1 then
    { a := 2 * s.a + 1, sq := mTrial Q s, lin2 := 2 * s.lin2 + 2 * Q, rhs := 4 * s.rhs }
  else
    { a := 2 * s.a, sq := 4 * s.sq, lin2 := 2 * s.lin2, rhs := 4 * s.rhs }

def mInit (P : ℕ) : MState := ⟨0, 0, 0, 4 * P⟩

def mIterate (Q : ℕ) : ℕ → MState → MState
  | 0, s => s
  | n + 1, s => mStep Q (mIterate Q n s)

theorem mBit_eq_one_iff (Q : ℕ) (s : MState) : mBit Q s = 1 ↔ mTrial Q s ≤ s.rhs := by
  unfold mBit
  split_ifs <;> simp_all

theorem mBit_ne_one_iff (Q : ℕ) (s : MState) : mBit Q s ≠ 1 ↔ ¬ mTrial Q s ≤ s.rhs := by
  rw [ne_eq, mBit_eq_one_iff]

theorem shift_one_value (x : Bits) : binaryValue (false :: x) = 2 * binaryValue x := by
  rw [binaryValue_cons']
  simp [bitNat]

theorem st0_value (sq lin2 q rhs : Bits) :
    CState.value (st0 sq lin2 q rhs) =
      4 * binaryValue sq + 2 * binaryValue lin2 + binaryValue q := by
  unfold CState.value CState.cval st0 TrialCompare.carryOf
  rw [TrialAdd.shift_value, shift_one_value]
  simp only [Bool.false_eq_true, if_false, Nat.zero_add]
  ring

theorem emitT_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitT (st0 sq lin2 q rhs)) =
      4 * binaryValue sq + 2 * binaryValue lin2 + binaryValue q := by
  rw [emitT_value _ (start_halted_holds sq lin2 q rhs), st0_value]

theorem emitS_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitS (st0 sq lin2 q rhs)) = 4 * binaryValue sq := by
  rw [emitS_value]
  show binaryValue (false :: false :: sq) = 4 * binaryValue sq
  exact TrialAdd.shift_value sq

theorem emitL_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitL (st0 sq lin2 q rhs)) = 2 * binaryValue lin2 := by
  rw [emitL_value]
  show binaryValue (false :: lin2) = 2 * binaryValue lin2
  exact shift_one_value lin2

theorem emitQ_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitQ (st0 sq lin2 q rhs)) = binaryValue q := by
  rw [emitQ_value]
  rfl

theorem emitQ2_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitQ2 (st0 sq lin2 q rhs)) = 2 * binaryValue q := by
  unfold emitQ2
  rw [binaryValue_cons', emitQ_st0]
  simp [bitNat]

theorem emitR_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitR (st0 sq lin2 q rhs)) = binaryValue rhs := by
  rw [emitR_value]
  rfl

theorem emitR4_st0 (sq lin2 q rhs : Bits) :
    binaryValue (emitR4 (st0 sq lin2 q rhs)) = 4 * binaryValue rhs := by
  unfold emitR4
  rw [binaryValue_cons', binaryValue_cons', emitR_st0]
  simp [bitNat]
  ring

theorem machine_mBit (Q : ℕ) (s : MState) :
    (!((CState.run (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)).w)) =
      decide (mBit Q s = 1) := by
  have hspec := CState.run_spec (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)
    (start_halted_holds _ _ _ _)
  have hval : CState.value (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits) = mTrial Q s := by
    rw [st0_value, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    rfl
  have hrval : binaryValue (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits).r = s.rhs := by
    show binaryValue s.rhs.bits = s.rhs
    exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits s.rhs
  have hw0 : CState.wval (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits) = 0 := rfl
  by_cases h : mBit Q s = 1
  · have hle : mTrial Q s ≤ s.rhs := (mBit_eq_one_iff Q s).mp h
    have hw : (CState.run (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)).w = false :=
      hspec.2.mpr (by rw [hval, hrval, hw0]; simpa using! hle)
    simp [h, hw]
  · have hle : ¬ mTrial Q s ≤ s.rhs := (mBit_ne_one_iff Q s).mp h
    have hw : (CState.run (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)).w = true := by
      by_cases hh : (CState.run (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)).w = true
      · exact hh
      · have hf : (CState.run (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)).w = false :=
          TrialCompare.bool_eq_false (by simpa using! hh)
        exact absurd (by have := hspec.2.mp hf; rwa [hval, hrval, hw0] at this) hle
    simp [h, hw]

theorem mStep_sq (Q : ℕ) (s : MState) :
    (mStep Q s).sq = if mBit Q s = 1 then mTrial Q s else 4 * s.sq := by
  unfold mStep
  by_cases h : mBit Q s = 1 <;> simp [h]

theorem mStep_lin2 (Q : ℕ) (s : MState) :
    (mStep Q s).lin2 = if mBit Q s = 1 then 2 * s.lin2 + 2 * Q else 2 * s.lin2 := by
  unfold mStep
  by_cases h : mBit Q s = 1 <;> simp [h]

theorem mStep_rhs_field (Q : ℕ) (s : MState) : (mStep Q s).rhs = 4 * s.rhs := by
  unfold mStep
  by_cases h : mBit Q s = 1 <;> simp [h]

theorem mStep_a_field (Q : ℕ) (s : MState) :
    (mStep Q s).a = 2 * s.a + (if mBit Q s = 1 then 1 else 0) := by
  unfold mStep
  by_cases h : mBit Q s = 1 <;> simp [h]

theorem machine_mStep (Q : ℕ) (s : MState) :
    (if (decide (mBit Q s = 1)) then
        binaryValue (emitT (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits))
      else binaryValue (emitS (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits))) =
      (mStep Q s).sq ∧
    (binaryValue (emitL (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)) +
        (if (decide (mBit Q s = 1)) then 1 else 0) *
          binaryValue (emitQ2 (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits))) =
      (mStep Q s).lin2 ∧
    binaryValue (emitR4 (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)) = (mStep Q s).rhs ∧
    binaryValue ((decide (mBit Q s = 1)) :: s.a.bits) = (mStep Q s).a := by
  have hT := emitT_st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits
  have hS := emitS_st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits
  have hL := emitL_st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits
  have hQ2 := emitQ2_st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits
  have hR := emitR4_st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits
  rw [hT, hS, hL, hQ2, hR, mStep_sq, mStep_lin2, mStep_rhs_field, mStep_a_field,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits s.sq,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits s.lin2,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits Q,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits s.rhs]
  by_cases h : mBit Q s = 1
  · simp [h, mTrial, bitNat, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  · simp [h, bitNat, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]

theorem mTrial_eq (Q : ℕ) (s : MState) (hsq : s.sq = s.a ^ 2 * Q)
    (hlin : s.lin2 = 2 * (s.a * Q)) : mTrial Q s = (2 * s.a + 1) ^ 2 * Q := by
  unfold mTrial
  rw [hsq, hlin]
  ring

theorem mStep_a (P Q j : ℕ) (s : MState) (hsq : s.sq = s.a ^ 2 * Q)
    (hlin : s.lin2 = 2 * (s.a * Q)) (hrhs : s.rhs = 2 ^ (2 * (j + 1)) * P) :
    (mStep Q s).a = intStep P Q j s.a := by
  rw [intStep_eq]
  unfold mStep
  by_cases h : mBit Q s = 1
  · have hc : mTrial Q s ≤ s.rhs := (mBit_eq_one_iff Q s).mp h
    have hcond : (2 * s.a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P := by
      rwa [mTrial_eq Q s hsq hlin, hrhs] at hc
    simp only [if_pos h, if_pos hcond]
  · have hc : ¬ mTrial Q s ≤ s.rhs := (mBit_ne_one_iff Q s).mp h
    have hcond : ¬ (2 * s.a + 1) ^ 2 * Q ≤ 2 ^ (2 * (j + 1)) * P := by
      rwa [mTrial_eq Q s hsq hlin, hrhs] at hc
    simp only [if_neg h, if_neg hcond, Nat.add_zero]

theorem mStep_invariant (Q : ℕ) (s : MState) (hsq : s.sq = s.a ^ 2 * Q)
    (hlin : s.lin2 = 2 * (s.a * Q)) :
    (mStep Q s).sq = (mStep Q s).a ^ 2 * Q ∧
      (mStep Q s).lin2 = 2 * ((mStep Q s).a * Q) := by
  unfold mStep
  by_cases h : mBit Q s = 1
  · have htr : mTrial Q s = (2 * s.a + 1) ^ 2 * Q := mTrial_eq Q s hsq hlin
    rw [if_pos h]
    rw [htr, hlin]
    constructor <;> ring
  · rw [if_neg h]
    rw [hsq, hlin]
    constructor <;> ring

theorem mStep_rhs (P Q j : ℕ) (s : MState) (hrhs : s.rhs = 2 ^ (2 * (j + 1)) * P) :
    (mStep Q s).rhs = 2 ^ (2 * ((j + 1) + 1)) * P := by
  have h4 : (2 : ℕ) ^ (2 * ((j + 1) + 1)) = 4 * 2 ^ (2 * (j + 1)) := by
    rw [show 2 * ((j + 1) + 1) = 2 * (j + 1) + 2 by omega, pow_add]
    ring
  have hfield : (mStep Q s).rhs = 4 * s.rhs := by
    unfold mStep
    split_ifs <;> rfl
  rw [hfield, hrhs, h4]
  ring

theorem mIterate_spec (P Q j : ℕ) (s : MState) (hsq : s.sq = s.a ^ 2 * Q)
    (hlin : s.lin2 = 2 * (s.a * Q)) (hrhs : s.rhs = 2 ^ (2 * (j + 1)) * P) :
    ∀ n : ℕ,
      (mIterate Q n s).a = intBisectFrom P Q n j s.a ∧
      (mIterate Q n s).sq = (mIterate Q n s).a ^ 2 * Q ∧
      (mIterate Q n s).lin2 = 2 * ((mIterate Q n s).a * Q) ∧
      (mIterate Q n s).rhs = 2 ^ (2 * (j + n + 1)) * P := by
  intro n
  induction n with
  | zero =>
      refine ⟨rfl, hsq, hlin, ?_⟩
      show s.rhs = 2 ^ (2 * (j + 0 + 1)) * P
      rw [hrhs, show j + 0 + 1 = j + 1 by omega]
  | succ n ih =>
      obtain ⟨ha, hsq', hlin', hrhs'⟩ := ih
      have hstep_a := mStep_a P Q (j + n) (mIterate Q n s) hsq' hlin' hrhs'
      have hstep_inv := mStep_invariant Q (mIterate Q n s) hsq' hlin'
      have hstep_rhs := mStep_rhs P Q (j + n) (mIterate Q n s) hrhs'
      refine ⟨?_, hstep_inv.1, hstep_inv.2, ?_⟩
      · show (mStep Q (mIterate Q n s)).a = intBisectFrom P Q (n + 1) j s.a
        rw [hstep_a, ha]
        rfl
      · show (mStep Q (mIterate Q n s)).rhs = 2 ^ (2 * (j + (n + 1) + 1)) * P
        rw [hstep_rhs]
        congr 1

theorem mIterate_intBisect (P Q k : ℕ) :
    (mIterate Q k (mInit P)).a = intBisect P Q k := by
  have hsq : (mInit P).sq = (mInit P).a ^ 2 * Q := by simp [mInit]
  have hlin : (mInit P).lin2 = 2 * ((mInit P).a * Q) := by simp [mInit]
  have hrhs : (mInit P).rhs = 2 ^ (2 * (0 + 1)) * P := by
    simp [mInit]
  have h := mIterate_spec P Q 0 (mInit P) hsq hlin hrhs k
  simpa [intBisect] using! h.1

theorem frontier5 :
    (∀ (sq lin q rhs aa : Bits),
      stackRun program (totalTicks sq lin q rhs) (startCfg sq lin q rhs aa) =
        some ⟨none, ⟨none, none, none, none, false, false, false⟩,
          store [] [] [] [] (runOut sq lin q rhs aa).aa (runOut sq lin q rhs aa).t
            (runOut sq lin q rhs aa).s (runOut sq lin q rhs aa).l (runOut sq lin q rhs aa).q2
            (runOut sq lin q rhs aa).r (runOut sq lin q rhs aa).qc
            (runOut sq lin q rhs aa).cmp⟩) ∧
    (∀ (Q : ℕ) (s : MState),
      (!((CState.run (st0 s.sq.bits s.lin2.bits Q.bits s.rhs.bits)).w)) =
        decide (mBit Q s = 1)) ∧
    (∀ (Q : ℕ) (s : MState),
      (mStep Q s).a = 2 * s.a + (if mBit Q s = 1 then 1 else 0)) ∧
    (∀ (P Q k : ℕ), (mIterate Q k (mInit P)).a = intBisect P Q k) := by
  refine ⟨stackRun_start, machine_mBit, mStep_a_field, mIterate_intBisect⟩

end TrialEmit

namespace TrialCopy

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

abbrev Local := Option Bool

inductive Label | copy | done deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.copy⟩

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Local
  | .copy =>
    .pop 0 (fun _ b => b)
      (.branch (fun v => v.isNone) (.goto (fun _ => .done))
        (.push 1 (fun v => v.getD false) (.load (fun _ => none) (.goto (fun _ => .copy)))))
  | .done => .halt

def store (src dst : Bits) : Fin 2 → Bits
  | i => if i = 0 then src else dst

@[simp] theorem store_zero (src dst : Bits) : store src dst 0 = src := by simp [store]

@[simp] theorem store_one (src dst : Bits) : store src dst 1 = dst := by simp [store]

theorem store_update_zero (src dst src' : Bits) :
    Function.update (store src dst) 0 src' = store src' dst := by
  funext i; fin_cases i <;> simp [store]

theorem store_update_one (src dst dst' : Bits) :
    Function.update (store src dst) 1 dst' = store src dst' := by
  funext i; fin_cases i <;> simp [store]

def cfg (src dst : Bits) : TM2.Cfg (fun _ : Fin 2 => Bool) Label Local :=
  ⟨some .copy, none, store src dst⟩

def startCfg (src dst : Bits) : TM2.Cfg (fun _ : Fin 2 => Bool) Label Local := cfg src dst

theorem step_cfg (b : Bool) (bs dst : Bits) :
    TM2.step program (cfg (b :: bs) dst) =
      some (cfg bs (b :: dst)) := by
  simp only [TM2.step, program, cfg, TM2.stepAux, store_update_zero, store_update_one,
    store_zero, store_one, List.head?_cons, List.tail_cons, Option.isNone, Option.getD_some,
    cond_false]

theorem step_cfg_nil (dst : Bits) :
    TM2.step program (cfg [] dst) =
      some ⟨some .done, none, store [] dst⟩ := by
  simp only [TM2.step, program, cfg, TM2.stepAux, store_update_zero, store_zero,
    List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem step_cfg_done (dst : Bits) :
    TM2.step program ⟨some .done, none, store [] dst⟩ =
      some ⟨none, none, store [] dst⟩ := by
  simp only [TM2.step, program, TM2.stepAux]

theorem run_fuel (src dst : Bits) :
    stackRun program (src.length + 2) (cfg src dst) =
      some ⟨none, none, store [] (src.reverse ++ dst)⟩ := by
  induction src generalizing dst with
  | nil =>
      show stackRun program (1 + 1) (cfg [] dst) =
        some ⟨none, none, store [] ([].reverse ++ dst)⟩
      rw [stackRun, step_cfg_nil, Option.bind_some, stackRun, step_cfg_done, Option.bind_some]
      rfl
  | cons b bs ih =>
      show stackRun program ((b :: bs).length + 2) (cfg (b :: bs) dst) =
        some ⟨none, none, store [] ((b :: bs).reverse ++ dst)⟩
      rw [show (b :: bs).length + 2 = (bs.length + 2) + 1 from rfl]
      rw [stackRun, step_cfg b bs dst, Option.bind_some]
      rw [ih (b :: dst)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem program_nodes_le : programNodes program ≤ 2 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l with
  | copy => simp [program, stackNodes]
  | done => simp only [program, stackNodes]; omega

theorem sweep_factor_le : sweepFactor program ≤ 13 := by
  have h := program_nodes_le
  unfold sweepFactor
  nlinarith

theorem initial_height (src dst : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg src dst).stk ≤
      max src.length dst.length := by
  unfold startCfg cfg store Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro i _
  fin_cases i <;> simp

theorem machine_bounds (src dst : Bits) :
    stackRunClock program (src.length + 2) (startCfg src dst)
        ≤ 3000 * (src.length + dst.length + 2) ^ 2 ∧
      stackRunMaxClock program (src.length + 2) (startCfg src dst)
        ≤ 200 * (src.length + dst.length + 2) ∧
      stackRunMaxHeight program (src.length + 2) (startCfg src dst)
        ≤ 10 * (src.length + dst.length + 2) := by
  let L := src.length + dst.length + 2
  have hn : src.length + 2 ≤ 2 * L := by dsimp [L]; omega
  have hh := initial_height src dst
  have hnodes := program_nodes_le
  have hsweep := sweep_factor_le
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hbase : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg src dst).stk +
      (src.length + 2) * programNodes program + 1 ≤ 10 * L := by
    have hmul : (src.length + 2) * programNodes program ≤ (2 * L) * 2 :=
      Nat.mul_le_mul hn hnodes
    have hlen : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg src dst).stk ≤ L := by
      dsimp [L]; omega
    omega
  constructor
  · have hprod : (src.length + 2) * sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg src dst).stk +
          (src.length + 2) * programNodes program + 1)
        ≤ ((2 * L) * 13) * (10 * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul hn hsweep) hbase
    have hfin : ((2 * L) * 13) * (10 * L) ≤ 3000 * L ^ 2 := by nlinarith
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le program _ _).trans
      (hprod.trans hfin)
  constructor
  · have hmul : sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg src dst).stk +
          (src.length + 2) * programNodes program + 1) ≤ 13 * (10 * L) :=
      Nat.mul_le_mul hsweep hbase
    have hfin : 13 * (10 * L) ≤ 200 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le program _ _).trans
      (hmul.trans hfin)
  · have hmul : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg src dst).stk +
        (src.length + 2) * programNodes program ≤ L + (2 * L) * 2 :=
      Nat.add_le_add (by dsimp [L]; omega) (Nat.mul_le_mul hn hnodes)
    have hfin : L + (2 * L) * 2 ≤ 10 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxHeight_le program _ _).trans
      (hmul.trans hfin)

theorem copy_stack (src dst : Bits) :
    (src.reverse ++ dst).reverse = dst.reverse ++ src := by
  rw [List.reverse_append, List.reverse_reverse]

theorem copy_value (src : Bits) :
    binaryValue ((src.reverse ++ []).reverse) = binaryValue src := by
  rw [copy_stack]
  simp

theorem copy_receipt (src dst : Bits) :
    stackRun program (src.length + 2) (startCfg src dst) =
        some ⟨none, none, store [] (src.reverse ++ dst)⟩ ∧
      stackRunClock program (src.length + 2) (startCfg src dst)
        ≤ 3000 * (src.length + dst.length + 2) ^ 2 ∧
      stackRunMaxClock program (src.length + 2) (startCfg src dst)
        ≤ 200 * (src.length + dst.length + 2) ∧
      stackRunMaxHeight program (src.length + 2) (startCfg src dst)
        ≤ 10 * (src.length + dst.length + 2) := by
  obtain ⟨h1, h2, h3⟩ := machine_bounds src dst
  exact ⟨run_fuel src dst, h1, h2, h3⟩

end TrialCopy

namespace TrialRound

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

open TrialCompare (CState fuel)

abbrev resetLocal :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local := ⟨none, none, none, none, false, false, false⟩

def clearBits (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  { v with
    oa := none
    ob := none
    od := none
    orr := none
    c0 := false
    c1 := false }

inductive Label

  | init

  | step

  | done

  | c4r

  | cQ

  | cS4

  | c2Q

  | cL1

  | cL2

  | cQlow

  | addL

  | addLstep

  | cShiftL

  | addS

  | addSstep

  | cShiftS
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.step⟩

structure Out where
  lA : Bits
  s : Bits
  lB : Bits
  q2 : Bits
  r4 : Bits
  qA : Bits
  qB : Bits

def apply (st : CState) (o : Out) : Out :=
  ⟨(TrialEmit.emitL st).reverse ++ o.lA, (TrialEmit.emitS st).reverse ++ o.s,
    (TrialEmit.emitL st).reverse ++ o.lB, (TrialEmit.emitQ st).reverse ++ o.q2,
    (TrialEmit.emitR st).reverse ++ o.r4, (TrialEmit.emitQ st).reverse ++ o.qA,
    (TrialEmit.emitQ st).reverse ++ o.qB⟩

def stepOut (st : CState) (o : Out) : Out :=
  ⟨st.b.head?.getD false :: o.lA, st.a.head?.getD false :: o.s,
    st.b.head?.getD false :: o.lB, st.d.head?.getD false :: o.q2,
    st.r.head?.getD false :: o.r4, st.d.head?.getD false :: o.qA,
    st.d.head?.getD false :: o.qB⟩

def copyStmt (self next : Label) (src dst : Fin 12) :
    TM2.Stmt (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  .pop src (fun v b => { v with oa := b })
    (.branch (fun v => v.oa.isNone) (.goto (fun _ => next))
      (.push dst (fun v => v.oa.getD false) (.goto (fun _ => self))))

def sum3 (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) : ℕ :=
  TrialAdd.bitOf v.oa + (if !v.w then TrialAdd.bitOf v.ob else 0) +
    (if !v.w then TrialAdd.bitOf v.od else 0) + TrialCompare.carryOf v.c0 v.c1

def sumBit (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) : Bool := decide (sum3 v % 2 = 1)

def sumNext (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  { v with
    oa := none
    ob := none
    od := none
    c0 := TrialCompare.carryBit0 (sum3 v)
    c1 := TrialCompare.carryBit1 (sum3 v) }

def emitStmt : TM2.Stmt (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  .push 5 (fun v => v.ob.getD false)
    (.push 6 (fun v => v.oa.getD false)
      (.push 7 (fun v => v.ob.getD false)
        (.push 8 (fun v => v.od.getD false)
          (.push 9 (fun v => v.orr.getD false)
            (.push 10 (fun v => v.od.getD false)
              (.push 11 (fun v => v.od.getD false)
                (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.next (.goto (fun _ => .step)))))))))

def addLStmt : TM2.Stmt (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  .pop 8 (fun v b => { v with oa := b })
    (.pop 6 (fun v b => { v with ob := b })
      (.branch (fun v => v.oa.isNone && v.ob.isNone && !v.c0 && !v.c1)
        (.goto (fun _ => .cShiftL))
        (.push 7 (fun v => sumBit v) (.load sumNext (.goto (fun _ => .addLstep))))))

def addSStmt : TM2.Stmt (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  .pop 9 (fun v b => { v with oa := b })
    (.pop 10 (fun v b => { v with ob := b })
      (.pop 5 (fun v b => { v with od := b })
        (.branch (fun v => v.oa.isNone && v.ob.isNone && v.od.isNone && !v.c0 && !v.c1)
          (.goto (fun _ => .cShiftS))
          (.push 11 (fun v => sumBit v) (.load sumNext (.goto (fun _ => .addSstep)))))))

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local
  | .init =>
    .push 8 (fun _ => false) (.push 9 (fun _ => false) (.push 9 (fun _ => false)
      (.load (fun _ => resetLocal) (.goto (fun _ => .step)))))
  | .step =>
    .pop 0 (fun v b => { v with oa := b })
      (.pop 1 (fun v b => { v with ob := b })
        (.pop 2 (fun v b => { v with od := b })
          (.pop 3 (fun v b => { v with orr := b })
            (.branch (fun v => v.stalled) (.goto (fun _ => .done)) emitStmt))))
  | .done =>
    .push 4 (fun v => !v.w) (.goto (fun _ => .c4r))
  | .c4r => copyStmt .c4r .cQ 9 3
  | .cQ => copyStmt .cQ .cS4 10 2
  | .cS4 => copyStmt .cS4 .c2Q 6 9
  | .c2Q => copyStmt .c2Q .cL1 8 6
  | .cL1 => copyStmt .cL1 .cL2 5 8
  | .cL2 => copyStmt .cL2 .cQlow 7 10
  | .cQlow => copyStmt .cQlow .addL 11 5
  | .addL =>
    .load (fun v => clearBits v) (.goto (fun _ => .addLstep))
  | .addLstep => addLStmt
  | .cShiftL =>
    .pop 7 (fun v b => { v with oa := b })
      (.branch (fun v => v.oa.isNone)
        (.push 1 (fun _ => false) (.goto (fun _ => .addS)))
        (.push 1 (fun v => v.oa.getD false) (.goto (fun _ => .cShiftL))))
  | .addS =>
    .load (fun v => clearBits v) (.goto (fun _ => .addSstep))
  | .addSstep => addSStmt
  | .cShiftS =>
    .pop 11 (fun v b => { v with oa := b })
      (.branch (fun v => v.oa.isNone)
        (.push 0 (fun _ => false) (.push 0 (fun _ => false) (.halt)))
        (.push 0 (fun v => v.oa.getD false) (.goto (fun _ => .cShiftS))))

def cfg (st : CState) (aa : Bits) (o : Out) : TM2.Cfg (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  ⟨some .step, ⟨none, none, none, none, st.c0, st.c1, st.w⟩,
    TrialEmit.store st.a st.b st.d st.r aa o.lA o.s o.lB o.q2 o.r4 o.qA o.qB⟩

def startCfg (s4 l2 q r aa : Bits) : TM2.Cfg (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  ⟨some .init, resetLocal, TrialEmit.store s4 l2 q r aa [] [] [] [] [] [] []⟩

def st0 (s4 l2 q r : Bits) : CState := ⟨s4, l2, q, r, false, false, false⟩

def o0 : Out := ⟨[], [], [], [false], [false, false], [], []⟩

theorem init_step (s4 l2 q r aa : Bits) :
    TM2.step program (startCfg s4 l2 q r aa) = some (cfg (st0 s4 l2 q r) aa o0) := by
  simp only [TM2.step, program, startCfg, cfg, st0, o0, TM2.stepAux,
    TrialEmit.store_update_eight, TrialEmit.store_update_nine,
    TrialEmit.store_eight, TrialEmit.store_nine]

theorem init_run (s4 l2 q r aa : Bits) :
    stackRun program 1 (startCfg s4 l2 q r aa) = some (cfg (st0 s4 l2 q r) aa o0) := by
  simp only [stackRun, init_step, Option.bind_some]

theorem step_cfg (st : CState) (aa : Bits) (o : Out) :
    TM2.step program (cfg st aa o) =
      some (if CState.halted st then
          ⟨some .done, ⟨none, none, none, none, st.c0, st.c1, st.w⟩,
            TrialEmit.store st.a.tail st.b.tail st.d.tail st.r.tail aa o.lA o.s o.lB o.q2 o.r4
              o.qA o.qB⟩
        else cfg (CState.step st) aa (stepOut st o)) := by
  unfold cfg
  by_cases h : CState.halted st
  · have hs : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.stalled
        ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩ = true :=
      (TrialCompare.stalled_iff st).mpr h
    rw [if_pos h]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := h
    simp only [TM2.step, program, TM2.stepAux, TrialEmit.store_update_zero,
      TrialEmit.store_update_one, TrialEmit.store_update_two, TrialEmit.store_update_three,
      TrialEmit.store_zero, TrialEmit.store_one, TrialEmit.store_two, TrialEmit.store_three,
      hs, cond]
    simp only [ha, hb, hd, hr, List.tail_nil, List.head?_nil, hc0, hc1]
  · have hfalse : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.stalled
        ⟨st.a.head?, st.b.head?, st.d.head?, st.r.head?, st.c0, st.c1, st.w⟩ = false :=
      TrialCompare.bool_eq_false (fun hh => h ((TrialCompare.stalled_iff st).mp hh))
    rw [if_neg h]
    simp only [TM2.step, program, TM2.stepAux, TrialEmit.store_update_zero,
      TrialEmit.store_update_one, TrialEmit.store_update_two, TrialEmit.store_update_three,
      TrialEmit.store_update_five, TrialEmit.store_update_six, TrialEmit.store_update_seven,
      TrialEmit.store_update_eight, TrialEmit.store_update_nine, TrialEmit.store_update_ten,
      TrialEmit.store_update_eleven, TrialEmit.store_zero, TrialEmit.store_one,
      TrialEmit.store_two, TrialEmit.store_three, TrialEmit.store_five, TrialEmit.store_six,
      TrialEmit.store_seven, TrialEmit.store_eight, TrialEmit.store_nine, TrialEmit.store_ten,
      TrialEmit.store_eleven, hfalse, cond_false, stepOut, emitStmt, Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.next, Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local.total,
      CState.total, CState.nextCarry, CState.nextW, CState.step]
    rfl

theorem apply_step (st : CState) (o : Out) (h : ¬ CState.halted st) :
    apply st o = apply (CState.step st) (stepOut st o) := by
  unfold apply stepOut
  conv_lhs =>
    rw [TrialEmit.emitL.eq_def, TrialEmit.emitS.eq_def, TrialEmit.emitQ.eq_def,
      TrialEmit.emitR.eq_def]
    simp only [if_neg h]
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem apply_halted (st : CState) (o : Out) (h : CState.halted st) : apply st o = o := by
  unfold apply
  conv_lhs =>
    rw [TrialEmit.emitL.eq_def, TrialEmit.emitS.eq_def, TrialEmit.emitQ.eq_def,
      TrialEmit.emitR.eq_def]
    simp only [if_pos h]
  simp only [List.reverse_nil, List.nil_append]

theorem run_fuel (st : CState) (aa : Bits) (o : Out) (hc : CState.cval st ≤ 2) :
    stackRun program (TrialCompare.fuel st) (cfg st aa o) =
      some ⟨some .done,
        ⟨none, none, none, none, (CState.run st).c0, (CState.run st).c1, (CState.run st).w⟩,
        TrialEmit.store (CState.run st).a (CState.run st).b (CState.run st).d (CState.run st).r aa
          (apply st o).lA (apply st o).s (apply st o).lB (apply st o).q2 (apply st o).r4
          (apply st o).qA (apply st o).qB⟩ := by
  revert aa o hc
  induction st using TrialCompare.fuel.induct with
  | case1 st hh =>
    intro aa o hc
    have hsame : cfg st aa o = cfg st aa o := rfl
    rw [hsame]
    rw [TrialCompare.fuel.eq_def, if_pos hh]
    have hrun : CState.run st = st := by rw [CState.run.eq_def, if_pos hh]
    rw [hrun, apply_halted st o hh]
    simp only [stackRun, step_cfg st aa o, if_pos hh, Option.bind_some]
    obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ := hh
    simp only [ha, hb, hd, hr, List.tail_nil]
  | case2 st hh ih =>
    intro aa o hc
    rw [TrialCompare.fuel.eq_def, if_neg hh]
    have hrun : CState.run st = CState.run (CState.step st) := by
      rw [CState.run.eq_def, if_neg hh]
    have happ : apply st o = apply (CState.step st) (stepOut st o) := apply_step st o hh
    rw [hrun, happ, Nat.one_add, stackRun, step_cfg st aa o, if_neg hh]
    simp only [Option.bind_some]
    exact ih aa (stepOut st o) (CState.cval_step_le_two st)

theorem done_step (aa : Bits) (c0 c1 w : Bool) (o : Out) :
    TM2.step program
        ⟨some .done, ⟨none, none, none, none, c0, c1, w⟩,
          TrialEmit.store [] [] [] [] aa o.lA o.s o.lB o.q2 o.r4 o.qA o.qB⟩ =
      some ⟨some .c4r, ⟨none, none, none, none, c0, c1, w⟩,
        TrialEmit.store [] [] [] [] ((!w) :: aa) o.lA o.s o.lB o.q2 o.r4 o.qA o.qB⟩ := by
  cases w <;>
    simp only [program, TM2.step, TM2.stepAux, TrialEmit.store_update_four,
      TrialEmit.store_four, Bool.not_false, Bool.not_true]

theorem done_run (aa : Bits) (c0 c1 w : Bool) (o : Out) :
    stackRun program 1
        ⟨some .done, ⟨none, none, none, none, c0, c1, w⟩,
          TrialEmit.store [] [] [] [] aa o.lA o.s o.lB o.q2 o.r4 o.qA o.qB⟩ =
      some ⟨some .c4r, ⟨none, none, none, none, c0, c1, w⟩,
        TrialEmit.store [] [] [] [] ((!w) :: aa) o.lA o.s o.lB o.q2 o.r4 o.qA o.qB⟩ := by
  simp only [stackRun, done_step, Option.bind_some]

def runState (s4 l2 q r : Bits) : CState := CState.run (st0 s4 l2 q r)

def runOut (s4 l2 q r : Bits) : Out := apply (st0 s4 l2 q r) o0

theorem start_cval (s4 l2 q r : Bits) : CState.cval (st0 s4 l2 q r) ≤ 2 := by
  simp [st0, CState.cval, TrialCompare.carryOf]

theorem emit_run (s4 l2 q r aa : Bits) :
    stackRun program (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1))
        (startCfg s4 l2 q r aa) =
      some ⟨some .c4r,
        ⟨none, none, none, none, (runState s4 l2 q r).c0, (runState s4 l2 q r).c1,
          (runState s4 l2 q r).w⟩,
        TrialEmit.store [] [] [] [] ((!(runState s4 l2 q r).w) :: aa)
          (runOut s4 l2 q r).lA (runOut s4 l2 q r).s (runOut s4 l2 q r).lB
          (runOut s4 l2 q r).q2 (runOut s4 l2 q r).r4 (runOut s4 l2 q r).qA
          (runOut s4 l2 q r).qB⟩ := by
  unfold runState runOut
  rw [run_add, init_run, Option.bind_some]
  rw [run_add, run_fuel (st0 s4 l2 q r) aa o0 (start_cval s4 l2 q r), Option.bind_some]
  obtain ⟨ha, hb, hd, hr, hc0, hc1⟩ :=
    (CState.run_spec (st0 s4 l2 q r) (start_cval s4 l2 q r)).1
  rw [ha, hb, hd, hr]
  exact done_run aa _ _ _ _

theorem emit_fuel_le (s4 l2 q r : Bits) :
    1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1) ≤
      2 * (s4.length + l2.length + q.length + r.length + 1) + 3 := by
  have h := TrialCompare.fuel_le (st0 s4 l2 q r)
  dsimp only [st0, CState.cval] at h ⊢
  simp only [TrialCompare.carryOf, Bool.false_eq_true, if_false, Nat.zero_add] at h
  omega

theorem stackNodes_program (l : Label) : stackNodes (program l) ≤ 11 := by
  cases l <;>
    simp only [program, copyStmt, emitStmt, addLStmt, addSStmt, stackNodes] <;> omega

theorem program_nodes_le : programNodes program ≤ 11 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  exact stackNodes_program l

theorem sweep_factor_le : sweepFactor program ≤ 265 := by
  have h := program_nodes_le
  have h0 : 0 ≤ programNodes program := Nat.zero_le _
  unfold sweepFactor
  nlinarith

theorem initial_height (s4 l2 q r aa : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg s4 l2 q r aa).stk ≤
      s4.length + l2.length + q.length + r.length + aa.length := by
  unfold startCfg TrialEmit.store Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro i _
  fin_cases i <;> simp <;> omega

theorem emit_bounds (s4 l2 q r aa : Bits) :
    stackRunClock program (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1))
        (startCfg s4 l2 q r aa) ≤
      40000 * (s4.length + l2.length + q.length + r.length + aa.length + 4) ^ 2 ∧
    stackRunMaxClock program (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1))
        (startCfg s4 l2 q r aa) ≤
      12000 * (s4.length + l2.length + q.length + r.length + aa.length + 4) ∧
    stackRunMaxHeight program (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1))
        (startCfg s4 l2 q r aa) ≤
      40 * (s4.length + l2.length + q.length + r.length + aa.length + 4) := by
  let L := s4.length + l2.length + q.length + r.length + aa.length + 4
  have hn := emit_fuel_le s4 l2 q r
  have hn' : 1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1) ≤ 3 * L := by dsimp [L]; omega
  have hh := initial_height s4 l2 q r aa
  have hnodes := program_nodes_le
  have hsweep := sweep_factor_le
  have hbase : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg s4 l2 q r aa).stk +
      (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * programNodes program + 1 ≤ 40 * L := by
    have hmul : (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * programNodes program ≤
        (3 * L) * 11 := Nat.mul_le_mul hn' hnodes
    have hlen : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg s4 l2 q r aa).stk ≤ L := by dsimp [L]; omega
    omega
  constructor
  · have hprod : (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg s4 l2 q r aa).stk +
          (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * programNodes program + 1) ≤
        (3 * L) * 265 * (40 * L) := by
      have h1 : (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * sweepFactor program ≤
          (3 * L) * 265 := Nat.mul_le_mul hn' hsweep
      exact Nat.mul_le_mul h1 hbase
    have hfin : 3 * L * 265 * (40 * L) ≤ 40000 * L ^ 2 := by nlinarith
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le program _ _).trans
      (hprod.trans hfin)
  constructor
  · have hmul : sweepFactor program *
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (startCfg s4 l2 q r aa).stk +
          (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * programNodes program + 1) ≤
        265 * (40 * L) := Nat.mul_le_mul hsweep hbase
    have hfin : 265 * (40 * L) ≤ 12000 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le program _ _).trans
      (hmul.trans hfin)
  · have hmul : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
        (startCfg s4 l2 q r aa).stk +
        (1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1)) * programNodes program ≤
        L + (3 * L) * 11 :=
      Nat.add_le_add (by dsimp [L]; omega) (Nat.mul_le_mul hn' hnodes)
    have hfin : L + (3 * L) * 11 ≤ 40 * L := by omega
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxHeight_le program _ _).trans
      (hmul.trans hfin)

theorem c4r_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a10 a11 : Bits) :
    TM2.step program
        ⟨some .c4r, v,
          TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 (b :: bs) a10 a11⟩ =
      some ⟨some .c4r, { v with oa := some b },
        TrialEmit.store a0 a1 a2 (b :: a3) a4 a5 a6 a7 a8 bs a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_nine,
    TrialEmit.store_update_three, TrialEmit.store_nine, TrialEmit.store_three,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem c4r_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a10 a11 : Bits) :
    TM2.step program
        ⟨some .c4r, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 [] a10 a11⟩ =
      some ⟨some .cQ, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 [] a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_nine,
    TrialEmit.store_nine, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem c4r_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a10 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .c4r, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 src a10 a11⟩ =
      some ⟨some .cQ, { v with oa := none },
        TrialEmit.store a0 a1 a2 (src.reverse ++ a3) a4 a5 a6 a7 a8 [] a10 a11⟩ := by
  induction src generalizing v a3 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, c4r_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      c4r_step b bs v a0 a1 a2 a3 a4 a5 a6 a7 a8 a10 a11, Option.bind_some]
    rw [ih _ (b :: a3)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cQ_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 : Bits) :
    TM2.step program
        ⟨some .cQ, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (b :: bs) a11⟩ =
      some ⟨some .cQ, { v with oa := some b },
        TrialEmit.store a0 a1 (b :: a2) a3 a4 a5 a6 a7 a8 a9 bs a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_ten,
    TrialEmit.store_update_two, TrialEmit.store_ten, TrialEmit.store_two,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cQ_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 : Bits) :
    TM2.step program
        ⟨some .cQ, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 [] a11⟩ =
      some ⟨some .cS4, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 [] a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_ten,
    TrialEmit.store_ten, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cQ_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cQ, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 src a11⟩ =
      some ⟨some .cS4, { v with oa := none },
        TrialEmit.store a0 a1 (src.reverse ++ a2) a3 a4 a5 a6 a7 a8 a9 [] a11⟩ := by
  induction src generalizing v a2 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cQ_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cQ_step b bs v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a11, Option.bind_some]
    rw [ih _ (b :: a2)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cS4_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cS4, v, TrialEmit.store a0 a1 a2 a3 a4 a5 (b :: bs) a7 a8 a9 a10 a11⟩ =
      some ⟨some .cS4, { v with oa := some b },
        TrialEmit.store a0 a1 a2 a3 a4 a5 bs a7 a8 (b :: a9) a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_six,
    TrialEmit.store_update_nine, TrialEmit.store_six, TrialEmit.store_nine,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cS4_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cS4, v, TrialEmit.store a0 a1 a2 a3 a4 a5 [] a7 a8 a9 a10 a11⟩ =
      some ⟨some .c2Q, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 [] a7 a8 a9 a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_six,
    TrialEmit.store_six, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cS4_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cS4, v, TrialEmit.store a0 a1 a2 a3 a4 a5 src a7 a8 a9 a10 a11⟩ =
      some ⟨some .c2Q, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 [] a7 a8 (src.reverse ++ a9) a10 a11⟩ := by
  induction src generalizing v a9 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cS4_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cS4_step b bs v a0 a1 a2 a3 a4 a5 a7 a8 a9 a10 a11, Option.bind_some]
    rw [ih _ (b :: a9)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem c2Q_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .c2Q, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 (b :: bs) a9 a10 a11⟩ =
      some ⟨some .c2Q, { v with oa := some b },
        TrialEmit.store a0 a1 a2 a3 a4 a5 (b :: a6) a7 bs a9 a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_eight,
    TrialEmit.store_update_six, TrialEmit.store_eight, TrialEmit.store_six,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem c2Q_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .c2Q, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 [] a9 a10 a11⟩ =
      some ⟨some .cL1, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 [] a9 a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_eight,
    TrialEmit.store_eight, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem c2Q_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a9 a10 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .c2Q, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 src a9 a10 a11⟩ =
      some ⟨some .cL1, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 (src.reverse ++ a6) a7 [] a9 a10 a11⟩ := by
  induction src generalizing v a6 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, c2Q_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      c2Q_step b bs v a0 a1 a2 a3 a4 a5 a6 a7 a9 a10 a11, Option.bind_some]
    rw [ih _ (b :: a6)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cL1_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a6 a7 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cL1, v, TrialEmit.store a0 a1 a2 a3 a4 (b :: bs) a6 a7 a8 a9 a10 a11⟩ =
      some ⟨some .cL1, { v with oa := some b },
        TrialEmit.store a0 a1 a2 a3 a4 bs a6 a7 (b :: a8) a9 a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_five,
    TrialEmit.store_update_eight, TrialEmit.store_five, TrialEmit.store_eight,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cL1_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a6 a7 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cL1, v, TrialEmit.store a0 a1 a2 a3 a4 [] a6 a7 a8 a9 a10 a11⟩ =
      some ⟨some .cL2, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 [] a6 a7 a8 a9 a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_five,
    TrialEmit.store_five, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cL1_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a6 a7 a8 a9 a10 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cL1, v, TrialEmit.store a0 a1 a2 a3 a4 src a6 a7 a8 a9 a10 a11⟩ =
      some ⟨some .cL2, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 [] a6 a7 (src.reverse ++ a8) a9 a10 a11⟩ := by
  induction src generalizing v a8 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cL1_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cL1_step b bs v a0 a1 a2 a3 a4 a6 a7 a8 a9 a10 a11, Option.bind_some]
    rw [ih _ (b :: a8)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cL2_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cL2, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 (b :: bs) a8 a9 a10 a11⟩ =
      some ⟨some .cL2, { v with oa := some b },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 bs a8 a9 (b :: a10) a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_seven,
    TrialEmit.store_update_ten, TrialEmit.store_seven, TrialEmit.store_ten,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cL2_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cL2, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 [] a8 a9 a10 a11⟩ =
      some ⟨some .cQlow, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 [] a8 a9 a10 a11⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_seven,
    TrialEmit.store_seven, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cL2_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cL2, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 src a8 a9 a10 a11⟩ =
      some ⟨some .cQlow, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 [] a8 a9 (src.reverse ++ a10) a11⟩ := by
  induction src generalizing v a10 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cL2_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cL2_step b bs v a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11, Option.bind_some]
    rw [ih _ (b :: a10)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cQlow_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Bits) :
    TM2.step program
        ⟨some .cQlow, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (b :: bs)⟩ =
      some ⟨some .cQlow, { v with oa := some b },
        TrialEmit.store a0 a1 a2 a3 a4 (b :: a5) a6 a7 a8 a9 a10 bs⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_eleven,
    TrialEmit.store_update_five, TrialEmit.store_eleven, TrialEmit.store_five,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cQlow_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Bits) :
    TM2.step program
        ⟨some .cQlow, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 []⟩ =
      some ⟨some .addL, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 []⟩ := by
  simp only [program, copyStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_eleven,
    TrialEmit.store_eleven, List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cQlow_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cQlow, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 src⟩ =
      some ⟨some .addL, { v with oa := none },
        TrialEmit.store a0 a1 a2 a3 a4 (src.reverse ++ a5) a6 a7 a8 a9 a10 []⟩ := by
  induction src generalizing v a5 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cQlow_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cQlow_step b bs v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, Option.bind_some]
    rw [ih _ (b :: a5)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cShiftL_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cShiftL, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 (b :: bs) a8 a9 a10 a11⟩ =
      some ⟨some .cShiftL, { v with oa := some b },
        TrialEmit.store a0 (b :: a1) a2 a3 a4 a5 a6 bs a8 a9 a10 a11⟩ := by
  simp only [program, TM2.step, TM2.stepAux, TrialEmit.store_update_seven,
    TrialEmit.store_update_one, TrialEmit.store_seven, TrialEmit.store_one,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cShiftL_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .cShiftL, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 [] a8 a9 a10 a11⟩ =
      some ⟨some .addS, { v with oa := none },
        TrialEmit.store a0 (false :: a1) a2 a3 a4 a5 a6 [] a8 a9 a10 a11⟩ := by
  simp only [program, TM2.step, TM2.stepAux, TrialEmit.store_update_seven,
    TrialEmit.store_update_one, TrialEmit.store_seven, TrialEmit.store_one,
    List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cShiftL_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cShiftL, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 src a8 a9 a10 a11⟩ =
      some ⟨some .addS, { v with oa := none },
        TrialEmit.store a0 (false :: (src.reverse ++ a1)) a2 a3 a4 a5 a6 [] a8 a9 a10 a11⟩ := by
  induction src generalizing v a1 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cShiftL_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cShiftL_step b bs v a0 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11, Option.bind_some]
    rw [ih _ (b :: a1)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cShiftS_step (b : Bool) (bs : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Bits) :
    TM2.step program
        ⟨some .cShiftS, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (b :: bs)⟩ =
      some ⟨some .cShiftS, { v with oa := some b },
        TrialEmit.store (b :: a0) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 bs⟩ := by
  simp only [program, TM2.step, TM2.stepAux, TrialEmit.store_update_eleven,
    TrialEmit.store_update_zero, TrialEmit.store_eleven, TrialEmit.store_zero,
    List.head?_cons, List.tail_cons, Option.getD_some, Option.isNone, cond]

theorem cShiftS_nil (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Bits) :
    TM2.step program
        ⟨some .cShiftS, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 []⟩ =
      some ⟨none, { v with oa := none },
        TrialEmit.store (false :: false :: a0) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 []⟩ := by
  simp only [program, TM2.step, TM2.stepAux, TrialEmit.store_update_eleven,
    TrialEmit.store_update_zero, TrialEmit.store_eleven, TrialEmit.store_zero,
    List.head?_nil, List.tail_nil, Option.isNone, cond]

theorem cShiftS_run (src : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Bits) :
    stackRun program (src.length + 1)
        ⟨some .cShiftS, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 src⟩ =
      some ⟨none, { v with oa := none },
        TrialEmit.store (false :: false :: (src.reverse ++ a0)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
          []⟩ := by
  induction src generalizing v a0 with
  | nil =>
    show stackRun program 1 _ = _
    rw [stackRun, cShiftS_nil, Option.bind_some]
    rfl
  | cons b bs ih =>
    show stackRun program ((b :: bs).length + 1) _ = _
    rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 from rfl, stackRun,
      cShiftS_step b bs v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, Option.bind_some]
    rw [ih _ (b :: a0)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

structure AState where
  x : Bits
  y : Bits
  z : Bits
  w : Bool
  c0 : Bool
  c1 : Bool
deriving DecidableEq

def AState.cval (st : AState) : ℕ := TrialCompare.carryOf st.c0 st.c1

def AState.total (st : AState) : ℕ :=
  TrialAdd.bitOf st.x.head? + (if !st.w then TrialAdd.bitOf st.y.head? else 0) +
    (if !st.w then TrialAdd.bitOf st.z.head? else 0) + st.cval

def AState.value (st : AState) : ℕ :=
  binaryValue st.x + (if !st.w then binaryValue st.y else 0) +
    (if !st.w then binaryValue st.z else 0) + st.cval

def AState.bit (st : AState) : ℕ := st.total % 2

def AState.outBit (st : AState) : Bool := decide (st.total % 2 = 1)

def AState.next (st : AState) : AState :=
  ⟨st.x.tail, st.y.tail, st.z.tail, st.w,
    TrialCompare.carryBit0 st.total, TrialCompare.carryBit1 st.total⟩

abbrev AState.halted (st : AState) : Prop :=
  st.x = [] ∧ st.y = [] ∧ st.z = [] ∧ st.c0 = false ∧ st.c1 = false

def AState.measure (st : AState) : ℕ :=
  2 * (st.x.length + st.y.length + st.z.length) + st.cval

theorem AState.total_le (st : AState) : st.total ≤ 3 + st.cval := by
  have h1 := TrialAdd.bitOf_le_one st.x.head?
  have h2 := TrialAdd.bitOf_le_one st.y.head?
  have h3 := TrialAdd.bitOf_le_one st.z.head?
  unfold AState.total
  split_ifs <;> omega

theorem AState.cval_next (st : AState) : (AState.next st).cval = min (st.total / 2) 2 := by
  show TrialCompare.carryOf (TrialCompare.carryBit0 st.total) (TrialCompare.carryBit1 st.total) =
    min (st.total / 2) 2
  exact TrialCompare.carryOf_bits st.total

theorem AState.cval_next_le_two (st : AState) : (AState.next st).cval ≤ 2 := by
  rw [AState.cval_next]
  exact Nat.min_le_right _ _

theorem AState.cval_next_le (st : AState) : (AState.next st).cval ≤ st.cval + 1 := by
  have h := AState.total_le st
  rw [AState.cval_next]
  omega

theorem AState.measure_step (st : AState) (h : ¬ st.halted) :
    (AState.next st).measure < st.measure := by
  unfold AState.halted at h
  by_cases hnil : st.x = [] ∧ st.y = [] ∧ st.z = []
  · obtain ⟨hx, hy, hz⟩ := hnil
    have hc0 : st.cval ≠ 0 := by
      intro h0
      exact h ⟨hx, hy, hz, (TrialCompare.carryOf_eq_zero.mp h0).1,
        (TrialCompare.carryOf_eq_zero.mp h0).2⟩
    have htotal : st.total = st.cval := by
      unfold AState.total
      rw [hx, hy, hz]
      simp only [List.head?_nil, TrialAdd.bitOf, Nat.zero_add]
      split_ifs <;> simp
    have hnext : (AState.next st).cval = min (st.cval / 2) 2 := by
      rw [AState.cval_next, htotal]
    have hpos : 0 < st.cval := Nat.pos_of_ne_zero hc0
    have hlt : min (st.cval / 2) 2 < st.cval := by
      have hdiv : st.cval / 2 < st.cval := Nat.div_lt_self hpos (by norm_num)
      omega
    show 2 * ((AState.next st).x.length + (AState.next st).y.length +
        (AState.next st).z.length) + (AState.next st).cval <
      2 * (st.x.length + st.y.length + st.z.length) + st.cval
    rw [hnext]
    have hx' : (AState.next st).x.length = 0 := by simp [AState.next, hx]
    have hy' : (AState.next st).y.length = 0 := by simp [AState.next, hy]
    have hz' : (AState.next st).z.length = 0 := by simp [AState.next, hz]
    rw [hx', hy', hz']
    omega
  · have hsum : (AState.next st).x.length + (AState.next st).y.length +
        (AState.next st).z.length < st.x.length + st.y.length + st.z.length := by
      have hxle : (AState.next st).x.length ≤ st.x.length := by
        simp only [AState.next]
        exact TrialCompare.length_tail_le st.x
      have hyle : (AState.next st).y.length ≤ st.y.length := by
        simp only [AState.next]
        exact TrialCompare.length_tail_le st.y
      have hzle : (AState.next st).z.length ≤ st.z.length := by
        simp only [AState.next]
        exact TrialCompare.length_tail_le st.z
      by_contra hcon
      push Not at hcon
      have e1 : (AState.next st).x.length = st.x.length := by omega
      have e2 : (AState.next st).y.length = st.y.length := by omega
      have e3 : (AState.next st).z.length = st.z.length := by omega
      have e1' : st.x.tail.length = st.x.length := by simpa only [AState.next] using! e1
      have e2' : st.y.tail.length = st.y.length := by simpa only [AState.next] using! e2
      have e3' : st.z.tail.length = st.z.length := by simpa only [AState.next] using! e3
      have hx : st.x = [] := by
        by_contra hh
        have hlt := TrialCompare.length_tail_lt hh
        omega
      have hy : st.y = [] := by
        by_contra hh
        have hlt := TrialCompare.length_tail_lt hh
        omega
      have hz : st.z = [] := by
        by_contra hh
        have hlt := TrialCompare.length_tail_lt hh
        omega
      exact hnil ⟨hx, hy, hz⟩
    have hc := AState.cval_next_le st
    show 2 * ((AState.next st).x.length + (AState.next st).y.length +
        (AState.next st).z.length) + (AState.next st).cval <
      2 * (st.x.length + st.y.length + st.z.length) + st.cval
    omega

def AState.run (st : AState) : AState :=
  if st.halted then st else AState.run (AState.next st)
termination_by st.measure
decreasing_by exact AState.measure_step st ‹¬ st.halted›

def AState.fuel (st : AState) : ℕ :=
  if st.halted then 1 else 1 + AState.fuel (AState.next st)
termination_by st.measure
decreasing_by exact AState.measure_step st ‹¬ st.halted›

theorem AState.fuel_le (st : AState) :
    st.fuel ≤ 2 * (st.x.length + st.y.length + st.z.length) + st.cval + 1 := by
  induction st using AState.fuel.induct with
  | case1 st h =>
    rw [AState.fuel.eq_def, if_pos h]
    omega
  | case2 st h ih =>
    rw [AState.fuel.eq_def, if_neg h]
    have hdec := AState.measure_step st h
    show 1 + (AState.next st).fuel ≤
      2 * (st.x.length + st.y.length + st.z.length) + st.cval + 1
    unfold AState.measure at hdec
    omega

def AState.emit (st : AState) : Bits :=
  if st.halted then [] else st.outBit :: AState.emit (AState.next st)
termination_by st.measure
decreasing_by exact AState.measure_step st ‹¬ st.halted›

theorem AState.value_step (st : AState) (hc : st.cval ≤ 2) :
    st.value = st.bit + 2 * (AState.next st).value := by
  have hcv : (AState.next st).cval = st.total / 2 := by
    rw [AState.cval_next]
    have h := AState.total_le st
    have h2 : st.total / 2 ≤ 2 := by omega
    exact Nat.min_eq_left h2
  have hx := TrialAdd.binaryValue_head_tail st.x
  have hy := TrialAdd.binaryValue_head_tail st.y
  have hz := TrialAdd.binaryValue_head_tail st.z
  have hmod := Nat.mod_add_div st.total 2
  have hnext : (AState.next st).value =
      binaryValue st.x.tail + (if !st.w then binaryValue st.y.tail else 0) +
        (if !st.w then binaryValue st.z.tail else 0) + st.total / 2 := by
    simp only [AState.value]
    rw [hcv]
    rfl
  have hval : st.value = st.total + 2 * (binaryValue st.x.tail +
      (if !st.w then binaryValue st.y.tail else 0) +
      (if !st.w then binaryValue st.z.tail else 0)) := by
    unfold AState.value AState.total
    rw [hx, hy, hz]
    by_cases hw : st.w
    · simp [hw]
      ring
    · have hwf : st.w = false := TrialCompare.bool_eq_false hw
      simp [hwf]
      ring
  rw [hval, hnext]
  have hbit : st.bit = st.total % 2 := rfl
  rw [hbit]
  ring_nf
  omega

theorem AState.run_spec (st : AState) (hc : st.cval ≤ 2) :
    (AState.run st).halted ∧ (AState.run st).value = 0 := by
  induction st using AState.run.induct with
  | case1 st h =>
    rw [AState.run.eq_def, if_pos h]
    refine ⟨h, ?_⟩
    obtain ⟨hx, hy, hz, hc0, hc1⟩ := h
    simp [AState.value, AState.cval, hx, hy, hz, hc0, hc1, TrialCompare.carryOf]
  | case2 st h ih =>
    rw [AState.run.eq_def, if_neg h]
    exact ih (AState.cval_next_le_two st)

theorem AState.run_w (st : AState) : (AState.run st).w = st.w := by
  induction st using AState.run.induct with
  | case1 st h =>
    rw [AState.run.eq_def, if_pos h]
  | case2 st h ih =>
    rw [AState.run.eq_def, if_neg h, ih]
    rfl

theorem AState.emit_value (st : AState) (hc : st.cval ≤ 2) :
    binaryValue st.emit = st.value := by
  induction st using AState.emit.induct with
  | case1 st h =>
    rw [AState.emit.eq_def, if_pos h]
    obtain ⟨hx, hy, hz, hc0, hc1⟩ := h
    simp [AState.value, AState.cval, hx, hy, hz, hc0, hc1, TrialCompare.carryOf]
  | case2 st h ih =>
    rw [AState.emit.eq_def, if_neg h]
    have hstep := AState.value_step st hc
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.ParseFramed.binaryValue_cons,
      ih (AState.cval_next_le_two st), hstep]
    have hbit : (if st.outBit = true then 1 else 0) = st.bit := by
      unfold AState.bit
      have h2 : st.total % 2 = 0 ∨ st.total % 2 = 1 := Nat.mod_two_eq_zero_or_one st.total
      rcases h2 with hb | hb <;>
        simp [AState.outBit, hb]
    omega

theorem addLstep_step (st : AState) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (hz : st.z = [])
    (h0 : v.c0 = st.c0) (h1 : v.c1 = st.c1) (hw : v.w = st.w) (hvd : v.od = none)
    (a0 a1 a2 a3 a4 a5 a7 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .addLstep, v,
          TrialEmit.store a0 a1 a2 a3 a4 a5 st.y a7 st.x a9 a10 a11⟩ =
      some (if AState.halted st then
          ⟨some .cShiftL, ⟨none, none, none, v.orr, st.c0, st.c1, st.w⟩,
            TrialEmit.store a0 a1 a2 a3 a4 a5 [] a7 [] a9 a10 a11⟩
        else
          ⟨some .addLstep,
            ⟨none, none, none, v.orr, (AState.next st).c0, (AState.next st).c1,
              (AState.next st).w⟩,
            TrialEmit.store a0 a1 a2 a3 a4 a5 st.y.tail (st.outBit :: a7) st.x.tail
              a9 a10 a11⟩) := by
  obtain ⟨x, y, z, w, c0, c1⟩ := st
  (try dsimp only at hz h0 h1 hw hvd ⊢)
  simp only [hz, AState.halted, AState.total, AState.outBit, AState.next, AState.cval,
    TrialCompare.carryOf, TrialCompare.carryBit0, TrialCompare.carryBit1, TrialAdd.bitOf]
  cases x <;> cases y <;> cases c0 <;> cases c1 <;>
    simp [program, addLStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_eight,
      TrialEmit.store_update_six, TrialEmit.store_update_seven, cond, h0, h1, hw, hvd,
      sum3, sumBit, sumNext, TrialCompare.carryBit0, TrialCompare.carryBit1,
      TrialCompare.carryOf, TrialAdd.bitOf]

theorem addSstep_step (st : AState) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (h0 : v.c0 = st.c0) (h1 : v.c1 = st.c1) (hw : v.w = st.w)
    (a0 a1 a2 a3 a4 a6 a7 a8 a11 : Bits) :
    TM2.step program
        ⟨some .addSstep, v,
          TrialEmit.store a0 a1 a2 a3 a4 st.z a6 a7 a8 st.x st.y a11⟩ =
      some (if AState.halted st then
          ⟨some .cShiftS, ⟨none, none, none, v.orr, st.c0, st.c1, st.w⟩,
            TrialEmit.store a0 a1 a2 a3 a4 [] a6 a7 a8 [] [] a11⟩
        else
          ⟨some .addSstep,
            ⟨none, none, none, v.orr, (AState.next st).c0, (AState.next st).c1,
              (AState.next st).w⟩,
            TrialEmit.store a0 a1 a2 a3 a4 st.z.tail a6 a7 a8 st.x.tail st.y.tail
              (st.outBit :: a11)⟩) := by
  obtain ⟨x, y, z, w, c0, c1⟩ := st
  (try dsimp only at h0 h1 hw ⊢)
  simp only [AState.halted, AState.total, AState.outBit, AState.next, AState.cval,
    TrialCompare.carryOf, TrialCompare.carryBit0, TrialCompare.carryBit1, TrialAdd.bitOf]
  cases x <;> cases y <;> cases z <;> cases c0 <;> cases c1 <;>
    simp [program, addSStmt, TM2.step, TM2.stepAux, TrialEmit.store_update_nine,
      TrialEmit.store_update_ten, TrialEmit.store_update_five,
      TrialEmit.store_update_eleven, cond, h0, h1, hw,
      sum3, sumBit, sumNext, TrialCompare.carryBit0, TrialCompare.carryBit1,
      TrialCompare.carryOf, TrialAdd.bitOf]

theorem addLstep_run (st : AState) (hz : st.z = []) :
    ∀ (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a7 a9 a10 a11 : Bits),
      v.c0 = st.c0 → v.c1 = st.c1 → v.w = st.w → v.od = none →
      stackRun program (AState.fuel st)
          ⟨some .addLstep, v,
            TrialEmit.store a0 a1 a2 a3 a4 a5 st.y a7 st.x a9 a10 a11⟩ =
        some ⟨some .cShiftL,
          ⟨none, none, none, v.orr, (AState.run st).c0, (AState.run st).c1,
            (AState.run st).w⟩,
          TrialEmit.store a0 a1 a2 a3 a4 a5 [] ((AState.emit st).reverse ++ a7) []
            a9 a10 a11⟩ := by
  revert hz
  induction st using AState.fuel.induct with
  | case1 st hh =>
    intro hz v a0 a1 a2 a3 a4 a5 a7 a9 a10 a11 h0 h1 hw hvd
    rw [AState.fuel.eq_def, if_pos hh, AState.run.eq_def, if_pos hh,
      AState.emit.eq_def, if_pos hh]
    rw [show ((1 : ℕ)) = 0 + 1 from rfl, stackRun,
      addLstep_step st v hz h0 h1 hw hvd, if_pos hh, Option.bind_some]
    rfl
  | case2 st hh ih =>
    intro hz v a0 a1 a2 a3 a4 a5 a7 a9 a10 a11 h0 h1 hw hvd
    rw [AState.fuel.eq_def, if_neg hh, Nat.one_add, stackRun,
      addLstep_step st v hz h0 h1 hw hvd, if_neg hh, Option.bind_some]
    rw [show List.tail st.x = (AState.next st).x from rfl,
      show List.tail st.y = (AState.next st).y from rfl]
    rw [ih (by simp only [AState.next, hz, List.tail_nil])
      ⟨none, none, none, v.orr, (AState.next st).c0, (AState.next st).c1,
        (AState.next st).w⟩ a0 a1 a2 a3 a4 a5 (st.outBit :: a7) a9 a10 a11
      rfl rfl rfl rfl]
    have hrun : AState.run st = AState.run (AState.next st) := by
      rw [AState.run.eq_def, if_neg hh]
    have hemp : AState.emit st = st.outBit :: AState.emit (AState.next st) := by
      rw [AState.emit.eq_def, if_neg hh]
    rw [hrun, hemp]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem addSstep_run (st : AState) :
    ∀ (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a6 a7 a8 a11 : Bits),
      v.c0 = st.c0 → v.c1 = st.c1 → v.w = st.w →
      stackRun program (AState.fuel st)
          ⟨some .addSstep, v,
            TrialEmit.store a0 a1 a2 a3 a4 st.z a6 a7 a8 st.x st.y a11⟩ =
        some ⟨some .cShiftS,
          ⟨none, none, none, v.orr, (AState.run st).c0, (AState.run st).c1,
            (AState.run st).w⟩,
          TrialEmit.store a0 a1 a2 a3 a4 [] a6 a7 a8 [] []
            ((AState.emit st).reverse ++ a11)⟩ := by
  induction st using AState.fuel.induct with
  | case1 st hh =>
    intro v a0 a1 a2 a3 a4 a6 a7 a8 a11 h0 h1 hw
    rw [AState.fuel.eq_def, if_pos hh, AState.run.eq_def, if_pos hh,
      AState.emit.eq_def, if_pos hh]
    rw [show ((1 : ℕ)) = 0 + 1 from rfl, stackRun,
      addSstep_step st v h0 h1 hw, if_pos hh, Option.bind_some]
    rfl
  | case2 st hh ih =>
    intro v a0 a1 a2 a3 a4 a6 a7 a8 a11 h0 h1 hw
    rw [AState.fuel.eq_def, if_neg hh, Nat.one_add, stackRun,
      addSstep_step st v h0 h1 hw, if_neg hh, Option.bind_some]
    rw [show List.tail st.x = (AState.next st).x from rfl,
      show List.tail st.y = (AState.next st).y from rfl,
      show List.tail st.z = (AState.next st).z from rfl]
    rw [ih ⟨none, none, none, v.orr, (AState.next st).c0, (AState.next st).c1,
        (AState.next st).w⟩ a0 a1 a2 a3 a4 a6 a7 a8 (st.outBit :: a11) rfl rfl rfl]
    have hrun : AState.run st = AState.run (AState.next st) := by
      rw [AState.run.eq_def, if_neg hh]
    have hemp : AState.emit st = st.outBit :: AState.emit (AState.next st) := by
      rw [AState.emit.eq_def, if_neg hh]
    rw [hrun, hemp]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem addL_load (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .addL, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11⟩ =
      some ⟨some .addLstep,
        ⟨none, none, none, none, false, false, v.w⟩,
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11⟩ := by
  simp only [program, TM2.step, TM2.stepAux, clearBits]

theorem addS_load (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Bits) :
    TM2.step program
        ⟨some .addS, v, TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11⟩ =
      some ⟨some .addSstep,
        ⟨none, none, none, none, false, false, v.w⟩,
        TrialEmit.store a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11⟩ := by
  simp only [program, TM2.step, TM2.stepAux, clearBits]

theorem addL_run (st : AState) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local) (hz : st.z = [])
    (hc0 : st.c0 = false) (hc1 : st.c1 = false) (hw : v.w = st.w)
    (a0 a1 a2 a3 a4 a5 a7 a9 a10 a11 : Bits) :
    stackRun program (1 + AState.fuel st)
        ⟨some .addL, v,
          TrialEmit.store a0 a1 a2 a3 a4 a5 st.y a7 st.x a9 a10 a11⟩ =
      some ⟨some .cShiftL,
        ⟨none, none, none, none, (AState.run st).c0, (AState.run st).c1,
          (AState.run st).w⟩,
        TrialEmit.store a0 a1 a2 a3 a4 a5 [] ((AState.emit st).reverse ++ a7) []
          a9 a10 a11⟩ := by
  rw [Nat.one_add, stackRun, addL_load, Option.bind_some]
  rw [addLstep_run st hz ⟨none, none, none, none, false, false, v.w⟩
    a0 a1 a2 a3 a4 a5 a7 a9 a10 a11 hc0.symm hc1.symm hw rfl]

theorem addS_run (st : AState) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local)
    (hc0 : st.c0 = false) (hc1 : st.c1 = false) (hw : v.w = st.w)
    (a0 a1 a2 a3 a4 a6 a7 a8 a11 : Bits) :
    stackRun program (1 + AState.fuel st)
        ⟨some .addS, v,
          TrialEmit.store a0 a1 a2 a3 a4 st.z a6 a7 a8 st.x st.y a11⟩ =
      some ⟨some .cShiftS,
        ⟨none, none, none, none, (AState.run st).c0, (AState.run st).c1,
          (AState.run st).w⟩,
        TrialEmit.store a0 a1 a2 a3 a4 [] a6 a7 a8 [] [] ((AState.emit st).reverse ++ a11)⟩ := by
  rw [Nat.one_add, stackRun, addS_load, Option.bind_some]
  rw [addSstep_run st ⟨none, none, none, none, false, false, v.w⟩
    a0 a1 a2 a3 a4 a6 a7 a8 a11 hc0.symm hc1.symm hw]

abbrev outL (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).lA
abbrev outS (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).s
abbrev outB (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).lB
abbrev outQ2 (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).q2
abbrev outR4 (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).r4
abbrev outQA (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).qA
abbrev outQB (s4 l2 q r : Bits) : Bits := (runOut s4 l2 q r).qB

abbrev stL (s4 l2 q r : Bits) : AState :=
  ⟨(outL s4 l2 q r).reverse, (outQ2 s4 l2 q r).reverse, [],
    (runState s4 l2 q r).w, false, false⟩

abbrev stS (s4 l2 q r : Bits) : AState :=
  ⟨(outS s4 l2 q r).reverse, (outB s4 l2 q r).reverse,
    (outQB s4 l2 q r).reverse, (runState s4 l2 q r).w, false, false⟩

abbrev roundCfg (s4 l2 q r aa : Bits) :
    TM2.Cfg (fun _ : Fin 12 => Bool) Label Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialCompare.Local :=
  ⟨none,
    ⟨none, none, none, none, (AState.run (stS s4 l2 q r)).c0,
      (AState.run (stS s4 l2 q r)).c1, (AState.run (stS s4 l2 q r)).w⟩,
    TrialEmit.store
      (false :: false :: AState.emit (stS s4 l2 q r))
      (false :: AState.emit (stL s4 l2 q r))
      (outQA s4 l2 q r).reverse (outR4 s4 l2 q r).reverse
      ((!(runState s4 l2 q r).w) :: aa)
      [] [] [] [] [] [] []⟩

def roundFuel (s4 l2 q r : Bits) : ℕ :=
  1 + (TrialCompare.fuel (st0 s4 l2 q r) + 1) +
    ((outR4 s4 l2 q r).length + 1 +
      ((outQA s4 l2 q r).length + 1 +
        ((outS s4 l2 q r).length + 1 +
          ((outQ2 s4 l2 q r).length + 1 +
            ((outL s4 l2 q r).length + 1 +
              ((outB s4 l2 q r).length + 1 +
                ((outQB s4 l2 q r).length + 1 +
                  ((1 + AState.fuel (stL s4 l2 q r)) +
                    ((AState.emit (stL s4 l2 q r)).reverse.length + 1 +
                      ((1 + AState.fuel (stS s4 l2 q r)) +
                        ((AState.emit (stS s4 l2 q r)).reverse.length + 1)))))))))))

theorem round_run (s4 l2 q r aa : Bits) :
    stackRun program (roundFuel s4 l2 q r) (startCfg s4 l2 q r aa) =
      some (roundCfg s4 l2 q r aa) := by
  unfold roundFuel
  rw [run_add, emit_run s4 l2 q r aa, Option.bind_some]
  rw [run_add, c4r_run, Option.bind_some]
  (try dsimp only)
  rw [run_add, cQ_run, Option.bind_some]
  (try dsimp only)
  rw [run_add, cS4_run, Option.bind_some]
  (try dsimp only)
  rw [run_add, c2Q_run, Option.bind_some]
  (try dsimp only)
  rw [run_add, cL1_run, Option.bind_some]
  (try dsimp only)
  rw [run_add, cL2_run, Option.bind_some]
  (try dsimp only)
  rw [run_add, cQlow_run, Option.bind_some]
  (try dsimp only)
  simp only [List.append_nil]
  rw [run_add,
    addL_run (stL s4 l2 q r)
      ⟨none, none, none, none, (runState s4 l2 q r).c0,
        (runState s4 l2 q r).c1, (runState s4 l2 q r).w⟩
      rfl rfl rfl rfl
      [] [] (outQA s4 l2 q r).reverse (outR4 s4 l2 q r).reverse
      ((!(runState s4 l2 q r).w) :: aa) (outQB s4 l2 q r).reverse []
      (outS s4 l2 q r).reverse (outB s4 l2 q r).reverse []
    , Option.bind_some]
  simp only [List.append_nil]
  rw [run_add, cShiftL_run, Option.bind_some]
  (try dsimp only)
  simp only [List.reverse_reverse, List.append_nil]
  rw [run_add,
    addS_run (stS s4 l2 q r)
      ⟨none, none, none, none, (AState.run (stL s4 l2 q r)).c0,
        (AState.run (stL s4 l2 q r)).c1, (AState.run (stL s4 l2 q r)).w⟩
      rfl rfl (AState.run_w (stL s4 l2 q r))
      [] (false :: AState.emit (stL s4 l2 q r)) (outQA s4 l2 q r).reverse
      (outR4 s4 l2 q r).reverse ((!(runState s4 l2 q r).w) :: aa) [] [] [] []
    , Option.bind_some]
  simp only [List.append_nil]
  rw [cShiftS_run]
  (try dsimp only)
  simp only [List.reverse_reverse, List.append_nil]

theorem outS_reverse (s4 l2 q r : Bits) :
    (outS s4 l2 q r).reverse = TrialEmit.emitS (st0 s4 l2 q r) := by
  simp [outS, runOut, apply, o0]

theorem outL_reverse (s4 l2 q r : Bits) :
    (outL s4 l2 q r).reverse = TrialEmit.emitL (st0 s4 l2 q r) := by
  simp [outL, runOut, apply, o0]

theorem outB_reverse (s4 l2 q r : Bits) :
    (outB s4 l2 q r).reverse = TrialEmit.emitL (st0 s4 l2 q r) := by
  simp [outB, runOut, apply, o0]

theorem outQ2_reverse (s4 l2 q r : Bits) :
    (outQ2 s4 l2 q r).reverse = TrialEmit.emitQ2 (st0 s4 l2 q r) := by
  simp [outQ2, runOut, apply, o0, TrialEmit.emitQ2]

theorem outR4_reverse (s4 l2 q r : Bits) :
    (outR4 s4 l2 q r).reverse = TrialEmit.emitR4 (st0 s4 l2 q r) := by
  simp [outR4, runOut, apply, o0, TrialEmit.emitR4]

theorem outQA_reverse (s4 l2 q r : Bits) :
    (outQA s4 l2 q r).reverse = TrialEmit.emitQ (st0 s4 l2 q r) := by
  simp [outQA, runOut, apply, o0]

theorem outQB_reverse (s4 l2 q r : Bits) :
    (outQB s4 l2 q r).reverse = TrialEmit.emitQ (st0 s4 l2 q r) := by
  simp [outQB, runOut, apply, o0]

theorem stS_value (s4 l2 q r : Bits) :
    (stS s4 l2 q r).value =
      binaryValue s4 + (if !(runState s4 l2 q r).w then
        binaryValue l2 + binaryValue q else 0) := by
  unfold stS AState.value AState.cval
  show binaryValue (outS s4 l2 q r).reverse +
      (if !(runState s4 l2 q r).w then binaryValue (outB s4 l2 q r).reverse else 0) +
      (if !(runState s4 l2 q r).w then binaryValue (outQB s4 l2 q r).reverse else 0) +
      TrialCompare.carryOf false false = _
  rw [outS_reverse, outB_reverse, outQB_reverse, TrialEmit.emitS_value,
    TrialEmit.emitL_value, TrialEmit.emitQ_value]
  simp only [st0, TrialCompare.carryOf, Bool.false_eq_true, if_false, Nat.zero_add]
  by_cases hw : (runState s4 l2 q r).w
  · simp [hw]
  · have hwf : (runState s4 l2 q r).w = false := TrialCompare.bool_eq_false hw
    simp [hwf]
    ring

theorem stL_value (s4 l2 q r : Bits) :
    (stL s4 l2 q r).value =
      binaryValue l2 + (if !(runState s4 l2 q r).w then
        2 * binaryValue q else 0) := by
  unfold stL AState.value AState.cval
  show binaryValue (outL s4 l2 q r).reverse +
      (if !(runState s4 l2 q r).w then binaryValue (outQ2 s4 l2 q r).reverse else 0) +
      (if !(runState s4 l2 q r).w then binaryValue [] else 0) +
      TrialCompare.carryOf false false = _
  rw [outL_reverse, outQ2_reverse, TrialEmit.emitL_value]
  unfold TrialEmit.emitQ2
  rw [TrialEmit.shift_one_value, TrialEmit.emitQ_value]
  simp only [st0, TrialCompare.carryOf, Bool.false_eq_true, if_false, Nat.zero_add,
    binaryValue_nil]
  by_cases hw : (runState s4 l2 q r).w <;> simp [hw]

theorem round_value (s4 l2 q r aa : Bits) :
    binaryValue ((roundCfg s4 l2 q r aa).stk 0) =
      4 * (binaryValue s4 +
        (if !(runState s4 l2 q r).w then binaryValue l2 + binaryValue q else 0)) ∧
    binaryValue ((roundCfg s4 l2 q r aa).stk 1) =
      2 * (binaryValue l2 +
        (if !(runState s4 l2 q r).w then 2 * binaryValue q else 0)) ∧
    binaryValue ((roundCfg s4 l2 q r aa).stk 2) = binaryValue q ∧
    binaryValue ((roundCfg s4 l2 q r aa).stk 3) = 4 * binaryValue r ∧
    binaryValue ((roundCfg s4 l2 q r aa).stk 4) =
      2 * binaryValue aa + (if !(runState s4 l2 q r).w then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show binaryValue (false :: false :: AState.emit (stS s4 l2 q r)) = _
    rw [TrialAdd.shift_value,
      AState.emit_value (stS s4 l2 q r) (by simp [AState.cval, TrialCompare.carryOf]),
      stS_value]
  · show binaryValue (false :: AState.emit (stL s4 l2 q r)) = _
    rw [TrialEmit.shift_one_value,
      AState.emit_value (stL s4 l2 q r) (by simp [AState.cval, TrialCompare.carryOf]),
      stL_value]
  · show binaryValue (outQA s4 l2 q r).reverse = binaryValue q
    rw [outQA_reverse, TrialEmit.emitQ_value]
    rfl
  · show binaryValue (outR4 s4 l2 q r).reverse = 4 * binaryValue r
    rw [outR4_reverse]
    unfold TrialEmit.emitR4
    rw [TrialAdd.shift_value, TrialEmit.emitR_value]
    rfl
  · show binaryValue ((!(runState s4 l2 q r).w) :: aa) = _
    rw [binaryValue_cons']
    by_cases hw : (runState s4 l2 q r).w <;> simp [hw, bitNat]

theorem round_bit (s4 l2 q r : Bits) :
    (!((runState s4 l2 q r).w)) =
      decide (binaryValue s4 + binaryValue l2 + binaryValue q ≤ binaryValue r) := by
  have hspec := CState.run_spec (st0 s4 l2 q r)
    (by simp [st0, CState.cval, TrialCompare.carryOf])
  have hval : CState.value (st0 s4 l2 q r) =
      binaryValue s4 + binaryValue l2 + binaryValue q := by
    simp [CState.value, st0, CState.cval, TrialCompare.carryOf]
  have hw0 : CState.wval (st0 s4 l2 q r) = 0 := rfl
  by_cases h : binaryValue s4 + binaryValue l2 + binaryValue q ≤ binaryValue r
  · have hw : (runState s4 l2 q r).w = false :=
      hspec.2.mpr (by rw [hval, hw0, Nat.add_zero]; exact h)
    simp [hw, h]
  · have hw : (runState s4 l2 q r).w = true := by
      by_contra hh
      have hf : (runState s4 l2 q r).w = false := TrialCompare.bool_eq_false hh
      exact h (by have hle := hspec.2.mp hf; rwa [hval, hw0, Nat.add_zero] at hle)
    simp [hw, h]

theorem machine_mRound (Q : ℕ) (s : TrialEmit.MState) :
    (!((runState (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
        (Nat.bits s.rhs)).w)) = decide (TrialEmit.mBit Q s = 1) ∧
    binaryValue ((roundCfg (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
        (Nat.bits s.rhs) (Nat.bits s.a)).stk 0) = 4 * (TrialEmit.mStep Q s).sq ∧
    binaryValue ((roundCfg (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
        (Nat.bits s.rhs) (Nat.bits s.a)).stk 1) = 2 * (TrialEmit.mStep Q s).lin2 ∧
    binaryValue ((roundCfg (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
        (Nat.bits s.rhs) (Nat.bits s.a)).stk 2) = Q ∧
    binaryValue ((roundCfg (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
        (Nat.bits s.rhs) (Nat.bits s.a)).stk 3) = (TrialEmit.mStep Q s).rhs ∧
    binaryValue ((roundCfg (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
        (Nat.bits s.rhs) (Nat.bits s.a)).stk 4) = (TrialEmit.mStep Q s).a := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := round_value (Nat.bits (4 * s.sq))
    (Nat.bits (2 * s.lin2)) (Nat.bits Q) (Nat.bits s.rhs) (Nat.bits s.a)
  have hbit : (!((runState (Nat.bits (4 * s.sq)) (Nat.bits (2 * s.lin2)) (Nat.bits Q)
      (Nat.bits s.rhs)).w)) = decide (TrialEmit.mBit Q s = 1) := by
    rw [round_bit]
    have hval : binaryValue (Nat.bits (4 * s.sq)) +
        binaryValue (Nat.bits (2 * s.lin2)) + binaryValue (Nat.bits Q) =
          TrialEmit.mTrial Q s := by
      rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
      unfold TrialEmit.mTrial
      ring
    rw [hval, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    by_cases h : TrialEmit.mBit Q s = 1
    · have hle : TrialEmit.mTrial Q s ≤ s.rhs := (TrialEmit.mBit_eq_one_iff Q s).mp h
      simp [h, hle]
    · have hle : ¬ TrialEmit.mTrial Q s ≤ s.rhs := (TrialEmit.mBit_ne_one_iff Q s).mp h
      simp [h, hle]
  refine ⟨hbit, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, hbit, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits, TrialEmit.mStep_sq]
    by_cases h : TrialEmit.mBit Q s = 1
    · simp [h, TrialEmit.mTrial]
      ring
    · simp [h]
  · rw [h1, hbit, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits, TrialEmit.mStep_lin2]
    by_cases h : TrialEmit.mBit Q s = 1 <;> simp [h]
  · rw [h2, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  · rw [h3, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
      TrialEmit.mStep_rhs_field]
  · rw [h4, hbit, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits, TrialEmit.mStep_a_field]
    by_cases h : TrialEmit.mBit Q s = 1 <;> simp [h]

end TrialRound

end output2

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain
