/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.AlgebraicRecoveryDefs
import Qatlib.Concepts.WalkFind.QRAMModel.QRAMImplementation
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.DlogCandidateRecovery
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodSamplingBudgetShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.DlogTwoDimSamplingLaw
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessingShor
import Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCandidateRecoveryStat
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodSamplingBudgetStat
import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogTwoDimSamplingLawStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessingStat

/-!
# Algebraic recovery constructions and encoding obstructions

Constructs integer encodings, decoders satisfying the stated recovery predicates, reversible
arithmetic circuits, and resource identities used in the factoring and discrete-logarithm
framework of [Shor1997]. `clause17` assembles the corresponding recovery, sampling, and
arithmetic results.

The module also analyzes integer matrix blocks and canonical presentation encodings. A collision
between presentation tapes in different dimensions proves `not_uniformCanonicalBasisMachine` for
the specified input encoding.

## Main statements

* `clause17`: Assembles the recovery contracts and arithmetic resource statements.
* `diagMergeAt`: Produces positive diagonal replacements through invertible integer
  transformations.
* `not_uniformCanonicalBasisMachine`: Refutes the uniform machine predicate using a
  presentation-tape collision.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
open Qatlib.Concepts.PeriodSampling.DlogGoodProb
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open scoped Classical

/-- Encodes an integer as twice its absolute value for a nonnegative input, and as twice its
absolute value minus one for a negative input. -/
def intEnc (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.natAbs else 2 * z.natAbs - 1

/-- Decodes an even natural number as its half and an odd natural number as the negative of half
its successor. -/
def intDec (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n + 1) / 2 : ℕ) : ℤ)

/-- Decoding the natural-number encoding of an integer returns that integer. -/
theorem intDec_intEnc (z : ℤ) : intDec (intEnc z) = z := by
  unfold intEnc intDec
  by_cases h : 0 ≤ z
  · have hz : (z.natAbs : ℤ) = z := Int.ofNat_natAbs_of_nonneg h
    have hpar : 2 * z.natAbs % 2 = 0 := by omega
    have h2 : 2 * z.natAbs / 2 = z.natAbs := by omega
    rw [if_pos h, if_pos hpar, h2]
    exact hz
  · have hz : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos (by omega)
    have hpos : 0 < z.natAbs := by omega
    have hpar : (2 * z.natAbs - 1) % 2 = 1 := by omega
    have h2 : (2 * z.natAbs - 1 + 1) / 2 = z.natAbs := by omega
    rw [if_neg h, if_neg (show ¬ (2 * z.natAbs - 1) % 2 = 0 from by omega), h2]
    rw [hz]
    ring

/-- Encoding the integer decoding of a natural number returns that natural number. -/
theorem intEnc_intDec (n : ℕ) : intEnc (intDec n) = n := by
  unfold intEnc intDec
  by_cases he : n % 2 = 0
  · have hz : (0 : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
    have habs : (((n / 2 : ℕ) : ℤ)).natAbs = n / 2 := rfl
    rw [if_pos he, if_pos hz, habs]
    omega
  · have h1 : 0 < (n + 1) / 2 := by omega
    have hz : ¬ (0 : ℤ) ≤ -(((n + 1) / 2 : ℕ) : ℤ) := by
      have hpos : (0 : ℤ) < (((n + 1) / 2 : ℕ) : ℤ) := by exact_mod_cast h1
      omega
    have habs : (-(((n + 1) / 2 : ℕ) : ℤ)).natAbs = (n + 1) / 2 := by
      have hneg : (-(((n + 1) / 2 : ℕ) : ℤ)) = Int.negOfNat ((n + 1) / 2) := rfl
      rw [hneg]
      exact Int.natAbs_negOfNat _
    rw [if_neg he, if_neg hz, habs]
    omega

/-- The integer-to-natural encoding `intEnc` is injective. -/
theorem intEnc_injective : Function.Injective intEnc := by
  intro a b h
  have h1 := congrArg intDec h
  rwa [intDec_intEnc, intDec_intEnc] at h1

/-- The sequence placing the absolute determinant at index zero and one at every other index. -/
def trivialChain {k : ℕ} (A : IMat k) : Fin k → ℕ :=
  fun i => if i.val = 0 then A.det.natAbs else 1

/-- The determinant-first sequence `trivialChain A` satisfies the descending divisibility
condition `IsFactorChain`. -/
theorem trivialChain_factorChain {k : ℕ} (A : IMat k) : IsFactorChain (trivialChain A) := by
  intro i j hj
  have hj0 : j.val ≠ 0 := by omega
  show trivialChain A j ∣ trivialChain A i
  rw [trivialChain, if_neg hj0]
  exact one_dvd _

/-- The product of `trivialChain A` is the absolute determinant of `A`. -/
theorem trivialChain_prod {k : ℕ} (A : IMat k) :
    (List.ofFn (trivialChain A)).prod = A.det.natAbs := by
  rw [List.prod_ofFn]
  rcases k with - | k
  · have hA : A.det = 1 := Matrix.det_fin_zero
    simp [trivialChain, hA]
  · rw [Fintype.prod_eq_single (0 : Fin (k + 1))]
    · simp [trivialChain]
    · intro x hx
      have hx0 : x.val ≠ 0 := by
        rintro (h : x.val = 0)
        apply hx
        exact Fin.val_injective (show x.val = (0 : Fin (k + 1)).val from h)
      simp [trivialChain, hx0]

/-- A decoder returning the determinant-first chain and using componentwise integer encodings
for coordinates, with both assigned resource values zero. -/
def trivialDecoder (k : ℕ) : CompactAbelianDecoder k where
  decompose := fun A => some (trivialChain A)
  toCoords := fun _ x => some (fun i => intEnc (x i))
  fromCoords := fun _ cs => some (fun i => intDec (cs i))
  bitCost := fun _ => 0
  bitSpace := fun _ => 0

/-- The explicit decoder `trivialDecoder k` satisfies `CompactAbelianDecoder.Correct`. -/
theorem trivialDecoder_correct (k : ℕ) : (trivialDecoder k).Correct := by
  intro A hA
  refine ⟨trivialChain A, rfl, trivialChain_factorChain A, trivialChain_prod A, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x y cs hx hy
    have hx' : (fun i => intEnc (x i)) = cs := Option.some.inj hx
    have hy' : (fun i => intEnc (y i)) = cs := Option.some.inj hy
    have hxy : x = y := by
      funext i
      apply intEnc_injective
      exact congrFun (hx'.trans hy'.symm) i
    rw [hxy, sub_self]
    exact Submodule.zero_mem _
  · intro x cs hx
    refine ⟨fun i => intDec (cs i), rfl, ?_⟩
    have hx' : (fun i => intEnc (x i)) = cs := Option.some.inj hx
    have hy : (fun i => intDec (cs i)) = x := by
      funext i
      rw [← hx']
      exact intDec_intEnc (x i)
    rw [hy, sub_self]
    exact Submodule.zero_mem _
  · intro cs y hy
    have hy' : (fun i => intDec (cs i)) = y := Option.some.inj hy
    show (trivialDecoder k).toCoords A y = some cs
    show some (fun i => intEnc (y i)) = some cs
    congr 1
    funext i
    rw [← hy']
    exact intEnc_intDec (cs i)

/-- A bounded discrete-logarithm search that checks exponents in decreasing order below the
supplied fuel. -/
def dlogScan {p : ℕ} (g x : ZMod p) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if g ^ n = x then some n else dlogScan g x n

/-- A discrete-logarithm search with zero fuel returns `none`. -/
theorem dlogScan_zero {p : ℕ} (g x : ZMod p) : dlogScan g x 0 = none := rfl

/-- A search with fuel `n + 1` first tests exponent `n`, then continues with fuel `n` if the
test fails. -/
theorem dlogScan_succ {p : ℕ} (g x : ZMod p) (n : ℕ) :
    dlogScan g x (n + 1) = if g ^ n = x then some n else dlogScan g x n := rfl

/-- A successful bounded discrete-logarithm search returns an exponent below its fuel whose
power equals the target. -/
theorem dlogScan_sound {p : ℕ} (g x : ZMod p) :
    ∀ (fuel r' : ℕ), dlogScan g x fuel = some r' → r' < fuel ∧ g ^ r' = x := by
  intro fuel
  induction fuel with
  | zero =>
    intro r' h
    rw [dlogScan_zero] at h
    simp at h
  | succ fuel ih =>
    intro r' h
    rw [dlogScan_succ] at h
    by_cases hg : g ^ fuel = x
    · rw [if_pos hg] at h
      injection h with hr
      subst hr
      exact ⟨Nat.lt_succ_self fuel, hg⟩
    · rw [if_neg hg] at h
      obtain ⟨hlt, heq⟩ := ih r' h
      exact ⟨by omega, heq⟩

/-- For a generator of order `p - 1` over a prime modulus `p ≥ 3`, equal powers with exponents
below `p - 1` have equal exponents. -/
theorem dlogScan_unique {p : ℕ} (g x : ZMod p) (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hord : orderOf g = p - 1) :
    ∀ a b : ℕ, a < p - 1 → b < p - 1 → g ^ a = g ^ b → a = b := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hg1 : g ^ (p - 1) = (1 : ZMod p) := by
    rw [← hord]
    exact pow_orderOf_eq_one g
  have hg0 : g ≠ (0 : ZMod p) := by
    rintro rfl
    have hz : (0 : ZMod p) ^ (p - 1) = 1 := hg1
    rw [zero_pow (by omega)] at hz
    exact absurd hz (by norm_num)
  intro a b ha hb h
  rcases le_total a b with hab | hab
  · have he : g ^ a * g ^ (b - a) = g ^ b := by
      rw [← pow_add]
      congr 1
      omega
    have hc : g ^ a = g ^ a * g ^ (b - a) := h.trans he.symm
    have hc1 : (g ^ a : ZMod p) * 1 = g ^ a * g ^ (b - a) := by
      rw [mul_one]
      exact hc
    have hcancel : (1 : ZMod p) = g ^ (b - a) := mul_left_cancel₀ (pow_ne_zero a hg0) hc1
    have hdvd : orderOf g ∣ b - a := orderOf_dvd_of_pow_eq_one hcancel.symm
    rw [hord] at hdvd
    have hz : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have he : g ^ b * g ^ (a - b) = g ^ a := by
      rw [← pow_add]
      congr 1
      omega
    have hc : g ^ b = g ^ b * g ^ (a - b) := h.symm.trans he.symm
    have hc1 : (g ^ b : ZMod p) * 1 = g ^ b * g ^ (a - b) := by
      rw [mul_one]
      exact hc
    have hcancel : (1 : ZMod p) = g ^ (a - b) := mul_left_cancel₀ (pow_ne_zero b hg0) hc1
    have hdvd : orderOf g ∣ a - b := orderOf_dvd_of_pow_eq_one hcancel.symm
    rw [hord] at hdvd
    have hz : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

/-- Given uniqueness of exponents below `p - 1`, a bounded search returns any matching exponent
below its fuel when the fuel is at most `p - 1`. -/
theorem dlogScan_complete {p : ℕ} (g x : ZMod p)
    (huniq : ∀ a b : ℕ, a < p - 1 → b < p - 1 → g ^ a = g ^ b → a = b) :
    ∀ (fuel r : ℕ), fuel ≤ p - 1 → r < fuel → g ^ r = x → dlogScan g x fuel = some r := by
  intro fuel
  induction fuel with
  | zero =>
    intro r hfuel hr _
    omega
  | succ fuel ih =>
    intro r hfuel hr hx
    rw [dlogScan_succ]
    by_cases hg : g ^ fuel = x
    · have hr2 : fuel = r := huniq fuel r (by omega) (by omega) (hg.trans hx.symm)
      rw [if_pos hg, hr2]
    · have hne : r ≠ fuel := fun he => hg (by rw [← he]; exact hx)
      rw [if_neg hg]
      exact ih r (by omega) (by omega) hx

/-- A two-dimensional discrete-logarithm decoder that searches all exponents below `p - 1`,
independently of the supplied sample pairs. -/
def bruteDlog : TwoDimDlogDecoder where
  decode := fun p q m g x _ => dlogScan g x (p - 1)

/-- The exhaustive decoder `bruteDlog` satisfies the stated two-dimensional discrete-logarithm
correctness predicate. -/
theorem bruteDlog_correct : bruteDlog.Correct := by
  intro p q m _ g x hp hp3 hpq hord
  refine ⟨?_, ?_⟩
  · intro ω r' h
    exact dlogScan_sound g x (p - 1) r' h
  · intro r ω hr hx _
    exact dlogScan_complete g x (dlogScan_unique g x hp hp3 hord) (p - 1) r
      (by omega) hr hx.symm

/-- The natural-number value of a `b`-bit register, with bit `i` weighted by `2 ^ i`. -/
def bitVal (b : ℕ) (u : Reg b) : ℕ := ∑ i : Fin b, if u i then 2 ^ (i : ℕ) else 0

/-- The value of the `b`-bit encoding of `n` is `n % 2 ^ b`. -/
theorem bitVal_encodeBits (b n : ℕ) : bitVal b (encodeBits b n) = n % 2 ^ b := by
  have hrow : ∀ i : Fin b,
      (if (encodeBits b n) i then 2 ^ (i : ℕ) else 0)
        = if Qatlib.Concepts.WalkFind.SearchAlgorithm.naturalBit n i.1
          then 2 ^ (i : ℕ) else 0 := by
    intro i
    show (if n.testBit i.1 then 2 ^ (i : ℕ) else 0) = _
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rfl
  show (∑ i : Fin b, if (encodeBits b n) i then 2 ^ (i : ℕ) else 0) = _
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  have hconv : (∑ i : Fin b,
        if Qatlib.Concepts.WalkFind.SearchAlgorithm.naturalBit n i.1
        then 2 ^ (i : ℕ) else 0)
      = ∑ i ∈ Finset.range b,
        if Qatlib.Concepts.WalkFind.SearchAlgorithm.naturalBit n i
        then 2 ^ i else 0 :=
    (Finset.sum_range (fun j =>
      if Qatlib.Concepts.WalkFind.SearchAlgorithm.naturalBit n j
      then 2 ^ j else 0)).symm
  rw [hconv]
  exact Qatlib.Concepts.WalkFind.QRAMModel.naturalBit_sum n b

/-- The `b`-bit encoding of zero is the all-zero register. -/
theorem encodeBits_zero (b : ℕ) : encodeBits b 0 = ZeroStr b := by
  funext i
  simp [encodeBits, ZeroStr]

/-- Splits a register of length `3 * b` into its three consecutive registers of length `b`. -/
def tripleOf (b : ℕ) (z : Reg (3 * b)) : Reg b × Reg b × Reg b :=
  (fun i => z ⟨i.1, by omega⟩,
    fun i => z ⟨b + i.1, by omega⟩,
    fun i => z ⟨2 * b + i.1, by omega⟩)

/-- Concatenates three registers of length `b` into one register of length `3 * b`. -/
def regOfTriple (b : ℕ) (u v w : Reg b) : Reg (3 * b) := fun i =>
  if h : i.1 < b then u ⟨i.1, h⟩
  else if h2 : i.1 < 2 * b then v ⟨i.1 - b, by omega⟩
  else w ⟨i.1 - 2 * b, by omega⟩

/-- Concatenating the three blocks extracted by `tripleOf` reconstructs the original register. -/
theorem regOfTriple_tripleOf (b : ℕ) (z : Reg (3 * b)) :
    regOfTriple b (tripleOf b z).1 (tripleOf b z).2.1 (tripleOf b z).2.2 = z := by
  funext i
  simp only [regOfTriple, tripleOf]
  by_cases h1 : i.1 < b
  · simp [h1]
  · by_cases h2 : i.1 < 2 * b
    · simp [h1, h2]
      exact congrArg z (Fin.val_injective (show b + (i.1 - b) = i.1 from by omega))
    · simp [h1, h2]
      exact congrArg z (Fin.val_injective (show 2 * b + (i.1 - 2 * b) = i.1 from by omega))

/-- Splitting a concatenation of three registers returns those three registers. -/
theorem tripleOf_regOfTriple (b : ℕ) (u v w : Reg b) :
    tripleOf b (regOfTriple b u v w) = (u, v, w) := by
  apply Prod.ext
  · funext i
    show regOfTriple b u v w ⟨i.1, _⟩ = u i
    simp only [regOfTriple]
    rw [dif_pos i.isLt]
  · apply Prod.ext
    · funext i
      show regOfTriple b u v w ⟨b + i.1, _⟩ = v i
      simp only [regOfTriple]
      rw [dif_neg (by omega : ¬ b + i.1 < b), dif_pos (by omega : b + i.1 < 2 * b)]
      exact congrArg v (Fin.val_injective (show b + i.1 - b = i.1 from by omega))
    · funext i
      show regOfTriple b u v w ⟨2 * b + i.1, _⟩ = w i
      simp only [regOfTriple]
      rw [dif_neg (by omega : ¬ 2 * b + i.1 < b), dif_neg (by omega : ¬ 2 * b + i.1 < 2 * b)]
      exact congrArg w (Fin.val_injective (show 2 * b + i.1 - 2 * b = i.1 from by omega))

/-- Splitting `encodeTriple b a c d` returns the three separate bit encodings. -/
theorem tripleOf_encodeTriple (b a c d : ℕ) :
    tripleOf b (encodeTriple b a c d) = (encodeBits b a, encodeBits b c, encodeBits b d) := by
  apply Prod.ext
  · funext i
    show encodeTriple b a c d ⟨i.1, _⟩ = encodeBits b a i
    simp only [encodeTriple, encodeBits]
    rw [if_pos i.isLt]
  · apply Prod.ext
    · funext i
      show encodeTriple b a c d ⟨b + i.1, _⟩ = encodeBits b c i
      simp only [encodeTriple, encodeBits]
      rw [if_neg (by omega : ¬ b + i.1 < b), if_pos (by omega : b + i.1 < 2 * b)]
      rw [show b + i.1 - b = i.1 from by omega]
    · funext i
      show encodeTriple b a c d ⟨2 * b + i.1, _⟩ = encodeBits b d i
      simp only [encodeTriple, encodeBits]
      rw [if_neg (by omega : ¬ 2 * b + i.1 < b), if_neg (by omega : ¬ 2 * b + i.1 < 2 * b)]
      rw [show 2 * b + i.1 - 2 * b = i.1 from by omega]

/-- Concatenating the bit encodings of `a`, `c`, and `d` gives `encodeTriple b a c d`. -/
theorem regOfTriple_encodeTriple (b a c d : ℕ) :
    regOfTriple b (encodeBits b a) (encodeBits b c) (encodeBits b d) = encodeTriple b a c d := by
  funext i
  simp only [regOfTriple, encodeTriple, encodeBits]
  by_cases h1 : i.1 < b
  · simp [h1]
  · by_cases h2 : (i : ℕ) < 2 * b
    · simp [h1, h2]
    · simp [h1, h2]

/-- The register map exchanging the all-zero register with `s` and fixing every other register. -/
def flipAt {b : ℕ} (s w : Reg b) : Reg b :=
  if w = ZeroStr b then s else if w = s then ZeroStr b else w

/-- The register exchange map `flipAt s` is an involution. -/
theorem flipAt_involutive {b : ℕ} (s : Reg b) : Function.Involutive (flipAt s) := by
  intro w
  by_cases h1 : w = ZeroStr b
  · by_cases h2 : s = ZeroStr b
    · simp [flipAt, h1, h2]
    · simp [flipAt, h1, h2]
  · by_cases h2 : w = s
    · simp [flipAt, h2]
    · simp [flipAt, h1, h2]

/-- A reversible register map preserving the first two blocks and exchanging zero with their
encoded sum modulo `2 ^ b` in the third block. -/
def addSigma (b : ℕ) : Reg (3 * b) → Reg (3 * b) := fun z =>
  let t := tripleOf b z
  regOfTriple b t.1 t.2.1
    (flipAt (encodeBits b ((bitVal b t.1 + bitVal b t.2.1) % 2 ^ b)) t.2.2)

/-- A reversible register map preserving the first two blocks and exchanging zero with their
encoded product modulo `2 ^ b` in the third block. -/
def mulSigma (b : ℕ) : Reg (3 * b) → Reg (3 * b) := fun z =>
  let t := tripleOf b z
  regOfTriple b t.1 t.2.1
    (flipAt (encodeBits b ((bitVal b t.1 * bitVal b t.2.1) % 2 ^ b)) t.2.2)

/-- Evaluates `addSigma` on three concatenated registers as the corresponding exchange in the
third register. -/
theorem addSigma_regOfTriple (b : ℕ) (u v w : Reg b) :
    addSigma b (regOfTriple b u v w)
      = regOfTriple b u v
          (flipAt (encodeBits b ((bitVal b u + bitVal b v) % 2 ^ b)) w) := by
  dsimp [addSigma]
  rw [tripleOf_regOfTriple]

/-- Evaluates `mulSigma` on three concatenated registers as the corresponding exchange in the
third register. -/
theorem mulSigma_regOfTriple (b : ℕ) (u v w : Reg b) :
    mulSigma b (regOfTriple b u v w)
      = regOfTriple b u v
          (flipAt (encodeBits b ((bitVal b u * bitVal b v) % 2 ^ b)) w) := by
  dsimp [mulSigma]
  rw [tripleOf_regOfTriple]

/-- The modular-addition register map `addSigma b` is an involution. -/
theorem addSigma_involutive (b : ℕ) : Function.Involutive (addSigma b) := by
  intro z
  obtain ⟨u, v, w, hz⟩ : ∃ (u v w : Reg b), z = regOfTriple b u v w :=
    ⟨(tripleOf b z).1, (tripleOf b z).2.1, (tripleOf b z).2.2,
      (regOfTriple_tripleOf b z).symm⟩
  subst hz
  rw [addSigma_regOfTriple, addSigma_regOfTriple, flipAt_involutive]

/-- The modular-multiplication register map `mulSigma b` is an involution. -/
theorem mulSigma_involutive (b : ℕ) : Function.Involutive (mulSigma b) := by
  intro z
  obtain ⟨u, v, w, hz⟩ : ∃ (u v w : Reg b), z = regOfTriple b u v w :=
    ⟨(tripleOf b z).1, (tripleOf b z).2.1, (tripleOf b z).2.2,
      (regOfTriple_tripleOf b z).symm⟩
  subst hz
  rw [mulSigma_regOfTriple, mulSigma_regOfTriple, flipAt_involutive]

/-- On bounded operands and a zero third register, `addSigma` writes the sum modulo `2 ^ b` into
the third register. -/
theorem addSigma_zero (b a c : ℕ) (ha : a < 2 ^ b) (hc : c < 2 ^ b) :
    addSigma b (encodeTriple b a c 0) = encodeTriple b a c ((a + c) % 2 ^ b) := by
  have htr : tripleOf b (encodeTriple b a c 0)
      = (encodeBits b a, encodeBits b c, ZeroStr b) := by
    rw [tripleOf_encodeTriple]
    simp [encodeBits_zero]
  dsimp [addSigma]
  rw [htr]
  have hva : bitVal b (encodeBits b a) = a := by
    rw [bitVal_encodeBits]
    exact Nat.mod_eq_of_lt ha
  have hvc : bitVal b (encodeBits b c) = c := by
    rw [bitVal_encodeBits]
    exact Nat.mod_eq_of_lt hc
  rw [hva, hvc]
  have hflip : flipAt (encodeBits b ((a + c) % 2 ^ b)) (ZeroStr b)
      = encodeBits b ((a + c) % 2 ^ b) := by
    unfold flipAt
    exact if_pos rfl
  rw [hflip]
  exact regOfTriple_encodeTriple b a c ((a + c) % 2 ^ b)

/-- On bounded operands and a zero third register, `mulSigma` writes the product modulo `2 ^ b`
into the third register. -/
theorem mulSigma_zero (b a c : ℕ) (ha : a < 2 ^ b) (hc : c < 2 ^ b) :
    mulSigma b (encodeTriple b a c 0) = encodeTriple b a c ((a * c) % 2 ^ b) := by
  have htr : tripleOf b (encodeTriple b a c 0)
      = (encodeBits b a, encodeBits b c, ZeroStr b) := by
    rw [tripleOf_encodeTriple]
    simp [encodeBits_zero]
  dsimp [mulSigma]
  rw [htr]
  have hva : bitVal b (encodeBits b a) = a := by
    rw [bitVal_encodeBits]
    exact Nat.mod_eq_of_lt ha
  have hvc : bitVal b (encodeBits b c) = c := by
    rw [bitVal_encodeBits]
    exact Nat.mod_eq_of_lt hc
  rw [hva, hvc]
  have hflip : flipAt (encodeBits b ((a * c) % 2 ^ b)) (ZeroStr b)
      = encodeBits b ((a * c) % 2 ^ b) := by
    unfold flipAt
    exact if_pos rfl
  rw [hflip]
  exact regOfTriple_encodeTriple b a c ((a * c) % 2 ^ b)

/-- Constructs reversible modular arithmetic from permutation gates for `addSigma` and
`mulSigma`, with assigned elementary-operation counts zero. -/
def arith : ReversibleArithmetic where
  add := fun b => [Step.gate (permMatrix (addSigma b))]
  mul := fun b => if b = 0 then [] else [Step.gate (permMatrix (mulSigma b))]
  addElem := fun _ => 0
  mulElem := fun _ => 0
  add_macros := fun b => by
    show GateCount [Step.gate (permMatrix (addSigma b))] ≤ 2 * b + 2
    simp [GateCount]
  mul_macros := fun b => by
    by_cases h : b = 0
    · subst h
      show GateCount [] ≤ schoolbookMulModBitCost 0
      simp [GateCount, schoolbookMulModBitCost]
    · have hb1 : 1 ≤ b := by omega
      rw [if_neg h]
      show GateCount [Step.gate (permMatrix (mulSigma b))] ≤ schoolbookMulModBitCost b
      simp only [GateCount, schoolbookMulModBitCost]
      nlinarith [sq_nonneg ((b : ℕ) - 1)]
  queries := fun b => by
    refine ⟨?_, ?_⟩
    · show QueryCount [Step.gate (permMatrix (addSigma b))] = 0
      simp [QueryCount]
    · by_cases h : b = 0
      · subst h
        show QueryCount [] = 0
        rfl
      · rw [if_neg h]
        show QueryCount [Step.gate (permMatrix (mulSigma b))] = 0
        simp [QueryCount]
  unitary := fun b => by
    refine ⟨?_, ?_⟩
    · show IsUnitaryCircuit [Step.gate (permMatrix (addSigma b))]
      simp [isUnitaryCircuit_gate, permMatrix_unitary (addSigma_involutive b)]
    · by_cases h : b = 0
      · subst h
        show IsUnitaryCircuit []
        exact isUnitaryCircuit_nil
      · rw [if_neg h]
        show IsUnitaryCircuit [Step.gate (permMatrix (mulSigma b))]
        simp [isUnitaryCircuit_gate, permMatrix_unitary (mulSigma_involutive b)]
  realizes := fun b => by
    refine ⟨?_, ?_⟩
    · intro a c ha hc
      show Run (1 : Matrix (Reg (3 * b)) (Reg (3 * b)) ℂ)
          [Step.gate (permMatrix (addSigma b))] (Qatlib.Foundations.PureStateMath.Ket (encodeTriple b a c 0)) = _
      simp only [Run]
      rw [applyGate_permMatrix_ket (addSigma_involutive b)]
      exact congrArg Qatlib.Foundations.PureStateMath.Ket (addSigma_zero b a c ha hc)
    · intro a c ha hc
      by_cases hb : b = 0
      · subst hb
        have ha0 : a = 0 := by omega
        have hc0 : c = 0 := by omega
        subst ha0
        subst hc0
        show Run (1 : Matrix (Reg 0) (Reg 0) ℂ) ([] : Circuit (Reg 0))
            (Qatlib.Foundations.PureStateMath.Ket (encodeTriple 0 0 0 0)) = _
        simp [Run]
      · rw [if_neg hb]
        show Run (1 : Matrix (Reg (3 * b)) (Reg (3 * b)) ℂ)
          [Step.gate (permMatrix (mulSigma b))] (Qatlib.Foundations.PureStateMath.Ket (encodeTriple b a c 0)) = _
        simp only [Run]
        rw [applyGate_permMatrix_ket (mulSigma_involutive b)]
        exact congrArg Qatlib.Foundations.PureStateMath.Ket (mulSigma_zero b a c ha hc)
  elem_poly := ⟨1, 1, fun b => by simp⟩

/-- The reversible arithmetic construction `arith` satisfies its polynomial resource-bound
predicate. -/
theorem arith_poly : arith.PolyBounded := by
  refine ⟨3, 2, ?_⟩
  intro b
  refine ⟨?_, ?_, ?_⟩
  · show schoolbookMulModBitCost b ≤ 3 * (b + 1) ^ 2
    unfold schoolbookMulModBitCost
    nlinarith [sq_nonneg ((b : ℕ) + 1), sq_nonneg ((b : ℕ) - 1)]
  · show 3 * b ≤ 3 * (b + 1) ^ 2
    nlinarith [sq_nonneg ((b : ℕ) + 1)]
  · show (arith.addElem b + arith.mulElem b : ℕ) ≤ 3 * (b + 1) ^ 2
    exact Nat.zero_le _

/-- The local Fourier circuit has the stated gate count and zero queries, with quadratic gate
and linear space bounds. -/
theorem qftLedger (n : ℕ) :
    GateCount (localProgramCircuit (localQFT n)) = qftGateCount n ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
      qftGateCount n ≤ 2 * (n + 1) ^ 2 ∧
      qftSpaceCost n ≤ n + 1 := by
  obtain ⟨-, -, -, hg, hq, -⟩ := localQFT_exact_gate_counts_and_wires n
  refine ⟨?_, hq, ?_, ?_⟩
  · rw [hg]
    rfl
  · have h1 : n * (n - 1) / 2 ≤ n * n := by
      calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
        _ ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    have h2 : n / 2 ≤ n := Nat.div_le_self n 2
    show qftGateCount n ≤ 2 * (n + 1) ^ 2
    unfold qftGateCount
    nlinarith
  · show qftSpaceCost n ≤ n + 1
    unfold qftSpaceCost
    omega

/-- The continued-fraction bit cost is its stage count times the schoolbook multiplication cost,
and exceeds the stage count when `M ≥ 2`. -/
theorem cfBitCost_stagecount (M : ℕ) :
    cfBitCost M = cfStageCount M * schoolbookMulModBitCost (shorBitLength M) ∧
      (2 ≤ M → cfStageCount M < cfBitCost M) := by
  refine ⟨rfl, ?_⟩
  intro hM
  have hlog : 1 ≤ Nat.log2 M := by
    rw [Nat.log2_eq_log_two]
    have := Nat.log_pos (by norm_num) hM
    omega
  have hb : 2 ≤ shorBitLength M := by
    unfold shorBitLength
    omega
  have hs : 1 < schoolbookMulModBitCost (shorBitLength M) := by
    unfold schoolbookMulModBitCost
    nlinarith [sq_nonneg ((shorBitLength M : ℕ) - 1)]
  have hpos : 0 < cfStageCount M := Nat.succ_pos _
  show cfStageCount M < cfBitCost M
  unfold cfBitCost
  rw [show cfDepth M + 1 = cfStageCount M from rfl]
  calc cfStageCount M = cfStageCount M * 1 := (mul_one _).symm
    _ < cfStageCount M * schoolbookMulModBitCost (shorBitLength M) :=
      Nat.mul_lt_mul_of_pos_left hs hpos

/-- Scans a list of residues and returns the first greatest common divisor with `N` that is a
proper nontrivial factor. -/
def jointScanList (N : ℕ) : List (ZMod N) → Option ℕ
  | [] => none
  | y :: ys =>
    if 1 < Nat.gcd y.val N ∧ Nat.gcd y.val N < N then some (Nat.gcd y.val N)
    else jointScanList N ys

/-- Any value returned by `jointScanList` is a proper nontrivial divisor of `N`. -/
theorem jointScanList_sound {N : ℕ} :
    ∀ (l : List (ZMod N)) (d : ℕ), jointScanList N l = some d →
      1 < d ∧ d < N ∧ d ∣ N := by
  intro l
  induction l with
  | nil =>
    intro d h
    simp [jointScanList] at h
  | cons y ys ih =>
    intro d h
    simp only [jointScanList] at h
    split at h
    · rename_i hg
      injection h with hd
      subst hd
      exact ⟨hg.1, hg.2, Nat.gcd_dvd_right _ _⟩
    · exact ih d h

/-- If some listed residue yields a classical factor, `jointScanList` returns a value. -/
theorem jointScanList_complete {N : ℕ} [NeZero N] (l : List (ZMod N)) :
    ∀ y ∈ l, (residueClassicalFactor N y).isSome → (jointScanList N l).isSome := by
  induction l with
  | nil =>
    intro y hy
    cases hy
  | cons z ys ih =>
    intro y hy hySome
    simp only [List.mem_cons] at hy
    by_cases hg : 1 < Nat.gcd z.val N ∧ Nat.gcd z.val N < N
    · simp only [jointScanList, if_pos hg]
      rfl
    · simp only [jointScanList, if_neg hg]
      rcases hy with h | h
      · subst h
        unfold residueClassicalFactor at hySome
        rw [if_neg hg] at hySome
        cases hySome
      · exact ih y h hySome

/-- Combines the residue gcd scan with `bruteDlog` and assigns zero bit-cost and bit-space
values. -/
def jointRecovery : JointRecovery where
  factoring := fun N m ω => jointScanList N (List.ofFn ω)
  dlog := bruteDlog
  bitCost := fun _ _ _ _ => 0
  bitSpace := fun _ _ _ _ => 0

/-- The explicit joint recovery construction satisfies its soundness, completeness,
discrete-logarithm, and assigned resource-bound requirements. -/
theorem jointRecovery_correct : jointRecovery.Correct := by
  refine ⟨?_, ?_, bruteDlog_correct, ?_⟩
  · intro N m _ ω d hd
    exact jointScanList_sound _ _ hd
  · intro N m _ ω hex
    obtain ⟨i, hi⟩ := hex
    exact jointScanList_complete (List.ofFn ω) (ω i) (List.mem_ofFn.mpr ⟨i, rfl⟩) hi
  · refine ⟨1, 0, ?_⟩
    intro N p q m
    simp [jointRecovery]

/-- Assembles decoder existence, factoring preprocessing, random-base success,
discrete-logarithm sampling and recovery, reversible arithmetic, and Fourier and
continued-fraction resource statements in the framework of [Shor1997]. -/
theorem clause17 :

  (∀ k : ℕ, ∃ c : CompactAbelianDecoder k, c.Correct) ∧

  (Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessing) ∧

  (∀ (N : ℕ) [NeZero N] (a : (ZMod N)ˣ), 1 < N → Odd N →
    (randomBaseGood N a ↔ Even (orderOf a) ∧
      ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1)) ∧

  (∀ (N : ℕ) [NeZero N], 1 < N → Odd N →
    2 ≤ N.primeFactors.card →
      1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ randomBaseSuccess N) ∧

  (Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogTwoDimSamplingLaw) ∧

  (Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCandidateRecovery) ∧

  (Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodSamplingBudget) ∧

  (∃ dec : TwoDimDlogDecoder, dec.Correct) ∧

  (∃ ar : ReversibleArithmetic, ar.PolyBounded) ∧

  (∀ n : ℕ,
    GateCount (localProgramCircuit (localQFT n)) = qftGateCount n ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
      qftGateCount n ≤ 2 * (n + 1) ^ 2 ∧
      qftSpaceCost n ≤ n + 1) ∧

  (∀ (B M y p q : ℕ), 0 < q → q ≤ B → p < q → Nat.Coprime p q →
    2 * B ^ 2 < M → y < M → |(y : ℚ) / M - (p : ℚ) / q| ≤ 1 / (M : ℚ) →
    (cfRationalDecode B M y).1 = some (p, q) ∧
      (cfRationalDecode B M y).2.1 ≤ cfDepth M + 1 ∧
      (cfRationalDecode B M y).2.2 = (cfDepth M + 1) * (cfDepth M + 2) / 2) ∧

  (∀ M : ℕ,
    cfBitCost M = cfStageCount M * schoolbookMulModBitCost (shorBitLength M) ∧
      (2 ≤ M → cfStageCount M < cfBitCost M)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨trivialDecoder k, trivialDecoder_correct k⟩
  · exact Qatlib.Concepts.PeriodSampling.FactorAlgorithm.factoringPreprocessing
  · exact random_base_exact_order_factor_characterization
  · exact random_base_crt_success_bound
  · exact Qatlib.Concepts.PeriodSampling.FactorAlgorithm.DlogTwoDimSamplingLaw_proof
  · exact Qatlib.Concepts.PeriodSampling.FactorAlgorithm.DlogCandidateRecovery_proof
  · exact Qatlib.Concepts.PeriodSampling.DlogGoodProb.dlogGoodSamplingBudget
  · exact ⟨bruteDlog, bruteDlog_correct⟩
  · exact ⟨arith, arith_poly⟩
  · exact qftLedger
  · exact continued_fraction_unique_window_decode_and_counts
  · exact cfBitCost_stagecount

/-- Defines an integer matrix by four prioritized entries at the indices `p` and `q`, with
identity entries elsewhere. -/
def blockAt {k : ℕ} (p q : Fin k) (a b c d : ℤ) : IMat k := fun i j =>
  if i = p ∧ j = p then a
  else if i = p ∧ j = q then b
  else if i = q ∧ j = p then c
  else if i = q ∧ j = q then d
  else if i = j then 1
  else 0

/-- Expands an entry of `blockAt` into its defining conditional expression. -/
theorem blockAt_apply {k : ℕ} (p q : Fin k) (a b c d : ℤ) (i j : Fin k) :
    blockAt p q a b c d i j =
      (if i = p ∧ j = p then a
      else if i = p ∧ j = q then b
      else if i = q ∧ j = p then c
      else if i = q ∧ j = q then d
      else if i = j then 1
      else 0) := rfl

/-- For distinct `p` and `q`, computes the action of `blockAt` on a column vector as a
two-coordinate transformation. -/
theorem sum_blockAt {k : ℕ} {p q : Fin k} (hpq : p ≠ q) (a b c d : ℤ) (w : Fin k → ℤ)
    (i : Fin k) :
    ∑ t, blockAt p q a b c d i t * w t =
      if i = p then a * w p + b * w q
      else if i = q then c * w p + d * w q
      else w i := by
  have hsubset : ∀ t : Fin k, t ∉ ({p, q, i} : Finset (Fin k)) →
      blockAt p q a b c d i t * w t = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    have htp : t ≠ p := ht.1
    have htq : t ≠ q := ht.2.1
    have hti : i ≠ t := fun h => ht.2.2 h.symm
    simp [blockAt_apply, htp, htq, hti]
  by_cases hp : i = p
  · have hsum : ∑ t, blockAt p q a b c d i t * w t
        = ∑ t ∈ ({p, q, i} : Finset (Fin k)), blockAt p q a b c d i t * w t :=
      (Finset.sum_subset (s₁ := ({p, q, i} : Finset (Fin k))) (Finset.subset_univ _)
        (fun t _ ht => hsubset t ht)).symm
    rw [hsum]
    have hpq' : ({p, q, i} : Finset (Fin k)) = {p, q} := by
      ext t
      simp [hp, or_comm, or_left_comm]
    rw [hpq', Finset.sum_insert (by simp [hpq, Ne.symm hpq]), Finset.sum_singleton, if_pos hp]
    simp [blockAt_apply, hp, hpq, Ne.symm hpq]
  · by_cases hq : i = q
    · have hsum : ∑ t, blockAt p q a b c d i t * w t
          = ∑ t ∈ ({p, q, i} : Finset (Fin k)), blockAt p q a b c d i t * w t :=
        (Finset.sum_subset (s₁ := ({p, q, i} : Finset (Fin k))) (Finset.subset_univ _)
          (fun t _ ht => hsubset t ht)).symm
      rw [hsum]
      have hpq' : ({p, q, i} : Finset (Fin k)) = {p, q} := by
        ext t
        simp [hq, or_comm, or_left_comm]
      rw [hpq', Finset.sum_insert (by simp [hpq, Ne.symm hpq]), Finset.sum_singleton,
        if_neg hp, if_pos hq]
      simp [blockAt_apply, hp, hq, hpq, Ne.symm hpq]
    · have hsum : ∑ t, blockAt p q a b c d i t * w t
          = ∑ t ∈ ({p, q, i} : Finset (Fin k)), blockAt p q a b c d i t * w t :=
        (Finset.sum_subset (s₁ := ({p, q, i} : Finset (Fin k))) (Finset.subset_univ _)
          (fun t _ ht => hsubset t ht)).symm
      rw [hsum, Finset.sum_insert (by simp [hpq, Ne.symm hpq, hp, Ne.symm hp, hq, Ne.symm hq]),
        Finset.sum_insert (by simp [hpq, Ne.symm hpq, hq, Ne.symm hq]),
        Finset.sum_singleton, if_neg hp, if_neg hq]
      simp [blockAt_apply, hp, hq, hpq, Ne.symm hpq]

/-- For distinct `p` and `q`, computes the action of a row vector on `blockAt` as a
two-coordinate transformation. -/
theorem sum_blockAt' {k : ℕ} {p q : Fin k} (hpq : p ≠ q) (a b c d : ℤ) (w : Fin k → ℤ)
    (j : Fin k) :
    ∑ t, w t * blockAt p q a b c d t j =
      if j = p then w p * a + w q * c
      else if j = q then w p * b + w q * d
      else w j := by
  have h : ∀ t, w t * blockAt p q a b c d t j = blockAt p q a c b d j t * w t := by
    intro t
    rw [mul_comm]
    congr 1
    rw [blockAt_apply, blockAt_apply]
    by_cases h1 : j = p
    · rw [h1]
      by_cases h2 : t = p
      · rw [h2]; simp [hpq, Ne.symm hpq]
      · by_cases h3 : t = q
        · rw [h3]; simp [hpq, Ne.symm hpq]
        · have h2' : p ≠ t := Ne.symm h2
          have h3' : q ≠ t := Ne.symm h3
          simp [h2, h2', h3, h3', hpq, Ne.symm hpq]
    · by_cases h3 : j = q
      · rw [h3]
        by_cases h2 : t = p
        · rw [h2]; simp [hpq, Ne.symm hpq]
        · by_cases h4 : t = q
          · rw [h4]; simp [hpq, Ne.symm hpq]
          · have h2' : p ≠ t := Ne.symm h2
            have h4' : q ≠ t := Ne.symm h4
            simp [h2, h2', h4, h4', hpq, Ne.symm hpq]
      · have h1' : p ≠ j := Ne.symm h1
        have h3' : q ≠ j := Ne.symm h3
        by_cases h2 : t = p
        · rw [h2]; simp [h1, h1', h3, h3', hpq, Ne.symm hpq]
        · by_cases h4 : t = q
          · rw [h4]; simp [h1, h1', h3, h3', hpq, Ne.symm hpq]
          · by_cases h5 : t = j
            · rw [h5]; simp [h1, h1', h3, h3', hpq, Ne.symm hpq]
            · have h2' : p ≠ t := Ne.symm h2
              have h4' : q ≠ t := Ne.symm h4
              have h5' : j ≠ t := Ne.symm h5
              simp [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', hpq, Ne.symm hpq]
  simp_rw [h]
  rw [sum_blockAt hpq a c b d]
  by_cases h1 : j = p <;> by_cases h2 : j = q
  all_goals simp_all [hpq, Ne.symm hpq]
  all_goals try (intro h'; simp_all [hpq, Ne.symm hpq])
  all_goals try (exact Ne.symm (by assumption))
  all_goals try (split_ifs <;> simp_all [hpq, Ne.symm hpq])
  all_goals try ring

/-- The block matrix with diagonal coefficients one and off-diagonal coefficients zero is the
identity when its two indices are distinct. -/
theorem blockAt_one {k : ℕ} (p q : Fin k) (hpq : p ≠ q) :
    blockAt p q 1 0 0 1 = (1 : IMat k) := by
  ext i j
  rw [blockAt_apply]
  by_cases h1 : i = p <;> by_cases h2 : j = p <;> by_cases h3 : i = q <;> by_cases h4 : j = q
  all_goals simp_all [Matrix.one_apply, hpq, Ne.symm hpq]
  all_goals try (intro h'; simp_all [Matrix.one_apply, hpq, Ne.symm hpq])
  all_goals try (exact Ne.symm (by assumption))
  all_goals try (split_ifs <;> simp_all [Matrix.one_apply, hpq, Ne.symm hpq])
  all_goals try ring

/-- For distinct indices, multiplying two embedded blocks gives the block whose coefficients are
the ordinary two-by-two matrix product. -/
theorem blockAt_mul {k : ℕ} {p q : Fin k} (hpq : p ≠ q) (a b c d a' b' c' d' : ℤ) :
    blockAt p q a b c d * blockAt p q a' b' c' d'
      = blockAt p q (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  rw [Matrix.mul_apply, sum_blockAt hpq]
  simp only [blockAt_apply]
  by_cases hp : i = p <;> by_cases hq : i = q <;> by_cases hj1 : j = p <;> by_cases hj2 : j = q
  all_goals simp_all [hpq, Ne.symm hpq]
  all_goals try (intro h'; simp_all [hpq, Ne.symm hpq])
  all_goals try (exact Ne.symm (by assumption))
  all_goals try (split_ifs <;> simp_all [hpq, Ne.symm hpq])
  all_goals try ring

/-- Computes every entry of a diagonal matrix multiplied on the left and right by embedded
two-coordinate blocks. -/
theorem blockAt_diagonal_blockAt_apply {k : ℕ} {p q : Fin k} (hpq : p ≠ q)
    (a b c d a' b' c' d' : ℤ) (w : Fin k → ℤ) (i j : Fin k) :
    (blockAt p q a b c d * Matrix.diagonal w * blockAt p q a' b' c' d') i j =
      if i = p ∧ j = p then a * w p * a' + b * w q * c'
      else if i = p ∧ j = q then a * w p * b' + b * w q * d'
      else if i = q ∧ j = p then c * w p * a' + d * w q * c'
      else if i = q ∧ j = q then c * w p * b' + d * w q * d'
      else if i = j then w i
      else 0 := by
  rw [Matrix.mul_apply]
  show ∑ t, (blockAt p q a b c d * Matrix.diagonal w) i t * blockAt p q a' b' c' d' t j = _
  simp_rw [Matrix.mul_diagonal]
  simp_rw [mul_assoc]
  rw [sum_blockAt hpq]
  simp only [blockAt_apply]
  by_cases hp : i = p <;> by_cases hq : i = q <;> by_cases hj1 : j = p <;> by_cases hj2 : j = q <;>
    by_cases hij : i = j
  all_goals simp_all [hpq, Ne.symm hpq]
  all_goals try (intro h'; simp_all [hpq, Ne.symm hpq])
  all_goals try (exact Ne.symm (by assumption))
  all_goals try (split_ifs <;> simp_all [hpq, Ne.symm hpq])
  all_goals try ring

/-- The stated four coefficient identities imply that the two embedded blocks multiply to the
identity. -/
theorem blockAt_unit {k : ℕ} {p q : Fin k} (hpq : p ≠ q) (a b c d a' b' c' d' : ℤ)
    (h1 : a * a' + b * c' = 1) (h2 : a * b' + b * d' = 0) (h3 : c * a' + d * c' = 0)
    (h4 : c * b' + d * d' = 1) :
    blockAt p q a b c d * blockAt p q a' b' c' d' = (1 : IMat k) := by
  rw [blockAt_mul hpq, h1, h2, h3, h4]
  exact blockAt_one p q hpq

/-- An embedded block possessing the stated right inverse has determinant of absolute value one. -/
theorem det_blockAt_one {k : ℕ} {p q : Fin k} (hpq : p ≠ q) (a b c d a' b' c' d' : ℤ)
    (h : blockAt p q a b c d * blockAt p q a' b' c' d' = (1 : IMat k)) :
    (blockAt p q a b c d).det.natAbs = 1 := by
  have h1 : (blockAt p q a b c d).det * (blockAt p q a' b' c' d').det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  have h2 : (blockAt p q a b c d).det = 1 ∨ (blockAt p q a b c d).det = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one h1
  rcases h2 with h2 | h2 <;> simp [h2]

/-- For two distinct positive diagonal entries, produces positive replacements and integer left
and right transformations with right inverses and determinants of absolute value one. -/
theorem diagMergeAt {k : ℕ} (d : Fin k → ℕ) {p q : Fin k} (hpq : p ≠ q)
    (hp : 0 < d p) (hq : 0 < d q) :
    ∃ (g l : ℕ) (U V Uinv Vinv : IMat k),
      0 < g ∧ 0 < l ∧
      U * Uinv = (1 : IMat k) ∧ V * Vinv = (1 : IMat k) ∧
      U.det.natAbs = 1 ∧ V.det.natAbs = 1 ∧
      U * Matrix.diagonal (fun i => (d i : ℤ)) * V
        = Matrix.diagonal (fun i =>
          ((if i = p then g else if i = q then l else d i : ℕ) : ℤ)) := by
  classical
  set g := Nat.gcd (d p) (d q) with hg0
  have hg : 0 < g := by
    rw [hg0]
    exact Nat.gcd_pos_of_pos_left _ hp
  set x' := (d p) / g with hx'
  set y' := (d q) / g with hy'
  set l := Nat.lcm (d p) (d q) with hl0
  have hlpos : 0 < l := by
    rw [hl0]
    exact Nat.lcm_pos hp hq
  have hgxNat : g * x' = d p := by
    rw [hx']
    exact Nat.mul_div_cancel' (by rw [hg0]; exact Nat.gcd_dvd_left _ _)
  have hgyNat : g * y' = d q := by
    rw [hy']
    exact Nat.mul_div_cancel' (by rw [hg0]; exact Nat.gcd_dvd_right _ _)
  have hx'pos : 0 < x' := by
    rcases Nat.eq_zero_or_pos x' with h | h
    · rw [h, mul_zero] at hgxNat
      omega
    · exact h
  have hy'pos : 0 < y' := by
    rcases Nat.eq_zero_or_pos y' with h | h
    · rw [h, mul_zero] at hgyNat
      omega
    · exact h
  have hgcd1 : Nat.gcd x' y' = 1 := by
    by_contra h
    obtain ⟨e, hed, he1⟩ : ∃ e, e ∣ Nat.gcd x' y' ∧ e ≠ 1 := ⟨Nat.gcd x' y', dvd_rfl, h⟩
    have hep : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | hp'
      · subst h0
        have hgz : Nat.gcd x' y' = 0 := zero_dvd_iff.1 hed
        have hgp : 0 < Nat.gcd x' y' :=
          Nat.gcd_pos_of_pos_left y' hx'pos
        omega
      · exact hp'
    have he2 : 1 < e := by omega
    have hmul : 1 < e * g := by nlinarith
    have hd1 : e * g ∣ d p := by
      have ha : e ∣ x' := hed.trans (Nat.gcd_dvd_left x' y')
      have hb : e * g ∣ x' * g := Nat.mul_dvd_mul_right ha g
      rw [Nat.mul_comm x' g, hgxNat] at hb
      exact hb
    have hd2 : e * g ∣ d q := by
      have ha : e ∣ y' := hed.trans (Nat.gcd_dvd_right x' y')
      have hb : e * g ∣ y' * g := Nat.mul_dvd_mul_right ha g
      rw [Nat.mul_comm y' g, hgyNat] at hb
      exact hb
    have hdv : e * g ∣ g := by
      rw [hg0]
      exact Nat.dvd_gcd hd1 hd2
    have hle : e * g ≤ g := Nat.le_of_dvd hg hdv
    nlinarith
  have hbez : (Nat.gcdA x' y' : ℤ) * (x' : ℤ) + (Nat.gcdB x' y' : ℤ) * (y' : ℤ) = 1 := by
    have h1 := (Nat.gcd_eq_gcd_ab x' y').symm
    rw [hgcd1] at h1
    push_cast at h1
    linear_combination h1
  have hgp : ((g : ℕ) : ℤ) * (x' : ℤ) = (d p : ℤ) := by exact_mod_cast hgxNat
  have hgq : ((g : ℕ) : ℤ) * (y' : ℤ) = (d q : ℤ) := by exact_mod_cast hgyNat
  have hllNat : l = g * x' * y' := by
    have key : d p * d q = (g * (x' * y')) * g := by
      rw [← hgxNat, ← hgyNat]
      ring
    have h2 : Nat.lcm (d p) (d q) = d p * d q / g := by
      rw [Nat.lcm, hg0]
    rw [hl0, h2, key, Nat.mul_div_cancel (g * (x' * y')) hg]
    ring
  have hll : ((l : ℕ) : ℤ) = ((g : ℕ) : ℤ) * (x' : ℤ) * (y' : ℤ) := by
    exact_mod_cast hllNat
  set u := Nat.gcdA x' y' with hu
  set v := Nat.gcdB x' y' with hv
  refine ⟨g, l,
    blockAt p q u v (-((y' : ℤ))) ((x' : ℤ)),
    blockAt p q (1 : ℤ) (-((v : ℤ) * (y' : ℤ))) 1 (u * (x' : ℤ)),
    blockAt p q ((x' : ℤ)) (-v) ((y' : ℤ)) u,
    blockAt p q (u * (x' : ℤ)) (v * (y' : ℤ)) (-1) (1 : ℤ), hg, hlpos, ?_, ?_, ?_, ?_, ?_⟩
  · refine blockAt_unit hpq u v (-((y' : ℤ))) ((x' : ℤ)) ((x' : ℤ)) (-v) ((y' : ℤ)) u
      ?_ ?_ ?_ ?_
    · linear_combination hbez
    · ring
    · ring
    · linear_combination hbez
  · refine blockAt_unit hpq (1 : ℤ) (-((v : ℤ) * (y' : ℤ))) 1 (u * (x' : ℤ))
      (u * (x' : ℤ)) (v * (y' : ℤ)) (-1) (1 : ℤ) ?_ ?_ ?_ ?_
    · linear_combination hbez
    · ring
    · ring
    · linear_combination hbez
  · exact det_blockAt_one hpq u v (-((y' : ℤ))) ((x' : ℤ)) ((x' : ℤ)) (-v) ((y' : ℤ)) u
      (blockAt_unit hpq u v (-((y' : ℤ))) ((x' : ℤ)) ((x' : ℤ)) (-v) ((y' : ℤ)) u
        (by linear_combination hbez) (by ring) (by ring) (by linear_combination hbez))
  · exact det_blockAt_one hpq (1 : ℤ) (-((v : ℤ) * (y' : ℤ))) 1 (u * (x' : ℤ))
      (u * (x' : ℤ)) (v * (y' : ℤ)) (-1) (1 : ℤ)
      (blockAt_unit hpq (1 : ℤ) (-((v : ℤ) * (y' : ℤ))) 1 (u * (x' : ℤ))
        (u * (x' : ℤ)) (v * (y' : ℤ)) (-1) (1 : ℤ)
        (by linear_combination hbez) (by ring) (by ring) (by linear_combination hbez))
  · ext i j
    rw [blockAt_diagonal_blockAt_apply hpq]
    simp only [Matrix.diagonal_apply]
    have harith1 : u * (d p : ℤ) * 1 + v * (d q : ℤ) * 1 = ((g : ℕ) : ℤ) := by
      rw [← hgp, ← hgq]
      linear_combination ((g : ℕ) : ℤ) * hbez
    have harith2 : u * (d p : ℤ) * (-(v * (y' : ℤ))) + v * (d q : ℤ) * (u * (x' : ℤ))
        = 0 := by
      rw [← hgp, ← hgq]
      ring
    have harith3 : (-(y' : ℤ)) * (d p : ℤ) * 1 + (x' : ℤ) * (d q : ℤ) * 1 = 0 := by
      rw [← hgp, ← hgq]
      ring
    have harith4 : (-(y' : ℤ)) * (d p : ℤ) * (-(v * (y' : ℤ)))
        + (x' : ℤ) * (d q : ℤ) * (u * (x' : ℤ)) = ((l : ℕ) : ℤ) := by
      rw [← hgp, ← hgq, hll]
      linear_combination ((g : ℕ) : ℤ) * (x' : ℤ) * (y' : ℤ) * hbez
    clear hg0 hx' hy' hl0 hgxNat hgyNat hgcd1 hgp hgq hu hv hbez hx'pos hy'pos hlpos hg hp
      hq hll hllNat
    split_ifs
    all_goals first
      | exact harith1
      | exact harith2
      | exact harith3
      | exact harith4
      | rfl
      | aesop

/-- The schoolbook modular multiplication cost is `2 * b * b + b` and is at most `3 * (b + 1) ^
2`. -/
theorem schoolbookLedger (b : ℕ) :
    schoolbookMulModBitCost b = 2 * b * b + b ∧
      schoolbookMulModBitCost b ≤ 3 * (b + 1) ^ 2 := by
  refine ⟨rfl, ?_⟩
  unfold schoolbookMulModBitCost
  nlinarith [sq_nonneg ((b : ℕ) + 1), sq_nonneg ((b : ℕ) - 1)]

/-- Expands the gcd bit cost as a Euclidean step bound times its per-step cost, with the stated
bit-length and multiplication formulas. -/
theorem gcdLedger (N : ℕ) :
    gcdBitCost N = euclidStepBound N * euclidStepBitCost N ∧
      euclidStepBound N = 2 * shorBitLength N + 1 ∧
      euclidStepBitCost N = schoolbookMulModBitCost (shorBitLength N) :=
  ⟨rfl, rfl, rfl⟩

/-- For a nonsingular integer presentation, classical canonicalization is canonical, preserves
the column span, satisfies the entry bound, and equals interleaved canonicalization. -/
theorem presentationBridge (k : ℕ) (A : IMat k) (hA : A.det ≠ 0) :
    IsCanonicalHNF (classicalCanonicalize A) ∧
      colSpan (classicalCanonicalize A) = colSpan A ∧
      (∀ i j : Fin k,
        (classicalCanonicalize A i j).natAbs ≤ 2 ^ (2 * (inputBitLength A) ^ 2)) ∧
      interleavedCanonicalize A = classicalCanonicalize A :=
  ⟨classicalCanonicalize_isCanonical A hA, colSpan_classicalCanonicalize A hA,
    fun i j => classicalCanonicalize_bitBound A hA i j, interleavedCanonicalize_eq A hA⟩

/-- Once `BitMachineAfter` is `none`, it remains `none` at every later time. -/
private theorem after_none_add {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {M : Turing.TM0.Machine Γ Λ} {input : List Γ} {t : ℕ}
    (h : BitMachineAfter M input t = none) (k : ℕ) :
    BitMachineAfter M input (t + k) = none := by
  induction k with
  | zero => exact h
  | succ k ih => simp [BitMachineAfter, ih]

/-- If a machine is in a terminal configuration at time `t`, any time `s` with a defined
configuration satisfies `s ≤ t`. -/
private theorem terminal_time_le {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {M : Turing.TM0.Machine Γ Λ} {input : List Γ} {t s : ℕ}
    {c d : Turing.TM0.Cfg Γ Λ}
    (ht : BitMachineAfter M input t = some c) (hc : Turing.TM0.step M c = none)
    (hs : BitMachineAfter M input s = some d) : s ≤ t := by
  by_contra h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show t + 1 ≤ s by omega)
  have hn : BitMachineAfter M input (t + 1) = none := by
    simp [BitMachineAfter, ht, hc]
  have hn' := after_none_add hn k
  rw [← hk, hs] at hn'
  contradiction

/-- Two terminal configurations reached by the same machine on the same input are equal. -/
theorem canonical_machine_final_unique {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {M : Turing.TM0.Machine Γ Λ} {input : List Γ} {t s : ℕ}
    {c d : Turing.TM0.Cfg Γ Λ}
    (ht : BitMachineAfter M input t = some c) (hc : Turing.TM0.step M c = none)
    (hs : BitMachineAfter M input s = some d) (hd : Turing.TM0.step M d = none) : c = d := by
  have hts := terminal_time_le ht hc hs
  have hst := terminal_time_le hs hd ht
  have heq : t = s := by omega
  subst s
  exact Option.some.inj (ht.symm.trans hs)

/-- The one-by-one integer matrix with its single entry equal to 129. -/
private def rankOneCollision : IMat 1 := fun _ _ => 129
/-- The two-by-two diagonal integer matrix with diagonal entries one and two. -/
private def rankTwoCollision : IMat 2 := fun i j => if i = j then (i.val : ℤ) + 1 else 0

/-- The one-by-one presentation with entry 129 and the two-by-two diagonal presentation with
entries one and two have identical presentation tapes. -/
theorem presentation_tape_dimension_collision :
    presentationTape (fun _ _ => 129 : IMat 1) =
      presentationTape (fun i j => if i = j then (i.val : ℤ) + 1 else 0 : IMat 2) := by decide

/-- Both presentations in the tape-collision example have nonzero determinant. -/
theorem presentation_collision_full_rank :
    IsCompactPresentation (fun _ _ => 129 : IMat 1) ∧
      IsCompactPresentation (fun i j => if i = j then (i.val : ℤ) + 1 else 0 : IMat 2) := by
  constructor
  · norm_num [IsCompactPresentation, Matrix.det_unique]
  · norm_num [IsCompactPresentation, Matrix.det_fin_two]

/-- The specified uniform canonical-basis machine predicate is false for the presentation-tape
encoding that allows the dimension collision. -/
theorem not_uniformCanonicalBasisMachine : ¬ UniformCanonicalBasisMachine := by
  rintro ⟨machine, out, _, h⟩
  obtain ⟨t, c, ht, hc, hout⟩ := h 1 rankOneCollision
  obtain ⟨s, d, hs, hd, hout'⟩ := h 2 rankTwoCollision
  have htape : presentationTape rankOneCollision = presentationTape rankTwoCollision :=
    presentation_tape_dimension_collision
  rw [← htape] at hs
  have heq := canonical_machine_final_unique ht hc hs hd
  subst d
  have hlen := congrArg List.length (hout.symm.trans hout')
  norm_num [List.finRange_succ] at hlen

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
