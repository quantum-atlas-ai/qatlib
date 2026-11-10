/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianDefs
import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianSieve
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieve
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge
import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawDihe
import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsDihe
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe
import Qatlib.Concepts.HspRecovery.RecordExtract.SummandExtractionDihe
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Multiset.Pi
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve

open Qatlib
open scoped Classical BigOperators ENNReal

def generalSlopeBits (N : ℕ) : ℕ := Nat.log2 N + 1

def generalSlopeBit (N : ℕ) (s : ZMod N) (i : ℕ) : Bool :=
  decide (s.val / 2 ^ i % 2 = 1)

def generalSlopeOfBits (N : ℕ) (k : ℕ) (b : ℕ → Bool) : ZMod N :=
  ((∑ i : Fin k, if b i.val then (2 ^ (i : ℕ) : ℕ) else 0 : ℕ) : ZMod N)

def generalSlopeBitList (N : ℕ) (s : ZMod N) : List Bool :=
  (List.range (generalSlopeBits N)).map (generalSlopeBit N s)

def bitListValue (bs : List Bool) : ℕ :=
  ∑ i ∈ Finset.range bs.length, if bs.getD i false then (2 ^ i : ℕ) else 0

def generalDescentSlope (N : ℕ) (k : ℕ) (s : ZMod N) : ZMod N :=
  ((s.val / 2 ^ k : ℕ) : ZMod N)

def generalDescentCandidate (N : ℕ) (bs : List Bool) : ZMod N :=
  ((bitListValue bs : ℕ) : ZMod N)

def generalWindowKey (N q : ℕ) (k : ZMod N) : ℕ := k.val % q

def generalWindowAgree (N q : ℕ) (k ℓ : ZMod N) : Prop :=
  generalWindowKey N q k = generalWindowKey N q ℓ

noncomputable def radixDigitCount (r : ℕ) (N : ℕ) : ℕ :=
  if r ≤ 1 then 0 else Nat.log r (N - 1) + 1

noncomputable def radixDigits (r : ℕ) (N : ℕ) (s : ZMod N) : List ℕ :=
  (List.range (radixDigitCount r N)).map fun i => (s.val / r ^ i) % r

noncomputable def radixWidths (r : ℕ) (N : ℕ) : List ℕ :=
  (List.range (radixDigitCount r N)).map fun i => radixDigitCount r N - i

noncomputable def radixRecoverySchedule (r : ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (radixWidths r (r ^ n)).map fun w => (w, 24 * 2 ^ (3 * Nat.ceil (Real.sqrt w)))

noncomputable def radixRecoverySamples (r : ℕ) (n : ℕ) : ℕ :=
  (radixRecoverySchedule r n).foldr (fun p acc => p.2 + acc) 0

def abelianShiftOracle (n : ℕ) {S : Type} (f g : ZMod (2 ^ n) → S) : DihedralReg (2 ^ n) → S :=
  shiftToDihedralOracle f g

noncomputable def abelianShiftRun (n : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) : PMF (Option (ZMod (2 ^ n))) :=
  slopeDescent n S (shiftToDihedralOracle f g)

def abelianShiftQueries (n : ℕ) : ℕ := descentRecords n

def AbelianShiftEndpoint (A : Type) [AddCommGroup A] [Fintype A] : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ lg : RecoveryLedger,
      ((lg.queries : ℝ) ≤ 2 ^ (C * Real.sqrt (labelBits (Fintype.card A)))) ∧
      ((lg.bitOps : ℝ) ≤ 2 ^ (C * Real.sqrt (labelBits (Fintype.card A)))) ∧
      ∃ run : (S : Type) → (A → S) → (A → S) → PMF (Option A),
        ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
          (f g : A → S) (s : A),
          HiddenShift f g s →
          (∀ u : A, u ≠ s → run S f g (some u) = 0) ∧
            ENNReal.ofReal (2 / 3) ≤ run S f g (some s)

def AbelianShiftTransport (A : Type) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f g : A → S) (s : A),
    HiddenShift f g s → AbelianReflectionHides (shiftToDihedralOracle f g) s

def generalSortCompareSteps (L : ℕ) : ℕ := L * (Nat.log2 (L + 1) + 1)

def generalSortBitOps (L b : ℕ) : ℕ := generalSortCompareSteps L * b

def generalWorkspaceBits (L b : ℕ) : ℕ := L * (b + 2)

noncomputable def generalRecoveryLedger (N : ℕ) (samples : ℕ) : RecoveryLedger where
  samples := samples
  queries := samples
  macros := samples
  measurements := samples
  comparisons := generalSortCompareSteps samples
  bitOps := generalSortBitOps samples (labelBits N)
  integerBits := labelBits N
  workspaceBits := generalWorkspaceBits samples (labelBits N)

def GeneralShiftEndpoint (N : ℕ) (p : ℝ) (lg : RecoveryLedger) : Prop :=
  ∃ run : (S : Type) → (DihedralReg N → S) → PMF (Option (ZMod N)),
    lg.samples ≤ lg.queries ∧
    generalSortCompareSteps lg.samples ≤ lg.comparisons ∧
    generalSortBitOps lg.samples lg.integerBits ≤ lg.bitOps ∧
    0 < lg.workspaceBits ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (s : ZMod N),
      DihedralReflectionHides N f s →
      (∀ u : ZMod N, u ≠ s → run S f (some u) = 0) ∧
        ENNReal.ofReal p ≤ run S f (some s)

def generalBasePoint (N : ℕ) : DihedralReg N := (0, false)

noncomputable def generalPartnerSetWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Finset (DihedralReg N) := by
  letI : DecidableEq S := dec
  exact Finset.univ.filter fun q => f q = f (generalBasePoint N) ∧ q.2 = true

noncomputable def generalRecoveredSlopeWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ZMod N :=
  (generalPartnerSetWith dec f).sum fun q => q.1

noncomputable def generalRecoveryRunWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : PMF (Option (ZMod N)) :=
  PMF.pure (some (generalRecoveredSlopeWith dec f))

noncomputable def generalRecoveryRun {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : PMF (Option (ZMod N)) :=
  generalRecoveryRunWith (Classical.decEq S) f

def generalRecoveryQueryCount (N : ℕ) : ℕ := 2 * N

def generalRecoveryCompareCount (N : ℕ) : ℕ := 2 * N

def zmodBasisWidth (n : ℕ) : ℕ := Nat.sqrt n + 1

def zmodBasis {n : ℕ} [NeZero n] (m : ℕ) : Finset (ZMod n) :=
  (Finset.range m).image (fun i : ℕ => (i : ZMod n)) ∪
    (Finset.range (n / m + 2)).image (fun j : ℕ => ((j * m : ℕ) : ZMod n))

def AbelianDifferenceBasis {A : Type} [AddCommGroup A] (D : Finset A) : Prop :=
  ∀ s : A, ∃ d₁ ∈ D, ∃ d₂ ∈ D, d₂ - d₁ = s

noncomputable def productDifferenceBasis {ι : Type} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, NeZero (n i)) (D : ∀ i, Finset (ZMod (n i))) :
    Finset ((i : ι) → ZMod (n i)) := by
  classical
  exact (Finset.univ.filter fun x => ∀ i, x i ∈ D i)

noncomputable def abelianDifferenceBasis {A : Type} [AddCommGroup A] [Fintype A] {ι : Type} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, NeZero (n i)) (D : ∀ i, Finset (ZMod (n i)))
    (e : A ≃+ ((i : ι) → ZMod (n i))) : Finset A := by
  classical
  exact (Finset.univ.filter fun x => ∀ i, (e x) i ∈ D i)

def abelianPairs {A : Type} (D : List A) : List (A × A) :=
  D.flatMap fun d₁ => D.map fun d₂ => (d₁, d₂)

noncomputable def abelianShiftPair {A S : Type} [DecidableEq A] [DecidableEq S]
    (f g : A → S) (D : List A) : Option (A × A) :=
  (abelianPairs D).find? fun p => f p.1 = g p.2

noncomputable def abelianShiftCandidate {A S : Type} [AddCommGroup A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (D : List A) : Option A :=
  (abelianShiftPair f g D).map fun p => p.2 - p.1

noncomputable def abelianBasisShiftRun {A S : Type} [AddCommGroup A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (D : List A) : PMF (Option A) :=
  PMF.pure (abelianShiftCandidate f g D)

def abelianShiftQueryCount {A : Type} (D : List A) : ℕ := 2 * D.length

def abelianShiftCompareCount {A : Type} (D : List A) : ℕ := (D.length) ^ 2

noncomputable def abelianShiftLedger {A : Type} (D : List A) (bits : ℕ) : RecoveryLedger where
  samples := 2 * D.length
  queries := 2 * D.length
  macros := 2 * D.length
  measurements := 2 * D.length
  comparisons := max (D.length ^ 2) (sortCompareSteps (2 * D.length))
  bitOps := sortBitOps (2 * D.length) bits
  integerBits := bits
  workspaceBits := workspaceBits (max (2 * D.length) 1) bits

def abelianSpliceCoordWeight (n : ℕ) : ℕ := Nat.log2 n + 2

def abelianSpliceLevels {a : ℕ} (N : Fin a → ℕ) : ℕ :=
  ∑ j : Fin a, abelianSpliceCoordWeight (N j)

structure ReducedSubgroupData (N : ℕ) : Type where

  period : ℕ

  slope : Option ℕ
  deriving DecidableEq

def subgroupRotationPeriod {N : ℕ} (H : DihedralSubgroupData N) : ℕ := N / H.period

def reduceSubgroupData {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    ReducedSubgroupData N where
  period := H.period
  slope := H.slope.map (fun s => s.val % subgroupRotationPeriod H)

def ReducedSubgroupDataWellFormed {N : ℕ} (d : ReducedSubgroupData N) : Prop :=
  d.period ∣ N ∧ ∀ s, d.slope = some s → s < N / d.period

noncomputable def rotationPeriodCandidatesWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Finset ℕ := by
  letI := dec
  exact (Finset.range (N + 1)).filter fun j =>
    decide (j = N ∨ (1 ≤ j ∧ f (0, false) = f ((j : ℕ), false)))

noncomputable def rotationPeriodCandidates {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : Finset ℕ :=
  rotationPeriodCandidatesWith (Classical.decEq S) f

noncomputable def rotationPeriodOfWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ℕ :=
  (rotationPeriodCandidatesWith dec f).min' ⟨N, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp⟩

noncomputable def rotationPeriodOf {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : ℕ :=
  rotationPeriodOfWith (Classical.decEq S) f

noncomputable def reflectionPartnerCandidatesWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Finset ℕ := by
  letI := dec
  exact (Finset.range (N + 1)).filter fun b =>
    decide (b = N ∨ f (0, false) = f ((b : ℕ), true))

noncomputable def reflectionPartnerCandidates {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : Finset ℕ :=
  reflectionPartnerCandidatesWith (Classical.decEq S) f

noncomputable def reflectionPartnerMinWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ℕ :=
  (reflectionPartnerCandidatesWith dec f).min' ⟨N, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp⟩

noncomputable def reflectionPartnerMin {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : ℕ :=
  reflectionPartnerMinWith (Classical.decEq S) f

noncomputable def reflectionPartnerOfWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Option ℕ :=
  if reflectionPartnerMinWith dec f = N then none else some (reflectionPartnerMinWith dec f)

noncomputable def reflectionPartnerOf {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : Option ℕ :=
  reflectionPartnerOfWith (Classical.decEq S) f

noncomputable def subgroupReductionAnswerWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ReducedSubgroupData N where
  period := N / rotationPeriodOfWith dec f
  slope := (reflectionPartnerOfWith dec f).map (fun b => b % rotationPeriodOfWith dec f)

noncomputable def subgroupReductionAnswer {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : ReducedSubgroupData N :=
  subgroupReductionAnswerWith (Classical.decEq S) f

noncomputable def subgroupReductionRunWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : PMF (Option (ReducedSubgroupData N)) :=
  PMF.pure (some (subgroupReductionAnswerWith dec f))

noncomputable def subgroupReductionRun {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : PMF (Option (ReducedSubgroupData N)) :=
  subgroupReductionRunWith (Classical.decEq S) f

def subgroupReductionQueryCount (N : ℕ) : ℕ := 2 * N + 1

def subgroupReductionCompareCount (N : ℕ) : ℕ := 2 * N

noncomputable def subgroupReductionLedger (N : ℕ) : RecoveryLedger where
  samples := subgroupReductionQueryCount N
  queries := subgroupReductionQueryCount N
  macros := 0
  measurements := 0
  comparisons := sortCompareSteps (subgroupReductionQueryCount N)
  bitOps := sortBitOps (subgroupReductionQueryCount N) (labelBits N)
  integerBits := labelBits N
  workspaceBits := workspaceBits (N + 1) (labelBits N)

def ReducedSubgroupEndpoint (N : ℕ) [NeZero N] (lg : RecoveryLedger) : Prop :=
  ∃ run : (S : Type) → (DihedralReg N → S) → PMF (Option (ReducedSubgroupData N)),
    lg.samples ≤ lg.queries ∧
    sortCompareSteps lg.samples ≤ lg.comparisons ∧
    sortBitOps lg.samples lg.integerBits ≤ lg.bitOps ∧
    0 < lg.workspaceBits ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (H : DihedralSubgroupData N),
      DihedralSubgroupHides f H →
      (∀ o : Option (ReducedSubgroupData N),
          o ≠ some (reduceSubgroupData H) → run S f o = 0) ∧
        ENNReal.ofReal 1 ≤ run S f (some (reduceSubgroupData H))

def radixAlpha (r k : ℕ) : ℕ :=
  if k = 0 then 0 else Nat.findGreatest (fun j => r ^ j ∣ k) k

def radixMinAlpha (r : ℕ) (L : List ℕ) : ℕ :=
  match L with
  | [] => 0
  | k :: rest => rest.foldl (fun acc j => Nat.min acc (radixAlpha r j)) (radixAlpha r k)

def radixMinAlphaSublist (r : ℕ) (L : List ℕ) : List ℕ :=
  L.filter fun k => radixAlpha r k == radixMinAlpha r L

def radixPairValue (r N : ℕ) (k ℓ : ℕ) : ℕ :=
  max (radixAlpha r ((k + ℓ) % N)) (radixAlpha r ((k + N - ℓ) % N))

def radixPairs (L : List ℕ) : List (ℕ × ℕ) :=
  L.flatMap fun k => (L.filter fun l => l != k).map fun l => (k, l)

noncomputable def radixGreedyValue (r N : ℕ) (L : List ℕ) : ℕ :=
  (radixPairs (radixMinAlphaSublist r L)).foldl
    (fun acc p => max acc (radixPairValue r N p.1 p.2)) 0

noncomputable def radixGreedyPair (r N : ℕ) (L : List ℕ) : Option (ℕ × ℕ) :=
  (radixPairs (radixMinAlphaSublist r L)).foldl
    (fun best p => match best with
      | none => some p
      | some q =>
          if radixPairValue r N p.1 p.2 > radixPairValue r N q.1 q.2 then some p else best)
    none

def radixBeta (r n k : ℕ) : ℕ := (n - 1) - radixAlpha r k

noncomputable def radixValue (r n k : ℕ) : ℝ :=
  Real.exp (-(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)))

noncomputable def radixListValue (r n : ℕ) (L : List ℕ) : ℝ :=
  (L.map (radixValue r n)).sum

def radixFinalTest (r n k : ℕ) : Prop := r ^ (n - 1) ∣ k ∧ k ≠ 0

def radixDiff (k ℓ : ℕ) : ℕ := if k ≥ ℓ then k - ℓ else ℓ - k

def radixTritsShare (r a k ℓ j : ℕ) : Prop := r ^ (a + j) ∣ radixDiff k ℓ

instance (r a k ℓ j : ℕ) : Decidable (radixTritsShare r a k ℓ j) :=
  inferInstanceAs (Decidable (r ^ (a + j) ∣ radixDiff k ℓ))

noncomputable def radixSharedTrits (r k ℓ : ℕ) : ℕ :=
  Nat.findGreatest (fun j => radixTritsShare r (radixAlpha r k) k ℓ j) (radixDiff k ℓ)

noncomputable def radixExpectedChildValue (r n : ℕ) (k ℓ : ℕ) : ℝ :=
  (radixValue r n ((k + ℓ) % (r ^ n)) + radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))) / 2

def radixQuantumChildren {N : ℕ} (k ℓ : ZMod N) : ZMod N × ZMod N :=
  (k + ℓ, k - ℓ)

noncomputable def radixQuantumExtractLaw {N : ℕ} [NeZero N] (k ℓ : ZMod N) :
    PMF (Bool × ZMod N) :=
  (PMF.uniformOfFintype' Bool).bind fun b => PMF.pure (b, if b then k - ℓ else k + ℓ)

def radixQuotient (r a k m : ℕ) : ℕ := (k / r ^ a) % r ^ (m + 1)

def radixFirstDigit (r a k m : ℕ) : ℕ := radixQuotient r a k m % r

def radixUpperDigits (r a k m : ℕ) : ℕ := radixQuotient r a k m / r

def radixPatternIndex (r a k m : ℕ) : ℕ × ℕ :=
  let d := radixFirstDigit r a k m
  let w := radixUpperDigits r a k m
  if d ≤ r - d then (d - 1, w) else (r - d - 1, r ^ m - 1 - w)

def radixSignAgree (M k ℓ : ℕ) : Prop := M ∣ k + ℓ ∨ M ∣ radixDiff k ℓ

def radixShiftReadout (r n k : ℕ) : ℕ := (k / r ^ (n - 1)) % r

noncomputable def radixPeriodAttrition (r n : ℕ) (L' : List ℕ) : ℝ :=
  (L'.map (radixValue r n)).sum

def radixKeptLabels (r : ℕ) (L : List ℕ) : List ℕ :=
  L.filter fun k => !(radixAlpha r k == radixMinAlpha r L)

def radixGreedyChild (r N : ℕ) (k ℓ : ℕ) : ℕ :=
  if radixAlpha r ((k + ℓ) % N) < radixAlpha r ((k + N - ℓ) % N)
  then (k + N - ℓ) % N else (k + ℓ) % N

noncomputable def radixPeriodChildren (r N : ℕ) (L : List ℕ) : List ℕ :=
  match radixGreedyPair r N L with
  | none => []
  | some (k, ℓ) => [radixGreedyChild r N k ℓ]

noncomputable def radixPeriodStep (r N : ℕ) (L : List ℕ) : List ℕ :=
  (radixKeptLabels r L) ++ (radixPeriodChildren r N L)

noncomputable def radixSieveRun (r N : ℕ) : ℕ → List ℕ → List ℕ
  | 0, L => L
  | p + 1, L => radixPeriodStep r N (radixSieveRun r N p L)

noncomputable def radixGreedyPeriodValue (r n : ℕ) (L : List ℕ) : ℝ :=
  radixListValue r n (radixPeriodStep r (r ^ n) L)

noncomputable def radixQuantumPeriodValue (r n : ℕ) (L : List ℕ) : ℝ :=
  match radixGreedyPair r (r ^ n) L with
  | none => radixListValue r n (radixKeptLabels r L)
  | some (k, ℓ) =>
      radixListValue r n (radixKeptLabels r L) + radixExpectedChildValue r n k ℓ

structure RadixPeriodConditions (n : ℕ) (L : List ℕ) : Prop where

  bound : ∀ k ∈ L, k < 3 ^ n

  nonzero : ∀ k ∈ L, k ≠ 0

  nodup : L.Nodup

  states : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → k + ℓ ≠ 3 ^ n

  shared : ∃ m : ℕ, radixMinAlpha 3 L + m + 1 ≤ n ∧
    (m : ℝ) ≤ Real.sqrt (2 * ((n - 1 - radixMinAlpha 3 L : ℕ) : ℝ)) ∧
    radixGreedyValue 3 (3 ^ n) L ≤ radixMinAlpha 3 L + m

  productive : ∃ k ℓ : ℕ, radixGreedyPair 3 (3 ^ n) L = some (k, ℓ) ∧
    radixPairValue 3 (3 ^ n) k ℓ > radixMinAlpha 3 L

noncomputable def radixQuantumPeriodStep (r N : ℕ) (coin : Bool) (L : List ℕ) : List ℕ :=
  match radixGreedyPair r N L with
  | none => radixKeptLabels r L
  | some (k, ℓ) =>
      radixKeptLabels r L ++ [if coin then (k + N - ℓ) % N else (k + ℓ) % N]

noncomputable def radixQuantumSieveRun (r N : ℕ) : List Bool → ℕ → List ℕ → List ℕ
  | [], _, L => L
  | _, 0, L => L
  | c :: cs, p + 1, L => radixQuantumSieveRun r N cs p (radixQuantumPeriodStep r N c L)

noncomputable def radixQuantumRunValue (r n N : ℕ) : ℕ → List ℕ → ℝ
  | 0, L => radixListValue r n L
  | p + 1, L =>
      (radixQuantumRunValue r n N p (radixQuantumPeriodStep r N false L)
        + radixQuantumRunValue r n N p (radixQuantumPeriodStep r N true L)) / 2

noncomputable def RadixQuantumRunConditions (n : ℕ) : ℕ → List ℕ → Prop
  | 0, _ => True
  | p + 1, L =>
      RadixPeriodConditions n L ∧
        ∀ b : Bool, RadixQuantumRunConditions n p (radixQuantumPeriodStep 3 (3 ^ n) b L)

noncomputable def radixQuantumLeaves (r N : ℕ) : ℕ → List ℕ → List (List ℕ)
  | 0, L => [L]
  | p + 1, L =>
      radixQuantumLeaves r N p (radixQuantumPeriodStep r N false L)
        ++ radixQuantumLeaves r N p (radixQuantumPeriodStep r N true L)

def generalCollisionWidth (N : ℕ) : ℕ := Nat.sqrt N + 1

def generalCollisionRotations (N m : ℕ) : List (ZMod N) :=
  (List.range m).map fun i => (i : ZMod N)

def generalCollisionReflections (N m : ℕ) : List (ZMod N) :=
  (List.range (N / m + 2)).map fun j => (j * m : ZMod N)

def generalCollisionQueryCount (N m : ℕ) : ℕ :=
  (generalCollisionRotations N m).length + (generalCollisionReflections N m).length

def generalCollisionCompareCount (N m : ℕ) : ℕ :=
  (generalCollisionRotations N m).length * (generalCollisionReflections N m).length

noncomputable def generalCollisionLedger (N m : ℕ) : RecoveryLedger where
  samples := generalCollisionQueryCount N m
  queries := generalCollisionQueryCount N m
  macros := generalCollisionQueryCount N m
  measurements := generalCollisionQueryCount N m
  comparisons :=
    max (generalCollisionCompareCount N m) (sortCompareSteps (generalCollisionQueryCount N m))
  bitOps := sortBitOps (generalCollisionQueryCount N m) (labelBits N)
  integerBits := labelBits N
  workspaceBits := workspaceBits (generalCollisionQueryCount N m) (labelBits N)

noncomputable def generalCollisionMatch {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (a : ZMod N) (bs : List (ZMod N)) :
    Option (ZMod N) := by
  letI : DecidableEq S := dec
  match bs with
  | [] => exact none
  | b :: rest =>
    if f (b, true) = f (a, false) then exact some b
    else exact generalCollisionMatch dec f a rest
  termination_by bs.length
  decreasing_by simp

noncomputable def generalCollisionPair {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (m : ℕ) (rots : List (ZMod N)) :
    Option (ZMod N × ZMod N) := by
  match rots with
  | [] => exact none
  | a :: rest =>
    match generalCollisionMatch dec f a (generalCollisionReflections N m) with
    | none => exact generalCollisionPair dec f m rest
    | some b => exact some (a, b)
  termination_by rots.length
  decreasing_by simp

noncomputable def generalCollisionSlopeWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (m : ℕ) : Option (ZMod N) :=
  match generalCollisionPair dec f m (generalCollisionRotations N m) with
  | some (a, b) => some (b - a)
  | none => none

noncomputable def generalCollisionRunWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (m : ℕ) : PMF (Option (ZMod N)) :=
  PMF.pure (generalCollisionSlopeWith dec f m)

noncomputable def generalCollisionRun {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) (m : ℕ) : PMF (Option (ZMod N)) :=
  generalCollisionRunWith (Classical.decEq S) f m

def radixFinalStateLabel (r n a : ℕ) : ℕ := a * r ^ (n - 1)

def radixFinalIndex (r n k : ℕ) : ℕ := (k / r ^ (n - 1)) % r

def radixPhaseIndex (r n s k : ℕ) : ℕ := ((s * k) / r ^ (n - 1)) % r

noncomputable def radixRootOfUnity (r t : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((t : ℝ) / (r : ℝ)) : ℝ) * Complex.I))

def radixShiftCandidates (r : ℕ) [NeZero r] (a t : ℕ) : Finset (ZMod r) :=
  Finset.univ.filter fun u => u * (a : ZMod r) == (t : ZMod r)

def radixReadout (r : ℕ) [NeZero r] (a t : ℕ) : ZMod r :=
  (t : ZMod r) * (a : ZMod r)⁻¹

noncomputable def radixActualLabelLaw {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : PMF (ZMod N) :=
  (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => q.1)

noncomputable def radixActualLabels {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : ℕ → PMF (List ℕ)
  | 0 => pure []
  | i + 1 =>
    (radixActualLabelLaw f).bind fun k =>
      (radixActualLabels f i).map fun L => k.val :: L

noncomputable def radixSieveTerminalLabels {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r i p : ℕ) :
    PMF (List ℕ) :=
  (radixActualLabels f i).map fun L => radixSieveRun r N p L

def radixLevelSlope (r s j : ℕ) : ℕ :=
  match j with
  | 0 => s
  | j + 1 => radixLevelSlope r (s / r) j

def radixLevelDigit (r s j : ℕ) : ZMod r :=
  match j with
  | 0 => ((s % r : ℕ) : ZMod r)
  | j + 1 => radixLevelDigit r (s / r) j

def radixReadouts (r n s : ℕ) : List (ZMod r) :=
  match n with
  | 0 => []
  | Nat.succ n => radixLevelDigit r s 0 :: radixReadouts r n (s / r)

def radixReadoutValue (r : ℕ) : List (ZMod r) → ℕ
  | [] => 0
  | d :: rest => d.val + r * radixReadoutValue r rest

noncomputable def radixBranchPhase (χ : QState Bool) : Option ℂ :=
  if h : χ false = 0 then none else some (χ true / χ false)

noncomputable def radixTomographyIndex (r : ℕ) [NeZero r] (χ : QState Bool) : Option (ZMod r) :=
  match radixBranchPhase χ with
  | none => none
  | some w =>
      ((Finset.univ : Finset (ZMod r)).toList).find? fun t => decide (radixRootOfUnity r t.val = w)

noncomputable def radixActualRecords {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : ℕ → PMF (List (ZMod N × NormQ)) :=
  actualFreshRecords N f

noncomputable def radixActualTerminalLabels {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r i p : ℕ) :
    PMF (List ℕ) :=
  (radixActualRecords f i).map fun (L : List (ZMod N × NormQ)) =>
    radixSieveRun r N p (L.map fun (rec : ZMod N × NormQ) => rec.1.val)

noncomputable def radixObservedRecords {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : ℕ → PMF (List (ZMod N × S))
  | 0 => pure []
  | i + 1 =>
    (dihedralActualRecord N f).bind fun q =>
      (radixObservedRecords f i).map fun L => (q.1, q.2.1) :: L

noncomputable def radixFinalRecordBy {α : Type} [DecidableEq α]
    (r n : ℕ) (label : α → ℕ) (L : List α) (T : List ℕ) : Option α :=
  L.find? fun rec => decide (radixFinalTest r n (label rec) && decide (label rec ∈ T))

def radixSubgroupEmbedding (r N : ℕ) (b : ℕ) :
    DihedralReg (N / r) → DihedralReg N
  | (a, false) => (((r * a.val : ℕ) : ZMod N), false)
  | (a, true) => (((r * a.val + b : ℕ) : ZMod N), true)

def radixRestrictedOracle (r N : ℕ) (b : ℕ) {S : Type}
    (f : DihedralReg N → S) : DihedralReg (N / r) → S :=
  f ∘ radixSubgroupEmbedding r N b

def radixLift (r N : ℕ) (b : ℕ) (t : ZMod (N / r)) : ZMod N :=
  ((r * t.val + b : ℕ) : ZMod N)

def radixStepEmbedding (r n : ℕ) (b : ℕ) :
    DihedralReg (r ^ n) → DihedralReg (r ^ (n + 1))
  | (a, false) => (((r * a.val : ℕ) : ZMod (r ^ (n + 1))), false)
  | (a, true) => (((r * a.val + b : ℕ) : ZMod (r ^ (n + 1))), true)

def radixStepOracle {S : Type} (r n : ℕ) (b : ℕ)
    (f : DihedralReg (r ^ (n + 1)) → S) : DihedralReg (r ^ n) → S :=
  f ∘ radixStepEmbedding r n b

def radixStepLift (r n : ℕ) (b : ℕ) (t : ZMod (r ^ n)) : ZMod (r ^ (n + 1)) :=
  ((r * t.val + b : ℕ) : ZMod (r ^ (n + 1)))

end Qatlib.Concepts.HspRecovery.OpenSieve
