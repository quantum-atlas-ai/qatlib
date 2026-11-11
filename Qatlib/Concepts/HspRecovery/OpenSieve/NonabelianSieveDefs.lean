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

/-!
# Definitions for dihedral recovery and radix sieves

This module defines data, probability laws, and resource ledgers for dihedral hidden subgroup
recovery and abelian hidden shifts. Binary slope encodings, collision searches, difference
bases, and reduced subgroup answers provide interfaces for recovery procedures.
`GeneralShiftEndpoint`, `AbelianShiftEndpoint`, and `ReducedSubgroupEndpoint` express recovery
specifications together with conditions on resource ledgers.

The radix sieve definitions describe label divisibility, greedy pairing, sum and difference
branches, and potential functions in the setting of the dihedral sieve of [Kuperberg2005]. They
also specify distributions of labels extracted from oracle records, phase readouts, and oracle
restrictions for recursive radix descent.

## Main definitions

* `AbelianDifferenceBasis`: a finite set whose differences cover an abelian group.
* `ReducedSubgroupData`: rotation data with an optional natural number slope representative.
* `radixPeriodStep` and `radixQuantumPeriodStep`: greedy and coin-controlled updates of sieve
  labels.
* `RadixPeriodConditions`: hypotheses for a productive period of the ternary sieve.
* `radixActualRecords`: the law of fresh label and qubit records extracted from an oracle.
* `radixRestrictedOracle` and `radixStepOracle`: oracle restrictions used in radix descent.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

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

/-- The binary encoding length `Nat.log2 N + 1` used for slope representatives modulo `N`. -/
def generalSlopeBits (N : ℕ) : ℕ := Nat.log2 N + 1

/-- The Boolean value of the `i`th binary digit of the natural representative `s.val`, starting
with the least significant digit. -/
def generalSlopeBit (N : ℕ) (s : ZMod N) (i : ℕ) : Bool :=
  decide (s.val / 2 ^ i % 2 = 1)

/-- The element of `ZMod N` obtained by summing the first `k` Boolean digits with weights `2 ^
i`. -/
def generalSlopeOfBits (N : ℕ) (k : ℕ) (b : ℕ → Bool) : ZMod N :=
  ((∑ i : Fin k, if b i.val then (2 ^ (i : ℕ) : ℕ) else 0 : ℕ) : ZMod N)

/-- The first `generalSlopeBits N` binary digits of `s.val`, listed from least to most
significant. -/
def generalSlopeBitList (N : ℕ) (s : ZMod N) : List Bool :=
  (List.range (generalSlopeBits N)).map (generalSlopeBit N s)

/-- The natural number represented by a Boolean list whose head is the least significant binary
digit. -/
def bitListValue (bs : List Bool) : ℕ :=
  ∑ i ∈ Finset.range bs.length, if bs.getD i false then (2 ^ i : ℕ) else 0

/-- The quotient `s.val / 2 ^ k`, cast back to `ZMod N` after discarding the lowest `k` binary
digits. -/
def generalDescentSlope (N : ℕ) (k : ℕ) (s : ZMod N) : ZMod N :=
  ((s.val / 2 ^ k : ℕ) : ZMod N)

/-- The slope candidate in `ZMod N` obtained by interpreting `bs` as binary digits with the
least significant digit first. -/
def generalDescentCandidate (N : ℕ) (bs : List Bool) : ZMod N :=
  ((bitListValue bs : ℕ) : ZMod N)

/-- The remainder of the natural label representative `k.val` modulo the window modulus `q`. -/
def generalWindowKey (N q : ℕ) (k : ZMod N) : ℕ := k.val % q

/-- The condition that `k` and `ℓ` have equal window keys modulo `q`. -/
def generalWindowAgree (N q : ℕ) (k ℓ : ZMod N) : Prop :=
  generalWindowKey N q k = generalWindowKey N q ℓ

/-- The radix encoding length `Nat.log r (N - 1) + 1` for `r > 1`, and zero for `r ≤ 1`. -/
noncomputable def radixDigitCount (r : ℕ) (N : ℕ) : ℕ :=
  if r ≤ 1 then 0 else Nat.log r (N - 1) + 1

/-- The first `radixDigitCount r N` base-`r` digits of `s.val`, listed from least to most
significant. -/
noncomputable def radixDigits (r : ℕ) (N : ℕ) (s : ZMod N) : List ℕ :=
  (List.range (radixDigitCount r N)).map fun i => (s.val / r ^ i) % r

/-- The descending list of positive widths from `radixDigitCount r N` to one, or the empty list
when that count is zero. -/
noncomputable def radixWidths (r : ℕ) (N : ℕ) : List ℕ :=
  (List.range (radixDigitCount r N)).map fun i => radixDigitCount r N - i

/-- The recovery schedule for modulus `r ^ n`, assigning `24 * 2 ^ (3 * Nat.ceil (Real.sqrt w))`
samples to each width `w` in `radixWidths r (r ^ n)`. -/
noncomputable def radixRecoverySchedule (r : ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (radixWidths r (r ^ n)).map fun w => (w, 24 * 2 ^ (3 * Nat.ceil (Real.sqrt w)))

/-- The sum of the sample counts in `radixRecoverySchedule r n`. -/
noncomputable def radixRecoverySamples (r : ℕ) (n : ℕ) : ℕ :=
  (radixRecoverySchedule r n).foldr (fun p acc => p.2 + acc) 0

/-- The dihedral oracle obtained by combining the two functions `f` and `g` through
`shiftToDihedralOracle`. -/
def abelianShiftOracle (n : ℕ) {S : Type} (f g : ZMod (2 ^ n) → S) : DihedralReg (2 ^ n) → S :=
  shiftToDihedralOracle f g

/-- The distribution of optional shift candidates obtained by applying `slopeDescent` to the
dihedral oracle associated with `f` and `g`. -/
noncomputable def abelianShiftRun (n : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) : PMF (Option (ZMod (2 ^ n))) :=
  slopeDescent n S (shiftToDihedralOracle f g)

/-- The query count assigned to binary hidden shift descent, given by `descentRecords n`. -/
def abelianShiftQueries (n : ℕ) : ℕ := descentRecords n

/-- The existence of a positive constant and a ledger whose query and bit operation counts are
bounded by `2 ^ (C * Real.sqrt (labelBits (Fintype.card A)))`, together with a hidden shift
recovery distribution. Under the hidden shift promise, it assigns zero mass to incorrect
shifts and at least `2 / 3` to the correct shift. -/
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

/-- The requirement that every hidden shift instance on `A` yields an `AbelianReflectionHides`
instance through `shiftToDihedralOracle`, with the same shift. -/
def AbelianShiftTransport (A : Type) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f g : A → S) (s : A),
    HiddenShift f g s → AbelianReflectionHides (shiftToDihedralOracle f g) s

/-- The sorting comparison budget `L * (Nat.log2 (L + 1) + 1)` for `L` labels. -/
def generalSortCompareSteps (L : ℕ) : ℕ := L * (Nat.log2 (L + 1) + 1)

/-- The bit operation budget obtained by multiplying `generalSortCompareSteps L` by the label
width `b`. -/
def generalSortBitOps (L b : ℕ) : ℕ := generalSortCompareSteps L * b

/-- The workspace budget `L * (b + 2)` bits for `L` labels of width `b`. -/
def generalWorkspaceBits (L b : ℕ) : ℕ := L * (b + 2)

/-- A recovery ledger assigning one query, macro, and measurement per sample, with sorting and
workspace budgets computed using `labelBits N`. -/
noncomputable def generalRecoveryLedger (N : ℕ) (samples : ℕ) : RecoveryLedger where
  samples := samples
  queries := samples
  macros := samples
  measurements := samples
  comparisons := generalSortCompareSteps samples
  bitOps := generalSortBitOps samples (labelBits N)
  integerBits := labelBits N
  workspaceBits := generalWorkspaceBits samples (labelBits N)

/-- The existence of a dihedral slope recovery distribution together with sample, sorting, bit
operation, and positive workspace conditions on `lg`. Under the reflection hiding promise,
the distribution gives zero mass to incorrect slopes and at least `ENNReal.ofReal p` to the
correct slope. -/
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

/-- The dihedral register base point `(0, false)` used in oracle collision searches. -/
def generalBasePoint (N : ℕ) : DihedralReg N := (0, false)

/-- The finite set of reflection registers whose oracle values equal the value at
`generalBasePoint N`, using the supplied equality decision on `S`. -/
noncomputable def generalPartnerSetWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Finset (DihedralReg N) := by
  letI : DecidableEq S := dec
  exact Finset.univ.filter fun q => f q = f (generalBasePoint N) ∧ q.2 = true

/-- The sum in `ZMod N` of the first coordinates of all registers in `generalPartnerSetWith dec
f`. -/
noncomputable def generalRecoveredSlopeWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ZMod N :=
  (generalPartnerSetWith dec f).sum fun q => q.1

/-- The point mass at the optional slope `some (generalRecoveredSlopeWith dec f)`. -/
noncomputable def generalRecoveryRunWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : PMF (Option (ZMod N)) :=
  PMF.pure (some (generalRecoveredSlopeWith dec f))

/-- The deterministic recovery distribution `generalRecoveryRunWith` using classical equality on
the oracle codomain. -/
noncomputable def generalRecoveryRun {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : PMF (Option (ZMod N)) :=
  generalRecoveryRunWith (Classical.decEq S) f

/-- The query count `2 * N` assigned to exhaustive dihedral recovery. -/
def generalRecoveryQueryCount (N : ℕ) : ℕ := 2 * N

/-- The comparison count `2 * N` assigned to exhaustive dihedral recovery. -/
def generalRecoveryCompareCount (N : ℕ) : ℕ := 2 * N

/-- The width `Nat.sqrt n + 1` used to construct cyclic difference basis candidates. -/
def zmodBasisWidth (n : ℕ) : ℕ := Nat.sqrt n + 1

/-- The subset of `ZMod n` formed by the residues of `0, …, m - 1` together with multiples `j *
m` for `j < n / m + 2`. -/
def zmodBasis {n : ℕ} [NeZero n] (m : ℕ) : Finset (ZMod n) :=
  (Finset.range m).image (fun i : ℕ => (i : ZMod n)) ∪
    (Finset.range (n / m + 2)).image (fun j : ℕ => ((j * m : ℕ) : ZMod n))

/-- The condition that every group element is a difference `d₂ - d₁` of two elements of the
finite set `D`. -/
def AbelianDifferenceBasis {A : Type} [AddCommGroup A] (D : Finset A) : Prop :=
  ∀ s : A, ∃ d₁ ∈ D, ∃ d₂ ∈ D, d₂ - d₁ = s

/-- The finite Cartesian product of the sets `D i` inside the product of the cyclic groups `ZMod
(n i)`. -/
noncomputable def productDifferenceBasis {ι : Type} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, NeZero (n i)) (D : ∀ i, Finset (ZMod (n i))) :
    Finset ((i : ι) → ZMod (n i)) := by
  classical
  exact (Finset.univ.filter fun x => ∀ i, x i ∈ D i)

/-- The subset of `A` whose image under the additive equivalence `e` lies in `D i` at every
coordinate `i`. -/
noncomputable def abelianDifferenceBasis {A : Type} [AddCommGroup A] [Fintype A] {ι : Type} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, NeZero (n i)) (D : ∀ i, Finset (ZMod (n i)))
    (e : A ≃+ ((i : ι) → ZMod (n i))) : Finset A := by
  classical
  exact (Finset.univ.filter fun x => ∀ i, (e x) i ∈ D i)

/-- The list of all ordered pairs from `D`, with the first coordinate as the outer enumeration
and repetitions retained. -/
def abelianPairs {A : Type} (D : List A) : List (A × A) :=
  D.flatMap fun d₁ => D.map fun d₂ => (d₁, d₂)

/-- The first pair in `abelianPairs D` satisfying `f p.1 = g p.2`, or `none` if no such pair is
found. -/
noncomputable def abelianShiftPair {A S : Type} [DecidableEq A] [DecidableEq S]
    (f g : A → S) (D : List A) : Option (A × A) :=
  (abelianPairs D).find? fun p => f p.1 = g p.2

/-- The difference `p.2 - p.1` associated with the first matching pair found by
`abelianShiftPair f g D`, when one exists. -/
noncomputable def abelianShiftCandidate {A S : Type} [AddCommGroup A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (D : List A) : Option A :=
  (abelianShiftPair f g D).map fun p => p.2 - p.1

/-- The point mass at the optional candidate produced by `abelianShiftCandidate f g D`. -/
noncomputable def abelianBasisShiftRun {A S : Type} [AddCommGroup A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (D : List A) : PMF (Option A) :=
  PMF.pure (abelianShiftCandidate f g D)

/-- The query budget `2 * D.length` for evaluating both hidden shift functions on `D`. -/
def abelianShiftQueryCount {A : Type} (D : List A) : ℕ := 2 * D.length

/-- The comparison budget `D.length ^ 2` for checking all ordered pairs from `D`. -/
def abelianShiftCompareCount {A : Type} (D : List A) : ℕ := (D.length) ^ 2

/-- The resource ledger for hidden shift collision search on `D`, with `2 * D.length` samples
and queries. Its comparison budget covers both all pairs and sorting, and its bit operation
and workspace budgets use the supplied label width. -/
noncomputable def abelianShiftLedger {A : Type} (D : List A) (bits : ℕ) : RecoveryLedger where
  samples := 2 * D.length
  queries := 2 * D.length
  macros := 2 * D.length
  measurements := 2 * D.length
  comparisons := max (D.length ^ 2) (sortCompareSteps (2 * D.length))
  bitOps := sortBitOps (2 * D.length) bits
  integerBits := bits
  workspaceBits := workspaceBits (max (2 * D.length) 1) bits

/-- The coordinate weight `Nat.log2 n + 2` used in the abelian splice level count. -/
def abelianSpliceCoordWeight (n : ℕ) : ℕ := Nat.log2 n + 2

/-- The sum of the splice coordinate weights `abelianSpliceCoordWeight (N j)` over `j : Fin a`. -/
def abelianSpliceLevels {a : ℕ} (N : Fin a → ℕ) : ℕ :=
  ∑ j : Fin a, abelianSpliceCoordWeight (N j)

/-- Reduced subgroup data for modulus `N`, consisting of a natural `period` parameter and an
optional natural slope representative. -/
structure ReducedSubgroupData (N : ℕ) : Type where

  period : ℕ

  slope : Option ℕ
  deriving DecidableEq

/-- The rotation period `N / H.period` associated with the dihedral subgroup data `H`. -/
def subgroupRotationPeriod {N : ℕ} (H : DihedralSubgroupData N) : ℕ := N / H.period

/-- The reduced data retaining `H.period` and replacing each optional slope by its natural
representative modulo `subgroupRotationPeriod H`. -/
def reduceSubgroupData {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    ReducedSubgroupData N where
  period := H.period
  slope := H.slope.map (fun s => s.val % subgroupRotationPeriod H)

/-- The condition that `d.period` divides `N` and every slope present in `d` is less than `N /
d.period`. -/
def ReducedSubgroupDataWellFormed {N : ℕ} (d : ReducedSubgroupData N) : Prop :=
  d.period ∣ N ∧ ∀ s, d.slope = some s → s < N / d.period

/-- The set containing the sentinel `N` and all positive `j < N` whose rotation oracle value
equals `f (0, false)`, using the supplied equality decision. -/
noncomputable def rotationPeriodCandidatesWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Finset ℕ := by
  letI := dec
  exact (Finset.range (N + 1)).filter fun j =>
    decide (j = N ∨ (1 ≤ j ∧ f (0, false) = f ((j : ℕ), false)))

/-- The rotation period candidate set computed with classical equality on the oracle codomain,
including the sentinel `N`. -/
noncomputable def rotationPeriodCandidates {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : Finset ℕ :=
  rotationPeriodCandidatesWith (Classical.decEq S) f

/-- The least element of `rotationPeriodCandidatesWith dec f`, whose sentinel `N` ensures that
the minimum exists. -/
noncomputable def rotationPeriodOfWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ℕ :=
  (rotationPeriodCandidatesWith dec f).min' ⟨N, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp⟩

/-- The least rotation period candidate, computed by `rotationPeriodOfWith` using classical
equality. -/
noncomputable def rotationPeriodOf {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : ℕ :=
  rotationPeriodOfWith (Classical.decEq S) f

/-- The set containing the sentinel `N` and all `b < N` satisfying `f (b, true) = f (0, false)`,
using the supplied equality decision. -/
noncomputable def reflectionPartnerCandidatesWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Finset ℕ := by
  letI := dec
  exact (Finset.range (N + 1)).filter fun b =>
    decide (b = N ∨ f (0, false) = f ((b : ℕ), true))

/-- The reflection partner candidate set computed with classical equality on the oracle
codomain, including the sentinel `N`. -/
noncomputable def reflectionPartnerCandidates {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : Finset ℕ :=
  reflectionPartnerCandidatesWith (Classical.decEq S) f

/-- The least element of `reflectionPartnerCandidatesWith dec f`, using `N` as a sentinel when
no smaller partner exists. -/
noncomputable def reflectionPartnerMinWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ℕ :=
  (reflectionPartnerCandidatesWith dec f).min' ⟨N, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp⟩

/-- The minimum reflection partner candidate computed with classical equality, with `N` as the
sentinel value. -/
noncomputable def reflectionPartnerMin {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : ℕ :=
  reflectionPartnerMinWith (Classical.decEq S) f

/-- The least reflection partner below `N`, returned as an option; the sentinel minimum `N` is
converted to `none`. -/
noncomputable def reflectionPartnerOfWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : Option ℕ :=
  if reflectionPartnerMinWith dec f = N then none else some (reflectionPartnerMinWith dec f)

/-- The optional least reflection partner obtained by `reflectionPartnerOfWith` using classical
equality. -/
noncomputable def reflectionPartnerOf {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : Option ℕ :=
  reflectionPartnerOfWith (Classical.decEq S) f

/-- The reduced subgroup candidate with period parameter `N / rotationPeriodOfWith dec f` and
optional reflection partner reduced modulo `rotationPeriodOfWith dec f`. -/
noncomputable def subgroupReductionAnswerWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : ReducedSubgroupData N where
  period := N / rotationPeriodOfWith dec f
  slope := (reflectionPartnerOfWith dec f).map (fun b => b % rotationPeriodOfWith dec f)

/-- The reduced subgroup candidate computed by `subgroupReductionAnswerWith` using classical
equality on the oracle codomain. -/
noncomputable def subgroupReductionAnswer {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : ReducedSubgroupData N :=
  subgroupReductionAnswerWith (Classical.decEq S) f

/-- The point mass at `some (subgroupReductionAnswerWith dec f)`, using the supplied equality
decision on oracle values. -/
noncomputable def subgroupReductionRunWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) : PMF (Option (ReducedSubgroupData N)) :=
  PMF.pure (some (subgroupReductionAnswerWith dec f))

/-- The deterministic subgroup reduction distribution obtained from `subgroupReductionRunWith`
using classical equality. -/
noncomputable def subgroupReductionRun {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) : PMF (Option (ReducedSubgroupData N)) :=
  subgroupReductionRunWith (Classical.decEq S) f

/-- The query count `2 * N + 1` assigned to subgroup reduction. -/
def subgroupReductionQueryCount (N : ℕ) : ℕ := 2 * N + 1

/-- The comparison count `2 * N` assigned to subgroup reduction. -/
def subgroupReductionCompareCount (N : ℕ) : ℕ := 2 * N

/-- The subgroup reduction ledger with `2 * N + 1` samples and queries, zero macros and
measurements, and sorting budgets at width `labelBits N`. Workspace is budgeted for `N + 1`
labels. -/
noncomputable def subgroupReductionLedger (N : ℕ) : RecoveryLedger where
  samples := subgroupReductionQueryCount N
  queries := subgroupReductionQueryCount N
  macros := 0
  measurements := 0
  comparisons := sortCompareSteps (subgroupReductionQueryCount N)
  bitOps := sortBitOps (subgroupReductionQueryCount N) (labelBits N)
  integerBits := labelBits N
  workspaceBits := workspaceBits (N + 1) (labelBits N)

/-- The existence of a reduced subgroup recovery distribution together with sample, sorting, bit
operation, and positive workspace conditions on `lg`. For an oracle hiding `H`, the
distribution is concentrated on `some (reduceSubgroupData H)` with probability one. -/
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

/-- The largest exponent `j ≤ k` for which `r ^ j` divides a nonzero label `k`, with value zero
assigned to `k = 0`. -/
def radixAlpha (r k : ℕ) : ℕ :=
  if k = 0 then 0 else Nat.findGreatest (fun j => r ^ j ∣ k) k

/-- The minimum `radixAlpha r k` among labels in `L`, with value zero for the empty list. -/
def radixMinAlpha (r : ℕ) (L : List ℕ) : ℕ :=
  match L with
  | [] => 0
  | k :: rest => rest.foldl (fun acc j => Nat.min acc (radixAlpha r j)) (radixAlpha r k)

/-- The sublist of labels attaining `radixMinAlpha r L`, preserving their order and
multiplicities. -/
def radixMinAlphaSublist (r : ℕ) (L : List ℕ) : List ℕ :=
  L.filter fun k => radixAlpha r k == radixMinAlpha r L

/-- The larger radix divisibility index of the natural labels `(k + ℓ) % N` and `(k + N - ℓ) %
N`. -/
def radixPairValue (r N : ℕ) (k ℓ : ℕ) : ℕ :=
  max (radixAlpha r ((k + ℓ) % N)) (radixAlpha r ((k + N - ℓ) % N))

/-- The list of ordered pairs from `L` whose label values are unequal, retaining repetitions
from the input list. -/
def radixPairs (L : List ℕ) : List (ℕ × ℕ) :=
  L.flatMap fun k => (L.filter fun l => l != k).map fun l => (k, l)

/-- The maximum `radixPairValue r N` over unequal pairs of labels attaining the minimum radix
index, with value zero when there are no such pairs. -/
noncomputable def radixGreedyValue (r N : ℕ) (L : List ℕ) : ℕ :=
  (radixPairs (radixMinAlphaSublist r L)).foldl
    (fun acc p => max acc (radixPairValue r N p.1 p.2)) 0

/-- An unequal pair from `radixMinAlphaSublist r L` maximizing `radixPairValue r N`, or `none`
if no such pair exists. Ties retain the first pair in the enumeration. -/
noncomputable def radixGreedyPair (r N : ℕ) (L : List ℕ) : Option (ℕ × ℕ) :=
  (radixPairs (radixMinAlphaSublist r L)).foldl
    (fun best p => match best with
      | none => some p
      | some q =>
          if radixPairValue r N p.1 p.2 > radixPairValue r N q.1 q.2 then some p else best)
    none

/-- The natural number deficit `(n - 1) - radixAlpha r k`, using truncated subtraction. -/
def radixBeta (r n k : ℕ) : ℕ := (n - 1) - radixAlpha r k

/-- The real potential `exp (-(log 3) * sqrt (2 * radixBeta r n k))` assigned to a label `k`. -/
noncomputable def radixValue (r n k : ℕ) : ℝ :=
  Real.exp (-(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)))

/-- The sum of the label potentials `radixValue r n` over `L`, counting multiplicities. -/
noncomputable def radixListValue (r n : ℕ) (L : List ℕ) : ℝ :=
  (L.map (radixValue r n)).sum

/-- The condition that `k` is nonzero and divisible by `r ^ (n - 1)`. -/
def radixFinalTest (r n k : ℕ) : Prop := r ^ (n - 1) ∣ k ∧ k ≠ 0

/-- The absolute difference of the natural labels `k` and `ℓ`, computed by subtracting the
smaller from the larger. -/
def radixDiff (k ℓ : ℕ) : ℕ := if k ≥ ℓ then k - ℓ else ℓ - k

/-- The condition that `r ^ (a + j)` divides the absolute difference of `k` and `ℓ`. -/
def radixTritsShare (r a k ℓ j : ℕ) : Prop := r ^ (a + j) ∣ radixDiff k ℓ

instance (r a k ℓ j : ℕ) : Decidable (radixTritsShare r a k ℓ j) :=
  inferInstanceAs (Decidable (r ^ (a + j) ∣ radixDiff k ℓ))

/-- The `Nat.findGreatest` search for an index `j` satisfying `radixTritsShare r (radixAlpha r
k) k ℓ j`, bounded by `radixDiff k ℓ`. -/
noncomputable def radixSharedTrits (r k ℓ : ℕ) : ℕ :=
  Nat.findGreatest (fun j => radixTritsShare r (radixAlpha r k) k ℓ j) (radixDiff k ℓ)

/-- The arithmetic mean of the potentials of `(k + ℓ) % (r ^ n)` and `(k + r ^ n - ℓ) % (r ^
n)`. -/
noncomputable def radixExpectedChildValue (r n : ℕ) (k ℓ : ℕ) : ℝ :=
  (radixValue r n ((k + ℓ) % (r ^ n)) + radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))) / 2

/-- The sum and difference labels `(k + ℓ, k - ℓ)` in `ZMod N`. -/
def radixQuantumChildren {N : ℕ} (k ℓ : ZMod N) : ZMod N × ZMod N :=
  (k + ℓ, k - ℓ)

/-- The distribution obtained by choosing a uniform Boolean branch and returning its flag
together with `k + ℓ` for `false` or `k - ℓ` for `true`. -/
noncomputable def radixQuantumExtractLaw {N : ℕ} [NeZero N] (k ℓ : ZMod N) :
    PMF (Bool × ZMod N) :=
  (PMF.uniformOfFintype' Bool).bind fun b => PMF.pure (b, if b then k - ℓ else k + ℓ)

/-- The block `(k / r ^ a) % r ^ (m + 1)` of radix digits starting at position `a`. -/
def radixQuotient (r a k m : ℕ) : ℕ := (k / r ^ a) % r ^ (m + 1)

/-- The remainder modulo `r` of `radixQuotient r a k m`, selecting its lowest radix digit. -/
def radixFirstDigit (r a k m : ℕ) : ℕ := radixQuotient r a k m % r

/-- The quotient of `radixQuotient r a k m` by `r`, discarding its lowest radix digit. -/
def radixUpperDigits (r a k m : ℕ) : ℕ := radixQuotient r a k m / r

/-- The pattern index `(d - 1, w)` when `d ≤ r - d`, and `(r - d - 1, r ^ m - 1 - w)` otherwise.
Here `d` and `w` are `radixFirstDigit r a k m` and `radixUpperDigits r a k m`, and all
subtraction is in the natural numbers. -/
def radixPatternIndex (r a k m : ℕ) : ℕ × ℕ :=
  let d := radixFirstDigit r a k m
  let w := radixUpperDigits r a k m
  if d ≤ r - d then (d - 1, w) else (r - d - 1, r ^ m - 1 - w)

/-- The condition that `M` divides either `k + ℓ` or the absolute difference of `k` and `ℓ`. -/
def radixSignAgree (M k ℓ : ℕ) : Prop := M ∣ k + ℓ ∨ M ∣ radixDiff k ℓ

/-- The digit `(k / r ^ (n - 1)) % r` used for radix shift readout. -/
def radixShiftReadout (r n k : ℕ) : ℕ := (k / r ^ (n - 1)) % r

/-- The sum of the label potentials `radixValue r n` over the list `L'` used to measure period
attrition. -/
noncomputable def radixPeriodAttrition (r n : ℕ) (L' : List ℕ) : ℝ :=
  (L'.map (radixValue r n)).sum

/-- The sublist of labels whose radix index differs from `radixMinAlpha r L`, preserving order
and multiplicities. -/
def radixKeptLabels (r : ℕ) (L : List ℕ) : List ℕ :=
  L.filter fun k => !(radixAlpha r k == radixMinAlpha r L)

/-- The label with larger radix index among `(k + ℓ) % N` and `(k + N - ℓ) % N`, choosing the
sum label when the indices are equal. -/
def radixGreedyChild (r N : ℕ) (k ℓ : ℕ) : ℕ :=
  if radixAlpha r ((k + ℓ) % N) < radixAlpha r ((k + N - ℓ) % N)
  then (k + N - ℓ) % N else (k + ℓ) % N

/-- The singleton list containing the greedy child of `radixGreedyPair r N L`, or the empty list
if no pair is selected. -/
noncomputable def radixPeriodChildren (r N : ℕ) (L : List ℕ) : List ℕ :=
  match radixGreedyPair r N L with
  | none => []
  | some (k, ℓ) => [radixGreedyChild r N k ℓ]

/-- One greedy sieve period, retaining `radixKeptLabels r L` and appending the selected child
list `radixPeriodChildren r N L`. -/
noncomputable def radixPeriodStep (r N : ℕ) (L : List ℕ) : List ℕ :=
  (radixKeptLabels r L) ++ (radixPeriodChildren r N L)

/-- The list obtained by iterating `radixPeriodStep r N` for the specified number of periods,
starting from the input labels. -/
noncomputable def radixSieveRun (r N : ℕ) : ℕ → List ℕ → List ℕ
  | 0, L => L
  | p + 1, L => radixPeriodStep r N (radixSieveRun r N p L)

/-- The total potential after one greedy sieve period with modulus `r ^ n`. -/
noncomputable def radixGreedyPeriodValue (r n : ℕ) (L : List ℕ) : ℝ :=
  radixListValue r n (radixPeriodStep r (r ^ n) L)

/-- The potential of the retained labels plus the mean potential of the two children of the
greedy pair. If no pair is selected, only the retained label potential is used. -/
noncomputable def radixQuantumPeriodValue (r n : ℕ) (L : List ℕ) : ℝ :=
  match radixGreedyPair r (r ^ n) L with
  | none => radixListValue r n (radixKeptLabels r L)
  | some (k, ℓ) =>
      radixListValue r n (radixKeptLabels r L) + radixExpectedChildValue r n k ℓ

/-- Conditions for a ternary sieve period: labels are distinct, nonzero, below `3 ^ n`, and no
two distinct labels sum to `3 ^ n`. The conditions also require a bounded sharing parameter
and a greedy pair whose score exceeds the minimum radix index. -/
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

/-- One sieve period retaining `radixKeptLabels r L` and, when a greedy pair exists, appending
its sum label for `false` or its natural subtraction label for `true`, reduced modulo `N`. -/
noncomputable def radixQuantumPeriodStep (r N : ℕ) (coin : Bool) (L : List ℕ) : List ℕ :=
  match radixGreedyPair r N L with
  | none => radixKeptLabels r L
  | some (k, ℓ) =>
      radixKeptLabels r L ++ [if coin then (k + N - ℓ) % N else (k + ℓ) % N]

/-- The sieve run driven by a Boolean list, applying one `radixQuantumPeriodStep` per coin until
the period budget or coin list is exhausted. -/
noncomputable def radixQuantumSieveRun (r N : ℕ) : List Bool → ℕ → List ℕ → List ℕ
  | [], _, L => L
  | _, 0, L => L
  | c :: cs, p + 1, L => radixQuantumSieveRun r N cs p (radixQuantumPeriodStep r N c L)

/-- The mean terminal potential after the specified number of periods, recursively averaging the
two Boolean branches of `radixQuantumPeriodStep r N` at each step. -/
noncomputable def radixQuantumRunValue (r n N : ℕ) : ℕ → List ℕ → ℝ
  | 0, L => radixListValue r n L
  | p + 1, L =>
      (radixQuantumRunValue r n N p (radixQuantumPeriodStep r N false L)
        + radixQuantumRunValue r n N p (radixQuantumPeriodStep r N true L)) / 2

/-- The recursive requirement that `RadixPeriodConditions n` hold at every nonterminal node of a
ternary sieve run, for both Boolean choices at each period. -/
noncomputable def RadixQuantumRunConditions (n : ℕ) : ℕ → List ℕ → Prop
  | 0, _ => True
  | p + 1, L =>
      RadixPeriodConditions n L ∧
        ∀ b : Bool, RadixQuantumRunConditions n p (radixQuantumPeriodStep 3 (3 ^ n) b L)

/-- The list of terminal label lists obtained by exploring both Boolean branches for the
specified number of periods, retaining repeated leaves. -/
noncomputable def radixQuantumLeaves (r N : ℕ) : ℕ → List ℕ → List (List ℕ)
  | 0, L => [L]
  | p + 1, L =>
      radixQuantumLeaves r N p (radixQuantumPeriodStep r N false L)
        ++ radixQuantumLeaves r N p (radixQuantumPeriodStep r N true L)

/-- The collision search width `Nat.sqrt N + 1` for modulus `N`. -/
def generalCollisionWidth (N : ℕ) : ℕ := Nat.sqrt N + 1

/-- The ordered list of residues of `0, …, m - 1` used as rotation labels in collision search
modulo `N`. -/
def generalCollisionRotations (N m : ℕ) : List (ZMod N) :=
  (List.range m).map fun i => (i : ZMod N)

/-- The ordered list of residues `j * m` for `j < N / m + 2` used as reflection labels in
collision search modulo `N`. -/
def generalCollisionReflections (N m : ℕ) : List (ZMod N) :=
  (List.range (N / m + 2)).map fun j => (j * m : ZMod N)

/-- The query budget given by the combined lengths of `generalCollisionRotations N m` and
`generalCollisionReflections N m`. -/
def generalCollisionQueryCount (N m : ℕ) : ℕ :=
  (generalCollisionRotations N m).length + (generalCollisionReflections N m).length

/-- The comparison budget given by the product of the rotation and reflection label list
lengths. -/
def generalCollisionCompareCount (N m : ℕ) : ℕ :=
  (generalCollisionRotations N m).length * (generalCollisionReflections N m).length

/-- The collision recovery ledger assigning one query, macro, and measurement per sampled label.
Its comparison budget is the maximum of the all-pairs and sorting budgets, with bit
operation and workspace budgets computed at width `labelBits N`. -/
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

/-- The first label `b` in `bs` satisfying `f (b, true) = f (a, false)`, or `none` when no match
is found, using the supplied equality decision. -/
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

/-- The first rotation label in `rots` having a matching reflection label in
`generalCollisionReflections N m`, paired with its first match. The result is `none` if the
search finds no collision. -/
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

/-- The optional difference `b - a` from the first collision found between
`generalCollisionRotations N m` and `generalCollisionReflections N m`. -/
noncomputable def generalCollisionSlopeWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (m : ℕ) : Option (ZMod N) :=
  match generalCollisionPair dec f m (generalCollisionRotations N m) with
  | some (a, b) => some (b - a)
  | none => none

/-- The point mass at the optional slope candidate returned by `generalCollisionSlopeWith dec f
m`. -/
noncomputable def generalCollisionRunWith {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (m : ℕ) : PMF (Option (ZMod N)) :=
  PMF.pure (generalCollisionSlopeWith dec f m)

/-- The deterministic collision recovery distribution obtained from `generalCollisionRunWith`
using classical equality on oracle values. -/
noncomputable def generalCollisionRun {N : ℕ} [NeZero N] {S : Type}
    (f : DihedralReg N → S) (m : ℕ) : PMF (Option (ZMod N)) :=
  generalCollisionRunWith (Classical.decEq S) f m

/-- The natural label `a * r ^ (n - 1)` used to represent a final radix state. -/
def radixFinalStateLabel (r n a : ℕ) : ℕ := a * r ^ (n - 1)

/-- The digit `(k / r ^ (n - 1)) % r` extracted from a final label. -/
def radixFinalIndex (r n k : ℕ) : ℕ := (k / r ^ (n - 1)) % r

/-- The phase index `((s * k) / r ^ (n - 1)) % r` computed from the natural slope and label. -/
def radixPhaseIndex (r n s k : ℕ) : ℕ := ((s * k) / r ^ (n - 1)) % r

/-- The complex phase `exp (2 * π * I * (t / r))`, with the quotient taken in the real numbers. -/
noncomputable def radixRootOfUnity (r t : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((t : ℝ) / (r : ℝ)) : ℝ) * Complex.I))

/-- The finite set of residues `u : ZMod r` satisfying `u * (a : ZMod r) = (t : ZMod r)`. -/
def radixShiftCandidates (r : ℕ) [NeZero r] (a t : ℕ) : Finset (ZMod r) :=
  Finset.univ.filter fun u => u * (a : ZMod r) == (t : ZMod r)

/-- The residue `(t : ZMod r) * (a : ZMod r)⁻¹` used for radix readout, using the inverse
operation of `ZMod r`. -/
def radixReadout (r : ℕ) [NeZero r] (a t : ℕ) : ZMod r :=
  (t : ZMod r) * (a : ZMod r)⁻¹

/-- The label marginal of `actualRecordFiniteLaw f`, obtained by retaining the `ZMod N`
coordinate of each finite record. -/
noncomputable def radixActualLabelLaw {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : PMF (ZMod N) :=
  (actualRecordFiniteLaw f).map (fun q : ZMod N × Bool × S => q.1)

/-- The law of a list of the specified number of independent samples from `radixActualLabelLaw
f`, recorded as natural representatives. -/
noncomputable def radixActualLabels {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : ℕ → PMF (List ℕ)
  | 0 => pure []
  | i + 1 =>
    (radixActualLabelLaw f).bind fun k =>
      (radixActualLabels f i).map fun L => k.val :: L

/-- The distribution obtained by applying `p` greedy radix sieve periods to `i` independently
sampled actual labels from `f`. -/
noncomputable def radixSieveTerminalLabels {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r i p : ℕ) :
    PMF (List ℕ) :=
  (radixActualLabels f i).map fun L => radixSieveRun r N p L

/-- The natural slope remaining after `j` successive divisions by `r`, starting from `s`. -/
def radixLevelSlope (r s j : ℕ) : ℕ :=
  match j with
  | 0 => s
  | j + 1 => radixLevelSlope r (s / r) j

/-- The residue in `ZMod r` of the least significant digit after `j` successive divisions of `s`
by `r`. -/
def radixLevelDigit (r s j : ℕ) : ZMod r :=
  match j with
  | 0 => ((s % r : ℕ) : ZMod r)
  | j + 1 => radixLevelDigit r (s / r) j

/-- The first `n` radix digits of `s` as residues in `ZMod r`, listed from least to most
significant by successive division by `r`. -/
def radixReadouts (r n s : ℕ) : List (ZMod r) :=
  match n with
  | 0 => []
  | Nat.succ n => radixLevelDigit r s 0 :: radixReadouts r n (s / r)

/-- The natural number reconstructed from radix readout residues with the least significant
digit first, recursively using `d.val + r * radixReadoutValue r rest`. -/
def radixReadoutValue (r : ℕ) : List (ZMod r) → ℕ
  | [] => 0
  | d :: rest => d.val + r * radixReadoutValue r rest

/-- The optional amplitude ratio `χ true / χ false`, returning `none` when the amplitude `χ
false` is zero. -/
noncomputable def radixBranchPhase (χ : QState Bool) : Option ℂ :=
  if h : χ false = 0 then none else some (χ true / χ false)

/-- The first residue `t` in the finite enumeration of `ZMod r` whose phase `radixRootOfUnity r
t.val` equals the amplitude ratio from `radixBranchPhase χ`. The result is `none` if that
ratio is undefined or no exact match is found. -/
noncomputable def radixTomographyIndex (r : ℕ) [NeZero r] (χ : QState Bool) : Option (ZMod r) :=
  match radixBranchPhase χ with
  | none => none
  | some w =>
      ((Finset.univ : Finset (ZMod r)).toList).find? fun t => decide (radixRootOfUnity r t.val = w)

/-- The distribution of lists of fresh label and qubit records from `f`, defined by
`actualFreshRecords N f`. -/
noncomputable def radixActualRecords {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : ℕ → PMF (List (ZMod N × NormQ)) :=
  actualFreshRecords N f

/-- The distribution obtained by projecting `i` fresh label and qubit records to natural labels
and applying `p` greedy radix sieve periods. -/
noncomputable def radixActualTerminalLabels {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r i p : ℕ) :
    PMF (List ℕ) :=
  (radixActualRecords f i).map fun (L : List (ZMod N × NormQ)) =>
    radixSieveRun r N p (L.map fun (rec : ZMod N × NormQ) => rec.1.val)

/-- The law of a list of independent samples from `dihedralActualRecord N f`, retaining only
each label and observed oracle value. -/
noncomputable def radixObservedRecords {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) : ℕ → PMF (List (ZMod N × S))
  | 0 => pure []
  | i + 1 =>
    (dihedralActualRecord N f).bind fun q =>
      (radixObservedRecords f i).map fun L => (q.1, q.2.1) :: L

/-- The first record in `L` whose label satisfies `radixFinalTest r n` and belongs to the
terminal label list `T`, or `none` if no such record exists. -/
noncomputable def radixFinalRecordBy {α : Type} [DecidableEq α]
    (r n : ℕ) (label : α → ℕ) (L : List α) (T : List ℕ) : Option α :=
  L.find? fun rec => decide (radixFinalTest r n (label rec) && decide (label rec ∈ T))

/-- The register map from modulus `N / r` to modulus `N` sending rotations to `(r * a.val,
false)` and reflections to `(r * a.val + b, true)`, with first coordinates cast to `ZMod N`. -/
def radixSubgroupEmbedding (r N : ℕ) (b : ℕ) :
    DihedralReg (N / r) → DihedralReg N
  | (a, false) => (((r * a.val : ℕ) : ZMod N), false)
  | (a, true) => (((r * a.val + b : ℕ) : ZMod N), true)

/-- The oracle on `DihedralReg (N / r)` obtained by precomposing `f` with
`radixSubgroupEmbedding r N b`. -/
def radixRestrictedOracle (r N : ℕ) (b : ℕ) {S : Type}
    (f : DihedralReg N → S) : DihedralReg (N / r) → S :=
  f ∘ radixSubgroupEmbedding r N b

/-- The residue modulo `N` represented by `r * t.val + b`, lifting a candidate from modulus `N /
r`. -/
def radixLift (r N : ℕ) (b : ℕ) (t : ZMod (N / r)) : ZMod N :=
  ((r * t.val + b : ℕ) : ZMod N)

/-- The register map from modulus `r ^ n` to modulus `r ^ (n + 1)` that scales the natural first
coordinate by `r` and adds `b` on the reflection branch. -/
def radixStepEmbedding (r n : ℕ) (b : ℕ) :
    DihedralReg (r ^ n) → DihedralReg (r ^ (n + 1))
  | (a, false) => (((r * a.val : ℕ) : ZMod (r ^ (n + 1))), false)
  | (a, true) => (((r * a.val + b : ℕ) : ZMod (r ^ (n + 1))), true)

/-- The oracle on `DihedralReg (r ^ n)` obtained by precomposing `f` with `radixStepEmbedding r
n b`. -/
def radixStepOracle {S : Type} (r n : ℕ) (b : ℕ)
    (f : DihedralReg (r ^ (n + 1)) → S) : DihedralReg (r ^ n) → S :=
  f ∘ radixStepEmbedding r n b

/-- The residue modulo `r ^ (n + 1)` represented by `r * t.val + b`, lifting a candidate from
modulus `r ^ n`. -/
def radixStepLift (r n : ℕ) (b : ℕ) (t : ZMod (r ^ n)) : ZMod (r ^ (n + 1)) :=
  ((r * t.val + b : ℕ) : ZMod (r ^ (n + 1)))

end Qatlib.Concepts.HspRecovery.OpenSieve
