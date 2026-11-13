/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord
import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralSummandExtraction
import Mathlib.Probability.Distributions.Uniform
import Mathlib.LinearAlgebra.Matrix.Rank
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieve
import Qatlib.Concepts.HspRecovery.Reduction.Reductions

/-!
# Dihedral representation records and recovery interfaces

`DihedralIrrep` and `IrrepFamily` encode unitary dihedral representations and a complete
dimension count. The module defines reflection fixed-space records, finite mass transport, and
probabilistic combination of records.

The `Nonabelian` namespace supplies sieve skeletons, bitwise descent procedures, resource
ledgers, and propositions specifying shift and subgroup recovery endpoints. See [Kuperberg2005]
for the mathematical background.

## Main statements

* `dimFixed`: rank of the reflection averaging operator.
* `StagedPmfBridge`: deterministic transport between successive probability laws.
* `shiftRecoveryRun`: iterative recovery of a binary shift candidate.
* `ShiftRecoveryEndpoint`: correctness and resource requirements for shift recovery.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

open Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Matrix
open scoped Classical

set_option autoImplicit false

/-- A pair of unitary matrices satisfying the dihedral relations, with scalar simultaneous
commutant. -/
structure DihedralIrrep (N : ℕ) where
  dim : ℕ
  rhoX : Matrix (Fin dim) (Fin dim) ℂ
  rhoY : Matrix (Fin dim) (Fin dim) ℂ
  unitaryX : rhoX ∈ Matrix.unitaryGroup (Fin dim) ℂ
  unitaryY : rhoY ∈ Matrix.unitaryGroup (Fin dim) ℂ
  orderX : rhoX ^ N = 1
  orderY : rhoY ^ 2 = 1
  relation : rhoY * rhoX * rhoY = rhoX.conjTranspose
  irreducible : ∀ M : Matrix (Fin dim) (Fin dim) ℂ,
    M * rhoX = rhoX * M → M * rhoY = rhoY * M → ∃ c : ℂ, M = c • 1

/-- The reflection matrix `rhoY * rhoX ^ s.val` associated with the slope `s`. -/
noncomputable def reflectionElem {N : ℕ} [NeZero N] (V : DihedralIrrep N) (s : ZMod N) :
    Matrix (Fin V.dim) (Fin V.dim) ℂ :=
  V.rhoY * V.rhoX ^ s.val

/-- The rank of the averaging matrix `(1 + reflectionElem V s) / 2`. -/
noncomputable def dimFixed {N : ℕ} [NeZero N] (V : DihedralIrrep N) (s : ZMod N) : ℕ :=
  Matrix.rank ((2 : ℂ)⁻¹ • ((1 : Matrix (Fin V.dim) (Fin V.dim) ℂ) + reflectionElem V s))

/-- A finite family of pairwise inequivalent dihedral representations whose squared dimensions
sum to `2 * N`. -/
structure IrrepFamily (N : ℕ) (Label : Type) [Fintype Label] [DecidableEq Label] where
  irrep : Label → DihedralIrrep N
  dimensionCount : (∑ l : Label, (irrep l).dim ^ 2) = 2 * N
  inequivalent : ∀ l₁ l₂ : Label, l₁ ≠ l₂ →
    ∀ M : Matrix (Fin (irrep l₁).dim) (Fin (irrep l₂).dim) ℂ,
      M * (irrep l₂).rhoX = (irrep l₁).rhoX * M →
        M * (irrep l₂).rhoY = (irrep l₁).rhoY * M → M = 0

/-- A representation label together with a row index in its reflection fixed space. -/
structure RepRecord (N : ℕ) (Label : Type) [Fintype Label] [DecidableEq Label]
    [NeZero N] (family : IrrepFamily N Label) (s : ZMod N) where
  label : Label
  row : Fin (dimFixed (family.irrep label) s)

/-- A real mass function is nonnegative at every point and has total mass one. -/
def IsPmfMass {α : Type} [Fintype α] (μ : α → ℝ) : Prop :=
  (∀ a : α, 0 ≤ μ a) ∧ (∑ a : α, μ a) = 1

/-- The mass at `b` obtained by summing `μ` over the fiber of `f` above `b`. -/
noncomputable def pushMass {α β : Type} [Fintype α] (f : α → β) (μ : α → ℝ) (b : β) : ℝ :=
  ∑ a : α, if f a = b then μ a else 0

/-- The joint record mass `V.dim / N`, independent of the row argument. -/
noncomputable def repJointMass {N : ℕ} [NeZero N] (V : DihedralIrrep N) (_row : ℕ) : ℝ :=
  (V.dim : ℝ) / N

/-- The representation label mass `V.dim * dimFixed V s / N`. -/
noncomputable def repLabelMass {N : ℕ} [NeZero N] (V : DihedralIrrep N) (s : ZMod N) : ℝ :=
  (V.dim : ℝ) * dimFixed V s * 2 / (2 * N)

/-- Two Boolean states differ by multiplication by a complex scalar of norm one. -/
def UpToPhase (ψ φ : QState Bool) : Prop := ∃ u : ℂ, ‖u‖ = 1 ∧ ψ = u • φ

/-- Successive probability laws connected by deterministic maps that push each law to the next. -/
structure StagedPmfBridge (α : ℕ → Type) (depth : ℕ) where
  law : (j : Fin (depth + 1)) → PMF (α j)
  step : (j : Fin depth) → α j.castSucc → α j.succ
  transport : ∀ j : Fin depth, law j.succ = (law j.castSucc).map (step j)

/-- Successive finite real mass functions connected by fiberwise pushforward identities. -/
structure StagedMassBridge (α : ℕ → Type) (depth : ℕ) [∀ j : ℕ, Fintype (α j)] where
  mass : (j : Fin (depth + 1)) → α j → ℝ
  step : (j : Fin depth) → α j.castSucc → α j.succ
  transport : ∀ (j : Fin depth) (b : α j.succ),
    mass j.succ b = pushMass (step j) (mass j.castSucc) b

/-- A modular label equipped with a natural number width. -/
structure HalfWidthRecord (N : ℕ) where
  label : ZMod N
  width : ℕ
  deriving DecidableEq

/-- The slope factor is at least one. -/
def LegalSlopeFactor (a : ℕ) : Prop := 1 ≤ a

/-- The natural number quotient `(w₁ + w₂) / a` used as the combined width. -/
def childWidth (w₁ w₂ a : ℕ) : ℕ := (w₁ + w₂) / a

/-- Combine two records by subtracting their labels and dividing the sum of their widths by `a`. -/
def combineRecords {N : ℕ} (a : ℕ) (r₁ r₂ : HalfWidthRecord N) : HalfWidthRecord N :=
  ⟨r₁.label - r₂.label, childWidth r₁.width r₂.width a⟩

/-- The label difference is divisible by `q` in `ZMod N`. -/
def windowAgreeMod (N q : ℕ) (k ℓ : ZMod N) : Prop := (q : ZMod N) ∣ (k - ℓ)

/-- Greedily pair list entries whose labels agree modulo the window factor, discarding unmatched
entries. -/
noncomputable def pairWindowMod {N : ℕ} (q : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod N) (L : List α) : List (α × α) := by
  match L with
  | [] => exact []
  | r :: rest =>
    match _h : rest.find? (fun r' => decide (windowAgreeMod N q (label r) (label r'))) with
    | none => exact pairWindowMod q label rest
    | some r' => exact (r, r') :: pairWindowMod q label (rest.erase r')
termination_by L.length
decreasing_by
  · simp
  · have hm : r' ∈ rest := List.mem_of_find?_eq_some _h
    have h1 := List.length_erase_add_one hm
    simp
    omega

/-- Independently retain each combined record with probability one half from a prescribed list
of pairs. -/
noncomputable def layerCombineLaw {N : ℕ} (a : ℕ) :
    List (HalfWidthRecord N × HalfWidthRecord N) → PMF (List (HalfWidthRecord N))
  | [] => pure []
  | (r₁, r₂) :: ps =>
    (PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (layerCombineLaw a ps).map fun tail =>
        if b = 1 then combineRecords a r₁ r₂ :: tail else tail

/-- Pair records by modular windows and apply the fair combination law to those pairs. -/
noncomputable def layerCombine {N : ℕ} (a q : ℕ) (L : List (HalfWidthRecord N)) :
    PMF (List (HalfWidthRecord N)) :=
  layerCombineLaw a (pairWindowMod (N := N) (q := q) HalfWidthRecord.label L)

/-- Iterate `layerCombine` for the specified number of layers, starting from the given record
list. -/
noncomputable def layeredCombine {N : ℕ} (a q : ℕ) :
    ℕ → List (HalfWidthRecord N) → PMF (List (HalfWidthRecord N))
  | 0, L => pure L
  | j + 1, L => (layeredCombine a q j L).bind (layerCombine a q)

/-- The law of a list of independent uniform modular labels, each carrying the fixed width `w`. -/
noncomputable def freshHalfWidthRecords (N : ℕ) [NeZero N] (w : ℕ) :
    ℕ → PMF (List (HalfWidthRecord N))
  | 0 => pure []
  | i + 1 =>
    (PMF.uniformOfFintype' (ZMod N)).bind fun k =>
      (freshHalfWidthRecords N w i).map fun L => ⟨k, w⟩ :: L

/-- A record has label `N / 2` when `N` is even, and label zero otherwise. -/
def isIdealHit (N : ℕ) (r : HalfWidthRecord N) : Prop :=
  r.label = if N % 2 = 0 then ((N / 2 : ℕ) : ZMod N) else (0 : ZMod N)

/-- The real expression `(1 - exp (-2 ^ (m / 3 - 2))) ^ m` used in sieve bounds. -/
noncomputable def idealHitLowerBound (m : ℕ) : ℝ :=
  (1 - Real.exp (-(2:ℝ) ^ ((m:ℝ) / 3 - 2))) ^ m

/-- The complement `1 - idealHitLowerBound m` of the designated sieve bound. -/
noncomputable def failureMass (m : ℕ) : ℝ := 1 - idealHitLowerBound m

/-- The fresh record budget `24 * 2 ^ (3 * m)`. -/
def sieveFreshRecordCount (m : ℕ) : ℕ := 24 * 2 ^ (3 * m)

/-- The query budget `48 * 2 ^ (3 * m) + 1`. -/
def sieveQueryLedger (m : ℕ) : ℕ := 48 * 2 ^ (3 * m) + 1

/-- Twice the fresh record budget for the sieve parameter `m`. -/
def sieveRecordCount (m : ℕ) : ℕ := 2 * sieveFreshRecordCount m

/-- The Born distribution of the dihedral joint record state, mapped to a label, Boolean flag,
and oracle value. -/
noncomputable def actualRecordFiniteLaw {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) :
    PMF (ZMod N × Bool × S) :=
  (bornDistribution (dihedralRecordJoint N f)
    (normalized_dihedralRecordJoint N f)).map
    (fun q => (q.1.1, q.1.2, q.2))

/-- The record type retaining the oracle value at stage zero, the flag at stage one, and only
the label thereafter. -/
def recordStages (N : ℕ) (S : Type) : ℕ → Type
  | 0 => ZMod N × Bool × S
  | 1 => ZMod N × Bool
  | _ => ZMod N

end Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian

open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open scoped Classical BigOperators ENNReal

/-- The bit obtained by dividing the canonical representative by `2 ^ (n - 1)` and reducing
modulo two. -/
def topBit (n : ℕ) (x : ZMod (2 ^ n)) : Fin 2 :=
  ⟨(x.val / 2 ^ (n - 1)) % 2, Nat.mod_lt _ (by decide : 0 < 2)⟩

/-- Nonempty pairwise disjoint supports of input bits, each equipped with an output offset bit. -/
structure TopBitBundle (R O : ℕ) : Type where

  sup : Fin O → Finset (Fin R)

  off : Fin O → Fin 2

  nonempty : ∀ i, (sup i).Nonempty

  disjoint : ∀ i j, i ≠ j → Disjoint (sup i) (sup j)

namespace TopBitBundle

/-- Evaluate each output as the sum of its supported input bits and its offset in `Fin 2`. -/
def apply {R O : ℕ} (B : TopBitBundle R O) (top : Fin R → Fin 2) : Fin O → Fin 2 :=
  fun i => (∑ j ∈ B.sup i, top j) + B.off i

end TopBitBundle

/-- Reconstruct a label modulo `2 ^ n` from a lower part and a top bit. -/
def skeletonLabel (n : ℕ) (low : ZMod (2 ^ (n - 1))) (t : Fin 2) : ZMod (2 ^ n) :=
  (((low.val + 2 ^ (n - 1) * t.val : ℕ)) : ZMod (2 ^ n))

/-- Use a fixed bit tape to retain label differences from the pairs formed at one sieve layer. -/
noncomputable def tapeLayer (n m j : ℕ) (tape : List (Fin 2)) (L : List (ZMod (2 ^ n))) :
    List (ZMod (2 ^ n)) :=
  ((sievePair n (sieveWindowWidth n m j) (m * j) L).zip tape).filterMap
    fun p => if p.2 = (1 : Fin 2) then some (p.1.2 - p.1.1) else none

/-- Run all sieve layers on reconstructed labels using fixed lower parts and fixed bit tapes. -/
noncomputable def sieveSkeleton (n m R : ℕ) (low : Fin R → ZMod (2 ^ (n - 1)))
    (tape : Fin m → List (Fin 2)) (top : Fin R → Fin 2) : List (ZMod (2 ^ n)) :=
  List.foldl (fun L j => tapeLayer n m j.val (tape j) L)
    (List.ofFn fun i : Fin R => skeletonLabel n (low i) (top i))
    (List.finRange m)

/-- For positive `n`, every fixed sieve skeleton expresses its output top bits through a
`TopBitBundle`. -/
def TopBitCoupling (n m R : ℕ) : Prop :=
  1 ≤ n →
    ∀ (low : Fin R → ZMod (2 ^ (n - 1))) (tape : Fin m → List (Fin 2)),
      ∃ (O : ℕ) (B : TopBitBundle R O),
        ∀ (top : Fin R → Fin 2),
          ((sieveSkeleton n m R low tape top).map (topBit n)) = List.ofFn (B.apply top)

/-- The mass of lists containing the target label bounds the mass of sufficiently long lists
times the designated fair-bit hit factor. -/
def TopBitFairness (n m : ℕ) : Prop :=
  (∑' L : List (ZMod (2 ^ n)),
      if (2 ^ m : ℕ) ≤ L.length
        then ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L
        else 0) *
      ENNReal.ofReal (1 - (2 : ℝ) ^ (-((2 ^ m : ℕ) : ℝ))) ≤
    ∑' L : List (ZMod (2 ^ n)),
      if ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ∈ L
        then ((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)) L
        else 0

/-- The ceiling of `sqrt (w - 1)` used as the sieve depth at width `w`. -/
noncomputable def descentDepth (w : ℕ) : ℕ := Nat.ceil (Real.sqrt ((w : ℝ) - 1))

/-- The triple of sample, macro, and measurement counts determined by the descent depth. -/
noncomputable def parityMacroLedger (w : ℕ) : ℕ × ℕ × ℕ :=
  let m := descentDepth w
  (24 * 2 ^ (3 * m), 48 * 2 ^ (3 * m) + 1, 48 * 2 ^ (3 * m) + 1)

/-- The stage sample count `24 * 2 ^ (3 * descentDepth w)`. -/
noncomputable def stageSamples (w : ℕ) : ℕ := 24 * 2 ^ (3 * descentDepth w)

/-- The prescribed stage hit bound, using the sieve expression for `w ≥ 2` and a fixed bound
otherwise. -/
noncomputable def stageHitBound (w : ℕ) : ℝ :=
  if 2 ≤ w then
    (1 - Real.exp (-(2 : ℝ) ^ ((descentDepth w : ℝ) / 3 - 2))) ^ descentDepth w -
      (2 : ℝ) ^ (-((2 ^ descentDepth w : ℕ) : ℝ))
  else 1 - (2 : ℝ) ^ (-(24 : ℝ))

/-- The remaining slope obtained by dividing the canonical representative of `s` by `2 ^ j`. -/
def descentSlope (n j : ℕ) (s : ZMod (2 ^ n)) : ZMod (2 ^ (n - j)) :=
  (((s.val / 2 ^ j : ℕ)) : ZMod (2 ^ (n - j)))

/-- Interpret a list of Boolean digits as a natural number with the least significant digit
first. -/
def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitValue bs

/-- Embed a smaller dihedral register by scaling its label and adding the recovered bit value on
the reflection branch. -/
def descentEmbedding (n : ℕ) (bs : List Bool) :
    DihedralReg (2 ^ (n - bs.length)) → DihedralReg (2 ^ n)
  | (a, flag) =>
    (((((2 ^ bs.length * a.val + (if flag then bitValue bs else 0) : ℕ))) :
      ZMod (2 ^ n)), flag)

/-- Interpret the recovered Boolean digits as a residue modulo `2 ^ n`. -/
def assembleCandidate (n : ℕ) (bs : List Bool) : ZMod (2 ^ n) :=
  ((((bitValue bs) % 2 ^ n : ℕ)) : ZMod (2 ^ n))

/-- Extend a successful partial bit list by one ideal sieve outcome, preserving failure as
`none`. -/
noncomputable def shiftStageStep (n : ℕ) (s : ZMod (2 ^ n))
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  st.bind fun o =>
    match o with
    | none => pure none
    | some bs =>
      (dihedralSieveRun (n - bs.length) (descentDepth (n - bs.length))
          (descentSlope n bs.length s)).1.bind fun o' =>
        match o' with
        | none => pure none
        | some b => pure (some (bs ++ [b]))

/-- Extend a successful partial bit list using the actual sieve on the oracle restricted along
the descent embedding. -/
noncomputable def actualShiftStageStep {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (n : ℕ) (f : DihedralReg (2 ^ n) → S)
    (st : PMF (Option (List Bool))) : PMF (Option (List Bool)) :=
  st.bind fun o =>
    match o with
    | none => pure none
    | some bs =>
      (dihedralSieveActual (n - bs.length) (descentDepth (n - bs.length))
          (f ∘ descentEmbedding n bs)).bind fun o' =>
        match o' with
        | none => pure none
        | some b => pure (some (bs ++ [b]))

/-- Iterate the ideal stage step `n` times and map the resulting bit list to a modular shift
candidate. -/
noncomputable def shiftRecoveryRun (n : ℕ) (s : ZMod (2 ^ n)) :
    PMF (Option (ZMod (2 ^ n))) :=
  let st : PMF (Option (List Bool)) :=
    (List.range n).foldl (fun acc _ => shiftStageStep n s acc)
      (pure (some ([] : List Bool)))
  PMF.map (Option.map (assembleCandidate n)) st

/-- Iterate the oracle-based stage step `n` times and assemble the resulting modular shift
candidate. -/
noncomputable def actualShiftRecoveryRun {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (n : ℕ) (f : DihedralReg (2 ^ n) → S) :
    PMF (Option (ZMod (2 ^ n))) :=
  let st : PMF (Option (List Bool)) :=
    (List.range n).foldl (fun acc _ => actualShiftStageStep n f acc)
      (pure (some ([] : List Bool)))
  PMF.map (Option.map (assembleCandidate n)) st

/-- Natural number budgets for sampling, queries, macros, measurements, comparisons, bit
operations, integer size, and workspace. -/
structure RecoveryLedger : Type where

  samples : ℕ

  queries : ℕ

  macros : ℕ

  measurements : ℕ

  comparisons : ℕ

  bitOps : ℕ

  integerBits : ℕ

  workspaceBits : ℕ

/-- The label size estimate `Nat.log2 N + 1`. -/
def labelBits (N : ℕ) : ℕ := Nat.log2 N + 1

/-- The sorting comparison estimate `L * (Nat.log2 (L + 1) + 1)`. -/
def sortCompareSteps (L : ℕ) : ℕ := L * (Nat.log2 (L + 1) + 1)

/-- The sorting comparison estimate multiplied by the bit width `b`. -/
def sortBitOps (L b : ℕ) : ℕ := sortCompareSteps L * b

/-- The workspace estimate `L * (b + 2)`. -/
def workspaceBits (L b : ℕ) : ℕ := L * (b + 2)

/-- The stage repetition count `1000 * (w + 1)`. -/
noncomputable def stageTrials (w : ℕ) : ℕ := 1000 * (w + 1)

/-- Aggregate stage budgets for binary descent, together with sorting and workspace estimates. -/
noncomputable def recoveryLedger (n : ℕ) : RecoveryLedger where
  samples := ∑ j ∈ Finset.range n, stageSamples (n - j)
  queries := ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).1
  macros := ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).2.1
  measurements := ∑ j ∈ Finset.range n, (parityMacroLedger (n - j)).2.2
  comparisons := sortCompareSteps (∑ j ∈ Finset.range n, stageSamples (n - j))
  bitOps := sortBitOps (∑ j ∈ Finset.range n, stageSamples (n - j)) (labelBits (2 ^ n))
  integerBits := labelBits (2 ^ n)
  workspaceBits := workspaceBits (stageSamples 1) (labelBits (2 ^ n))

/-- Aggregate stage budgets weighted by `stageTrials`, together with sorting and workspace
estimates. -/
noncomputable def amplifiedRecoveryLedger (n : ℕ) : RecoveryLedger where
  samples := ∑ j ∈ Finset.range n, stageTrials (n - j) * stageSamples (n - j)
  queries := ∑ j ∈ Finset.range n,
    stageTrials (n - j) * (parityMacroLedger (n - j)).1
  macros := ∑ j ∈ Finset.range n,
    stageTrials (n - j) * (parityMacroLedger (n - j)).2.1
  measurements := ∑ j ∈ Finset.range n,
    stageTrials (n - j) * (parityMacroLedger (n - j)).2.2
  comparisons := sortCompareSteps
    (∑ j ∈ Finset.range n, stageTrials (n - j) * stageSamples (n - j))
  bitOps := sortBitOps
    (∑ j ∈ Finset.range n, stageTrials (n - j) * stageSamples (n - j))
    (labelBits (2 ^ n))
  integerBits := labelBits (2 ^ n)
  workspaceBits := workspaceBits (stageSamples 1) (labelBits (2 ^ n))

/-- The existence of an oracle-dependent run that outputs only the hidden slope or failure, with
success at least `p` and the stated ledger inequalities. -/
def ShiftRecoveryEndpoint (N : ℕ) (p : ℝ) (lg : RecoveryLedger) : Prop :=
  ∃ run : (S : Type) → (DihedralReg N → S) → PMF (Option (ZMod N)),
    lg.samples ≤ lg.queries ∧
    sortCompareSteps lg.samples ≤ lg.comparisons ∧
    sortBitOps lg.samples lg.integerBits ≤ lg.bitOps ∧
    0 < lg.workspaceBits ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (s : ZMod N),
      DihedralReflectionHides N f s →
      (∀ u : ZMod N, u ≠ s → run S f (some u) = 0) ∧
        ENNReal.ofReal p ≤ run S f (some s)

/-- A radix at least two supports shift recovery with success at least two thirds and the
specified query and bit-operation bounds. -/
def RadixRecoveryEndpoint (r : ℕ) : Prop :=
  2 ≤ r ∧ ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∃ lg : RecoveryLedger,
      ShiftRecoveryEndpoint (r ^ n) (2 / 3) lg ∧
        ((lg.queries : ℝ) ≤ C * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ k) ∧
        ((lg.bitOps : ℝ) ≤
          C * (lg.queries : ℝ) * (Real.log ((lg.queries : ℝ) + 2)) ^ k)

/-- Finite abelian hidden shifts possess a recovery run with success at least two thirds, no
incorrect output, and the stated subexponential budgets. -/
def AbelianShiftRecoveryEndpoint : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (A : Type) [AddCommGroup A] [Fintype A],
    1 ≤ Fintype.card A →
    ∃ lg : RecoveryLedger,
      ((lg.queries : ℝ) ≤
        2 ^ (C * Real.sqrt (labelBits (Fintype.card A)))) ∧
      ((lg.bitOps : ℝ) ≤
        2 ^ (C * Real.sqrt (labelBits (Fintype.card A)))) ∧
      ∃ run : (S : Type) → (A → S) → (A → S) → PMF (Option A),
        ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
          (f g : A → S) (s : A),
          HiddenShift f g s →
          (∀ u : A, u ≠ s → run S f g (some u) = 0) ∧
            ENNReal.ofReal (2 / 3) ≤ run S f g (some s)

/-- A divisor of the modulus together with an optional reflection slope describing subgroup
data. -/
structure DihedralSubgroupData (N : ℕ) : Type where

  period : ℕ

  periodDvd : period ∣ N

  slope : Option (ZMod N)

/-- The subgroup data with period one and no reflection slope. -/
def trivialSubgroup (N : ℕ) : DihedralSubgroupData N where
  period := 1
  periodDvd := one_dvd N
  slope := none

/-- The orbit relation described by translation steps of size `N / H.period` and the optional
reflection slope. -/
def DihedralSubgroupOrbit (N : ℕ) (H : DihedralSubgroupData N) :
    DihedralReg N → DihedralReg N → Prop
  | (a, false), (b, false) =>
    ∃ k : ℕ, b = a + (((k * (N / H.period) : ℕ)) : ZMod N)
  | (a, false), (b, true) =>
    ∃ s : ZMod N, H.slope = some s ∧
      ∃ k : ℕ, b = a + s + (((k * (N / H.period) : ℕ)) : ZMod N)
  | (a, true), (b, true) =>
    ∃ k : ℕ, b = a + (((k * (N / H.period) : ℕ)) : ZMod N)
  | (a, true), (b, false) =>
    ∃ s : ZMod N, H.slope = some s ∧
      ∃ k : ℕ, b = a - s + (((k * (N / H.period) : ℕ)) : ZMod N)

/-- Oracle values agree exactly on pairs related by `DihedralSubgroupOrbit`. -/
def DihedralSubgroupHides {S : Type} [DecidableEq S] {N : ℕ}
    (f : DihedralReg N → S) (H : DihedralSubgroupData N) : Prop :=
  ∀ p q : DihedralReg N, f p = f q ↔ DihedralSubgroupOrbit N H p q

/-- The existence of a run concentrated on the designated subgroup answer, with success at least
two thirds and the stated ledger inequalities. -/
def SubgroupRecoveryEndpoint (N : ℕ) (lg : RecoveryLedger) : Prop :=
  ∃ run : (S : Type) → (DihedralReg N → S) → PMF (Option (DihedralSubgroupData N)),
    lg.samples ≤ lg.queries ∧
    sortCompareSteps lg.samples ≤ lg.comparisons ∧
    sortBitOps lg.samples lg.integerBits ≤ lg.bitOps ∧
    0 < lg.workspaceBits ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg N → S) (H : DihedralSubgroupData N),
      DihedralSubgroupHides f H →
      let ans : Option (DihedralSubgroupData N) :=
        if H = trivialSubgroup N then none else some H
      (∀ o : Option (DihedralSubgroupData N), o ≠ ans → run S f o = 0) ∧
        ENNReal.ofReal (2 / 3) ≤ run S f ans

end Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
