/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

/-!
# Local fermionic gates and covariance data

This module defines local gate words for Jordan-Wigner operators, quadratic generators, and
Hubbard terms. `localGateListOp` and `localGateSumOp` interpret these words as register
matrices, following the fermionic encoding of [JordanWigner1928].

It also supplies Majorana index maps, local covariance blocks, and resource counters used in
fermionic circuit calculations. `covarianceUpdate` replaces only the selected local block;
`frameRotation` embeds a local rotation into the full Majorana frame. The covariance formalism
is described in [Bravyi2005Fermionic].

## Main definitions

* `jwLocalGateList`: the parity prefix followed by the local lowering matrix.
* `hubbardHamiltonianWord`: a weighted gate-word expansion of the Hubbard terms.
* `localRotation`: the exponential of twice the local real skew-symmetric form.

## References

* [Jordan and Wigner, 1928][JordanWigner1928]
* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix
open scoped BigOperators
open scoped Matrix
open Qatlib
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

/-- Embeds the one-qubit matrix `G` at site `j`, with identity action on all other register
bits. -/
noncomputable def localGate {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x =>
    if ∀ k : Fin n, k ≠ j → y k = x k then G (boolEquivFin2 (y j)) (boolEquivFin2 (x j))
    else 0

/-- The one-qubit Pauli Z matrix, with diagonal entries 1 and -1. -/
noncomputable def oneQubitZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then (if c = 1 then -1 else 1) else 0

/-- The identity matrix on the one-qubit computational basis. -/
noncomputable def oneQubitI : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then 1 else 0

/-- The diagonal one-qubit matrix with entries 1 and `Complex.exp (-Complex.I * θ)`. -/
noncomputable def oneQubitPhase (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then (if c = 1 then Complex.exp (-Complex.I * θ) else 1) else 0

/-- A list of register sites paired with one-qubit matrices. -/
abbrev LocalGateList (n : ℕ) := List (Fin n × Matrix (Fin 2) (Fin 2) ℂ)

/-- Interprets a local gate list as the matrix product in list order, with the empty list
interpreted as the identity. -/
noncomputable def localGateListOp {n : ℕ} : LocalGateList n → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | (j, G) :: rest => localGate j G * localGateListOp rest

/-- Counts the entries in a local gate list. -/
def localGateCount {n : ℕ} : LocalGateList n → ℕ
  | [] => 0
  | _ :: rest => 1 + localGateCount rest

/-- The site-address width, equal to 1 for `n ≤ 1` and to `Nat.log2 n + 1` otherwise. -/
def modeAddressBits (n : ℕ) : ℕ := if n ≤ 1 then 1 else Nat.log2 n + 1

/-- The number of local gates multiplied by the site-address width. -/
def localGateBitCost {n : ℕ} (gl : LocalGateList n) : ℕ :=
  localGateCount gl * modeAddressBits n

/-- Assigns the register width `n` as the space cost of a local gate list. -/
def localGateSpaceCost {n : ℕ} (_gl : LocalGateList n) : ℕ := n

/-- A nonempty local gate list has strictly positive gate count. -/
theorem localGateCount_pos {n : ℕ} (gl : LocalGateList n) :
    gl ≠ [] → 0 < localGateCount gl := by
  cases gl with
  | nil => simp
  | cons g rest =>
      intro h
      simp [localGateCount]

/-- The site factor of a Jordan-Wigner annihilation word: Pauli Z before `i`, the lowering
matrix at `i`, and identity after `i`. -/
noncomputable def jwSiteFactor {n : ℕ} (i j : Fin n) (y x : Reg n) : ℂ :=
  if j < i then (if y j = x j then (if x j then -1 else 1 : ℂ) else 0)
  else if i < j then (if y j = x j then 1 else 0)
  else sigmaMinus (boolEquivFin2 (y j)) (boolEquivFin2 (x j))

/-- Each matrix entry of the Jordan-Wigner word is the product of its site factors. -/
theorem jwPauliWord_eq_siteFactors {n : ℕ} (i : Fin n) (y x : Reg n) :
    jwPauliWord i y x = ∏ j : Fin n, jwSiteFactor i j y x := by
  rfl

/-- A Jordan-Wigner word has zero matrix entry whenever the input and output differ at a site
other than `i`. -/
theorem jwPauliWord_local {n : ℕ} (i : Fin n) (y x : Reg n)
    (hk : ∃ k : Fin n, k ≠ i ∧ y k ≠ x k) : jwPauliWord i y x = 0 := by
  rw [jwPauliWord_eq_siteFactors]
  obtain ⟨k, hki, hkx⟩ := hk
  have hk0 : jwSiteFactor i k y x = 0 := by
    unfold jwSiteFactor
    by_cases hlt : k < i
    · rw [if_pos hlt, if_neg hkx]
    · have hilt : i < k := by omega
      rw [if_neg hlt, if_pos hilt, if_neg hkx]
  calc (∏ j : Fin n, jwSiteFactor i j y x)
      = (∏ j ∈ (Finset.univ : Finset (Fin n)).erase k, jwSiteFactor i j y x)
          * jwSiteFactor i k y x := by
        exact (Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
          (fun j => jwSiteFactor i j y x) (Finset.mem_univ k)).symm
    _ = 0 := by rw [hk0]; simp

/-- The prefix length `i.val + 1` is bounded by the register width. -/
theorem jwPauliWord_gateCount {n : ℕ} (i : Fin n) :
    (i.val + 1) ≤ n := by omega

/-- The diagonal entry of a local gate at the bit selected by the register configuration. -/
def localGateDiagEntry {n : ℕ} (p : Fin n × Matrix (Fin 2) (Fin 2) ℂ) (y : Reg n) : ℂ :=
  p.2 (boolEquivFin2 (y p.1)) (boolEquivFin2 (y p.1))

/-- The list of Pauli Z gates at all sites strictly before `i`. -/
def jwZPrefix {n : ℕ} (i : Fin n) : LocalGateList n :=
  ((Finset.univ : Finset (Fin n)).filter (· < i)).toList.map (fun j => (j, oneQubitZ))

/-- The Jordan-Wigner annihilation gate word, consisting of the Z prefix followed by the
lowering matrix at `i`. -/
def jwLocalGateList {n : ℕ} (i : Fin n) : LocalGateList n :=
  jwZPrefix i ++ [(i, sigmaMinus)]

/-- Every matrix appearing in a Jordan-Wigner Z prefix is `oneQubitZ`. -/
theorem jwZPrefix_mem {n : ℕ} (i : Fin n) {p : Fin n × Matrix (Fin 2) (Fin 2) ℂ}
    (hp : p ∈ jwZPrefix i) : p.2 = oneQubitZ := by
  unfold jwZPrefix at hp
  rw [List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  rfl

/-- The number operator entry is 1 exactly when the configurations agree and mode `i` is
occupied, and is 0 otherwise. -/
theorem numberOp_apply {n : ℕ} (i : Fin n) (y x : Reg n) :
    numberOp i y x = if x = y ∧ x i then 1 else 0 := rfl

/-- Off-diagonal matrix entries of the number operator vanish. -/
theorem numberOp_diagonal {n : ℕ} (i : Fin n) (y x : Reg n) (h : y ≠ x) :
    numberOp i y x = 0 := by
  rw [numberOp_apply]
  split <;> simp_all

/-- The one-qubit phase gate embedded at site `i`. -/
noncomputable def onsiteLocalGate {n : ℕ} (i : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  localGate i (oneQubitPhase θ)

/-- The raising matrix `(pauliX - Complex.I • pauliY) / 2`. -/
noncomputable def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliX - Complex.I • pauliY)

/-- The one-qubit occupation projector with diagonal entries 0 and 1. -/
noncomputable def oneQubitNumber : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then (if c = 1 then 1 else 0) else 0

/-- The product of local Pauli Z gates over the finite set `S`. -/
def zSetOperator {n : ℕ} (S : Finset (Fin n)) : Matrix (Reg n) (Reg n) ℂ :=
  localGateListOp ((S.toList).map (fun k => (k, oneQubitZ)))

/-- The set of sites in the half-open interval from `i` to `j`. -/
def zRangeSet {n : ℕ} (i j : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j)

/-- The list of local Pauli Z gates on `zRangeSet i j`. -/
def zRangeGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  (zRangeSet i j).toList.map (fun k => (k, oneQubitZ))

/-- The set of sites strictly between `i` and `j`. -/
def zTailSet {n : ℕ} (i j : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => i < k ∧ k < j)

/-- The list of local Pauli Z gates at sites strictly between `i` and `j`. -/
def zTailGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  (zTailSet i j).toList.map (fun k => (k, oneQubitZ))

/-- Embeds the matrix `B` on the ordered pair of sites `i`, `j`, requiring all other register
bits to agree. -/
noncomputable def twoSiteGate {n : ℕ} (i j : Fin n)
    (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x =>
    if ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k then
      B (boolEquivFin2 (y i), boolEquivFin2 (y j)) (boolEquivFin2 (x i), boolEquivFin2 (x j))
    else 0

/-- The Jordan-Wigner creation word, with a raising matrix at `i` followed by its Z prefix. -/
def jwCreationGateList {n : ℕ} (i : Fin n) : LocalGateList n :=
  [(i, sigmaPlus)] ++ jwZPrefix i

/-- The singleton gate list containing the occupation projector at site `i`. -/
def numberGateList {n : ℕ} (i : Fin n) : LocalGateList n :=
  [(i, oneQubitNumber)]

/-- The gate word with a raising matrix at `i`, the Z string on `[i, j)`, and a lowering matrix
at `j`. -/
def hopForwardGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  [(i, sigmaPlus)] ++ zRangeGateList i j ++ [(j, sigmaMinus)]

/-- The gate word with a raising matrix at `j`, the Z string on `[i, j)`, and a lowering matrix
at `i`. -/
def hopBackwardGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  [(j, sigmaPlus)] ++ zRangeGateList i j ++ [(i, sigmaMinus)]

/-- Data for a quadratic two-mode term: ordered sites `i < j` and a complex two-by-two
coefficient matrix. -/
structure QuadraticTerm (n : ℕ) where

  i : Fin n

  j : Fin n

  hij : i < j

  A : Matrix (Fin 2) (Fin 2) ℂ

/-- A list of complex coefficients paired with local gate words. -/
abbrev LocalGateSum (n : ℕ) := List (ℂ × LocalGateList n)

/-- Interprets a weighted list of gate words as the sum of their coefficient-scaled operators. -/
noncomputable def localGateSumOp {n : ℕ} : LocalGateSum n → Matrix (Reg n) (Reg n) ℂ
  | [] => 0
  | (c, gl) :: rest => c • localGateListOp gl + localGateSumOp rest

/-- The sum of the local gate counts over all words in a weighted gate sum. -/
def localGateSumCount {n : ℕ} : LocalGateSum n → ℕ
  | [] => 0
  | (_, gl) :: rest => localGateCount gl + localGateSumCount rest

/-- The sum of the bit costs of the words in a weighted gate sum. -/
def localGateSumBitCost {n : ℕ} : LocalGateSum n → ℕ
  | [] => 0
  | (_, gl) :: rest => localGateBitCost gl + localGateSumBitCost rest

/-- The recursive maximum of the register widths assigned to the terms, with cost 0 for an empty
sum. -/
def localGateSumSpaceCost {n : ℕ} : LocalGateSum n → ℕ
  | [] => 0
  | (_, gl) :: rest => max n (localGateSumSpaceCost rest)

/-- The finite set of ordered mode pairs whose first index is strictly smaller than the second. -/
def modePairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- The list obtained from the finite set `modePairs n`. -/
def modePairList (n : ℕ) : List (Fin n × Fin n) := (modePairs n).toList

/-- The two-site matrix with entries given by the raising matrix on the first site and the
lowering matrix on the second. -/
noncomputable def hopForwardBlock : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => sigmaPlus a.1 c.1 * sigmaMinus a.2 c.2

/-- The two-site matrix with entries given by the lowering matrix on the first site and the
raising matrix on the second. -/
noncomputable def hopBackwardBlock : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => sigmaMinus a.1 c.1 * sigmaPlus a.2 c.2

/-- The diagonal two-site occupation projector for the first site. -/
noncomputable def numberBlockI : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => if a = c then (if a.1 = 1 then 1 else 0) else 0

/-- The diagonal two-site occupation projector for the second site. -/
noncomputable def numberBlockJ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => if a = c then (if a.2 = 1 then 1 else 0) else 0

/-- The two-site generator formed from the entries of `A` multiplying the two occupation blocks
and the two hopping blocks. -/
noncomputable def generatorBlock (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => A 0 0 * numberBlockI a c + A 0 1 * hopForwardBlock a c
    + A 1 0 * hopBackwardBlock a c + A 1 1 * numberBlockJ a c

/-- Extracts the bits at `i` and `j` as an ordered pair in `Fin 2 × Fin 2`. -/
def twoSiteBits {n : ℕ} (i j : Fin n) (y : Reg n) : Fin 2 × Fin 2 :=
  (boolEquivFin2 (y i), boolEquivFin2 (y j))

/-- Replaces the bits at `i` and `j` by the supplied pair, giving the update at `i` priority if
the sites coincide. -/
def twoSiteExtend {n : ℕ} (i j : Fin n) (y : Reg n) (w : Fin 2 × Fin 2) : Reg n :=
  fun k => if k = i then boolEquivFin2.symm w.1
    else if k = j then boolEquivFin2.symm w.2 else y k

/-- The weighted gate word representing `μ` times the occupation projector at `i`. -/
def hubbardOnsiteWord {n : ℕ} (μ : ℂ) (i : Fin n) : LocalGateSum n :=
  [(μ, numberGateList i)]

/-- The weighted product of the occupation projectors at `i` and `j`, with coefficient `U`. -/
def hubbardInteractionWord {n : ℕ} (U : ℂ) (i j : Fin n) : LocalGateSum n :=
  [(U, numberGateList i ++ numberGateList j)]

/-- The sum of the forward and backward hopping words, each with coefficient `t`. -/
def hubbardHoppingWord {n : ℕ} (t : ℂ) (i j : Fin n) : LocalGateSum n :=
  [(t, hopForwardGateList i j), (t, hopBackwardGateList i j)]

/-- Concatenates the onsite, interaction, and hopping gate words over the modes and pairs used
by the Hubbard model. -/
def hubbardHamiltonianWord {n : ℕ} (t μ U : ℂ) : LocalGateSum n :=
  (List.finRange n).flatMap (fun i => hubbardOnsiteWord μ i)
    ++ (fermionPairs n).flatMap (fun p => hubbardInteractionWord U p.1 p.2)
    ++ (fermionPairs n).flatMap (fun p => hubbardHoppingWord t p.1 p.2)

/-- The coefficient-weighted matrix sum of the list `hubbardJWTerms t μ U`. -/
noncomputable def hubbardTermSum {n : ℕ} (t μ U : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (hubbardJWTerms t μ U).foldr (fun p acc => p.1 • p.2 + acc) 0

/-- The sum of `μ` times the number operator over all modes. -/
noncomputable def hubbardOnsiteSum {n : ℕ} (μ : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (List.finRange n).foldr (fun i acc => μ • numberOp i + acc) 0

/-- The sum of `U` times the product of the two number operators over `fermionPairs n`. -/
noncomputable def hubbardInteractionSum {n : ℕ} (U : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (fermionPairs n).foldr (fun p acc => U • (numberOp p.1 * numberOp p.2) + acc) 0

/-- The sum of the forward and reverse creation-annihilation products over `fermionPairs n`,
each scaled by `t`. -/
noncomputable def hubbardHoppingSum {n : ℕ} (t : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (fermionPairs n).foldr
    (fun p acc => t • (creation p.1 * annihilation p.2 + creation p.2 * annihilation p.1) + acc) 0

/-- A one-body term specified by a mode and a complex coefficient. -/
structure OneBodyTerm (n : ℕ) where

  i : Fin n

  h : ℂ

/-- The weighted singleton occupation word associated with a one-body term. -/
def oneBodyWord {n : ℕ} (t : OneBodyTerm n) : LocalGateSum n :=
  [(t.h, numberGateList t.i)]

/-- Every gate matrix in the occupation word of a one-body term is `oneQubitNumber`. -/
theorem oneBodyWord_mem {n : ℕ} (t : OneBodyTerm n) {p : Fin n × Matrix (Fin 2) (Fin 2) ℂ}
    (hp : p ∈ numberGateList t.i) : p.2 = oneQubitNumber := by
  simp only [numberGateList, List.mem_singleton] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

/-- A list of pairs of mode indices equipped with complex two-by-two generator matrices. -/
abbrev MatchGateCircuit (n : ℕ) := List (Fin n × Fin n × Matrix (Fin 2) (Fin 2) ℂ)

/-- Interprets a matchgate circuit as its matrix product in list order, with the empty circuit
interpreted as the identity. -/
noncomputable def matchGateCircuitOp {n : ℕ} : MatchGateCircuit n → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | (i, j, A) :: rest => matchGate i j A * matchGateCircuitOp rest

/-- Counts the gates in a matchgate circuit. -/
def matchGateCount {n : ℕ} : MatchGateCircuit n → ℕ
  | [] => 0
  | _ :: rest => 1 + matchGateCount rest

/-- The matchgate count equals the length of the circuit list. -/
theorem matchGateCount_eq_length {n : ℕ} (gl : MatchGateCircuit n) :
    matchGateCount gl = gl.length := by
  induction gl with
  | nil => rfl
  | cons e rest ih => simp [matchGateCount, ih, Nat.add_comm]

/-- The assigned classical operation count of one matchgate, equal to 64. -/
def matchGateClassicalOps : ℕ := 64

/-- The gate count multiplied by the assigned classical cost of one matchgate. -/
def matchGateCircuitClassicalOps {n : ℕ} (gl : MatchGateCircuit n) : ℕ :=
  matchGateCount gl * matchGateClassicalOps

/-- The assigned classical cost of a matchgate circuit is at most 64 times its gate count. -/
theorem matchGateCircuitClassicalOps_le {n : ℕ} (gl : MatchGateCircuit n) :
    matchGateCircuitClassicalOps gl ≤ 64 * matchGateCount gl := by
  simp only [matchGateCircuitClassicalOps, matchGateClassicalOps]
  omega

/-- Encodes a mode `k` and a binary label `b` as the Majorana index `2 * k.val + b.val`. -/
def majoranaIndices {n : ℕ} (k : Fin n) (b : Fin 2) : Fin (2 * n) :=
  ⟨2 * k.val + b.val, by omega⟩

/-- The predicate that a Majorana index belongs to one of the two modes `i` and `j`. -/
def isLocalMajorana {n : ℕ} (i j : Fin n) (c : Fin (2 * n)) : Prop :=
  c = majoranaIndices i 0 ∨ c = majoranaIndices i 1
    ∨ c = majoranaIndices j 0 ∨ c = majoranaIndices j 1

instance isLocalMajoranaDecidable {n : ℕ} (i j : Fin n) (c : Fin (2 * n)) :
    Decidable (isLocalMajorana i j c) := by
  unfold isLocalMajorana
  infer_instance

/-- Distinct binary labels at the same mode give distinct Majorana indices. -/
theorem majoranaIndices_ne {n : ℕ} (i : Fin n) (b c : Fin 2) (hbc : b ≠ c) :
    majoranaIndices i b ≠ majoranaIndices i c := by
  intro h
  apply hbc
  apply Fin.ext
  simp only [majoranaIndices, Fin.mk.injEq] at h ⊢
  omega

/-- Two encoded Majorana indices agree exactly when both their mode indices and binary labels
agree. -/
theorem majoranaIndices_eq {n : ℕ} (i j : Fin n) (b c : Fin 2) :
    majoranaIndices i b = majoranaIndices j c ↔ i = j ∧ b = c := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [majoranaIndices, Fin.mk.injEq] at hv
    have hbc : b.val = c.val := by omega
    have hij : i.val = j.val := by omega
    exact ⟨Fin.ext hij, Fin.ext hbc⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Lists the two Majorana indices of `i` followed by the two Majorana indices of `j`. -/
def localIndices {n : ℕ} (i j : Fin n) (p : Fin 4) : Fin (2 * n) :=
  match p.val with
  | 0 => majoranaIndices i 0
  | 1 => majoranaIndices i 1
  | 2 => majoranaIndices j 0
  | _ => majoranaIndices j 1

/-- Selects a local slot by testing the Majorana indices of `i` and `j`, with slot 3 as the
default. -/
def localSlot {n : ℕ} (i j : Fin n) (a : Fin (2 * n)) : Fin 4 :=
  if a = majoranaIndices i 0 then 0
  else if a = majoranaIndices j 0 then 2
  else if a = majoranaIndices i 1 then 1
  else 3

/-- Extracts the four-by-four submatrix at the Majorana indices of `i` and `j`. -/
noncomputable def localBlock {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q => Γ (localIndices i j p) (localIndices i j q)

/-- Replaces entries with two local indices by those of `R * localBlock Γ i j * R.transpose`,
and retains every other entry. -/
noncomputable def covarianceUpdate {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := by
  classical
  exact Matrix.of fun a b =>
    if isLocalMajorana i j a ∧ isLocalMajorana i j b then
      (R * localBlock Γ i j * R.transpose) (localSlot i j a) (localSlot i j b)
    else Γ a b

/-- The local-block covariance update preserves an entry whose two indices are outside the
selected modes. -/
theorem covarianceUpdate_eq_of_not_local {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin (2 * n))
    (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b) :
    covarianceUpdate Γ i j R a b = Γ a b := by
  unfold covarianceUpdate
  simp [ha, hb]

/-- The linear combination of Majorana operators specified by row `a` of the real matrix `S`. -/
noncomputable def majoranaInBasis {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ c : Fin (2 * n), (S a c : ℂ) • majorana c

/-- The difference of the traces of `Mᴴ * (X * Y) * M` and `Mᴴ * (Y * X) * M`. -/
noncomputable def covarianceComplexOf {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (X Y : Matrix (Reg n) (Reg n) ℂ) : ℂ :=
  Matrix.trace (Mᴴ * (X * Y) * M) - Matrix.trace (Mᴴ * (Y * X) * M)

/-- Minus one half of the imaginary part of the trace commutator `covarianceComplexOf M X Y`. -/
noncomputable def covarianceOf {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (X Y : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  -(1 / 2 : ℝ) * (covarianceComplexOf M X Y).im

/-- The matrix of `covarianceOf` evaluated on the Majorana combinations determined by `S`. -/
noncomputable def covarianceInBasis {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b => covarianceOf M (majoranaInBasis S a) (majoranaInBasis S b)

/-- The linear combination of the four selected Majorana operators specified by row `p` of `R`. -/
noncomputable def localMajoranaInBasis {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 4) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ s : Fin 4, (R p s : ℂ) • majorana (localIndices i j s)

/-- The four-by-four covariance matrix of the selected Majorana combinations determined by `R`. -/
noncomputable def localCovarianceInBasis {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q => covarianceOf M (localMajoranaInBasis i j R p) (localMajoranaInBasis i j R q)

/-- The occupation expression `(1 - Γ (majoranaIndices k 0) (majoranaIndices k 1)) / 2`. -/
def occupationFromCovariance {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (k : Fin n) : ℝ :=
  (1 - Γ (majoranaIndices k 0) (majoranaIndices k 1)) / 2

/-- The real part of the trace of the number operator sandwiched between `Mᴴ` and `M`. -/
noncomputable def occupationExpectation {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) : ℝ :=
  (Matrix.trace (Mᴴ * (numberOp k) * M)).re

/-- The assigned classical cost of reading one occupation value, equal to 1. -/
def occupationClassicalCost {n : ℕ} (_k : Fin n) : ℕ := 1

/-- The assigned physical measurement cost `2 ^ n` for a register of width `n`. -/
def physicalMeasurementCost (n : ℕ) : ℕ := 2 ^ n

/-- The list of successive mode pairs along a line. -/
def linearConnectivity (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).zip (List.finRange n).tail

/-- The linear connectivity with the last-to-first edge appended when `n` is positive, and the
empty list when `n = 0`. -/
def ringConnectivity (n : ℕ) : List (Fin n × Fin n) :=
  if h : 0 < n then
    linearConnectivity n ++ [(⟨n - 1, by omega⟩, ⟨0, by omega⟩)]
  else []

/-- The line connectivity contains `n - 1` edges. -/
theorem length_linearConnectivity (n : ℕ) : (linearConnectivity n).length = n - 1 := by
  simp [linearConnectivity]

/-- The natural-number operation count `(m ^ 3 - m) / 3` assigned to a determinant of size `m`. -/
def determinantOpCost (m : ℕ) : ℕ := (m ^ 3 - m) / 3

/-- The assigned determinant operation count is bounded by `m ^ 3`. -/
theorem determinantOpCost_le (m : ℕ) : determinantOpCost m ≤ m ^ 3 := by
  unfold determinantOpCost
  have h : m ^ 3 - m ≤ m ^ 3 := by omega
  omega

/-- The assigned Pfaffian cost, defined as the determinant cost at size `2 * m`. -/
def pfaffianOpCost (m : ℕ) : ℕ := determinantOpCost (2 * m)

/-- The assigned Pfaffian operation count is bounded by `(2 * m) ^ 3`. -/
theorem pfaffianOpCost_le (m : ℕ) : pfaffianOpCost m ≤ (2 * m) ^ 3 := by
  unfold pfaffianOpCost
  exact determinantOpCost_le (2 * m)

/-- The real four-by-four array whose six specified upper-triangular entries are half of the
selected real and imaginary parts of `A`. -/
def localFormSym (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q =>
    if p = 0 ∧ q = 1 then (A 0 0).im / 2
    else if p = 2 ∧ q = 3 then (A 1 1).im / 2
    else if p = 0 ∧ q = 2 then (A 0 1).re / 2
    else if p = 1 ∧ q = 3 then (A 0 1).re / 2
    else if p = 0 ∧ q = 3 then (A 0 1).im / 2
    else if p = 1 ∧ q = 2 then -(A 0 1).im / 2
    else 0

/-- The skew-symmetric matrix obtained by subtracting the transpose of `localFormSym A`. -/
def localFormMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  localFormSym A - (localFormSym A).transpose

/-- The real matrix exponential of twice `localFormMatrix A`. -/
noncomputable def localRotation (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  NormedSpace.exp ((2 : ℝ) • localFormMatrix A)

/-- Selects mode `i` for the first two local slots and mode `j` for the last two. -/
def localMode {n : ℕ} (i j : Fin n) (p : Fin 4) : Fin n :=
  if p.val < 2 then i else j

/-- The parity of a local slot, viewed as an element of `Fin 2`. -/
def localBit (p : Fin 4) : Fin 2 := ⟨p.val % 2, Nat.mod_lt _ (by decide)⟩

/-- The finite set of Majorana indices belonging to modes `i` or `j`. -/
def localMajoranaFinset {n : ℕ} (i j : Fin n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (isLocalMajorana i j)

/-- Embeds `localRotation A` into the selected Majorana block and uses the identity entries
elsewhere. -/
noncomputable def frameRotation {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b =>
    if isLocalMajorana i j a ∧ isLocalMajorana i j b then
      (localRotation A) (localSlot i j a) (localSlot i j b)
    else if a = b then 1 else 0

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
