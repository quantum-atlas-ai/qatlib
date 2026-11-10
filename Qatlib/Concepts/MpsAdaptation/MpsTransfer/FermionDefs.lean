/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
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

noncomputable def localGate {n : ℕ} (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x =>
    if ∀ k : Fin n, k ≠ j → y k = x k then G (boolEquivFin2 (y j)) (boolEquivFin2 (x j))
    else 0

noncomputable def oneQubitZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then (if c = 1 then -1 else 1) else 0

noncomputable def oneQubitI : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then 1 else 0

noncomputable def oneQubitPhase (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then (if c = 1 then Complex.exp (-Complex.I * θ) else 1) else 0

abbrev LocalGateList (n : ℕ) := List (Fin n × Matrix (Fin 2) (Fin 2) ℂ)

noncomputable def localGateListOp {n : ℕ} : LocalGateList n → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | (j, G) :: rest => localGate j G * localGateListOp rest

def localGateCount {n : ℕ} : LocalGateList n → ℕ
  | [] => 0
  | _ :: rest => 1 + localGateCount rest

def modeAddressBits (n : ℕ) : ℕ := if n ≤ 1 then 1 else Nat.log2 n + 1

def localGateBitCost {n : ℕ} (gl : LocalGateList n) : ℕ :=
  localGateCount gl * modeAddressBits n

def localGateSpaceCost {n : ℕ} (_gl : LocalGateList n) : ℕ := n

theorem localGateCount_pos {n : ℕ} (gl : LocalGateList n) :
    gl ≠ [] → 0 < localGateCount gl := by
  cases gl with
  | nil => simp
  | cons g rest =>
      intro h
      simp [localGateCount]

noncomputable def jwSiteFactor {n : ℕ} (i j : Fin n) (y x : Reg n) : ℂ :=
  if j < i then (if y j = x j then (if x j then -1 else 1 : ℂ) else 0)
  else if i < j then (if y j = x j then 1 else 0)
  else sigmaMinus (boolEquivFin2 (y j)) (boolEquivFin2 (x j))

theorem jwPauliWord_eq_siteFactors {n : ℕ} (i : Fin n) (y x : Reg n) :
    jwPauliWord i y x = ∏ j : Fin n, jwSiteFactor i j y x := by
  rfl

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

theorem jwPauliWord_gateCount {n : ℕ} (i : Fin n) :
    (i.val + 1) ≤ n := by omega

def localGateDiagEntry {n : ℕ} (p : Fin n × Matrix (Fin 2) (Fin 2) ℂ) (y : Reg n) : ℂ :=
  p.2 (boolEquivFin2 (y p.1)) (boolEquivFin2 (y p.1))

def jwZPrefix {n : ℕ} (i : Fin n) : LocalGateList n :=
  ((Finset.univ : Finset (Fin n)).filter (· < i)).toList.map (fun j => (j, oneQubitZ))

def jwLocalGateList {n : ℕ} (i : Fin n) : LocalGateList n :=
  jwZPrefix i ++ [(i, sigmaMinus)]

theorem jwZPrefix_mem {n : ℕ} (i : Fin n) {p : Fin n × Matrix (Fin 2) (Fin 2) ℂ}
    (hp : p ∈ jwZPrefix i) : p.2 = oneQubitZ := by
  unfold jwZPrefix at hp
  rw [List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  rfl

theorem numberOp_apply {n : ℕ} (i : Fin n) (y x : Reg n) :
    numberOp i y x = if x = y ∧ x i then 1 else 0 := rfl

theorem numberOp_diagonal {n : ℕ} (i : Fin n) (y x : Reg n) (h : y ≠ x) :
    numberOp i y x = 0 := by
  rw [numberOp_apply]
  split <;> simp_all

noncomputable def onsiteLocalGate {n : ℕ} (i : Fin n) (θ : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  localGate i (oneQubitPhase θ)

noncomputable def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliX - Complex.I • pauliY)

noncomputable def oneQubitNumber : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b c => if b = c then (if c = 1 then 1 else 0) else 0

def zSetOperator {n : ℕ} (S : Finset (Fin n)) : Matrix (Reg n) (Reg n) ℂ :=
  localGateListOp ((S.toList).map (fun k => (k, oneQubitZ)))

def zRangeSet {n : ℕ} (i j : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => i ≤ k ∧ k < j)

def zRangeGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  (zRangeSet i j).toList.map (fun k => (k, oneQubitZ))

def zTailSet {n : ℕ} (i j : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => i < k ∧ k < j)

def zTailGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  (zTailSet i j).toList.map (fun k => (k, oneQubitZ))

noncomputable def twoSiteGate {n : ℕ} (i j : Fin n)
    (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x =>
    if ∀ k : Fin n, k ≠ i → k ≠ j → y k = x k then
      B (boolEquivFin2 (y i), boolEquivFin2 (y j)) (boolEquivFin2 (x i), boolEquivFin2 (x j))
    else 0

def jwCreationGateList {n : ℕ} (i : Fin n) : LocalGateList n :=
  [(i, sigmaPlus)] ++ jwZPrefix i

def numberGateList {n : ℕ} (i : Fin n) : LocalGateList n :=
  [(i, oneQubitNumber)]

def hopForwardGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  [(i, sigmaPlus)] ++ zRangeGateList i j ++ [(j, sigmaMinus)]

def hopBackwardGateList {n : ℕ} (i j : Fin n) : LocalGateList n :=
  [(j, sigmaPlus)] ++ zRangeGateList i j ++ [(i, sigmaMinus)]

structure QuadraticTerm (n : ℕ) where

  i : Fin n

  j : Fin n

  hij : i < j

  A : Matrix (Fin 2) (Fin 2) ℂ

abbrev LocalGateSum (n : ℕ) := List (ℂ × LocalGateList n)

noncomputable def localGateSumOp {n : ℕ} : LocalGateSum n → Matrix (Reg n) (Reg n) ℂ
  | [] => 0
  | (c, gl) :: rest => c • localGateListOp gl + localGateSumOp rest

def localGateSumCount {n : ℕ} : LocalGateSum n → ℕ
  | [] => 0
  | (_, gl) :: rest => localGateCount gl + localGateSumCount rest

def localGateSumBitCost {n : ℕ} : LocalGateSum n → ℕ
  | [] => 0
  | (_, gl) :: rest => localGateBitCost gl + localGateSumBitCost rest

def localGateSumSpaceCost {n : ℕ} : LocalGateSum n → ℕ
  | [] => 0
  | (_, gl) :: rest => max n (localGateSumSpaceCost rest)

def modePairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def modePairList (n : ℕ) : List (Fin n × Fin n) := (modePairs n).toList

noncomputable def hopForwardBlock : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => sigmaPlus a.1 c.1 * sigmaMinus a.2 c.2

noncomputable def hopBackwardBlock : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => sigmaMinus a.1 c.1 * sigmaPlus a.2 c.2

noncomputable def numberBlockI : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => if a = c then (if a.1 = 1 then 1 else 0) else 0

noncomputable def numberBlockJ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => if a = c then (if a.2 = 1 then 1 else 0) else 0

noncomputable def generatorBlock (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => A 0 0 * numberBlockI a c + A 0 1 * hopForwardBlock a c
    + A 1 0 * hopBackwardBlock a c + A 1 1 * numberBlockJ a c

def twoSiteBits {n : ℕ} (i j : Fin n) (y : Reg n) : Fin 2 × Fin 2 :=
  (boolEquivFin2 (y i), boolEquivFin2 (y j))

def twoSiteExtend {n : ℕ} (i j : Fin n) (y : Reg n) (w : Fin 2 × Fin 2) : Reg n :=
  fun k => if k = i then boolEquivFin2.symm w.1
    else if k = j then boolEquivFin2.symm w.2 else y k

def hubbardOnsiteWord {n : ℕ} (μ : ℂ) (i : Fin n) : LocalGateSum n :=
  [(μ, numberGateList i)]

def hubbardInteractionWord {n : ℕ} (U : ℂ) (i j : Fin n) : LocalGateSum n :=
  [(U, numberGateList i ++ numberGateList j)]

def hubbardHoppingWord {n : ℕ} (t : ℂ) (i j : Fin n) : LocalGateSum n :=
  [(t, hopForwardGateList i j), (t, hopBackwardGateList i j)]

def hubbardHamiltonianWord {n : ℕ} (t μ U : ℂ) : LocalGateSum n :=
  (List.finRange n).flatMap (fun i => hubbardOnsiteWord μ i)
    ++ (fermionPairs n).flatMap (fun p => hubbardInteractionWord U p.1 p.2)
    ++ (fermionPairs n).flatMap (fun p => hubbardHoppingWord t p.1 p.2)

noncomputable def hubbardTermSum {n : ℕ} (t μ U : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (hubbardJWTerms t μ U).foldr (fun p acc => p.1 • p.2 + acc) 0

noncomputable def hubbardOnsiteSum {n : ℕ} (μ : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (List.finRange n).foldr (fun i acc => μ • numberOp i + acc) 0

noncomputable def hubbardInteractionSum {n : ℕ} (U : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (fermionPairs n).foldr (fun p acc => U • (numberOp p.1 * numberOp p.2) + acc) 0

noncomputable def hubbardHoppingSum {n : ℕ} (t : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (fermionPairs n).foldr
    (fun p acc => t • (creation p.1 * annihilation p.2 + creation p.2 * annihilation p.1) + acc) 0

structure OneBodyTerm (n : ℕ) where

  i : Fin n

  h : ℂ

def oneBodyWord {n : ℕ} (t : OneBodyTerm n) : LocalGateSum n :=
  [(t.h, numberGateList t.i)]

theorem oneBodyWord_mem {n : ℕ} (t : OneBodyTerm n) {p : Fin n × Matrix (Fin 2) (Fin 2) ℂ}
    (hp : p ∈ numberGateList t.i) : p.2 = oneQubitNumber := by
  simp only [numberGateList, List.mem_singleton] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

abbrev MatchGateCircuit (n : ℕ) := List (Fin n × Fin n × Matrix (Fin 2) (Fin 2) ℂ)

noncomputable def matchGateCircuitOp {n : ℕ} : MatchGateCircuit n → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | (i, j, A) :: rest => matchGate i j A * matchGateCircuitOp rest

def matchGateCount {n : ℕ} : MatchGateCircuit n → ℕ
  | [] => 0
  | _ :: rest => 1 + matchGateCount rest

theorem matchGateCount_eq_length {n : ℕ} (gl : MatchGateCircuit n) :
    matchGateCount gl = gl.length := by
  induction gl with
  | nil => rfl
  | cons e rest ih => simp [matchGateCount, ih, Nat.add_comm]

def matchGateClassicalOps : ℕ := 64

def matchGateCircuitClassicalOps {n : ℕ} (gl : MatchGateCircuit n) : ℕ :=
  matchGateCount gl * matchGateClassicalOps

theorem matchGateCircuitClassicalOps_le {n : ℕ} (gl : MatchGateCircuit n) :
    matchGateCircuitClassicalOps gl ≤ 64 * matchGateCount gl := by
  simp only [matchGateCircuitClassicalOps, matchGateClassicalOps]
  omega

def majoranaIndices {n : ℕ} (k : Fin n) (b : Fin 2) : Fin (2 * n) :=
  ⟨2 * k.val + b.val, by omega⟩

def isLocalMajorana {n : ℕ} (i j : Fin n) (c : Fin (2 * n)) : Prop :=
  c = majoranaIndices i 0 ∨ c = majoranaIndices i 1
    ∨ c = majoranaIndices j 0 ∨ c = majoranaIndices j 1

instance isLocalMajoranaDecidable {n : ℕ} (i j : Fin n) (c : Fin (2 * n)) :
    Decidable (isLocalMajorana i j c) := by
  unfold isLocalMajorana
  infer_instance

theorem majoranaIndices_ne {n : ℕ} (i : Fin n) (b c : Fin 2) (hbc : b ≠ c) :
    majoranaIndices i b ≠ majoranaIndices i c := by
  intro h
  apply hbc
  apply Fin.ext
  simp only [majoranaIndices, Fin.mk.injEq] at h ⊢
  omega

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

def localIndices {n : ℕ} (i j : Fin n) (p : Fin 4) : Fin (2 * n) :=
  match p.val with
  | 0 => majoranaIndices i 0
  | 1 => majoranaIndices i 1
  | 2 => majoranaIndices j 0
  | _ => majoranaIndices j 1

def localSlot {n : ℕ} (i j : Fin n) (a : Fin (2 * n)) : Fin 4 :=
  if a = majoranaIndices i 0 then 0
  else if a = majoranaIndices j 0 then 2
  else if a = majoranaIndices i 1 then 1
  else 3

noncomputable def localBlock {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q => Γ (localIndices i j p) (localIndices i j q)

noncomputable def covarianceUpdate {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := by
  classical
  exact Matrix.of fun a b =>
    if isLocalMajorana i j a ∧ isLocalMajorana i j b then
      (R * localBlock Γ i j * R.transpose) (localSlot i j a) (localSlot i j b)
    else Γ a b

theorem covarianceUpdate_eq_of_not_local {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin (2 * n))
    (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b) :
    covarianceUpdate Γ i j R a b = Γ a b := by
  unfold covarianceUpdate
  simp [ha, hb]

noncomputable def majoranaInBasis {n : ℕ} (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ c : Fin (2 * n), (S a c : ℂ) • majorana c

noncomputable def covarianceComplexOf {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (X Y : Matrix (Reg n) (Reg n) ℂ) : ℂ :=
  Matrix.trace (Mᴴ * (X * Y) * M) - Matrix.trace (Mᴴ * (Y * X) * M)

noncomputable def covarianceOf {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (X Y : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  -(1 / 2 : ℝ) * (covarianceComplexOf M X Y).im

noncomputable def covarianceInBasis {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b => covarianceOf M (majoranaInBasis S a) (majoranaInBasis S b)

noncomputable def localMajoranaInBasis {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 4) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ s : Fin 4, (R p s : ℂ) • majorana (localIndices i j s)

noncomputable def localCovarianceInBasis {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q => covarianceOf M (localMajoranaInBasis i j R p) (localMajoranaInBasis i j R q)

def occupationFromCovariance {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (k : Fin n) : ℝ :=
  (1 - Γ (majoranaIndices k 0) (majoranaIndices k 1)) / 2

noncomputable def occupationExpectation {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) : ℝ :=
  (Matrix.trace (Mᴴ * (numberOp k) * M)).re

def occupationClassicalCost {n : ℕ} (_k : Fin n) : ℕ := 1

def physicalMeasurementCost (n : ℕ) : ℕ := 2 ^ n

def linearConnectivity (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).zip (List.finRange n).tail

def ringConnectivity (n : ℕ) : List (Fin n × Fin n) :=
  if h : 0 < n then
    linearConnectivity n ++ [(⟨n - 1, by omega⟩, ⟨0, by omega⟩)]
  else []

theorem length_linearConnectivity (n : ℕ) : (linearConnectivity n).length = n - 1 := by
  simp [linearConnectivity]

def determinantOpCost (m : ℕ) : ℕ := (m ^ 3 - m) / 3

theorem determinantOpCost_le (m : ℕ) : determinantOpCost m ≤ m ^ 3 := by
  unfold determinantOpCost
  have h : m ^ 3 - m ≤ m ^ 3 := by omega
  omega

def pfaffianOpCost (m : ℕ) : ℕ := determinantOpCost (2 * m)

theorem pfaffianOpCost_le (m : ℕ) : pfaffianOpCost m ≤ (2 * m) ^ 3 := by
  unfold pfaffianOpCost
  exact determinantOpCost_le (2 * m)

def localFormSym (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q =>
    if p = 0 ∧ q = 1 then (A 0 0).im / 2
    else if p = 2 ∧ q = 3 then (A 1 1).im / 2
    else if p = 0 ∧ q = 2 then (A 0 1).re / 2
    else if p = 1 ∧ q = 3 then (A 0 1).re / 2
    else if p = 0 ∧ q = 3 then (A 0 1).im / 2
    else if p = 1 ∧ q = 2 then -(A 0 1).im / 2
    else 0

def localFormMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  localFormSym A - (localFormSym A).transpose

noncomputable def localRotation (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  NormedSpace.exp ((2 : ℝ) • localFormMatrix A)

def localMode {n : ℕ} (i j : Fin n) (p : Fin 4) : Fin n :=
  if p.val < 2 then i else j

def localBit (p : Fin 4) : Fin 2 := ⟨p.val % 2, Nat.mod_lt _ (by decide)⟩

def localMajoranaFinset {n : ℕ} (i j : Fin n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (isLocalMajorana i j)

noncomputable def frameRotation {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b =>
    if isLocalMajorana i j a ∧ isLocalMajorana i j b then
      (localRotation A) (localSlot i j a) (localSlot i j b)
    else if a = b then 1 else 0

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
