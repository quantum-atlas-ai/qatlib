/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.ActualNestedAmplificationStat
import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsLows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

private def projH {H : Type} (M : Matrix (Space H 1) (Space H 1) ℂ) : Matrix H H ℂ :=
  fun h h' => M (h, (0 : Fin 1)) (h', (0 : Fin 1))

private theorem projH_mul {H : Type} [Fintype H] [DecidableEq H]
    (M N : Matrix (Space H 1) (Space H 1) ℂ) :
    projH (M * N) = projH M * projH N := by
  ext h h'
  show (∑ p : H × Fin 1, M (h, (0 : Fin 1)) p * N p (h', (0 : Fin 1))) = _
  rw [Fintype.sum_prod_type]
  have hk : ∀ x : H,
      (∑ k : Fin 1, M (h, (0 : Fin 1)) (x, k) * N (x, k) (h', (0 : Fin 1)))
        = M (h, (0 : Fin 1)) (x, (0 : Fin 1)) * N (x, (0 : Fin 1)) (h', (0 : Fin 1)) := by
    intro x
    rw [Fin.sum_univ_one]
  rw [Finset.sum_congr rfl fun x _ => hk x]
  rfl

private theorem projH_mul5 {H : Type} [Fintype H] [DecidableEq H]
    (A B C D E : Matrix (Space H 1) (Space H 1) ℂ) :
    projH (A * B * C * D * E) = projH A * projH B * projH C * projH D * projH E := by
  rw [projH_mul, projH_mul, projH_mul, projH_mul]

private theorem projH_one {H : Type} [Fintype H] [DecidableEq H] :
    projH (1 : Matrix (Space H 1) (Space H 1) ℂ) = (1 : Matrix H H ℂ) := by
  ext h h'
  by_cases hh : h = h'
  · subst hh
    simp [projH]
  · simp [projH, hh]

private theorem projH_conjTranspose {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix (Space H 1) (Space H 1) ℂ) :
    projH (Mᴴ) = (projH M)ᴴ := by
  ext h h'
  show star (M (h', (0 : Fin 1)) (h, (0 : Fin 1))) = star (M (h', (0 : Fin 1)) (h, (0 : Fin 1)))
  rfl

private theorem projH_neg_one {H : Type} [Fintype H] [DecidableEq H] :
    projH (-1 : Matrix (Space H 1) (Space H 1) ℂ) = (-1 : Matrix H H ℂ) := by
  ext h h'
  by_cases hh : h = h'
  · subst hh
    simp [projH]
  · simp [projH, hh]

private theorem projH_controlled_univ {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) :
    projH (controlled U Finset.univ) = U := by
  ext h h'
  show (if (0 : Fin 1) = (0 : Fin 1) then
      (if (0 : Fin 1) ∈ Finset.univ then U h h' else if h = h' then (1 : ℂ) else 0) else 0)
    = U h h'
  simp

private theorem projH_mul_conjTranspose {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix (Space H 1) (Space H 1) ℂ) (hM : M ∈ Matrix.unitaryGroup (Space H 1) ℂ) :
    projH M * (projH M)ᴴ = 1 := by
  have hMM : M * Mᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff).mp hM
  have key := congrArg projH hMM
  rw [projH_mul, projH_conjTranspose, projH_one] at key
  exact key

private theorem projH_conjTranspose_mul {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix (Space H 1) (Space H 1) ℂ) (hM : M ∈ Matrix.unitaryGroup (Space H 1) ℂ) :
    (projH M)ᴴ * projH M = 1 := by
  have hMM : Mᴴ * M = 1 := (Matrix.mem_unitaryGroup_iff').mp hM
  have key := congrArg projH hMM
  rw [projH_mul, projH_conjTranspose, projH_one] at key
  exact key

private theorem clockState_eq_projH {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H) :
    clockState U C ω = projH (wordMatrix U C) *ᵥ ω := by
  funext h
  show run (by omega) U C ω (h, (0 : Fin 1)) = _
  simp only [run]
  show (wordMatrix U C *ᵥ clean 1 (by omega) ω) (h, (0 : Fin 1)) = _
  show (∑ p : H × Fin 1, wordMatrix U C (h, (0 : Fin 1)) p * clean 1 (by omega) ω p) = _
  rw [Fintype.sum_prod_type]
  have hk : ∀ x : H,
      (∑ k : Fin 1, wordMatrix U C (h, (0 : Fin 1)) (x, k) * clean 1 (by omega) ω (x, k))
        = wordMatrix U C (h, (0 : Fin 1)) (x, (0 : Fin 1)) * ω x := by
    intro x
    rw [Fin.sum_univ_one]
    show wordMatrix U C (h, (0 : Fin 1)) (x, (0 : Fin 1)) *
        (if (0 : Fin 1) = (⟨0, by omega⟩ : Fin 1) then ω x else 0) = _
    simp
  rw [Finset.sum_congr rfl fun x _ => hk x]
  rfl

private theorem normalized_clockState {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H)
    (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ)
    (hlegal : legal slots C) (hω : Normalized ω) : Normalized (clockState U C ω) := by
  have hrun : Normalized (run (by omega) U C ω) := run_normalized (by omega) U C ω hU hlegal hω
  show ∑ h : H, ‖clockState U C ω h‖ ^ 2 = 1
  have hsum : (∑ p : H × Fin 1, ‖run (by omega) U C ω p‖ ^ 2) = 1 := hrun
  rw [Fintype.sum_prod_type] at hsum
  have hk : ∀ x : H,
      (∑ k : Fin 1, ‖run (by omega) U C ω (x, k)‖ ^ 2)
        = ‖run (by omega) U C ω (x, (0 : Fin 1))‖ ^ 2 := by
    intro x
    rw [Fin.sum_univ_one]
  rw [Finset.sum_congr rfl fun x _ => hk x] at hsum
  exact hsum

private theorem wordMatrix_nil {H : Type} [Fintype H] [DecidableEq H]
    (oracles : ℕ → Matrix H H ℂ) : wordMatrix oracles ([] : Word H 1) = 1 := by
  unfold wordMatrix
  simp

private theorem wordMatrix_singleton_known {H : Type} [Fintype H] [DecidableEq H]
    (oracles : ℕ → Matrix H H ℂ) (V : Matrix (Space H 1) (Space H 1) ℂ) :
    wordMatrix oracles [.known V] = V := by
  unfold wordMatrix
  simp

private theorem wordMatrix_append5 {H : Type} [Fintype H] [DecidableEq H]
    (oracles : ℕ → Matrix H H ℂ) (A B C D E : Word H 1) :
    wordMatrix oracles (A ++ B ++ C ++ D ++ E)
      = wordMatrix oracles E * wordMatrix oracles D * wordMatrix oracles C
        * wordMatrix oracles B * wordMatrix oracles A := by
  rw [wordMatrix_append, wordMatrix_append, wordMatrix_append, wordMatrix_append]
  simp only [mul_assoc]

private theorem calls_singleton_known {H : Type} {r : ℕ}
    (V : Matrix (Space H r) (Space H r) ℂ) (j : ℕ) :
    calls [.known V] j = 0 := rfl

private theorem gateCount_singleton_known {H : Type} {r : ℕ}
    (V : Matrix (Space H r) (Space H r) ℂ) :
    gateCount [.known V] = 1 := rfl

private theorem weightedCost_singleton_known {H : Type} {r : ℕ}
    (prices : ℕ → ℕ) (V : Matrix (Space H r) (Space H r) ℂ) :
    weightedCost prices [.known V] = 0 := rfl

private theorem gateCount_append {H : Type} {r : ℕ} (C D : Word H r) :
    gateCount (C ++ D) = gateCount C + gateCount D := List.countP_append

private theorem weightedCost_append {H : Type} {r : ℕ}
    (prices : ℕ → ℕ) (C D : Word H r) :
    weightedCost prices (C ++ D) = weightedCost prices C + weightedCost prices D := by
  show ((C ++ D).map
        (fun (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) => match s with | .call j _ _ => prices j | _ => 0)).sum
      = ((C.map (fun (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) => match s with | .call j _ _ => prices j | _ => 0)).sum)
        + ((D.map (fun (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) => match s with | .call j _ _ => prices j | _ => 0)).sum)
  rw [List.map_append, List.sum_append]

private theorem gateCount_wordAdjoint {H : Type} {r : ℕ} (C : Word H r) :
    gateCount (wordAdjoint C) = gateCount C := by
  have hdef : ∀ D : Word H r, gateCount D =
      D.countP (fun (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) => match s with | .known _ => true | _ => false) :=
    fun _ => rfl
  rw [hdef (wordAdjoint C), hdef C, wordAdjoint_eq, List.countP_map, List.countP_reverse]
  congr 1
  funext s
  cases s with
  | known V => rfl
  | call i T a => rfl

private theorem weightedCost_wordAdjoint {H : Type} {r : ℕ}
    (prices : ℕ → ℕ) (C : Word H r) :
    weightedCost prices (wordAdjoint C) = weightedCost prices C := by
  have hdef : ∀ D : Word H r, weightedCost prices D =
      ((D.map (fun (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) => match s with | .call j _ _ => prices j | _ => 0)).sum) :=
    fun _ => rfl
  rw [hdef (wordAdjoint C), hdef C, wordAdjoint_eq, List.map_map, List.map_reverse,
    List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro s _
  cases s with
  | known V => rfl
  | call i T a =>
    cases a with
    | true => rfl
    | false => rfl

private theorem legal_append {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (slots : ℕ) (C D : Word H r) :
    legal slots (C ++ D) ↔ legal slots C ∧ legal slots D := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (List.mem_append.mpr (Or.inl ht)),
      fun t ht => h t (List.mem_append.mpr (Or.inr ht))⟩
  · intro h t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h.1 t ht
    · exact h.2 t ht

private theorem legal_singleton_known {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (V : Matrix (Space H 1) (Space H 1) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Space H 1) ℂ) : legal slots [.known V] := by
  intro t ht
  have ht' : t = .known V := List.mem_singleton.mp ht
  subst ht'
  exact hV

private theorem neg_one_unitary {n : Type} [Fintype n] [DecidableEq n] :
    (-1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  show (-1 : Matrix n n ℂ) * star (-1) = 1
  rw [star_neg, star_one, neg_mul_neg, one_mul]

private def aaRound {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) : Word H 1 :=
  ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)] : Word H 1)

private theorem aaWord_eq {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ) :
    aaWord B ω G s = B ++ (List.replicate s (aaRound B ω G)).flatten := rfl

private theorem calls_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (j : ℕ) :
    calls (aaRound B ω G) j = 2 * calls B j := by
  show calls ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)]) j = _
  rw [calls_append, calls_append, calls_append, calls_append, calls_wordAdjoint,
    calls_singleton_known, calls_singleton_known, calls_singleton_known]
  ring

private theorem gateCount_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) :
    gateCount (aaRound B ω G) = 2 * gateCount B + 3 := by
  show gateCount ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)]) = _
  rw [gateCount_append, gateCount_append, gateCount_append, gateCount_append,
    gateCount_singleton_known, gateCount_singleton_known, gateCount_singleton_known,
    gateCount_wordAdjoint]
  ring

private theorem weightedCost_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (prices : ℕ → ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) :
    weightedCost prices (aaRound B ω G) = 2 * weightedCost prices B := by
  show weightedCost prices ([.known (controlled (ReflectionAbout G) Finset.univ)] ++
      wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)]) = _
  rw [weightedCost_append, weightedCost_append, weightedCost_append, weightedCost_append,
    weightedCost_singleton_known, weightedCost_singleton_known, weightedCost_singleton_known,
    weightedCost_wordAdjoint]
  ring

private theorem legal_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ)
    (hG : IsOrthogonalProjector G) (hω : Normalized ω) (hB : legal slots B) :
    legal slots (aaRound B ω G) := by
  have hRG : legal slots
      ([.known (controlled (ReflectionAbout G) Finset.univ)] : Word H 1) :=
    legal_singleton_known slots _ (controlled_unitary (reflectionAbout_unitary hG) Finset.univ)
  have hRω : legal slots
      ([.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] : Word H 1) := by
    apply legal_singleton_known
    have hseed : seedProjector ω = outerProduct ω := pureDensity_eq_outerProduct ω
    rw [hseed]
    exact controlled_unitary (outerProduct_reflection_unitary hω) Finset.univ
  have hneg : legal slots [.known (-1 : Matrix (Space H 1) (Space H 1) ℂ)] :=
    legal_singleton_known slots (-1 : Matrix (Space H 1) (Space H 1) ℂ) neg_one_unitary
  have hAdj : legal slots (wordAdjoint B) := legal_wordAdjoint B hB
  intro t ht
  change t ∈ ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)] : Word H 1) at ht
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append] at ht
  simp only [List.mem_singleton] at ht
  simp only [or_assoc] at ht
  rcases ht with h | h | h | h | h
  · subst h
    exact controlled_unitary (reflectionAbout_unitary hG) Finset.univ
  · exact hAdj t h
  · subst h
    have hseed : seedProjector ω = outerProduct ω := pureDensity_eq_outerProduct ω
    rw [hseed]
    exact controlled_unitary (outerProduct_reflection_unitary hω) Finset.univ
  · exact hB t h
  · subst h
    exact neg_one_unitary

private theorem calls_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s j : ℕ) :
    calls ((List.replicate s (aaRound B ω G)).flatten) j = s * calls (aaRound B ω G) j := by
  induction s with
  | zero =>
    show calls ([] : Word H 1) j = (0 : ℕ) * calls (aaRound B ω G) j
    rw [zero_mul]
    rfl
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, calls_append, ih]
    ring

private theorem gateCount_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ) :
    gateCount ((List.replicate s (aaRound B ω G)).flatten) = s * gateCount (aaRound B ω G) := by
  induction s with
  | zero =>
    show gateCount ([] : Word H 1) = (0 : ℕ) * gateCount (aaRound B ω G)
    rw [zero_mul]
    rfl
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, gateCount_append, ih]
    ring

private theorem weightedCost_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (prices : ℕ → ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ) :
    weightedCost prices ((List.replicate s (aaRound B ω G)).flatten)
      = s * weightedCost prices (aaRound B ω G) := by
  induction s with
  | zero =>
    show weightedCost prices ([] : Word H 1) = (0 : ℕ) * weightedCost prices (aaRound B ω G)
    rw [zero_mul]
    rfl
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, weightedCost_append, ih]
    ring

private theorem legal_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ)
    (h : legal slots (aaRound B ω G)) :
    legal slots ((List.replicate s (aaRound B ω G)).flatten) := by
  induction s with
  | zero =>
    intro t ht
    simp at ht
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, legal_append]
    exact ⟨h, ih⟩

private def roundOp {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) : Matrix H H ℂ :=
  -((ReflectionAbout (outerProduct ψ)) * (ReflectionAbout G))

private theorem outerProduct_conj {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (φ : QState I) :
    A * outerProduct φ * Aᴴ = outerProduct (A *ᵥ φ) := by
  ext i j
  simp only [outerProduct, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    starRingEnd_apply, Matrix.mulVec, dotProduct]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [star_mul]
  ring

private theorem seedProjector_eq_outerProduct {H : Type} (ω : QState H) :
    seedProjector ω = outerProduct ω := pureDensity_eq_outerProduct ω

private theorem mul5_reassoc {n : Type} [Fintype n] [DecidableEq n]
    (A B C D E : Matrix n n ℂ) :
    A * B * C * D * E = A * (B * C * D) * E := by
  simp only [mul_assoc]

private theorem projH_wordMatrix_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ)
    (_hG : IsOrthogonalProjector G) (slots : ℕ)
    (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ) (hB : legal slots B) :
    projH (wordMatrix U (aaRound B ω G)) = roundOp (clockState U B ω) G := by
  have hWM : wordMatrix U B ∈ Matrix.unitaryGroup (Space H 1) ℂ :=
    wordMatrix_unitary U B hU hB
  have hWunit : projH (wordMatrix U B) * (projH (wordMatrix U B))ᴴ = 1 :=
    projH_mul_conjTranspose _ hWM
  have hchain : wordMatrix U (aaRound B ω G)
      = wordMatrix U [.known (-1 : Matrix (Space H 1) (Space H 1) ℂ)]
        * wordMatrix U B
        * wordMatrix U [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)]
        * wordMatrix U (wordAdjoint B)
        * wordMatrix U [.known (controlled (ReflectionAbout G) Finset.univ)] :=
    wordMatrix_append5 U _ _ _ _ _
  rw [hchain, projH_mul5, wordMatrix_singleton_known, wordMatrix_singleton_known,
    wordMatrix_singleton_known, wordMatrix_wordAdjoint, projH_neg_one,
    projH_controlled_univ, projH_conjTranspose, projH_controlled_univ]
  have hconj : projH (wordMatrix U B) * ReflectionAbout (seedProjector ω)
        * (projH (wordMatrix U B))ᴴ
      = ReflectionAbout (outerProduct (clockState U B ω)) := by
    have hseed : seedProjector ω = outerProduct ω := seedProjector_eq_outerProduct ω
    rw [hseed, ReflectionAbout, ReflectionAbout]
    rw [mul_sub, sub_mul, mul_one]
    have hsmul : projH (wordMatrix U B) * ((2 : ℂ) • outerProduct ω) * (projH (wordMatrix U B))ᴴ
        = (2 : ℂ) • (projH (wordMatrix U B) * outerProduct ω * (projH (wordMatrix U B))ᴴ) := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [hsmul, hWunit]
    have houter : projH (wordMatrix U B) * outerProduct ω * (projH (wordMatrix U B))ᴴ
        = outerProduct (projH (wordMatrix U B) *ᵥ ω) :=
      outerProduct_conj (projH (wordMatrix U B)) ω
    rw [houter, clockState_eq_projH]
  have hre : (-1 : Matrix H H ℂ) * projH (wordMatrix U B)
      * ReflectionAbout (seedProjector ω) * (projH (wordMatrix U B))ᴴ
      = (-1 : Matrix H H ℂ) * (projH (wordMatrix U B) * ReflectionAbout (seedProjector ω)
          * (projH (wordMatrix U B))ᴴ) := by
    simp only [mul_assoc]
  rw [hre, hconj]
  have hfinal : (-1 : Matrix H H ℂ)
      * ReflectionAbout (outerProduct (clockState U B ω)) * ReflectionAbout G
      = (-1 : Matrix H H ℂ) *
        (ReflectionAbout (outerProduct (clockState U B ω)) * ReflectionAbout G) := by
    simp only [mul_assoc]
  rw [hfinal]
  exact (neg_eq_neg_one_mul
    (ReflectionAbout (outerProduct (clockState U B ω)) * ReflectionAbout G)).symm

private theorem projH_wordMatrix_flatten {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ)
    (hG : IsOrthogonalProjector G) (slots : ℕ)
    (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ) (hB : legal slots B) (s : ℕ) :
    projH (wordMatrix U ((List.replicate s (aaRound B ω G)).flatten))
      = (roundOp (clockState U B ω) G) ^ s := by
  have hR : projH (wordMatrix U (aaRound B ω G)) = roundOp (clockState U B ω) G :=
    projH_wordMatrix_aaRound U B ω G hG slots hU hB
  induction s with
  | zero =>
    show projH (wordMatrix U ([] : Word H 1)) = _
    rw [wordMatrix_nil, projH_one, pow_zero]
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, wordMatrix_append, projH_mul, hR, ih]
    exact (pow_succ (roundOp (clockState U B ω) G) s).symm

private theorem clockState_aaWord {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ)
    (hG : IsOrthogonalProjector G) (slots : ℕ)
    (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ) (hB : legal slots B) (s : ℕ) :
    clockState U (aaWord B ω G s) ω
      = (roundOp (clockState U B ω) G) ^ s *ᵥ (clockState U B ω) := by
  rw [aaWord_eq, clockState_eq_projH, wordMatrix_append, projH_mul, ← Matrix.mulVec_mulVec,
    projH_wordMatrix_flatten U B ω G hG slots hU hB s, ← clockState_eq_projH]

private theorem inner_add_left' {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ψ + φ) χ = Qatlib.Foundations.PureStateMath.Inner ψ χ + Qatlib.Foundations.PureStateMath.Inner φ χ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.add_apply, Pi.star_apply, RCLike.star_def, map_add,
    add_mul, Finset.sum_add_distrib]

private theorem inner_zero_left' {I : Type} [Fintype I] (φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (0 : QState I) φ = 0 := by
  simp [Qatlib.Foundations.PureStateMath.Inner]

private theorem inner_zero_right' {I : Type} [Fintype I] (ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (0 : QState I) = 0 := by
  simp [Qatlib.Foundations.PureStateMath.Inner]

private theorem inner_conj_symm' {I : Type} [Fintype I] (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ φ = star (Qatlib.Foundations.PureStateMath.Inner φ ψ) := by
  rw [inner_apply, inner_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Complex.star_def, map_mul, starRingEnd_self_apply, mul_comm]

private theorem inner_add_right' {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ + χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ + Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  rw [inner_conj_symm' ψ (φ + χ), inner_add_left', star_add,
    ← inner_conj_symm' ψ φ, ← inner_conj_symm' ψ χ]

private theorem inner_mulVec_conjTranspose_right' {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (A *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner (Aᴴ *ᵥ ψ) φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

private theorem inner_mulVec_left' {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (A *ᵥ ψ) φ = Qatlib.Foundations.PureStateMath.Inner ψ (Aᴴ *ᵥ φ) := by
  rw [inner_conj_symm', inner_mulVec_conjTranspose_right', inner_conj_symm', star_star]

private theorem inner_self_eq_normVec_sq {I : Type} [Fintype I] (ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ ψ = (((normVec ψ) ^ 2 : ℝ) : ℂ) := by
  rw [inner_self, ← Complex.ofReal_sum]
  congr 1
  exact (norm_toEuclidean_fromVec_sq ψ).symm

private theorem good_bad_geometry {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) (hψ : Normalized ψ) :
    let g := G *ᵥ ψ
    let b := ((1 : Matrix H H ℂ) - G) *ᵥ ψ
    g + b = ψ ∧
    Qatlib.Foundations.PureStateMath.Inner g b = 0 ∧ Qatlib.Foundations.PureStateMath.Inner b g = 0 ∧
    Qatlib.Foundations.PureStateMath.Inner g g = (((normVec g) ^ 2 : ℝ) : ℂ) ∧
    Qatlib.Foundations.PureStateMath.Inner b b = (((1 - (normVec g) ^ 2 : ℝ)) : ℂ) ∧
    Qatlib.Foundations.PureStateMath.Inner ψ g = (((normVec g) ^ 2 : ℝ) : ℂ) ∧
    Qatlib.Foundations.PureStateMath.Inner ψ b = (((1 - (normVec g) ^ 2 : ℝ)) : ℂ) ∧
    (0 : ℝ) ≤ normVec g ∧ normVec g ≤ 1 := by
  set g : QState H := G *ᵥ ψ with hg
  set b : QState H := ((1 : Matrix H H ℂ) - G) *ᵥ ψ with hb
  have hGG : G * G = G := hG.1
  have hGH : Gᴴ = G := hG.2
  have hsum : g + b = ψ := by
    rw [hg, hb, ← Matrix.add_mulVec]
    have h1 : (G + ((1 : Matrix H H ℂ) - G)) = 1 := add_sub_cancel _ _
    rw [h1, Matrix.one_mulVec]
  have hGb : G *ᵥ b = 0 := by
    rw [hb, Matrix.mulVec_mulVec, mul_sub, mul_one, hGG, sub_self, Matrix.zero_mulVec]
  have hGg : G *ᵥ g = g := by
    rw [hg, Matrix.mulVec_mulVec, hGG]
  have horth : Qatlib.Foundations.PureStateMath.Inner g b = 0 := by
    rw [hg, hb, inner_mulVec_left', hGH]
    have h2 : G *ᵥ (((1 : Matrix H H ℂ) - G) *ᵥ ψ) = 0 := by
      rw [Matrix.mulVec_mulVec, mul_sub, mul_one, hGG, sub_self, Matrix.zero_mulVec]
    rw [h2, inner_zero_right']
  have horth2 : Qatlib.Foundations.PureStateMath.Inner b g = 0 := by
    rw [inner_conj_symm', horth, star_zero]
  have hgg : Qatlib.Foundations.PureStateMath.Inner g g = (((normVec g) ^ 2 : ℝ) : ℂ) :=
      inner_self_eq_normVec_sq g
  have hψψ : Qatlib.Foundations.PureStateMath.Inner ψ ψ = 1 := inner_self_eq_one hψ
  have hexpand : Qatlib.Foundations.PureStateMath.Inner ψ ψ = Qatlib.Foundations.PureStateMath.Inner g g + Qatlib.Foundations.PureStateMath.Inner b b := by
    rw [← hsum, inner_add_left', inner_add_right', inner_add_right',
      horth, horth2]
    simp
  have hnorm : (normVec ψ) ^ 2 = (normVec g) ^ 2 + (normVec b) ^ 2 := by
    have h1 :
        Qatlib.Foundations.PureStateMath.Inner ψ ψ = Qatlib.Foundations.PureStateMath.Inner g g + Qatlib.Foundations.PureStateMath.Inner b b := hexpand
    rw [inner_self_eq_normVec_sq, inner_self_eq_normVec_sq, inner_self_eq_normVec_sq] at h1
    have h2 : (((normVec ψ) ^ 2 : ℝ) : ℂ)
        = (((normVec g) ^ 2 : ℝ) : ℂ) + (((normVec b) ^ 2 : ℝ) : ℂ) := h1
    exact_mod_cast h2
  have hψsq : (normVec ψ) ^ 2 = 1 := by
    show ‖toEuclidean_fromVec ψ‖ ^ 2 = 1
    rw [norm_toEuclidean_fromVec_sq]
    exact hψ
  have hbb : Qatlib.Foundations.PureStateMath.Inner b b = (((1 - (normVec g) ^ 2 : ℝ)) : ℂ) := by
    have hbbsq : Qatlib.Foundations.PureStateMath.Inner b b = (((normVec b) ^ 2 : ℝ) : ℂ) :=
        inner_self_eq_normVec_sq b
    rw [hbbsq]
    congr 1
    nlinarith [hnorm, hψsq]
  have hψg : Qatlib.Foundations.PureStateMath.Inner ψ g = (((normVec g) ^ 2 : ℝ) : ℂ) := by
    rw [← hsum, inner_add_left', horth2, add_zero, hgg]
  have hψb : Qatlib.Foundations.PureStateMath.Inner ψ b = (((1 - (normVec g) ^ 2 : ℝ)) : ℂ) := by
    rw [← hsum, inner_add_left', horth, zero_add, hbb]
  have hgnonneg : 0 ≤ normVec g := norm_nonneg _
  have hgle : normVec g ≤ 1 := by
    have h : (normVec g) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (normVec b), hnorm, hψsq]
    nlinarith [h, sq_nonneg (normVec g - 1), hgnonneg]
  exact ⟨hsum, horth, horth2, hgg, hbb, hψg, hψb, hgnonneg, hgle⟩

private theorem reflection_good_fixed {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) :
    ReflectionAbout G *ᵥ (G *ᵥ ψ) = G *ᵥ ψ := by
  apply applyGate_reflectionAbout_of_fixed
  show G *ᵥ (G *ᵥ ψ) = G *ᵥ ψ
  rw [Matrix.mulVec_mulVec, hG.1]

private theorem reflection_bad_neg {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) :
    ReflectionAbout G *ᵥ (((1 : Matrix H H ℂ) - G) *ᵥ ψ) = -(((1 : Matrix H H ℂ) - G) *ᵥ ψ) := by
  apply applyGate_reflectionAbout_of_zero
  show G *ᵥ (((1 : Matrix H H ℂ) - G) *ᵥ ψ) = 0
  rw [Matrix.mulVec_mulVec, mul_sub, mul_one, hG.1, sub_self, Matrix.zero_mulVec]

private theorem round_two_component {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) (hψ : Normalized ψ) :
    let g := G *ᵥ ψ
    let b := ((1 : Matrix H H ℂ) - G) *ᵥ ψ
    let μ := (normVec g) ^ 2
    roundOp ψ G *ᵥ g = (((-2 * μ : ℝ) : ℂ)) • b + (((1 - 2 * μ : ℝ) : ℂ)) • g ∧
    roundOp ψ G *ᵥ b = (((1 - 2 * μ : ℝ) : ℂ)) • b + (((2 * (1 - μ) : ℝ) : ℂ)) • g := by
  set g : QState H := G *ᵥ ψ with hg
  set b : QState H := ((1 : Matrix H H ℂ) - G) *ᵥ ψ with hb
  set μ : ℝ := (normVec g) ^ 2 with hμ
  obtain ⟨hsum, horth, horth2, hgg, hbb, hψg, hψb, _, _⟩ :=
    good_bad_geometry ψ G hG hψ
  rw [← hg, ← hb] at hsum
  rw [← hg] at hψg
  rw [← hg, ← hb] at hψb
  have hRGg : ReflectionAbout G *ᵥ g = g := reflection_good_fixed ψ G hG
  have hRGb : ReflectionAbout G *ᵥ b = -b := reflection_bad_neg ψ G hG
  have hRψ : ∀ v : QState H,
      ReflectionAbout (outerProduct ψ) *ᵥ v = (2 : ℂ) • (Qatlib.Foundations.PureStateMath.Inner ψ v • ψ) - v := by
    intro v
    rw [ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      outerProduct_mulVec]
  have hstepg : roundOp ψ G *ᵥ g
      = (((-2 * μ : ℝ) : ℂ)) • b + (((1 - 2 * μ : ℝ) : ℂ)) • g := by
    have e1 : roundOp ψ G *ᵥ g
        = - (ReflectionAbout (outerProduct ψ) *ᵥ (ReflectionAbout G *ᵥ g)) := by
      rw [roundOp, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    rw [e1, hRGg, hRψ, hψg, ← hμ, ← hsum, smul_smul]
    push_cast
    module
  have hstepb : roundOp ψ G *ᵥ b
      = (((1 - 2 * μ : ℝ) : ℂ)) • b + (((2 * (1 - μ) : ℝ) : ℂ)) • g := by
    have e1 : roundOp ψ G *ᵥ b
        = - (ReflectionAbout (outerProduct ψ) *ᵥ (ReflectionAbout G *ᵥ b)) := by
      rw [roundOp, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    rw [e1, hRGb, Matrix.mulVec_neg, neg_neg, hRψ, hψb, ← hμ, ← hsum, smul_smul]
    push_cast
    module
  exact ⟨hstepg, hstepb⟩

private theorem cos_pos_of_lt_half_pi {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    0 < Real.cos θ := by
  have hsin : 0 < Real.sin (Real.pi / 2 - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.sin_pi_div_two_sub θ] at hsin
  exact hsin

private theorem two_component_comb {V : Type} [AddCommMonoid V] [Module ℂ V]
    (bad good : V) (r1 r2 c1 c2 c3 c4 α' β' : ℂ)
    (h1 : r1 * c1 + r2 * c3 = α') (h2 : r1 * c2 + r2 * c4 = β') :
    r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good) = α' • bad + β' • good := by
  have hsplit : r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good)
      = (r1 * c1 + r2 * c3) • bad + (r1 * c2 + r2 * c4) • good := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, add_smul,
      add_smul]
    abel
  rw [hsplit, h1, h2]

private theorem orbit_coef_bad (θ x : ℝ) (_hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    (Real.cos x / Real.cos θ) * (1 - 2 * (Real.sin θ) ^ 2)
      + (Real.sin x / Real.sin θ) * (-2 * (Real.sin θ) ^ 2)
      = Real.cos (x + 2 * θ) / Real.cos θ := by
  have h1 : 1 - 2 * (Real.sin θ) ^ 2 = 2 * (Real.cos θ) ^ 2 - 1 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  field_simp
  rw [Real.cos_add, Real.cos_two_mul, Real.sin_two_mul, h1]
  ring

private theorem orbit_coef_good (θ x : ℝ) (hs : Real.sin θ ≠ 0) (_hc : Real.cos θ ≠ 0) :
    (Real.cos x / Real.cos θ) * (2 * (1 - (Real.sin θ) ^ 2))
      + (Real.sin x / Real.sin θ) * (1 - 2 * (Real.sin θ) ^ 2)
      = Real.sin (x + 2 * θ) / Real.sin θ := by
  have h1 : 1 - 2 * (Real.sin θ) ^ 2 = 2 * (Real.cos θ) ^ 2 - 1 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  have h2 : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  field_simp
  rw [Real.sin_add, Real.cos_two_mul, Real.sin_two_mul, h1, h2]
  ring

private theorem round_orbit {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) (hψ : Normalized ψ)
    (θ : ℝ) (k : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hθs : Real.sin θ ^ 2 = (normVec (G *ᵥ ψ)) ^ 2) :
    (roundOp ψ G) ^ k *ᵥ ψ
      = (((Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.cos θ : ℝ) : ℂ))
          • (((1 : Matrix H H ℂ) - G) *ᵥ ψ)
        + (((Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ)) • (G *ᵥ ψ) := by
  have hs : Real.sin θ ≠ 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    positivity
  have hc : Real.cos θ ≠ 0 := by
    have := cos_pos_of_lt_half_pi hθ0 hθ1
    positivity
  set g : QState H := G *ᵥ ψ with hg
  set b : QState H := ((1 : Matrix H H ℂ) - G) *ᵥ ψ with hb
  set μ : ℝ := (normVec g) ^ 2 with hμ
  have hgeo := good_bad_geometry ψ G hG hψ
  have hsum : g + b = ψ := hgeo.1
  obtain ⟨hstepg, hstepb⟩ := round_two_component ψ G hG hψ
  rw [← hg, ← hb, ← hμ] at hstepg hstepb
  have hμsin : μ = (Real.sin θ) ^ 2 := hθs.symm
  rw [hμsin] at hstepg hstepb
  induction k with
  | zero =>
    have h0 : (2 * ((0 : ℕ) : ℝ) + 1) * θ = θ := by push_cast; ring
    rw [pow_zero, Matrix.one_mulVec, h0, div_self hc, div_self hs]
    push_cast
    rw [one_smul, one_smul, add_comm]
    exact hsum.symm
  | succ k ih =>
    have hang : (2 * (((k + 1 : ℕ) : ℝ)) + 1) * θ
        = (2 * (k : ℝ) + 1) * θ + 2 * θ := by push_cast; ring
    rw [hang, pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hstepb, hstepg]
    refine (two_component_comb (V := QState H)) _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact_mod_cast orbit_coef_bad θ ((2 * (k : ℝ) + 1) * θ) hs hc
    · exact_mod_cast orbit_coef_good θ ((2 * (k : ℝ) + 1) * θ) hs hc

private theorem good_amplified {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) (hψ : Normalized ψ)
    (θ : ℝ) (k : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hθs : Real.sin θ ^ 2 = (normVec (G *ᵥ ψ)) ^ 2) :
    G *ᵥ ((roundOp ψ G) ^ k *ᵥ ψ)
      = (((Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ)) • (G *ᵥ ψ) := by
  rw [round_orbit ψ G hG hψ θ k hθ0 hθ1 hθs, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hGb : G *ᵥ (((1 : Matrix H H ℂ) - G) *ᵥ ψ) = 0 := by
    rw [Matrix.mulVec_mulVec, mul_sub, mul_one, hG.1, sub_self, Matrix.zero_mulVec]
  have hGg : G *ᵥ (G *ᵥ ψ) = G *ᵥ ψ := by
    rw [Matrix.mulVec_mulVec, hG.1]
  simp only [hGb, hGg, smul_zero, zero_add]

private theorem gainLoss_mul (ρ : ℕ) (a : ℝ) (ha : a ≠ 0) :
    ((ρ : ℝ) * gainLoss ρ a) = Real.sin ((ρ : ℝ) * Real.arcsin a) / a := by
  unfold gainLoss
  rw [if_neg ha]
  rcases Nat.eq_zero_or_pos ρ with hρ | hρ
  · subst hρ
    simp
  · have hρ0 : (ρ : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hρ)
    field_simp [ha, hρ0]

private theorem coeff_eq (s : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (((2 * s + 1 : ℕ) : ℂ) * (((gainLoss (2 * s + 1) a : ℝ) : ℂ)))
      = (((Real.sin (((2 * s + 1 : ℕ) : ℝ) * Real.arcsin a) / a : ℝ) : ℂ)) := by
  have h1 : ((2 * s + 1 : ℕ) : ℂ) = (((2 * s + 1 : ℕ) : ℝ) : ℂ) := by norm_num
  rw [h1, ← Complex.ofReal_mul]
  congr 1
  exact gainLoss_mul (2 * s + 1) a ha

private theorem normVec_eq_zero {I : Type} [Fintype I] (v : QState I) :
    normVec v = 0 → v = 0 := by
  intro h
  have h2 : (normVec v) ^ 2 = ∑ i, ‖v i‖ ^ 2 := norm_toEuclidean_fromVec_sq v
  rw [h, zero_pow (by norm_num)] at h2
  have h4 : ∑ i, ‖v i‖ ^ 2 = 0 := h2.symm
  have hi : ∀ i : I, ‖v i‖ ^ 2 = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (‖v j‖))).mp h4 i (Finset.mem_univ i)
  funext i
  have := hi i
  exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)

private theorem pow_mulVec_fix {n : Type} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (x : QState n) (h : Q *ᵥ x = x) (k : ℕ) : Q ^ k *ᵥ x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, h]

private theorem pow_mulVec_neg {n : Type} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (x : QState n) (h : Q *ᵥ x = -x) (k : ℕ) :
    Q ^ k *ᵥ x = (((-1 : ℂ) ^ k)) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h,
      ← neg_one_smul ℂ x, smul_smul, ← pow_succ]

private theorem sin_nat_mul_pi_div_two (s : ℕ) :
    Real.sin (((2 * s + 1 : ℕ) : ℝ) * (Real.pi / 2)) = ((-1 : ℝ) ^ s) := by
  have h : (((2 * s + 1 : ℕ) : ℝ) * (Real.pi / 2))
      = (s : ℝ) * Real.pi + Real.pi / 2 := by push_cast; ring
  rw [h, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, zero_add, mul_one]
  exact Real.cos_nat_mul_pi s

private theorem sine_law {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (U : ℕ → Matrix H H ℂ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ)
    (s : ℕ) (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ)
    (hB : legal slots B) (hω : Normalized ω) (hG : IsOrthogonalProjector G) :
    G *ᵥ clockState U (aaWord B ω G s) ω
      = (((2 * s + 1 : ℕ) : ℂ)
          * (((gainLoss (2 * s + 1) (normVec (G *ᵥ clockState U B ω)) : ℝ) : ℂ)))
        • (G *ᵥ clockState U B ω) := by
  set ψ : QState H := clockState U B ω with hψdef
  set g : QState H := G *ᵥ ψ with hg
  set a : ℝ := normVec g with ha
  have hψn : Normalized ψ := normalized_clockState slots U B ω hU hB hω
  have hgeo := good_bad_geometry ψ G hG hψn
  have hR : clockState U (aaWord B ω G s) ω = (roundOp ψ G) ^ s *ᵥ ψ :=
    clockState_aaWord U B ω G hG slots hU hB s
  rw [hR]
  by_cases ha0 : a = 0
  · have hg0 : g = 0 := normVec_eq_zero g ha0
    have hfix : roundOp ψ G *ᵥ ψ = ψ := by
      have hGψ : G *ᵥ ψ = 0 := by rw [← hg, hg0]
      have hRg : ReflectionAbout G *ᵥ ψ = -ψ := by
        apply applyGate_reflectionAbout_of_zero
        exact hGψ
      have hRψ : ReflectionAbout (outerProduct ψ) *ᵥ ψ = ψ := by
        rw [ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          outerProduct_mulVec, inner_self_eq_one hψn]
        module
      rw [roundOp, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hRg, Matrix.mulVec_neg,
        neg_neg, hRψ]
    rw [pow_mulVec_fix (roundOp ψ G) ψ hfix s]
    have hgz : G *ᵥ ψ = 0 := by rw [← hg, hg0]
    rw [hgz, hg0, smul_zero]
  by_cases ha1 : a = 1
  · have hgn : normVec g = 1 := ha1
    have hgnorm : normVec (G *ᵥ ψ) = 1 := by rw [← hg]; exact hgn
    have hbbsq : (normVec (((1 : Matrix H H ℂ) - G) *ᵥ ψ)) ^ 2 = 0 := by
      have hbb : Qatlib.Foundations.PureStateMath.Inner (((1 : Matrix H H ℂ) - G) *ᵥ ψ) (((1 : Matrix H H ℂ) - G) *ᵥ ψ)
          = (((1 - (normVec (G *ᵥ ψ)) ^ 2 : ℝ)) : ℂ) := hgeo.2.2.2.2.1
      have hbbsq0 : Qatlib.Foundations.PureStateMath.Inner (((1 : Matrix H H ℂ) - G) *ᵥ ψ) (((1 : Matrix H H ℂ) - G) *ᵥ ψ)
          = (((normVec (((1 : Matrix H H ℂ) - G) *ᵥ ψ)) ^ 2 : ℝ) : ℂ) :=
        inner_self_eq_normVec_sq _
      rw [hbbsq0] at hbb
      have h1 : (((normVec (((1 : Matrix H H ℂ) - G) *ᵥ ψ)) ^ 2 : ℝ) : ℂ) = (((0 : ℝ) : ℂ)) := by
        rw [hbb, hgnorm]
        norm_num
      exact_mod_cast h1
    have hb0 : ((1 : Matrix H H ℂ) - G) *ᵥ ψ = 0 :=
      normVec_eq_zero _ (pow_eq_zero_iff (two_ne_zero) |>.mp hbbsq)
    have hψg : G *ᵥ ψ = ψ := by
      have hsum := hgeo.1
      rw [hb0, add_zero] at hsum
      exact hsum
    have hstep : roundOp ψ G *ᵥ ψ = -ψ := by
      obtain ⟨hstepg, _⟩ := round_two_component ψ G hG hψn
      have hψnorm : (normVec ψ) ^ 2 = 1 := by
        show ‖toEuclidean_fromVec ψ‖ ^ 2 = 1
        rw [norm_toEuclidean_fromVec_sq]
        exact hψn
      rw [hψg, hb0, hψnorm] at hstepg
      norm_num at hstepg
      exact hstepg
    rw [pow_mulVec_neg (roundOp ψ G) ψ hstep s, Matrix.mulVec_smul, ha1]
    have hcoeff : (((2 * s + 1 : ℕ) : ℂ) * (((gainLoss (2 * s + 1) 1 : ℝ) : ℂ)))
        = (((-1 : ℂ) ^ s)) := by
      have hgain : gainLoss (2 * s + 1) 1
          = Real.sin (((2 * s + 1 : ℕ) : ℝ) * Real.arcsin 1) / (((2 * s + 1 : ℕ) : ℝ) * 1) := by
        unfold gainLoss
        rw [if_neg (by norm_num : (1:ℝ) ≠ 0)]
      have harc : Real.arcsin (1:ℝ) = Real.pi / 2 := Real.arcsin_one
      have hre : (((2 * s + 1 : ℕ) : ℝ)
          * (Real.sin (((2 * s + 1 : ℕ) : ℝ) * (Real.pi / 2)) / (((2 * s + 1 : ℕ) : ℝ) * 1)))
          = Real.sin (((2 * s + 1 : ℕ) : ℝ) * (Real.pi / 2)) := by
        rcases Nat.eq_zero_or_pos (2 * s + 1) with h | h
        · omega
        · have h0 : ((2 * s + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
          rw [mul_one, mul_div_cancel₀ _ h0]
      have hco : (((2 * s + 1 : ℕ) : ℂ)
          * (((Real.sin (((2 * s + 1 : ℕ) : ℝ) * (Real.pi / 2))
              / (((2 * s + 1 : ℕ) : ℝ) * 1) : ℝ) : ℂ)))
          = (((Real.sin (((2 * s + 1 : ℕ) : ℝ) * (Real.pi / 2)) : ℝ) : ℂ)) :=
        by exact_mod_cast hre
      rw [hgain, harc, hco, sin_nat_mul_pi_div_two]
      rw [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    rw [hcoeff]
  · have ha0l : 0 < a := lt_of_le_of_ne (norm_nonneg _) (ne_comm.mpr ha0)
    have ha1l : a < 1 := lt_of_le_of_ne hgeo.2.2.2.2.2.2.2.2 ha1
    set θ : ℝ := Real.arcsin a with hθ
    have hsinθ : Real.sin θ = a := by
      rw [hθ]
      exact Real.sin_arcsin (by linarith) (by linarith)
    have hθ0 : 0 < θ := by
      rw [hθ]
      exact Real.arcsin_pos.mpr ha0l
    have hθ1 : θ < Real.pi / 2 := by
      rw [hθ]
      exact Real.arcsin_lt_pi_div_two.mpr ha1l
    have hθs : Real.sin θ ^ 2 = (normVec (G *ᵥ ψ)) ^ 2 := by
      rw [hsinθ, ha, hg]
    rw [good_amplified ψ G hG hψn θ s hθ0 hθ1 hθs]
    have hcast : (2 * (s : ℝ) + 1) = ((2 * s + 1 : ℕ) : ℝ) := by norm_num
    have hscalar : (((Real.sin ((2 * (s : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ))
        = (((2 * s + 1 : ℕ) : ℂ) * (((gainLoss (2 * s + 1) a : ℝ) : ℂ))) := by
      have hre : Real.sin ((2 * (s : ℝ) + 1) * θ) / Real.sin θ
          = Real.sin (((2 * s + 1 : ℕ) : ℝ) * Real.arcsin a) / a := by
        rw [hsinθ, hθ, hcast]
      rw [coeff_eq s a ha0l.ne']
      exact_mod_cast hre
    rw [hscalar]

theorem Clause5ActualNestedAmplification_answer : Clause5ActualNestedAmplification := by
  intro H _instF _instD slots U B ω G s hU hlegal hω hG ψ a _hangle
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [aaWord_eq, List.mem_append] at ht
    rcases ht with h | h
    · exact hlegal t h
    · exact legal_flatten_replicate slots B ω G s
        (legal_aaRound slots B ω G hG hω hlegal) t h
  · exact sine_law slots U B ω G s hU hlegal hω hG
  · intro j
    rw [aaWord_eq, calls_append, calls_flatten_replicate, calls_aaRound]
    ring
  · rw [aaWord_eq, gateCount_append, gateCount_flatten_replicate, gateCount_aaRound]
    ring
  · intro prices
    rw [aaWord_eq, weightedCost_append, weightedCost_flatten_replicate,
      weightedCost_aaRound]
    ring

end Qatlib.Concepts.QlsReadoutSpec.Amplification
