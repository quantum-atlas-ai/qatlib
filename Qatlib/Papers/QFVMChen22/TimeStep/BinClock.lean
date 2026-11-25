/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinProgramReadout
public import Qatlib.Concepts.QlsReadoutSpec.Amplification.AmplificationProductsLows
public import Qatlib.Concepts.QlsReadoutSpec.Amplification.StoppedStageTransportLows
public import Qatlib.Concepts.QlsReadoutSpec.Amplification.OptimizedTunableConsumerLows
public import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation

@[expose] public section

/-!
# Stopping projectors for the staged stencil solver

[ChenXueChenEtAl2022], Appendix C.3, refers to a variable-time linear solver.
The clock projectors are coordinate projections onto tapes that accepted
before the next stage. The final projection includes every tape. The bin
stages satisfy the fixed-subspace condition of the variable-time
amplification contract, and a diagonal bad event commutes with the clock.
The final potential detects the Born mass of the physical success event.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath (Ket MeasureProb QState applyGate_eq_mulVec_ket applyGate_one ket_apply)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse PostMeasure Projector projector_univ measureProb_collapse)
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement (IsOrthogonalProjector projector_isOrthogonalProjector)
open Qatlib.Foundations.QueryWordCore.Circuit (Run run_gate run_nil)
open Qatlib.Concepts.BlockEncoding.Postselection (stateVector_norm_sq)
open Qatlib.Concepts.SketchArith.GramAction (toEuclidean_postMeasure_eq_normalize)
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel (wordMatrix_append)
open Qatlib.Concepts.QlsReadoutSpec.Amplification
  (clockLegal stageLegal Clause2ProjectorOrder_answer Clause4StoppedStageTransport_answer
    OptimizedTunableOptimizedTunableConsumer_answer extendClock plainAmplitude tunable legal
    nestedWord postAmplitude weightedCost quasinorm23 clockState plainPrefix potential normVec
    Word wordMatrix controlled clean run lam totalLoss amplification_products_invariant
    amplification_products_intended)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators Classical ComplexOrder

variable {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]

/-- Before the end of the clock, a coordinate is stopped precisely when an earlier
decision accepted. All coordinates stop at the final time. -/
def binStoppedSet (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) (elapsed : ℕ) :
    Finset (BinStageWorkspace width condition precision M) :=
  Finset.univ.filter fun p =>
    n ≤ elapsed ∨ ∃ s : Fin n, s.val < elapsed ∧ (p.1 s).1 = true

/-- The coordinate projection onto tapes that have stopped by this time. -/
def binClockProjection (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ)
    (elapsed : Fin (n + 1)) :
    Matrix (BinStageWorkspace width condition precision M) (BinStageWorkspace width condition precision M) ℂ :=
  Projector (binStoppedSet width condition precision elapsed.val)

/-- Coordinate projections multiply to the smaller projection when their coordinate sets
are nested. -/
private theorem projector_mul_of_subset {X : Type} [Fintype X] [DecidableEq X]
    (S T : Finset X) (h : S ⊆ T) : Projector T * Projector S = Projector S := by
  unfold Projector
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases hp : p ∈ S
  · simp [hp, h hp]
  · simp [hp]

/-- The clock of a positive-length bin schedule is legal with any diagonal bad event. -/
theorem bin_clock_legal (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) (hn : 0 < n)
    (bad : Finset (BinStageWorkspace width condition precision M)) :
    clockLegal n (binClockProjection width condition precision) (Projector bad) := by
  let P := binClockProjection (M := M) width condition precision
  have hP (j : Fin (n + 1)) : IsOrthogonalProjector (P j) :=
    projector_isOrthogonalProjector (binStoppedSet width condition precision j.val)
  refine ⟨hP, ?_, ?_, ?_, projector_isOrthogonalProjector bad, ?_⟩
  · simp [binClockProjection, binStoppedSet, Nat.not_le_of_lt hn, Projector]
  · simp [binClockProjection, binStoppedSet, projector_univ]
  · intro j k hjk
    have hSub : binStoppedSet (M := M) width condition precision j.val ⊆
        binStoppedSet width condition precision k.val := by
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases h with h | ⟨s, hs, ha⟩
      · exact Or.inl (h.trans hjk)
      · exact Or.inr ⟨s, hs.trans_le hjk, ha⟩
    exact ((Clause2ProjectorOrder_answer _ (P j) (P k) (hP j) (hP k)).2.2.2.2.2.1).mp
      (projector_mul_of_subset _ _ hSub)
  · intro j
    simp only [binClockProjection, Projector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    exact mul_comm _ _

variable {N : Type} [Fintype N] [DecidableEq N]

/-- Slot zero is the identity. Positive slots execute the corresponding bin stage in
clock order. -/
def binStageOracle (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ) (slot : ℕ) :
    Matrix (BinStageWorkspace width condition precision M) (BinStageWorkspace width condition precision M) ℂ :=
  if h : 0 < slot ∧ slot - 1 < n then
    let t : Fin n := ⟨slot - 1, h.2⟩
    stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U
  else 1

omit [DecidableEq N] in
/-- The successor slot calls the matching stage. -/
theorem bin_stage_oracle_succ (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ) (t : Fin n) :
    binStageOracle width condition threshold precision C U (t.val + 1) =
      stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) C U := by
  simp [binStageOracle, t.isLt]

/-- The stage oracle is unitary and fixes the preceding clock subspace at every call. -/
theorem bin_stage_legal (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1) (hWidth : ∀ t, 0 < width t) :
    stageLegal n (binClockProjection width condition precision)
      (binStageOracle width condition threshold precision C U) := by
  let V := binStageOracle width condition threshold precision C U
  let P := binClockProjection (M := M) width condition precision
  obtain ⟨hPos, hMass⟩ := common_bin_mass_bounds condition precision
  have hLocal (t : Fin n) := stencil_bin_stage_unitary width condition precision
    (commonBinMass condition precision) t (threshold t) C U hC hSelf hSq (hWidth t) hPos (hMass t)
  have hUnitary (slot : Fin (n + 1)) : V slot.val ∈ Matrix.unitaryGroup _ ℂ := by
    dsimp only [V, binStageOracle]
    split_ifs with h
    · exact hLocal ⟨slot.val - 1, h.2⟩
    · exact Submonoid.one_mem _
  refine ⟨hUnitary, ?_⟩
  intro t
  let prev : Fin (n + 1) := ⟨t.val, by omega⟩
  let next : Fin (n + 1) := ⟨t.val + 1, by omega⟩
  let S := binStoppedSet (M := M) width condition precision t.val
  have hProj : IsOrthogonalProjector (P prev) := projector_isOrthogonalProjector S
  change V next.val * P prev = P prev
  apply ((Clause4StoppedStageTransport_answer.1 _ (P prev) (V next.val) hProj (hUnitary next)).1).mpr
  change Projector S * V (t.val + 1) = Projector S
  rw [show V (t.val + 1) = _ from bin_stage_oracle_succ width condition threshold precision C U t]
  ext p q
  simp only [Projector, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hp : p ∈ S
  · have hStopped : ∃ s : Fin n, s < t ∧ (p.1 s).1 = true := by
      have h := (Finset.mem_filter.mp hp).2
      exact h.resolve_left (Nat.not_le_of_lt t.isLt)
    have hEntry := stencil_bin_stage_stopped width condition precision (commonBinMass condition precision)
      t (threshold t) C U (Ket q) p hStopped
    rw [applyGate_eq_mulVec_ket, ket_apply] at hEntry
    simp only [hp, ite_true, one_mul, hEntry]
  · simp [hp]

/-- Coordinates treated as failures when the final stage has stopped all branches. -/
def stencilBinFailure {depth rows columns : ℕ} (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) :
    Finset (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns)) :=
  Finset.univ.filter fun p => p ∉ stencilBinSuccess rowScratch columnScratch width condition precision

/-- The final clock potential is the projection onto the selected success coordinates. -/
theorem bin_terminal_potential {depth rows columns : ℕ} (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ) :
    potential
        (extendClock n (binClockProjection (M := StencilWorkspace depth rows columns) width condition precision) n)
        (Projector (stencilBinFailure rowScratch columnScratch width condition precision)) =
      Projector (stencilBinSuccess rowScratch columnScratch width condition precision) := by
  have hLast : extendClock n
      (binClockProjection (M := StencilWorkspace depth rows columns) width condition precision) n = 1 := by
    simp [extendClock, binClockProjection, binStoppedSet, projector_univ]
  rw [potential, hLast, Matrix.one_mul]
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases hp : p ∈ stencilBinSuccess rowScratch columnScratch width condition precision <;>
      simp [Projector, stencilBinFailure, hp]
  · simp [Projector, hpq]

/-- A fully enabled call on the one-value clock acts on the data state and leaves the clock clean. -/
private theorem controlled_clean_data {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (ψ : QState H) :
    controlled V Finset.univ *ᵥ clean 1 Nat.zero_lt_one ψ = clean 1 Nat.zero_lt_one (V *ᵥ ψ) := by
  funext p
  rcases p with ⟨h, k⟩
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  change (∑ t : H × Fin 1, controlled V Finset.univ (h, (0 : Fin 1)) t * clean 1 Nat.zero_lt_one ψ t) = _
  rw [Fintype.sum_prod_type]
  have hInner (h' : H) :
      (∑ k' : Fin 1, controlled V Finset.univ (h, (0 : Fin 1)) (h', k') * clean 1 Nat.zero_lt_one ψ (h', k')) =
        V h h' * ψ h' := by
    rw [Fin.sum_univ_one]
    simp [controlled, clean]
  rw [Finset.sum_congr rfl fun h' _ => hInner h']
  change (V *ᵥ ψ) h = clean 1 Nat.zero_lt_one (V *ᵥ ψ) (h, (0 : Fin 1))
  simp [clean]

/-- Forward calls on the unique clock slice execute the same gates in the same order. -/
private theorem clock_state_forward_calls {H : Type} [Fintype H] [DecidableEq H]
    (V : ℕ → Matrix H H ℂ) (slots : List ℕ) (ψ : QState H) :
    clockState V (slots.map fun i => .call i Finset.univ false) ψ =
      Run 1 (slots.map fun i => .gate (V i)) ψ := by
  induction slots generalizing ψ with
  | nil =>
    rw [List.map_nil, List.map_nil, run_nil]
    funext h
    change ((1 : Matrix (H × Fin 1) (H × Fin 1) ℂ) *ᵥ clean 1 Nat.zero_lt_one ψ) (h, (0 : Fin 1)) = ψ h
    rw [Matrix.one_mulVec]
    simp [clean]
  | cons i slots ih =>
    have hCall : wordMatrix V ([.call i Finset.univ false] : Word H 1) = controlled (V i) Finset.univ := by
      simp [wordMatrix]
    change clockState V (([.call i Finset.univ false] : Word H 1) ++
      slots.map (fun j => .call j Finset.univ false)) ψ = Run 1 (.gate (V i) :: slots.map (fun j => .gate (V j))) ψ
    rw [run_gate]
    change _ = Run 1 (slots.map fun j => .gate (V j)) (V i *ᵥ ψ)
    rw [← ih]
    funext h
    unfold clockState run
    rw [wordMatrix_append, hCall, ← Matrix.mulVec_mulVec, controlled_clean_data]

/-- Erasing the bounds from the successive finite indices gives the corresponding natural indices. -/
private theorem fin_range_val (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.finRange_succ, List.range_succ_eq_map, List.map_cons, List.map_map, ← ih, List.map_map]
    rfl

/-- The plain clock word executes the actual staged stencil on the cached QRAM residual. -/
theorem stencil_bin_plain_state {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ) :
    let G := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let V := binStageOracle width condition threshold precision G U
    let initial := stencilBinInput rowScratch columnScratch residual width hWidth condition precision
    clockState V (plainPrefix n) initial =
      stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual width hWidth condition
        threshold precision := by
  intro G U V initial
  have hZero : V 0 = 1 := by simp [V, binStageOracle]
  unfold plainPrefix stencilBinOutput encodedStencilBinProgram encodedStencilBinGates
  rw [clock_state_forward_calls, List.range_succ_eq_map, List.map_cons, run_gate, hZero, applyGate_one]
  rw [← fin_range_val n]
  simp only [List.map_map]
  change Run 1 ((List.finRange n).map fun t => .gate (V (t.val + 1))) initial =
    Run 1 ((List.finRange n).map fun t => .gate
      (stencilBinStage width condition precision (commonBinMass condition precision) t (threshold t) G U)) initial
  congr 1
  apply List.map_congr_left
  intro t _
  rw [show V (t.val + 1) = _ from bin_stage_oracle_succ width condition threshold precision G U t]

/-- The terminal good amplitude squared is the measured success mass for any state on the bin workspace. -/
theorem bin_terminal_amplitude_sq {depth rows columns : ℕ} (rowScratch : Fin rows) (columnScratch : Fin columns)
    (width : Fin n → ℕ) (condition : Fin n → ℝ) (precision : ℝ)
    (ψ : QState (BinStageWorkspace width condition precision (StencilWorkspace depth rows columns))) :
    (normVec (potential
      (extendClock n (binClockProjection (M := StencilWorkspace depth rows columns) width condition precision) n)
      (Projector (stencilBinFailure rowScratch columnScratch width condition precision)) *ᵥ ψ)) ^ 2 =
        MeasureProb ψ (stencilBinSuccess rowScratch columnScratch width condition precision) := by
  rw [bin_terminal_potential]
  change ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector
    (Collapse ψ (stencilBinSuccess rowScratch columnScratch width condition precision))‖ ^ 2 = _
  rw [stateVector_norm_sq, measureProb_collapse, Finset.inter_univ]

/-- The square of the raw amplitude used by the amplifier equals the Born mass of stencil success. -/
theorem stencil_bin_plain_amplitude_sq {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns) (residual : Tree ℝ depth)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ) :
    let G := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let P := binClockProjection (M := StencilWorkspace depth geometry.stencilSize columns) width condition precision
    let V := binStageOracle width condition threshold precision G U
    let bad := Projector (stencilBinFailure (depth := depth) rowScratch columnScratch width condition precision)
    let initial := stencilBinInput rowScratch columnScratch residual width hWidth condition precision
    plainAmplitude (extendClock n P) bad V initial n ^ 2 =
      MeasureProb (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual width hWidth
        condition threshold precision) (stencilBinSuccess rowScratch columnScratch width condition precision) := by
  intro G U P V bad initial
  unfold plainAmplitude
  rw [bin_terminal_amplitude_sq, stencil_bin_plain_state]

set_option maxHeartbeats 1200000 in
/-- A positive raw success probability enables variable-time amplification of the actual encoded
stencil with the cached residual. The amplified word has physical success probability at least
`1/100` and preserves the entire conditional state on the success event. The charge assigns the
given price to each slot. -/
theorem encoded_stencil_bin_amplification {depth columns : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columns)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hResidual : 0 < mass residual)
    (width : Fin n → ℕ) (condition threshold : Fin n → ℝ) (precision : ℝ) (prices : ℕ → ℕ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columns)
    (hn : 0 < n) (hWidth : ∀ t, 0 < width t) :
    let G := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let P := binClockProjection (M := StencilWorkspace depth geometry.stencilSize columns) width condition precision
    let V := binStageOracle width condition threshold precision G U
    let bad := Projector (stencilBinFailure (depth := depth) rowScratch columnScratch width condition precision)
    let E := extendClock n P
    let initial := stencilBinInput rowScratch columnScratch residual width hWidth condition precision
    let a := plainAmplitude E bad V initial n
    let success := stencilBinSuccess (depth := depth) rowScratch columnScratch width condition precision
    0 < MeasureProb (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual width hWidth
        condition threshold precision) success →
      ∃ K : ℝ, 0 < K ∧ ∃ (α : ℕ → ℝ) (rs : ℕ → ℕ),
        tunable n E bad V initial α rs ∧
        (∀ j : Fin n, α (j.val + 1) ≤ 1) ∧ (∑ j : Fin n, α (j.val + 1)) ≤ 1 ∧
        legal (n + 1) (nestedWord E bad initial rs n) ∧ 1 / 10 ≤ postAmplitude E bad initial V rs n ∧
        1 / 100 ≤ MeasureProb (clockState V (nestedWord E bad initial rs n) initial) success ∧
        (weightedCost prices (nestedWord E bad initial rs n) : ℝ) ≤ K / a *
          (((prices 0 + prices 1 : ℕ) : ℝ) + quasinorm23 (fun j : Fin (n - 1) =>
            plainAmplitude E bad V initial (j.val + 1) * prices (j.val + 2))) ∧
        PostMeasure (clockState V (nestedWord E bad initial rs n) initial) success =
          PostMeasure (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
            residual width hWidth condition threshold precision) success := by
  intro G U P V bad E initial a success hRaw
  have hSquare : a ^ 2 = MeasureProb (stencilBinOutput geometry coefficients entryScale rowScratch columnScratch
    residual width hWidth condition threshold precision) success :=
    stencil_bin_plain_amplitude_sq geometry coefficients entryScale rowScratch columnScratch residual width hWidth
      condition threshold precision
  have ha : 0 < a := by
    have hNonneg : 0 ≤ a := norm_nonneg _
    by_contra hp
    have hZero : a = 0 := le_antisymm (le_of_not_gt hp) hNonneg
    rw [← hSquare, hZero] at hRaw
    norm_num at hRaw
  obtain ⟨hG, hSelf, hSq, _⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hClock : clockLegal n P bad :=
    bin_clock_legal width condition precision hn (stencilBinFailure rowScratch columnScratch width condition precision)
  have hStages : stageLegal n P V := bin_stage_legal width condition threshold precision G U hG hSelf hSq hWidth
  have hInitial := stencil_bin_input_normalized rowScratch columnScratch residual
    hValid hResidual width hWidth condition precision hG
  obtain ⟨K, hK, hUniversal⟩ := OptimizedTunableOptimizedTunableConsumer_answer
  obtain ⟨α, rs, hTunable, hThreshold, hSum, hLegal, hAmp, hCost⟩ :=
    hUniversal _ n P bad V initial prices hn hClock hStages hInitial ha
  let amplified := clockState V (nestedWord E bad initial rs n) initial
  let raw := stencilBinOutput geometry coefficients entryScale rowScratch columnScratch residual width hWidth
    condition threshold precision
  refine ⟨K, hK, α, rs, hTunable, hThreshold, hSum, hLegal, hAmp, ?_, hCost, ?_⟩
  · have hMeasured := bin_terminal_amplitude_sq rowScratch columnScratch width condition precision amplified
    change postAmplitude E bad initial V rs n ^ 2 = _ at hMeasured
    rw [← hMeasured]
    calc
      (1 / 100 : ℝ) = (1 / 10 : ℝ) ^ 2 := by norm_num
      _ ≤ postAmplitude E bad initial V rs n ^ 2 :=
        (sq_le_sq₀ (by norm_num) (by linarith)).mpr hAmp
  · let gain := ∏ k : Fin n, lam E bad V initial rs k.val
    let oddProduct : ℝ := ((∏ k : Fin n, (2 * rs (k.val + 1) + 1)) : ℕ)
    let loss := totalLoss n E bad V initial rs
    have hOdds : 0 < oddProduct := by
      have hp : 0 < ∏ k : Fin n, (2 * rs (k.val + 1) + 1) :=
        Finset.prod_pos fun _ _ => by omega
      exact Nat.cast_pos.mpr hp
    have hGainProduct : gain = oddProduct * loss := by
      dsimp only [gain, oddProduct, loss, lam, totalLoss]
      rw [Finset.prod_mul_distrib, Nat.cast_prod]
    have hRatio := (amplification_products_intended n P bad V initial α rs hClock hStages hInitial
      ha hTunable hThreshold).2.2
    change oddProduct = postAmplitude E bad initial V rs n / (a * loss) at hRatio
    have hDen : a * loss ≠ 0 := fun h => hOdds.ne' (by simpa only [h, div_zero] using hRatio)
    have hGainAmp : gain * a = postAmplitude E bad initial V rs n := by
      rw [hGainProduct, mul_assoc, mul_comm loss a]
      exact (eq_div_iff hDen).mp hRatio
    have hGain : 0 < gain := (mul_pos_iff_of_pos_right ha).mp (by rw [hGainAmp]; linarith)
    have hSelected := amplification_products_invariant n P bad V initial α rs hClock hStages hInitial
      hTunable hThreshold n le_rfl
    rw [← Complex.ofReal_prod,
      bin_terminal_potential rowScratch columnScratch width condition precision,
      stencil_bin_plain_state geometry coefficients entryScale rowScratch columnScratch
        residual width hWidth condition threshold precision] at hSelected

    change Collapse amplified success = (gain : ℂ) • Collapse raw success at hSelected
    have hScale : toEuclidean_fromVec ((gain : ℂ) • Collapse raw success) =
        gain • toEuclidean_fromVec (Collapse raw success) :=
      (WithLp.toLp_smul 2 (gain : ℂ) (Collapse raw success)).trans
        (RCLike.real_smul_eq_coe_smul (K := ℂ) gain (toEuclidean_fromVec (Collapse raw success))).symm
    have he := toEuclidean_postMeasure_eq_normalize amplified success
    rw [hSelected, hScale, NormedSpace.normalize_smul_of_pos hGain, ← toEuclidean_postMeasure_eq_normalize] at he
    exact congrArg WithLp.ofLp he

end Qatlib.Papers.QFVMChen22.TimeStep
