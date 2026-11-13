/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Foundations.StandardModel.WindowSim.Theorem2QtmCircuitSimulationStat
import Qatlib.Foundations.StandardModel.WindowSim.GUnitExistenceQuan
import Qatlib.Foundations.StandardModel.WindowSim.OneRoundWindowSimulationQuan
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Quadratic circuit simulation of a quantum Turing machine

This module proves `theorem2QtmCircuitSimulation`, constructing a unitary circuit that simulates
`t` finite-window machine steps using at most `2 * t * t` gates and no oracle queries. The
construction repeats `kRoundCircuit` and preserves the encoded configuration amplitudes and
their Born probabilities.

Local gate unitarity, linearity of the embedding, and bounds on head motion allow the one-round
simulation equality to be iterated from the initial configuration.

The mathematical background is discussed in [Yao1993].

## Main statements

* `gUnitFull_unitary`: lifts unitarity of a local gate to the full register.
* `sim_run`: iterates the simulation under a head-support bound.
* `theorem2QtmCircuitSimulation`: proves the circuit existence and probability agreement
  contract.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

/-- Swapping markers one and two is an involution on cell states. -/
private theorem markSwap_invol {Q A : Type*} :
    Function.Involutive (markSwap : CellState Q A → CellState Q A) := by
  intro r
  rcases r with ⟨m, o, a⟩
  fin_cases m <;> simp [markSwap]

/-- The matrix swapping markers in all register cells is unitary. -/
private theorem iSwapFull_unitary (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] :
    iSwapFull t ∈ Matrix.unitaryGroup (WReg t Q A) ℂ := by
  rw [iSwapFull]
  exact permMatrix_unitary (fun r => funext fun j => markSwap_invol (r j))

/-- The value of a global window-cell index is the starting index plus its local offset. -/
private theorem gUnitCells_val (t : ℕ) (k : Fin (2 * t - 1)) (q : Fin 3) :
    (gUnitCells t k q).val = k.val + q.val := by
  fin_cases q <;> rfl

/-- Distinct local cell offsets select distinct global cells. -/
private theorem gUnitCells_ne {t : ℕ} (k : Fin (2 * t - 1)) {a b : Fin 3}
    (hab : a.val ≠ b.val) : gUnitCells t k a ≠ gUnitCells t k b := by
  intro h
  apply hab
  have hv := congrArg Fin.val h
  simp only [gUnitCells_val] at hv
  omega

/-- Agreement of two registers outside the three cells of the selected local gate. -/
private def gOff {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (k : Fin (2 * t - 1)) (u v : WReg t Q A) : Prop :=
  ∀ j : Fin (2 * t + 1), (∀ q : Fin 3, gUnitCells t k q ≠ j) → u j = v j

private instance instDecidableGOff {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (k : Fin (2 * t - 1)) (u v : WReg t Q A) :
    Decidable (gOff k u v) := by
  unfold gOff
  infer_instance

/-- Agreement outside a gate's active cells is symmetric. -/
private theorem gOff_symm {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (k : Fin (2 * t - 1)) {u v : WReg t Q A}
    (h : gOff k u v) : gOff k v u := fun j hj => (h j hj).symm

/-- Agreement outside a gate's active cells is transitive. -/
private theorem gOff_trans {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (k : Fin (2 * t - 1))
    {u v w : WReg t Q A} (h1 : gOff k u v) (h2 : gOff k v w) : gOff k u w :=
  fun j hj => (h1 j hj).trans (h2 j hj)

/-- A lifted gate entry is the local gate entry when the registers agree outside the active
cells and is zero otherwise. -/
private theorem gUnitFull_apply {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A]
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (k : Fin (2 * t - 1)) (u v : WReg t Q A) :
    gUnitFull G k u v =
      if gOff k u v then G (fun q => u (gUnitCells t k q)) (fun q => v (gUnitCells t k q))
      else 0 := by
  rw [gUnitFull, Matrix.of_apply]
  by_cases h : ∀ j : Fin (2 * t + 1), (∀ q : Fin 3, gUnitCells t k q ≠ j) → u j = v j
  · rw [if_pos h, if_pos (show gOff k u v from h)]
  · rw [if_neg h, if_neg (show ¬gOff k u v from h)]

/-- Insert a three-cell window into a full register while preserving all other cells. -/
private def ofWin (t : ℕ) {Q A : Type*} (k : Fin (2 * t - 1)) (x : WReg t Q A)
    (w : GWindow Q A) : WReg t Q A :=
  fun j => if j = gUnitCells t k 0 then w 0
    else if j = gUnitCells t k 1 then w 1
    else if j = gUnitCells t k 2 then w 2 else x j

/-- Inserting a window gives its prescribed entries at each active cell. -/
private theorem ofWin_cells (t : ℕ) {Q A : Type*} (k : Fin (2 * t - 1)) (x : WReg t Q A)
    (w : GWindow Q A) (q : Fin 3) :
    ofWin t k x w (gUnitCells t k q) = w q := by
  fin_cases q
  · simp [ofWin]
  · simp [ofWin, gUnitCells_ne k (a := 1) (b := 0) (by decide)]
  · simp [ofWin, gUnitCells_ne k (a := 2) (b := 0) (by decide),
      gUnitCells_ne k (a := 2) (b := 1) (by decide)]

/-- Inserting a window leaves every cell outside the active window unchanged. -/
private theorem ofWin_off (t : ℕ) {Q A : Type*} (k : Fin (2 * t - 1)) (x : WReg t Q A)
    (w : GWindow Q A) (j : Fin (2 * t + 1))
    (hj : ∀ q : Fin 3, gUnitCells t k q ≠ j) :
    ofWin t k x w j = x j := by
  simp only [ofWin]
  rw [if_neg (Ne.symm (hj 0)), if_neg (Ne.symm (hj 1)), if_neg (Ne.symm (hj 2))]

/-- A register agrees with the result of a window insertion outside the active cells. -/
private theorem gOff_x_ofWin (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (k : Fin (2 * t - 1)) (x : WReg t Q A)
    (w : GWindow Q A) : gOff k x (ofWin t k x w) :=
  fun j hj => (ofWin_off t k x w j hj).symm

/-- A register agreeing with `x` outside the window is obtained by inserting its own window
entries into `x`. -/
private theorem ofWin_gOff {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (k : Fin (2 * t - 1)) {x y : WReg t Q A}
    (h : gOff k x y) : y = ofWin t k x (fun q => y (gUnitCells t k q)) := by
  funext j
  by_cases h0 : j = gUnitCells t k 0
  · subst h0
    rw [ofWin_cells]
  by_cases h1 : j = gUnitCells t k 1
  · subst h1
    rw [ofWin_cells]
  by_cases h2 : j = gUnitCells t k 2
  · subst h2
    rw [ofWin_cells]
  have hne : ∀ q : Fin 3, gUnitCells t k q ≠ j := by
    intro q hq
    fin_cases q
    · exact h0 hq.symm
    · exact h1 hq.symm
    · exact h2 hq.symm
  rw [ofWin_off t k x _ j hne]
  exact (h j hne).symm

/-- Two full registers are equal if they agree on the active cells and outside those cells. -/
private theorem wreg_ext {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (k : Fin (2 * t - 1)) {x y : WReg t Q A}
    (hcells : ∀ q : Fin 3, x (gUnitCells t k q) = y (gUnitCells t k q))
    (hoff : gOff k x y) : x = y := by
  funext j
  by_cases h0 : j = gUnitCells t k 0
  · subst h0
    exact hcells 0
  by_cases h1 : j = gUnitCells t k 1
  · subst h1
    exact hcells 1
  by_cases h2 : j = gUnitCells t k 2
  · subst h2
    exact hcells 2
  exact hoff j (fun q hq => by
    fin_cases q
    · exact h0 hq.symm
    · exact h1 hq.symm
    · exact h2 hq.symm)

set_option maxHeartbeats 1000000 in

/-- Lifting a unitary three-cell gate to the full register preserves unitarity. -/
private theorem gUnitFull_unitary {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {G : Matrix (GWindow Q A) (GWindow Q A) ℂ}
    (hG : G ∈ Matrix.unitaryGroup (GWindow Q A) ℂ) (k : Fin (2 * t - 1)) :
    gUnitFull G k ∈ Matrix.unitaryGroup (WReg t Q A) ℂ := by
  have hG' : Gᴴ * G = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hG
    exact hG
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x z
  have hentry : ((gUnitFull G k)ᴴ * gUnitFull G k) x z
      = ∑ y : WReg t Q A, star (gUnitFull G k y x) * gUnitFull G k y z := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hentry, Matrix.one_apply]
  by_cases hxz : gOff k x z
  · have key : ∀ y : WReg t Q A,
        star (gUnitFull G k y x) * gUnitFull G k y z
          = if gOff k x y then
              star (G (fun q => y (gUnitCells t k q)) (fun q => x (gUnitCells t k q))) *
              G (fun q => y (gUnitCells t k q)) (fun q => z (gUnitCells t k q))
            else 0 := by
      intro y
      by_cases hy : gOff k x y
      · rw [if_pos hy, gUnitFull_apply, gUnitFull_apply, if_pos (gOff_symm k hy),
          if_pos (gOff_trans k (gOff_symm k hy) hxz)]
      · rw [if_neg hy, gUnitFull_apply, if_neg (fun hc => hy (gOff_symm k hc)),
          star_zero, zero_mul]
    simp only [key]
    have hnb : ∑ y : WReg t Q A, (if gOff k x y then
              star (G (fun q => y (gUnitCells t k q)) (fun q => x (gUnitCells t k q))) *
              G (fun q => y (gUnitCells t k q)) (fun q => z (gUnitCells t k q))
            else 0)
          = ∑ w : GWindow Q A,
            star (G w (fun q => x (gUnitCells t k q))) *
            G w (fun q => z (gUnitCells t k q)) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_nbij (fun y q => y (gUnitCells t k q)) ?_ ?_ ?_ ?_
      · intro y _
        exact Finset.mem_univ _
      · intro y1 h1 y2 h2 heq
        exact wreg_ext k (fun q => congrFun heq q)
          (gOff_trans k (gOff_symm k ((Finset.mem_filter.mp h1).2))
            ((Finset.mem_filter.mp h2).2))
      · intro w _
        exact ⟨ofWin t k x w,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, gOff_x_ofWin t k x w⟩,
          funext fun q => ofWin_cells t k x w q⟩
      · intro y _
        rfl
    rw [hnb]
    have hGG : ∑ w : GWindow Q A,
        star (G w (fun q => x (gUnitCells t k q))) *
        G w (fun q => z (gUnitCells t k q))
        = (Gᴴ * G) (fun q => x (gUnitCells t k q))
          (fun q => z (gUnitCells t k q)) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hGG, hG', Matrix.one_apply]
    by_cases hcells :
        (fun q => x (gUnitCells t k q)) = (fun q => z (gUnitCells t k q))
    · rw [if_pos hcells, if_pos (wreg_ext k (fun q => congrFun hcells q) hxz)]
    · rw [if_neg hcells, if_neg (fun he => hcells (by rw [he]))]
  · have hz : ∀ y ∈ (Finset.univ : Finset (WReg t Q A)),
        star (gUnitFull G k y x) * gUnitFull G k y z = 0 := by
      intro y _
      rw [gUnitFull_apply, gUnitFull_apply]
      by_cases h1 : gOff k y x
      · by_cases h2 : gOff k y z
        · exact absurd (gOff_trans k (gOff_symm k h1) h2) hxz
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, star_zero, zero_mul]
    rw [Finset.sum_eq_zero hz]
    have hex : ∃ j : Fin (2 * t + 1), (∀ q : Fin 3, gUnitCells t k q ≠ j) ∧ x j ≠ z j := by
      by_contra hcon
      apply hxz
      intro j hj
      by_contra hjne
      exact hcon ⟨j, hj, hjne⟩
    obtain ⟨j, hj, hjne⟩ := hex
    have hxzne : x ≠ z := fun he => hjne (by rw [he])
    simp [hxzne]

/-- A circuit formed from a list of gates has gate count equal to the list length and query
count zero. -/
private theorem gateCounts_map_gate {I : Type*} {ι : Type*}
    (l : List ι) (f : ι → Matrix I I ℂ) :
    GateCount (l.map (fun i => Step.gate (f i))) = l.length ∧
      QueryCount (l.map (fun i => Step.gate (f i))) = 0 := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- A list of gate steps forms a unitary circuit when every listed matrix is unitary. -/
private theorem isUnitaryCircuit_map_gate {I : Type*} [Fintype I] [DecidableEq I]
    {ι : Type*} (l : List ι) (f : ι → Matrix I I ℂ)
    (h : ∀ i ∈ l, f i ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (l.map (fun i => Step.gate (f i))) := by
  induction l with
  | nil => exact isUnitaryCircuit_nil
  | cons i l ih =>
    rw [List.map_cons, isUnitaryCircuit_gate]
    exact ⟨h i List.mem_cons_self,
      ih (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))⟩

/-- For positive `t`, one simulation round contains exactly `2 * t` gates. -/
private theorem kRound_gateCount (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (ht : 0 < t) :
    GateCount (kRoundCircuit t G) = 2 * t := by
  have h1 := (gateCounts_map_gate
    (List.finRange (2 * t - 1)) (fun k => gUnitFull G k)).1
  have hlen : (List.finRange (2 * t - 1)).length = 2 * t - 1 := by
    exact List.length_finRange
  simp only [kRoundCircuit, gateCount_append, gateCount_gate, gateCount_nil, hlen, h1]
  omega

/-- One simulation round makes no oracle queries. -/
private theorem kRound_queryCount (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    QueryCount (kRoundCircuit t G) = 0 := by
  have h1 := (gateCounts_map_gate
    (List.finRange (2 * t - 1)) (fun k => gUnitFull G k)).2
  simp only [kRoundCircuit, queryCount_append, queryCount_gate, queryCount_nil, add_zero,
    h1]

/-- A simulation round is a unitary circuit whenever its local gate is unitary. -/
private theorem kRound_isUnitary (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {G : Matrix (GWindow Q A) (GWindow Q A) ℂ}
    (hG : G ∈ Matrix.unitaryGroup (GWindow Q A) ℂ) :
    IsUnitaryCircuit (kRoundCircuit t G) := by
  simp only [kRoundCircuit]
  rw [isUnitaryCircuit_append, isUnitaryCircuit_gate]
  refine ⟨isUnitaryCircuit_map_gate _ _ ?_, iSwapFull_unitary t, isUnitaryCircuit_nil⟩
  intro k _
  exact gUnitFull_unitary hG k

/-- Matrix action distributes over a sum of states indexed by a finite type. -/
private theorem mulVec_sum {I : Type*} [Fintype I] {ι : Type*} [Fintype ι]
    (M : Matrix I I ℂ) (f : ι → QState I) :
    M *ᵥ (∑ i, f i) = ∑ i, M *ᵥ f i := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Running a circuit preserves addition of input states. -/
private theorem run_add {I : Type*} [Fintype I] (oracle : Matrix I I ℂ)
    (C : Circuit I) (ψ χ : QState I) :
    Run oracle C (ψ + χ) = Run oracle C ψ + Run oracle C χ := by
  induction C generalizing ψ χ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [run_gate, ApplyGate, Matrix.mulVec_add]
      exact ih _ _
    | query =>
      simp only [run_query, ApplyGate, Matrix.mulVec_add]
      exact ih _ _

/-- Running a circuit commutes with multiplication of the input state by a complex scalar. -/
private theorem run_smul {I : Type*} [Fintype I] (oracle : Matrix I I ℂ)
    (C : Circuit I) (a : ℂ) (ψ : QState I) :
    Run oracle C (a • ψ) = a • Run oracle C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [run_gate, ApplyGate, Matrix.mulVec_smul]
      exact ih _
    | query =>
      simp only [run_query, ApplyGate, Matrix.mulVec_smul]
      exact ih _

/-- Running a circuit commutes with finite sums of input states. -/
private theorem run_sum {I : Type*} [Fintype I] (oracle : Matrix I I ℂ)
    (C : Circuit I) {ι : Type*} [Fintype ι] (f : ι → QState I) :
    Run oracle C (∑ i, f i) = ∑ i, Run oracle C (f i) := by
  induction C generalizing f with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      have h : U *ᵥ (∑ i, f i) = ∑ i, U *ᵥ f i := mulVec_sum U f
      simp only [run_gate, ApplyGate, h]
      exact ih _
    | query =>
      have h : oracle *ᵥ (∑ i, f i) = ∑ i, oracle *ᵥ f i := mulVec_sum oracle f
      simp only [run_query, ApplyGate, h]
      exact ih _

/-- Every state on a finite basis equals the sum of its amplitudes times the corresponding basis
kets. -/
private theorem ket_sum {I : Type*} [Fintype I] [DecidableEq I] (φ : QState I) :
    (∑ i, φ i • Qatlib.Foundations.PureStateMath.Ket i) = φ := by
  funext j
  have hsum : (∑ i, φ i • Qatlib.Foundations.PureStateMath.Ket i) j = ∑ i, φ i * Qatlib.Foundations.PureStateMath.Ket i j := by
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, Finset.sum_eq_single j
    (fun b _ hb => by simp [ket_apply, Ne.symm hb, mul_zero])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp

/-- The encoding of window configurations into cell registers is injective. -/
private theorem windowEncode_inj {t : ℕ} {Q A : Type*} :
    Function.Injective (windowEncode : WindowCfg t Q A → WReg t Q A) := by
  intro c c' h
  have hhead : c.head = c'.head := by
    by_cases hne : c.head = c'.head
    · exact hne
    · have hmarker := congrArg Prod.fst (congrFun h c.head)
      simp only [windowEncode] at hmarker
      simp [hne] at hmarker
  have hst : c.state = c'.state := by
    have hh := congrFun h c'.head
    simp only [windowEncode] at hh
    rw [hhead] at hh
    simp at hh
    exact hh.1
  have htp : c.tape = c'.tape := by
    funext j
    have hj := congrArg (fun p => p.2.2) (congrFun h j)
    simp only [windowEncode] at hj
    rw [← hhead] at hj
    split at hj <;> simp_all
  rcases c with ⟨hd, st, tp⟩
  rcases c' with ⟨hd', st', tp'⟩
  simp_all

/-- The embedded amplitude at an encoded configuration equals its original amplitude. -/
private theorem windowEmbed_apply {t : ℕ} {Q A : Type*} (φ : QState (WindowCfg t Q A))
    (c : WindowCfg t Q A) : windowEmbed φ (windowEncode c) = φ c :=
  windowEncode_inj.extend_apply φ 0 c

/-- The embedded amplitude is zero on a register that encodes no configuration. -/
private theorem windowEmbed_apply' {t : ℕ} {Q A : Type*} (φ : QState (WindowCfg t Q A))
    (z : WReg t Q A) (hz : ∀ c, windowEncode c ≠ z) : windowEmbed φ z = 0 :=
  Function.extend_apply' φ (0 : WReg t Q A → ℂ) z (fun ⟨c, he⟩ => hz c he)

/-- Embedding a configuration ket gives the ket of its register encoding. -/
private theorem windowEmbed_ket {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (c : WindowCfg t Q A) :
    windowEmbed (Qatlib.Foundations.PureStateMath.Ket c) = Qatlib.Foundations.PureStateMath.Ket (windowEncode c) := by
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    rw [windowEmbed_apply]
    by_cases hc : c₀ = c
    · subst hc
      simp
    · simp [ket_apply, hc, windowEncode_inj.ne hc]
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩)]
    have hzne : z ≠ windowEncode c := fun h => hz ⟨c, h.symm⟩
    simp [ket_apply, hzne]

/-- An embedded state is the sum of encoded configuration kets weighted by the original
amplitudes. -/
private theorem windowEmbed_eq_sum {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (φ : QState (WindowCfg t Q A)) :
    windowEmbed φ = ∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c) := by
  have hsum : ∀ z : WReg t Q A,
      (∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) z = ∑ c, φ c * Qatlib.Foundations.PureStateMath.Ket (windowEncode c) z := by
    intro z
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    rw [windowEmbed_apply, hsum, Finset.sum_eq_single c₀
      (fun b _ hb => by
        simp [ket_apply, Ne.symm (windowEncode_inj.ne hb), mul_zero])
      (fun hj => absurd (Finset.mem_univ c₀) hj)]
    simp
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩), hsum, Finset.sum_eq_zero]
    intro c _
    have hzne : z ≠ windowEncode c := fun h => hz ⟨c, h.symm⟩
    simp [ket_apply, hzne]

/-- The window embedding commutes with arbitrary finite sums of configuration states. -/
private theorem windowEmbed_sum_gen {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {ι : Type*} [Fintype ι]
    (F : ι → QState (WindowCfg t Q A)) :
    windowEmbed (∑ i, F i) = ∑ i, windowEmbed (F i) := by
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    rw [windowEmbed_apply]
    simp [windowEmbed_apply]
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩), Finset.sum_apply,
      Finset.sum_eq_zero]
    intro i _
    rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩)]

/-- The window embedding commutes with complex scalar multiplication. -/
private theorem windowEmbed_smul {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (a : ℂ)
    (φ : QState (WindowCfg t Q A)) :
    windowEmbed (a • φ) = a • windowEmbed φ := by
  funext z
  by_cases hz : ∃ c₀, windowEncode c₀ = z
  · obtain ⟨c₀, hzc⟩ := hz
    subst hzc
    simp only [windowEmbed_apply, Pi.smul_apply, smul_eq_mul]
  · rw [windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩)]
    simp only [Pi.smul_apply, smul_eq_mul,
      windowEmbed_apply' _ _ (fun c₀ hc => hz ⟨c₀, hc⟩), mul_zero]

/-- A successful head move changes the head index by minus one, zero, or plus one according to
its direction. -/
private theorem moveCell_spec {t : ℕ} (d : QtmMove) (h h' : Fin (2 * t + 1))
    (hh : moveCell d h = some h') :
    (d = QtmMove.left → h'.val + 1 = h.val) ∧ (d = QtmMove.stay → h'.val = h.val) ∧
      (d = QtmMove.right → h'.val = h.val + 1) := by
  cases d with
  | left =>
    simp only [moveCell] at hh
    split at hh
    · exact absurd hh (by simp)
    · simp only [Option.some.injEq] at hh
      subst hh
      refine ⟨fun _ => by show h.val - 1 + 1 = h.val; omega,
        fun hc => QtmMove.noConfusion hc, fun hc => QtmMove.noConfusion hc⟩
  | stay =>
    simp only [moveCell, Option.some.injEq] at hh
    subst hh
    exact ⟨fun hc => QtmMove.noConfusion hc, fun _ => rfl,
      fun hc => QtmMove.noConfusion hc⟩
  | right =>
    simp only [moveCell] at hh
    split at hh
    · exact absurd hh (by simp)
    · simp only [Option.some.injEq] at hh
      subst hh
      exact ⟨fun hc => QtmMove.noConfusion hc, fun hc => QtmMove.noConfusion hc,
        fun _ => rfl⟩

/-- Every configuration with nonzero output amplitude has a contributing input configuration
with nonzero amplitude whose head is at most one cell away. -/
private theorem windowStep_support {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (β : QState (WindowCfg t Q A))
    (c' : WindowCfg t Q A) (hβ : (windowStep M *ᵥ β) c' ≠ 0) :
    ∃ c : WindowCfg t Q A, β c ≠ 0 ∧
      c.head.val ≤ c'.head.val + 1 ∧ c'.head.val ≤ c.head.val + 1 := by
  have hsum : ∑ c : WindowCfg t Q A, windowStep M c' c * β c ≠ 0 := by
    simpa [Matrix.mulVec, dotProduct] using hβ
  obtain ⟨c, _, hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hne : windowStep M c' c ≠ 0 := fun h => hnz (by simp [h])
  have hb : c.head.val ≤ c'.head.val + 1 ∧ c'.head.val ≤ c.head.val + 1 := by
    simp only [windowStep, Matrix.of_apply] at hne
    obtain ⟨d, -, hd2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨q', -, hq3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd2
    obtain ⟨b, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq3
    by_cases hcond : moveCell d c.head = some c'.head ∧ c'.state = q' ∧
        ∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j
    · rw [if_pos hcond] at hterm
      obtain ⟨hm, -, -⟩ := hcond
      rcases moveCell_spec d c.head c'.head hm with ⟨hl, hs, hr⟩
      cases d with
      | left =>
        have hlr := hl rfl
        omega
      | stay =>
        have hsr := hs rfl
        omega
      | right =>
        have hrr := hr rfl
        omega
    · rw [if_neg hcond] at hterm
      exact absurd hterm (by simp)
  exact ⟨c, fun h0 => hnz (by simp [h0]), hb.1, hb.2⟩

/-- A simulation round agrees with the embedded machine step on every state supported on
interior head positions, assuming the local gate contracts. -/
private theorem round_embed {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (ht : 0 < t) (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (hfix : GUnitFixesH M G) (hstep : GUnitSteps M G)
    (φ : QState (WindowCfg t Q A))
    (hgood : ∀ c, φ c ≠ 0 → 0 < c.head.val ∧ c.head.val < 2 * t) :
    Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G) (windowEmbed φ)
      = windowEmbed (windowStep M *ᵥ φ) := by
  have key : ∀ c : WindowCfg t Q A,
      φ c • Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (Qatlib.Foundations.PureStateMath.Ket (windowEncode c))
        = φ c • windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) := by
    intro c
    by_cases hc : φ c = 0
    · rw [hc, zero_smul, zero_smul]
    · rw [oneRoundWindowSimulation Q A M t ht G hfix hstep c
        (hgood c hc).1 (hgood c hc).2]
  calc Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G) (windowEmbed φ)
      = Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) := by rw [windowEmbed_eq_sum]
    _ = ∑ c, Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (φ c • Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) := by rw [run_sum]
    _ = ∑ c, φ c • Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
          (Qatlib.Foundations.PureStateMath.Ket (windowEncode c)) := by
          exact Finset.sum_congr rfl fun c _ => run_smul _ _ _ _
    _ = ∑ c, φ c • windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) :=
        Finset.sum_congr rfl fun c _ => key c
    _ = windowEmbed (∑ c, φ c • windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c) := by
          rw [windowEmbed_sum_gen]
          exact Finset.sum_congr rfl fun c _ => (windowEmbed_smul _ _).symm
    _ = windowEmbed (windowStep M *ᵥ ∑ c, φ c • Qatlib.Foundations.PureStateMath.Ket c) := by
          rw [mulVec_sum]
          exact congrArg _ (Finset.sum_congr rfl fun c _ =>
            (Matrix.mulVec_smul _ _ _).symm)
    _ = windowEmbed (windowStep M *ᵥ φ) := by rw [ket_sum]

/-- A machine step enlarges a head-support interval of radius `r` about cell `t` to radius `r +
1`. -/
private theorem good_step {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (M : LocalQTM Q A) {r : ℕ}
    (φ : QState (WindowCfg t Q A))
    (hg : ∀ c, φ c ≠ 0 → t ≤ c.head.val + r ∧ c.head.val ≤ t + r) :
    ∀ c, (windowStep M *ᵥ φ) c ≠ 0 →
      t ≤ c.head.val + (r + 1) ∧ c.head.val ≤ t + (r + 1) := by
  intro c' hc'
  obtain ⟨c, hc0, hb1, hb2⟩ := windowStep_support M φ c' hc'
  obtain ⟨hA, hB⟩ := hg c hc0
  exact ⟨by omega, by omega⟩

/-- Repeating the simulation round `k` times implements `windowStep ^ k` on embedded states
supported within radius `r` of the center when `k + r ≤ t`. -/
private theorem sim_run {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (ht : 0 < t) (M : LocalQTM Q A)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (hfix : GUnitFixesH M G) (hstep : GUnitSteps M G) :
    ∀ (k : ℕ), k ≤ t → ∀ (r : ℕ), k + r ≤ t → ∀ φ : QState (WindowCfg t Q A),
      (∀ c, φ c ≠ 0 → t ≤ c.head.val + r ∧ c.head.val ≤ t + r) →
      Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ)
          (RepeatCircuit (kRoundCircuit t G) k) (windowEmbed φ)
        = windowEmbed (windowStep M ^ k *ᵥ φ) := by
  intro k
  induction k with
  | zero =>
    intro _ r _ φ _
    simp only [RepeatCircuit, run_nil, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    intro hkle r hkr φ hg
    have hk : k ≤ t := Nat.le_trans (Nat.le_succ k) hkle
    have hgood : ∀ c, φ c ≠ 0 → 0 < c.head.val ∧ c.head.val < 2 * t := by
      intro c hc
      obtain ⟨hA, hB⟩ := hg c hc
      omega
    simp only [RepeatCircuit]
    rw [run_append, round_embed ht M G hfix hstep φ hgood,
      ih hk (r + 1) (by omega) (windowStep M *ᵥ φ) (good_step M φ hg),
      Matrix.mulVec_mulVec, pow_succ]

/-- For positive input length `n ≤ t`, a unitary circuit with no queries and at most `2 * t * t`
gates simulates `t` machine steps from every initialized input and matches encoded
configuration Born probabilities. See [Yao1993]. -/
theorem theorem2QtmCircuitSimulation : Theorem2QtmCircuitSimulation := by
  intro Q _ _ A _ _ M n t hn ht hnt
  obtain ⟨G, hGunit, hGfix, hGstep⟩ := gUnitExistence Q A M
  refine ⟨RepeatCircuit (kRoundCircuit t G) t,
    (kRound_isUnitary t hGunit).repeatCircuit t, ?_, ?_, ?_⟩
  · rw [queryCount_repeatCircuit, kRound_queryCount, mul_zero]
  · rw [gateCount_repeatCircuit, kRound_gateCount t G ht, Nat.mul_comm t (2 * t)]
  · intro x c
    have hc₀ : (initWindowCfg (t := t) M n x).head.val = t := rfl
    have hgood0 : ∀ c, (Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := t) M n x)) c ≠ 0 →
        t ≤ c.head.val + 0 ∧ c.head.val ≤ t + 0 := by
      intro c hc
      simp only [ket_apply] at hc
      by_cases hcc : c = initWindowCfg (t := t) M n x
      · subst hcc
        omega
      · rw [if_neg hcc] at hc
        exact absurd rfl hc
    have hrun := sim_run ht M G hGfix hGstep t (le_refl t) 0 (by omega)
      (Qatlib.Foundations.PureStateMath.Ket (initWindowCfg (t := t) M n x)) hgood0
    rw [windowEmbed_ket] at hrun
    refine ⟨hrun, ?_⟩
    rw [hrun]
    simp only [BornProb, windowEmbed_apply]

end Qatlib.Foundations.StandardDefs.WindowSim
