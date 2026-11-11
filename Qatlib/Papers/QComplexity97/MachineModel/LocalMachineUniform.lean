/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QComplexity97.MachineModel.LocalMachineUniformDefs

/-!
# Local well-formedness and the normal-form control schedule

The module checks the local normalization and orthogonality conditions for `nfRule`, using
disjoint supports and the two Hadamard scan rows. It constructs `nfRule_toLocal` and proves that
all stay amplitudes vanish.

The deterministic control trace `nfCtrlRun` is evaluated through its forward scan, return scan,
and final three moves. `clause4_complete` collects the local conditions and the exact `2 * n +
4` schedule returning to cell one. See [BernsteinVazirani1997].

## Main statements

* `nfRule_localWellformed`: verifies the five local well-formedness conditions.
* `nfCtrlRun_halt`: evaluates the control trace at its budget.
* `clause4_complete`: collects the local and control-schedule results.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Papers.QComplexity97.MachineDefs.LocalMachineUniform

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace LocalMachineUniform

/-- The transition amplitude of `nfRule` vanishes outside `nfSupport`. -/
theorem nfStep_eq_zero_off {q : NFState} {a : FourierSymbol} {d : QtmMove} {q' : NFState}
    {b : FourierSymbol} (h : (d, q', b) ∉ nfSupport q a) :
    nfRule.step q a d q' b = 0 := by
  simp [nfRule, h]

/-- Every nonzero transition amplitude of `nfRule` has its slot in `nfSupport`. -/
theorem nfStep_mem_of_ne_zero {q : NFState} {a : FourierSymbol} {d : QtmMove} {q' : NFState}
    {b : FourierSymbol} (h : nfRule.step q a d q' b ≠ 0) :
    (d, q', b) ∈ nfSupport q a := by
  simp only [nfRule, nfValue] at h
  split_ifs at h with hc
  · exact hc
  · exact absurd h (by simp)

/-- Every transition slot in `nfSupport q a` moves left or right rather than staying. -/
theorem nfSupport_no_stay (q : NFState) (a : FourierSymbol) :
    ∀ slot ∈ nfSupport q a, slot.1 ≠ QtmMove.stay := by
  cases q <;> cases a <;> simp [nfSupport]

/-- All stay-move transition amplitudes of `nfRule` are zero. -/
theorem nfRule_no_stay : ∀ (q : NFState) (a : FourierSymbol) (q' : NFState) (b : FourierSymbol),
    nfRule.step q a QtmMove.stay q' b = 0 := by
  intro q a q' b
  by_cases hm : (QtmMove.stay, q', b) ∈ nfSupport q a
  · exact absurd hm (by
      intro hm
      exact (nfSupport_no_stay q a (QtmMove.stay, q', b) hm) rfl)
  · exact nfStep_eq_zero_off hm

/-- The target state `q'` occurs in a right-moving slot of the support at `v`. -/
abbrev nfRightTarget (q' : NFState) (v : NFState × FourierSymbol) : Prop :=
  ∃ c : FourierSymbol, (QtmMove.right, q', c) ∈ nfSupportOf v

/-- The target state `q'` occurs in a left-moving slot of the support at `v`. -/
abbrev nfLeftTarget (q' : NFState) (v : NFState × FourierSymbol) : Prop :=
  ∃ c : FourierSymbol, (QtmMove.left, q', c) ∈ nfSupportOf v

/-- No target state occurs in both a right-moving support row and a left-moving support row. -/
theorem nfRight_left_disjoint : ∀ (v1 v2 : NFState × FourierSymbol) (q' : NFState),
    ¬ (nfRightTarget q' v1 ∧ nfLeftTarget q' v2) := by
  decide

/-- The two source pairs are the binary scan rows `(.scan, .bit0)` and `(.scan, .bit1)`, in
either order. -/
abbrev nfHadamardPair (v1 v2 : NFState × FourierSymbol) : Prop :=
  (v1 = (.scan, .bit0) ∧ v2 = (.scan, .bit1)) ∨
  (v1 = (.scan, .bit1) ∧ v2 = (.scan, .bit0))

/-- The Boolean test that every slot of the first support list is absent from the second support
list. -/
def nfDisjointCheck (v1 v2 : NFState × FourierSymbol) : Bool :=
  (nfSupportOf v1).all (fun slot => !(nfSupportOf v2).contains slot)

/-- The Boolean test that the source pairs form the two binary Hadamard scan rows, in either
order. -/
def nfHadamardCheck (v1 v2 : NFState × FourierSymbol) : Bool :=
  decide (v1 = (.scan, .bit0) ∧ v2 = (.scan, .bit1)) ||
    decide (v1 = (.scan, .bit1) ∧ v2 = (.scan, .bit0))

/-- Two distinct source pairs either have disjoint support lists or form the Hadamard scan pair. -/
theorem nfDisjoint_or_hadamard : ∀ (v1 v2 : NFState × FourierSymbol), v1 ≠ v2 →
    nfDisjointCheck v1 v2 = true ∨ nfHadamardCheck v1 v2 = true := by
  decide

/-- Distinct source pairs either form `nfHadamardPair` or have disjoint transition supports. -/
theorem nfSupport_meet (v1 v2 : NFState × FourierSymbol) (hne : v1 ≠ v2) :
    nfHadamardPair v1 v2 ∨ (∀ slot ∈ nfSupportOf v1, slot ∉ nfSupportOf v2) := by
  rcases nfDisjoint_or_hadamard v1 v2 hne with hd | hh
  · right
    unfold nfDisjointCheck at hd
    rw [List.all_eq_true] at hd
    intro slot hslot
    have h := hd slot hslot
    simp at h
    exact h
  · left
    simp only [nfHadamardCheck, Bool.or_eq_true, decide_eq_true_eq] at hh
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

/-- Every entry of `fourierH` between nonblank symbols has squared complex norm `1 / 2`. -/
lemma normSq_fourierH (b' b : FourierSymbol) (h1 : b' ≠ FourierSymbol.blank)
    (h2 : b ≠ FourierSymbol.blank) : ‖fourierH b' b‖ ^ 2 = (1 / 2 : ℝ) := by
  have habs : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  have hinv : ‖((((Real.sqrt 2 : ℝ) : ℂ))⁻¹)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [norm_inv, habs]
    have hsq : (Real.sqrt 2 : ℝ)⁻¹ ^ 2 = ((Real.sqrt 2 : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
    rw [hsq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  by_cases h3 : b' = FourierSymbol.bit1 ∧ b = FourierSymbol.bit1
  · simp [fourierH, h1, h2, h3, hinv]
  · simp [fourierH, h1, h2, h3, hinv]

/-- The full finite set of normal-form states consists of `scan`, `back`, `zig`, `zin`, and
`halt`. -/
theorem nfState_univ : (Finset.univ : Finset NFState) =
    ({NFState.scan, NFState.back, NFState.zig, NFState.zin, NFState.halt} : Finset NFState) := by
  decide

/-- The full finite symbol set consists of `blank`, `bit0`, and `bit1`. -/
theorem nfSymbol_univ : (Finset.univ : Finset FourierSymbol) =
    ({FourierSymbol.blank, FourierSymbol.bit0, FourierSymbol.bit1} : Finset FourierSymbol) := by
  decide

/-- The full finite move set consists of left, stay, and right moves. -/
theorem nfMove_univ : (Finset.univ : Finset QtmMove) =
    ({QtmMove.left, QtmMove.stay, QtmMove.right} : Finset QtmMove) := by
  decide

/-- For every source state and symbol, the sum of squared transition amplitudes of `nfRule` is
one. -/
theorem nfRule_wf_norm : ∀ (q : NFState) (a : FourierSymbol),
    ∑ q' : NFState, ∑ b : FourierSymbol, ∑ d : QtmMove,
      ‖nfRule.step q a d q' b‖ ^ 2 = 1 := by
  intro q a
  rw [nfState_univ, nfSymbol_univ, nfMove_univ]
  cases q <;> cases a <;> simp [nfRule, nfSupport, nfValue, normSq_fourierH] <;> norm_num

/-- The transition rows for scanning `bit0` and scanning `bit1` have zero complex inner product. -/
theorem nfHadamard_inner_bit0 :
    ∑ q' : NFState, ∑ b : FourierSymbol, ∑ d : QtmMove,
      star (nfRule.step (.scan) (.bit0) d q' b) * nfRule.step (.scan) (.bit1) d q' b = 0 := by
  rw [nfState_univ, nfSymbol_univ, nfMove_univ]
  simp [nfRule, nfSupport, nfValue, fourierH]

/-- The transition rows for scanning `bit1` and scanning `bit0` have zero complex inner product. -/
theorem nfHadamard_inner_bit1 :
    ∑ q' : NFState, ∑ b : FourierSymbol, ∑ d : QtmMove,
      star (nfRule.step (.scan) (.bit1) d q' b) * nfRule.step (.scan) (.bit0) d q' b = 0 := by
  rw [nfState_univ, nfSymbol_univ, nfMove_univ]
  simp [nfRule, nfSupport, nfValue, fourierH]

/-- The transition rows of `nfRule` at distinct source state-symbol pairs are orthogonal. -/
theorem nfRule_wf_sameCell : ∀ (q₁ : NFState) (a₁ : FourierSymbol) (q₂ : NFState) (a₂ : FourierSymbol),
    (q₁, a₁) ≠ (q₂, a₂) →
      ∑ q' : NFState, ∑ b : FourierSymbol, ∑ d : QtmMove,
        star (nfRule.step q₁ a₁ d q' b) * nfRule.step q₂ a₂ d q' b = 0 := by
  intro q₁ a₁ q₂ a₂ hne
  rcases nfSupport_meet (q₁, a₁) (q₂, a₂) hne with hpair | hdis
  · rcases hpair with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · exact nfHadamard_inner_bit0
    · exact nfHadamard_inner_bit1
  · have hterm : ∀ (q' : NFState) (b : FourierSymbol) (d : QtmMove),
        star (nfRule.step q₁ a₁ d q' b) * nfRule.step q₂ a₂ d q' b = 0 := by
      intro q' b d
      by_cases hm₁ : (d, q', b) ∈ nfSupportOf (q₁, a₁)
      · have hnot : (d, q', b) ∉ nfSupportOf (q₂, a₂) := hdis (d, q', b) hm₁
        rw [nfStep_eq_zero_off hnot]
        simp
      · rw [nfStep_eq_zero_off hm₁]
        simp
    refine Finset.sum_eq_zero fun q' _ => ?_
    refine Finset.sum_eq_zero fun b _ => ?_
    exact Finset.sum_eq_zero fun d _ => hterm q' b d

/-- The right-moving and stay-moving transition rows of `nfRule` have zero overlap in the stated
local condition. -/
theorem nfRule_wf_rightStay : ∀ (q₁ : NFState) (a₁ : FourierSymbol) (q₂ : NFState) (a₂ : FourierSymbol)
    (c d : FourierSymbol),
    ∑ q' : NFState, nfRule.step q₁ a₁ QtmMove.right q' c *
      star (nfRule.step q₂ a₂ QtmMove.stay q' d) = 0 := by
  intro q₁ a₁ q₂ a₂ c d
  refine Finset.sum_eq_zero fun q' _ => ?_
  rw [nfRule_no_stay]
  simp

/-- The stay-moving and left-moving transition rows of `nfRule` have zero overlap in the stated
local condition. -/
theorem nfRule_wf_stayLeft : ∀ (q₁ : NFState) (a₁ : FourierSymbol) (q₂ : NFState) (a₂ : FourierSymbol)
    (c d : FourierSymbol),
    ∑ q' : NFState, nfRule.step q₁ a₁ QtmMove.stay q' c *
      star (nfRule.step q₂ a₂ QtmMove.left q' d) = 0 := by
  intro q₁ a₁ q₂ a₂ c d
  refine Finset.sum_eq_zero fun q' _ => ?_
  rw [nfRule_no_stay]
  simp

/-- The right-moving and left-moving transition rows of `nfRule` have zero overlap in the stated
local condition. -/
theorem nfRule_wf_rightLeft : ∀ (q₁ : NFState) (a₁ : FourierSymbol) (q₂ : NFState) (a₂ : FourierSymbol)
    (c d : FourierSymbol),
    ∑ q' : NFState, nfRule.step q₁ a₁ QtmMove.right q' c *
      star (nfRule.step q₂ a₂ QtmMove.left q' d) = 0 := by
  intro q₁ a₁ q₂ a₂ c d
  have hterm : ∀ q' : NFState,
      nfRule.step q₁ a₁ QtmMove.right q' c * star (nfRule.step q₂ a₂ QtmMove.left q' d) = 0 := by
    intro q'
    by_cases h₁ : nfRule.step q₁ a₁ QtmMove.right q' c = 0
    · rw [h₁]
      simp
    · have hm₁ : (QtmMove.right, q', c) ∈ nfSupportOf (q₁, a₁) := nfStep_mem_of_ne_zero h₁
      by_cases h₂ : nfRule.step q₂ a₂ QtmMove.left q' d = 0
      · rw [h₂]
        simp
      · have hm₂ : (QtmMove.left, q', d) ∈ nfSupportOf (q₂, a₂) := nfStep_mem_of_ne_zero h₂
        have hr : nfRightTarget q' (q₁, a₁) := ⟨c, hm₁⟩
        have hl : nfLeftTarget q' (q₂, a₂) := ⟨d, hm₂⟩
        exact absurd (nfRight_left_disjoint (q₁, a₁) (q₂, a₂) q' ⟨hr, hl⟩) (by simp)
  refine Finset.sum_eq_zero fun q' _ => ?_
  exact hterm q'

/-- The rule `nfRule` satisfies `QtmRule.LocalWellformed`. -/
theorem nfRule_localWellformed : nfRule.LocalWellformed :=
  ⟨nfRule_wf_norm, nfRule_wf_sameCell, nfRule_wf_rightStay, nfRule_wf_stayLeft,
    nfRule_wf_rightLeft⟩

/-- The locally well-formed machine obtained from `nfRule` and its local well-formedness proof. -/
noncomputable def nfRule_toLocal : LocalQTM NFState FourierSymbol :=
  nfRule.toLocal nfRule_localWellformed

/-- The control trace at successor time is obtained by applying `nfCtrlStep` to the previous
trace value. -/
theorem nfCtrlRun_succ (n t : ℕ) :
    nfCtrlRun n (Nat.succ t) = nfCtrlStep n (nfCtrlRun n t) := rfl

/-- At every time `t ≤ n`, the control trace is in state `scan` at cell `1 + t`. -/
theorem nfCtrlRun_scan (n : ℕ) : ∀ t, t ≤ n →
    nfCtrlRun n t = (.scan, 1 + t) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    have hdata : nfDataCell n (1 + t) := by
      refine ⟨by omega, by omega⟩
    rw [nfCtrlRun_succ, ih (by omega)]
    simp [nfCtrlStep, nfCellClass, hdata]
    omega

/-- For `n < t ≤ 2 * n`, the control trace is in state `back` at cell `2 * n + 1 - t`. -/
theorem nfCtrlRun_back (n : ℕ) : ∀ t, n < t → t ≤ 2 * n →
    nfCtrlRun n t = (.back, 2 * n + 1 - t) := by
  intro t
  induction t with
  | zero => intro h1 h2; omega
  | succ t ih =>
    intro h1 h2
    by_cases hbase : t = n
    · rw [hbase]
      rw [nfCtrlRun_succ, nfCtrlRun_scan n n (by omega)]
      have hnd : ¬ nfDataCell n (1 + n) := by
        simp [nfDataCell] <;> omega
      simp [nfCtrlStep, nfCellClass, hnd] <;> omega
    · have hlt : n < t := by omega
      rw [nfCtrlRun_succ, ih hlt (by omega)]
      have hdata : nfDataCell n (2 * n + 1 - t) := by
        refine ⟨by omega, by omega⟩
      simp [nfCtrlStep, nfCellClass, hdata]
      omega

/-- For `n ≥ 1`, the control trace at time `2 * n + 1` is `(.back, 0)`. -/
theorem nfCtrlRun_at_2n1 (n : ℕ) (hn : 1 ≤ n) :
    nfCtrlRun n (2 * n + 1) = (.back, 0) := by
  show nfCtrlRun n (Nat.succ (2 * n)) = _
  rw [nfCtrlRun_succ, nfCtrlRun_back n (2 * n) (by omega) (by omega)]
  have hdata : nfDataCell n 1 := by
    refine ⟨by omega, by omega⟩
  simp [nfCtrlStep, nfCellClass, hdata]

/-- For `n ≥ 1`, the control trace at time `2 * n + 2` is `(.zig, 1)`. -/
theorem nfCtrlRun_at_2n2 (n : ℕ) (hn : 1 ≤ n) :
    nfCtrlRun n (2 * n + 2) = (.zig, 1) := by
  show nfCtrlRun n (Nat.succ (Nat.succ (2 * n))) = _
  rw [nfCtrlRun_succ, nfCtrlRun_at_2n1 n hn]
  have hnd : ¬ nfDataCell n 0 := by
    simp [nfDataCell]
  simp [nfCtrlStep, nfCellClass, hnd]

/-- For `n ≥ 1`, the control trace at time `2 * n + 3` is `(.zin, 2)`. -/
theorem nfCtrlRun_at_2n3 (n : ℕ) (hn : 1 ≤ n) :
    nfCtrlRun n (2 * n + 3) = (.zin, 2) := by
  show nfCtrlRun n (Nat.succ (Nat.succ (Nat.succ (2 * n)))) = _
  rw [nfCtrlRun_succ, nfCtrlRun_at_2n2 n hn]
  have hdata : nfDataCell n 1 := by
    refine ⟨by omega, by omega⟩
  simp [nfCtrlStep, nfCellClass, hdata]

/-- For `n ≥ 1`, the control trace at `nfBudget n` is in state `halt` at the starting cell one. -/
theorem nfCtrlRun_halt (n : ℕ) (hn : 1 ≤ n) :
    nfCtrlRun n (nfBudget n) = (.halt, 1) := by
  have h : nfBudget n = Nat.succ (Nat.succ (Nat.succ (Nat.succ (2 * n)))) := by
    unfold nfBudget
    omega
  rw [h, nfCtrlRun_succ, nfCtrlRun_at_2n3 n hn]
  by_cases hdata : nfDataCell n 2
  · simp [nfCtrlStep, nfCellClass, hdata]
  · simp [nfCtrlStep, nfCellClass, hdata]

/-- For `n ≥ 1` and time at most `nfBudget n`, the control state follows the displayed scan,
back, zig, zin, and halt schedule. -/
theorem nfCtrlRun_schedule (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (h : t ≤ nfBudget n) :
    (nfCtrlRun n t).1 =
      if t ≤ n then NFState.scan
      else if t ≤ 2 * n then NFState.back
      else if t = 2 * n + 1 then NFState.back
      else if t = 2 * n + 2 then NFState.zig
      else if t = 2 * n + 3 then NFState.zin
      else NFState.halt := by
  have hb : nfBudget n = 2 * n + 4 := by unfold nfBudget; rfl
  by_cases h1 : t ≤ n
  · rw [nfCtrlRun_scan n t h1]
    simp [h1]
  · by_cases h2 : t ≤ 2 * n
    · rw [nfCtrlRun_back n t (by omega) h2]
      simp [h1, h2]
    · by_cases h3 : t = 2 * n + 1
      · have h1' : ¬ (2 * n + 1 ≤ n) := by omega
        have h2' : ¬ (2 * n + 1 ≤ 2 * n) := by omega
        rw [h3, nfCtrlRun_at_2n1 n hn]
        simp [h1', h2', h3]
      · by_cases h4 : t = 2 * n + 2
        · have h1' : ¬ (2 * n + 2 ≤ n) := by omega
          have h2' : ¬ (2 * n + 2 ≤ 2 * n) := by omega
          rw [h4, nfCtrlRun_at_2n2 n hn]
          simp [h1', h2', h3, h4]
        · by_cases h5 : t = 2 * n + 3
          · have h1' : ¬ (2 * n + 3 ≤ n) := by omega
            have h2' : ¬ (2 * n + 3 ≤ 2 * n) := by omega
            rw [h5, nfCtrlRun_at_2n3 n hn]
            simp [h1', h2', h3, h4, h5]
          · have h6 : t = 2 * n + 4 := by omega
            have h1' : ¬ (2 * n + 4 ≤ n) := by omega
            have h2' : ¬ (2 * n + 4 ≤ 2 * n) := by omega
            rw [h6]
            show (nfCtrlRun n (nfBudget n)).1 = _
            rw [nfCtrlRun_halt n hn]
            simp [h1', h2', h3, h4, h5, h6]

/-- For `n ≥ 1` and time at most `nfBudget n`, the cell index follows the displayed forward
scan, return scan, and final positions zero, one, two, and one. -/
theorem nfCtrlRun_cell (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (h : t ≤ nfBudget n) :
    (nfCtrlRun n t).2 =
      if t ≤ n then 1 + t
      else if t ≤ 2 * n then 2 * n + 1 - t
      else if t = 2 * n + 1 then 0
      else if t = 2 * n + 2 then 1
      else if t = 2 * n + 3 then 2
      else 1 := by
  have hb : nfBudget n = 2 * n + 4 := by unfold nfBudget; rfl
  by_cases h1 : t ≤ n
  · rw [nfCtrlRun_scan n t h1]
    simp [h1]
  · by_cases h2 : t ≤ 2 * n
    · rw [nfCtrlRun_back n t (by omega) h2]
      simp [h1, h2]
    · by_cases h3 : t = 2 * n + 1
      · have h1' : ¬ (2 * n + 1 ≤ n) := by omega
        have h2' : ¬ (2 * n + 1 ≤ 2 * n) := by omega
        rw [h3, nfCtrlRun_at_2n1 n hn]
        simp [h1', h2', h3]
      · by_cases h4 : t = 2 * n + 2
        · have h1' : ¬ (2 * n + 2 ≤ n) := by omega
          have h2' : ¬ (2 * n + 2 ≤ 2 * n) := by omega
          rw [h4, nfCtrlRun_at_2n2 n hn]
          simp [h1', h2', h3, h4]
        · by_cases h5 : t = 2 * n + 3
          · have h1' : ¬ (2 * n + 3 ≤ n) := by omega
            have h2' : ¬ (2 * n + 3 ≤ 2 * n) := by omega
            rw [h5, nfCtrlRun_at_2n3 n hn]
            simp [h1', h2', h3, h4, h5]
          · have h6 : t = 2 * n + 4 := by omega
            have h1' : ¬ (2 * n + 4 ≤ n) := by omega
            have h2' : ¬ (2 * n + 4 ≤ 2 * n) := by omega
            rw [h6]
            show (nfCtrlRun n (nfBudget n)).2 = _
            rw [nfCtrlRun_halt n hn]
            simp [h1', h2', h3, h4, h5, h6]

/-- The machine satisfies the five local conditions, has no stay transitions, and possesses the
displayed exact control-state and cell schedule, ending at `(.halt, 1)` after `2 * n + 4`
steps for `n ≥ 1`. These are the local and scheduling components related to Theorem 8.4.1 of
[BernsteinVazirani1997]. -/
theorem clause4_complete :
    Qatlib.Concepts.UniformBqp.Phi3Compile.LocalQTMFiveConditions nfRule_toLocal ∧
    (∀ (q : NFState) (a : FourierSymbol) (q' : NFState) (b : FourierSymbol),
      nfRule.step q a QtmMove.stay q' b = 0) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (h : t ≤ nfBudget n),
      (nfCtrlRun n t).1 =
        (if t ≤ n then NFState.scan
          else if t ≤ 2 * n then NFState.back
          else if t = 2 * n + 1 then NFState.back
          else if t = 2 * n + 2 then NFState.zig
          else if t = 2 * n + 3 then NFState.zin
          else NFState.halt)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (h : t ≤ nfBudget n),
      (nfCtrlRun n t).2 =
        (if t ≤ n then 1 + t
          else if t ≤ 2 * n then 2 * n + 1 - t
          else if t = 2 * n + 1 then 0
          else if t = 2 * n + 2 then 1
          else if t = 2 * n + 3 then 2
          else 1)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n), nfCtrlRun n (nfBudget n) = (.halt, 1)) ∧
    (∀ n : ℕ, nfBudget n = 2 * n + 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨nfRule_toLocal.wf_norm, nfRule_toLocal.wf_sameCell, nfRule_toLocal.wf_rightStay,
      nfRule_toLocal.wf_stayLeft, nfRule_toLocal.wf_rightLeft⟩
  · intro q a q' b
    exact nfRule_no_stay q a q' b
  · intro n hn t h
    exact nfCtrlRun_schedule n hn t h
  · intro n hn t h
    exact nfCtrlRun_cell n hn t h
  · intro n hn
    exact nfCtrlRun_halt n hn
  · intro n
    rfl

end LocalMachineUniform
end Qatlib.Papers.QComplexity97.MachineDefs
