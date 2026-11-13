/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.QtmUniformDefs
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote

/-!
# Concrete quantum-machine simulation and bounds

This module develops bounded-arity address circuits, finite-window quantum-machine dynamics, and
concrete machines implementing one-wire gate sequences and tours over input cells. It proves
local well-formedness conditions, configuration evolution formulas, acceptance-mass identities,
and repetition bounds in the quantum-machine and circuit frameworks of [BernsteinVazirani1997]
and [Yao1993].

The module also records limits of specific simulation specifications and encodings: head-motion
light cones constrain input access, and a collision in `dLambdaOpsEnc` prevents a deterministic
size emitter for that encoding. `clause8_complete` collects these obstructions together with the
stated communication, formula, and concrete-machine results.

## Main statements

* `addrWordBounded_run`: correctness of bounded-arity compilation on address wires with clean
  ancillary wires.
* `layerLocalQTM_five`: the layered one-cell machine satisfies the five local conditions.
* `allCellTour_acceptProb`: identifies acceptance mass with the designated output amplitude
  after the tour.
* `dLambdaEmitterClause_impossible`: the colliding encoding cannot support the specified size
  emitter.
* `amplificationFailure_le`: a logarithmically chosen exponent bounds the geometric failure
  factor.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachine
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CircuitImpl.Phi3Universal.QtmUniform

set_option autoImplicit false

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal
namespace QtmUniform

open Matrix

/-- With false ancillary bits, the multi-controlled-X program acts on address wires exactly as
the specified address gate. -/
theorem mcxProgram_addrGate {n : ℕ} (g : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate n)
    (x : Reg (n + (n - 1))) (hanc : ∀ a : Fin (n - 1), x (ancWire n a) = false) :
    ∀ w : Fin n,
      (BoundedGate.run (mcxProgram g.target g.pattern) x) (addrWire (n - 1) w)
        = (g.eval (fun w => x (addrWire (n - 1) w))) w := by
  intro w
  rw [mcxProgram_run g.target g.pattern x hanc]
  exact mcxPerm_addrGate g.target g.pattern x w

/-- The multi-controlled-X program restores all initially false ancillary bits. -/
theorem mcxProgram_addrGate_ancillas {n : ℕ} (g : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate n)
    (x : Reg (n + (n - 1))) (hanc : ∀ a : Fin (n - 1), x (ancWire n a) = false) :
    ∀ a : Fin (n - 1),
      (BoundedGate.run (mcxProgram g.target g.pattern) x) (ancWire n a) = x (ancWire n a) := by
  intro a
  rw [mcxProgram_run g.target g.pattern x hanc]
  exact mcxPerm_target_only g.target g.pattern x (ancWire n a)
    ((addrWire_ne_ancWire n (n - 1) g.target a).symm)

/-- With false ancillary bits, bounded-gate compilation of an address word agrees with its
evaluation on every address wire. -/
theorem addrWordBounded_run {n : ℕ} :
    ∀ (w : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n) (x : Reg (n + (n - 1))),
      (∀ a : Fin (n - 1), x (ancWire n a) = false) →
      ∀ (wi : Fin n),
        (BoundedGate.run (addrWordBounded w) x) (addrWire (n - 1) wi)
          = (Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord.eval w (fun w => x (addrWire (n - 1) w))) wi := by
  intro w
  induction w with
  | nil =>
      intro x hanc wi
      rfl
  | cons g l ih =>
      intro x hanc wi
      have hrun : BoundedGate.run (addrWordBounded (g :: l)) x
          = BoundedGate.run (addrWordBounded l) (BoundedGate.run (mcxProgram g.target g.pattern) x) := by
        simp only [addrWordBounded]
        rw [BoundedGate.run_append]
      rw [hrun]
      have hanc' : ∀ b : Fin (n - 1),
          (BoundedGate.run (mcxProgram g.target g.pattern) x) (ancWire n b) = false := by
        intro b
        rw [mcxProgram_addrGate_ancillas g x hanc b]
        exact hanc b
      have hmain := ih (BoundedGate.run (mcxProgram g.target g.pattern) x) hanc' wi
      rw [hmain]
      have hfun : (fun w => (BoundedGate.run (mcxProgram g.target g.pattern) x) (addrWire (n - 1) w))
          = g.eval (fun w => x (addrWire (n - 1) w)) := by
        funext w
        exact mcxProgram_addrGate g x hanc w
      rw [hfun]
      rfl

/-- Bounded-gate compilation of an address word restores its initially false ancillary bits. -/
theorem addrWordBounded_ancillas {n : ℕ} :
    ∀ (w : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n) (x : Reg (n + (n - 1))),
      (∀ a : Fin (n - 1), x (ancWire n a) = false) →
      ∀ a : Fin (n - 1),
        (BoundedGate.run (addrWordBounded w) x) (ancWire n a) = x (ancWire n a) := by
  intro w
  induction w with
  | nil =>
      intro x hanc a
      rfl
  | cons g l ih =>
      intro x hanc a
      have hrun : BoundedGate.run (addrWordBounded (g :: l)) x
          = BoundedGate.run (addrWordBounded l) (BoundedGate.run (mcxProgram g.target g.pattern) x) := by
        simp only [addrWordBounded]
        rw [BoundedGate.run_append]
      rw [hrun]
      have hanc' : ∀ b : Fin (n - 1),
          (BoundedGate.run (mcxProgram g.target g.pattern) x) (ancWire n b) = false := by
        intro b
        rw [mcxProgram_addrGate_ancillas g x hanc b]
        exact hanc b
      have hmain := ih (BoundedGate.run (mcxProgram g.target g.pattern) x) hanc' a
      rw [hmain]
      rw [mcxProgram_addrGate_ancillas g x hanc a]

/-- The bounded-gate compilation has length at most the address-word length times `4*(n-1)+1`. -/
theorem addrWordBounded_gate_count {n : ℕ} (w : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n) :
    (addrWordBounded w).length ≤ w.length * (4 * (n - 1) + 1) := by
  induction w with
  | nil => simp [addrWordBounded]
  | cons g l ih =>
      have h1 := mcxProgram_gate_count g.target g.pattern
      have h2 : (addrWordBounded l).length ≤ l.length * (4 * (n - 1) + 1) := ih
      simp only [addrWordBounded, List.length_append, List.length_cons]
      calc (mcxProgram g.target g.pattern).length + (addrWordBounded l).length
          ≤ (4 * (n - 1) + 1) + l.length * (4 * (n - 1) + 1) := Nat.add_le_add h1 h2
        _ = (l.length + 1) * (4 * (n - 1) + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _

/-- Every gate in the bounded compilation of an address word has arity at most three. -/
theorem addrWordBounded_arity {n : ℕ} (w : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n) :
    ∀ g ∈ addrWordBounded w, g.arity ≤ 3 := by
  induction w with
  | nil =>
      intro g hg
      simp [addrWordBounded] at hg
  | cons h l ih =>
      intro g hg
      rw [addrWordBounded] at hg
      rcases List.mem_append.mp hg with hg' | hg'
      · exact mcxProgram_arity h.target h.pattern g hg'
      · exact ih g hg'

/-- With false ancillary bits, the bounded compilation of a routing word agrees with that word
on every head-address wire. -/
theorem routeGateWord_bounded {B : ℕ} (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.WindowCenter B) :
    ∀ (x : Reg (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B
        + (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B - 1))),
      (∀ a : Fin (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B - 1),
          x (ancWire (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B) a) = false) →
      ∀ (wi : Fin (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B)),
        (BoundedGate.run (addrWordBounded (Qatlib.Concepts.UniformBqp.Phi3Compile.routeGateWord B i)) x)
            (addrWire (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B - 1) wi)
          = (Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord.eval (Qatlib.Concepts.UniformBqp.Phi3Compile.routeGateWord B i)
              (fun w => x (addrWire (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B - 1) w))) wi := by
  intro x hanc wi
  exact addrWordBounded_run _ x hanc wi

/-- The bounded routing compilation has length at most the routing-word length times
`4*(headQubits B-1)+1`. -/
theorem routeGateWord_bounded_gate_count {B : ℕ} (i : Qatlib.Concepts.QueryComplexity.DegreeMethod.WindowCenter B) :
    (addrWordBounded (Qatlib.Concepts.UniformBqp.Phi3Compile.routeGateWord B i)).length
      ≤ (Qatlib.Concepts.UniformBqp.Phi3Compile.routeGateWord B i).length
        * (4 * (Qatlib.Concepts.QueryComplexity.DegreeMethod.headQubits B - 1) + 1) :=
  addrWordBounded_gate_count _

/-- A globally well-formed rule gives the five local conditions when stay-free, and its mixed
right-stay and stay-left overlap sum vanishes. -/
theorem stay_boundary {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (R : Rule Q A) (q0 : Q) (hw : R.GloballyWellformed) :
    (∀ (hs : stayFree R),
        LocalQTMFiveConditions (toLocalQTM R q0 hs hw)) ∧
      (∀ (q₁ q₂ : Q) (a₁ a₂ c d : A),
        ∑ q' : Q,
          (star (qtmStep R q₁ a₁ QtmMove.right q' c) * qtmStep R q₂ a₂ QtmMove.stay q' d
            + star (qtmStep R q₁ a₁ QtmMove.stay q' c) * qtmStep R q₂ a₂ QtmMove.left q' d) = 0) :=
  ⟨fun hs => toLocalQTM_fiveConditions R q0 hs hw,
   fun q₁ q₂ a₁ a₂ c d => qtm_adjacent_combined_of_global R hw q₁ q₂ a₁ a₂ c d⟩

/-- A successful head move changes its cell index by at most one in either direction. -/
theorem moveCell_dist {w : ℕ} (d : QtmMove) (h h' : Fin (2 * w + 1))
    (hm : moveCell d h = some h') : h'.val ≤ h.val + 1 ∧ h.val ≤ h'.val + 1 := by
  cases d with
  | left =>
      simp only [moveCell] at hm
      split at hm
      · exact absurd hm (by simp)
      · rw [Option.some.injEq] at hm
        obtain rfl := hm
        show h.val - 1 ≤ h.val + 1 ∧ h.val ≤ h.val - 1 + 1
        omega
  | stay =>
      rw [moveCell, Option.some.injEq] at hm
      obtain rfl := hm
      omega
  | right =>
      simp only [moveCell] at hm
      split at hm
      · exact absurd hm (by simp)
      · rw [Option.some.injEq] at hm
        obtain rfl := hm
        show h.val + 1 ≤ h.val + 1 ∧ h.val ≤ h.val + 1 + 1
        omega

/-- A one-step window transition has zero amplitude when the head positions differ by at least
two cells. -/
theorem windowStep_zero_of_far {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (c d : WindowCfg w Q Bool)
    (hfar : d.head.val + 2 ≤ c.head.val ∨ c.head.val + 2 ≤ d.head.val) :
    windowStep (t := w) M c d = 0 := by
  simp only [windowStep, Matrix.of_apply]
  refine Finset.sum_eq_zero ?_
  intro dd _
  refine Finset.sum_eq_zero ?_
  intro q' _
  refine Finset.sum_eq_zero ?_
  intro b _
  rw [if_neg]
  intro hcond
  rcases hcond with ⟨hmove, -⟩
  obtain ⟨h1, h2⟩ := moveCell_dist dd d.head c.head hmove
  omega

/-- Evolution from a configuration with centered head has zero amplitude outside the head cone
of radius equal to the number of steps. -/
theorem evolve_headCone {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (i : WindowCfg w Q Bool) (hi : i.head.val = w) :
    ∀ (t : ℕ) (c : WindowCfg w Q Bool),
      ¬(w ≤ c.head.val + t ∧ c.head.val ≤ w + t) →
      ((windowStep (t := w) M) ^ t *ᵥ Ket i) c = 0 := by
  intro t
  induction t with
  | zero =>
      intro c hc
      rw [pow_zero, Matrix.one_mulVec]
      by_cases hci : c = i
      · rw [hci, hi] at hc
        simp at hc
      · simp [Qatlib.Foundations.PureStateMath.Ket, hci]
  | succ t ih =>
      intro c hc
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have hsum : (((windowStep (t := w) M) *ᵥ
          ((windowStep (t := w) M) ^ t *ᵥ Ket i)) c) =
          ∑ d : WindowCfg w Q Bool,
            windowStep (t := w) M c d * ((windowStep (t := w) M) ^ t *ᵥ Ket i) d := by
        simp [Matrix.mulVec, dotProduct]
      rw [hsum]
      refine Finset.sum_eq_zero ?_
      intro d _
      by_cases hcone : (w ≤ d.head.val + t ∧ d.head.val ≤ w + t)
      · have hzero : windowStep (t := w) M c d = 0 := by
          refine windowStep_zero_of_far M c d ?_
          have h1 : d.head.val ≤ w + t := hcone.2
          have h2 : w ≤ d.head.val + t := hcone.1
          omega
        rw [hzero, zero_mul]
      · rw [ih d hcone, mul_zero]

/-- Input bit `i` appears at window position `w+1+i` whenever that position exists. -/
theorem initWindowCfg_tape_at {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {w n : ℕ} (M : LocalQTM Q A) (x : Fin n → A) (i : Fin n) :
    ∀ (j : Fin (2 * w + 1)), j.val = w + 1 + i.val →
      (initWindowCfg (t := w) M n x).tape j = x i := by
  intro j hj
  simp only [initWindowCfg]
  have hcond : w < j.val ∧ j.val ≤ w + n := by
    rw [hj]
    omega
  rw [dif_pos hcond]
  congr 1
  apply Fin.ext
  show j.val - w - 1 = i.val
  omega

/-- Evolution of an initialized window configuration has zero amplitude outside the head cone
centered at `w`. -/
theorem initWindowCfg_headCone {Q : Type} [Fintype Q] [DecidableEq Q] {w n : ℕ}
    (M : LocalQTM Q Bool) (x : Fin n → Bool) (t : ℕ) (c : WindowCfg w Q Bool) :
    ¬(w ≤ c.head.val + t ∧ c.head.val ≤ w + t) →
    ((windowStep (t := w) M) ^ t *ᵥ Ket (initWindowCfg (t := w) M n x)) c = 0 := by
  exact evolve_headCone M (initWindowCfg (t := w) M n x) rfl t c

/-- Every circuit has a step budget at least its input width and at most `(n + Size C + 2)^6`. -/
theorem headStayLightcone_budget_fits :
    ∀ (n : ℕ) (C : Circuit (Reg n)),
      ∃ t : ℕ, n ≤ t ∧ t ≤ (n + Size C + 2) ^ 6 := by
  intro n C
  refine ⟨n, le_rfl, ?_⟩
  have hpow : n + Size C + 2 ≤ (n + Size C + 2) ^ 6 := Nat.le_pow (b := 6) (by omega)
  omega

/-- The width-independent value `(1+2)^6` is `729`, below `730`, whereas the width-dependent
bound at `730` exceeds that width. -/
theorem frozen_step_budget_can_be_too_small :
    (1 + 2) ^ 6 = 729 ∧ 729 < 730 ∧ 730 ≤ (730 + 1 + 2) ^ 6 := by
  norm_num

/-- An input cell with index at least `t` lies strictly to the right of the radius-`t` head
cone. -/
theorem input_line_beyond_lightcone {w n : ℕ} (t : ℕ) (i : Fin n) (hi : t ≤ i.val) :
    w + 1 + i.val > w + t := by
  omega

/-- A shift rule with a non-stay move is stay-free. -/
theorem shiftRule_stayFree {Q A : Type} [Fintype Q] [Fintype A] (blank : A) (move : Move)
    (hm : move ≠ Move.stay) : stayFree (shiftRule Q A blank move) := by
  intro q a q' b
  have hne : (Move.stay, q', b) ≠ (move, q, a) := by
    intro h
    have h1 : Move.stay = move := congrArg Prod.fst h
    exact hm h1.symm
  simp [shiftRule, hne]

/-- Complex conjugation applied twice returns the original number. -/
theorem complex_star_star (z : ℂ) : star (star z) = z := by
  simp

/-- The squared norm of a complex number is the real part of its product with its conjugate. -/
theorem complex_normSq_eq_re_mul_star (z : ℂ) :
    Complex.normSq z = (z * star z).re := by
  rw [Complex.normSq_apply, Complex.mul_re]
  simp [Complex.conj_im]

/-- An entry of the conjugate transpose is the conjugate of the corresponding transposed entry. -/
theorem star_matrix_apply (U : Matrix Bool Bool ℂ) (a b : Bool) :
    star U b a = star (U a b) := by
  rw [show star U = Uᴴ from rfl, Matrix.conjTranspose_apply]

/-- A sum over head moves equals its stay term when the left and right terms vanish. -/
theorem sum_qtmMove_eq_stay {M : Type} [AddCommMonoid M] (f : QtmMove → M)
    (hl : f QtmMove.left = 0) (hr : f QtmMove.right = 0) :
    (∑ d : QtmMove, f d) = f QtmMove.stay := by
  refine Finset.sum_eq_single QtmMove.stay ?_ ?_
  · intro d _ hd
    cases d with
    | left => exact hl
    | stay => exact absurd rfl hd
    | right => exact hr
  · intro hn
    exact absurd (Finset.mem_univ QtmMove.stay) hn

/-- A sum indexed by `Unit` is its unique summand. -/
theorem sum_unit_eq {M : Type} [AddCommMonoid M] (f : Unit → M) :
    (∑ q : Unit, f q) = f () := by
  refine Finset.sum_eq_single () ?_ ?_
  · intro q _ hne
    exact absurd rfl hne
  · intro hn
    exact (hn (Finset.mem_univ ())).elim

/-- The stay amplitude for a one-qubit gate step is the corresponding matrix entry. -/
theorem gateStep_stay (U : Matrix Bool Bool ℂ) (a b : Bool) :
    gateStep U a QtmMove.stay b = U b a := by
  simp [gateStep]

/-- Complex conjugation commutes with a sum over Boolean indices. -/
theorem complex_star_sum (f : Bool → ℂ) :
    star (∑ b : Bool, f b) = ∑ b : Bool, star (f b) := by
  exact star_sum (Finset.univ : Finset Bool) f

/-- The one-state local quantum machine applying a given one-qubit unitary without moving its
head. -/
def gateLocalQTM (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTM Unit Bool where
  blank := false
  start := ()
  step := gateStepFn U
  wf_norm := by
    intro q a
    have hmat : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hunit : (∑ q' : Unit, ∑ b : Bool, ∑ d : QtmMove,
            ‖gateStepFn U q a d q' b‖ ^ 2)
        = ∑ b : Bool, ∑ d : QtmMove, ‖gateStep U a d b‖ ^ 2 := by
      rw [sum_unit_eq]
      apply Finset.sum_congr rfl
      intro b _
      rfl
    rw [hunit]
    have hd : ∀ (b : Bool), (∑ d : QtmMove, ‖gateStep U a d b‖ ^ 2) = ‖U b a‖ ^ 2 := by
      intro b
      refine (sum_qtmMove_eq_stay (fun d => ‖gateStep U a d b‖ ^ 2) ?_ ?_).trans ?_
      · simp [gateStep]
      · simp [gateStep]
      · rw [gateStep_stay]
    rw [Finset.sum_congr rfl (fun b _ => hd b)]
    have hA : (∑ b : Bool, ‖U b a‖ ^ 2) = ∑ b : Bool, Complex.normSq (U b a) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Complex.sq_norm _
    have hB : (∑ b : Bool, Complex.normSq (U b a))
        = ∑ b : Bool, (U b a * star (U b a)).re := by
      apply Finset.sum_congr rfl
      intro b _
      exact complex_normSq_eq_re_mul_star _
    have hC : (∑ b : Bool, (U b a * star (U b a)).re)
        = (∑ b : Bool, U b a * star (U b a)).re := by
      rw [← Complex.re_sum]
    have hD : (∑ b : Bool, U b a * star (U b a)) = (star U * U) a a := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro b _
      rw [star_matrix_apply]
      exact mul_comm _ _
    rw [hA, hB, hC, hD]
    simp [hmat]
  wf_sameCell := by
    intro q₁ a₁ q₂ a₂ hne
    have hmat : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have ha : a₁ ≠ a₂ := by
      intro hcontra
      apply hne
      cases q₁
      cases q₂
      exact Prod.ext rfl hcontra
    have hunit : (∑ q' : Unit, ∑ b : Bool, ∑ d : QtmMove,
            star (gateStepFn U q₁ a₁ d q' b) * gateStepFn U q₂ a₂ d q' b)
        = ∑ b : Bool, ∑ d : QtmMove,
          star (gateStep U a₁ d b) * gateStep U a₂ d b := by
      rw [sum_unit_eq]
      apply Finset.sum_congr rfl
      intro b _
      rfl
    rw [hunit]
    have hd : ∀ (b : Bool), (∑ d : QtmMove, star (gateStep U a₁ d b) * gateStep U a₂ d b)
        = star (U b a₁) * U b a₂ := by
      intro b
      refine (sum_qtmMove_eq_stay (fun d => star (gateStep U a₁ d b) * gateStep U a₂ d b) ?_ ?_).trans ?_
      · simp [gateStep]
      · simp [gateStep]
      · rw [gateStep_stay, gateStep_stay]
    rw [Finset.sum_congr rfl (fun b _ => hd b)]
    have hC : (∑ b : Bool, star (U b a₁) * U b a₂) = (star U * U) a₁ a₂ := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro b _
      rw [star_matrix_apply]
    rw [hC]
    simp [hmat, ha]
  wf_rightStay := by
    intro q₁ a₁ q₂ a₂ c d
    simp [gateStepFn, gateStep]
  wf_stayLeft := by
    intro q₁ a₁ q₂ a₂ c d
    simp [gateStepFn, gateStep]
  wf_rightLeft := by
    intro q₁ a₁ q₂ a₂ c d
    simp [gateStepFn, gateStep]

/-- The one-qubit gate machine satisfies the five local quantum-machine conditions. -/
theorem gateLocalQTM_five (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTMFiveConditions (gateLocalQTM U hU) := by
  exact ⟨(gateLocalQTM U hU).wf_norm, (gateLocalQTM U hU).wf_sameCell,
    (gateLocalQTM U hU).wf_rightStay, (gateLocalQTM U hU).wf_stayLeft,
    (gateLocalQTM U hU).wf_rightLeft⟩

/-- A target configuration is obtained by writing at the source head exactly when its head and
state agree and its tape has the specified single-cell update. -/
theorem writeHead_eq_iff {w : ℕ} {Q A : Type} (src tgt : WindowCfg w Q A) :
    tgt = writeHead src (tgt.tape src.head) ↔
      tgt.head = src.head ∧ tgt.state = src.state ∧
        ∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j := by
  constructor
  · intro h
    have hh : tgt.head = src.head := by
      have := congrArg WindowCfg.head h
      simpa [writeHead] using! this
    have hs : tgt.state = src.state := by
      have := congrArg WindowCfg.state h
      simpa [writeHead] using! this
    have ht : ∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j := by
      intro j
      have := congrArg (fun c => c.tape j) h
      simpa [writeHead] using! this
    exact ⟨hh, hs, ht⟩
  · rintro ⟨h1, h2, h3⟩
    cases tgt with
    | mk head state tape =>
      simp only [WindowCfg.mk.injEq, writeHead, WindowCfg.mk.injEq]
      refine ⟨h1, h2, ?_⟩
      funext j
      exact h3 j

/-- The gate machine has amplitude `U` between configurations differing only at the head cell,
and zero otherwise. -/
theorem gateLocalQTM_windowStep (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w Unit Bool) :
    (windowStep (t := w) (gateLocalQTM U hU) tgt) src =
      if src.head = tgt.head ∧
          (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j)
      then U (tgt.tape src.head) (src.tape src.head) else 0 := by
  classical
  simp only [windowStep, Matrix.of_apply, gateLocalQTM, gateStepFn, gateStep]
  rw [Finset.sum_eq_single_of_mem QtmMove.stay (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem () (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem (tgt.tape src.head) (Finset.mem_univ _)]
      · simp only [moveCell, Option.some.injEq, ↓reduceIte]
        by_cases h1 : (src.head = tgt.head ∧ True ∧
            (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j))
        · rw [if_pos h1]
          by_cases h2 : (src.head = tgt.head ∧
              (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j))
          · rw [if_pos h2]
          · rw [if_neg h2]
            exact (h2 ⟨h1.1, h1.2.2⟩).elim
        · rw [if_neg h1]
          by_cases h2 : (src.head = tgt.head ∧
              (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j))
          · rw [if_pos h2]
            exact (h1 ⟨h2.1, trivial, h2.2⟩).elim
          · rw [if_neg h2]
      · intro b _ hb
        simp only [moveCell, Option.some.injEq, ↓reduceIte]
        by_cases hcon : (src.head = tgt.head ∧ True ∧
            (∀ j, tgt.tape j = if j = src.head then b else src.tape j))
        · rw [if_pos hcon]
          have hlt : tgt.tape src.head = b := by
            have hstep := hcon.2.2 src.head
            simpa using! hstep
          exact (hb hlt.symm).elim
        · rw [if_neg hcon]
    · intro q' _ hq
      exact (hq (Subsingleton.elim _ _)).elim
  · intro d _ hd
    apply Finset.sum_eq_zero
    intro q' _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hcon : (moveCell d src.head = some tgt.head ∧ True ∧
        (∀ j, tgt.tape j = if j = src.head then b else src.tape j))
    · rw [if_pos hcon, if_neg hd]
    · rw [if_neg hcon]

/-- The gate machine transition amplitude is the corresponding entry of `U` exactly for a
`writeHead` target, and zero otherwise. -/
theorem gateLocalQTM_windowStep_writeHead (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w Unit Bool) :
    (windowStep (t := w) (gateLocalQTM U hU) tgt) src =
      if tgt = writeHead src (tgt.tape src.head)
      then U (tgt.tape src.head) (src.tape src.head) else 0 := by
  rw [gateLocalQTM_windowStep U hU src tgt]
  by_cases h : src.head = tgt.head ∧
      (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j)
  · rw [if_pos h]
    rw [if_pos (Iff.mpr (writeHead_eq_iff src tgt)
      ⟨h.1.symm, Subsingleton.elim _ _, h.2⟩)]
  · rw [if_neg h]
    by_cases hh : (tgt = writeHead src (tgt.tape src.head))
    · rw [if_pos hh]
      have hparts := Iff.mp (writeHead_eq_iff src tgt) hh
      exact (h ⟨hparts.1.symm, hparts.2.2⟩).elim
    · rw [if_neg hh]

/-- One step from a basis configuration applies `U` to the head-cell symbol and has zero
amplitude on configurations with any other change. -/
theorem gateLocalQTM_windowStep_ket (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w Unit Bool) :
    (windowStep (t := w) (gateLocalQTM U hU) *ᵥ Ket src) tgt =
      if src.head = tgt.head ∧
          (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j)
      then U (tgt.tape src.head) (src.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact gateLocalQTM_windowStep U hU src tgt
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- The first measurement-state amplitude flips the Boolean tape symbol deterministically. -/
theorem meas_amp_row {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ) (a b : Bool) :
    layerAmp Us (measState k) a b = if b = !a then 1 else 0 := by
  simp [layerAmp, measState]

/-- The second measurement-state amplitude preserves the Boolean tape symbol deterministically. -/
theorem meas2_amp_row {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ) (a b : Bool) :
    layerAmp Us (.meas2 : LayerState k) a b = if b = a then 1 else 0 := by
  simp [layerAmp]

/-- Each column of a unitary in the gate sequence has squared norm one. -/
theorem gateCol_norm {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (i : Fin k) (a : Bool) :
    ∑ b : Bool, ‖Us i b a‖ ^ 2 = 1 := by
  have hmat : star (Us i) * (Us i) = 1 := Matrix.mem_unitaryGroup_iff'.mp (hU i)
  have hD : (∑ b : Bool, Us i b a * star (Us i b a)) = (star (Us i) * (Us i)) a a := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [star_matrix_apply]
    exact mul_comm _ _
  have hA : (∑ b : Bool, ‖Us i b a‖ ^ 2) = ∑ b : Bool, Complex.normSq (Us i b a) := by
    apply Finset.sum_congr rfl
    intro b _
    exact Complex.sq_norm _
  have hB : (∑ b : Bool, Complex.normSq (Us i b a))
      = ∑ b : Bool, (Us i b a * star (Us i b a)).re := by
    apply Finset.sum_congr rfl
    intro b _
    exact complex_normSq_eq_re_mul_star _
  have hC : (∑ b : Bool, (Us i b a * star (Us i b a)).re)
      = (∑ b : Bool, Us i b a * star (Us i b a)).re := by
    rw [← Complex.re_sum]
  rw [hA, hB, hC, hD]
  simp [hmat]

/-- Distinct columns of each unitary in the gate sequence are orthogonal. -/
theorem gateCol_orth {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (i : Fin k) (a₁ a₂ : Bool) (hne : a₁ ≠ a₂) :
    ∑ b : Bool, star (Us i b a₁) * Us i b a₂ = 0 := by
  have hmat : star (Us i) * (Us i) = 1 := Matrix.mem_unitaryGroup_iff'.mp (hU i)
  have hC : (∑ b : Bool, star (Us i b a₁) * Us i b a₂) = (star (Us i) * (Us i)) a₁ a₂ := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [star_matrix_apply]
  rw [hC]
  simp [hmat, hne]

/-- For unitary gate data, each layered transition-amplitude row has squared norm one. -/
theorem layerAmp_norm {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (q : LayerState k) (a : Bool) :
    ∑ b : Bool, ‖layerAmp Us q a b‖ ^ 2 = 1 := by
  cases q with
  | toInput => cases a <;> simp [layerAmp]
  | layer i =>
      by_cases h : i.val < k
      · simp only [layerAmp, dif_pos h]
        exact gateCol_norm Us hU ⟨i.val, h⟩ a
      · have hn : ¬ (i.val < k) := by omega
        simp only [layerAmp, dif_neg hn]
        cases a <;> simp
  | acc => cases a <;> simp [layerAmp]
  | rej => cases a <;> simp [layerAmp]
  | meas2 => cases a <;> simp [layerAmp]

/-- Summing the squared norm of an amplitude supported on one head move gives the squared norm
of that amplitude. -/
theorem sum_norm_move (x : ℂ) (d₀ : QtmMove) :
    ∑ d : QtmMove, ‖(if d = d₀ then x else 0)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [Finset.sum_eq_single_of_mem d₀ (Finset.mem_univ _)]
  · simp
  · intro d _ hd
    simp [hd]

/-- The sum of two single-move-supported factors is their product when their supports coincide,
and zero otherwise. -/
theorem sum_move_mul (x y : ℂ) (d₁ d₂ : QtmMove) :
    ∑ d : QtmMove, (if d = d₁ then x else 0) * (if d = d₂ then y else 0) =
      if d₁ = d₂ then x * y else 0 := by
  by_cases h : d₁ = d₂
  · subst h
    rw [Finset.sum_eq_single_of_mem d₁ (Finset.mem_univ _)]
    · simp
    · intro d _ hd
      simp [hd]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd1 : d = d₁ <;> by_cases hd2 : d = d₂
    · rw [if_pos hd1, if_pos hd2]
      exact absurd (hd1.symm.trans hd2) h
    · rw [if_pos hd1, if_neg hd2]
      simp
    · rw [if_neg hd1, if_pos hd2]
      simp
    · rw [if_neg hd1, if_neg hd2]
      simp

/-- The conjugate-product sum of two single-move-supported amplitudes is their conjugate product
when the moves coincide, and zero otherwise. -/
theorem sum_move_mul_star (x y : ℂ) (d₁ d₂ : QtmMove) :
    ∑ d : QtmMove, star (if d = d₁ then x else 0) * (if d = d₂ then y else 0) =
      if d₁ = d₂ then star x * y else 0 := by
  by_cases h : d₁ = d₂
  · subst h
    rw [Finset.sum_eq_single_of_mem d₁ (Finset.mem_univ _)]
    · simp
    · intro d _ hd
      simp [hd]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd1 : d = d₁ <;> by_cases hd2 : d = d₂
    · rw [if_pos hd1, if_pos hd2]
      exact absurd (hd1.symm.trans hd2) h
    · rw [if_pos hd1, if_neg hd2]
      simp
    · rw [if_neg hd1, if_pos hd2]
      simp
    · rw [if_neg hd1, if_neg hd2]
      simp

/-- Distinct deterministic symbol-preserving amplitude rows are orthogonal. -/
theorem layerAmp_det_orth {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ) (q : LayerState k)
    (a₁ a₂ : Bool) (hne : a₁ ≠ a₂)
    (hrow : ∀ b, layerAmp Us q a₁ b = if b = a₁ then 1 else 0)
    (hrow2 : ∀ b, layerAmp Us q a₂ b = if b = a₂ then 1 else 0) :
    ∑ b : Bool, star (layerAmp Us q a₁ b) * layerAmp Us q a₂ b = 0 := by
  have hsum : (∑ b : Bool, star (layerAmp Us q a₁ b) * layerAmp Us q a₂ b)
      = ∑ b : Bool, star (if b = a₁ then 1 else 0) * (if b = a₂ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [hrow, hrow2]
  rw [hsum]
  cases a₁ <;> cases a₂ <;>
    first
    | exact (hne rfl).elim
    | simp

/-- For equal input symbols, the first and second measurement-state amplitude rows have zero
overlap in both orders. -/
theorem layerAmp_meas_orth {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (a₁ a₂ : Bool) (heq : a₁ = a₂) :
    (∑ b : Bool, star (layerAmp Us (measState k) a₁ b)
        * layerAmp Us (.meas2 : LayerState k) a₂ b = 0) ∧
    (∑ b : Bool, star (layerAmp Us (.meas2 : LayerState k) a₂ b)
        * layerAmp Us (measState k) a₁ b = 0) := by
  have hsum : (∑ b : Bool, star (layerAmp Us (measState k) a₁ b)
        * layerAmp Us (.meas2 : LayerState k) a₂ b)
      = ∑ b : Bool, star (if b = !a₁ then 1 else 0) * (if b = a₂ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [meas_amp_row, meas2_amp_row]
  have hsum2 : (∑ b : Bool, star (layerAmp Us (.meas2 : LayerState k) a₂ b)
        * layerAmp Us (measState k) a₁ b)
      = ∑ b : Bool, star (if b = a₂ then 1 else 0) * (if b = !a₁ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [meas2_amp_row, meas_amp_row]
  constructor
  · rw [hsum]
    rcases a₁ with _ | _ <;> rcases a₂ with _ | _
    all_goals first
      | exact Bool.noConfusion heq
      | simp
  · rw [hsum2]
    rcases a₁ with _ | _ <;> rcases a₂ with _ | _
    all_goals first
      | exact Bool.noConfusion heq
      | simp

/-- Distinct state-symbol inputs with the same next state have orthogonal layered amplitude rows
when the gate data are unitary. -/
theorem layerAmp_orth {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    (q₁ q₂ : LayerState k) (a₁ a₂ : Bool)
    (hne : (q₁, a₁) ≠ (q₂, a₂))
    (hnxt : layerNext q₁ a₁ = layerNext q₂ a₂) :
    ∑ b : Bool, star (layerAmp Us q₁ a₁ b) * layerAmp Us q₂ a₂ b = 0 := by
  cases q₁ with
  | toInput =>
      cases q₂ with
      | toInput =>
          have ha : a₁ ≠ a₂ := by
            intro h
            apply hne
            exact Prod.ext rfl h
          exact layerAmp_det_orth Us (.toInput : LayerState k) a₁ a₂ ha
            (fun b => by simp [layerAmp]) (fun b => by simp [layerAmp])
      | layer j =>
          by_cases hj : j.val < k
          · exfalso
            cases a₂ <;> simp [layerNext, hj] at hnxt
          · exfalso
            cases a₂ <;> simp [layerNext, hj] at hnxt
      | acc =>
          exfalso
          simp [layerNext] at hnxt
      | rej =>
          exfalso
          simp [layerNext] at hnxt
      | meas2 =>
          exfalso
          cases a₂ <;> simp [layerNext] at hnxt
  | layer i =>
      by_cases hi : i.val < k
      · cases q₂ with
        | toInput =>
            exfalso
            simp [layerNext, hi] at hnxt
        | layer j =>
            by_cases hj : j.val < k
            · have hij : i = j := by
                simp [layerNext, hi, hj] at hnxt
                exact Fin.ext hnxt
              have ha : a₁ ≠ a₂ := by
                intro h
                apply hne
                exact Prod.ext (congrArg LayerState.layer hij) h
              subst hij
              simp only [layerAmp, dif_pos hi]
              exact gateCol_orth Us hU ⟨i.val, hi⟩ a₁ a₂ ha
            · exfalso
              cases a₂ <;> simp [layerNext, hi, hj] at hnxt
        | acc =>
            exfalso
            simp [layerNext, hi] at hnxt
        | rej =>
            exfalso
            simp [layerNext, hi] at hnxt
        | meas2 =>
            exfalso
            cases a₂ <;> simp [layerNext, hi] at hnxt
      · have hi' : i.val = k := by omega
        cases q₂ with
        | toInput =>
            exfalso
            cases a₁ <;> simp [layerNext, hi'] at hnxt
        | layer j =>
            by_cases hj : j.val < k
            · exfalso
              cases a₁ <;> simp [layerNext, hi', hj] at hnxt
            · have hj' : j.val = k := by omega
              have ha : a₁ = a₂ := by
                by_cases ha : a₁ = a₂
                · exact ha
                · exfalso
                  rcases a₁ with _ | _ <;> rcases a₂ with _ | _
                  all_goals simp_all [layerNext]
              exfalso
              apply hne
              exact Prod.ext (congrArg LayerState.layer (Fin.ext (by omega))) ha
        | acc =>
            exfalso
            cases a₁ <;> simp [layerNext, hi'] at hnxt
        | rej =>
            exfalso
            cases a₁ <;> simp [layerNext, hi'] at hnxt
        | meas2 =>
            have ha : a₁ = a₂ := by
              by_cases ha : a₁ = a₂
              · exact ha
              · exfalso
                rcases a₁ with _ | _ <;> rcases a₂ with _ | _
                all_goals simp_all [layerNext]
            have hconv : LayerState.layer i = measState k := by
              simp only [measState]
              congr 1
              apply Fin.ext
              show i.val = k
              exact hi'
            rw [hconv]
            exact (layerAmp_meas_orth Us a₁ a₂ ha).1
  | acc =>
      cases q₂ with
      | toInput =>
          exfalso
          simp [layerNext] at hnxt
      | layer j =>
          by_cases hj : j.val < k
          · exfalso
            simp [layerNext, hj] at hnxt
          · exfalso
            cases a₂ <;> simp [layerNext, hj] at hnxt
      | acc =>
          have ha : a₁ ≠ a₂ := by
            intro h
            apply hne
            exact Prod.ext rfl h
          exact layerAmp_det_orth Us (.acc : LayerState k) a₁ a₂ ha
            (fun b => by simp [layerAmp]) (fun b => by simp [layerAmp])
      | rej =>
          exfalso
          simp [layerNext] at hnxt
      | meas2 =>
          exfalso
          cases a₂ <;> simp [layerNext] at hnxt
  | rej =>
      cases q₂ with
      | toInput =>
          exfalso
          simp [layerNext] at hnxt
      | layer j =>
          by_cases hj : j.val < k
          · exfalso
            simp [layerNext, hj] at hnxt
          · exfalso
            cases a₂ <;> simp [layerNext, hj] at hnxt
      | acc =>
          exfalso
          simp [layerNext] at hnxt
      | rej =>
          have ha : a₁ ≠ a₂ := by
            intro h
            apply hne
            exact Prod.ext rfl h
          exact layerAmp_det_orth Us (.rej : LayerState k) a₁ a₂ ha
            (fun b => by simp [layerAmp]) (fun b => by simp [layerAmp])
      | meas2 =>
          exfalso
          cases a₂ <;> simp [layerNext] at hnxt
  | meas2 =>
      cases q₂ with
      | toInput =>
          exfalso
          cases a₁ <;> simp [layerNext] at hnxt
      | layer j =>
          by_cases hj : j.val < k
          · exfalso
            cases a₁ <;> simp [layerNext, hj] at hnxt
          · have hj' : j.val = k := by omega
            have ha : a₁ = a₂ := by
              by_cases ha : a₁ = a₂
              · exact ha
              · exfalso
                rcases a₁ with _ | _ <;> rcases a₂ with _ | _
                all_goals simp_all [layerNext]
            have hconv : LayerState.layer j = measState k := by
              simp only [measState]
              congr 1
              apply Fin.ext
              show j.val = k
              exact hj'
            rw [hconv]
            exact (layerAmp_meas_orth Us a₂ a₁ ha.symm).2
      | acc =>
          exfalso
          cases a₁ <;> simp [layerNext] at hnxt
      | rej =>
          exfalso
          cases a₁ <;> simp [layerNext] at hnxt
      | meas2 =>
          exfalso
          cases a₁ <;> cases a₂
          all_goals first
            | exact absurd rfl hne
            | simp [layerNext] at hnxt

/-- Every layered-machine state other than `toInput` has a stay move. -/
theorem layerMove_eq_stay_of_ne {k : ℕ} (q : LayerState k) (hq : q ≠ .toInput) :
    layerMove q = QtmMove.stay := by
  cases q with
  | toInput => exact absurd rfl hq
  | layer i => rfl
  | acc => rfl
  | rej => rfl
  | meas2 => rfl

/-- No layered-machine state moves the head left. -/
theorem layerMove_ne_left {k : ℕ} (q : LayerState k) : layerMove q ≠ QtmMove.left := by
  cases q <;> simp [layerMove]

/-- No state other than `toInput` transitions to layer zero. -/
theorem layerNext_ne_layer0 {k : ℕ} (q : LayerState k) (a : Bool) (hq : q ≠ .toInput) :
    layerNext q a ≠ .layer 0 := by
  cases q with
  | toInput => exact absurd rfl hq
  | layer i =>
      by_cases h : i.val < k
      · simp [layerNext, h]
      · cases a <;> simp [layerNext, h]
  | acc => simp [layerNext]
  | rej => simp [layerNext]
  | meas2 => cases a <;> simp [layerNext]

/-- The local quantum machine that moves to the input, applies the given unitary sequence, and
records its Boolean outcome. -/
def layerLocalQTM {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) : LocalQTM (LayerState k) Bool where
  blank := false
  start := .toInput
  step := layerStep Us
  wf_norm := by
    intro q a
    classical
    rw [Finset.sum_eq_single_of_mem (layerNext q a) (Finset.mem_univ _)]
    · simp only [layerStep, eq_self, and_true]
      calc (∑ x : Bool, ∑ d : QtmMove,
            ‖(if d = layerMove q then layerAmp Us q a x else 0)‖ ^ 2)
          = ∑ x : Bool, ‖layerAmp Us q a x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [sum_norm_move]
        _ = 1 := layerAmp_norm Us hU q a
    · intro q' _ hne
      simp [layerStep, hne]
  wf_sameCell := by
    intro q₁ a₁ q₂ a₂ hne
    classical
    rw [Finset.sum_eq_single_of_mem (layerNext q₁ a₁) (Finset.mem_univ _)]
    · by_cases hnxt : layerNext q₁ a₁ = layerNext q₂ a₂
      · simp only [layerStep, eq_self, and_true, hnxt]
        have hsum : (∑ x : Bool, ∑ d : QtmMove, star (if d = layerMove q₁ then layerAmp Us q₁ a₁ x else 0) * (if d = layerMove q₂ then layerAmp Us q₂ a₂ x else 0))
            = ∑ x : Bool, (if layerMove q₁ = layerMove q₂ then star (layerAmp Us q₁ a₁ x) * layerAmp Us q₂ a₂ x else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sum_move_mul_star]
        rw [hsum]
        by_cases hmv : layerMove q₁ = layerMove q₂
        · simp only [if_pos hmv]
          exact layerAmp_orth Us hU q₁ q₂ a₁ a₂ hne hnxt
        · have hsum2 : (∑ x : Bool, if layerMove q₁ = layerMove q₂ then star (layerAmp Us q₁ a₁ x) * layerAmp Us q₂ a₂ x else 0)
              = ∑ x : Bool, 0 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [if_neg hmv]
          rw [hsum2]
          simp
      · rw [Finset.sum_eq_zero]
        intro x _
        rw [Finset.sum_eq_zero]
        intro d _
        simp only [layerStep, and_true]
        by_cases h1 : (d = layerMove q₁)
        · rw [if_pos h1]
          by_cases h2 : (d = layerMove q₂ ∧ layerNext q₁ a₁ = layerNext q₂ a₂)
          · rw [if_pos h2]
            exact (hnxt h2.2).elim
          · rw [if_neg h2]
            simp
        · rw [if_neg h1]
          simp
    · intro q' _ hne'
      simp [layerStep, hne']
  wf_rightStay := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    by_cases hq₂ : q₂ = .toInput
    · subst hq₂
      rw [show layerStep Us (.toInput : LayerState k) a₂ QtmMove.stay q' d = 0 by
        simp [layerStep, layerMove]]
      simp
    · by_cases hq₁ : q₁ = .toInput
      · subst hq₁
        rw [show layerStep Us (.toInput : LayerState k) a₁ QtmMove.right q' c
              = if q' = .layer 0 then layerAmp Us (.toInput : LayerState k) a₁ c else 0 by
          simp only [layerStep, layerMove, layerNext]
          by_cases h : q' = .layer 0 <;> simp [h]]
        rw [show layerStep Us q₂ a₂ QtmMove.stay q' d
              = if q' = layerNext q₂ a₂ then layerAmp Us q₂ a₂ d else 0 by
          simp [layerStep, layerMove_eq_stay_of_ne q₂ hq₂]]
        by_cases h1 : q' = .layer 0
        · rw [if_pos h1]
          by_cases h2 : q' = layerNext q₂ a₂
          · rw [if_pos h2]
            exfalso
            have hz : layerNext q₂ a₂ = .layer 0 := by
              rw [← h1]
              exact h2.symm
            exact (layerNext_ne_layer0 q₂ a₂ hq₂ hz).elim
          · rw [if_neg h2]
            simp
        · rw [if_neg h1]
          simp
      · rw [show layerStep Us q₁ a₁ QtmMove.right q' c = 0 by
          simp [layerStep, layerMove_eq_stay_of_ne q₁ hq₁]]
        simp
  wf_stayLeft := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    have hz : layerStep Us q₂ a₂ QtmMove.left q' d = 0 := by
      unfold layerStep
      rw [if_neg (by
        intro h
        exact (layerMove_ne_left q₂) h.1.symm)]
    rw [hz]
    simp
  wf_rightLeft := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    have hz : layerStep Us q₂ a₂ QtmMove.left q' d = 0 := by
      unfold layerStep
      rw [if_neg (by
        intro h
        exact (layerMove_ne_left q₂) h.1.symm)]
    rw [hz]
    simp

/-- The layered machine built from unitary gates satisfies the five local conditions. -/
theorem layerLocalQTM_five {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTMFiveConditions (layerLocalQTM Us hU) := by
  exact ⟨(layerLocalQTM Us hU).wf_norm, (layerLocalQTM Us hU).wf_sameCell,
    (layerLocalQTM Us hU).wf_rightStay, (layerLocalQTM Us hU).wf_stayLeft,
    (layerLocalQTM Us hU).wf_rightLeft⟩

/-- A layered-machine transition has its prescribed local amplitude precisely when the head
move, next state, and tape update agree with the rule. -/
theorem layerLocalQTM_windowStep {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w (LayerState k) Bool) :
    (windowStep (t := w) (layerLocalQTM Us hU) tgt) src =
      if moveCell (layerMove src.state) src.head = some tgt.head ∧
          tgt.state = layerNext src.state (src.tape src.head) ∧
          (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j)
      then layerAmp Us src.state (src.tape src.head) (tgt.tape src.head) else 0 := by
  classical
  simp only [windowStep, Matrix.of_apply, layerLocalQTM, layerStep]
  rw [Finset.sum_eq_single_of_mem (layerMove src.state) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (layerNext src.state (src.tape src.head))
      (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem (tgt.tape src.head) (Finset.mem_univ _)]
      · by_cases h : (moveCell (layerMove src.state) src.head = some tgt.head ∧
            tgt.state = layerNext src.state (src.tape src.head) ∧
            (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j))
        · simp only [if_pos h, and_self, eq_self, ↓reduceIte]
        · simp only [if_neg h]
      · intro b _ hb
        by_cases hcon : (moveCell (layerMove src.state) src.head = some tgt.head ∧
            tgt.state = layerNext src.state (src.tape src.head) ∧
            (∀ j, tgt.tape j = if j = src.head then b else src.tape j))
        · rw [if_pos hcon]
          have hlt : tgt.tape src.head = b := by
            have hstep := hcon.2.2 src.head
            simpa using! hstep
          exact (hb hlt.symm).elim
        · rw [if_neg hcon]
    · intro q' _ hq
      apply Finset.sum_eq_zero
      intro b _
      by_cases hcon : (moveCell (layerMove src.state) src.head = some tgt.head ∧
          tgt.state = q' ∧
          (∀ j, tgt.tape j = if j = src.head then b else src.tape j))
      · rw [if_pos hcon]
        rw [if_neg (fun hh => hq hh.2)]
      · rw [if_neg hcon]
  · intro d _ hd
    apply Finset.sum_eq_zero
    intro q' _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hcon : (moveCell d src.head = some tgt.head ∧ tgt.state = q' ∧
        (∀ j, tgt.tape j = if j = src.head then b else src.tape j))
    · rw [if_pos hcon]
      rw [if_neg (fun hh => hd hh.1)]
    · rw [if_neg hcon]

/-- One step from a layered basis configuration has the prescribed local amplitude on valid
successor configurations and zero elsewhere. -/
theorem layerLocalQTM_windowStep_ket {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w (LayerState k) Bool) :
    (windowStep (t := w) (layerLocalQTM Us hU) *ᵥ Ket src) tgt =
      if moveCell (layerMove src.state) src.head = some tgt.head ∧
          tgt.state = layerNext src.state (src.tape src.head) ∧
          (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j)
      then layerAmp Us src.state (src.tape src.head) (tgt.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact layerLocalQTM_windowStep Us hU src tgt
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- The state field of a layered configuration is its supplied state. -/
theorem layerCfg_state {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (q : LayerState k) (b : Bool) :
    (layerCfg base q b).state = q := rfl

/-- Constructing a layered configuration preserves the base head position. -/
theorem layerCfg_head {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (q : LayerState k) (b : Bool) :
    (layerCfg base q b).head = base.head := rfl

/-- The layered configuration tape is the base tape with the head cell replaced by the supplied
bit. -/
theorem layerCfg_tape {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (q : LayerState k) (b : Bool) (j : Fin (2 * w + 1)) :
    (layerCfg base q b).tape j = if j = base.head then b else base.tape j := rfl

/-- The tape symbol at the base head in a layered configuration is its supplied bit. -/
theorem layerCfg_tape_at {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (q : LayerState k) (b : Bool) :
    (layerCfg base q b).tape base.head = b := by
  simp [layerCfg]

/-- A layered configuration agrees with the base tape away from the head cell. -/
theorem layerCfg_tape_of_ne {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (q : LayerState k) (b : Bool) {j : Fin (2 * w + 1)} (hj : j ≠ base.head) :
    (layerCfg base q b).tape j = base.tape j := by
  simp [layerCfg, hj]

/-- Window configurations with equal heads, states, and tape symbols are equal. -/
theorem WindowCfg_eq_of_fields {w : ℕ} {Q A : Type} (c₁ c₂ : WindowCfg w Q A)
    (hh : c₁.head = c₂.head) (hs : c₁.state = c₂.state)
    (ht : ∀ j, c₁.tape j = c₂.tape j) : c₁ = c₂ := by
  cases c₁
  cases c₂
  simp only [WindowCfg.mk.injEq]
  refine ⟨hh, hs, ?_⟩
  funext j
  simpa using! ht j

/-- Layered configurations with different supplied bits are distinct. -/
theorem layerCfg_ne {k w : ℕ} (base : WindowCfg w (LayerState k) Bool)
    (q : LayerState k) {b0 b1 : Bool} (h : b0 ≠ b1) :
    layerCfg base q b0 ≠ layerCfg base q b1 := by
  intro heq
  have h' := congrArg (fun c => c.tape base.head) heq
  simp [layerCfg] at h'
  exact (h h').elim

/-- A layered transition is characterized by its head move, next state, and agreement of the
tapes away from the source head. -/
theorem layerLocalQTM_windowStep_norm {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w (LayerState k) Bool) :
    (windowStep (t := w) (layerLocalQTM Us hU) tgt) src =
      if moveCell (layerMove src.state) src.head = some tgt.head ∧
          tgt.state = layerNext src.state (src.tape src.head) ∧
          (∀ j, j ≠ src.head → tgt.tape j = src.tape j)
      then layerAmp Us src.state (src.tape src.head) (tgt.tape src.head) else 0 := by
  have hiff : (moveCell (layerMove src.state) src.head = some tgt.head ∧
        tgt.state = layerNext src.state (src.tape src.head) ∧
        (∀ j, tgt.tape j = if j = src.head then tgt.tape src.head else src.tape j))
      ↔ (moveCell (layerMove src.state) src.head = some tgt.head ∧
        tgt.state = layerNext src.state (src.tape src.head) ∧
        (∀ j, j ≠ src.head → tgt.tape j = src.tape j)) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro j hj
      have hj' := h3 j
      simp only [if_neg hj] at hj'
      exact hj'
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro j
      by_cases hj : j = src.head
      · simp [hj]
      · simp [hj, h3 j hj]
  rw [layerLocalQTM_windowStep Us hU src tgt]
  by_cases h : (moveCell (layerMove src.state) src.head = some tgt.head ∧
      tgt.state = layerNext src.state (src.tape src.head) ∧
      (∀ j, j ≠ src.head → tgt.tape j = src.tape j))
  · simp only [if_pos h]
    rw [if_pos (hiff.mpr h)]
  · simp only [if_neg h]
    rw [if_neg (fun hh => h (hiff.mp hh))]

/-- The amplitude after a layered step from a basis ket is the local amplitude exactly when the
head move, next state, and off-head tape agreement hold. -/
theorem layerLocalQTM_windowStep_ket_norm {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt : WindowCfg w (LayerState k) Bool) :
    (windowStep (t := w) (layerLocalQTM Us hU) *ᵥ Ket src) tgt =
      if moveCell (layerMove src.state) src.head = some tgt.head ∧
          tgt.state = layerNext src.state (src.tape src.head) ∧
          (∀ j, j ≠ src.head → tgt.tape j = src.tape j)
      then layerAmp Us src.state (src.tape src.head) (tgt.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact layerLocalQTM_windowStep_norm Us hU src tgt
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- One layered-machine step advances a two-basis-state superposition and multiplies its two
amplitudes by the unitary for that layer. -/
theorem layerLocalQTM_layerEvolution {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (j : ℕ) (hj : j < k)
    (α β : ℂ) :
    (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ
        (α • Ket (layerCfg base (.layer ⟨j, by omega⟩) false) +
          β • Ket (layerCfg base (.layer ⟨j, by omega⟩) true))
      = (Us ⟨j, by omega⟩ false false * α
          + Us ⟨j, by omega⟩ false true * β) •
          Ket (layerCfg base (.layer ⟨j + 1, by omega⟩) false) +
        (Us ⟨j, by omega⟩ true false * α
          + Us ⟨j, by omega⟩ true true * β) •
          Ket (layerCfg base (.layer ⟨j + 1, by omega⟩) true) := by
  classical
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  ext tgt
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [layerLocalQTM_windowStep_ket_norm, layerLocalQTM_windowStep_ket_norm]
  simp only [layerCfg_state, layerCfg_head, layerMove, moveCell, layerNext,
    layerAmp, hj, layerCfg_tape, Option.some.injEq, dif_pos,
    if_pos]
  have htab : (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j)
      ↔ (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then true else base.tape j) := by
    constructor
    · intro h j hj
      have hh := h j hj
      rw [if_neg hj] at hh
      rw [if_neg hj]
      exact hh
    · intro h j hj
      have hh := h j hj
      rw [if_neg hj] at hh
      rw [if_neg hj]
      exact hh
  by_cases h : (base.head = tgt.head ∧ tgt.state = .layer ⟨j + 1, by omega⟩ ∧
      (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j))
  · rw [if_pos h]
    have h1 : (base.head = tgt.head ∧ tgt.state = .layer ⟨j + 1, by omega⟩ ∧
        (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then true else base.tape j)) :=
      ⟨h.1, h.2.1, fun j hj => (htab.mp h.2.2) j hj⟩
    rw [if_pos h1]
    by_cases hb : tgt.tape base.head = false
    · have htgt : tgt = layerCfg base (.layer ⟨j + 1, by omega⟩) false := by
        apply WindowCfg_eq_of_fields
        · exact h.1.symm
        · exact h.2.1
        · intro i
          by_cases hi : i = base.head
          · simp [layerCfg, hi, hb]
          · have hh := h.2.2 i hi
            simp only [if_neg hi] at hh
            simp [layerCfg, hi, hh]
      rw [htgt]
      have hne : layerCfg base (.layer ⟨j + 1, by omega⟩) false
          ≠ layerCfg base (.layer ⟨j + 1, by omega⟩) true :=
        layerCfg_ne base _ (by simp)
      simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, layerCfg_tape_at]
      rw [if_neg hne]
      ring
    · have htgt : tgt = layerCfg base (.layer ⟨j + 1, by omega⟩) true := by
        apply WindowCfg_eq_of_fields
        · exact h.1.symm
        · exact h.2.1
        · intro i
          by_cases hi : i = base.head
          · simp [layerCfg, hi, hb]
          · have hh := h.2.2 i hi
            simp only [if_neg hi] at hh
            simp [layerCfg, hi, hh]
      rw [htgt]
      have hne : layerCfg base (.layer ⟨j + 1, by omega⟩) true
          ≠ layerCfg base (.layer ⟨j + 1, by omega⟩) false :=
        layerCfg_ne base _ (by simp)
      simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, layerCfg_tape_at]
      rw [if_neg hne]
      ring
  · rw [if_neg h]
    have h1 : ¬ (base.head = tgt.head ∧ tgt.state = .layer ⟨j + 1, by omega⟩ ∧
        (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then true else base.tape j)) :=
      fun hh => h ⟨hh.1, hh.2.1, fun j hj => (htab.mpr hh.2.2) j hj⟩
    rw [if_neg h1]
    by_cases h0 : tgt = layerCfg base (.layer ⟨j + 1, by omega⟩) false
    · exfalso
      have hcond' : base.head = tgt.head ∧
          tgt.state = .layer ⟨j + 1, by omega⟩ ∧
          (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j) := by
        rw [h0]
        refine ⟨rfl, rfl, ?_⟩
        intro j hj
        simp [layerCfg, hj]
      exact h hcond'
    · by_cases h2 : tgt = layerCfg base (.layer ⟨j + 1, by omega⟩) true
      · exfalso
        have hcond' : base.head = tgt.head ∧
            tgt.state = .layer ⟨j + 1, by omega⟩ ∧
            (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j) := by
          rw [h2]
          refine ⟨rfl, rfl, ?_⟩
          intro j hj
          simp [layerCfg, hj]
        exact h hcond'
      · simp [Qatlib.Foundations.PureStateMath.Ket, h0, h2]

/-- One layered step advances `layerCfgSuper` and applies the corresponding unitary to its
Boolean amplitude vector. -/
theorem layerLocalQTM_gateStep_super {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (j : ℕ) (hj : j < k) (v : Bool → ℂ) :
    (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ layerCfgSuper base j (by omega) v
      = layerCfgSuper base (j + 1) (by omega) (Us ⟨j, by omega⟩ *ᵥ v) := by
  rw [layerCfgSuper, layerCfgSuper, Matrix.mulVec_add, ← Matrix.mulVec_add]
  rw [layerLocalQTM_layerEvolution Us hU base j hj (v false) (v true)]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply]
  ring

/-- After `j ≤ k` steps, the layered superposition is at layer `j` with amplitude vector
multiplied by the first `j` gates. -/
theorem layerLocalQTM_gateSeq {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (v : Bool → ℂ) :
    ∀ (j : ℕ) (hj : j ≤ k),
      (windowStep (t := w) (layerLocalQTM Us hU)) ^ j *ᵥ layerCfgSuper base 0 (by omega) v
        = layerCfgSuper base j hj (gateSeqProd Us j hj *ᵥ v) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [layerCfgSuper, pow_zero, Matrix.one_mulVec, gateSeqProd]
  | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [ih (by omega)]
      rw [layerLocalQTM_gateStep_super Us hU base j hjk]
      rw [Matrix.mulVec_mulVec]
      have hprod : gateSeqProd Us (j + 1) hj
          = Us ⟨j, by omega⟩ * gateSeqProd Us j (by omega) := rfl
      rw [hprod]

/-- The terminal layer maps a basis bit to its accepting or rejecting configuration while
flipping that tape bit. -/
theorem layerLocalQTM_measure_ket {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (a : Bool)
    (tgt : WindowCfg w (LayerState k) Bool) :
    (windowStep (t := w) (layerLocalQTM Us hU) *ᵥ Ket (layerCfg base (.layer ⟨k, by omega⟩) a)) tgt
      = (if tgt = layerCfg base (if a then .acc else .rej) (!a) then 1 else 0) := by
  classical
  rw [layerLocalQTM_windowStep_ket_norm]
  simp only [layerCfg_state, layerCfg_head, layerCfg_tape_at]
  rw [show moveCell (layerMove (.layer ⟨k, by omega⟩)) base.head = some base.head by
    simp [layerMove, moveCell]]
  rw [show layerNext (.layer ⟨k, by omega⟩) a = (if a then .acc else .rej) by
    simp [layerNext]]
  rw [show layerAmp Us (.layer ⟨k, by omega⟩) a (tgt.tape base.head)
      = (if tgt.tape base.head = !a then 1 else 0) by simp [layerAmp]]
  simp only [Option.some.injEq]
  by_cases hC : (base.head = tgt.head ∧ tgt.state = (if a then .acc else .rej) ∧
      (∀ j, j ≠ base.head → tgt.tape j = (layerCfg base (.layer ⟨k, by omega⟩) a).tape j))
  · rw [if_pos hC]
    by_cases hflip : tgt.tape base.head = !a
    · rw [if_pos hflip]
      have hcon : tgt = layerCfg base (if a then .acc else .rej) (!a) := by
        apply WindowCfg_eq_of_fields
        · exact hC.1.symm
        · exact hC.2.1
        · intro j
          by_cases hj : j = base.head
          · subst hj
            simp [layerCfg, hflip]
          · have hh := hC.2.2 j hj
            simp [layerCfg, hj] at hh
            simp [layerCfg, hj]
            exact hh
      rw [if_pos hcon]
    · rw [if_neg hflip]
      rw [if_neg]
      intro hcon
      have hh := congrArg (fun c => c.tape base.head) hcon
      simp [layerCfg] at hh
      exact hflip hh
  · rw [if_neg hC]
    rw [if_neg]
    intro hcon
    have hstate := congrArg WindowCfg.state hcon
    have htape := congrArg (fun c => c.tape) hcon
    refine hC ⟨?_, ?_, ?_⟩
    · have hh := congrArg WindowCfg.head hcon
      simpa [layerCfg] using! hh.symm
    · simpa [layerCfg] using! hstate
    · intro j hj
      have hh := congrFun htape j
      simp [layerCfg, hj] at hh
      rw [layerCfg_tape base (.layer ⟨k, by omega⟩) a j]
      simp [hj]
      exact hh

/-- A step from the terminal-layer superposition separates its false and true amplitudes into
rejecting and accepting basis configurations. -/
theorem layerLocalQTM_measure {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (v : Bool → ℂ) :
    (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ layerCfgSuper base k (by omega) v
      = v false • Ket (layerCfg base (.rej) true) + v true • Ket (layerCfg base (.acc) false) := by
  classical
  funext tgt
  rw [layerCfgSuper, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have h1 := layerLocalQTM_measure_ket Us hU base false tgt
  have h2 := layerLocalQTM_measure_ket Us hU base true tgt
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [h1, h2]
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- After the gate sequence and measurement step, total accepting Born mass is the squared norm
of the true component of the resulting amplitude vector. -/
theorem layerLocalQTM_acceptMass {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (v : Bool → ℂ) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
      BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 1) *ᵥ
        layerCfgSuper base 0 (by omega) v) c)
      = ‖(gateSeqProd Us k (by omega) *ᵥ v) true‖ ^ 2 := by
  classical
  have hψ : (windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 1) *ᵥ
      layerCfgSuper base 0 (by omega) v
      = (gateSeqProd Us k (by omega) *ᵥ v) false • Ket (layerCfg base (.rej) true) +
        (gateSeqProd Us k (by omega) *ᵥ v) true • Ket (layerCfg base (.acc) false) := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [layerLocalQTM_gateSeq Us hU base v k (by omega)]
    rw [layerLocalQTM_measure Us hU base (gateSeqProd Us k (by omega) *ᵥ v)]
  rw [hψ]
  have hne : layerCfg base (.acc) false ≠ layerCfg base (.rej) true := by
    intro hcon
    have hh := congrArg WindowCfg.state hcon
    simp [layerCfg_state] at hh
  rw [Finset.sum_eq_single (layerCfg base (.acc) false)]
  · have hval : ((gateSeqProd Us k (by omega) *ᵥ v) false • Ket (layerCfg base (.rej) true) +
        (gateSeqProd Us k (by omega) *ᵥ v) true • Ket (layerCfg base (.acc) false))
        (layerCfg base (.acc) false)
      = (gateSeqProd Us k (by omega) *ᵥ v) true := by
      simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, hne]
    rw [BornProb, hval]
  · intro c hc hne'
    have hstate : c.state = (.acc : LayerState k) := (Finset.mem_filter.mp hc).2
    rw [BornProb]
    have hne1 : c ≠ layerCfg base (.rej) true := by
      intro hcon
      have hh := congrArg WindowCfg.state hcon
      simp [layerCfg_state] at hh
      exact absurd (hstate.symm.trans hh) (by simp)
    simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, hne1, hne']
  · intro h
    exact (h (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, layerCfg_state base (.acc : LayerState k) false⟩)).elim

/-- Applying a one-qubit-register matrix to a basis ket gives the corresponding matrix column. -/
theorem applyGate_reg1_ket (U : Matrix (Reg 1) (Reg 1) ℂ) (x y : Reg 1) :
    ApplyGate U (Ket x) y = U y x := by
  rw [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single x]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro b _ hb
    simp [Qatlib.Foundations.PureStateMath.Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The identity Boolean matrix is unitary. -/
theorem one_unitary : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp [star_one]

/-- The Boolean matrix that flips the basis bit. -/
def bitFlip : Matrix Bool Bool ℂ := fun b a => if b = !a then 1 else 0

/-- The Boolean bit-flip matrix is unitary. -/
theorem bitFlip_unitary : bitFlip ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext b a
  simp [Matrix.mul_apply, Matrix.star_apply, bitFlip, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · have h2 : b ≠ a := fun hh => h hh.symm
    simp [h, h2]

/-- One-qubit registers are equal when their unique bits agree. -/
theorem reg1_ext {x y : Reg 1} (h : x ⟨0, by omega⟩ = y ⟨0, by omega⟩) : x = y := by
  funext j
  have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
  rw [hj]
  exact h

/-- The action of a one-qubit-register matrix corresponds to `reg1Gate` multiplication on
Boolean amplitude vectors. -/
theorem applyGate_reg1 (U : Matrix (Reg 1) (Reg 1) ℂ) (v : Bool → ℂ) (y : Reg 1) :
    ApplyGate U (fun z => v (reg1Bool z)) y = (reg1Gate U *ᵥ v) (reg1Bool y) := by
  classical
  have hreindex : (∑ z : Reg 1, U y z * v (reg1Bool z))
      = ∑ a : Bool, U y (reg1Bool.symm a) * v a := by
    refine Fintype.sum_equiv reg1Bool (fun z : Reg 1 => U y z * v (reg1Bool z))
      (fun a : Bool => U y (reg1Bool.symm a) * v a) (fun z => ?_)
    show U y z * v (reg1Bool z)
        = U y (reg1Bool.symm (reg1Bool z)) * v (reg1Bool z)
    rw [Equiv.symm_apply_apply]
  calc ApplyGate U (fun z => v (reg1Bool z)) y
      = ∑ z : Reg 1, U y z * v (reg1Bool z) := by
        simp [ApplyGate, Matrix.mulVec, dotProduct]
    _ = ∑ a : Bool, U y (reg1Bool.symm a) * v a := hreindex
    _ = (reg1Gate U *ᵥ v) (reg1Bool y) := by
        symm
        simp only [Matrix.mulVec, dotProduct, reg1Gate, Equiv.symm_apply_apply]

/-- Running a list of one-qubit-register gates corresponds to multiplying by the product of
their Boolean matrices. -/
theorem run_reg1 (gs : List (Matrix (Reg 1) (Reg 1) ℂ)) (v : Bool → ℂ) (y : Reg 1) :
    (Run (1 : Matrix (Reg 1) (Reg 1) ℂ) (gs.map Step.gate) (fun z => v (reg1Bool z))) y
      = (boolGateProd (gs.map reg1Gate) *ᵥ v) (reg1Bool y) := by
  classical
  induction gs generalizing v with
  | nil =>
      simp [boolGateProd, Matrix.one_mulVec]
  | cons U gs ih =>
      simp only [List.map_cons, Run]
      rw [funext (applyGate_reg1 U v)]
      rw [ih]
      rw [Matrix.mulVec_mulVec]
      simp [boolGateProd]

/-- A one-wire state's acceptance probability is the squared norm of its true-basis amplitude. -/
theorem acceptProb_oneWire (ψ : QState (Reg 1)) (h : 0 < 1) :
    AcceptProb ψ h = ‖ψ (reg1Bool.symm true)‖ ^ 2 := by
  classical
  rw [AcceptProb, MeasureProb]
  have hfilter : Finset.univ.filter (fun x : Reg 1 => x ⟨0, by omega⟩ = true)
      = {reg1Bool.symm true} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have h1 : x = reg1Bool.symm (x ⟨0, by omega⟩) := by
        funext j
        have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
        rw [hj]
        rfl
      calc x = reg1Bool.symm (x ⟨0, by omega⟩) := h1
        _ = reg1Bool.symm true := by rw [hx]
    · intro hx
      subst hx
      rfl
  rw [hfilter]
  rw [Finset.sum_eq_single (reg1Bool.symm true)]
  · rfl
  · intro b hmem hb
    have hba : b = reg1Bool.symm true := Finset.mem_singleton.mp hmem
    exact (hb hba).elim
  · intro hmem
    exact absurd (Finset.mem_singleton.mpr rfl) hmem

/-- A one-qubit basis ket is the Boolean amplitude function `wireAmp` transported through
`reg1Bool`. -/
theorem ket_eq_wireAmp (x : Reg 1) : Ket x = fun z => wireAmp x (reg1Bool z) := by
  funext z
  simp only [Qatlib.Foundations.PureStateMath.Ket, wireAmp]
  by_cases h : z = x
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (by
      intro hh
      apply h
      apply reg1_ext
      have hh' := hh
      rw [show reg1Bool z = z ⟨0, by omega⟩ from rfl] at hh'
      rw [show x ⟨0, by omega⟩ = reg1Bool x from rfl] at hh'
      exact hh')]

/-- When the right neighbor exists, the input-routing step sends its basis configuration to the
corresponding `layerWalk` configuration. -/
theorem layerLocalQTM_walk {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (b : Bool)
    (h' : Fin (2 * w + 1)) (hh : h'.val = base.head.val + 1) :
    (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ Ket (layerCfg base (.toInput) b)
      = Ket (layerWalk (layerCfg base (.toInput) b) h') := by
  classical
  have hlt : base.head.val + 1 < 2 * w + 1 := by
    have := h'.isLt
    omega
  have hmove : moveCell (layerMove (.toInput : LayerState k)) base.head = some h' := by
    simp only [layerMove, moveCell]
    split
    · rename_i hbad
      omega
    · have heq : (⟨base.head.val + 1, by omega⟩ : Fin (2 * w + 1)) = h' := Fin.ext hh.symm
      rw [heq]
  have hamp : ∀ t : Bool, layerAmp Us (.toInput : LayerState k) b t
      = if t = b then 1 else 0 := by
    intro t
    simp [layerAmp]
  funext tgt
  rw [layerLocalQTM_windowStep_ket_norm]
  simp only [layerCfg_state, layerCfg_head, layerCfg_tape_at]
  by_cases hcond : (moveCell (layerMove (.toInput : LayerState k)) base.head = some tgt.head ∧
      tgt.state = layerNext (.toInput : LayerState k) b ∧
      (∀ j, j ≠ base.head → tgt.tape j = (layerCfg base (.toInput) b).tape j))
  · rw [if_pos hcond, hamp]
    by_cases hsym : tgt.tape base.head = b
    · rw [if_pos hsym]
      have hEq : tgt = layerWalk (layerCfg base (.toInput) b) h' := by
        refine WindowCfg_eq_of_fields tgt (layerWalk (layerCfg base (.toInput) b) h') ?_ ?_ ?_
        · have h1 := hcond.1
          rw [hmove] at h1
          have h1' : tgt.head = h' := Option.some.inj h1 |>.symm
          simpa [layerWalk, layerCfg] using! h1'
        · have h2 := hcond.2.1
          simpa only [layerNext] using! h2
        · intro j
          by_cases hj : j = base.head
          · subst hj
            have h1 : (layerWalk (layerCfg base (.toInput) b) h').tape base.head
                = (layerCfg base (.toInput) b).tape base.head := rfl
            have h2 : (layerCfg base (.toInput) b).tape base.head = b := layerCfg_tape_at base _ _
            rw [h1, h2]
            exact hsym
          · have h3 := hcond.2.2 j hj
            have h1 : (layerWalk (layerCfg base (.toInput) b) h').tape j
                = (layerCfg base (.toInput) b).tape j := rfl
            have h4 : (layerCfg base (.toInput) b).tape j = base.tape j := by
              simp only [layerCfg_tape, if_neg hj]
            rw [h1, h4]
            exact h3.trans h4
      simp [Qatlib.Foundations.PureStateMath.Ket, hEq]
    · rw [if_neg hsym]
      have hEq : tgt ≠ layerWalk (layerCfg base (.toInput) b) h' := by
        intro heq
        apply hsym
        have h1 := congrArg (fun c => c.tape base.head) heq
        have h1' : tgt.tape base.head
            = (layerWalk (layerCfg base (.toInput) b) h').tape base.head := by
          simpa using! h1
        have h2 : (layerWalk (layerCfg base (.toInput) b) h').tape base.head
            = (layerCfg base (.toInput) b).tape base.head := rfl
        have h3 : (layerCfg base (.toInput) b).tape base.head = b := layerCfg_tape_at base _ _
        rw [h2, h3] at h1'
        exact h1'
      simp [Qatlib.Foundations.PureStateMath.Ket, hEq]
  · rw [if_neg hcond]
    have hEq : tgt ≠ layerWalk (layerCfg base (.toInput) b) h' := by
      intro heq
      have h1 := congrArg WindowCfg.head heq
      have h2 := congrArg WindowCfg.state heq
      have h3 := congrArg (fun c => c.tape) heq
      refine hcond ⟨?_, ?_, ?_⟩
      · have h1' : tgt.head = h' := by
          simp [layerWalk, layerCfg] at h1
          exact h1
        have hmv := hmove
        rw [h1']
        exact hmv
      · simpa only [layerNext, layerCfg, layerWalk] using! h2
      · intro j hj
        have hj' := congrFun h3 j
        have hj'' : tgt.tape j = (layerCfg base (.toInput) b).tape j := by
          simpa [layerWalk] using! hj'
        exact hj''
    simp [Qatlib.Foundations.PureStateMath.Ket, hEq]

/-- A layer-zero basis configuration equals the layered superposition concentrated on its
head-cell bit. -/
theorem ket_eq_layerCfgSuper {k w : ℕ} (base : WindowCfg w (LayerState k) Bool) (b : Bool)
    (hb : base.tape base.head = b) (hst : base.state = .layer 0) :
    Ket base = layerCfgSuper base 0 (by omega) (fun c => if c = b then (1 : ℂ) else 0) := by
  classical
  have hcfg : base = layerCfg base (.layer ⟨0, by omega⟩) b := by
    refine WindowCfg_eq_of_fields base (layerCfg base (.layer ⟨0, by omega⟩) b) rfl ?_ ?_
    · simpa [layerCfg] using! hst
    · intro j
      by_cases hj : j = base.head
      · subst hj
        simp [layerCfg, hb]
      · simp [layerCfg, hj]
  funext y
  rw [layerCfgSuper]
  simp only [Pi.add_apply, Pi.smul_apply]
  by_cases hbf : b = false
  · rw [hbf]
    rw [if_pos rfl, if_neg (by simp)]
    simp only [one_smul, zero_smul]
    have hcfgF : base = layerCfg base (.layer ⟨0, by omega⟩) false := by
      rw [hbf] at hcfg
      exact hcfg
    rw [hcfgF.symm]
    exact (add_zero (Ket base y : ℂ)).symm
  · have hbt : b = true := by
      cases b with
      | false => exact absurd (by simp : false = false) hbf
      | true => rfl
    rw [hbt]
    rw [if_neg (by simp), if_pos rfl]
    simp only [one_smul, zero_smul]
    have hcfgT : base = layerCfg base (.layer ⟨0, by omega⟩) true := by
      rw [hbt] at hcfg
      exact hcfg
    rw [hcfgT.symm]
    exact (zero_add (Ket base y : ℂ)).symm

/-- After `k+1` steps, a layer-zero superposition has rejecting and accepting amplitudes equal
to the false and true components of the full gate product. -/
theorem layerLocalQTM_gateSeq_measure {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (LayerState k) Bool) (v : Bool → ℂ) :
    (windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 1) *ᵥ layerCfgSuper base 0 (by omega) v
      = (gateSeqProd Us k (by omega) *ᵥ v) false • Ket (layerCfg base (.rej) true) +
        (gateSeqProd Us k (by omega) *ᵥ v) true • Ket (layerCfg base (.acc) false) := by
  classical
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rw [layerLocalQTM_gateSeq Us hU base v k (by omega)]
  rw [layerLocalQTM_measure Us hU base (gateSeqProd Us k (by omega) *ᵥ v)]

/-- Multiplying a prefix product of the tail sequence by the first gate gives the corresponding
longer prefix product of the full sequence. -/
theorem gateSeqProd_cons {k : ℕ} (Us : Fin (k+1) → Matrix Bool Bool ℂ) :
    ∀ (j : ℕ) (hj : j ≤ k),
      gateSeqProd (fun i => Us i.succ) j (by omega) * Us 0
        = gateSeqProd Us (j+1) (by omega) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [gateSeqProd]
  | succ j ih =>
      intro hj
      have h1 : gateSeqProd (fun i => Us i.succ) (j + 1) (by omega)
          = Us ⟨j + 1, by omega⟩ * gateSeqProd (fun i => Us i.succ) j (by omega) := rfl
      have h2 : gateSeqProd Us (j + 2) (by omega)
          = Us ⟨j + 1, by omega⟩ * gateSeqProd Us (j + 1) (by omega) := rfl
      rw [h1, h2]
      rw [Matrix.mul_assoc]
      rw [ih (by omega)]

/-- The product of a finite gate sequence listed by `List.ofFn` equals its full `gateSeqProd`. -/
theorem boolGateProd_ofFn : ∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ),
    boolGateProd (List.ofFn Us) = gateSeqProd Us k (by omega) := by
  intro k
  induction k with
  | zero =>
      intro Us
      rfl
  | succ k ih =>
      intro Us
      rw [List.ofFn_succ, boolGateProd]
      rw [ih (fun i => Us i.succ)]
      rw [gateSeqProd_cons Us (k) (by omega)]

/-- Converting a Boolean gate to a one-qubit-register matrix and back returns the original gate. -/
theorem reg1Gate_reg1Gate' (U : Matrix Bool Bool ℂ) : reg1Gate (reg1Gate' U) = U := by
  funext b a
  rfl

/-- The initialized layered machine has the false blank symbol at its head. -/
theorem init_tape_head {k w n : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (x : Reg n) :
    (initWindowCfg (t := w) (layerLocalQTM Us hU) n x).tape
        (initWindowCfg (t := w) (layerLocalQTM Us hU) n x).head = false := by
  simp [initWindowCfg, layerLocalQTM]

/-- For positive input and window widths, the cell immediately right of the initialized head
contains the first input bit. -/
theorem init_tape_succ {k w n : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (hw : 0 < w) (hn : 0 < n) (x : Reg n)
    (j : Fin (2 * w + 1)) (hj : j.val = w + 1) :
    (initWindowCfg (t := w) (layerLocalQTM Us hU) n x).tape j
      = x ⟨0, hn⟩ := by
  have hj' : j = ⟨w + 1, by omega⟩ := Fin.ext hj
  rw [hj']
  have h1n : 1 ≤ n := by omega
  simp [initWindowCfg, layerLocalQTM, h1n]

/-- Replacing a configuration's state and head-cell bit by their existing values leaves the
configuration unchanged. -/
theorem layerCfg_eq_self {k w : ℕ} (base : WindowCfg w (LayerState k) Bool) (q : LayerState k)
    (b : Bool) (hq : base.state = q) (hb : base.tape base.head = b) :
    layerCfg base q b = base := by
  refine WindowCfg_eq_of_fields _ _ rfl ?_ ?_
  · simpa [layerCfg] using! hq.symm
  · intro j
    by_cases hj : j = base.head
    · subst hj
      simp [layerCfg, hb]
    · simp [layerCfg, hj]

/-- For a positive window width, the layered machine's accepting Born mass after `k+2` steps
equals the acceptance probability of the corresponding one-wire circuit. -/
theorem headStay_acceptProb_oneWire
    (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ)
    (w : ℕ) (hw : 0 < w) (x : Reg 1) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
      BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
        *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x)) c)
      = AcceptProb (Run (1 : Matrix (Reg 1) (Reg 1) ℂ)
          ((List.ofFn (fun i => reg1Gate' (Us i))).map Step.gate) (Ket x)) (by omega) := by
  classical
  set h' : Fin (2 * w + 1) := ⟨w + 1, by omega⟩ with h'eq
  have hinit : layerCfg (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) (.toInput) false
      = initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x :=
    layerCfg_eq_self _ _ _ (by rfl)
      (by simpa [layerLocalQTM] using! init_tape_head Us hU x)
  have hstep : (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ
        Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x)
      = Ket (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h') := by
    have hhead : (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x).head.val = w := rfl
    have h := layerLocalQTM_walk Us hU
      (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) false h' (by
        simp only [h']
        rw [hhead])
    rw [hinit] at h
    exact h
  have hbase_state :
      (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h').state = .layer 0 := rfl
  have hhead : (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x).head.val = w := rfl
  have h'val : h'.val = w + 1 := by
    simp only [h']
  have hne : h' ≠ (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x).head := by
    intro heq
    have hh := congrArg Fin.val heq
    rw [hhead] at hh
    simp only [h'] at hh
    omega
  have hbase_tape :
      (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h').tape
        (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h').head
        = x ⟨0, by omega⟩ := by
    have h1 : (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h').tape
          (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h').head
        = (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x).tape h' := by
      simp only [layerWalk]
    rw [h1]
    exact init_tape_succ Us hU hw (by omega) x h' h'val

  have hmach : (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
        BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
          *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x)) c)
      = ‖(gateSeqProd Us k (by omega) *ᵥ wireAmp x) true‖ ^ 2 := by
    have hsuper : Ket (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h')
        = layerCfgSuper (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h') 0 (by omega)
            (fun c => if c = x ⟨0, by omega⟩ then (1 : ℂ) else 0) :=
      ket_eq_layerCfgSuper _ _ hbase_tape hbase_state
    have hmass : (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
        BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 1)
          *ᵥ layerCfgSuper (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x) h') 0 (by omega)
            (fun c => if c = x ⟨0, by omega⟩ then (1 : ℂ) else 0)) c)
        = ‖(gateSeqProd Us k (by omega) *ᵥ
            (fun c => if c = x ⟨0, by omega⟩ then (1 : ℂ) else 0)) true‖ ^ 2 :=
      layerLocalQTM_acceptMass Us hU _ _
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    rw [hstep]
    rw [hsuper]
    rw [hmass]
    rfl

  have hstd : AcceptProb (Run (1 : Matrix (Reg 1) (Reg 1) ℂ)
        ((List.ofFn (fun i => reg1Gate' (Us i))).map Step.gate) (Ket x)) (by omega)
      = ‖(boolGateProd ((List.ofFn (fun i => reg1Gate' (Us i))).map reg1Gate)
          *ᵥ wireAmp x) true‖ ^ 2 := by
    have hamp : Ket x = fun z => wireAmp x (reg1Bool z) := ket_eq_wireAmp x
    rw [acceptProb_oneWire]
    rw [hamp]
    have hrun := run_reg1 (List.ofFn (fun i => reg1Gate' (Us i))) (wireAmp x)
      (reg1Bool.symm true)
    rw [hrun]
    rw [Equiv.apply_symm_apply]

  rw [hmach, hstd]
  have hprod : boolGateProd ((List.ofFn (fun i => reg1Gate' (Us i))).map reg1Gate)
      = gateSeqProd Us k (by omega) := by
    have h1 : (List.ofFn (fun i => reg1Gate' (Us i))).map reg1Gate
        = List.ofFn (fun i => reg1Gate (reg1Gate' (Us i))) := by
      rw [List.map_ofFn]
      congr 1
    rw [h1]
    have h2 : (fun i => reg1Gate (reg1Gate' (Us i))) = Us := by
      funext i
      exact reg1Gate_reg1Gate' (Us i)
    rw [h2]
    exact boolGateProd_ofFn k Us
  rw [hprod]

/-- For nonempty input and positive window width, the layered machine's accepting mass after
`k+2` steps is the true-component squared norm of the gate product applied to the first
input bit. -/
theorem headStay_acceptMass_multi
    {k w n : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (hw : 0 < w) (hn : 0 < n) (x : Reg n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
      BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
        *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) n x)) c)
      = ‖(gateSeqProd Us k (by omega) *ᵥ
          (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) true‖ ^ 2 := by
  classical
  set h' : Fin (2 * w + 1) := ⟨w + 1, by omega⟩ with h'eq
  have hinit : layerCfg (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) (.toInput) false
      = initWindowCfg (t := w) (layerLocalQTM Us hU) n x :=
    layerCfg_eq_self _ _ _ (by rfl)
      (by simpa [layerLocalQTM] using! init_tape_head Us hU x)
  have hhead : (initWindowCfg (t := w) (layerLocalQTM Us hU) n x).head.val = w := rfl
  have hstep : (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ
        Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) n x)
      = Ket (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h') := by
    have h := layerLocalQTM_walk Us hU
      (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) false h' (by
        simp only [h']
        rw [hhead])
    rw [hinit] at h
    exact h
  have hbase_state :
      (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h').state = .layer 0 := rfl
  have hne : h' ≠ (initWindowCfg (t := w) (layerLocalQTM Us hU) n x).head := by
    intro heq
    have hh := congrArg Fin.val heq
    rw [hhead] at hh
    simp only [h'] at hh
    omega
  have hbase_tape :
      (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h').tape
        (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h').head
        = x ⟨0, hn⟩ := by
    have h1 : (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h').tape
          (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h').head
        = (initWindowCfg (t := w) (layerLocalQTM Us hU) n x).tape h' := by
      simp only [layerWalk]
    rw [h1]
    exact init_tape_succ Us hU hw hn x h' (by simp only [h'])
  have hsuper : Ket (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h')
      = layerCfgSuper (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h') 0 (by omega)
          (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0) :=
    ket_eq_layerCfgSuper _ _ hbase_tape hbase_state
  have hmass : (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
      BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 1)
        *ᵥ layerCfgSuper (layerWalk (initWindowCfg (t := w) (layerLocalQTM Us hU) n x) h') 0 (by omega)
          (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) c)
      = ‖(gateSeqProd Us k (by omega) *ᵥ
          (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) true‖ ^ 2 :=
    layerLocalQTM_acceptMass Us hU _ _
  rw [pow_succ, ← Matrix.mulVec_mulVec]
  rw [hstep]
  rw [hsuper]
  rw [hmass]

/-- An element of `Fin n` with value zero equals the zero index formed from any proof that `n`
is positive. -/
theorem fin_val_zero {n : ℕ} (hn : 0 < n) {j : Fin n} (hj : j.val = 0) :
    j = ⟨0, hn⟩ := by
  apply Fin.ext
  simp [hj]

/-- Setting bit zero gives the assigned value at the zero index. -/
theorem setBit0_bit0 {n : ℕ} (hn : 0 < n) (x : Reg n) (b : Bool) :
    setBit0 x b ⟨0, hn⟩ = b := by
  simp [setBit0]

/-- Setting bit zero leaves every nonzero-index bit unchanged. -/
theorem setBit0_of_ne {n : ℕ} (x : Reg n) (b : Bool) {j : Fin n} (hj : j.val ≠ 0) :
    setBit0 x b j = x j := by
  simp [setBit0, hj]

/-- Flipping bit zero negates its Boolean value. -/
theorem flip0_bit0 {n : ℕ} (hn : 0 < n) (x : Reg n) :
    flip0 hn x ⟨0, hn⟩ = !x ⟨0, hn⟩ := by
  simp [flip0, setBit0]

/-- Flipping bit zero preserves every nonzero-index bit. -/
theorem flip0_of_ne {n : ℕ} (hn : 0 < n) (x : Reg n) {j : Fin n} (hj : j.val ≠ 0) :
    flip0 hn x j = x j := by
  simp [flip0, setBit0, hj]

/-- Agreement outside bit zero is symmetric. -/
theorem AgreesOutside_comm {n : ℕ} (x y : Reg n) :
    AgreesOutside x y ↔ AgreesOutside y x := by
  constructor
  · intro h j hj
    exact (h j hj).symm
  · intro h j hj
    exact (h j hj).symm

/-- On a nonempty register, agreement outside bit zero means the registers are equal or differ
by flipping bit zero. -/
theorem agreesOutside_iff {n : ℕ} (hn : 0 < n) (x y : Reg n) :
    AgreesOutside x y ↔ (y = x ∨ y = flip0 hn x) := by
  constructor
  · intro h
    by_cases hb : y ⟨0, hn⟩ = x ⟨0, hn⟩
    · left
      funext j
      by_cases hj : j.val = 0
      · have hj' : j = ⟨0, hn⟩ := fin_val_zero hn hj
        rw [hj']
        exact hb
      · exact h j hj
    · right
      have hne : y ⟨0, hn⟩ = !x ⟨0, hn⟩ := by
        cases hy : y ⟨0, hn⟩ <;> cases hx : x ⟨0, hn⟩ <;> simp_all
      funext j
      by_cases hj : j.val = 0
      · have hj' : j = ⟨0, hn⟩ := fin_val_zero hn hj
        rw [hj']
        simp [flip0, setBit0, hne]
      · exact (h j hj).trans (flip0_of_ne hn x hj).symm
  · intro h
    rcases h with rfl | rfl
    · intro j hj
      rfl
    · intro j hj
      exact flip0_of_ne hn x hj

/-- Flipping bit zero of a nonempty register changes the register. -/
theorem flip0_ne {n : ℕ} (hn : 0 < n) (x : Reg n) : flip0 hn x ≠ x := by
  intro h
  have h1 := congrFun h ⟨0, hn⟩
  rw [flip0_bit0 hn x] at h1
  have h2 : x ⟨0, hn⟩ ≠ !x ⟨0, hn⟩ := by
    cases hx : x ⟨0, hn⟩ <;> simp_all
  exact h2 h1.symm

/-- A Boolean sum equals the term at any bit plus the term at its negation. -/
theorem sum_bool_pair (f : Bool → ℂ) (b : Bool) :
    f b + f (!b) = ∑ z : Bool, f z := by
  cases b with
  | false =>
      have h : (!false) = true := Bool.not_false
      rw [h, Fintype.sum_bool]
      exact add_comm _ _
  | true =>
      have h : (!true) = false := Bool.not_true
      rw [h, Fintype.sum_bool]

/-- Boolean matrix-vector multiplication is the sum of the two entry-amplitude products. -/
theorem mulVec_bool (U : Matrix Bool Bool ℂ) (c : Bool → ℂ) (b : Bool) :
    (U *ᵥ c) b = ∑ z : Bool, U b z * c z := by
  simp [Matrix.mulVec, dotProduct]

/-- Applying a gate embedded on the first wire of a `FirstWireState` multiplies its Boolean
amplitude vector by the gate and preserves the outside-agreement factor. -/
theorem embedReg1_applyGate {n : ℕ} (hn : 0 < n) (U : Matrix Bool Bool ℂ) (x : Reg n)
    (c : Bool → ℂ) (ψ : Reg n → ℂ) (hψ : FirstWireState hn x c ψ) :
    ∀ y : Reg n,
      ApplyGate (embedReg1 hn U) ψ y = (U *ᵥ c) (y ⟨0, hn⟩) * agreesOutside x y := by
  classical
  intro y
  have hne : x ≠ flip0 hn x := (flip0_ne hn x).symm
  have key : ∀ z ∈ (Finset.univ : Finset (Reg n)), z ∉ ({x, flip0 hn x} : Finset (Reg n)) →
      embedReg1 hn U y z * ψ z = 0 := by
    intro z _ hz
    have hag : ¬ AgreesOutside x z := by
      intro h
      rcases (agreesOutside_iff hn x z).mp h with h | h
      · exact hz (by simp [h])
      · exact hz (by simp [h])
    have hz0 : agreesOutside x z = 0 := by simp [agreesOutside, hag]
    rw [hψ z, hz0, mul_zero, mul_zero]
  have hsum : (∑ z : Reg n, embedReg1 hn U y z * ψ z)
      = ∑ z ∈ ({x, flip0 hn x} : Finset (Reg n)), embedReg1 hn U y z * ψ z :=
    (Finset.sum_subset (s₁ := ({x, flip0 hn x} : Finset (Reg n)))
      (s₂ := (Finset.univ : Finset (Reg n)))
      (f := fun z => embedReg1 hn U y z * ψ z)
      (fun _ _ => by simp)
      key).symm
  have hpair : (∑ z ∈ ({x, flip0 hn x} : Finset (Reg n)), embedReg1 hn U y z * ψ z)
      = embedReg1 hn U y x * ψ x + embedReg1 hn U y (flip0 hn x) * ψ (flip0 hn x) :=
    Finset.sum_pair (f := fun z => embedReg1 hn U y z * ψ z) hne
  have hagx : AgreesOutside x x := by intro j hj; rfl
  have hagf : AgreesOutside x (flip0 hn x) := by
    intro j hj
    exact flip0_of_ne hn x hj
  have hψx : ψ x = c (x ⟨0, hn⟩) := by
    rw [hψ x, agreesOutside, if_pos hagx]
    simp
  have hψf : ψ (flip0 hn x) = c ((flip0 hn x) ⟨0, hn⟩) := by
    rw [hψ (flip0 hn x), agreesOutside, if_pos hagf]
    simp
  have hcond : (AgreesOutside y x) ↔ (AgreesOutside y (flip0 hn x)) := by
    constructor
    · intro h j hj
      exact (flip0_of_ne hn x hj).trans (h j hj)
    · intro h j hj
      exact (flip0_of_ne hn x hj).symm.trans (h j hj)
  change (∑ z : Reg n, embedReg1 hn U y z * ψ z) = _
  rw [hsum, hpair, hψx, hψf]
  simp only [embedReg1, agreesOutside]
  by_cases hA : AgreesOutside y x
  · have hA' : AgreesOutside y (flip0 hn x) := hcond.mp hA
    have hagxy : AgreesOutside x y := (AgreesOutside_comm x y).mpr hA
    rw [if_pos hA, if_pos hA', if_pos hagxy, mul_one]
    have hfl := flip0_bit0 hn x
    rw [hfl]
    have hb := sum_bool_pair (f := fun z => U (y ⟨0, hn⟩) z * c z) (x ⟨0, hn⟩)
    rw [hb, mulVec_bool]
  · have hA' : ¬ AgreesOutside y (flip0 hn x) := fun h => hA (hcond.mpr h)
    have hagxy : ¬ AgreesOutside x y := fun h => hA ((AgreesOutside_comm x y).mp h)
    rw [if_neg hA, if_neg hA', if_neg hagxy]
    simp

/-- Applying a gate-list product with first gate `U` equals first applying `U`, then applying
the tail product. -/
theorem mulVec_boolGateProd_cons (gs : List (Matrix Bool Bool ℂ)) (U : Matrix Bool Bool ℂ)
    (c : Bool → ℂ) (b : Bool) :
    (boolGateProd (U :: gs) *ᵥ c) b = (boolGateProd gs *ᵥ (U *ᵥ c)) b := by
  rw [boolGateProd, Matrix.mulVec_mulVec]

/-- Running first-wire embedded gates on a `FirstWireState` applies their Boolean matrix product
to its amplitude vector and preserves the remaining bits. -/
theorem run_embed_firstWire {n : ℕ} (hn : 0 < n) (gs : List (Matrix Bool Bool ℂ)) (x : Reg n)
    (c : Bool → ℂ) (ψ : Reg n → ℂ) (hψ : FirstWireState hn x c ψ) :
    ∀ y : Reg n,
      Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedReg1 hn U)).map Step.gate) ψ y
        = (boolGateProd gs *ᵥ c) (y ⟨0, hn⟩) * agreesOutside x y := by
  induction gs generalizing c ψ with
  | nil =>
      intro y
      simp only [List.map_nil]
      have hrun : Run (1 : Matrix (Reg n) (Reg n) ℂ) ([] : Circuit (Reg n)) ψ = ψ := rfl
      rw [hrun, boolGateProd, Matrix.one_mulVec]
      exact hψ y
  | cons U gs ih =>
      intro y
      simp only [List.map_cons, Run]
      have hψ' : FirstWireState hn x (U *ᵥ c) (ApplyGate (embedReg1 hn U) ψ) :=
        embedReg1_applyGate hn U x c ψ hψ
      have hih := ih (U *ᵥ c) (ApplyGate (embedReg1 hn U) ψ) hψ' y
      rw [hih, mulVec_boolGateProd_cons]

/-- Equality of registers is equivalent to equality of bit zero together with agreement outside
bit zero. -/
theorem ket_eq_x_iff {n : ℕ} (hn : 0 < n) (x y : Reg n) :
    y = x ↔ (y ⟨0, hn⟩ = x ⟨0, hn⟩ ∧ AgreesOutside x y) := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, fun j hj => rfl⟩
  · intro h
    rcases (agreesOutside_iff hn x y).mp h.2 with hxy | hfl
    · exact hxy
    · exfalso
      have h1 := congrFun hfl ⟨0, hn⟩
      rw [flip0_bit0 hn x] at h1
      have h2 : x ⟨0, hn⟩ ≠ !x ⟨0, hn⟩ := by
        cases hx : x ⟨0, hn⟩ <;> simp_all
      exact h2 (h.1.symm.trans h1)

/-- Every basis ket is a `FirstWireState` with Boolean amplitudes concentrated on its first bit. -/
theorem ket_firstWire {n : ℕ} (hn : 0 < n) (x : Reg n) :
    FirstWireState hn x (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0) (Ket x) := by
  have hagx : AgreesOutside x x := by intro j hj; rfl
  intro y
  by_cases hconj : (y ⟨0, hn⟩ = x ⟨0, hn⟩ ∧ AgreesOutside x y)
  · have hy : y = x := (ket_eq_x_iff hn x y).mpr hconj
    rw [hy]
    simp [Qatlib.Foundations.PureStateMath.Ket, agreesOutside]
  · by_cases hbit : y ⟨0, hn⟩ = x ⟨0, hn⟩
    · have hyn : y ≠ x := by
        intro h
        exact hconj ⟨hbit, by rw [h]; exact hagx⟩
      have hag0 : agreesOutside x y = 0 := by
        have : ¬ AgreesOutside x y := fun h => hconj ⟨hbit, h⟩
        rw [agreesOutside, if_neg this]
      simp [Qatlib.Foundations.PureStateMath.Ket, hag0, hbit, hyn]
    · have hyn : y ≠ x := by
        intro h
        exact hbit (congrFun h ⟨0, hn⟩)
      have hc0 : (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0) (y ⟨0, hn⟩) = 0 := by
        simp [hbit]
      simp [Qatlib.Foundations.PureStateMath.Ket, hc0, hyn]

/-- Setting bit zero to true makes its zero-index value true. -/
theorem setBit0_true_bit0 {n : ℕ} (hn : 0 < n) (x : Reg n) :
    setBit0 x true ⟨0, hn⟩ = true := by
  simp [setBit0]

/-- A register agreeing with `x` outside bit zero and having true first bit is uniquely `setBit0
x true`. -/
theorem agreesOutside_accepting_unique {n : ℕ} (hn : 0 < n) (x y : Reg n)
    (hy : y ⟨0, hn⟩ = true) (hag : AgreesOutside x y) :
    y = setBit0 x true := by
  rcases (agreesOutside_iff hn x y).mp hag with hxy | hfl
  · have hx1 : x ⟨0, hn⟩ = true := by
      rw [← hxy]
      exact hy
    rw [hxy]
    funext j
    by_cases hj : j.val = 0
    · have hj' : j = ⟨0, hn⟩ := fin_val_zero hn hj
      rw [hj']
      simp [setBit0, hx1]
    · simp [setBit0, hj]
  · have hnot : (!x ⟨0, hn⟩) = true := by
      have h1 := congrFun hfl ⟨0, hn⟩
      rw [flip0_bit0 hn x] at h1
      exact h1.symm.trans hy
    rw [hfl]
    exact congrArg (setBit0 x) hnot

/-- The acceptance probability after first-wire embedded gates is the squared norm of the true
component of their Boolean product applied to the initial first bit. -/
theorem acceptProb_embed {n : ℕ} (hn : 0 < n) (gs : List (Matrix Bool Bool ℂ)) (x : Reg n) :
    AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        ((gs.map (fun U => embedReg1 hn U)).map Step.gate) (Ket x)) hn
      = ‖(boolGateProd gs *ᵥ (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) true‖ ^ 2 := by
  classical
  set c₀ : Bool → ℂ := fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0 with hc₀
  have hket : FirstWireState hn x c₀ (Ket x) := by
    rw [hc₀]
    exact ket_firstWire hn x
  have hrun := run_embed_firstWire hn gs x c₀ (Ket x) hket
  set A : ℂ := (boolGateProd gs *ᵥ c₀) true with hA
  have hag_xTrue : AgreesOutside x (setBit0 x true) := by
    intro j hj
    exact setBit0_of_ne x true hj
  have hxTrue_mem : setBit0 x true ∈
      (Finset.univ.filter (fun y : Reg n => y ⟨0, hn⟩ = true)) := by
    simp [setBit0]
  have hag_xTrue1 : agreesOutside x (setBit0 x true) = 1 := by
    rw [agreesOutside, if_pos hag_xTrue]
  have hzero : ∀ y ∈ (Finset.univ.filter (fun y : Reg n => y ⟨0, hn⟩ = true)),
      y ≠ setBit0 x true → agreesOutside x y = 0 := by
    intro y hy hne
    have hy' : y ⟨0, hn⟩ = true := (Finset.mem_filter.mp hy).2
    by_cases hag : AgreesOutside x y
    · exact absurd (agreesOutside_accepting_unique hn x y hy' hag) hne
    · rw [agreesOutside, if_neg hag]
  have hsum : (∑ y ∈ (Finset.univ.filter (fun y : Reg n => y ⟨0, hn⟩ = true)),
        BornProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedReg1 hn U)).map Step.gate) (Ket x)) y)
      = BornProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedReg1 hn U)).map Step.gate) (Ket x)) (setBit0 x true) := by
    apply Finset.sum_eq_single_of_mem (setBit0 x true) hxTrue_mem
    intro y hy hne
    have hag0 : agreesOutside x y = 0 := hzero y hy hne
    have h1 : Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedReg1 hn U)).map Step.gate) (Ket x) y = 0 := by
      have h1' := hrun y
      rw [h1', hag0]
      simp
    rw [BornProb, h1]
    simp
  rw [AcceptProb, MeasureProb, hsum]
  have h2 : Run (1 : Matrix (Reg n) (Reg n) ℂ)
        ((gs.map (fun U => embedReg1 hn U)).map Step.gate) (Ket x) (setBit0 x true) = A := by
    have h1' := hrun (setBit0 x true)
    rw [h1']
    rw [setBit0_true_bit0 hn x]
    rw [hag_xTrue1]
    simp [hA]
  rw [BornProb, h2]

/-- Mapping first-wire embedding over a finite gate list equals listing the individually
embedded gates. -/
theorem map_embed_ofFn {n k : ℕ} (hn : 0 < n) (Us : Fin k → Matrix Bool Bool ℂ) :
    (List.ofFn Us).map (fun U => embedReg1 hn U) = List.ofFn (fun i => embedReg1 hn (Us i)) := by
  rw [List.map_ofFn]
  rfl

/-- For nonempty input and positive window width, the layered machine's accepting mass after
`k+2` steps equals the acceptance probability of the circuit acting on the first wire. -/
theorem headStay_acceptProb_multi {k w n : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (hw : 0 < w) (hn : 0 < n) (x : Reg n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
      BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
        *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) n x)) c)
      = AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((List.ofFn (fun i => embedReg1 hn (Us i))).map Step.gate) (Ket x)) hn := by
  calc
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
        BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
          *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) n x)) c)
      = ‖(gateSeqProd Us k (by omega) *ᵥ
          (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) true‖ ^ 2 :=
        headStay_acceptMass_multi Us hU hw hn x
    _ = ‖(boolGateProd (List.ofFn Us) *ᵥ
          (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) true‖ ^ 2 := by
        rw [boolGateProd_ofFn k Us]
    _ = AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((List.ofFn (fun i => embedReg1 hn (Us i))).map Step.gate) (Ket x)) hn := by
        have h := (acceptProb_embed hn (List.ofFn Us) x).symm
        rw [map_embed_ofFn hn Us] at h
        exact h

/-- A communication decision list computing register equality must query every Alice input
position. -/
theorem alicePositions_eq_univ {m : ℕ} (P : CommDecisionList m)
    (h : ∀ a b : Reg m, commListOutput P a b = decide (a = b)) :
    alicePositions P = Finset.univ := by
  refine Finset.eq_univ_of_forall fun i => ?_
  by_contra hnot
  have hnotq : ∀ q ∈ P.queries, q.1 = true → q.2 ≠ i := by
    intro q hq hq1
    have hmem : q.2 ∈ alicePositions P := by
      refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
      simp [hq, hq1]
    intro hqi
    subst hqi
    exact hnot hmem
  let zeroReg : Reg m := fun _ => false
  let eReg : Reg m := fun j => if j = i then true else false
  have hne : eReg ≠ zeroReg := by
    intro heq
    have hcontra := congrFun heq i
    simp [eReg, zeroReg] at hcontra
  have htr : P.queries.map (fun q => if q.1 then eReg q.2 else zeroReg q.2)
      = P.queries.map (fun q => if q.1 then zeroReg q.2 else zeroReg q.2) := by
    refine List.map_congr_left (fun q hq => ?_)
    cases hq1 : q.1 with
    | true =>
        have hne' : q.2 ≠ i := hnotq q hq hq1
        simp [eReg, hne', zeroReg]
    | false =>
        simp
  have hout : commListOutput P eReg zeroReg = commListOutput P zeroReg zeroReg := by
    unfold commListOutput
    rw [htr]
  have h1 := h eReg zeroReg
  have h2 := h zeroReg zeroReg
  rw [hout] at h1
  have h3 : decide (eReg = zeroReg) = decide (zeroReg = zeroReg) := h1.symm.trans h2
  have h5 : decide (eReg = zeroReg) = true := h3.trans (decide_eq_true_eq.mpr rfl)
  exact hne (of_decide_eq_true h5)

/-- A communication decision list computing register equality must query every Bob input
position. -/
theorem bobPositions_eq_univ {m : ℕ} (P : CommDecisionList m)
    (h : ∀ a b : Reg m, commListOutput P a b = decide (a = b)) :
    bobPositions P = Finset.univ := by
  refine Finset.eq_univ_of_forall fun i => ?_
  by_contra hnot
  have hnotq : ∀ q ∈ P.queries, q.1 = false → q.2 ≠ i := by
    intro q hq hq1
    have hmem : q.2 ∈ bobPositions P := by
      refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
      simp [hq, hq1]
    intro hqi
    subst hqi
    exact hnot hmem
  let zeroReg : Reg m := fun _ => false
  let eReg : Reg m := fun j => if j = i then true else false
  have hne : eReg ≠ zeroReg := by
    intro heq
    have hcontra := congrFun heq i
    simp [eReg, zeroReg] at hcontra
  have htr : P.queries.map (fun q => if q.1 then zeroReg q.2 else eReg q.2)
      = P.queries.map (fun q => if q.1 then zeroReg q.2 else zeroReg q.2) := by
    refine List.map_congr_left (fun q hq => ?_)
    cases hq1 : q.1 with
    | true =>
        simp
    | false =>
        have hne' : q.2 ≠ i := hnotq q hq hq1
        simp [eReg, hne', zeroReg]
  have hout : commListOutput P zeroReg eReg = commListOutput P zeroReg zeroReg := by
    unfold commListOutput
    rw [htr]
  have h1 := h zeroReg eReg
  have h2 := h zeroReg zeroReg
  rw [hout] at h1
  have h3 : decide (zeroReg = eReg) = decide (zeroReg = zeroReg) := h1.symm.trans h2
  have h5 : decide (zeroReg = eReg) = true := h3.trans (decide_eq_true_eq.mpr rfl)
  exact hne (of_decide_eq_true h5).symm

/-- A communication decision list computing equality of `m`-bit registers has cost at least
`2*m`. -/
theorem commListCost_eq_ge_two_mul {m : ℕ} (P : CommDecisionList m)
    (h : ∀ a b : Reg m, commListOutput P a b = decide (a = b)) :
    2 * m ≤ commListCost P := by
  have hA := alicePositions_eq_univ P h
  have hB := bobPositions_eq_univ P h
  have hcardA : (alicePositions P).card = m := by
    rw [hA, Finset.card_univ, Fintype.card_fin]
  have hcardB : (bobPositions P).card = m := by
    rw [hB, Finset.card_univ, Fintype.card_fin]
  have hSAle : m ≤ ((P.queries.toFinset).filter (fun q => q.1 = true)).card := by
    calc m = (alicePositions P).card := hcardA.symm
      _ = (((P.queries.toFinset).filter (fun q => q.1 = true)).image (fun q => q.2)).card := rfl
      _ ≤ ((P.queries.toFinset).filter (fun q => q.1 = true)).card := Finset.card_image_le
  have hSBle : m ≤ ((P.queries.toFinset).filter (fun q => q.1 = false)).card := by
    calc m = (bobPositions P).card := hcardB.symm
      _ = (((P.queries.toFinset).filter (fun q => q.1 = false)).image (fun q => q.2)).card := rfl
      _ ≤ ((P.queries.toFinset).filter (fun q => q.1 = false)).card := Finset.card_image_le
  have hdisj : Disjoint ((P.queries.toFinset).filter (fun q => q.1 = true))
      ((P.queries.toFinset).filter (fun q => q.1 = false)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.1 = true := (Finset.mem_filter.mp hp1).2
    have h2 : p.1 = false := (Finset.mem_filter.mp hp2).2
    exact Bool.noConfusion (h1.symm.trans h2)
  have hsum : ((P.queries.toFinset).filter (fun q => q.1 = true)).card
      + ((P.queries.toFinset).filter (fun q => q.1 = false)).card
      ≤ (P.queries.toFinset).card := by
    calc ((P.queries.toFinset).filter (fun q => q.1 = true)).card
          + ((P.queries.toFinset).filter (fun q => q.1 = false)).card
        = (((P.queries.toFinset).filter (fun q => q.1 = true))
          ∪ ((P.queries.toFinset).filter (fun q => q.1 = false))).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (P.queries.toFinset).card :=
          Finset.card_le_card
            (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have htoFinset : (P.queries.toFinset).card ≤ P.queries.length := List.toFinset_card_le _
  calc 2 * m = m + m := by omega
    _ ≤ ((P.queries.toFinset).filter (fun q => q.1 = true)).card
        + ((P.queries.toFinset).filter (fun q => q.1 = false)).card := Nat.add_le_add hSAle hSBle
    _ ≤ (P.queries.toFinset).card := hsum
    _ ≤ commListCost P := htoFinset

/-- Equality-computing communication decision lists satisfy the iterated-logarithm lower bound
in `CommunicationOmegaLogLogSpec`. -/
theorem communication_omega_log_log : CommunicationOmegaLogLogSpec := by
  refine ⟨1, by norm_num, ?_⟩
  intro m hm P hP
  have hcost : 2 * m ≤ commListCost P := commListCost_eq_ge_two_mul P hP
  have hlog : Nat.log 2 (Nat.log 2 (2 ^ m)) = Nat.log 2 m := by
    rw [Nat.log_pow (by omega : 1 < 2) m]
  have hle : Nat.log 2 m ≤ 2 * m := by
    have h := Nat.log_le_self 2 m
    omega
  calc 1 * Nat.log 2 (Nat.log 2 (2 ^ m)) = Nat.log 2 m := by rw [hlog]; simp
    _ ≤ 2 * m := hle
    _ ≤ commListCost P := hcost

/-- The number of distinct variables in a Boolean formula is at most its size. -/
theorem formulaVars_card_le_size {n : ℕ} (F : BoolFormula (Fin n)) :
    (formulaVars F).card ≤ F.size := by
  induction F with
  | var v => simp [formulaVars, BoolFormula.size]
  | not f ih => simpa [formulaVars, BoolFormula.size] using! ih
  | and f g ihf ihg =>
      simp only [formulaVars, BoolFormula.size]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add ihf ihg)
  | or f g ihf ihg =>
      simp only [formulaVars, BoolFormula.size]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add ihf ihg)

/-- A Boolean formula has equal evaluations on inputs agreeing on every variable occurring in
it. -/
theorem eval_congr_of_subset {n : ℕ} (F : BoolFormula (Fin n)) {x x' : Reg n}
    (h : ∀ v, v ∈ formulaVars F → x v = x' v) : F.eval x = F.eval x' := by
  induction F with
  | var v => simp [BoolFormula.eval, h v (Finset.mem_singleton_self v)]
  | not f ih => simp [BoolFormula.eval, ih h]
  | and f g ihf ihg =>
      simp [BoolFormula.eval, ihf (fun v hv => h v (Finset.mem_union_left _ hv)),
        ihg (fun v hv => h v (Finset.mem_union_right _ hv))]
  | or f g ihf ihg =>
      simp [BoolFormula.eval, ihf (fun v hv => h v (Finset.mem_union_left _ hv)),
        ihg (fun v hv => h v (Finset.mem_union_right _ hv))]

/-- The Hamming weight of a Boolean register equals the cardinality of its support. -/
theorem regWeight_eq_support_card {n : ℕ} (x : Reg n) :
    regWeight n x = (regSupport x).card := by
  have hsum : regWeight n x = ∑ i : Fin n, (if x i = true then 1 else 0) := by
    unfold regWeight
    apply Finset.sum_congr rfl
    intro i _
    cases h : x i <;> rfl
  rw [hsum]
  unfold regSupport
  rw [Finset.card_filter]

/-- The support of the register associated with a finite set is that set. -/
theorem regSupport_regOfSet {n : ℕ} (S : Finset (Fin n)) :
    regSupport (regOfSet S) = S := by
  ext j
  simp [regSupport, regOfSet]

/-- The Hamming weight of a register associated with a finite set equals the set's cardinality. -/
theorem regWeight_regOfSet {n : ℕ} (S : Finset (Fin n)) :
    regWeight n (regOfSet S) = S.card := by
  rw [regWeight_eq_support_card, regSupport_regOfSet]

/-- Membership in the first `k` indices is equivalent to having value less than `k`, assuming `k
≤ n`. -/
theorem mem_firstIndices {n k : ℕ} (hk : k ≤ n) (j : Fin n) :
    j ∈ firstIndices k hk ↔ j.val < k := by
  rw [firstIndices, Finset.mem_image]
  constructor
  · rintro ⟨v, _, rfl⟩
    exact v.isLt
  · intro hj
    refine ⟨⟨j.val, by omega⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl

/-- The set of the first `k` indices in `Fin n` has cardinality `k` when `k ≤ n`. -/
theorem card_firstIndices {n k : ℕ} (hk : k ≤ n) : (firstIndices k hk).card = k := by
  unfold firstIndices
  rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
    (Fin.castLE_injective hk)]
  rw [Finset.card_univ, Fintype.card_fin]

/-- Strict majority is true exactly when the register weight is at least `n/2+1`. -/
theorem regMajority_eq_true_iff {n : ℕ} (x : Reg n) :
    regMajority n x = true ↔ n / 2 + 1 ≤ regWeight n x := by
  unfold regMajority
  rw [decide_eq_true_eq]
  omega

/-- Strict majority is false exactly when the register weight is less than `n/2+1`. -/
theorem regMajority_eq_false_iff {n : ℕ} (x : Reg n) :
    regMajority n x = false ↔ regWeight n x < n / 2 + 1 := by
  unfold regMajority
  rw [decide_eq_false_iff_not]
  omega

/-- Each bit of a nonempty register can change strict majority from false to true while all
other bits remain fixed. -/
theorem majority_sensitive {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∃ x x' : Reg n, (∀ j : Fin n, j ≠ i → x j = x' j) ∧
      regMajority n x = false ∧ regMajority n x' = true := by
  set f := n / 2 with hf
  have hfk : f + 1 ≤ n := by omega
  have hfk0 : f ≤ n := by omega
  by_cases hcase : i.val ≤ f
  · set Foundations : Finset (Fin n) := firstIndices (f + 1) hfk with hS1
    set S : Finset (Fin n) := Foundations.erase i with hS
    have hiS1 : i ∈ Foundations := by
      rw [mem_firstIndices hfk i]
      omega
    have hwLow : regWeight n (regOfSet S) = f := by
      have hcard : S.card = f := by
        rw [hS, Finset.card_erase_of_mem hiS1, card_firstIndices hfk]
        omega
      rw [regWeight_regOfSet, hcard]
    have hwHigh : regWeight n (regOfSet Foundations) = f + 1 := by
      rw [regWeight_regOfSet, card_firstIndices hfk]
    refine ⟨regOfSet S, regOfSet Foundations, ?_, ?_, ?_⟩
    · intro j hj
      have hs : j ∈ S ↔ j ∈ Foundations := by
        rw [hS, Finset.mem_erase]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨hj, h⟩
      by_cases h1 : j ∈ Foundations
      · have h2 : j ∈ S := hs.mpr h1
        simp [regOfSet, h1, h2]
      · have h2 : j ∉ S := fun hh => h1 (hs.mp hh)
        simp [regOfSet, h1, h2]
    · refine (regMajority_eq_false_iff _).mpr ?_
      calc regWeight n (regOfSet S) = f := by rw [hwLow]
        _ < n / 2 + 1 := by omega
    · refine (regMajority_eq_true_iff _).mpr ?_
      calc n / 2 + 1 ≤ f + 1 := by omega
        _ = regWeight n (regOfSet Foundations) := by rw [hwHigh]
  · set S : Finset (Fin n) := firstIndices f hfk0 with hS
    set S' : Finset (Fin n) := S ∪ {i} with hS'
    have hiS : i ∉ S := by
      rw [mem_firstIndices hfk0 i]
      omega
    have hwLow : regWeight n (regOfSet S) = f := by
      rw [regWeight_regOfSet, hS, card_firstIndices hfk0]
    have hwHigh : regWeight n (regOfSet S') = f + 1 := by
      have hdisj : Disjoint S {i} := Finset.disjoint_singleton_right.mpr hiS
      have hcard : S'.card = f + 1 := by
        rw [hS', Finset.card_union_of_disjoint hdisj, hS, card_firstIndices hfk0]
        simp
      rw [regWeight_regOfSet, hcard]
    refine ⟨regOfSet S, regOfSet S', ?_, ?_, ?_⟩
    · intro j hj
      have hs : j ∈ S ↔ j ∈ S' := by
        rw [hS', Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro h
          exact Or.inl h
        · intro h
          rcases h with h | h
          · exact h
          · exact absurd h hj
      by_cases h1 : j ∈ S
      · have h2 : j ∈ S' := hs.mp h1
        simp [regOfSet, h1, h2]
      · have h2 : j ∉ S' := fun hh => h1 (hs.mpr hh)
        simp [regOfSet, h1, h2]
    · refine (regMajority_eq_false_iff _).mpr ?_
      calc regWeight n (regOfSet S) = f := by rw [hwLow]
        _ < n / 2 + 1 := by omega
    · refine (regMajority_eq_true_iff _).mpr ?_
      calc n / 2 + 1 ≤ f + 1 := by omega
        _ = regWeight n (regOfSet S') := by rw [hwHigh]

/-- A Boolean formula computing strict majority has size at least the number of input variables,
as specified by `MajorityFormulaLowerBoundSpec`. -/
theorem majority_formula_lower_bound : MajorityFormulaLowerBoundSpec := by
  intro n F hF
  by_cases hn : n = 0
  · omega
  · have hn0 : 0 < n := by omega
    have hmem : ∀ i : Fin n, i ∈ formulaVars F := by
      intro i
      by_contra hnot
      obtain ⟨x, x', hagree, hmajx, hmajx'⟩ := majority_sensitive hn0 i
      have heval : F.eval x = F.eval x' := eval_congr_of_subset F (fun v hv => by
        by_cases hvi : v = i
        · have hmem' : i ∈ formulaVars F := by rw [← hvi]; exact hv
          exact (hnot hmem').elim
        · exact hagree v hvi)
      have h1 := hF x
      have h2 := hF x'
      rw [heval] at h1
      rw [hmajx] at h1
      rw [hmajx'] at h2
      exact Bool.noConfusion (h1.symm.trans h2)
    calc n = (formulaVars F).card := by
            rw [Finset.eq_univ_of_forall hmem, Finset.card_univ, Fintype.card_fin]
      _ ≤ F.size := formulaVars_card_le_size F

/-- Each column of every unitary in the cell-indexed gate family has squared norm one. -/
theorem cellGateCol_norm {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (i : Fin n) (j : Fin k) (a : Bool) :
    ∑ b : Bool, ‖V i j b a‖ ^ 2 = 1 := by
  exact gateCol_norm (fun j => V i j) (fun j => hV i j) j a

/-- Distinct columns of each cell-indexed unitary gate are orthogonal. -/
theorem cellGateCol_orth {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (i : Fin n) (j : Fin k)
    (a₁ a₂ : Bool) (hne : a₁ ≠ a₂) :
    ∑ b : Bool, star (V i j b a₁) * V i j b a₂ = 0 := by
  exact gateCol_orth (fun j => V i j) (fun j => hV i j) j a₁ a₂ hne

/-- The cell-machine walk advances its counter until the target offset, where it enters gate
stage zero. -/
theorem cellNext_walk {n k tgt : ℕ} (d : Fin (tgt + 1)) (a : Bool) :
    cellNext (.walk d : CellState n k tgt) a =
      if h : d.val = tgt then .gate ⟨0, by omega⟩ else .walk ⟨d.val + 1, by omega⟩ := rfl

/-- A cell-machine gate state advances its stage below `k` and otherwise selects acceptance or
rejection from the current bit. -/
theorem cellNext_gate {n k tgt : ℕ} (j : Fin (k + 1)) (a : Bool) :
    cellNext (.gate j : CellState n k tgt) a =
      if h : j.val < k then .gate ⟨j.val + 1, by omega⟩ else (if a then .acc else .rej) := rfl

/-- The accepting cell-machine state transitions to the second measurement state. -/
theorem cellNext_acc {n k tgt : ℕ} (a : Bool) : cellNext (.acc : CellState n k tgt) a = .meas2 :=
    rfl

/-- The rejecting cell-machine state transitions to walk stage zero. -/
theorem cellNext_rej {n k tgt : ℕ} (a : Bool) : cellNext (.rej : CellState n k tgt) a = .walk ⟨0,
    by omega⟩ := rfl

/-- The second measurement state selects acceptance or rejection from the current bit. -/
theorem cellNext_meas2 {n k tgt : ℕ} (a : Bool) :
    cellNext (.meas2 : CellState n k tgt) a = if a then .acc else .rej := rfl

/-- Distinct cell-machine walk stages have distinct next states. -/
theorem cellNext_walk_ne_walk {n k tgt : ℕ} (d₁ d₂ : Fin (tgt + 1)) (a₁ a₂ : Bool)
    (h : d₁ ≠ d₂) :
    cellNext (.walk d₁ : CellState n k tgt) a₁ ≠ cellNext (.walk d₂ : CellState n k tgt) a₂ := by
  intro hcon
  by_cases h1 : d₁.val = tgt
  · by_cases h2 : d₂.val = tgt
    · have hd' : d₁ = d₂ := Fin.ext (by omega)
      exact (h hd').elim
    · rw [cellNext_walk d₁ a₁, cellNext_walk d₂ a₂, dif_pos h1, dif_neg h2] at hcon
      injection hcon
  · by_cases h2 : d₂.val = tgt
    · rw [cellNext_walk d₁ a₁, cellNext_walk d₂ a₂, dif_neg h1, dif_pos h2] at hcon
      injection hcon
    · rw [cellNext_walk d₁ a₁, cellNext_walk d₂ a₂, dif_neg h1, dif_neg h2] at hcon
      injection hcon with hval
      have hv : d₁.val + 1 = d₂.val + 1 := by
        simpa using! congrArg Fin.val hval
      have hd' : d₁ = d₂ := Fin.ext (by omega)
      exact (h hd').elim

/-- The next state of a walk stage differs from the next state of every state outside the walk
family. -/
theorem cellNext_walk_ne {n k tgt : ℕ} (d : Fin (tgt + 1)) (a₁ : Bool)
    (q₂ : CellState n k tgt) (hq₂ : ∀ d₂, q₂ ≠ .walk d₂) (a₂ : Bool) :
    cellNext (.walk d : CellState n k tgt) a₁ ≠ cellNext q₂ a₂ := by
  cases q₂ with
  | walk d₂ => exact (hq₂ d₂ rfl).elim
  | gate j₂ =>
      intro hcon
      by_cases h1 : d.val = tgt
      · by_cases h2 : j₂.val < k
        · rw [cellNext_walk d a₁, cellNext_gate j₂ a₂, dif_pos h1, dif_pos h2] at hcon
          injection hcon with hval
          have hv : (0 : ℕ) = j₂.val + 1 := by
            simpa using! congrArg Fin.val hval
          omega
        · rw [cellNext_walk d a₁, cellNext_gate j₂ a₂, dif_pos h1, dif_neg h2] at hcon
          cases a₂ <;> injection hcon
      · by_cases h2 : j₂.val < k
        · rw [cellNext_walk d a₁, cellNext_gate j₂ a₂, dif_neg h1, dif_pos h2] at hcon
          injection hcon
        · rw [cellNext_walk d a₁, cellNext_gate j₂ a₂, dif_neg h1, dif_neg h2] at hcon
          cases a₂ <;> injection hcon
  | acc =>
      intro hcon
      by_cases h1 : d.val = tgt
      · rw [cellNext_walk d a₁, cellNext_acc a₂, dif_pos h1] at hcon
        injection hcon
      · rw [cellNext_walk d a₁, cellNext_acc a₂, dif_neg h1] at hcon
        injection hcon
  | rej =>
      intro hcon
      by_cases h1 : d.val = tgt
      · rw [cellNext_walk d a₁, cellNext_rej a₂, dif_pos h1] at hcon
        injection hcon
      · rw [cellNext_walk d a₁, cellNext_rej a₂, dif_neg h1] at hcon
        injection hcon with hval
        have hv : d.val + 1 = 0 := by
          simpa using! congrArg Fin.val hval
        omega
  | meas2 =>
      intro hcon
      by_cases h1 : d.val = tgt
      · rw [cellNext_walk d a₁, cellNext_meas2 a₂, dif_pos h1] at hcon
        cases a₂ <;> injection hcon
      · rw [cellNext_walk d a₁, cellNext_meas2 a₂, dif_neg h1] at hcon
        cases a₂ <;> injection hcon

/-- Distinct cell-machine gate stages have distinct next states. -/
theorem cellNext_gate_ne {n k tgt : ℕ} (j₁ j₂ : Fin (k + 1)) (a₁ a₂ : Bool)
    (h : j₁ ≠ j₂) :
    cellNext (.gate j₁ : CellState n k tgt) a₁ ≠ cellNext (.gate j₂ : CellState n k tgt) a₂ := by
  intro hcon
  by_cases h1 : j₁.val < k
  · by_cases h2 : j₂.val < k
    · rw [cellNext_gate j₁ a₁, cellNext_gate j₂ a₂, dif_pos h1, dif_pos h2] at hcon
      injection hcon with hval
      have hv : j₁.val + 1 = j₂.val + 1 := by
        simpa using! congrArg Fin.val hval
      have hj : j₁ = j₂ := Fin.ext (by omega)
      exact (h hj).elim
    · rw [cellNext_gate j₁ a₁, cellNext_gate j₂ a₂, dif_pos h1, dif_neg h2] at hcon
      cases a₂ <;> injection hcon
  · by_cases h2 : j₂.val < k
    · rw [cellNext_gate j₁ a₁, cellNext_gate j₂ a₂, dif_neg h1, dif_pos h2] at hcon
      cases a₁ <;> injection hcon
    · have hj : j₁ = j₂ := Fin.ext (by omega)
      exact (h hj).elim

/-- Each cell-machine walk stage preserves the tape symbol with amplitude one. -/
theorem cellAmp_walk_row {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (d : Fin (tgt + 1)) (a b : Bool) :
    cellAmp V htgt (.walk d : CellState n k tgt) a b = (if b = a then 1 else 0) := by
  simp [cellAmp]

/-- Below the final gate stage, the cell-machine amplitudes are the entries of the corresponding
gate at the target cell. -/
theorem cellAmp_gate_row {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (j : Fin (k + 1)) (h : j.val < k) (a b : Bool) :
    cellAmp V htgt (.gate j : CellState n k tgt) a b = V ⟨tgt, htgt⟩ ⟨j.val, h⟩ b a := by
  simp [cellAmp, h]

/-- At the final gate stage, the cell-machine amplitudes flip the tape symbol deterministically. -/
theorem cellAmp_measure_row {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (j : Fin (k + 1)) (h : ¬ (j.val < k)) (a b : Bool) :
    cellAmp V htgt (.gate j : CellState n k tgt) a b = (if b = !a then 1 else 0) := by
  simp [cellAmp, h]

/-- The accepting, rejecting, and second measurement states preserve the tape symbol
deterministically. -/
theorem cellAmp_det_row {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (a b : Bool) :
    (cellAmp V htgt (.acc : CellState n k tgt) a b = (if b = a then 1 else 0)) ∧
      (cellAmp V htgt (.rej : CellState n k tgt) a b = (if b = a then 1 else 0)) ∧
      (cellAmp V htgt (.meas2 : CellState n k tgt) a b = (if b = a then 1 else 0)) := by
  simp [cellAmp]

/-- For unitary gate data, each cell-machine amplitude row has squared norm one. -/
theorem cellAmp_norm {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (q : CellState n k tgt) (a : Bool) :
    ∑ b : Bool, ‖cellAmp V htgt q a b‖ ^ 2 = 1 := by
  cases q with
  | walk d => cases a <;> simp [cellAmp]
  | gate j =>
      by_cases h : j.val < k
      · simp only [cellAmp, dif_pos h]
        exact cellGateCol_norm V hV ⟨tgt, htgt⟩ ⟨j.val, h⟩ a
      · have hn : ¬ (j.val < k) := by omega
        simp only [cellAmp, dif_neg hn]
        cases a <;> simp
  | acc => cases a <;> simp [cellAmp]
  | rej => cases a <;> simp [cellAmp]
  | meas2 => cases a <;> simp [cellAmp]

/-- Distinct deterministic symbol-preserving cell-machine amplitude rows are orthogonal. -/
theorem cellAmp_det_orth {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (q : CellState n k tgt) (a₁ a₂ : Bool) (hne : a₁ ≠ a₂)
    (hrow : ∀ b, cellAmp V htgt q a₁ b = if b = a₁ then 1 else 0)
    (hrow2 : ∀ b, cellAmp V htgt q a₂ b = if b = a₂ then 1 else 0) :
    ∑ b : Bool, star (cellAmp V htgt q a₁ b) * cellAmp V htgt q a₂ b = 0 := by
  have hsum : (∑ b : Bool, star (cellAmp V htgt q a₁ b) * cellAmp V htgt q a₂ b)
      = ∑ b : Bool, star (if b = a₁ then 1 else 0) * (if b = a₂ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [hrow, hrow2]
  rw [hsum]
  cases a₁ <;> cases a₂ <;>
    first
    | exact (hne rfl).elim
    | simp

/-- The final gate-stage amplitude rows for distinct input symbols are orthogonal. -/
theorem cellAmp_measure_orth {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (j : Fin (k + 1)) (h : ¬ (j.val < k)) (a₁ a₂ : Bool) (hne : a₁ ≠ a₂) :
    ∑ b : Bool, star (cellAmp V htgt (.gate j : CellState n k tgt) a₁ b)
        * cellAmp V htgt (.gate j : CellState n k tgt) a₂ b = 0 := by
  have hsum : (∑ b : Bool, star (cellAmp V htgt (.gate j : CellState n k tgt) a₁ b)
        * cellAmp V htgt (.gate j : CellState n k tgt) a₂ b)
      = ∑ b : Bool, star (if b = !a₁ then 1 else 0) * (if b = !a₂ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [cellAmp_measure_row V htgt j h, cellAmp_measure_row V htgt j h]
  rw [hsum]
  cases a₁ <;> cases a₂ <;>
    first
    | exact (hne rfl).elim
    | simp

/-- For equal input symbols, final gate-stage and second measurement-state amplitude rows have
zero overlap in both orders. -/
theorem cellAmp_meas_orth {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (j : Fin (k + 1)) (h : ¬ (j.val < k)) (a₁ a₂ : Bool) (heq : a₁ = a₂) :
    (∑ b : Bool, star (cellAmp V htgt (.gate j : CellState n k tgt) a₁ b)
        * cellAmp V htgt (.meas2 : CellState n k tgt) a₂ b = 0) ∧
    (∑ b : Bool, star (cellAmp V htgt (.meas2 : CellState n k tgt) a₂ b)
        * cellAmp V htgt (.gate j : CellState n k tgt) a₁ b = 0) := by
  have hdet : ∀ b, cellAmp V htgt (.meas2 : CellState n k tgt) a₂ b
      = if b = a₂ then 1 else 0 := by
    intro b
    exact (cellAmp_det_row V htgt a₂ b).2.2
  have hsum : (∑ b : Bool, star (cellAmp V htgt (.gate j : CellState n k tgt) a₁ b)
        * cellAmp V htgt (.meas2 : CellState n k tgt) a₂ b)
      = ∑ b : Bool, star (if b = !a₁ then 1 else 0) * (if b = a₂ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [cellAmp_measure_row V htgt j h, hdet]
  have hsum2 : (∑ b : Bool, star (cellAmp V htgt (.meas2 : CellState n k tgt) a₂ b)
        * cellAmp V htgt (.gate j : CellState n k tgt) a₁ b)
      = ∑ b : Bool, star (if b = a₂ then 1 else 0) * (if b = !a₁ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [hdet, cellAmp_measure_row V htgt j h]
  constructor
  · rw [hsum]
    rcases a₁ with _ | _ <;> rcases a₂ with _ | _
    all_goals first
      | exact Bool.noConfusion heq
      | simp
  · rw [hsum2]
    rcases a₁ with _ | _ <;> rcases a₂ with _ | _
    all_goals first
      | exact Bool.noConfusion heq
      | simp

/-- With unitary gate data, distinct state-symbol inputs with a common next state have
orthogonal cell-machine amplitude rows. -/
theorem cellAmp_orth {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (q₁ q₂ : CellState n k tgt) (a₁ a₂ : Bool)
    (hne : (q₁, a₁) ≠ (q₂, a₂))
    (hnxt : cellNext q₁ a₁ = cellNext q₂ a₂) :
    ∑ b : Bool, star (cellAmp V htgt q₁ a₁ b) * cellAmp V htgt q₂ a₂ b = 0 := by
  cases q₁ with
  | walk d₁ =>
      cases q₂ with
      | walk d₂ =>
          by_cases hd : d₁ = d₂
          · subst hd
            have ha : a₁ ≠ a₂ := by
              intro h
              apply hne
              exact Prod.ext rfl h
            exact cellAmp_det_orth V htgt (.walk d₁ : CellState n k tgt) a₁ a₂ ha
              (fun b => cellAmp_walk_row V htgt d₁ a₁ b)
              (fun b => cellAmp_walk_row V htgt d₁ a₂ b)
          · exfalso
            exact (cellNext_walk_ne_walk d₁ d₂ a₁ a₂ hd) hnxt
      | gate j₂ =>
          exfalso
          exact (cellNext_walk_ne d₁ a₁ (.gate j₂ : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₂) hnxt
      | acc =>
          exfalso
          exact (cellNext_walk_ne d₁ a₁ (.acc : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₂) hnxt
      | rej =>
          exfalso
          exact (cellNext_walk_ne d₁ a₁ (.rej : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₂) hnxt
      | meas2 =>
          exfalso
          exact (cellNext_walk_ne d₁ a₁ (.meas2 : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₂) hnxt
  | gate j₁ =>
      cases q₂ with
      | walk d₂ =>
          exfalso
          exact (cellNext_walk_ne d₂ a₂ (.gate j₁ : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₁) hnxt.symm
      | gate j₂ =>
          by_cases hj : j₁ = j₂
          · subst hj
            have ha : a₁ ≠ a₂ := by
              intro h
              apply hne
              exact Prod.ext rfl h
            by_cases h : j₁.val < k
            · simp only [cellAmp, dif_pos h]
              exact cellGateCol_orth V hV ⟨tgt, htgt⟩ ⟨j₁.val, h⟩ a₁ a₂ ha
            · have hn : ¬ (j₁.val < k) := by omega
              exact cellAmp_measure_orth V htgt j₁ hn a₁ a₂ ha
          · exfalso
            exact (cellNext_gate_ne j₁ j₂ a₁ a₂ hj) hnxt
      | acc =>
          exfalso
          have hn : cellNext (.gate j₁ : CellState n k tgt) a₁
              ≠ cellNext (.acc : CellState n k tgt) a₂ := by
            intro hcon
            by_cases h : j₁.val < k
            · rw [cellNext_gate j₁ a₁, cellNext_acc a₂, dif_pos h] at hcon
              injection hcon
            · rw [cellNext_gate j₁ a₁, cellNext_acc a₂, dif_neg h] at hcon
              cases a₁ <;> injection hcon
          exact hn hnxt
      | rej =>
          exfalso
          have hn : cellNext (.gate j₁ : CellState n k tgt) a₁
              ≠ cellNext (.rej : CellState n k tgt) a₂ := by
            intro hcon
            by_cases h : j₁.val < k
            · rw [cellNext_gate j₁ a₁, cellNext_rej a₂, dif_pos h] at hcon
              injection hcon
            · rw [cellNext_gate j₁ a₁, cellNext_rej a₂, dif_neg h] at hcon
              cases a₁ <;> injection hcon
          exact hn hnxt
      | meas2 =>
          by_cases h : j₁.val < k
          · exfalso
            have hn : cellNext (.gate j₁ : CellState n k tgt) a₁
                ≠ cellNext (.meas2 : CellState n k tgt) a₂ := by
              intro hcon
              rw [cellNext_gate j₁ a₁, cellNext_meas2 a₂, dif_pos h] at hcon
              cases a₂ <;> injection hcon
            exact hn hnxt
          · have hn : ¬ (j₁.val < k) := by omega
            have ha : a₁ = a₂ := by
              by_cases ha' : a₁ = a₂
              · exact ha'
              · exfalso
                rw [cellNext_gate j₁ a₁, cellNext_meas2 a₂, dif_neg hn] at hnxt
                cases a₁ <;> cases a₂ <;> simp_all
            exact (cellAmp_meas_orth V htgt j₁ hn a₁ a₂ ha).1
  | acc =>
      cases q₂ with
      | walk d₂ =>
          exfalso
          exact (cellNext_walk_ne d₂ a₂ (.acc : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₁) hnxt.symm
      | gate j₂ =>
          exfalso
          have hn : cellNext (.acc : CellState n k tgt) a₁
              ≠ cellNext (.gate j₂ : CellState n k tgt) a₂ := by
            intro hcon
            by_cases h : j₂.val < k
            · rw [cellNext_acc a₁, cellNext_gate j₂ a₂, dif_pos h] at hcon
              injection hcon
            · rw [cellNext_acc a₁, cellNext_gate j₂ a₂, dif_neg h] at hcon
              cases a₂ <;> injection hcon
          exact hn hnxt
      | acc =>
          have ha : a₁ ≠ a₂ := by
            intro h
            apply hne
            exact Prod.ext rfl h
          exact cellAmp_det_orth V htgt (.acc : CellState n k tgt) a₁ a₂ ha
            (fun b => (cellAmp_det_row V htgt a₁ b).1)
            (fun b => (cellAmp_det_row V htgt a₂ b).1)
      | rej =>
          exfalso
          have hn : cellNext (.acc : CellState n k tgt) a₁
              ≠ cellNext (.rej : CellState n k tgt) a₂ := by
            intro hcon
            rw [cellNext_acc a₁, cellNext_rej a₂] at hcon
            injection hcon
          exact hn hnxt
      | meas2 =>
          exfalso
          have hn : cellNext (.acc : CellState n k tgt) a₁
              ≠ cellNext (.meas2 : CellState n k tgt) a₂ := by
            intro hcon
            rw [cellNext_acc a₁, cellNext_meas2 a₂] at hcon
            cases a₂ <;> injection hcon
          exact hn hnxt
  | rej =>
      cases q₂ with
      | walk d₂ =>
          exfalso
          exact (cellNext_walk_ne d₂ a₂ (.rej : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₁) hnxt.symm
      | gate j₂ =>
          exfalso
          have hn : cellNext (.rej : CellState n k tgt) a₁
              ≠ cellNext (.gate j₂ : CellState n k tgt) a₂ := by
            intro hcon
            by_cases h : j₂.val < k
            · rw [cellNext_rej a₁, cellNext_gate j₂ a₂, dif_pos h] at hcon
              injection hcon
            · rw [cellNext_rej a₁, cellNext_gate j₂ a₂, dif_neg h] at hcon
              cases a₂ <;> injection hcon
          exact hn hnxt
      | acc =>
          exfalso
          have hn : cellNext (.rej : CellState n k tgt) a₁
              ≠ cellNext (.acc : CellState n k tgt) a₂ := by
            intro hcon
            rw [cellNext_rej a₁, cellNext_acc a₂] at hcon
            injection hcon
          exact hn hnxt
      | rej =>
          have ha : a₁ ≠ a₂ := by
            intro h
            apply hne
            exact Prod.ext rfl h
          exact cellAmp_det_orth V htgt (.rej : CellState n k tgt) a₁ a₂ ha
            (fun b => (cellAmp_det_row V htgt a₁ b).2.1)
            (fun b => (cellAmp_det_row V htgt a₂ b).2.1)
      | meas2 =>
          exfalso
          have hn : cellNext (.rej : CellState n k tgt) a₁
              ≠ cellNext (.meas2 : CellState n k tgt) a₂ := by
            intro hcon
            rw [cellNext_rej a₁, cellNext_meas2 a₂] at hcon
            cases a₂ <;> injection hcon
          exact hn hnxt
  | meas2 =>
      cases q₂ with
      | walk d₂ =>
          exfalso
          exact (cellNext_walk_ne d₂ a₂ (.meas2 : CellState n k tgt)
            (fun d₂' hq => by cases hq) a₁) hnxt.symm
      | gate j₂ =>
          by_cases h : j₂.val < k
          · exfalso
            have hn : cellNext (.meas2 : CellState n k tgt) a₁
                ≠ cellNext (.gate j₂ : CellState n k tgt) a₂ := by
              intro hcon
              rw [cellNext_meas2 a₁, cellNext_gate j₂ a₂, dif_pos h] at hcon
              cases a₁ <;> injection hcon
            exact hn hnxt
          · have hn : ¬ (j₂.val < k) := by omega
            have ha : a₁ = a₂ := by
              by_cases ha' : a₁ = a₂
              · exact ha'
              · exfalso
                rw [cellNext_meas2 a₁, cellNext_gate j₂ a₂, dif_neg hn] at hnxt
                cases a₁ <;> cases a₂ <;> simp_all
            simpa [ha] using! (cellAmp_meas_orth V htgt j₂ hn a₁ a₂ ha).2
      | acc =>
          exfalso
          have hn : cellNext (.meas2 : CellState n k tgt) a₁
              ≠ cellNext (.acc : CellState n k tgt) a₂ := by
            intro hcon
            rw [cellNext_meas2 a₁, cellNext_acc a₂] at hcon
            cases a₁ <;> injection hcon
          exact hn hnxt
      | rej =>
          exfalso
          have hn : cellNext (.meas2 : CellState n k tgt) a₁
              ≠ cellNext (.rej : CellState n k tgt) a₂ := by
            intro hcon
            rw [cellNext_meas2 a₁, cellNext_rej a₂] at hcon
            cases a₁ <;> injection hcon
          exact hn hnxt
      | meas2 =>
          have ha : a₁ ≠ a₂ := by
            intro h
            apply hne
            exact Prod.ext rfl h
          exact cellAmp_det_orth V htgt (.meas2 : CellState n k tgt) a₁ a₂ ha
            (fun b => (cellAmp_det_row V htgt a₁ b).2.2)
            (fun b => (cellAmp_det_row V htgt a₂ b).2.2)

/-- No cell-machine state moves the head left. -/
theorem cellMove_ne_left {n k tgt : ℕ} (q : CellState n k tgt) :
    cellMove q ≠ QtmMove.left := by
  cases q <;> simp [cellMove]

/-- The local quantum machine that walks to a specified input cell, applies its unitary gate
sequence, and records the Boolean result. -/
def cellLocalQTM {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTM (CellState n k tgt) Bool where
  blank := false
  start := .walk ⟨0, by omega⟩
  step := cellStep V htgt
  wf_norm := by
    intro q a
    classical
    rw [Finset.sum_eq_single_of_mem (cellNext q a) (Finset.mem_univ _)]
    · simp only [cellStep, eq_self, and_true]
      calc (∑ x : Bool, ∑ d : QtmMove,
            ‖(if d = cellMove q then cellAmp V htgt q a x else 0)‖ ^ 2)
          = ∑ x : Bool, ‖cellAmp V htgt q a x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [sum_norm_move]
        _ = 1 := cellAmp_norm V htgt hV q a
    · intro q' _ hne
      simp [cellStep, hne]
  wf_sameCell := by
    intro q₁ a₁ q₂ a₂ hne
    classical
    rw [Finset.sum_eq_single_of_mem (cellNext q₁ a₁) (Finset.mem_univ _)]
    · by_cases hnxt : cellNext q₁ a₁ = cellNext q₂ a₂
      · simp only [cellStep, eq_self, and_true, hnxt]
        have hsum : (∑ x : Bool, ∑ d : QtmMove,
              star (if d = cellMove q₁ then cellAmp V htgt q₁ a₁ x else 0) *
                (if d = cellMove q₂ then cellAmp V htgt q₂ a₂ x else 0))
            = ∑ x : Bool, (if cellMove q₁ = cellMove q₂
                then star (cellAmp V htgt q₁ a₁ x) * cellAmp V htgt q₂ a₂ x else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sum_move_mul_star]
        rw [hsum]
        by_cases hmv : cellMove q₁ = cellMove q₂
        · simp only [if_pos hmv]
          exact cellAmp_orth V htgt hV q₁ q₂ a₁ a₂ hne hnxt
        · have hsum2 : (∑ x : Bool, if cellMove q₁ = cellMove q₂
              then star (cellAmp V htgt q₁ a₁ x) * cellAmp V htgt q₂ a₂ x else 0)
            = ∑ x : Bool, 0 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [if_neg hmv]
          rw [hsum2]
          simp
      · rw [Finset.sum_eq_zero]
        intro x _
        rw [Finset.sum_eq_zero]
        intro d _
        simp only [cellStep, and_true]
        by_cases h1 : (d = cellMove q₁)
        · rw [if_pos h1]
          by_cases h2 : (d = cellMove q₂ ∧ cellNext q₁ a₁ = cellNext q₂ a₂)
          · rw [if_pos h2]
            exact (hnxt h2.2).elim
          · rw [if_neg h2]
            simp
        · rw [if_neg h1]
          simp
    · intro q' _ hne'
      simp [cellStep, hne']
  wf_rightStay := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    by_cases hq₂ : ∃ d₂, q₂ = .walk d₂
    · obtain ⟨d₂, rfl⟩ := hq₂
      rw [show cellStep V htgt (.walk d₂ : CellState n k tgt) a₂ QtmMove.stay q' d = 0 by
        simp [cellStep, cellMove]]
      simp
    · by_cases hq₁ : ∃ d₁, q₁ = .walk d₁
      · obtain ⟨d₁, rfl⟩ := hq₁
        have hstep : cellStep V htgt (.walk d₁ : CellState n k tgt) a₁ QtmMove.right q' c
            = if q' = cellNext (.walk d₁ : CellState n k tgt) a₁
              then cellAmp V htgt (.walk d₁ : CellState n k tgt) a₁ c else 0 := by
          simp [cellStep, cellMove]
        have hmv : cellMove q₂ = QtmMove.stay := by
          cases q₂ with
          | walk d₂ => exact (hq₂ ⟨d₂, rfl⟩).elim
          | gate j₂ => rfl
          | acc => rfl
          | rej => rfl
          | meas2 => rfl
        have hstay : cellStep V htgt q₂ a₂ QtmMove.stay q' d
            = if q' = cellNext q₂ a₂ then cellAmp V htgt q₂ a₂ d else 0 := by
          simp [cellStep, hmv]
        rw [hstep, hstay]
        by_cases h2 : q' = cellNext (.walk d₁ : CellState n k tgt) a₁
        · rw [if_pos h2]
          by_cases h3 : q' = cellNext q₂ a₂
          · rw [if_pos h3]
            exfalso
            exact (cellNext_walk_ne d₁ a₁ q₂ (fun d₂' hq => (hq₂ ⟨d₂', hq⟩).elim) a₂)
              (h2.symm.trans h3)
          · rw [if_neg h3]
            simp
        · rw [if_neg h2]
          simp
      · have hmv : cellMove q₁ = QtmMove.stay := by
          cases q₁ with
          | walk d₁ => exact (hq₁ ⟨d₁, rfl⟩).elim
          | gate j₁ => rfl
          | acc => rfl
          | rej => rfl
          | meas2 => rfl
        rw [show cellStep V htgt q₁ a₁ QtmMove.right q' c = 0 by
          simp [cellStep, hmv]]
        simp
  wf_stayLeft := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    have hz : cellStep V htgt q₂ a₂ QtmMove.left q' d = 0 := by
      unfold cellStep
      rw [if_neg (by
        intro h
        exact (cellMove_ne_left q₂) h.1.symm)]
    rw [hz]
    simp
  wf_rightLeft := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    have hz : cellStep V htgt q₂ a₂ QtmMove.left q' d = 0 := by
      unfold cellStep
      rw [if_neg (by
        intro h
        exact (cellMove_ne_left q₂) h.1.symm)]
    rw [hz]
    simp

/-- The target-cell machine built from unitary gate data satisfies the five local conditions. -/
theorem cellLocalQTM_five {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTMFiveConditions (cellLocalQTM V htgt hV) := by
  exact ⟨(cellLocalQTM V htgt hV).wf_norm, (cellLocalQTM V htgt hV).wf_sameCell,
    (cellLocalQTM V htgt hV).wf_rightStay, (cellLocalQTM V htgt hV).wf_stayLeft,
    (cellLocalQTM V htgt hV).wf_rightLeft⟩

/-- A target-cell transition has its local amplitude precisely when the head move, next state,
and single-cell tape update are valid. -/
theorem cellLocalQTM_windowStep {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (CellState n k tgt) Bool) :
    (windowStep (t := w) (cellLocalQTM V htgt hV) tgt') src =
      if moveCell (cellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = cellNext src.state (src.tape src.head) ∧
          (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j)
      then cellAmp V htgt src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  classical
  simp only [windowStep, Matrix.of_apply, cellLocalQTM, cellStep]
  rw [Finset.sum_eq_single_of_mem (cellMove src.state) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (cellNext src.state (src.tape src.head))
      (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem (tgt'.tape src.head) (Finset.mem_univ _)]
      · by_cases h : (moveCell (cellMove src.state) src.head = some tgt'.head ∧
            tgt'.state = cellNext src.state (src.tape src.head) ∧
            (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j))
        · simp only [if_pos h, and_self, eq_self, ↓reduceIte]
        · simp only [if_neg h]
      · intro b _ hb
        by_cases hcon : (moveCell (cellMove src.state) src.head = some tgt'.head ∧
            tgt'.state = cellNext src.state (src.tape src.head) ∧
            (∀ j, tgt'.tape j = if j = src.head then b else src.tape j))
        · rw [if_pos hcon]
          have hlt : tgt'.tape src.head = b := by
            have hstep := hcon.2.2 src.head
            simpa using! hstep
          exact (hb hlt.symm).elim
        · rw [if_neg hcon]
    · intro q' _ hq
      apply Finset.sum_eq_zero
      intro b _
      by_cases hcon : (moveCell (cellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = q' ∧
          (∀ j, tgt'.tape j = if j = src.head then b else src.tape j))
      · rw [if_pos hcon]
        rw [if_neg (fun hh => hq hh.2)]
      · rw [if_neg hcon]
  · intro d _ hd
    apply Finset.sum_eq_zero
    intro q' _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hcon : (moveCell d src.head = some tgt'.head ∧ tgt'.state = q' ∧
        (∀ j, tgt'.tape j = if j = src.head then b else src.tape j))
    · rw [if_pos hcon]
      rw [if_neg (fun hh => hd hh.1)]
    · rw [if_neg hcon]

/-- A step from a target-cell basis configuration has its local amplitude on valid successor
configurations and zero elsewhere. -/
theorem cellLocalQTM_windowStep_ket {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (CellState n k tgt) Bool) :
    (windowStep (t := w) (cellLocalQTM V htgt hV) *ᵥ Ket src) tgt' =
      if moveCell (cellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = cellNext src.state (src.tape src.head) ∧
          (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j)
      then cellAmp V htgt src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact cellLocalQTM_windowStep V htgt hV src tgt'
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- Replaces a target-cell configuration's state and head-cell bit while preserving its head and
the rest of its tape. -/
def cellCfg {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) (b : Bool) : WindowCfg w (CellState n k tgt) Bool :=
  { base with state := q, tape := fun j => if j = base.head then b else base.tape j }

/-- The two-basis-state superposition at a fixed cell-machine state with a supplied Boolean
amplitude vector. -/
def cellCfgSuper {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) (v : Bool → ℂ) : QState (WindowCfg w (CellState n k tgt) Bool) :=
  v false • Ket (cellCfg base q false) + v true • Ket (cellCfg base q true)

/-- The walk-stage configuration with unchanged tape and head shifted by the walk-stage index
from the base head. -/
def cellWalkCfg {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (d : Fin (tgt + 1)) (h : Fin (2 * w + 1)) (hh : h.val = base.head.val + d.val) :
    WindowCfg w (CellState n k tgt) Bool :=
  { base with head := h, state := .walk d }

/-- The configuration obtained by assigning the supplied next head position and the next walk
state, leaving the tape unchanged. -/
def cellWalkStepCfg {n k tgt w : ℕ} (src : WindowCfg w (CellState n k tgt) Bool)
    (d : Fin (tgt + 1)) (h' : Fin (2 * w + 1)) : WindowCfg w (CellState n k tgt) Bool :=
  { src with head := h', state := cellNext (.walk d) (src.tape src.head) }

/-- A target-cell transition is characterized by its head move, next state, and equality of tape
symbols away from the source head. -/
theorem cellLocalQTM_windowStep_norm {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (CellState n k tgt) Bool) :
    (windowStep (t := w) (cellLocalQTM V htgt hV) tgt') src =
      if moveCell (cellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = cellNext src.state (src.tape src.head) ∧
          (∀ j, j ≠ src.head → tgt'.tape j = src.tape j)
      then cellAmp V htgt src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  have hiff : (moveCell (cellMove src.state) src.head = some tgt'.head ∧
        tgt'.state = cellNext src.state (src.tape src.head) ∧
        (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j))
      ↔ (moveCell (cellMove src.state) src.head = some tgt'.head ∧
        tgt'.state = cellNext src.state (src.tape src.head) ∧
        (∀ j, j ≠ src.head → tgt'.tape j = src.tape j)) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro j hj
      have hj' := h3 j
      simp only [if_neg hj] at hj'
      exact hj'
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro j
      by_cases hj : j = src.head
      · simp [hj]
      · simp [hj, h3 j hj]
  rw [cellLocalQTM_windowStep V htgt hV src tgt']
  by_cases h : (moveCell (cellMove src.state) src.head = some tgt'.head ∧
      tgt'.state = cellNext src.state (src.tape src.head) ∧
      (∀ j, j ≠ src.head → tgt'.tape j = src.tape j))
  · simp only [if_pos h]
    rw [if_pos (hiff.mpr h)]
  · simp only [if_neg h]
    rw [if_neg (fun hh => h (hiff.mp hh))]

/-- The amplitude after a target-cell basis step is its local amplitude exactly when the move,
next state, and off-head tape agreement hold. -/
theorem cellLocalQTM_windowStep_ket_norm {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (CellState n k tgt) Bool) :
    (windowStep (t := w) (cellLocalQTM V htgt hV) *ᵥ Ket src) tgt' =
      if moveCell (cellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = cellNext src.state (src.tape src.head) ∧
          (∀ j, j ≠ src.head → tgt'.tape j = src.tape j)
      then cellAmp V htgt src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact cellLocalQTM_windowStep_norm V htgt hV src tgt'
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- Under the stated head-position and window bounds, one walk step maps a basis configuration
to the prescribed next walk configuration. -/
theorem cellLocalQTM_walkStep {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (d : Fin (tgt + 1)) (h : Fin (2 * w + 1)) (hh : h.val = base.head.val + d.val)
    (hlt : h.val < 2 * w) (h' : Fin (2 * w + 1)) (hh' : h'.val = h.val + 1) :
    (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ Ket (cellWalkCfg base d h hh)
      = Ket (cellWalkStepCfg (cellWalkCfg base d h hh) d h') := by
  classical
  have hmove : moveCell (cellMove (.walk d : CellState n k tgt)) h = some h' := by
    simp only [cellMove, moveCell]
    split
    · rename_i hbad
      omega
    · have heq : (⟨h.val + 1, by omega⟩ : Fin (2 * w + 1)) = h' := Fin.ext hh'.symm
      rw [heq]
  have hamp : ∀ t : Bool, cellAmp V htgt (.walk d : CellState n k tgt) (base.tape h) t
      = if t = base.tape h then 1 else 0 := by
    intro t
    simp [cellAmp]
  have hrec : cellWalkStepCfg (cellWalkCfg base d h hh) d h'
      = (WindowCfg.mk h' (cellNext (.walk d) (base.tape h)) base.tape : WindowCfg w (CellState n k tgt) Bool) := by
    rfl
  funext tgtC
  rw [cellLocalQTM_windowStep_ket_norm]
  simp only [cellWalkCfg, cellWalkStepCfg]
  by_cases hcond : (moveCell (cellMove (.walk d : CellState n k tgt)) h = some tgtC.head ∧
      tgtC.state = cellNext (.walk d : CellState n k tgt) (base.tape h) ∧
      (∀ j, j ≠ h → tgtC.tape j = base.tape j))
  · rw [if_pos hcond, hamp]
    by_cases hsym : tgtC.tape h = base.tape h
    · rw [if_pos hsym]
      have hEq : tgtC = cellWalkStepCfg (cellWalkCfg base d h hh) d h' := by
        refine WindowCfg_eq_of_fields tgtC (cellWalkStepCfg (cellWalkCfg base d h hh) d h') ?_ ?_ ?_
        · have h1 := hcond.1
          rw [hmove] at h1
          have h1' : tgtC.head = h' := Option.some.inj h1 |>.symm
          simpa [cellWalkStepCfg, cellWalkCfg] using! h1'
        · have h2 := hcond.2.1
          simpa [cellWalkStepCfg, cellWalkCfg] using! h2
        · intro j
          by_cases hj : j = h
          · subst hj
            exact hsym
          · have h3 := hcond.2.2 j hj
            simpa [cellWalkStepCfg, cellWalkCfg] using! h3
      have hEqrec :
          tgtC = (WindowCfg.mk h' (cellNext (.walk d) (base.tape h)) base.tape : WindowCfg w (CellState n k tgt) Bool) := hEq.trans hrec
      rw [hEqrec]
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · rw [if_neg hsym]
      have hEqrec : tgtC ≠ (WindowCfg.mk h' (cellNext (.walk d) (base.tape h)) base.tape : WindowCfg w (CellState n k tgt) Bool) := by
        intro heq
        apply hsym
        have h1 := congrArg (fun c => c.tape h) heq
        have h1' : tgtC.tape h = ((WindowCfg.mk h' (cellNext (.walk d) (base.tape h)) base.tape : WindowCfg w (CellState n k tgt) Bool)).tape h := by
          simpa using! h1
        have h2 :
            ((WindowCfg.mk h' (cellNext (.walk d) (base.tape h)) base.tape : WindowCfg w (CellState n k tgt) Bool)).tape h = base.tape h := rfl
        rw [h1', h2]
      simp [Qatlib.Foundations.PureStateMath.Ket, hEqrec]
  · rw [if_neg hcond]
    have hEqrec : tgtC ≠ (WindowCfg.mk h' (cellNext (.walk d) (base.tape h)) base.tape : WindowCfg w (CellState n k tgt) Bool) := by
      intro heq
      apply hcond
      refine ⟨?_, ?_, ?_⟩
      · rw [hmove]
        have hhead := congrArg (fun c => c.head) heq
        have hhead' : tgtC.head = h' := by
          simpa using! hhead
        rw [hhead']
      · have hst := congrArg (fun c => c.state) heq
        simpa using! hst
      · intro j _hj
        have ht := congrArg (fun c => c.tape j) heq
        simpa using! ht
    simp [Qatlib.Foundations.PureStateMath.Ket, hEqrec]

/-- Starting at walk stage zero with sufficient window space, `e ≤ tgt` steps shift the head
right by `e` and advance the walk stage to `e`. -/
theorem cellLocalQTM_walkIter {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (hstart : base.state = .walk 0) (hbound : base.head.val + tgt + 1 ≤ 2 * w) (e : ℕ) :
    ∀ (he : e ≤ tgt),
    (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ e *ᵥ Ket base
      = Ket (cellWalkCfg base ⟨e, by omega⟩ ⟨base.head.val + e, by omega⟩ rfl) := by
  induction e with
  | zero =>
      intro he
      simp only [pow_zero, Matrix.one_mulVec]
      have hcfg : cellWalkCfg base ⟨0, by omega⟩ ⟨base.head.val + 0, by omega⟩ rfl
          = base := by
        refine WindowCfg_eq_of_fields _ _ ?_ ?_ ?_
        · apply Fin.ext
          rfl
        · simpa [cellWalkCfg] using! hstart.symm
        · intro j
          rfl
      rw [hcfg]
  | succ e ih =>
      intro he
      have he' : e < tgt := by omega
      have hlt : base.head.val + e < 2 * w := by omega
      calc
        (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (e + 1) *ᵥ Ket base
            = (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ
              ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ e *ᵥ Ket base) := by
                rw [pow_succ', ← Matrix.mulVec_mulVec]
        _ = (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ
              Ket (cellWalkCfg base ⟨e, by omega⟩ ⟨base.head.val + e, by omega⟩ rfl) :=
            congrArg (fun v => (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ v)
              (ih (Nat.le_of_lt he'))
        _ = Ket (cellWalkStepCfg (cellWalkCfg base ⟨e, by omega⟩ ⟨base.head.val + e, by omega⟩ rfl)
              ⟨e, by omega⟩ ⟨base.head.val + e + 1, by omega⟩) :=
            cellLocalQTM_walkStep V htgt hV base ⟨e, by omega⟩ ⟨base.head.val + e, by omega⟩
              rfl hlt ⟨base.head.val + e + 1, by omega⟩ rfl
        _ = Ket (cellWalkCfg base ⟨e + 1, by omega⟩ ⟨base.head.val + e + 1, by omega⟩ rfl) := by
            have hrec : cellWalkStepCfg (cellWalkCfg base ⟨e, by omega⟩ ⟨base.head.val + e, by omega⟩
                rfl) ⟨e, by omega⟩ ⟨base.head.val + e + 1, by omega⟩
                = (WindowCfg.mk ⟨base.head.val + e + 1, by omega⟩
                    (cellNext (.walk ⟨e, by omega⟩) (base.tape ⟨base.head.val + e, by omega⟩))
                    base.tape : WindowCfg w (CellState n k tgt) Bool) := by
              rfl
            rw [hrec]
            have hnext : cellNext (.walk ⟨e, by omega⟩ : CellState n k tgt)
                  (base.tape ⟨base.head.val + e, by omega⟩)
                = .walk ⟨e + 1, by omega⟩ := by
              rw [cellNext_walk]
              have hne : ¬ (⟨e, by omega⟩ : Fin (tgt + 1)).val = tgt := by
                intro hcon
                have hcon' : e = tgt := by simpa using! hcon
                omega
              rw [dif_neg hne]
            rw [hnext]
            apply congrArg Ket
            refine WindowCfg_eq_of_fields _ _ ?_ ?_ ?_
            · rfl
            · rfl
            · intro j
              rfl

/-- With `n ≤ w`, the initialized target-cell machine places each input bit at its designated
window position `w+1+i`. -/
theorem cellInit_tape_input {n k tgt w : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (x : Reg n) (hw : n ≤ w) (i : Fin n) (j : Fin (2 * w + 1))
    (hj : j.val = w + 1 + i.val) :
    (initWindowCfg (t := w) (cellLocalQTM (k := k) V htgt hV) n x).tape j = x i := by
  have hj' : j = ⟨w + 1 + i.val, by omega⟩ := Fin.ext hj
  rw [hj']
  have h1n : 1 + i.val ≤ n := by omega
  have h2 : w + 1 + i.val ≤ w + n := by omega
  simp only [initWindowCfg]
  rw [dif_pos ⟨by omega, h2⟩]
  have hval : (w + 1 + i.val - w - 1) = i.val := by omega
  have hfin : (⟨w + 1 + i.val - w - 1, by omega⟩ : Fin n) = i := by
    apply Fin.ext
    exact hval
  rw [hfin]

/-- The configuration at gate stage zero with unchanged tape and head shifted right by `tgt+1`,
assuming sufficient window space. -/
def cellArriveCfg {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (hed : base.head.val + tgt + 1 ≤ 2 * w) :
    WindowCfg w (CellState n k tgt) Bool :=
  { base with head := ⟨base.head.val + tgt + 1, by omega⟩, state := .gate ⟨0, by omega⟩ }

/-- From walk stage zero with sufficient window space, `tgt+1` steps reach `cellArriveCfg`
exactly. -/
theorem cellLocalQTM_walkArrive {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (hstart : base.state = .walk 0) (hbound : base.head.val + tgt + 1 ≤ 2 * w) :
    (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (tgt + 1) *ᵥ Ket base
      = Ket (cellArriveCfg base hbound) := by
  classical
  have hlt : base.head.val + tgt < 2 * w := by omega
  have hiter : (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ tgt *ᵥ Ket base
      = Ket (cellWalkCfg base ⟨tgt, by omega⟩ ⟨base.head.val + tgt, by omega⟩ rfl) :=
    cellLocalQTM_walkIter V htgt hV base hstart hbound tgt (Nat.le_refl tgt)
  calc
    (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (tgt + 1) *ᵥ Ket base
        = (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ
          ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ tgt *ᵥ Ket base) := by
            rw [pow_succ', ← Matrix.mulVec_mulVec]
    _ = (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ
          Ket (cellWalkCfg base ⟨tgt, by omega⟩ ⟨base.head.val + tgt, by omega⟩ rfl) :=
          by rw [hiter]
    _ = Ket (cellWalkStepCfg (cellWalkCfg base ⟨tgt, by omega⟩ ⟨base.head.val + tgt, by omega⟩ rfl)
          ⟨tgt, by omega⟩ ⟨base.head.val + tgt + 1, by omega⟩) :=
          cellLocalQTM_walkStep V htgt hV base ⟨tgt, by omega⟩ ⟨base.head.val + tgt, by omega⟩
            rfl hlt ⟨base.head.val + tgt + 1, by omega⟩ rfl
    _ = Ket (cellArriveCfg base hbound) := by
        have hrec : cellWalkStepCfg (cellWalkCfg base ⟨tgt, by omega⟩
              ⟨base.head.val + tgt, by omega⟩ rfl) ⟨tgt, by omega⟩
              ⟨base.head.val + tgt + 1, by omega⟩
            = (WindowCfg.mk ⟨base.head.val + tgt + 1, by omega⟩
                (cellNext (.walk ⟨tgt, by omega⟩) (base.tape ⟨base.head.val + tgt, by omega⟩))
                base.tape : WindowCfg w (CellState n k tgt) Bool) := by
          rfl
        rw [hrec]
        have hnext : cellNext (.walk ⟨tgt, by omega⟩ : CellState n k tgt)
              (base.tape ⟨base.head.val + tgt, by omega⟩)
            = .gate ⟨0, by omega⟩ := by
          rw [cellNext_walk]
          have heq : (⟨tgt, by omega⟩ : Fin (tgt + 1)).val = tgt := rfl
          rw [dif_pos heq]
        rw [hnext]
        apply congrArg Ket
        refine WindowCfg_eq_of_fields _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · intro j
          rfl

/-- The state field of `cellCfg` is its supplied state. -/
theorem cellCfg_state {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) (b : Bool) :
    (cellCfg base q b).state = q := rfl

/-- Constructing `cellCfg` preserves the base head position. -/
theorem cellCfg_head {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) (b : Bool) :
    (cellCfg base q b).head = base.head := rfl

/-- The tape of `cellCfg` is the base tape with its head cell assigned the supplied bit. -/
theorem cellCfg_tape {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) (b : Bool) :
    ∀ j, (cellCfg base q b).tape j = if j = base.head then b else base.tape j := by
  intro j
  simp [cellCfg]

/-- The head-cell symbol of `cellCfg` is its supplied bit. -/
theorem cellCfg_tape_at {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) (b : Bool) :
    (cellCfg base q b).tape base.head = b := by
  simp [cellCfg]

/-- The false-bit and true-bit configurations constructed by `cellCfg` are distinct. -/
theorem cellCfg_ne {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (q : CellState n k tgt) :
    cellCfg base q false ≠ cellCfg base q true := by
  intro h
  have h1 := congrArg (fun c => c.tape base.head) h
  simp [cellCfg] at h1

/-- The superposition at gate stage `j ≤ k` with the supplied Boolean amplitude vector at the
head cell. -/
def cellGateSuper {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (j : ℕ) (hj : j ≤ k) (v : Bool → ℂ) : QState (WindowCfg w (CellState n k tgt) Bool) :=
  v false • Ket (cellCfg base (.gate ⟨j, by omega⟩) false) +
    v true • Ket (cellCfg base (.gate ⟨j, by omega⟩) true)

/-- One target-cell gate step advances the stage and multiplies the two basis amplitudes by the
corresponding target-cell unitary. -/
theorem cellLocalQTM_gateStep {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool) (j : ℕ) (hj : j < k)
    (v : Bool → ℂ) :
    (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ
        (v false • Ket (cellCfg base (.gate ⟨j, by omega⟩) false) +
          v true • Ket (cellCfg base (.gate ⟨j, by omega⟩) true))
      = (V ⟨tgt, htgt⟩ ⟨j, by omega⟩ false false * v false
          + V ⟨tgt, htgt⟩ ⟨j, by omega⟩ false true * v true) •
          Ket (cellCfg base (.gate ⟨j + 1, by omega⟩) false) +
        (V ⟨tgt, htgt⟩ ⟨j, by omega⟩ true false * v false
          + V ⟨tgt, htgt⟩ ⟨j, by omega⟩ true true * v true) •
          Ket (cellCfg base (.gate ⟨j + 1, by omega⟩) true) := by
  classical
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  ext tgt
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [cellLocalQTM_windowStep_ket_norm, cellLocalQTM_windowStep_ket_norm]
  simp only [cellCfg_state, cellCfg_head, cellMove, moveCell, cellNext,
    cellAmp, hj, cellCfg_tape, Option.some.injEq, dif_pos, if_pos]
  have htab : (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j)
      ↔ (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then true else base.tape j) := by
    constructor
    · intro h j hj
      have hh := h j hj
      rw [if_neg hj] at hh
      rw [if_neg hj]
      exact hh
    · intro h j hj
      have hh := h j hj
      rw [if_neg hj] at hh
      rw [if_neg hj]
      exact hh
  by_cases h : (base.head = tgt.head ∧ tgt.state = .gate ⟨j + 1, by omega⟩ ∧
      (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j))
  · rw [if_pos h]
    have h1 : (base.head = tgt.head ∧ tgt.state = .gate ⟨j + 1, by omega⟩ ∧
        (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then true else base.tape j)) :=
      ⟨h.1, h.2.1, fun j hj => (htab.mp h.2.2) j hj⟩
    rw [if_pos h1]
    by_cases hb : tgt.tape base.head = false
    · have htgt : tgt = cellCfg base (.gate ⟨j + 1, by omega⟩) false := by
        apply WindowCfg_eq_of_fields
        · exact h.1.symm
        · exact h.2.1
        · intro i
          by_cases hi : i = base.head
          · simp [cellCfg, hi, hb]
          · have hh := h.2.2 i hi
            simp only [if_neg hi] at hh
            simp [cellCfg, hi, hh]
      rw [htgt]
      have hne : cellCfg base (.gate ⟨j + 1, by omega⟩) false
          ≠ cellCfg base (.gate ⟨j + 1, by omega⟩) true :=
        cellCfg_ne base _
      simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, cellCfg_tape_at]
      rw [if_neg hne]
      ring
    · have htgt : tgt = cellCfg base (.gate ⟨j + 1, by omega⟩) true := by
        apply WindowCfg_eq_of_fields
        · exact h.1.symm
        · exact h.2.1
        · intro i
          by_cases hi : i = base.head
          · simp [cellCfg, hi, hb]
          · have hh := h.2.2 i hi
            simp only [if_neg hi] at hh
            simp [cellCfg, hi, hh]
      rw [htgt]
      have hne : cellCfg base (.gate ⟨j + 1, by omega⟩) true
          ≠ cellCfg base (.gate ⟨j + 1, by omega⟩) false :=
        (cellCfg_ne base _).symm
      simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, cellCfg_tape_at]
      rw [if_neg hne]
      ring
  · rw [if_neg h]
    have h1 : ¬ (base.head = tgt.head ∧ tgt.state = .gate ⟨j + 1, by omega⟩ ∧
        (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then true else base.tape j)) :=
      fun hh => h ⟨hh.1, hh.2.1, fun j hj => (htab.mpr hh.2.2) j hj⟩
    rw [if_neg h1]
    by_cases h0 : tgt = cellCfg base (.gate ⟨j + 1, by omega⟩) false
    · exfalso
      have hcond' : base.head = tgt.head ∧
          tgt.state = .gate ⟨j + 1, by omega⟩ ∧
          (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j) := by
        rw [h0]
        refine ⟨rfl, rfl, ?_⟩
        intro j hj
        simp [cellCfg, hj]
      exact h hcond'
    · by_cases h2 : tgt = cellCfg base (.gate ⟨j + 1, by omega⟩) true
      · exfalso
        have hcond' : base.head = tgt.head ∧
            tgt.state = .gate ⟨j + 1, by omega⟩ ∧
            (∀ j, j ≠ base.head → tgt.tape j = if j = base.head then false else base.tape j) := by
          rw [h2]
          refine ⟨rfl, rfl, ?_⟩
          intro j hj
          simp [cellCfg, hj]
        exact h hcond'
      · simp [Qatlib.Foundations.PureStateMath.Ket, h0, h2]

/-- A target-cell gate step advances `cellGateSuper` and applies the corresponding unitary to
its Boolean amplitude vector. -/
theorem cellLocalQTM_gateStep_super {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool) (j : ℕ) (hj : j < k)
    (v : Bool → ℂ) :
    (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ cellGateSuper base j (by omega) v
      = cellGateSuper base (j + 1) (by omega) (V ⟨tgt, htgt⟩ ⟨j, by omega⟩ *ᵥ v) := by
  rw [cellGateSuper, cellGateSuper, Matrix.mulVec_add, ← Matrix.mulVec_add]
  rw [cellLocalQTM_gateStep V htgt hV base j hj v]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply]
  ring

/-- After `j ≤ k` gate steps, the target-cell superposition has amplitude vector given by the
first `j` target-cell gates. -/
theorem cellLocalQTM_gateSeq {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool) (v : Bool → ℂ) :
    ∀ (j : ℕ) (hj : j ≤ k),
      (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ j *ᵥ cellGateSuper base 0 (by omega) v
        = cellGateSuper base j hj (gateSeqProd (V ⟨tgt, htgt⟩) j hj *ᵥ v) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [cellGateSuper, pow_zero, Matrix.one_mulVec, gateSeqProd]
  | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [ih (by omega)]
      rw [cellLocalQTM_gateStep_super V htgt hV base j hjk]
      rw [Matrix.mulVec_mulVec]
      have hprod : gateSeqProd (V ⟨tgt, htgt⟩) (j + 1) hj
          = V ⟨tgt, htgt⟩ ⟨j, by omega⟩ * gateSeqProd (V ⟨tgt, htgt⟩) j (by omega) := rfl
      rw [hprod]

/-- The terminal target-cell gate stage sends a basis bit to its accepting or rejecting
configuration and flips the tape bit. -/
theorem cellLocalQTM_measure_ket {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool) (a : Bool)
    (tgtC : WindowCfg w (CellState n k tgt) Bool) :
    (windowStep (t := w) (cellLocalQTM V htgt hV) *ᵥ
        Ket (cellCfg base (.gate ⟨k, by omega⟩) a)) tgtC
      = (if tgtC = cellCfg base (if a then .acc else .rej) (!a) then 1 else 0) := by
  classical
  rw [cellLocalQTM_windowStep_ket_norm]
  simp only [cellCfg_state, cellCfg_head, cellCfg_tape_at]
  rw [show moveCell (cellMove (.gate ⟨k, by omega⟩ : CellState n k tgt)) base.head = some base.head by
    simp [cellMove, moveCell]]
  rw [show cellNext (.gate ⟨k, by omega⟩ : CellState n k tgt) a = (if a then .acc else .rej) by
    simp [cellNext]]
  rw [show cellAmp V htgt (.gate ⟨k, by omega⟩ : CellState n k tgt) a (tgtC.tape base.head)
      = (if tgtC.tape base.head = !a then 1 else 0) by simp [cellAmp]]
  simp only [Option.some.injEq]
  by_cases hC : (base.head = tgtC.head ∧ tgtC.state = (if a then .acc else .rej) ∧
      (∀ j, j ≠ base.head → tgtC.tape j = (cellCfg base (.gate ⟨k, by omega⟩) a).tape j))
  · rw [if_pos hC]
    by_cases hflip : tgtC.tape base.head = !a
    · rw [if_pos hflip]
      have hcon : tgtC = cellCfg base (if a then .acc else .rej) (!a) := by
        apply WindowCfg_eq_of_fields
        · exact hC.1.symm
        · exact hC.2.1
        · intro j
          by_cases hj : j = base.head
          · subst hj
            simp [cellCfg, hflip]
          · have hh := hC.2.2 j hj
            simp [cellCfg, hj, hh]
      rw [hcon]
      simp
    · rw [if_neg hflip]
      have hne : tgtC ≠ cellCfg base (if a then .acc else .rej) (!a) := by
        intro heq
        apply hflip
        have h1 := congrArg (fun c => c.tape base.head) heq
        simpa [cellCfg] using! h1
      simp [hne]
  · rw [if_neg hC]
    have hne : tgtC ≠ cellCfg base (if a then .acc else .rej) (!a) := by
      intro heq
      apply hC
      refine ⟨?_, ?_, ?_⟩
      · have h1 := congrArg (fun c => c.head) heq
        simpa [cellCfg] using! h1.symm
      · have h2 := congrArg (fun c => c.state) heq
        simpa [cellCfg] using! h2
      · intro j hj
        have h3 := congrArg (fun c => c.tape j) heq
        simpa [cellCfg, hj] using! h3
    simp [hne]

/-- A step from the terminal target-cell superposition separates the false and true amplitudes
into rejecting and accepting configurations. -/
theorem cellLocalQTM_measure {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool) (v : Bool → ℂ) :
    (windowStep (t := w) (cellLocalQTM V htgt hV)) *ᵥ cellGateSuper base k (by omega) v
      = v false • Ket (cellCfg base (.rej) true) +
        v true • Ket (cellCfg base (.acc) false) := by
  classical
  funext tgtC
  rw [cellGateSuper, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have h1 := cellLocalQTM_measure_ket V htgt hV base false tgtC
  have h2 := cellLocalQTM_measure_ket V htgt hV base true tgtC
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [h1, h2]
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- After `k+1` steps from gate stage zero, accepting Born mass is the true-component squared
norm of the target-cell gate product applied to the initial amplitude vector. -/
theorem cellLocalQTM_acceptMass {n k tgt : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (htgt : tgt < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool) (v : Bool → ℂ) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : CellState n k tgt)),
      BornProb ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (k + 1) *ᵥ
        cellGateSuper base 0 (by omega) v) c)
      = ‖(gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v) true‖ ^ 2 := by
  classical
  have hψ : (windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (k + 1) *ᵥ
      cellGateSuper base 0 (by omega) v
      = (gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v) false • Ket (cellCfg base (.rej) true) +
        (gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v) true • Ket (cellCfg base (.acc) false) := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [cellLocalQTM_gateSeq V htgt hV base v k (by omega)]
    rw [cellLocalQTM_measure V htgt hV base (gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v)]
  rw [hψ]
  have hne : cellCfg base (.acc) false ≠ cellCfg base (.rej) true := by
    intro hcon
    have hh := congrArg WindowCfg.state hcon
    simp [cellCfg_state] at hh
  rw [Finset.sum_eq_single (cellCfg base (.acc) false)]
  · have hval : ((gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v) false
          • Ket (cellCfg base (.rej) true) +
        (gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v) true • Ket (cellCfg base (.acc) false))
        (cellCfg base (.acc) false)
      = (gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ v) true := by
      simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, hne]
    rw [BornProb, hval]
  · intro c hc hne'
    have hstate : c.state = (.acc : CellState n k tgt) := (Finset.mem_filter.mp hc).2
    rw [BornProb]
    have hne1 : c ≠ cellCfg base (.rej) true := by
      intro hcon
      have hh := congrArg WindowCfg.state hcon
      simp [cellCfg_state] at hh
      exact absurd (hstate.symm.trans hh) (by simp)
    simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, hne1, hne']
  · intro h
    exact (h (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, cellCfg_state base (.acc : CellState n k tgt) false⟩)).elim

/-- A basis configuration at gate stage zero equals the target-cell superposition concentrated
on its head-cell bit. -/
theorem ket_eq_cellGateSuper {n k tgt w : ℕ} (base : WindowCfg w (CellState n k tgt) Bool)
    (b : Bool) (hb : base.tape base.head = b) (hq : base.state = .gate 0) :
    Ket base = cellGateSuper base 0 (by omega) (fun c => if c = b then (1 : ℂ) else 0) := by
  classical
  have hcfg : base = cellCfg base (.gate 0) b := by
    refine WindowCfg_eq_of_fields base (cellCfg base (.gate 0) b) rfl ?_ ?_
    · simpa [cellCfg] using! hq
    · intro j
      by_cases hj : j = base.head
      · subst hj
        simp [cellCfg, hb]
      · simp [cellCfg, hj]
  funext y
  rw [cellGateSuper]
  simp only [Pi.add_apply, Pi.smul_apply]
  by_cases hbf : b = false
  · rw [hbf]
    rw [if_pos rfl, if_neg (by simp)]
    simp only [one_smul, zero_smul]
    have hcfgF : base = cellCfg base (.gate ⟨0, by omega⟩) false := by
      rw [hbf] at hcfg
      exact hcfg
    rw [hcfgF.symm]
    exact (add_zero (Ket base y : ℂ)).symm
  · have hbt : b = true := by
      cases b with
      | false => exact absurd (by simp : false = false) hbf
      | true => rfl
    rw [hbt]
    rw [if_neg (by simp), if_pos rfl]
    simp only [one_smul, zero_smul]
    have hcfgT : base = cellCfg base (.gate ⟨0, by omega⟩) true := by
      rw [hbt] at hcfg
      exact hcfg
    rw [hcfgT.symm]
    exact (zero_add (Ket base y : ℂ)).symm

/-- For `n ≤ w`, the initialized target-cell machine's accepting mass after `tgt+k+2` steps is
the true-component squared norm of the target-cell gate product applied to its input bit. -/
theorem headStay_cell_acceptMass_multi {n k tgt w : ℕ}
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (htgt : tgt < n)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (hw : n ≤ w) (x : Reg n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : CellState n k tgt)),
      BornProb ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (tgt + k + 2)
        *ᵥ Ket (initWindowCfg (t := w) (cellLocalQTM V htgt hV) n x)) c)
      = ‖(gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ
          (fun c => if c = x ⟨tgt, htgt⟩ then (1 : ℂ) else 0)) true‖ ^ 2 := by
  classical
  set base := initWindowCfg (t := w) (cellLocalQTM V htgt hV) n x with hbase
  have hstart : base.state = .walk 0 := by
    simp [hbase, initWindowCfg, cellLocalQTM]
  have hbound : base.head.val + tgt + 1 ≤ 2 * w := by
    have h1 : base.head.val = w := by
      simp [hbase, initWindowCfg]
    have h2 : tgt + 1 ≤ w := by omega
    omega
  have harrive := cellLocalQTM_walkArrive V htgt hV base hstart hbound
  have hhead1 : base.head.val = w := by
    simp [hbase, initWindowCfg]
  have harr_state : (cellArriveCfg base hbound).state = .gate 0 := rfl
  have harr_tape : (cellArriveCfg base hbound).tape (cellArriveCfg base hbound).head
      = x ⟨tgt, htgt⟩ := by
    have hhead : (cellArriveCfg base hbound).head = ⟨w + 1 + tgt, by omega⟩ := by
      apply Fin.ext
      simp [cellArriveCfg]
      omega
    rw [hhead]
    have htape : base.tape ⟨w + 1 + tgt, by omega⟩ = x ⟨tgt, htgt⟩ :=
      cellInit_tape_input V htgt hV x hw ⟨tgt, htgt⟩ ⟨w + 1 + tgt, by omega⟩ rfl
    simpa [cellArriveCfg, hbase] using! htape
  have hsuper : Ket (cellArriveCfg base hbound)
      = cellGateSuper (cellArriveCfg base hbound) 0 (by omega)
          (fun c => if c = x ⟨tgt, htgt⟩ then (1 : ℂ) else 0) :=
    ket_eq_cellGateSuper _ _ harr_tape harr_state
  have hpow : (k + 1) + (tgt + 1) = tgt + k + 2 := by omega
  rw [← hpow, pow_add, ← Matrix.mulVec_mulVec, harrive, hsuper]
  exact cellLocalQTM_acceptMass V htgt hV (cellArriveCfg base hbound) _

/-- Setting wire `i` gives the assigned bit on that wire. -/
theorem setBitI_bit {n : ℕ} (i : Fin n) (x : Reg n) (b : Bool) :
    setBitI i x b i = b := by
  simp [setBitI]

/-- Setting wire `i` leaves every other wire unchanged. -/
theorem setBitI_of_ne {n : ℕ} (i : Fin n) (x : Reg n) (b : Bool) {j : Fin n} (hj : j ≠ i) :
    setBitI i x b j = x j := by
  simp [setBitI, hj]

/-- Flipping wire `i` negates its Boolean value. -/
theorem flipI_bit {n : ℕ} (i : Fin n) (x : Reg n) : flipI i x i = !x i := by
  simp [flipI, setBitI]

/-- Flipping wire `i` preserves every other wire. -/
theorem flipI_of_ne {n : ℕ} (i : Fin n) (x : Reg n) {j : Fin n} (hj : j ≠ i) :
    flipI i x j = x j := by
  simp [flipI, setBitI, hj]

/-- Flipping a selected wire changes the register. -/
theorem flipI_ne {n : ℕ} (i : Fin n) (x : Reg n) : flipI i x ≠ x := by
  intro h
  have h1 := congrFun h i
  rw [flipI_bit] at h1
  have h2 : x i ≠ !x i := by
    cases hx : x i <;> simp_all
  exact h2 h1.symm

/-- Agreement outside a selected wire is symmetric. -/
theorem AgreesOutsideI_comm {n : ℕ} (i : Fin n) (x y : Reg n) :
    AgreesOutsideI i x y ↔ AgreesOutsideI i y x := by
  constructor
  · intro h j hj
    exact (h j hj).symm
  · intro h j hj
    exact (h j hj).symm

/-- Registers agreeing outside wire `i` are either equal or differ by flipping wire `i`. -/
theorem agreesOutsideI_iff {n : ℕ} (i : Fin n) (x y : Reg n) :
    AgreesOutsideI i x y ↔ (y = x ∨ y = flipI i x) := by
  constructor
  · intro h
    by_cases hb : y i = x i
    · left
      funext j
      by_cases hj : j = i
      · rw [hj]
        exact hb
      · exact h j hj
    · right
      have hne : y i = !x i := by
        cases hy : y i <;> cases hx : x i <;> simp_all
      funext j
      by_cases hj : j = i
      · rw [hj]
        simp [flipI, setBitI, hne]
      · exact (h j hj).trans (flipI_of_ne i x hj).symm
  · intro h
    rcases h with rfl | rfl
    · intro j hj
      rfl
    · intro j hj
      exact flipI_of_ne i x hj

/-- Every basis ket is a `WireState` with Boolean amplitudes concentrated on its bit at the
selected wire. -/
theorem ket_wireI {n : ℕ} (i : Fin n) (x : Reg n) :
    WireState i x (fun c => if c = x i then (1 : ℂ) else 0) (Ket x) := by
  intro y
  by_cases hbit : y i = x i
  · by_cases hag : AgreesOutsideI i x y
    · have hy : y = x := by
        rcases (agreesOutsideI_iff i x y).mp hag with h | h
        · exact h
        · exfalso
          have hfl := congrFun h i
          rw [flipI_bit] at hfl
          simp_all
      have hagx : AgreesOutsideI i x x := by intro j hj; rfl
      rw [hy]
      simp [Qatlib.Foundations.PureStateMath.Ket, agreesOutsideI, hagx]
    · have hyn : y ≠ x := by
        intro h
        exact hag (by rw [h]; intro j hj; rfl)
      have hag0 : agreesOutsideI i x y = 0 := by
        rw [agreesOutsideI, if_neg hag]
      simp [Qatlib.Foundations.PureStateMath.Ket, hag0, hbit, hyn]
  · have hyn : y ≠ x := by
      intro h
      exact hbit (congrFun h i)
    have hc0 : (fun c => if c = x i then (1 : ℂ) else 0) (y i) = 0 := by
      simp [hbit]
    simp [Qatlib.Foundations.PureStateMath.Ket, hc0, hyn]

/-- Applying a gate embedded on wire `i` of a `WireState` multiplies its Boolean amplitude
vector and preserves the outside-agreement factor. -/
theorem embedRegI_applyGate {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ) (x : Reg n)
    (c : Bool → ℂ) (ψ : Reg n → ℂ) (hψ : WireState i x c ψ) :
    ∀ y : Reg n,
      ApplyGate (embedRegI i U) ψ y = (U *ᵥ c) (y i) * agreesOutsideI i x y := by
  classical
  intro y
  have hne : x ≠ flipI i x := (flipI_ne i x).symm
  have key : ∀ z ∈ (Finset.univ : Finset (Reg n)), z ∉ ({x, flipI i x} : Finset (Reg n)) →
      embedRegI i U y z * ψ z = 0 := by
    intro z _ hz
    have hag : ¬ AgreesOutsideI i x z := by
      intro h
      rcases (agreesOutsideI_iff i x z).mp h with h | h
      · exact hz (by simp [h])
      · exact hz (by simp [h])
    have hz0 : agreesOutsideI i x z = 0 := by simp [agreesOutsideI, hag]
    rw [hψ z, hz0, mul_zero, mul_zero]
  have hsum : (∑ z : Reg n, embedRegI i U y z * ψ z)
      = ∑ z ∈ ({x, flipI i x} : Finset (Reg n)), embedRegI i U y z * ψ z :=
    (Finset.sum_subset (s₁ := ({x, flipI i x} : Finset (Reg n)))
      (s₂ := (Finset.univ : Finset (Reg n)))
      (f := fun z => embedRegI i U y z * ψ z)
      (fun _ _ => by simp)
      key).symm
  have hpair : (∑ z ∈ ({x, flipI i x} : Finset (Reg n)), embedRegI i U y z * ψ z)
      = embedRegI i U y x * ψ x + embedRegI i U y (flipI i x) * ψ (flipI i x) :=
    Finset.sum_pair (f := fun z => embedRegI i U y z * ψ z) hne
  have hagx : AgreesOutsideI i x x := by intro j hj; rfl
  have hagf : AgreesOutsideI i x (flipI i x) := by
    intro j hj
    exact flipI_of_ne i x hj
  have hψx : ψ x = c (x i) := by
    rw [hψ x, agreesOutsideI, if_pos hagx]
    simp
  have hψf : ψ (flipI i x) = c ((flipI i x) i) := by
    rw [hψ (flipI i x), agreesOutsideI, if_pos hagf]
    simp
  have hcond : (AgreesOutsideI i y x) ↔ (AgreesOutsideI i y (flipI i x)) := by
    constructor
    · intro h j hj
      exact (flipI_of_ne i x hj).trans (h j hj)
    · intro h j hj
      exact (flipI_of_ne i x hj).symm.trans (h j hj)
  change (∑ z : Reg n, embedRegI i U y z * ψ z) = _
  rw [hsum, hpair, hψx, hψf]
  simp only [embedRegI, agreesOutsideI]
  by_cases hA : AgreesOutsideI i y x
  · have hA' : AgreesOutsideI i y (flipI i x) := hcond.mp hA
    have hagxy : AgreesOutsideI i x y := (AgreesOutsideI_comm i x y).mpr hA
    rw [if_pos hA, if_pos hA', if_pos hagxy, mul_one]
    have hfl := flipI_bit i x
    rw [hfl]
    have hb := sum_bool_pair (f := fun z => U (y i) z * c z) (x i)
    rw [hb, mulVec_bool]
  · have hA' : ¬ AgreesOutsideI i y (flipI i x) := fun h => hA (hcond.mpr h)
    have hagxy : ¬ AgreesOutsideI i x y := fun h => hA ((AgreesOutsideI_comm i x y).mp h)
    rw [if_neg hA, if_neg hA', if_neg hagxy]
    simp

/-- Running gates embedded on wire `i` applies their Boolean product to its amplitude vector and
preserves the remaining bits of a `WireState`. -/
theorem run_embed_wireI {n : ℕ} (i : Fin n) (gs : List (Matrix Bool Bool ℂ)) (x : Reg n)
    (c : Bool → ℂ) (ψ : Reg n → ℂ) (hψ : WireState i x c ψ) :
    ∀ y : Reg n,
      Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedRegI i U)).map Step.gate) ψ y
        = (boolGateProd gs *ᵥ c) (y i) * agreesOutsideI i x y := by
  induction gs generalizing c ψ with
  | nil =>
      intro y
      simp only [List.map_nil]
      have hrun : Run (1 : Matrix (Reg n) (Reg n) ℂ) ([] : Circuit (Reg n)) ψ = ψ := rfl
      rw [hrun, boolGateProd, Matrix.one_mulVec]
      exact hψ y
  | cons U gs ih =>
      intro y
      simp only [List.map_cons, Run]
      have hψ' : WireState i x (U *ᵥ c) (ApplyGate (embedRegI i U) ψ) :=
        embedRegI_applyGate i U x c ψ hψ
      have hih := ih (U *ᵥ c) (ApplyGate (embedRegI i U) ψ) hψ' y
      rw [hih, mulVec_boolGateProd_cons]

/-- A register agreeing with `x` outside wire `i` and having true bit at `i` is uniquely
`setBitI i x true`. -/
theorem agreesOutsideI_accepting_unique {n : ℕ} (i : Fin n) (x y : Reg n)
    (hy : y i = true) (hag : AgreesOutsideI i x y) : y = setBitI i x true := by
  funext j
  by_cases hj : j = i
  · rw [hj]
    exact hy.trans (setBitI_bit i x true).symm
  · rw [setBitI, if_neg hj]
    exact hag j hj

/-- The probability of true at wire `i` after gates embedded there equals the true-component
squared norm of their Boolean product applied to the initial bit. -/
theorem acceptProb_embedI {n : ℕ} (i : Fin n) (gs : List (Matrix Bool Bool ℂ)) (x : Reg n) :
    AcceptProbAt i (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        ((gs.map (fun U => embedRegI i U)).map Step.gate) (Ket x))
      = ‖(boolGateProd gs *ᵥ (fun c => if c = x i then (1 : ℂ) else 0)) true‖ ^ 2 := by
  classical
  set c₀ : Bool → ℂ := fun c => if c = x i then (1 : ℂ) else 0 with hc₀
  have hket : WireState i x c₀ (Ket x) := by
    rw [hc₀]
    exact ket_wireI i x
  have hrun := run_embed_wireI i gs x c₀ (Ket x) hket
  set A : ℂ := (boolGateProd gs *ᵥ c₀) true with hA
  have hag_xTrue : AgreesOutsideI i x (setBitI i x true) := by
    intro j hj
    exact setBitI_of_ne i x true hj
  have hxTrue_mem : setBitI i x true ∈
      (Finset.univ.filter (fun y : Reg n => y i = true)) := by
    simp [setBitI]
  have hag_xTrue1 : agreesOutsideI i x (setBitI i x true) = 1 := by
    rw [agreesOutsideI, if_pos hag_xTrue]
  have hzero : ∀ y ∈ (Finset.univ.filter (fun y : Reg n => y i = true)),
      y ≠ setBitI i x true → agreesOutsideI i x y = 0 := by
    intro y hy hne
    have hy' : y i = true := (Finset.mem_filter.mp hy).2
    by_cases hag : AgreesOutsideI i x y
    · exact absurd (agreesOutsideI_accepting_unique i x y hy' hag) hne
    · rw [agreesOutsideI, if_neg hag]
  have hsum : (∑ y ∈ (Finset.univ.filter (fun y : Reg n => y i = true)),
        BornProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedRegI i U)).map Step.gate) (Ket x)) y)
      = BornProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedRegI i U)).map Step.gate) (Ket x)) (setBitI i x true) := by
    apply Finset.sum_eq_single_of_mem (setBitI i x true) hxTrue_mem
    intro y hy hne
    have hag0 : agreesOutsideI i x y = 0 := hzero y hy hne
    have h1 : Run (1 : Matrix (Reg n) (Reg n) ℂ)
          ((gs.map (fun U => embedRegI i U)).map Step.gate) (Ket x) y = 0 := by
      have h1' := hrun y
      rw [h1', hag0]
      simp
    rw [BornProb, h1]
    simp
  rw [AcceptProbAt, MeasureProb, hsum]
  have h2 : Run (1 : Matrix (Reg n) (Reg n) ℂ)
        ((gs.map (fun U => embedRegI i U)).map Step.gate) (Ket x) (setBitI i x true) = A := by
    have h1' := hrun (setBitI i x true)
    rw [h1']
    rw [setBitI_bit]
    rw [hag_xTrue1]
    simp [hA]
  rw [BornProb, h2]

/-- For `n ≤ w`, the target-cell machine's accepting mass after `tgt+k+2` steps equals the
corresponding embedded circuit's true probability at the target wire. -/
theorem headStay_cell_acceptProb_multi {n k tgt w : ℕ}
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (htgt : tgt < n)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (hw : n ≤ w) (x : Reg n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : CellState n k tgt)),
      BornProb ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (tgt + k + 2)
        *ᵥ Ket (initWindowCfg (t := w) (cellLocalQTM V htgt hV) n x)) c)
      = AcceptProbAt ⟨tgt, htgt⟩
          ((Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (((List.ofFn (V ⟨tgt, htgt⟩)).map
                  (fun U => embedRegI ⟨tgt, htgt⟩ U)).map Step.gate))
            (Ket x)) := by
  calc
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : CellState n k tgt)),
        BornProb ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (tgt + k + 2)
          *ᵥ Ket (initWindowCfg (t := w) (cellLocalQTM V htgt hV) n x)) c)
      = ‖(gateSeqProd (V ⟨tgt, htgt⟩) k (by omega) *ᵥ
          (fun c => if c = x ⟨tgt, htgt⟩ then (1 : ℂ) else 0)) true‖ ^ 2 :=
        headStay_cell_acceptMass_multi V htgt hV hw x
    _ = ‖(boolGateProd (List.ofFn (V ⟨tgt, htgt⟩)) *ᵥ
          (fun c => if c = x ⟨tgt, htgt⟩ then (1 : ℂ) else 0)) true‖ ^ 2 := by
        rw [boolGateProd_ofFn k (V ⟨tgt, htgt⟩)]
    _ = AcceptProbAt ⟨tgt, htgt⟩
          ((Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (((List.ofFn (V ⟨tgt, htgt⟩)).map
                  (fun U => embedRegI ⟨tgt, htgt⟩ U)).map Step.gate))
            (Ket x)) := by
        have h := (acceptProb_embedI ⟨tgt, htgt⟩ (List.ofFn (V ⟨tgt, htgt⟩)) x).symm
        exact h

/-- The true probability at wire zero is the standard acceptance probability. -/
theorem acceptProbAt_zero {n : ℕ} (hn : 0 < n) (ψ : QState (Reg n)) :
    AcceptProbAt ⟨0, hn⟩ ψ = AcceptProb ψ hn := rfl

/-- The all-cell machine starts serving cell zero at gate stage zero. -/
theorem allCellNext_start {n k : ℕ} (hn : 0 < n) (a : Bool) :
    allCellNext hn (.start : AllCellState n k) a = .serve ⟨0, hn⟩ ⟨0, by omega⟩ := rfl

/-- A serve state advances its gate stage, moves to the next cell after its last gate, or
selects acceptance or rejection at the final cell. -/
theorem allCellNext_serve {n k : ℕ} (hn : 0 < n) (i : Fin n) (j : Fin (k + 1)) (a : Bool) :
    allCellNext hn (.serve i j) a =
      if h : j.val < k then .serve i ⟨j.val + 1, by omega⟩
      else if hi : i.val + 1 < n then .serve ⟨i.val + 1, by omega⟩ ⟨0, by omega⟩
      else (if a then .acc else .rej) := rfl

/-- The all-cell accepting state transitions to the second measurement state. -/
theorem allCellNext_acc {n k : ℕ} (hn : 0 < n) (a : Bool) :
    allCellNext hn (.acc : AllCellState n k) a = .meas2 := rfl

/-- The all-cell rejecting state transitions to restart. -/
theorem allCellNext_rej {n k : ℕ} (hn : 0 < n) (a : Bool) :
    allCellNext hn (.rej : AllCellState n k) a = .restart := rfl

/-- The all-cell second measurement state selects acceptance or rejection from the current bit. -/
theorem allCellNext_meas2 {n k : ℕ} (hn : 0 < n) (a : Bool) :
    allCellNext hn (.meas2 : AllCellState n k) a = if a then .acc else .rej := rfl

/-- The all-cell restart state transitions to the start state. -/
theorem allCellNext_restart {n k : ℕ} (hn : 0 < n) (a : Bool) :
    allCellNext hn (.restart : AllCellState n k) a = .start := rfl

/-- The all-cell start state moves the head right. -/
theorem allCellMove_start {n k : ℕ} : allCellMove (.start : AllCellState n k) = .right := rfl

/-- A serve state stays during its gate sequence, moves right between cells, and stays after the
final cell. -/
theorem allCellMove_serve {n k : ℕ} (i : Fin n) (j : Fin (k + 1)) :
    allCellMove (.serve i j) =
      if j.val < k then .stay else if i.val + 1 < n then .right else .stay := rfl

/-- No all-cell machine state moves the head left. -/
theorem allCellMove_ne_left {n k : ℕ} (q : AllCellState n k) :
    allCellMove q ≠ QtmMove.left := by
  cases q with
  | start => simp [allCellMove]
  | serve i j =>
    by_cases h : j.val < k
    · simp [allCellMove, h]
    · by_cases h2 : i.val + 1 < n
      · simp [allCellMove, h, h2]
      · simp [allCellMove, h, h2]
  | acc => simp [allCellMove]
  | rej => simp [allCellMove]
  | meas2 => simp [allCellMove]
  | restart => simp [allCellMove]

/-- Every left-moving transition amplitude of the all-cell machine is zero. -/
theorem allCellStep_left_zero {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (q : AllCellState n k) (a : Bool)
    (q' : AllCellState n k) (b : Bool) :
    allCellStep hn V q a QtmMove.left q' b = 0 := by
  simp [allCellStep, allCellMove_ne_left q, Ne.symm (allCellMove_ne_left q)]

/-- The all-cell start state preserves the tape symbol deterministically. -/
theorem allCellAmp_start_row {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (a b : Bool) : allCellAmp V (.start : AllCellState n k) a b = (if b = a then 1 else 0) := rfl

/-- Below the final stage, a serve state's amplitudes are the entries of its cell's designated
unitary gate. -/
theorem allCellAmp_serve_gate_row {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val < k) (a b : Bool) :
    allCellAmp V (.serve i j) a b = V i ⟨j.val, hj⟩ b a := by
  simp [allCellAmp, hj]

/-- At the final stage of a nonfinal cell, a serve state preserves the tape symbol
deterministically. -/
theorem allCellAmp_serve_move_row {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 < n) (a b : Bool) :
    allCellAmp V (.serve i j) a b = (if b = a then 1 else 0) := by
  simp [allCellAmp, hj, hi]

/-- At the final stage of the final cell, a serve state flips the tape symbol deterministically. -/
theorem allCellAmp_serve_measure_row {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 = n) (a b : Bool) :
    allCellAmp V (.serve i j) a b = (if b = !a then 1 else 0) := by
  simp [allCellAmp, hj, hi]

/-- The accepting, rejecting, second measurement, and restart states preserve the tape symbol
deterministically. -/
theorem allCellAmp_det_row {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (q : AllCellState n k) (a b : Bool)
    (hq : q = .acc ∨ q = .rej ∨ q = .meas2 ∨ q = .restart) :
    allCellAmp V q a b = (if b = a then 1 else 0) := by
  rcases hq with hq | hq | hq | hq <;> subst hq <;> rfl

/-- With unitary gate data, each all-cell amplitude row has squared norm one. -/
theorem allCellAmp_norm {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (q : AllCellState n k) (a : Bool) :
    ∑ b : Bool, ‖allCellAmp V q a b‖ ^ 2 = 1 := by
  cases q with
  | start => cases a <;> simp [allCellAmp]
  | serve i j =>
    by_cases hj : j.val < k
    · simp only [allCellAmp_serve_gate_row V i j hj]
      exact cellGateCol_norm V hV i ⟨j.val, hj⟩ a
    · by_cases hi : i.val + 1 < n
      · simp only [allCellAmp_serve_move_row V i j (by omega) hi]
        cases a <;> simp
      · simp only [allCellAmp_serve_measure_row V i j (by omega) (by omega)]
        cases a <;> simp
  | acc => cases a <;> simp [allCellAmp]
  | rej => cases a <;> simp [allCellAmp]
  | meas2 => cases a <;> simp [allCellAmp]
  | restart => cases a <;> simp [allCellAmp]

/-- Deterministic identity rows for distinct input bits are orthogonal. -/
theorem allCellAmp_id_orth (a₁ a₂ : Bool) (hne : a₁ ≠ a₂) :
    ∑ b : Bool, star ((if b = a₁ then (1 : ℂ) else 0)) * ((if b = a₂ then (1 : ℂ) else 0)) = 0 := by
  cases a₁ <;> cases a₂ <;> simp_all

/-- For the same input bit, the deterministic flip row is orthogonal to the identity row. -/
theorem allCellAmp_flip_id_orth (a : Bool) :
    ∑ b : Bool, star ((if b = !a then (1 : ℂ) else 0)) * ((if b = a then (1 : ℂ) else 0)) = 0 := by
  cases a <;> simp

/-- Deterministic flip rows for distinct input bits are orthogonal. -/
theorem allCellAmp_flip_orth (a₁ a₂ : Bool) (hne : a₁ ≠ a₂) :
    ∑ b : Bool, star ((if b = !a₁ then (1 : ℂ) else 0)) * ((if b = !a₂ then (1 : ℂ) else 0)) = 0 := by
  cases a₁ <;> cases a₂ <;> simp_all

/-- With unitary gate data, distinct input symbols in the same all-cell state have orthogonal
amplitude rows. -/
theorem allCellAmp_same_orth {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (q : AllCellState n k) (a₁ a₂ : Bool) (hne : a₁ ≠ a₂) :
    ∑ b : Bool, star (allCellAmp V q a₁ b) * allCellAmp V q a₂ b = 0 := by
  cases q with
  | start =>
    simp only [allCellAmp_start_row]
    exact allCellAmp_id_orth a₁ a₂ hne
  | serve i j =>
    by_cases hj : j.val < k
    · simp only [allCellAmp_serve_gate_row V i j hj]
      exact cellGateCol_orth V hV i ⟨j.val, hj⟩ a₁ a₂ hne
    · by_cases hi : i.val + 1 < n
      · simp only [allCellAmp_serve_move_row V i j (by omega) hi]
        exact allCellAmp_id_orth a₁ a₂ hne
      · simp only [allCellAmp_serve_measure_row V i j (by omega) (by omega)]
        exact allCellAmp_flip_orth a₁ a₂ hne
  | acc =>
    simp only [allCellAmp_det_row V (.acc : AllCellState n k) a₁ _ (Or.inl rfl)]
    exact allCellAmp_id_orth a₁ a₂ hne
  | rej =>
    simp only [allCellAmp_det_row V (.rej : AllCellState n k) a₁ _ (Or.inr (Or.inl rfl))]
    exact allCellAmp_id_orth a₁ a₂ hne
  | meas2 =>
    simp only [allCellAmp_det_row V (.meas2 : AllCellState n k) a₁ _ (Or.inr (Or.inr (Or.inl rfl)))]
    exact allCellAmp_id_orth a₁ a₂ hne
  | restart =>
    simp only [allCellAmp_det_row V (.restart : AllCellState n k) a₁ _ (Or.inr (Or.inr (Or.inr rfl)))]
    exact allCellAmp_id_orth a₁ a₂ hne

/-- Equal all-cell next states require equal source states, except for the two orders of a final
measurement serve state paired with `meas2` on equal input bits. -/
theorem allCellNext_view {n k : ℕ} (hn : 0 < n) (q₁ q₂ : AllCellState n k) (a₁ a₂ : Bool)
    (h : allCellNext hn q₁ a₁ = allCellNext hn q₂ a₂) :
    (q₁ = q₂) ∨
    (q₁ = .serve ⟨n - 1, by omega⟩ ⟨k, by omega⟩ ∧ q₂ = .meas2 ∧ a₁ = a₂) ∨
    (q₁ = .meas2 ∧ q₂ = .serve ⟨n - 1, by omega⟩ ⟨k, by omega⟩ ∧ a₁ = a₂) := by
  have hmeas : ∀ (i : Fin n) (j : Fin (k + 1)), j.val = k ∧ i.val + 1 = n →
      i = ⟨n - 1, by omega⟩ ∧ j = ⟨k, by omega⟩ := by
    intro i j hj
    have hj1 := hj.1
    have hj2 := hj.2
    refine ⟨Fin.ext (by simp only [Fin.val_mk]; omega), Fin.ext (by simp only [Fin.val_mk]; omega)⟩
  have hmeas1 : ∀ (i : Fin n) (j : Fin (k + 1)), j.val = k ∧ i.val + 1 = n →
      (.serve i j : AllCellState n k) = .serve ⟨n - 1, by omega⟩ ⟨k, by omega⟩ := by
    intro i j hj
    obtain ⟨h1, h2⟩ := hmeas i j hj
    cases h1
    cases h2
    rfl
  cases q₁ with
  | start =>
    cases q₂ with
    | start => exact Or.inl rfl
    | serve i j =>
      rw [allCellNext_serve hn i j a₂] at h
      by_cases hj : j.val < k
      · simp only [dif_pos hj] at h
        injection h with _ h2
        have h2v := congrArg Fin.val h2
        simp only [Fin.val_mk] at h2v
        omega
      · by_cases hi : i.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          injection h with h1 _
          have h1v := congrArg Fin.val h1
          simp only [Fin.val_mk] at h1v
          omega
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₂ <;> cases h
    | acc =>
      rw [allCellNext_acc hn a₂] at h
      cases h
    | rej =>
      rw [allCellNext_rej hn a₂] at h
      cases h
    | meas2 =>
      rw [allCellNext_meas2 hn a₂] at h
      cases a₂ <;> cases h
    | restart =>
      rw [allCellNext_restart hn a₂] at h
      cases h
  | serve i₁ j₁ =>
    cases q₂ with
    | start =>
      rw [allCellNext_serve hn i₁ j₁ a₁] at h
      by_cases hj : j₁.val < k
      · simp only [dif_pos hj] at h
        injection h with _ h2
        have h2v := congrArg Fin.val h2
        simp only [Fin.val_mk] at h2v
        omega
      · by_cases hi : i₁.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          injection h with h1 _
          have h1v := congrArg Fin.val h1
          simp only [Fin.val_mk] at h1v
          omega
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₁ <;> cases h
    | serve i₂ j₂ =>
      by_cases hj1 : j₁.val < k
      · by_cases hj2 : j₂.val < k
        · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
          simp only [dif_pos hj1, dif_pos hj2] at h
          injection h with h1 h2
          have h1v := congrArg Fin.val h1
          have h2v := congrArg Fin.val h2
          simp only [Fin.val_mk] at h1v h2v
          have hieq : i₁ = i₂ := Fin.ext h1v
          have hjeq : j₁ = j₂ := Fin.ext (by omega)
          subst hieq
          subst hjeq
          exact Or.inl rfl
        · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
          simp only [dif_pos hj1, dif_neg hj2] at h
          by_cases hi2 : i₂.val + 1 < n
          · simp only [dif_pos hi2] at h
            injection h with _ h2
            have h2v := congrArg Fin.val h2
            simp only [Fin.val_mk] at h2v
            omega
          · simp only [dif_neg hi2] at h
            cases a₂ <;> cases h
      · by_cases hj2 : j₂.val < k
        · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
          simp only [dif_neg hj1, dif_pos hj2] at h
          by_cases hi1 : i₁.val + 1 < n
          · simp only [dif_pos hi1] at h
            injection h with _ h2
            have h2v := congrArg Fin.val h2
            simp only [Fin.val_mk] at h2v
            omega
          · simp only [dif_neg hi1] at h
            cases a₁ <;> cases h
        · by_cases hi1 : i₁.val + 1 < n
          · by_cases hi2 : i₂.val + 1 < n
            · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
              simp only [dif_neg hj1, dif_neg hj2, dif_pos hi1, dif_pos hi2] at h
              injection h with h1 _
              have h1v := congrArg Fin.val h1
              simp only [Fin.val_mk] at h1v
              have hieq : i₁ = i₂ := Fin.ext (by omega)
              have hjeq : j₁ = j₂ := Fin.ext (by omega)
              subst hieq
              subst hjeq
              exact Or.inl rfl
            · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
              simp only [dif_neg hj1, dif_neg hj2, dif_pos hi1, dif_neg hi2] at h
              cases a₂ <;> cases h
          · by_cases hi2 : i₂.val + 1 < n
            · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
              simp only [dif_neg hj1, dif_neg hj2, dif_neg hi1, dif_pos hi2] at h
              cases a₁ <;> cases a₂ <;> cases h
            · rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_serve hn i₂ j₂ a₂] at h
              simp only [dif_neg hj1, dif_neg hj2, dif_neg hi1, dif_neg hi2] at h
              by_cases ha : a₁ = a₂
              · have hieq : i₁ = i₂ := Fin.ext (by omega)
                have hjeq : j₁ = j₂ := Fin.ext (by omega)
                subst hieq
                subst hjeq
                exact Or.inl rfl
              · cases a₁ <;> cases a₂
                · simp at ha
                · cases h
                · cases h
                · simp at ha
    | acc =>
      rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_acc hn a₂] at h
      by_cases hj : j₁.val < k
      · simp only [dif_pos hj] at h
        cases h
      · by_cases hi : i₁.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₁ <;> cases h
    | rej =>
      rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_rej hn a₂] at h
      by_cases hj : j₁.val < k
      · simp only [dif_pos hj] at h
        cases h
      · by_cases hi : i₁.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₁ <;> cases h
    | meas2 =>
      rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_meas2 hn a₂] at h
      by_cases hj : j₁.val < k
      · simp only [dif_pos hj] at h
        cases a₂ <;> cases h
      · by_cases hi : i₁.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases a₂ <;> cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          by_cases ha : a₁ = a₂
          · exact Or.inr (Or.inl ⟨hmeas1 i₁ j₁ ⟨by omega, by omega⟩, rfl, ha⟩)
          · cases a₁ <;> cases a₂
            · simp at ha
            · cases h
            · cases h
            · simp at ha
    | restart =>
      rw [allCellNext_serve hn i₁ j₁ a₁, allCellNext_restart hn a₂] at h
      by_cases hj : j₁.val < k
      · simp only [dif_pos hj] at h
        cases h
      · by_cases hi : i₁.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₁ <;> cases h
  | acc =>
    cases q₂ with
    | start =>
      rw [allCellNext_acc hn a₁, allCellNext_start hn a₂] at h
      cases h
    | serve i j =>
      rw [allCellNext_acc hn a₁, allCellNext_serve hn i j a₂] at h
      by_cases hj : j.val < k
      · simp only [dif_pos hj] at h
        cases h
      · by_cases hi : i.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₂ <;> cases h
    | acc => exact Or.inl rfl
    | rej =>
      rw [allCellNext_acc hn a₁, allCellNext_rej hn a₂] at h
      cases h
    | meas2 =>
      rw [allCellNext_acc hn a₁, allCellNext_meas2 hn a₂] at h
      cases a₂ <;> cases h
    | restart =>
      rw [allCellNext_acc hn a₁, allCellNext_restart hn a₂] at h
      cases h
  | rej =>
    cases q₂ with
    | start =>
      rw [allCellNext_rej hn a₁, allCellNext_start hn a₂] at h
      cases h
    | serve i j =>
      rw [allCellNext_rej hn a₁, allCellNext_serve hn i j a₂] at h
      by_cases hj : j.val < k
      · simp only [dif_pos hj] at h
        cases h
      · by_cases hi : i.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₂ <;> cases h
    | acc =>
      rw [allCellNext_rej hn a₁, allCellNext_acc hn a₂] at h
      cases h
    | rej => exact Or.inl rfl
    | meas2 =>
      rw [allCellNext_rej hn a₁, allCellNext_meas2 hn a₂] at h
      cases a₂ <;> cases h
    | restart =>
      rw [allCellNext_rej hn a₁, allCellNext_restart hn a₂] at h
      cases h
  | meas2 =>
    cases q₂ with
    | start =>
      rw [allCellNext_meas2 hn a₁, allCellNext_start hn a₂] at h
      cases a₁ <;> cases h
    | serve i j =>
      rw [allCellNext_meas2 hn a₁, allCellNext_serve hn i j a₂] at h
      by_cases hj : j.val < k
      · simp only [dif_pos hj] at h
        cases a₁ <;> cases h
      · by_cases hi : i.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases a₁ <;> cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          by_cases ha : a₁ = a₂
          · exact Or.inr (Or.inr ⟨rfl, hmeas1 i j ⟨by omega, by omega⟩, ha⟩)
          · cases a₁ <;> cases a₂
            · simp at ha
            · cases h
            · cases h
            · simp at ha
    | acc =>
      rw [allCellNext_meas2 hn a₁, allCellNext_acc hn a₂] at h
      cases a₁ <;> cases h
    | rej =>
      rw [allCellNext_meas2 hn a₁, allCellNext_rej hn a₂] at h
      cases a₁ <;> cases h
    | meas2 => exact Or.inl rfl
    | restart =>
      rw [allCellNext_meas2 hn a₁, allCellNext_restart hn a₂] at h
      cases a₁ <;> cases h
  | restart =>
    cases q₂ with
    | start =>
      rw [allCellNext_restart hn a₁, allCellNext_start hn a₂] at h
      cases h
    | serve i j =>
      rw [allCellNext_restart hn a₁, allCellNext_serve hn i j a₂] at h
      by_cases hj : j.val < k
      · simp only [dif_pos hj] at h
        cases h
      · by_cases hi : i.val + 1 < n
        · simp only [dif_neg hj, dif_pos hi] at h
          cases h
        · simp only [dif_neg hj, dif_neg hi] at h
          cases a₂ <;> cases h
    | acc =>
      rw [allCellNext_restart hn a₁, allCellNext_acc hn a₂] at h
      cases h
    | rej =>
      rw [allCellNext_restart hn a₁, allCellNext_rej hn a₂] at h
      cases h
    | meas2 =>
      rw [allCellNext_restart hn a₁, allCellNext_meas2 hn a₂] at h
      cases a₂ <;> cases h
    | restart => exact Or.inl rfl

/-- For the same input bit, the deterministic identity row is orthogonal to the flip row. -/
theorem allCellAmp_id_flip_orth (a : Bool) :
    ∑ b : Bool, star ((if b = a then (1 : ℂ) else 0)) * ((if b = !a then (1 : ℂ) else 0)) = 0 := by
  cases a <;> simp

/-- A serve state at the final gate stage of the final input cell. -/
def IsMeasure {n k : ℕ} (q : AllCellState n k) : Prop :=
  ∃ (i : Fin n) (j : Fin (k + 1)), j.val = k ∧ i.val + 1 = n ∧ q = .serve i j

/-- An all-cell measurement serve state flips the tape symbol deterministically. -/
theorem allCellAmp_measure_row {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (q : AllCellState n k) (a b : Bool) (hq : IsMeasure q) :
    allCellAmp V q a b = (if b = !a then 1 else 0) := by
  obtain ⟨i, j, hj, hi, rfl⟩ := hq
  simp [allCellAmp, hj, hi]

/-- The final measurement serve state's amplitude row is orthogonal to the `meas2` row on the
same input bit. -/
theorem allCellAmp_measure_meas2_orth {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hn : 0 < n) (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 = n) (a : Bool) :
    ∑ b : Bool, star (allCellAmp V (.serve i j) a b) * allCellAmp V (.meas2) a b = 0 := by
  simp [allCellAmp, hj, hi]

/-- The `meas2` amplitude row is orthogonal to the final measurement serve-state row on the same
input bit. -/
theorem allCellAmp_meas2_measure_orth {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hn : 0 < n) (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 = n) (a : Bool) :
    ∑ b : Bool, star (allCellAmp V (.meas2) a b) * allCellAmp V (.serve i j) a b = 0 := by
  simp [allCellAmp, hj, hi]

/-- With nonempty input and unitary gate data, distinct state-symbol inputs with the same next
state have orthogonal all-cell amplitude rows. -/
theorem allCellAmp_orth {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hn : 0 < n) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (q₁ q₂ : AllCellState n k) (a₁ a₂ : Bool)
    (hne : (q₁, a₁) ≠ (q₂, a₂))
    (hnxt : allCellNext hn q₁ a₁ = allCellNext hn q₂ a₂) :
    ∑ b : Bool, star (allCellAmp V q₁ a₁ b) * allCellAmp V q₂ a₂ b = 0 := by
  rcases allCellNext_view hn q₁ q₂ a₁ a₂ hnxt with h | h | h
  · subst h
    have ha : a₁ ≠ a₂ := by
      intro ha
      apply hne
      exact Prod.ext rfl ha
    exact allCellAmp_same_orth V hV q₁ a₁ a₂ ha
  · obtain ⟨h1, h2, h3⟩ := h
    rw [h2]
    have hq : IsMeasure q₁ :=
      ⟨⟨n - 1, by omega⟩, ⟨k, by omega⟩, rfl, by simp only [Fin.val_mk] <;> omega, h1⟩
    simp only [allCellAmp_measure_row V q₁ a₁ _ hq,
      allCellAmp_det_row V (.meas2 : AllCellState n k) a₂ _ (Or.inr (Or.inr (Or.inl rfl)))]
    rw [h3]
    exact allCellAmp_flip_id_orth a₂
  · obtain ⟨h1, h2, h3⟩ := h
    rw [h1]
    have hq : IsMeasure q₂ :=
      ⟨⟨n - 1, by omega⟩, ⟨k, by omega⟩, rfl, by simp only [Fin.val_mk] <;> omega, h2⟩
    simp only [allCellAmp_det_row V (.meas2 : AllCellState n k) a₁ _ (Or.inr (Or.inr (Or.inl rfl))),
      allCellAmp_measure_row V q₂ a₂ _ hq]
    rw [h3]
    exact allCellAmp_id_flip_orth a₂

/-- The accepting, rejecting, second measurement, and restart states all leave the head
stationary. -/
theorem allCellMove_det_stay {n k : ℕ} (q : AllCellState n k)
    (hq : q = .acc ∨ q = .rej ∨ q = .meas2 ∨ q = .restart) :
    allCellMove q = QtmMove.stay := by
  rcases hq with hq | hq | hq | hq <;> subst hq <;> rfl

/-- The final gate stage of the final cell leaves the head stationary. -/
theorem allCellMove_measure_stay {n k : ℕ} (hn : 0 < n) (i : Fin n) (j : Fin (k + 1))
    (hj : j.val = k) (hi : i.val + 1 = n) :
    allCellMove (.serve i j) = QtmMove.stay := by
  simp [allCellMove, hj, hi]

/-- A right-moving source state and a stationary source state have different all-cell next
states. -/
theorem allCellNext_right_ne_stay {n k : ℕ} (hn : 0 < n)
    (q₁ : AllCellState n k) (a₁ : Bool) (q₂ : AllCellState n k) (a₂ : Bool)
    (hr : allCellMove q₁ = QtmMove.right) (hs : allCellMove q₂ = QtmMove.stay) :
    allCellNext hn q₁ a₁ ≠ allCellNext hn q₂ a₂ := by
  intro hcon
  rcases allCellNext_view hn q₁ q₂ a₁ a₂ hcon with h | h | h
  · subst h
    rw [hr] at hs
    cases hs
  · obtain ⟨h1, h2, h3⟩ := h
    have hq : IsMeasure q₁ :=
      ⟨⟨n - 1, by omega⟩, ⟨k, by omega⟩, rfl, by simp only [Fin.val_mk] <;> omega, h1⟩
    have hstay : allCellMove q₁ = QtmMove.stay := by
      obtain ⟨i, j, hj, hi, rfl⟩ := hq
      simp [allCellMove, hj, hi]
    rw [hstay] at hr
    cases hr
  · obtain ⟨h1, h2, h3⟩ := h
    subst h1
    have hstay : allCellMove (.meas2 : AllCellState n k) = QtmMove.stay := rfl
    rw [hstay] at hr
    cases hr

/-- The local quantum machine that serves every input cell in order with its given unitary
sequence and then records the last cell's Boolean result. -/
def allCellLocalQTM {n k : ℕ} (hn : 0 < n) (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTM (AllCellState n k) Bool where
  blank := false
  start := .start
  step := allCellStep hn V
  wf_norm := by
    intro q a
    classical
    rw [Finset.sum_eq_single_of_mem (allCellNext hn q a) (Finset.mem_univ _)]
    · simp only [allCellStep, eq_self, and_true]
      calc (∑ x : Bool, ∑ d : QtmMove,
            ‖(if d = allCellMove q then allCellAmp V q a x else 0)‖ ^ 2)
          = ∑ x : Bool, ‖allCellAmp V q a x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [sum_norm_move]
        _ = 1 := allCellAmp_norm V hV q a
    · intro q' _ hne
      simp [allCellStep, hne]
  wf_sameCell := by
    intro q₁ a₁ q₂ a₂ hne
    classical
    rw [Finset.sum_eq_single_of_mem (allCellNext hn q₁ a₁) (Finset.mem_univ _)]
    · by_cases hnxt : allCellNext hn q₁ a₁ = allCellNext hn q₂ a₂
      · simp only [allCellStep, eq_self, and_true, hnxt]
        have hsum : (∑ x : Bool, ∑ d : QtmMove,
              star (if d = allCellMove q₁ then allCellAmp V q₁ a₁ x else 0) *
                (if d = allCellMove q₂ then allCellAmp V q₂ a₂ x else 0))
            = ∑ x : Bool, (if allCellMove q₁ = allCellMove q₂
                then star (allCellAmp V q₁ a₁ x) * allCellAmp V q₂ a₂ x else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sum_move_mul_star]
        rw [hsum]
        by_cases hmv : allCellMove q₁ = allCellMove q₂
        · simp only [if_pos hmv]
          exact allCellAmp_orth V hn hV q₁ q₂ a₁ a₂ hne hnxt
        · rw [Finset.sum_eq_zero]
          intro x _
          rw [if_neg hmv]
      · rw [Finset.sum_eq_zero]
        intro x _
        rw [Finset.sum_eq_zero]
        intro d _
        simp only [allCellStep, and_true]
        by_cases h1 : (d = allCellMove q₁)
        · rw [if_pos h1]
          by_cases h2 : (d = allCellMove q₂ ∧ allCellNext hn q₁ a₁ = allCellNext hn q₂ a₂)
          · rw [if_pos h2]
            exact (hnxt h2.2).elim
          · rw [if_neg h2]
            simp
        · rw [if_neg h1]
          simp
    · intro q' _ hne'
      simp [allCellStep, hne']
  wf_rightStay := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    by_cases h1 : allCellMove q₁ = QtmMove.right
    · by_cases h2 : allCellMove q₂ = QtmMove.stay
      · have hne := allCellNext_right_ne_stay hn q₁ a₁ q₂ a₂ h1 h2
        by_cases hq : q' = allCellNext hn q₁ a₁
        · have hstep1 : allCellStep hn V q₁ a₁ QtmMove.right q' c = allCellAmp V q₁ a₁ c := by
            simp [allCellStep, h1, hq]
          have hstep2 : allCellStep hn V q₂ a₂ QtmMove.stay q' d = 0 := by
            simp [allCellStep, h2, hne, hq]
          rw [hstep1, hstep2]
          simp
        · have hstep1 : allCellStep hn V q₁ a₁ QtmMove.right q' c = 0 := by
            simp [allCellStep, h1, hq]
          rw [hstep1]
          simp
      · have hz : allCellStep hn V q₂ a₂ QtmMove.stay q' d = 0 := by
          simp [allCellStep, h2, Ne.symm h2]
        rw [hz]
        simp
    · have hz : allCellStep hn V q₁ a₁ QtmMove.right q' c = 0 := by
        simp [allCellStep, h1, Ne.symm h1]
      rw [hz]
      simp
  wf_stayLeft := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    rw [allCellStep_left_zero hn V q₂ a₂ q' d]
    simp
  wf_rightLeft := by
    intro q₁ a₁ q₂ a₂ c d
    rw [Finset.sum_eq_zero]
    intro q' _
    rw [allCellStep_left_zero hn V q₂ a₂ q' d]
    simp

/-- For nonempty input and unitary gate data, the all-cell machine satisfies the five local
conditions. -/
theorem allCellLocalQTM_five {n k : ℕ} (hn : 0 < n) (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) :
    LocalQTMFiveConditions (allCellLocalQTM hn V hV) := by
  exact ⟨(allCellLocalQTM hn V hV).wf_norm, (allCellLocalQTM hn V hV).wf_sameCell,
    (allCellLocalQTM hn V hV).wf_rightStay, (allCellLocalQTM hn V hV).wf_stayLeft,
    (allCellLocalQTM hn V hV).wf_rightLeft⟩

/-- An all-cell transition has its prescribed local amplitude exactly when the head move, next
state, and single-cell tape update are valid. -/
theorem allCellLocalQTM_windowStep {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (AllCellState n k) Bool) :
    (windowStep (t := w) (allCellLocalQTM hn V hV) tgt') src =
      if moveCell (allCellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
          (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j)
      then allCellAmp V src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  classical
  simp only [windowStep, Matrix.of_apply, allCellLocalQTM, allCellStep]
  rw [Finset.sum_eq_single_of_mem (allCellMove src.state) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (allCellNext hn src.state (src.tape src.head))
      (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem (tgt'.tape src.head) (Finset.mem_univ _)]
      · by_cases h : (moveCell (allCellMove src.state) src.head = some tgt'.head ∧
            tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
            (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j))
        · simp only [if_pos h, and_self, eq_self, ↓reduceIte]
        · simp only [if_neg h]
      · intro b _ hb
        by_cases hcon : (moveCell (allCellMove src.state) src.head = some tgt'.head ∧
            tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
            (∀ j, tgt'.tape j = if j = src.head then b else src.tape j))
        · rw [if_pos hcon]
          have hlt : tgt'.tape src.head = b := by
            have hstep := hcon.2.2 src.head
            simpa using! hstep
          exact (hb hlt.symm).elim
        · rw [if_neg hcon]
    · intro q' _ hq
      apply Finset.sum_eq_zero
      intro b _
      by_cases hcon : (moveCell (allCellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = q' ∧
          (∀ j, tgt'.tape j = if j = src.head then b else src.tape j))
      · rw [if_pos hcon]
        rw [if_neg (fun hh => hq hh.2)]
      · rw [if_neg hcon]
  · intro d _ hd
    apply Finset.sum_eq_zero
    intro q' _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hcon : (moveCell d src.head = some tgt'.head ∧ tgt'.state = q' ∧
        (∀ j, tgt'.tape j = if j = src.head then b else src.tape j))
    · rw [if_pos hcon]
      rw [if_neg (fun hh => hd hh.1)]
    · rw [if_neg hcon]

/-- An all-cell transition is characterized by its head move, next state, and equality of tape
symbols away from the source head. -/
theorem allCellLocalQTM_windowStep_norm {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (AllCellState n k) Bool) :
    (windowStep (t := w) (allCellLocalQTM hn V hV) tgt') src =
      if moveCell (allCellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
          (∀ j, j ≠ src.head → tgt'.tape j = src.tape j)
      then allCellAmp V src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  have hiff : (moveCell (allCellMove src.state) src.head = some tgt'.head ∧
        tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
        (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j))
      ↔ (moveCell (allCellMove src.state) src.head = some tgt'.head ∧
        tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
        (∀ j, j ≠ src.head → tgt'.tape j = src.tape j)) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro j hj
      have hj' := h3 j
      simp only [if_neg hj] at hj'
      exact hj'
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro j
      by_cases hj : j = src.head
      · simp [hj]
      · simp [hj, h3 j hj]
  rw [allCellLocalQTM_windowStep hn V hV src tgt']
  by_cases h : (moveCell (allCellMove src.state) src.head = some tgt'.head ∧
      tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
      (∀ j, j ≠ src.head → tgt'.tape j = src.tape j))
  · simp only [if_pos h]
    rw [if_pos (hiff.mpr h)]
  · simp only [if_neg h]
    rw [if_neg (fun hh => h (hiff.mp hh))]

/-- One step from an all-cell basis configuration has the prescribed local amplitude on valid
successors and zero elsewhere. -/
theorem allCellLocalQTM_windowStep_ket {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (AllCellState n k) Bool) :
    (windowStep (t := w) (allCellLocalQTM hn V hV) *ᵥ Ket src) tgt' =
      if moveCell (allCellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
          (∀ j, tgt'.tape j = if j = src.head then tgt'.tape src.head else src.tape j)
      then allCellAmp V src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact allCellLocalQTM_windowStep hn V hV src tgt'
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- The amplitude after an all-cell basis step is its local amplitude exactly when its move,
next state, and off-head tape agreement hold. -/
theorem allCellLocalQTM_windowStep_ket_norm {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    {w : ℕ} (src tgt' : WindowCfg w (AllCellState n k) Bool) :
    (windowStep (t := w) (allCellLocalQTM hn V hV) *ᵥ Ket src) tgt' =
      if moveCell (allCellMove src.state) src.head = some tgt'.head ∧
          tgt'.state = allCellNext hn src.state (src.tape src.head) ∧
          (∀ j, j ≠ src.head → tgt'.tape j = src.tape j)
      then allCellAmp V src.state (src.tape src.head) (tgt'.tape src.head) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem src (Finset.mem_univ _)]
  · simp only [Qatlib.Foundations.PureStateMath.Ket, ↓reduceIte, mul_one]
    exact allCellLocalQTM_windowStep_norm hn V hV src tgt'
  · intro d _ hd
    simp [Qatlib.Foundations.PureStateMath.Ket, hd]

/-- Given a valid head move and the source head symbol, one all-cell step is the sum of the two
successor kets weighted by their local amplitudes. -/
theorem allCellLocalQTM_step_ket {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (src : WindowCfg w (AllCellState n k) Bool) (a : Bool) (h' : Fin (2 * w + 1))
    (hmove : moveCell (allCellMove src.state) src.head = some h')
    (htape : src.tape src.head = a) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ Ket src
      = (allCellAmp V src.state a false) • Ket (allCellSuccCfg hn src a false h')
        + (allCellAmp V src.state a true) • Ket (allCellSuccCfg hn src a true h') := by
  classical
  funext tgtC
  rw [allCellLocalQTM_windowStep_ket hn V hV]
  rw [htape]
  by_cases hcond : (moveCell (allCellMove src.state) src.head = some tgtC.head ∧
      tgtC.state = allCellNext hn src.state a ∧
      (∀ j, tgtC.tape j = if j = src.head then tgtC.tape src.head else src.tape j))
  · rw [if_pos hcond]
    have hhead : tgtC.head = h' := by
      rw [hmove] at hcond
      exact Option.some.inj hcond.1 |>.symm
    have hstate : tgtC.state = allCellNext hn src.state a := hcond.2.1
    have hne : allCellSuccCfg hn src a false h' ≠ allCellSuccCfg hn src a true h' := by
      intro hcon
      have hh := congrArg (fun c => c.tape src.head) hcon
      simp only [allCellSuccCfg_tape_at hn src a false h',
        allCellSuccCfg_tape_at hn src a true h'] at hh
      exact absurd hh (by simp)
    have hne' : allCellSuccCfg hn src a true h' ≠ allCellSuccCfg hn src a false h' :=
      Ne.symm hne
    by_cases hb : tgtC.tape src.head = false
    · have hEq : tgtC = allCellSuccCfg hn src a false h' := by
        refine WindowCfg_eq_of_fields tgtC (allCellSuccCfg hn src a false h') ?_ ?_ ?_
        · exact hhead
        · exact hstate
        · intro j
          have h3 := hcond.2.2 j
          by_cases hj : j = src.head
          · rw [hj]
            rw [allCellSuccCfg_tape hn src a false h' src.head, if_pos rfl]
            rw [hb]
          · rw [allCellSuccCfg_tape hn src a false h' j, if_neg hj]
            rw [h3, if_neg hj]
      rw [hEq]
      rw [allCellSuccCfg_tape_at hn src a false h']
      simp [Qatlib.Foundations.PureStateMath.Ket, hne, hne', Pi.smul_apply, Pi.add_apply]
    · have hb' : tgtC.tape src.head = true := by
        cases hval : tgtC.tape src.head with
        | false => exact absurd hval hb
        | true => rfl
      have hEq : tgtC = allCellSuccCfg hn src a true h' := by
        refine WindowCfg_eq_of_fields tgtC (allCellSuccCfg hn src a true h') ?_ ?_ ?_
        · exact hhead
        · exact hstate
        · intro j
          have h3 := hcond.2.2 j
          by_cases hj : j = src.head
          · rw [hj]
            rw [allCellSuccCfg_tape hn src a true h' src.head, if_pos rfl]
            rw [hb']
          · rw [allCellSuccCfg_tape hn src a true h' j, if_neg hj]
            rw [h3, if_neg hj]
      rw [hEq]
      rw [allCellSuccCfg_tape_at hn src a true h']
      simp [Qatlib.Foundations.PureStateMath.Ket, hne, hne', Pi.smul_apply, Pi.add_apply]
  · rw [if_neg hcond]
    have hneF : tgtC ≠ allCellSuccCfg hn src a false h' := by
      intro hcon
      apply hcond
      refine ⟨?_, ?_, ?_⟩
      · rw [hmove]
        have hh := congrArg (fun c => c.head) hcon
        simp only [allCellSuccCfg_head] at hh
        rw [hh]
      · have hs := congrArg (fun c => c.state) hcon
        simp only [allCellSuccCfg_state] at hs
        exact hs
      · intro j
        have ht := congrArg (fun c => c.tape j) hcon
        simp only [allCellSuccCfg_tape hn src a false h' j] at ht
        by_cases hj : j = src.head
        · rw [hj]
          rw [if_pos rfl]
        · rw [if_neg hj] at ht
          rw [if_neg hj]
          exact ht
    have hneT : tgtC ≠ allCellSuccCfg hn src a true h' := by
      intro hcon
      apply hcond
      refine ⟨?_, ?_, ?_⟩
      · rw [hmove]
        have hh := congrArg (fun c => c.head) hcon
        simp only [allCellSuccCfg_head] at hh
        rw [hh]
      · have hs := congrArg (fun c => c.state) hcon
        simp only [allCellSuccCfg_state] at hs
        exact hs
      · intro j
        have ht := congrArg (fun c => c.tape j) hcon
        simp only [allCellSuccCfg_tape hn src a true h' j] at ht
        by_cases hj : j = src.head
        · rw [hj]
          rw [if_pos rfl]
        · rw [if_neg hj] at ht
          rw [if_neg hj]
          exact ht
    simp [Qatlib.Foundations.PureStateMath.Ket, hneF, hneT]

/-- The symbol-preserving successor of a start configuration is the prescribed start-step
configuration at the supplied head position. -/
theorem allCellSuccCfg_start {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h' : Fin (2 * w + 1)) :
    allCellSuccCfg hn (allCellStartCfg base) (base.tape base.head) (base.tape base.head) h'
      = allCellStartStepCfg hn base h' := by
  refine WindowCfg_eq_of_fields _ _ ?_ ?_ ?_
  · rfl
  · simp [allCellSuccCfg_state, allCellStartCfg_state, allCellStartStepCfg_state,
      allCellNext_start hn]
  · intro j
    rw [allCellSuccCfg_start_tape hn base h' j]
    rw [allCellStartStepCfg_tape hn base h' j]

/-- When the right neighbor exists, one step from the start configuration reaches the first
serve configuration without changing the tape. -/
theorem allCellLocalQTM_startStep_ket {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool)
    (h' : Fin (2 * w + 1)) (hh : h'.val = base.head.val + 1) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ Ket (allCellStartCfg base)
      = Ket (allCellStartStepCfg hn base h') := by
  classical
  have hne : base.head.val ≠ 2 * w := by omega
  have hmove : moveCell (allCellMove (allCellStartCfg base).state) (allCellStartCfg base).head
      = some h' := by
    rw [allCellStartCfg_state, allCellStartCfg_head, allCellMove_start]
    have h1 : moveCell QtmMove.right base.head = some ⟨base.head.val + 1, by omega⟩ := by
      simp [moveCell, hne]
    rw [h1]
    congr 1
    apply Fin.ext
    exact hh.symm
  rw [allCellLocalQTM_step_ket hn V hV (allCellStartCfg base) (base.tape base.head) h'
    hmove (allCellStartCfg_tape_at base)]
  by_cases ha : base.tape base.head = false
  · rw [ha]
    have hEq : allCellSuccCfg hn (allCellStartCfg base) false false h'
        = allCellStartStepCfg hn base h' := by
      have h := allCellSuccCfg_start hn base h'
      rw [ha] at h
      exact h
    rw [hEq]
    simp [allCellStartCfg_state, allCellAmp_start_row]
  · have ha' : base.tape base.head = true := by
        cases hval : base.tape base.head with
        | false => exact absurd hval ha
        | true => rfl
    rw [ha']
    have hEq : allCellSuccCfg hn (allCellStartCfg base) true true h'
        = allCellStartStepCfg hn base h' := by
      have h := allCellSuccCfg_start hn base h'
      rw [ha'] at h
      exact h
    rw [hEq]
    simp [allCellStartCfg_state, allCellAmp_start_row]

/-- During a gate stage, the successor construction increments the serve stage and replaces the
head-cell bit by the output symbol. -/
theorem allCellSuccCfg_serve {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val < k) (a b : Bool) :
    allCellSuccCfg hn (allCellServeCfg base h i j a) a b h
      = allCellServeCfg base h i ⟨j.val + 1, by omega⟩ b := by
  refine WindowCfg_eq_of_fields _ _ ?_ ?_ ?_
  · rfl
  · simp [allCellSuccCfg_state, allCellServeCfg_state, allCellNext_serve hn i j a, hj]
  · intro m
    rw [allCellSuccCfg_serve_tape hn base h i j a b m]
    rw [allCellServeCfg_tape base h i ⟨j.val + 1, by omega⟩ b m]

/-- One all-cell gate step advances the serve stage and applies the designated cell unitary to
the local amplitude vector. -/
theorem allCellLocalQTM_gateStep_super {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val < k) (v : Bool → ℂ) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ allCellServeSuper base h i j v
      = allCellServeSuper base h i ⟨j.val + 1, by omega⟩ (V i ⟨j.val, hj⟩ *ᵥ v) := by
  classical
  have hmove : moveCell (allCellMove (allCellServeCfg base h i j false).state)
      (allCellServeCfg base h i j false).head = some h := by
    rw [allCellServeCfg_state, allCellServeCfg_head, allCellMove_serve]
    simp [hj, moveCell]
  rw [allCellServeSuper, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hstepF := allCellLocalQTM_step_ket hn V hV (allCellServeCfg base h i j false) false h
    hmove (allCellServeCfg_tape_at base h i j false)
  have hstepT := allCellLocalQTM_step_ket hn V hV (allCellServeCfg base h i j true) true h
    hmove (allCellServeCfg_tape_at base h i j true)
  rw [hstepF, hstepT]
  rw [allCellSuccCfg_serve hn base h i j hj false false]
  rw [allCellSuccCfg_serve hn base h i j hj false true]
  rw [allCellSuccCfg_serve hn base h i j hj true false]
  rw [allCellSuccCfg_serve hn base h i j hj true true]
  simp only [allCellServeCfg_state, allCellAmp_serve_gate_row V i j hj]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, allCellServeSuper, Matrix.mulVec]
  simp only [dotProduct, Fintype.sum_bool]
  ring

/-- After `j ≤ k` serve steps at one cell, its superposition is at stage `j` with amplitudes
given by that cell's first `j` gates. -/
theorem allCellLocalQTM_gateSeq {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (v : Bool → ℂ) :
    ∀ (j : ℕ) (hj : j ≤ k),
      (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ j *ᵥ
          allCellServeSuper base h i ⟨0, by omega⟩ v
        = allCellServeSuper base h i ⟨j, by omega⟩
            (gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) j hj *ᵥ v) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [allCellServeSuper, pow_zero, Matrix.one_mulVec, gateSeqProd]
  | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [ih (by omega)]
      rw [allCellLocalQTM_gateStep_super hn V hV base h i ⟨j, by omega⟩ hjk]
      rw [Matrix.mulVec_mulVec]
      have hprod : gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) (j + 1) hj
          = V i ⟨j, by omega⟩ * gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) j (by omega) := rfl
      rw [hprod]

/-- At the final stage of a nonfinal cell, the symbol-preserving successor is the next-cell
advance configuration. -/
theorem allCellSuccCfg_advance {n k w : ℕ} (hn : 0 < n)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 < n)
    (h' : Fin (2 * w + 1)) :
    allCellSuccCfg hn (allCellServeCfg base h i j (base.tape h)) (base.tape h) (base.tape h) h'
      = allCellAdvanceCfg base i hi h' := by
  refine WindowCfg_eq_of_fields _ _ ?_ ?_ ?_
  · rfl
  · simp [allCellSuccCfg_state, allCellServeCfg_state, allCellAdvanceCfg_state,
      allCellNext_serve hn i j (base.tape h), hj, hi]
  · intro m
    rw [allCellSuccCfg_advance_tape hn base h i j h' m]
    rw [allCellAdvanceCfg_tape base i hi h' m]

/-- After the last gate of a nonfinal cell, one step moves right to the next cell's advance
configuration and preserves the tape. -/
theorem allCellLocalQTM_advanceStep_ket {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 < n)
    (h' : Fin (2 * w + 1)) (hh : h'.val = h.val + 1) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
        Ket (allCellServeCfg base h i j (base.tape h))
      = Ket (allCellAdvanceCfg base i hi h') := by
  classical
  have hne : h.val ≠ 2 * w := by omega
  have hmove : moveCell (allCellMove (allCellServeCfg base h i j (base.tape h)).state)
      (allCellServeCfg base h i j (base.tape h)).head = some h' := by
    rw [allCellServeCfg_state, allCellServeCfg_head, allCellMove_serve]
    simp [hj, hi, moveCell, hne]
    congr 1
    exact hh.symm
  rw [allCellLocalQTM_step_ket hn V hV (allCellServeCfg base h i j (base.tape h))
    (base.tape h) h' hmove (allCellServeCfg_tape_at base h i j (base.tape h))]
  by_cases hb : base.tape h = false
  · rw [hb]
    have hEq : allCellSuccCfg hn (allCellServeCfg base h i j false) false false h'
        = allCellAdvanceCfg base i hi h' := by
      have h := allCellSuccCfg_advance hn base h i j hj hi h'
      rw [hb] at h
      exact h
    rw [hEq]
    simp [allCellServeCfg_state, allCellAmp_serve_move_row V i j hj hi]
  · have hb' : base.tape h = true := by
        cases hval : base.tape h with
        | false => exact absurd hval hb
        | true => rfl
    rw [hb']
    have hEq : allCellSuccCfg hn (allCellServeCfg base h i j true) true true h'
        = allCellAdvanceCfg base i hi h' := by
      have h := allCellSuccCfg_advance hn base h i j hj hi h'
      rw [hb'] at h
      exact h
    rw [hEq]
    simp [allCellServeCfg_state, allCellAmp_serve_move_row V i j hj hi]

/-- At the final stage of the final cell, a superposition separates into the true and false
successor branches with their original amplitudes and flipped output symbols. -/
theorem allCellLocalQTM_measure_super {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val = k) (hi : i.val + 1 = n) (v : Bool → ℂ) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ allCellServeSuper base h i j v
      = v true • Ket (allCellSuccCfg hn (allCellServeCfg base h i j true) true false h)
        + v false • Ket (allCellSuccCfg hn (allCellServeCfg base h i j false) false true h) := by
  classical
  have hmove : moveCell (allCellMove (allCellServeCfg base h i j false).state)
      (allCellServeCfg base h i j false).head = some h := by
    rw [allCellServeCfg_state, allCellServeCfg_head, allCellMove_serve]
    simp [hj, hi, moveCell]
  rw [allCellServeSuper, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hstepF := allCellLocalQTM_step_ket hn V hV (allCellServeCfg base h i j false) false h
    hmove (allCellServeCfg_tape_at base h i j false)
  have hstepT := allCellLocalQTM_step_ket hn V hV (allCellServeCfg base h i j true) true h
    hmove (allCellServeCfg_tape_at base h i j true)
  rw [hstepF, hstepT]
  have hne : allCellSuccCfg hn (allCellServeCfg base h i j true) true false h
      ≠ allCellSuccCfg hn (allCellServeCfg base h i j false) false true h := by
    intro hcon
    have hh := congrArg (fun c => c.state) hcon
    simp only [allCellSuccCfg_state, allCellServeCfg_state] at hh
    simp [allCellNext_serve hn i j true, allCellNext_serve hn i j false, hj, hi] at hh
  simp only [allCellServeCfg_state, allCellAmp_serve_measure_row V i j hj hi]
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket]
  by_cases hcf : c = allCellSuccCfg hn (allCellServeCfg base h i j true) true false h
  · rw [if_pos hcf]
    by_cases hct : c = allCellSuccCfg hn (allCellServeCfg base h i j false) false true h
    · rw [if_pos hct]
      have : allCellSuccCfg hn (allCellServeCfg base h i j true) true false h
          = allCellSuccCfg hn (allCellServeCfg base h i j false) false true h :=
        hcf.symm.trans hct
      exact absurd this hne
    · rw [if_neg hct]
      simp
  · rw [if_neg hcf]
    simp

/-- From gate stage zero of the final cell, accepting mass after `k+1` steps is the
true-component squared norm of its gate product applied to the supplied amplitudes. -/
theorem allCellLocalQTM_acceptMass {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (hj : i.val + 1 = n) (v : Bool → ℂ) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
      BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (k + 1) *ᵥ
        allCellServeSuper base h i ⟨0, by omega⟩ v) c)
      = ‖(gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v) true‖ ^ 2 := by
  classical
  have hψ : (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (k + 1) *ᵥ
        allCellServeSuper base h i ⟨0, by omega⟩ v
      = (gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v) true •
          Ket (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ true) true false h)
        + (gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v) false •
          Ket (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ false) false true h) := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [allCellLocalQTM_gateSeq hn V hV base h i v k (by omega)]
    rw [allCellLocalQTM_measure_super hn V hV base h i ⟨k, by omega⟩ rfl hj
      (gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v)]
  rw [hψ]
  have hacc : (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ true) true false h).state
      = (.acc : AllCellState n k) := by
    rw [allCellSuccCfg_state, allCellServeCfg_state]
    rw [allCellNext_serve hn i ⟨k, by omega⟩ true]
    simp <;> omega
  have hrej : (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ false) false true h).state
      = (.rej : AllCellState n k) := by
    rw [allCellSuccCfg_state, allCellServeCfg_state]
    rw [allCellNext_serve hn i ⟨k, by omega⟩ false]
    simp <;> omega
  have hne : allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ true) true false h
      ≠ allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ false) false true h := by
    intro hcon
    have hh := congrArg WindowCfg.state hcon
    rw [hacc, hrej] at hh
    exact absurd hh (by simp)
  rw [Finset.sum_eq_single
    (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ true) true false h)]
  · have hval :
        ((gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v) true •
            Ket (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ true) true false h) +
          (gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v) false •
            Ket (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ false) false true h))
          (allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ true) true false h)
        = (gateSeqProd (fun l : Fin k => V i ⟨l.val, by omega⟩) k (by omega) *ᵥ v) true := by
      simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, hne]
    rw [BornProb, hval]
  · intro c hc hne'
    have hstate : c.state = (.acc : AllCellState n k) := (Finset.mem_filter.mp hc).2
    rw [BornProb]
    have hne1 : c ≠ allCellSuccCfg hn (allCellServeCfg base h i ⟨k, by omega⟩ false) false true h := by
      intro hcon
      have hh := congrArg WindowCfg.state hcon
      rw [hrej] at hh
      simp [hstate] at hh
    simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket, hne1, hne']
  · intro h
    exact (h (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hacc⟩)).elim

/-- Serving the final cell from its input-bit basis amplitudes gives accepting mass equal to the
corresponding embedded circuit's true probability at that cell. -/
theorem allCell_acceptProb_cell {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (h : Fin (2 * w + 1))
    (i : Fin n) (hj : i.val + 1 = n) (x : Reg n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
      BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (k + 1) *ᵥ
        allCellServeSuper base h i ⟨0, by omega⟩
          (fun c => if c = x i then (1 : ℂ) else 0)) c)
      = AcceptProbAt i (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (((List.ofFn (fun l : Fin k => V i ⟨l.val, by omega⟩)).map
            (fun U => embedRegI i U)).map Step.gate) (Ket x)) := by
  rw [allCellLocalQTM_acceptMass hn V hV base h i hj
    (fun c => if c = x i then (1 : ℂ) else 0)]
  rw [acceptProb_embedI i (List.ofFn (fun l : Fin k => V i ⟨l.val, by omega⟩)) x]
  rw [boolGateProd_ofFn k (fun l : Fin k => V i ⟨l.val, by omega⟩)]

/-- A finite product factors into its selected factor and the product over all remaining
indices. -/
theorem fin_prod_split {n : ℕ} {M : Type*} [CommSemiring M] (i : Fin n) (f : Fin n → M) :
    (∏ j : Fin n, f j) = f i * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j := by
  classical
  calc (∏ j : Fin n, f j) = ∏ j ∈ (Finset.univ : Finset (Fin n)), f j := rfl
    _ = ∏ j ∈ insert i (Finset.univ.erase i), f j := by
      congr 1
      ext j
      simp
    _ = f i * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j := by
      exact Finset.prod_insert (f := f) (by simp)

/-- Summing a product of independent Boolean-coordinate factors over all Boolean registers
equals the product of their Boolean sums. -/
theorem fin_sum_prod {n : ℕ} {M : Type*} [CommSemiring M]
    (g : Fin n → Bool → M) :
    (∑ y : Fin n → Bool, ∏ j : Fin n, g j (y j)) = ∏ j : Fin n, (∑ b : Bool, g j b) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hconv : (∑ y : Fin (n + 1) → Bool, ∏ j : Fin (n + 1), g j (y j))
          = ∑ p : Bool × (Fin n → Bool),
              ∏ j : Fin (n + 1), g j ((finBoolCons n) p j) := by
        refine Fintype.sum_equiv (finBoolCons n).symm _ _ ?_
        intro y
        simp
      rw [hconv]
      rw [Fintype.sum_prod_type]
      have hsplit : ∀ (p : Bool × (Fin n → Bool)),
          ∏ j : Fin (n + 1), g j ((finBoolCons n) p j)
            = g 0 p.1 * ∏ i : Fin n, g (Fin.succ i) (p.2 i) := by
        intro p
        rw [Fin.prod_univ_succ]
        congr 1
      simp only [hsplit]
      calc (∑ x : Bool, ∑ y : Fin n → Bool, g 0 x * (∏ i : Fin n, g (Fin.succ i) (y i)))
          = ∑ x : Bool, g 0 x * (∑ y : Fin n → Bool, ∏ i : Fin n, g (Fin.succ i) (y i)) := by
            apply Finset.sum_congr rfl
            intro x _
            exact (Finset.mul_sum (Finset.univ : Finset (Fin n → Bool))
              (fun y => ∏ i : Fin n, g (Fin.succ i) (y i)) (g 0 x)).symm
        _ = (∑ x : Bool, g 0 x)
            * (∑ y : Fin n → Bool, ∏ i : Fin n, g (Fin.succ i) (y i)) := by
            exact (Finset.sum_mul (Finset.univ : Finset Bool) (fun x => g 0 x)
              (∑ y : Fin n → Bool, ∏ i : Fin n, g (Fin.succ i) (y i))).symm
        _ = (∑ x : Bool, g 0 x) * (∏ i : Fin n, ∑ b : Bool, g (Fin.succ i) b) := by
            rw [ih (fun i => g (Fin.succ i))]
        _ = ∏ j : Fin (n + 1), (∑ b : Bool, g j b) := by
            rw [Fin.prod_univ_succ]

/-- The product of coordinatewise equality indicators is the indicator of equality of the full
registers. -/
theorem prod_indicator {n : ℕ} (y x : Reg n) :
    (∏ j : Fin n, (if y j = x j then (1 : ℂ) else 0)) = if y = x then 1 else 0 := by
  classical
  by_cases h : y = x
  · subst h
    simp
  · obtain ⟨j, hj⟩ : ∃ j : Fin n, y j ≠ x j := by
      by_contra hc
      have hc' : ∀ j : Fin n, y j = x j := by
        intro j
        by_contra h2
        exact hc ⟨j, h2⟩
      exact h (funext fun i => hc' i)
    rw [if_neg h]
    have hsplit := fin_prod_split j (fun j => (if y j = x j then (1 : ℂ) else 0))
    rw [if_neg hj] at hsplit
    rw [hsplit]
    simp

/-- The norm of a finite complex product equals the product of the factor norms. -/
theorem norm_prod {n : ℕ} (f : Fin n → ℂ) :
    ‖∏ j : Fin n, f j‖ = ∏ j : Fin n, ‖f j‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Complex.norm_mul, ih (fun i => f (Fin.succ i))]
    rw [Fin.prod_univ_succ]

/-- The squared norm of a finite complex product equals the product of the squared factor norms. -/
theorem norm_prod_sq {n : ℕ} (f : Fin n → ℂ) :
    ‖∏ j : Fin n, f j‖ ^ 2 = ∏ j : Fin n, ‖f j‖ ^ 2 := by
  rw [norm_prod, ← Finset.prod_pow]

/-- The two terms indexed by a bit and its negation sum to the corresponding component of
Boolean matrix-vector multiplication. -/
theorem embedRegI_pair {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ)
    (amps : Fin n → Bool → ℂ) (y : Reg n) :
    U (y i) (y i) * amps i (y i) + U (y i) (! (y i)) * amps i (! (y i))
      = (U *ᵥ amps i) (y i) := by
  have hb := sum_bool_pair (f := fun z => U (y i) z * amps i z) (y i)
  rw [mulVec_bool, ← hb]

/-- Every register basis ket is a tensor state of its coordinate basis amplitudes. -/
theorem ket_tensor {n : ℕ} (x : Reg n) :
    TensorState (fun j => fun c => if c = x j then (1 : ℂ) else 0) (Ket x) := by
  intro y
  rw [prod_indicator]
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- A gate embedded on one wire of a tensor state transforms that wire's amplitude vector and
leaves the other amplitude factors unchanged. -/
theorem embedRegI_applyGate_tensor {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ)
    (amps : Fin n → Bool → ℂ) (ψ : QState (Reg n)) (hψ : TensorState amps ψ) :
    ∀ y : Reg n,
      ApplyGate (embedRegI i U) ψ y
        = (U *ᵥ amps i) (y i) * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, amps j (y j) := by
  classical
  intro y
  have hne : y ≠ flipI i y := (flipI_ne i y).symm
  have hkey : ∀ z ∈ (Finset.univ : Finset (Reg n)), z ∉ ({y, flipI i y} : Finset (Reg n)) →
      embedRegI i U y z * ψ z = 0 := by
    intro z _ hz
    have hag : ¬ AgreesOutsideI i y z := by
      intro h
      rcases (agreesOutsideI_iff i y z).mp h with h | h
      · exact hz (by simp [h])
      · exact hz (by simp [h])
    rw [embedRegI, if_neg hag]
    simp
  have hsum : (∑ z : Reg n, embedRegI i U y z * ψ z)
      = ∑ z ∈ ({y, flipI i y} : Finset (Reg n)), embedRegI i U y z * ψ z :=
    (Finset.sum_subset (s₁ := ({y, flipI i y} : Finset (Reg n)))
      (s₂ := (Finset.univ : Finset (Reg n)))
      (f := fun z => embedRegI i U y z * ψ z)
      (fun _ _ => by simp)
      hkey).symm
  have hpair : (∑ z ∈ ({y, flipI i y} : Finset (Reg n)), embedRegI i U y z * ψ z)
      = embedRegI i U y y * ψ y + embedRegI i U y (flipI i y) * ψ (flipI i y) :=
    Finset.sum_pair (f := fun z => embedRegI i U y z * ψ z) hne
  have hmat1 : embedRegI i U y y = U (y i) (y i) := by
    rw [embedRegI, if_pos (by intro j hj; rfl)]
  have hmat2 : embedRegI i U y (flipI i y) = U (y i) (! (y i)) := by
    rw [embedRegI, if_pos (by intro j hj; exact flipI_of_ne i y hj)]
    rw [flipI_bit]
  have hps1 : ψ y = amps i (y i) * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, amps j (y j) := by
    rw [hψ y, fin_prod_split i (fun j => amps j (y j))]
  have hps2 : ψ (flipI i y)
      = amps i (! (y i)) * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, amps j (y j) := by
    rw [hψ (flipI i y)]
    have hsp := fin_prod_split i (fun j => amps j (flipI i y j))
    rw [hsp]
    have hcong : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, amps j ((flipI i y) j))
        = ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, amps j (y j) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [flipI_of_ne i y hjne]
    rw [hcong]
    rw [flipI_bit]
  change (∑ z : Reg n, embedRegI i U y z * ψ z) = _
  rw [hsum, hpair, hmat1, hmat2, hps1, hps2]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, embedRegI_pair i U amps y]

/-- Applying an embedded one-wire gate preserves the tensor-state form and updates only that
wire's amplitude vector. -/
theorem embedRegI_applyGate_tensorState {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ)
    (amps : Fin n → Bool → ℂ) (ψ : QState (Reg n)) (hψ : TensorState amps ψ) :
    TensorState (ampsUpd i (U *ᵥ amps i) amps) (ApplyGate (embedRegI i U) ψ) := by
  intro y
  rw [embedRegI_applyGate_tensor i U amps ψ hψ y]
  rw [fin_prod_split i (fun j => ampsUpd i (U *ᵥ amps i) amps j (y j))]
  rw [show ampsUpd i (U *ᵥ amps i) amps i (y i) = (U *ᵥ amps i) (y i) by simp [ampsUpd]]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [ampsUpd, hjne]

/-- A tensor state's true probability at wire `i` equals its local true squared amplitude times
the product of the other wires' total squared masses. -/
theorem acceptProbAt_tensor {n : ℕ} (i : Fin n) (amps : Fin n → Bool → ℂ)
    (ψ : QState (Reg n)) (hψ : TensorState amps ψ) :
    AcceptProbAt i ψ
      = ‖amps i true‖ ^ 2
        * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (∑ b : Bool, ‖amps j b‖ ^ 2) := by
  classical
  rw [AcceptProbAt, MeasureProb]
  have hnorm : ∀ y : Reg n, BornProb ψ y = ∏ j : Fin n, ‖amps j (y j)‖ ^ 2 := by
    intro y
    rw [BornProb, hψ y, norm_prod_sq]
  have hsum : (∑ y ∈ (Finset.univ : Finset (Reg n)).filter (fun y => y i = true), BornProb ψ y)
      = ∑ y ∈ (Finset.univ : Finset (Reg n)).filter (fun y => y i = true),
          ∏ j : Fin n, ‖amps j (y j)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro y _
    exact hnorm y
  rw [hsum]
  set g : Fin n → Bool → ℝ :=
    fun j b => if j = i then (if b = true then ‖amps j b‖ ^ 2 else 0) else ‖amps j b‖ ^ 2 with hg
  have hgprod : ∀ y : Reg n, (if y i = true then (∏ j : Fin n, ‖amps j (y j)‖ ^ 2) else 0)
      = ∏ j : Fin n, g j (y j) := by
    intro y
    by_cases hy : y i = true
    · rw [if_pos hy, fin_prod_split i (fun j => ‖amps j (y j)‖ ^ 2),
        fin_prod_split i (fun j => g j (y j))]
      congr 1
      · simp [hg, hy]
      · refine Finset.prod_congr rfl ?_
        intro j hj
        have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [hg, hjne]
    · rw [if_neg hy, fin_prod_split i (fun j => g j (y j))]
      simp [hg, hy]
  calc (∑ y ∈ (Finset.univ : Finset (Reg n)).filter (fun y => y i = true),
          ∏ j : Fin n, ‖amps j (y j)‖ ^ 2)
      = ∑ y : Reg n, if y i = true then (∏ j : Fin n, ‖amps j (y j)‖ ^ 2) else 0 := by
        rw [Finset.sum_filter]
    _ = ∑ y : Reg n, ∏ j : Fin n, g j (y j) := by
      apply Finset.sum_congr rfl
      intro y _
      exact hgprod y
    _ = ∏ j : Fin n, (∑ b : Bool, g j b) := fin_sum_prod g
    _ = (∑ b : Bool, g i b)
        * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (∑ b : Bool, g j b) := by
      rw [fin_prod_split i]
    _ = ‖amps i true‖ ^ 2
        * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (∑ b : Bool, ‖amps j b‖ ^ 2) := by
      congr 1
      · simp [hg]
      · refine Finset.prod_congr rfl ?_
        intro j hj
        have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [hg, hjne]

/-- Running a concatenated circuit first runs its first part and then runs its second part. -/
theorem run_append {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (C D : Circuit I) (ψ : QState I) :
    Run oracle (C ++ D) ψ = Run oracle D (Run oracle C ψ) := by
  induction C generalizing ψ with
  | nil => simp [Run]
  | cons s C ih =>
      cases s with
      | gate U => simp [Run, ih]
      | query => simp [Run, ih]

/-- Updating an amplitude family at `i` returns the new vector there and the original vector at
every other index. -/
theorem ampsUpd_eq {n : ℕ} (i : Fin n) (v : Bool → ℂ) (A : Fin n → Bool → ℂ)
    (j : Fin n) : ampsUpd i v A j = if j = i then v else A j := rfl

/-- Running a gate list on one wire preserves tensor-state form and updates that wire's
amplitudes by the Boolean gate product. -/
theorem run_wireGates_tensor {n : ℕ} (i : Fin n) (gs : List (Matrix Bool Bool ℂ))
    (amps : Fin n → Bool → ℂ) (ψ : QState (Reg n)) (hψ : TensorState amps ψ) :
    TensorState (ampsUpd i (boolGateProd gs *ᵥ amps i) amps)
      (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (gs.map (fun U => Step.gate (embedRegI i U))) ψ) := by
  induction gs generalizing amps ψ with
  | nil =>
      rw [boolGateProd, Matrix.one_mulVec]
      have hA : ampsUpd i (amps i) amps = amps := by
        funext j
        by_cases hj : j = i
        · simp [ampsUpd, hj]
        · simp [ampsUpd, hj]
      rw [hA]
      change TensorState amps ψ
      exact hψ
  | cons U gs ih =>
      have hψ' : TensorState (ampsUpd i (U *ᵥ amps i) amps)
          (ApplyGate (embedRegI i U) ψ) :=
        embedRegI_applyGate_tensorState i U amps ψ hψ
      have h := ih (ampsUpd i (U *ᵥ amps i) amps) (ApplyGate (embedRegI i U) ψ) hψ'
      have hrun : Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (List.map (fun U => Step.gate (embedRegI i U)) (U :: gs)) ψ
        = Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (List.map (fun U => Step.gate (embedRegI i U)) gs)
          (ApplyGate (embedRegI i U) ψ) := by
        simp only [List.map_cons, Run]
      intro y
      rw [hrun, h y]
      rw [fin_prod_split i (fun j =>
        ampsUpd i (boolGateProd gs *ᵥ (ampsUpd i (U *ᵥ amps i) amps) i)
          (ampsUpd i (U *ᵥ amps i) amps) j (y j))]
      rw [fin_prod_split i (fun j =>
        ampsUpd i (boolGateProd (U :: gs) *ᵥ amps i) amps j (y j))]
      congr 1
      · simp [ampsUpd, boolGateProd, Matrix.mulVec_mulVec]
      · refine Finset.prod_congr rfl ?_
        intro j hj
        have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [ampsUpd, hjne]

/-- Updating an unprocessed cell to its tour amplitudes extends the set of processed cells by
that cell. -/
theorem ampsUpd_tour {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    ampsUpd i (tourAmps V x i)
      (fun j => if j ∈ S then tourAmps V x j
                else (fun c => if c = x j then (1 : ℂ) else 0))
      = (fun j => if j ∈ insert i S then tourAmps V x j
                  else (fun c => if c = x j then (1 : ℂ) else 0)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [ampsUpd]
  · by_cases hjS : j ∈ S
    · simp [ampsUpd, hj, hjS]
    · simp [ampsUpd, hj, hjS]

/-- Running a list of distinct, previously unprocessed cells extends a partial tensor amplitude
assignment to the union with those cells. -/
theorem run_cells_tensor {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n) :
    ∀ (S : Finset (Fin n)) (l : List (Fin n)), l.Nodup → (∀ i ∈ l, i ∉ S) →
    ∀ (ψ : QState (Reg n)),
      TensorState (partialAmps V x S) ψ →
      TensorState (partialAmps V x (S ∪ l.toFinset))
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (l.flatMap (cellGateList V)) ψ) := by
  intro S l
  induction l generalizing S with
  | nil =>
      intro hnodup hdisj ψ hψ
      have hfin : (S ∪ ([] : List (Fin n)).toFinset : Finset (Fin n)) = S := by
        ext j
        simp
      rw [hfin]
      change TensorState _ ψ
      exact hψ
  | cons i l ih =>
      intro hnodup hdisj ψ hψ
      have hNodup : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hdisjl : ∀ j ∈ l, j ∉ S := fun j hj => hdisj j (List.mem_cons_of_mem i hj)
      have hnoti : ∀ j ∈ l, j ≠ i := by
        intro j hj hji
        exact (List.nodup_cons.mp hnodup).1 (hji ▸ hj)
      have hiS : i ∉ S := hdisj i List.mem_cons_self
      have htour : boolGateProd (cellGates V i) *ᵥ (partialAmps V x S i) = tourAmps V x i := by
        have hi : partialAmps V x S i = (fun c => if c = x i then (1 : ℂ) else 0) := by
          simp [partialAmps, hiS]
        rw [hi]
        rfl
      have hwire : TensorState (ampsUpd i (tourAmps V x i) (partialAmps V x S))
          (Run (1 : Matrix (Reg n) (Reg n) ℂ) (cellGateList V i) ψ) := by
        have h := run_wireGates_tensor i (cellGates V i) (partialAmps V x S) ψ hψ
        rw [htour] at h
        exact h
      have hconv : ampsUpd i (tourAmps V x i) (partialAmps V x S) = partialAmps V x (insert i S) := by
        exact ampsUpd_tour V x S i hiS
      rw [hconv] at hwire
      rw [List.flatMap_cons, run_append]
      have hres := ih (insert i S) hNodup
        (fun j hj hjS => by
          rcases (Finset.mem_insert.mp hjS) with rfl | hjin
          · exact (hnoti j hj) rfl
          · exact hdisjl j hj hjin)
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (cellGateList V i) ψ) hwire
      intro y
      rw [hres y]
      have hfin : (insert i S ∪ l.toFinset : Finset (Fin n)) = S ∪ (i :: l).toFinset := by
        rw [List.toFinset_cons]
        ext j
        simp
      rw [hfin]

/-- The composite cell circuit sends an input basis ket to the tensor state described by
`tourAmps`. -/
theorem run_compositeCellCircuit_tensor {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (x : Reg n) :
    TensorState (tourAmps V x)
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)) := by
  have hket : TensorState (partialAmps V x (∅ : Finset (Fin n))) (Ket x) := by
    have hk := ket_tensor x
    rw [show partialAmps V x (∅ : Finset (Fin n))
        = (fun j => fun c => if c = x j then (1 : ℂ) else 0) by
      funext j
      simp [partialAmps]]
    exact hk
  have h := run_cells_tensor V x (∅ : Finset (Fin n)) (List.finRange n)
    (List.nodup_finRange n) (by simp) (Qatlib.Foundations.PureStateMath.Ket x) hket
  have hfin : ((∅ : Finset (Fin n)) ∪ (List.finRange n).toFinset)
      = (Finset.univ : Finset (Fin n)) := by
    rw [List.toFinset_finRange]
    simp
  rw [hfin] at h
  have heq : partialAmps V x (Finset.univ : Finset (Fin n)) = tourAmps V x := by
    funext j
    simp [partialAmps]
  rw [heq] at h
  exact h

/-- The composite circuit's true probability at the last wire is its local true squared
amplitude times the total squared masses of the other tour amplitude vectors. -/
theorem compositeCellCircuit_acceptProbAt {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n) :
    AcceptProbAt ⟨n - 1, by omega⟩
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x))
      = ‖(tourAmps V x ⟨n - 1, by omega⟩) true‖ ^ 2
        * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩,
            (∑ b : Bool, ‖(tourAmps V x j) b‖ ^ 2) := by
  rw [acceptProbAt_tensor ⟨n - 1, by omega⟩ (tourAmps V x)
    (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x))
    (run_compositeCellCircuit_tensor V x)]

/-- The composite circuit's last-wire true probability factors into the last cell's gate-product
true squared amplitude and the other cells' gate-product total masses. -/
theorem compositeCellCircuit_acceptProbAt_cell {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n) :
    AcceptProbAt ⟨n - 1, by omega⟩
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x))
      = ‖(gateSeqProd (fun l : Fin k => V ⟨n - 1, by omega⟩ l) k (by omega) *ᵥ
            (fun c => if c = x ⟨n - 1, by omega⟩ then (1 : ℂ) else 0)) true‖ ^ 2
        * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩,
            (∑ b : Bool, ‖(gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
                (fun c => if c = x j then (1 : ℂ) else 0)) b‖ ^ 2) := by
  rw [compositeCellCircuit_acceptProbAt hn V x]
  have hamp : ∀ j : Fin n, tourAmps V x j
      = gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
        (fun c => if c = x j then (1 : ℂ) else 0) := by
    intro j
    simp [tourAmps, cellGates, boolGateProd_ofFn]
  have hprod : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩,
            (∑ b : Bool, ‖(tourAmps V x j) b‖ ^ 2))
      = ∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩,
            (∑ b : Bool, ‖(gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
                (fun c => if c = x j then (1 : ℂ) else 0)) b‖ ^ 2) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hamp j]
  rw [hprod]
  rw [hamp]

/-- The Boolean amplitude vector obtained by applying a cell's full gate sequence to its input
basis bit. -/
noncomputable def cellFinalAmp {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (x : Reg n) (j : Fin n) : Bool → ℂ :=
  gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
    (fun c => if c = x j then (1 : ℂ) else 0)

/-- The final cell amplitude vector agrees with the tour amplitude vector. -/
theorem cellFinalAmp_eq_tourAmps {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (x : Reg n) (j : Fin n) : cellFinalAmp V x j = tourAmps V x j := by
  simp [cellFinalAmp, tourAmps, cellGates, boolGateProd_ofFn]

/-- The total product mass over all assignments to a prefix equals the product of the individual
cells' total masses. -/
theorem cellPrefixMass {n k i : ℕ} (hi : i ≤ n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n) :
    (∑ f : Fin i → Bool, ∏ j : Fin i, ‖(cellFinalAmp V x (Fin.castLE hi j)) (f j)‖ ^ 2)
      = ∏ j : Fin i, (∑ b : Bool, ‖(cellFinalAmp V x (Fin.castLE hi j)) b‖ ^ 2) := by
  exact fin_sum_prod (fun j b => ‖(cellFinalAmp V x (Fin.castLE hi j)) b‖ ^ 2)

/-- The squared norm of a complex number is the real part of its product with its conjugate. -/
theorem complex_normSq_eq_re (z : ℂ) : Complex.normSq z = (z * star z).re := by
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re]
  simp [Complex.conj_re, Complex.conj_im]

/-- The sum of each unitary gate column's entry-conjugate products is the complex number one. -/
theorem gateCol_norm_complex {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (i : Fin k) (a : Bool) :
    (∑ b : Bool, (Us i b a) * star (Us i b a)) = 1 := by
  have hmat : star (Us i) * (Us i) = 1 := Matrix.mem_unitaryGroup_iff'.mp (hU i)
  have hD : (∑ b : Bool, (Us i b a) * star (Us i b a)) = (star (Us i) * (Us i)) a a := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [star_matrix_apply]
    exact mul_comm _ _
  rw [hD]
  simp [hmat]

/-- Unitary Boolean matrix-vector multiplication preserves the sum of entry-conjugate products. -/
theorem mulVec_norm_preserved_complex {U : Matrix Bool Bool ℂ}
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (v : Bool → ℂ) :
    (∑ b : Bool, ((U *ᵥ v) b) * star ((U *ᵥ v) b))
      = (∑ a : Bool, v a * star (v a)) := by
  classical
  calc (∑ b : Bool, ((U *ᵥ v) b) * star ((U *ᵥ v) b))
      = ∑ b : Bool, ∑ a : Bool, ∑ a' : Bool,
          (U b a * v a) * (star (U b a') * star (v a')) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Matrix.mulVec, dotProduct]
        have hstar : star ((∑ a : Bool, U b a * v a))
            = ∑ a' : Bool, star (U b a') * star (v a') := by
          rw [star_sum]
          apply Finset.sum_congr rfl
          intro a' _
          rw [star_mul]
          ring
        rw [hstar]
        rw [Fintype.sum_mul_sum]
    _ = ∑ a : Bool, ∑ a' : Bool,
          (∑ b : Bool, U b a * star (U b a')) * (v a * star (v a')) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a' _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = ∑ a : Bool, ∑ a' : Bool, (if a = a' then 1 else 0) * (v a * star (v a')) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro a' _
      by_cases h : a = a'
      · subst h
        rw [if_pos rfl]
        have hcol : (∑ b : Bool, U b a * star (U b a)) = 1 :=
          gateCol_norm_complex (k := 1) (fun _ => U) (fun _ => hU) ⟨0, by omega⟩ a
        rw [hcol]
      · rw [if_neg h]
        have hcol : (∑ b : Bool, U b a * star (U b a')) = 0 := by
          have h1 : (∑ b : Bool, U b a * star (U b a')) = ∑ b : Bool, star (U b a') * U b a := by
            apply Finset.sum_congr rfl
            intro b _
            ring
          rw [h1]
          exact gateCol_orth (k := 1) (fun _ => U) (fun _ => hU) ⟨0, by omega⟩ a' a (Ne.symm h)
        rw [hcol]
    _ = ∑ a : Bool, v a * star (v a) := by
      apply Finset.sum_congr rfl
      intro a _
      have hone : (∑ a' : Bool, (if a = a' then 1 else 0) * (v a * star (v a')))
          = v a * star (v a) := by
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
        · simp
        · intro b _ hb
          rw [if_neg (Ne.symm hb)]
          ring
      rw [hone]

/-- Unitary Boolean matrix-vector multiplication preserves the sum of squared amplitude norms. -/
theorem mulVec_norm_preserved {U : Matrix Bool Bool ℂ}
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (v : Bool → ℂ) :
    ∑ b : Bool, ‖(U *ᵥ v) b‖ ^ 2 = ∑ a : Bool, ‖v a‖ ^ 2 := by
  have h := mulVec_norm_preserved_complex hU v
  have h2 : (∑ b : Bool, Complex.normSq ((U *ᵥ v) b))
      = (∑ b : Bool, ((U *ᵥ v) b) * star ((U *ᵥ v) b)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact complex_normSq_eq_re _
  have h3 : (∑ a : Bool, Complex.normSq (v a)) = (∑ a : Bool, v a * star (v a)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact complex_normSq_eq_re _
  calc (∑ b : Bool, ‖(U *ᵥ v) b‖ ^ 2)
      = ∑ b : Bool, Complex.normSq ((U *ᵥ v) b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact Complex.sq_norm _
    _ = (∑ b : Bool, ((U *ᵥ v) b) * star ((U *ᵥ v) b)).re := h2
    _ = (∑ a : Bool, v a * star (v a)).re := by rw [h]
    _ = ∑ a : Bool, Complex.normSq (v a) := h3.symm
    _ = ∑ a : Bool, ‖v a‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        exact (Complex.sq_norm _).symm

/-- Every prefix of a unitary gate sequence preserves the total squared amplitude norm. -/
theorem gateSeqProd_norm {k : ℕ} (Us : Fin k → Matrix Bool Bool ℂ)
    (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (v : Bool → ℂ) :
    ∀ (j : ℕ) (hj : j ≤ k),
      ∑ b : Bool, ‖(gateSeqProd Us j hj *ᵥ v) b‖ ^ 2 = ∑ a : Bool, ‖v a‖ ^ 2 := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [gateSeqProd]
  | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hprod : gateSeqProd Us (j + 1) hj
          = Us ⟨j, hjk⟩ * gateSeqProd Us j (by omega) := rfl
      rw [hprod]
      rw [← Matrix.mulVec_mulVec]
      rw [mulVec_norm_preserved (hU ⟨j, hjk⟩) (gateSeqProd Us j (by omega) *ᵥ v)]
      exact ih (by omega)

/-- For unitary gate data, each final cell amplitude vector has total squared mass one. -/
theorem cellFinalAmp_mass {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (x : Reg n) (j : Fin n) :
    ∑ b : Bool, ‖(cellFinalAmp V x j) b‖ ^ 2 = 1 := by
  have h := gateSeqProd_norm (fun l : Fin k => V j l) (fun l => hV j l)
    (fun c => if c = x j then (1 : ℂ) else 0) k (by omega)
  have hone : (∑ a : Bool, ‖(fun c => if c = x j then (1 : ℂ) else 0) a‖ ^ 2) = 1 := by
    cases hx : x j with
    | false => simp [Complex.sq_norm]
    | true => simp [Complex.sq_norm]
  calc (∑ b : Bool, ‖(cellFinalAmp V x j) b‖ ^ 2)
      = ∑ b : Bool, ‖(gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
          (fun c => if c = x j then (1 : ℂ) else 0)) b‖ ^ 2 := rfl
    _ = ∑ a : Bool, ‖(fun c => if c = x j then (1 : ℂ) else 0) a‖ ^ 2 := h
    _ = 1 := hone

/-- For unitary gate data, the total product mass over every Boolean assignment to a cell prefix
is one. -/
theorem cellPrefixMass_one {n k i : ℕ} (hi : i ≤ n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (x : Reg n) :
    (∑ f : Fin i → Bool, ∏ j : Fin i, ‖(cellFinalAmp V x (Fin.castLE hi j)) (f j)‖ ^ 2) = 1 := by
  calc (∑ f : Fin i → Bool, ∏ j : Fin i, ‖(cellFinalAmp V x (Fin.castLE hi j)) (f j)‖ ^ 2)
      = ∏ j : Fin i, (∑ b : Bool, ‖(cellFinalAmp V x (Fin.castLE hi j)) b‖ ^ 2) :=
        cellPrefixMass hi V x
    _ = ∏ j : Fin i, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact cellFinalAmp_mass V hV x (Fin.castLE hi j)
    _ = 1 := by simp

/-- When the input fits in the window, the initialized tape at a tour position contains its
corresponding input bit. -/
theorem allCellTourPos_tape_init {n k w : ℕ} (M : LocalQTM (AllCellState n k) Bool)
    (nn : ℕ) (x : Reg nn) (i : ℕ) (hi : i < nn) (hw : nn ≤ w) :
    (initWindowCfg (t := w) M nn x).tape (allCellTourPos i hi hw) = x ⟨i, hi⟩ := by
  have h1 : w < w + 1 + i := by omega
  have h2 : w + 1 + i ≤ w + nn := by omega
  have h3 : w + 1 + i - w - 1 = i := by omega
  simp [initWindowCfg, allCellTourPos, h1, h2, h3]

/-- A gate step from a tour basis configuration is the two-symbol successor superposition at the
next gate stage, with the processed prefix fixed. -/
theorem allCellTour_step_gate {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (hj : j.val < k)
    (f : Fin i → Bool) (b : Bool) :
    (windowStep (t := w) (allCellLocalQTM hn V hV))
        *ᵥ Ket (allCellTourCfg base i hi hw j f b)
      = (allCellAmp V (.serve ⟨i, hi⟩ j) b false)
          • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f false)
        + (allCellAmp V (.serve ⟨i, hi⟩ j) b true)
          • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f true) := by
  classical
  have hsrc : (allCellTourCfg base i hi hw j f b).tape
      (allCellTourCfg base i hi hw j f b).head = b :=
    allCellTourCfg_tape_at base i hi hw j f b
  have hmove : moveCell (allCellMove (allCellTourCfg base i hi hw j f b).state)
      (allCellTourCfg base i hi hw j f b).head = some (allCellTourPos i hi hw) := by
    rw [allCellTourCfg_state, allCellTourCfg_head]
    have hmv : allCellMove (.serve ⟨i, hi⟩ j) = QtmMove.stay := by
      simp [allCellMove, hj]
    rw [hmv]
    simp [moveCell]
  rw [allCellLocalQTM_step_ket hn V hV (allCellTourCfg base i hi hw j f b) b
    (allCellTourPos i hi hw) hmove hsrc]
  have hsucc (b' : Bool) :
      allCellSuccCfg hn (allCellTourCfg base i hi hw j f b) b b' (allCellTourPos i hi hw)
        = allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f b' := by
    have hstate : allCellNext hn (.serve ⟨i, hi⟩ j) b
        = (.serve ⟨i, hi⟩ ⟨j.val + 1, by omega⟩ : AllCellState n k) := by
      simp [allCellNext, hj]
    have hhead : (allCellTourCfg base i hi hw j f b).head = allCellTourPos i hi hw :=
      allCellTourCfg_head base i hi hw j f b
    unfold allCellSuccCfg
    rw [allCellTourCfg_state, hhead]
    simp only [allCellTourCfg]
    refine (WindowCfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, hstate, ?_⟩
    funext m
    by_cases hm : m = allCellTourPos i hi hw
    · simp [hm]
    · simp [hm]
  rw [hsucc false, hsucc true]
  rw [allCellTourCfg_state]

/-- With the input encoded in the base tape, a nonfinal cell's advance step extends the
processed prefix and starts the next cell on its input bit. -/
theorem allCellTour_step_advance {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n)
    (i : ℕ) (hi : i < n) (hnext : i + 1 < n) (hw : n ≤ w)
    (f : Fin i → Bool) (b : Bool)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c) :
    (windowStep (t := w) (allCellLocalQTM hn V hV))
        *ᵥ Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)
      = (allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b false)
          • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
              (Fin.extendLast f false) (x ⟨i + 1, hnext⟩))
        + (allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b true)
          • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
              (Fin.extendLast f true) (x ⟨i + 1, hnext⟩)) := by
  classical
  have hsrc := allCellTourCfg_tape_at base i hi hw (allCellTourLayerK k) f b
  have hmove : moveCell (allCellMove (allCellTourCfg base i hi hw (allCellTourLayerK k) f b).state)
      (allCellTourCfg base i hi hw (allCellTourLayerK k) f b).head
      = some (allCellTourPosNext i hnext hw) := by
    rw [allCellTourCfg_state, allCellTourCfg_head]
    have hmv : allCellMove (.serve ⟨i, hi⟩ (allCellTourLayerK k)) = QtmMove.right := by
      simp [allCellMove, hnext, allCellTourLayerK]
    rw [hmv]
    have hval : (allCellTourPos i hi hw).val ≠ 2 * w := by
      rw [allCellTourPos_val]
      omega
    simp only [moveCell, dif_neg hval]
    congr 1
    apply Fin.ext
    show (allCellTourPos i hi hw).val + 1 = (allCellTourPosNext i hnext hw).val
    rw [allCellTourPos_val, allCellTourPosNext_val]
    omega
  rw [allCellLocalQTM_step_ket hn V hV
    (allCellTourCfg base i hi hw (allCellTourLayerK k) f b) b
    (allCellTourPosNext i hnext hw) hmove hsrc]
  have hstate : allCellNext hn (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b
      = (.serve ⟨i + 1, hnext⟩ (allCellTourLayer0 k) : AllCellState n k) := by
    simp [allCellNext, hnext, allCellTourLayerK, allCellTourLayer0]
  have hhead : (allCellTourCfg base i hi hw (allCellTourLayerK k) f b).head
      = allCellTourPos i hi hw :=
    allCellTourCfg_head base i hi hw (allCellTourLayerK k) f b
  have hsucc (b' : Bool) :
      allCellSuccCfg hn (allCellTourCfg base i hi hw (allCellTourLayerK k) f b) b b'
          (allCellTourPosNext i hnext hw)
        = allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
            (Fin.extendLast f b') (x ⟨i + 1, hnext⟩) := by
    unfold allCellSuccCfg
    rw [allCellTourCfg_state, hhead]
    refine (WindowCfg.mk.injEq _ _ _ _ _ _).mpr ⟨?_, hstate, ?_⟩
    · rw [allCellTourPosNext_eq]
    · simp only [allCellTourCfg_tape]
      funext m
      rw [allCellTourTape_extend base i f b' m]
      by_cases hmval : m.val = w + 1 + i
      · have hm : m = allCellTourPos i hi hw := allCellTourPos_eq_of_val i hi hw m hmval
        have hm2 : m ≠ allCellTourPos (i + 1) hnext hw := by
          intro hcon
          have heq : allCellTourPos i hi hw = allCellTourPos (i + 1) hnext hw := by
            rw [← hm, hcon]
          have hval2 := congrArg Fin.val heq
          simp only [allCellTourPos_val] at hval2
          omega
        rw [if_pos hm, if_neg hm2, if_pos hmval]
      · have hm : m ≠ allCellTourPos i hi hw := by
          intro hcon
          apply hmval
          rw [hcon, allCellTourPos_val]
        by_cases hm2 : m = allCellTourPos (i + 1) hnext hw
        · rw [if_neg hm, if_neg hm, if_pos hm2]
          rw [hm2]
          rw [allCellTourTape_at_next base i hnext hw f]
          rw [← hx ⟨i + 1, hnext⟩]
        · rw [if_neg hm, if_neg hm, if_neg hm2, if_neg hmval]
  rw [hsucc false, hsucc true]
  rw [allCellTourCfg_state]

/-- At the final cell, one step from the last gate stage gives the two final configuration
branches weighted by their local amplitudes. -/
theorem allCellTour_step_measure {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hlast : i + 1 = n) (hw : n ≤ w)
    (f : Fin i → Bool) (b : Bool) :
    (windowStep (t := w) (allCellLocalQTM hn V hV))
        *ᵥ Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)
      = (allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b false)
          • Ket (allCellTourFinalCfg base i hi hw f b false)
        + (allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b true)
          • Ket (allCellTourFinalCfg base i hi hw f b true) := by
  classical
  have hsrc := allCellTourCfg_tape_at base i hi hw (allCellTourLayerK k) f b
  have hmove : moveCell (allCellMove (allCellTourCfg base i hi hw (allCellTourLayerK k) f b).state)
      (allCellTourCfg base i hi hw (allCellTourLayerK k) f b).head
      = some (allCellTourPos i hi hw) := by
    rw [allCellTourCfg_state, allCellTourCfg_head]
    have hmv : allCellMove (.serve ⟨i, hi⟩ (allCellTourLayerK k)) = QtmMove.stay := by
      simp [allCellMove, hlast, allCellTourLayerK]
    rw [hmv]
    simp [moveCell]
  rw [allCellLocalQTM_step_ket hn V hV
    (allCellTourCfg base i hi hw (allCellTourLayerK k) f b) b
    (allCellTourPos i hi hw) hmove hsrc]
  have hstate : allCellNext hn (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b
      = (if b then (.acc : AllCellState n k) else .rej) := by
    simp [allCellNext, hlast, allCellTourLayerK]
  have hhead : (allCellTourCfg base i hi hw (allCellTourLayerK k) f b).head
      = allCellTourPos i hi hw :=
    allCellTourCfg_head base i hi hw (allCellTourLayerK k) f b
  have hsucc (b' : Bool) :
      allCellSuccCfg hn (allCellTourCfg base i hi hw (allCellTourLayerK k) f b) b b'
          (allCellTourPos i hi hw)
        = allCellTourFinalCfg base i hi hw f b b' := by
    unfold allCellSuccCfg
    rw [allCellTourCfg_state, hhead]
    simp only [allCellTourFinalCfg]
    refine (WindowCfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, hstate, ?_⟩
    funext m
    rw [allCellTourCfg_tape]
    by_cases hm : m = allCellTourPos i hi hw
    · simp [hm]
    · simp [hm]
  rw [hsucc false, hsucc true]
  rw [allCellTourCfg_state]

/-- Complex matrix-vector multiplication commutes with a sum over a finite subset of its column
index type. -/
theorem mulVec_sum {ι β : Type*} [Fintype ι] (s : Finset ι) (M : Matrix β ι ℂ)
    (f : ι → (ι → ℂ)) :
    M *ᵥ (s.sum f) = s.sum (fun i => M *ᵥ (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Matrix.mulVec_add, ih]

/-- The Boolean amplitude vector after the first `j.val` gates at a cell, starting from its
input basis bit. -/
noncomputable def cellPartialAmp {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (x : Reg n) (i : Fin n) (j : Fin (k + 1)) : Bool → ℂ :=
  gateSeqProd (fun l : Fin k => V i l) j.val (by omega) *ᵥ
    (fun c => if c = x i then (1 : ℂ) else 0)

/-- Advancing a cell's partial amplitude vector by one stage applies its next unitary matrix. -/
theorem cellPartialAmp_step {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (x : Reg n) (i : Fin n) (j : Fin (k + 1)) (hj : j.val < k) :
    cellPartialAmp V x i ⟨j.val + 1, by omega⟩ = V i ⟨j.val, hj⟩ *ᵥ cellPartialAmp V x i j := by
  have hprod : gateSeqProd (fun l : Fin k => V i l) (j.val + 1) (by omega)
      = V i ⟨j.val, hj⟩ * gateSeqProd (fun l : Fin k => V i l) j.val (by omega) := rfl
  simp only [cellPartialAmp]
  rw [hprod]
  rw [← Matrix.mulVec_mulVec]

/-- The product of completed-cell amplitudes along a prefix and the current cell's partial
amplitude. -/
noncomputable def allCellTourAmp {n k i : ℕ} (hi : i < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (j : Fin (k + 1)) (f : Fin i → Bool) (b : Bool) : ℂ :=
  (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j')) *
    (cellPartialAmp V x ⟨i, hi⟩ j b)

/-- The tour superposition over processed-prefix assignments and the current cell bit, weighted
by `allCellTourAmp`. -/
noncomputable def allCellTourState {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1))
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n) :
    QState (WindowCfg w (AllCellState n k) Bool) :=
  ∑ f : Fin i → Bool, ∑ b : Bool,
    (allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b)

/-- Complex matrix-vector multiplication commutes with a finite sum of state vectors. -/
theorem mulVec_sum_state {m n ι : Type*} [Fintype n] [Fintype ι] (M : Matrix m n ℂ)
    (f : ι → (n → ℂ)) :
    M *ᵥ (Finset.univ.sum f) = Finset.univ.sum (fun i => M *ᵥ (f i)) := by
  classical
  have h : ∀ (s : Finset ι), M *ᵥ (s.sum f) = s.sum (fun i => M *ᵥ (f i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Matrix.mulVec_zero]
        simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, Matrix.mulVec_add, ih]
  simpa using! h (Finset.univ : Finset ι)

/-- Summing Boolean-indexed scalar multiples of a fixed state equals multiplication by the sum
of their scalars. -/
theorem sum_smul_state {β : Type*} (c : Bool → ℂ) (w : β → ℂ) :
    (∑ b : Bool, c b • w) = (∑ b : Bool, c b) • w := by
  funext i
  simp only [Fintype.sum_bool, Pi.add_apply, Pi.smul_apply]
  ring

/-- A Boolean sum of two-branch superpositions groups into the two successor states with summed
coefficients. -/
theorem tour_successor_sum {β : Type*} (c c' : Bool → ℂ) (w0 w1 : β → ℂ) :
    (∑ b : Bool, ((c b) • w0 + (c' b) • w1))
      = (∑ b : Bool, c b) • w0 + (∑ b : Bool, c' b) • w1 := by
  simp only [Finset.sum_add_distrib, sum_smul_state]

/-- During a proper gate stage, the all-cell serve amplitude is the corresponding entry of the
designated cell gate. -/
theorem allCellAmp_serve_gate {n k : ℕ} (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (i : Fin n) (j : Fin (k + 1)) (hj : j.val < k) (a b : Bool) :
    allCellAmp V (.serve i j) a b = V i ⟨j.val, hj⟩ b a := by
  simp [allCellAmp, hj]

/-- Summing tour amplitudes against the current gate transition yields the tour amplitude at the
next gate stage. -/
theorem allCellTourAmp_gate_step {n k i : ℕ} (hi : i < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (j : Fin (k + 1)) (hj : j.val < k) (f : Fin i → Bool) (b' : Bool) :
    (∑ b : Bool, allCellTourAmp hi V x j f b * allCellAmp V (.serve ⟨i, hi⟩ j) b b')
      = allCellTourAmp hi V x ⟨j.val + 1, by omega⟩ f b' := by
  have hstep : cellPartialAmp V x ⟨i, hi⟩ ⟨j.val + 1, by omega⟩
      = V ⟨i, hi⟩ ⟨j.val, hj⟩ *ᵥ cellPartialAmp V x ⟨i, hi⟩ j :=
    cellPartialAmp_step V x ⟨i, hi⟩ j hj
  simp only [allCellAmp_serve_gate V ⟨i, hi⟩ j hj, allCellTourAmp]
  calc (∑ b : Bool, (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j'))
        * (cellPartialAmp V x ⟨i, hi⟩ j b)
        * (V ⟨i, hi⟩ ⟨j.val, hj⟩ b' b))
      = ∑ b : Bool, (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j'))
        * ((cellPartialAmp V x ⟨i, hi⟩ j b) * (V ⟨i, hi⟩ ⟨j.val, hj⟩ b' b)) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ = (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j'))
        * (∑ b : Bool, (cellPartialAmp V x ⟨i, hi⟩ j b) * (V ⟨i, hi⟩ ⟨j.val, hj⟩ b' b)) := by
          rw [Finset.mul_sum]
    _ = (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j'))
        * ((V ⟨i, hi⟩ ⟨j.val, hj⟩ *ᵥ cellPartialAmp V x ⟨i, hi⟩ j) b') := by
          congr 1
          simp [Matrix.mulVec, dotProduct]
          all_goals ac_rfl
    _ = (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j'))
        * (cellPartialAmp V x ⟨i, hi⟩ ⟨j.val + 1, by omega⟩ b') := by
          rw [hstep]

/-- One all-cell machine step advances a tour state by one gate stage below `k`. -/
theorem allCellTourState_step_gate {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (j : Fin (k + 1)) (hj : j.val < k)
    (x : Reg n) :
    (windowStep (t := w) (allCellLocalQTM hn V hV))
        *ᵥ allCellTourState base i hi hw j V x
      = allCellTourState base i hi hw ⟨j.val + 1, by omega⟩ V x := by
  classical
  have hbranch (f : Fin i → Bool) (b : Bool) :
      (windowStep (t := w) (allCellLocalQTM hn V hV))
          *ᵥ (allCellTourAmp hi V x j f b • Ket (allCellTourCfg base i hi hw j f b))
        = (allCellTourAmp hi V x j f b * allCellAmp V (.serve ⟨i, hi⟩ j) b false)
            • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f false) +
          (allCellTourAmp hi V x j f b * allCellAmp V (.serve ⟨i, hi⟩ j) b true)
            • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f true) := by
    rw [Matrix.mulVec_smul]
    rw [allCellTour_step_gate hn V hV base i hi hw j hj f b]
    funext tgtC
    simp only [Pi.smul_apply, Pi.add_apply]
    ring
  have hinner (f : Fin i → Bool) :
      (∑ b : Bool,
          ((allCellTourAmp hi V x j f b * allCellAmp V (.serve ⟨i, hi⟩ j) b false)
              • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f false)
            + (allCellTourAmp hi V x j f b * allCellAmp V (.serve ⟨i, hi⟩ j) b true)
              • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f true)))
        = ∑ b : Bool, (allCellTourAmp hi V x ⟨j.val + 1, by omega⟩ f b)
              • Ket (allCellTourCfg base i hi hw ⟨j.val + 1, by omega⟩ f b) := by
    rw [tour_successor_sum]
    rw [allCellTourAmp_gate_step hi V x j hj f false]
    rw [allCellTourAmp_gate_step hi V x j hj f true]
    rw [Fintype.sum_bool]
    exact add_comm _ _
  have hdist :
      (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
          (Finset.univ.sum (fun f : Fin i → Bool =>
            Finset.univ.sum (fun b : Bool =>
              (allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b))))
        = Finset.univ.sum (fun f : Fin i → Bool =>
            (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
              (Finset.univ.sum (fun b : Bool =>
                (allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b)))) := by
    exact mulVec_sum_state _
      (fun f : Fin i → Bool => Finset.univ.sum (fun b : Bool =>
        (allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b)))
  have hdist2 :
      Finset.univ.sum (fun f : Fin i → Bool =>
            (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
              (Finset.univ.sum (fun b : Bool =>
                (allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b))))
        = Finset.univ.sum (fun f : Fin i → Bool =>
            Finset.univ.sum (fun b : Bool =>
              (windowStep (t := w) (allCellLocalQTM hn V hV))
                *ᵥ ((allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b)))) := by
    apply Finset.sum_congr rfl
    intro f _
    exact mulVec_sum_state _
      (fun b => (allCellTourAmp hi V x j f b) • Ket (allCellTourCfg base i hi hw j f b))
  simp only [allCellTourState]
  rw [hdist]
  rw [hdist2]
  simp_rw [hbranch]
  simp_rw [hinner]

/-- With the input encoded in the base tape, a step after a nonfinal cell's full gate sequence
gives the next cell's stage-zero tour state. -/
theorem allCellTourState_step_advance {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n)
    (i : ℕ) (hi : i < n) (hnext : i + 1 < n) (hw : n ≤ w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c) :
    (windowStep (t := w) (allCellLocalQTM hn V hV))
        *ᵥ allCellTourState base i hi hw (allCellTourLayerK k) V x
      = allCellTourState base (i + 1) hnext hw (allCellTourLayer0 k) V x := by
  classical
  have hampFF : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) false false = 1 := by
    simp [allCellAmp, allCellTourLayerK, hnext]
  have hampFT : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) false true = 0 := by
    simp [allCellAmp, allCellTourLayerK, hnext]
  have hampTF : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) true false = 0 := by
    simp [allCellAmp, allCellTourLayerK, hnext]
  have hampTT : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) true true = 1 := by
    simp [allCellAmp, allCellTourLayerK, hnext]

  have hbranch (f : Fin i → Bool) (b : Bool) :
      (windowStep (t := w) (allCellLocalQTM hn V hV))
          *ᵥ (allCellTourAmp hi V x (allCellTourLayerK k) f b
              • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))
        = (allCellTourAmp hi V x (allCellTourLayerK k) f b
            * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b false)
            • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                (Fin.extendLast f false) (x ⟨i + 1, hnext⟩)) +
          (allCellTourAmp hi V x (allCellTourLayerK k) f b
            * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b true)
            • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                (Fin.extendLast f true) (x ⟨i + 1, hnext⟩)) := by
    rw [Matrix.mulVec_smul]
    rw [allCellTour_step_advance hn V hV base x i hi hnext hw f b hx]
    funext tgtC
    simp only [Pi.smul_apply, Pi.add_apply]
    ring

  have hsum (f : Fin i → Bool) :
      (∑ b : Bool,
          ((allCellTourAmp hi V x (allCellTourLayerK k) f b
                * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b false)
              • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                  (Fin.extendLast f false) (x ⟨i + 1, hnext⟩)) +
            (allCellTourAmp hi V x (allCellTourLayerK k) f b
                * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b true)
              • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                  (Fin.extendLast f true) (x ⟨i + 1, hnext⟩))))
        = ∑ b' : Bool, (allCellTourAmp hi V x (allCellTourLayerK k) f b')
              • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                  (Fin.extendLast f b') (x ⟨i + 1, hnext⟩)) := by
    simp only [Fintype.sum_bool]
    rw [hampFF, hampFT, hampTF, hampTT]
    simp only [mul_zero, mul_one, zero_smul, add_zero, zero_add]

  have hreindex :
      (∑ f : Fin i → Bool, ∑ b : Bool,
          (allCellTourAmp hi V x (allCellTourLayerK k) f b)
            • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                (Fin.extendLast f b) (x ⟨i + 1, hnext⟩)))
        = ∑ f' : Fin (i + 1) → Bool,
            (allCellTourAmp hi V x (allCellTourLayerK k)
                ((allCellPrefixSuccEquiv i).symm f').1
                ((allCellPrefixSuccEquiv i).symm f').2)
            • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
                (Fin.extendLast ((allCellPrefixSuccEquiv i).symm f').1
                    ((allCellPrefixSuccEquiv i).symm f').2)
                (x ⟨i + 1, hnext⟩)) := by
    rw [fin_sum_extendLast_state
      (S := QState (WindowCfg w (AllCellState n k) Bool))
      (A := fun f b =>
        (allCellTourAmp hi V x (allCellTourLayerK k) f b)
          • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k)
              (Fin.extendLast f b) (x ⟨i + 1, hnext⟩)))]

  have hcs (j : Fin i) : Fin.castSucc j = (⟨j.val, by omega⟩ : Fin (i + 1)) := by
    apply Fin.ext
    rfl
  have hlast : Fin.last i = (⟨i, by omega⟩ : Fin (i + 1)) := by
    apply Fin.ext
    rfl
  have hcast {n m : ℕ} (h : n ≤ m) (a : Fin n) :
      Fin.castLE h a = (⟨a.val, by omega⟩ : Fin m) := by
    apply Fin.ext
    rfl
  have epre (f' : Fin (i + 1) → Bool) (j : Fin i) :
      ((allCellPrefixSuccEquiv i).symm f').1 j = f' (⟨j.val, by omega⟩ : Fin (i + 1)) := by
    rfl
  have elast (f' : Fin (i + 1) → Bool) :
      ((allCellPrefixSuccEquiv i).symm f').2 = f' (⟨i, by omega⟩ : Fin (i + 1)) := by
    rfl
  have hextend (f' : Fin (i + 1) → Bool) :
      Fin.extendLast ((allCellPrefixSuccEquiv i).symm f').1 ((allCellPrefixSuccEquiv i).symm f').2
        = f' := by
    exact Equiv.apply_symm_apply (allCellPrefixSuccEquiv i) f'
  have hprod (f' : Fin (i + 1) → Bool) :
      (∏ j' : Fin i, (cellFinalAmp V x (Fin.castLE (show i ≤ n by omega) j'))
            (((allCellPrefixSuccEquiv i).symm f').1 j'))
        * (cellFinalAmp V x ⟨i, hi⟩ ((allCellPrefixSuccEquiv i).symm f').2)
      = ∏ j'' : Fin (i + 1), (cellFinalAmp V x (Fin.castLE (show i + 1 ≤ n by omega) j'')) (f' j'') := by
    rw [Fin.prod_univ_castSucc (fun j'' : Fin (i + 1) =>
      (cellFinalAmp V x (Fin.castLE (show i + 1 ≤ n by omega) j'')) (f' j''))]
    simp only [epre f', elast f', hcs, hlast, hcast]
  have hampid' (f' : Fin (i + 1) → Bool) :
      allCellTourAmp hnext V x (allCellTourLayer0 k) f' (x ⟨i + 1, hnext⟩)
        = allCellTourAmp hi V x (allCellTourLayerK k)
          ((allCellPrefixSuccEquiv i).symm f').1 ((allCellPrefixSuccEquiv i).symm f').2 := by
    have hfin (b : Bool) :
        cellPartialAmp V x ⟨i, hi⟩ (allCellTourLayerK k) b = cellFinalAmp V x ⟨i, hi⟩ b := by
      rfl
    have hzero :
        cellPartialAmp V x ⟨i + 1, hnext⟩ (allCellTourLayer0 k) (x ⟨i + 1, hnext⟩) = 1 := by
      simp [cellPartialAmp, allCellTourLayer0, gateSeqProd, Matrix.one_mulVec]
    simp only [allCellTourAmp]
    rw [hzero, hfin]
    rw [hprod f']
    simp only [mul_one]
  have hampid (f' : Fin (i + 1) → Bool) :
      allCellTourAmp hi V x (allCellTourLayerK k)
          ((allCellPrefixSuccEquiv i).symm f').1 ((allCellPrefixSuccEquiv i).symm f').2
        = allCellTourAmp hnext V x (allCellTourLayer0 k) f' (x ⟨i + 1, hnext⟩) :=
    (hampid' f').symm

  have hpart (b' : Bool) :
      cellPartialAmp V x ⟨i + 1, hnext⟩ (allCellTourLayer0 k) b'
        = (if b' = x ⟨i + 1, hnext⟩ then (1 : ℂ) else 0) := by
    simp [cellPartialAmp, allCellTourLayer0, gateSeqProd, Matrix.one_mulVec]
  have hcoll (f' : Fin (i + 1) → Bool) :
      (∑ b' : Bool, (allCellTourAmp hnext V x (allCellTourLayer0 k) f' b')
            • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k) f' b'))
        = (allCellTourAmp hnext V x (allCellTourLayer0 k) f' (x ⟨i + 1, hnext⟩))
          • Ket (allCellTourCfg base (i + 1) hnext hw (allCellTourLayer0 k) f' (x ⟨i + 1, hnext⟩)) := by
    simp only [allCellTourAmp, hpart]
    rw [Fintype.sum_bool]
    cases hx' : x ⟨i + 1, hnext⟩ <;>
      simp [mul_zero, mul_one, zero_smul, add_zero, zero_add]

  have hdist :
      (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
          (Finset.univ.sum (fun f : Fin i → Bool => Finset.univ.sum (fun b : Bool =>
            (allCellTourAmp hi V x (allCellTourLayerK k) f b)
              • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))))
        = Finset.univ.sum (fun f : Fin i → Bool =>
            (windowStep (t := w) (allCellLocalQTM hn V hV))
              *ᵥ (Finset.univ.sum (fun b : Bool =>
                (allCellTourAmp hi V x (allCellTourLayerK k) f b)
                  • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)))) := by
    exact mulVec_sum_state _
      (fun f : Fin i → Bool => Finset.univ.sum (fun b : Bool =>
        (allCellTourAmp hi V x (allCellTourLayerK k) f b)
          • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)))
  have hdist2 :
      Finset.univ.sum (fun f : Fin i → Bool =>
            (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
              (Finset.univ.sum (fun b : Bool =>
                (allCellTourAmp hi V x (allCellTourLayerK k) f b)
                  • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))))
        = Finset.univ.sum (fun f : Fin i → Bool =>
            Finset.univ.sum (fun b : Bool =>
              (windowStep (t := w) (allCellLocalQTM hn V hV))
                *ᵥ ((allCellTourAmp hi V x (allCellTourLayerK k) f b)
                  • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)))) := by
    apply Finset.sum_congr rfl
    intro f _
    exact mulVec_sum_state _
      (fun b => (allCellTourAmp hi V x (allCellTourLayerK k) f b)
        • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))
  simp only [allCellTourState]
  rw [hdist]
  rw [hdist2]
  simp_rw [hbranch]
  simp_rw [hsum]
  rw [hreindex]
  simp_rw [hextend]
  simp_rw [hampid]
  simp_rw [hcoll]

/-- For a centered base head and correctly encoded input, the start step reaches the first
cell's stage-zero basis configuration. -/
theorem allCellTour_start_ket {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ Ket (allCellStartCfg base)
      = Ket (allCellTourCfg base 0 hn hw (allCellTourLayer0 k) (fun _ => false) (x ⟨0, hn⟩)) := by
  have hstart := allCellLocalQTM_startStep_ket hn V hV base (allCellTourPos 0 hn hw)
    (by rw [allCellTourPos_val]; omega)
  rw [hstart]
  have heq : allCellStartStepCfg hn base (allCellTourPos 0 hn hw)
      = allCellTourCfg base 0 hn hw (allCellTourLayer0 k) (fun _ => false) (x ⟨0, hn⟩) := by
    simp only [allCellStartStepCfg, allCellTourCfg]
    congr
    funext m
    by_cases hm : m = allCellTourPos 0 hn hw
    · subst hm
      have hx0 := hx ⟨0, hn⟩
      rw [if_pos rfl]
      simpa using! hx0
    · rw [if_neg hm]
      simp only [allCellTourTape]
      split
      · rename_i h
        omega
      · rfl
  rw [heq]

/-- Collects the five local conditions for general native machines, their query-free window
simulation with the stated quadratic gate bound and Born-probability agreement, bounded
address-word correctness, and well-formedness of the gate and layered machines. -/
theorem clause7_complete :
    (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (M : GeneralNativeMachine Q A), LocalQTMFiveConditions M.localQTM) ∧
    (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (M : GeneralNativeMachine Q A) (n t : ℕ), 0 < n → 0 < t →
      ∃ C : Circuit (WReg (generalWindowSize n t) Q A),
        IsUnitaryCircuit C ∧ QueryCount C = 0 ∧
          GateCount C ≤ 2 * generalWindowSize n t * generalWindowSize n t ∧
          (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
            Run (1 : Matrix (WReg (generalWindowSize n t) Q A)
              (WReg (generalWindowSize n t) Q A) ℂ) C
                (Ket (windowEncode (initWindowCfg M.localQTM n x)))
              = windowEmbed ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
                Ket (initWindowCfg M.localQTM n x)) ∧
            BornProb (Run (1 : Matrix (WReg (generalWindowSize n t) Q A)
              (WReg (generalWindowSize n t) Q A) ℂ) C
                (Ket (windowEncode (initWindowCfg M.localQTM n x)))) (windowEncode c)
              = BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
                Ket (initWindowCfg M.localQTM n x)) c)) ∧
    (∀ (n : ℕ) (w : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord n) (x : Reg (n + (n - 1))),
      (∀ a : Fin (n - 1), x (ancWire n a) = false) →
      ∀ (wi : Fin n),
        (BoundedGate.run (addrWordBounded w) x) (addrWire (n - 1) wi)
          = (Qatlib.Concepts.UniformBqp.Phi3Compile.AddrWord.eval w (fun w => x (addrWire (n - 1) w))) wi) ∧
    (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
      (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ),
      LocalQTMFiveConditions (layerLocalQTM Us hU)) ∧
    (∀ (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ),
      LocalQTMFiveConditions (gateLocalQTM U hU)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Q A instQ instDecQ instA instDecA M
    exact M.fiveConditions
  · intro Q A instQ instDecQ instA instDecA M n t hn ht
    exact generalTheorem2_window M n t hn ht
  · intro n w x hanc wi
    exact addrWordBounded_run w x hanc wi
  · intro k Us hU
    exact layerLocalQTM_five Us hU
  · intro U hU
    exact gateLocalQTM_five U hU

/-- When the input fits in the window, the machine targeting cell zero has accepting mass after
`k+2` steps equal to the standard acceptance probability of the first-wire circuit. -/
theorem headStay_cell_acceptProb_zero {n k w : ℕ}
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (hn : 0 < n)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (hw : n ≤ w) (x : Reg n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : CellState n k 0)),
      BornProb ((windowStep (t := w) (cellLocalQTM V (n := n) (tgt := 0) hn hV)) ^ (k + 2)
        *ᵥ Ket (initWindowCfg (t := w) (cellLocalQTM V (n := n) (tgt := 0) hn hV) n x)) c)
      = AcceptProb
          ((Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (((List.ofFn (V ⟨0, hn⟩)).map (fun U => embedRegI ⟨0, hn⟩ U)).map Step.gate))
            (Ket x)) hn := by
  have h := headStay_cell_acceptProb_multi V (n := n) (tgt := 0) hn hV hw x
  have hp : 0 + k + 2 = k + 2 := by omega
  rw [hp] at h
  rw [h]
  have hz := acceptProbAt_zero hn
    ((Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (((List.ofFn (V ⟨0, hn⟩)).map (fun U => embedRegI ⟨0, hn⟩ U)).map Step.gate))
        (Ket x))
  exact hz

/-- Multiplication by a product of two powers of a matrix equals successive multiplication by
those powers. -/
theorem mulVec_pow_mul {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (x y : ℕ)
    (v : m → ℂ) :
    ((M ^ x) * (M ^ y)) *ᵥ v = (M ^ x) *ᵥ ((M ^ y) *ᵥ v) :=
  (Matrix.mulVec_mulVec v (M ^ x) (M ^ y)).symm

/-- Applying the `b`th and then the `a`th matrix power equals applying the `(a+b)`th power. -/
theorem mulVec_pow_add {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (a b : ℕ)
    (v : m → ℂ) :
    (M ^ a) *ᵥ ((M ^ b) *ᵥ v) = (M ^ (a + b)) *ᵥ v := by
  calc (M ^ a) *ᵥ ((M ^ b) *ᵥ v) = ((M ^ a) * (M ^ b)) *ᵥ v :=
        Matrix.mulVec_mulVec v (M ^ a) (M ^ b)
    _ = (M ^ (a + b)) *ᵥ v := by rw [pow_add]

/-- A sum over Boolean functions on `Fin 0` equals its value at the unique empty function. -/
theorem sum_fin0_bool {M : Type*} [AddCommMonoid M] (f : (Fin 0 → Bool) → M) :
    (∑ g : Fin 0 → Bool, f g) = f (fun _ => false) := by
  rw [Fintype.sum_eq_single (fun _ => false)]
  intro b hb
  exfalso
  apply hb
  funext j
  exact Fin.elim0 j

/-- At the first cell's stage zero, the tour amplitude is just the first cell's partial
amplitude because the processed prefix is empty. -/
theorem allCellTourAmp_zero {n k : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (f : Fin 0 → Bool) (b : Bool) :
    allCellTourAmp hn V x (allCellTourLayer0 k) f b
      = cellPartialAmp V x ⟨0, hn⟩ (allCellTourLayer0 k) b := by
  simp only [allCellTourAmp]
  have hprod : (∏ j' : Fin 0, (cellFinalAmp V x (Fin.castLE (by omega) j')) (f j')) = 1 := by
    simp
  rw [hprod, one_mul]

/-- The first cell's stage-zero tour state reduces to a Boolean sum with coefficients given by
its partial amplitude vector. -/
theorem allCellTourState_zero {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w) :
    allCellTourState base 0 hn hw (allCellTourLayer0 k) V x
      = ∑ b : Bool, (cellPartialAmp V x ⟨0, hn⟩ (allCellTourLayer0 k) b) •
          Ket (allCellTourCfg base 0 hn hw (allCellTourLayer0 k) (fun _ => false) b) := by
  simp only [allCellTourState]
  rw [sum_fin0_bool]
  apply Finset.sum_congr rfl
  intro b _
  rw [allCellTourAmp_zero hn V x (fun _ => false) b]

/-- The first cell's stage-zero tour state is the basis ket with the first input bit and empty
processed prefix. -/
theorem allCellTourState_zero_collapse {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w) :
    allCellTourState base 0 hn hw (allCellTourLayer0 k) V x
      = Ket (allCellTourCfg base 0 hn hw (allCellTourLayer0 k) (fun _ => false) (x ⟨0, hn⟩)) := by
  rw [allCellTourState_zero hn V base x hw]
  have hpart (b' : Bool) :
      cellPartialAmp V x ⟨0, hn⟩ (allCellTourLayer0 k) b'
        = (if b' = x ⟨0, hn⟩ then (1 : ℂ) else 0) := by
    simp [cellPartialAmp, allCellTourLayer0, gateSeqProd, Matrix.one_mulVec]
  simp only [hpart]
  rw [Fintype.sum_bool]
  cases hx : x ⟨0, hn⟩ <;>
    simp [mul_zero, mul_one, zero_smul, add_zero, zero_add]

/-- For a centered base head and correctly encoded input, one start step gives the first cell's
stage-zero tour state. -/
theorem allCellTour_start_state {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ Ket (allCellStartCfg base)
      = allCellTourState base 0 hn hw (allCellTourLayer0 k) V x := by
  rw [allCellTour_start_ket hn V hV base x hw hhead hx]
  exact (allCellTourState_zero_collapse hn V base x hw).symm

/-- Evolving a cell's stage-zero tour state for `j ≤ k` steps gives its stage-`j` tour state. -/
theorem allCellTourState_layers {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) :
    ∀ (j : ℕ) (hj : j ≤ k),
      (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ j *ᵥ
          allCellTourState base i hi hw (allCellTourLayer0 k) V x
        = allCellTourState base i hi hw ⟨j, by omega⟩ V x := by
  intro j
  induction j with
  | zero =>
      intro hj
      have hz : (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ 0 *ᵥ
          allCellTourState base i hi hw (allCellTourLayer0 k) V x
        = allCellTourState base i hi hw (allCellTourLayer0 k) V x := by
        simp
      rw [hz]
      rfl
  | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hjlt : j < k + 1 := by omega
      have ih' := ih (by omega)
      have hstep := allCellTourState_step_gate hn V hV base i hi hw ⟨j, hjlt⟩ hjk x
      calc (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (j + 1) *ᵥ
            allCellTourState base i hi hw (allCellTourLayer0 k) V x
          = (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
            ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ j *ᵥ
              allCellTourState base i hi hw (allCellTourLayer0 k) V x) := by
              rw [pow_succ', ← Matrix.mulVec_mulVec]
        _ = (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
            allCellTourState base i hi hw ⟨j, hjlt⟩ V x := by rw [ih']
        _ = allCellTourState base i hi hw ⟨j + 1, by omega⟩ V x := hstep

/-- For a centered base head and correctly encoded input fitting in the window, the tour reaches
cell `i` at stage zero after `1+i*(k+1)` steps. -/
theorem allCellTour_reach {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c) :
    ∀ (i : ℕ) (hi : i < n),
      (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (1 + i * (k + 1)) *ᵥ
          Ket (allCellStartCfg base)
        = allCellTourState base i hi hw (allCellTourLayer0 k) V x := by
  intro i
  induction i with
  | zero =>
      intro hi
      have h := allCellTour_start_state hn V hV base x hw hhead hx
      have hpow : 1 + 0 * (k + 1) = 1 := by ring
      rw [hpow]
      simp only [pow_one]
      exact h
  | succ i ih =>
      intro hi
      have hih : i < n := by omega
      have hinext : i + 1 < n := by omega
      have hreach := ih hih
      have hlayers := allCellTourState_layers hn V hV base x i hih hw k (by omega)
      have hadv := allCellTourState_step_advance hn V hV base x i hih hinext hw hx

      have hA : (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (1 + i * (k + 1) + k) *ᵥ
          Ket (allCellStartCfg base)
        = allCellTourState base i hih hw (allCellTourLayerK k) V x := by
        have hpow : 1 + i * (k + 1) + k = k + (1 + i * (k + 1)) := by ring
        rw [hpow, pow_add, mulVec_pow_mul, hreach]
        exact hlayers

      have hB : (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (1 + (i + 1) * (k + 1)) *ᵥ
          Ket (allCellStartCfg base)
        = allCellTourState base (i + 1) hinext hw (allCellTourLayer0 k) V x := by
        have hpow : 1 + (i + 1) * (k + 1) = 1 + (1 + i * (k + 1) + k) := by ring
        rw [hpow, pow_add, mulVec_pow_mul, hA]
        simp only [pow_one]
        exact hadv
      exact hB

/-- A zero-weighted second basis ket contributes nothing to a two-ket sum. -/
theorem ket_add_zero {β : Type} [DecidableEq β] (c₁ c₂ : β) (a : ℂ) :
    (a • Ket c₁ + 0 • Ket c₂) = a • Ket c₁ := by
  funext tgtC
  simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket]

/-- A zero-weighted first basis ket contributes nothing to a two-ket sum. -/
theorem ket_zero_add {β : Type} [DecidableEq β] (c₁ c₂ : β) (a : ℂ) :
    (0 • Ket c₁ + a • Ket c₂) = a • Ket c₂ := by
  funext tgtC
  simp [Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket]

/-- Evaluating a finite sum of complex-valued functions equals summing their values at that
argument. -/
theorem sum_apply {ι β : Type*} [Fintype ι] (g : ι → (β → ℂ)) (c : β) :
    (∑ i, g i) c = ∑ i, (g i) c := by
  classical
  have h : ∀ (s : Finset ι), (s.sum g) c = s.sum (fun i => (g i) c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, Pi.add_apply, ih]
  simpa using! h (Finset.univ : Finset ι)

/-- A final tour configuration is accepting exactly for a true premeasurement bit and rejecting
for a false one. -/
theorem allCellTourFinalCfg_state {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (f : Fin i → Bool) (a b : Bool) :
    (allCellTourFinalCfg base i hi hw f a b).state
      = (if a then (.acc : AllCellState n k) else .rej) := rfl

/-- A final tour configuration has the processed-prefix tape with the current tour cell replaced
by the supplied output symbol. -/
theorem allCellTourFinalCfg_tape {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (f : Fin i → Bool) (a b : Bool)
    (m : Fin (2 * w + 1)) :
    (allCellTourFinalCfg base i hi hw f a b).tape m
      = if m = allCellTourPos i hi hw then b else allCellTourTape base i f m := rfl

/-- The tape at the current tour position in a final configuration is its supplied output
symbol. -/
theorem allCellTourFinalCfg_tape_at {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (f : Fin i → Bool) (a b : Bool) :
    (allCellTourFinalCfg base i hi hw f a b).tape (allCellTourPos i hi hw) = b := by
  simp [allCellTourFinalCfg_tape]

/-- The processed tour tape stores each prefix assignment bit at its corresponding input-cell
position. -/
theorem allCellTourTape_at {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i ≤ n) (hw : n ≤ w) (f : Fin i → Bool) (j : Fin i) :
    allCellTourTape base i f (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1)) = f j := by
  have h1 : w + 1 ≤ (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1)).val := by simp
  have h2 : (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1)).val ≤ w + i := by
    simp
    omega
  simp only [allCellTourTape_of_in base i f (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1))
    h1 h2]
  congr 1
  apply Fin.ext
  simp
  omega

/-- Equality of final tour configurations determines the premeasurement bit, output symbol, and
entire processed-prefix assignment. -/
theorem allCellTourFinalCfg_inj {n k w : ℕ} (base : WindowCfg w (AllCellState n k) Bool)
    (i : ℕ) (hi : i < n) (hw : n ≤ w) (f f' : Fin i → Bool) (a a' b b' : Bool)
    (h : allCellTourFinalCfg base i hi hw f a b = allCellTourFinalCfg base i hi hw f' a' b') :
    a = a' ∧ b = b' ∧ f = f' := by
  have hh := congrArg WindowCfg.state h
  have ht := congrArg WindowCfg.tape h
  rw [allCellTourFinalCfg_state, allCellTourFinalCfg_state] at hh
  have hstate : a = a' := by
    cases a <;> cases a'
    · rfl
    · have hcontra : (.rej : AllCellState n k) = .acc := hh
      cases hcontra
    · have hcontra : (.acc : AllCellState n k) = .rej := hh
      cases hcontra
    · rfl
  have hbsymm : b = b' := by
    have hb := congrFun ht (allCellTourPos i hi hw)
    rw [allCellTourFinalCfg_tape_at, allCellTourFinalCfg_tape_at] at hb
    exact hb
  have hf : f = f' := by
    funext j
    by_contra hj
    have hm : (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1)) ≠ allCellTourPos i hi hw := by
      intro heq
      have heqv := congrArg Fin.val heq
      simp only [Fin.val_mk, allCellTourPos_val] at heqv
      omega
    have hteq := congrFun ht (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1))
    rw [allCellTourFinalCfg_tape, allCellTourFinalCfg_tape] at hteq
    rw [if_neg hm, if_neg hm] at hteq
    have hv1 : allCellTourTape base i f (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1)) = f j := by
      simp only [allCellTourTape_of_in base i f
        (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1))
        (by simp) (by simp; omega)]
      congr 1
      apply Fin.ext
      simp
      omega
    have hv2 : allCellTourTape base i f' (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1)) = f' j := by
      simp only [allCellTourTape_of_in base i f'
        (⟨w + 1 + j.val, by omega⟩ : Fin (2 * w + 1))
        (by simp) (by simp; omega)]
      congr 1
      apply Fin.ext
      simp
      omega
    exact hj (hv1.symm.trans (hteq.trans hv2))
  exact ⟨hstate, hbsymm, hf⟩

/-- The superposition of final tour configurations with amplitudes from the completed gate stage
and the current bit flipped on the tape. -/
noncomputable def allCellTourFinalState {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (base : WindowCfg w (AllCellState n k) Bool) (hw : n ≤ w)
    (i : ℕ) (hi : i < n) :
    QState (WindowCfg w (AllCellState n k) Bool) :=
  ∑ f : Fin i → Bool, ∑ b : Bool,
    (allCellTourAmp hi V x (allCellTourLayerK k) f b) •
      Ket (allCellTourFinalCfg base i hi hw f b (!b))

/-- Evaluating the final tour state gives a sum of tour amplitudes times indicators of the
corresponding final configurations. -/
theorem allCellTourFinalState_apply {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ) (x : Reg n)
    (base : WindowCfg w (AllCellState n k) Bool) (hw : n ≤ w)
    (i : ℕ) (hi : i < n) (c : WindowCfg w (AllCellState n k) Bool) :
    allCellTourFinalState hn V x base hw i hi c
      = ∑ f : Fin i → Bool, ∑ b : Bool,
          (allCellTourAmp hi V x (allCellTourLayerK k) f b) *
            (if c = allCellTourFinalCfg base i hi hw f b (!b) then 1 else 0) := by
  classical
  simp only [allCellTourFinalState]
  simp only [sum_apply, Fintype.sum_bool, Pi.add_apply, Pi.smul_apply, Qatlib.Foundations.PureStateMath.Ket,
    Bool.not_false, Bool.not_true]
  rfl

/-- At the final cell's last gate stage, one step sends the tour state to the
final-configuration sum with each current bit flipped. -/
theorem allCellTourState_step_measure {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n)
    (i : ℕ) (hi : i < n) (hlast : i + 1 = n) (hw : n ≤ w) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
        allCellTourState base i hi hw (allCellTourLayerK k) V x
      = ∑ f : Fin i → Bool, ∑ b : Bool,
          (allCellTourAmp hi V x (allCellTourLayerK k) f b) •
            Ket (allCellTourFinalCfg base i hi hw f b (!b)) := by
  classical

  have hmeas (b b' : Bool) :
      allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b b' = (if b' = !b then 1 else 0) := by
    rw [allCellAmp_serve_measure_row V ⟨i, hi⟩ (allCellTourLayerK k) (by rfl) (by omega) b b']

  have hbranch (f : Fin i → Bool) (b : Bool) :
      (windowStep (t := w) (allCellLocalQTM hn V hV))
          *ᵥ (allCellTourAmp hi V x (allCellTourLayerK k) f b
              • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))
        = (allCellTourAmp hi V x (allCellTourLayerK k) f b
            * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b false)
            • Ket (allCellTourFinalCfg base i hi hw f b false)
          + (allCellTourAmp hi V x (allCellTourLayerK k) f b
            * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b true)
            • Ket (allCellTourFinalCfg base i hi hw f b true) := by
    rw [Matrix.mulVec_smul]
    rw [allCellTour_step_measure hn V hV base i hi hlast hw f b]
    funext tgtC
    simp only [Pi.smul_apply, Pi.add_apply]
    ring

  have hcollapse (f : Fin i → Bool) (b : Bool) :
      (allCellTourAmp hi V x (allCellTourLayerK k) f b
            * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b false)
            • Ket (allCellTourFinalCfg base i hi hw f b false)
          + (allCellTourAmp hi V x (allCellTourLayerK k) f b
            * allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) b true)
            • Ket (allCellTourFinalCfg base i hi hw f b true)
        = (allCellTourAmp hi V x (allCellTourLayerK k) f b) •
            Ket (allCellTourFinalCfg base i hi hw f b (!b)) := by
    cases b with
    | true =>
        have h1 : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) true false = 1 := by
          rw [hmeas]
          simp
        have h2 : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) true true = 0 := by
          rw [hmeas]
          simp
        rw [h1, h2, mul_one, mul_zero, zero_smul, add_zero, Bool.not_true]
    | false =>
        have h1 : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) false false = 0 := by
          rw [hmeas]
          simp
        have h2 : allCellAmp V (.serve ⟨i, hi⟩ (allCellTourLayerK k)) false true = 1 := by
          rw [hmeas]
          simp
        rw [h1, h2, mul_zero, mul_one, zero_smul, zero_add, Bool.not_false]

  have hdist :
      (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
          (Finset.univ.sum (fun f : Fin i → Bool => Finset.univ.sum (fun b : Bool =>
            (allCellTourAmp hi V x (allCellTourLayerK k) f b)
              • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))))
        = Finset.univ.sum (fun f : Fin i → Bool =>
            (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
              (Finset.univ.sum (fun b : Bool =>
                (allCellTourAmp hi V x (allCellTourLayerK k) f b)
                  • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)))) := by
    exact mulVec_sum_state _
      (fun f : Fin i → Bool => Finset.univ.sum (fun b : Bool =>
        (allCellTourAmp hi V x (allCellTourLayerK k) f b)
          • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)))
  have hdist2 :
      Finset.univ.sum (fun f : Fin i → Bool =>
            (windowStep (t := w) (allCellLocalQTM hn V hV)) *ᵥ
              (Finset.univ.sum (fun b : Bool =>
                (allCellTourAmp hi V x (allCellTourLayerK k) f b)
                  • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))))
        = Finset.univ.sum (fun f : Fin i → Bool =>
            Finset.univ.sum (fun b : Bool =>
              (windowStep (t := w) (allCellLocalQTM hn V hV))
                *ᵥ ((allCellTourAmp hi V x (allCellTourLayerK k) f b)
                  • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b)))) := by
    apply Finset.sum_congr rfl
    intro f _
    exact mulVec_sum_state _
      (fun b => (allCellTourAmp hi V x (allCellTourLayerK k) f b)
        • Ket (allCellTourCfg base i hi hw (allCellTourLayerK k) f b))
  simp only [allCellTourState]
  rw [hdist]
  rw [hdist2]
  simp_rw [hbranch]
  simp_rw [hcollapse]

/-- For a centered base head and correctly encoded input fitting in the window, `n*(k+1)+1`
steps give the final tour state at the last cell. -/
theorem allCellTour_final {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
    (i : ℕ) (hi : i < n) (hlast : i + 1 = n) :
    (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
        Ket (allCellStartCfg base)
      = allCellTourFinalState hn V x base hw i hi := by
  have hreach := allCellTour_reach hn V hV base x hw hhead hx i hi
  have hlayers := allCellTourState_layers hn V hV base x i hi hw k (by omega)
  have hmeas := allCellTourState_step_measure hn V hV base x i hi hlast hw

  have hA : (windowStep (t := w) (allCellLocalQTM hn V hV)) ^
      (k + (1 + i * (k + 1))) *ᵥ Ket (allCellStartCfg base)
        = allCellTourState base i hi hw (allCellTourLayerK k) V x := by
    rw [pow_add, mulVec_pow_mul, hreach]
    exact hlayers

  have hB : (windowStep (t := w) (allCellLocalQTM hn V hV)) ^
      (1 + (k + (1 + i * (k + 1)))) *ᵥ Ket (allCellStartCfg base)
        = allCellTourFinalState hn V x base hw i hi := by
    rw [pow_add, mulVec_pow_mul, hA]
    simp only [pow_one]
    rw [hmeas]
    rfl
  have hpow : n * (k + 1) + 1 = 1 + (k + (1 + i * (k + 1))) := by
    rw [← hlast]
    ring
  rw [hpow]
  exact hB

/-- The squared norm of a complex product is the product of the squared norms. -/
theorem norm_sq_mul (a b : ℂ) : ‖a * b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [Complex.norm_mul]
  ring

/-- For unitary gate data, summing the true-branch tour squared amplitudes over all prefix
assignments gives the current cell's final true squared amplitude. -/
theorem allCellTour_acceptAmp_mass {n k i : ℕ} (hi : i < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ j l, V j l ∈ Matrix.unitaryGroup Bool ℂ) (x : Reg n) :
    (∑ f : Fin i → Bool, ‖allCellTourAmp hi V x (allCellTourLayerK k) f true‖ ^ 2)
      = ‖cellFinalAmp V x ⟨i, hi⟩ true‖ ^ 2 := by
  have hnorm (f : Fin i → Bool) :
      ‖allCellTourAmp hi V x (allCellTourLayerK k) f true‖ ^ 2
        = (∏ j' : Fin i, ‖(cellFinalAmp V x (Fin.castLE (by omega) j')) (f j')‖ ^ 2)
          * ‖cellPartialAmp V x ⟨i, hi⟩ (allCellTourLayerK k) true‖ ^ 2 := by
    simp only [allCellTourAmp]
    rw [norm_sq_mul, norm_prod_sq]
  have hcomm :
      (∑ f : Fin i → Bool,
          (∏ j' : Fin i, ‖(cellFinalAmp V x (Fin.castLE (by omega) j')) (f j')‖ ^ 2)
            * ‖cellPartialAmp V x ⟨i, hi⟩ (allCellTourLayerK k) true‖ ^ 2)
        = ‖cellPartialAmp V x ⟨i, hi⟩ (allCellTourLayerK k) true‖ ^ 2
          * (∑ f : Fin i → Bool,
              ∏ j' : Fin i, ‖(cellFinalAmp V x (Fin.castLE (by omega) j')) (f j')‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring
  have hsum : (∑ f : Fin i → Bool, ‖allCellTourAmp hi V x (allCellTourLayerK k) f true‖ ^ 2)
      = ∑ f : Fin i → Bool,
          (∏ j' : Fin i, ‖(cellFinalAmp V x (Fin.castLE (by omega) j')) (f j')‖ ^ 2)
            * ‖cellPartialAmp V x ⟨i, hi⟩ (allCellTourLayerK k) true‖ ^ 2 := by
    apply Fintype.sum_congr
    intro f
    exact hnorm f
  rw [hsum]
  rw [hcomm]
  rw [cellPrefixMass_one (show i ≤ n by omega) V hV x, mul_one]
  have hfin (b : Bool) :
      cellPartialAmp V x ⟨i, hi⟩ (allCellTourLayerK k) b = cellFinalAmp V x ⟨i, hi⟩ b := by
    rfl
  rw [hfin]

/-- Under the centered-head, input-encoding, and window-fit assumptions, accepting mass after
the full tour is the sum of true-branch squared amplitudes over processed-prefix
assignments. -/
theorem allCellTour_acceptMass {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
    (i : ℕ) (hi : i < n) (hlast : i + 1 = n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
      BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
        Ket (allCellStartCfg base)) c)
      = ∑ f : Fin i → Bool,
          ‖allCellTourAmp hi V x (allCellTourLayerK k) f true‖ ^ 2 := by
  classical

  set g : (Fin i → Bool) → WindowCfg w (AllCellState n k) Bool :=
    fun f => allCellTourFinalCfg base i hi hw f true false with hg
  have hacc (f : Fin i → Bool) : (g f).state = (.acc : AllCellState n k) := by
    rw [hg]
    rw [allCellTourFinalCfg_state]
    simp
  have hinj : Function.Injective g := by
    intro f f' heq
    have heq' : allCellTourFinalCfg base i hi hw f true false
        = allCellTourFinalCfg base i hi hw f' true false := by
      simpa only [hg] using! heq
    obtain ⟨-, -, hff'⟩ := allCellTourFinalCfg_inj base i hi hw f f' true true false false heq'
    exact hff'

  have hamp (f : Fin i → Bool) :
      allCellTourFinalState hn V x base hw i hi (g f)
        = allCellTourAmp hi V x (allCellTourLayerK k) f true := by
    rw [allCellTourFinalState_apply]
    rw [Fintype.sum_eq_single f]
    · rw [Fintype.sum_eq_single true]
      · simp only [hg, Bool.not_true]
        simp
      · intro b hb
        have hne : g f ≠ allCellTourFinalCfg base i hi hw f b (!b) := by
          intro hcon
          cases b with
          | true => exact absurd hb (by simp)
          | false =>
              have hst := congrArg WindowCfg.state hcon
              rw [hg, allCellTourFinalCfg_state, allCellTourFinalCfg_state] at hst
              have hcontra : (.rej : AllCellState n k) = .acc := by
                simpa using! hst
              cases hcontra
        rw [if_neg hne, mul_zero]
    · intro f' hf'
      apply Finset.sum_eq_zero
      intro b _
      have hne : g f ≠ allCellTourFinalCfg base i hi hw f' b (!b) := by
        intro hcon
        obtain ⟨ha, hb, hff'⟩ :=
          allCellTourFinalCfg_inj base i hi hw f f' true b false (!b) hcon
        exact hf' hff'.symm
      rw [if_neg hne, mul_zero]

  have hsubset : Finset.image g (Finset.univ : Finset (Fin i → Bool))
      ⊆ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)) := by
    intro c hc
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc f⟩

  have hzero : ∀ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
      c ∉ Finset.image g (Finset.univ : Finset (Fin i → Bool)) →
        BornProb (allCellTourFinalState hn V x base hw i hi) c = 0 := by
    intro c hc hnot
    rw [BornProb]
    have happ : allCellTourFinalState hn V x base hw i hi c = 0 := by
      rw [allCellTourFinalState_apply]
      apply Finset.sum_eq_zero
      intro f _
      apply Finset.sum_eq_zero
      intro b _
      have hne : c ≠ allCellTourFinalCfg base i hi hw f b (!b) := by
        intro hcon
        have hcs : c.state = (.acc : AllCellState n k) := (Finset.mem_filter.mp hc).2
        have hst := congrArg WindowCfg.state hcon
        rw [allCellTourFinalCfg_state] at hst
        have hbtrue : b = true := by
          cases b with
          | true => rfl
          | false =>
              have hcontra : (.rej : AllCellState n k) = .acc := by
                have hrej : c.state = .rej := by simpa using! hst
                rw [hcs] at hrej
                exact hrej.symm
              cases hcontra
        subst hbtrue
        apply hnot
        refine Finset.mem_image.mpr ⟨f, Finset.mem_univ _, ?_⟩
        rw [hg]
        exact hcon.symm
      rw [if_neg hne, mul_zero]
    rw [happ]
    simp
  rw [allCellTour_final hn V hV base x hw hhead hx i hi hlast]
  rw [← Finset.sum_subset hsubset hzero]
  rw [Finset.sum_image (s := (Finset.univ : Finset (Fin i → Bool))) (by
    intro f _ f' _ hff'
    exact hinj (by simpa using! hff'))]
  simp only [BornProb]
  have hsum : (∑ f : Fin i → Bool,
        ‖allCellTourFinalState hn V x base hw i hi (g f)‖ ^ 2)
      = ∑ f : Fin i → Bool, ‖allCellTourAmp hi V x (allCellTourLayerK k) f true‖ ^ 2 := by
    apply Fintype.sum_congr
    intro f
    rw [hamp f]
  rw [hsum]

/-- Under the centered-head, input-encoding, and window-fit assumptions, accepting mass after
`n*(k+1)+1` steps equals the composite cell circuit's true probability at the last wire. -/
theorem allCellTour_acceptProb {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
    (i : ℕ) (hi : i < n) (hlast : i + 1 = n) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
      BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
        Ket (allCellStartCfg base)) c)
      = AcceptProbAt ⟨i, hi⟩
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)) := by
  have hmass := allCellTour_acceptAmp_mass hi V hV x
  have hlastfin : (⟨n - 1, by omega⟩ : Fin n) = ⟨i, hi⟩ := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

  have hstd : AcceptProbAt ⟨i, hi⟩
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x))
      = ‖cellFinalAmp V x ⟨i, hi⟩ true‖ ^ 2 := by
    rw [← hlastfin]
    rw [compositeCellCircuit_acceptProbAt_cell hn V x]
    have hmass1 : ∀ j : Fin n, j ≠ ⟨n - 1, by omega⟩ →
        (∑ b : Bool, ‖(cellFinalAmp V x j) b‖ ^ 2) = 1 := by
      intro j hj
      exact cellFinalAmp_mass V hV x j
    have hprod : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩,
        (∑ b : Bool, ‖(gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
          (fun c => if c = x j then (1 : ℂ) else 0)) b‖ ^ 2)) = 1 := by
      calc (∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩,
            (∑ b : Bool, ‖(gateSeqProd (fun l : Fin k => V j l) k (by omega) *ᵥ
              (fun c => if c = x j then (1 : ℂ) else 0)) b‖ ^ 2))
          = ∏ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩, (1 : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            have h1 := hmass1 j (by
              intro hcon
              exact (Finset.mem_erase.mp hj).1 hcon)
            simpa [cellFinalAmp] using! h1
          _ = 1 := by simp
    rw [hprod, mul_one]
    rfl
  calc
    (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
      BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
        Ket (allCellStartCfg base)) c)
      = ∑ f : Fin i → Bool, ‖allCellTourAmp hi V x (allCellTourLayerK k) f true‖ ^ 2 :=
        allCellTour_acceptMass hn V hV base x hw hhead hx i hi hlast
    _ = ‖cellFinalAmp V x ⟨i, hi⟩ true‖ ^ 2 := hmass
    _ = AcceptProbAt ⟨i, hi⟩
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)) := hstd.symm

/-- The two-operation ten-wire word consisting of controlled-NOT from wire `2` to `1` followed
by Hadamard on `1` has the same encoding as controlled-NOT from `2` to `9` alone. -/
theorem dLambdaOpsEnc_collision :
    dLambdaOpsEnc [.cnot (2 : Fin 10) 1, .hGate 1] = dLambdaOpsEnc [.cnot (2 : Fin 10) 9] := by
  decide

/-- If one deterministic emitter outputs circuit-size descriptions from encoded operation lists,
equal encodings at the same width force equal size descriptions. -/
theorem emitterClause_determined_size
    {enc : (n : ℕ) → List (DLambdaOp n) → List Bool}
    {q c d : ℕ} {emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))}
    (hclause : ∀ (n : ℕ) (ops : List (DLambdaOp n)),
      TM0EmitsPoly emitter c d (n.bits ++ [false] ++ enc n ops)
        ((Size (dLambdaCircuit ops)).bits ++ [false]))
    (n : ℕ) (ops₁ ops₂ : List (DLambdaOp n)) (henc : enc n ops₁ = enc n ops₂) :
    (Size (dLambdaCircuit ops₁)).bits ++ [false]
      = (Size (dLambdaCircuit ops₂)).bits ++ [false] := by
  have h1 := hclause n ops₁
  have h2 := hclause n ops₂
  have h1' : TM0EmitsPoly emitter c d (n.bits ++ [false] ++ enc n ops₂)
      ((Size (dLambdaCircuit ops₁)).bits ++ [false]) := by
    rw [← henc]
    exact h1
  exact TM0EmitsPoly_output_unique emitter h1' h2

/-- No deterministic machine with the specified polynomial emission bound can output all
circuit-size descriptions from `dLambdaOpsEnc` inputs. -/
theorem dLambdaEmitterClause_impossible :
    ¬ ∃ (q c d : ℕ) (emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
      ∀ (n : ℕ) (ops : List (DLambdaOp n)),
        TM0EmitsPoly emitter c d (n.bits ++ [false] ++ dLambdaOpsEnc ops)
          ((Size (dLambdaCircuit ops)).bits ++ [false]) := by
  rintro ⟨q, c, d, emitter, h⟩
  have hdet := emitterClause_determined_size (enc := fun n ops => dLambdaOpsEnc ops)
    (hclause := h) 10 [.cnot (2 : Fin 10) 1, .hGate 1] [.cnot (2 : Fin 10) 9]
    dLambdaOpsEnc_collision
  have hsizeA : Size (dLambdaCircuit [.cnot (2 : Fin 10) 1, .hGate 1]) = 2 := by
    rw [dLambdaCircuit_size]
    rfl
  have hsizeB : Size (dLambdaCircuit [.cnot (2 : Fin 10) 9]) = 1 := by
    rw [dLambdaCircuit_size]
    rfl
  rw [hsizeA, hsizeB] at hdet
  exact absurd hdet (by decide)

/-- The length of the initial run of true bits in a Boolean list. -/
def trueRun : List Bool → ℕ
  | [] => 0
  | true :: rest => 1 + trueRun rest
  | false :: _ => 0

/-- A list of `m` true bits followed by false and any suffix has initial true-run length `m`. -/
theorem trueRun_replicate_succ (m : ℕ) (rest : List Bool) :
    trueRun (List.replicate m true ++ false :: rest) = m := by
  induction m with
  | zero => rfl
  | succ k ih =>
      show trueRun (true :: (List.replicate k true ++ false :: rest)) = k + 1
      simp only [trueRun]
      omega

/-- The initial true-run length of the modified operation encoding is exactly the operation-list
length. -/
theorem dLambdaOpsEnc'_count {n : ℕ} (ops : List (DLambdaOp n)) :
    trueRun (dLambdaOpsEnc' ops) = ops.length := by
  have happ : (List.replicate ops.length true ++ [false]) ++ dLambdaOpsEnc ops
      = List.replicate ops.length true ++ (false :: dLambdaOpsEnc ops) := by
    simp [List.append_assoc]
  rw [dLambdaOpsEnc', happ]
  exact trueRun_replicate_succ ops.length (dLambdaOpsEnc ops)

/-- Equal modified operation encodings at a fixed register width yield equal compiled
circuit-size descriptions. -/
theorem dLambdaOpsEnc'_size_desc {n : ℕ} (ops₁ ops₂ : List (DLambdaOp n))
    (h : dLambdaOpsEnc' ops₁ = dLambdaOpsEnc' ops₂) :
    (Size (dLambdaCircuit ops₁)).bits ++ [false]
      = (Size (dLambdaCircuit ops₂)).bits ++ [false] := by
  have hcount : trueRun (dLambdaOpsEnc' ops₁) = trueRun (dLambdaOpsEnc' ops₂) := by
    rw [h]
  rw [dLambdaOpsEnc'_count ops₁, dLambdaOpsEnc'_count ops₂] at hcount
  have hsize : Size (dLambdaCircuit ops₁) = Size (dLambdaCircuit ops₂) := by
    rw [dLambdaCircuit_size, dLambdaCircuit_size, hcount]
  rw [hsize]

/-- For every positive `ε`, the geometric factor `(8/9)^ceil(log(1/ε)/log(9/8))` is at most `ε`. -/
theorem amplificationFailure_le (ε : ℝ) (hε : 0 < ε) :
    (8 / 9 : ℝ) ^ Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) ≤ ε := by
  have hd : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log (1 / ε) / Real.log (9 / 8))
  have hmul := (div_le_iff₀ hd).mp hc
  have hlog : Real.log (8 / 9 : ℝ) = -Real.log (9 / 8 : ℝ) := by
    rw [show (8 / 9 : ℝ) = (9 / 8 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hεlog : Real.log (1 / ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  apply (Real.log_le_log_iff (by positivity) hε).mp
  rw [Real.log_pow, hlog]
  rw [hεlog] at hmul ⊢
  nlinarith

/-- For `0 < ε ≤ 1`, the amplification copy count is at most `2*(log(1/ε)/log(9/8)+2)+1`. -/
theorem amplificationCopies_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    amplificationCopies ε ≤ 2 * (Real.log (1 / ε) / Real.log (9 / 8) + 2) + 1 := by
  have hpos : 0 ≤ Real.log (1 / ε) / Real.log (9 / 8) := by
    have h1 : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
    have h2 : 0 ≤ Real.log (1 / ε) := by
      have hle : (1 : ℝ) ≤ 1 / ε := (one_le_div₀ hε).2 hε1
      exact Real.log_nonneg hle
    exact div_nonneg h2 (le_of_lt h1)
  have hceil : (Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) : ℝ)
      ≤ Real.log (1 / ε) / Real.log (9 / 8) + 1 := by
    have h1 := Nat.ceil_lt_add_one hpos
    linarith
  unfold amplificationCopies
  have h2 : (2 * (Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) : ℝ) + 1)
      ≤ 2 * (Real.log (1 / ε) / Real.log (9 / 8) + 2) + 1 := by linarith
  exact_mod_cast h2

/-- For correctly encoded input with centered head and sufficient window space, a normalized
final tour state with circuit success probability at least `2/3` has majority-failure
probability at most any positive `ε` using `amplificationCopies ε` tensor copies. -/
theorem allCellTour_amplified_failMass {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
    (hφ : Normalized ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
      Ket (allCellStartCfg base)))
    (hverdict : (2 / 3 : ℝ) ≤ AcceptProbAt ⟨n - 1, by omega⟩
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)))
    (ε : ℝ) (hε : 0 < ε) :
    MeasureProb (PiTensorState fun _ : Fin (amplificationCopies ε) =>
        ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
          Ket (allCellStartCfg base)))
      (Finset.univ.filter fun ω =>
        (Finset.univ.filter fun j : Fin (amplificationCopies ε) =>
          ω j ∈ tourAcceptSet (n := n) (k := k) (w := w)).card
          ≤ (amplificationCopies ε - 1) / 2)
      ≤ ε := by
  classical
  set φ : QState (WindowCfg w (AllCellState n k) Bool) :=
    (windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
      Ket (allCellStartCfg base) with hφdef
  set S : Finset (WindowCfg w (AllCellState n k) Bool) :=
    tourAcceptSet (n := n) (k := k) (w := w) with hSdef
  have hφ' : Normalized φ := by simpa [hφdef] using! hφ

  have hacc : MeasureProb φ S = AcceptProbAt ⟨n - 1, by omega⟩
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)) := by
    have h := allCellTour_acceptProb hn V hV base x hw hhead hx (n - 1) (by omega) (by omega)
    simpa [MeasureProb, hφdef, hSdef, tourAcceptSet] using! h

  have hcompl : MeasureProb φ Sᶜ = 1 - MeasureProb φ S := by
    have hsum : MeasureProb φ S + MeasureProb φ Sᶜ = MeasureProb φ Finset.univ :=
      Finset.sum_add_sum_compl S _
    rw [measureProb_univ hφ'] at hsum
    linarith
  have hq : MeasureProb φ Sᶜ ≤ 1 / 3 := by
    rw [hcompl]
    have h2 : (2 / 3 : ℝ) ≤ MeasureProb φ S := by linarith [hverdict, hacc]
    linarith

  have hmain := majority_copies_fail_mass
    (Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8))) φ hφ' S hq
  have htail : (8 / 9 : ℝ) ^ Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) ≤ ε :=
    amplificationFailure_le ε hε
  have hle : MeasureProb (PiTensorState fun _ : Fin (amplificationCopies ε) => φ)
      (Finset.univ.filter fun ω =>
        (Finset.univ.filter fun j : Fin (amplificationCopies ε) => ω j ∈ S).card
          ≤ (amplificationCopies ε - 1) / 2)
      ≤ (8 / 9 : ℝ) ^ Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) := by
    have h2 := hmain
    simpa [amplificationCopies, hSdef] using! h2
  exact hle.trans htail

/-- Collects the failure of `HeadStaySimulationSpec`, the stated communication and
majority-formula lower bounds, and the concrete machines' local conditions, evolution,
acceptance, tour, encoding, and amplification results. -/
theorem clause8_complete :
    ¬ HeadStaySimulationSpec ∧
      CommunicationOmegaLogLogSpec ∧
      MajorityFormulaLowerBoundSpec ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ),
        LocalQTMFiveConditions (layerLocalQTM Us hU)) ∧
      (∀ (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ),
        LocalQTMFiveConditions (gateLocalQTM U hU)) ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (w : ℕ)
        (base : WindowCfg w (LayerState k) Bool) (j : ℕ) (hj : j < k) (α β : ℂ),
        (windowStep (t := w) (layerLocalQTM Us hU)) *ᵥ
            (α • Ket (layerCfg base (.layer ⟨j, by omega⟩) false) +
              β • Ket (layerCfg base (.layer ⟨j, by omega⟩) true))
          = (Us ⟨j, by omega⟩ false false * α
              + Us ⟨j, by omega⟩ false true * β) •
              Ket (layerCfg base (.layer ⟨j + 1, by omega⟩) false) +
            (Us ⟨j, by omega⟩ true false * α
              + Us ⟨j, by omega⟩ true true * β) •
              Ket (layerCfg base (.layer ⟨j + 1, by omega⟩) true)) ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (w : ℕ)
        (base : WindowCfg w (LayerState k) Bool) (v : Bool → ℂ) (j : ℕ) (hj : j ≤ k),
        (windowStep (t := w) (layerLocalQTM Us hU)) ^ j *ᵥ
            layerCfgSuper base 0 (by omega) v
          = layerCfgSuper base j hj (gateSeqProd Us j hj *ᵥ v)) ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (w : ℕ)
        (base : WindowCfg w (LayerState k) Bool) (v : Bool → ℂ),
        (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
          BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 1) *ᵥ
            layerCfgSuper base 0 (by omega) v) c)
          = ‖(gateSeqProd Us k (by omega) *ᵥ v) true‖ ^ 2) ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (w : ℕ), 0 < w →
        ∀ (x : Reg 1),
        (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
          BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
            *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) 1 x)) c)
          = AcceptProb (Run (1 : Matrix (Reg 1) (Reg 1) ℂ)
              ((List.ofFn (fun i => reg1Gate' (Us i))).map Step.gate) (Ket x)) (by omega)) ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (w : ℕ), 0 < w →
        ∀ (n : ℕ), (hn : 0 < n) → ∀ (x : Reg n),
        (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
          BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
            *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) n x)) c)
          = ‖(gateSeqProd Us k (by omega) *ᵥ
              (fun c => if c = x ⟨0, hn⟩ then (1 : ℂ) else 0)) true‖ ^ 2) ∧
      (∀ (k : ℕ) (Us : Fin k → Matrix Bool Bool ℂ)
        (hU : ∀ i, Us i ∈ Matrix.unitaryGroup Bool ℂ) (w : ℕ), 0 < w →
        ∀ (n : ℕ), (hn : 0 < n) → ∀ (x : Reg n),
        (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : LayerState k)),
          BornProb ((windowStep (t := w) (layerLocalQTM Us hU)) ^ (k + 2)
            *ᵥ Ket (initWindowCfg (t := w) (layerLocalQTM Us hU) n x)) c)
          = AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
              ((List.ofFn (fun i => embedReg1 hn (Us i))).map Step.gate) (Ket x)) hn) ∧
      (∀ (n k tgt : ℕ) (V : Fin n → Fin k → Matrix Bool Bool ℂ) (htgt : tgt < n)
        (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ),
        LocalQTMFiveConditions (cellLocalQTM V htgt hV)) ∧
      (∀ (n : ℕ) (i : Fin n) (gs : List (Matrix Bool Bool ℂ)) (x : Reg n),
        AcceptProbAt i (Run (1 : Matrix (Reg n) (Reg n) ℂ)
            ((gs.map (fun U => embedRegI i U)).map Step.gate) (Ket x))
          = ‖(boolGateProd gs *ᵥ (fun c => if c = x i then (1 : ℂ) else 0)) true‖ ^ 2) ∧
      (∀ (n k tgt w : ℕ) (V : Fin n → Fin k → Matrix Bool Bool ℂ) (htgt : tgt < n)
        (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ), n ≤ w → ∀ (x : Reg n),
        (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : CellState n k tgt)),
          BornProb ((windowStep (t := w) (cellLocalQTM V htgt hV)) ^ (tgt + k + 2)
            *ᵥ Ket (initWindowCfg (t := w) (cellLocalQTM V htgt hV) n x)) c)
          = AcceptProbAt ⟨tgt, htgt⟩
            ((Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (((List.ofFn (V ⟨tgt, htgt⟩)).map
                  (fun U => embedRegI ⟨tgt, htgt⟩ U)).map Step.gate))
              (Ket x))) ∧
      (∀ (n k i : ℕ) (hi : i ≤ n)
        (V : Fin n → Fin k → Matrix Bool Bool ℂ)
        (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ) (x : Reg n),
        (∑ f : Fin i → Bool, ∏ j : Fin i,
          ‖(cellFinalAmp V x (Fin.castLE hi j)) (f j)‖ ^ 2) = 1) ∧
      (∀ (n k w : ℕ) (hn : 0 < n)
        (V : Fin n → Fin k → Matrix Bool Bool ℂ)
        (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
        (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
        (hhead : base.head.val = w)
        (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
        (i : ℕ) (hi : i < n) (hlast : i + 1 = n),
        (∑ c ∈ Finset.univ.filter (fun c => c.state = (.acc : AllCellState n k)),
          BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
            Ket (allCellStartCfg base)) c)
        = AcceptProbAt ⟨i, hi⟩
          ((Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)))) ∧
      (dLambdaOpsEnc [.cnot (2 : Fin 10) 1, .hGate 1]
        = dLambdaOpsEnc [.cnot (2 : Fin 10) 9]) ∧
      (¬ ∃ (q c d : ℕ) (emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
        ∀ (n : ℕ) (ops : List (DLambdaOp n)),
          TM0EmitsPoly emitter c d (n.bits ++ [false] ++ dLambdaOpsEnc ops)
            ((Size (dLambdaCircuit ops)).bits ++ [false])) ∧
      (∀ (n : ℕ) (ops₁ ops₂ : List (DLambdaOp n)),
        dLambdaOpsEnc' ops₁ = dLambdaOpsEnc' ops₂ →
          (Size (dLambdaCircuit ops₁)).bits ++ [false]
            = (Size (dLambdaCircuit ops₂)).bits ++ [false]) ∧
      (∀ (ε : ℝ), 0 < ε →
        (8 / 9 : ℝ) ^ Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) ≤ ε) ∧
      (∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        amplificationCopies ε ≤ 2 * (Real.log (1 / ε) / Real.log (9 / 8) + 2) + 1) ∧
      (∀ (n k w : ℕ) (hn : 0 < n)
        (V : Fin n → Fin k → Matrix Bool Bool ℂ)
        (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
        (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
        (hhead : base.head.val = w)
        (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
        (hφ : Normalized ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
          Ket (allCellStartCfg base)))
        (hverdict : (2 / 3 : ℝ) ≤ AcceptProbAt ⟨n - 1, by omega⟩
          (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)))
        (ε : ℝ) (hε : 0 < ε),
        MeasureProb (PiTensorState fun _ : Fin (amplificationCopies ε) =>
            ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
              Ket (allCellStartCfg base)))
          (Finset.univ.filter fun ω =>
            (Finset.univ.filter fun j : Fin (amplificationCopies ε) =>
              ω j ∈ tourAcceptSet (n := n) (k := k) (w := w)).card
              ≤ (amplificationCopies ε - 1) / 2)
          ≤ ε) := by
  refine ⟨clause1_headStaySimulationSpec_lightCone_false, communication_omega_log_log,
    majority_formula_lower_bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k Us hU
    exact layerLocalQTM_five Us hU
  · intro U hU
    exact gateLocalQTM_five U hU
  · intro k Us hU w base j hj α β
    exact layerLocalQTM_layerEvolution Us hU base j hj α β
  · intro k Us hU w base v j hj
    exact layerLocalQTM_gateSeq Us hU base v j hj
  · intro k Us hU w base v
    exact layerLocalQTM_acceptMass Us hU base v
  · intro k Us hU w hw x
    exact headStay_acceptProb_oneWire k Us hU w hw x
  · intro k Us hU w hw n hn x
    exact headStay_acceptMass_multi Us hU hw hn x
  · intro k Us hU w hw n hn x
    exact headStay_acceptProb_multi Us hU hw hn x
  · intro n k tgt V htgt hV
    exact cellLocalQTM_five V htgt hV
  · intro n i gs x
    exact acceptProb_embedI i gs x
  · intro n k tgt w V htgt hV hw x
    exact headStay_cell_acceptProb_multi V htgt hV hw x
  · intro n k i hi V hV x
    exact cellPrefixMass_one hi V hV x
  · intro n k w hn V hV base x hw hhead hx i hi hlast
    exact allCellTour_acceptProb hn V hV base x hw hhead hx i hi hlast
  · exact dLambdaOpsEnc_collision
  · exact dLambdaEmitterClause_impossible
  · intro n ops₁ ops₂ h
    exact dLambdaOpsEnc'_size_desc ops₁ ops₂ h
  · intro ε hε
    exact amplificationFailure_le ε hε
  · intro ε hε hε1
    exact amplificationCopies_le ε hε hε1
  · intro n k w hn V hV base x hw hhead hx hφ hverdict ε hε
    exact allCellTour_amplified_failMass hn V hV base x hw hhead hx hφ hverdict ε hε

end QtmUniform
end Qatlib.Concepts.CircuitImpl.Phi3Universal
