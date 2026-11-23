/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeQuantumMachineDefs
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

/-!
# Reversible Turing machines as well-formed quantum machines

This module formalizes the finite-support configuration model of a deterministic Turing machine
with a two-way infinite tape and only left or right head moves. The reversibility criterion of
[BernsteinVazirani1997], Theorem B.0.13, has two local parts: every destination state is entered
with a single head direction, and forgetting the head direction leaves an injective map on
control-symbol pairs.

The main results show that these two local conditions make the global configuration update a
bijection, so every configuration has exactly one predecessor (Corollary B.0.14), and that
assigning amplitude one to each deterministic transition produces a globally well-formed quantum
rule on the configuration Hilbert space (Theorem 4.1.2). The local cell transition matrix is
the permutation matrix of the induced cell equivalence and therefore has Euclidean L2 operator
norm one whenever the cell type is nonempty.

## Main statements

* `targetCfg_injective`: the two local conditions of Theorem B.0.13 make the global update
  injective.
* `existsUnique_predecessor`: every configuration has exactly one predecessor
  (Corollary B.0.14).
* `rule_globallyWellformed`: the amplitude-one transitions of a reversible machine form a globally
  well-formed rule (Theorem 4.1.2).
* `cellPermMatrix_opNorm`: the local transition matrix has Euclidean L2 operator norm one.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Papers.QComplexity97.ReversibleTm

namespace ReversibleStep

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped Matrix.Norms.L2Operator

/-! ### Machine data and the two reversibility conditions -/

/-- A head direction of a reversible machine. The source model allows only left and right moves. -/
inductive Dir where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The integer displacement of a head direction. -/
def Dir.offset : Dir → ℤ
  | .left => -1
  | .right => 1

/-- The embedding of a left or right direction into the three-way move type of the configuration
model. -/
def Dir.toMove : Dir → Move
  | .left => .left
  | .right => .right

/-- Distinct head directions have distinct integer displacements. -/
theorem Dir.offset_injective : Function.Injective Dir.offset := by
  intro a b h
  cases a <;> cases b <;> simp_all [Dir.offset]

/-- The embedding of a direction into `Move` preserves its integer displacement. -/
@[simp] theorem Dir.toMove_offset (d : Dir) : d.toMove.offset = d.offset := by
  cases d <;> rfl

/-- The local result of a deterministic transition: the written symbol, the next control state,
and the head direction. -/
structure Transition (Q A : Type*) where
  /-- The symbol written at the current head position. -/
  write : A
  /-- The control state after the transition. -/
  next : Q
  /-- The direction in which the head moves. -/
  dir : Dir

/-- A deterministic Turing machine with a two-way infinite tape, a total transition function, and
only left or right head moves. -/
structure Machine (Q A : Type*) where
  /-- The distinguished blank symbol of the tape alphabet. -/
  blank : A
  /-- The total transition function. -/
  step : Q → A → Transition Q A

/-- Theorem B.0.13(i): every destination state is entered with a single head direction. -/
def IncomingDirectionUnique {Q A : Type*} (M : Machine Q A) : Prop :=
  ∀ (p₁ : Q) (a₁ : A) (p₂ : Q) (a₂ : A),
    (M.step p₁ a₁).next = (M.step p₂ a₂).next → (M.step p₁ a₁).dir = (M.step p₂ a₂).dir

/-- The cell map obtained from the transition function by forgetting the head direction. -/
def CellMap {Q A : Type*} (M : Machine Q A) : Q × A → A × Q :=
  fun pa => ((M.step pa.1 pa.2).write, (M.step pa.1 pa.2).next)

/-- Theorem B.0.13(ii): forgetting the head direction gives an injective cell map. -/
def CellMapInjective {Q A : Type*} (M : Machine Q A) : Prop :=
  Function.Injective (CellMap M)

/-! ### The global configuration update -/

/-- The configuration reached from `c` by one deterministic machine step. -/
def targetCfg {Q A : Type*} (M : Machine Q A) (c : Config Q A M.blank) : Config Q A M.blank :=
  ⟨(M.step c.state (c.tape c.head)).next,
    c.tape.write c.head (M.step c.state (c.tape c.head)).write,
    c.head + (M.step c.state (c.tape c.head)).dir.offset⟩

/-- Under the two conditions of Theorem B.0.13, the global configuration update is injective. -/
theorem targetCfg_injective {Q A : Type*}
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M) :
    Function.Injective (targetCfg M) := by
  intro c d h
  have hs : (M.step c.state (c.tape c.head)).next = (M.step d.state (d.tape d.head)).next :=
    congrArg Config.state h
  have hdirEq : (M.step c.state (c.tape c.head)).dir =
      (M.step d.state (d.tape d.head)).dir :=
    hdir c.state (c.tape c.head) d.state (d.tape d.head) hs
  have hhead : c.head = d.head := by
    have hh := congrArg Config.head h
    simp only [targetCfg] at hh
    rw [hdirEq] at hh
    omega
  have hwrite : (M.step c.state (c.tape c.head)).write =
      (M.step d.state (d.tape d.head)).write := by
    have ht := congrArg Config.tape h
    simp only [targetCfg] at ht
    have hv := congrArg (fun T : Tape A M.blank => T c.head) ht
    rw [Tape.write_same] at hv
    have hd : (d.tape.write d.head (M.step d.state (d.tape d.head)).write) c.head =
        (M.step d.state (d.tape d.head)).write := by
      rw [← hhead, Tape.write_same]
    exact hv.trans hd
  have hpair : (c.state, c.tape c.head) = (d.state, d.tape d.head) := by
    apply hcell
    change ((M.step c.state (c.tape c.head)).write, (M.step c.state (c.tape c.head)).next) =
      ((M.step d.state (d.tape d.head)).write, (M.step d.state (d.tape d.head)).next)
    exact Prod.ext hwrite hs
  have hread : c.tape c.head = d.tape d.head := congrArg Prod.snd hpair
  have htape : c.tape = d.tape := by
    have ht := congrArg Config.tape h
    simp only [targetCfg] at ht
    apply Tape.ext
    intro i
    by_cases hi : i = c.head
    · subst hi
      conv_rhs => rw [hhead]
      exact hread
    · have hcw : c.tape i =
          (c.tape.write c.head (M.step c.state (c.tape c.head)).write) i := by
        rw [Tape.write_other _ _ _ _ hi]
      have hdw : d.tape i =
          (d.tape.write d.head (M.step d.state (d.tape d.head)).write) i := by
        rw [Tape.write_other _ _ _ _ (by omega : i ≠ d.head)]
      rw [hcw, hdw, ht]
  exact Config.ext (congrArg Prod.fst hpair) htape hhead

/-! ### The explicit inverse and bijectivity -/

/-- For finite `Q` and `A`, the injective cell map is bijective because `Q × A` and `A × Q` have
the same cardinality. -/
theorem cellMap_bijective {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hcell : CellMapInjective M) : Function.Bijective (CellMap M) :=
  (Fintype.bijective_iff_injective_and_card (CellMap M)).mpr
    ⟨hcell, by simp [Fintype.card_prod, Nat.mul_comm]⟩

/-- The equivalence on control-symbol pairs induced by the injective cell map of a finite machine.
It is a bijection because the finite types `Q × A` and `A × Q` have the same cardinality. -/
def cellEquiv {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hcell : CellMapInjective M) : Q × A ≃ A × Q :=
  Equiv.ofBijective (CellMap M) (cellMap_bijective M hcell)

/-- The unique incoming direction of a destination control state, obtained from any transition
into that state. -/
def incomingDir {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (_hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (q' : Q) : Dir :=
  let pa := (cellEquiv M hcell).symm (M.blank, q')
  (M.step pa.1 pa.2).dir

/-- The incoming direction of a destination state agrees with every transition into it. -/
theorem incomingDir_spec {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (p : Q) (a : A) :
    incomingDir M hdir hcell (M.step p a).next = (M.step p a).dir := by
  let pa := (cellEquiv M hcell).symm (M.blank, (M.step p a).next)
  have hpre : (M.step pa.1 pa.2).next = (M.step p a).next :=
    congrArg Prod.snd ((cellEquiv M hcell).apply_symm_apply (M.blank, (M.step p a).next))
  exact hdir _ _ _ _ hpre

/-- An explicit predecessor obtained by moving the head backwards along the incoming direction and
using the cell inverse to recover the previous control state and restore the previous tape symbol. -/
def invStep {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (c : Config Q A M.blank) : Config Q A M.blank :=
  let d := incomingDir M hdir hcell c.state
  let h := c.head - d.offset
  let pa := (cellEquiv M hcell).symm (c.tape h, c.state)
  ⟨pa.1, c.tape.write h pa.2, h⟩

/-- The explicit predecessor is mapped to the configuration by one machine step. -/
theorem targetCfg_invStep {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (c : Config Q A M.blank) : targetCfg M (invStep M hdir hcell c) = c := by
  set d := incomingDir M hdir hcell c.state
  set h := c.head - d.offset
  set pa := (cellEquiv M hcell).symm (c.tape h, c.state)
  have hpa : CellMap M pa = (c.tape h, c.state) :=
    (cellEquiv M hcell).apply_symm_apply (c.tape h, c.state)
  have hnext : (M.step pa.1 pa.2).next = c.state := congrArg Prod.snd hpa
  have hwrite : (M.step pa.1 pa.2).write = c.tape h := congrArg Prod.fst hpa
  have hdirpa : (M.step pa.1 pa.2).dir = d := by
    have hs := incomingDir_spec M hdir hcell pa.1 pa.2
    rw [hnext] at hs
    exact hs.symm
  have hstep : invStep M hdir hcell c = ⟨pa.1, c.tape.write h pa.2, h⟩ := rfl
  rw [hstep]
  apply Config.ext
  · change (M.step pa.1 ((c.tape.write h pa.2) h)).next = c.state
    rw [Tape.write_same]
    exact hnext
  · change (c.tape.write h pa.2).write h ((M.step pa.1 ((c.tape.write h pa.2) h)).write) = c.tape
    rw [Tape.write_same]
    rw [hwrite, Tape.write_write, Tape.write_read]
  · change h + (M.step pa.1 ((c.tape.write h pa.2) h)).dir.offset = c.head
    rw [Tape.write_same, hdirpa]
    change (c.head - d.offset) + d.offset = c.head
    omega

/-- Taking the predecessor after one machine step recovers the original configuration. -/
theorem invStep_targetCfg {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (c : Config Q A M.blank) : invStep M hdir hcell (targetCfg M c) = c := by
  set t := M.step c.state (c.tape c.head)
  have hdirT : incomingDir M hdir hcell (targetCfg M c).state = t.dir := by
    change incomingDir M hdir hcell t.next = t.dir
    exact incomingDir_spec M hdir hcell c.state (c.tape c.head)
  have htau : (targetCfg M c).tape c.head = t.write := by
    change (c.tape.write c.head t.write) c.head = t.write
    rw [Tape.write_same]
  have hpa : (cellEquiv M hcell).symm (t.write, t.next) = (c.state, c.tape c.head) := by
    have h1 : cellEquiv M hcell (c.state, c.tape c.head) = (t.write, t.next) := rfl
    rw [← h1, Equiv.symm_apply_apply]
  change (let d := incomingDir M hdir hcell (targetCfg M c).state
    let h := (targetCfg M c).head - d.offset
    let pa := (cellEquiv M hcell).symm ((targetCfg M c).tape h, (targetCfg M c).state)
    (⟨pa.1, (targetCfg M c).tape.write h pa.2, h⟩ : Config Q A M.blank)) = c
  dsimp only
  rw [hdirT]
  have hheadEq : (targetCfg M c).head - t.dir.offset = c.head := by
    change c.head + t.dir.offset - t.dir.offset = c.head
    omega
  have hstateEq : (targetCfg M c).state = t.next := rfl
  simp only [hheadEq, htau, hstateEq, hpa]
  ext <;> simp [targetCfg, Tape.write_write, Tape.write_read]

/-- The two local conditions of Theorem B.0.13 make the global configuration update bijective. -/
theorem targetCfg_bijective {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M) :
    Function.Bijective (targetCfg M) :=
  ⟨targetCfg_injective M hdir hcell,
    fun c => ⟨invStep M hdir hcell c, targetCfg_invStep M hdir hcell c⟩⟩

/-- Corollary B.0.14: every configuration of a reversible machine has exactly one predecessor. -/
theorem existsUnique_predecessor {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (c : Config Q A M.blank) :
    ∃! d : Config Q A M.blank, targetCfg M d = c := by
  refine ⟨invStep M hdir hcell c, targetCfg_invStep M hdir hcell c, ?_⟩
  intro d hd
  have h := congrArg (invStep M hdir hcell) hd
  simpa only [invStep_targetCfg] using h

/-! ### The evolution isometry and the amplitude-one rule -/

/-- The bijective configuration update as an equivalence of configuration types. -/
def stepEquiv {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M) :
    Config Q A M.blank ≃ Config Q A M.blank :=
  Equiv.ofBijective (targetCfg M) (targetCfg_bijective M hdir hcell)

/-- The one-step evolution operator on the configuration Hilbert space, obtained by reindexing
square-summable amplitudes along the bijective configuration update. -/
def stepUnitary {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M) :
    State Q A M.blank ≃ₗᵢ[ℂ] State Q A M.blank :=
  hilbertReindex (stepEquiv M hdir hcell)

/-- The evolution operator preserves the Euclidean norm of every configuration superposition. -/
theorem step_norm_map {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
    (ψ : State Q A M.blank) : ‖stepUnitary M hdir hcell ψ‖ = ‖ψ‖ :=
  (stepUnitary M hdir hcell).norm_map ψ

/-- The uniform norm bound with constant one, placed outside the universal quantifiers over the
machine data and the state. -/
theorem step_norm_bound_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q A : Type*} [Fintype Q] [Fintype A]
        (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M)
        (ψ : State Q A M.blank), ‖stepUnitary M hdir hcell ψ‖ ≤ C * ‖ψ‖ := by
  refine ⟨1, one_pos, ?_⟩
  intro Q A _ _ M hdir hcell ψ
  rw [step_norm_map, one_mul]

/-- The quantum rule assigning amplitude one to every deterministic transition of the machine. -/
def rule {Q A : Type*} [DecidableEq Q] [DecidableEq A] (M : Machine Q A) : Rule Q A where
  blank := M.blank
  amplitude p a m q b :=
    if m = (M.step p a).dir.toMove ∧ q = (M.step p a).next ∧ b = (M.step p a).write
    then 1 else 0

/-- The amplitude-one rule has value one exactly on the deterministic transition triple and zero
elsewhere. -/
theorem rule_amplitude {Q A : Type*} [DecidableEq Q] [DecidableEq A]
    (M : Machine Q A) (p : Q) (a : A)
    (m : Move) (q : Q) (b : A) :
    (rule M).amplitude p a m q b =
      if m = (M.step p a).dir.toMove ∧ q = (M.step p a).next ∧ b = (M.step p a).write then 1
      else 0 := by
  rfl

/-- The transition column of the amplitude-one rule at a configuration is the basis vector of the
corresponding deterministic successor configuration. -/
theorem rule_column {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : Machine Q A) (c : Config Q A M.blank) :
    (rule M).column c = ket (targetCfg M c) := by
  classical
  let t := M.step c.state (c.tape c.head)
  have hval : (rule M).amplitude c.state (c.tape c.head) t.dir.toMove t.next t.write = 1 := by
    rw [rule_amplitude]
    simp [t]
  have hzero : ∀ x ∈ (Finset.univ : Finset (Move × Q × A)),
      x ≠ (t.dir.toMove, t.next, t.write) →
        (rule M).amplitude c.state (c.tape c.head) x.1 x.2.1 x.2.2 •
          ket (target c x.1 x.2.1 x.2.2) = 0 := by
    rintro ⟨m, q, a⟩ _ hx
    rw [rule_amplitude]
    rw [ite_eq_right (by
      rintro ⟨hm, hq, ha⟩
      exact hx (Prod.ext hm (Prod.ext hq ha)))]
    exact zero_smul ℂ _
  have hsingle : (rule M).column c = ket (target c t.dir.toMove t.next t.write) := by
    unfold Rule.column
    rw [Finset.sum_eq_single (t.dir.toMove, t.next, t.write)]
    · rw [hval, one_smul]
    · exact hzero
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsingle]
  congr 1
  apply Config.ext
  · rfl
  · rfl
  · simp [target, targetCfg, Dir.toMove_offset, t]

/-- Theorem 4.1.2: assigning amplitude one to each deterministic transition of a reversible
machine gives a globally well-formed quantum rule. -/
theorem rule_globallyWellformed {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A]
    (M : Machine Q A) (hdir : IncomingDirectionUnique M) (hcell : CellMapInjective M) :
    (rule M).GloballyWellformed := by
  classical
  refine ⟨stepUnitary M hdir hcell, fun c => ?_⟩
  rw [rule_column]
  change hilbertReindex (stepEquiv M hdir hcell) (ket c) = ket (targetCfg M c)
  rw [show ket c = lp.single 2 c 1 from rfl, hilbertReindex_single]
  rfl

/-! ### The local cell permutation and its Euclidean operator norm -/

/-- The permutation of cell types induced by the reversible cell map, using the product
commutativity to place domain and codomain on the same type. -/
def cellPerm {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hcell : CellMapInjective M) : Equiv.Perm (Q × A) :=
  (cellEquiv M hcell).trans (Equiv.prodComm A Q)

/-- The induced permutation acts on a cell by exchanging the written symbol and the next state. -/
@[simp] theorem cellPerm_apply {Q A : Type*} [Fintype Q] [Fintype A]
    (M : Machine Q A) (hcell : CellMapInjective M) (p : Q) (a : A) :
    cellPerm M hcell (p, a) = ((M.step p a).next, (M.step p a).write) := rfl

/-- The local transition matrix of a reversible machine, viewed as a permutation matrix, has
Euclidean L2 operator norm one on every nonempty cell type. -/
theorem cellPermMatrix_opNorm {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] [Nonempty (Q × A)]
    (M : Machine Q A) (hcell : CellMapInjective M) :
    ‖(cellPerm M hcell).permMatrix ℂ‖ = 1 :=
  Matrix.permMatrix_l2_opNorm_eq _

/-- The unit operator-norm bound for local cell permutations, with the constant placed outside all
quantifiers over machine data. -/
theorem cellPermMatrix_opNorm_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
        [Nonempty (Q × A)] (M : Machine Q A) (hcell : CellMapInjective M),
        ‖(cellPerm M hcell).permMatrix ℂ‖ ≤ C := by
  refine ⟨1, one_pos, ?_⟩
  intro Q A _ _ _ _ _ M hcell
  rw [cellPermMatrix_opNorm M hcell]

end ReversibleStep

end Qatlib.Papers.QComplexity97.ReversibleTm
