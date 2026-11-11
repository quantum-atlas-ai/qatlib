/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Native quantum machine configurations and unitary constructions

`Tape`, `Config`, `State`, and `Rule` describe finite-support tapes, classical configurations,
square-summable superpositions, and local transition amplitudes. `Rule.GloballyWellformed`
requires the transition columns to be realized by a linear isometric equivalence of the
configuration Hilbert space.

The module derives local orthogonality constraints, constructs control-basis changes and clocked
evolution, proves exact simulation over five clock phases, and extends the local transition
isometry to a finite unitary swap. These constructions support the quantum machine framework of
[BernsteinVazirani1997].

## Main statements

* `Rule.local_inner_of_global`: derives local normalization and orthogonality from global
  unitary evolution.
* `Rule.basisChanged_direction_of_noStay`: determines movement from the target control sector
  when stationary transitions vanish.
* `Rule.changeBasis_globallyWellformed`: preserves global well-formedness under a control-basis
  change.
* `fivePhase_cycles`: simulates `t` applications of the original unitary in `5 * t` clock steps.
* `Rule.cellSwap_unitary`: extends the local transition isometry to a unitary matrix on an
  enlarged cell space.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped BigOperators ComplexConjugate Classical Matrix

/-- A tape indexed by the integers with only finitely many cells different from the
distinguished blank symbol. -/
structure Tape (A : Type*) (blank : A) where
  cell : ℤ → A
  finite_nonblank : Set.Finite {i | cell i ≠ blank}

instance {A : Type*} {blank : A} : CoeFun (Tape A blank) (fun _ => ℤ → A) := ⟨Tape.cell⟩

/-- Two tapes are equal if their symbols agree at every integer position. -/
@[ext] theorem Tape.ext {A : Type*} {blank : A} {T S : Tape A blank}
    (h : ∀ i, T i = S i) : T = S := by
  cases T
  cases S
  congr
  exact funext h

/-- The tape whose symbol is blank at every position. -/
def Tape.empty {A : Type*} (blank : A) : Tape A blank :=
  ⟨fun _ => blank, by simp⟩

/-- Replaces the symbol at `head` by `symbol`, preserving finiteness of the set of nonblank
cells. -/
def Tape.write {A : Type*} {blank : A} (T : Tape A blank) (head : ℤ) (symbol : A) : Tape A blank :=
  ⟨Function.update T.cell head symbol, (T.finite_nonblank.insert head).subset (by
    intro i hi
    by_cases h : i = head
    · exact Or.inl h
    · apply Or.inr
      change Function.update T.cell head symbol i ≠ blank at hi
      change T.cell i ≠ blank
      simpa only [Function.update_of_ne h] using! hi)⟩

/-- Every cell of the empty tape contains the blank symbol. -/
@[simp] theorem Tape.empty_apply {A : Type*} (blank : A) (i : ℤ) : Tape.empty blank i = blank := rfl

/-- Reading the cell just written returns the written symbol. -/
@[simp] theorem Tape.write_same {A : Type*} {blank : A} (T : Tape A blank) (h : ℤ) (a : A) :
    T.write h a h = a := Function.update_self _ _ _

/-- Writing at `h` leaves the symbol at every distinct position `i` unchanged. -/
theorem Tape.write_other {A : Type*} {blank : A} (T : Tape A blank) (h i : ℤ) (a : A) (hi : i ≠ h) :
    T.write h a i = T i := Function.update_of_ne hi _ _

/-- Two consecutive writes to the same cell have the same effect as the second write alone. -/
@[simp] theorem Tape.write_write {A : Type*} {blank : A} (T : Tape A blank) (h : ℤ) (a b : A) :
    (T.write h a).write h b = T.write h b := by
  apply Tape.ext
  intro i
  exact congrFun (Function.update_idem a b T.cell) i

/-- The three possible head movements: left, stationary, and right. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq, Fintype

/-- The integer head displacement associated with a movement: `-1`, `0`, or `1`. -/
def Move.offset : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Distinct movements have distinct integer offsets. -/
theorem Move.offset_injective : Function.Injective Move.offset := by
  intro a b h
  cases a <;> cases b <;> simp_all [Move.offset]

/-- A classical machine configuration consisting of a control state, a finite-support tape, and
an integer head position. -/
structure Config (Q A : Type*) (blank : A) where
  state : Q
  tape : Tape A blank
  head : ℤ

/-- Configurations with the same control state, tape, and head position are equal. -/
@[ext] theorem Config.ext {Q A : Type*} {blank : A} {c d : Config Q A blank}
    (hs : c.state = d.state) (ht : c.tape = d.tape) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases ht
  cases hh
  rfl

/-- The complex Hilbert space of square-summable amplitudes indexed by machine configurations. -/
noncomputable abbrev State (Q A : Type*) (blank : A) : Type _ :=
    lp (fun _ : Config Q A blank => ℂ) 2

/-- The configuration basis vector with amplitude one at `c` and zero elsewhere. -/
noncomputable def ket {Q A : Type*} {blank : A} (c : Config Q A blank) : State Q A blank := by
  classical
  exact lp.single 2 c 1

/-- A blank symbol together with complex transition amplitudes indexed by the current control
state and scanned symbol, movement, new control state, and written symbol. -/
structure Rule (Q A : Type*) where
  blank : A
  amplitude : Q → A → Move → Q → A → ℂ

/-- The configuration obtained by writing `a` at the current head, moving by `m.offset`, and
setting the control state to `q`. -/
def target {Q A : Type*} {blank : A} (c : Config Q A blank) (m : Move) (q : Q) (a : A) : Config Q A blank :=
  ⟨q, c.tape.write c.head a, c.head + m.offset⟩

/-- The finite superposition of target configurations weighted by a rule's transition amplitudes
from `c`. -/
noncomputable def Rule.column {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (c : Config Q A R.blank) : State Q A R.blank :=
  ∑ t : Move × Q × A, R.amplitude c.state (c.tape c.head) t.1 t.2.1 t.2.2 • ket (target c t.1 t.2.1 t.2.2)

/-- The condition that a rule's transition columns are realized on configuration basis vectors
by a complex linear isometric equivalence of the full state space. -/
def Rule.GloballyWellformed {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A) : Prop :=
  ∃ U : State Q A R.blank ≃ₗᵢ[ℂ] State Q A R.blank, ∀ c, U (ket c) = R.column c

/-- The configuration with control state `q`, head at zero, and an otherwise blank tape with
symbol `a` written at zero. -/
def canonicalConfig {Q A : Type*} (blank : A) (q : Q) (a : A) : Config Q A blank :=
  ⟨q, (Tape.empty blank).write 0 a, 0⟩

/-- The configuration determined by an output triple, with its symbol written at zero and its
head at the movement offset. -/
def localOutput {Q A : Type*} (blank : A) (t : Move × Q × A) : Config Q A blank :=
  ⟨t.2.1, (Tape.empty blank).write 0 t.2.2, t.1.offset⟩

/-- Applying a local transition to a canonical configuration gives the configuration encoded by
its output triple. -/
theorem target_canonical {Q A : Type*} (blank : A) (q : Q) (a : A) (t : Move × Q × A) :
    target (canonicalConfig blank q a) t.1 t.2.1 t.2.2 = localOutput blank t := by
  apply Config.ext
  · rfl
  · exact Tape.write_write _ _ _ _
  · simp [target, canonicalConfig, localOutput]

/-- The configuration encoded by a local output uniquely determines its movement, control state,
and written symbol. -/
theorem localOutput_injective {Q A : Type*} (blank : A) : Function.Injective (localOutput (Q := Q) blank) := by
  intro a b h
  have hm := Move.offset_injective (congrArg Config.head h)
  have hq := congrArg Config.state h
  have hb := congrArg (fun c : Config Q A blank => c.tape 0) h
  simp only [localOutput, Tape.write_same] at hb
  exact Prod.ext hm (Prod.ext hq hb)

/-- A canonical configuration uniquely determines its control state and symbol at zero. -/
theorem canonicalConfig_injective {Q A : Type*} (blank : A) :
    Function.Injective (fun p : Q × A => canonicalConfig blank p.1 p.2) := by
  intro a b h
  have hq := congrArg Config.state h
  have ha := congrArg (fun c : Config Q A blank => c.tape 0) h
  simp only [canonicalConfig, Tape.write_same] at ha
  exact Prod.ext hq ha

/-- The inner product of two configuration basis vectors is one when their configurations
coincide and zero otherwise. -/
theorem ket_inner {Q A : Type*} {blank : A} (c d : Config Q A blank) :
    inner ℂ (ket c) (ket d) = if c = d then 1 else 0 := by
  classical
  simp [ket, lp.inner_single_left, lp.single_apply, Pi.single_apply]

/-- The configuration basis vectors form an orthonormal family. -/
theorem ket_orthonormal {Q A : Type*} (blank : A) : Orthonormal ℂ (ket (Q := Q) (blank := blank)) := by
  classical
  rw [orthonormal_iff_ite]
  exact ket_inner

/-- The transition columns of a globally well-formed rule have inner product one for identical
source configurations and zero otherwise. -/
theorem Rule.column_inner_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (c d : Config Q A R.blank) :
    inner ℂ (R.column c) (R.column d) = if c = d then 1 else 0 := by
  obtain ⟨U, hU⟩ := h
  rw [← hU, ← hU, U.inner_map_map, ket_inner]

/-- The column at a canonical configuration is the sum of local-output basis vectors weighted by
the corresponding transition amplitudes. -/
theorem Rule.column_canonical {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (q : Q) (a : A) :
    R.column (canonicalConfig R.blank q a) =
      ∑ t : Move × Q × A, R.amplitude q a t.1 t.2.1 t.2.2 • ket (localOutput R.blank t) := by
  unfold Rule.column
  simp only [target_canonical]
  rfl

/-- For a globally well-formed rule, the local amplitude vectors indexed by input control-symbol
pairs are orthonormal. This is a local constraint in the quantum machine framework of
[BernsteinVazirani1997]. -/
theorem Rule.local_inner_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ : A) :
    (∑ t : Move × Q × A,
      star (R.amplitude q₁ a₁ t.1 t.2.1 t.2.2) * R.amplitude q₂ a₂ t.1 t.2.1 t.2.2) =
      if (q₁, a₁) = (q₂, a₂) then 1 else 0 := by
  classical
  obtain ⟨U, hU⟩ := h
  have hv : Orthonormal ℂ (fun t : Move × Q × A => ket (localOutput R.blank t)) :=
    (ket_orthonormal (Q := Q) R.blank).comp (localOutput R.blank) (localOutput_injective R.blank)
  calc
    _ = inner ℂ (R.column (canonicalConfig R.blank q₁ a₁)) (R.column (canonicalConfig R.blank q₂ a₂)) := by
      rw [R.column_canonical, R.column_canonical]
      exact (hv.inner_sum _ _ Finset.univ).symm
    _ = inner ℂ (ket (canonicalConfig R.blank q₁ a₁)) (ket (canonicalConfig R.blank q₂ a₂)) := by
      rw [← hU, ← hU, U.inner_map_map]
    _ = _ := by
      rw [ket_inner]
      congr 1
      apply propext
      constructor
      · intro hx
        exact @canonicalConfig_injective Q A R.blank (q₁, a₁) (q₂, a₂) hx
      · intro h
        exact congrArg (fun p : Q × A => canonicalConfig R.blank p.1 p.2) h

/-- The squared norms of all local transition amplitudes from a fixed control-symbol pair sum to
one for a globally well-formed rule. -/
theorem Rule.local_norm_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q : Q) (a : A) :
    ∑ t : Move × Q × A, ‖R.amplitude q a t.1 t.2.1 t.2.2‖ ^ 2 = 1 := by
  have hz (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    simpa only [RCLike.inner_apply, mul_comm] using! (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  have hh := congrArg Complex.re (R.local_inner_of_global h q q a a)
  simpa only [ite_true, Complex.re_sum, hz, Complex.one_re] using! hh

/-- Local transition amplitude vectors from distinct control-symbol pairs have zero inner
product for a globally well-formed rule. -/
theorem Rule.local_sameCell_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ : A)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    ∑ t : Move × Q × A,
      star (R.amplitude q₁ a₁ t.1 t.2.1 t.2.2) * R.amplitude q₂ a₂ t.1 t.2.1 t.2.2 = 0 := by
  simpa only [if_neg hne] using! R.local_inner_of_global h q₁ q₂ a₁ a₂

/-- The complex linear equivalence of square-summable sequence spaces induced by reindexing
along `e`. -/
noncomputable def hilbertReindexLinear {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : ι => ℂ) 2 ≃ₗ[ℂ] lp (fun _ : κ => ℂ) 2 where
  toFun f := ⟨fun j => f (e.symm j), memℓp_gen (e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num)))⟩
  invFun g := ⟨fun i => g (e i), memℓp_gen (e.summable_iff.mpr ((lp.memℓp g).summable (by norm_num)))⟩
  left_inv f := by ext i; exact congrArg (fun j => f j) (e.symm_apply_apply i)
  right_inv f := by ext i; exact congrArg (fun j => f j) (e.apply_symm_apply i)
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl

/-- The complex linear isometric equivalence induced by reindexing square-summable amplitudes
along `e`. -/
noncomputable def hilbertReindex {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2 :=
  (hilbertReindexLinear e).isometryOfInner (by
    intro f g
    simp only [lp.inner_eq_tsum]
    exact e.symm.tsum_eq (fun i => inner ℂ (f i) (g i)))

/-- The amplitude at `j` after reindexing along `e` is the original amplitude at `e.symm j`. -/
@[simp] theorem hilbertReindex_apply {ι κ : Type*} (e : ι ≃ κ) (f : lp (fun _ : ι => ℂ) 2) (j : κ) :
    hilbertReindex e f j = f (e.symm j) := rfl

/-- Reindexing sends a vector supported at `i` with amplitude `a` to the vector supported at `e
i` with the same amplitude. -/
theorem hilbertReindex_single {ι κ : Type*} (e : ι ≃ κ) (i : ι) (a : ℂ) :
    hilbertReindex e (lp.single 2 i a) = lp.single 2 (e i) a := by
  classical
  ext j
  by_cases h : e i = j
  · subst j
    simp [lp.single_apply, Pi.single_apply]
  · have hi : i ≠ e.symm j := by
      intro hh
      apply h
      rw [hh, e.apply_symm_apply]
    simp [lp.single_apply, h, hi]

/-- The configuration equivalence that adds `k` to the head position and leaves the control
state and tape unchanged. -/
def headTranslate {Q A : Type*} {blank : A} (k : ℤ) : Config Q A blank ≃ Config Q A blank where
  toFun c := ⟨c.state, c.tape, c.head + k⟩
  invFun c := ⟨c.state, c.tape, c.head - k⟩
  left_inv c := by ext <;> simp
  right_inv c := by ext <;> simp

/-- The deterministic transition rule that performs `move` while preserving the control state
and scanned symbol. -/
noncomputable def shiftRule (Q A : Type*) (blank : A) (move : Move) : Rule Q A where
  blank := blank
  amplitude q a d q' b := if (d, q', b) = (move, q, a) then 1 else 0

/-- Writing the symbol already present at a tape position leaves the tape unchanged. -/
theorem Tape.write_read {A : Type*} {blank : A} (T : Tape A blank) (h : ℤ) : T.write h (T h) = T := by
  apply Tape.ext
  intro i
  by_cases hi : i = h
  · subst i; simp
  · exact Tape.write_other T h i (T h) hi

/-- The deterministic head-shift rule is globally well-formed. -/
theorem shiftRule_globallyWellformed (Q A : Type*) [Fintype Q] [Fintype A] (blank : A) (move : Move) :
    (shiftRule Q A blank move).GloballyWellformed := by
  classical
  refine ⟨hilbertReindex (headTranslate move.offset), ?_⟩
  intro c
  change hilbertReindex (headTranslate move.offset) (lp.single 2 c 1) = _
  rw [hilbertReindex_single]
  have hc : (shiftRule Q A blank move).column c = ket (target c move c.state (c.tape c.head)) := by
    unfold Rule.column
    rw [Finset.sum_eq_single (move, c.state, c.tape c.head)]
    · simp only [shiftRule, ite_true]
      ext x
      exact one_mul _
    · intro b _ hb
      rcases b with ⟨d, q, a⟩
      change (if (d, q, a) = (move, c.state, c.tape c.head) then (1 : ℂ) else 0) • ket
          (target c d q a) = 0
      rw [if_neg hb]
      exact zero_smul ℂ _
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hc]
  change ket ((headTranslate move.offset) c) = ket (target c move c.state (c.tape c.head))
  congr 1
  apply Config.ext
  · rfl
  · exact (Tape.write_read c.tape c.head).symm
  · rfl

/-- Writes to two distinct tape positions commute. -/
theorem Tape.write_comm {A : Type*} {blank : A} (T : Tape A blank) (i j : ℤ) (a b : A)
    (h : i ≠ j) : (T.write i a).write j b = (T.write j b).write i a := by
  apply Tape.ext
  intro k
  by_cases hi : k = i
  · subst k
    rw [Tape.write_other _ _ _ _ h, Tape.write_same, Tape.write_same]
  · by_cases hj : k = j
    · subst k
      rw [Tape.write_same, Tape.write_other _ _ _ _ h.symm, Tape.write_same]
    · rw [Tape.write_other _ _ _ _ hj, Tape.write_other _ _ _ _ hi,
        Tape.write_other _ _ _ _ hi, Tape.write_other _ _ _ _ hj]

/-- The tape obtained from the blank tape by writing `a` at zero and then `b` at `gap`. -/
def Tape.pair {A : Type*} (blank : A) (gap : ℤ) (a b : A) : Tape A blank :=
  ((Tape.empty blank).write 0 a).write gap b

/-- If `gap` is nonzero, the paired tape contains `a` at zero. -/
theorem Tape.pair_zero {A : Type*} (blank : A) (gap : ℤ) (a b : A) (hg : gap ≠ 0) :
    Tape.pair blank gap a b 0 = a := by
  rw [Tape.pair, Tape.write_other _ _ _ _ hg.symm, Tape.write_same]

/-- The paired tape contains `b` at `gap`. -/
theorem Tape.pair_gap {A : Type*} (blank : A) (gap : ℤ) (a b : A) :
    Tape.pair blank gap a b gap = b := Tape.write_same _ _ _

/-- For nonzero `gap`, writing `c` at zero in a paired tape replaces its first symbol by `c`. -/
theorem Tape.pair_write_zero {A : Type*} (blank : A) (gap : ℤ) (a b c : A) (hg : gap ≠ 0) :
    (Tape.pair blank gap a b).write 0 c = Tape.pair blank gap c b := by
  rw [Tape.pair, Tape.write_comm _ gap 0 b c hg, Tape.write_write]
  rfl

/-- Writing `c` at `gap` in a paired tape replaces its second symbol by `c`. -/
theorem Tape.pair_write_gap {A : Type*} (blank : A) (gap : ℤ) (a b c : A) :
    (Tape.pair blank gap a b).write gap c = Tape.pair blank gap a c := Tape.write_write _ _ _ _

/-- The configuration with control state `q`, specified head position, and the paired tape
carrying `a` at zero before writing `b` at `gap`. -/
def twoCellConfig {Q A : Type*} (blank : A) (gap head : ℤ) (q : Q) (a b : A) : Config Q A blank :=
  ⟨q, Tape.pair blank gap a b, head⟩

/-- For the stated configurations with heads separated by a nonzero gap, two transition targets
coincide exactly when their output control states agree, each written symbol matches the
other tape, and `m.offset = gap + n.offset`. -/
theorem target_twoCell_collision {Q A : Type*} (blank : A) (gap : ℤ) (hg : gap ≠ 0)
    (q₁ q₂ q r : Q) (a₁ a₂ b₁ b₂ x y : A) (m n : Move) :
    target (twoCellConfig blank gap 0 q₁ a₁ b₂) m q x =
      target (twoCellConfig blank gap gap q₂ b₁ a₂) n r y ↔
      q = r ∧ x = b₁ ∧ y = b₂ ∧ m.offset = gap + n.offset := by
  constructor
  · intro h
    have hs := congrArg Config.state h
    have h0 := congrArg (fun c : Config Q A blank => c.tape 0) h
    have hk := congrArg (fun c : Config Q A blank => c.tape gap) h
    have hh := congrArg Config.head h
    change x = ((Tape.pair blank gap b₁ a₂).write gap y) 0 at h0
    rw [Tape.write_other _ _ _ _ hg.symm, Tape.pair_zero _ _ _ _ hg] at h0
    change ((Tape.pair blank gap a₁ b₂).write 0 x) gap =
        ((Tape.pair blank gap b₁ a₂).write gap y) gap at hk
    rw [Tape.write_same, Tape.write_other _ _ _ _ hg, Tape.pair_gap] at hk
    exact ⟨hs, h0, hk.symm, by simpa [target, twoCellConfig] using! hh⟩
  · rintro ⟨hq, hx, hy, hh⟩
    subst r
    subst x
    subst y
    apply Config.ext
    · rfl
    · change (Tape.pair blank gap a₁ b₂).write 0 b₁ = (Tape.pair blank gap b₁ a₂).write gap b₂
      rw [Tape.pair_write_zero _ _ _ _ _ hg, Tape.pair_write_gap]
    · simpa [target, twoCellConfig] using! hh

/-- The inner product of two transition columns is the sum of products of their amplitudes over
pairs of transitions with equal target configurations. -/
theorem Rule.column_inner_expansion {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (c d : Config Q A R.blank) :
    inner ℂ (R.column c) (R.column d) =
      ∑ s : Move × Q × A, ∑ t : Move × Q × A,
        if target c s.1 s.2.1 s.2.2 = target d t.1 t.2.1 t.2.2 then
          star (R.amplitude c.state (c.tape c.head) s.1 s.2.1 s.2.2) *
            R.amplitude d.state (d.tape d.head) t.1 t.2.1 t.2.2 else 0 := by
  unfold Rule.column
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro s _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [inner_smul_left, inner_smul_right, ket_inner]
  split_ifs <;> simp

/-- For the specified two-cell configurations with nonzero head gap, the column inner product is
the sum of amplitude products whose movements satisfy `m.offset = gap + n.offset`. -/
theorem Rule.twoCell_inner {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (gap : ℤ) (hg : gap ≠ 0) (q₁ q₂ : Q) (a₁ a₂ b₁ b₂ : A) :
    inner ℂ (R.column (twoCellConfig R.blank gap 0 q₁ a₁ b₂))
      (R.column (twoCellConfig R.blank gap gap q₂ b₁ a₂)) =
      ∑ m : Move, ∑ q : Q, ∑ n : Move,
        if m.offset = gap + n.offset then
          star (R.amplitude q₁ a₁ m q b₁) * R.amplitude q₂ a₂ n q b₂ else 0 := by
  rw [Rule.column_inner_expansion]
  simp only [target_twoCell_collision R.blank gap hg, Fintype.sum_prod_type]
  simp only [twoCellConfig, Tape.pair_zero _ _ _ _ hg, Tape.pair_gap]
  simp [ite_and, Finset.sum_ite_irrel]

/-- A sum over all movements is the sum of its left, stationary, and right terms. -/
theorem Move.sum_univ {M : Type*} [AddCommMonoid M] (f : Move → M) :
    ∑ m : Move, f m = f .left + f .stay + f .right := by
  have hu : (Finset.univ : Finset Move) = {.left, .stay, .right} := by decide
  rw [hu]
  simp [add_assoc]

/-- For a globally well-formed rule and a nonzero head gap, the sum of local amplitude products
over movements that produce coincident heads is zero. -/
theorem Rule.crossHead_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (gap : ℤ) (hg : gap ≠ 0)
    (q₁ q₂ : Q) (a₁ a₂ b₁ b₂ : A) :
    ∑ m : Move, ∑ q : Q, ∑ n : Move,
      (if m.offset = gap + n.offset then
        star (R.amplitude q₁ a₁ m q b₁) * R.amplitude q₂ a₂ n q b₂ else 0) = 0 := by
  have hn : twoCellConfig R.blank gap 0 q₁ a₁ b₂ ≠ twoCellConfig R.blank gap gap q₂ b₁ a₂ := by
    intro he
    have hh := congrArg Config.head he
    exact hg hh.symm
  have he := R.column_inner_of_global h (twoCellConfig R.blank gap 0 q₁ a₁ b₂)
    (twoCellConfig R.blank gap gap q₂ b₁ a₂)
  rw [if_neg hn, R.twoCell_inner gap hg] at he
  exact he

/-- Global well-formedness forces the sum of the right-stationary and stationary-left amplitude
inner products to vanish for the stated input and written symbols. -/
theorem Rule.local_adjacent_gram_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ b₁ b₂ : A) :
    ∑ q : Q, (star (R.amplitude q₁ a₁ .right q b₁) * R.amplitude q₂ a₂ .stay q b₂ +
      star (R.amplitude q₁ a₁ .stay q b₁) * R.amplitude q₂ a₂ .left q b₂) = 0 := by
  have he := R.crossHead_of_global h 1 (by decide) q₁ q₂ a₁ a₂ b₁ b₂
  simpa [Move.sum_univ, Move.offset, Finset.sum_add_distrib, add_comm] using! he

/-- For a globally well-formed rule, the sum of conjugate-right times left transition amplitudes
over output control states is zero. -/
theorem Rule.local_rightLeft_gram_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ b₁ b₂ : A) :
    ∑ q : Q, star (R.amplitude q₁ a₁ .right q b₁) * R.amplitude q₂ a₂ .left q b₂ = 0 := by
  have he := R.crossHead_of_global h 2 (by decide) q₁ q₂ a₁ a₂ b₁ b₂
  simpa [Move.sum_univ, Move.offset] using! he

/-- For a globally well-formed rule, the sum of right transition amplitudes times conjugate-left
amplitudes over output control states vanishes. This is a local orthogonality constraint
associated with [BernsteinVazirani1997]. -/
theorem Rule.local_rightLeft_of_global {Q A : Type*} [Fintype Q] [Fintype A]
    (R : Rule Q A) (h : R.GloballyWellformed) (q₁ q₂ : Q) (a₁ a₂ b₁ b₂ : A) :
    ∑ q : Q, R.amplitude q₁ a₁ .right q b₁ * star (R.amplitude q₂ a₂ .left q b₂) = 0 := by
  have he := congrArg star (R.local_rightLeft_gram_of_global h q₁ q₂ a₁ a₂ b₁ b₂)
  simpa using! he

/-- The vector of output-control amplitudes for a fixed input control state, scanned symbol,
movement, and written symbol. -/
noncomputable def Rule.restrictedVector {Q A : Type*} [Fintype Q] (R : Rule Q A)
    (m : Move) (p : Q) (a b : A) : EuclideanSpace ℂ Q :=
  WithLp.toLp 2 (fun q => R.amplitude p a m q b)

/-- The span of all output-control amplitude vectors associated with the movement `m`. -/
noncomputable def Rule.directionSpace {Q A : Type*} [Fintype Q] (R : Rule Q A) (m : Move) :
    Submodule ℂ (EuclideanSpace ℂ Q) :=
  Submodule.span ℂ (Set.range (fun v : Q × A × A => R.restrictedVector m v.1 v.2.1 v.2.2))

/-- Every restricted transition vector belongs to the span associated with its movement. -/
theorem Rule.restrictedVector_mem {Q A : Type*} [Fintype Q] (R : Rule Q A) (m : Move) (p : Q) (a b : A) :
    R.restrictedVector m p a b ∈ R.directionSpace m :=
  Submodule.subset_span ⟨(p,a,b), rfl⟩

/-- For a globally well-formed rule, every right-moving restricted vector is orthogonal to every
left-moving restricted vector. -/
theorem Rule.restricted_right_left_inner {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (p r : Q) (a b c d : A) :
    inner ℂ (R.restrictedVector .right p a b) (R.restrictedVector .left r c d) = 0 := by
  change (∑ q : Q, R.amplitude r c .left q d * star (R.amplitude p a .right q b)) = 0
  simpa only [mul_comm] using! R.local_rightLeft_gram_of_global h p r a c b d

/-- The left-moving and right-moving output-control subspaces of a globally well-formed rule are
orthogonal. -/
theorem Rule.directionSpaces_orthogonal {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) : R.directionSpace .left ⟂ R.directionSpace .right := by
  apply Submodule.isOrtho_span.mpr
  rintro _ ⟨⟨p,a,b⟩, rfl⟩ _ ⟨⟨r,c,d⟩, rfl⟩
  exact inner_eq_zero_symm.mpr (R.restricted_right_left_inner h r p c d a b)

/-- The two control subspaces given by the left-moving span for false and its orthogonal
complement for true. -/
noncomputable def Rule.directionSplit {Q A : Type*} [Fintype Q] (R : Rule Q A) (side : Bool) :
    Submodule ℂ (EuclideanSpace ℂ Q) := if side then (R.directionSpace .left)ᗮ else R.directionSpace .left

/-- The left-moving subspace and its orthogonal complement form an internal direct sum of the
control space. -/
theorem Rule.directionSplit_internal {Q A : Type*} [Fintype Q] (R : Rule Q A) :
    DirectSum.IsInternal R.directionSplit := by
  apply (DirectSum.isInternal_submodule_iff_isCompl R.directionSplit (show false ≠ true by decide) (by ext side; cases side <;> simp)).mpr
  exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

set_option backward.isDefEq.respectTransparency true in

/-- The inclusions of the two direction-split subspaces form an orthogonal family. -/
theorem Rule.directionSplit_orthogonal {Q A : Type*} [Fintype Q] (R : Rule Q A) :
    OrthogonalFamily ℂ (fun side => R.directionSplit side) (fun side => (R.directionSplit side).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  change R.directionSplit i ⟂ R.directionSplit j
  cases i <;> cases j <;> simp_all [Rule.directionSplit]

/-- The index type for bases of the two direction-split subspaces, pairing a Boolean sector with
an index below that sector's complex dimension. -/
abbrev Rule.DirectionIndex {Q A : Type*} [Fintype Q] (R : Rule Q A) :=
  Σ side : Bool, Fin (Module.finrank ℂ (R.directionSplit side))

/-- An orthonormal basis of the control space assembled from orthonormal bases of the two
direction-split subspaces. -/
noncomputable def Rule.directionBasis {Q A : Type*} [Fintype Q] (R : Rule Q A) :
    OrthonormalBasis R.DirectionIndex ℂ (EuclideanSpace ℂ Q) :=
  R.directionSplit_internal.collectedOrthonormalBasis R.directionSplit_orthogonal
    (fun side => stdOrthonormalBasis ℂ (R.directionSplit side))

/-- Each direction-adapted basis vector lies in the subspace selected by its Boolean sector. -/
theorem Rule.directionBasis_mem {Q A : Type*} [Fintype Q] (R : Rule Q A) (i : R.DirectionIndex) :
    R.directionBasis i ∈ R.directionSplit i.1 :=
  R.directionSplit_internal.collectedOrthonormalBasis_mem R.directionSplit_orthogonal
    (fun side => stdOrthonormalBasis ℂ (R.directionSplit side)) i

/-- The direction-adapted basis has as many indices as the original control-state type. -/
theorem Rule.directionBasis_card {Q A : Type*} [Fintype Q] (R : Rule Q A) :
    Fintype.card R.DirectionIndex = Fintype.card Q := by
  rw [← Module.finrank_eq_card_basis R.directionBasis.toBasis]
  simp

/-- Every left-moving restricted vector has zero coordinate at a direction-basis index in the
true sector. -/
theorem Rule.directionBasis_left_zero {Q A : Type*} [Fintype Q] (R : Rule Q A) (i : R.DirectionIndex)
    (hi : i.1 = true) (p : Q) (a b : A) :
    R.directionBasis.repr (R.restrictedVector .left p a b) i = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  have hm := R.directionBasis_mem i
  rw [hi] at hm
  exact (R.directionSpace .left).inner_left_of_mem_orthogonal
      (R.restrictedVector_mem .left p a b) hm

/-- For a globally well-formed rule, every right-moving restricted vector has zero coordinate at
a direction-basis index in the false sector. -/
theorem Rule.directionBasis_right_zero {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (i : R.DirectionIndex) (hi : i.1 = false) (p : Q) (a b : A) :
    R.directionBasis.repr (R.restrictedVector .right p a b) i = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  have hm := R.directionBasis_mem i
  rw [hi] at hm
  exact (R.directionSpaces_orthogonal h).inner_eq hm (R.restrictedVector_mem .right p a b)

/-- The transition rule expressed in the direction-adapted control basis. -/
noncomputable def Rule.basisChanged {Q A : Type*} [Fintype Q] (R : Rule Q A) : Rule R.DirectionIndex A where
  blank := R.blank
  amplitude i a m j b := ∑ p : Q, R.directionBasis i p * R.directionBasis.repr (R.restrictedVector m p a b) j

/-- In the direction-adapted rule, every left-moving amplitude into the true sector vanishes. -/
theorem Rule.basisChanged_left_zero {Q A : Type*} [Fintype Q] (R : Rule Q A)
    (i j : R.DirectionIndex) (hj : j.1 = true) (a b : A) : R.basisChanged.amplitude i a .left j b = 0 := by
  change (∑ p : Q,
      R.directionBasis i p * R.directionBasis.repr (R.restrictedVector .left p a b) j) = 0
  apply Finset.sum_eq_zero
  intro p _
  rw [R.directionBasis_left_zero j hj p a b, mul_zero]

/-- For a globally well-formed rule, every right-moving amplitude into the false sector vanishes
after changing to the direction-adapted basis. -/
theorem Rule.basisChanged_right_zero {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (i j : R.DirectionIndex) (hj : j.1 = false) (a b : A) :
    R.basisChanged.amplitude i a .right j b = 0 := by
  change (∑ p : Q,
      R.directionBasis i p * R.directionBasis.repr (R.restrictedVector .right p a b) j) = 0
  apply Finset.sum_eq_zero
  intro p _
  rw [R.directionBasis_right_zero h j hj p a b, mul_zero]

/-- If all stationary amplitudes of a rule vanish, they also vanish after changing to the
direction-adapted basis. -/
theorem Rule.basisChanged_stay_zero {Q A : Type*} [Fintype Q] (R : Rule Q A)
    (hz : ∀ p a q b, R.amplitude p a .stay q b = 0) (i j : R.DirectionIndex) (a b : A) :
    R.basisChanged.amplitude i a .stay j b = 0 := by
  have hv (p : Q) : R.restrictedVector .stay p a b = 0 := by
    ext q
    exact hz p a q b
  change (∑ p : Q,
      R.directionBasis i p * R.directionBasis.repr (R.restrictedVector .stay p a b) j) = 0
  apply Finset.sum_eq_zero
  intro p _
  simp [hv]

/-- For a globally well-formed rule with no stationary transitions, a nonzero amplitude after
the direction-basis change moves right into a true-sector state and left into a false-sector
state. -/
theorem Rule.basisChanged_direction_of_noStay {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (hz : ∀ p a q b, R.amplitude p a .stay q b = 0)
    (i j : R.DirectionIndex) (a b : A) (m : Move) (hn : R.basisChanged.amplitude i a m j b ≠ 0) :
    m = if j.1 then Move.right else Move.left := by
  cases m with
  | left =>
    by_cases hj : j.1 = true
    · exact False.elim (hn (R.basisChanged_left_zero i j hj a b))
    · have hf : j.1 = false := Bool.eq_false_iff.mpr hj
      simp [hf]
  | stay => exact False.elim (hn (R.basisChanged_stay_zero hz i j a b))
  | right =>
    by_cases hj : j.1 = false
    · exact False.elim (hn (R.basisChanged_right_zero h i j hj a b))
    · have ht : j.1 = true := by cases he : j.1 <;> simp_all
      simp [ht]

/-- The standard square-summable basis vector with amplitude one at `i`. -/
noncomputable def l2Ket {ι : Type*} (i : ι) : lp (fun _ : ι => ℂ) 2 := lp.single 2 i 1

/-- The inner product of standard square-summable basis vectors is one for equal indices and
zero otherwise. -/
theorem l2Ket_inner {ι : Type*} (i j : ι) : inner ℂ (l2Ket i) (l2Ket j) = if i = j then 1 else 0 := by
  simp [l2Ket, lp.inner_single_left, lp.single_apply, Pi.single_apply]

/-- The linear embedding of a finite control vector into the slice with fixed second coordinate
`k` in the square-summable product space. -/
noncomputable def l2Slice {Q κ : Type*} [Fintype Q] (k : κ) :
    EuclideanSpace ℂ Q →ₗ[ℂ] lp (fun _ : Q × κ => ℂ) 2 where
  toFun f := ∑ q : Q, f q • l2Ket (q,k)
  map_add' f g := by
    change (∑ q : Q, (f q + g q) • l2Ket (q,k)) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a f := by
    change (∑ q : Q, (a * f q) • l2Ket (q,k)) = a • ∑ q : Q, f q • l2Ket (q,k)
    simp only [mul_smul, Finset.smul_sum]

/-- The slice embedding is the sum of standard product basis vectors weighted by the control
coordinates. -/
theorem l2Slice_apply {Q κ : Type*} [Fintype Q] (k : κ) (f : EuclideanSpace ℂ Q) :
    l2Slice k f = ∑ q : Q, f q • l2Ket (q,k) := rfl

/-- Embedding a single control coordinate with amplitude `a` into slice `k` gives `a` times the
product basis vector at `(q, k)`. -/
theorem l2Slice_single {Q κ : Type*} [Fintype Q] [DecidableEq Q] (k : κ) (q : Q) (a : ℂ) :
    l2Slice k (EuclideanSpace.single q a) = a • l2Ket (q,k) := by
  rw [l2Slice_apply, Finset.sum_eq_single q]
  · simp
  · intro r _ hr
    simp [hr]
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

/-- The embedding into a fixed slice preserves inner products. -/
theorem l2Slice_inner {Q κ : Type*} [Fintype Q] (k : κ) (f g : EuclideanSpace ℂ Q) :
    inner ℂ (l2Slice k f) (l2Slice k g) = inner ℂ f g := by
  have hv : Orthonormal ℂ (fun q : Q => l2Ket (q,k)) := by
    rw [orthonormal_iff_ite]
    intro q r
    rw [l2Ket_inner]
    simp
  rw [l2Slice_apply, l2Slice_apply, hv.inner_sum _ _ Finset.univ]
  change (∑ q : Q, star (f q) * g q) = ∑ q : Q, g q * star (f q)
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Vectors embedded into slices with distinct second coordinates are orthogonal. -/
theorem l2Slice_disjoint_inner {Q κ : Type*} [Fintype Q] (k l : κ) (h : k ≠ l)
    (f g : EuclideanSpace ℂ Q) : inner ℂ (l2Slice k f) (l2Slice l g) = 0 := by
  rw [l2Slice_apply, l2Slice_apply, sum_inner]
  apply Finset.sum_eq_zero
  intro q _
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro r _
  rw [inner_smul_left, inner_smul_right, l2Ket_inner, if_neg (fun he => h (congrArg Prod.snd he))]
  simp only [mul_zero]

/-- The vector obtained by embedding the basis vector `b ik.1` into the slice indexed by `ik.2`. -/
noncomputable def rotatedL2Ket {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (ik : I × κ) : lp (fun _ : Q × κ => ℂ) 2 :=
  l2Slice ik.2 (b ik.1)

/-- The vectors obtained by placing an orthonormal control basis in every slice form an
orthonormal family. -/
theorem rotatedL2Ket_orthonormal {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) : Orthonormal ℂ (rotatedL2Ket (κ := κ) b) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,k⟩ ⟨j,l⟩
  by_cases h : k = l
  · subst l
    rw [rotatedL2Ket, rotatedL2Ket, l2Slice_inner, b.inner_eq_ite]
    simp
  · rw [rotatedL2Ket, rotatedL2Ket, l2Slice_disjoint_inner k l h]
    rw [if_neg (fun he => h (congrArg Prod.snd he))]

/-- Each standard product basis vector is the finite sum of rotated slice vectors weighted by
its coordinates in `b`. -/
theorem rotatedL2Ket_reconstruct {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (q : Q) (k : κ) :
    ∑ i : I, b.repr (EuclideanSpace.single q 1) i • rotatedL2Ket b (i,k) = l2Ket (q,k) := by
  calc
    _ = l2Slice k (∑ i : I, b.repr (EuclideanSpace.single q 1) i • b i) := by rw [map_sum]; simp only [map_smul, rotatedL2Ket]
    _ = _ := by rw [b.sum_repr, l2Slice_single, one_smul]

/-- The linear span of the rotated slice vectors is dense in the square-summable product space. -/
theorem rotatedL2Ket_dense {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (rotatedL2Ket (κ := κ) b))).topologicalClosure := by
  let canon : HilbertBasis (Q × κ) ℂ (lp (fun _ : Q × κ => ℂ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs : Submodule.span ℂ (Set.range canon) ≤ Submodule.span ℂ (Set.range (rotatedL2Ket (κ := κ) b)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨q,k⟩, rfl⟩
    change l2Ket (q,k) ∈ _
    rw [← rotatedL2Ket_reconstruct b q k]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,k), rfl⟩)
  have hc := Submodule.topologicalClosure_mono hs
  rw [canon.dense_span] at hc
  exact hc

/-- The Hilbert basis of the square-summable product space obtained by rotating the control
basis in every slice. -/
noncomputable def rotatedL2Basis {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) : HilbertBasis (I × κ) ℂ (lp (fun _ : Q × κ => ℂ) 2) :=
  HilbertBasis.mk (rotatedL2Ket_orthonormal b) (rotatedL2Ket_dense b)

/-- The linear isometric equivalence that applies the control basis `b` on each slice of a
square-summable product space. -/
noncomputable def liftL2Basis {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) :
    lp (fun _ : I × κ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Q × κ => ℂ) 2 := (rotatedL2Basis b).repr.symm

/-- The lifted basis transformation sends the standard vector at `(i, k)` to the sum at slice
`k` weighted by the coordinates of `b i`. -/
theorem liftL2Basis_single {I Q κ : Type*} [Fintype I] [Fintype Q]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (i : I) (k : κ) :
    liftL2Basis b (l2Ket (i,k)) = ∑ q : Q, b i q • l2Ket (q,k) := by
  letI : DecidableEq (I × κ) := Classical.typeDecidableEq _
  change (rotatedL2Basis (κ := κ) b).repr.symm (lp.single 2 (i,k) 1) = _
  rw [HilbertBasis.repr_symm_single]
  change (HilbertBasis.mk (rotatedL2Ket_orthonormal b) (rotatedL2Ket_dense b)) (i,k) = _
  rw [HilbertBasis.coe_mk]
  rfl

/-- Reindexing sends the standard basis vector at `i` to the standard basis vector at `e i`. -/
theorem hilbertReindex_l2Ket {ι κ : Type*} (e : ι ≃ κ) (i : ι) :
    hilbertReindex e (l2Ket i) = l2Ket (e i) := hilbertReindex_single e i 1

/-- The equivalence between configurations and tuples of a control state, tape, and head
position. -/
def configCoordinates {Q A : Type*} {blank : A} : Config Q A blank ≃ Q × (Tape A blank × ℤ) where
  toFun c := (c.state, c.tape, c.head)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨q,T,h⟩; rfl

/-- The linear embedding of a control vector into machine states with fixed tape `T` and head
position `h`. -/
noncomputable def controlSlice {Q A : Type*} [Fintype Q] {blank : A} (T : Tape A blank) (h : ℤ) :
    EuclideanSpace ℂ Q →ₗ[ℂ] State Q A blank :=
  (hilbertReindex (configCoordinates (Q := Q) (blank := blank)).symm).toLinearEquiv.toLinearMap.comp (l2Slice (T,h))

/-- A control slice is the sum of configuration basis vectors with fixed tape and head, weighted
by the control vector's coordinates. -/
theorem controlSlice_apply {Q A : Type*} [Fintype Q] {blank : A} (T : Tape A blank) (h : ℤ) (v : EuclideanSpace ℂ Q) :
    controlSlice T h v = ∑ q : Q, v q • ket ⟨q,T,h⟩ := by
  unfold controlSlice
  change hilbertReindex configCoordinates.symm (l2Slice (T,h) v) = _
  rw [l2Slice_apply, map_sum]
  simp only [map_smul, hilbertReindex_l2Ket]
  rfl

/-- Embedding a single control coordinate with amplitude `a` gives `a` times the corresponding
configuration basis vector. -/
theorem controlSlice_single {Q A : Type*} [Fintype Q] [DecidableEq Q] {blank : A} (T : Tape A blank) (h : ℤ) (q : Q) (a : ℂ) :
    controlSlice T h (EuclideanSpace.single q a) = a • ket ⟨q,T,h⟩ := by
  unfold controlSlice
  change hilbertReindex configCoordinates.symm (l2Slice (T,h) (EuclideanSpace.single q a)) = _
  rw [l2Slice_single, map_smul, hilbertReindex_l2Ket]
  rfl

/-- The linear isometric equivalence applying the orthonormal basis transformation `b` to the
control component of a machine state. -/
noncomputable def controlBasisLift {I Q A : Type*} [Fintype I] [Fintype Q] {blank : A}
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) : State I A blank ≃ₗᵢ[ℂ] State Q A blank :=
  ((hilbertReindex (configCoordinates (Q := I) (blank := blank))).trans (liftL2Basis b)).trans
    (hilbertReindex (configCoordinates (Q := Q) (blank := blank)).symm)

/-- The control-basis lift sends a configuration basis vector to the sum of configurations
weighted by its transformed control vector, with tape and head unchanged. -/
theorem controlBasisLift_ket {I Q A : Type*} [Fintype I] [Fintype Q] {blank : A}
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (c : Config I A blank) :
    controlBasisLift b (ket c) = ∑ q : Q, b c.state q • ket ⟨q,c.tape,c.head⟩ := by
  change hilbertReindex configCoordinates.symm
      (liftL2Basis b (hilbertReindex configCoordinates (l2Ket c))) = _
  rw [hilbertReindex_l2Ket]
  change hilbertReindex configCoordinates.symm (liftL2Basis b (l2Ket (c.state,(c.tape,c.head)))) = _
  rw [liftL2Basis_single, map_sum]
  simp only [map_smul, hilbertReindex_l2Ket]
  rfl

/-- The control-basis lift of a configuration basis vector is the control slice of its basis
vector `b c.state`. -/
theorem controlBasisLift_ket_slice {I Q A : Type*} [Fintype I] [Fintype Q] {blank : A}
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (c : Config I A blank) :
    controlBasisLift b (ket c) = controlSlice c.tape c.head (b c.state) := by
  rw [controlBasisLift_ket, controlSlice_apply]

/-- The inverse control-basis lift expands a configuration basis vector using the
`b`-coordinates of its standard control vector. -/
theorem controlBasisLift_symm_ket {I Q A : Type*} [Fintype I] [Fintype Q] {blank : A}
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (c : Config Q A blank) :
    (controlBasisLift b).symm (ket c) =
      ∑ i : I, b.repr (EuclideanSpace.single c.state 1) i • ket ⟨i,c.tape,c.head⟩ := by
  apply (controlBasisLift b).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_sum]
  simp only [map_smul, controlBasisLift_ket_slice]
  have he := congrArg (controlSlice c.tape c.head) (b.sum_repr (EuclideanSpace.single c.state 1))
  rw [map_sum] at he
  simp only [map_smul] at he
  rw [controlSlice_single, one_smul] at he
  cases c
  exact he.symm

/-- Applying the control-basis lift to a control slice replaces its control vector `v` by
`b.repr.symm v`. -/
theorem controlBasisLift_slice {I Q A : Type*} [Fintype I] [Fintype Q] {blank : A}
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (T : Tape A blank) (h : ℤ) (v : EuclideanSpace ℂ I) :
    controlBasisLift b (controlSlice T h v) = controlSlice T h (b.repr.symm v) := by
  have he := congrArg (controlSlice (Q := Q) T h) (b.sum_repr_symm v)
  rw [map_sum] at he
  simp only [map_smul] at he
  rw [controlSlice_apply, map_sum]
  simp only [map_smul, controlBasisLift_ket_slice]
  exact he

/-- The local transition rule obtained by expressing both input and output control states in the
orthonormal basis `b`. -/
noncomputable def Rule.changeBasis {I Q A : Type*} [Fintype I] [Fintype Q] (R : Rule Q A)
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) : Rule I A where
  blank := R.blank
  amplitude i a m j c := b.repr (∑ p : Q, b i p • R.restrictedVector m p a c) j

/-- A restricted vector of the changed rule is the `b`-coordinate vector of the original
restricted vectors combined with the input basis coefficients. -/
theorem Rule.changeBasis_restricted {I Q A : Type*} [Fintype I] [Fintype Q] (R : Rule Q A)
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (i : I) (a c : A) (m : Move) :
    (R.changeBasis b).restrictedVector m i a c = b.repr (∑ p : Q, b i p • R.restrictedVector m p a c) := by
  ext j
  rfl

/-- A transition column decomposes into control slices indexed by movement and written symbol,
with the corresponding restricted transition vectors as coefficients. -/
theorem Rule.column_as_slices {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A) (c : Config Q A R.blank) :
    R.column c = ∑ m : Move, ∑ a : A,
      controlSlice (c.tape.write c.head a) (c.head+m.offset) (R.restrictedVector m c.state (c.tape c.head) a) := by
  unfold Rule.column
  simp only [Fintype.sum_prod_type, controlSlice_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  rfl

/-- A global isometric equivalence realizing the rule sends a control slice to the sum of
updated tape-and-head slices whose control vectors are the corresponding linear combinations
of restricted transition vectors. -/
theorem Rule.controlSlice_evolve {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (U : State Q A R.blank ≃ₗᵢ[ℂ] State Q A R.blank) (hU : ∀ c, U (ket c) = R.column c)
    (T : Tape A R.blank) (h : ℤ) (v : EuclideanSpace ℂ Q) :
    U (controlSlice T h v) = ∑ m : Move, ∑ a : A,
      controlSlice (T.write h a) (h+m.offset) (∑ p : Q, v p • R.restrictedVector m p (T h) a) := by
  rw [controlSlice_apply, map_sum]
  simp only [map_smul, hU, Rule.column_as_slices, Finset.smul_sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]

/-- Lifting a transition column of the changed rule gives the sum of original-coordinate output
slices weighted by the input basis coefficients. -/
theorem Rule.changeBasis_column_lift {I Q A : Type*} [Fintype I] [Fintype Q] [Fintype A] (R : Rule Q A)
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (c : Config I A R.blank) :
    controlBasisLift b ((R.changeBasis b).column c) = ∑ m : Move, ∑ a : A,
      controlSlice (c.tape.write c.head a) (c.head+m.offset)
        (∑ p : Q, b c.state p • R.restrictedVector m p (c.tape c.head) a) := by
  rw [Rule.column_as_slices, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [controlBasisLift_slice, Rule.changeBasis_restricted, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- A global evolution realizing the original rule intertwines with the control-basis lift on
every basis configuration of the changed rule. -/
theorem Rule.changeBasis_column_compat {I Q A : Type*} [Fintype I] [Fintype Q] [Fintype A] (R : Rule Q A)
    (U : State Q A R.blank ≃ₗᵢ[ℂ] State Q A R.blank) (hU : ∀ c, U (ket c) = R.column c)
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) (c : Config I A R.blank) :
    U (controlBasisLift b (ket c)) = controlBasisLift b ((R.changeBasis b).column c) := by
  rw [controlBasisLift_ket_slice, R.controlSlice_evolve U hU, R.changeBasis_column_lift]

/-- Changing a rule's control basis preserves global well-formedness. -/
theorem Rule.changeBasis_globallyWellformed {I Q A : Type*} [Fintype I] [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ Q)) :
    (R.changeBasis b).GloballyWellformed := by
  obtain ⟨U,hU⟩ := h
  refine ⟨((controlBasisLift b).trans U).trans (controlBasisLift b).symm, ?_⟩
  intro c
  apply (controlBasisLift b).injective
  change controlBasisLift b ((controlBasisLift b).symm (U (controlBasisLift b (ket c)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, controlBasisLift_ket_slice,
    R.controlSlice_evolve U hU, R.changeBasis_column_lift]

/-- The direction-adapted rule equals the general basis-change construction applied to the
direction basis. -/
theorem Rule.basisChanged_eq_changeBasis {Q A : Type*} [Fintype Q] (R : Rule Q A) :
    R.basisChanged = R.changeBasis R.directionBasis := by
  unfold Rule.basisChanged Rule.changeBasis
  congr 1
  funext i a m j c
  change (∑ p : Q, R.directionBasis i p * R.directionBasis.repr (R.restrictedVector m p a c) j) =
    R.directionBasis.repr (∑ p : Q, R.directionBasis i p • R.restrictedVector m p a c) j
  rw [map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]

/-- A globally well-formed rule remains globally well-formed after changing to its
direction-adapted control basis. This implements a basis-change step in
[BernsteinVazirani1997]. -/
theorem Rule.basisChanged_globallyWellformed {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) : R.basisChanged.GloballyWellformed := by
  rw [R.basisChanged_eq_changeBasis]
  exact R.changeBasis_globallyWellformed h R.directionBasis

/-- The rule with control transition coefficients `C`, fixed movement `m`, and no change to the
scanned tape symbol. -/
noncomputable def controlMoveRule (Q A : Type*) (blank : A) (C : Q → Q → ℂ) (m : Move) : Rule Q A where
  blank := blank
  amplitude p a d q b := if d = m ∧ b = a then C p q else 0

/-- The column of a control-and-movement rule is the sum of shifted-head configurations weighted
by `C c.state q`, with the tape unchanged. -/
theorem controlMoveRule_column {Q A : Type*} [Fintype Q] [Fintype A]
    (blank : A) (C : Q → Q → ℂ) (m : Move) (c : Config Q A blank) :
    (controlMoveRule Q A blank C m).column c = ∑ q : Q, C c.state q • ket ⟨q,c.tape,c.head+m.offset⟩ := by
  change (∑ i : Move × Q × A,
    (if i.1 = m ∧ i.2.2 = c.tape c.head then C c.state i.2.1 else 0) •
      (ket (target c i.1 i.2.1 i.2.2) : State Q A blank)) = _
  ext d
  simp only [Fintype.sum_prod_type, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
  simp [ite_mul, ite_and, Finset.sum_ite_irrel, target, Tape.write_read]

/-- The Hilbert-space head translation sends the basis vector of `c` to the basis vector of the
translated configuration. -/
theorem headTranslate_ket {Q A : Type*} {blank : A} (k : ℤ) (c : Config Q A blank) :
    hilbertReindex (headTranslate k) (ket c) = ket (headTranslate k c) :=
  hilbertReindex_l2Ket (headTranslate k) c

/-- The rule combining a fixed head movement with the control basis transformation `b`, or its
inverse when `inverse` is true. -/
noncomputable def basisMoveRule {Q A : Type*} [Fintype Q] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (inverse : Bool) (m : Move) : Rule Q A :=
  controlMoveRule Q A blank
    (if inverse then (fun p q => b.repr (EuclideanSpace.single p 1) q) else (fun p q => b p q)) m

/-- The linear isometric equivalence combining the specified head translation with the control
basis transformation, using its inverse when `inverse` is true. -/
noncomputable def basisMoveUnitary {Q A : Type*} [Fintype Q] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (inverse : Bool) (m : Move) :
    State Q A blank ≃ₗᵢ[ℂ] State Q A blank :=
  if inverse then (hilbertReindex (headTranslate m.offset)).trans (controlBasisLift b).symm
  else (controlBasisLift b).trans (hilbertReindex (headTranslate m.offset))

/-- The basis-and-movement isometric equivalence realizes the columns of the corresponding local
rule. -/
theorem basisMoveUnitary_columns {Q A : Type*} [Fintype Q] [Fintype A] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (inverse : Bool) (m : Move) :
    ∀ c, basisMoveUnitary blank b inverse m (ket c) = (basisMoveRule blank b inverse m).column c := by
  intro c
  cases inverse with
  | false =>
    change hilbertReindex (headTranslate m.offset) (controlBasisLift b (ket c)) =
      (controlMoveRule Q A blank (fun p q => b p q) m).column c
    rw [controlBasisLift_ket, map_sum]
    simp only [map_smul, headTranslate_ket]
    rw [controlMoveRule_column]
    rfl
  | true =>
    change (controlBasisLift b).symm (hilbertReindex (headTranslate m.offset) (ket c)) =
      (controlMoveRule Q A blank (fun p q => b.repr (EuclideanSpace.single p 1) q) m).column c
    rw [headTranslate_ket, controlBasisLift_symm_ket, controlMoveRule_column]
    rfl

/-- A rule consisting of a control basis transformation or its inverse and a fixed head movement
is globally well-formed. -/
theorem basisMoveRule_globallyWellformed {Q A : Type*} [Fintype Q] [Fintype A] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (inverse : Bool) (m : Move) :
    (basisMoveRule blank b inverse m).GloballyWellformed :=
  ⟨basisMoveUnitary blank b inverse m, basisMoveUnitary_columns blank b inverse m⟩

/-- The linear equivalence that decomposes square-summable amplitudes on `Φ × κ` into a finite
family of square-summable `κ`-indexed components. -/
noncomputable def finiteL2SplitLinear {Φ κ : Type*} [Fintype Φ] :
    lp (fun _ : Φ × κ => ℂ) 2 ≃ₗ[ℂ] PiLp 2 (fun _ : Φ => lp (fun _ : κ => ℂ) 2) where
  toFun f := WithLp.toLp 2 (fun p => ⟨fun k => f (p,k),
    memℓp_gen (((lp.memℓp f).summable (by norm_num)).prod_factor p)⟩)
  invFun g := ⟨fun pk => g pk.1 pk.2, by
    apply memℓp_gen
    apply (summable_prod_of_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)).mpr
    exact ⟨fun p => (lp.memℓp (g p)).summable (by norm_num), Summable.of_finite⟩⟩
  left_inv f := by ext pk; rfl
  right_inv g := by ext p k; rfl
  map_add' f g := by ext p k; rfl
  map_smul' a f := by ext p k; rfl

/-- The `p`th component of the linear splitting, evaluated at `k`, is the original amplitude at
`(p, k)`. -/
@[simp] theorem finiteL2SplitLinear_ofLp_apply {Φ κ : Type*} [Fintype Φ]
    (f : lp (fun _ : Φ × κ => ℂ) 2) (p : Φ) (k : κ) :
    (finiteL2SplitLinear f).ofLp p k = f (p, k) := rfl

/-- The linear isometric equivalence identifying the square-summable product space with the
finite Hilbert sum of its phase components. -/
noncomputable def finiteL2Split {Φ κ : Type*} [Fintype Φ] :
    lp (fun _ : Φ × κ => ℂ) 2 ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Φ => lp (fun _ : κ => ℂ) 2) :=
  finiteL2SplitLinear.isometryOfInner (by
    intro f g
    simp only [PiLp.inner_apply, lp.inner_eq_tsum, finiteL2SplitLinear_ofLp_apply]
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]
    exact (lp.summable_inner (𝕜 := ℂ) f g).tsum_prod.symm)

/-- Splitting a product-space vector into phase components preserves its amplitude at each pair
`(p, k)`. -/
@[simp] theorem finiteL2Split_apply {Φ κ : Type*} [Fintype Φ]
    (f : lp (fun _ : Φ × κ => ℂ) 2) (p : Φ) (k : κ) : finiteL2Split f p k = f (p,k) := rfl

/-- Reassembling phase components gives amplitude `g p k` at `(p, k)`. -/
@[simp] theorem finiteL2Split_symm_apply {Φ κ : Type*} [Fintype Φ]
    (g : PiLp 2 (fun _ : Φ => lp (fun _ : κ => ℂ) 2)) (p : Φ) (k : κ) :
    finiteL2Split.symm g (p,k) = g p k := rfl

/-- Splitting the standard basis vector at `(p, k)` places the standard vector at `k` solely in
phase `p`. -/
theorem finiteL2Split_single {Φ κ : Type*} [Fintype Φ] [DecidableEq Φ] (p : Φ) (k : κ) :
    finiteL2Split (l2Ket (p,k)) = PiLp.single 2 p (l2Ket k) := by
  ext q l
  by_cases h : q = p
  · subst q
    simp [l2Ket, lp.single_apply, Pi.single_apply]
  · simp [l2Ket, lp.single_apply, h]

/-- The linear embedding of a square-summable vector into the product space at the fixed phase
`p`. -/
noncomputable def phaseL2Embed {Φ κ : Type*} [Fintype Φ] (p : Φ) :
    lp (fun _ : κ => ℂ) 2 →ₗ[ℂ] lp (fun _ : Φ × κ => ℂ) 2 :=
  finiteL2Split.symm.toLinearEquiv.toLinearMap.comp
    (((WithLp.linearEquiv 2 ℂ (Φ → lp (fun _ : κ => ℂ) 2)).symm.toLinearMap).comp
      (LinearMap.single ℂ (fun _ : Φ => lp (fun _ : κ => ℂ) 2) p))

/-- The phase embedding is obtained by placing `v` in a single phase component and applying the
inverse finite splitting. -/
theorem phaseL2Embed_apply {Φ κ : Type*} [Fintype Φ] (p : Φ) (v : lp (fun _ : κ => ℂ) 2) :
    phaseL2Embed p v = finiteL2Split.symm (PiLp.single 2 p v) := rfl

/-- Embedding the standard basis vector at `k` into phase `p` gives the standard product basis
vector at `(p, k)`. -/
theorem phaseL2Embed_single {Φ κ : Type*} [Fintype Φ] (p : Φ) (k : κ) :
    phaseL2Embed p (l2Ket k) = l2Ket (p,k) := by
  apply finiteL2Split.injective
  rw [phaseL2Embed_apply, LinearIsometryEquiv.apply_symm_apply, finiteL2Split_single]

/-- The linear isometric equivalence that applies the phase-dependent map `U p` and advances the
phase by the permutation `e`. -/
noncomputable def clockL2Unitary {Φ κ : Type*} [Fintype Φ] (e : Φ ≃ Φ)
    (U : Φ → (lp (fun _ : κ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2)) :
    lp (fun _ : Φ × κ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Φ × κ => ℂ) 2 :=
  ((finiteL2Split.trans (LinearIsometryEquiv.piLpCongrRight 2 U)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ (lp (fun _ : κ => ℂ) 2) e)).trans finiteL2Split.symm

/-- On a vector supported in phase `p`, clocked evolution applies `U p` and moves the resulting
vector into phase `e p`. -/
theorem clockL2Unitary_phase {Φ κ : Type*} [Fintype Φ] (e : Φ ≃ Φ)
    (U : Φ → (lp (fun _ : κ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2)) (p : Φ) (v : lp (fun _ : κ => ℂ) 2) :
    clockL2Unitary e U (phaseL2Embed p v) = phaseL2Embed (e p) (U p v) := by
  change finiteL2Split.symm (LinearIsometryEquiv.piLpCongrLeft 2 ℂ _ e
    (LinearIsometryEquiv.piLpCongrRight 2 U (finiteL2Split (phaseL2Embed p v)))) = _
  rw [phaseL2Embed_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.piLpCongrRight_single, LinearIsometryEquiv.piLpCongrLeft_single]
  rfl

/-- The equivalence separating the phase component of an augmented configuration from its
underlying machine configuration. -/
def clockCoordinates {Φ Q A : Type*} {blank : A} : Config (Φ × Q) A blank ≃ Φ × Config Q A blank where
  toFun c := (c.state.1, ⟨c.state.2,c.tape,c.head⟩)
  invFun c := ⟨(c.1,c.2.state),c.2.tape,c.2.head⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨p,q,T,h⟩; rfl

/-- The linear embedding of a machine state into configurations whose control phase is fixed to
`p`. -/
noncomputable def phaseEmbed {Φ Q A : Type*} [Fintype Φ] {blank : A} (p : Φ) :
    State Q A blank →ₗ[ℂ] State (Φ × Q) A blank :=
  (hilbertReindex (clockCoordinates (Φ := Φ) (Q := Q) (blank := blank)).symm).toLinearEquiv.toLinearMap.comp (phaseL2Embed p)

/-- Embedding a configuration basis vector into phase `p` appends `p` to its control state. -/
theorem phaseEmbed_ket {Φ Q A : Type*} [Fintype Φ] {blank : A} (p : Φ) (c : Config Q A blank) :
    phaseEmbed p (ket c) = ket ⟨(p,c.state),c.tape,c.head⟩ := by
  change hilbertReindex clockCoordinates.symm (phaseL2Embed p (l2Ket c)) = _
  rw [phaseL2Embed_single, hilbertReindex_l2Ket]
  rfl

/-- A phase-embedded state has its original configuration amplitude when the phase equals `p`,
and zero otherwise. -/
theorem phaseEmbed_apply {Φ Q A : Type*} [Fintype Φ] {blank : A}
    (p : Φ) (v : State Q A blank) (c : Config (Φ × Q) A blank) :
    phaseEmbed p v c = if c.state.1 = p then v ⟨c.state.2,c.tape,c.head⟩ else 0 := by
  change (PiLp.single 2 p v : PiLp 2 (fun _ : Φ => State Q A blank)) c.state.1 ⟨c.state.2,c.tape,c.head⟩ = _
  by_cases h : c.state.1 = p
  · subst p
    simp
  · simp [h]

/-- Embedding a machine state into a fixed phase preserves its norm. -/
theorem phaseEmbed_norm {Φ Q A : Type*} [Fintype Φ] {blank : A}
    (p : Φ) (v : State Q A blank) : ‖phaseEmbed p v‖ = ‖v‖ := by
  change ‖hilbertReindex clockCoordinates.symm
    (finiteL2Split.symm (PiLp.single 2 p v))‖ = _
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, PiLp.norm_single]

/-- The global linear isometric equivalence that applies the evolution indexed by the current
phase and advances the phase by `e`. -/
noncomputable def clockUnitary {Φ Q A : Type*} [Fintype Φ] {blank : A} (e : Φ ≃ Φ)
    (U : Φ → (State Q A blank ≃ₗᵢ[ℂ] State Q A blank)) :
    State (Φ × Q) A blank ≃ₗᵢ[ℂ] State (Φ × Q) A blank :=
  ((hilbertReindex clockCoordinates).trans (clockL2Unitary e U)).trans (hilbertReindex clockCoordinates.symm)

/-- Clocked machine evolution sends a state in phase `p` to the phase embedding at `e p` of its
image under `U p`. -/
theorem clockUnitary_phase {Φ Q A : Type*} [Fintype Φ] {blank : A} (e : Φ ≃ Φ)
    (U : Φ → (State Q A blank ≃ₗᵢ[ℂ] State Q A blank)) (p : Φ) (v : State Q A blank) :
    clockUnitary e U (phaseEmbed p v) = phaseEmbed (e p) (U p v) := by
  change hilbertReindex clockCoordinates.symm (clockL2Unitary e U
    (hilbertReindex clockCoordinates (hilbertReindex clockCoordinates.symm (phaseL2Embed p v)))) = _
  have hh : (hilbertReindex (clockCoordinates (Φ := Φ) (Q := Q) (blank := blank)))
      (hilbertReindex clockCoordinates.symm (phaseL2Embed p v)) = phaseL2Embed p v := by
    ext pk
    simp
  rw [hh, clockL2Unitary_phase]
  rfl

/-- The augmented local rule that uses the amplitudes selected by the current phase and changes
that phase according to `e`. -/
noncomputable def clockRule {Φ Q A : Type*} (blank : A) (e : Φ ≃ Φ)
    (δ : Φ → Q → A → Move → Q → A → ℂ) : Rule (Φ × Q) A where
  blank := blank
  amplitude p a m q b := if q.1 = e p.1 then δ p.1 p.2 a m q.2 b else 0

/-- A clocked rule's transition column is the next-phase embedding of the column of the local
rule selected by the current phase. -/
theorem clockRule_column {Φ Q A : Type*} [Fintype Φ] [Fintype Q] [Fintype A]
    (blank : A) (e : Φ ≃ Φ) (δ : Φ → Q → A → Move → Q → A → ℂ) (c : Config (Φ × Q) A blank) :
    (clockRule blank e δ).column c = phaseEmbed (e c.state.1)
      ((⟨blank,δ c.state.1⟩ : Rule Q A).column ⟨c.state.2,c.tape,c.head⟩) := by
  change (∑ i : Move × (Φ × Q) × A,
    (if i.2.1.1 = e c.state.1 then δ c.state.1 c.state.2 (c.tape c.head) i.1 i.2.1.2 i.2.2 else 0) •
      (ket (target c i.1 i.2.1 i.2.2) : State (Φ × Q) A blank)) = _
  rw [Rule.column, map_sum]
  simp only [map_smul, phaseEmbed_ket]
  ext d
  simp only [Fintype.sum_prod_type, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
  simp [ite_mul, Finset.sum_ite_irrel, target]

/-- If each phase evolution realizes its local transition columns, their clocked isometric
equivalence realizes the columns of the augmented clock rule. -/
theorem clockUnitary_columns {Φ Q A : Type*} [Fintype Φ] [Fintype Q] [Fintype A]
    (blank : A) (e : Φ ≃ Φ) (δ : Φ → Q → A → Move → Q → A → ℂ)
    (U : Φ → (State Q A blank ≃ₗᵢ[ℂ] State Q A blank))
    (hU : ∀ p (c : Config Q A blank), U p (ket c) = (⟨blank,δ p⟩ : Rule Q A).column c) :
    ∀ c : Config (Φ × Q) A blank, clockUnitary e U (ket c) = (clockRule blank e δ).column c := by
  intro c
  have hc : phaseEmbed c.state.1 (ket (⟨c.state.2,c.tape,c.head⟩ : Config Q A blank)) = ket c := by
    rw [phaseEmbed_ket]
  rw [← hc, clockUnitary_phase, hU, clockRule_column]

/-- A clock rule is globally well-formed whenever each phase's local amplitudes are realized by
the specified global linear isometric equivalence. -/
theorem clockRule_globallyWellformed {Φ Q A : Type*} [Fintype Φ] [Fintype Q] [Fintype A]
    (blank : A) (e : Φ ≃ Φ) (δ : Φ → Q → A → Move → Q → A → ℂ)
    (U : Φ → (State Q A blank ≃ₗᵢ[ℂ] State Q A blank))
    (hU : ∀ p (c : Config Q A blank), U p (ket c) = (⟨blank,δ p⟩ : Rule Q A).column c) :
    (clockRule blank e δ).GloballyWellformed := ⟨clockUnitary e U, clockUnitary_columns blank e δ U hU⟩

/-- Translating a state by `-a` and then by `a` returns the original state. -/
theorem headTranslate_cancel {Q A : Type*} {blank : A} (a : ℤ) (v : State Q A blank) :
    hilbertReindex (headTranslate a) (hilbertReindex (headTranslate (-a)) v) = v := by
  ext c
  change v ⟨c.state,c.tape,(c.head-a)-(-a)⟩ = v c
  have hc : (⟨c.state,c.tape,(c.head-a)-(-a)⟩ : Config Q A blank) = c := by
    apply Config.ext
    · rfl
    · rfl
    · change (c.head-a)-(-a) = c.head
      omega
  exact congrArg (fun d : Config Q A blank => v d) hc

/-- Head translation by `m.offset` realizes the columns of the basis-movement rule using the
standard control basis. -/
theorem basisMoveIdentity_columns {Q A : Type*} [Fintype Q] [Fintype A] (blank : A) (m : Move)
    (c : Config Q A blank) :
    hilbertReindex (headTranslate m.offset) (ket c) =
      (basisMoveRule blank (EuclideanSpace.basisFun Q ℂ) false m).column c := by
  have he := basisMoveUnitary_columns blank (EuclideanSpace.basisFun Q ℂ) false m c
  change hilbertReindex (headTranslate m.offset)
      (controlBasisLift (EuclideanSpace.basisFun Q ℂ) (ket c)) = _ at he
  rw [controlBasisLift_ket_slice, EuclideanSpace.basisFun_apply, controlSlice_single,
      one_smul] at he
  exact he

/-- The local amplitudes of five successive phases: a right shift, an inverse-basis left move,
the basis-changed rule, a forward-basis left move, and a right shift. -/
noncomputable def fivePhaseAmp {Q A : Type*} [Fintype Q] (R : Rule Q A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (p : Fin 5) : Q → A → Move → Q → A → ℂ :=
  match p.val with
  | 0 => (basisMoveRule R.blank (EuclideanSpace.basisFun Q ℂ) false .right).amplitude
  | 1 => (basisMoveRule R.blank b true .left).amplitude
  | 2 => (R.changeBasis b).amplitude
  | 3 => (basisMoveRule R.blank b false .left).amplitude
  | _ => (basisMoveRule R.blank (EuclideanSpace.basisFun Q ℂ) false .right).amplitude

/-- The phase-dependent global isometric equivalences implementing the two right shifts, inverse
and forward basis moves, and conjugated original evolution of the five-phase construction. -/
noncomputable def fivePhaseUnitary {Q A : Type*} [Fintype Q] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (U : State Q A blank ≃ₗᵢ[ℂ] State Q A blank)
    (p : Fin 5) : State Q A blank ≃ₗᵢ[ℂ] State Q A blank :=
  match p.val with
  | 0 => hilbertReindex (headTranslate 1)
  | 1 => basisMoveUnitary blank b true .left
  | 2 => ((controlBasisLift b).trans U).trans (controlBasisLift b).symm
  | 3 => basisMoveUnitary blank b false .left
  | _ => hilbertReindex (headTranslate 1)

/-- When `U` realizes the original rule, each of the five phase isometric equivalences realizes
the corresponding local transition columns. -/
theorem fivePhaseUnitary_columns {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (U : State Q A R.blank ≃ₗᵢ[ℂ] State Q A R.blank) (hU : ∀ c, U (ket c) = R.column c)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : ∀ (p : Fin 5) (c : Config Q A R.blank),
    fivePhaseUnitary R.blank b U p (ket c) = (⟨R.blank,fivePhaseAmp R b p⟩ : Rule Q A).column c := by
  intro p c
  fin_cases p
  · exact basisMoveIdentity_columns R.blank .right c
  · exact basisMoveUnitary_columns R.blank b true .left c
  · change (controlBasisLift b).symm (U (controlBasisLift b (ket c))) = (R.changeBasis b).column c
    apply (controlBasisLift b).injective
    rw [LinearIsometryEquiv.apply_symm_apply, R.changeBasis_column_compat U hU b c]
    rfl
  · exact basisMoveUnitary_columns R.blank b false .left c
  · exact basisMoveIdentity_columns R.blank .right c

/-- The rule augmenting the control with a cyclic five-phase clock and using `fivePhaseAmp` at
each phase. -/
noncomputable def fivePhaseRule {Q A : Type*} [Fintype Q] (R : Rule Q A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : Rule (Fin 5 × Q) A :=
  clockRule R.blank (finRotate 5) (fivePhaseAmp R b)

/-- The five-phase augmentation of a globally well-formed rule is globally well-formed. This
supplies the well-formedness part of the construction associated with [Bernstein and
Vazirani, Lemma 5.3.2][BernsteinVazirani1997]. -/
theorem fivePhaseRule_globallyWellformed {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) :
    (fivePhaseRule R b).GloballyWellformed := by
  obtain ⟨U,hU⟩ := h
  exact clockRule_globallyWellformed R.blank (finRotate 5) (fivePhaseAmp R b) (fivePhaseUnitary R.blank b U)
    (fivePhaseUnitary_columns R U hU b)

/-- Starting at phase zero, five steps of the clocked construction apply `U` once and return to
phase zero. This is the exact five-step simulation identity associated with [Bernstein and
Vazirani, Lemma 5.3.2][BernsteinVazirani1997]. -/
theorem fivePhase_cycle {Q A : Type*} [Fintype Q] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (U : State Q A blank ≃ₗᵢ[ℂ] State Q A blank)
    (v : State Q A blank) :
    ((clockUnitary (finRotate 5) (fivePhaseUnitary blank b U)).toLinearEquiv.toLinearMap ^ 5)
      (phaseEmbed (0 : Fin 5) v) = phaseEmbed (0 : Fin 5) (U v) := by
  generalize hC : clockUnitary (finRotate 5) (fivePhaseUnitary blank b U) = C
  have hstep (p : Fin 5) (w : State Q A blank) :
      C (phaseEmbed p w) = phaseEmbed (finRotate 5 p) (fivePhaseUnitary blank b U p w) := by
    rw [← hC]
    exact clockUnitary_phase (finRotate 5) (fivePhaseUnitary blank b U) p w
  change C (C (C (C (C (phaseEmbed (0 : Fin 5) v))))) = _
  have h0 : finRotate 5 (0 : Fin 5) = 1 := rfl
  have h1 : finRotate 5 (1 : Fin 5) = 2 := rfl
  have h2 : finRotate 5 (2 : Fin 5) = 3 := rfl
  have h3 : finRotate 5 (3 : Fin 5) = 4 := rfl
  have h4 : finRotate 5 (4 : Fin 5) = 0 := rfl
  simp only [hstep, h0, h1, h2, h3, h4]
  change phaseEmbed (0 : Fin 5)
    (hilbertReindex (headTranslate 1) (hilbertReindex (headTranslate (-1))
      (controlBasisLift b ((controlBasisLift b).symm
        (U (controlBasisLift b ((controlBasisLift b).symm
          (hilbertReindex (headTranslate (-1)) (hilbertReindex (headTranslate 1) v))))))))) = _
  have hcancel : hilbertReindex (headTranslate (-1)) (hilbertReindex (headTranslate 1) v) = v := by
    simpa using! headTranslate_cancel (-1) v
  simp only [LinearIsometryEquiv.apply_symm_apply, hcancel, headTranslate_cancel]

/-- Starting at phase zero, `5 * t` steps of the clocked construction apply `U` exactly `t`
times and return to phase zero. -/
theorem fivePhase_cycles {Q A : Type*} [Fintype Q] (blank : A)
    (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (U : State Q A blank ≃ₗᵢ[ℂ] State Q A blank)
    (t : ℕ) (v : State Q A blank) :
    ((clockUnitary (finRotate 5) (fivePhaseUnitary blank b U)).toLinearEquiv.toLinearMap ^ (5*t))
      (phaseEmbed (0 : Fin 5) v) = phaseEmbed (0 : Fin 5) ((U.toLinearEquiv.toLinearMap ^ t) v) := by
  have hc (w : State Q A blank) := fivePhase_cycle blank b U w
  generalize hC : (clockUnitary (finRotate 5) (fivePhaseUnitary blank b U)).toLinearEquiv.toLinearMap = C at hc ⊢
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [Nat.mul_succ, pow_add]
    change (C ^ (5*t)) ((C ^ 5) (phaseEmbed (0 : Fin 5) v)) = _
    rw [hc]
    rw [pow_succ]
    exact ih (U v)

/-- The block matrix with blocks `0`, `Kᴴ`, `K`, and `1 - K * Kᴴ`, extending the action of `K`
to the direct-sum space. -/
noncomputable def isometrySwap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  Matrix.fromBlocks 0 K.conjTranspose K (1-K*K.conjTranspose)

/-- The block matrix `isometrySwap K` is Hermitian for every `K`. -/
theorem isometrySwap_hermitian {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) : (isometrySwap K).conjTranspose = isometrySwap K := by
  simp [isometrySwap, Matrix.fromBlocks_conjTranspose]

/-- If `Kᴴ * K = 1`, the block matrix `isometrySwap K` squares to the identity. -/
theorem isometrySwap_square {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) (hK : K.conjTranspose*K = 1) : isometrySwap K * isometrySwap K = 1 := by
  have hP : (K*K.conjTranspose)*(K*K.conjTranspose) = K*K.conjTranspose := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc K.conjTranspose, hK, Matrix.one_mul]
  have hlast : K*K.conjTranspose + (1-K*K.conjTranspose)*(1-K*K.conjTranspose) = 1 := by
    calc
      _ = 1 - K*K.conjTranspose + (K*K.conjTranspose)*(K*K.conjTranspose) := by noncomm_ring
      _ = 1 := by rw [hP]; abel
  have hright : K.conjTranspose * (1-K*K.conjTranspose) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hK, Matrix.one_mul, sub_self]
  have hleft : (1-K*K.conjTranspose) * K = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hK, Matrix.mul_one, sub_self]
  unfold isometrySwap
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, hK, hright, hleft, hlast,
    Matrix.fromBlocks_one]

/-- The block matrix `isometrySwap K` is unitary when `K` is an isometry. -/
theorem isometrySwap_unitary {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) (hK : K.conjTranspose*K = 1) :
    isometrySwap K ∈ Matrix.unitaryGroup (ι ⊕ κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change isometrySwap K * (isometrySwap K).conjTranspose = 1
  rw [isometrySwap_hermitian, isometrySwap_square K hK]

/-- The swap block matrix sends a vector in the left summand to its image under `K` in the right
summand. -/
theorem isometrySwap_left {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) (x : ι → ℂ) :
    isometrySwap K *ᵥ Sum.elim x (0 : κ → ℂ) = Sum.elim (0 : ι → ℂ) (K *ᵥ x) := by
  rw [isometrySwap, Matrix.fromBlocks_mulVec]
  change Sum.elim ((0 : Matrix ι ι ℂ) *ᵥ x + K.conjTranspose *ᵥ 0)
    (K *ᵥ x + (1-K*K.conjTranspose) *ᵥ 0) = _
  simp

/-- When `K` is an isometry, the swap block matrix sends `K *ᵥ x` in the right summand back to
`x` in the left summand. -/
theorem isometrySwap_right {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) (hK : K.conjTranspose*K = 1) (x : ι → ℂ) :
    isometrySwap K *ᵥ Sum.elim (0 : ι → ℂ) (K *ᵥ x) = Sum.elim x (0 : κ → ℂ) := by
  rw [← isometrySwap_left K x, Matrix.mulVec_mulVec, isometrySwap_square K hK, Matrix.one_mulVec]

/-- The swap block matrix fixes right-summand vectors in the kernel of `Kᴴ`. -/
theorem isometrySwap_fixed {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix κ ι ℂ) (y : κ → ℂ) (hy : K.conjTranspose *ᵥ y = 0) :
    isometrySwap K *ᵥ Sum.elim (0 : ι → ℂ) y = Sum.elim (0 : ι → ℂ) y := by
  rw [isometrySwap, Matrix.fromBlocks_mulVec]
  change Sum.elim ((0 : Matrix ι ι ℂ) *ᵥ 0 + K.conjTranspose *ᵥ y)
    (K *ᵥ 0 + (1-K*K.conjTranspose) *ᵥ y) = _
  simp only [Matrix.mulVec_zero, zero_add, Matrix.sub_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hy, sub_zero]

/-- The local transition matrix with input control-symbol pairs as columns and output
movement-control-symbol triples as rows. -/
noncomputable def Rule.cellIsometry {Q A : Type*} (R : Rule Q A) : Matrix (Move × Q × A) (Q × A) ℂ :=
  fun out inp => R.amplitude inp.1 inp.2 out.1 out.2.1 out.2.2

/-- The local transition matrix of a globally well-formed rule satisfies `R.cellIsometryᴴ *
R.cellIsometry = 1`. -/
theorem Rule.cellIsometry_gram {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) :
    R.cellIsometry.conjTranspose * R.cellIsometry = 1 := by
  ext inp inp'
  change (∑ out : Move × Q × A,
    star (R.amplitude inp.1 inp.2 out.1 out.2.1 out.2.2) *
      R.amplitude inp'.1 inp'.2 out.1 out.2.1 out.2.2) = _
  rw [R.local_inner_of_global h]
  simp [Matrix.one_apply]

/-- The swap block matrix built from the local transition matrix on the sum of input and output
cell spaces. -/
noncomputable def Rule.cellSwap {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A] (R : Rule Q A) :
    Matrix ((Q × A) ⊕ (Move × Q × A)) ((Q × A) ⊕ (Move × Q × A)) ℂ := isometrySwap R.cellIsometry

/-- The local cell-swap matrix of a globally well-formed rule is unitary. -/
theorem Rule.cellSwap_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) :
    R.cellSwap ∈ Matrix.unitaryGroup ((Q × A) ⊕ (Move × Q × A)) ℂ :=
  isometrySwap_unitary R.cellIsometry (R.cellIsometry_gram h)

/-- The cell-swap matrix sends an input-cell vector to its local transition image in the
output-cell summand. -/
theorem Rule.cellSwap_forward {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (x : Q × A → ℂ) :
    R.cellSwap *ᵥ Sum.elim x (0 : Move × Q × A → ℂ) =
      Sum.elim (0 : Q × A → ℂ) (R.cellIsometry *ᵥ x) := isometrySwap_left R.cellIsometry x

/-- For a globally well-formed rule, the cell-swap matrix sends a local transition image back to
its original input-cell vector. -/
theorem Rule.cellSwap_reverse {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (x : Q × A → ℂ) :
    R.cellSwap *ᵥ Sum.elim (0 : Q × A → ℂ) (R.cellIsometry *ᵥ x) =
      Sum.elim x (0 : Move × Q × A → ℂ) := isometrySwap_right R.cellIsometry (R.cellIsometry_gram h) x

/-- The output-row, input-column entry of the cell-swap matrix is the corresponding local
transition amplitude. -/
theorem Rule.cellSwap_new_old {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (out : Move × Q × A) (inp : Q × A) :
    R.cellSwap (.inr out) (.inl inp) = R.amplitude inp.1 inp.2 out.1 out.2.1 out.2.2 := rfl

/-- The output-output block entry of the cell-swap matrix is the identity entry minus the sum of
products of output transition amplitudes over input control-symbol pairs. -/
theorem Rule.cellSwap_new_new {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (out out' : Move × Q × A) :
    R.cellSwap (.inr out) (.inr out') = (if out = out' then 1 else 0) -
      ∑ inp : Q × A, R.amplitude inp.1 inp.2 out.1 out.2.1 out.2.2 *
        star (R.amplitude inp.1 inp.2 out'.1 out'.2.1 out'.2.2) := by
  rfl

/-- The enlarged cell-swap space has cardinality `4 * Fintype.card Q * Fintype.card A`. -/
theorem Rule.cellSwap_card {Q A : Type*} [Fintype Q] [Fintype A] :
    Fintype.card ((Q × A) ⊕ (Move × Q × A)) = 4 * Fintype.card Q * Fintype.card A := by
  have hm : Fintype.card Move = 3 := by decide
  simp only [Fintype.card_sum, Fintype.card_prod, hm]
  ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod
