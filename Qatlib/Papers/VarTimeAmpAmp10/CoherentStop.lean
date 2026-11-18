/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.XorOracle
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

/-!
# The coherent stop-marking operator (VTAA first executable slice)

Fixed source arXiv:1010.4458v2 (Ambainis, *Variable time amplitude amplification and a
faster quantum algorithm for solving systems of linear equations*): the Section 3.1
model read as the first executable stage on the route to Theorem 1
.  Before any amplification schedule exists, the variable-time program
must expose a *coherent* way to mark the subspace in which the computation has already
stopped.  This slice consumes the standard XOR oracle interface of
`Qatlib.Concepts.CircuitLang.XorOracle` (the module carrying the `PhaseOf` phase
form and the Oriented O/Ω/Θ protocol): the register is the standard address / answer /
work register `OReg a w`, a stop predicate is a map `f : Addr a → Bool` on the address
block, and the coherent stop marking `stopMark f` is the phase form of one standard
query — the answer-wire Hadamard layer `ansH` sandwiching `xorOracle f`.

The register splits into three subspaces: the marked (stopped) sector `stopSub f` of
flag-set basis states at stopped addresses, the unmarked (continue) sector `contSub f`
of flag-set states at still-running addresses, and the auxiliary flag-unset sector
`auxSub`.  `stopMark f` is unitary and acts exactly as promised: it multiplies
`stopSub f` by the phase `-1` and fixes `contSub f` and `auxSub` pointwise; the three
sectors span the whole register and the marked/continue split is direct.

Boundary (kept out of this slice on purpose): the amplification schedule and its round
counts, the success probability of any amplified algorithm, stopping-time and cost
semantics (nothing here prescribes ν or a number of calls; those must be derived from
an actual algorithm later), and any step-by-step measurement of the stop register —
the marking is a unitary action, not a measurement.  No asymptotic O/Ω/Θ or
repeated-sampling statement is made.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.XorOracle
open scoped Matrix

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentStop

variable {a w : ℕ}

/-! ### The answer-wire Hadamard layer -/

/-- The answer-wire Hadamard layer of the standard register: block-diagonal, acting as
the public single-qubit `Hadamard` on the answer bit inside each address/work block. -/
def ansH : Matrix (OReg a w) (OReg a w) ℂ :=
  Matrix.of fun r r' =>
    if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then Hadamard r.2.1 r'.2.1 else 0

/-- Register-sum collapse: summing a block-supported summand over the whole register
with fixed address/work block reduces to the answer-wire sum inside that block. -/
theorem sum_collapse (G : OReg a w → ℂ) (r : OReg a w) :
    ∑ r' : OReg a w, (if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then G r' else 0)
      = ∑ b' : Bool, G (r.1, b', r.2.2) := by
  have h1 : ∑ r' : OReg a w, (if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then G r' else 0)
      = ∑ x : Addr a, ∑ p : Bool × (Fin w → Bool),
          (if r.1 = x ∧ r.2.2 = p.2 then G (x, p.1, p.2) else 0) :=
    Fintype.sum_prod_type' fun (x : Addr a) (p : Bool × (Fin w → Bool)) =>
      if r.1 = x ∧ r.2.2 = p.2 then G (x, p.1, p.2) else 0
  have h2 : ∀ x : Addr a, (∑ p : Bool × (Fin w → Bool),
          (if r.1 = x ∧ r.2.2 = p.2 then G (x, p.1, p.2) else 0))
      = ∑ b' : Bool, ∑ u' : Fin w → Bool,
          (if r.1 = x ∧ r.2.2 = u' then G (x, b', u') else 0) := fun x =>
    Fintype.sum_prod_type' fun (b : Bool) (u : Fin w → Bool) =>
      if r.1 = x ∧ r.2.2 = u then G (x, b, u) else 0
  have hcomb : ∑ r' : OReg a w, (if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then G r' else 0)
      = ∑ x : Addr a, ∑ b' : Bool, ∑ u' : Fin w → Bool,
          (if r.1 = x ∧ r.2.2 = u' then G (x, b', u') else 0) := by
    rw [h1]
    exact Finset.sum_congr rfl fun x _ => h2 x
  have hpx : ∀ (x : Addr a) (b' : Bool), (∑ u' : Fin w → Bool,
        (if r.1 = x ∧ r.2.2 = u' then G (x, b', u') else 0))
      = (if r.1 = x then (∑ u' : Fin w → Bool,
          (if r.2.2 = u' then G (x, b', u') else 0)) else 0) := by
    intro x b'
    by_cases hx : r.1 = x <;> simp [hx]
  have hu : ∀ (x : Addr a) (b' : Bool), (∑ u' : Fin w → Bool,
        (if r.2.2 = u' then G (x, b', u') else 0))
      = G (x, b', r.2.2) := by
    intro x b'
    rw [Finset.sum_ite_eq]
    simp
  have hw : (∑ x : Addr a, ∑ b' : Bool, ∑ u' : Fin w → Bool,
        (if r.1 = x ∧ r.2.2 = u' then G (x, b', u') else 0))
      = ∑ x : Addr a, ∑ b' : Bool, (if r.1 = x then G (x, b', r.2.2) else 0) := by
    rw [Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun b' _ => hpx x b'))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b' _ => ?_
    by_cases hx : r.1 = x
    · simp [hx, hu x b']
    · simp [hx]
  have hq : ∀ b' : Bool, (∑ x : Addr a, (if r.1 = x then G (x, b', r.2.2) else 0))
      = G (r.1, b', r.2.2) := by
    intro b'
    rw [Finset.sum_ite_eq]
    simp
  rw [hcomb, hw, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ => hq b'

/-- Applying the answer-wire Hadamard layer reduces to one wire Hadamard application
inside the addressed block. -/
theorem ansH_apply (v : QState (OReg a w)) (r : OReg a w) :
    (ansH *ᵥ v) r = ∑ b' : Bool, Hadamard r.2.1 b' * v (r.1, b', r.2.2) := by
  have hmerge : ∀ r' : OReg a w,
      ansH r r' * v r'
        = if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then Hadamard r.2.1 r'.2.1 * v r' else 0 := by
    intro r'
    have hA : ansH r r'
        = if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then Hadamard r.2.1 r'.2.1 else 0 := rfl
    rw [hA]
    by_cases c : r.1 = r'.1 ∧ r.2.2 = r'.2.2 <;> simp [c]
  simp only [Matrix.mulVec, dotProduct, hmerge]
  rw [sum_collapse (fun r' => Hadamard r.2.1 r'.2.1 * v r') r]

/-- The answer-wire Hadamard layer squares to the identity: each diagonal block is the
involutory wire Hadamard. -/
theorem ansH_sq : ansH * ansH = (1 : Matrix (OReg a w) (OReg a w) ℂ) := by
  ext r r''
  simp only [Matrix.one_apply]
  by_cases hblk : r.1 = r''.1 ∧ r.2.2 = r''.2.2
  · have hmerge : ∀ r' : OReg a w,
        ansH r r' * ansH r' r''
        = if r.1 = r'.1 ∧ r.2.2 = r'.2.2
            then Hadamard r.2.1 r'.2.1 * Hadamard r'.2.1 r''.2.1 else 0 := by
      intro r'
      have hA : ansH r r'
          = if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then Hadamard r.2.1 r'.2.1 else 0 := rfl
      have hB : ansH r' r''
          = if r'.1 = r''.1 ∧ r'.2.2 = r''.2.2 then Hadamard r'.2.1 r''.2.1 else 0 := rfl
      rw [hA, hB]
      by_cases c1 : r.1 = r'.1 ∧ r.2.2 = r'.2.2
      · have c2 : r'.1 = r''.1 ∧ r'.2.2 = r''.2.2 :=
          ⟨c1.1.symm.trans hblk.1, c1.2.symm.trans hblk.2⟩
        simp [c1, c2]
      · simp [c1]
    simp only [Matrix.mul_apply, hmerge]
    rw [sum_collapse (fun r' => Hadamard r.2.1 r'.2.1 * Hadamard r'.2.1 r''.2.1) r]
    show (∑ b' : Bool, Hadamard r.2.1 b' * Hadamard b' r''.2.1)
      = (if r = r'' then 1 else 0)
    rw [← Matrix.mul_apply, hadamard_mul_self, Matrix.one_apply]
    by_cases hflag : r.2.1 = r''.2.1
    · rw [Prod.ext hblk.1 (Prod.ext hflag hblk.2)]
      simp
    · have hrne : ¬(r = r'') := fun he =>
        hflag (Prod.ext_iff.mp (Prod.ext_iff.mp he).2).1
      simp [hrne, hflag]
  · have hrne : ¬(r = r'') := by
      rintro he
      have h := Prod.ext_iff.mp he
      exact hblk ⟨h.1, (Prod.ext_iff.mp h.2).2⟩
    rw [Matrix.mul_apply]
    simp only [hrne]
    refine Finset.sum_eq_zero fun r' _ => ?_
    have hA : ansH r r'
        = if r.1 = r'.1 ∧ r.2.2 = r'.2.2 then Hadamard r.2.1 r'.2.1 else 0 := rfl
    have hB : ansH r' r''
        = if r'.1 = r''.1 ∧ r'.2.2 = r''.2.2 then Hadamard r'.2.1 r''.2.1 else 0 := rfl
    rw [hA, hB]
    by_cases c1 : r.1 = r'.1 ∧ r.2.2 = r'.2.2
    · have c2 : ¬(r'.1 = r''.1 ∧ r'.2.2 = r''.2.2) :=
        fun h => hblk ⟨c1.1.trans h.1, c1.2.trans h.2⟩
      simp [c1, c2]
    · simp [c1]

/-- The answer-wire Hadamard layer equals its conjugate transpose: it is real and
block-symmetric, mirroring the public wire Hadamard. -/
theorem ansH_conjT : (ansHᴴ : Matrix (OReg a w) (OReg a w) ℂ) = ansH := by
  have hH : ∀ x y : Bool, star (Hadamard y x) = Hadamard x y := by
    intro x y
    have h1 : Hadamardᴴ x y = Hadamard x y := congrFun (congrFun hadamard_conjTranspose x) y
    rwa [Matrix.conjTranspose_apply] at h1
  ext r r''
  simp only [Matrix.conjTranspose_apply, ansH, Matrix.of_apply]
  split
  · next h =>
    simp only [show r.1 = r''.1 ∧ r.2.2 = r''.2.2 from ⟨h.1.symm, h.2.symm⟩]
    exact hH _ _
  · next h =>
    rw [star_zero]
    split
    · next hc => exact absurd ⟨hc.1.symm, hc.2.symm⟩ h
    · rfl

/-- The answer-wire Hadamard layer is unitary. -/
theorem ansH_uni : ansH ∈ Matrix.unitaryGroup (OReg a w) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ansH_conjT]
  exact ansH_sq

/-! ### Wire-extended states and blockwise action -/

/-- The register state with the address block at `x`, the work block at `u`, and the
answer (flag) wire in the pure qubit state `φ`. -/
def wireExt (x : Addr a) (φ : QState Bool) (u : Fin w → Bool) : QState (OReg a w) :=
  fun r => if r.1 = x ∧ r.2.2 = u then φ r.2.1 else 0

/-- A computational basis state is the wire extension of the wire basis state. -/
theorem ket_wireExt (x : Addr a) (b : Bool) (u : Fin w → Bool) :
    Ket (x, b, u) = wireExt x (Ket b) u := by
  funext r
  by_cases h1 : r.1 = x
  · by_cases h2 : r.2.2 = u
    · by_cases hb : r.2.1 = b <;>
        simp [Qatlib.Foundations.PureStateMath.Ket, wireExt, h1, h2, hb, Prod.ext_iff]
    · simp [Qatlib.Foundations.PureStateMath.Ket, wireExt, h1, h2, Prod.ext_iff]
  · simp [Qatlib.Foundations.PureStateMath.Ket, wireExt, h1, Prod.ext_iff]

/-- The answer-wire Hadamard layer acts inside a wire-extended block as the wire
Hadamard. -/
theorem ansH_wireExt (x : Addr a) (φ : QState Bool) (u : Fin w → Bool) :
    ansH *ᵥ wireExt x φ u = wireExt x (Hadamard *ᵥ φ) u := by
  funext r
  rw [ansH_apply]
  by_cases h : r.1 = x ∧ r.2.2 = u
  · simp [h, wireExt, Matrix.mulVec, dotProduct]
  · simp [wireExt, h]

/-- The standard oracle permutes amplitudes by the XOR update of the register. -/
theorem xor_apply (f : Addr a → Bool) (v : QState (OReg a w)) (r : OReg a w) :
    (xorOracle f *ᵥ v) r = v (xorInto f r) :=
  applyGate_permMatrix (xorInto_inv (a := a) (w := w) f) v r

/-- The standard oracle acts inside a wire-extended block by XOR-shifting the flag
amplitudes of the addressed block. -/
theorem xor_wireExt (f : Addr a → Bool) (x : Addr a) (φ : QState Bool) (u : Fin w → Bool) :
    xorOracle f *ᵥ wireExt x φ u = wireExt x (fun b => φ (b ^^ f x)) u := by
  funext r
  rw [xor_apply]
  have hdef : wireExt x φ u (xorInto f r)
      = if r.1 = x ∧ r.2.2 = u then φ (r.2.1 ^^ f r.1) else 0 := rfl
  rw [hdef]
  by_cases h : r.1 = x ∧ r.2.2 = u
  · simp only [wireExt, h]
  · simp [wireExt, h]

/-! ### The coherent stop marking -/

/-- The stop predicate `f` packaged with the concrete answer-wire Hadamard layer as a
`PhaseOf` typed interface of the standard oracle. -/
def stopPhase (f : Addr a → Bool) : PhaseOf (a := a) (w := w) where
  f := f
  hLayer := ansH
  hUni := ansH_uni

/-- The coherent stop-marking unitary: the phase form of the standard XOR oracle for
the stop predicate `f` — one standard query bracketed by answer-wire Hadamard layers. -/
def stopMark (f : Addr a → Bool) : Matrix (OReg a w) (OReg a w) ℂ :=
  ansH * xorOracle f * ansH

/-- **Unitarity.** The coherent stop marking is unitary, as an instance of the public
phase-form interface `PhaseOf` of the standard oracle. -/
theorem stopMark_uni (f : Addr a → Bool) :
    stopMark f ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  phaseOf_uni (stopPhase (a := a) (w := w) f)

/-- The coherent stop marking acts inside a wire-extended block as the wire-level
Hadamard–XOR–Hadamard sandwich of the flag state. -/
theorem mark_wireExt (f : Addr a → Bool) (x : Addr a) (φ : QState Bool) (u : Fin w → Bool) :
    stopMark f *ᵥ wireExt x φ u
      = wireExt x (Hadamard *ᵥ (fun b => (Hadamard *ᵥ φ) (b ^^ f x))) u := by
  rw [stopMark, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ansH_wireExt, xor_wireExt, ansH_wireExt]

/-- The wire Hadamard sends `Plus` back to the unflagged basis state. -/
theorem had_plus : Hadamard *ᵥ Plus = Ket false := by
  have hP : Hadamard *ᵥ Ket false = Plus := applyGate_hadamard_ket_false
  rw [← hP, Matrix.mulVec_mulVec, hadamard_mul_self, Matrix.one_mulVec]

/-- The wire Hadamard sends `Minus` back to the flagged basis state. -/
theorem had_minus : Hadamard *ᵥ Minus = Ket true := by
  have hM : Hadamard *ᵥ Ket true = Minus := applyGate_hadamard_ket_true
  rw [← hM, Matrix.mulVec_mulVec, hadamard_mul_self, Matrix.one_mulVec]

/-- The uniform `Plus` state is invariant under XOR shifts of the wire index. -/
theorem plusFlat (c : Bool) : (fun b => Plus (b ^^ c)) = Plus := by
  funext b
  cases b <;> cases c <;> rfl

/-- XOR-shifting the wire index reflects the `Minus` state. -/
theorem minusFlip : (fun b => Minus (b ^^ true)) = (-1 : ℂ) • Minus := by
  funext b
  cases b <;> simp [Minus, Hadamard, Pi.smul_apply, smul_eq_mul]

/-- Scalar multiplication distributes through wire extension. -/
theorem wireExt_smul (c : ℂ) (x : Addr a) (φ : QState Bool) (u : Fin w → Bool) :
    wireExt x (c • φ) u = c • wireExt x φ u := by
  funext r
  simp [wireExt]

/-- The negated flagged basis state, wire-extended: the pointwise form used by the
marked generator action. -/
theorem wire_negKet (x : Addr a) (b : Bool) (u : Fin w → Bool) :
    wireExt x ((-1 : ℂ) • Ket b) u = -(Ket (x, b, u)) := by
  funext r
  by_cases h1 : r.1 = x
  · by_cases h2 : r.2.2 = u
    · by_cases hb : r.2.1 = b <;>
        simp [Qatlib.Foundations.PureStateMath.Ket, wireExt, h1, h2, hb, Prod.ext_iff]
    · simp [Qatlib.Foundations.PureStateMath.Ket, wireExt, h1, h2, Prod.ext_iff]
  · simp [Qatlib.Foundations.PureStateMath.Ket, wireExt, h1, Prod.ext_iff]

/-- The sandwich at a running predicate value is the identity on the flagged wire
state. -/
theorem shift_had_zero (b : Bool) :
    Hadamard *ᵥ (fun b' : Bool => (Hadamard *ᵥ Ket b) (b' ^^ false)) = Ket b := by
  rw [show (fun b' : Bool => (Hadamard *ᵥ Ket b) (b' ^^ false)) = Hadamard *ᵥ Ket b by
    funext b'; cases b' <;> rfl]
  rw [Matrix.mulVec_mulVec, hadamard_mul_self, Matrix.one_mulVec]

/-- **Generator action, marked.** On a flag-set basis state at a stopped address the
coherent stop marking applies the phase `-1`. -/
theorem ketMarked (f : Addr a → Bool) (x : Addr a) (u : Fin w → Bool)
    (hstop : f x = true) :
    stopMark f *ᵥ Ket (x, true, u) = -(Ket (x, true, u)) := by
  have hM : Hadamard *ᵥ Ket true = Minus := applyGate_hadamard_ket_true
  rw [show -(Ket (x, true, u)) = wireExt x ((-1 : ℂ) • Ket true) u from
      (wire_negKet x true u).symm]
  rw [ket_wireExt, mark_wireExt, hstop, hM, minusFlip, Matrix.mulVec_smul, had_minus]

/-- **Generator action, unflagged.** The coherent stop marking fixes every flag-unset
basis state, independently of the stop predicate. -/
theorem ketUnflagged (f : Addr a → Bool) (x : Addr a) (u : Fin w → Bool) :
    stopMark f *ᵥ Ket (x, false, u) = Ket (x, false, u) := by
  have hP : Hadamard *ᵥ Ket false = Plus := applyGate_hadamard_ket_false
  rw [ket_wireExt, mark_wireExt, hP, plusFlat (f x), had_plus]

/-- **Generator action, continue.** On any basis state of a still-running address the
coherent stop marking is the identity. -/
theorem ketContinue (f : Addr a → Bool) (x : Addr a) (b : Bool) (u : Fin w → Bool)
    (hrun : f x = false) :
    stopMark f *ᵥ Ket (x, b, u) = Ket (x, b, u) := by
  rw [ket_wireExt, mark_wireExt, hrun, shift_had_zero]

/-! ### The stop/continue subspace decomposition -/

def stopSub (f : Addr a → Bool) : Submodule ℂ (QState (OReg a w)) :=
  Submodule.span ℂ {s | ∃ r : OReg a w, r.2.1 = true ∧ f r.1 = true ∧ s = Ket r}

/-- The unmarked (continue) subspace: the span of the flag-set basis states at
still-running addresses. -/
def contSub (f : Addr a → Bool) : Submodule ℂ (QState (OReg a w)) :=
  Submodule.span ℂ {s | ∃ r : OReg a w, r.2.1 = true ∧ f r.1 = false ∧ s = Ket r}

/-- The auxiliary flag-unset subspace: the span of the basis states whose answer wire
carries no flag. -/
def auxSub : Submodule ℂ (QState (OReg a w)) :=
  Submodule.span ℂ {s | ∃ r : OReg a w, r.2.1 = false ∧ s = Ket r}

/-- **Action on the marked subspace.** The coherent stop marking multiplies every
stopped-sector state by the phase `-1`. -/
theorem markStopSub (f : Addr a → Bool) {v : QState (OReg a w)}
    (hv : v ∈ stopSub f) : stopMark f *ᵥ v = -v := by
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨r, hr1, hrf, rfl⟩ := hs
    obtain ⟨x, b, u⟩ := r
    subst hr1
    exact ketMarked f x u hrf
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy, neg_add]
  | smul c s _ ih => rw [Matrix.mulVec_smul, ih, smul_neg]

/-- **Action on the unmarked subspace.** The coherent stop marking fixes every
continue-sector state. -/
theorem markContSub (f : Addr a → Bool) {v : QState (OReg a w)}
    (hv : v ∈ contSub f) : stopMark f *ᵥ v = v := by
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨r, hr1, hrf, rfl⟩ := hs
    obtain ⟨x, b, u⟩ := r
    subst hr1
    exact ketContinue f x true u hrf
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy]
  | smul c s _ ih => rw [Matrix.mulVec_smul, ih]

/-- The coherent stop marking also fixes the auxiliary flag-unset sector pointwise. -/
theorem markAuxSub (f : Addr a → Bool) {v : QState (OReg a w)}
    (hv : v ∈ auxSub) : stopMark f *ᵥ v = v := by
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨r, hr1, rfl⟩ := hs
    obtain ⟨x, b, u⟩ := r
    subst hr1
    exact ketUnflagged f x u
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy]
  | smul c s _ ih => rw [Matrix.mulVec_smul, ih]

/-- A stopped-sector state vanishes at every basis index outside the stopped sector. -/
theorem stopCoord (f : Addr a → Bool) {v : QState (OReg a w)}
    (hv : v ∈ stopSub f) (r : OReg a w) (hr : ¬(r.2.1 = true ∧ f r.1 = true)) :
    v r = 0 := by
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, hi1, hif, rfl⟩ := hs
    exact ket_ne (by rintro rfl; exact hr ⟨hi1, hif⟩)
  | zero => rfl
  | add x y _ _ ihx ihy => simp [ihx, ihy]
  | smul c s _ ih => simp [ih]

/-- A continue-sector state vanishes at every basis index outside the continue
sector. -/
theorem contCoord (f : Addr a → Bool) {v : QState (OReg a w)}
    (hv : v ∈ contSub f) (r : OReg a w) (hr : ¬(r.2.1 = true ∧ f r.1 = false)) :
    v r = 0 := by
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, hi1, hif, rfl⟩ := hs
    exact ket_ne (by rintro rfl; exact hr ⟨hi1, hif⟩)
  | zero => rfl
  | add x y _ _ ihx ihy => simp [ihx, ihy]
  | smul c s _ ih => simp [ih]

/-- An auxiliary-sector state vanishes at every flag-set basis index. -/
theorem auxCoord {v : QState (OReg a w)}
    (hv : v ∈ auxSub) (r : OReg a w) (hr : ¬(r.2.1 = false)) : v r = 0 := by
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, hi1, rfl⟩ := hs
    exact ket_ne (by rintro rfl; exact hr hi1)
  | zero => rfl
  | add x y _ _ ihx ihy => simp [ihx, ihy]
  | smul c s _ ih => simp [ih]

/-- The stopped and running flag-set sectors are disjoint: the marked/continue split of
the flag-set sector is direct. -/
theorem stopDisjCont (f : Addr a → Bool) :
    Disjoint (stopSub (w := w) f) (contSub (w := w) f) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro v hv
  have h1 : v ∈ stopSub (w := w) f := (Submodule.mem_inf.mp hv).1
  have h2 : v ∈ contSub (w := w) f := (Submodule.mem_inf.mp hv).2
  funext r
  by_cases hb : r.2.1 = true
  · by_cases hf : f r.1 = true
    · exact contCoord f h2 r (by simp [hb, hf])
    · exact stopCoord f h1 r (by simp [hb, hf])
  · exact stopCoord f h1 r (by simp [hb])

/-- The stopped sector is disjoint from the auxiliary flag-unset sector. -/
theorem stopDisjAux (f : Addr a → Bool) :
    Disjoint (stopSub (w := w) f) (auxSub (a := a) (w := w)) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro v hv
  have h1 : v ∈ stopSub (w := w) f := (Submodule.mem_inf.mp hv).1
  have h2 : v ∈ auxSub (a := a) (w := w) := (Submodule.mem_inf.mp hv).2
  funext r
  by_cases hb : r.2.1 = true
  · exact auxCoord h2 r (by simp [hb])
  · exact stopCoord f h1 r (by simp [hb])

/-- The running sector is disjoint from the auxiliary flag-unset sector. -/
theorem contDisjAux (f : Addr a → Bool) :
    Disjoint (contSub (w := w) f) (auxSub (a := a) (w := w)) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro v hv
  have h1 : v ∈ contSub (w := w) f := (Submodule.mem_inf.mp hv).1
  have h2 : v ∈ auxSub (a := a) (w := w) := (Submodule.mem_inf.mp hv).2
  funext r
  by_cases hb : r.2.1 = true
  · exact auxCoord h2 r (by simp [hb])
  · exact contCoord f h1 r (by simp [hb])

/-- **Subspace decomposition.** The stopped sector, the running sector and the
auxiliary flag-unset sector together span the whole register. -/
theorem markSupTop (f : Addr a → Bool) :
    stopSub (w := w) f ⊔ contSub (w := w) f ⊔ (auxSub (a := a) (w := w)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [state_ket_expansion v]
  refine Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_
  by_cases hb : r.2.1 = true
  · by_cases hf : f r.1 = true
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_left (Submodule.subset_span ⟨r, hb, hf, rfl⟩))
    · have hf' : f r.1 = false := by simp [hf]
      exact Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.subset_span ⟨r, hb, hf', rfl⟩))
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨r, by simp [hb], rfl⟩)

end Qatlib.Papers.VarTimeAmpAmp10.CoherentStop
