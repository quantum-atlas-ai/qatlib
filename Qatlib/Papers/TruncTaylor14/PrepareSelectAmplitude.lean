/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.PrepareSelectCount
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Rotation-angle and amplitude semantics of the Taylor PREPARE cascade

This module gives the analytic meaning of the physical unary cascade defined in
`PrepareSelectCount`.  The all-zero register is the input basis state.  At each new
wire, the controlled rotation leaves every non-top unary amplitude unchanged, keeps
`cos θ` times the old top amplitude on the old top state, and moves `-sin θ` times the
old top amplitude to the new top state.  `cascadeAmplitude` is the resulting exact
real amplitude recurrence.  The prepared state is normalized because it is the action
of the denotation of the actual unitary cascade word on a computational basis ket.

The tail-angle theorem turns the recurrence into a preparation prescription.  If the
cosine at each step is the desired non-top amplitude divided by the current tail norm,
and minus the sine is the next tail norm divided by the current tail norm, then every
amplitude has its prescribed value. The concrete factorial coefficients, tail sums,
negative arccos angles, and physical prepared-state specialization are constructed in
`Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor.taylor_prepared_entry`.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Papers.TruncTaylor14.ResourceCount
open Qatlib.Papers.TruncTaylor14.PrepareSelectCount

open scoped Matrix
open scoped BigOperators

namespace Qatlib.Papers.TruncTaylor14.PrepareSelectAmplitude

noncomputable section

/-- The all-false computational basis register, the input of the PREPARE cascade. -/
def zeroReg (n : ℕ) : Reg n := fun _ => false

/-- The real amplitude recurrence of the cascade on `n` wires.  Indices above `n`
have zero amplitude; index `n` is the current top unary state. -/
def cascadeAmplitude (θ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
      if k < n then cascadeAmplitude θ n k
      else if k = n then cascadeAmplitude θ n n * Real.cos (θ n)
      else if k = n + 1 then -cascadeAmplitude θ n n * Real.sin (θ n)
      else 0

/-- The amplitude on the current top unary basis state. -/
def cascadeTop (θ : ℕ → ℝ) (n : ℕ) : ℝ := cascadeAmplitude θ n n

/-- On the first wire the two amplitudes are respectively cosine and minus sine. -/
theorem cascadeAmplitude_one (θ : ℕ → ℝ) (k : ℕ) :
    cascadeAmplitude θ 1 k =
      if k = 0 then Real.cos (θ 0)
      else if k = 1 then -Real.sin (θ 0) else 0 := by
  by_cases hk0 : k = 0
  · subst k
    simp [cascadeAmplitude]
  · by_cases hk1 : k = 1
    · subst k
      simp [cascadeAmplitude]
    · simp [cascadeAmplitude, hk0, hk1]

/-- Amplitudes above the current top unary state vanish. -/
theorem cascadeAmplitude_eq_zero (θ : ℕ → ℝ) {n k : ℕ} (h : n < k) :
    cascadeAmplitude θ n k = 0 := by
  induction n generalizing k with
  | zero => simp [cascadeAmplitude, Nat.ne_of_gt h]
  | succ n ih =>
      simp only [cascadeAmplitude]
      split_ifs with hkn hkn' hks
      · omega
      · omega
      · omega
      · rfl

/-- Adding a wire leaves every strictly non-top old amplitude unchanged. -/
theorem cascadeAmplitude_lt (θ : ℕ → ℝ) {n k : ℕ} (h : k < n) :
    cascadeAmplitude θ (n + 1) k = cascadeAmplitude θ n k := by
  simp [cascadeAmplitude, h]

/-- Adding a wire multiplies the old penultimate position of the enlarged register by
cosine; equivalently, the old top amplitude is split by the new controlled rotation. -/
theorem cascadeAmplitude_penultimate (θ : ℕ → ℝ) (n : ℕ) :
    cascadeAmplitude θ (n + 1) n = cascadeTop θ n * Real.cos (θ n) := by
  simp [cascadeAmplitude, cascadeTop]

/-- The new top amplitude is minus sine times the old top amplitude. -/
theorem cascadeTop_succ (θ : ℕ → ℝ) (n : ℕ) :
    cascadeTop θ (n + 1) = -cascadeTop θ n * Real.sin (θ n) := by
  simp [cascadeTop, cascadeAmplitude]

/-- Exact angle-to-amplitude semantics.  The sequence `r` is the norm remaining in
the current top state, and `a` is the desired amplitude left behind at each stage.
The hypotheses are precisely the cosine/sine splitting equations of the cascade. -/
theorem cascadeAmplitude_of_tail (θ a r : ℕ → ℝ) (hr0 : r 0 = 1)
    (hcos : ∀ n, Real.cos (θ n) * r n = a n)
    (hsin : ∀ n, -Real.sin (θ n) * r n = r (n + 1)) :
    (∀ n, cascadeTop θ n = r n) ∧
      ∀ n k, k < n → cascadeAmplitude θ n k = a k := by
  have htop : ∀ n, cascadeTop θ n = r n := by
    intro n
    induction n with
    | zero => simpa [cascadeTop, cascadeAmplitude] using hr0.symm
    | succ n ih =>
        rw [cascadeTop_succ, ih]
        have h := hsin n
        nlinarith
  refine ⟨htop, ?_⟩
  intro n
  induction n with
  | zero => intro k h; omega
  | succ n ih =>
      intro k hk
      by_cases hkn : k < n
      · rw [cascadeAmplitude_lt θ hkn]
        exact ih k hkn
      · have hk' : k = n := by omega
        subst k
        rw [cascadeAmplitude_penultimate, htop n]
        have h := hcos n
        nlinarith

/-- A one-qubit rotation sends the false ket to cosine on false and minus sine on true. -/
private theorem rot2_apply_false (θ : ℝ) :
    ApplyGate (rot2 θ) (Ket false) =
      fun b : Bool => if b then (-Real.sin θ : ℂ) else (Real.cos θ : ℂ) := by
  funext b
  cases b <;> simp [ApplyGate, Matrix.mulVec, dotProduct, rot2, rot2C,
    Qatlib.Foundations.PureStateMath.Ket]

/-- A controlled rotation with a false control leaves a basis ket unchanged. -/
private theorem crot2_apply_false_control (θ : ℝ) (b : Bool) :
    ApplyGate (crot2 θ) (Ket (false, b)) = Ket (false, b) := by
  funext x
  rcases x with ⟨a, c⟩
  cases a <;> cases b <;> cases c <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, crot2, relabelGate,
      Matrix.blockDiagonal_apply, Matrix.one_apply, Qatlib.Foundations.PureStateMath.Ket,
      rot2, rot2C]

/-- A controlled rotation on a true control and false target splits the basis ket into
cosine on the unchanged state and minus sine on the true-target state. -/
private theorem crot2_apply_true_false (θ : ℝ) :
    ApplyGate (crot2 θ) (Ket (true, false)) =
      fun x : Bool × Bool =>
        if x = (true, false) then (Real.cos θ : ℂ)
        else if x = (true, true) then (-Real.sin θ : ℂ) else 0 := by
  funext x
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, crot2, relabelGate,
      Matrix.blockDiagonal_apply, Matrix.one_apply, Qatlib.Foundations.PureStateMath.Ket,
      rot2, rot2C]

/-- Relabeling a computational basis ket relabels its basis index. -/
private theorem relabelState_ket {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (i : I) :
    relabelState e (Ket i) = Ket (e i) := by
  funext j
  simp [Qatlib.Foundations.PureStateMath.Ket, relabelState, Equiv.symm_apply_eq]

/-- The register-transported controlled rotation is the identity when its control is false. -/
private theorem crotB_apply_false_control (θ : ℝ) (b : Bool) :
    ApplyGate (crotB θ) (Ket (regOneBool.symm false, b)) =
      Ket (regOneBool.symm false, b) := by
  let e := regOneBool.symm.prodCongr (Equiv.refl Bool)
  have hf : Ket (regOneBool.symm false, b) =
      relabelState e (Ket (false, b)) := (relabelState_ket e (false, b)).symm
  calc
    ApplyGate (crotB θ) (Ket (regOneBool.symm false, b)) =
        relabelState e (ApplyGate (crot2 θ) (Ket (false, b))) := by
      rw [show crotB θ = relabelGate e (crot2 θ) from rfl, hf, applyGate_relabelGate]
    _ = relabelState e (Ket (false, b)) := by rw [crot2_apply_false_control]
    _ = Ket (regOneBool.symm false, b) := relabelState_ket e (false, b)

/-- The register-transported controlled rotation splits a true-control/false-target ket. -/
private theorem crotB_apply_true_false (θ : ℝ) :
    ApplyGate (crotB θ) (Ket (regOneBool.symm true, false)) =
      fun x : Reg 1 × Bool =>
        if x = (regOneBool.symm true, false) then (Real.cos θ : ℂ)
        else if x = (regOneBool.symm true, true) then (-Real.sin θ : ℂ) else 0 := by
  let e := regOneBool.symm.prodCongr (Equiv.refl Bool)
  have hf : Ket (regOneBool.symm true, false) =
      relabelState e (Ket (true, false)) := (relabelState_ket e (true, false)).symm
  rw [show crotB θ = relabelGate e (crot2 θ) from rfl, hf, applyGate_relabelGate,
    crot2_apply_true_false]
  funext x
  by_cases hxf : x = (regOneBool.symm true, false)
  · subst x
    simp [e, relabelState]
  · by_cases hxt : x = (regOneBool.symm true, true)
    · subst x
      simp [e, relabelState]
    · have hef : e.symm x ≠ (true, false) := by
        intro h
        apply hxf
        rw [← Equiv.apply_symm_apply e x, h]
        rfl
      have het : e.symm x ≠ (true, true) := by
        intro h
        apply hxt
        rw [← Equiv.apply_symm_apply e x, h]
        rfl
      simp [relabelState, hxf, hxt, hef, het]

/-- Append one Boolean wire to a register using the canonical register split. -/
def snocReg (n : ℕ) (x : Reg n) (b : Bool) : Reg (n + 1) :=
  (regAppendEquiv n 1).symm (x, regOneBool.symm b)

/-- Reading an old wire after `snocReg` returns the old register bit. -/
theorem snocReg_castAdd (n : ℕ) (x : Reg n) (b : Bool) (i : Fin n) :
    snocReg n x b (Fin.castAdd 1 i) = x i := by
  have h := congrArg (fun z : Reg n × Reg 1 => z.1 i)
    (Equiv.apply_symm_apply (regAppendEquiv n 1) (x, regOneBool.symm b))
  exact h

/-- Reading the appended wire after `snocReg` returns the appended bit. -/
theorem snocReg_last (n : ℕ) (x : Reg n) (b : Bool) :
    snocReg n x b (Fin.natAdd n ⟨0, by omega⟩) = b := by
  have h := congrArg (fun z : Reg n × Reg 1 => regOneBool z.2)
    (Equiv.apply_symm_apply (regAppendEquiv n 1) (x, regOneBool.symm b))
  exact h

/-- Appending false to a unary basis state gives the same unary index in the enlarged
register. -/
theorem snocReg_unary (n : ℕ) (k : Fin (n + 1)) :
    snocReg n (unaryReg n k) false = unaryReg (n + 1) k.castSucc := by
  funext i
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val, hi⟩
    have hij : i = Fin.castAdd 1 j := Fin.ext rfl
    rw [hij, snocReg_castAdd]
    rfl
  · have hi' : i.val = n := by omega
    have hij : i = Fin.natAdd n ⟨0, by omega⟩ := Fin.ext (by simpa using hi')
    rw [hij, snocReg_last]
    change false = decide (n < k.val)
    have hnk : ¬ n < k.val := by omega
    simp [hnk]

/-- Appending true to the old top unary state gives the new top unary state. -/
theorem snocReg_unary_top_true (n : ℕ) :
    snocReg (n + 1) (unaryReg (n + 1) (Fin.last (n + 1))) true =
      unaryReg (n + 2) (Fin.last (n + 2)) := by
  funext i
  by_cases hi : i.val < n + 1
  · let j : Fin (n + 1) := ⟨i.val, hi⟩
    have hij : i = Fin.castAdd 1 j := Fin.ext rfl
    rw [hij, snocReg_castAdd]
    simp [unaryReg, j]
    omega
  · have hi' : i.val = n + 1 := by omega
    have hij : i = Fin.natAdd (n + 1) ⟨0, by omega⟩ := Fin.ext (by simpa using hi')
    rw [hij, snocReg_last]
    change true = decide (n + 1 < n + 2)
    simp

/-- Appending false to the all-zero register gives the all-zero register. -/
theorem snocReg_zero (n : ℕ) : snocReg n (zeroReg n) false = zeroReg (n + 1) := by
  have hz (m : ℕ) : zeroReg m = unaryReg m ⟨0, by omega⟩ := by
    funext i
    simp [zeroReg, unaryReg]
  rw [hz n, hz (n + 1)]
  exact snocReg_unary n ⟨0, by omega⟩

/-- Extend a state by one computational Boolean basis wire. -/
def snocState (n : ℕ) (ψ : QState (Reg n)) (b : Bool) : QState (Reg (n + 1)) :=
  relabelState (regAppendEquiv n 1).symm (TensorState ψ (Ket (regOneBool.symm b)))

/-- Extending a basis ket by a wire gives the ket of the appended register. -/
theorem snocState_ket (n : ℕ) (x : Reg n) (b : Bool) :
    snocState n (Ket x) b = Ket (snocReg n x b) := by
  rw [snocState, tensorState_ket_ket, relabelState_ket]
  rfl

/-- State extension is additive in the original state. -/
private theorem snocState_add (n : ℕ) (ψ φ : QState (Reg n)) (b : Bool) :
    snocState n (ψ + φ) b = snocState n ψ b + snocState n φ b := by
  funext x
  simp [snocState, relabelState, TensorState, add_mul]

/-- State extension commutes with complex scalar multiplication. -/
private theorem snocState_smul (n : ℕ) (c : ℂ) (ψ : QState (Reg n)) (b : Bool) :
    snocState n (c • ψ) b = c • snocState n ψ b := by
  funext x
  simp [snocState, relabelState, TensorState, mul_assoc]

/-- State extension preserves a finite sum of scalar multiples of basis kets. -/
private theorem snocState_sum_ket {ι : Type*} [DecidableEq ι] (n : ℕ)
    (s : Finset ι) (a : ι → ℂ) (f : ι → Reg n) :
    snocState n (∑ i ∈ s, a i • Ket (f i)) false =
      ∑ i ∈ s, a i • Ket (snocReg n (f i) false) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext x
      simp [snocState, relabelState, TensorState]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, snocState_add, snocState_smul, ih, snocState_ket]

/-- The denotation of a prefix-lifted word is the placement of its denotation. -/
private theorem denoteLiftFirst (n : ℕ) (C : Circuit (Reg n)) :
    Denote (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ) (C.map (liftFirst n)) =
      PlacedFirst n 1 (Denote (1 : Matrix (Reg n) (Reg n) ℂ) C) := by
  induction C with
  | nil =>
      simp [denote_nil, PlacedFirst, tensorGate_one]
  | cons s C ih =>
      cases s with
      | gate U =>
          simp only [List.map_cons, liftFirst, denote_gate, ih, PlacedFirst]
          rw [← reidxMul, tensorGate_mul, Matrix.mul_one]
      | query =>
          simp only [List.map_cons, liftFirst, denote_query, ih, Matrix.mul_one]

/-- A prefix-placed gate acts on the original factor and leaves the appended basis wire
unchanged. -/
private theorem applyPlacedFirst (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    ApplyGate (PlacedFirst n 1 U) (snocState n ψ false) =
      snocState n (ApplyGate U ψ) false := by
  rw [show PlacedFirst n 1 U =
      relabelGate (regAppendEquiv n 1).symm (TensorGate U 1) from rfl,
    snocState, applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  rfl

/-- The final split of the cascade reads the old register and the newly appended wire. -/
private theorem lastE_snocReg (n : ℕ) (p : Reg (n + 1)) (b : Bool) :
    lastE n (snocReg (n + 1) p b) =
      ((regAppendEquiv n 1 p).1, ((regAppendEquiv n 1 p).2, b)) := by
  apply Prod.ext
  · funext i
    change snocReg (n + 1) p b (Fin.castAdd 2 i) = (regAppendEquiv n 1 p).1 i
    rw [show (Fin.castAdd 2 i : Fin (n + 1 + 1)) =
        Fin.castAdd 1 (Fin.castAdd 1 i) from rfl,
      snocReg_castAdd, regAppendEquiv_apply_fst]
  · apply Prod.ext
    · apply regOneBool.injective
      change snocReg (n + 1) p b
        (Fin.natAdd n (Fin.castAdd 1 ⟨0, by omega⟩)) =
          (regAppendEquiv n 1 p).2 ⟨0, by omega⟩
      rw [show (Fin.natAdd n (Fin.castAdd 1 ⟨0, by omega⟩) : Fin (n + 1 + 1)) =
          Fin.castAdd 1 (Fin.natAdd n ⟨0, by omega⟩) from rfl,
        snocReg_castAdd, regAppendEquiv_apply_snd]
    · change snocReg (n + 1) p b (Fin.natAdd (n + 1) ⟨0, by omega⟩) = b
      exact snocReg_last (n + 1) p b

/-- The last controlled rotation acts only on the predecessor/target pair, leaving the
spectator register as a tensor factor. -/
private theorem lastCrot_snocReg (n : ℕ) (θ : ℝ) (p : Reg (n + 1)) (b : Bool) :
    ApplyGate (lastCrot n θ) (Ket (snocReg (n + 1) p b)) =
      relabelState (lastE n).symm
        (TensorState (Ket (regAppendEquiv n 1 p).1)
          (ApplyGate (crotB θ)
            (Ket ((regAppendEquiv n 1 p).2, b)))) := by
  rw [lastCrot]
  have hk : Ket (snocReg (n + 1) p b) =
      relabelState (lastE n).symm
        (Ket ((regAppendEquiv n 1 p).1, ((regAppendEquiv n 1 p).2, b))) := by
    rw [← lastE_snocReg n p b, relabelState_ket, Equiv.symm_apply_apply]
  rw [hk, applyGate_relabelGate, ← tensorState_ket_ket, applyGate_tensorGate,
    applyGate_one]

/-- The predecessor control bit of a unary basis state is true exactly at its top index. -/
private theorem unary_predecessor (n : ℕ) (k : Fin (n + 2)) :
    regOneBool (regAppendEquiv n 1 (unaryReg (n + 1) k)).2 = decide (n < k.val) := by
  change unaryReg (n + 1) k (Fin.natAdd n ⟨0, by omega⟩) = decide (n < k.val)
  rfl

/-- The state obtained by executing the actual cascade word on the all-zero ket. -/
def cascadePrepared (n : ℕ) (θ : Fin n → ℝ) : QState (Reg n) :=
  ApplyGate (Denote (1 : Matrix (Reg n) (Reg n) ℂ) (cascWord n θ)) (Ket (zeroReg n))

/-- The split of a true-control basis ket as a sum of the unchanged and advanced kets. -/
private theorem crotB_apply_true_false_sum (θ : ℝ) :
    ApplyGate (crotB θ) (Ket (regOneBool.symm true, false)) =
      (Real.cos θ : ℂ) • Ket (regOneBool.symm true, false) +
        (-Real.sin θ : ℂ) • Ket (regOneBool.symm true, true) := by
  rw [crotB_apply_true_false]
  funext x
  by_cases hxf : x = (regOneBool.symm true, false)
  · simp [hxf, Qatlib.Foundations.PureStateMath.Ket]
  · by_cases hxt : x = (regOneBool.symm true, true)
    · simp [hxt, Qatlib.Foundations.PureStateMath.Ket]
    · simp [hxf, hxt, Qatlib.Foundations.PureStateMath.Ket]

/-- Addition in the predecessor/target factor commutes with the final register relabeling. -/
private theorem lastTensor_add (n : ℕ) (s : Reg n) (φ χ : QState (Reg 1 × Bool)) :
    relabelState (lastE n).symm (TensorState (Ket s) (φ + χ)) =
      relabelState (lastE n).symm (TensorState (Ket s) φ) +
        relabelState (lastE n).symm (TensorState (Ket s) χ) := by
  funext x
  simp [relabelState, TensorState, mul_add]

/-- Scalar multiplication in the predecessor/target factor commutes with the final
register relabeling. -/
private theorem lastTensor_smul (n : ℕ) (s : Reg n) (c : ℂ)
    (φ : QState (Reg 1 × Bool)) :
    relabelState (lastE n).symm (TensorState (Ket s) (c • φ)) =
      c • relabelState (lastE n).symm (TensorState (Ket s) φ) := by
  funext x
  simp [relabelState, TensorState, mul_left_comm]

/-- Below the top unary index, the last controlled rotation leaves the basis ket fixed. -/
private theorem lastCrot_unary_of_lt (n : ℕ) (θ : ℝ) (k : Fin (n + 2))
    (hk : k.val < n + 1) :
    ApplyGate (lastCrot n θ) (Ket (unaryReg (n + 2) k.castSucc)) =
      Ket (unaryReg (n + 2) k.castSucc) := by
  rw [← snocReg_unary (n + 1) k, lastCrot_snocReg]
  have hc : (regAppendEquiv n 1 (unaryReg (n + 1) k)).2 = regOneBool.symm false := by
    apply regOneBool.injective
    simp [unary_predecessor, show ¬n < k.val by omega]
  rw [hc, crotB_apply_false_control, tensorState_ket_ket, relabelState_ket,
    ← hc, ← lastE_snocReg, Equiv.symm_apply_apply]

/-- At the top unary index, the last controlled rotation splits the old top ket into its
cosine-weighted penultimate part and its minus-sine-weighted new top part. -/
private theorem lastCrot_unary_top (n : ℕ) (θ : ℝ) :
    ApplyGate (lastCrot n θ) (Ket (unaryReg (n + 2) (Fin.last (n + 1)).castSucc)) =
      (Real.cos θ : ℂ) • Ket (unaryReg (n + 2) (Fin.last (n + 1)).castSucc) +
        (-Real.sin θ : ℂ) • Ket (unaryReg (n + 2) (Fin.last (n + 2))) := by
  rw [← snocReg_unary (n + 1) (Fin.last (n + 1)), lastCrot_snocReg]
  have hc : (regAppendEquiv n 1 (unaryReg (n + 1) (Fin.last (n + 1)))).2 =
      regOneBool.symm true := by
    apply regOneBool.injective
    simp [unary_predecessor]
  rw [hc, crotB_apply_true_false_sum, lastTensor_add, lastTensor_smul, lastTensor_smul,
    tensorState_ket_ket, tensorState_ket_ket, relabelState_ket, relabelState_ket,
    ← hc, ← lastE_snocReg, Equiv.symm_apply_apply]
  have hnew : (lastE n).symm
      ((regAppendEquiv n 1 (unaryReg (n + 1) (Fin.last (n + 1)))).1,
        ((regAppendEquiv n 1 (unaryReg (n + 1) (Fin.last (n + 1)))).2, true)) =
      unaryReg (n + 2) (Fin.last (n + 2)) := by
    rw [← lastE_snocReg, Equiv.symm_apply_apply, snocReg_unary_top_true]
  rw [hnew]

/-- The exact successor equation of the physical cascade state: first execute the prefix
cascade with a false appended wire, then apply the new last controlled rotation. -/
theorem cascadePrepared_succ (n : ℕ) (θ : Fin (n + 2) → ℝ) :
    cascadePrepared (n + 2) θ =
      ApplyGate (lastCrot n (θ ⟨n + 1, by omega⟩))
        (snocState (n + 1) (cascadePrepared (n + 1) (fun i => θ i.castSucc)) false) := by
  have hk : Ket (zeroReg (n + 2)) = snocState (n + 1) (Ket (zeroReg (n + 1))) false := by
    rw [snocState_ket, snocReg_zero]
  rw [cascadePrepared, show cascWord (n + 2) θ =
      (cascWord (n + 1) (fun i => θ i.castSucc)).map (liftFirst (n + 1)) ++
        [Step.gate (lastCrot n (θ ⟨n + 1, by omega⟩))] from rfl,
    denote_append, denote_gate, denote_nil, Matrix.one_mul, denoteLiftFirst,
    applyGate_mul, hk, applyPlacedFirst]
  rfl

/-- A finite linear combination of the unary basis kets with real coefficients. -/
def unaryState (n : ℕ) (a : ℕ → ℝ) : QState (Reg n) :=
  ∑ k : Fin (n + 1), (a k.val : ℂ) • Ket (unaryReg n k)

/-- Matrix action preserves finite sums of states. -/
private theorem applyGate_sum {I ι : Type*} [Fintype I]
    (U : Matrix I I ℂ) (s : Finset ι) (f : ι → QState I) :
    ApplyGate U (∑ i ∈ s, f i) = ∑ i ∈ s, ApplyGate U (f i) := by
  exact Matrix.mulVec_sum U s f

/-- Matrix action preserves sums of two states. -/
private theorem applyGate_add {I : Type*} [Fintype I]
    (U : Matrix I I ℂ) (ψ φ : QState I) :
    ApplyGate U (ψ + φ) = ApplyGate U ψ + ApplyGate U φ := by
  exact Matrix.mulVec_add U ψ φ

/-- Extending a unary expansion by a false wire preserves its coefficients and shifts only
the ambient register size. -/
private theorem snocState_unaryState (n : ℕ) (a : ℕ → ℝ) :
    snocState n (unaryState n a) false =
      ∑ k : Fin (n + 1), (a k.val : ℂ) • Ket (unaryReg (n + 1) k.castSucc) := by
  rw [unaryState, snocState_sum_ket]
  exact Finset.sum_congr rfl (fun k _ => by rw [snocReg_unary])

/-- Matrix action preserves scalar multiples of states. -/
private theorem applyGate_smul {I : Type*} [Fintype I]
    (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  exact Matrix.mulVec_smul U c ψ

/-- The physically prepared cascade state is normalized, by unitarity of the actual
composed word rather than by an externally imposed normalization postulate. -/
theorem cascadePrepared_normalized (n : ℕ) (θ : Fin n → ℝ) :
    Normalized (cascadePrepared n θ) := by
  exact normalized_applyGate
    (denote_unitary _ (Submonoid.one_mem _) (cascUni n θ)) (normalized_ket (zeroReg n))

/-- The empty cascade prepares the unique empty-register basis ket. -/
theorem cascadePrepared_zero (θ : Fin 0 → ℝ) :
    cascadePrepared 0 θ = Ket (zeroReg 0) := by
  simp [cascadePrepared, cascWord, denote_nil]

/-- The one-wire cascade has exactly the cosine/minus-sine amplitudes of `rot2`. -/
theorem cascadePrepared_one (θ : Fin 1 → ℝ) (x : Reg 1) :
    cascadePrepared 1 θ x =
      if regOneBool x then (-Real.sin (θ 0) : ℂ) else (Real.cos (θ 0) : ℂ) := by
  rw [cascadePrepared]
  have hword : cascWord 1 θ =
      [Step.gate (relabelGate regOneBool.symm (rot2 (θ 0)))] := rfl
  rw [hword, denote_gate, denote_nil, Matrix.one_mul]
  have hk : Ket (zeroReg 1) = relabelState regOneBool.symm (Ket false) := by
    funext y
    by_cases hy : y = zeroReg 1
    · subst y
      simp [Qatlib.Foundations.PureStateMath.Ket, relabelState, zeroReg, regOneBool]
    · have hy0 : y 0 = true := by
        cases h : y 0 with
        | false =>
            exfalso
            apply hy
            funext i
            have hi : i = 0 := Subsingleton.elim i 0
            subst i
            exact h
        | true => rfl
      simp [Qatlib.Foundations.PureStateMath.Ket, relabelState, regOneBool, hy, hy0]
  rw [hk, applyGate_relabelGate]
  have hrot : ApplyGate (rot2 (θ 0)) (Ket false) =
      fun b : Bool => if b then (-Real.sin (θ 0) : ℂ) else (Real.cos (θ 0) : ℂ) := by
    funext b
    cases b <;> simp [ApplyGate, Matrix.mulVec, dotProduct, rot2, rot2C,
      Qatlib.Foundations.PureStateMath.Ket]
  rw [hrot]
  rfl

/-- The enlarged unary expansion splits into the old non-top terms, the cosine-weighted
old top term, and the minus-sine-weighted new top term. -/
private theorem unaryState_succ (θ : ℕ → ℝ) (n : ℕ) :
    unaryState (n + 2) (cascadeAmplitude θ (n + 2)) =
      (∑ k : Fin (n + 1), (cascadeAmplitude θ (n + 1) k.val : ℂ) •
          Ket (unaryReg (n + 2) k.castSucc.castSucc)) +
        (((cascadeAmplitude θ (n + 1) (n + 1) : ℝ) : ℂ) *
          (Real.cos (θ (n + 1)) : ℂ)) •
            Ket (unaryReg (n + 2) (Fin.last (n + 1)).castSucc) +
        (((cascadeAmplitude θ (n + 1) (n + 1) : ℝ) : ℂ) *
          (-Real.sin (θ (n + 1)) : ℂ)) •
            Ket (unaryReg (n + 2) (Fin.last (n + 2))) := by
  rw [unaryState, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt (k : Fin (n + 1)) :
      cascadeAmplitude θ (n + 2) (k.castSucc.castSucc).val =
        cascadeAmplitude θ (n + 1) (k.castSucc.castSucc).val :=
    cascadeAmplitude_lt θ (by
      simp only [Fin.val_castSucc, Fin.val_castSucc]
      exact k.isLt)
  have hsum : (∑ i : Fin (n + 1), ((cascadeAmplitude θ (n + 2) i.castSucc.castSucc.val : ℝ) : ℂ) •
          Qatlib.Foundations.PureStateMath.Ket (unaryReg (n + 2) i.castSucc.castSucc)) =
      (∑ i : Fin (n + 1), ((cascadeAmplitude θ (n + 1) i.val : ℝ) : ℂ) •
          Qatlib.Foundations.PureStateMath.Ket (unaryReg (n + 2) i.castSucc.castSucc)) :=
    Finset.sum_congr rfl (fun k _ => by
      rw [hlt k, Fin.val_castSucc, Fin.val_castSucc])
  rw [hsum]
  have h2 : cascadeAmplitude θ (n + 2) ((Fin.last (n + 1)).castSucc).val =
      cascadeAmplitude θ (n + 1) (n + 1) * Real.cos (θ (n + 1)) := by
    simp only [Fin.val_castSucc, Fin.val_last]
    have h := cascadeAmplitude_penultimate θ (n + 1)
    rw [show n + 1 + 1 = n + 2 from rfl, cascadeTop] at h
    exact h
  have h3 : cascadeAmplitude θ (n + 2) (Fin.last (n + 2)).val =
      -cascadeAmplitude θ (n + 1) (n + 1) * Real.sin (θ (n + 1)) := by
    simp [Fin.val_last, cascadeAmplitude]
  rw [h2, h3, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, mul_neg]

/-- Applying the new controlled rotation to an extended unary expansion gives the next
unary expansion, with exactly the coefficients of `cascadeAmplitude`. -/
private theorem lastCrot_unaryState (θ : ℕ → ℝ) (n : ℕ) :
    ApplyGate (lastCrot n (θ (n + 1)))
        (snocState (n + 1) (unaryState (n + 1) (cascadeAmplitude θ (n + 1))) false) =
      unaryState (n + 2) (cascadeAmplitude θ (n + 2)) := by
  rw [snocState_unaryState, unaryState_succ, Fin.sum_univ_castSucc, applyGate_add,
    applyGate_sum]
  simp_rw [applyGate_smul]
  have hfix (k : Fin (n + 1)) :
      ApplyGate (lastCrot n (θ (n + 1)))
          (Ket (unaryReg (n + 2) k.castSucc.castSucc)) =
        Ket (unaryReg (n + 2) k.castSucc.castSucc) :=
    lastCrot_unary_of_lt n (θ (n + 1)) k.castSucc
      (by simp only [Fin.val_castSucc]; exact k.isLt)
  simp_rw [hfix]
  rw [lastCrot_unary_top]
  simp only [smul_add, smul_smul, Fin.val_castSucc, Fin.val_last]
  simp only [add_assoc]

/-- A unary expansion has the prescribed coefficient on its indexed unary basis state. -/
theorem unaryState_entry (n : ℕ) (a : ℕ → ℝ) (k : Fin (n + 1)) :
    unaryState n a (unaryReg n k) = (a k.val : ℂ) := by
  classical
  rw [unaryState, Finset.sum_apply, Finset.sum_eq_single k]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro j _ hj
    have hne : unaryReg n j ≠ unaryReg n k := fun h => hj (unaryReg_inj _ h)
    simp [Qatlib.Foundations.PureStateMath.Ket, Ne.symm hne]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- A unary expansion vanishes outside the unary basis support. -/
theorem unaryState_support (n : ℕ) (a : ℕ → ℝ) (x : Reg n)
    (hx : ∀ k : Fin (n + 1), x ≠ unaryReg n k) : unaryState n a x = 0 := by
  classical
  rw [unaryState, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  simp [Qatlib.Foundations.PureStateMath.Ket, hx k]

/-- Exact denotation semantics for every infinite angle sequence, restricted to the
finite angle vector of each cascade. -/
theorem cascadePrepared_eq_unaryState_all (θ : ℕ → ℝ) (n : ℕ) :
    cascadePrepared n (fun i => θ i.val) = unaryState n (cascadeAmplitude θ n) := by
  have hpair : ∀ m : ℕ,
      (cascadePrepared m (fun i => θ i.val) = unaryState m (cascadeAmplitude θ m)) ∧
      (cascadePrepared (m + 1) (fun i => θ i.val) =
        unaryState (m + 1) (cascadeAmplitude θ (m + 1))) := by
    intro m
    induction m with
    | zero =>
        constructor
        · funext x
          have hx : x = zeroReg 0 := Subsingleton.elim x (zeroReg 0)
          subst hx
          have hu : unaryReg 0 (0 : Fin 1) = zeroReg 0 := Subsingleton.elim _ _
          rw [cascadePrepared_zero, ← hu, unaryState_entry]
          simp [Qatlib.Foundations.PureStateMath.Ket, cascadeAmplitude, hu]
        · funext x
          rw [cascadePrepared_one, show regOneBool x = x (0 : Fin 1) from rfl]
          cases hxb : x (0 : Fin 1) with
          | true =>
              have hx : x = unaryReg 1 1 := by
                funext i
                have hi : i = (0 : Fin 1) := Fin.ext (by omega)
                subst hi
                simp [unaryReg, hxb]
              rw [hx, unaryState_entry]
              simp [cascadeAmplitude_one]
          | false =>
              have hx : x = unaryReg 1 0 := by
                funext i
                have hi : i = (0 : Fin 1) := Fin.ext (by omega)
                subst hi
                simp [unaryReg, hxb]
              rw [hx, unaryState_entry]
              simp [cascadeAmplitude_one]
    | succ m ih =>
        refine ⟨ih.2, ?_⟩
        have hang : (fun i : Fin (m + 1) => θ (i.castSucc).val) = fun i => θ i.val := by
          funext i
          rw [Fin.val_castSucc]
        rw [cascadePrepared_succ, hang, ih.2]
        exact lastCrot_unaryState θ m
  exact (hpair n).1

/-- Extend a finite angle vector by zero for application of the infinite-sequence
semantics theorem. -/
def angleExtension {n : ℕ} (θ : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if h : k < n then θ ⟨k, h⟩ else 0

/-- The actual cascade prepared from any finite angle vector is exactly the unary
expansion with coefficients given by `cascadeAmplitude`. -/
theorem cascadePrepared_eq_unaryState (n : ℕ) (θ : Fin n → ℝ) :
    cascadePrepared n θ = unaryState n (cascadeAmplitude (angleExtension θ) n) := by
  have h := cascadePrepared_eq_unaryState_all (angleExtension θ) n
  have he : (fun i : Fin n => angleExtension θ i.val) = θ := by
    funext i
    simp [angleExtension]
  rw [he] at h
  exact h

/-- Exact prepared-state entry on the `k`-th unary basis state. -/
theorem cascadePrepared_entry (n : ℕ) (θ : Fin n → ℝ) (k : Fin (n + 1)) :
    cascadePrepared n θ (unaryReg n k) =
      (cascadeAmplitude (angleExtension θ) n k.val : ℂ) := by
  rw [cascadePrepared_eq_unaryState, unaryState_entry]

/-- Unary support of the actual cascade word: every basis state outside the `K+1`
unary strings has zero prepared amplitude. -/
theorem cascadePrepared_support (n : ℕ) (θ : Fin n → ℝ) (x : Reg n)
    (hx : ∀ k : Fin (n + 1), x ≠ unaryReg n k) : cascadePrepared n θ x = 0 := by
  rw [cascadePrepared_eq_unaryState]
  exact unaryState_support n _ x hx

/-- The real rotation amplitudes are normalized in the complex ℓ² sense.  The sum is
over exactly the `n+1` unary basis states; all other basis states vanish by
`cascadePrepared_support`. -/
theorem cascadeAmplitude_normalized (θ : ℕ → ℝ) (n : ℕ) :
    ∑ k : Fin (n + 1), ‖(cascadeAmplitude θ n k.val : ℂ)‖ ^ 2 = 1 := by
  classical
  have h := cascadePrepared_normalized n (fun i : Fin n => θ i.val)
  rw [cascadePrepared_eq_unaryState_all] at h
  unfold Normalized at h
  calc
    ∑ k : Fin (n + 1), ‖(cascadeAmplitude θ n k.val : ℂ)‖ ^ 2 =
        ∑ x ∈ Finset.univ.image (unaryReg n),
          ‖unaryState n (cascadeAmplitude θ n) x‖ ^ 2 := by
      rw [Finset.sum_image (fun a _ b _ hab => unaryReg_inj n hab)]
      exact Finset.sum_congr rfl (fun k _ => by rw [unaryState_entry])
    _ = ∑ x, ‖unaryState n (cascadeAmplitude θ n) x‖ ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      have hx' : ∀ k : Fin (n + 1), x ≠ unaryReg n k := by
        intro k hk
        apply hx
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩
      rw [unaryState_support n _ x hx']
      simp
    _ = 1 := h

end

end Qatlib.Papers.TruncTaylor14.PrepareSelectAmplitude
