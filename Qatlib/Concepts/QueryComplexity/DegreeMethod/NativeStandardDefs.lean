/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeQuantumMachineDefs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Log
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.SubspaceUnitary
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Bool
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped BigOperators ComplexConjugate Classical Matrix Kronecker

theorem target_head_bounds {Q A : Type*} {blank : A} (c : Config Q A blank) (m : Move) (q : Q) (a : A) :
    c.head - 1 ≤ (target c m q a).head ∧ (target c m q a).head ≤ c.head + 1 := by
  cases m <;> dsimp [target, Move.offset] <;> omega

theorem target_tape_other {Q A : Type*} {blank : A} (c : Config Q A blank) (m : Move) (q : Q) (a : A)
    (i : ℤ) (hi : i ≠ c.head) : (target c m q a).tape i = c.tape i := Tape.write_other _ _ _ _ hi

noncomputable def Rule.runBasis {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A) :
    ℕ → Config Q A R.blank → State Q A R.blank
  | 0, c => ket c
  | t + 1, c => ∑ s : Move × Q × A,
      R.amplitude c.state (c.tape c.head) s.1 s.2.1 s.2.2 • R.runBasis t (target c s.1 s.2.1 s.2.2)

theorem Rule.runBasis_eq_unitary_power {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (U : State Q A R.blank ≃ₗᵢ[ℂ] State Q A R.blank) (hU : ∀ c, U (ket c) = R.column c)
    (t : ℕ) (c : Config Q A R.blank) :
    (U.toLinearEquiv.toLinearMap ^ t) (ket c) = R.runBasis t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ]
    change (U.toLinearEquiv.toLinearMap ^ t) (U (ket c)) = _
    rw [hU, Rule.column, map_sum]
    simp only [map_smul, ih, Rule.runBasis]

theorem ket_apply {Q A : Type*} {blank : A} (c d : Config Q A blank) :
    ket c d = if c = d then 1 else 0 := by
  classical
  simp [ket, lp.single_apply, Pi.single_apply, eq_comm]

theorem Rule.runBasis_head_zero {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (t : ℕ) (c d : Config Q A R.blank)
    (hfar : d.head < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < d.head) : R.runBasis t c d = 0 := by
  induction t generalizing c with
  | zero =>
    have hc : c ≠ d := by intro h; subst d; omega
    simp only [Rule.runBasis, ket_apply, if_neg hc]
  | succ t ih =>
    simp only [Rule.runBasis, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul]
    apply Finset.sum_eq_zero
    intro s _
    have hb := target_head_bounds c s.1 s.2.1 s.2.2
    have hnext : d.head < (target c s.1 s.2.1 s.2.2).head - (t : ℤ) ∨
        (target c s.1 s.2.1 s.2.2).head + (t : ℤ) < d.head := by omega
    rw [ih _ hnext, mul_zero]

theorem Rule.runBasis_tape_zero {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (t : ℕ) (c d : Config Q A R.blank) (i : ℤ)
    (hfar : i < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < i) (hchange : d.tape i ≠ c.tape i) :
    R.runBasis t c d = 0 := by
  induction t generalizing c with
  | zero =>
    have hc : c ≠ d := by intro h; subst d; exact hchange rfl
    simp only [Rule.runBasis, ket_apply, if_neg hc]
  | succ t ih =>
    simp only [Rule.runBasis, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul]
    apply Finset.sum_eq_zero
    intro s _
    have hb := target_head_bounds c s.1 s.2.1 s.2.2
    have hi : i ≠ c.head := by omega
    have hnext : i < (target c s.1 s.2.1 s.2.2).head - (t : ℤ) ∨
        (target c s.1 s.2.1 s.2.2).head + (t : ℤ) < i := by omega
    have hneq : d.tape i ≠ (target c s.1 s.2.1 s.2.2).tape i := by
      rwa [target_tape_other c s.1 s.2.1 s.2.2 i hi]
    rw [ih _ hnext hneq, mul_zero]

theorem Rule.global_lightcone {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) :
    ∃ U : State Q A R.blank ≃ₗᵢ[ℂ] State Q A R.blank,
      (∀ c, U (ket c) = R.column c) ∧ ∀ (t : ℕ) (c d : Config Q A R.blank),
        (d.head < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < d.head →
          (U.toLinearEquiv.toLinearMap ^ t) (ket c) d = 0) ∧
        (∀ i, (i < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < i) → d.tape i ≠ c.tape i →
          (U.toLinearEquiv.toLinearMap ^ t) (ket c) d = 0) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, hU, ?_⟩
  intro t c d
  rw [R.runBasis_eq_unitary_power U hU]
  exact ⟨R.runBasis_head_zero t c d, fun i => R.runBasis_tape_zero t c d i⟩

theorem shiftRule_runBasis (Q A : Type*) [Fintype Q] [Fintype A] (blank : A) (move : Move)
    (t : ℕ) (c : Config Q A blank) :
    (shiftRule Q A blank move).runBasis t c = ket ((headTranslate ((t : ℤ) * move.offset)) c) := by
  classical
  induction t generalizing c with
  | zero =>
    change ket c = ket ((headTranslate (0 * move.offset)) c)
    congr 1
    apply Config.ext <;> simp [headTranslate]
  | succ t ih =>
    rw [Rule.runBasis, Finset.sum_eq_single (move, c.state, c.tape c.head)]
    · simp only [shiftRule, ite_true]
      change (1 : ℂ) • (shiftRule Q A blank move).runBasis t
          (target c move c.state (c.tape c.head)) = _
      rw [one_smul, ih]
      congr 1
      apply Config.ext
      · rfl
      · exact Tape.write_read c.tape c.head
      · dsimp [headTranslate, target]
        ring
    · intro b _ hb
      rcases b with ⟨d, q, a⟩
      change (if (d, q, a) = (move, c.state, c.tape c.head) then (1 : ℂ) else 0) •
        (shiftRule Q A blank move).runBasis t (target c d q a) = 0
      rw [if_neg hb]
      exact zero_smul ℂ _
    · intro h
      exact False.elim (h (Finset.mem_univ _))

theorem Rule.runBasis_norm {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (t : ℕ) (c : Config Q A R.blank) : ‖R.runBasis t c‖ = 1 := by
  obtain ⟨U, hU⟩ := h
  have hp (s : ℕ) (v : State Q A R.blank) : ‖(U.toLinearEquiv.toLinearMap ^ s) v‖ = ‖v‖ := by
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [pow_succ']
      change ‖U ((U.toLinearEquiv.toLinearMap ^ s) v)‖ = ‖v‖
      rw [U.norm_map, ih]
  rw [← R.runBasis_eq_unitary_power U hU, hp]
  exact (ket_orthonormal R.blank).norm_eq_one c

theorem Rule.runBasis_born_mass {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (t : ℕ) (c : Config Q A R.blank) :
    ∑' d : Config Q A R.blank, ‖R.runBasis t c d‖ ^ 2 = 1 := by
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (R.runBasis t c)
  have hs : ‖R.runBasis t c‖ ^ 2 = ∑' d : Config Q A R.blank, ‖R.runBasis t c d‖ ^ 2 := by
    simpa using! hn
  rw [← hs, R.runBasis_norm h, one_pow]

def windowPos (center : ℤ) (t : ℕ) (j : Fin (2*t+1)) : ℤ := center - (t : ℤ) + (j.val : ℤ)

def windowIndex (center : ℤ) (t : ℕ) (i : ℤ)
    (h : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ)) : Fin (2*t+1) :=
  ⟨(i-center+(t : ℤ)).toNat, by omega⟩

theorem windowPos_bounds (center : ℤ) (t : ℕ) (j : Fin (2*t+1)) :
    center - (t : ℤ) ≤ windowPos center t j ∧ windowPos center t j ≤ center + (t : ℤ) := by
  dsimp [windowPos]
  omega

theorem windowPos_index (center : ℤ) (t : ℕ) (i : ℤ)
    (h : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ)) :
    windowPos center t (windowIndex center t i h) = i := by
  dsimp [windowPos, windowIndex]
  omega

theorem windowIndex_pos (center : ℤ) (t : ℕ) (j : Fin (2*t+1)) :
    windowIndex center t (windowPos center t j) (windowPos_bounds center t j) = j := by
  apply Fin.ext
  dsimp [windowPos, windowIndex]
  omega

theorem windowPos_injective (center : ℤ) (t : ℕ) : Function.Injective (windowPos center t) := by
  intro i j h
  apply Fin.ext
  dsimp [windowPos] at h
  omega

def Tape.patchWindow {A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ)
    (a : Fin (2*t+1) → A) : Tape A blank where
  cell i := if h : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ) then a (windowIndex center t i h) else T i
  finite_nonblank := (T.finite_nonblank.union (Set.finite_Icc (center-(t : ℤ)) (center+(t : ℤ)))).subset (by
    intro i hi
    by_cases h : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ)
    · exact Or.inr h
    · apply Or.inl
      change (if h : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ) then a (windowIndex center t i h) else T i) ≠ blank at hi
      simpa only [dif_neg h] using! hi)

theorem Tape.patchWindow_at {A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ)
    (a : Fin (2*t+1) → A) (j : Fin (2*t+1)) :
    T.patchWindow center t a (windowPos center t j) = a j := by
  change (if h : center - (t : ℤ) ≤ windowPos center t j ∧ windowPos center t j ≤ center + (t : ℤ)
    then a (windowIndex center t (windowPos center t j) h) else T (windowPos center t j)) = _
  rw [dif_pos (windowPos_bounds center t j), windowIndex_pos]

theorem Tape.patchWindow_outside {A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ)
    (a : Fin (2*t+1) → A) (i : ℤ)
    (h : i < center - (t : ℤ) ∨ center + (t : ℤ) < i) : T.patchWindow center t a i = T i := by
  change (if h : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ) then a (windowIndex center t i h) else T i) = _
  rw [dif_neg (by omega)]

abbrev WindowConfig (Q A : Type*) (t : ℕ) := Q × Fin (2*t+1) × (Fin (2*t+1) → A)

def encodeWindow {Q A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ)
    (w : WindowConfig Q A t) : Config Q A blank :=
  ⟨w.1, T.patchWindow center t w.2.2, windowPos center t w.2.1⟩

theorem encodeWindow_injective {Q A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ) :
    Function.Injective (encodeWindow (Q := Q) T center t) := by
  intro a b h
  have hs := congrArg Config.state h
  have hh := windowPos_injective center t (congrArg Config.head h)
  have ht : a.2.2 = b.2.2 := by
    funext j
    have hj := congrArg (fun c : Config Q A blank => c.tape (windowPos center t j)) h
    exact (Tape.patchWindow_at T center t a.2.2 j).symm.trans
        (hj.trans (Tape.patchWindow_at T center t b.2.2 j))
  exact Prod.ext hs (Prod.ext hh ht)

theorem WindowConfig.card (Q A : Type*) [Fintype Q] [Fintype A] (t : ℕ) :
    Fintype.card (WindowConfig Q A t) = Fintype.card Q * (2*t+1) * Fintype.card A ^ (2*t+1) := by
  simp [WindowConfig, mul_assoc]

def decodeWindow {Q A : Type*} {blank : A} (center : ℤ) (t : ℕ)
    (c : Config Q A blank) : Option (WindowConfig Q A t) :=
  if h : center - (t : ℤ) ≤ c.head ∧ c.head ≤ center + (t : ℤ) then
    some (c.state, windowIndex center t c.head h, fun j => c.tape (windowPos center t j)) else none

theorem decodeWindow_encode {Q A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ)
    (w : WindowConfig Q A t) : decodeWindow center t (encodeWindow T center t w) = some w := by
  unfold decodeWindow
  dsimp only [encodeWindow]
  rw [dif_pos (windowPos_bounds center t w.2.1), windowIndex_pos]
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext j
      exact Tape.patchWindow_at T center t w.2.2 j

theorem encodeWindow_of_compatible {Q A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (t : ℕ)
    (c : Config Q A blank) (hh : center - (t : ℤ) ≤ c.head ∧ c.head ≤ center + (t : ℤ))
    (ht : ∀ i, (i < center - (t : ℤ) ∨ center + (t : ℤ) < i) → c.tape i = T i) :
    encodeWindow T center t (c.state, windowIndex center t c.head hh, fun j => c.tape (windowPos center t j)) = c := by
  apply Config.ext
  · rfl
  · apply Tape.ext
    intro i
    by_cases hi : center - (t : ℤ) ≤ i ∧ i ≤ center + (t : ℤ)
    · change T.patchWindow center t (fun j => c.tape (windowPos center t j)) i = c.tape i
      have he :=
          Tape.patchWindow_at T center t (fun j => c.tape (windowPos center t j))
          (windowIndex center t i hi)
      simpa only [windowPos_index] using! he
    · change T.patchWindow center t (fun j => c.tape (windowPos center t j)) i = c.tape i
      have ho : i < center - (t : ℤ) ∨ center + (t : ℤ) < i := by omega
      rw [Tape.patchWindow_outside _ _ _ _ _ ho, ht i ho]
  · exact windowPos_index center t c.head hh

theorem Rule.runBasis_window_witness {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (t : ℕ) (c d : Config Q A R.blank) (hn : R.runBasis t c d ≠ 0) :
    ∃! w : WindowConfig Q A t, encodeWindow c.tape c.head t w = d := by
  have hh : c.head - (t : ℤ) ≤ d.head ∧ d.head ≤ c.head + (t : ℤ) := by
    by_contra h
    have hf : d.head < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < d.head := by omega
    exact hn (R.runBasis_head_zero t c d hf)
  have ht : ∀ i, (i < c.head - (t : ℤ) ∨ c.head + (t : ℤ) < i) → d.tape i = c.tape i := by
    intro i hf
    by_contra he
    exact hn (R.runBasis_tape_zero t c d i hf he)
  let w : WindowConfig Q A t :=
      (d.state, windowIndex c.head t d.head hh, fun j => d.tape (windowPos c.head t j))
  have hw : encodeWindow c.tape c.head t w = d := encodeWindow_of_compatible c.tape c.head t d hh ht
  refine ⟨w, hw, ?_⟩
  intro v hv
  exact encodeWindow_injective c.tape c.head t (hv.trans hw.symm)

theorem Rule.runBasis_eq_window_sum {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (t : ℕ) (c : Config Q A R.blank) :
    R.runBasis t c = ∑ w : WindowConfig Q A t,
      R.runBasis t c (encodeWindow c.tape c.head t w) • ket (encodeWindow c.tape c.head t w) := by
  ext d
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ket_apply]
  by_cases he : ∃ w : WindowConfig Q A t, encodeWindow c.tape c.head t w = d
  · obtain ⟨w, rfl⟩ := he
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      rw [if_neg (fun hh => hv (encodeWindow_injective c.tape c.head t hh)), mul_zero]
    · intro hh
      exact False.elim (hh (Finset.mem_univ _))
  · have hz : R.runBasis t c d = 0 := by
      by_contra hn
      obtain ⟨w, hw, _⟩ := R.runBasis_window_witness t c d hn
      exact he ⟨w, hw⟩
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg (fun hh => he ⟨w, hh⟩), mul_zero]

theorem Rule.window_born_mass {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (t : ℕ) (c : Config Q A R.blank) :
    ∑ w : WindowConfig Q A t, ‖R.runBasis t c (encodeWindow c.tape c.head t w)‖ ^ 2 = 1 := by
  have hv : Orthonormal ℂ (fun w : WindowConfig Q A t => ket (encodeWindow c.tape c.head t w)) :=
    (ket_orthonormal (Q := Q) R.blank).comp _ (encodeWindow_injective c.tape c.head t)
  have he := hv.inner_sum (fun w => R.runBasis t c (encodeWindow c.tape c.head t w))
    (fun w => R.runBasis t c (encodeWindow c.tape c.head t w)) Finset.univ
  rw [← R.runBasis_eq_window_sum t c] at he
  have hz (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    simpa only [RCLike.inner_apply, mul_comm] using! (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  change inner ℂ (R.runBasis t c) (R.runBasis t c) =
    ∑ w : WindowConfig Q A t, star (R.runBasis t c (encodeWindow c.tape c.head t w)) *
      R.runBasis t c (encodeWindow c.tape c.head t w) at he
  calc
    _ = (∑ w : WindowConfig Q A t, star (R.runBasis t c (encodeWindow c.tape c.head t w)) *
        R.runBasis t c (encodeWindow c.tape c.head t w)).re := by simp only [Complex.re_sum, hz]
    _ = (inner ℂ (R.runBasis t c) (R.runBasis t c)).re := congrArg Complex.re he.symm
    _ = ‖R.runBasis t c‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    _ = 1 := by rw [R.runBasis_norm h, one_pow]

def WindowConfig.step? {Q A : Type*} {B : ℕ} (w : WindowConfig Q A B) (m : Move) (q : Q) (a : A) :
    Option (WindowConfig Q A B) :=
  if h : 0 ≤ (w.2.1.val : ℤ) + m.offset ∧ (w.2.1.val : ℤ) + m.offset < ((2*B+1 : ℕ) : ℤ) then
    some (q, ⟨((w.2.1.val : ℤ) + m.offset).toNat, by omega⟩, Function.update w.2.2 w.2.1 a) else none

theorem WindowConfig.step?_spec {Q A : Type*} {B : ℕ} (w v : WindowConfig Q A B) (m : Move) (q : Q) (a : A)
    (h : w.step? m q a = some v) :
    v.1 = q ∧ v.2.2 = Function.update w.2.2 w.2.1 a ∧ (v.2.1.val : ℤ) = (w.2.1.val : ℤ) + m.offset := by
  unfold WindowConfig.step? at h
  split_ifs at h with hb
  · cases Option.some.inj h
    refine ⟨rfl, rfl, ?_⟩
    dsimp
    omega

theorem WindowConfig.step?_exists {Q A : Type*} {B : ℕ} (w : WindowConfig Q A B) (m : Move) (q : Q) (a : A)
    (hb : 0 ≤ (w.2.1.val : ℤ) + m.offset ∧ (w.2.1.val : ℤ) + m.offset < ((2*B+1 : ℕ) : ℤ)) :
    ∃ v, w.step? m q a = some v := by
  unfold WindowConfig.step?
  rw [dif_pos hb]
  exact ⟨_, rfl⟩

theorem Tape.patchWindow_update {A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (B : ℕ)
    (cells : Fin (2*B+1) → A) (j : Fin (2*B+1)) (a : A) :
    (T.patchWindow center B cells).write (windowPos center B j) a =
      T.patchWindow center B (Function.update cells j a) := by
  apply Tape.ext
  intro i
  by_cases hi : i = windowPos center B j
  · subst i
    rw [Tape.write_same, Tape.patchWindow_at, Function.update_self]
  · rw [Tape.write_other _ _ _ _ hi]
    by_cases hb : center - (B : ℤ) ≤ i ∧ i ≤ center + (B : ℤ)
    · let k := windowIndex center B i hb
      have hk : windowPos center B k = i := windowPos_index center B i hb
      have hj : k ≠ j := by
        intro he
        exact hi (hk.symm.trans (congrArg (windowPos center B) he))
      rw [← hk, Tape.patchWindow_at, Tape.patchWindow_at, Function.update_of_ne hj]
    · have hf : i < center - (B : ℤ) ∨ center + (B : ℤ) < i := by omega
      rw [Tape.patchWindow_outside _ _ _ _ _ hf, Tape.patchWindow_outside _ _ _ _ _ hf]

theorem encodeWindow_step {Q A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (B : ℕ)
    (w v : WindowConfig Q A B) (m : Move) (q : Q) (a : A) (h : w.step? m q a = some v) :
    encodeWindow T center B v = target (encodeWindow T center B w) m q a := by
  obtain ⟨hs, ht, hh⟩ := WindowConfig.step?_spec w v m q a h
  apply Config.ext
  · exact hs
  · change T.patchWindow center B v.2.2 = (T.patchWindow center B w.2.2).write (windowPos center B w.2.1) a
    rw [ht, Tape.patchWindow_update]
  · dsimp [encodeWindow, target, windowPos]
    omega

def WindowConfig.Room {Q A : Type*} {B : ℕ} (w : WindowConfig Q A B) (s : ℕ) : Prop :=
  s ≤ w.2.1.val ∧ w.2.1.val + s < 2*B+1

theorem Move.offset_bounds (m : Move) : -1 ≤ m.offset ∧ m.offset ≤ 1 := by
  cases m <;> simp [Move.offset]

theorem WindowConfig.step?_room {Q A : Type*} {B : ℕ} (w : WindowConfig Q A B) (s : ℕ)
    (hr : w.Room (s+1)) (m : Move) (q : Q) (a : A) :
    ∃ v, w.step? m q a = some v ∧ v.Room s := by
  have hm := Move.offset_bounds m
  have hb : 0 ≤ (w.2.1.val : ℤ) + m.offset ∧ (w.2.1.val : ℤ) + m.offset < ((2*B+1 : ℕ) : ℤ) := by
    dsimp [WindowConfig.Room] at hr
    omega
  obtain ⟨v, hv⟩ := WindowConfig.step?_exists w m q a hb
  refine ⟨v, hv, ?_⟩
  have hh := (WindowConfig.step?_spec w v m q a hv).2.2
  dsimp [WindowConfig.Room] at hr ⊢
  omega

theorem encodeWindow_read {Q A : Type*} {blank : A} (T : Tape A blank) (center : ℤ) (B : ℕ)
    (w : WindowConfig Q A B) :
    (encodeWindow T center B w).tape (encodeWindow T center B w).head = w.2.2 w.2.1 :=
  Tape.patchWindow_at T center B w.2.2 w.2.1

noncomputable def windowEmbed {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) :
    (WindowConfig Q A B → ℂ) →ₗ[ℂ] State Q A blank where
  toFun f := ∑ w : WindowConfig Q A B, f w • ket (encodeWindow T center B w)
  map_add' f g := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a f := by simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem windowEmbed_apply {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) (f : WindowConfig Q A B → ℂ) :
    windowEmbed T center B f = ∑ w : WindowConfig Q A B, f w • ket (encodeWindow T center B w) := rfl

theorem windowEmbed_eval {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) (f : WindowConfig Q A B → ℂ) (w : WindowConfig Q A B) :
    windowEmbed T center B f (encodeWindow T center B w) = f w := by
  rw [windowEmbed_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ket_apply]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    rw [if_neg (fun he => hv (encodeWindow_injective T center B he)), mul_zero]
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

theorem windowEmbed_single {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) (w : WindowConfig Q A B) (a : ℂ) :
    windowEmbed T center B (Pi.single w a) = a • ket (encodeWindow T center B w) := by
  rw [windowEmbed_apply, Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    rw [Pi.single_eq_of_ne hv]
    exact zero_smul ℂ _
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

noncomputable def Rule.windowRun {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A) (B : ℕ) :
    ℕ → WindowConfig Q A B → (WindowConfig Q A B → ℂ)
  | 0, w => Pi.single w 1
  | s+1, w => ∑ i : Move × Q × A, R.amplitude w.1 (w.2.2 w.2.1) i.1 i.2.1 i.2.2 •
      match w.step? i.1 i.2.1 i.2.2 with
      | none => 0
      | some v => R.windowRun B s v

theorem Rule.windowRun_embed {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (T : Tape A R.blank) (center : ℤ) (B s : ℕ) (w : WindowConfig Q A B) (hr : w.Room s) :
    windowEmbed T center B (R.windowRun B s w) = R.runBasis s (encodeWindow T center B w) := by
  induction s generalizing w with
  | zero =>
    rw [Rule.windowRun, windowEmbed_single, one_smul, Rule.runBasis]
  | succ s ih =>
    rw [Rule.windowRun, map_sum, Rule.runBasis]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨v, hv, hroom⟩ := WindowConfig.step?_room w s hr i.1 i.2.1 i.2.2
    rw [map_smul, hv, ih v hroom, encodeWindow_step T center B w v i.1 i.2.1 i.2.2 hv]
    rw [encodeWindow_read]
    rfl

theorem Rule.windowRun_eq {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (T : Tape A R.blank) (center : ℤ) (B s : ℕ) (w v : WindowConfig Q A B) (hr : w.Room s) :
    R.windowRun B s w v = R.runBasis s (encodeWindow T center B w) (encodeWindow T center B v) := by
  rw [← windowEmbed_eval T center B (R.windowRun B s w) v, R.windowRun_embed T center B s w hr]

theorem windowEmbed_inner {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) (f g : WindowConfig Q A B → ℂ) :
    inner ℂ (windowEmbed T center B f) (windowEmbed T center B g) = ∑ w : WindowConfig Q A B, star (f w) * g w := by
  have hv : Orthonormal ℂ (fun w : WindowConfig Q A B => ket (encodeWindow T center B w)) :=
    (ket_orthonormal (Q := Q) blank).comp _ (encodeWindow_injective T center B)
  rw [windowEmbed_apply, windowEmbed_apply]
  exact hv.inner_sum f g Finset.univ

theorem windowEmbed_norm_sq {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) (f : WindowConfig Q A B → ℂ) :
    ‖windowEmbed T center B f‖ ^ 2 = ∑ w : WindowConfig Q A B, ‖f w‖ ^ 2 := by
  have hz (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    simpa only [RCLike.inner_apply, mul_comm] using! (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  calc
    _ = (inner ℂ (windowEmbed T center B f) (windowEmbed T center B f)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := by rw [windowEmbed_inner, Complex.re_sum]; simp only [hz]

theorem Rule.windowRun_mass {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (T : Tape A R.blank) (center : ℤ) (B s : ℕ)
    (w : WindowConfig Q A B) (hr : w.Room s) : ∑ v : WindowConfig Q A B, ‖R.windowRun B s w v‖ ^ 2 = 1 := by
  rw [← windowEmbed_norm_sq T center B, R.windowRun_embed T center B s w hr, R.runBasis_norm h,
      one_pow]

def initialWindow {Q A : Type*} {blank : A} (B : ℕ) (c : Config Q A blank) : WindowConfig Q A B :=
  (c.state, windowIndex c.head B c.head (by omega), fun j => c.tape (windowPos c.head B j))

theorem initialWindow_head {Q A : Type*} {blank : A} (B : ℕ) (c : Config Q A blank) :
    (initialWindow B c).2.1.val = B := by
  dsimp [initialWindow, windowIndex]
  omega

theorem initialWindow_room {Q A : Type*} {blank : A} (B s : ℕ) (c : Config Q A blank) (hs : s ≤ B) :
    (initialWindow B c).Room s := by
  dsimp [WindowConfig.Room]
  rw [initialWindow_head]
  omega

theorem encodeWindow_initial {Q A : Type*} {blank : A} (B : ℕ) (c : Config Q A blank) :
    encodeWindow c.tape c.head B (initialWindow B c) = c :=
  encodeWindow_of_compatible c.tape c.head B c (by omega) (fun _ _ => rfl)

theorem Rule.windowRun_initial {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (B s : ℕ) (hs : s ≤ B) (c : Config Q A R.blank) :
    windowEmbed c.tape c.head B (R.windowRun B s (initialWindow B c)) = R.runBasis s c := by
  rw [R.windowRun_embed c.tape c.head B s _ (initialWindow_room B s c hs), encodeWindow_initial]

theorem Rule.windowRun_initial_mass {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (B s : ℕ) (hs : s ≤ B) (c : Config Q A R.blank) :
    ∑ v : WindowConfig Q A B, ‖R.windowRun B s (initialWindow B c) v‖ ^ 2 = 1 :=
  R.windowRun_mass h c.tape c.head B s _ (initialWindow_room B s c hs)

theorem windowEmbed_outside {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}
    (T : Tape A blank) (center : ℤ) (B : ℕ) (f : WindowConfig Q A B → ℂ) (d : Config Q A blank)
    (hd : ¬ ∃ w : WindowConfig Q A B, encodeWindow T center B w = d) : windowEmbed T center B f d = 0 := by
  rw [windowEmbed_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ket_apply]
  apply Finset.sum_eq_zero
  intro w _
  rw [if_neg (fun he => hd ⟨w, he⟩), mul_zero]

theorem Rule.windowRun_born_value {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (T : Tape A R.blank) (center : ℤ) (B s : ℕ) (w : WindowConfig Q A B) (hr : w.Room s)
    (P : Config Q A R.blank → ℝ) :
    (∑' d : Config Q A R.blank, ‖R.runBasis s (encodeWindow T center B w) d‖ ^ 2 * P d) =
      ∑ v : WindowConfig Q A B, ‖R.windowRun B s w v‖ ^ 2 * P (encodeWindow T center B v) := by
  let e : WindowConfig Q A B ↪ Config Q A R.blank :=
      ⟨encodeWindow T center B, encodeWindow_injective T center B⟩
  have hz (d : Config Q A R.blank) (hd : d ∉ Finset.univ.map e) :
      R.runBasis s (encodeWindow T center B w) d = 0 := by
    have hn : ¬ ∃ v : WindowConfig Q A B, encodeWindow T center B v = d := by
      rintro ⟨v, hv⟩
      exact hd (Finset.mem_map.mpr ⟨v, Finset.mem_univ _, hv⟩)
    rw [← R.windowRun_embed T center B s w hr]
    exact windowEmbed_outside T center B _ d hn
  calc
    _ = ∑ d ∈ Finset.univ.map e, ‖R.runBasis s (encodeWindow T center B w) d‖ ^ 2 * P d := by
      apply tsum_eq_sum
      intro d hd
      rw [hz d hd, norm_zero, zero_pow (by decide), zero_mul]
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro v _
      change ‖R.runBasis s (encodeWindow T center B w) (encodeWindow T center B v)‖ ^ 2 *
        P (encodeWindow T center B v) = _
      rw [← R.windowRun_eq T center B s w v hr]

theorem Rule.windowRun_initial_value {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (B s : ℕ) (hs : s ≤ B) (c : Config Q A R.blank) (P : Config Q A R.blank → ℝ) :
    (∑' d : Config Q A R.blank, ‖R.runBasis s c d‖ ^ 2 * P d) =
      ∑ v : WindowConfig Q A B, ‖R.windowRun B s (initialWindow B c) v‖ ^ 2 * P (encodeWindow c.tape c.head B v) := by
  simpa only [encodeWindow_initial] using! R.windowRun_born_value c.tape c.head B s (initialWindow B c)
    (initialWindow_room B s c hs) P

theorem fivePhase_runBasis {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (t : ℕ)
    (c : Config Q A R.blank) :
    (fivePhaseRule R b).runBasis (5*t) ⟨(0,c.state),c.tape,c.head⟩ = phaseEmbed (0 : Fin 5) (R.runBasis t c) := by
  obtain ⟨U,hU⟩ := h
  have hC := clockUnitary_columns R.blank (finRotate 5) (fivePhaseAmp R b) (fivePhaseUnitary R.blank b U)
    (fivePhaseUnitary_columns R U hU b)
  rw [← (fivePhaseRule R b).runBasis_eq_unitary_power _ hC]
  rw [← phaseEmbed_ket]
  exact (fivePhase_cycles R.blank b U t (ket c)).trans
    (congrArg (phaseEmbed (0 : Fin 5)) (R.runBasis_eq_unitary_power U hU t c))

theorem fivePhase_runBasis_apply {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) (b : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (t : ℕ)
    (c d : Config Q A R.blank) (p : Fin 5) :
    (fivePhaseRule R b).runBasis (5*t) ⟨(0,c.state),c.tape,c.head⟩ ⟨(p,d.state),d.tape,d.head⟩ =
      if p = 0 then R.runBasis t c d else 0 := by
  rw [fivePhase_runBasis R h b, phaseEmbed_apply]
  by_cases hp : p = 0 <;> simp [hp]

abbrev CellRest (A : Type*) {B : ℕ} (i : Fin (2*B+1)) := {j : Fin (2*B+1) // j ≠ i} → A

abbrev CellView (Q A : Type*) := (Q × A) ⊕ (Move × Q × A)

def cellAssemble {A : Type*} {B : ℕ} (i : Fin (2*B+1)) (a : A) (r : CellRest A i) : Fin (2*B+1) → A :=
  (Equiv.funSplitAt i A).symm (a,r)

@[simp] theorem cellAssemble_same {A : Type*} {B : ℕ} (i : Fin (2*B+1)) (a : A) (r : CellRest A i) :
    cellAssemble i a r i = a := by simp [cellAssemble, Equiv.funSplitAt, Equiv.piSplitAt]

theorem cellAssemble_other {A : Type*} {B : ℕ} (i j : Fin (2*B+1)) (a : A) (r : CellRest A i) (h : j ≠ i) :
    cellAssemble i a r j = r ⟨j,h⟩ := by simp [cellAssemble, Equiv.funSplitAt, Equiv.piSplitAt, h]

theorem cellAssemble_update {A : Type*} {B : ℕ} (i : Fin (2*B+1)) (a b : A) (r : CellRest A i) :
    Function.update (cellAssemble i a r) i b = cellAssemble i b r := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [cellAssemble_other, h]

theorem cellAssemble_injective {A : Type*} {B : ℕ} (i : Fin (2*B+1)) :
    Function.Injective (fun ar : A × CellRest A i => cellAssemble i ar.1 ar.2) :=
  (Equiv.funSplitAt i A).symm.injective

def windowNeighbor {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) (m : Move) : Fin (2*B+1) :=
  ⟨((i.val : ℤ)+m.offset).toNat, by have hm := Move.offset_bounds m; omega⟩

theorem windowNeighbor_val {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) (m : Move) :
    ((windowNeighbor i hi m).val : ℤ) = (i.val : ℤ)+m.offset := by
  have hm := Move.offset_bounds m
  dsimp [windowNeighbor]
  omega

theorem windowNeighbor_injective {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    Function.Injective (windowNeighbor i hi) := by
  intro m n h
  have he := congrArg (fun j : Fin (2*B+1) => (j.val : ℤ)) h
  change ((windowNeighbor i hi m).val : ℤ) = (windowNeighbor i hi n).val at he
  rw [windowNeighbor_val, windowNeighbor_val] at he
  cases m <;> cases n <;> simp_all [Move.offset]

def cellPlace {Q A : Type*} {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (vr : CellView Q A × CellRest A i) : Bool × WindowConfig Q A B :=
  match vr.1 with
  | .inl qa => (false,qa.1,i,cellAssemble i qa.2 vr.2)
  | .inr mqa => (true,mqa.2.1,windowNeighbor i hi mqa.1,cellAssemble i mqa.2.2 vr.2)

theorem cellPlace_injective {Q A : Type*} {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    Function.Injective (cellPlace (Q := Q) (A := A) i hi) := by
  rintro ⟨v,r⟩ ⟨v',r'⟩ h
  cases v with
  | inl qa =>
    cases v' with
    | inl qb =>
      have hq := congrArg (fun z : Bool × WindowConfig Q A B => z.2.1) h
      have ha : (qa.2,r) = (qb.2,r') := by
        apply cellAssemble_injective i
        exact congrArg (fun z : Bool × WindowConfig Q A B => z.2.2.2) h
      exact Prod.ext
          (congrArg Sum.inl (Prod.ext hq (congrArg (fun ar : A × CellRest A i => ar.1) ha)))
          (congrArg (fun ar : A × CellRest A i => ar.2) ha)
    | inr mb => exact False.elim (Bool.false_ne_true (congrArg Prod.fst h))
  | inr ma =>
    cases v' with
    | inl qb => exact False.elim (Bool.false_ne_true (congrArg Prod.fst h).symm)
    | inr mb =>
      have hm :=
          windowNeighbor_injective i hi (congrArg (fun z : Bool × WindowConfig Q A B => z.2.2.1) h)
      have hq := congrArg (fun z : Bool × WindowConfig Q A B => z.2.1) h
      have ha : (ma.2.2,r) = (mb.2.2,r') := by
        apply cellAssemble_injective i
        exact congrArg (fun z : Bool × WindowConfig Q A B => z.2.2.2) h
      exact Prod.ext
          (congrArg Sum.inr (Prod.ext hm (Prod.ext hq (congrArg (fun ar : A × CellRest A i => ar.1) ha)))) (congrArg (fun ar : A × CellRest A i => ar.2) ha)

noncomputable def injectionFrame {ι κ : Type*} [DecidableEq κ] (f : ι → κ) : Matrix κ ι ℂ :=
  fun x i => if x = f i then 1 else 0

theorem injectionFrame_isometry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (injectionFrame f) := by
  ext i j
  change (∑ x : κ, star (if x = f i then (1 : ℂ) else 0) * (if x = f j then 1 else 0)) = _
  have hs (x : κ) : star (if x = f i then (1 : ℂ) else 0) = (if x = f i then 1 else 0) := by
    split_ifs <;> simp
  simp only [hs, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, Matrix.one_apply, hf.eq_iff]

noncomputable def cellLocalFrame {Q A : Type*} [DecidableEq Q] [DecidableEq A] {B : ℕ}
    (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    Matrix (Bool × WindowConfig Q A B) (CellView Q A × CellRest A i) ℂ :=
  injectionFrame (cellPlace i hi)

theorem cellLocalFrame_isometry {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (cellLocalFrame (Q := Q) (A := A) i hi) :=
  injectionFrame_isometry _ (cellPlace_injective i hi)

noncomputable def Rule.cellLocalGate {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (cellLocalFrame i hi) (R.cellSwap ⊗ₖ (1 : Matrix (CellRest A i) (CellRest A i) ℂ))

theorem Rule.cellLocalGate_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    R.cellLocalGate i hi ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  apply Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_unitary _
      (cellLocalFrame_isometry i hi)
  exact Matrix.kronecker_mem_unitary (R.cellSwap_unitary h) (one_mem _)

theorem Rule.cellLocalGate_frame {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) :
    R.cellLocalGate i hi * cellLocalFrame i hi =
      cellLocalFrame i hi * (R.cellSwap ⊗ₖ (1 : Matrix (CellRest A i) (CellRest A i) ℂ)) :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_frame _ (cellLocalFrame_isometry i hi) _

theorem cellPlace_step {Q A : Type*} {B : ℕ}
    (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (q : Q) (a : A) (r : CellRest A i) (m : Move) (q' : Q) (b : A) :
    WindowConfig.step? ((q,i,cellAssemble i a r) : WindowConfig Q A B) m q' b =
      some (cellPlace i hi (.inr (m,q',b),r)).2 := by
  have hm := Move.offset_bounds m
  have hb : 0 ≤ (i.val : ℤ)+m.offset ∧ (i.val : ℤ)+m.offset < ((2*B+1 : ℕ) : ℤ) := by omega
  unfold WindowConfig.step?
  rw [dif_pos hb, cellAssemble_update]
  rfl

theorem Rule.cellLocalGate_column {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (vr : CellView Q A × CellRest A i) (x : Bool × WindowConfig Q A B) :
    R.cellLocalGate i hi x (cellPlace i hi vr) =
      ∑ v : CellView Q A, R.cellSwap v vr.1 * (if x = cellPlace i hi (v,vr.2) then 1 else 0) := by
  have he := congrArg (fun M : Matrix (Bool × WindowConfig Q A B) (CellView Q A × CellRest A i) ℂ => M x vr)
    (R.cellLocalGate_frame i hi)
  change (∑ y : Bool × WindowConfig Q A B, R.cellLocalGate i hi x y * (if y = cellPlace i hi vr then 1 else 0)) =
    ∑ z : CellView Q A × CellRest A i,
      (if x = cellPlace i hi z then 1 else 0) *
        (R.cellSwap z.1 vr.1 * (if z.2 = vr.2 then 1 else 0)) at he
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  rw [Fintype.sum_prod_type] at he
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

theorem Rule.cellLocalGate_old_column {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (q : Q) (a : A) (r : CellRest A i) (x : Bool × WindowConfig Q A B) :
    R.cellLocalGate i hi x (false,q,i,cellAssemble i a r) =
      ∑ out : Move × Q × A, R.amplitude q a out.1 out.2.1 out.2.2 *
        (if x = cellPlace i hi (.inr out,r) then 1 else 0) := by
  rw [← show cellPlace i hi (.inl (q,a),r) = (false,q,i,cellAssemble i a r) from rfl,
    R.cellLocalGate_column]
  rw [Fintype.sum_sum_type]
  simp only [Rule.cellSwap, isometrySwap, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.fromBlocks_apply₂₁, Rule.cellIsometry]

theorem Rule.cellLocalGate_actual_step {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (q : Q) (a : A) (r : CellRest A i) (x : Bool × WindowConfig Q A B) :
    R.cellLocalGate i hi x (false,q,i,cellAssemble i a r) =
      if x.1 then R.windowRun B 1 (q,i,cellAssemble i a r) x.2 else 0 := by
  rw [R.cellLocalGate_old_column]
  rw [Rule.windowRun]
  simp only [cellAssemble_same, Rule.windowRun]
  rcases x with ⟨mode,w⟩
  cases mode with
  | false =>
    simp [cellPlace]
  | true =>
    simp only [ite_true, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro out _
    congr 1
    rw [cellPlace_step i hi q a r out.1 out.2.1 out.2.2]
    simp [cellPlace, Pi.single_apply]

theorem injectionFrame_adjoint_outside {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (y : κ) (hy : ∀ j, y ≠ f j) :
    (injectionFrame f).conjTranspose *ᵥ Pi.single y 1 = 0 := by
  ext j
  simp [Matrix.conjTranspose_apply, injectionFrame, hy j]

theorem frameUnitary_outside {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (T : Matrix ι ι ℂ) (y : κ) (hy : ∀ j, y ≠ f j) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame f) T *ᵥ Pi.single y 1 = Pi.single y 1 := by
  have he := injectionFrame_adjoint_outside f y hy
  simp only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, he,
    Matrix.mulVec_zero, sub_zero, add_zero]

theorem Rule.cellLocalGate_other_old {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (w : WindowConfig Q A B) (hw : w.2.1 ≠ i) :
    R.cellLocalGate i hi *ᵥ Pi.single (false,w) 1 = Pi.single (false,w) 1 := by
  apply frameUnitary_outside
  rintro ⟨v,r⟩ h
  cases v with
  | inl qa => exact hw (congrArg (fun z : Bool × WindowConfig Q A B => z.2.2.1) h)
  | inr ma => exact Bool.false_ne_true (congrArg Prod.fst h)

theorem Rule.cellLocalGate_actual_step_all {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (w : WindowConfig Q A B) (hw : w.2.1 = i) (x : Bool × WindowConfig Q A B) :
    R.cellLocalGate i hi x (false,w) = if x.1 then R.windowRun B 1 w x.2 else 0 := by
  let r : CellRest A i := fun j => w.2.2 j
  have ht : cellAssemble i (w.2.2 i) r = w.2.2 := (Equiv.funSplitAt i A).symm_apply_apply w.2.2
  have he : (w.1,i,cellAssemble i (w.2.2 i) r) = w := by rw [ht, ← hw]
  rw [← he]
  exact R.cellLocalGate_actual_step i hi w.1 (w.2.2 i) r x

theorem frameUnitary_fixed {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (E : Matrix κ ι ℂ) (T : Matrix ι ι ℂ) (x : κ → ℂ)
    (hx : T *ᵥ (E.conjTranspose *ᵥ x) = E.conjTranspose *ᵥ x) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary E T *ᵥ x = x := by
  simp only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx,
    sub_add_cancel]

theorem kronecker_one_mulVec_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (f : ι × κ → ℂ) (i : ι) (k : κ) :
    ((M ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ f) (i,k) = (M *ᵥ (fun j => f (j,k))) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite]

theorem injectionFrame_adjoint_apply {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (x : κ → ℂ) (j : ι) : ((injectionFrame f).conjTranspose *ᵥ x) j = x (f j) := by
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, injectionFrame, ite_mul]

def windowMode {Q A : Type*} {B : ℕ} (p : Bool) :
    (WindowConfig Q A B → ℂ) →ₗ[ℂ] (Bool × WindowConfig Q A B → ℂ) where
  toFun f x := if x.1 = p then f x.2 else 0
  map_add' f g := by ext x; split_ifs with h <;> simp [h]
  map_smul' a f := by ext x; split_ifs with h <;> simp [h]

theorem windowMode_single {Q A : Type*} [DecidableEq Q] [DecidableEq A] {B : ℕ}
    (p : Bool) (w : WindowConfig Q A B) :
    windowMode p (Pi.single w 1) = Pi.single (p,w) 1 := by
  ext x
  simp [windowMode, Pi.single_apply, Prod.ext_iff, ite_and]

theorem Rule.cellLocalGate_fixed_new {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (y : WindowConfig Q A B → ℂ)
    (hy : ∀ (q : Q) (a : A) (r : CellRest A i),
      ∑ out : Move × Q × A, star (R.amplitude q a out.1 out.2.1 out.2.2) *
        y (cellPlace i hi (.inr out,r)).2 = 0) :
    R.cellLocalGate i hi *ᵥ windowMode true y = windowMode true y := by
  apply frameUnitary_fixed
  ext vr
  rcases vr with ⟨v,r⟩
  rw [kronecker_one_mulVec_apply]
  have hs : (fun v : CellView Q A => ((cellLocalFrame i hi).conjTranspose *ᵥ windowMode true y) (v,r)) =
      Sum.elim (0 : Q × A → ℂ) (fun out : Move × Q × A => y (cellPlace i hi (.inr out,r)).2) := by
    funext v
    rw [cellLocalFrame, injectionFrame_adjoint_apply]
    cases v <;> simp [windowMode, cellPlace]
  have hk : R.cellIsometry.conjTranspose *ᵥ
      (fun out : Move × Q × A => y (cellPlace i hi (.inr out,r)).2) = 0 := by
    ext qa
    exact hy qa.1 qa.2 r
  have hfix := isometrySwap_fixed R.cellIsometry _ hk
  rw [hs]
  exact (congrArg (fun f : CellView Q A → ℂ => f v) hfix).trans
    (congrArg (fun f : CellView Q A → ℂ => f v) hs.symm)

theorem Rule.windowRun_one_inner_ne {Q A : Type*} [Fintype Q] [Fintype A] (R : Rule Q A)
    (h : R.GloballyWellformed) {B : ℕ} (u v : WindowConfig Q A B) (hu : u.Room 1) (hv : v.Room 1)
    (hne : u ≠ v) :
    ∑ w : WindowConfig Q A B, star (R.windowRun B 1 u w) * R.windowRun B 1 v w = 0 := by
  let T := Tape.empty R.blank
  rw [← windowEmbed_inner T 0 B]
  rw [R.windowRun_embed T 0 B 1 u hu, R.windowRun_embed T 0 B 1 v hv]
  obtain ⟨U,hU⟩ := h
  rw [← R.runBasis_eq_unitary_power U hU 1, ← R.runBasis_eq_unitary_power U hU 1]
  change inner ℂ (U (ket (encodeWindow T 0 B u))) (U (ket (encodeWindow T 0 B v))) = 0
  rw [U.inner_map_map, ket_inner]
  exact if_neg (fun he => hne (encodeWindow_injective T 0 B he))

theorem Rule.windowRun_one_inner_local {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (q : Q) (a : A) (r : CellRest A i) (y : WindowConfig Q A B → ℂ) :
    (∑ w : WindowConfig Q A B, star (R.windowRun B 1 (q,i,cellAssemble i a r) w) * y w) =
      ∑ out : Move × Q × A, star (R.amplitude q a out.1 out.2.1 out.2.2) *
        y (cellPlace i hi (.inr out,r)).2 := by
  have hstep (out : Move × Q × A) := cellPlace_step i hi q a r out.1 out.2.1 out.2.2
  simp only [Rule.windowRun, cellAssemble_same, hstep, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [star_sum, star_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro out _
  simp [Pi.single_apply]

theorem Rule.cellLocalGate_processed {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (i : Fin (2*B+1))
    (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1) (w : WindowConfig Q A B) (hw : w.Room 1) (hne : w.2.1 ≠ i) :
    R.cellLocalGate i hi *ᵥ windowMode true (R.windowRun B 1 w) = windowMode true (R.windowRun B 1 w) := by
  apply R.cellLocalGate_fixed_new i hi
  intro q a r
  rw [← R.windowRun_one_inner_local i hi q a r]
  apply R.windowRun_one_inner_ne h
  · exact hi
  · exact hw
  · intro he
    exact hne (congrArg (fun c : WindowConfig Q A B => c.2.1) he).symm

theorem Rule.cellLocalGate_source {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : Fin (2*B+1)) (hi : 1 ≤ i.val ∧ i.val+1 < 2*B+1)
    (w : WindowConfig Q A B) (hw : w.2.1 = i) :
    R.cellLocalGate i hi *ᵥ Pi.single (false,w) 1 = windowMode true (R.windowRun B 1 w) := by
  ext x
  rw [Matrix.mulVec_single_one]
  change R.cellLocalGate i hi x (false,w) = _
  rw [R.cellLocalGate_actual_step_all i hi w hw]
  cases h : x.1 <;> simp [windowMode, h]

abbrev WindowCenter (B : ℕ) := {i : Fin (2*B+1) // 1 ≤ i.val ∧ i.val+1 < 2*B+1}

noncomputable def Rule.cellSweep {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} : List (WindowCenter B) →
      Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ
  | [] => 1
  | i :: l => R.cellSweep l * R.cellLocalGate i.val i.property

theorem Rule.cellSweep_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (l : List (WindowCenter B)) :
    R.cellSweep l ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  induction l with
  | nil => exact one_mem _
  | cons i l ih => exact mul_mem ih (R.cellLocalGate_unitary h i.val i.property)

theorem Rule.cellSweep_processed {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (l : List (WindowCenter B))
    (w : WindowConfig Q A B) (hw : w.Room 1) (hne : ∀ i ∈ l, w.2.1 ≠ i.val) :
    R.cellSweep l *ᵥ windowMode true (R.windowRun B 1 w) = windowMode true (R.windowRun B 1 w) := by
  induction l with
  | nil => simp [Rule.cellSweep]
  | cons i l ih =>
    rw [Rule.cellSweep, ← Matrix.mulVec_mulVec,
        R.cellLocalGate_processed h i.val i.property w hw (hne i (by simp))]
    exact ih (fun j hj => hne j (by simp [hj]))

theorem Rule.cellSweep_source {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (l : List (WindowCenter B)) (hl : l.Nodup)
    (w : WindowConfig Q A B) (hw : w.Room 1) :
    R.cellSweep l *ᵥ Pi.single (false,w) 1 =
      if (⟨w.2.1,hw⟩ : WindowCenter B) ∈ l then windowMode true (R.windowRun B 1 w) else Pi.single (false,w) 1 := by
  induction l with
  | nil => simp only [Rule.cellSweep, Matrix.one_mulVec, List.not_mem_nil, if_false]
  | cons i l ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hl
    rw [Rule.cellSweep, ← Matrix.mulVec_mulVec]
    by_cases hiw : w.2.1 = i.val
    · rw [R.cellLocalGate_source i.val i.property w hiw]
      have hcenter : (⟨w.2.1,hw⟩ : WindowCenter B) = i := Subtype.ext hiw
      have hnone (j : WindowCenter B) (hj : j ∈ l) : w.2.1 ≠ j.val := by
        intro he
        have hij : i = j := Subtype.ext (hiw.symm.trans he)
        exact hnot (hij ▸ hj)
      rw [R.cellSweep_processed h l w hw hnone]
      simp [hcenter]
    · rw [R.cellLocalGate_other_old i.val i.property w hiw, ih htail]
      have hcenter : (⟨w.2.1,hw⟩ : WindowCenter B) ≠ i := fun he => hiw (congrArg Subtype.val he)
      simp [hcenter]

def windowCenterAt (B : ℕ) (j : Fin (2*B-1)) : WindowCenter B :=
  ⟨⟨j.val+1,by omega⟩,by dsimp; omega⟩

def windowCenters (B : ℕ) : List (WindowCenter B) := List.ofFn (windowCenterAt B)

theorem windowCenters_length (B : ℕ) : (windowCenters B).length = 2*B-1 := List.length_ofFn

theorem windowCenters_nodup (B : ℕ) : (windowCenters B).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b he
  have hv := congrArg (fun i : WindowCenter B => i.val.val) he
  apply Fin.ext
  dsimp [windowCenterAt] at hv
  omega

theorem mem_windowCenters {B : ℕ} (i : WindowCenter B) : i ∈ windowCenters B := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨i.val.val-1,by have hi := i.property; omega⟩, ?_⟩
  apply Subtype.ext
  apply Fin.ext
  dsimp [windowCenterAt]
  have hi := i.property
  omega

theorem Rule.cellSweep_complete {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (w : WindowConfig Q A B) (hw : w.Room 1) :
    R.cellSweep (windowCenters B) *ᵥ Pi.single (false,w) 1 = windowMode true (R.windowRun B 1 w) := by
  rw [R.cellSweep_source h _ (windowCenters_nodup B) w hw, if_pos (mem_windowCenters _)]

theorem injectionFrame_equiv_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ κ) (x : κ → ℂ) (y : κ) : (injectionFrame e *ᵥ x) y = x (e.symm y) := by
  have he (j : κ) : y = e j ↔ j = e.symm y := by
    constructor
    · intro h
      exact (e.symm_apply_eq.mpr h).symm
    · intro h
      rw [h, e.apply_symm_apply]
  simp [Matrix.mulVec, dotProduct, injectionFrame, ite_mul, he]

noncomputable def windowFlip {Q A : Type*} [DecidableEq Q] [DecidableEq A] (B : ℕ) :
    Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ :=
  injectionFrame (Equiv.prodCongr Equiv.boolNot (Equiv.refl (WindowConfig Q A B)))

theorem windowFlip_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A] (B : ℕ) :
    windowFlip (Q := Q) (A := A) B ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  exact injectionFrame_isometry _ (Equiv.prodCongr Equiv.boolNot (Equiv.refl _)).injective

theorem windowFlip_mode {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (B : ℕ) (p : Bool) (x : WindowConfig Q A B → ℂ) :
    windowFlip B *ᵥ windowMode p x = windowMode (!p) x := by
  ext y
  rw [windowFlip, injectionFrame_equiv_mulVec]
  rcases y with ⟨b,w⟩
  cases b <;> cases p <;> simp [windowMode, Equiv.boolNot]

noncomputable def Rule.windowUnitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (B : ℕ) : Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ :=
  windowFlip B * R.cellSweep (windowCenters B)

theorem Rule.windowUnitary_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (B : ℕ) :
    R.windowUnitary B ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ :=
  mul_mem (windowFlip_unitary B) (R.cellSweep_unitary h _)

theorem Rule.windowUnitary_source {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (w : WindowConfig Q A B) (hw : w.Room 1) :
    R.windowUnitary B *ᵥ Pi.single (false,w) 1 = windowMode false (R.windowRun B 1 w) := by
  rw [Rule.windowUnitary, ← Matrix.mulVec_mulVec, R.cellSweep_complete h w hw, windowFlip_mode]
  rfl

theorem Rule.windowUnitary_power {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (B t : ℕ) (w : WindowConfig Q A B) (hw : w.Room t) :
    (R.windowUnitary B ^ t) *ᵥ Pi.single (false,w) 1 = windowMode false (R.windowRun B t w) := by
  induction t generalizing w with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, Rule.windowRun]
    ext x
    simp [windowMode, Pi.single_apply, Prod.ext_iff, ite_and]
  | succ t ih =>
    have hroom : w.Room 1 := by dsimp [WindowConfig.Room] at hw ⊢; omega
    rw [pow_succ, ← Matrix.mulVec_mulVec, R.windowUnitary_source h w hroom]
    change Matrix.toLin' (R.windowUnitary B ^ t) (windowMode false (R.windowRun B 1 w)) = _
    simp only [Rule.windowRun, map_sum]
    apply Finset.sum_congr rfl
    intro out _
    obtain ⟨v,hv,hr⟩ := WindowConfig.step?_room w t hw out.1 out.2.1 out.2.2
    rw [hv, map_smul, map_smul]
    have hs : windowMode false (R.windowRun B 0 v) = Pi.single (false,v) 1 := by
      ext x
      simp [Rule.windowRun, windowMode, Pi.single_apply, Prod.ext_iff, ite_and]
    change _ • Matrix.toLin' (R.windowUnitary B ^ t) (windowMode false (R.windowRun B 0 v)) = _
    rw [hs, map_smul]
    exact congrArg (fun y => R.amplitude w.1 (w.2.2 w.2.1) out.1 out.2.1 out.2.2 • y) (ih v hr)

theorem Rule.windowUnitary_global {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (T : Tape A R.blank) (center : ℤ) (B t : ℕ)
    (w : WindowConfig Q A B) (hw : w.Room t) :
    windowEmbed T center B (fun v => ((R.windowUnitary B ^ t) *ᵥ Pi.single (false,w) 1) (false,v)) =
      R.runBasis t (encodeWindow T center B w) := by
  rw [R.windowUnitary_power h B t w hw]
  change windowEmbed T center B (R.windowRun B t w) = _
  exact R.windowRun_embed T center B t w hw

theorem Rule.windowUnitary_new_zero {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (B t : ℕ) (w v : WindowConfig Q A B) (hw : w.Room t) :
    ((R.windowUnitary B ^ t) *ᵥ Pi.single (false,w) 1) (true,v) = 0 := by
  rw [R.windowUnitary_power h B t w hw]
  simp [windowMode]

theorem Rule.windowUnitary_initial {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (B t : ℕ) (ht : t ≤ B) (c : Config Q A R.blank) :
    windowEmbed c.tape c.head B (fun v =>
      ((R.windowUnitary B ^ t) *ᵥ Pi.single (false,initialWindow B c) 1) (false,v)) = R.runBasis t c := by
  rw [R.windowUnitary_global h c.tape c.head B t _ (initialWindow_room B t c ht),
      encodeWindow_initial]

theorem Rule.windowUnitary_initial_value {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) (B t : ℕ) (ht : t ≤ B) (c : Config Q A R.blank)
    (P : Config Q A R.blank → ℝ) :
    (∑' d : Config Q A R.blank, ‖R.runBasis t c d‖ ^ 2 * P d) =
      ∑ x : Bool × WindowConfig Q A B,
        ‖((R.windowUnitary B ^ t) *ᵥ Pi.single (false,initialWindow B c) 1) x‖ ^ 2 *
          P (encodeWindow c.tape c.head B x.2) := by
  rw [R.windowRun_initial_value B t ht c,
      R.windowUnitary_power h B t _ (initialWindow_room B t c ht)]
  simp [Fintype.sum_prod_type, windowMode]

inductive WindowOp (B : ℕ) where
  | cell : WindowCenter B → WindowOp B
  | flip : WindowOp B
  deriving DecidableEq

def windowStepOps (B : ℕ) : List (WindowOp B) :=
  (windowCenters B).map WindowOp.cell ++ [.flip]

def windowWord (B : ℕ) : ℕ → List (WindowOp B)
  | 0 => []
  | t+1 => windowStepOps B ++ windowWord B t

noncomputable def WindowOp.matrix {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} : WindowOp B → Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ
  | .cell i => R.cellLocalGate i.val i.property
  | .flip => windowFlip B

noncomputable def Rule.windowWordMatrix {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} : List (WindowOp B) → Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ
  | [] => 1
  | g :: l => R.windowWordMatrix l * g.matrix R

theorem Rule.windowWordMatrix_append {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (l r : List (WindowOp B)) :
    R.windowWordMatrix (l++r) = R.windowWordMatrix r * R.windowWordMatrix l := by
  induction l with
  | nil => simp [Rule.windowWordMatrix]
  | cons a l ih => simp only [List.cons_append, Rule.windowWordMatrix, ih, Matrix.mul_assoc]

theorem Rule.windowWordMatrix_cells {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (l : List (WindowCenter B)) :
    R.windowWordMatrix (l.map WindowOp.cell) = R.cellSweep l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, Rule.windowWordMatrix, Rule.cellSweep, ih, WindowOp.matrix]

theorem Rule.windowStepOps_matrix {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (B : ℕ) : R.windowWordMatrix (windowStepOps B) = R.windowUnitary B := by
  rw [windowStepOps, R.windowWordMatrix_append, R.windowWordMatrix_cells]
  simp [Rule.windowWordMatrix, WindowOp.matrix, Rule.windowUnitary]

theorem Rule.windowWord_matrix {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (B t : ℕ) : R.windowWordMatrix (windowWord B t) = R.windowUnitary B ^ t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [windowWord, R.windowWordMatrix_append, R.windowStepOps_matrix, ih, pow_succ]

theorem windowStepOps_length (B : ℕ) : (windowStepOps B).length = (2*B-1)+1 := by
  simp [windowStepOps, windowCenters_length]

theorem windowWord_length (B t : ℕ) : (windowWord B t).length = t*((2*B-1)+1) := by
  induction t with
  | zero => simp [windowWord]
  | succ t ih => simp [windowWord, List.length_append, windowStepOps_length, ih, Nat.succ_mul, Nat.add_comm]

theorem windowWord_length_bound (B t : ℕ) : (windowWord B t).length ≤ t*(2*B+1) := by
  rw [windowWord_length]
  exact Nat.mul_le_mul_left t (by omega)

def WindowOp.encode {B : ℕ} : WindowOp B → ℕ
  | .cell i => i.val.val+1
  | .flip => 0

def WindowOp.decode (B n : ℕ) : Option (WindowOp B) :=
  if n = 0 then some .flip else
  if h : n-1 < 2*B+1 ∧ 1 ≤ n-1 ∧ (n-1)+1 < 2*B+1 then
    some (.cell ⟨⟨n-1,h.1⟩,h.2⟩) else none

theorem WindowOp.decode_encode {B : ℕ} (g : WindowOp B) : decode B g.encode = some g := by
  cases g with
  | flip => simp [encode,decode]
  | cell i =>
    have hi := i.property
    simp only [encode,decode]
    rw [if_neg (by omega), dif_pos (by omega)]
    congr 3

def windowWordCode (B t : ℕ) : List ℕ := (windowWord B t).map WindowOp.encode

theorem windowWordCode_decode (B t : ℕ) :
    (windowWordCode B t).mapM (WindowOp.decode B) = some (windowWord B t) := by
  simp only [windowWordCode, List.mapM_map, Function.comp_def, WindowOp.decode_encode]
  generalize windowWord B t = l
  induction l with
  | nil => rfl
  | cons g l ih => simp [List.mapM_cons, ih]

def slotRoutePrefix {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α) : ℕ → Equiv.Perm α
  | 0 => Equiv.refl α
  | n+1 => if h : n < k then
      (slotRoutePrefix a b n).trans (Equiv.swap (slotRoutePrefix a b n (a ⟨n,h⟩)) (b ⟨n,h⟩))
    else slotRoutePrefix a b n

theorem slotRoutePrefix_spec {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (n : ℕ) (hn : n ≤ k) :
    ∀ j : Fin k, j.val < n → slotRoutePrefix a b n (a j) = b j := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have hnk : n < k := by omega
    rw [slotRoutePrefix, dif_pos hnk, Equiv.trans_apply]
    by_cases he : j.val = n
    · have hjn : j = ⟨n,hnk⟩ := Fin.ext he
      subst j
      exact Equiv.swap_apply_left _ _
    · have hjn : j.val < n := by omega
      have hprev := ih (by omega) j hjn
      rw [hprev]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hbad
        have heq := ha ((slotRoutePrefix a b n).injective (hprev.trans hbad))
        exact he (congrArg Fin.val heq)
      · intro hbad
        exact he (congrArg Fin.val (hb hbad))

def slotRoute {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α) : Equiv.Perm α :=
  slotRoutePrefix a b k

theorem slotRoute_spec {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (j : Fin k) :
    slotRoute a b (a j) = b j := slotRoutePrefix_spec a b ha hb k le_rfl j j.isLt

def swapWordEval {α : Type*} [DecidableEq α] : List (α × α) → Equiv.Perm α
  | [] => Equiv.refl α
  | ab :: l => (Equiv.swap ab.1 ab.2).trans (swapWordEval l)

theorem swapWordEval_append {α : Type*} [DecidableEq α] (l r : List (α × α)) :
    swapWordEval (l++r) = (swapWordEval l).trans (swapWordEval r) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.cons_append, swapWordEval, ih]
    rfl

def slotRouteSwaps {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α) : ℕ → List (α × α)
  | 0 => []
  | n+1 => if h : n < k then
      slotRouteSwaps a b n ++ [(slotRoutePrefix a b n (a ⟨n,h⟩),b ⟨n,h⟩)]
    else slotRouteSwaps a b n

theorem slotRouteSwaps_eval {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α) (n : ℕ) :
    swapWordEval (slotRouteSwaps a b n) = slotRoutePrefix a b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < k
    · rw [slotRouteSwaps, dif_pos hn, swapWordEval_append, ih, slotRoutePrefix, dif_pos hn]
      rfl
    · rw [slotRouteSwaps, dif_neg hn, slotRoutePrefix, dif_neg hn, ih]

theorem slotRouteSwaps_length {α : Type*} [DecidableEq α] {k : ℕ} (a b : Fin k → α)
    (n : ℕ) (hn : n ≤ k) : (slotRouteSwaps a b n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [slotRouteSwaps, dif_pos (by omega), List.length_append]
    simp [ih (by omega)]

abbrev WindowHead (B : ℕ) := Bool × Fin (2*B+1)

def cellHeadSlots {B : ℕ} (i : WindowCenter B) : Fin 4 → WindowHead B
  | 0 => (false,i.val)
  | 1 => (true,windowNeighbor i.val i.property .left)
  | 2 => (true,windowNeighbor i.val i.property .stay)
  | _ => (true,windowNeighbor i.val i.property .right)

theorem cellHeadSlots_injective {B : ℕ} (i : WindowCenter B) : Function.Injective (cellHeadSlots i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cellHeadSlots]
  all_goals
    have he := windowNeighbor_injective i.val i.property h
    cases he

def canonicalHeadSlots {B : ℕ} (i : WindowCenter B) : Fin 4 → WindowHead B
  | 0 => (false,⟨0,by omega⟩)
  | 1 => (true,⟨0,by omega⟩)
  | 2 => (false,⟨1,by have hi := i.property; omega⟩)
  | _ => (true,⟨1,by have hi := i.property; omega⟩)

theorem canonicalHeadSlots_injective {B : ℕ} (i : WindowCenter B) :
    Function.Injective (canonicalHeadSlots i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [canonicalHeadSlots]

def cellHeadRoute {B : ℕ} (i : WindowCenter B) : Equiv.Perm (WindowHead B) :=
  slotRoute (cellHeadSlots i) (canonicalHeadSlots i)

theorem cellHeadRoute_spec {B : ℕ} (i : WindowCenter B) (j : Fin 4) :
    cellHeadRoute i (cellHeadSlots i j) = canonicalHeadSlots i j :=
  slotRoute_spec _ _ (cellHeadSlots_injective i) (canonicalHeadSlots_injective i) j

def cellHeadRouteWord {B : ℕ} (i : WindowCenter B) : List (WindowHead B × WindowHead B) :=
  slotRouteSwaps (cellHeadSlots i) (canonicalHeadSlots i) 4

theorem cellHeadRouteWord_eval {B : ℕ} (i : WindowCenter B) :
    swapWordEval (cellHeadRouteWord i) = cellHeadRoute i := slotRouteSwaps_eval _ _ 4

theorem cellHeadRouteWord_length {B : ℕ} (i : WindowCenter B) : (cellHeadRouteWord i).length = 4 :=
  slotRouteSwaps_length _ _ 4 le_rfl

def headAddressEquiv (B : ℕ) : WindowHead B ≃ Fin ((2*B+1)*2) :=
  ((Equiv.prodComm Bool (Fin (2*B+1))).trans
    (Equiv.prodCongr (Equiv.refl (Fin (2*B+1))) finTwoEquiv.symm)).trans finProdFinEquiv

theorem headAddressEquiv_val (B : ℕ) (x : WindowHead B) :
    (headAddressEquiv B x).val = 2*x.2.val + (if x.1 then 1 else 0) := by
  rcases x with ⟨b,h⟩
  cases b <;> simp [headAddressEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

def headQubits (B : ℕ) : ℕ := Nat.clog 2 ((2*B+1)*2)

theorem headQubits_capacity (B : ℕ) : (2*B+1)*2 ≤ 2 ^ headQubits B := Nat.le_pow_clog (by decide) _

def headToBits (B : ℕ) (x : WindowHead B) : Qatlib.Foundations.PureStateMath.Reg (headQubits B) :=
  (Qatlib.Foundations.PureStateMath.bitVecEquiv (headQubits B)).symm (Fin.castLE (headQubits_capacity B) (headAddressEquiv B x))

def headFromBits (B : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) : Option (WindowHead B) :=
  if h : (Qatlib.Foundations.PureStateMath.bitVecEquiv (headQubits B) x).val < (2*B+1)*2 then
    some ((headAddressEquiv B).symm ⟨_,h⟩) else none

theorem headToBits_address (B : ℕ) (x : WindowHead B) :
    (Qatlib.Foundations.PureStateMath.bitVecEquiv (headQubits B) (headToBits B x)).val = (headAddressEquiv B x).val := by
  simp [headToBits]

theorem headToBits_injective (B : ℕ) : Function.Injective (headToBits B) := by
  intro x y h
  apply (headAddressEquiv B).injective
  apply Fin.ext
  exact (headToBits_address B x).symm.trans
      ((congrArg (fun b => (Qatlib.Foundations.PureStateMath.bitVecEquiv (headQubits B) b).val) h).trans (headToBits_address B y))

theorem headFromBits_toBits (B : ℕ) (x : WindowHead B) : headFromBits B (headToBits B x) = some x := by
  unfold headFromBits
  rw [dif_pos (by rw [headToBits_address]; exact (headAddressEquiv B x).isLt)]
  congr 1
  apply (headAddressEquiv B).injective
  simp only [Equiv.apply_symm_apply]
  exact Fin.ext (headToBits_address B x)

theorem canonicalHeadSlots_address {B : ℕ} (i : WindowCenter B) (j : Fin 4) :
    (headAddressEquiv B (canonicalHeadSlots i j)).val = j.val := by
  fin_cases j <;> rw [headAddressEquiv_val] <;> rfl

def cellHeadBitRouteWord {B : ℕ} (i : WindowCenter B) :
    List (Qatlib.Foundations.PureStateMath.Reg (headQubits B) × Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :=
  (cellHeadRouteWord i).map (fun xy => (headToBits B xy.1,headToBits B xy.2))

theorem cellHeadBitRouteWord_length {B : ℕ} (i : WindowCenter B) : (cellHeadBitRouteWord i).length = 4 := by
  rw [cellHeadBitRouteWord, List.length_map, cellHeadRouteWord_length]

theorem swap_injection {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (a b x : α) : Equiv.swap (f a) (f b) (f x) = f (Equiv.swap a b x) := by
  by_cases hxa : x = a
  · subst x
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hxb : x = b
    · subst x
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hxa (hf h)) (fun h => hxb (hf h)),
        Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem swapWordEval_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List (α × α)) (x : α) :
    swapWordEval (l.map (fun xy => (f xy.1,f xy.2))) (f x) = f (swapWordEval l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons ab l ih =>
    simp only [List.map_cons, swapWordEval, Equiv.trans_apply, swap_injection f hf]
    exact ih _

theorem swapWordEval_map_outside {α β : Type*} [DecidableEq β] (f : α → β)
    (l : List (α × α)) (y : β) (hy : ∀ x, y ≠ f x) :
    swapWordEval (l.map (fun xy => (f xy.1,f xy.2))) y = y := by
  induction l with
  | nil => rfl
  | cons ab l ih =>
    simp only [List.map_cons, swapWordEval, Equiv.trans_apply,
      Equiv.swap_apply_of_ne_of_ne (hy ab.1) (hy ab.2)]
    exact ih

def cellHeadBitRoute {B : ℕ} (i : WindowCenter B) : Equiv.Perm (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :=
  swapWordEval (cellHeadBitRouteWord i)

theorem cellHeadBitRoute_encoded {B : ℕ} (i : WindowCenter B) (x : WindowHead B) :
    cellHeadBitRoute i (headToBits B x) = headToBits B (cellHeadRoute i x) := by
  rw [cellHeadBitRoute, cellHeadBitRouteWord, swapWordEval_map _ (headToBits_injective B),
      cellHeadRouteWord_eval]

theorem cellHeadBitRoute_spec {B : ℕ} (i : WindowCenter B) (j : Fin 4) :
    cellHeadBitRoute i (headToBits B (cellHeadSlots i j)) = headToBits B (canonicalHeadSlots i j) := by
  rw [cellHeadBitRoute_encoded, cellHeadRoute_spec]

theorem cellHeadBitRoute_spec_address {B : ℕ} (i : WindowCenter B) (j : Fin 4) :
    (Qatlib.Foundations.PureStateMath.bitVecEquiv (headQubits B) (cellHeadBitRoute i (headToBits B (cellHeadSlots i j)))).val = j.val := by
  rw [cellHeadBitRoute_spec, headToBits_address, canonicalHeadSlots_address]

theorem cellHeadBitRoute_inverse_spec {B : ℕ} (i : WindowCenter B) (j : Fin 4) :
    (cellHeadBitRoute i).symm (headToBits B (canonicalHeadSlots i j)) = headToBits B (cellHeadSlots i j) :=
  (cellHeadBitRoute i).symm_apply_eq.mpr (cellHeadBitRoute_spec i j).symm

theorem cellHeadBitRoute_illegal {B : ℕ} (i : WindowCenter B) (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B))
    (hx : headFromBits B x = none) : cellHeadBitRoute i x = x := by
  apply swapWordEval_map_outside
  intro y he
  rw [he, headFromBits_toBits] at hx
  contradiction

theorem injectionFrame_equiv_trans {κ : Type*} [Fintype κ] [DecidableEq κ] (e f : Equiv.Perm κ) :
    injectionFrame (e.trans f) = injectionFrame f * injectionFrame e := by
  ext x y
  change (if x = f (e y) then (1 : ℂ) else 0) =
    ∑ z : κ, (if x = f z then 1 else 0) * (if z = e y then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

noncomputable def swapWordMatrix {κ : Type*} [Fintype κ] [DecidableEq κ] : List (κ × κ) → Matrix κ κ ℂ
  | [] => 1
  | ab :: l => swapWordMatrix l * injectionFrame (Equiv.swap ab.1 ab.2)

theorem swapWordMatrix_eval {κ : Type*} [Fintype κ] [DecidableEq κ] (l : List (κ × κ)) :
    swapWordMatrix l = injectionFrame (swapWordEval l) := by
  induction l with
  | nil => ext x y; simp [swapWordMatrix, swapWordEval, injectionFrame, Matrix.one_apply]
  | cons ab l ih => rw [swapWordMatrix, ih, swapWordEval, injectionFrame_equiv_trans]

theorem swapWordMatrix_unitary {κ : Type*} [Fintype κ] [DecidableEq κ] (l : List (κ × κ)) :
    swapWordMatrix l ∈ Matrix.unitaryGroup κ ℂ := by
  rw [swapWordMatrix_eval, Matrix.mem_unitaryGroup_iff']
  exact injectionFrame_isometry _ (swapWordEval l).injective

theorem swapWordMatrix_single {κ : Type*} [Fintype κ] [DecidableEq κ] (l : List (κ × κ)) (x : κ) :
    swapWordMatrix l *ᵥ Pi.single x 1 = Pi.single (swapWordEval l x) 1 := by
  rw [swapWordMatrix_eval]
  ext y
  simp [injectionFrame, Pi.single_apply]

noncomputable def cellHeadBitRouteMatrix {B : ℕ} (i : WindowCenter B) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) ℂ :=
  swapWordMatrix (cellHeadBitRouteWord i)

theorem cellHeadBitRouteMatrix_unitary {B : ℕ} (i : WindowCenter B) :
    cellHeadBitRouteMatrix i ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) ℂ := swapWordMatrix_unitary _

theorem cellHeadBitRouteMatrix_source {B : ℕ} (i : WindowCenter B) (j : Fin 4) :
    cellHeadBitRouteMatrix i *ᵥ Pi.single (headToBits B (cellHeadSlots i j)) 1 =
      Pi.single (headToBits B (canonicalHeadSlots i j)) 1 := by
  rw [cellHeadBitRouteMatrix, swapWordMatrix_single]
  rw [← cellHeadBitRoute, cellHeadBitRoute_spec]

theorem cellHeadBitRouteMatrix_illegal {B : ℕ} (i : WindowCenter B) (x : Qatlib.Foundations.PureStateMath.Reg (headQubits B))
    (hx : headFromBits B x = none) : cellHeadBitRouteMatrix i *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [cellHeadBitRouteMatrix, swapWordMatrix_single]
  rw [← cellHeadBitRoute, cellHeadBitRoute_illegal i x hx]

theorem WindowOp.encode_decode {B n : ℕ} {g : WindowOp B} (h : decode B n = some g) : g.encode = n := by
  unfold decode at h
  split_ifs at h with hz hb
  · cases Option.some.inj h
    exact hz.symm
  · cases Option.some.inj h
    dsimp [encode]
    omega

theorem headToBits_fromBits {B : ℕ} {x : Qatlib.Foundations.PureStateMath.Reg (headQubits B)} {y : WindowHead B}
    (h : headFromBits B x = some y) : headToBits B y = x := by
  unfold headFromBits at h
  split_ifs at h with hb
  · cases Option.some.inj h
    apply (Qatlib.Foundations.PureStateMath.bitVecEquiv (headQubits B)).injective
    apply Fin.ext
    rw [headToBits_address, Equiv.apply_symm_apply]

theorem WindowOp.matrix_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (g : WindowOp B) :
    g.matrix R ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  cases g with
  | cell i => exact R.cellLocalGate_unitary h i.val i.property
  | flip => exact windowFlip_unitary B

theorem Rule.windowWordMatrix_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (l : List (WindowOp B)) :
    R.windowWordMatrix l ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  induction l with
  | nil => exact one_mem _
  | cons g l ih => exact mul_mem ih (g.matrix_unitary R h)

def cellViewCoords {Q A : Type*} : CellView Q A ≃ Fin 4 × Q × A where
  toFun
    | .inl qa => (0,qa)
    | .inr (.left,qa) => (1,qa)
    | .inr (.stay,qa) => (2,qa)
    | .inr (.right,qa) => (3,qa)
  invFun x := match x.1.val with
    | 0 => .inl x.2
    | 1 => .inr (.left,x.2)
    | 2 => .inr (.stay,x.2)
    | _ => .inr (.right,x.2)
  left_inv x := by cases x with
    | inl qa => rfl
    | inr ma => rcases ma with ⟨m,qa⟩; cases m <;> rfl
  right_inv x := by rcases x with ⟨j,qa⟩; fin_cases j <;> rfl

def windowHeadCoords (Q A : Type*) (B : ℕ) :
    (Bool × WindowConfig Q A B) ≃ WindowHead B × Q × (Fin (2*B+1) → A) where
  toFun x := ((x.1,x.2.2.1),x.2.1,x.2.2.2)
  invFun x := (x.1.1,x.2.1,x.1.2,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def headRouteWindow {Q A : Type*} {B : ℕ} (i : WindowCenter B) : Equiv.Perm (Bool × WindowConfig Q A B) :=
  ((windowHeadCoords Q A B).trans (Equiv.prodCongr (cellHeadRoute i) (Equiv.refl _))).trans
    (windowHeadCoords Q A B).symm

def canonicalCellPlace {Q A : Type*} {B : ℕ} (i : WindowCenter B)
    (vr : CellView Q A × CellRest A i.val) : Bool × WindowConfig Q A B :=
  let v := cellViewCoords vr.1
  let h := canonicalHeadSlots i v.1
  (h.1,v.2.1,h.2,cellAssemble i.val v.2.2 vr.2)

theorem headRouteWindow_place {Q A : Type*} {B : ℕ} (i : WindowCenter B)
    (vr : CellView Q A × CellRest A i.val) :
    headRouteWindow i (cellPlace i.val i.property vr) = canonicalCellPlace i vr := by
  rcases vr with ⟨v,r⟩
  cases v with
  | inl qa =>
    have he := cellHeadRoute_spec i 0
    change cellHeadRoute i (false,i.val) = canonicalHeadSlots i 0 at he
    change ((cellHeadRoute i (false,i.val)).1,qa.1,(cellHeadRoute i (false,i.val)).2,
      cellAssemble i.val qa.2 r) = _
    rw [he]
    rfl
  | inr ma =>
    rcases ma with ⟨m,qa⟩
    cases m with
    | left =>
      have he := cellHeadRoute_spec i 1
      change cellHeadRoute i
          (true,windowNeighbor i.val i.property .left) = canonicalHeadSlots i 1 at he
      change ((cellHeadRoute i (true,windowNeighbor i.val i.property .left)).1,qa.1,
        (cellHeadRoute i (true,windowNeighbor i.val i.property .left)).2,cellAssemble i.val qa.2 r) = _
      rw [he]
      rfl
    | stay =>
      have he := cellHeadRoute_spec i 2
      change cellHeadRoute i
          (true,windowNeighbor i.val i.property .stay) = canonicalHeadSlots i 2 at he
      change ((cellHeadRoute i (true,windowNeighbor i.val i.property .stay)).1,qa.1,
        (cellHeadRoute i (true,windowNeighbor i.val i.property .stay)).2,cellAssemble i.val qa.2 r) = _
      rw [he]
      rfl
    | right =>
      have he := cellHeadRoute_spec i 3
      change cellHeadRoute i
          (true,windowNeighbor i.val i.property .right) = canonicalHeadSlots i 3 at he
      change ((cellHeadRoute i (true,windowNeighbor i.val i.property .right)).1,qa.1,
        (cellHeadRoute i (true,windowNeighbor i.val i.property .right)).2,cellAssemble i.val qa.2 r) = _
      rw [he]
      rfl

theorem injectionFrame_comp {ι κ η : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq η]
    (f : ι → κ) (g : κ → η) : injectionFrame (g ∘ f) = injectionFrame g * injectionFrame f := by
  ext x y
  change (if x = g (f y) then (1 : ℂ) else 0) =
    ∑ z : κ, (if x = g z then 1 else 0) * (if z = f y then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem frameUnitary_conjugate {H I : Type*} [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]
    (P : Matrix H H ℂ) (hP : P ∈ Matrix.unitaryGroup H ℂ) (E : Matrix H I ℂ) (T : Matrix I I ℂ) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (P*E) T = P * Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary E T * P.conjTranspose := by
  have hPP : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hP
  simp only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
    Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  rw [hPP]

noncomputable def headRouteWindowMatrix {Q A : Type*} [DecidableEq Q] [DecidableEq A] {B : ℕ}
    (i : WindowCenter B) : Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ :=
  injectionFrame (headRouteWindow i)

theorem headRouteWindowMatrix_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    {B : ℕ} (i : WindowCenter B) :
    headRouteWindowMatrix (Q := Q) (A := A) i ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  exact injectionFrame_isometry _ (headRouteWindow i).injective

noncomputable def canonicalCellFrame {Q A : Type*} [DecidableEq Q] [DecidableEq A] {B : ℕ}
    (i : WindowCenter B) : Matrix (Bool × WindowConfig Q A B) (CellView Q A × CellRest A i.val) ℂ :=
  injectionFrame (canonicalCellPlace i)

theorem canonicalCellFrame_route {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    {B : ℕ} (i : WindowCenter B) :
    canonicalCellFrame (Q := Q) (A := A) i = headRouteWindowMatrix i * cellLocalFrame i.val i.property := by
  unfold canonicalCellFrame headRouteWindowMatrix cellLocalFrame
  have he := injectionFrame_comp (cellPlace (Q := Q) (A := A) i.val i.property) (headRouteWindow i)
  calc
    _ = injectionFrame (⇑(headRouteWindow i) ∘ cellPlace i.val i.property) := by
      congr 1
      funext vr
      exact (headRouteWindow_place i vr).symm
    _ = _ := he

noncomputable def Rule.canonicalCellGate {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : WindowCenter B) :
    Matrix (Bool × WindowConfig Q A B) (Bool × WindowConfig Q A B) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (canonicalCellFrame i)
    (R.cellSwap ⊗ₖ (1 : Matrix (CellRest A i.val) (CellRest A i.val) ℂ))

theorem Rule.canonicalCellGate_conjugate {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : WindowCenter B) :
    R.canonicalCellGate i = headRouteWindowMatrix i * R.cellLocalGate i.val i.property * (headRouteWindowMatrix i).conjTranspose := by
  unfold Rule.canonicalCellGate
  rw [canonicalCellFrame_route]
  exact frameUnitary_conjugate (headRouteWindowMatrix i) (headRouteWindowMatrix_unitary i)
    (cellLocalFrame i.val i.property) (R.cellSwap ⊗ₖ (1 : Matrix (CellRest A i.val) (CellRest A i.val) ℂ))

theorem canonicalCellPlace_injective {Q A : Type*} {B : ℕ} (i : WindowCenter B) :
    Function.Injective (canonicalCellPlace (Q := Q) (A := A) i) := by
  intro a b he
  apply cellPlace_injective i.val i.property
  apply (headRouteWindow i).injective
  rw [headRouteWindow_place, headRouteWindow_place]
  exact he

theorem canonicalCellFrame_isometry {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    {B : ℕ} (i : WindowCenter B) : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (canonicalCellFrame (Q := Q) (A := A) i) :=
  injectionFrame_isometry _ (canonicalCellPlace_injective i)

theorem Rule.canonicalCellGate_unitary {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (h : R.GloballyWellformed) {B : ℕ} (i : WindowCenter B) :
    R.canonicalCellGate i ∈ Matrix.unitaryGroup (Bool × WindowConfig Q A B) ℂ := by
  apply Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_unitary _
      (canonicalCellFrame_isometry i)
  exact Matrix.kronecker_mem_unitary (R.cellSwap_unitary h) (one_mem _)

theorem Rule.cellLocalGate_routed {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) {B : ℕ} (i : WindowCenter B) :
    R.cellLocalGate i.val i.property = (headRouteWindowMatrix i).conjTranspose * R.canonicalCellGate i * headRouteWindowMatrix i := by
  have hP : (headRouteWindowMatrix (Q := Q) (A := A) i).conjTranspose * headRouteWindowMatrix i = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (headRouteWindowMatrix_unitary i)
  rw [R.canonicalCellGate_conjugate]
  simp only [← Matrix.mul_assoc, hP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hP, Matrix.mul_one]

def cellLabelEquiv (q a : ℕ) : CellView (Fin q) (Fin a) ≃ Fin (4*(q*a)) :=
  ((cellViewCoords).trans (Equiv.prodCongr (Equiv.refl (Fin 4)) finProdFinEquiv)).trans finProdFinEquiv

def cellQubits (q a : ℕ) : ℕ := Nat.clog 2 (4*(q*a))

theorem cellQubits_capacity (q a : ℕ) : 4*(q*a) ≤ 2 ^ cellQubits q a :=
    Nat.le_pow_clog (by decide) _

theorem cellQubits_bound (q a : ℕ) : cellQubits q a ≤ 2 + Nat.clog 2 q + Nat.clog 2 a := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  calc
    4*(q*a) ≤ 4*(2^Nat.clog 2 q * 2^Nat.clog 2 a) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul (Nat.le_pow_clog (by decide) q) (Nat.le_pow_clog (by decide) a))
    _ = 2 ^ (2 + Nat.clog 2 q + Nat.clog 2 a) := by rw [pow_add, pow_add]; norm_num; ring

def cellToBits (q a : ℕ) (x : CellView (Fin q) (Fin a)) : Qatlib.Foundations.PureStateMath.Reg (cellQubits q a) :=
  (Qatlib.Foundations.PureStateMath.bitVecEquiv (cellQubits q a)).symm
    (Fin.castLE (cellQubits_capacity q a) (cellLabelEquiv q a x))

def cellFromBits (q a : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)) : Option (CellView (Fin q) (Fin a)) :=
  if h : (Qatlib.Foundations.PureStateMath.bitVecEquiv (cellQubits q a) b).val < 4*(q*a) then
    some ((cellLabelEquiv q a).symm ⟨_,h⟩) else none

theorem cellToBits_address (q a : ℕ) (x : CellView (Fin q) (Fin a)) :
    (Qatlib.Foundations.PureStateMath.bitVecEquiv (cellQubits q a) (cellToBits q a x)).val = (cellLabelEquiv q a x).val := by
  simp [cellToBits]

theorem cellToBits_injective (q a : ℕ) : Function.Injective (cellToBits q a) := by
  intro x y h
  apply (cellLabelEquiv q a).injective
  apply Fin.ext
  exact (cellToBits_address q a x).symm.trans
    ((congrArg (fun b => (Qatlib.Foundations.PureStateMath.bitVecEquiv (cellQubits q a) b).val) h).trans (cellToBits_address q a y))

theorem cellFromBits_toBits (q a : ℕ) (x : CellView (Fin q) (Fin a)) :
    cellFromBits q a (cellToBits q a x) = some x := by
  unfold cellFromBits
  rw [dif_pos (by rw [cellToBits_address]; exact (cellLabelEquiv q a x).isLt)]
  congr 1
  apply (cellLabelEquiv q a).injective
  simp only [Equiv.apply_symm_apply]
  exact Fin.ext (cellToBits_address q a x)

theorem cellToBits_fromBits {q a : ℕ} {b : Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)} {x : CellView (Fin q) (Fin a)}
    (h : cellFromBits q a b = some x) : cellToBits q a x = b := by
  unfold cellFromBits at h
  split_ifs at h with hb
  cases Option.some.inj h
  apply (Qatlib.Foundations.PureStateMath.bitVecEquiv (cellQubits q a)).injective
  apply Fin.ext
  rw [cellToBits_address, Equiv.apply_symm_apply]

noncomputable def cellBinaryFrame (q a : ℕ) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)) (CellView (Fin q) (Fin a)) ℂ := injectionFrame (cellToBits q a)

theorem cellBinaryFrame_isometry (q a : ℕ) : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (cellBinaryFrame q a) :=
  injectionFrame_isometry _ (cellToBits_injective q a)

noncomputable def Rule.cellBinaryGate {q a : ℕ} (R : Rule (Fin q) (Fin a)) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)) (Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (cellBinaryFrame q a) R.cellSwap

theorem Rule.cellBinaryGate_unitary {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed) :
    R.cellBinaryGate ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_unitary _ (cellBinaryFrame_isometry q a) _ (R.cellSwap_unitary h)

theorem Rule.cellBinaryGate_frame {q a : ℕ} (R : Rule (Fin q) (Fin a)) :
    R.cellBinaryGate * cellBinaryFrame q a = cellBinaryFrame q a * R.cellSwap :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_frame _ (cellBinaryFrame_isometry q a) _

theorem Rule.cellBinaryGate_state {q a : ℕ} (R : Rule (Fin q) (Fin a)) (x : CellView (Fin q) (Fin a) → ℂ) :
    R.cellBinaryGate *ᵥ (cellBinaryFrame q a *ᵥ x) = cellBinaryFrame q a *ᵥ (R.cellSwap *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, R.cellBinaryGate_frame, ← Matrix.mulVec_mulVec]

theorem Rule.cellBinaryGate_illegal {q a : ℕ} (R : Rule (Fin q) (Fin a))
    (b : Qatlib.Foundations.PureStateMath.Reg (cellQubits q a)) (hb : cellFromBits q a b = none) :
    R.cellBinaryGate *ᵥ Pi.single b 1 = Pi.single b 1 := by
  apply frameUnitary_outside
  intro x he
  rw [he, cellFromBits_toBits] at hb
  contradiction

theorem injectionFrame_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (x : ι) : injectionFrame f *ᵥ Pi.single x 1 = Pi.single (f x) 1 := by
  ext y
  simp [injectionFrame, Pi.single_apply]

theorem Rule.cellSwap_old_column {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q] [DecidableEq A]
    (R : Rule Q A) (inp : Q × A) :
    R.cellSwap *ᵥ Pi.single (.inl inp) 1 =
      ∑ out : Move × Q × A, R.amplitude inp.1 inp.2 out.1 out.2.1 out.2.2 • Pi.single (.inr out) 1 := by
  ext v
  rw [Matrix.mulVec_single_one]
  cases v with
  | inl qa => simp [Rule.cellSwap, isometrySwap, Matrix.col]
  | inr out => simp [Matrix.col, Rule.cellSwap_new_old, Pi.single_apply]

theorem Rule.cellBinaryGate_old_column {q a : ℕ} (R : Rule (Fin q) (Fin a)) (inp : Fin q × Fin a) :
    R.cellBinaryGate *ᵥ Pi.single (cellToBits q a (.inl inp)) 1 =
      ∑ out : Move × Fin q × Fin a, R.amplitude inp.1 inp.2 out.1 out.2.1 out.2.2 •
        Pi.single (cellToBits q a (.inr out)) 1 := by
  rw [← injectionFrame_single (cellToBits q a) (.inl inp)]
  change R.cellBinaryGate *ᵥ (cellBinaryFrame q a *ᵥ Pi.single (.inl inp) 1) = _
  rw [R.cellBinaryGate_state, R.cellSwap_old_column, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro out _
  rw [Matrix.mulVec_smul]
  rw [cellBinaryFrame, injectionFrame_single]

theorem swapWordEval_reverse {α : Type*} [DecidableEq α] (l : List (α × α)) :
    swapWordEval l.reverse = (swapWordEval l).symm := by
  induction l with
  | nil => rfl
  | cons ab l ih =>
    rw [List.reverse_cons, swapWordEval_append, ih, swapWordEval]
    rfl

theorem injectionFrame_equiv_symm {α : Type*} [DecidableEq α] (e : Equiv.Perm α) :
    injectionFrame e.symm = (injectionFrame e).conjTranspose := by
  ext x y
  have he : x = e.symm y ↔ y = e x := by
    constructor
    · intro h; rw [h,e.apply_symm_apply]
    · intro h; rw [h,e.symm_apply_apply]
  simp [injectionFrame, Matrix.conjTranspose_apply, he]

theorem swapWordMatrix_reverse {α : Type*} [Fintype α] [DecidableEq α] (l : List (α × α)) :
    swapWordMatrix l.reverse = (swapWordMatrix l).conjTranspose := by
  rw [swapWordMatrix_eval, swapWordEval_reverse, injectionFrame_equiv_symm, swapWordMatrix_eval]

def cellHeadBitRouteReverseWord {B : ℕ} (i : WindowCenter B) :
    List (Qatlib.Foundations.PureStateMath.Reg (headQubits B) × Qatlib.Foundations.PureStateMath.Reg (headQubits B)) := (cellHeadBitRouteWord i).reverse

theorem cellHeadBitRouteReverseWord_eval {B : ℕ} (i : WindowCenter B) :
    swapWordEval (cellHeadBitRouteReverseWord i) = (cellHeadBitRoute i).symm := swapWordEval_reverse _

theorem cellHeadBitRouteReverseWord_length {B : ℕ} (i : WindowCenter B) :
    (cellHeadBitRouteReverseWord i).length = 4 := by
  rw [cellHeadBitRouteReverseWord, List.length_reverse, cellHeadBitRouteWord_length]

theorem cellHeadBitRouteReverseWord_matrix {B : ℕ} (i : WindowCenter B) :
    swapWordMatrix (cellHeadBitRouteReverseWord i) = (cellHeadBitRouteMatrix i).conjTranspose := swapWordMatrix_reverse _

def finiteQubits (n : ℕ) : ℕ := Nat.clog 2 n

def finToBits (n : ℕ) (x : Fin n) : Qatlib.Foundations.PureStateMath.Reg (finiteQubits n) :=
  (Qatlib.Foundations.PureStateMath.bitVecEquiv (finiteQubits n)).symm (Fin.castLE (Nat.le_pow_clog (by decide) n) x)

def finFromBits (n : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (finiteQubits n)) : Option (Fin n) :=
  if h : (Qatlib.Foundations.PureStateMath.bitVecEquiv (finiteQubits n) b).val < n then some ⟨_,h⟩ else none

theorem finToBits_injective (n : ℕ) : Function.Injective (finToBits n) := by
  intro x y h
  apply Fin.ext
  have he :=
      congrArg (fun b => (Qatlib.Foundations.PureStateMath.bitVecEquiv (finiteQubits n) b).val) h
  simpa [finToBits] using! he

theorem finFromBits_toBits (n : ℕ) (x : Fin n) : finFromBits n (finToBits n x) = some x := by
  unfold finFromBits
  simp only [finToBits, Equiv.apply_symm_apply, Fin.val_castLE]
  rw [dif_pos x.isLt]

theorem finToBits_fromBits {n : ℕ} {b : Qatlib.Foundations.PureStateMath.Reg (finiteQubits n)} {x : Fin n}
    (h : finFromBits n b = some x) : finToBits n x = b := by
  unfold finFromBits at h
  split_ifs at h with hb
  cases Option.some.inj h
  apply (Qatlib.Foundations.PureStateMath.bitVecEquiv (finiteQubits n)).injective
  simp [finToBits]

abbrev BinaryWindow (q a B : ℕ) := Qatlib.Foundations.PureStateMath.Reg (headQubits B) ×
  Qatlib.Foundations.PureStateMath.Reg (finiteQubits q) × (Fin (2*B+1) → Qatlib.Foundations.PureStateMath.Reg (finiteQubits a))

def windowToBits (q a B : ℕ) (x : Bool × WindowConfig (Fin q) (Fin a) B) : BinaryWindow q a B :=
  (headToBits B (x.1,x.2.2.1),finToBits q x.2.1,fun j => finToBits a (x.2.2.2 j))

theorem windowToBits_injective (q a B : ℕ) : Function.Injective (windowToBits q a B) := by
  intro x y he
  have hh := headToBits_injective B (congrArg (fun z : BinaryWindow q a B => z.1) he)
  have hq := finToBits_injective q (congrArg (fun z : BinaryWindow q a B => z.2.1) he)
  have ht : x.2.2.2 = y.2.2.2 := by
    funext j
    exact finToBits_injective a (congrArg (fun z : BinaryWindow q a B => z.2.2 j) he)
  exact Prod.ext (congrArg (fun h : WindowHead B => h.1) hh)
      (Prod.ext hq (Prod.ext (congrArg (fun h : WindowHead B => h.2) hh) ht))

noncomputable def windowBinaryFrame (q a B : ℕ) : Matrix (BinaryWindow q a B) (Bool × WindowConfig (Fin q) (Fin a) B) ℂ :=
  injectionFrame (windowToBits q a B)

theorem windowBinaryFrame_isometry (q a B : ℕ) : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (windowBinaryFrame q a B) :=
  injectionFrame_isometry _ (windowToBits_injective q a B)

def binaryRestEncode {a B : ℕ} (i : Fin (2*B+1)) (r : CellRest (Fin a) i) :
    CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i := fun j => finToBits a (r j)

def binaryCanonicalPlace {q a B : ℕ} (i : WindowCenter B)
    (vr : CellView (Fin q) (Fin a) × CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val) : BinaryWindow q a B :=
  let v := cellViewCoords vr.1
  (headToBits B (canonicalHeadSlots i v.1),finToBits q v.2.1,
    cellAssemble i.val (finToBits a v.2.2) vr.2)

theorem binaryCanonicalPlace_injective {q a B : ℕ} (i : WindowCenter B) :
    Function.Injective (binaryCanonicalPlace (q := q) (a := a) i) := by
  rintro ⟨v,r⟩ ⟨v',r'⟩ he
  have hh :=
      canonicalHeadSlots_injective i
      (headToBits_injective B (congrArg (fun z : BinaryWindow q a B => z.1) he))
  have hq := finToBits_injective q (congrArg (fun z : BinaryWindow q a B => z.2.1) he)
  have ht : (finToBits a (cellViewCoords v).2.2,r) = (finToBits a (cellViewCoords v').2.2,r') := by
    apply cellAssemble_injective i.val
    exact congrArg (fun z : BinaryWindow q a B => z.2.2) he
  apply Prod.ext
  · apply cellViewCoords.injective
    exact Prod.ext hh (Prod.ext hq (finToBits_injective a (congrArg (fun z : Qatlib.Foundations.PureStateMath.Reg (finiteQubits a) ×
      CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val => z.1) ht)))
  · exact congrArg
      (fun z : Qatlib.Foundations.PureStateMath.Reg (finiteQubits a) × CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val => z.2) ht

theorem finToBits_assemble {a B : ℕ} (i : Fin (2*B+1)) (c : Fin a) (r : CellRest (Fin a) i) :
    (fun j => finToBits a (cellAssemble i c r j)) = cellAssemble i (finToBits a c) (binaryRestEncode i r) := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp only [cellAssemble_other i j _ _ hj, binaryRestEncode]

theorem binaryCanonicalPlace_encode {q a B : ℕ} (i : WindowCenter B)
    (vr : CellView (Fin q) (Fin a) × CellRest (Fin a) i.val) :
    windowToBits q a B (canonicalCellPlace i vr) = binaryCanonicalPlace i (vr.1,binaryRestEncode i.val vr.2) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact finToBits_assemble i.val _ _

theorem frameUnitary_tensor_single {K S H : Type*} [Fintype K] [Fintype S] [Fintype H]
    [DecidableEq K] [DecidableEq S] [DecidableEq H] (f : K × S → H) (hf : Function.Injective f)
    (T : Matrix K K ℂ) (v : K) (r : S) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame f) (T ⊗ₖ (1 : Matrix S S ℂ)) *ᵥ Pi.single (f (v,r)) 1 =
      ∑ k : K, T k v • Pi.single (f (k,r)) 1 := by
  ext x
  rw [Matrix.mulVec_single_one]
  have he := congrArg (fun M : Matrix H (K × S) ℂ => M x (v,r))
    (Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_frame (injectionFrame f) (injectionFrame_isometry f hf) (T ⊗ₖ (1 : Matrix S S ℂ)))
  change (∑ y : H, Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame f) (T ⊗ₖ (1 : Matrix S S ℂ)) x y *
      (if y = f (v,r) then 1 else 0)) =
    ∑ z : K × S, (if x = f z then 1 else 0) * (T z.1 v * (if z.2 = r then 1 else 0)) at he
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  rw [Fintype.sum_prod_type] at he
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  change Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame f)
      (T ⊗ₖ (1 : Matrix S S ℂ)) x (f (v,r)) = _
  rw [he]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

theorem frameUnitary_tensor_natural {K R S I J : Type*} [Fintype K] [Fintype R] [Fintype S] [Fintype I] [Fintype J]
    [DecidableEq K] [DecidableEq R] [DecidableEq S] [DecidableEq I] [DecidableEq J]
    (e : K × R → I) (he : Function.Injective e) (g : K × S → J) (hg : Function.Injective g)
    (f : I → J) (s : R → S) (T : Matrix K K ℂ)
    (hcomm : ∀ k r, f (e (k,r)) = g (k,s r))
    (hout : ∀ x, (¬ ∃ kr, e kr = x) → ∀ ks, f x ≠ g ks) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame g) (T ⊗ₖ (1 : Matrix S S ℂ)) * injectionFrame f =
      injectionFrame f * Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame e) (T ⊗ₖ (1 : Matrix R R ℂ)) := by
  apply Matrix.ext_of_mulVec_single
  intro x
  rw [← Matrix.mulVec_mulVec, injectionFrame_single, ← Matrix.mulVec_mulVec]
  by_cases hx : ∃ kr, e kr = x
  · obtain ⟨⟨k,r⟩,rfl⟩ := hx
    rw [frameUnitary_tensor_single e he, hcomm, frameUnitary_tensor_single g hg]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, injectionFrame_single, hcomm]
  · rw [frameUnitary_outside e _ x (fun kr h => hx ⟨kr,h.symm⟩), injectionFrame_single,
      frameUnitary_outside g _ _ (hout x hx)]

theorem canonicalCellPlace_head_range {Q A : Type*} {B : ℕ} (i : WindowCenter B)
    (x : Bool × WindowConfig Q A B) :
    (∃ vr, canonicalCellPlace i vr = x) ↔ ∃ j : Fin 4, canonicalHeadSlots i j = (x.1,x.2.2.1) := by
  constructor
  · rintro ⟨⟨v,r⟩,rfl⟩
    exact ⟨(cellViewCoords v).1,rfl⟩
  · rintro ⟨j,hj⟩
    let r : CellRest A i.val := fun k => x.2.2.2 k
    refine ⟨(cellViewCoords.symm (j,x.2.1,x.2.2.2 i.val),r), ?_⟩
    have ht : cellAssemble i.val (x.2.2.2 i.val) r = x.2.2.2 :=
      (Equiv.funSplitAt i.val A).symm_apply_apply x.2.2.2
    have hm := congrArg (fun h : WindowHead B => h.1) hj
    have hh := congrArg (fun h : WindowHead B => h.2) hj
    simp only [canonicalCellPlace, Equiv.apply_symm_apply, hm, hh, ht]

noncomputable def Rule.binaryCanonicalGate {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame (binaryCanonicalPlace i))
    (R.cellSwap ⊗ₖ (1 : Matrix (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val)
      (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val) ℂ))

theorem Rule.binaryCanonicalGate_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (i : WindowCenter B) :
    R.binaryCanonicalGate i ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ := by
  apply Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_unitary _
      (injectionFrame_isometry _ (binaryCanonicalPlace_injective i))
  exact Matrix.kronecker_mem_unitary (R.cellSwap_unitary h) (one_mem _)

theorem Rule.binaryCanonicalGate_intertwine {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    R.binaryCanonicalGate i * windowBinaryFrame q a B = windowBinaryFrame q a B * R.canonicalCellGate i := by
  apply frameUnitary_tensor_natural (canonicalCellPlace i) (canonicalCellPlace_injective i)
    (binaryCanonicalPlace i) (binaryCanonicalPlace_injective i) (windowToBits q a B)
    (binaryRestEncode i.val) R.cellSwap
  · intro k r
    exact binaryCanonicalPlace_encode i (k,r)
  · intro x hx kr hbad
    apply hx
    apply (canonicalCellPlace_head_range i x).mpr
    refine ⟨(cellViewCoords kr.1).1, ?_⟩
    exact (headToBits_injective B (congrArg (fun b : BinaryWindow q a B => b.1) hbad)).symm

def binaryHeadRouteWindow (q a : ℕ) {B : ℕ} (i : WindowCenter B) : Equiv.Perm (BinaryWindow q a B) :=
  Equiv.prodCongr (cellHeadBitRoute i) (Equiv.refl _)

noncomputable def binaryHeadRouteWindowMatrix (q a : ℕ) {B : ℕ} (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ := injectionFrame (binaryHeadRouteWindow q a i)

theorem binaryHeadRouteWindowMatrix_unitary (q a : ℕ) {B : ℕ} (i : WindowCenter B) :
    binaryHeadRouteWindowMatrix q a i ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  exact injectionFrame_isometry _ (binaryHeadRouteWindow q a i).injective

theorem binaryHeadRouteWindow_encode (q a : ℕ) {B : ℕ} (i : WindowCenter B)
    (x : Bool × WindowConfig (Fin q) (Fin a) B) :
    binaryHeadRouteWindow q a i (windowToBits q a B x) = windowToBits q a B (headRouteWindow i x) := by
  apply Prod.ext
  · exact cellHeadBitRoute_encoded i (x.1,x.2.2.1)
  · rfl

theorem binaryHeadRouteWindowMatrix_intertwine (q a : ℕ) {B : ℕ} (i : WindowCenter B) :
    binaryHeadRouteWindowMatrix q a i * windowBinaryFrame q a B =
      windowBinaryFrame q a B * headRouteWindowMatrix i := by
  unfold binaryHeadRouteWindowMatrix windowBinaryFrame headRouteWindowMatrix
  calc
    _ = injectionFrame (⇑(binaryHeadRouteWindow q a i) ∘ windowToBits q a B) :=
      (injectionFrame_comp (windowToBits q a B) (binaryHeadRouteWindow q a i)).symm
    _ = injectionFrame (windowToBits q a B ∘ headRouteWindow i) := by
      congr 1
      funext x
      exact binaryHeadRouteWindow_encode q a i x
    _ = _ := injectionFrame_comp (headRouteWindow (Q := Fin q) (A := Fin a) i) (windowToBits q a B)

theorem intertwine_adjoint {H I : Type*} [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]
    (P : Matrix H H ℂ) (Q : Matrix I I ℂ) (E : Matrix H I ℂ)
    (hP : P ∈ Matrix.unitaryGroup H ℂ) (hQ : Q ∈ Matrix.unitaryGroup I ℂ) (h : P*E = E*Q) :
    P.conjTranspose*E = E*Q.conjTranspose := by
  have hPP : P.conjTranspose*P=1 := Matrix.mem_unitaryGroup_iff'.mp hP
  have hQQ : Q*Q.conjTranspose=1 := Matrix.mem_unitaryGroup_iff.mp hQ
  calc
    _ = P.conjTranspose*(E*(Q*Q.conjTranspose)) := by rw [hQQ, Matrix.mul_one]
    _ = P.conjTranspose*((E*Q)*Q.conjTranspose) := by rw [Matrix.mul_assoc E Q]
    _ = P.conjTranspose*((P*E)*Q.conjTranspose) := by rw [← h]
    _ = (P.conjTranspose*P)*E*Q.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPP, Matrix.one_mul]

noncomputable def Rule.binaryCellGate {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  (binaryHeadRouteWindowMatrix q a i).conjTranspose * R.binaryCanonicalGate i * binaryHeadRouteWindowMatrix q a i

theorem Rule.binaryCellGate_intertwine {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    R.binaryCellGate i * windowBinaryFrame q a B = windowBinaryFrame q a B * R.cellLocalGate i.val i.property := by
  let P := binaryHeadRouteWindowMatrix q a i
  let Q := headRouteWindowMatrix (Q := Fin q) (A := Fin a) i
  let E := windowBinaryFrame q a B
  have hp : P*E=E*Q := binaryHeadRouteWindowMatrix_intertwine q a i
  have hpinv : P.conjTranspose*E=E*Q.conjTranspose :=
    intertwine_adjoint P Q E (binaryHeadRouteWindowMatrix_unitary q a i) (headRouteWindowMatrix_unitary i) hp
  calc
    _ = P.conjTranspose * (R.binaryCanonicalGate i * (P*E)) := by simp only [Rule.binaryCellGate, P, E, Matrix.mul_assoc]
    _ = P.conjTranspose * ((R.binaryCanonicalGate i * E)*Q) := by rw [hp, ← Matrix.mul_assoc _ E Q]
    _ = P.conjTranspose * ((E*R.canonicalCellGate i)*Q) := by rw [R.binaryCanonicalGate_intertwine]
    _ = (P.conjTranspose*E)*R.canonicalCellGate i*Q := by simp only [Matrix.mul_assoc]
    _ = E*(Q.conjTranspose*R.canonicalCellGate i*Q) := by rw [hpinv]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [← R.cellLocalGate_routed i]

theorem Rule.binaryCellGate_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (i : WindowCenter B) :
    R.binaryCellGate i ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ :=
  mul_mem (mul_mem (Unitary.star_mem (binaryHeadRouteWindowMatrix_unitary q a i))
    (R.binaryCanonicalGate_unitary h i)) (binaryHeadRouteWindowMatrix_unitary q a i)

def headFlipBits (B : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) : Qatlib.Foundations.PureStateMath.Reg (headQubits B) :=
  match headFromBits B b with
  | none => b
  | some h => headToBits B (!h.1,h.2)

theorem headFlipBits_encoded (B : ℕ) (h : WindowHead B) :
    headFlipBits B (headToBits B h) = headToBits B (!h.1,h.2) := by
  rw [headFlipBits, headFromBits_toBits]

theorem headFlipBits_involutive (B : ℕ) : Function.Involutive (headFlipBits B) := by
  intro b
  cases hb : headFromBits B b with
  | none => simp [headFlipBits, hb]
  | some h =>
    have he := headToBits_fromBits hb
    rw [← he, headFlipBits_encoded, headFlipBits_encoded]
    rcases h with ⟨p,j⟩
    cases p <;> rfl

def headFlipBitsEquiv (B : ℕ) : Equiv.Perm (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :=
  (headFlipBits_involutive B).toPerm

def binaryWindowFlipEquiv (q a B : ℕ) : Equiv.Perm (BinaryWindow q a B) :=
  Equiv.prodCongr (headFlipBitsEquiv B) (Equiv.refl _)

noncomputable def binaryWindowFlip (q a B : ℕ) : Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  injectionFrame (binaryWindowFlipEquiv q a B)

theorem binaryWindowFlip_unitary (q a B : ℕ) :
    binaryWindowFlip q a B ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  exact injectionFrame_isometry _ (binaryWindowFlipEquiv q a B).injective

theorem binaryWindowFlip_intertwine (q a B : ℕ) :
    binaryWindowFlip q a B * windowBinaryFrame q a B = windowBinaryFrame q a B * windowFlip B := by
  unfold binaryWindowFlip windowBinaryFrame windowFlip
  calc
    _ = injectionFrame (⇑(binaryWindowFlipEquiv q a B) ∘ windowToBits q a B) :=
      (injectionFrame_comp (windowToBits q a B) (binaryWindowFlipEquiv q a B)).symm
    _ = injectionFrame (windowToBits q a B ∘
        Equiv.prodCongr Equiv.boolNot (Equiv.refl (WindowConfig (Fin q) (Fin a) B))) := by
      congr 1
      funext x
      apply Prod.ext
      · exact headFlipBits_encoded B (x.1,x.2.2.1)
      · rfl
    _ = _ := injectionFrame_comp
      (Equiv.prodCongr Equiv.boolNot (Equiv.refl (WindowConfig (Fin q) (Fin a) B))) (windowToBits q a B)

noncomputable def WindowOp.binaryMatrix {q a : ℕ} (R : Rule (Fin q) (Fin a)) {B : ℕ} :
    WindowOp B → Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ
  | .cell i => R.binaryCellGate i
  | .flip => binaryWindowFlip q a B

theorem WindowOp.binaryMatrix_intertwine {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (g : WindowOp B) :
    g.binaryMatrix R * windowBinaryFrame q a B = windowBinaryFrame q a B * g.matrix R := by
  cases g with
  | cell i => exact R.binaryCellGate_intertwine i
  | flip => exact binaryWindowFlip_intertwine q a B

theorem WindowOp.binaryMatrix_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (g : WindowOp B) :
    g.binaryMatrix R ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ := by
  cases g with
  | cell i => exact R.binaryCellGate_unitary h i
  | flip => exact binaryWindowFlip_unitary q a B

noncomputable def Rule.binaryWordMatrix {q a B : ℕ} (R : Rule (Fin q) (Fin a)) :
    List (WindowOp B) → Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ
  | [] => 1
  | g :: l => R.binaryWordMatrix l * g.binaryMatrix R

theorem Rule.binaryWordMatrix_intertwine {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (l : List (WindowOp B)) :
    R.binaryWordMatrix l * windowBinaryFrame q a B = windowBinaryFrame q a B * R.windowWordMatrix l := by
  induction l with
  | nil => simp [Rule.binaryWordMatrix, Rule.windowWordMatrix]
  | cons g l ih =>
    rw [Rule.binaryWordMatrix, Matrix.mul_assoc, g.binaryMatrix_intertwine, ← Matrix.mul_assoc,
      ih, Matrix.mul_assoc, Rule.windowWordMatrix]

theorem Rule.binaryWordMatrix_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (l : List (WindowOp B)) :
    R.binaryWordMatrix l ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ := by
  induction l with
  | nil => exact one_mem _
  | cons g l ih => exact mul_mem ih (g.binaryMatrix_unitary R h)

def tapeBitsEquiv (N k : ℕ) : (Fin N → Qatlib.Foundations.PureStateMath.Reg k) ≃ Qatlib.Foundations.PureStateMath.Reg (N*k) :=
  (Equiv.curry (Fin N) (Fin k) Bool).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

def binaryWindowQubits (q a B : ℕ) : ℕ := headQubits B + finiteQubits q + (2*B+1)*finiteQubits a

def binaryWindowFlatten (q a B : ℕ) : BinaryWindow q a B ≃ Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B) :=
  (((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (tapeBitsEquiv (2*B+1) (finiteQubits a)))).trans
    (Equiv.prodAssoc _ _ _).symm).trans
      (Equiv.prodCongr (Qatlib.Foundations.PureStateMath.regAppendEquiv (headQubits B) (finiteQubits q)).symm (Equiv.refl _))).trans
        (Qatlib.Foundations.PureStateMath.regAppendEquiv (headQubits B + finiteQubits q) ((2*B+1)*finiteQubits a)).symm

noncomputable def binaryWindowFlattenMatrix (q a B : ℕ) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (BinaryWindow q a B) ℂ :=
  injectionFrame (binaryWindowFlatten q a B)

theorem binaryWindowFlattenMatrix_isometry (q a B : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (binaryWindowFlattenMatrix q a B) :=
  injectionFrame_isometry _ (binaryWindowFlatten q a B).injective

def windowToQubits (q a B : ℕ) (x : Bool × WindowConfig (Fin q) (Fin a) B) :
    Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B) := binaryWindowFlatten q a B (windowToBits q a B x)

noncomputable def windowQubitFrame (q a B : ℕ) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (Bool × WindowConfig (Fin q) (Fin a) B) ℂ :=
  injectionFrame (windowToQubits q a B)

theorem windowQubitFrame_flatten (q a B : ℕ) :
    windowQubitFrame q a B = binaryWindowFlattenMatrix q a B * windowBinaryFrame q a B := by
  rw [windowQubitFrame, binaryWindowFlattenMatrix, windowBinaryFrame, ← injectionFrame_comp]
  rfl

theorem windowQubitFrame_isometry (q a B : ℕ) : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (windowQubitFrame q a B) :=
  injectionFrame_isometry _ ((binaryWindowFlatten q a B).injective.comp (windowToBits_injective q a B))

theorem injectionFrame_symm {I J : Type*} [DecidableEq I] [DecidableEq J] (e : I ≃ J) :
    injectionFrame e.symm = (injectionFrame e).conjTranspose := by
  ext x y
  have he : x = e.symm y ↔ y = e x := by
    constructor
    · intro h; rw [h,e.apply_symm_apply]
    · intro h; rw [h,e.symm_apply_apply]
  simp [injectionFrame, Matrix.conjTranspose_apply, he]

theorem injectionFrame_equiv_complete {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : injectionFrame e * (injectionFrame e).conjTranspose = 1 := by
  have he := injectionFrame_isometry e.symm e.symm.injective
  change (injectionFrame e.symm).conjTranspose * injectionFrame e.symm = 1 at he
  rw [injectionFrame_symm, Matrix.conjTranspose_conjTranspose] at he
  exact he

noncomputable def WindowOp.qubitMatrix {q a : ℕ} (R : Rule (Fin q) (Fin a)) {B : ℕ} (g : WindowOp B) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) ℂ :=
  binaryWindowFlattenMatrix q a B * g.binaryMatrix R * (binaryWindowFlattenMatrix q a B).conjTranspose

theorem WindowOp.qubitMatrix_intertwine {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (g : WindowOp B) :
    g.qubitMatrix R * windowQubitFrame q a B = windowQubitFrame q a B * g.matrix R := by
  have hE : (binaryWindowFlattenMatrix q a B).conjTranspose * binaryWindowFlattenMatrix q a B = 1 :=
    binaryWindowFlattenMatrix_isometry q a B
  rw [WindowOp.qubitMatrix, windowQubitFrame_flatten]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (binaryWindowFlattenMatrix q a B).conjTranspose, hE, Matrix.one_mul,
    g.binaryMatrix_intertwine]

theorem WindowOp.qubitMatrix_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (g : WindowOp B) :
    g.qubitMatrix R ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) ℂ := by
  have hB := Matrix.mem_unitaryGroup_iff'.mp (g.binaryMatrix_unitary R h)
  change (g.binaryMatrix R).conjTranspose * g.binaryMatrix R = 1 at hB
  have hE : (binaryWindowFlattenMatrix q a B).conjTranspose * binaryWindowFlattenMatrix q a B = 1 :=
    binaryWindowFlattenMatrix_isometry q a B
  have hEE : binaryWindowFlattenMatrix q a B * (binaryWindowFlattenMatrix q a B).conjTranspose = 1 :=
    injectionFrame_equiv_complete (binaryWindowFlatten q a B)
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (g.qubitMatrix R).conjTranspose * g.qubitMatrix R = 1
  simp only [WindowOp.qubitMatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (binaryWindowFlattenMatrix q a B).conjTranspose, hE, Matrix.one_mul]
  rw [← Matrix.mul_assoc (g.binaryMatrix R).conjTranspose, hB, Matrix.one_mul, hEE]

noncomputable def Rule.qubitWordMatrix {q a B : ℕ} (R : Rule (Fin q) (Fin a)) :
    List (WindowOp B) → Matrix (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) ℂ
  | [] => 1
  | g :: l => R.qubitWordMatrix l * g.qubitMatrix R

theorem Rule.qubitWordMatrix_intertwine {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (l : List (WindowOp B)) :
    R.qubitWordMatrix l * windowQubitFrame q a B = windowQubitFrame q a B * R.windowWordMatrix l := by
  induction l with
  | nil => simp [Rule.qubitWordMatrix, Rule.windowWordMatrix]
  | cons g l ih =>
    rw [Rule.qubitWordMatrix, Matrix.mul_assoc, g.qubitMatrix_intertwine, ← Matrix.mul_assoc,
      ih, Matrix.mul_assoc, Rule.windowWordMatrix]

theorem Rule.qubitWordMatrix_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (l : List (WindowOp B)) :
    R.qubitWordMatrix l ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) ℂ := by
  induction l with
  | nil => exact one_mem _
  | cons g l ih => exact mul_mem ih (g.qubitMatrix_unitary R h)

theorem injectionFrame_eval {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (x : I → ℂ) (i : I) :
    (injectionFrame f *ᵥ x) (f i) = x i := by
  have he := congrArg (fun v : I → ℂ => v i)
    (congrArg (fun M : Matrix I I ℂ => M *ᵥ x) (injectionFrame_isometry f hf))
  (try dsimp only at he)
  rw [← Matrix.mulVec_mulVec, injectionFrame_adjoint_apply, Matrix.one_mulVec] at he
  exact he

theorem Rule.qubitWord_source {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (B t : ℕ) (w : WindowConfig (Fin q) (Fin a) B) (hw : w.Room t) :
    R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,w)) 1 =
      windowQubitFrame q a B *ᵥ windowMode false (R.windowRun B t w) := by
  rw [← injectionFrame_single (windowToQubits q a B) (false,w)]
  change R.qubitWordMatrix (windowWord B t) *ᵥ (windowQubitFrame q a B *ᵥ Pi.single (false,w) 1) = _
  rw [Matrix.mulVec_mulVec, R.qubitWordMatrix_intertwine, ← Matrix.mulVec_mulVec,
    R.windowWord_matrix, R.windowUnitary_power h B t w hw]

theorem Rule.qubitWord_global {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (T : Tape (Fin a) R.blank) (center : ℤ) (B t : ℕ) (w : WindowConfig (Fin q) (Fin a) B) (hw : w.Room t) :
    windowEmbed T center B (fun v =>
      (R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,w)) 1)
        (windowToQubits q a B (false,v))) = R.runBasis t (encodeWindow T center B w) := by
  rw [R.qubitWord_source h B t w hw]
  have he (v : WindowConfig (Fin q) (Fin a) B) := injectionFrame_eval (windowToQubits q a B)
    ((binaryWindowFlatten q a B).injective.comp (windowToBits_injective q a B))
    (windowMode false (R.windowRun B t w)) (false,v)
  simp_rw [show ∀ v, (windowQubitFrame q a B *ᵥ windowMode false (R.windowRun B t w))
      (windowToQubits q a B (false,v)) = R.windowRun B t w v from fun v => he v]
  exact R.windowRun_embed T center B t w hw

theorem injectionFrame_outside {I J : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) (x : I → ℂ) (j : J) (hj : ¬ ∃ i, f i = j) : (injectionFrame f *ᵥ x) j = 0 := by
  simp only [Matrix.mulVec, dotProduct, injectionFrame]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (fun he => hj ⟨i,he.symm⟩), zero_mul]

theorem injectionFrame_born_value {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (x : I → ℂ) (P : J → ℝ) :
    (∑ j : J, ‖(injectionFrame f *ᵥ x) j‖^2 * P j) = ∑ i : I, ‖x i‖^2 * P (f i) := by
  calc
    _ = ∑ j ∈ Finset.univ.image f, ‖(injectionFrame f *ᵥ x) j‖^2 * P j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hout : ¬ ∃ i, f i = j := by
        simpa only [Finset.mem_image, Finset.mem_univ, true_and] using! hj
      rw [injectionFrame_outside f x j hout]
      simp
    _ = _ := by rw [Finset.sum_image (fun a _ b _ he => hf he)]; simp only [injectionFrame_eval f hf]

def tapeBitsDecode (a B : ℕ) (b : Fin (2*B+1) → Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) :
    Option (Fin (2*B+1) → Fin a) :=
  if h : ∀ j, (Qatlib.Foundations.PureStateMath.bitVecEquiv (finiteQubits a) (b j)).val < a then
    some (fun j => ⟨_,h j⟩) else none

theorem tapeBitsDecode_encode (a B : ℕ) (x : Fin (2*B+1) → Fin a) :
    tapeBitsDecode a B (fun j => finToBits a (x j)) = some x := by
  unfold tapeBitsDecode
  simp only [finToBits, Equiv.apply_symm_apply, Fin.val_castLE]
  rw [dif_pos (fun j => (x j).isLt)]

def windowFromBits (q a B : ℕ) (b : BinaryWindow q a B) : Option (Bool × WindowConfig (Fin q) (Fin a) B) := do
  let h ← headFromBits B b.1
  let c ← finFromBits q b.2.1
  let tape ← tapeBitsDecode a B b.2.2
  return (h.1,c,h.2,tape)

theorem windowFromBits_toBits (q a B : ℕ) (x : Bool × WindowConfig (Fin q) (Fin a) B) :
    windowFromBits q a B (windowToBits q a B x) = some x := by
  simp [windowFromBits, windowToBits, headFromBits_toBits, finFromBits_toBits,
      tapeBitsDecode_encode]

def windowFromQubits (q a B : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) :
    Option (Bool × WindowConfig (Fin q) (Fin a) B) := windowFromBits q a B ((binaryWindowFlatten q a B).symm b)

theorem windowFromQubits_toQubits (q a B : ℕ) (x : Bool × WindowConfig (Fin q) (Fin a) B) :
    windowFromQubits q a B (windowToQubits q a B x) = some x := by
  rw [windowFromQubits, windowToQubits, Equiv.symm_apply_apply, windowFromBits_toBits]

theorem Rule.qubitWord_born_value {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (B t : ℕ) (w : WindowConfig (Fin q) (Fin a) B) (hw : w.Room t)
    (P : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B) → ℝ) :
    (∑ b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B),
      ‖(R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,w)) 1) b‖^2 * P b) =
      ∑ v : WindowConfig (Fin q) (Fin a) B, ‖R.windowRun B t w v‖^2 * P (windowToQubits q a B (false,v)) := by
  rw [R.qubitWord_source h B t w hw, windowQubitFrame, injectionFrame_born_value (windowToQubits q a B)
    ((binaryWindowFlatten q a B).injective.comp (windowToBits_injective q a B))]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, windowMode, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Bool.true_eq_false, if_false, if_true, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul,
    Finset.sum_const_zero, zero_add]

def qubitDecodedPayoff {q a B : ℕ} {blank : Fin a} (T : Tape (Fin a) blank) (center : ℤ)
    (P : Config (Fin q) (Fin a) blank → ℝ) (b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) : ℝ :=
  match windowFromQubits q a B b with
  | none => 0
  | some x => if x.1 then 0 else P (encodeWindow T center B x.2)

theorem Rule.qubitWord_initial_value {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (B t : ℕ) (ht : t ≤ B) (c : Config (Fin q) (Fin a) R.blank) (P : Config (Fin q) (Fin a) R.blank → ℝ) :
    (∑' d : Config (Fin q) (Fin a) R.blank, ‖R.runBasis t c d‖^2 * P d) =
      ∑ b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B),
        ‖(R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,initialWindow B c)) 1) b‖^2 *
          qubitDecodedPayoff c.tape c.head P b := by
  rw [R.qubitWord_born_value h B t _ (initialWindow_room B t c ht),
      R.windowRun_initial_value B t ht c]
  apply Finset.sum_congr rfl
  intro v _
  simp [qubitDecodedPayoff, windowFromQubits_toQubits]

theorem tapeBitsDecode_fromBits {a B : ℕ} {b : Fin (2*B+1) → Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)}
    {x : Fin (2*B+1) → Fin a} (h : tapeBitsDecode a B b = some x) :
    (fun j => finToBits a (x j)) = b := by
  unfold tapeBitsDecode at h
  split_ifs at h with hb
  cases Option.some.inj h
  funext j
  apply (Qatlib.Foundations.PureStateMath.bitVecEquiv (finiteQubits a)).injective
  simp [finToBits]

theorem windowToBits_fromBits {q a B : ℕ} {b : BinaryWindow q a B}
    {x : Bool × WindowConfig (Fin q) (Fin a) B} (h : windowFromBits q a B b = some x) : windowToBits q a B x = b := by
  unfold windowFromBits at h
  cases hh : headFromBits B b.1 with
  | none => simp [hh] at h
  | some hp =>
    cases hc : finFromBits q b.2.1 with
    | none => simp [hh,hc] at h
    | some cp =>
      cases ht : tapeBitsDecode a B b.2.2 with
      | none => simp [hh,hc,ht] at h
      | some tp =>
        have he : (hp.1,cp,hp.2,tp) = x := by simpa [hh,hc,ht] using! h
        rw [← he]
        apply Prod.ext
        · exact headToBits_fromBits hh
        · exact Prod.ext (finToBits_fromBits hc) (tapeBitsDecode_fromBits ht)

theorem windowToQubits_fromQubits {q a B : ℕ} {b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)}
    {x : Bool × WindowConfig (Fin q) (Fin a) B} (h : windowFromQubits q a B b = some x) :
    windowToQubits q a B x = b := by
  have he := windowToBits_fromBits h
  exact (congrArg (binaryWindowFlatten q a B) he).trans
      ((binaryWindowFlatten q a B).apply_symm_apply b)

theorem finiteQubits_le (n : ℕ) : finiteQubits n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide) |>.le)

theorem binaryWindowQubits_bound (q a B : ℕ) : binaryWindowQubits q a B ≤ (2*B+1)*2 + q + (2*B+1)*a := by
  have hh : headQubits B ≤ (2*B+1)*2 := finiteQubits_le _
  have hq := finiteQubits_le q
  have ha := Nat.mul_le_mul_left (2*B+1) (finiteQubits_le a)
  exact Nat.add_le_add (Nat.add_le_add hh hq) ha

theorem Rule.qubitWord_initial {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (B t : ℕ) (ht : t ≤ B) (c : Config (Fin q) (Fin a) R.blank) :
    windowEmbed c.tape c.head B (fun v =>
      (R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,initialWindow B c)) 1)
        (windowToQubits q a B (false,v))) = R.runBasis t c := by
  rw [R.qubitWord_global h c.tape c.head B t _ (initialWindow_room B t c ht), encodeWindow_initial]

theorem Rule.qubitWord_illegal_zero {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (B t : ℕ) (w : WindowConfig (Fin q) (Fin a) B) (hw : w.Room t)
    (b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (hb : windowFromQubits q a B b = none) :
    (R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,w)) 1) b = 0 := by
  rw [R.qubitWord_source h B t w hw, windowQubitFrame]
  apply injectionFrame_outside
  rintro ⟨x,hx⟩
  rw [← hx, windowFromQubits_toQubits] at hb
  contradiction

theorem Rule.qubitWord_born_mass {q a : ℕ} (R : Rule (Fin q) (Fin a)) (h : R.GloballyWellformed)
    (B t : ℕ) (w : WindowConfig (Fin q) (Fin a) B) (hw : w.Room t) :
    (∑ b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B),
      ‖(R.qubitWordMatrix (windowWord B t) *ᵥ Pi.single (windowToQubits q a B (false,w)) 1) b‖^2) = 1 := by
  have hv := R.qubitWord_born_value h B t w hw (fun _ => 1)
  simp only [mul_one] at hv
  rw [hv]
  exact R.windowRun_mass h (Tape.empty R.blank) 0 B t w hw

theorem injectionFrame_prod_identity {K H S : Type*} [DecidableEq K] [DecidableEq H] [DecidableEq S]
    (f : K → H) :
    injectionFrame (fun kr : K × S => (f kr.1,kr.2)) =
      injectionFrame f ⊗ₖ (1 : Matrix S S ℂ) := by
  ext ⟨x,r⟩ ⟨k,s⟩
  simp only [injectionFrame, Matrix.kronecker_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem frameUnitary_tensor_identity {K H S : Type*} [Fintype K] [Fintype H] [Fintype S]
    [DecidableEq K] [DecidableEq H] [DecidableEq S] (E : Matrix H K ℂ) (T : Matrix K K ℂ) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (E ⊗ₖ (1 : Matrix S S ℂ)) (T ⊗ₖ (1 : Matrix S S ℂ)) =
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary E T ⊗ₖ (1 : Matrix S S ℂ) := by
  simp only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]
  ext ⟨x,r⟩ ⟨y,s⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

theorem frameUnitary_basisEquiv {H J K : Type*} [Fintype H] [Fintype J] [Fintype K]
    [DecidableEq H] [DecidableEq J] [DecidableEq K]
    (e : H ≃ J) (E : Matrix H K ℂ) (T : Matrix K K ℂ) :
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame e * E) T =
      injectionFrame e * Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary E T * (injectionFrame e).conjTranspose := by
  have he := injectionFrame_equiv_complete e
  simp only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
    Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  rw [he]

abbrev SmallCellBits (q a B : ℕ) := Qatlib.Foundations.PureStateMath.Reg (headQubits B) ×
  Qatlib.Foundations.PureStateMath.Reg (finiteQubits q) × Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)

def binaryCellSplit (q a : ℕ) {B : ℕ} (i : Fin (2*B+1)) :
    BinaryWindow q a B ≃ SmallCellBits q a B × CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i where
  toFun b := ((b.1,b.2.1,b.2.2 i),fun j => b.2.2 j)
  invFun lr := (lr.1.1,lr.1.2.1,cellAssemble i lr.1.2.2 lr.2)
  left_inv b := by
    exact Prod.ext rfl (Prod.ext rfl
      ((Equiv.funSplitAt i (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a))).symm_apply_apply b.2.2))
  right_inv lr := by
    apply Prod.ext
    · simp only [cellAssemble_same]
    · funext j
      exact cellAssemble_other i j.val _ _ j.property

def smallCellPlace {q a B : ℕ} (i : WindowCenter B) (v : CellView (Fin q) (Fin a)) : SmallCellBits q a B :=
  (headToBits B (canonicalHeadSlots i (cellViewCoords v).1),
    finToBits q (cellViewCoords v).2.1,finToBits a (cellViewCoords v).2.2)

theorem smallCellPlace_injective {q a B : ℕ} (i : WindowCenter B) :
    Function.Injective (smallCellPlace (q := q) (a := a) i) := by
  intro v w he
  apply cellViewCoords.injective
  apply Prod.ext
  · exact canonicalHeadSlots_injective i
      (headToBits_injective B (congrArg (fun z : SmallCellBits q a B => z.1) he))
  · apply Prod.ext
    · exact finToBits_injective q (congrArg (fun z : SmallCellBits q a B => z.2.1) he)
    · exact finToBits_injective a (congrArg (fun z : SmallCellBits q a B => z.2.2) he)

theorem binaryCellSplit_place {q a B : ℕ} (i : WindowCenter B)
    (vr : CellView (Fin q) (Fin a) × CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val) :
    binaryCellSplit q a i.val (binaryCanonicalPlace i vr) = (smallCellPlace i vr.1,vr.2) := by
  apply Prod.ext
  · simp only [binaryCellSplit, Equiv.coe_fn_mk, binaryCanonicalPlace, smallCellPlace,
      cellAssemble_same]
  · funext j
    exact cellAssemble_other i.val j.val _ _ j.property

noncomputable def Rule.smallCellGate {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    Matrix (SmallCellBits q a B) (SmallCellBits q a B) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary (injectionFrame (smallCellPlace i)) R.cellSwap

theorem Rule.smallCellGate_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (i : WindowCenter B) :
    R.smallCellGate i ∈ Matrix.unitaryGroup (SmallCellBits q a B) ℂ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_unitary _ (injectionFrame_isometry _ (smallCellPlace_injective i))
    _ (R.cellSwap_unitary h)

theorem Rule.binaryCanonicalGate_local {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    injectionFrame (binaryCellSplit q a i.val) * R.binaryCanonicalGate i *
        (injectionFrame (binaryCellSplit q a i.val)).conjTranspose =
      R.smallCellGate i ⊗ₖ (1 : Matrix (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val)
        (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val) ℂ) := by
  rw [Rule.binaryCanonicalGate, ← frameUnitary_basisEquiv, ← injectionFrame_comp]
  have hp : (fun vr : CellView (Fin q) (Fin a) × CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i.val =>
      binaryCellSplit q a i.val (binaryCanonicalPlace i vr)) = fun vr => (smallCellPlace i vr.1,vr.2) := by
    funext vr
    exact binaryCellSplit_place i vr
  change (⇑(binaryCellSplit q a i.val) ∘ binaryCanonicalPlace i) = _ at hp
  rw [hp, injectionFrame_prod_identity, frameUnitary_tensor_identity]
  rfl

def smallCellQubits (q a B : ℕ) : ℕ := headQubits B + finiteQubits q + finiteQubits a

def smallCellFlatten (q a B : ℕ) : SmallCellBits q a B ≃ Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B) :=
  ((Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr (Qatlib.Foundations.PureStateMath.regAppendEquiv (headQubits B) (finiteQubits q)).symm (Equiv.refl _))).trans
      (Qatlib.Foundations.PureStateMath.regAppendEquiv (headQubits B + finiteQubits q) (finiteQubits a)).symm

def tapeCellWires {N k : ℕ} (i : Fin N) : Fin k ↪ Fin (N*k) :=
  ⟨fun j => finProdFinEquiv (i,j),fun _ _ h => congrArg Prod.snd (finProdFinEquiv.injective h)⟩

def smallCellWires (q a : ℕ) {B : ℕ} (i : Fin (2*B+1)) :
    Fin (smallCellQubits q a B) ↪ Fin (binaryWindowQubits q a B) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((Function.Embedding.sumMap (Function.Embedding.refl _) (tapeCellWires (k := finiteQubits a) i)).trans
      finSumFinEquiv.toEmbedding)

theorem smallCellWires_prefix (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (j : Fin (headQubits B + finiteQubits q)) :
    smallCellWires q a i (Fin.castAdd (finiteQubits a) j) = Fin.castAdd ((2*B+1)*finiteQubits a) j := by
  change finSumFinEquiv (Sum.map id (tapeCellWires i)
    (finSumFinEquiv.symm (Fin.castAdd (finiteQubits a) j))) = _
  simp

theorem smallCellWires_symbol (q a : ℕ) {B : ℕ} (i : Fin (2*B+1)) (j : Fin (finiteQubits a)) :
    smallCellWires q a i (Fin.natAdd (headQubits B + finiteQubits q) j) =
      Fin.natAdd (headQubits B + finiteQubits q) (finProdFinEquiv (i,j)) := by
  change finSumFinEquiv (Sum.map id (tapeCellWires i)
    (finSumFinEquiv.symm (Fin.natAdd (headQubits B + finiteQubits q) j))) = _
  simp [tapeCellWires]

theorem regJoin_prefix (m n : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg m) (y : Qatlib.Foundations.PureStateMath.Reg n) (j : Fin m) :
    (Qatlib.Foundations.PureStateMath.regAppendEquiv m n).symm (x,y) (Fin.castAdd n j) = x j :=
  congrArg (fun p : Qatlib.Foundations.PureStateMath.Reg m × Qatlib.Foundations.PureStateMath.Reg n => p.1 j)
    ((Qatlib.Foundations.PureStateMath.regAppendEquiv m n).apply_symm_apply (x,y))

theorem regJoin_suffix (m n : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg m) (y : Qatlib.Foundations.PureStateMath.Reg n) (j : Fin n) :
    (Qatlib.Foundations.PureStateMath.regAppendEquiv m n).symm (x,y) (Fin.natAdd m j) = y j :=
  congrArg (fun p : Qatlib.Foundations.PureStateMath.Reg m × Qatlib.Foundations.PureStateMath.Reg n => p.2 j)
    ((Qatlib.Foundations.PureStateMath.regAppendEquiv m n).apply_symm_apply (x,y))

theorem smallCellWires_read (q a : ℕ) {B : ℕ} (i : Fin (2*B+1)) (b : BinaryWindow q a B)
    (j : Fin (smallCellQubits q a B)) :
    binaryWindowFlatten q a B b (smallCellWires q a i j) =
      smallCellFlatten q a B ((binaryCellSplit q a i b).1) j := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · rw [smallCellWires_prefix]
    change (Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm
      ((Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm (b.1,b.2.1),tapeBitsEquiv _ _ b.2.2) (Fin.castAdd _ k) =
      (Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm
        ((Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm (b.1,b.2.1),b.2.2 i) (Fin.castAdd _ k)
    rw [regJoin_prefix, regJoin_prefix]
  · rw [smallCellWires_symbol]
    change (Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm
      ((Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm (b.1,b.2.1),tapeBitsEquiv _ _ b.2.2) (Fin.natAdd _ (finProdFinEquiv (i,k))) =
      (Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm
        ((Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm (b.1,b.2.1),b.2.2 i) (Fin.natAdd _ k)
    rw [regJoin_suffix, regJoin_suffix]
    change Function.uncurry b.2.2 (finProdFinEquiv.symm (finProdFinEquiv (i,k))) = b.2.2 i k
    rw [Equiv.symm_apply_apply]
    rfl

noncomputable def Rule.smallCellQubitGate {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ :=
  injectionFrame (smallCellFlatten q a B) * R.smallCellGate i * (injectionFrame (smallCellFlatten q a B)).conjTranspose

theorem Rule.smallCellQubitGate_unitary {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (i : WindowCenter B) :
    R.smallCellQubitGate i ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ := by
  rw [Rule.smallCellQubitGate, Rule.smallCellGate, ← frameUnitary_basisEquiv]
  apply Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary_unitary
  · rw [← injectionFrame_comp]
    exact injectionFrame_isometry _
        ((smallCellFlatten q a B).injective.comp (smallCellPlace_injective i))
  · exact R.cellSwap_unitary h

theorem finiteQubits_pow_bound (n : ℕ) : 2 ^ finiteQubits n ≤ 2*(n+1) := by
  by_cases hn : 1 < n
  · have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hn
    have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) hn
    have he : Nat.clog 2 n = (Nat.clog 2 n).pred + 1 := (Nat.succ_pred_eq_of_pos hc).symm
    change 2 ^ Nat.clog 2 n ≤ _
    rw [he, pow_succ]
    omega
  · interval_cases n <;> decide

theorem smallCellBits_card_bound (q a B : ℕ) :
    Fintype.card (SmallCellBits q a B) ≤ 8*(2*(2*B+1)+1)*(q+1)*(a+1) := by
  simp only [SmallCellBits, Fintype.card_prod, Qatlib.Foundations.PureStateMath.card_reg]
  have hh := finiteQubits_pow_bound ((2*B+1)*2)
  have hq := finiteQubits_pow_bound q
  have ha := finiteQubits_pow_bound a
  change 2 ^ finiteQubits ((2*B+1)*2) * (2 ^ finiteQubits q * 2 ^ finiteQubits a) ≤ _
  calc
    _ ≤ (2*(((2*B+1)*2)+1)) * ((2*(q+1))*(2*(a+1))) := Nat.mul_le_mul hh (Nat.mul_le_mul hq ha)
    _ = _ := by ring

theorem injectionFrame_equiv_conjugate_apply {H J : Type*} [Fintype H] [Fintype J]
    [DecidableEq H] [DecidableEq J] (e : H ≃ J) (M : Matrix H H ℂ) (x y : H) :
    (injectionFrame e * M * (injectionFrame e).conjTranspose) (e x) (e y) = M x y := by
  have he : ((injectionFrame e * M * (injectionFrame e).conjTranspose) *ᵥ Pi.single (e y) 1) (e x) = M x y := by
    rw [← Matrix.mulVec_mulVec, ← injectionFrame_symm, injectionFrame_single, Equiv.symm_apply_apply,
      ← Matrix.mulVec_mulVec, injectionFrame_eval e e.injective, Matrix.mulVec_single_one]
    rfl
  simpa only [Matrix.mulVec_single_one] using! he

theorem Rule.binaryCanonicalGate_entry {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B)
    (x y : BinaryWindow q a B) :
    R.binaryCanonicalGate i x y =
      R.smallCellGate i (binaryCellSplit q a i.val x).1 (binaryCellSplit q a i.val y).1 *
        if (binaryCellSplit q a i.val x).2 = (binaryCellSplit q a i.val y).2 then 1 else 0 := by
  have he := congrArg (fun M => M (binaryCellSplit q a i.val x) (binaryCellSplit q a i.val y))
    (R.binaryCanonicalGate_local i)
  (try dsimp only at he)
  rw [injectionFrame_equiv_conjugate_apply] at he
  exact he

def qubitCellSplit (q a : ℕ) {B : ℕ} (i : Fin (2*B+1)) :
    Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B) ≃
      Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B) × CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i :=
  ((binaryWindowFlatten q a B).symm.trans (binaryCellSplit q a i)).trans
    (Equiv.prodCongr (smallCellFlatten q a B) (Equiv.refl _))

theorem qubitCellSplit_flat (q a : ℕ) {B : ℕ} (i : Fin (2*B+1)) (b : BinaryWindow q a B) :
    qubitCellSplit q a i (binaryWindowFlatten q a B b) =
      (smallCellFlatten q a B (binaryCellSplit q a i b).1,(binaryCellSplit q a i b).2) := by
  change Equiv.prodCongr (smallCellFlatten q a B) (Equiv.refl _)
    (binaryCellSplit q a i ((binaryWindowFlatten q a B).symm (binaryWindowFlatten q a B b))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem qubitCellSplit_read (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (j : Fin (smallCellQubits q a B)) :
    (qubitCellSplit q a i b).1 j = b (smallCellWires q a i j) := by
  have he := smallCellWires_read q a i ((binaryWindowFlatten q a B).symm b) j
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

noncomputable def selectedQubitGate {q a B : ℕ} (i : Fin (2*B+1))
    (T : Matrix (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) ℂ :=
  injectionFrame (qubitCellSplit q a i).symm *
    (T ⊗ₖ (1 : Matrix (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
      (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i) ℂ)) * (injectionFrame (qubitCellSplit q a i).symm).conjTranspose

theorem selectedQubitGate_entry {q a B : ℕ} (i : Fin (2*B+1))
    (T : Matrix (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ)
    (x y : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) :
    selectedQubitGate i T x y = T (qubitCellSplit q a i x).1 (qubitCellSplit q a i y).1 *
      if (qubitCellSplit q a i x).2 = (qubitCellSplit q a i y).2 then 1 else 0 := by
  have he := injectionFrame_equiv_conjugate_apply (qubitCellSplit q a i).symm
    (T ⊗ₖ (1 : Matrix (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
      (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i) ℂ))
    (qubitCellSplit q a i x) (qubitCellSplit q a i y)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at he
  exact he

theorem Rule.binaryCanonicalGate_selected_entry {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B)
    (x y : BinaryWindow q a B) :
    selectedQubitGate i.val (R.smallCellQubitGate i) (binaryWindowFlatten q a B x) (binaryWindowFlatten q a B y) =
      R.binaryCanonicalGate i x y := by
  rw [selectedQubitGate_entry, qubitCellSplit_flat, qubitCellSplit_flat]
  simp only [Rule.smallCellQubitGate, injectionFrame_equiv_conjugate_apply]
  exact (R.binaryCanonicalGate_entry i x y).symm

theorem Rule.binaryCanonicalGate_selected {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    binaryWindowFlattenMatrix q a B * R.binaryCanonicalGate i * (binaryWindowFlattenMatrix q a B).conjTranspose =
      selectedQubitGate i.val (R.smallCellQubitGate i) := by
  ext x y
  obtain ⟨x,rfl⟩ := (binaryWindowFlatten q a B).surjective x
  obtain ⟨y,rfl⟩ := (binaryWindowFlatten q a B).surjective y
  rw [binaryWindowFlattenMatrix, injectionFrame_equiv_conjugate_apply,
      R.binaryCanonicalGate_selected_entry]

theorem qubitCellSplit_rest_read (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B))
    (r : {j : Fin (2*B+1) // j ≠ i}) (k : Fin (finiteQubits a)) :
    (qubitCellSplit q a i b).2 r k =
      b (Fin.natAdd (headQubits B + finiteQubits q) (finProdFinEquiv (r.val,k))) := by
  obtain ⟨b,rfl⟩ := (binaryWindowFlatten q a B).surjective b
  rw [qubitCellSplit_flat]
  change b.2.2 r.val k = (Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm
    ((Qatlib.Foundations.PureStateMath.regAppendEquiv _ _).symm (b.1,b.2.1),tapeBitsEquiv _ _ b.2.2)
      (Fin.natAdd _ (finProdFinEquiv (r.val,k)))
  rw [regJoin_suffix]
  change b.2.2 r.val k = Function.uncurry b.2.2 (finProdFinEquiv.symm (finProdFinEquiv (r.val,k)))
  rw [Equiv.symm_apply_apply]
  rfl

theorem smallCellWires_ne_rest (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (r : {j : Fin (2*B+1) // j ≠ i}) (k : Fin (finiteQubits a)) (j : Fin (smallCellQubits q a B)) :
    Fin.natAdd (headQubits B + finiteQubits q) (finProdFinEquiv (r.val,k)) ≠ smallCellWires q a i j := by
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · rw [smallCellWires_prefix]
    intro h
    have he := congrArg Fin.val h
    change headQubits B + finiteQubits q + (finProdFinEquiv (r.val,k)).val = l.val at he
    have hl := l.isLt
    omega
  · rw [smallCellWires_symbol]
    intro h
    have hp : finProdFinEquiv (r.val,k) = finProdFinEquiv (i,l) := by
      apply Fin.ext
      have he := congrArg Fin.val h
      change headQubits B + finiteQubits q + (finProdFinEquiv (r.val,k)).val =
        headQubits B + finiteQubits q + (finProdFinEquiv (i,l)).val at he
      omega
    exact r.property (congrArg Prod.fst (finProdFinEquiv.injective hp))

theorem qubitCellSplit_update (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (b : Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) (j : Fin (smallCellQubits q a B)) (v : Bool) :
    qubitCellSplit q a i (Function.update b (smallCellWires q a i j) v) =
      (Function.update (qubitCellSplit q a i b).1 j v,(qubitCellSplit q a i b).2) := by
  apply Prod.ext
  · change (qubitCellSplit q a i (Function.update b (smallCellWires q a i j) v)).1 =
      Function.update (qubitCellSplit q a i b).1 j v
    funext k
    rw [qubitCellSplit_read]
    by_cases hk : k = j
    · subst k
      simp
    · rw [Function.update_of_ne (fun h => hk ((smallCellWires q a i).injective h)), Function.update_of_ne hk,
        qubitCellSplit_read]
  · change (qubitCellSplit q a i (Function.update b (smallCellWires q a i j) v)).2 = (qubitCellSplit q a i b).2
    funext r k
    rw [qubitCellSplit_rest_read]
    have hn := smallCellWires_ne_rest q a i r k j
    exact (Function.update_of_ne hn v b).trans (qubitCellSplit_rest_read q a i b r k).symm

theorem qubitCellJoin_update (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (x : Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
    (j : Fin (smallCellQubits q a B)) (v : Bool) :
    Function.update ((qubitCellSplit q a i).symm (x,r)) (smallCellWires q a i j) v =
      (qubitCellSplit q a i).symm (Function.update x j v,r) := by
  apply (qubitCellSplit q a i).injective
  rw [qubitCellSplit_update, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem qubitCellJoin_read (q a : ℕ) {B : ℕ} (i : Fin (2*B+1))
    (x : Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
    (j : Fin (smallCellQubits q a B)) :
    (qubitCellSplit q a i).symm (x,r) (smallCellWires q a i j) = x j := by
  have he := qubitCellSplit_read q a i ((qubitCellSplit q a i).symm (x,r)) j
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

theorem injectionFrame_ket {H K : Type*} [Fintype K] [DecidableEq H] [DecidableEq K]
    (f : K → H) (x : K) : injectionFrame f *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (f x) := by
  ext y
  simp [Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct, injectionFrame,
      mul_ite]

def cellWireGate {q a B : ℕ} (i : Fin (2*B+1)) :
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (smallCellQubits q a B) → Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (binaryWindowQubits q a B)
  | .inl (j,U) => .inl (smallCellWires q a i j,U)
  | .inr (c,t) => .inr (smallCellWires q a i c,smallCellWires q a i t)

theorem cellWireGate_legal {q a B : ℕ} (i : Fin (2*B+1))
    (g : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (smallCellQubits q a B)) (hg : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateLegal g) :
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateLegal (cellWireGate i g) := by
  cases g with
  | inl ju => exact hg
  | inr ct => exact fun h => hg ((smallCellWires q a i).injective h)

theorem selectedQubitGate_single {q a B : ℕ} (i : Fin (2*B+1))
    (T : Matrix (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ)
    (x : Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i) :
    selectedQubitGate i T *ᵥ Pi.single ((qubitCellSplit q a i).symm (x,r)) 1 =
      ∑ y, T y x • Pi.single ((qubitCellSplit q a i).symm (y,r)) 1 := by
  have he := frameUnitary_tensor_single (qubitCellSplit q a i).symm
    (qubitCellSplit q a i).symm.injective T x r
  have hh := injectionFrame_equiv_complete (qubitCellSplit q a i).symm
  simpa only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.frameUnitary, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
    hh, sub_self, zero_add] using! he

noncomputable def cellSliceEmbed {q a B : ℕ} (i : Fin (2*B+1))
    (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B))) :
    Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)) :=
  injectionFrame (fun x => (qubitCellSplit q a i).symm (x,r)) *ᵥ ψ

theorem cellWireGate_slice {q a B : ℕ} (i : Fin (2*B+1))
    (g : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (smallCellQubits q a B)) (hg : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateLegal g)
    (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i) (x : Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) :
    Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix (cellWireGate i g))
        (Qatlib.Foundations.PureStateMath.Ket ((qubitCellSplit q a i).symm (x,r))) =
      cellSliceEmbed i r (Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix g) (Qatlib.Foundations.PureStateMath.Ket x)) := by
  cases g with
  | inl ju =>
    rcases ju with ⟨j,U⟩
    simp only [cellWireGate, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_wireGate_ket,
      qubitCellJoin_read, qubitCellJoin_update]
    simp only [cellSliceEmbed, Matrix.mulVec_add, Matrix.mulVec_smul, injectionFrame_ket]
  | inr ct =>
    rcases ct with ⟨c,t⟩
    simp only [cellWireGate, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix]
    rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_cnotGate_ket _ _ _ (fun h => hg ((smallCellWires q a i).injective h)),
      Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_cnotGate_ket _ _ _ hg]
    simp only [qubitCellJoin_read, qubitCellJoin_update, cellSliceEmbed, injectionFrame_ket]

theorem ket_eq_single {H : Type*} [DecidableEq H] (x : H) : Qatlib.Foundations.PureStateMath.Ket x = Pi.single x 1 := by
  ext y
  simp [Qatlib.Foundations.PureStateMath.Ket, Pi.single_apply, eq_comm]

theorem cellSliceEmbed_sum {q a B : ℕ} (i : Fin (2*B+1))
    (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B))) :
    cellSliceEmbed i r ψ = ∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket ((qubitCellSplit q a i).symm (x,r)) := by
  ext b
  simp only [cellSliceEmbed, Matrix.mulVec, dotProduct, injectionFrame, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem selectedQubitGate_slice {q a B : ℕ} (i : Fin (2*B+1))
    (T : Matrix (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ)
    (x : Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (r : CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i) :
    selectedQubitGate i T *ᵥ Qatlib.Foundations.PureStateMath.Ket ((qubitCellSplit q a i).symm (x,r)) =
      cellSliceEmbed i r (T *ᵥ Qatlib.Foundations.PureStateMath.Ket x) := by
  rw [ket_eq_single, selectedQubitGate_single, cellSliceEmbed_sum]
  simp only [ket_eq_single, Matrix.mulVec_single_one]
  rfl

theorem cellWireGate_matrix {q a B : ℕ} (i : Fin (2*B+1))
    (g : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (smallCellQubits q a B)) (hg : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateLegal g) :
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix (cellWireGate i g) =
      selectedQubitGate i (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix g) := by
  apply Matrix.ext_of_mulVec_single
  intro b
  obtain ⟨⟨x,r⟩,rfl⟩ := (qubitCellSplit q a i).symm.surjective b
  have he := cellWireGate_slice i g hg r x
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate] at he
  rw [← selectedQubitGate_slice i (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionGateMatrix g) x r] at he
  simpa only [ket_eq_single] using! he

theorem selectedQubitGate_mul {q a B : ℕ} (i : Fin (2*B+1))
    (S T : Matrix (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) (Qatlib.Foundations.PureStateMath.Reg (smallCellQubits q a B)) ℂ) :
    selectedQubitGate i (S*T) = selectedQubitGate i S * selectedQubitGate i T := by
  have he : (injectionFrame (qubitCellSplit q a i).symm).conjTranspose * injectionFrame (qubitCellSplit q a i).symm = 1 :=
    injectionFrame_isometry _ (qubitCellSplit q a i).symm.injective
  simp only [selectedQubitGate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (injectionFrame (qubitCellSplit q a i).symm).conjTranspose, he,
      Matrix.one_mul]
  rw [← Matrix.mul_assoc (S ⊗ₖ (1 : Matrix (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i)
    (CellRest (Qatlib.Foundations.PureStateMath.Reg (finiteQubits a)) i) ℂ)), ← Matrix.mul_kronecker_mul, Matrix.one_mul]

@[simp] theorem selectedQubitGate_one {q a B : ℕ} (i : Fin (2*B+1)) :
    selectedQubitGate (q := q) (a := a) i 1 = 1 := by
  rw [selectedQubitGate, Matrix.one_kronecker_one, Matrix.mul_one]
  exact injectionFrame_equiv_complete _

theorem cellWireProgram_matrix {q a B : ℕ} (i : Fin (2*B+1))
    (gs : List (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (smallCellQubits q a B))) (hgs : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionLegal gs) :
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix (gs.map (cellWireGate i)) =
      selectedQubitGate i (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix gs) := by
  induction gs with
  | nil => simp [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix]
  | cons g gs ih =>
    rw [List.map_cons, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix,
      ih (fun k hk => hgs k (List.mem_cons_of_mem g hk)), cellWireGate_matrix i g (hgs g List.mem_cons_self),
      selectedQubitGate_mul]

theorem cellWireProgram_resources {q a B : ℕ} (i : Fin (2*B+1))
    (gs : List (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (smallCellQubits q a B))) (hgs : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionLegal gs) :
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionLegal (gs.map (cellWireGate i)) ∧
      (gs.map (cellWireGate i)).length = gs.length ∧
      Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile (gs.map (cellWireGate i))) = 0 ∧
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile (gs.map (cellWireGate i))) = gs.length := by
  refine ⟨?_,List.length_map _,Qatlib.Concepts.GateVocabulary.LocalReflectionGates.queryCount_reflectionCompile _,?_⟩
  · intro g hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    exact cellWireGate_legal i z (hgs z hz)
  · rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.gateCount_reflectionCompile, List.length_map]

theorem smallCellQubits_pos (q a B : ℕ) : 1 ≤ smallCellQubits q a B := by
  have hh : 0 < Nat.clog 2 ((2*B+1)*2) := Nat.clog_pos (by decide) (by omega)
  change 1 ≤ Nat.clog 2 ((2*B+1)*2) + finiteQubits q + finiteQubits a
  omega

theorem smallCellBits_card (q a B : ℕ) : Fintype.card (SmallCellBits q a B) = 2 ^ smallCellQubits q a B :=
  (Fintype.card_congr (smallCellFlatten q a B)).trans (Qatlib.Foundations.PureStateMath.card_reg _)

theorem smallCellQubits_bound (q a B : ℕ) : smallCellQubits q a B ≤ 2*(2*B+1)+q+a := by
  have hh : headQubits B ≤ 2*(2*B+1) := by
    exact (finiteQubits_le ((2*B+1)*2)).trans (Nat.le_of_eq (Nat.mul_comm _ _))
  exact Nat.add_le_add (Nat.add_le_add hh (finiteQubits_le q)) (finiteQubits_le a)

def smallCellGateBudget (q a B : ℕ) : ℕ :=
  768*(smallCellQubits q a B+1)^3*4^smallCellQubits q a B

theorem smallCellGateBudget_bound (q a B : ℕ) : smallCellGateBudget q a B ≤
    768*(2*(2*B+1)+q+a+1)^3 * (8*(2*(2*B+1)+1)*(q+1)*(a+1))^2 := by
  have hd := smallCellBits_card_bound q a B
  rw [smallCellBits_card] at hd
  have hp : 4 ^ smallCellQubits q a B = (2 ^ smallCellQubits q a B)^2 := by
    change (2^2)^smallCellQubits q a B = (2^smallCellQubits q a B)^2
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2]
  have hb : 4 ^ smallCellQubits q a B ≤ (8*(2*(2*B+1)+1)*(q+1)*(a+1))^2 := by
    rw [hp]
    exact Nat.pow_le_pow_left hd 2
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 768
    (Nat.pow_le_pow_left (Nat.add_le_add_right (smallCellQubits_bound q a B) 1) 3)) hb

theorem Rule.binaryCanonicalGate_continuous_table {q a B : ℕ} (R : Rule (Fin q) (Fin a))
    (h : R.GloballyWellformed) (i : WindowCenter B) :
    ∃ gs : List (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.ReflectionGate (binaryWindowQubits q a B)),
      Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionLegal gs ∧ gs.length ≤ smallCellGateBudget q a B ∧
      Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile gs) = 0 ∧
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile gs) = gs.length ∧
      ∀ ψ : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg (binaryWindowQubits q a B)),
        Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionCompile gs) ψ =
          (binaryWindowFlattenMatrix q a B * R.binaryCanonicalGate i * (binaryWindowFlattenMatrix q a B).conjTranspose) *ᵥ ψ := by
  obtain ⟨gs,hgs,hlen,_,_,hrun⟩ := Qatlib.Concepts.CircuitImpl.MultiControl.known_unitary_no_work_actual_local_synthesis
    (smallCellQubits q a B) (smallCellQubits_pos q a B) (R.smallCellQubitGate i) (R.smallCellQubitGate_unitary h i)
  have hm : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionProgramMatrix gs = R.smallCellQubitGate i := by
    apply Matrix.ext_of_mulVec_single
    intro x
    have he := hrun (Pi.single x 1)
    rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.run_reflectionCompile] at he
    exact he
  refine ⟨gs.map (cellWireGate i.val), (cellWireProgram_resources i.val gs hgs).1, ?_,
    Qatlib.Concepts.GateVocabulary.LocalReflectionGates.queryCount_reflectionCompile _, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.gateCount_reflectionCompile _, ?_⟩
  · simpa only [List.length_map, smallCellGateBudget] using! hlen
  · intro ψ
    rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.run_reflectionCompile, cellWireProgram_matrix i.val gs hgs, hm,
      R.binaryCanonicalGate_selected]
    rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeMachineCompletion

open Qatlib
open scoped BigOperators ComplexConjugate Classical Matrix Kronecker

def headFlipPair {B : ℕ} (j : Fin (2*B+1)) : WindowHead B × WindowHead B := ((false, j), (true, j))

def headFlipWord (B : ℕ) : List (WindowHead B × WindowHead B) :=
  (List.finRange (2*B+1)).map headFlipPair

theorem headFlipWord_length (B : ℕ) : (headFlipWord B).length = 2*B+1 := by
  simp [headFlipWord]

theorem swapWordEval_headFlipList {B : ℕ} (l : List (Fin (2*B+1))) (p : Bool) (k : Fin (2*B+1))
    (hnodup : l.Nodup) :
    swapWordEval (l.map headFlipPair) (p, k) =
      if k ∈ l then (!p, k) else (p, k) := by
  induction l generalizing p k with
  | nil => simp [swapWordEval]
  | cons j l ih =>
    have hnotj : j ∉ l := (List.nodup_cons.mp hnodup).1
    have htail : l.Nodup := (List.nodup_cons.mp hnodup).2
    rw [List.map_cons, swapWordEval, Equiv.trans_apply]
    simp only [headFlipPair]
    by_cases hkj : k = j
    · subst k
      cases p with
      | false =>
        rw [Equiv.swap_apply_left]
        have hinner := ih (hnodup := htail) true j
        rw [hinner, if_neg hnotj, if_pos (by simp : j ∈ j :: l)]
        rfl
      | true =>
        rw [Equiv.swap_apply_right]
        have hinner := ih (hnodup := htail) false j
        rw [hinner, if_neg hnotj, if_pos (by simp : j ∈ j :: l)]
        rfl
    · have h1 : (p, k) ≠ (false, j) := by
        intro hc
        exact hkj (congrArg Prod.snd hc)
      have h2 : (p, k) ≠ (true, j) := by
        intro hc
        exact hkj (congrArg Prod.snd hc)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hinner := ih (hnodup := htail) p k
      rw [hinner]
      simp [hkj]

theorem headFlipWord_eval (B : ℕ) (h : WindowHead B) :
    swapWordEval (headFlipWord B) h = (!h.1, h.2) := by
  rcases h with ⟨p, k⟩
  rw [headFlipWord, swapWordEval_headFlipList (List.finRange (2*B+1)) p k
    (List.nodup_finRange (2*B+1)), if_pos (List.mem_finRange k)]

def headFlipBitWord (B : ℕ) :
    List (Qatlib.Foundations.PureStateMath.Reg (headQubits B) × Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :=
  (headFlipWord B).map (fun xy => (headToBits B xy.1, headToBits B xy.2))

theorem headFlipBitWord_length (B : ℕ) : (headFlipBitWord B).length = 2*B+1 := by
  rw [headFlipBitWord, List.length_map, headFlipWord_length]

theorem headFlipBitWord_eval (B : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :
    swapWordEval (headFlipBitWord B) b = headFlipBits B b := by
  cases hb : headFromBits B b with
  | none =>
    rw [headFlipBits, hb]
    apply swapWordEval_map_outside
    intro x hx
    rw [hx, headFromBits_toBits] at hb
    contradiction
  | some h =>
    rw [headFlipBits, hb, ← headToBits_fromBits hb]
    calc
      swapWordEval (headFlipBitWord B) (headToBits B h)
          = headToBits B (swapWordEval (headFlipWord B) h) :=
            swapWordEval_map (headToBits B) (headToBits_injective B) (headFlipWord B) h
      _ = headToBits B (!h.1, h.2) := by rw [headFlipWord_eval]

theorem headFlipBitsEquiv_apply (B : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :
    headFlipBitsEquiv B b = headFlipBits B b := rfl

theorem headFlipBitWord_matrix (B : ℕ) :
    swapWordMatrix (headFlipBitWord B) = injectionFrame (headFlipBitsEquiv B) := by
  rw [swapWordMatrix_eval]
  congr 1
  funext b
  exact headFlipBitWord_eval B b

theorem headFlipBitWord_unitary (B : ℕ) :
    swapWordMatrix (headFlipBitWord B) ∈
      Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) ℂ := swapWordMatrix_unitary _

theorem headFlipBitWord_matrix_single (B : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :
    swapWordMatrix (headFlipBitWord B) *ᵥ Pi.single b 1 = Pi.single (headFlipBits B b) 1 := by
  rw [swapWordMatrix_single, headFlipBitWord_eval]

theorem headFlipBitWord_illegal (B : ℕ) (b : Qatlib.Foundations.PureStateMath.Reg (headQubits B))
    (hb : headFromBits B b = none) :
    swapWordMatrix (headFlipBitWord B) *ᵥ Pi.single b 1 = Pi.single b 1 := by
  rw [swapWordMatrix_single, headFlipBitWord_eval, headFlipBits, hb]

abbrev WindowSpectators (q a B : ℕ) :=
  Qatlib.Foundations.PureStateMath.Reg (finiteQubits q) × (Fin (2*B+1) → Qatlib.Foundations.PureStateMath.Reg (finiteQubits a))

noncomputable def binaryWindowFlipWordMatrix (q a B : ℕ) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  injectionFrame (Equiv.prodCongr (swapWordEval (headFlipBitWord B))
    (Equiv.refl (WindowSpectators q a B)))

theorem binaryWindowFlipWordMatrix_eq (q a B : ℕ) :
    binaryWindowFlipWordMatrix q a B = binaryWindowFlip q a B := by
  unfold binaryWindowFlipWordMatrix binaryWindowFlip
  have hprod : Equiv.prodCongr (swapWordEval (headFlipBitWord B))
      (Equiv.refl (WindowSpectators q a B))
      = Equiv.prodCongr (headFlipBitsEquiv B) (Equiv.refl (WindowSpectators q a B)) := by
    apply Equiv.ext
    intro x
    rcases x with ⟨h, s⟩
    apply Prod.ext
    · exact headFlipBitWord_eval B h
    · rfl
  rw [hprod]
  rfl

theorem binaryWindowFlipWordMatrix_unitary (q a B : ℕ) :
    binaryWindowFlipWordMatrix q a B ∈ Matrix.unitaryGroup (BinaryWindow q a B) ℂ := by
  rw [binaryWindowFlipWordMatrix_eq]
  exact binaryWindowFlip_unitary q a B

theorem binaryWindowFlipWordMatrix_spectators (q a B : ℕ)
    (h : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (s : WindowSpectators q a B) :
    binaryWindowFlipWordMatrix q a B *ᵥ Pi.single (h, s) 1 =
      Pi.single (headFlipBits B h, s) 1 := by
  rw [binaryWindowFlipWordMatrix, injectionFrame_single]
  have hprod : (Equiv.prodCongr (swapWordEval (headFlipBitWord B))
      (Equiv.refl (WindowSpectators q a B))) (h, s) = (headFlipBits B h, s) := by
    apply Prod.ext
    · exact headFlipBitWord_eval B h
    · rfl
  rw [hprod]

theorem binaryWindowFlipWordMatrix_state (q a B : ℕ) (v : BinaryWindow q a B → ℂ)
    (y : BinaryWindow q a B) :
    (binaryWindowFlipWordMatrix q a B *ᵥ v) y =
      v ((Equiv.prodCongr (swapWordEval (headFlipBitWord B))
        (Equiv.refl (WindowSpectators q a B))).symm y) := by
  rw [binaryWindowFlipWordMatrix]
  exact injectionFrame_equiv_mulVec _ v y

theorem binaryWindowFlipWordMatrix_illegal (q a B : ℕ)
    (h : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (s : WindowSpectators q a B)
    (hh : headFromBits B h = none) :
    binaryWindowFlipWordMatrix q a B *ᵥ Pi.single (h, s) 1 = Pi.single (h, s) 1 := by
  rw [binaryWindowFlipWordMatrix, injectionFrame_single]
  have hfix : swapWordEval (headFlipBitWord B) h = h := by
    rw [headFlipBitWord_eval, headFlipBits, hh]
  have hprod : (Equiv.prodCongr (swapWordEval (headFlipBitWord B))
      (Equiv.refl (WindowSpectators q a B))) (h, s) = (h, s) := by
    apply Prod.ext
    · exact hfix
    · rfl
  rw [hprod]

noncomputable def binaryHeadRouteWordMatrix (q a B : ℕ) (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  injectionFrame (Equiv.prodCongr (swapWordEval (cellHeadBitRouteWord i))
    (Equiv.refl (WindowSpectators q a B)))

theorem binaryHeadRouteWordMatrix_eq (q a B : ℕ) (i : WindowCenter B) :
    binaryHeadRouteWordMatrix q a B i = binaryHeadRouteWindowMatrix q a i := by
  unfold binaryHeadRouteWordMatrix binaryHeadRouteWindowMatrix
  have hprod : Equiv.prodCongr (swapWordEval (cellHeadBitRouteWord i))
      (Equiv.refl (WindowSpectators q a B))
      = Equiv.prodCongr (cellHeadBitRoute i) (Equiv.refl (WindowSpectators q a B)) := by
    apply Equiv.ext
    intro x
    rcases x with ⟨h, s⟩
    apply Prod.ext
    · rfl
    · rfl
  rw [hprod]
  rfl

noncomputable def binaryHeadRouteReverseWordMatrix (q a B : ℕ) (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  injectionFrame (Equiv.prodCongr (swapWordEval (cellHeadBitRouteReverseWord i))
    (Equiv.refl (WindowSpectators q a B)))

set_option maxHeartbeats 800000 in

theorem binaryHeadRouteReverseWordMatrix_eq (q a B : ℕ) (i : WindowCenter B) :
    binaryHeadRouteReverseWordMatrix q a B i = (binaryHeadRouteWindowMatrix q a i).conjTranspose := by
  unfold binaryHeadRouteReverseWordMatrix binaryHeadRouteWindowMatrix
  have hsym : Equiv.prodCongr (swapWordEval (cellHeadBitRouteReverseWord i))
      (Equiv.refl (WindowSpectators q a B))
      = (Equiv.prodCongr (cellHeadBitRoute i) (Equiv.refl (WindowSpectators q a B))).symm := by
    apply Equiv.ext
    intro x
    rcases x with ⟨h, s⟩
    apply Prod.ext
    · exact congrArg (fun e => e h) (cellHeadBitRouteReverseWord_eval i)
    · rfl
  rw [hsym, injectionFrame_equiv_symm]
  rfl

def cellRouteWord (B : ℕ) (i : WindowCenter B) :
    List (Qatlib.Foundations.PureStateMath.Reg (headQubits B) × Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :=
  cellHeadBitRouteWord i ++ cellHeadBitRouteReverseWord i

theorem cellRouteWord_length (B : ℕ) (i : WindowCenter B) : (cellRouteWord B i).length = 8 := by
  rw [cellRouteWord, List.length_append, cellHeadBitRouteWord_length,
    cellHeadBitRouteReverseWord_length]

theorem cellRouteWord_eval (B : ℕ) (i : WindowCenter B) (b : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) :
    swapWordEval (cellRouteWord B i) b = b := by
  rw [cellRouteWord, swapWordEval_append, cellHeadBitRouteReverseWord_eval]
  show (cellHeadBitRoute i).symm ((cellHeadBitRoute i) b) = b
  exact Equiv.symm_apply_apply _ _

theorem cellRouteWord_eq_refl (B : ℕ) (i : WindowCenter B) :
    swapWordEval (cellRouteWord B i) = Equiv.refl (Qatlib.Foundations.PureStateMath.Reg (headQubits B)) := by
  rw [cellRouteWord, swapWordEval_append, cellHeadBitRouteReverseWord_eval]
  apply Equiv.ext
  intro b
  show (cellHeadBitRoute i).symm ((cellHeadBitRoute i) b) = b
  exact Equiv.symm_apply_apply _ _

theorem cellRouteWord_matrix (B : ℕ) (i : WindowCenter B) :
    swapWordMatrix (cellRouteWord B i) = 1 := by
  rw [swapWordMatrix_eval, cellRouteWord_eq_refl]
  ext x y
  simp [injectionFrame, Matrix.one_apply]

noncomputable def binaryCellWordMatrix (q a B : ℕ) (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    Matrix (BinaryWindow q a B) (BinaryWindow q a B) ℂ :=
  (binaryHeadRouteReverseWordMatrix q a B i) * R.binaryCanonicalGate i *
    (binaryHeadRouteWordMatrix q a B i)

theorem binaryCellWordMatrix_eq (q a B : ℕ) (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    binaryCellWordMatrix q a B R i = R.binaryCellGate i := by
  unfold binaryCellWordMatrix Rule.binaryCellGate
  rw [binaryHeadRouteReverseWordMatrix_eq, binaryHeadRouteWordMatrix_eq]

theorem binaryHeadRouteWordMatrix_state (q a B : ℕ) (i : WindowCenter B)
    (v : BinaryWindow q a B → ℂ) (y : BinaryWindow q a B) :
    (binaryHeadRouteWordMatrix q a B i *ᵥ v) y =
      v ((Equiv.prodCongr (cellHeadBitRoute i)
        (Equiv.refl (WindowSpectators q a B))).symm y) := by
  rw [binaryHeadRouteWordMatrix]
  exact injectionFrame_equiv_mulVec _ v y

theorem binaryHeadRouteWordMatrix_spectators (q a B : ℕ) (i : WindowCenter B)
    (h : Qatlib.Foundations.PureStateMath.Reg (headQubits B)) (s : WindowSpectators q a B) :
    binaryHeadRouteWordMatrix q a B i *ᵥ Pi.single (h, s) 1 =
      Pi.single (cellHeadBitRoute i h, s) 1 := by
  rw [binaryHeadRouteWordMatrix, injectionFrame_single]
  rfl

theorem windowStepCell_eq_word (q a B : ℕ) (R : Rule (Fin q) (Fin a)) (i : WindowCenter B) :
    WindowOp.binaryMatrix R (.cell i : WindowOp B) = binaryCellWordMatrix q a B R i := by
  rw [binaryCellWordMatrix_eq]
  rfl

theorem windowStepFlip_eq_word (q a B : ℕ) (R : Rule (Fin q) (Fin a)) :
    WindowOp.binaryMatrix R (.flip : WindowOp B) = binaryWindowFlipWordMatrix q a B := by
  rw [binaryWindowFlipWordMatrix_eq]
  rfl

theorem binaryWordMatrix_append {q a B : ℕ} (R : Rule (Fin q) (Fin a)) (l r : List (WindowOp B)) :
    R.binaryWordMatrix (l ++ r) = R.binaryWordMatrix r * R.binaryWordMatrix l := by
  induction l with
  | nil => simp [Rule.binaryWordMatrix]
  | cons a l ih =>
    simp only [List.cons_append, Rule.binaryWordMatrix, ih, Matrix.mul_assoc]

theorem binaryStepWordMatrix_eq (q a B : ℕ) (R : Rule (Fin q) (Fin a)) :
    R.binaryWordMatrix (windowStepOps B) =
      binaryWindowFlipWordMatrix q a B * R.binaryWordMatrix ((windowCenters B).map WindowOp.cell) := by
  rw [windowStepOps, binaryWordMatrix_append, Rule.binaryWordMatrix]
  simp [Rule.binaryWordMatrix, windowStepFlip_eq_word]

theorem binaryStepCells_two (q a B : ℕ) (R : Rule (Fin q) (Fin a)) (i j : WindowCenter B) :
    R.binaryWordMatrix [WindowOp.cell i, WindowOp.cell j] =
      binaryCellWordMatrix q a B R j * binaryCellWordMatrix q a B R i := by
  rw [Rule.binaryWordMatrix, Rule.binaryWordMatrix]
  simp [Rule.binaryWordMatrix, windowStepCell_eq_word]

def cellRouteSwapCount : ℕ := 8

def windowStepSwapCount (B : ℕ) : ℕ :=
  (2*B-1) * cellRouteSwapCount + (2*B+1)

theorem windowStepSwapCount_bound (B : ℕ) : windowStepSwapCount B ≤ 18*B + 1 := by
  unfold windowStepSwapCount cellRouteSwapCount
  omega

def windowWordSwapCount (B t : ℕ) : ℕ := t * windowStepSwapCount B

theorem windowWordSwapCount_bound (B t : ℕ) : windowWordSwapCount B t ≤ t * (18*B + 1) := by
  unfold windowWordSwapCount
  exact Nat.mul_le_mul (Nat.le_refl t) (windowStepSwapCount_bound B)

def windowStepGateCount (q a B : ℕ) : ℕ :=
  windowStepSwapCount B + (2*B-1) * smallCellGateBudget q a B

theorem windowStepGateCount_bound (q a B : ℕ) :
    windowStepGateCount q a B ≤ (18*B+1) + (2*B+1) * smallCellGateBudget q a B := by
  have h1 : 2*B-1 ≤ 2*B+1 := by omega
  have hcells : (2*B-1) * smallCellGateBudget q a B
      ≤ (2*B+1) * smallCellGateBudget q a B := by
    calc
      (2*B-1) * smallCellGateBudget q a B = smallCellGateBudget q a B * (2*B-1) := by
        rw [Nat.mul_comm]
      _ ≤ smallCellGateBudget q a B * (2*B+1) := Nat.mul_le_mul_left _ h1
      _ = (2*B+1) * smallCellGateBudget q a B := by rw [Nat.mul_comm]
  unfold windowStepGateCount
  exact Nat.add_le_add (Nat.le_trans (windowStepSwapCount_bound B) le_rfl) hcells

theorem windowStepGateCount_poly_bound (q a B : ℕ) :
    windowStepGateCount q a B ≤ (18*B+1) + (2*B+1) *
      (768*(2*(2*B+1)+q+a+1)^3 * (8*(2*(2*B+1)+1)*(q+1)*(a+1))^2) := by
  calc
    windowStepGateCount q a B ≤ (18*B+1) + (2*B+1) * smallCellGateBudget q a B :=
      windowStepGateCount_bound q a B
    _ ≤ (18*B+1) + (2*B+1) *
        (768*(2*(2*B+1)+q+a+1)^3 * (8*(2*(2*B+1)+1)*(q+1)*(a+1))^2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (2*B+1) (smallCellGateBudget_bound q a B))
        (18*B+1)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeMachineCompletion
