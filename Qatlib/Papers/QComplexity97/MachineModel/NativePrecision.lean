/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeQuantumMachineDefs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Precision accumulation with an initial discrepancy

The module proves error accumulation for complex linear isometries, retaining the initial
discrepancy as an explicit term. With a common initial state, the estimate reduces to the usual
`T * ε` bound.

An explicit unit complex phase gives normalized counterexamples when the initial states are
allowed to differ. `native_shift_precision_counter` realizes this phenomenon on finitely
supported native QTM states. See [BernsteinVazirani1997].

## Main statements

* `precision_with_initial_error`: bounds final error by the initial discrepancy plus Tε.
* `precision_common_initial`: recovers the common-initial-state bound.
* `native_shift_precision_counter`: constructs a native shift example violating the bound with
  the initial discrepancy omitted.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QComplexity97.MachineDefs

/-- For an isometry `U`, the stated one-step deviations give final error at most `‖φt 0 - φ 0‖ +
T * ε`. This makes the initial discrepancy explicit in the accumulation estimate associated
with Theorem 3.4.1 of [BernsteinVazirani1997]. -/
theorem precision_with_initial_error {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (U : E →ₗᵢ[ℂ] E) (φ φt : ℕ → E) (ε : ℝ) (T : ℕ)
    (hstep : ∀ i, i < T → φ (i+1) = U (φt i))
    (hdev : ∀ i, 0 < i → i ≤ T → ‖φ i - φt i‖ ≤ ε) :
    ‖φt T - U^[T] (φ 0)‖ ≤ ‖φt 0 - φ 0‖ + T*ε := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hstepT := hstep T (Nat.lt_succ_self T)
    have hidx : φt (T+1) - U^[T+1] (φ 0) =
        U (φt T - U^[T] (φ 0)) - (φ (T+1) - φt (T+1)) := by
      rw [Function.iterate_succ_apply', hstepT, map_sub]
      abel
    have hi := ih (fun i h => hstep i (Nat.lt_trans h (Nat.lt_succ_self T)))
      (fun i h0 h => hdev i h0 (Nat.le_trans h (Nat.le_succ T)))
    have hd := hdev (T+1) (Nat.succ_pos _) le_rfl
    rw [hidx]
    calc ‖U (φt T - U^[T] (φ 0)) - (φ (T+1) - φt (T+1))‖
        ≤ ‖U (φt T - U^[T] (φ 0))‖ + ‖φ (T+1) - φt (T+1)‖ := norm_sub_le _ _
      _ ≤ ‖φt 0 - φ 0‖ + (T:ℝ)*ε + ε := by rw [U.norm_map]; linarith
      _ = ‖φt 0 - φ 0‖ + ((T+1:ℕ):ℝ)*ε := by push_cast; ring

/-- With a common initial state, the stated deviations from isometric evolution accumulate to at
most `T * ε` after `T` steps. This is the common-initial-state form of Theorem 3.4.1 of
[BernsteinVazirani1997]. -/
theorem precision_common_initial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (U : E →ₗᵢ[ℂ] E) (φ φt : ℕ → E) (ε : ℝ) (T : ℕ)
    (h0 : φt 0 = φ 0)
    (hstep : ∀ i, i < T → φ (i+1) = U (φt i))
    (hdev : ∀ i, 0 < i → i ≤ T → ‖φ i - φt i‖ ≤ ε) :
    ‖φt T - U^[T] (φ 0)‖ ≤ T*ε := by
  simpa only [h0, sub_self, norm_zero, zero_add] using
    precision_with_initial_error U φ φt ε T hstep hdev

/-- The complex phase `(63 / 65 : ℝ) + (16 / 65 : ℝ) * Complex.I` used in the precision
counterexample. -/
private def smallPhase : ℂ := (63/65 : ℝ) + (16/65 : ℝ) * Complex.I

/-- The complex number `smallPhase` has norm one. -/
private theorem smallPhase_norm : ‖smallPhase‖ = 1 := by
  rw [Complex.norm_def]
  norm_num [smallPhase, Complex.normSq]

/-- The distance between one and `smallPhase` is at most `1 / 4`. -/
private theorem smallPhase_step : ‖1-smallPhase‖ ≤ (1/4:ℝ) := by
  have hs : Complex.normSq (1-smallPhase) = (4/65:ℝ) := by
    norm_num [smallPhase, Complex.normSq]
  rw [Complex.norm_def,hs]
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- The distance between `smallPhase ^ 2` and one is strictly greater than `1 / 4`. -/
private theorem smallPhase_twice : (1/4:ℝ) < ‖smallPhase^2-1‖ := by
  have hs : Complex.normSq (smallPhase^2-1) = (32/65:ℝ)^2 := by
    norm_num [smallPhase, Complex.normSq, pow_two, Complex.mul_re, Complex.mul_im]
  rw [Complex.norm_def,hs,Real.sqrt_sq (by norm_num : (0:ℝ)≤32/65)]
  norm_num

/-- Given the stated unit vector and scalar-stable predicate, there are normalized sequences
satisfying that predicate and the one-step deviation bound `1 / 4` whose final error exceeds
`1 / 4`. This construction allows a nonzero initial discrepancy. -/
theorem precision_positive_time_counter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (U : E →ₗᵢ[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (P : E → Prop) (hP : ∀ (z : ℂ) (v : E), P v → P (z • v))
    (hPψ : P ψ) (hPUψ : P (U ψ)) :
    ∃ φ φt : ℕ → E,
      (∀ i, P (φ i) ∧ P (φt i)) ∧
      (∀ i, ‖φ i‖ = 1 ∧ ‖φt i‖ = 1) ∧
      (∀ i, i < 1 → φ (i+1) = U (φt i)) ∧
      (∀ i, i ≤ 1 → ‖φ i-φt i‖ ≤ (1/4:ℝ)) ∧
      (1:ℕ) > 0 ∧ (1:ℝ)*(1/4) < ‖φt 1-U^[1] (φ 0)‖ := by
  let φ : ℕ → E := fun i => if i=0 then ψ else smallPhase • U ψ
  let φt : ℕ → E := fun i => if i=0 then smallPhase • ψ else smallPhase^2 • U ψ
  refine ⟨φ,φt,?_,?_,?_,?_,by decide,?_⟩
  · intro i
    by_cases hi : i=0
    · simpa only [φ,φt,hi,ite_true] using And.intro hPψ (hP smallPhase ψ hPψ)
    · simpa only [φ,φt,hi,ite_false] using
        And.intro (hP smallPhase (U ψ) hPUψ) (hP (smallPhase^2) (U ψ) hPUψ)
  · intro i
    by_cases hi : i=0 <;> simp [φ,φt,hi,norm_smul,smallPhase_norm,hψ,U.norm_map]
  · intro i hi
    have : i=0 := by omega
    subst i
    simp [φ,φt,map_smul]
  · intro i hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl|rfl
    · change ‖ψ-smallPhase • ψ‖ ≤ _
      have he : ψ-smallPhase • ψ = (1-smallPhase) • ψ := by rw [sub_smul,one_smul]
      rw [he, norm_smul, hψ, mul_one]
      exact smallPhase_step
    · change ‖smallPhase • U ψ-smallPhase^2 • U ψ‖ ≤ _
      rw [← sub_smul, norm_smul, U.norm_map, hψ, mul_one]
      have he : smallPhase-smallPhase^2 = smallPhase*(1-smallPhase) := by ring
      rw [he,norm_mul,smallPhase_norm,one_mul]
      exact smallPhase_step
  · change (1:ℝ)*(1/4) < ‖smallPhase^2 • U ψ-U ψ‖
    have he : smallPhase^2 • U ψ-U ψ = (smallPhase^2-1) • U ψ := by rw [sub_smul,one_smul]
    rw [he,norm_smul,U.norm_map,hψ,mul_one,one_mul]
    exact smallPhase_twice

open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- A native right-shift isometry possesses finitely supported normalized sequences satisfying
the stated one-step deviations of at most `1 / 4`, while the final error exceeds `1 / 4`.
This demonstrates the role of a common initial state in the estimate associated with Theorem
3.4.1 of [BernsteinVazirani1997]. -/
theorem native_shift_precision_counter :
    ∃ U : State Bool Unit () ≃ₗᵢ[ℂ] State Bool Unit (),
      (∀ c, U (ket c) = (shiftRule Bool Unit () .right).column c) ∧
      ∃ φ φt : ℕ → State Bool Unit (),
        (∀ i, Set.Finite {c | φ i c ≠ 0} ∧ Set.Finite {c | φt i c ≠ 0}) ∧
        (∀ i, ‖φ i‖ = 1 ∧ ‖φt i‖ = 1) ∧
        (∀ i, i < 1 → φ (i+1) = U (φt i)) ∧
        (∀ i, i ≤ 1 → ‖φ i-φt i‖ ≤ (1/4:ℝ)) ∧
        (1:ℕ) > 0 ∧ (1:ℝ)*(1/4) < ‖φt 1-U^[1] (φ 0)‖ := by
  obtain ⟨U,hU⟩ := shiftRule_globallyWellformed Bool Unit () .right
  refine ⟨U,hU,?_⟩
  let P : State Bool Unit () → Prop := fun v => Set.Finite {c | v c ≠ 0}
  have hsmul (z : ℂ) (v : State Bool Unit ()) (hv : P v) : P (z • v) := by
    apply hv.subset
    intro c hc
    change z * v c ≠ 0 at hc
    exact (mul_ne_zero_iff.mp hc).2
  have hket (c : Config Bool Unit ()) : P (ket c) := by
    apply (Set.finite_singleton c).subset
    intro d hd
    by_contra hn
    have hdne : d ≠ c := by simpa only [Set.mem_singleton_iff] using hn
    exact hd (by simp [ket,lp.single_apply,hdne])
  have hcolumn (c : Config Bool Unit ()) : P ((shiftRule Bool Unit () .right).column c) := by
    classical
    let slots : Finset (Config Bool Unit ()) := Finset.univ.image
      (fun t : Move × Bool × Unit => target c t.1 t.2.1 t.2.2)
    apply slots.finite_toSet.subset
    intro d hd
    by_contra hn
    have hx (t : Move × Bool × Unit) : target c t.1 t.2.1 t.2.2 ≠ d := by
      intro he
      apply hn
      exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,he⟩
    apply hd
    simp only [Rule.column,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro t _
    simp [ket,lp.single_apply,(hx t).symm]
  exact precision_positive_time_counter U.toLinearIsometry
    (ket (canonicalConfig () false ())) ((ket_orthonormal (Q:=Bool) ()).norm_eq_one _)
    P hsmul (hket _) (by
      change P (U (ket (canonicalConfig () false ())))
      rw [hU]
      exact hcolumn _)

end Qatlib.Papers.QComplexity97.MachineDefs
