/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux
public import Qatlib.Papers.QShannonWilde11.MainResults.QEntropy.SingularProbe
public import Qatlib.Papers.QShannonWilde11.MainResults.Recovery.WeakRecovery

@[expose] public section


/-! # A zero-function counterexample to the old logarithmic three-lines contract

The source theorem is about a bounded holomorphic function. Its norm estimate
survives zeros; the total real logarithm used in the old contract does not.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.Recovery.ContractProbe

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Papers.QShannonWilde11.MainResults.QEntropy.SingularProbe
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.ChannelTheory.Stinespring
open Filter Topology

/-- The zero holomorphic function satisfies all old strip bounds but violates
the logarithmic three-lines inequality. -/
theorem three_lines_zero_failure :
    let f : ℂ → ℂ := fun _ => 0
    let M : ℝ := 1 / 2
    let θ : ℝ := 1 / 2
    0 < M ∧
      DifferentiableOn ℂ f {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} ∧
      (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ C) ∧
      (∀ t : ℝ, ‖f (t * Complex.I)‖ ≤ M) ∧
      (∀ t : ℝ, ‖f (1 + t * Complex.I)‖ ≤ M) ∧
      0 ≤ θ ∧ θ ≤ 1 ∧
      ¬ Real.log ‖f (θ : ℂ)‖ ≤ (1 - θ) * Real.log M + θ * Real.log M := by
  dsimp
  refine ⟨by norm_num, differentiableOn_const _,
    ⟨0, by simp⟩, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h : Real.log ((1 : ℝ) / 2) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  simp only [norm_zero, Real.log_zero]
  linarith

/-- A midpoint pulse refutes the old interpolation claim with a freely supplied norm. -/
theorem interpolation_failure :
    let sn : Matrix (Fin 1) (Fin 1) ℂ → ℝ → ℝ := fun M _ => (M 0 0).re
    let G : ℝ → Matrix (Fin 1) (Fin 1) ℂ := fun t => if t = 1 / 2 then 1 else 0
    let p : ℝ → ℝ := fun _ => 1
    let θ : ℝ := 1 / 2
    0 ≤ θ ∧ θ ≤ 1 ∧ 1 ≤ p 0 ∧ 1 ≤ p 1 ∧
      1 / p θ = (1 - θ) / p 0 + θ / p 1 ∧
      ¬ sn (G θ) (p θ) ≤
        Real.rpow (sn (G 0) (p 0)) (1 - θ) * Real.rpow (sn (G 1) (p 1)) θ := by
  norm_num [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0), Matrix.one_apply]

/-- A free exponential core produces the constant one family, not the entropy loss. -/
theorem renyi_family_failure :
    let s := basisDensity 0
    let Dα : ℝ → ℝ := fun _ => 1
    let core : ℝ → ℝ := fun a => Real.exp (a - 1)
    (∀ a, a ≠ 1 → Dα a = (1 / (a - 1)) * Real.log (core a)) ∧
      ¬ Tendsto Dα (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds (relEntR s s - relEntR s s)) := by
  dsimp
  constructor
  · intro a ha
    rw [Real.log_exp, one_div, inv_mul_cancel₀ (sub_ne_zero.mpr ha)]
  · intro h
    have hz : Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds (0 : ℝ)) := by
      simpa only [sub_self] using h
    have heq : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
    norm_num at heq

/-- A genuine replacement channel refutes equality conditions for an arbitrary recovery. -/
theorem arbitrary_recovery_failure :
    let ρ := basisDensity 0
    let σ := basisDensity 1
    let R : ℝ → QChannel 2 2 := fun _ => ofPhyslib (CPTPMap.replacement (state σ))
    ¬ (relEntR ρ ρ = relEntR ρ ρ ↔ ∀ t, (R t).map ρ.val = ρ.val) := by
  dsimp
  intro h
  have hm : (basisDensity 1).val =
      (ofPhyslib (CPTPMap.replacement (state (basisDensity 1)))).map (basisDensity 0).val := by
    simpa using CPTPMap.mat_coe_eq_apply_mat
      (CPTPMap.replacement (state (basisDensity 1))) (state (basisDensity 0))
  exact basis_distinct (hm.trans (h.mp rfl 0)).symm

end Qatlib.Papers.QShannonWilde11.MainResults.Recovery.ContractProbe
