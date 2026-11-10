/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21

theorem actual_assumption21 (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ r≤T, s r ∈ Set.Icc (0:ℝ) 1) :
    ∃ K : ℝ, 0<K ∧
      (∀ t≤T, fCoord s t (fun _ => 0)=0) ∧
      (∀ t≤T, ∀ u v : Fin (t+1) → ℝ,
        |fCoord s t u-fCoord s t v|≤K*Real.sqrt (∑ a, (u a-v a)^2)) ∧
      (∀ t≤T, ∀ (h h' : ℝ) (u v : Fin (t+1) → ℝ),
        |FCoord (s t) h u-FCoord (s t) h' v|≤K*
          Real.sqrt ((h-h')^2+∑ a, (u a-v a)^2)) := by
  refine ⟨2*Real.sqrt (T:ℝ)+(1+4/27), by positivity, ?_, ?_, ?_⟩
  · intro t _
    exact fCoord_zero s t
  · intro t ht u v
    exact (fCoord_lipschitz_l2 s T t ht hs u v).trans
      (mul_le_mul_of_nonneg_right (by linarith : 2*Real.sqrt (T:ℝ)≤2*Real.sqrt (T:ℝ)+(1+4/27)) (by positivity))
  · intro t ht h h' u v
    exact (FCoord_lipschitz_l2 (s t) (hs t ht) h h' u v).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg (T:ℝ)] :
        (1+4/27:ℝ)≤2*Real.sqrt (T:ℝ)+(1+4/27)) (by positivity))

theorem catalyst_attained : (2/3:ℝ)^2*(1-2/3)=4/27 := by norm_num

theorem actual_initial_coordinate {r N : ℕ} (M : ℝ)
    (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) :
    ampHistory M J seed s t 0=fun i => clip M (seed i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Fin.snoc (α:=fun _ : Fin (t+2) => Fin N → ℝ) (ampHistory M J seed s t) (ampNext M J s t (ampHistory M J seed s t))
      ((0:Fin (t+1)).castSucc)=_
    rw [Fin.snoc_castSucc]
    exact ih

theorem bounded_initial_coordinate {r N : ℕ} (M : ℝ)
    (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (hseed : ∀ i, seed i ∈ Set.Icc (-M) M) (s : ℕ → ℝ) (t : ℕ) :
    ampHistory M J seed s t 0=seed := by
  rw [actual_initial_coordinate]
  funext i
  exact clip_eq M (seed i) (hseed i)

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21
