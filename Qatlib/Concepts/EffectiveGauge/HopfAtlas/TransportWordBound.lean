/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.TransverseTransportBound
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.TransportMajorant

set_option backward.isDefEq.respectTransparency false

/-! # Coordinate-word estimates for the actual transport, by strict lower-order induction -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- These are numerical recurrence inequalities. No norm or derivative of q
occurs in this predicate; the executable rational recurrence supplies it. -/
def TransportMajorantSpec (Q K : ℕ → ℝ) (N : ℕ) : Prop :=
  1 ≤ Q 0 ∧ (∀ j ≤ N, 0 ≤ Q j) ∧ (∀ j ≤ N, 0 ≤ K j) ∧
  (∀ n < N, wordProductMajorant Q K n ≤ Q (n+1)) ∧
  (∀ n < N, 7*(∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*K (j+1)*Q (n-j)) ≤ Q (n+1))

/-- Original `transportWordBound_on_cube` guarantee for the `TransportWordBound` construction; the complete source hypotheses are retained. -/
theorem transportWordBound_on_cube (q K : SpatialPoint → ℍ)
    (hq : ContDiff ℝ ∞ q) (hK : ContDiff ℝ ∞ K)
    (hunit : ∀ x : SpatialPoint, InUnitCube x → ‖q x‖=1)
    (hpure : ∀ x : SpatialPoint, InUnitCube x → (K x).re=0)
    (hode : ∀ x : SpatialPoint, 0 ≤ x 0 ∧ x 0 ≤ 1 → spatialWordPartial q [0] x=q x*K x)
    (c : ℍ) (hplane : ∀ x : SpatialPoint, x 0=0 → q x=c)
    (Q G : ℕ → ℝ) (N : ℕ) (hspec : TransportMajorantSpec Q G N)
    (hKB : ∀ u : List (Fin 3), u.length ≤ N → ∀ x, InUnitCube x →
      ‖spatialWordPartial K u x‖ ≤ G u.length)
    (w : List (Fin 3)) (hwN : w.length ≤ N) (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial q w x‖ ≤ Q w.length := by
  rcases hspec with ⟨hzero,hQ,hG,hlong,htrans⟩
  have hall : ∀ r : ℕ, r ≤ N → ∀ w : List (Fin 3), w.length=r → ∀ x,
      InUnitCube x → ‖spatialWordPartial q w x‖ ≤ Q r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr w hw x hx
      cases r with
      | zero =>
        have he : w=[] := List.length_eq_zero_iff.mp hw
        subst w
        simpa only [spatialWordPartial,hunit x hx] using hzero
      | succ n =>
        have hqB : ∀ u : List (Fin 3), u.length < w.length → ∀ y, InUnitCube y →
            ‖spatialWordPartial q u y‖ ≤ Q u.length := by
          intro u hu y hy
          exact ih u.length (by omega) (by omega) u rfl y hy
        by_cases hz : (0 : Fin 3) ∈ w
        · let u := w.erase 0
          have hperm : w.Perm (0::u) := List.perm_cons_erase hz
          have hulen : u.length=n := by
            have hlen := hperm.length_eq
            simp only [List.length_cons] at hlen
            omega
          rw [spatialWordPartial_perm q hq hperm,
            spatialWordPartial_transport_slab q K hq hK hode u x (hx 0)]
          have hb := spatialWordPartial_mul_norm_le q K hq hK Q G u x
            (fun j hj => hQ j (by omega)) (fun j hj => hG j (by omega))
            (fun z hz => hqB z (by omega) x hx)
            (fun z hz => hKB z (by omega) x hx)
          rw [hulen] at hb
          exact hb.trans (hlong n (by omega))
        · have hwt : ∀ i ∈ w, i≠0 := by
            intro i hi he
            subst i
            exact hz hi
          have hne : w≠[] := by intro he; simp [he] at hw
          have hb := spatialWordPartial_transverse_transport_bound q K hq hK hunit hpure hode
            c hplane Q G w hwt hne
            (fun j hj => hQ j (by omega)) (fun j hj => hG j (by omega)) hqB
            (fun z hz => hKB z (by omega)) x hx
          rw [hw,wordProductRemainderMajorant_transverse] at hb
          have hsum : 0 ≤ ∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*G (j+1)*Q (n-j) := by
            apply Finset.sum_nonneg
            intro j hj
            have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG _ (by omega))) (hQ _ (by omega))
          have hseven : (∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*G (j+1)*Q (n-j)) ≤
              7*(∑ j ∈ range (n+1), ((n+1).choose (j+1) : ℝ)*G (j+1)*Q (n-j)) := by linarith
          exact hb.trans (hseven.trans (htrans n (by omega)))
  exact hall w.length hwN w rfl x hx

/-- The actual finite rational recurrence supplies the numerical induction
invariant; none of its fields assumes a norm bound on the unknown lift. -/
theorem transportWordMajorant_spec (K : ℕ → ℚ) (hK : ∀ j, 0 ≤ K j) (N : ℕ) :
    TransportMajorantSpec (fun j => (transportWordMajorant K j : ℝ)) (fun j => (K j : ℝ)) N := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [transportWordMajorant]
  · intro j hj
    exact Rat.cast_nonneg.mpr (transportWordMajorant_nonneg K hK j)
  · intro j hj
    exact Rat.cast_nonneg.mpr (hK j)
  · intro n hn
    unfold wordProductMajorant
    rw [Finset.sum_range]
    conv_rhs =>
      dsimp only
      rw [transportWordMajorant.eq_def]
    simp only [Rat.cast_max,Rat.cast_mul,Rat.cast_sum,Rat.cast_natCast,Rat.cast_ofNat]
    exact le_max_right _ _
  · intro n hn
    rw [Finset.sum_range]
    conv_rhs =>
      dsimp only
      rw [transportWordMajorant.eq_def]
    simp only [Rat.cast_max,Rat.cast_mul,Rat.cast_sum,Rat.cast_natCast,Rat.cast_ofNat]
    exact le_max_left _ _

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
