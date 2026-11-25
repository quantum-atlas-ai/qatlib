/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversaryHam11.MainResults.HamiltonianOracleModel
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Final-state overlap for the binary readout

Split the inner product into the two complementary projective outcomes. Bound each term
by the product of its branch norms. The classical two-outcome overlap of the branch
probabilities is at most the coefficient in the output condition of §3.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.AdversaryHam11.MainResults

namespace Qatlib.Papers.AdversaryHam11.MainResults

/-- The overlap of two binary probability vectors with opposite correct outcomes is bounded
by the coefficient determined by the larger allowed error. -/
private theorem binary_overlap_bound {p q ε : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpε : p ≤ ε)
    (hqε : q ≤ ε) (hε : ε ≤ 1 / 2) :
    Real.sqrt p * Real.sqrt (1 - q) + Real.sqrt q * Real.sqrt (1 - p) ≤
      2 * Real.sqrt (ε * (1 - ε)) := by
  let a := Real.sqrt p
  let b := Real.sqrt q
  let c := Real.sqrt (1 - p)
  let e := Real.sqrt (1 - q)
  have ha : a ^ 2 = p := Real.sq_sqrt hp
  have hb : b ^ 2 = q := Real.sq_sqrt hq
  have hc : c ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have he : e ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hcs : (a * e + b * c) ^ 2 + (a * c - b * e) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + e ^ 2) := by ring
  rw [ha, hb, hc, he] at hcs
  have hmon := mul_nonneg (show 0 ≤ 2 * ε - (p + q) by linarith)
    (show 0 ≤ 2 - 2 * ε - (p + q) by linarith)
  have hεp : 0 ≤ ε * (1 - ε) := mul_nonneg (hp.trans hpε) (by linarith)
  change a * e + b * c ≤ _
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt hεp]
  nlinarith [sq_nonneg (a * c - b * e)]

/-- For an orthogonal projector, projecting the second argument has no additional effect
once the first argument has been projected. -/
private theorem inner_project_twice {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : P.IsHermitian) (hi : P * P = P) (u v : QState H) :
    Inner (P *ᵥ u) (P *ᵥ v) = Inner (P *ᵥ u) v := by
  calc
    _ = Inner u (P *ᵥ (P *ᵥ v)) := by rw [inner_mulVec_left_rect, hP.eq]
    _ = Inner u (P *ᵥ v) := by rw [Matrix.mulVec_mulVec, hi]
    _ = _ := by rw [inner_mulVec_left_rect, hP.eq]

/-- Two normalized states with opposite bounded-error outcomes under complementary
orthogonal projectors satisfy the binary overlap bound. -/
private theorem projected_overlap_bound {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (hQQ : (1 - P) * (1 - P) = 1 - P) (u v : QState H)
    (hu : Normalized u) (hv : Normalized v) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (huok : 1 - ε ≤ (Inner ((1 - P) *ᵥ u) u).re)
    (hvok : 1 - ε ≤ (Inner (P *ᵥ v) v).re) :
    ‖Inner u v‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  let Q : Matrix H H ℂ := 1 - P
  have hQ : Q.IsHermitian := by
    change (1 - P)ᴴ = 1 - P
    simp [hP.eq]
  have hdec (w z : QState H) :
      Inner (P *ᵥ w) z + Inner (Q *ᵥ w) z = Inner w z := by
    have hsum : P *ᵥ w + Q *ᵥ w = w := by
      have hPQ : P + Q = 1 := by dsimp [Q]; abel
      rw [← Matrix.add_mulVec, hPQ, Matrix.one_mulVec]
    calc
      _ = Inner (P *ᵥ w + Q *ᵥ w) z := by
        simp only [Qatlib.Foundations.PureStateMath.Inner, star_add, add_dotProduct]
      _ = _ := congrArg (fun v => Inner v z) hsum
  have hPnorm (w : QState H) :
      ‖toEuclidean_fromVec (P *ᵥ w)‖ ^ 2 = (Inner (P *ᵥ w) w).re := by
    rw [norm_toEuclidean_sq_eq_re_inner, inner_project_twice P hP hPP]
  have hQnorm (w : QState H) :
      ‖toEuclidean_fromVec (Q *ᵥ w)‖ ^ 2 = (Inner (Q *ᵥ w) w).re := by
    rw [norm_toEuclidean_sq_eq_re_inner, inner_project_twice Q hQ hQQ]
  have htot (w : QState H) (hw : Normalized w) :
      ‖toEuclidean_fromVec (P *ᵥ w)‖ ^ 2 + ‖toEuclidean_fromVec (Q *ᵥ w)‖ ^ 2 = 1 := by
    rw [hPnorm, hQnorm, ← Complex.add_re, hdec, (normalized_iff_inner_self w).mp hw]
    exact Complex.one_re
  let p := ‖toEuclidean_fromVec (P *ᵥ u)‖ ^ 2
  let q := ‖toEuclidean_fromVec (Q *ᵥ v)‖ ^ 2
  have hp : p ≤ ε := by
    change 1 - ε ≤ (Inner (Q *ᵥ u) u).re at huok
    rw [← hQnorm] at huok
    have h := htot u hu
    dsimp [p]
    linarith
  have hq : q ≤ ε := by
    rw [← hPnorm] at hvok
    have h := htot v hv
    dsimp [q]
    linarith
  have hPu : ‖toEuclidean_fromVec (P *ᵥ u)‖ = Real.sqrt p := (Real.sqrt_sq (norm_nonneg _)).symm
  have hQv : ‖toEuclidean_fromVec (Q *ᵥ v)‖ = Real.sqrt q := (Real.sqrt_sq (norm_nonneg _)).symm
  have hPv : ‖toEuclidean_fromVec (P *ᵥ v)‖ = Real.sqrt (1 - q) := by
    rw [show 1 - q = ‖toEuclidean_fromVec (P *ᵥ v)‖ ^ 2 by dsimp [q]; linarith [htot v hv],
      Real.sqrt_sq (norm_nonneg _)]
  have hQu : ‖toEuclidean_fromVec (Q *ᵥ u)‖ = Real.sqrt (1 - p) := by
    rw [show 1 - p = ‖toEuclidean_fromVec (Q *ᵥ u)‖ ^ 2 by dsimp [p]; linarith [htot u hu],
      Real.sqrt_sq (norm_nonneg _)]
  have hsplit : Inner u v = Inner (P *ᵥ u) (P *ᵥ v) + Inner (Q *ᵥ u) (Q *ᵥ v) := by
    rw [inner_project_twice P hP hPP, inner_project_twice Q hQ hQQ, hdec]
  rw [hsplit]
  calc
    _ ≤ ‖Inner (P *ᵥ u) (P *ᵥ v)‖ + ‖Inner (Q *ᵥ u) (Q *ᵥ v)‖ := norm_add_le _ _
    _ ≤ ‖toEuclidean_fromVec (P *ᵥ u)‖ * ‖toEuclidean_fromVec (P *ᵥ v)‖ +
        ‖toEuclidean_fromVec (Q *ᵥ u)‖ * ‖toEuclidean_fromVec (Q *ᵥ v)‖ := by
        simp only [← inner_euclidean_fromVec]
        exact add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = Real.sqrt p * Real.sqrt (1 - q) + Real.sqrt q * Real.sqrt (1 - p) := by
        rw [hPu, hPv, hQu, hQv, mul_comm (Real.sqrt (1 - p))]
    _ ≤ _ := binary_overlap_bound (sq_nonneg _) (sq_nonneg _) hp hq hε

/-- The terminal states for distinct outputs of a bounded-error computation obey
the two-state overlap inequality of §3. -/
theorem terminal_pair_overlap {X H : Type} [Fintype X] [Fintype H] [DecidableEq H] {n : ℕ}
    (M : HamiltonianModel X H n) (f : X → Bool) {ε T : ℝ}
    (halg : BoundedErrorComputes M f ε T) (hε : ε ≤ 1 / 2) {x y : X} (hxy : f x ≠ f y) :
    ‖Inner (M.state x T) (M.state y T)‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  have hpair (a b : X) (ha : f a = false) (hb : f b = true) :
      ‖Inner (M.state a T) (M.state b T)‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) :=
    projected_overlap_bound halg.accept halg.accept_herm halg.accept_idem halg.complement_idem
      _ _ (M.state_normalized a T) (M.state_normalized b T) hε
      (by simpa [ha] using halg.success a) (by simpa [hb] using halg.success b)
  cases hx : f x <;> cases hy : f y
  · exact (hxy (hx.trans hy.symm)).elim
  · exact hpair x y hx hy
  · have hswap : ‖Inner (M.state x T) (M.state y T)‖ = ‖Inner (M.state y T) (M.state x T)‖ := by
      simp only [← inner_euclidean_fromVec]
      exact norm_inner_symm _ _
    exact hswap.le.trans (hpair y x hy hx)
  · exact (hxy (hx.trans hy.symm)).elim

end Qatlib.Papers.AdversaryHam11.MainResults
