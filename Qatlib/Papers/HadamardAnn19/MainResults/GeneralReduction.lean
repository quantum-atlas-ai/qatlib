/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Papers.HadamardAnn19.MainResults.GeneralReduction

set_option autoImplicit false

def hAnd (qi qj qk δ : ℝ) : ℝ :=
  δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)

theorem hAnd_and {qi qj δ : ℝ} (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) :
    hAnd qi qj (qi * qj) δ = 0 := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num

def threeBodyReduced (qa qb qc qe δ : ℝ) : ℝ :=
  qe * qc + hAnd qa qb qe δ

theorem threeBody_reduction {qa qb qc qe δ : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (he : qe = qa * qb) :
    qa * qb * qc = threeBodyReduced qa qb qc qe δ := by
  subst he
  unfold threeBodyReduced
  rw [hAnd_and ha hb]
  ring

theorem threeBody_reduction_mul {qa qb qc qe δ c : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (he : qe = qa * qb) :
    c * (qa * qb * qc) = c * threeBodyReduced qa qb qc qe δ := by
  rw [threeBody_reduction ha hb he]

def fourBodyReduced (qa qb qc qd qe qf δ : ℝ) : ℝ :=
  qe * qf + hAnd qa qb qe δ + hAnd qc qd qf δ

theorem fourBody_reduction {qa qb qc qd qe qf δ : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (hc : qc = 0 ∨ qc = 1) (hd : qd = 0 ∨ qd = 1)
    (he : qe = qa * qb) (hf : qf = qc * qd) :
    qa * qb * qc * qd = fourBodyReduced qa qb qc qd qe qf δ := by
  subst he
  subst hf
  unfold fourBodyReduced
  rw [hAnd_and ha hb, hAnd_and hc hd]
  ring

theorem fourBody_reduction_mul {qa qb qc qd qe qf δ c : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (hc : qc = 0 ∨ qc = 1) (hd : qd = 0 ∨ qd = 1)
    (he : qe = qa * qb) (hf : qf = qc * qd) :
    c * (qa * qb * qc * qd) = c * fourBodyReduced qa qb qc qd qe qf δ := by
  rw [fourBody_reduction ha hb hc hd he hf]

theorem fourBody_reduction_mul_rest {qa qb qc qd qe qf δ R : ℝ}
    (ha : qa = 0 ∨ qa = 1) (hb : qb = 0 ∨ qb = 1)
    (hc : qc = 0 ∨ qc = 1) (hd : qd = 0 ∨ qd = 1)
    (he : qe = qa * qb) (hf : qf = qc * qd) :
    qa * qb * qc * qd * R = fourBodyReduced qa qb qc qd qe qf δ * R := by
  rw [fourBody_reduction ha hb hc hd he hf]

end Qatlib.Papers.HadamardAnn19.MainResults.GeneralReduction
