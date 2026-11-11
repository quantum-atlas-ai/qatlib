/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.TimeDependentSegmentSplitSimu
import Qatlib.Foundations.OperatorErrors.OperatorError

set_option backward.isDefEq.respectTransparency false

/-!
# Source p. 4 — time-dependent extension: final error `≤ ε`

arXiv:1412.4687v1, p. 4, time-dependent section (Eqs. (26)–(28)).
The evolution `U(t) = T exp(-i ∫₀^t H(s) ds)` is split into `r` equal segments
of length `t/r`; on each segment Eq. (28) approximates the segment propagator,
and OAA (as in the time-independent case) produces a state within `O(ε/r)` of
the exact segment evolution.  Repeating `r` times yields the final state
within error `ε` against `U(t)|ψ⟩`.

The frozen kit used here:
* `TimeDependentSegmentSplit` — the exact total evolution equals the product
  of the `r` segment evolutions (later segments to the left);
* `ordered_evolution_hermitian_unitary` — each segment propagator is unitary
  (a continuous Hermitian field);
* `l2_norm_unitary_le_one` — unitaries have L2 operator norm `≤ 1`.

The paper-layer theorem states the composition step: given `r` actual segment
words `U_k` of norm `≤ 1`, each within `ε/r` of the exact segment evolution,
the product word is within `ε` of the total evolution.  The per-segment input
`U_k` is exactly what Eq. (28) + OAA deliver; that synthesis step is the
frozen `Equation28`/`Equation28UnitarySum` package and is not re-proved here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.TimeDependent
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.TruncTaylor14.TimeDependent.OverallError

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Later-segment-first product of the segment matrices `A 0, …, A (r-1)`. -/
def segmentProduct (r : ℕ) (A : Fin r → Matrix I I ℂ) : Matrix I I ℂ :=
  (List.ofFn A).reverse.prod

/-- The segment product is the last factor times the product of the prefix. -/
theorem segmentProduct_succ (r : ℕ) (A : Fin (r + 1) → Matrix I I ℂ) :
    segmentProduct (r + 1) A =
      A (Fin.last r) * segmentProduct r (fun k => A k.castSucc) := by
  simp only [segmentProduct, List.ofFn_succ', List.concat_eq_append, List.reverse_append,
    List.reverse_singleton, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

/-- A segment product of factors of norm `≤ 1` has norm `≤ 1`. -/
theorem segmentProduct_norm_le_one (r : ℕ) (A : Fin r → Matrix I I ℂ)
    (hA : ∀ k, ‖A k‖ ≤ 1) : ‖segmentProduct r A‖ ≤ 1 := by
  induction r with
  | zero =>
    simpa [segmentProduct, List.ofFn_zero] using (l2_norm_one_le (I := I))
  | succ r ih =>
    rw [segmentProduct_succ]
    calc ‖A (Fin.last r) * segmentProduct r (fun k => A k.castSucc)‖
        ≤ ‖A (Fin.last r)‖ * ‖segmentProduct r (fun k => A k.castSucc)‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul (hA _) (ih _ (fun k => hA _)) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

/-- Telescoping error bound: if `r` approximants `A k` and exact factors `V k`
all have norm `≤ 1` and differ by at most `η` factorwise, the segment products
differ by at most `r·η` (subadditivity over the `r` factors). -/
theorem segmentProduct_norm_sub_le (r : ℕ) :
    ∀ (A V : Fin r → Matrix I I ℂ) (η : ℝ),
      (∀ k, ‖A k‖ ≤ 1) → (∀ k, ‖V k‖ ≤ 1) →
      (∀ k, ‖A k - V k‖ ≤ η) → 0 ≤ η →
      ‖segmentProduct r A - segmentProduct r V‖ ≤ (r : ℝ) * η := by
  induction r with
  | zero =>
    intro A V η _ _ _ _
    simp [segmentProduct, List.ofFn_zero]
  | succ r ih =>
    intro A V η hA hV h hη
    rw [segmentProduct_succ, segmentProduct_succ]
    have hAlast : ‖A (Fin.last r)‖ ≤ 1 := hA _
    have hVlast : ‖V (Fin.last r)‖ ≤ 1 := hV _
    have herr_last : ‖A (Fin.last r) - V (Fin.last r)‖ ≤ η := h _
    have hA' : ∀ k : Fin r, ‖A k.castSucc‖ ≤ 1 := fun k => hA _
    have hV' : ∀ k : Fin r, ‖V k.castSucc‖ ≤ 1 := fun k => hV _
    have herr' : ∀ k : Fin r, ‖A k.castSucc - V k.castSucc‖ ≤ η := fun k => h _
    have ih' := ih (fun k => A k.castSucc) (fun k => V k.castSucc) η hA' hV' herr' hη
    have hVP1 : ‖segmentProduct r (fun k => V k.castSucc)‖ ≤ 1 :=
      segmentProduct_norm_le_one r _ hV'
    have hsplit :
        A (Fin.last r) * segmentProduct r (fun k => A k.castSucc) -
            V (Fin.last r) * segmentProduct r (fun k => V k.castSucc) =
          A (Fin.last r) * (segmentProduct r (fun k => A k.castSucc) -
              segmentProduct r (fun k => V k.castSucc)) +
            (A (Fin.last r) - V (Fin.last r)) *
              segmentProduct r (fun k => V k.castSucc) := by
      noncomm_ring
    rw [hsplit]
    have h1 : ‖A (Fin.last r) * (segmentProduct r (fun k => A k.castSucc) -
        segmentProduct r (fun k => V k.castSucc))‖ ≤ (r : ℝ) * η := by
      calc ‖A (Fin.last r) * (segmentProduct r (fun k => A k.castSucc) -
              segmentProduct r (fun k => V k.castSucc))‖
          ≤ ‖A (Fin.last r)‖ * ‖segmentProduct r (fun k => A k.castSucc) -
              segmentProduct r (fun k => V k.castSucc)‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ 1 * ((r : ℝ) * η) :=
            mul_le_mul hAlast ih' (norm_nonneg _) (by positivity)
        _ = (r : ℝ) * η := one_mul _
    have h2 : ‖(A (Fin.last r) - V (Fin.last r)) *
        segmentProduct r (fun k => V k.castSucc)‖ ≤ η := by
      calc ‖(A (Fin.last r) - V (Fin.last r)) *
              segmentProduct r (fun k => V k.castSucc)‖
          ≤ ‖A (Fin.last r) - V (Fin.last r)‖ *
              ‖segmentProduct r (fun k => V k.castSucc)‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ η * 1 := mul_le_mul herr_last hVP1 (norm_nonneg _) hη
        _ = η := mul_one η
    calc ‖A (Fin.last r) * (segmentProduct r (fun k => A k.castSucc) -
            segmentProduct r (fun k => V k.castSucc)) +
          (A (Fin.last r) - V (Fin.last r)) *
            segmentProduct r (fun k => V k.castSucc)‖
        ≤ ‖A (Fin.last r) * (segmentProduct r (fun k => A k.castSucc) -
            segmentProduct r (fun k => V k.castSucc))‖ +
          ‖(A (Fin.last r) - V (Fin.last r)) *
            segmentProduct r (fun k => V k.castSucc)‖ := norm_add_le _ _
      _ ≤ (r : ℝ) * η + η := add_le_add h1 h2
      _ = ((r + 1 : ℕ) : ℝ) * η := by push_cast; ring

/-- arXiv:1412.4687v1 p. 4, time-dependent extension: if each of the `r`
segment words `U k` is within `ε/r` of the exact segment propagator
`U((k+1)t/r, kt/r)`, the `r`-fold composition is within `ε` of the full
time-ordered evolution `U(t)`. -/
theorem source_time_dependent_error
    (H : ℝ → Matrix I I ℂ) (t ε : ℝ) (r : ℕ)
    (hH : Continuous H) (hHerm : ∀ u, (H u).IsHermitian)
    (ht : 0 ≤ t) (hr : 0 < r) (hε : 0 ≤ ε)
    (U : Fin r → Matrix I I ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (hseg : ∀ k : Fin r,
      ‖U k - orderedEvolution (fun u => Complex.I • H u)
        ((k.val : ℝ) * t / (r : ℝ))
        (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ))‖ ≤ ε / r) :
    ‖segmentProduct r U - orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ ε := by
  have hsplit := timeDependentSegmentSplit I H t r hH ht hr
  have hunit : ∀ k : Fin r,
      orderedEvolution (fun u => Complex.I • H u)
        ((k.val : ℝ) * t / (r : ℝ))
        (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ)) ∈ Matrix.unitaryGroup I ℂ :=
    fun k => ordered_evolution_hermitian_unitary I H hH hHerm _ _
  have hVnorm : ∀ k : Fin r,
      ‖orderedEvolution (fun u => Complex.I • H u)
        ((k.val : ℝ) * t / (r : ℝ))
        (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ))‖ ≤ 1 :=
    fun k => l2_norm_unitary_le_one (hunit k)
  have hUnorm : ∀ k : Fin r, ‖U k‖ ≤ 1 := fun k => l2_norm_unitary_le_one (hU k)
  have hη : 0 ≤ ε / r := by positivity
  have hbound := segmentProduct_norm_sub_le r U
    (fun k => orderedEvolution (fun u => Complex.I • H u)
      ((k.val : ℝ) * t / (r : ℝ))
      (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ))) (ε / r) hUnorm hVnorm hseg hη
  have hsegprod : segmentProduct r (fun k =>
      orderedEvolution (fun u => Complex.I • H u)
        ((k.val : ℝ) * t / (r : ℝ))
        (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ))) =
      orderedEvolution (fun u => Complex.I • H u) 0 t := by
    unfold segmentProduct
    exact hsplit.symm
  rw [hsegprod] at hbound
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have heq : (r : ℝ) * (ε / (r : ℝ)) = ε := by field_simp
  rwa [heq] at hbound

end Qatlib.Papers.TruncTaylor14.TimeDependent.OverallError
