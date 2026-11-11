/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit
import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicPeriodSampling

/-!
# Elementary properties of polynomial ordered-search states

This module establishes coordinate, normalization, root-parity, and resource-count identities
for the polynomial circuit definitions. The invariant ordered-search framework is described in
[FarhiEtAl1999], and the polynomial witness formulation is developed in
[ChildsLandahlParrilo2007]. The lemmas connect `tiPolynomialState` and `tiMomentumRoot` to the
phase factors used by `tiPolynomialTransition`.

Equality of polynomial norms at every root of `z^n = (-1)^t` ensures that `tiTransitionPhase`
has modulus one and that the transition matrix is unitary. The counting results apply directly
to the circuit words without this analytic hypothesis.

## Main statements

* `ti_state_normalized` and `ti_state_dirichlet` establish normalization from normalized
  coefficients and identify the initial uniform state.
* `ti_transition_phase_eval` and `ti_transition_unitary` justify the active-mode phase and
  transition unitarity under the rootwise norm hypothesis.
- `ti_query_zero_state` describes the zero-input oracle action.
- `ti_polynomial_word_counts` gives the query and gate counts with and without preparation.

## References

- [Farhi et al., 1999][FarhiEtAl1999], invariant ordered-search algorithms.
* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007], polynomial constraints for
  ordered search.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.HspRecovery.CyclicRecovery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

/-- Splits a sum over `Fin (2*n)` into the sums over coordinates `i` and `n+i`, each indexed by
`Fin n`. -/
theorem ti_sum_halves {α : Type*} [AddCommMonoid α] (n : ℕ) (f : Fin (2*n) → α) :
    ∑ i, f i =
      (∑ i : Fin n, f ⟨i.val,by have := i.isLt; omega⟩)+
      ∑ i : Fin n, f ⟨n+i.val,by have := i.isLt; omega⟩ := by
  let g : Fin (n+n) → α := fun i => f (Fin.cast (by omega) i)
  have hs := Fin.sum_univ_add g
  have he : (∑ i : Fin (n+n), g i) = ∑ i, f i := by
    exact Fintype.sum_equiv (finCongr (by omega)) _ _ (fun _ => rfl)
  rw [he] at hs
  exact hs

/-- Evaluates the first-half coordinate of `tiPolynomialState n t p` at `i` as `p i / sqrt 2`. -/
theorem ti_state_first (n t : ℕ) (p : Fin n → ℂ) (i : Fin n) :
    tiPolynomialState n t p ⟨i.val,by have := i.isLt; omega⟩ =
      (Real.sqrt 2 : ℂ)⁻¹*p i := by
  simp only [tiPolynomialState,dif_pos i.isLt]

/-- Evaluates the second-half coordinate of `tiPolynomialState n t p` at `n+i` as `(-1)^t * p
i`, scaled by `1 / sqrt 2`. -/
theorem ti_state_second (n t : ℕ) (p : Fin n → ℂ) (i : Fin n) :
    tiPolynomialState n t p ⟨n+i.val,by have := i.isLt; omega⟩ =
      (Real.sqrt 2 : ℂ)⁻¹*((-1:ℂ)^t*p i) := by
  have hi : ¬n+i.val<n := by omega
  simp only [tiPolynomialState,dif_neg hi,Nat.add_sub_cancel_left]

/-- Shows that `tiPolynomialState n t p` is normalized when the sum of the squared complex norms
of the coefficients of `p` is one. -/
theorem ti_state_normalized (n t : ℕ) (p : Fin n → ℂ)
    (hp : ∑ i,Complex.normSq (p i)=1) : Normalized (tiPolynomialState n t p) := by
  have hscale : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹) = (1/2:ℝ) := by
    rw [Complex.normSq_inv,Complex.normSq_ofReal,← pow_two,Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [Normalized,← Complex.normSq_eq_norm_sq]
  rw [ti_sum_halves]
  simp only [ti_state_first,ti_state_second,Complex.normSq_mul,hscale,map_pow,
    Complex.normSq_neg,map_one,one_pow,one_mul,← Finset.mul_sum,hp]
  norm_num

/-- Identifies the time-zero polynomial state of `tiDirichletVec n` with the uniform vector on
`Fin (2*n)`. -/
theorem ti_state_dirichlet (n : ℕ) :
    tiPolynomialState n 0 (tiDirichletVec n) = Uniform (Fin (2*n)) := by
  have hs : (Real.sqrt (2*n:ℝ) : ℂ) = (Real.sqrt 2 : ℂ)*(Real.sqrt (n:ℝ) : ℂ) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Complex.ofReal_mul]
  funext i
  dsimp [tiPolynomialState,tiDirichletVec,Uniform]
  rw [Fintype.card_fin]
  push_cast
  rw [hs]
  split_ifs <;> simp [_root_.mul_inv_rev,mul_comm]

/-- Shows that the `n`th power of the chosen primitive `(2*n)`th root is `-1` when `n` is
nonzero. -/
theorem ti_primitive_half_turn (n : ℕ) [NeZero n] : primRoot (2*n)^n = (-1:ℂ) := by
  have hn := NeZero.pos n
  have hr := isPrimitiveRoot_primRoot (by omega : 2*n≠0)
  have hsq : (primRoot (2*n)^n)^2 = (1:ℂ)^2 := by
    rw [← pow_mul,show n*2=2*n by omega,hr.pow_eq_one,one_pow]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · exact False.elim ((hr.pow_ne_one_of_pos_of_lt (NeZero.ne n) (by omega)) h)
  · exact h

/-- Computes the `n`th power of `tiMomentumRoot n l` as `(-1)^l.val` for nonzero `n`. -/
theorem ti_momentum_root_parity (n : ℕ) [NeZero n] (l : Fin (2*n)) :
    tiMomentumRoot n l ^ n = (-1:ℂ)^l.val := by
  unfold tiMomentumRoot
  rw [← zpow_natCast,← _root_.zpow_mul]
  rw [show -(l.val:ℤ)*(n:ℤ)=(n:ℤ)*-(l.val:ℤ) by ring,
    _root_.zpow_mul,zpow_natCast,ti_primitive_half_turn]
  simp [← _root_.inv_pow]

/-- Shows that a momentum mode with the parity of `t` satisfies `tiMomentumRoot n l ^ n =
(-1)^t`. -/
theorem ti_momentum_root_active (n t : ℕ) [NeZero n] (l : Fin (2*n))
    (h : l.val%2=t%2) : tiMomentumRoot n l^n=(-1:ℂ)^t := by
  rw [ti_momentum_root_parity,neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two t,h]

/-- Proves that every transition phase has modulus one when `a` and `b` have equal polynomial
norms at all roots of `z^n = (-1)^t`. -/
theorem ti_transition_phase_norm (n t : ℕ) [NeZero n] (a b : Fin n → ℂ)
    (hm : ∀ z : ℂ,z^n=(-1:ℂ)^t → ‖tiPolyEval a z‖=‖tiPolyEval b z‖)
    (l : Fin (2*n)) : ‖tiTransitionPhase n t a b l‖=1 := by
  unfold tiTransitionPhase
  split_ifs with hl ha
  · simp
  · have he := hm (tiMomentumRoot n l) (ti_momentum_root_active n t l hl)
    rw [norm_div,norm_neg,← he,div_self (norm_ne_zero_iff.mpr ha)]
  · simp

/-- Shows that at an active-parity mode the transition phase sends the negative evaluation of
`a` to the evaluation of `b`, assuming their norms agree on the relevant roots. -/
theorem ti_transition_phase_eval (n t : ℕ) [NeZero n] (a b : Fin n → ℂ)
    (hm : ∀ z : ℂ,z^n=(-1:ℂ)^t → ‖tiPolyEval a z‖=‖tiPolyEval b z‖)
    (l : Fin (2*n)) (hl : l.val%2=t%2) :
    tiTransitionPhase n t a b l * (-tiPolyEval a (tiMomentumRoot n l)) =
      tiPolyEval b (tiMomentumRoot n l) := by
  have he := hm (tiMomentumRoot n l) (ti_momentum_root_active n t l hl)
  unfold tiTransitionPhase
  rw [if_pos hl]
  split_ifs with ha
  · have hb : tiPolyEval b (tiMomentumRoot n l)=0 := norm_eq_zero.mp (by simpa [ha] using he.symm)
    simp [ha,hb]
  · field_simp

/-- Proves that `tiPolynomialTransition n t a b` is unitary when the polynomial evaluations of
`a` and `b` have equal norms at every root of `z^n = (-1)^t`. -/
theorem ti_transition_unitary (n t : ℕ) [NeZero n] (a b : Fin n → ℂ)
    (hm : ∀ z : ℂ,z^n=(-1:ℂ)^t → ‖tiPolyEval a z‖=‖tiPolyEval b z‖) :
    tiPolynomialTransition n t a b ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ := by
  have hd : Matrix.diagonal (tiTransitionPhase n t a b) ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]
    congr 1
    funext l
    change star (tiTransitionPhase n t a b l)*tiTransitionPhase n t a b l=1
    simp only [Complex.star_def]
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,ti_transition_phase_norm n t a b hm l]
    norm_num
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem (qftMatrix_unitary (by have := NeZero.pos n; omega)) hd)
    (qftMatrix_conjTranspose_unitary _ (by have := NeZero.pos n; omega))

/-- For positive `t`, shows that the zero-input ordered-search phase oracle sends the time-`t-1`
polynomial state to the negative of the time-`t` state with the same coefficients. -/
theorem ti_query_zero_state (n t : ℕ) [NeZero n] (ht : 0<t) (a : Fin n → ℂ) :
    ApplyGate (PhaseOracle (ospBit n 0)) (tiPolynomialState n (t-1) a) =
      -tiPolynomialState n t a := by
  have hp : (-1:ℂ)^(t-1) = -(-1:ℂ)^t := by
    have he : t-1+1=t := by omega
    have hh := congrArg (fun r => (-1:ℂ)^r) he
    (try dsimp only at hh)
    rw [pow_succ] at hh
    linear_combination -hh
  funext i
  rw [applyGate_phaseOracle]
  have hi : (0:ℤ) ≤ i.val := by positivity
  have hi' : (i.val:ℤ)<2*n := by exact_mod_cast i.isLt
  have hm : (i.val:ℤ)%(2*n)=i.val := Int.emod_eq_of_lt hi hi'
  have ho : ospBit n 0 i=decide (i.val<n) := by
    change decide (((i.val:ℤ)-0)%(2*(n:ℤ))<(n:ℤ))=decide (i.val<n)
    rw [sub_zero,hm]
    simp
  rw [ho]
  change (if decide (i.val<n) then (-1:ℂ) else 1)*tiPolynomialState n (t-1) a i =
    -tiPolynomialState n t a i
  unfold tiPolynomialState
  by_cases h : i.val<n
  · simp [h]
  · simp [h,hp]

/-- Shows that `tiInvariantQueryWord n k U` contains exactly `k` query steps and `k` gate steps. -/
theorem ti_invariant_word_counts (n k : ℕ)
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ) :
    QueryCount (tiInvariantQueryWord n k U)=k ∧ GateCount (tiInvariantQueryWord n k U)=k := by
  induction k with
  | zero => simp [tiInvariantQueryWord]
  | succ k ih =>
    rw [tiInvariantQueryWord,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [queryCount_append,gateCount_append]
    change QueryCount (tiInvariantQueryWord n k U)+1=k+1 ∧
      GateCount (tiInvariantQueryWord n k U)+1=k+1
    exact ⟨congrArg (·+1) ih.1,congrArg (·+1) ih.2⟩

/-- Expresses the polynomial query word as the invariant query word whose time-`t` gate is the
transition from `p (t-1)` to `p t`. -/
theorem ti_polynomial_word_eq_invariant (n k : ℕ) (p : ℕ → Fin n → ℂ) :
    tiPolynomialQueryWord n k p=tiInvariantQueryWord n k
      (fun t => tiPolynomialTransition n t (p (t-1)) (p t)) := by
  unfold tiPolynomialQueryWord tiInvariantQueryWord
  congr 1

/-- Shows that both polynomial words have `k` queries, while the query word has `k` gates and
the prepared word has `k+1` gates. -/
theorem ti_polynomial_word_counts (n k : ℕ) (p : ℕ → Fin n → ℂ) :
    QueryCount (tiPolynomialQueryWord n k p)=k ∧
    GateCount (tiPolynomialQueryWord n k p)=k ∧
    QueryCount (tiPolynomialPreparedWord n k p)=k ∧
    GateCount (tiPolynomialPreparedWord n k p)=k+1 := by
  have hc : QueryCount (tiPolynomialQueryWord n k p)=k ∧ GateCount (tiPolynomialQueryWord n k p)=k := by
    rw [ti_polynomial_word_eq_invariant]
    exact ti_invariant_word_counts n k _
  exact ⟨hc.1,hc.2,by simpa [tiPolynomialPreparedWord] using hc.1,
    by simpa [tiPolynomialPreparedWord] using hc.2⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
