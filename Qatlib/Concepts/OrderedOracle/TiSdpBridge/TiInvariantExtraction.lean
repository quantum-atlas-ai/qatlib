/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiSpectralHelpers

/-!
# Polynomial coefficients from invariant query programs

This module extracts `tiInvariantCoefficients` from the execution of a query program whose gates
commute with cyclic translation. Each prefix lies in the parity sector determined by the number
of queries and equals the corresponding `tiPolynomialState`. With unitary gates, the extracted
coefficients are normalized and satisfy the polynomial matching conditions at the relevant
roots. The invariant ordered search setting is developed in [FarhiEtAl1999].

## Main statements

* `ti_invariant_prefix_state`: represents the zero-input prefix by its extracted coefficients.
* `ti_invariant_coefficients_normalized`: proves coefficient normalization for unitary prefixes.
* `ti_invariant_coefficients_match`: proves equality of successive polynomial magnitudes at the
  specified roots.
* `ti_invariant_prefix_all`: describes every input prefix as a translated polynomial state.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
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

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

/-- The zero-input run of an invariant query word at step `t + 1` is obtained from its step `t`
state by applying the oracle and then `U (t + 1)`. -/
theorem ti_invariant_run_succ (n t : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ) :
    Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n (t+1) U) (Uniform (Fin (2*n))) =
      ApplyGate (U (t+1)) (ApplyGate (PhaseOracle (ospBit n 0))
        (Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n))))) := by
  rw [tiInvariantQueryWord,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U ++
    [Step.query,Step.gate (U (t+1))]) (Uniform (Fin (2*n))) = _
  rw [run_append]
  rfl

/-- When the gates commute with translation through step `k`, each zero-input prefix at step `t
≤ k` is an eigenvector of translation by `n` with eigenvalue `(-1) ^ t`. -/
theorem ti_invariant_prefix_sector (n k : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hc : ∀ t ∈ Finset.Icc 1 k,tiTranslation n*U t=U t*tiTranslation n)
    (t : ℕ) (ht : t≤k) :
    ApplyGate ((tiTranslation n)^n)
      (Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n)))) =
      (-1:ℂ)^t • Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n))) := by
  induction t with
  | zero =>
    simp only [tiInvariantQueryWord,List.range_zero,List.flatMap_nil,Run]
    rw [← ti_state_dirichlet n]
    exact ti_state_sector n 0 _
  | succ t ih =>
    have hs := ih (by omega)
    let ψ := Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n)))
    let q : Fin n → ℂ := fun i => (Real.sqrt 2 : ℂ)*ψ ⟨i.val,by have := i.isLt; omega⟩
    have hψ : ψ=tiPolynomialState n t q := ti_sector_representation n t ψ hs
    have hquery : ApplyGate (PhaseOracle (ospBit n 0)) ψ = -tiPolynomialState n (t+1) q := by
      rw [hψ]
      simpa only [Nat.add_sub_cancel] using ti_query_zero_state n (t+1) (by omega) q
    rw [ti_invariant_run_succ]
    apply ti_commuting_preserves_sector n (t+1) _ (hc (t+1) (by simp only [Finset.mem_Icc]; omega))
    change ApplyGate ((tiTranslation n)^n) (ApplyGate (PhaseOracle (ospBit n 0)) ψ) =
      (-1:ℂ)^(t+1) • ApplyGate (PhaseOracle (ospBit n 0)) ψ
    rw [hquery]
    simpa only [ApplyGate,Matrix.mulVec_neg,smul_neg] using
      congrArg Neg.neg (ti_state_sector n (t+1) q)

/-- The coefficients extracted from the zero-input invariant run: `tiDirichletVec n` at step
zero, and square root of two times the first `n` state amplitudes at positive steps. -/
def tiInvariantCoefficients (n : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ) (t : ℕ) (i : Fin n) : ℂ :=
  if t=0 then tiDirichletVec n i else
    (Real.sqrt 2 : ℂ)*Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U)
      (Uniform (Fin (2*n))) ⟨i.val,by have := i.isLt; omega⟩

/-- For gates commuting with translation through step `k`, the zero-input prefix at each step `t
≤ k` equals the polynomial state formed from `tiInvariantCoefficients n U t`. -/
theorem ti_invariant_prefix_state (n k : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hc : ∀ t ∈ Finset.Icc 1 k,tiTranslation n*U t=U t*tiTranslation n)
    (t : ℕ) (ht : t≤k) :
    Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n))) =
      tiPolynomialState n t (tiInvariantCoefficients n U t) := by
  by_cases h : t=0
  · subst t
    have hp : tiInvariantCoefficients n U 0=tiDirichletVec n := by
      funext i
      simp [tiInvariantCoefficients]
    simp [tiInvariantQueryWord,hp,ti_state_dirichlet]
  · have hp : tiInvariantCoefficients n U t = fun i => (Real.sqrt 2 : ℂ)*
        Run (PhaseOracle (ospBit n 0)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n)))
          ⟨i.val,by have := i.isLt; omega⟩ := by
      funext i
      simp only [tiInvariantCoefficients,h,ite_false]
    rw [hp]
    exact ti_sector_representation n t _ (ti_invariant_prefix_sector n k U hc t ht)

/-- Coefficients extracted from a prefix of translation-commuting unitary gates have total
squared norm one. -/
theorem ti_invariant_coefficients_normalized (n k : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hu : ∀ t ∈ Finset.Icc 1 k,U t ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ)
    (hc : ∀ t ∈ Finset.Icc 1 k,tiTranslation n*U t=U t*tiTranslation n)
    (t : ℕ) (ht : t≤k) :
    ∑ i,Complex.normSq (tiInvariantCoefficients n U t i)=1 := by
  have hword := ti_invariant_word_unitary n t U (fun s hs => hu s (by
    simp only [Finset.mem_Icc] at hs ⊢; omega))
  have hψ := hword.normalized_run (phaseOracle_unitary (ospBit n 0)) (normalized_uniform (by
    simp only [Fintype.card_fin]; have := NeZero.pos n; omega : 0<Fintype.card (Fin (2*n))))
  rw [ti_invariant_prefix_state n k U hc t ht] at hψ
  have hn : ∑ i,Complex.normSq (tiPolynomialState n t (tiInvariantCoefficients n U t) i)=1 := by
    simpa only [Normalized,← Complex.normSq_eq_norm_sq] using hψ
  simpa only [ti_state_norm_sum] using hn

/-- If a translation-commuting unitary carries the queried polynomial state for `a` to the next
polynomial state for `b`, then their polynomial magnitudes agree at every root of `z ^ n =
(-1) ^ t`. -/
theorem ti_invariant_transition_match (n t : ℕ) [NeZero n] (ht : 0<t)
    (U : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hu : U ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ)
    (hc : tiTranslation n*U=U*tiTranslation n) (a b : Fin n → ℂ)
    (he : ApplyGate U (ApplyGate (PhaseOracle (ospBit n 0)) (tiPolynomialState n (t-1) a)) =
      tiPolynomialState n t b) (z : ℂ) (hz : z^n=(-1:ℂ)^t) :
    ‖tiPolyEval b z‖=‖tiPolyEval a z‖ := by
  obtain ⟨l,hl,ha⟩ := ti_source_root_mode n t z hz
  rw [ti_query_zero_state n t ht] at he
  have hn := ti_invariant_fourier_norm n U hu hc (-tiPolynomialState n t a) l
  have hneg : ApplyGate (QFTMatrix (2*n))ᴴ (-tiPolynomialState n t a) l =
      -(ApplyGate (QFTMatrix (2*n))ᴴ (tiPolynomialState n t a) l) := by
    simp only [ApplyGate,Matrix.mulVec_neg,Pi.neg_apply]
  rw [he,hneg,norm_neg,ti_polynomial_fourier,ti_polynomial_fourier,if_pos ha,if_pos ha,hl,
    norm_mul,norm_mul] at hn
  have hs : (Real.sqrt (n:ℝ) : ℂ)≠0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos n))
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (inv_ne_zero hs)) hn

/-- Successive coefficient vectors extracted from a translation-invariant unitary program have
equal polynomial magnitudes at the roots specified by the transition step. -/
theorem ti_invariant_coefficients_match (n k : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hu : ∀ t ∈ Finset.Icc 1 k,U t ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ)
    (hc : ∀ t ∈ Finset.Icc 1 k,tiTranslation n*U t=U t*tiTranslation n)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 k) (z : ℂ) (hz : z^n=(-1:ℂ)^t) :
    ‖tiPolyEval (tiInvariantCoefficients n U t) z‖=
      ‖tiPolyEval (tiInvariantCoefficients n U (t-1)) z‖ := by
  have ht1 : 1≤t := (Finset.mem_Icc.mp ht).1
  have htk : t≤k := (Finset.mem_Icc.mp ht).2
  have he := ti_invariant_run_succ n (t-1) U
  rw [Nat.sub_add_cancel ht1,ti_invariant_prefix_state n k U hc t htk,
    ti_invariant_prefix_state n k U hc (t-1) (by omega)] at he
  exact ti_invariant_transition_match n t (by omega) (U t) (hu t ht) (hc t ht) _ _ he.symm z hz

/-- For translation-commuting gates, the prefix run on input `j` is translation by `j.val` of
the polynomial state formed from the extracted zero-input coefficients. -/
theorem ti_invariant_prefix_all (n k : ℕ) [NeZero n]
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hc : ∀ t ∈ Finset.Icc 1 k,tiTranslation n*U t=U t*tiTranslation n)
    (t : ℕ) (ht : t≤k) (j : Fin (2*n)) :
    Run (PhaseOracle (ospBit n j)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n))) =
      ApplyGate ((tiTranslation n)^j.val) (tiPolynomialState n t (tiInvariantCoefficients n U t)) := by
  have hgate : ∀ A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ,
      Step.gate A ∈ tiInvariantQueryWord n t U → tiTranslation n*A=A*tiTranslation n := by
    intro A hA
    obtain ⟨s,hs,rfl⟩ := ti_invariant_gate_member n t U A hA
    apply hc s
    simp only [Finset.mem_Icc] at hs ⊢
    omega
  have he := ti_run_covariant n j (tiInvariantQueryWord n t U) hgate (Uniform (Fin (2*n)))
  rw [ti_translation_uniform,ti_invariant_prefix_state n k U hc t ht] at he
  exact he

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
