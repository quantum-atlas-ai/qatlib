/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedReturnedWordConsumersQuan
import Qatlib.Concepts.GramQueryCore.GramRealization.NoncoherentStateConversion

/-!
# Optimized state-conversion complexity endpoints

Proves coherent and noncoherent lower bounds from successful legal source words and relates word
query counts to the corresponding query complexities. Ancillary output states are handled
through `sourceGarbageEquiv`, normalization, and the entrywise product rule for Gram matrices.

`optimizedConversionEndpoints` combines these bounds with the constructed upper endpoints,
giving the tolerance changes and logarithmic error overhead recorded in
`OptimizedConversionEndpoints`. This is the state-conversion comparison associated with
[LeeEtAl2011].

## Main statements

* `sourceGarbageTarget_gram`: output and ancillary Gram matrices combine by entrywise
  multiplication.
* `sourceCoherent_raw_lower`: the coherent raw quantity is at most twice coherent query
  complexity.
* `sourceNoncoherent_raw_lower`: the noncoherent raw quantity is at most twice noncoherent query
  complexity.
* `optimizedConversionEndpoints`: establishes the uniform coherent and noncoherent endpoint
  comparisons.

## References

* [Lee et al., Theorem 4.9][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics

namespace Qatlib.Concepts.QueryComplexity.StateConversion
open Matrix
open scoped Classical BigOperators ENNReal ComplexOrder

/-- Reorders the source register into the output register `H` followed by the combined ancillary
registers. -/
def sourceGarbageEquiv (n q r : ℕ) (H : Type) :
    SourceSpace n q H r ≃ H × ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)) where
  toFun p := (p.2.1.2,(p.1,(p.2.1.1,p.2.2)))
  invFun p := (p.2.1,((p.2.2.1,p.1),p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The source garbage target is the tensor product of the output and ancillary states relabeled
into source-register order. -/
theorem sourceGarbageTarget_relabel {H : Type} {n q r : ℕ} (σ : QState H)
    (ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r))) :
    sourceGarbageTarget n q r σ ξ=relabelState (sourceGarbageEquiv n q r H).symm (qStateTensor σ ξ) := rfl

/-- A source garbage target is normalized when both its output state and ancillary state are
normalized. -/
theorem sourceGarbageTarget_normalized {H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (σ : QState H) (ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)))
    (hσ : Normalized σ) (hξ : Normalized ξ) : Normalized (sourceGarbageTarget n q r σ ξ) := by
  rw [sourceGarbageTarget_relabel]
  exact normalized_relabelState _ (normalized_qStateTensor hσ hξ)

/-- The Gram matrix of the source garbage targets is the entrywise product of the output and
ancillary Gram matrices. -/
theorem sourceGarbageTarget_gram {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (σ : X → QState H)
    (ξ : X → QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r))) :
    gramStateMatrix (fun x => sourceGarbageTarget n q r (σ x) (ξ x))=
      gramStateMatrix σ ⊙ gramStateMatrix ξ := by
  rw [← gramStateMatrix_qStateTensor σ ξ]
  ext x y
  simp only [gramStateMatrix,sourceGarbageTarget_relabel]
  exact inner_relabelState _ _ _

/-- For normalized state families and `0 < ε ≤ 1/3`, a legal coherently successful source word
bounds `sourceQDelta` at tolerance `2 * sqrt (2 * ε)` by twice its query count. -/
theorem sourceCoherent_actual_word_raw_lower {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q r : ℕ}
    (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hε : 0<ε) (hε1 : ε≤1/3)
    (C : SourceWord (SourceSpace n q H r)) (hC : sourceWordLegal C)
    (hSuccess : ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥ Real.sqrt (1-ε)) :
    sourceQDelta input (2*Real.sqrt (2*ε)) (gramStateMatrix ρ) (gramStateMatrix σ) ≤
      (2 : ℝ≥0∞)*(sourceWordCalls C : ℝ≥0∞) := by
  let out :=
      fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ sourceClean n q r hr false (ρ x)
  let target := fun x => sourceClean n q r hr true (σ x)
  have hOut (x : X) : Normalized (out x) := normalized_applyGate
    (sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) C hC)
    (sourceClean_normalized n q r hr false _ (hn x).1)
  have hTarget (x : X) : Normalized (target x) := sourceClean_normalized n q r hr true _ (hn x).2
  let T := gramStateMatrix out
  have hTPSD : T.PosSemidef := gramStateMatrix_posSemidef out
  have hFeas : sourceUnfiltered (T-gramStateMatrix σ)≤ENNReal.ofReal (2*Real.sqrt (2*ε)) := by
    rw [← sourceGram_clean_gram n q r hr true σ]
    exact generalOutputGramBridges.2.1 X (SourceSpace n q H r) out target ε (fun x => ⟨hOut x,hTarget x⟩) hε.le
      (by linarith) hSuccess
  have hObj : sourceRectValue (gramStateMatrix ρ-T) (sourceAlphabetDelta input)≤ENNReal.ofReal (2*sourceWordCalls C) :=
    generalOutputGramBridges.1 X H n q r hr input ρ C (fun x => (hn x).1) hC
  let τ : {T : Matrix X X ℂ // T.PosSemidef ∧
      sourceUnfiltered (T-gramStateMatrix σ)≤ENNReal.ofReal (2*Real.sqrt (2*ε))} := ⟨T,hTPSD,hFeas⟩
  have hle : sourceQDelta input (2*Real.sqrt (2*ε)) (gramStateMatrix ρ) (gramStateMatrix σ)≤
      sourceRectValue (gramStateMatrix ρ-τ.val) (sourceAlphabetDelta input) :=
    iInf_le (fun T : {T : Matrix X X ℂ // T.PosSemidef ∧
      sourceUnfiltered (T-gramStateMatrix σ)≤ENNReal.ofReal (2*Real.sqrt (2*ε))} =>
      sourceRectValue (gramStateMatrix ρ-T.val) (sourceAlphabetDelta input)) τ
  exact hle.trans (hObj.trans_eq (by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_natCast]
    norm_num))

/-- For normalized state families and `0 < ε ≤ 1/3`, `sourceQDelta` at tolerance `2 * sqrt (2 *
ε)` is at most twice the coherent query complexity. -/
theorem sourceCoherent_raw_lower {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hε : 0<ε) (hε1 : ε≤1/3) :
    sourceQDelta input (2*Real.sqrt (2*ε)) (gramStateMatrix ρ) (gramStateMatrix σ) ≤
      (2 : ℝ≥0∞)*sourceCoherentQ input ρ σ ε := by
  unfold sourceCoherentQ
  rw [sInf_eq_iInf]
  simp_rw [ENNReal.mul_iInf_of_ne (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠⊤)]
  apply le_iInf
  intro b
  apply le_iInf
  rintro ⟨r,hr,C,hb,hC,hSuccess⟩
  rw [hb]
  exact sourceCoherent_actual_word_raw_lower hr input ρ σ ε hn hε hε1 C hC hSuccess

/-- For normalized state families and `0 < ε ≤ 1/3`, a legal source word achieving the required
overlap with normalized garbage targets bounds `sourceQNoncoherentDelta` at tolerance `2 *
sqrt (2 * ε)` by twice its query count. -/
theorem sourceNoncoherent_actual_word_raw_lower {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q r : ℕ}
    (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hε : 0<ε) (hε1 : ε≤1/3)
    (C : SourceWord (SourceSpace n q H r)) (hC : sourceWordLegal C)
    (hSuccess : ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p)*sourceGarbageTarget n q r (σ x) ξ p‖ ≥ Real.sqrt (1-ε)) :
    sourceQNoncoherentDelta input (2*Real.sqrt (2*ε)) (gramStateMatrix ρ) (gramStateMatrix σ) ≤
      (2 : ℝ≥0∞)*(sourceWordCalls C : ℝ≥0∞) := by
  choose ξ hξ hOver using hSuccess
  let out :=
      fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ sourceClean n q r hr false (ρ x)
  let χ := fun x => sourceGarbageTarget n q r (σ x) (ξ x)
  let a := fun x => overlapPhase (Qatlib.Foundations.PureStateMath.Inner (out x) (χ x))
  let ξ' := fun x p => a x*ξ x p
  let χ' := fun x => sourceGarbageTarget n q r (σ x) (ξ' x)
  have hξ' (x : X) : Normalized (ξ' x) := normalized_phase (ξ x) (hξ x) (a x) (overlapPhase_norm _)
  have hχ' (x : X) : Normalized (χ' x) :=
      sourceGarbageTarget_normalized (σ x) (ξ' x) (hn x).2 (hξ' x)
  have hOut (x : X) : Normalized (out x) := normalized_applyGate
    (sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) C hC)
    (sourceClean_normalized n q r hr false _ (hn x).1)
  have hPhase (x : X) : Qatlib.Foundations.PureStateMath.Inner (out x) (χ' x)=(‖Qatlib.Foundations.PureStateMath.Inner (out x) (χ x)‖ : ℂ) := by
    calc
      _ = a x*Qatlib.Foundations.PureStateMath.Inner (out x) (χ x) := by
        simp only [inner_apply,χ',χ,ξ',sourceGarbageTarget]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = _ := overlapPhase_mul _
  have hOverlap (x : X) : (Qatlib.Foundations.PureStateMath.Inner (out x) (χ' x)).re≥Real.sqrt (1-ε) := by
    rw [hPhase,Complex.ofReal_re]
    exact hOver x
  let T := gramStateMatrix out
  let K := gramStateMatrix ξ'
  have hTPSD : T.PosSemidef := gramStateMatrix_posSemidef out
  have hKPSD : K.PosSemidef := gramStateMatrix_posSemidef ξ'
  have hKdiag (x : X) : K x x=1 := (normalized_iff_inner_self _).mp (hξ' x)
  have hFeas : sourceUnfiltered (T-gramStateMatrix σ ⊙ K)≤ENNReal.ofReal (2*Real.sqrt (2*ε)) := by
    rw [← sourceGarbageTarget_gram σ ξ']
    exact generalOutputGramBridges.2.1 X (SourceSpace n q H r) out χ' ε
        (fun x => ⟨hOut x,hχ' x⟩) hε.le (by linarith) hOverlap
  have hObj : sourceRectValue (gramStateMatrix ρ-T) (sourceAlphabetDelta input)≤ENNReal.ofReal (2*sourceWordCalls C) :=
    generalOutputGramBridges.1 X H n q r hr input ρ C (fun x => (hn x).1) hC
  let τ0 : {T : Matrix X X ℂ // T.PosSemidef} := ⟨T,hTPSD⟩
  let κ0 : {K : Matrix X X ℂ // K.PosSemidef ∧ ∀ x, K x x=1} := ⟨K,hKPSD,hKdiag⟩
  have hInner : (⨅ K : {K : Matrix X X ℂ // K.PosSemidef ∧ ∀ x, K x x=1},
      if sourceUnfiltered (T-gramStateMatrix σ ⊙ K.val)≤ENNReal.ofReal (2*Real.sqrt (2*ε)) then
        sourceRectValue (gramStateMatrix ρ-T) (sourceAlphabetDelta input) else ⊤) ≤
        (2 : ℝ≥0∞)*(sourceWordCalls C : ℝ≥0∞) := by
    refine (iInf_le _ κ0).trans ?_
    rw [if_pos hFeas]
    exact hObj.trans_eq (by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_natCast]
      norm_num)
  exact (iInf_le (fun τ : {T : Matrix X X ℂ // T.PosSemidef} =>
    ⨅ K : {K : Matrix X X ℂ // K.PosSemidef ∧ ∀ x, K x x=1},
      if sourceUnfiltered (τ.val-gramStateMatrix σ ⊙ K.val)≤ENNReal.ofReal (2*Real.sqrt (2*ε)) then
        sourceRectValue (gramStateMatrix ρ-τ.val) (sourceAlphabetDelta input) else ⊤) τ0).trans hInner

/-- For normalized state families and `0 < ε ≤ 1/3`, `sourceQNoncoherentDelta` at tolerance `2 *
sqrt (2 * ε)` is at most twice the noncoherent query complexity. -/
theorem sourceNoncoherent_raw_lower {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hε : 0<ε) (hε1 : ε≤1/3) :
    sourceQNoncoherentDelta input (2*Real.sqrt (2*ε)) (gramStateMatrix ρ) (gramStateMatrix σ) ≤
      (2 : ℝ≥0∞)*sourceNoncoherentQ input ρ σ ε := by
  unfold sourceNoncoherentQ
  rw [sInf_eq_iInf]
  simp_rw [ENNReal.mul_iInf_of_ne (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠⊤)]
  apply le_iInf
  intro b
  apply le_iInf
  rintro ⟨r,hr,C,hb,hC,hSuccess⟩
  rw [hb]
  exact sourceNoncoherent_actual_word_raw_lower hr input ρ σ ε hn hε hε1 C hC hSuccess

/-- Any legal source word satisfying the coherent overlap threshold gives an upper bound on
coherent query complexity by its query count. -/
theorem sourceCoherentQ_le_calls {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (C : SourceWord (SourceSpace n q H r)) (hC : sourceWordLegal C)
    (hSuccess : ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥ Real.sqrt (1-ε)) :
    sourceCoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞) := by
  unfold sourceCoherentQ
  refine sInf_le ?_
  simp only [Set.mem_setOf_eq]
  exact ⟨r,hr,C,rfl,hC,hSuccess⟩

/-- Any legal source word satisfying the noncoherent overlap threshold with normalized ancillary
states bounds noncoherent query complexity by its query count. -/
theorem sourceNoncoherentQ_le_calls {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (C : SourceWord (SourceSpace n q H r)) (hC : sourceWordLegal C)
    (hSuccess : ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p)*sourceGarbageTarget n q r (σ x) ξ p‖ ≥ Real.sqrt (1-ε)) :
    sourceNoncoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞) := by
  unfold sourceNoncoherentQ
  refine sInf_le ?_
  simp only [Set.mem_setOf_eq]
  exact ⟨r,hr,C,rfl,hC,hSuccess⟩

/-- A real upper bound on a source word's query count induces the corresponding upper bound in
the extended nonnegative reals. -/
theorem sourceCalls_le_ofReal {n q : ℕ} {r : ℕ} {H : Type} {C : SourceWord (SourceSpace n q H r)}
    {B : ℝ} (h : (sourceWordCalls C : ℝ)≤B) :
    (sourceWordCalls C : ℝ≥0∞) ≤ ENNReal.ofReal B := by
  have := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_natCast] at this

/-- Coherent and noncoherent state-conversion query complexities satisfy the optimized lower and
upper endpoint comparisons with their raw filtered-norm quantities. See [Lee et al., Theorem
4.9][LeeEtAl2011]. -/
theorem optimizedConversionEndpoints : OptimizedConversionEndpoints := by
  refine ⟨17179869184,by norm_num,?_⟩
  intro X _ _ H _ _ _ n q input ρ σ ε hn hε hε1
  have hlog : 0<Real.log (1/ε) := by
    have h1 : (1:ℝ) < 1/ε := by
      rw [lt_div_iff₀ hε, one_mul]
      linarith
    exact Real.log_pos h1
  have hε2 : 0<ε^2 := pow_pos hε 2
  have hcoeff : 0 < (Real.log (1/ε)/ε^2 : ℝ) := div_pos hlog hε2
  refine ⟨?_,?_,?_,?_⟩
  · exact (sourceCoherent_raw_lower input ρ σ ε hn hε hε1).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ≥0∞)≤17179869184) bot_le)
  · set δ := sourceQDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ)
    by_cases hδ : δ=⊤
    · have heq : (↑(17179869184:ℕ) * ENNReal.ofReal (Real.log (1/ε)/ε^2) * δ : ℝ≥0∞)=⊤ := by
        rw [hδ]
        exact ENNReal.mul_top (by
          have hpos : (0:ℝ≥0∞) < ENNReal.ofReal (Real.log (1/ε)/ε^2) :=
              ENNReal.ofReal_pos.mpr hcoeff
          exact mul_ne_zero (by norm_num : ((17179869184:ℕ):ℝ≥0∞) ≠ 0) (ne_of_gt hpos))
      rw [heq]
      exact le_top
    · have hW : 0≤δ.toReal := ENNReal.toReal_nonneg
      have hle : δ ≤ ENNReal.ofReal δ.toReal := by
        rw [ENNReal.ofReal_toReal hδ]
      obtain ⟨r,hr,C,hC,hreal,hok⟩ := sourceCoherent_raw_budget_word input ρ σ ε δ.toReal
        hn hε hε1 hW hle
      have hQ : sourceCoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞) :=
        sourceCoherentQ_le_calls hr input ρ σ ε C hC hok
      have hcalls := sourceCalls_le_ofReal hreal
      refine hQ.trans (hcalls.trans ?_)
      have hm : (17179869184*δ.toReal*Real.log (1/ε)/ε^2 : ℝ) =
          17179869184*(Real.log (1/ε)/ε^2)*δ.toReal := by ring
      rw [hm,ENNReal.ofReal_mul (by positivity)]
      have h2 : ENNReal.ofReal (17179869184*(Real.log (1/ε)/ε^2)) =
          (17179869184 : ℝ≥0∞)*ENNReal.ofReal (Real.log (1/ε)/ε^2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤17179869184)]
        exact_mod_cast rfl
      rw [h2,ENNReal.ofReal_toReal hδ]
      exact le_rfl
  · exact (sourceNoncoherent_raw_lower input ρ σ ε hn hε hε1).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ≥0∞)≤17179869184) bot_le)
  · set δ := sourceQNoncoherentDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ)
    by_cases hδ : δ=⊤
    · have heq : (↑(17179869184:ℕ) * ENNReal.ofReal (Real.log (1/ε)/ε^2) * δ : ℝ≥0∞)=⊤ := by
        rw [hδ]
        exact ENNReal.mul_top (by
          have hpos : (0:ℝ≥0∞) < ENNReal.ofReal (Real.log (1/ε)/ε^2) :=
              ENNReal.ofReal_pos.mpr hcoeff
          exact mul_ne_zero (by norm_num : ((17179869184:ℕ):ℝ≥0∞) ≠ 0) (ne_of_gt hpos))
      rw [heq]
      exact le_top
    · have hW : 0≤δ.toReal := ENNReal.toReal_nonneg
      have hle : δ ≤ ENNReal.ofReal δ.toReal := by
        rw [ENNReal.ofReal_toReal hδ]
      obtain ⟨r,hr,C,hC,hreal,hok⟩ := sourceNoncoherent_raw_budget_word input ρ σ ε δ.toReal
        hn hε hε1 hW hle
      have hQ : sourceNoncoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞) :=
        sourceNoncoherentQ_le_calls hr input ρ σ ε C hC hok
      have hcalls := sourceCalls_le_ofReal hreal
      refine hQ.trans (hcalls.trans ?_)
      have hm : (17179869184*δ.toReal*Real.log (1/ε)/ε^2 : ℝ) =
          17179869184*(Real.log (1/ε)/ε^2)*δ.toReal := by ring
      rw [hm,ENNReal.ofReal_mul (by positivity)]
      have h2 : ENNReal.ofReal (17179869184*(Real.log (1/ε)/ε^2)) =
          (17179869184 : ℝ≥0∞)*ENNReal.ofReal (Real.log (1/ε)/ε^2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤17179869184)]
        exact_mod_cast rfl
      rw [h2,ENNReal.ofReal_toReal hδ]
      exact le_rfl

end Qatlib.Concepts.QueryComplexity.StateConversion
