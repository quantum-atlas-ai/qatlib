/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.PhaseDetectionStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionPhaseProgram
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Phase detection by source words

Compiles phase reflection circuits into legal source words while preserving their matrices and
query counts. Clock routing combines repeated phase registers into a single register whose zero
state is preserved.

The spectral estimates prove exact action on fixed states and approximate sign reversal away
from the low-phase subspace, with quantitative query and workspace bounds as in [LeeEtAl2011].

## Main statements

* `phaseSourceCompile_matrix`: identifies the compiled word's matrix.
* `sourcePhaseHighError`: controls the reflection error outside the low-phase subspace.
* `phaseDetection`: proves the phase detection specification.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Translates an adjoint circuit step into a source letter, relabeling gates and retaining the
direction of oracle calls. -/
def phaseSourceStep {I J : Type} (e : I ≃ J) : AdjointStep I → Matrix J J ℂ ⊕ Bool
  | .gate U => .inl (relabelGate e U)
  | .forward => .inr false
  | .backward => .inr true

/-- Compiles an adjoint circuit into a source word by reversing its steps and translating each
step through a basis equivalence. -/
def phaseSourceCompile {I J : Type} (e : I ≃ J) (cs : List (AdjointStep I)) : SourceWord J :=
  cs.reverse.map (phaseSourceStep e)

/-- Compilation preserves the number of forward and backward oracle calls. -/
theorem phaseSourceCompile_calls {I J : Type} (e : I ≃ J) (cs : List (AdjointStep I)) :
    sourceWordCalls (phaseSourceCompile e cs) = adjointQueryCount cs := by
  have hmap (ds : List (AdjointStep I)) : sourceWordCalls (ds.map (phaseSourceStep e)) = adjointQueryCount ds := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      unfold sourceWordCalls at ih ⊢
      rw [List.map_cons, List.countP_cons]
      cases d <;> simp [phaseSourceStep, adjointQueryCount, ih]
  have hrev : adjointQueryCount cs.reverse = adjointQueryCount cs := by
    induction cs with
    | nil => rfl
    | cons c cs ih => cases c <;> simp [List.reverse_cons,adjointQueryCount_append,adjointQueryCount,ih]
  exact (hmap cs.reverse).trans hrev

/-- A well-formed adjoint circuit compiles to a legal source word. -/
theorem phaseSourceCompile_legal {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (cs : List (AdjointStep I))
    (hcs : WellFormedAdjointCircuit cs) : sourceWordLegal (phaseSourceCompile e cs) := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hd' := List.mem_reverse.mp hd
  cases d with
  | gate U => exact (relabelGate_mem_unitaryGroup e U).mpr (hcs U hd')
  | forward => trivial
  | backward => trivial

/-- The compiled source word evaluates to the relabeling of the original adjoint circuit's
matrix. -/
theorem phaseSourceCompile_matrix {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (O : Matrix I I ℂ) (cs : List (AdjointStep I)) :
    sourceWordMatrix (relabelGate e O) (phaseSourceCompile e cs) = relabelGate e (evaluate O cs) := by
  have hstar : (relabelGate e O)ᴴ = relabelGate e Oᴴ := by ext i j; rfl
  have hprod (ds : List (AdjointStep I)) :
      (ds.map (fun c => match phaseSourceStep e c with | .inl U => U | .inr b => if b then (relabelGate e O)ᴴ else relabelGate e O)).prod =
        relabelGate e (evaluate O ds) := by
    induction ds with
    | nil => exact (CircuitRelabel.relabelGate_one e).symm
    | cons c ds ih =>
      rw [List.map_cons, List.prod_cons, ih]
      cases c <;> simp
          [phaseSourceStep,evaluate,instructionMatrix,hstar,CircuitRelabel.relabelGate_mul]
  unfold sourceWordMatrix phaseSourceCompile
  simp only [List.map_map, ← List.map_reverse, List.reverse_reverse]
  exact hprod cs

/-- A finite equivalence packing `k` clock registers of size `2^a` into one register of size
`2^(a*k)`. -/
def sourcePhaseClockBase (a k : ℕ) : (Fin k → Fin (2^a)) ≃ Fin (2^(a*k)) :=
  (Fintype.equivFin (Fin k → Fin (2^a))).trans
    (Equiv.cast (congrArg Fin (by simp [Fintype.card_fin,pow_mul])))

/-- A clock-packing equivalence adjusted to send the tuple of zero clock values to zero. -/
def sourcePhaseClock (a k : ℕ) : (Fin k → Fin (2^a)) ≃ Fin (2^(a*k)) :=
  (sourcePhaseClockBase a k).trans (Equiv.swap (sourcePhaseClockBase a k (fun _ => 0)) 0)

/-- The clock-packing equivalence sends the all-zero clock tuple to zero. -/
theorem sourcePhaseClock_zero (a k : ℕ) : sourcePhaseClock a k (fun _ => 0) = 0 := by
  simp [sourcePhaseClock]

/-- Reorders the phase reflection basis and packs its clock registers into a single finite
register. -/
def sourcePhaseRoute (H : Type) (a k : ℕ) :
    PhaseReflectionSpace H (2^a) k ≃ ((Bool × H) × Fin (2^(a*k))) where
  toFun p := (p.2,sourcePhaseClock a k p.1)
  invFun p := ((sourcePhaseClock a k).symm p.2,p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- Routing the parallel controlled oracle gives the source controlled oracle with its packed
clock register. -/
theorem sourcePhaseRoute_oracle (H : Type) [DecidableEq H] (a k : ℕ) (U : Matrix H H ℂ) :
    relabelGate (sourcePhaseRoute H a k) (parallelOracle (controlOracle U)) =
      sourceControlledU (2^(a*k)) U := by
  ext p t
  have heq : (sourcePhaseClock a k).symm p.2 = (sourcePhaseClock a k).symm t.2 ↔ p.2=t.2 :=
    (sourcePhaseClock a k).symm.injective.eq_iff
  simp [relabelGate,sourcePhaseRoute,parallelOracle,Qatlib.Concepts.BlockEncoding.LCU.select,
    controlOracle,sourceControlledU,heq]
  split_ifs <;> simp_all [Matrix.one_apply]

/-- Routing the phase reflection embedding gives the state with a false control and a zero
packed clock. -/
theorem sourcePhaseRoute_embed {H : Type} [DecidableEq H] (a k : ℕ) (ψ : QState H) :
    relabelState (sourcePhaseRoute H a k) (phaseReflectionEmbed (2^a) k ψ) =
      TensorState (TensorState (Ket false) ψ) (Ket (0 : Fin (2^(a*k)))) := by
  have hz (c : Fin k → Fin (2^a)) : (∀ j, c j=0) ↔ c=(fun _ => 0) := by
    constructor
    · intro h; funext j; exact h j
    · intro h; subst c; simp
  have heq (i : Fin (2^(a*k))) : (sourcePhaseClock a k).symm i=(fun _ => 0) ↔ i=0 := by
    rw [Equiv.symm_apply_eq,sourcePhaseClock_zero]
  ext p
  simp [relabelState,sourcePhaseRoute,phaseReflectionEmbed,TensorState,Ket,hz,heq]
  split_ifs <;> simp_all

/-- For a principal angle in `(-π, π]`, the circular distance of its normalized phase from zero
is `|θ|/(2*π)`. -/
theorem sourcePrincipalPhaseDistance (θ : ℝ) (hlo : -Real.pi < θ)
    (hhi : θ ≤ Real.pi) : phaseDistance (θ/(2*Real.pi)) 0 = |θ|/(2*Real.pi) := by
  have hp : 0 < 2*Real.pi := by positivity
  by_cases he : θ=Real.pi
  · subst θ
    have hf : (Real.pi/(2*Real.pi) : ℝ)=1/2 := by field_simp
    rw [hf]
    norm_num [phaseDistance,abs_of_pos Real.pi_pos]
    field_simp
  · have hu : θ/(2*Real.pi)+1/2 < 1 := by
      have ht : θ<Real.pi := lt_of_le_of_ne hhi he
      have hh := (div_lt_iff₀ hp).mpr (show θ<(1/2 : ℝ)*(2*Real.pi) by nlinarith)
      linarith
    have hl : 0 ≤ θ/(2*Real.pi)+1/2 := by
      have hh := (lt_div_iff₀ hp).mpr (show (-1/2 : ℝ)*(2*Real.pi)<θ by nlinarith)
      linarith
    have hf : ⌊θ/(2*Real.pi)+1/2⌋=(0 : ℤ) := Int.floor_eq_iff.mpr (by simpa using! And.intro hl hu)
    simp only [phaseDistance,sub_zero,hf,Int.cast_zero,abs_div,abs_of_pos hp]

/-- For `K ≥ 1`, the selected power-of-two clock size lies between `16*K` and `32*K`, and its
bit count is at most `Nat.clog 2 (K+1) + 4`. -/
theorem sourcePhaseClock_bounds (K : ℕ) (hK : 1 ≤ K) :
    16*K ≤ 2^(Nat.clog 2 (16*K)) ∧
    2^(Nat.clog 2 (16*K)) ≤ 32*K ∧
    Nat.clog 2 (16*K) ≤ Nat.clog 2 (K+1)+4 := by
  have hl := Nat.le_pow_clog (by omega : 1<2) (16*K)
  have ha : 0 < Nat.clog 2 (16*K) := by
    have hh := (Nat.lt_clog_iff_pow_lt (by omega : 1<2) (x := 16*K) (y := 0)).mpr (by simp; omega)
    exact hh
  have hu := Nat.pow_pred_clog_lt_self (by omega : 1<2) (show 1<16*K by omega)
  simp only [Nat.pred_eq_sub_one] at hu
  have he : 2^(Nat.clog 2 (16*K))=2^(Nat.clog 2 (16*K)-1)*2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  refine ⟨hl, ?_, ?_⟩
  · rw [he]
    omega
  · apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have hk := Nat.le_pow_clog (by omega : 1<2) (K+1)
    norm_num only [show (2 : ℕ)^4=16 by norm_num]
    omega

/-- The columns of a unitary matrix are orthonormal, and every state is reconstructed from its
adjoint coordinates in those columns. -/
theorem sourcePhaseColumns {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (ψ : QState H) :
    (∀ j l, Inner (fun i => V i j) (fun i => V i l)=if j=l then 1 else 0) ∧
    (∑ j, (Vᴴ *ᵥ ψ) j • (fun i => V i j))=ψ := by
  have hVV : V*Vᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  constructor
  · intro j l
    have hc (j : H) : V *ᵥ Ket j = fun i => V i j := by
      ext i
      simp [Matrix.mulVec,dotProduct,Ket]
    rw [← hc j,← hc l]
    exact (inner_applyGate hV (Ket j) (Ket l)).trans (inner_ket_ket j l)
  · have he : (∑ j, (Vᴴ *ᵥ ψ) j • (fun i => V i j))= V *ᵥ (Vᴴ *ᵥ ψ) := by
      ext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he,Matrix.mulVec_mulVec,hVV,Matrix.one_mulVec]

/-- For positive `δ`, the logarithmically chosen repetition count bounds the amplified phase
error by `δ`. -/
theorem sourcePhaseRepetitions (δ : ℝ) (hδ : 0<δ) :
    2*(1/2 : ℝ)^(2*(Nat.ceil (Real.log (2/min 1 δ))+1)) ≤ δ := by
  let d := min 1 δ
  let L := Nat.ceil (Real.log (2/d))+1
  have hd : 0<d := lt_min (by norm_num) hδ
  have hdδ : d≤δ := min_le_right _ _
  have hL : Real.log (2/d)≤(L : ℝ) := by
    dsimp [L]
    exact (Nat.le_ceil _).trans (by push_cast; linarith)
  have hlog : (1/2 : ℝ)<Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hb : Real.log 2-((2*L : ℕ) : ℝ)*Real.log 2 ≤ Real.log d := by
    rw [Real.log_div (by norm_num : (2 : ℝ)≠0) hd.ne'] at hL
    push_cast
    nlinarith [show (0 : ℝ)≤(L : ℝ) by positivity]
  have he := Real.exp_le_exp.mpr hb
  rw [Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<2),Real.exp_nat_mul,
    Real.exp_log hd] at he
  have hh : (1/2 : ℝ)^(2*L)=(Real.exp (Real.log 2)^(2*L))⁻¹ := by
    rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
    simp [inv_pow]
  change 2*(1/2 : ℝ)^(2*L)≤δ
  rw [hh,← div_eq_mul_inv]
  exact he.trans hdδ

/-- The columns of a unitary spectral basis are eigenvectors with the eigenvalues expressed
using their normalized phases. -/
theorem sourcePhaseEigenvectors {H : Type} [Fintype H] [DecidableEq H]
    (U V : Matrix H H ℂ) (angles : H → ℝ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hU : U=V*Matrix.diagonal (fun j => Complex.exp (Complex.I*angles j))*Vᴴ) :
    ∀ j, ApplyGate U (fun i => V i j)=
      Complex.exp (2*Real.pi*Complex.I*(angles j/(2*Real.pi))) • (fun i => V i j) := by
  have hVhV : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  intro j
  have hc : (fun i => V i j)=V *ᵥ Ket j := by
    ext i
    simp [Matrix.mulVec,dotProduct,Ket]
  have hp : (2*Real.pi*Complex.I*(angles j/(2*Real.pi)) : ℂ)=Complex.I*angles j := by
    field_simp
  rw [hp,hc]
  change U *ᵥ (V *ᵥ Ket j)=_
  rw [hU]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (Ket j) Vᴴ V,hVhV,Matrix.one_mulVec]
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  by_cases hij : i=j
  · subst i; simp [Matrix.mulVec_diagonal,Ket]
  · simp [Matrix.mulVec_diagonal,Ket,hij]

/-- A state annihilated by the low-phase projector has zero spectral coefficient at every angle
of absolute value at most `Θ`. -/
theorem sourcePhaseLowCoefficients {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (angles : H → ℝ) (Θ : ℝ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (ψ : QState H) (hψ : sourcePhaseProjector V angles Θ *ᵥ ψ=0) :
    ∀ j, |angles j|≤Θ → (Vᴴ *ᵥ ψ) j=0 := by
  have hVhV : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hz := congrArg (fun z => Vᴴ *ᵥ z) hψ
  simp only [sourcePhaseProjector,← Matrix.mulVec_mulVec] at hz
  rw [Matrix.mulVec_mulVec _ Vᴴ V,hVhV,Matrix.one_mulVec,Matrix.mulVec_zero] at hz
  intro j hj
  have hh := congrFun hz j
  simpa only [Matrix.mulVec_diagonal,if_pos hj,one_mul,Pi.zero_apply] using! hh

/-- Outside the low-phase subspace, a clock satisfying `2*π ≤ M*Θ` bounds the phase reflection's
error from sign reversal by `2*(1/2)^k` times the state norm. -/
theorem sourcePhaseHighError {H : Type} [Fintype H] [DecidableEq H]
    (M k : ℕ) (hM : 2≤M) (U V : Matrix H H ℂ) (angles : H → ℝ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hangles : ∀ j, -Real.pi<angles j ∧ angles j≤Real.pi)
    (hUV : U=V*Matrix.diagonal (fun j => Complex.exp (Complex.I*angles j))*Vᴴ)
    (Θ : ℝ) (hΘ : 0<Θ) (hsize : 2*Real.pi ≤ (M : ℝ)*Θ)
    (ψ : QState H) (hψ : sourcePhaseProjector V angles Θ *ᵥ ψ=0) :
    ‖toEuclidean_fromVec (phaseReflectionState U M k ψ+phaseReflectionEmbed M k ψ)‖ ≤
      2*(1/2 : ℝ)^k*‖toEuclidean_fromVec ψ‖ := by
  let v : H → QState H := fun j i => V i j
  let c := Vᴴ *ᵥ ψ
  let φ : H → ℝ := fun j => angles j/(2*Real.pi)
  obtain ⟨hv,hs⟩ := sourcePhaseColumns V hV ψ
  have he : ∀ j, ApplyGate U (v j)=Complex.exp (2*Real.pi*Complex.I*(φ j : ℂ)) • v j := by
    simpa only [φ,v,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat] using!
      sourcePhaseEigenvectors U V angles hV hUV
  have hzero := sourcePhaseLowCoefficients V angles Θ hV ψ hψ
  have hb (j : H) : ‖c j‖^2*‖qpeKernel M (φ j) (⟨0,by omega⟩ : Fin M)‖^(2*k) ≤
      ‖c j‖^2*(1/2 : ℝ)^(2*k) := by
    by_cases hj : |angles j|≤Θ
    · have hz : c j=0 := hzero j hj
      simp [hz]
    · have hg : Θ/(2*Real.pi)≤phaseDistance (φ j) 0 := by
        dsimp only [φ]
        rw [sourcePrincipalPhaseDistance _ (hangles j).1 (hangles j).2]
        exact div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hj)) (by positivity)
      have hk := phase_detection_zero_label_gap_bound M (by omega) (φ j)
        (Θ/(2*Real.pi)) (by positivity) hg
      have hhalf : 1/(2*(M : ℝ)*(Θ/(2*Real.pi)))≤(1/2 : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0<2*(M : ℝ)*(Θ/(2*Real.pi)))).mpr
        have hh : (M : ℝ)*Θ/(2*Real.pi)≥1 :=
          (le_div_iff₀ (by positivity : 0<2*Real.pi)).mpr (by simpa using! hsize)
        have he : (1/2 : ℝ)*(2*(M : ℝ)*(Θ/(2*Real.pi)))=(M : ℝ)*Θ/(2*Real.pi) := by ring
        rw [he]
        exact hh
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hk.trans hhalf) (2*k)) (sq_nonneg _)
  have heq := conversion_phase_packet_error_sq M k hM U hU v c φ he hv
  have hparse := degenerate_packet_norm_sq v c hv
  change (∑ j,c j • v j)=ψ at hs
  rw [hs] at heq hparse
  have hsq : ‖toEuclidean_fromVec (phaseReflectionState U M k ψ+phaseReflectionEmbed M k ψ)‖^2 ≤
      (2*(1/2 : ℝ)^k*‖toEuclidean_fromVec ψ‖)^2 := by
    rw [heq]
    have hsum := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
    rw [← Finset.sum_mul,← hparse] at hsum
    have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ)≤4)
    convert! hh using 1
    rw [show 2*k=k*2 by omega,pow_mul]
    ring
  nlinarith [norm_nonneg (toEuclidean_fromVec (phaseReflectionState U M k ψ+phaseReflectionEmbed M k ψ)),
    show (0 : ℝ)≤2*(1/2 : ℝ)^k*‖toEuclidean_fromVec ψ‖ by positivity]

/-- Running the compiled phase word on the clean packed embedding agrees with routing the
original phase reflection state. -/
theorem sourcePhaseCompiledRun {H : Type} [Fintype H] [DecidableEq H]
    (a k : ℕ) (U : Matrix H H ℂ) (ψ : QState H) :
    sourceWordMatrix (sourceControlledU (2^(a*k)) U)
      (phaseSourceCompile (sourcePhaseRoute H a k) (phaseReflectionWord (2^a) k)) *ᵥ
      TensorState (TensorState (Ket false) ψ) (Ket (0 : Fin (2^(a*k)))) =
    relabelState (sourcePhaseRoute H a k) (phaseReflectionState U (2^a) k ψ) := by
  rw [← sourcePhaseRoute_oracle H a k U,phaseSourceCompile_matrix,← sourcePhaseRoute_embed]
  exact applyGate_relabelGate _ _ _

/-- Proves phase detection with exact action on fixed states, controlled error on high-phase
states, and query and workspace bounds as in [Lee et al., Theorem 4.3][LeeEtAl2011]. -/
theorem phaseDetection : PhaseDetection := by
  refine ⟨128,by norm_num,?_⟩
  intro H _ _ Θ δ hΘ hδ
  let K := max 1 (Nat.ceil (1/Θ))
  let L := Nat.ceil (Real.log (2/min 1 δ))+1
  let a := Nat.clog 2 (16*K)
  let k := 2*L
  let M := 2^a
  have hK : 1≤K := le_max_left _ _
  have hL : 1≤L := by dsimp [L]; omega
  obtain ⟨hMl,hMu,ha⟩ := sourcePhaseClock_bounds K hK
  change 16*K≤M at hMl
  change M≤32*K at hMu
  change a≤Nat.clog 2 (K+1)+4 at ha
  have hM : 2≤M := by omega
  have hw := phase_reflection_actual_queries_and_macros (I := H) M k hM
  refine ⟨a*k,phaseSourceCompile (sourcePhaseRoute H a k) (phaseReflectionWord M k),
    phaseSourceCompile_legal _ _ hw.1,?_,?_,?_⟩
  · rw [phaseSourceCompile_calls,hw.2.1]
    change 2*(2*L)*(M-1)≤128*K*L
    nlinarith [Nat.mul_le_mul_right L hMu,Nat.mul_le_mul_right (4*L) (Nat.sub_le M 1)]
  · change a*(2*L)≤128*(Nat.clog 2 (K+1)+1)*L
    have hh : a*2≤128*(Nat.clog 2 (K+1)+1) := by omega
    have hb := Nat.mul_le_mul_right L hh
    nlinarith
  · intro U V angles hU hV hangles hUV ψ
    (try dsimp only)
    constructor
    · intro hψ
      have he : ApplyGate U ψ=Complex.exp (2*Real.pi*Complex.I*(0 : ℝ)) • ψ := by
        simpa only [ApplyGate,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul] using! hψ
      have hf := (phase_reflection_actual_eigenstate_error M k hM U ψ 0 hU he).1
        (by norm_num [phaseDistance])
      rw [sourcePhaseCompiledRun,hf,sourcePhaseRoute_embed]
    · intro hψ
      have hKi : (1/Θ : ℝ)≤(K : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (1/Θ))))
      have hKΘ : 1≤(K : ℝ)*Θ := (div_le_iff₀ hΘ).mp hKi
      have hMΘ : 2*Real.pi≤(M : ℝ)*Θ := by
        have hh : (16 : ℝ)*(K : ℝ)≤(M : ℝ) := by exact_mod_cast hMl
        have hb := mul_le_mul_of_nonneg_right hh hΘ.le
        nlinarith [Real.pi_lt_four]
      have herr := sourcePhaseHighError M k hM U V angles hU hV hangles hUV Θ hΘ hMΘ ψ hψ
      rw [sourcePhaseCompiledRun,← sourcePhaseRoute_embed]
      change ‖toEuclidean_fromVec (relabelState (sourcePhaseRoute H a k)
        (phaseReflectionState U M k ψ+phaseReflectionEmbed M k ψ))‖≤_
      rw [norm_toEuclidean_relabelState]
      exact herr.trans (mul_le_mul_of_nonneg_right (sourcePhaseRepetitions δ hδ)
        (norm_nonneg _))

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
