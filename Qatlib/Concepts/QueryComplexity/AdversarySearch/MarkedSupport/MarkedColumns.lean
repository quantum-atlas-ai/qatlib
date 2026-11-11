/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Concepts.MixedFidelity.FidelityMetric.RankOneTraceNormBound
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.ReferenceError.RefTraceError
/-! Marked-column localization, quantum query energy, and adaptive hybrid.
The 2/sqrt(N) local trace-distance factor is derived from actual matrix
unitarity and column agreement outside disjoint data fibers. The proof uses
one common rho-only purification and handles arbitrary subnormalized PSD
inputs. Reference registers are mathematical witnesses, not prepared resources.

The concrete block-encoding hard family, its controlled/adjoint mode matrices,
numerical-range geometry, finite-protocol compilation and block-output
reduction are separate obligations. This module does not close that task. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder Matrix.Norms.L2Operator

/-- The finite protocol identity or bound `rankOne_hilbert` holds under exactly the displayed hypotheses. -/
private theorem rankOne_hilbert {I : Type} [Fintype I] [DecidableEq I] (u v : QState I) :
    Matrix.traceNorm (Matrix.vecMulVec u (star v))≤
      ‖toEuclidean_fromVec u‖*‖toEuclidean_fromVec v‖ := by
  have hh := traceNorm_rankOne_le u v
  simp only [Complex.normSq_eq_norm_sq] at hh
  rw [←norm_toEuclidean_fromVec_sq,←norm_toEuclidean_fromVec_sq,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)] at hh
  exact hh

/-- The finite protocol identity or bound `outer_difference` holds under exactly the displayed hypotheses. -/
private theorem outer_difference {I : Type} [Fintype I] [DecidableEq I] (u v : QState I) :
    outerProduct u-outerProduct v=
      Matrix.vecMulVec (u-v) (star u)+Matrix.vecMulVec v (star (u-v)) := by
  ext i j
  simp only [outerProduct_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.vecMulVec_apply,
    Pi.star_apply,Pi.sub_apply,star_sub,RCLike.star_def]
  ring

/-- Raw pure-state trace difference: no normalization or positive-mass division. -/
theorem pure_raw_trace_difference {I : Type} [Fintype I] [DecidableEq I] (u v : QState I) :
    Matrix.traceNorm (outerProduct u-outerProduct v)≤
      (‖toEuclidean_fromVec u‖+‖toEuclidean_fromVec v‖)*‖toEuclidean_fromVec (u-v)‖ := by
  rw [outer_difference]
  have hh := (Matrix.traceNorm_add_le _ _).trans (add_le_add (rankOne_hilbert (u-v) u) (rankOne_hilbert v (u-v)))
  nlinarith


/-- One and the same raw purification can be used for every hidden unitary.
The witness is not chosen separately as a function of the hidden instance. -/
theorem reduced_unitary_trace_difference {D E : ℕ} (U V : Operator D)
    (hU : U∈Matrix.unitaryGroup (Fin D) ℂ) (hV : V∈Matrix.unitaryGroup (Fin D) ℂ)
    (ψ : QState (Fin D × Fin E)) :
    Matrix.traceNorm (U*PartialTrace (outerProduct ψ)*U.conjTranspose-
      V*PartialTrace (outerProduct ψ)*V.conjTranspose)/2≤
      ‖toEuclidean_fromVec ψ‖*‖toEuclidean_fromVec
        (ApplyGate (TensorGate U (1 : Operator E)) ψ-ApplyGate (TensorGate V (1 : Operator E)) ψ)‖ := by
  let u := ApplyGate (TensorGate U (1 : Operator E)) ψ
  let v := ApplyGate (TensorGate V (1 : Operator E)) ψ
  have he : Matrix.traceRight (outerProduct u-outerProduct v)=
      U*PartialTrace (outerProduct ψ)*U.conjTranspose-
      V*PartialTrace (outerProduct ψ)*V.conjTranspose := by
    change PartialTrace (outerProduct u-outerProduct v)=_
    have hs : PartialTrace (outerProduct u-outerProduct v)=PartialTrace (outerProduct u)-PartialTrace (outerProduct v) := by
      ext i j
      simp only [PartialTrace,Matrix.sub_apply,Finset.sum_sub_distrib]
    rw [hs]
    exact congrArg₂ (fun A B => A-B) (partialTrace_outerProduct_apply_tensorLeft D E U ψ)
      (partialTrace_outerProduct_apply_tensorLeft D E V ψ)
  have hc := traceRight_hermitian_trace_contraction (outerProduct u-outerProduct v)
    ((outerProduct_posSemidef u).isHermitian.sub (outerProduct_posSemidef v).isHermitian)
  rw [he] at hc
  have hu : ‖toEuclidean_fromVec u‖=‖toEuclidean_fromVec ψ‖ :=
    norm_applyGate_of_mem_unitaryGroup (tensorGate_one_unitary hU) ψ
  have hv : ‖toEuclidean_fromVec v‖=‖toEuclidean_fromVec ψ‖ :=
    norm_applyGate_of_mem_unitaryGroup (tensorGate_one_unitary hV) ψ
  have hp := pure_raw_trace_difference u v
  rw [hu,hv] at hp
  exact (div_le_div_of_nonneg_right (hc.trans hp) (by norm_num)).trans_eq (by ring)



/-- The finite protocol identity or bound `energy_average` holds under exactly the displayed hypotheses. -/
private theorem energy_average (N : ℕ) (hN : 0<N) (a : ℝ) (ha : 0≤a)
    (x : Fin N → ℝ) (he : (∑ w,(x w)^2)≤4*a^2) :
    a*(∑ w,x w)/(N : ℝ)≤(2/Real.sqrt N)*a^2 := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hs : (0 : ℝ)<Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) (fun _ => (1 : ℝ)) x
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
  have hq : (∑ w,x w)^2≤4*(N : ℝ)*a^2 := by
    exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left he hNr.le])
  have hb : (∑ w,x w)≤2*Real.sqrt N*a := by
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ 4*(N : ℝ)*a^2 := hq
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hNr.le]; ring
  have hratio : Real.sqrt N/(N : ℝ)=1/Real.sqrt N := by
    apply (div_eq_div_iff hNr.ne' hs.ne').mpr
    nlinarith [Real.sq_sqrt hNr.le]
  calc
    _ ≤ a*(2*Real.sqrt N*a)/(N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb ha) hNr.le
    _ = 2*(Real.sqrt N/(N : ℝ))*a^2 := by ring
    _ = _ := by rw [hratio]; ring

/-- Energy-to-local-query bridge with one rho-only purification. The energy
premise is still to be derived from actual marked-column agreement. -/
theorem local_query_bound_of_energy {D N : ℕ} (hN : 0<N) (U : Fin N → Operator D) (V : Operator D)
    (hU : ∀ w,U w∈Matrix.unitaryGroup (Fin D) ℂ) (hV : V∈Matrix.unitaryGroup (Fin D) ℂ)
    (henergy : ∀ ψ : QState (Fin D × Fin D),
      (∑ w,‖toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator D)) ψ-
        ApplyGate (TensorGate V (1 : Operator D)) ψ)‖^2)≤4*‖toEuclidean_fromVec ψ‖^2)
    (ρ : Operator D) (hρ : ρ.PosSemidef) :
    (∑ w,(1/(N : ℝ))*(Matrix.traceNorm (U w*ρ*(U w).conjTranspose-V*ρ*V.conjTranspose)/2))≤
      (2/Real.sqrt N)*(Matrix.trace ρ).re := by
  obtain ⟨ψ,hmarg,hmass⟩ := density_purification_exists ρ hρ
  have hmass' : ‖toEuclidean_fromVec ψ‖^2=(Matrix.trace ρ).re := by
    rw [norm_toEuclidean_fromVec_sq]
    exact hmass
  let x := fun w => ‖toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator D)) ψ-
    ApplyGate (TensorGate V (1 : Operator D)) ψ)‖
  have hb := energy_average N hN ‖toEuclidean_fromVec ψ‖ (norm_nonneg _) x (henergy ψ)
  rw [hmass'] at hb
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ ∑ w,(1/(N : ℝ))*(‖toEuclidean_fromVec ψ‖*x w) := by
      apply Finset.sum_le_sum
      intro w _
      have hh := reduced_unitary_trace_difference (U w) V (hU w) hV ψ
      rw [hmarg] at hh
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ‖toEuclidean_fromVec ψ‖*(∑ w,x w)/(N : ℝ) := by
      rw [←Finset.mul_sum,←Finset.mul_sum]
      ring
    _ ≤ _ := hb



/-- Construction for lifted Fiber in the marked columns model. -/
private def liftedFiber {D E N : ℕ} (address : Fin D → Option (Fin N)) (w : Fin N) :
    Finset (Fin D × Fin E) := Finset.univ.filter (fun p => address p.1=some w)

/-- The finite protocol identity or bound `localized_apply` holds under exactly the displayed hypotheses. -/
private theorem localized_apply {D E N : ℕ} (address : Fin D → Option (Fin N))
    (U : Fin N → Operator D) (V : Operator D)
    (hcol : ∀ w j,address j≠some w → ∀ i,U w i j=V i j)
    (w : Fin N) (ψ : QState (Fin D × Fin E)) :
    ApplyGate (TensorGate (U w) (1 : Operator E)) ψ-ApplyGate (TensorGate V (1 : Operator E)) ψ=
      ApplyGate (TensorGate (U w) (1 : Operator E)) (Collapse ψ (liftedFiber address w))-
      ApplyGate (TensorGate V (1 : Operator E)) (Collapse ψ (liftedFiber address w)) := by
  funext p
  simp only [Pi.sub_apply,ApplyGate,Matrix.mulVec,dotProduct]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : address q.1=some w
  · have hm : q∈liftedFiber (E := E) address w := by simp [liftedFiber,hq]
    rw [collapse_apply,ite_eq_left hm]
  · have he : U w p.1 q.1=V p.1 q.1 := hcol w q.1 hq p.1
    have hm : q∉liftedFiber (E := E) address w := by simp [liftedFiber,hq]
    rw [collapse_apply,ite_eq_right hm]
    simp [TensorGate,Matrix.kroneckerMap_apply,he]

/-- The finite protocol identity or bound `fiber_mass_partition` holds under exactly the displayed hypotheses. -/
private theorem fiber_mass_partition {D E N : ℕ} (address : Fin D → Option (Fin N))
    (ψ : QState (Fin D × Fin E)) :
    (∑ w,‖toEuclidean_fromVec (Collapse ψ (liftedFiber address w))‖^2)≤‖toEuclidean_fromVec ψ‖^2 := by
  simp only [norm_toEuclidean_fromVec_sq]
  have he (w : Fin N) (p : Fin D × Fin E) : ‖Collapse ψ (liftedFiber address w) p‖^2=
      if address p.1=some w then ‖ψ p‖^2 else 0 := by
    by_cases hp : address p.1=some w <;> simp [collapse_apply,liftedFiber,hp]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  cases hp : address p.1 with
  | none => simp
  | some w => simp

/-- Summed query energy is derived from actual unitarity and column agreement
outside disjoint mark fibers. The reference/purification register is arbitrary. -/
theorem marked_query_energy {D E N : ℕ} (address : Fin D → Option (Fin N))
    (U : Fin N → Operator D) (V : Operator D)
    (hU : ∀ w,U w∈Matrix.unitaryGroup (Fin D) ℂ) (hV : V∈Matrix.unitaryGroup (Fin D) ℂ)
    (hcol : ∀ w j,address j≠some w → ∀ i,U w i j=V i j)
    (ψ : QState (Fin D × Fin E)) :
    (∑ w,‖toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator E)) ψ-
      ApplyGate (TensorGate V (1 : Operator E)) ψ)‖^2)≤4*‖toEuclidean_fromVec ψ‖^2 := by
  have hs (w : Fin N) :
      ‖toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator E)) ψ-
        ApplyGate (TensorGate V (1 : Operator E)) ψ)‖≤
      2*‖toEuclidean_fromVec (Collapse ψ (liftedFiber address w))‖ := by
    rw [localized_apply address U V hcol w ψ]
    have he : toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator E)) (Collapse ψ (liftedFiber address w))-
        ApplyGate (TensorGate V (1 : Operator E)) (Collapse ψ (liftedFiber address w)))=
      toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator E)) (Collapse ψ (liftedFiber address w)))-
        toEuclidean_fromVec (ApplyGate (TensorGate V (1 : Operator E)) (Collapse ψ (liftedFiber address w))) := by
      simp only [toEuclidean_fromVec,WithLp.toLp_sub]
    rw [he]
    have hh := norm_sub_le
      (toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator E)) (Collapse ψ (liftedFiber address w))))
      (toEuclidean_fromVec (ApplyGate (TensorGate V (1 : Operator E)) (Collapse ψ (liftedFiber address w))))
    rw [norm_applyGate_of_mem_unitaryGroup (tensorGate_one_unitary (hU w)),
      norm_applyGate_of_mem_unitaryGroup (tensorGate_one_unitary hV)] at hh
    linarith
  calc
    _ ≤ ∑ w,4*‖toEuclidean_fromVec (Collapse ψ (liftedFiber address w))‖^2 := by
      apply Finset.sum_le_sum
      intro w _
      have hh := hs w
      nlinarith [norm_nonneg (toEuclidean_fromVec (ApplyGate (TensorGate (U w) (1 : Operator E)) ψ-
        ApplyGate (TensorGate V (1 : Operator E)) ψ))]
    _ ≤ _ := by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (fiber_mass_partition address ψ) (by norm_num)



/-- Local quantum error is DERIVED from actual marked-column agreement and
unitarity, for arbitrary subnormalized positive inputs and finite dimensions. -/
theorem local_query_bound_of_marked_columns {D N : ℕ} (hN : 0<N)
    (address : Fin D → Option (Fin N)) (U : Fin N → Operator D) (V : Operator D)
    (hU : ∀ w,U w∈Matrix.unitaryGroup (Fin D) ℂ) (hV : V∈Matrix.unitaryGroup (Fin D) ℂ)
    (hcol : ∀ w j,address j≠some w → ∀ i,U w i j=V i j)
    (ρ : Operator D) (hρ : ρ.PosSemidef) :
    (∑ w,(1/(N : ℝ))*(Matrix.traceNorm (U w*ρ*(U w).conjTranspose-V*ρ*V.conjTranspose)/2))≤
      (2/Real.sqrt N)*(Matrix.trace ρ).re :=
  local_query_bound_of_energy hN U V hU hV
    (fun ψ => marked_query_energy address U V hU hV hcol ψ) ρ hρ

/-- Construction for mark Law in the marked columns model. -/
def markLaw (N : ℕ) (hN : 0<N) : FinDist (Fin N) where
  prob _ := 1/(N : ℝ)
  nonneg _ := by positivity
  sum_one := by
    have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
    simp [hn]

/-- Construction for oracle Channel in the marked columns model. -/
def oracleChannel {D : ℕ} (U : Operator D) (hU : U∈Matrix.unitaryGroup (Fin D) ℂ) : QuantumChannel D D where
  map := conjBranch U
  completelyPositive := completelyPositive_conjBranch U
  tracePreserving := trace_conjBranch_unitary U hU

/-- An actual finite adaptive quantum hybrid with a derived 2/sqrt(N) query
factor. Only concrete matrix unitarity and off-fiber column equalities are
required; there is no per-query trace-distance bound supplied as a field. -/
theorem marked_adaptive_hybrid {D R N : ℕ} (hN : 0<N)
    (address : Bool → Fin D → Option (Fin N)) (U : Fin N → Bool → Operator D) (V : Bool → Operator D)
    (hU : ∀ w mode,U w mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ mode,V mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hcol : ∀ mode w j,address mode j≠some w → ∀ i,U w mode i j=V mode i j)
    (S : ℝ → Fin R) (P : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program D R) (ρ : Operator D) (hρ : ρ.PosSemidef) :
    (∑ w,(markLaw N hN).prob w*Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.recordDistance
      (fun mode => oracleChannel (U w mode) (hU w mode))
      (fun mode => oracleChannel (V mode) (hV mode)) S P ρ ρ)≤
      (2/Real.sqrt N)*(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.queryDepth P : ℝ)*(Matrix.trace ρ).re := by
  apply Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.adaptive_query_hybrid _ _ _ _ _ (by positivity) _ P ρ hρ
  intro mode σ hσ
  exact local_query_bound_of_marked_columns hN (address mode) (fun w => U w mode) (V mode)
    (fun w => hU w mode) (hV mode) (hcol mode) σ hσ



/-- Construction for joint Marked Prior in the marked columns model. -/
def jointMarkedPrior {Θ : Type} [Fintype Θ] (π : FinDist Θ) (N : ℕ) (hN : 0<N) :
    FinDist (Θ × Fin N) := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw π (fun _ => markLaw N hN)

/-- An arbitrary finite nuisance parameter is retained in the same joint law.
One rho-only purification serves all nuisance parameters and all marks. -/
theorem joint_marked_query_error {Θ : Type} [Fintype Θ] {D N : ℕ} (π : FinDist Θ) (hN : 0<N)
    (address : Bool → Fin D → Option (Fin N)) (U : Θ → Fin N → Bool → Operator D) (V : Bool → Operator D)
    (hU : ∀ θ w mode,U θ w mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ mode,V mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hcol : ∀ θ mode w j,address mode j≠some w → ∀ i,U θ w mode i j=V mode i j)
    (mode : Bool) (ρ : Operator D) (hρ : ρ.PosSemidef) :
    (∑ h : Θ × Fin N,(jointMarkedPrior π N hN).prob h*
      (Matrix.traceNorm (U h.1 h.2 mode*ρ*(U h.1 h.2 mode).conjTranspose-
        V mode*ρ*(V mode).conjTranspose)/2))≤(2/Real.sqrt N)*(Matrix.trace ρ).re := by
  have he : (∑ h : Θ × Fin N,(jointMarkedPrior π N hN).prob h*
      (Matrix.traceNorm (U h.1 h.2 mode*ρ*(U h.1 h.2 mode).conjTranspose-
        V mode*ρ*(V mode).conjTranspose)/2))=
      ∑ θ,π.prob θ*(∑ w,(1/(N : ℝ))*(Matrix.traceNorm
        (U θ w mode*ρ*(U θ w mode).conjTranspose-V mode*ρ*(V mode).conjTranspose)/2)) := by
    change (∑ h : Θ × Fin N,(π.prob h.1*(1/(N : ℝ)))*
      (Matrix.traceNorm (U h.1 h.2 mode*ρ*(U h.1 h.2 mode).conjTranspose-
        V mode*ρ*(V mode).conjTranspose)/2))=_
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  calc
    _ ≤ ∑ θ,π.prob θ*((2/Real.sqrt N)*(Matrix.trace ρ).re) := by
      apply Finset.sum_le_sum
      intro θ _
      exact mul_le_mul_of_nonneg_left (local_query_bound_of_marked_columns hN (address mode)
        (fun w => U θ w mode) (V mode) (fun w => hU θ w mode) (hV mode) (hcol θ mode) ρ hρ) (π.nonneg θ)
    _ = _ := by rw [←Finset.sum_mul,π.sum_one,one_mul]

/-- The joint finite-protocol hybrid has no assumed query-distance bound:
4 queryDepth/sqrt(N) is derived from the physical matrix family. One-angle
visibility and actual classical support agreement remain geometric premises. -/
theorem marked_joint_support_bound {Θ : Type} [Fintype Θ] [DecidableEq Θ] {D R N : ℕ}
    (π : FinDist Θ) (hN : 0<N) (address : Bool → Fin D → Option (Fin N))
    (U : Θ → Fin N → Bool → Operator D) (V : Bool → Operator D)
    (hU : ∀ θ w mode,U θ w mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ mode,V mode∈Matrix.unitaryGroup (Fin D) ℂ)
    (hcol : ∀ θ mode w j,address mode j≠some w → ∀ i,U θ w mode i j=V mode i j)
    (S : (Θ × Fin N) → ℝ → Fin R) (B : ℝ → Fin R) (P : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program D R)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (bad : (Θ × Fin N) → ℝ → Prop) (hS : ∀ h a,¬bad h a → S h a=B a) (s : ℕ) (v : ℝ)
    (hv : ∀ a,(∑ h∈Finset.univ.filter (fun h => bad h a),(jointMarkedPrior π N hN).prob h)≤v)
    (hc : ∀ p : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Path P, (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathCharge P p).2 ≤ s) :
    (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw (jointMarkedPrior π N hN)
      (fun h => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathLaw
        (fun mode => oracleChannel (U h.1 h.2 mode) (hU h.1 h.2 mode)) (S h) P ρ hρ htrace)).prob hp-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw (jointMarkedPrior π N hN)
        (fun _ => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathLaw (fun mode => oracleChannel (V mode) (hV mode)) B P ρ hρ htrace)).prob hp|)/2≤
      4*(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.queryDepth P : ℝ)/Real.sqrt N+(s : ℝ)*v := by
  have hh := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.finite_protocol_query_bound (jointMarkedPrior π N hN)
    (fun h mode => oracleChannel (U h.1 h.2 mode) (hU h.1 h.2 mode))
    (fun mode => oracleChannel (V mode) (hV mode)) S B P ρ hρ htrace bad hS (2/Real.sqrt N) v s
    (by positivity) (fun mode σ hσ => joint_marked_query_error π hN address U V hU hV hcol mode σ hσ) hv hc
  exact hh.trans_eq (by ring)

end Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport
