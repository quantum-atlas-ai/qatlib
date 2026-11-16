/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
public import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
public import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointQuan
public import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
public import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
public import Qatlib.Papers.QMetropolis11.GibbsMixing.UniquenessErgodicity.ErgodicDefinition
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# Detailed balance, uniqueness, and trace-norm ergodicity

Fixed source: arXiv:0911.3635v2, Section 3.2, printed page 8.

The source connects universal updates with ergodicity of the quantum
Metropolis channel. This module proves the analytic consequence of the
eventual strict contraction interface inherited from the source skeleton.

The interface now quantifies only over distinct density operators. The old
interface included equal pairs and therefore required a strict decrease from
zero to zero. No result is proved from that inconsistent interface.

Detailed balance supplies stationarity. Density matrices form a compact set;
trace distance is continuous and obeys channel data processing. A compact
Lyapunov argument then proves convergence from eventual strict contraction,
without assuming a uniform contraction coefficient or the convergence
conclusion. Constructing the concrete universal-update Metropolis channel
and proving that it satisfies this interface remains outside this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.UniquenessErgodicity

/-- Eventual strict descent on a compact invariant set forces a nonnegative
continuous Lyapunov function to converge to zero along every orbit. -/
theorem compact_descent {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (K : Set X) (hK : IsCompact K)
    (f : X → X) (hf : Continuous f) (hmap : Set.MapsTo f K K)
    (V : X → ℝ) (hV : Continuous V) (hVnonneg : ∀ x ∈ K, 0 ≤ V x)
    (hstep : ∀ x ∈ K, V (f x) ≤ V x)
    (hstrict : ∀ x ∈ K, V x ≠ 0 → ∃ m : ℕ, V ((f^[m]) x) < V x)
    (x : X) (hx : x ∈ K) :
    Tendsto (fun n : ℕ => V ((f^[n]) x)) atTop (nhds 0) := by
  have hiter : ∀ n : ℕ, (f^[n]) x ∈ K := fun n => hmap.iterate n hx
  have hanti : Antitone (fun n : ℕ => V ((f^[n]) x)) := by
    apply antitone_nat_of_succ_le
    intro n
    simpa only [Function.iterate_succ_apply'] using hstep ((f^[n]) x) (hiter n)
  have hbdd : BddBelow (Set.range (fun n : ℕ => V ((f^[n]) x))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hVnonneg _ (hiter n)⟩
  let L := ⨅ n : ℕ, V ((f^[n]) x)
  have hlim : Tendsto (fun n : ℕ => V ((f^[n]) x)) atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hbdd
  obtain ⟨y, hy, φ, hφ, hsub⟩ := hK.tendsto_subseq hiter
  have hval : V y = L := tendsto_nhds_unique (hV.tendsto y |>.comp hsub)
    (hlim.comp hφ.tendsto_atTop)
  have hzero : V y = 0 := by
    by_contra hne
    obtain ⟨m, hm⟩ := hstrict y hy hne
    have hshift : Tendsto (fun n : ℕ => φ n + m) atTop atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) m) hφ.tendsto_atTop
    have hlimshift : Tendsto (fun n : ℕ => V ((f^[φ n + m]) x)) atTop (nhds L) :=
      hlim.comp hshift
    have hcompshift : Tendsto (fun n : ℕ => V ((f^[φ n + m]) x)) atTop
        (nhds (V ((f^[m]) y))) := by
      convert ((hV.comp (hf.iterate m)).tendsto y |>.comp hsub) using 1
      · ext n
        simp only [Function.comp_apply, Function.iterate_add_apply,
          add_comm (φ n) m]
      · rfl
    have heq := tendsto_nhds_unique hcompshift hlimshift
    rw [hval, heq] at hm
    exact lt_irrefl _ hm
  simpa only [← hval, hzero] using hlim

open Matrix
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QuantumGibbs.DetailedBalance

/-- The finite matrix trace norm is a continuous function of the matrix. -/
theorem continuous_traceNorm (D : ℕ) : Continuous (fun A : Operator D => Matrix.traceNorm A) := by
  have hbound (A : Operator D) : A.traceNorm ≤ (D : ℝ) * ‖A‖ := by
    rw [Matrix.traceNorm_eq_sum_singularValues]
    calc
      ∑ i : Fin D, singularValues A i ≤ ∑ _i : Fin D, ‖A‖ :=
        Finset.sum_le_sum (fun i _ => Matrix.singularValues_le_opNorm A i)
      _ = (D : ℝ) * ‖A‖ := by simp
  have hLip : LipschitzWith ⟨D, Nat.cast_nonneg D⟩
      (fun A : Operator D => Matrix.traceNorm A) := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    rw [Real.dist_eq, dist_eq_norm]
    apply abs_le.mpr
    have hab := Matrix.traceNorm_add_le (A - B) B
    have hba := Matrix.traceNorm_add_le (B - A) A
    rw [sub_add_cancel] at hab hba
    have hneg : (B - A).traceNorm = (A - B).traceNorm := by
      rw [← neg_sub A B, Matrix.traceNorm_neg]
    rw [hneg] at hba
    change -((D : ℝ) * ‖A - B‖) ≤ _ ∧ _ ≤ (D : ℝ) * ‖A - B‖
    constructor <;> linarith [hbound (A - B)]
  exact hLip.continuous

/-- Finite-dimensional density operators form a compact set of actual matrices. -/
theorem compact_densities (D : ℕ) : IsCompact {ρ : Operator D | IsDensityOperator ρ} := by
  have hcompact : IsCompact (Set.range (MState.m (d := Fin D))) :=
    isCompact_range MState.Continuous_Matrix
  convert hcompact using 1
  ext ρ
  constructor
  · intro hρ
    exact ⟨densityMatrixEquivMState (Fin D) ⟨ρ, hρ⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.psd, s.tr'⟩

/-- The old unrestricted strict-contraction interface fails at any equal
pair of density operators, independently of the channel. -/
theorem equal_pair_obstruction {D : ℕ} (T : QuantumChannel D D) (σ : Operator D)
    (hσ : IsDensityOperator σ) :
    ¬ (∀ ρ φ : Operator D, IsDensityOperator ρ → IsDensityOperator φ →
      ∃ m : ℕ, SchattenOne ((T.map^[m]) ρ - (T.map^[m]) φ) < SchattenOne (ρ - φ)) := by
  intro h
  obtain ⟨m, hm⟩ := h σ σ hσ hσ
  simp only [sub_self] at hm
  exact lt_irrefl _ hm

/-- Eventual strict contraction of distinct densities makes the detailed-balance
density the unique stationary density. Equal pairs are correctly excluded. -/
theorem source_unique_fixedPoint {D : ℕ} (T : QuantumChannel D D) (σ : Operator D)
    (hσ : IsDensityOperator σ) (hdb : QuantumDetailedBalance T.map σ)
    (huniversal : ∀ ρ φ : Operator D, IsDensityOperator ρ → IsDensityOperator φ → ρ ≠ φ →
      ∃ m : ℕ, SchattenOne ((T.map^[m]) ρ - (T.map^[m]) φ) < SchattenOne (ρ - φ)) :
    ∀ ρ : Operator D, IsDensityOperator ρ → T.map ρ = ρ → ρ = σ := by
  intro ρ hρ hfix
  by_contra hne
  obtain ⟨m, hm⟩ := huniversal ρ σ hρ hσ hne
  have hσfix := quantumDetailedBalanceFixedPoint D T σ hσ hdb
  have hρiter : ∀ k : ℕ, (T.map^[k]) ρ = ρ := fun k => Function.IsFixedPt.iterate hfix k
  have hσiter : ∀ k : ℕ, (T.map^[k]) σ = σ := fun k => Function.IsFixedPt.iterate hσfix k
  rw [hρiter, hσiter] at hm
  exact lt_irrefl _ hm

/-- Compactness and trace-distance data processing promote eventual strict
contraction of distinct densities to convergence, without assuming a uniform rate. -/
theorem source_ergodic {D : ℕ} (T : QuantumChannel D D) (σ : Operator D)
    (hσ : IsDensityOperator σ) (hdb : QuantumDetailedBalance T.map σ)
    (huniversal : ∀ ρ φ : Operator D, IsDensityOperator ρ → IsDensityOperator φ → ρ ≠ φ →
      ∃ m : ℕ, SchattenOne ((T.map^[m]) ρ - (T.map^[m]) φ) < SchattenOne (ρ - φ)) :
    MetropolisErgodic T σ := by
  intro ρ hρ
  have hfix := quantumDetailedBalanceFixedPoint D T σ hσ hdb
  have hσiter : ∀ k : ℕ, (T.map^[k]) σ = σ := fun k => Function.IsFixedPt.iterate hfix k
  apply compact_descent {ρ : Operator D | IsDensityOperator ρ} (compact_densities D)
    T.map (T.map.continuous_of_finiteDimensional) (fun _ h => T.preservesDensity h)
    (fun x => SchattenOne (x - σ))
  · simp only [schattenOne_eq_physlib_traceNorm]
    convert (continuous_traceNorm D).comp (continuous_id.sub continuous_const) using 1
    ext x
    rfl
  · intro x _
    rw [schattenOne_eq_physlib_traceNorm]
    exact Matrix.traceNorm_nonneg _
  · intro x hx
    rw [schattenOne_eq_physlib_traceNorm, schattenOne_eq_physlib_traceNorm]
    have h := Qatlib.Concepts.ReferenceError.DensityToRaw.channel_hermitian_trace_contraction
      T (Matrix.IsHermitian.sub hx.1.1 hσ.1.1)
    simpa only [map_sub, hfix] using h
  · intro x hx hne
    have hxs : x ≠ σ := by
      intro heq
      apply hne
      rw [heq, sub_self, schattenOne_eq_physlib_traceNorm, Matrix.traceNorm_zero]
    obtain ⟨m, hm⟩ := huniversal x σ hx hσ hxs
    exact ⟨m, by simpa only [hσiter] using hm⟩
  · exact hρ


open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath.BornBridge

/-- The genuine completely positive trace-preserving replacement channel has
the standard linear action on every input matrix. -/
theorem replacement_mapD {D : ℕ} [Nonempty (Fin D)] (σ : MState (Fin D)) (X : Operator D) :
    (ofPhyslib (CPTPMap.replacement σ : CPTPMap (Fin D) (Fin D))).map X =
      Matrix.trace X • σ.m := by
  ext i j
  change (∑ a : Fin D, X a a * σ.m i j) = (∑ a : Fin D, X a a) * σ.m i j
  exact (Finset.sum_mul _ _ _).symm

/-- A replacement channel satisfies square-root quantum detailed balance for
its target density, rather than merely being stationary at that density. -/
theorem replacement_detailed_balanceD {D : ℕ} [Nonempty (Fin D)] (σ : MState (Fin D)) :
    QuantumDetailedBalance
      (ofPhyslib (CPTPMap.replacement σ : CPTPMap (Fin D) (Fin D))).map σ.m := by
  have hs : IsDensityOperator σ.m := ⟨σ.psd, σ.tr'⟩
  have htrace (X : Operator D) :
      Matrix.trace (densSqrt σ.m * X * densSqrt σ.m) = Matrix.trace (σ.m * X) := by
    rw [Matrix.trace_mul_cycle, densSqrt_mul_self σ.m hs]
  intro ρ φ
  rw [replacement_mapD, replacement_mapD, htrace φ, htrace ρ]
  rw [Matrix.conjTranspose_smul, σ.psd.1.eq]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hstar : star (Matrix.trace (σ.m * ρ)) = Matrix.trace (ρᴴ * σ.m) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, σ.psd.1.eq]
  rw [hstar]
  ring

/-- Distinct density inputs become equal after one genuine replacement-channel
step, and hence strictly decrease their originally positive trace distance. -/
theorem replacement_strictD {D : ℕ} [Nonempty (Fin D)] (σ : MState (Fin D))
    (ρ φ : Operator D) (hρ : IsDensityOperator ρ) (hφ : IsDensityOperator φ) (hne : ρ ≠ φ) :
    ∃ m : ℕ, SchattenOne
      (((ofPhyslib (CPTPMap.replacement σ : CPTPMap (Fin D) (Fin D))).map^[m]) ρ -
       ((ofPhyslib (CPTPMap.replacement σ : CPTPMap (Fin D) (Fin D))).map^[m]) φ) <
      SchattenOne (ρ - φ) := by
  refine ⟨1, ?_⟩
  simp only [Function.iterate_one, replacement_mapD, hρ.2, hφ.2, one_smul, sub_self]
  rw [schattenOne_eq_physlib_traceNorm, schattenOne_eq_physlib_traceNorm, Matrix.traceNorm_zero]
  apply lt_of_le_of_ne (Matrix.traceNorm_nonneg _)
  intro h
  apply hne
  exact sub_eq_zero.mp ((Matrix.traceNorm_zero_iff _).mp h.symm)

/-- A two-dimensional depolarizing channel witnesses all repaired assumptions,
with two distinct admissible density inputs that really collapse in one step. -/
theorem nontrivial_metropolis_exampleD :
    ∃ T : QuantumChannel 2 2, ∃ σ : Operator 2,
      IsDensityOperator σ ∧ QuantumDetailedBalance T.map σ ∧
      (∀ ρ φ : Operator 2, IsDensityOperator ρ → IsDensityOperator φ → ρ ≠ φ →
        ∃ m : ℕ, SchattenOne ((T.map^[m]) ρ - (T.map^[m]) φ) < SchattenOne (ρ - φ)) ∧
      ∃ ρ φ : Operator 2, IsDensityOperator ρ ∧ IsDensityOperator φ ∧ ρ ≠ φ ∧
        T.map ρ = σ ∧ T.map φ = σ := by
  let σ : MState (Fin 2) := MState.uniform
  let T : QuantumChannel 2 2 := ofPhyslib (CPTPMap.replacement σ)
  refine ⟨T, σ.m, ⟨σ.psd, σ.tr'⟩, replacement_detailed_balanceD σ, ?_, ?_⟩
  · exact replacement_strictD σ
  · let ρ : MState (Fin 2) := MState.pure (_root_.Ket.basis 0)
    let φ : MState (Fin 2) := MState.pure (_root_.Ket.basis 1)
    refine ⟨ρ.m, φ.m, ⟨ρ.psd, ρ.tr'⟩, ⟨φ.psd, φ.tr'⟩, ?_, ?_, ?_⟩
    · intro h
      have hentry := congrArg (fun X : Operator 2 => X 0 0) h
      norm_num [ρ, φ, MState.pure_apply, _root_.Ket.basis, _root_.Ket.coe_fun_eq] at hentry
    · simp only [T, replacement_mapD, ρ.tr', one_smul]
    · simp only [T, replacement_mapD, φ.tr', one_smul]

end Qatlib.Papers.QMetropolis11.GibbsMixing.UniquenessErgodicity
