/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

/-!
# Finite Fourier laws for amplitude estimation

`phaseMass` is the squared Fourier-kernel amplitude and `rawMass` averages the two reflected
eigenphase branches of amplitude estimation. The module proves normalization, exact grid
behavior, and the sine-quotient formula with its singular values filled in.

`actual_prepared_qae_law` identifies the actual prepared readout with `rawMass` for interior
amplitudes. Reflection symmetry then reduces expectations of sine-squared payoffs to a single
phase branch. See [KanekoEtAl2020].

## Main statements

* `completedKernel_eq_mass`: the completed sine quotient equals the physical kernel mass.
* `actual_prepared_qae_law`: equality with the actual prepared QAE readout.
* `nonlinear_payoff_expectation`: equality of raw and single-branch payoff expectations.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier

/-- The squared norm of the finite Fourier phase-estimation kernel at outcome `k`. -/
def phaseMass (M : ℕ) (θ : ℝ) (k : Fin M) : ℝ := ‖qpeKernel M θ k‖^2

/-- For positive `M`, the QPE kernel equals the inverse-Fourier amplitude of the BHMT phase
state. -/
theorem kernel_eq_bhmt_amplitude (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    qpeKernel M θ k = ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M θ)) k := by
  rw [(offgrid_phase_kernel_formula M θ k hM).2.1,
    bhmt_phase_estimation_theorem11_amplitude M θ hM k]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  push_cast
  ring

/-- The Fourier-kernel mass agrees with the BHMT phase-estimation outcome mass for positive `M`. -/
theorem phaseMass_eq_bhmt (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    phaseMass M θ k = bhmt11OutcomeMass M θ k := by
  rw [phaseMass,kernel_eq_bhmt_amplitude M θ hM k]
  rfl

/-- For positive `M`, the phase masses sum to one. -/
theorem phaseMass_sum_one (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    ∑ k : Fin M, phaseMass M θ k=1 := by
  simp_rw [phaseMass_eq_bhmt M θ hM]
  exact bhmt_phase_estimation_theorem11_normalization M θ hM

/-- The finite probability distribution defined by the normalized phase-kernel masses. -/
def phaseLaw (M : ℕ) (θ : ℝ) (hM : 0 < M) : FinDist (Fin M) where
  prob := phaseMass M θ
  nonneg _ := sq_nonneg _
  sum_one := phaseMass_sum_one M θ hM

/-- A phase exactly on the Fourier grid produces unit mass at its grid index and zero mass
elsewhere. See [KanekoEtAl2020]. -/
theorem phaseMass_grid (M : ℕ) (hM : 0 < M) (j k : Fin M) :
    phaseMass M (j.val/(M:ℝ)) k = if k=j then 1 else 0 := by
  rw [phaseMass,(offgrid_phase_geometric_and_periodic M (j.val/(M:ℝ)) k hM).2.2 j]
  by_cases h : k=j <;> simp [Ket,h,eq_comm]

/-- The equal mixture of phase-kernel masses for phases `θ` and `1-θ`. -/
def rawMass (M : ℕ) (θ : ℝ) (k : Fin M) : ℝ :=
  (phaseMass M θ k+phaseMass M (1-θ) k)/2

/-- The finite probability distribution obtained by mixing the two reflected phase branches
equally. -/
def rawLaw (M : ℕ) (θ : ℝ) (hM : 0 < M) : FinDist (Fin M) where
  prob := rawMass M θ
  nonneg k := div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  sum_one := by
    change (∑ k : Fin M, rawMass M θ k)=1
    dsimp only [rawMass]
    rw [← Finset.sum_div,Finset.sum_add_distrib,phaseMass_sum_one M θ hM,
      phaseMass_sum_one M (1-θ) hM]
    norm_num

/-- For an interior prepared amplitude and `M ≥ 2`, the actual QAE outcome mass equals the equal
mixture of its two phase branches. See [KanekoEtAl2020]. -/
theorem actual_prepared_qae_law {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/2)
    (ha : MeasureProb (preparedAAState A j) S=Real.sin (θ*Real.pi)^2) (k : Fin M) :
    (aeLaw M A j S hA hM).prob k=rawMass M θ k := by
  have h := prepared_ae_two_phase_distribution M hM A j S hA (θ*Real.pi)
    (mul_pos hθ0 Real.pi_pos) (by nlinarith [Real.pi_pos]) ha k
  have he : θ*Real.pi/Real.pi=θ := by field_simp
  have hen : -(θ*Real.pi)/Real.pi = -θ := by field_simp
  rw [he,hen] at h
  have hp : qpeKernel M (1-θ) k=qpeKernel M (-θ) k := by
    have harg : -θ+(1:ℤ)=1-θ := by push_cast; ring
    simpa only [harg] using qpeKernel_int_add M (-θ) k 1
  simpa only [rawMass,phaseMass,hp] using h

/-- The squared chord length from one to a complex phase is four times the corresponding squared
sine. -/
theorem phase_chord (t : ℝ) :
    ‖Complex.exp (2*Real.pi*Complex.I*t)-1‖^2=4*Real.sin (t*Real.pi)^2 := by
  have h := zoo_amplified_qft_lemma18_chord_sq (2*Real.pi*t)
  have he : 2*Real.pi*Complex.I*(t:ℂ)=((2*Real.pi*t:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,norm_sub_rev,h]
  congr 2
  ring

/-- The phase mass multiplied by the squared sine denominator satisfies the exact finite-kernel
sine identity. -/
theorem mass_sine_identity (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    (M:ℝ)^2*phaseMass M θ k*Real.sin ((θ-k.val/(M:ℝ))*Real.pi)^2 =
      Real.sin ((M:ℝ)*θ*Real.pi)^2 := by
  have h := congrArg (fun z : ℂ => ‖z‖^2) (qpeKernel_geometric_identity M θ k hM)
  simp only [norm_mul,mul_pow,Complex.norm_natCast] at h
  have hd := phase_chord (θ-k.val/(M:ℝ))
  have hn := phase_chord ((M:ℝ)*θ)
  push_cast at hd hn h
  rw [hd,hn] at h
  change (M:ℝ)^2*phaseMass M θ k*(4*Real.sin ((θ-k.val/(M:ℝ))*Real.pi)^2)=
    4*Real.sin ((M:ℝ)*θ*Real.pi)^2 at h
  nlinarith

/-- Away from a zero sine denominator, the phase mass equals the squared-sine quotient. -/
theorem mass_quotient (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M)
    (hs : Real.sin ((θ-k.val/(M:ℝ))*Real.pi) ≠ 0) :
    phaseMass M θ k = Real.sin ((M:ℝ)*θ*Real.pi)^2 /
      ((M:ℝ)^2*Real.sin ((θ-k.val/(M:ℝ))*Real.pi)^2) := by
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hM.ne')) (pow_ne_zero 2 hs))).mpr
  nlinarith [mass_sine_identity M θ hM k]

/-- At a zero sine denominator, the phase mass is one. -/
theorem mass_at_singularity (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M)
    (hs : Real.sin ((θ-k.val/(M:ℝ))*Real.pi)=0) : phaseMass M θ k=1 := by
  obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hs
  have harg : θ=k.val/(M:ℝ)+(n:ℝ) := by nlinarith [Real.pi_pos]
  rw [phaseMass,harg,qpeKernel_int_add,
    (offgrid_phase_geometric_and_periodic M (k.val/(M:ℝ)) k hM).2.2 k]
  simp [Ket]

/-- The sine-quotient kernel completed with value one at zero sine denominators. -/
def completedKernel (M : ℕ) (θ : ℝ) (k : Fin M) : ℝ :=
  if Real.sin ((θ-k.val/(M:ℝ))*Real.pi)=0 then 1 else
  Real.sin ((M:ℝ)*θ*Real.pi)^2 / ((M:ℝ)^2*Real.sin ((θ-k.val/(M:ℝ))*Real.pi)^2)

/-- For positive `M`, the completed sine-quotient kernel equals the phase mass at every outcome. -/
theorem completedKernel_eq_mass (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    completedKernel M θ k=phaseMass M θ k := by
  unfold completedKernel
  split_ifs with hs
  · exact (mass_at_singularity M θ hM k hs).symm
  · exact (mass_quotient M θ hM k hs).symm

/-- Reflects a Fourier index modulo `M`, fixing zero and sending nonzero `k` to `M-k`. -/
def reflect {M : ℕ} (k : Fin M) : Fin M :=
  if h : k.val=0 then k else ⟨M-k.val,by have := k.isLt; omega⟩

/-- Reflection of Fourier indices is an involution. -/
theorem reflect_involutive {M : ℕ} : Function.Involutive (reflect (M:=M)) := by
  intro k
  apply Fin.ext
  dsimp only [reflect]
  split_ifs <;> simp_all only <;> have := k.isLt <;> omega

/-- The reflected grid coordinate is zero at index zero and otherwise one minus the original
coordinate. -/
theorem reflect_grid (M : ℕ) (hM : 0 < M) (k : Fin M) :
    (reflect k).val/(M:ℝ)=if k.val=0 then 0 else 1-k.val/(M:ℝ) := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  by_cases hk : k.val=0
  · simp [reflect,hk]
  · simp only [reflect,hk,↓reduceDIte,Fin.val_mk,↓reduceIte]
    rw [Nat.cast_sub (le_of_lt k.isLt)]
    field_simp

/-- Negating the phase parameter preserves the squared norm of the finite exponential sum. -/
theorem expSum_norm_neg (M : ℕ) (t : ℝ) :
    ‖bhmt_phase_estimation_theorem11_expSum M (-t)‖^2=
      ‖bhmt_phase_estimation_theorem11_expSum M t‖^2 := by
  rw [bhmt_phase_estimation_theorem11_expSum_abs M (-t),abs_neg,
    ← bhmt_phase_estimation_theorem11_expSum_abs M t]

/-- Reflecting the phase from `θ` to `1-θ` is equivalent to reflecting the outcome index. -/
theorem phaseMass_reflection (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    phaseMass M (1-θ) k=phaseMass M θ (reflect k) := by
  rw [phaseMass_eq_bhmt M (1-θ) hM,phaseMass_eq_bhmt M θ hM,
    bhmt_phase_estimation_theorem11_mass_expSum M (1-θ) hM,
    bhmt_phase_estimation_theorem11_mass_expSum M θ hM,reflect_grid M hM]
  congr 1
  by_cases hk : k.val=0
  · simp only [hk,Nat.cast_zero,zero_div,↓reduceIte,sub_zero]
    have hs := bhmt_phase_estimation_theorem11_expSum_shift M (1-θ) 1
    have he : 1-θ-(1:ℤ) = -θ := by push_cast; ring
    rw [he] at hs
    rw [← hs,expSum_norm_neg]
  · rw [if_neg hk]
    have he : 1-θ-k.val/(M:ℝ)=-(θ-(1-k.val/(M:ℝ))) := by ring
    rw [he,expSum_norm_neg]

/-- A reflection-invariant readout has the same expectation under the raw two-branch law and the
single phase law. -/
theorem raw_expectation_eq_single (M : ℕ) (θ : ℝ) (hM : 0 < M) (h : Fin M → ℝ)
    (hh : ∀ k,h (reflect k)=h k) :
    ∑ k,rawMass M θ k*h k=∑ k,phaseMass M θ k*h k := by
  have hs : (∑ k,phaseMass M (1-θ) k*h k) = ∑ k,phaseMass M θ k*h k := by
    calc
      _ = ∑ k,phaseMass M θ (reflect k)*h (reflect k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [phaseMass_reflection M θ hM,hh]
      _ = _ := Equiv.sum_comp (reflect_involutive.toPerm reflect) (fun k : Fin M => phaseMass M θ k*h k)
  calc
    _ = ((∑ k,phaseMass M θ k*h k)+(∑ k,phaseMass M (1-θ) k*h k))/2 := by
      dsimp only [rawMass]
      simp_rw [div_mul_eq_mul_div,add_mul]
      rw [← Finset.sum_div,Finset.sum_add_distrib]
    _ = _ := by rw [hs]; ring

/-- The sine-squared readout is invariant under reflection of the Fourier index. -/
theorem sinSquare_reflection (M : ℕ) (hM : 0 < M) (k : Fin M) :
    Real.sin ((reflect k).val/(M:ℝ)*Real.pi)^2=Real.sin (k.val/(M:ℝ)*Real.pi)^2 := by
  rw [reflect_grid M hM]
  by_cases hk : k.val=0
  · simp [hk]
  · rw [if_neg hk,sub_mul,one_mul,Real.sin_pi_sub]

/-- Every payoff of the scaled sine-squared readout has the same expectation under the raw law
and the single phase branch. See [KanekoEtAl2020]. -/
theorem nonlinear_payoff_expectation (M : ℕ) (θ D : ℝ) (hM : 0 < M) (g : ℝ → ℝ) :
    ∑ k,rawMass M θ k*g (D*Real.sin (k.val/(M:ℝ)*Real.pi)^2)=
      ∑ k,phaseMass M θ k*g (D*Real.sin (k.val/(M:ℝ)*Real.pi)^2) := by
  apply raw_expectation_eq_single M θ hM
  intro k
  rw [sinSquare_reflection M hM]

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier
