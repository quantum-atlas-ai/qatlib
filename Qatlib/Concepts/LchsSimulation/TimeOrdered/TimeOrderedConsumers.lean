/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Concepts.LchsSimulation.TimeOrdered.OrderedFrozenSegment

/-!
# Forced ordered evolution and sampled Hamiltonian programs

`orderedForcedSolution` gives the Duhamel solution of a forced linear differential equation,
with its derivative, uniqueness, and dissipative norm bound. `interactionGenerator` expresses
the interaction picture. `sampledEvolutionWord` implements a left-sampled frozen-Hamiltonian
product with an explicit error estimate and gate count. For the interaction-picture setting, see
[Low and Wiebe, 2018][LowWiebe2018].

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `ordered_forced_solution_duhamel_and_bound`: collects the forced initial-value problem and
  norm bound.
* `ordered_interaction_picture_identity`: factors out the constant Hamiltonian evolution.
* `ordered_sampled_program_error_and_cost`: gives error `L * T ^ 2 / (2 * N)` and exactly `N`
  gates.

## References

* [An et al., 2023][AnLiuLin2023]
-/


open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.LchsSimulation.TimeOrdered
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- The Duhamel expression consisting of homogeneous ordered evolution of the initial vector
plus the integrated propagated source. -/
noncomputable def orderedForcedSolution {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s : ℝ) (v : QState I) (t : ℝ) : QState I :=
  orderedEvolution A s t *ᵥ v + ∫ u in s..t, orderedEvolution A u t *ᵥ b u

/-- The interaction-picture perturbation obtained by conjugating `V t` with the constant
Hamiltonian evolution. -/
noncomputable def interactionGenerator {I : Type} [Fintype I] [DecidableEq I]
    (H₀ : Matrix I I ℂ) (V : ℝ → Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution H₀ (-t) * V t * HamiltonianEvolution H₀ t

/-- The circuit of `N` Hamiltonian gates, each evolving for `T / N` under the Hamiltonian
sampled at its interval left endpoint. -/
noncomputable def sampledEvolutionWord {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (N : ℕ) : Circuit I :=
  (List.range N).map (fun j => Step.gate (HamiltonianEvolution (H ((j:ℝ)*T/N)) (T/N)))

/-- At its initial time, the forced ordered solution equals the initial vector. -/
@[simp] theorem orderedForcedSolution_self {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s : ℝ) (v : QState I) :
    orderedForcedSolution A b s v s = v := by
  simp [orderedForcedSolution]

/-- The derivative of a matrix-vector product is the sum of the derivative matrix acting on the
vector and the matrix acting on the derivative vector. -/
private theorem ordered_mulVec_deriv {I : Type} [Fintype I] [DecidableEq I]
    {M : ℝ → Matrix I I ℂ} {v : ℝ → QState I} {M' : Matrix I I ℂ} {v' : QState I} {t : ℝ}
    (hM : HasDerivAt M M' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun u => M u *ᵥ v u) (M' *ᵥ v t + M t *ᵥ v') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hm (j : I) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) j
  have hvj (j : I) := hasDerivAt_pi.mp hv j
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using!
    HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hm j).mul (hvj j))

/-- For a continuous generator, ordered evolution to a fixed endpoint is continuous in its
starting time. -/
private theorem ordered_start_continuous {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) :
    Continuous (fun u => orderedEvolution A u s) :=
  continuous_iff_continuousAt.mpr (fun u => (orderedEvolution_hasDerivAt_start A hA s u).continuousAt)

/-- The forced solution factors into homogeneous ordered evolution applied to the initial vector
plus the source integral transported back to the initial time. -/
private theorem ordered_forced_factor {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (hA : Continuous A) (hb : Continuous b)
    (s : ℝ) (v : QState I) (t : ℝ) :
    orderedForcedSolution A b s v t = orderedEvolution A s t *ᵥ
      (v + ∫ u in s..t, orderedEvolution A u s *ᵥ b u) := by
  let L : QState I →L[ℝ] QState I :=
      ((Matrix.mulVecLin (orderedEvolution A s t)).restrictScalars ℝ).toContinuousLinearMap
  have hi :=
      ((ordered_start_continuous A hA s).matrix_mulVec hb).intervalIntegrable
      (μ := MeasureTheory.volume) s t
  have he (u : ℝ) : orderedEvolution A u t *ᵥ b u =
      L (orderedEvolution A u s *ᵥ b u) := by
    change _ = orderedEvolution A s t *ᵥ (orderedEvolution A u s *ᵥ b u)
    rw [Matrix.mulVec_mulVec, orderedEvolution_cocycle A hA u s t]
  unfold orderedForcedSolution
  rw [Matrix.mulVec_add]
  congr 1
  rw [intervalIntegral.integral_congr (fun u _ => he u), L.intervalIntegral_comp_comm hi]
  rfl

/-- For continuous generator and source, the forced ordered solution has derivative `-(A t *ᵥ u
t) + b t`. -/
theorem orderedForcedSolution_hasDerivAt {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (hA : Continuous A) (hb : Continuous b)
    (s : ℝ) (v : QState I) (t : ℝ) :
    HasDerivAt (orderedForcedSolution A b s v)
      (-(A t *ᵥ orderedForcedSolution A b s v t) + b t) t := by
  have hc := (ordered_start_continuous A hA s).matrix_mulVec hb
  have hJ := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable s t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := ordered_mulVec_deriv (orderedEvolution_hasDerivAt A hA s t) (hJ.const_add v)
  have he : (fun u => orderedEvolution A s u *ᵥ
      (v + ∫ r in s..u, orderedEvolution A r s *ᵥ b r)) = orderedForcedSolution A b s v :=
    funext (fun u => (ordered_forced_factor A b hA hb s v u).symm)
  rw [he] at hd
  convert! hd using 1
  rw [ordered_forced_factor A b hA hb s v t]
  simp only [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  rw [orderedEvolution_cocycle A hA t s t, orderedEvolution_self, Matrix.one_mulVec]

/-- Any global differentiable solution of the forced equation with initial value `v` at `s`
equals `orderedForcedSolution A b s v`. -/
theorem orderedForcedSolution_unique {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (hA : Continuous A) (hb : Continuous b)
    (s : ℝ) (v : QState I) (u : ℝ → QState I) (hu : u s = v)
    (hder : ∀ t, HasDerivAt u (-(A t *ᵥ u t) + b t) t) :
    u = orderedForcedSolution A b s v := by
  let w := fun t => u t - orderedForcedSolution A b s v t
  have hw (t : ℝ) : HasDerivAt w (-(A t *ᵥ w t)) t := by
    convert! (hder t).sub (orderedForcedSolution_hasDerivAt A b hA hb s v t) using 1
    simp only [w, Matrix.mulVec_sub]
    abel
  have hz (t : ℝ) : HasDerivAt (fun r => orderedEvolution A r s *ᵥ w r) 0 t := by
    convert! ordered_mulVec_deriv (orderedEvolution_hasDerivAt_start A hA s t) (hw t) using 1
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_neg]
    abel
  have he (t : ℝ) : orderedEvolution A t s *ᵥ w t = 0 := by
    have hh := is_const_of_deriv_eq_zero (fun r => (hz r).differentiableAt)
      (fun r => (hz r).deriv) t s
    simpa [w, hu] using! hh
  funext t
  have hh := congrArg (fun x => orderedEvolution A s t *ᵥ x) (he t)
  (try dsimp only at hh)
  rw [Matrix.mulVec_mulVec, orderedEvolution_cocycle A hA t s t,
    orderedEvolution_self, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
  exact sub_eq_zero.mp hh

/-- If the Hermitian part of the continuous generator is positive semidefinite, the forced
solution norm is bounded by the initial norm plus the integral of the source norm. -/
theorem orderedForcedSolution_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (hA : Continuous A) (hb : Continuous b)
    (hPSD : ∀ t, (A t + (A t)ᴴ).PosSemidef) (s t : ℝ) (hst : s ≤ t) (v : QState I) :
    ‖toEuclidean_fromVec (orderedForcedSolution A b s v t)‖ ≤
      ‖toEuclidean_fromVec v‖ + ∫ u in s..t, ‖toEuclidean_fromVec (b u)‖ := by
  let e : QState I →L[ℝ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ
  have hi :=
      ((ordered_start_continuous A hA t).matrix_mulVec hb).intervalIntegrable
      (μ := MeasureTheory.volume) s t
  have hnorm (r : ℝ) (hr : r ≤ t) (x : QState I) :
      ‖e (orderedEvolution A r t *ᵥ x)‖ ≤ ‖e x‖ := by
    have hn := ordered_evolution_psd_contraction I A hA hPSD r t hr
    exact (Matrix.l2_opNorm_mulVec (orderedEvolution A r t) (e x)).trans
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))
  change ‖e (orderedEvolution A s t *ᵥ v + ∫ u in s..t, orderedEvolution A u t *ᵥ b u)‖ ≤
    ‖e v‖ + ∫ u in s..t, ‖e (b u)‖
  rw [map_add, ← e.intervalIntegral_comp_comm hi]
  refine (norm_add_le _ _).trans (add_le_add (hnorm s hst v) ?_)
  apply intervalIntegral.norm_integral_le_of_norm_le hst
  · exact Filter.Eventually.of_forall (fun u hu => hnorm u hu.2 (b u))
  · exact (e.continuous.comp hb).norm.intervalIntegrable s t

/-- For continuous coefficients, the Duhamel expression satisfies the forced initial-value
problem uniquely and obeys the stated norm bound when the generator has positive
semidefinite Hermitian part [AnLiuLin2023]. -/
theorem ordered_forced_solution_duhamel_and_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : ℝ → Matrix I I ℂ)
      (b : ℝ → QState I) (s : ℝ) (v : QState I),
      Continuous A → Continuous b →
      orderedForcedSolution A b s v s = v ∧
      (∀ t, HasDerivAt (orderedForcedSolution A b s v)
        (-(A t *ᵥ orderedForcedSolution A b s v t) + b t) t) ∧
      (∀ u : ℝ → QState I, u s = v →
        (∀ t, HasDerivAt u (-(A t *ᵥ u t) + b t) t) → u = orderedForcedSolution A b s v) ∧
      ((∀ t, (A t + (A t)ᴴ).PosSemidef) → ∀ t, s ≤ t →
        ‖toEuclidean_fromVec (orderedForcedSolution A b s v t)‖ ≤
          ‖toEuclidean_fromVec v‖ + ∫ u in s..t, ‖toEuclidean_fromVec (b u)‖) := by
  intro I _ _ A b s v hA hb
  exact ⟨orderedForcedSolution_self A b s v, orderedForcedSolution_hasDerivAt A b hA hb s v,
    orderedForcedSolution_unique A b hA hb s v,
    fun hp t ht => orderedForcedSolution_norm_le A b hA hb hp s t ht v⟩

/-- The derivative of constant Hamiltonian evolution is left multiplication by `-(Complex.I •
H)`. -/
private theorem ordered_hamiltonian_deriv {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) :
    HasDerivAt (HamiltonianEvolution H) (-(Complex.I • H * HamiltonianEvolution H t)) t := by
  have he : (fun u : ℝ => NormedSpace.exp (u • (-Complex.I • H))) = HamiltonianEvolution H := by
    funext u
    unfold HamiltonianEvolution
    congr 1
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
    ring
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Complex.I • H) t
  rw [congrFun he t] at hd
  rw [he] at hd
  simpa [neg_smul, neg_mul] using! hd

/-- Ordered evolution under a constant Hamiltonian equals its Hamiltonian evolution over the
elapsed time `t - s`. -/
theorem orderedEvolution_constant_hamiltonian {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (s t : ℝ) :
    orderedEvolution (fun _ => Complex.I • H) s t = HamiltonianEvolution H (t-s) := by
  have hd (u : ℝ) : HasDerivAt (fun r => HamiltonianEvolution H (r-s))
      (-(Complex.I • H * HamiltonianEvolution H (u-s))) u := by
    simpa using! (ordered_hamiltonian_deriv H (u-s)).scomp u ((hasDerivAt_id u).sub_const s)
  have he := ordered_matrix_ode_unique (fun _ => Complex.I • H) continuous_const
    (fun r => HamiltonianEvolution H (r-s)) (orderedEvolution (fun _ => Complex.I • H) s)
    s (by simp) hd (orderedEvolution_hasDerivAt _ continuous_const s)
  exact (congrFun he t).symm

/-- For a constant Hermitian `H₀` and a continuous Hermitian perturbation, full ordered
evolution factors into the `H₀` evolution and the ordered interaction-picture evolution
[LowWiebe2018]. -/
theorem ordered_interaction_picture_identity :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H₀ : Matrix I I ℂ)
      (V : ℝ → Matrix I I ℂ), H₀.IsHermitian → Continuous V →
      (∀ t, (V t).IsHermitian) → ∀ t : ℝ,
      orderedEvolution (fun u => Complex.I • (H₀ + V u)) 0 t =
        HamiltonianEvolution H₀ t *
          orderedEvolution (fun u => Complex.I • interactionGenerator H₀ V u) 0 t := by
  intro I _ _ H₀ V _hH₀ hV _hHerm t
  let U := HamiltonianEvolution H₀
  let B := fun u => Complex.I • interactionGenerator H₀ V u
  let A := fun u => Complex.I • (H₀ + V u)
  have hU : Continuous U :=
      continuous_iff_continuousAt.mpr (fun u => (ordered_hamiltonian_deriv H₀ u).continuousAt)
  have hB : Continuous B := by
    change Continuous (fun u => Complex.I • (U (-u) * V u * U u))
    fun_prop
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hc (u : ℝ) : U u * B u = (Complex.I • V u) * U u := by
    have hi : U u * U (-u) = 1 := by
      rw [← hamiltonianEvolution_add]
      simp
    dsimp [B, interactionGenerator]
    rw [Matrix.mul_smul, ← mul_assoc, ← mul_assoc, hi, one_mul, Matrix.smul_mul]
  have hd (u : ℝ) : HasDerivAt (fun r => U r * orderedEvolution B 0 r)
      (-(A u * (U u * orderedEvolution B 0 u))) u := by
    convert! (ordered_hamiltonian_deriv H₀ u).mul (orderedEvolution_hasDerivAt B hB 0 u) using 1
    dsimp [A]
    simp only [smul_add, Matrix.add_mul, mul_neg, neg_mul]
    rw [← mul_assoc (U u) (B u), hc]
    dsimp only [U]
    simp only [mul_assoc, neg_add]
  have he := ordered_matrix_ode_unique A hA (fun r => U r * orderedEvolution B 0 r)
    (orderedEvolution A 0) 0 (by simp [U]) hd (orderedEvolution_hasDerivAt A hA 0)
  exact (congrFun he t).symm

/-- If Hamiltonian variation from the segment left endpoint is at most `L * (u - a)`, freezing
it there incurs error at most `L * (b - a) ^ 2 / 2`. -/
private theorem ordered_sampled_local_error {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (hHerm : ∀ u, (H u).IsHermitian)
    (a b L : ℝ) (hab : a ≤ b)
    (hLip : ∀ u ∈ Set.Icc a b, ‖H u - H a‖ ≤ L*(u-a)) :
    ‖HamiltonianEvolution (H a) (b-a) - orderedEvolution (fun u => Complex.I • H u) a b‖ ≤
      L*(b-a)^2/2 := by
  have hf : IntervalIntegrable (fun u => ‖H u - H a‖) MeasureTheory.volume a b :=
    (hH.sub continuous_const).norm.intervalIntegrable a b
  have hg : IntervalIntegrable (fun u => L * (u - a)) MeasureTheory.volume a b :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable a b
  calc
    _ = ‖orderedEvolution (fun u => Complex.I • H u) a b -
        HamiltonianEvolution (H a) (b - a)‖ := norm_sub_rev _ _
    _ ≤ ∫ u in a..b, ‖H u - H a‖ :=
      orderedEvolution_frozen_segment_error H hH hHerm hab
    _ ≤ ∫ u in a..b, L * (u - a) :=
      intervalIntegral.integral_mono_on hab hf hg hLip
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ : ℝ => a)
          (continuous_id.intervalIntegrable a b)
          (continuous_const.intervalIntegrable a b), integral_id,
        intervalIntegral.integral_const]
      ring

/-- The chronologically composed product of frozen Hamiltonian evolutions at successive
left-sampled times. -/
private noncomputable def orderedSampledProduct {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (h : ℝ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | n+1 => HamiltonianEvolution (H ((n:ℝ)*h)) h * orderedSampledProduct H h n

/-- Execution of the left-sampled Hamiltonian gate list equals application of
`orderedSampledProduct`. -/
private theorem orderedSampledProduct_run {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (h : ℝ) (n : ℕ) (v : QState I) :
    Run 1 ((List.range n).map (fun j : ℕ => Step.gate (HamiltonianEvolution (H ((j:ℝ)*h)) h))) v =
      orderedSampledProduct H h n *ᵥ v := by
  induction n with
  | zero => simp [orderedSampledProduct]
  | succ n ih =>
    rw [List.range_succ, List.map_append, run_append, ih]
    simp [Run, ApplyGate, orderedSampledProduct, Matrix.mulVec_mulVec]

/-- The sampled evolution word is the list of frozen Hamiltonian gates at the uniform
left-sampled times. -/
private theorem sampledEvolutionWord_eq_map {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (N : ℕ) : sampledEvolutionWord H T N =
      (List.range N).map (fun j : ℕ => Step.gate (HamiltonianEvolution (H ((j:ℝ)*T/N)) (T/N))) := by
  change ((List.range N).flatMap (fun j : ℕ => [(j:ℝ)])).map _ = _
  rw [← List.map_eq_flatMap, List.map_map]
  rfl

/-- For a Hermitian Hamiltonian, the sampled word is a unitary circuit with zero oracle queries
and exactly `N` gates. -/
theorem sampledEvolutionWord_unitary_counts {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hHerm : ∀ u, (H u).IsHermitian) (T : ℝ) (N : ℕ) :
    IsUnitaryCircuit (sampledEvolutionWord H T N) ∧
    QueryCount (sampledEvolutionWord H T N) = 0 ∧ GateCount (sampledEvolutionWord H T N) = N := by
  have hq (js : List ℕ) : QueryCount (js.map (fun j : ℕ => Step.gate (HamiltonianEvolution (H ((j:ℝ)*T/N)) (T/N)))) = 0 := by
    induction js with
    | nil => rfl
    | cons j js ih => simpa [QueryCount] using! ih
  have hg (js : List ℕ) : GateCount (js.map (fun j : ℕ => Step.gate (HamiltonianEvolution (H ((j:ℝ)*T/N)) (T/N)))) = js.length := by
    induction js with
    | nil => rfl
    | cons j js ih => simp [ih]
  rw [sampledEvolutionWord_eq_map]
  refine ⟨?_, hq _, ?_⟩
  · intro U hU
    obtain ⟨j, _hj, he⟩ := List.mem_map.mp hU
    cases he
    exact hamiltonianEvolution_unitary (hHerm _) _
  · simpa using! hg (List.range N)

/-- For a continuous Hermitian Hamiltonian Lipschitz on `[0, T]`, the `N`-step frozen product
has operator error at most `L * T ^ 2 / (2 * N)` for positive `N`. -/
private theorem orderedSampledProduct_error {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (hHerm : ∀ u, (H u).IsHermitian)
    (T L : ℝ) (N : ℕ) (hT : 0 ≤ T) (hN : 0 < N)
    (hLip : ∀ u ∈ Set.Icc (0:ℝ) T, ∀ v ∈ Set.Icc (0:ℝ) T, ‖H u-H v‖ ≤ L*|u-v|) :
    ‖orderedSampledProduct H (T/N) N - orderedEvolution (fun u => Complex.I • H u) 0 T‖ ≤
      L*T^2/(2*N) := by
  let h : ℝ := T/N
  let A := fun u => Complex.I • H u
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hh : 0 ≤ h := div_nonneg hT (Nat.cast_nonneg N)
  have hNh : (N : ℝ)*h = T := by dsimp [h]; field_simp
  have hmem (n : ℕ) (hn : n ≤ N) : (n : ℝ)*h ∈ Set.Icc (0:ℝ) T := by
    refine ⟨mul_nonneg (Nat.cast_nonneg n) hh, ?_⟩
    have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
    exact (mul_le_mul_of_nonneg_right hn' hh).trans_eq hNh
  have herr (n : ℕ) (hn : n ≤ N) :
      ‖orderedSampledProduct H h n - orderedEvolution A 0 ((n:ℝ)*h)‖ ≤ (n:ℝ)*L*h^2/2 := by
    induction n with
    | zero => simp [orderedSampledProduct]
    | succ n ih =>
      have hn0 : n ≤ N := (Nat.le_succ n).trans hn
      have hi := ih hn0
      let a := (n:ℝ)*h
      let b := ((n+1:ℕ):ℝ)*h
      have ha : a ∈ Set.Icc (0:ℝ) T := hmem n hn0
      have hb : b ∈ Set.Icc (0:ℝ) T := hmem (n+1) hn
      have heh : b-a = h := by dsimp [a, b]; push_cast; ring
      have hab : a ≤ b := by linarith
      have hloc := ordered_sampled_local_error H hH hHerm a b L hab (fun u hu => (by
        have huT : u ∈ Set.Icc (0:ℝ) T := ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
        simpa [abs_of_nonneg (sub_nonneg.mpr hu.1)] using! hLip u huT a ha))
      rw [heh] at hloc
      let U := HamiltonianEvolution (H a) h
      let E := orderedEvolution A a b
      let P := orderedSampledProduct H h n
      let Q := orderedEvolution A 0 a
      have hU : ‖U‖ ≤ 1 := l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hHerm a) h)
      have hQ : ‖Q‖ ≤ 1 :=
          l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hH hHerm 0 a)
      have he : orderedSampledProduct H h (n+1) - orderedEvolution A 0 b =
          U*(P-Q) + (U-E)*Q := by
        rw [orderedSampledProduct, ← orderedEvolution_cocycle A (by dsimp [A]; fun_prop) 0 a b]
        dsimp [U, P, Q, E, a]
        noncomm_ring
      rw [he]
      calc
        _ ≤ ‖U*(P-Q)‖ + ‖(U-E)*Q‖ := norm_add_le _ _
        _ ≤ ‖P-Q‖ + ‖U-E‖ := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              ((mul_le_mul_of_nonneg_right hU (norm_nonneg _)).trans_eq (one_mul _))
          · exact (norm_mul_le _ _).trans
              ((mul_le_mul_of_nonneg_left hQ (norm_nonneg _)).trans_eq (mul_one _))
        _ ≤ (n:ℝ)*L*h^2/2 + L*h^2/2 := add_le_add hi hloc
        _ = _ := by push_cast; ring
  have hn := herr N le_rfl
  rw [hNh] at hn
  convert! hn using 1
  dsimp [h]
  field_simp

/-- For a continuous Hermitian Hamiltonian with Lipschitz constant `L` on `[0, T]`, the sampled
program uses zero queries and `N` gates and has state error at most `L * T ^ 2 / (2 * N)`
times the input norm [LowWiebe2018]. -/
theorem ordered_sampled_program_error_and_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ)
      (T L : ℝ) (N : ℕ), Continuous H → (∀ u, (H u).IsHermitian) →
      0 ≤ T → 0 ≤ L → 0 < N →
      (∀ u ∈ Set.Icc (0:ℝ) T, ∀ v ∈ Set.Icc (0:ℝ) T, ‖H u - H v‖ ≤ L*|u-v|) →
      IsUnitaryCircuit (sampledEvolutionWord H T N) ∧
      QueryCount (sampledEvolutionWord H T N) = 0 ∧ GateCount (sampledEvolutionWord H T N) = N ∧
      (∀ ψ : QState I, ‖toEuclidean_fromVec
        (Run 1 (sampledEvolutionWord H T N) ψ -
          orderedEvolution (fun u => Complex.I • H u) 0 T *ᵥ ψ)‖ ≤
        L*T^2/(2*N) * ‖toEuclidean_fromVec ψ‖) := by
  intro I _ _ H T L N hH hHerm hT _hL hN hLip
  obtain ⟨hu, hq, hg⟩ := sampledEvolutionWord_unitary_counts H hHerm T N
  refine ⟨hu, hq, hg, ?_⟩
  intro ψ
  have hrun : Run 1 (sampledEvolutionWord H T N) ψ = orderedSampledProduct H (T/N) N *ᵥ ψ := by
    simpa [sampledEvolutionWord_eq_map, mul_div_assoc] using! orderedSampledProduct_run H (T/N) N ψ
  rw [hrun, ← Matrix.sub_mulVec]
  exact (Matrix.l2_opNorm_mulVec _ (toEuclidean_fromVec ψ)).trans
    (mul_le_mul_of_nonneg_right (orderedSampledProduct_error H hH hHerm T L N hT hN hLip) (norm_nonneg _))

end Qatlib.Concepts.LchsSimulation.TimeOrdered
