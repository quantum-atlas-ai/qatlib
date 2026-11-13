/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution

/-!
# Cyclic period sampling and fresh measurement laws

Defines the cyclic sampling circuit consisting of a Fourier transform, an additive oracle query,
and an inverse Fourier transform. Its measured first-register distribution is represented both
by `cyclicSampleDist` and by a probability mass function, with fresh and counted repetitions
linked to independent product probabilities.

Under the exact congruence collision promise for a period `r` dividing `N`, the record
distribution is uniform on multiples of `N / r`. This is the exact-period Fourier sampling
mechanism underlying [Shor1997].

## Main statements

* `cyclic_actual_sampling_semantics_cost`: gives the measured semantics and circuit counts.
* `cyclicFreshSamples_apply`: identifies fresh measurement masses with product probabilities.
* `cyclic_period_born_uniform_multiples`: proves the exact supported uniform law.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.HspRecovery.CyclicRecovery

open Matrix

variable {R : Type} [Fintype R] [DecidableEq R] [AddCommGroup R]

/-- The circuit applying the cyclic Fourier transform to the first register, making one additive
oracle query, and applying the inverse Fourier transform to the first register. -/
noncomputable def cyclicSamplingCircuit (N : ℕ) : Circuit (Fin N × R) :=
  [Step.gate (TensorGate (QFTMatrix N) (1 : Matrix R R ℂ)), Step.query,
    Step.gate (TensorGate (QFTMatrix N)ᴴ (1 : Matrix R R ℂ))]

/-- For positive `N`, the conjugate transpose of `QFTMatrix N` is unitary. -/
theorem qftMatrix_conjTranspose_unitary (N : ℕ) (hN : 0 < N) :
    (QFTMatrix N)ᴴ ∈ unitaryGroup (Fin N) ℂ := by
  have h := Unitary.star_mem (qftMatrix_unitary hN)
  rwa [Matrix.star_eq_conjTranspose] at h

omit [AddCommGroup R] in

/-- For positive `N`, every gate in the cyclic sampling circuit is unitary. -/
theorem isUnitaryCircuit_cyclicSamplingCircuit (N : ℕ) (hN : 0 < N) :
    IsUnitaryCircuit (cyclicSamplingCircuit (R := R) N) := by
  intro U hU
  simp only [cyclicSamplingCircuit, List.mem_cons, List.not_mem_nil, or_false] at hU
  rcases hU with hU | hU | hU
  · obtain rfl := Step.gate.inj hU
    exact tensorGate_unitary (qftMatrix_unitary hN) (Submonoid.one_mem _)
  · cases hU
  · obtain rfl := Step.gate.inj hU
    exact tensorGate_unitary (qftMatrix_conjTranspose_unitary N hN) (Submonoid.one_mem _)

/-- For positive `N`, the cyclic Fourier transform sends the zero basis state to the uniform
state. -/
theorem applyGate_qftMatrix_ket_zero (N : ℕ) (hN : 0 < N) :
    ApplyGate (QFTMatrix N) (Ket (⟨0, hN⟩ : Fin N)) = Uniform (Fin N) := by
  funext x
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, qftMatrix_apply, Uniform,
    Fintype.card_fin]
  show (Real.sqrt (N : ℝ) : ℂ)⁻¹ * primRoot N ^ ((x.val : ℤ) * ((0 : ℕ) : ℤ)) = _
  simp

omit [AddCommGroup R] in

/-- Applying `U` to the first register and the identity to the second acts by `U` on each fixed
second-register slice. -/
theorem applyGate_tensorGate_one_left_slice {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (ψ : QState (Fin N × R)) (y : Fin N) (z : R) :
    ApplyGate (TensorGate U (1 : Matrix R R ℂ)) ψ (y, z) =
      ApplyGate U (fun x => ψ (x, z)) y := by
  simp only [ApplyGate, TensorGate, Matrix.kronecker_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply]
  simp

/-- Running cyclic sampling from zero basis states equals querying the uniform first-register
state and then applying the inverse Fourier transform to that register. -/
theorem run_cyclicSamplingCircuit (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
        (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R))) =
      ApplyGate (TensorGate (QFTMatrix N)ᴴ (1 : Matrix R R ℂ))
        (ApplyGate (AddOracle f) (TensorState (Uniform (Fin N)) (Ket (0 : R)))) := by
  show ApplyGate (TensorGate (QFTMatrix N)ᴴ (1 : Matrix R R ℂ)) (ApplyGate (AddOracle f)
    (ApplyGate (TensorGate (QFTMatrix N) (1 : Matrix R R ℂ))
      (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R))))) = _
  rw [applyGate_tensorGate, applyGate_qftMatrix_ket_zero N hN, applyGate_one]

/-- The output of cyclic sampling from zero basis states is normalized for positive `N`. -/
theorem normalized_run_cyclicSamplingCircuit (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    Normalized (Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
      (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R)))) :=
  (isUnitaryCircuit_cyclicSamplingCircuit N hN).normalized_run (addOracle_unitary f)
    (normalized_tensorState (normalized_ket _) (normalized_ket _))

/-- The finite distribution of first-register measurements after running the cyclic sampling
circuit from zero basis states. -/
noncomputable def cyclicSampleDist (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    FinDist (Fin N) where
  prob y := MarginalProbLeft (Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
    (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R)))) {y}
  nonneg _ := measureProb_nonneg _ _
  sum_one := by
    have hnorm := normalized_run_cyclicSamplingCircuit (R := R) N hN f
    simp only [MarginalProbLeft, MeasureProb, Finset.sum_product, Finset.sum_singleton]
    rw [← Fintype.sum_prod_type]
    exact hnorm

/-- The cyclic sampling circuit uses one query and two gate macros, has unitary gates, and
realizes the first-register marginal defining `cyclicSampleDist` [Shor1997]. -/
theorem cyclic_actual_sampling_semantics_cost (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    QueryCount (cyclicSamplingCircuit (R := R) N) = 1 ∧
      GateCount (cyclicSamplingCircuit (R := R) N) = 2 ∧
      IsUnitaryCircuit (cyclicSamplingCircuit (R := R) N) ∧
      (∀ y : Fin N, (cyclicSampleDist N hN f).prob y =
        MarginalProbLeft (Run (AddOracle f) (cyclicSamplingCircuit N)
          (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R)))) {y}) :=
  ⟨rfl, rfl, isUnitaryCircuit_cyclicSamplingCircuit N hN, fun _ => rfl⟩

/-- The joint Born probability mass function of both registers after cyclic sampling. -/
noncomputable def cyclicJointLaw (N : ℕ) (hN : 0 < N) (f : Fin N → R) : PMF (Fin N × R) :=
  bornDistribution
    (Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
      (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R))))
    (normalized_run_cyclicSamplingCircuit N hN f)

/-- The first-register marginal probability mass function of `cyclicJointLaw`. -/
noncomputable def cyclicSampleLaw (N : ℕ) (hN : 0 < N) (f : Fin N → R) : PMF (Fin N) :=
  (cyclicJointLaw N hN f).map Prod.fst

/-- The probability of a cyclic sample `y` is its singleton first-register marginal after
running the sampling circuit. -/
theorem cyclicSampleDist_prob_apply (N : ℕ) (hN : 0 < N) (f : Fin N → R) (y : Fin N) :
    (cyclicSampleDist N hN f).prob y =
      MarginalProbLeft (Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
        (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R)))) {y} := rfl

/-- The probability mass of `cyclicSampleLaw` is the `ENNReal.ofReal` conversion of the
corresponding `cyclicSampleDist` probability. -/
theorem cyclicSampleLaw_apply (N : ℕ) (hN : 0 < N) (f : Fin N → R) (y : Fin N) :
    cyclicSampleLaw N hN f y = ENNReal.ofReal ((cyclicSampleDist N hN f).prob y) := by
  simp only [cyclicSampleLaw, cyclicJointLaw, PMF.map_apply, tsum_fintype,
    Fintype.sum_prod_type, bornDistribution_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => bornProb_nonneg _ (y, z)),
    cyclicSampleDist_prob_apply]
  unfold MarginalProbLeft MeasureProb
  rw [Finset.sum_product, Finset.sum_singleton]

/-- The probability mass function of a finite sequence of fresh cyclic sampling measurements,
retaining the first register of each run. -/
noncomputable def cyclicFreshSamples (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    (m : ℕ) → PMF (Fin m → Fin N)
  | 0 => PMF.pure Fin.elim0
  | m + 1 => (cyclicJointLaw N hN f).bind fun q =>
      (cyclicFreshSamples N hN f m).map (Fin.cons q.1)

/-- A fresh sequence of length `m + 1` is generated by drawing from `cyclicSampleLaw` and
prepending it to an independent fresh sequence of length `m`. -/
theorem cyclicFreshSamples_succ (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    cyclicFreshSamples N hN f (m + 1) =
      (cyclicSampleLaw N hN f).bind fun y =>
        (cyclicFreshSamples N hN f m).map (Fin.cons y) := by
  simp only [cyclicFreshSamples, cyclicSampleLaw, PMF.bind_map, Function.comp_def]

/-- The cyclic sample law charged one oracle query. -/
noncomputable def cyclicCountedSample (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    CostedLaw (Fin N) :=
  (cyclicJointLaw N hN f).map (fun q => (q.1, 1))

/-- The costed law of fresh cyclic samples, accumulating one oracle query per sample. -/
noncomputable def cyclicCountedFreshSamples (N : ℕ) (hN : 0 < N) (f : Fin N → R) :
    (m : ℕ) → CostedLaw (Fin m → Fin N)
  | 0 => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret Fin.elim0
  | m + 1 => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (cyclicCountedSample N hN f) fun y =>
      (cyclicCountedFreshSamples N hN f m).map (fun out => (Fin.cons y out.1, out.2))

/-- The counted law of `m` fresh samples equals the uncounted law paired with constant cost `m`. -/
theorem cyclicCountedFreshSamples_eq (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    cyclicCountedFreshSamples N hN f m =
      (cyclicFreshSamples N hN f m).map (fun ω => (ω, m)) := by
  induction m with
  | zero => simp [cyclicCountedFreshSamples, cyclicFreshSamples, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
  | succ m ih =>
    simp only [cyclicCountedFreshSamples, cyclicCountedSample, cyclicFreshSamples,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, ih, PMF.bind_map, PMF.map_comp, PMF.map_bind,
      Function.comp_def, Nat.add_comm]

/-- Erasing costs from the counted fresh-sample law recovers `cyclicFreshSamples`. -/
theorem cyclicCountedFreshSamples_erase (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    (cyclicCountedFreshSamples N hN f m).map Prod.fst = cyclicFreshSamples N hN f m := by
  rw [cyclicCountedFreshSamples_eq, PMF.map_comp]
  exact PMF.map_id _

/-- The mass of a fresh sequence with specified head and tail factors as the head mass times the
fresh tail mass. -/
theorem cyclicFreshSamples_cons (N : ℕ) (hN : 0 < N) (f : Fin N → R)
    (m : ℕ) (y : Fin N) (ys : Fin m → Fin N) :
    cyclicFreshSamples N hN f (m + 1) (Fin.cons y ys) =
      cyclicSampleLaw N hN f y * cyclicFreshSamples N hN f m ys := by
  rw [cyclicFreshSamples_succ]
  simp [PMF.bind_apply, PMF.map_apply, tsum_fintype, Fin.cons_inj, ite_and,
    Finset.sum_ite_irrel, mul_ite]

/-- The mass of a fresh cyclic sample sequence equals the `ENNReal.ofReal` conversion of its
independent product probability. -/
theorem cyclicFreshSamples_apply (N : ℕ) (hN : 0 < N) (f : Fin N → R)
    (m : ℕ) (ys : Fin m → Fin N) :
    cyclicFreshSamples N hN f m ys =
      ENNReal.ofReal ((cyclicSampleDist N hN f).probOf ys) := by
  induction m with
  | zero =>
    simp [cyclicFreshSamples, PMF.pure_apply, Subsingleton.elim ys Fin.elim0,
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
  | succ m ih =>
    conv_lhs => rw [← Fin.cons_self_tail ys]
    rw [cyclicFreshSamples_cons, cyclicSampleLaw_apply, ih]
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf, Fin.prod_univ_succ]
    exact (ENNReal.ofReal_mul ((cyclicSampleDist N hN f).nonneg (ys 0))).symm

/-- The probability of any decidable fresh-sample event equals the `ENNReal.ofReal` conversion
of its `FinDist.probEvent` value. -/
theorem cyclicFreshSamples_event (N : ℕ) (hN : 0 < N) (f : Fin N → R)
    (m : ℕ) (E : (Fin m → Fin N) → Prop) [DecidablePred E] :
    (∑ ys ∈ Finset.univ.filter E, cyclicFreshSamples N hN f m ys) =
      ENNReal.ofReal ((cyclicSampleDist N hN f).probEvent E) := by
  simp only [cyclicFreshSamples_apply,
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent]
  exact (ENNReal.ofReal_sum_of_nonneg (fun ys _ =>
    Finset.prod_nonneg (fun i _ => (cyclicSampleDist N hN f).nonneg (ys i)))).symm

/-- For positive `N = d * M`, the root-of-unity sum over exponents `c * d * k` is `M` if `M`
divides `c` and zero otherwise. -/
theorem sum_primRoot_zpow_step (N : ℕ) (hN : 0 < N) {d M : ℕ} (hdM : d * M = N) (c : ℤ) :
    ∑ k : Fin M, primRoot N ^ (c * ((d * k.val : ℕ) : ℤ)) =
      if ((M : ℤ) ∣ c) then (M : ℂ) else 0 := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; rw [Nat.zero_mul] at hdM; omega
    · exact hd
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; rw [Nat.mul_zero] at hdM; omega
    · exact hM
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdiv_iff : (N : ℤ) ∣ c * (d : ℤ) ↔ (M : ℤ) ∣ c := by
    rw [← hdM, Nat.cast_mul, mul_comm c (d : ℤ)]
    exact Int.mul_dvd_mul_iff_left hdZ
  have hterm : ∀ k : Fin M, primRoot N ^ (c * ((d * k.val : ℕ) : ℤ))
      = (primRoot N ^ (c * (d : ℤ))) ^ k.val := by
    intro k
    have he : (c : ℤ) * ((d * k.val : ℕ) : ℤ) = (c * (d : ℤ)) * (k.val : ℤ) := by
      push_cast; ring
    rw [he, _root_.zpow_mul, zpow_natCast]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  rw [Fin.sum_univ_eq_sum_range (fun k => (primRoot N ^ (c * (d : ℤ))) ^ k) M]
  have hwM : (primRoot N ^ (c * (d : ℤ))) ^ M = 1 := by
    rw [← zpow_natCast (primRoot N ^ (c * (d : ℤ))) M, ← _root_.zpow_mul]
    have he : (c * (d : ℤ)) * (M : ℤ) = c * (N : ℤ) := by
      rw [← hdM]; push_cast; ring
    rw [he]
    exact (primRoot_zpow_eq_one_iff hN _).mpr ⟨c, by ring⟩
  by_cases hw : primRoot N ^ (c * (d : ℤ)) = 1
  · rw [ite_eq_left (hdiv_iff.mp ((primRoot_zpow_eq_one_iff hN _).mp hw))]
    rw [Finset.sum_congr rfl (fun k _ => by rw [hw, one_pow]), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right (fun hMc => hw ((primRoot_zpow_eq_one_iff hN _).mpr (hdiv_iff.mpr hMc)))]
    rw [geom_sum_eq hw M, hwM, sub_self, zero_div]

/-- Evaluates the root-of-unity sum over a residue fiber modulo `r`: it vanishes unless `N / r`
divides the frequency, in which case it equals the fiber size times the phase at its
representative. -/
theorem sum_fiber_mod_primRoot (N : ℕ) (hN : 0 < N) {r : ℕ} (hr : 0 < r) (hrdvd : r ∣ N)
    (a : ℕ) (ha : a < r) (c : ℤ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin N => x.val % r = a),
        primRoot N ^ (c * (x.val : ℤ))
      = if (((N / r : ℕ) : ℤ) ∣ c) then
          ((N / r : ℕ) : ℂ) * primRoot N ^ (c * (a : ℤ)) else 0 := by
  set q := N / r with hqdef
  have hq : r * q = N := Nat.mul_div_cancel' hrdvd
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · rw [hq0, Nat.mul_zero] at hq; omega
    · exact hq0
  have hbound : ∀ k : Fin q, a + r * k.val < N := by
    intro k
    have hkle : k.val + 1 ≤ q := k.isLt
    have h1 : r * (k.val + 1) ≤ r * q := Nat.mul_le_mul_left r hkle
    have h2 : r * (k.val + 1) = r * k.val + r := by ring
    omega
  have hinj : Function.Injective (fun k : Fin q => (⟨a + r * k.val, hbound k⟩ : Fin N)) := by
    intro k₁ k₂ h
    have hval := Fin.ext_iff.mp h
    have hval' : a + r * k₁.val = a + r * k₂.val := hval
    have := Nat.add_left_cancel hval'
    exact Fin.ext (Nat.mul_left_cancel hr this)
  have hfilter : Finset.univ.filter (fun x : Fin N => x.val % r = a)
      = Finset.univ.map ⟨fun k : Fin q => ⟨a + r * k.val, hbound k⟩, hinj⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      refine ⟨⟨x.val / r, ?_⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hr]
        calc x.val < N := x.isLt
          _ = r * q := hq.symm
          _ = q * r := Nat.mul_comm _ _
      · apply Fin.ext
        show a + r * (x.val / r) = x.val
        rw [← hx]
        exact Nat.mod_add_div x.val r
    · rintro ⟨k, rfl⟩
      show (a + r * k.val) % r = a
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  rw [hfilter, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ k : Fin q, primRoot N ^ (c * ((a + r * k.val : ℕ) : ℤ))
      = primRoot N ^ (c * (a : ℤ)) * primRoot N ^ (c * ((r * k.val : ℕ) : ℤ)) := by
    intro k
    have he : (c : ℤ) * ((a + r * k.val : ℕ) : ℤ)
        = c * (a : ℤ) + c * ((r * k.val : ℕ) : ℤ) := by push_cast; ring
    rw [he, zpow_add₀ (primRoot_ne_zero N)]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum,
    sum_primRoot_zpow_step N hN (d := r) (M := q) hq c]
  by_cases hdvd : ((q : ℕ) : ℤ) ∣ c
  · rw [ite_eq_left hdvd, ite_eq_left hdvd]; ring
  · rw [ite_eq_right hdvd, ite_eq_right hdvd, mul_zero]

omit [Fintype R] [AddCommGroup R] in

/-- If collisions of `f` are exactly equality of residues modulo a positive divisor `r` of `N`,
the image of `f` has cardinality `r`. -/
theorem card_image_of_exact_collision (N : ℕ) (hN : 0 < N) (f : Fin N → R)
    {r : ℕ} (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) :
    (Finset.univ.image f).card = r := by
  have hrN : r ≤ N := Nat.le_of_dvd hN hrdvd
  set g : Fin r → R := fun a => f ⟨a.val, lt_of_lt_of_le a.isLt hrN⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have h := (hcol ⟨a.val, lt_of_lt_of_le a.isLt hrN⟩ ⟨b.val, lt_of_lt_of_le b.isLt hrN⟩).mp hab
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h
    exact Fin.ext h
  have himage : Finset.univ.image f = Finset.univ.image g := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x.val % r, Nat.mod_lt _ hr⟩, ?_⟩
      show f ⟨x.val % r, lt_of_lt_of_le (Nat.mod_lt _ hr) hrN⟩ = f x
      exact (hcol _ _).mpr (Nat.mod_mod _ _)
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, lt_of_lt_of_le a.isLt hrN⟩, rfl⟩
  rw [himage, Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin]

/-- Under the exact congruence collision promise with positive `r ∣ N`, a cyclic Fourier record
has probability `1 / r` when divisible by `N / r` and zero otherwise [Shor1997]. -/
theorem cyclic_period_born_uniform_multiples (N r : ℕ) (hN : 0 < N) (f : Fin N → R)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) :
    ∀ y : Fin N, (cyclicSampleDist N hN f).prob y =
      if (N / r) ∣ y.val then 1 / (r : ℝ) else 0 := by
  intro y
  set q := N / r with hqdef
  set ψ := Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
    (TensorState (Ket (⟨0, hN⟩ : Fin N)) (Ket (0 : R))) with hψdef
  have hqftH : ∀ a b : Fin N, (QFTMatrix N)ᴴ a b =
      ((Real.sqrt (N : ℝ) : ℂ))⁻¹ * primRoot N ^ (-((b.val : ℤ) * (a.val : ℤ))) := by
    intro a b
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [qftMatrix_apply, map_mul, map_inv₀, Complex.conj_ofReal, primRoot_conj_zpow]
  have hψ2 : ∀ (x : Fin N) (z : R),
      ApplyGate (AddOracle f) (TensorState (Uniform (Fin N)) (Ket (0 : R))) (x, z)
        = if z = f x then ((Real.sqrt (N : ℝ) : ℂ))⁻¹ else 0 := by
    intro x z
    rw [applyGate_addOracle]
    simp only [tensorState_apply, ket_apply, Uniform, Fintype.card_fin, sub_eq_zero,
      mul_ite, mul_one, mul_zero]
  have hamp : ∀ (yy : Fin N) (z : R), ψ (yy, z)
      = (N : ℂ)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : Fin N => f x = z),
          primRoot N ^ (-((x.val : ℤ) * (yy.val : ℤ))) := by
    intro yy z
    rw [hψdef, run_cyclicSamplingCircuit N hN f, applyGate_tensorGate_one_left_slice]
    have h2 : (fun x : Fin N =>
          ApplyGate (AddOracle f) (TensorState (Uniform (Fin N)) (Ket (0 : R))) (x, z))
        = fun x : Fin N => if z = f x then ((Real.sqrt (N : ℝ) : ℂ))⁻¹ else 0 :=
      funext fun x => hψ2 x z
    rw [h2]
    simp only [ApplyGate, Matrix.mulVec, dotProduct]
    have h1 : ∀ x : Fin N, (QFTMatrix N)ᴴ yy x *
          (if z = f x then ((Real.sqrt (N : ℝ) : ℂ))⁻¹ else 0)
        = if f x = z then (((Real.sqrt (N : ℝ) : ℂ))⁻¹ * ((Real.sqrt (N : ℝ) : ℂ))⁻¹)
            * primRoot N ^ (-((x.val : ℤ) * (yy.val : ℤ))) else 0 := by
      intro x
      rw [hqftH yy x]
      by_cases h : z = f x
      · rw [ite_eq_left h, ite_eq_left h.symm]; ring
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm), mul_zero]
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_filter, ← Finset.mul_sum,
      inv_sqrt_mul_inv_sqrt hN]
  have hborn : ∀ z : R, BornProb ψ (y, z)
      = if z ∈ Finset.univ.image f then
          (if q ∣ y.val then ((r : ℝ))⁻¹ ^ 2 else 0) else 0 := by
    intro z
    unfold BornProb
    by_cases hz : z ∈ Finset.univ.image f
    · obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hz
      rw [ite_eq_left hz]
      have hfilter : Finset.univ.filter (fun x : Fin N => f x = z)
          = Finset.univ.filter (fun x : Fin N => x.val % r = s.val % r) := by
        apply Finset.filter_congr
        intro x _
        rw [← hs]
        exact hcol x s
      have hsum := sum_fiber_mod_primRoot N hN hr hrdvd (s.val % r) (Nat.mod_lt _ hr)
        (-(y.val : ℤ))
      have hexp : ∑ x ∈ Finset.univ.filter (fun x : Fin N => x.val % r = s.val % r),
            primRoot N ^ (-((x.val : ℤ) * (y.val : ℤ)))
          = ∑ x ∈ Finset.univ.filter (fun x : Fin N => x.val % r = s.val % r),
            primRoot N ^ ((-(y.val : ℤ)) * (x.val : ℤ)) :=
        Finset.sum_congr rfl fun x _ => by
          have he : -((x.val : ℤ) * (y.val : ℤ)) = -(y.val : ℤ) * (x.val : ℤ) := by ring
          rw [he]
      have hdvd_iff : ((q : ℕ) : ℤ) ∣ -(y.val : ℤ) ↔ q ∣ y.val := by
        rw [Int.dvd_neg, Int.natCast_dvd_natCast]
      have hnormN : ‖((N : ℂ))⁻¹‖ = ((N : ℝ))⁻¹ := by
        rw [norm_inv, ← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg N)]
      have hnormq : ‖((q : ℕ) : ℂ)‖ = (q : ℝ) := by
        rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg _)]
      have hqR : (q : ℝ) = (N : ℝ) / r := by
        have hqcast : (r : ℝ) * q = N := by exact_mod_cast Nat.mul_div_cancel' hrdvd
        have hrR0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
        field_simp [hrR0]
        linarith
      rw [hamp y z, hfilter, hexp, hsum]
      by_cases hqy : q ∣ y.val
      · rw [ite_eq_left (hdvd_iff.mpr hqy), ite_eq_left hqy]
        rw [norm_mul, norm_mul, hnormN, hnormq, norm_primRoot_zpow, mul_one]
        have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        have heq : (N : ℝ)⁻¹ * (q : ℝ) = (r : ℝ)⁻¹ := by
          rw [hqR, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]
        rw [heq]
      · rw [ite_eq_right (fun h => hqy (hdvd_iff.mp h)), ite_eq_right hqy]
        simp
    · rw [ite_eq_right hz]
      have hfilter : Finset.univ.filter (fun x : Fin N => f x = z) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro x _ hfx
        exact hz (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hfx⟩)
      rw [hamp y z, hfilter]
      simp
  have hprob : (cyclicSampleDist N hN f).prob y = ∑ z : R, BornProb ψ (y, z) := by
    rw [hψdef, cyclicSampleDist_prob_apply]
    unfold MarginalProbLeft MeasureProb
    rw [Finset.sum_product, Finset.sum_singleton]
  rw [hprob, Finset.sum_congr rfl fun z _ => hborn z]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  by_cases hqy : q ∣ y.val
  · rw [show (∑ z : R, if z ∈ Finset.univ.image f then
            (if q ∣ y.val then ((r : ℝ))⁻¹ ^ 2 else 0) else 0)
        = ∑ z : R, if z ∈ Finset.univ.image f then ((r : ℝ))⁻¹ ^ 2 else 0 from
      Finset.sum_congr rfl fun z _ => by rw [ite_eq_left hqy]]
    rw [ite_eq_left hqy, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, card_image_of_exact_collision N hN f hr hrdvd hcol, sq]
    calc (r : ℝ) * ((r : ℝ)⁻¹ * (r : ℝ)⁻¹) = (r * (r : ℝ)⁻¹) * (r : ℝ)⁻¹ := by ring
      _ = (r : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hrR, one_mul]
      _ = 1 / (r : ℝ) := (one_div (r : ℝ)).symm
  · rw [show (∑ z : R, if z ∈ Finset.univ.image f then
            (if q ∣ y.val then ((r : ℝ))⁻¹ ^ 2 else 0) else 0) = (0 : ℝ) from
      Finset.sum_eq_zero fun z _ => by rw [ite_eq_right hqy]; split_ifs <;> rfl]
    rw [ite_eq_right hqy]

end Qatlib.Concepts.HspRecovery.CyclicRecovery
