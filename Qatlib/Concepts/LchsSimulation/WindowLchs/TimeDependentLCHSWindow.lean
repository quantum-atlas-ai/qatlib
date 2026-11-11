/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSConsumers
import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticLCHSConsumers

/-!
# Time-dependent LCHS windows and conditional outputs

`timeDependentLchsWindowCutoff` and `timeDependentLchsWindowNodes` choose a finite quadrature
with positive coefficient mass at most two and error at most `ε`. The compiled circuit then has
conditional density error at most `4 * ε / τ`, weighted window success at least `1 / 8`, and
explicit input and selection access counts under the output norm hypotheses.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `time_dependent_lchs_window_schedule_quadrature`: proves the computed quadrature guarantees.
* `time_dependent_lchs_window_actual_conditional_output`: bounds conditional density error.
* `time_dependent_lchs_window_success`: proves the finite-window success lower bound.
* `time_dependent_lchs_window_actual_access_ledger`: records the compiled circuit access counts.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.WindowLchs
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The positive cutoff `max 1 (Nat.ceil (4 / (π * ε)))` for the time-dependent LCHS window
schedule. -/
noncomputable def timeDependentLchsWindowCutoff (ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (4/(Real.pi*ε)))

/-- The positive node count obtained by rounding the maximum of `4 * K` and `4 * K * Λ / ε`
upward, where `K` is the prescribed window cutoff. -/
noncomputable def timeDependentLchsWindowNodes (ε Λ : ℝ) : ℕ :=
  max 1 (Nat.ceil (max (4*(timeDependentLchsWindowCutoff ε : ℝ))
    (4*(timeDependentLchsWindowCutoff ε : ℝ)*Λ/ε)))

/-- For positive `ε` and `Λ` bounding `2 / π + ∫ u in s..t, ‖L u‖`, the computed schedule has
positive cutoff and node count, grid width at most `1 / 2`, coefficient mass in `(0, 2]`,
and quadrature error at most `ε` [AnLiuLin2023]. -/
theorem time_dependent_lchs_window_schedule_quadrature :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t ε Λ : ℝ), Continuous L → Continuous H →
    (∀ u : ℝ, (L u).PosSemidef) → (∀ u : ℝ, (H u).IsHermitian) → s ≤ t →
    0 < ε → 2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    let K := timeDependentLchsWindowCutoff ε
    let N := timeDependentLchsWindowNodes ε Λ
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => orderedEvolution
      (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
    0 < K ∧ 0 < N ∧ 2*(K : ℝ)/(N : ℝ) ≤ 1/2 ∧
      0 < coefficientMass c ∧ coefficientMass c ≤ 2 ∧
      ‖(∑ j : Fin N, c j • V j) -
        orderedEvolution (fun u => L u+Complex.I • H u) s t‖ ≤ ε := by
  intro I _ _ L H s t ε Λ hL hH hPSD hHerm hst hε hΛ
  (try dsimp only)
  let K := timeDependentLchsWindowCutoff ε
  let N := timeDependentLchsWindowNodes ε Λ
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcut : 4/(Real.pi*ε) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (4/(Real.pi*ε)))))
  have hnodes : max (4*(K : ℝ)) (4*(K : ℝ)*Λ/ε) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hnceil : Nat.ceil (max (4*(K : ℝ)) (4*(K : ℝ)*Λ/ε)) ≤ N :=
        le_max_right _ _
      exact_mod_cast hnceil)
  have hmesh : 2*(K : ℝ)/(N : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hNr).mpr
    have := (le_max_left _ _).trans hnodes
    linarith
  have htail : 2/(Real.pi*(K : ℝ)) ≤ ε/2 := by
    apply (div_le_iff₀ (mul_pos Real.pi_pos hKr)).mpr
    have := (div_le_iff₀ (mul_pos Real.pi_pos hε)).mp hcut
    nlinarith
  have hcell : (2*(K : ℝ)/(N : ℝ))*Λ ≤ ε/2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hNr).mpr
    have := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hnodes)
    nlinarith
  refine ⟨hK, hN, hmesh, static_lchs_coefficient_mass_pos K N hK hN,
    static_lchs_grid_coefficient_mass_le_two K N hN hmesh, ?_⟩
  calc
    _ ≤ 2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/(N : ℝ))*
        (2/Real.pi + (∫ u in s..t, ‖L u‖)) :=
      time_dependent_lchs_quadrature_error I L H s t K N hL hH hPSD hHerm hst hK hN
    _ ≤ 2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/(N : ℝ))*Λ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hΛ
        (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKr.le) hNr.le))
    _ ≤ ε := by linarith

/-- Each time-dependent LCHS window node gives a unitary ordered Hamiltonian propagator under
the continuity and Hermiticity hypotheses. -/
private theorem tdLchsWindow_unitary (I : Type) [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N : ℕ)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (j : Fin N) :
    orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t ∈
      unitaryGroup I ℂ :=
  ordered_evolution_hermitian_unitary I (fun u => H u+staticLchsGrid K N j • L u)
    (by fun_prop)
    (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) s t

/-- If the target output norm is at least `τ` and `ε ≤ τ / 2`, every positive-success compiled
window output has normalized density trace norm error at most `4 * ε / τ` [AnLiuLin2023]. -/
theorem time_dependent_lchs_window_actual_conditional_output :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t ε τ Λ : ℝ) (B : Matrix I I ℂ) (i₀ : I),
    Continuous L → Continuous H → (∀ u : ℝ, (L u).PosSemidef) →
    (∀ u : ℝ, (H u).IsHermitian) → s ≤ t → B ∈ Matrix.unitaryGroup I ℂ →
    0 < ε → 0 < τ → ε ≤ τ/2 → 2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    τ ≤ ‖toEuclidean_fromVec
      (orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ (B *ᵥ Ket i₀))‖ →
    let K := timeDependentLchsWindowCutoff ε
    let N := timeDependentLchsWindowNodes ε Λ
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => orderedEvolution
      (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
    ∀ (j₀ : Fin N) (k : ℕ),
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    let y := Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ k) (Ket (j₀,i₀))
    0 < MeasureProb y S →
    Matrix.traceNorm (staticLchsOutputDensity (staticLchsDataBranch j₀ y) -
      staticLchsOutputDensity
        (orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ (B *ᵥ Ket i₀))) ≤
        4*ε/τ := by
  intro I _ _ L H s t ε τ Λ B i₀ hL hH hPSD hHerm hst hB hε hτ hετ hΛ hτv
  (try dsimp only)
  let K := timeDependentLchsWindowCutoff ε
  let N := timeDependentLchsWindowNodes ε Λ
  let c := staticLchsCoeff K N
  let V := fun j : Fin N => orderedEvolution
    (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
  have hs := time_dependent_lchs_window_schedule_quadrature I L H s t ε Λ
    hL hH hPSD hHerm hst hε hΛ
  intro j₀ k
  exact (static_lchs_actual_output_and_window_of_operator_error I N c V B
    (orderedEvolution (fun u => L u+Complex.I • H u) s t) j₀ i₀ ε τ
    hs.2.2.2.1 (tdLchsWindow_unitary I L H s t K N hL hH hPSD hHerm)
    hB hε hτ hετ hτv hs.2.2.2.2.2).1 k

/-- Under the window approximation hypotheses, the nonnegative iteration weights sum to one, the
window has size at most `2 * α / τ + 1`, and weighted success is at least `1 / 8`
[AnLiuLin2023]. -/
theorem time_dependent_lchs_window_success :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t ε τ Λ : ℝ) (B : Matrix I I ℂ) (i₀ : I),
    Continuous L → Continuous H → (∀ u : ℝ, (L u).PosSemidef) →
    (∀ u : ℝ, (H u).IsHermitian) → s ≤ t → B ∈ Matrix.unitaryGroup I ℂ →
    0 < ε → 0 < τ → ε ≤ τ/2 → 2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    τ ≤ ‖toEuclidean_fromVec
      (orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ (B *ᵥ Ket i₀))‖ →
    let K := timeDependentLchsWindowCutoff ε
    let N := timeDependentLchsWindowNodes ε Λ
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => orderedEvolution
      (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
    let α := coefficientMass c
    let m := staticLchsWindow α τ
    (∀ j : Fin m, 0 ≤ staticLchsIterationWeight m j) ∧
      (∑ j : Fin m, staticLchsIterationWeight m j) = 1 ∧
      (m : ℝ) ≤ 2*α/τ+1 ∧
      ∀ j₀ : Fin N,
      let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
      (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
        MeasureProb (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ j.val)
          (Ket (j₀,i₀))) S := by
  intro I _ _ L H s t ε τ Λ B i₀ hL hH hPSD hHerm hst hB hε hτ hετ hΛ hτv
  (try dsimp only)
  let K := timeDependentLchsWindowCutoff ε
  let N := timeDependentLchsWindowNodes ε Λ
  let c := staticLchsCoeff K N
  let V := fun j : Fin N => orderedEvolution
    (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
  have hs := time_dependent_lchs_window_schedule_quadrature I L H s t ε Λ
    hL hH hPSD hHerm hst hε hΛ
  obtain ⟨hm, hmb⟩ := static_lchs_window_bound (coefficientMass c) τ hs.2.2.2.1 hτ
  have hw := static_lchs_iteration_weight_distribution _ hm
  refine ⟨hw.1, hw.2, hmb, ?_⟩
  intro j₀
  exact (static_lchs_actual_output_and_window_of_operator_error I N c V B
    (orderedEvolution (fun u => L u+Complex.I • H u) s t) j₀ i₀ ε τ
    hs.2.2.2.1 (tdLchsWindow_unitary I L H s t K N hL hH hPSD hHerm)
    hB hε hτ hετ hτv hs.2.2.2.2.2).2

/-- The time-dependent compiled circuit is unitary with exact query, forward and backward input,
selection, and word-length counts; every window index uses at most `2 * m + 1` input
accesses and selection accesses [AnLiuLin2023]. -/
theorem time_dependent_lchs_window_actual_access_ledger :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t ε τ Λ : ℝ) (B : Matrix I I ℂ) (i₀ : I),
    Continuous L → Continuous H → (∀ u : ℝ, (L u).PosSemidef) →
    (∀ u : ℝ, (H u).IsHermitian) → s ≤ t → B ∈ Matrix.unitaryGroup I ℂ →
    0 < ε → 0 < τ → ε ≤ τ/2 → 2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    τ ≤ ‖toEuclidean_fromVec
      (orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ (B *ᵥ Ket i₀))‖ →
    let K := timeDependentLchsWindowCutoff ε
    let N := timeDependentLchsWindowNodes ε Λ
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => orderedEvolution
      (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
    let α := coefficientMass c
    let m := staticLchsWindow α τ
    ∀ j₀ : Fin N,
    (∀ k : ℕ,
      IsUnitaryCircuit (staticLchsCompile c V B j₀ i₀ k) ∧
      QueryCount (staticLchsCompile c V B j₀ i₀ k) = k ∧
      (staticLchsWord k).count .inputF = k+1 ∧
      (staticLchsWord k).count .inputB = k ∧
      (staticLchsWord k).count .selectF = k+1 ∧
      (staticLchsWord k).count .selectB = k ∧
      (staticLchsWord k).length = 10*k+4) ∧
    (∀ j : Fin m,
      (staticLchsWord j.val).count .inputF + (staticLchsWord j.val).count .inputB ≤
        2*m+1 ∧
      (staticLchsWord j.val).count .selectF + (staticLchsWord j.val).count .selectB ≤
        2*m+1) := by
  intro I _ _ L H s t ε τ Λ B i₀ hL hH hPSD hHerm hst hB hε _hτ _hετ hΛ _hτv
  (try dsimp only)
  let K := timeDependentLchsWindowCutoff ε
  let N := timeDependentLchsWindowNodes ε Λ
  let c := staticLchsCoeff K N
  let V := fun j : Fin N => orderedEvolution
    (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
  have hs := time_dependent_lchs_window_schedule_quadrature I L H s t ε Λ
    hL hH hPSD hHerm hst hε hΛ
  intro j₀
  constructor
  · intro k
    have h := time_dependent_lchs_actual_prepared_output I L H s t K N k B i₀ j₀
      hL hH hPSD hHerm hst hs.1 hs.2.1 hB
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  · exact static_lchs_window_actual_access_budget I N c V B j₀ i₀ hs.2.2.2.1
      (tdLchsWindow_unitary I L H s t K N hL hH hPSD hHerm) hB _

end Qatlib.Concepts.LchsSimulation.WindowLchs
