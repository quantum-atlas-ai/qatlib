/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Concepts.LchsSimulation.TimeLchs
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11: a scaled block encoding of the time-ordered propagator

The paper's Lemma 11 (`arXiv:2303.01029v2`, supplementary Eq. (S44)) builds an
`(‖c‖₁, log M, ε)`-block-encoding of `T exp(-∫₀ᵀ A)` from the Cauchy-weighted
family of quadrature unitaries `T exp(-∫ᵢ(H + k_j L))`.

This file reduces that statement to already frozen infrastructure:

* the LCU preparation/select circuit of `EncodingCore.coefficientLCUUnitary`
  compresses to `∑ j, c_j • U_j` with subnormalization `∑ j, ‖c_j‖`
  (`coefficientLCUUnitary_blockEncoding`), and
* the Cauchy left-grid quadrature error of the noncommuting propagator is
  `2/(πK) + (2K/N)(2/π + ∫‖L‖)` (`time_dependent_lchs_quadrature_error`).

Composing the two with the block-encoding perturbation lemma yields the scaled
block encoding of the propagator itself. Circuit synthesis, the `O(1)` queries to
the coefficient oracle and the explicit `log M` ancilla count are not formalized
here; only the operator-level encoding and its error are.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LCHamSim23.TimeOrdered

open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The left-grid Cauchy quadrature unitaries are unitary: each is the
time-ordered propagator of the Hermitian generator `H + k L`. -/
theorem lchsQuadratureUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N : ℕ)
    (hL : Continuous L) (hH : Continuous H) (hPSD : ∀ u, (L u).PosSemidef)
    (hHerm : ∀ u, (H u).IsHermitian) (j : Fin N) :
    orderedEvolution (fun u => Complex.I • (H u + staticLchsGrid K N j • L u)) s t ∈
      Matrix.unitaryGroup I ℂ :=
  ordered_evolution_hermitian_unitary I (fun u => H u + staticLchsGrid K N j • L u)
    (hH.add (hL.const_smul (staticLchsGrid K N j)))
    (fun u => (hHerm u).add
      ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all (staticLchsGrid K N j)))) s t

/-- Lemma 11, operator form. The explicit PREPARE-adjoint / SELECT / PREPARE
circuit of the Cauchy left grid is a `(‖c‖₁, ε)`-block-encoding of the actual
time-ordered propagator `T exp(-∫₀ᵀ (L + iH))`, with the quadrature error
`ε = 2/(πK) + (2K/N)(2/π + ∫‖L‖)`. -/
theorem time_dependent_lchs_block_encoding (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N : ℕ)
    (hL : Continuous L) (hH : Continuous H) (hPSD : ∀ u, (L u).PosSemidef)
    (hHerm : ∀ u, (H u).IsHermitian) (hst : s ≤ t) (hK : 0 < K) (hN : 0 < N) :
    BlockEncoding (orderedEvolution (fun u => L u + Complex.I • H u) s t)
      (coefficientLCUUnitary (staticLchsCoeff K N)
        (fun j : Fin N => orderedEvolution
          (fun u => Complex.I • (H u + staticLchsGrid K N j • L u)) s t) ⟨0, hN⟩)
      (prepareLift (I := I) (Ket (⟨0, hN⟩ : Fin N)))
      (prepareLift (I := I) (Ket (⟨0, hN⟩ : Fin N)))
      (coefficientMass (staticLchsCoeff K N))
      (2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/(N : ℝ))*(2/Real.pi + ∫ u in s..t, ‖L u‖)) := by
  have hmass : 0 < coefficientMass (staticLchsCoeff K N) :=
    static_lchs_coefficient_mass_pos K N hK hN
  have hV : ∀ j : Fin N, orderedEvolution
      (fun u => Complex.I • (H u + staticLchsGrid K N j • L u)) s t ∈
        Matrix.unitaryGroup I ℂ :=
    fun j => lchsQuadratureUnitary L H s t K N hL hH hPSD hHerm j
  have hbase := coefficientLCUUnitary_blockEncoding (staticLchsCoeff K N)
    (fun j : Fin N => orderedEvolution
      (fun u => Complex.I • (H u + staticLchsGrid K N j • L u)) s t) ⟨0, hN⟩ hmass hV
  have hquad : ‖(∑ j : Fin N, staticLchsCoeff K N j • orderedEvolution
      (fun u => Complex.I • (H u + staticLchsGrid K N j • L u)) s t) -
      orderedEvolution (fun u => L u + Complex.I • H u) s t‖ ≤
        2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/(N : ℝ))*(2/Real.pi + ∫ u in s..t, ‖L u‖) :=
    time_dependent_lchs_quadrature_error I L H s t K N hL hH hPSD hHerm hst hK hN
  have hε : 0 ≤ 2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/(N : ℝ))*(2/Real.pi + ∫ u in s..t, ‖L u‖) := by
    have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hInt : 0 ≤ ∫ u in s..t, ‖L u‖ :=
      intervalIntegral.integral_nonneg hst (fun u _ => norm_nonneg (L u))
    have h1 : 0 ≤ 2/(Real.pi*(K : ℝ)) := by positivity
    have h2 : 0 ≤ 2*(K : ℝ)/(N : ℝ) := by positivity
    have hpi : (0 : ℝ) < 2/Real.pi := by positivity
    have h3 : 0 ≤ 2/Real.pi + ∫ u in s..t, ‖L u‖ := by linarith [hpi, hInt]
    nlinarith [mul_nonneg h2 h3]
  have hres := hbase.perturb hε (by simpa only [norm_sub_rev] using hquad)
  simpa only [zero_add] using hres

/-- The quadrature mass is uniformly bounded when the Cauchy grid is at most
`1/2`-fine, so the encoding factor in Lemma 11 is `O(1)`. -/
theorem time_dependent_lchs_block_encoding_mass_le_two (K N : ℕ) (hN : 0 < N)
    (hh : 2*(K : ℝ)/(N : ℝ) ≤ 1/2) :
    coefficientMass (staticLchsCoeff K N) ≤ 2 :=
  static_lchs_grid_coefficient_mass_le_two K N hN hh

end Qatlib.Papers.LCHamSim23.TimeOrdered
