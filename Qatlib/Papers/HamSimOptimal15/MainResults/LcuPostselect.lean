/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation

set_option backward.isDefEq.respectTransparency false

/-!
# LcuPostselect — Lemmas 4, 5 and 6 of arXiv:1501.01715v3

Paper: Berry–Childs–Kothari, *Hamiltonian simulation with nearly optimal
dependence on all parameters*, arXiv:1501.01715v3 (2015-12-07).

* Lemma 4 (LCU Lemma), p.6: for `Ṽ = ∑_m a_m U_m` that is `δ`-close to a unitary,
  approximate `Ṽ` to within `O(δ)` using `O(a)` select operations and `O(M a)`
  additional two-qubit gates, `a = ∑_m |a_m|`.
* Lemma 5, p.6: there is a unitary `W` on `H₁ ⊗ H₂` with `Z = P W P = (1/s)(|ς⟩⟨ς| ⊗ Ṽ)`,
  `P = |ς⟩⟨ς| ⊗ I`, applied with `O(1)` select and `O(M)` additional gates.
* Lemma 6 (robust oblivious amplitude amplification), p.6, eq.(18): with
  `sin(π/(2(2ℓ+1))) = 1/s` and `R = −W(I−2P)W†(I−2P)`,
  `‖P R^ℓ W P − (|ς⟩⟨ς| ⊗ Ṽ)‖ = O(δ)`.

The repository's LCU infrastructure realises Lemma 5 and the *correctness* half of
Lemma 4 exactly: `coefficientLCUUnitary` is the PREPARE / SELECT / PREPARE† unitary,
its compression in the tagged frames is the `1/s`-normalised linear combination
(`scaled_lcu_coefficient_mass`), and `scaled_approximate_lcu_encoding` accumulates the
per-term block-encoding errors.  The oblivious amplification is available at
`ℓ = 1`, `s = 2` as `coherent_oaa_compressed_error` (the cubic response), which is the
case used by the paper's main algorithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.HamSimOptimal15.MainResults

variable {J H O I : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- **Lemma 4 (LCU Lemma), arXiv:1501.01715v3 p.6**: a family of block encodings
`(A_j, U_j)` with subnormalisation `α_j` and error `ε_j` yields a block encoding of the
linear combination `∑_j c_j • A_j` by the single LCU unitary, with subnormalisation
`∑_j ‖c_j‖ α_j` and accumulated error `∑_j ‖c_j‖ ε_j` (the paper's `O(δ)` with
`δ := ∑_j ‖c_j‖ ε_j`, weighted by `a := ∑_j ‖c_j‖ α_j`).

This is the correctness/approximation half of the LCU Lemma; it is the repository's
`scaled_approximate_lcu_encoding` with the heterogeneous scales absorbed into the
coefficients (`scaledLCUCoefficients`).  The resource half of the paper's statement —
`O(a)` select operations and `O(M a)` additional gates after `ℓ`-fold amplification —
is not formalised here (see the PR notes). -/
theorem lemma4_lcu_lemma (j₀ : J) (A : J → Matrix O I ℂ) (U : J → Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (c : J → ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (A j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α)) :
    BlockEncoding (∑ j, c j • A j)
      (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀)
      (tagFrame j₀ L) (tagFrame j₀ R)
      (∑ j, ‖c j‖ * α j) (∑ j, ‖c j‖ * ε j) :=
  scaled_approximate_lcu_encoding j₀ A U L R c α ε henc hmass

/-- **Lemma 5, compression form, arXiv:1501.01715v3 p.6**: the LCU unitary
`coefficientLCUUnitary d U j₀` (the PREPARE / SELECT / PREPARE† word) compresses in the
tagged frames exactly to the `1/s`-normalised linear combination,
`compress (tagFrame L) W (tagFrame R) = ∑_j (d_j / s) • compress L (U_j) R`
with `s = coefficientMass d = ∑_j ‖d_j‖`.  With `Ṽ := ∑_j d_j • U_j` and `a_j := d_j`
this is the paper's `Z = P W P = (1/s)(|ς⟩⟨ς| ⊗ Ṽ)` (the frame `tagFrame j₀ ·` plays the
role of `|ς⟩`). -/
theorem lemma5_lcu_postselect_compression (j₀ : J) (U : J → Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (c : J → ℂ) (α : J → ℝ)
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α)) :
    compress (tagFrame j₀ L)
        (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀)
        (tagFrame j₀ R)
      = ∑ j, (scaledLCUCoefficients c α j / (coefficientMass (scaledLCUCoefficients c α) : ℂ))
          • (compress L (U j) R) := by
  set d := scaledLCUCoefficients c α
  rw [compress_tagFrame, coefficientLCUUnitary_compress d U j₀ hmass]
  calc Lᴴ * (∑ j, (d j / (coefficientMass d : ℂ)) • U j) * R
      = (∑ j, Lᴴ * ((d j / (coefficientMass d : ℂ)) • U j)) * R := by rw [Matrix.mul_sum]
    _ = ∑ j, Lᴴ * ((d j / (coefficientMass d : ℂ)) • U j) * R := Matrix.sum_mul _ _ _
    _ = ∑ j, (d j / (coefficientMass d : ℂ)) • (Lᴴ * U j * R) :=
        Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **Lemma 5, existence and unitarity, arXiv:1501.01715v3 p.6**: for unitary `U_j` and
positive LCU mass the word `coefficientLCUUnitary d U j₀` is a genuine unitary on the
workspace, whose compressed action is the normalised linear combination of the previous
theorem.  This exhibits the paper's `W` together with `Z = P W P`. -/
theorem lemma5_lcu_postselect_unitary (j₀ : J) (U : J → Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (c : J → ℂ) (α : J → ℝ)
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α))
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup H ℂ) :
    coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀
        ∈ Matrix.unitaryGroup (J × H) ℂ ∧
      compress (tagFrame j₀ L)
          (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀)
          (tagFrame j₀ R)
        = ∑ j, (scaledLCUCoefficients c α j / (coefficientMass (scaledLCUCoefficients c α) : ℂ))
            • (compress L (U j) R) :=
  ⟨coefficientLCUUnitary_unitary _ U j₀ hmass hU,
    lemma5_lcu_postselect_compression j₀ U L R c α hmass⟩

/-- **Lemma 5, circuit cost, arXiv:1501.01715v3 p.6**: the paper's `W` is realised by
the two-macro-gate, one-query circuit `PREPARE / SELECT / PREPARE†`; the SELECT part is
the single supplied query oracle and PREPARE is a register preparation costing `O(M)`
additional gates.  This records the `O(1)` select / `O(M)` gate accounting at the
circuit level (`QueryCount = 1`, `GateCount = 2` for the two preparation macros). -/
theorem lemma5_lcu_postselect_circuit (j₀ : J) (d : J → ℂ) (U : J → Matrix I I ℂ)
    (ψ : QState (J × I)) :
    QueryCount (scaledLCUCircuit (I := I) d j₀) = 1 ∧
      GateCount (scaledLCUCircuit (I := I) d j₀) = 2 :=
  ⟨(scaled_lcu_run_and_cost j₀ d U ψ).2.1, (scaled_lcu_run_and_cost j₀ d U ψ).2.2.1⟩

/-- **Lemma 6, one-step instance (`ℓ = 1`, `s = 2`), arXiv:1501.01715v3 p.6 eq.(18)**:
around a `(2, ε)` block encoding of a unitary `V`, one application of the cubic robust
amplification word produces a unitary whose compression is within the explicit
`coherentOAAError ε = 3ε + (3/2)ε² + (1/2)ε³` of `V` — the paper's `O(δ)` with the
constant made explicit for `sin(π/(2·3)) = 1/2`.

This is the repository's `coherent_oaa_compressed_error` with the error polynomial
expanded. -/
theorem lemma6_robust_oaa_one_step (V : Matrix I I ℂ) (U : Matrix H H ℂ)
    (W : Matrix H I ℂ) (ε : ℝ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : BlockEncoding V U W W 2 ε) :
    ‖compress W (coherentOAAOperator U W) W - V‖ ≤
      3 * ε + (3 / 2) * ε ^ 2 + (1 / 2) * ε ^ 3 := by
  calc ‖compress W (coherentOAAOperator U W) W - V‖ ≤ coherentOAAError ε :=
        (coherent_oaa_compressed_error V U W ε hV h).2
    _ = 3 * ε + (3 / 2) * ε ^ 2 + (1 / 2) * ε ^ 3 := by
        unfold coherentOAAError; ring

/-- **Lemma 6, general `ℓ`, arXiv:1501.01715v3 p.6 eq.(18)**: for every `ℓ ≥ 1` there is
a constant `C > 0` (depending only on `ℓ`) such that for every unitary `V`, every
`(2, ε)` block encoding `(U, W)` of `V` with `ε < 1`, the `ℓ`-fold amplified word is a
unitary whose compression approximates `V` to within `C ε`.  This is the paper's
`‖P R^ℓ W P − (|ς⟩⟨ς| ⊗ Ṽ)‖ = O(δ)` with the `O(δ)` constant depending only on `ℓ`
(Cebyshev expansion of eq.(21), evaluated at eq.(37)).

Registered as a proposition, not proved: the repository only contains the `ℓ = 1`
cubic instance (`coherentOAAOperator`, `coherentOAAWord`,
`coherent_oaa_word_correct`), so the `ℓ`-fold composition `R^ℓ` with Chebyshev
polynomials `T_{2ℓ+1}` of eq.(21) has no Lean counterpart yet.  See the PR notes for
the suggested follow-up. -/
def lemma6_robust_oaa_general (ℓ : ℕ) : Prop :=
  0 < ℓ → ∃ C : ℝ, 0 < C ∧ ∀ {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
      [DecidableEq I] (V : Matrix I I ℂ) (U : Matrix H H ℂ) (W : Matrix H I ℂ) (ε : ℝ),
      ε < 1 → V ∈ Matrix.unitaryGroup I ℂ → BlockEncoding V U W W 2 ε →
      ∃ Aℓ : Matrix H H ℂ, Aℓ ∈ Matrix.unitaryGroup H ℂ ∧
        ‖compress W Aℓ W - V‖ ≤ C * ε

end Qatlib.Papers.HamSimOptimal15.MainResults
