/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliFamily
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentBridge

@[expose] public section


/-! The original complete Pauli family normalized by one over the square root of 3n.
The scalar-commutant proof removes a genuinely nonzero normalization only when n is positive. -/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix

namespace Qatlib.Concepts.GibbsSource.SourceForms

noncomputable def localPauliScale (n : ℕ) : ℂ :=
  ((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ)

/-- The original `3n` normalized proposals, with the normalization inside every component. -/
noncomputable def normalizedLocalPauli (n : ℕ) (p : Fin n × Fin 3) :
    Operator (fullPauliDim n) :=
  localPauliScale n • fullPauliFamily n p

/-- Card local Pauli Labels for the stated finite source data. -/
theorem card_localPauliLabels (n : ℕ) : Fintype.card (Fin n × Fin 3) = 3 * n := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

/-- Local Pauli Scale ne zero for the stated finite source data. -/
theorem localPauliScale_ne_zero {n : ℕ} (hn : 0 < n) : localPauliScale n ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply inv_ne_zero
  exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hn)))

/-- The complete normalized family has exactly the scalar common commutant.
Only X and Z are needed; Y remains part of the source family. -/
theorem normalizedLocalPauli_commutant_scalar {n : ℕ} (hn : 0 < n)
    (Z : Operator (fullPauliDim n))
    (hcomm : ∀ p, Z * normalizedLocalPauli n p = normalizedLocalPauli n p * Z) :
    ∃ c : ℂ, Z = c • (1 : Operator (fullPauliDim n)) := by
  have hs := localPauliScale_ne_zero hn
  apply fullPauliFamily_commutant_scalar n Z
  intro p
  have h : localPauliScale n • (Z * fullPauliFamily n p) =
      localPauliScale n • (fullPauliFamily n p * Z) := by
    simpa only [normalizedLocalPauli, Matrix.mul_smul, Matrix.smul_mul] using hcomm p
  have h' := congrArg (fun M : Operator (fullPauliDim n) => (localPauliScale n)⁻¹ • M) h
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using h'


end Qatlib.Concepts.GibbsSource.SourceForms
