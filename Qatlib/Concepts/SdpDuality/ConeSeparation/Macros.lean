/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def sdpDualPayoff (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (α : ℝ)
    (y : ℕ → Fin m → ℝ) : ℕ → Operator D :=
  fun s => ((4*α : ℝ))⁻¹ • ((∑ i, y s i • A i) - Cv + (2*α) • (1 : Operator D))

def sdpDualCertificate (m : ℕ) (δ α R : ℝ) (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) :
    Fin m → ℝ :=
  fun j => (if j = j₀ then δ*α/(2*R) else 0) + (∑ t ∈ Finset.range T, y t j)/T

def sdpDualCertRounds (D : ℕ) (R δ η : ℝ) : ℕ :=
  Nat.ceil (16*R*Real.log D/(δ*η)) + 1

end Qatlib.Concepts.SdpDuality.ConeSeparation
