/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.DecoderCapacity

def correctErrors {E S : Type*} [DecidableEq E]
    (syndrome : E → S) (decode : S → E) (errors : Finset E) : Finset E :=
  errors.filter (fun e => decode (syndrome e) = e)

def KernelSeparated {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq K]
    (syndrome : (ι → K) →ₗ[K] (κ → K)) (radius : ℕ) : Prop :=
  ∀ z, syndrome z = 0 → z ≠ 0 → 2 * radius < hammingNorm z

end Qatlib.Concepts.CodingDecoding.DecoderCapacity
