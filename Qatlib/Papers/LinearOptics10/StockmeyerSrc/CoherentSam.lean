/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs

@[expose] public section


/-! # The exact historical coherent-sampler and isometry-law predicates

Fixed arXiv:1011.3245v1. These predicates are preserved for source audit.
The finite seed sampler does not encode coherent preparations, cost, or
postselection. The old density predicate has no mass-one requirement;
its support on the column-isometry manifold is retained explicitly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexConjugate
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.CoherentSam
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Concepts.BosonFock.BosonOperators

/-- An oracle that takes a random string `r` and `n`, and outputs a sample from a
distribution `D_n` over `Φ_{2n,n}` (Theorem 34(ii)). -/
structure SamplingOracle where
  /-- Oracle output: `n`, the random bit budget `L`, and the seed. -/
  out : (n : ℕ) → (L : ℕ) → (Fin L → Bool) → FockOccupation (2 * n) n

/-- A distribution family over `Φ_{2n,n}` is coherent-state samplable: for every
`n` a boson computer with coherent-state inputs samples it in poly time
(Theorem 34(i); the polynomial time bound is not modelled, only the sampler). -/
def CoherentLaw (D : (n : ℕ) → FockOccupation (2 * n) n → ℝ) : Prop :=
  ∀ n, ∃ Sam : LoSampler (2 * n) n, ∀ S, loSamplerDist Sam S = D n S

/-- `O` samples the family `D`: for every `n` some seed length realises `D_n`
exactly on the uniform seed distribution (Theorem 34(ii)). -/
def SamplesFamily (D : (n : ℕ) → FockOccupation (2 * n) n → ℝ)
    (O : SamplingOracle) : Prop :=
  ∀ n, ∃ L : ℕ, ∀ S : FockOccupation (2 * n) n,
    (∑ r : (Fin L → Bool), if O.out n L r = S then (1 : ℝ) else 0) /
      ((2 : ℕ) ^ L : ℝ) = D n S


/-- The historical real density predicate records nonnegativity, positive support
on column isometries, and left unitary invariance. It has no mass-one condition
and is not asserted to construct an actual Haar probability law. -/
def HaarIsometryLaw (m n : ℕ) (μ : (Fin m → Fin n → ℂ) → ℝ) : Prop :=
  (∀ A, 0 ≤ μ A) ∧
  (∀ A, 0 < μ A → (Matrix.of A)ᴴ * Matrix.of A = 1) ∧
  (∀ U : Matrix (Fin m) (Fin m) ℂ, U ∈ Matrix.unitaryGroup (Fin m) ℂ →
    ∀ A, μ (fun i j => ∑ k, U i k * A k j) = μ A)


/-- The old isometry-law predicate even admits the zero density, since normalization is absent. -/
theorem zeroLaw (m n : ℕ) : HaarIsometryLaw m n (fun _ => 0) := by
  simp [HaarIsometryLaw]

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.CoherentSam
