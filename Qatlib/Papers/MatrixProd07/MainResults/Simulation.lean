/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs

/-!
# Polynomial matrix product evaluation costs

`evalOpCount_poly` transports a polynomial bond dimension bound to the matrix product evaluation
cost. `PolyMpsCost` combines representations with a polynomial cost bound, and the two
simulation theorems package this bound with optional polynomial circuit length. These
constructions are associated with [PerezGarciaEtAl2007].

## Main statements

* `theorem18_mbqc_simulation`: polynomial evaluation cost for a polynomial bond bound.
* `theorem19_circuit_simulation`: polynomial aggregate cost with a polynomial step count.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.Simulation

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

/-- The space of complex amplitude functions on configurations of `N` sites of local dimension
`d`. -/
abbrev Ket (N d : ℕ) := (Fin N → Fin d) → ℂ

/-- A polynomial bound on bond dimensions gives a polynomial bound on `mpsEvalOpCount N (D N)`.
See [PerezGarciaEtAl2007]. -/
theorem evalOpCount_poly (D : ℕ → ℕ) (hD : PolyBudget D) :
    PolyBudget (fun N => mpsEvalOpCount N (D N)) := by
  obtain ⟨C, k, hC⟩ := hD
  refine ⟨2 * C * C + C, 2 * k + 1, fun N => ?_⟩
  have hDN : D N ≤ C * (N + 1) ^ k := hC N
  have hbase : 1 ≤ N + 1 := by omega
  have hpow : (N + 1) ^ k * (N + 1) ^ k = (N + 1) ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : N * ((N + 1) ^ k * (N + 1) ^ k) ≤ (N + 1) ^ (2 * k + 1) := by
    rw [hpow, pow_succ]
    calc N * (N + 1) ^ (2 * k) ≤ (N + 1) * (N + 1) ^ (2 * k) :=
          Nat.mul_le_mul_right _ (Nat.le_succ N)
      _ = (N + 1) ^ (2 * k) * (N + 1) := Nat.mul_comm _ _
  have h2 : (N + 1) ^ k ≤ (N + 1) ^ (2 * k + 1) :=
    pow_le_pow_right' hbase (by omega)
  show N * (2 * D N * D N) + D N ≤ (2 * C * C + C) * (N + 1) ^ (2 * k + 1)
  have hmain1 : N * (2 * D N * D N) ≤ 2 * C * C * (N + 1) ^ (2 * k + 1) := by
    have hstep : N * (2 * D N * D N) ≤ N * (2 * (C * (N + 1) ^ k) * (C * (N + 1) ^ k)) := by
      gcongr
    refine hstep.trans ?_
    rw [show N * (2 * (C * (N + 1) ^ k) * (C * (N + 1) ^ k))
          = 2 * C * C * (N * ((N + 1) ^ k * (N + 1) ^ k)) by ring]
    exact Nat.mul_le_mul_left _ h1
  calc N * (2 * D N * D N) + D N
      ≤ 2 * C * C * (N + 1) ^ (2 * k + 1) + C * (N + 1) ^ (2 * k + 1) :=
        Nat.add_le_add hmain1 (hDN.trans (Nat.mul_le_mul_left C h2))
    _ = (2 * C * C + C) * (N + 1) ^ (2 * k + 1) := by ring

/-- The predicate that a family has matrix product representations with dimensions `D N` and
polynomially bounded evaluation operation counts. -/
def PolyMpsCost {d : ℕ} (D : ℕ → ℕ) (ψ : (N : ℕ) → Ket N d) : Prop :=
  ∃ (hD : ∀ N, NeZero (D N)) (A : (N : ℕ) → Fin N → Fin d → BM (D N)),
    (∀ N, @IsMpsRepresentation N d (D N) (hD N) (A N) (ψ N)) ∧
    PolyBudget (fun N => mpsEvalOpCount N (D N))

/-- If each state has a matrix product representation with polynomially bounded bond dimension
`D`, then the family satisfies `PolyMpsCost D ψ`. See [PerezGarciaEtAl2007]. -/
theorem theorem18_mbqc_simulation {d : ℕ} (D : ℕ → ℕ) (ψ : (N : ℕ) → Ket N d)
    (hMPS : ∀ N, ∃ (hD : NeZero (D N)) (A : Fin N → Fin d → BM (D N)),
      @IsMpsRepresentation N d (D N) hD A (ψ N))
    (hD : PolyBudget D) :
    PolyMpsCost D ψ := by
  classical
  refine ⟨fun N => (hMPS N).choose, fun N => (hMPS N).choose_spec.choose, ?_,
    evalOpCount_poly D hD⟩
  intro N
  exact (hMPS N).choose_spec.choose_spec

/-- If both the circuit step count `T` and the representing bond dimension `D` have polynomial
bounds, then `T N * (mpsEvalOpCount N (D N) + 1)` has a polynomial bound and the state
family satisfies `PolyMpsCost`. See [PerezGarciaEtAl2007]. -/
theorem theorem19_circuit_simulation {d : ℕ} (T D : ℕ → ℕ) (ψ : (N : ℕ) → Ket N d)
    (hT : PolyBudget T)
    (hMPS : ∀ N, ∃ (hD : NeZero (D N)) (A : Fin N → Fin d → BM (D N)),
      @IsMpsRepresentation N d (D N) hD A (ψ N))
    (hD : PolyBudget D) :
    (∃ cost : ℕ → ℕ, PolyBudget cost ∧
        ∀ N, cost N = T N * (mpsEvalOpCount N (D N) + 1)) ∧
      PolyMpsCost D ψ := by
  classical
  refine ⟨⟨fun N => T N * (mpsEvalOpCount N (D N) + 1), ?_, fun N => rfl⟩,
    theorem18_mbqc_simulation D ψ hMPS hD⟩
  obtain ⟨C₁, k₁, hT⟩ := hT
  obtain ⟨C₂, k₂, hD⟩ := hD
  obtain ⟨C₃, k₃, hE⟩ := evalOpCount_poly D ⟨C₂, k₂, hD⟩
  refine ⟨C₁ * (C₃ + 1), k₁ + k₃, fun N => ?_⟩
  have hT' : T N ≤ C₁ * (N + 1) ^ k₁ := hT N
  have hE' : mpsEvalOpCount N (D N) ≤ C₃ * (N + 1) ^ k₃ := hE N
  have hbase : 1 ≤ N + 1 := by omega
  have hpow : (N + 1) ^ k₁ * (N + 1) ^ k₃ = (N + 1) ^ (k₁ + k₃) := by
    rw [pow_add]
  have h1 : mpsEvalOpCount N (D N) + 1 ≤ (C₃ + 1) * (N + 1) ^ k₃ := by
    have : (1 : ℕ) ≤ (N + 1) ^ k₃ := Nat.one_le_pow _ _ hbase
    calc mpsEvalOpCount N (D N) + 1 ≤ C₃ * (N + 1) ^ k₃ + (N + 1) ^ k₃ := by omega
      _ = (C₃ + 1) * (N + 1) ^ k₃ := by ring
  calc T N * (mpsEvalOpCount N (D N) + 1)
      ≤ (C₁ * (N + 1) ^ k₁) * ((C₃ + 1) * (N + 1) ^ k₃) :=
        Nat.mul_le_mul hT' h1
    _ = C₁ * (C₃ + 1) * ((N + 1) ^ k₁ * (N + 1) ^ k₃) := by ring
    _ = C₁ * (C₃ + 1) * (N + 1) ^ (k₁ + k₃) := by rw [hpow]

end Qatlib.Papers.MatrixProd07.MainResults.Simulation
