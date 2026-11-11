/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSpectralHess24.MainResults.Core.Model

set_option backward.isDefEq.respectTransparency false

/-!
# QSpectralHess24 — oracle-conversion and derived objects

Paper: arXiv:2407.03833v2. This module extends `Core/Model` with

* the permutation-matrix implementation of a bijective basis map (used for the
  arithmetic-oracle lemma, Lemma 2.3);
* a **single-oracle** and a **two-oracle simulation certificate** for statements of
  the form "given `U` we can obtain `O` with `k` applications of `U`"
  (Propositions 2.5, 2.11, Lemma 2.14, Lemmas 3.3 and 3.5);
* concrete diagonal phase oracles for a complex-valued function and for a real
  function acting only on the input register of a product register;
* the concrete binary-value oracle used for the binary-oracle constructions;
* the gradient vector and real restriction of a complex analytic function, used to
  state the Hessian claims.

The simulation certificates quantify over one fixed unitary fixed-gate circuit and
charge only oracle queries, exactly the query-only accounting of the paper's
`O(…) applications of …` statements.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QSpectralHess24.MainResults.Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Permutation matrices implementing basis permutations -/

/-- The permutation matrix that sends the basis vector `|j⟩` to `|σ j⟩`. -/
noncomputable def basisPermMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix ι ι ℂ :=
  Equiv.Perm.permMatrix ℂ σ.symm

/-- A permutation matrix is unitary. -/
theorem basisPermMatrix_mem_unitaryGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : basisPermMatrix σ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 : basisPermMatrix σ = Matrix.permMatrixHom (R := ℂ) σ := rfl
  have h2 : star (basisPermMatrix σ) = Matrix.permMatrixHom (R := ℂ) σ⁻¹ := by
    unfold basisPermMatrix
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rfl
  rw [h2, h1, ← map_mul]
  simp

/-- The permutation matrix acts on a basis vector by the permutation. -/
theorem basisPermMatrix_mulVec_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (j : ι) :
    basisPermMatrix σ *ᵥ (Pi.single j (1 : ℂ)) = Pi.single (σ j) (1 : ℂ) := by
  rw [basisPermMatrix, Matrix.permMatrix_mulVec]
  funext i
  rw [Function.comp_apply]
  by_cases h : i = σ j
  · subst h
    rw [Equiv.symm_apply_apply]
    simp
  · have h' : σ.symm i ≠ j := fun e => h ((Equiv.symm_apply_eq σ).mp e)
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

/-! ## Oracle-simulation certificates -/

/-- The two-oracle register oracle `U₁ ⊕ U₂` on `ι ⊕ ι`, used to model access to two
phase oracles in the paper. -/
noncomputable def sumOracle {ι : Type} [Fintype ι] [DecidableEq ι]
    (U₁ U₂ : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks U₁ 0 0 U₂

/-- **Single-oracle simulation certificate.** A fixed unitary fixed-gate circuit using
`U` at most `k` times maps every computational basis state `|x⟩` to a global phase
times the target oracle `O` applied to `|x⟩`. This is the paper's "we can obtain `O`
from `U` with `k` applications of `U`" (Section 2.1). -/
noncomputable def ObtainableFromOracle {ι : Type} [Fintype ι] [DecidableEq ι]
    (U O : Matrix ι ι ℂ) (k : ℕ) : Prop :=
  ∃ (C : Circuit ι), IsUnitaryCircuit C ∧ QueryCount C ≤ k ∧
    ∀ x : ι, ∃ c : ℂ, ‖c‖ = 1 ∧
      Run U C (Ket x) = fun y => c * (O.mulVec (Ket x)) y

/-- **Two-oracle simulation certificate.** Like `ObtainableFromOracle` but with access
to two phase oracles on the two blocks of `ι ⊕ ι`; `k` bounds the total number of
oracle queries. -/
noncomputable def ObtainableFromOraclePair {ι : Type} [Fintype ι] [DecidableEq ι]
    (U₁ U₂ O : Matrix ι ι ℂ) (k : ℕ) : Prop :=
  ∃ (C : Circuit (ι ⊕ ι)), IsUnitaryCircuit C ∧ QueryCount C ≤ k ∧
    ∀ x : ι, ∃ c : ℂ, ‖c‖ = 1 ∧
      Run (sumOracle U₁ U₂) C (Ket (Sum.inl x)) =
        fun y => c * ((sumOracle O O).mulVec (Ket (Sum.inl x))) y

/-- The phase oracle `|x⟩ ↦ e^{i f(x)} |x⟩` for a complex-valued `f`; this models the
`η`-accurate binary oracle of Definition 2.1 at the level of the phase it induces. -/
noncomputable def complexPhaseOracle {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun x => Complex.exp (Complex.I * f x)

/-- The phase oracle acting only on the input coordinate of a product register. -/
noncomputable def phaseOracleOnInput {ι β : Type} [Fintype ι] [Fintype β]
    [DecidableEq ι] [DecidableEq β] (φ : ι → ℝ) : Matrix (ι × β) (ι × β) ℂ :=
  Matrix.diagonal fun p => Complex.exp (Complex.I * (φ p.1 : ℂ))

/-- The binary-value oracle of Definition 2.1 on a register of input `x : ι` together
with two `n`-bit value registers: it adds the encoded values of `g₁(x)` and `g₂(x)`
into the two value registers (a basis permutation). -/
noncomputable def binaryValueOracle {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) [NeZero (2 ^ n)] (g₁ g₂ : ι → ZMod (2 ^ n)) :
    Matrix (ι × ZMod (2 ^ n) × ZMod (2 ^ n)) (ι × ZMod (2 ^ n) × ZMod (2 ^ n)) ℂ :=
  basisPermMatrix
    { toFun := fun p => (p.1, p.2.1 + g₁ p.1, p.2.2 + g₂ p.1)
      invFun := fun p => (p.1, p.2.1 - g₁ p.1, p.2.2 - g₂ p.1)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }

/-! ## Derived objects for the estimation claims -/

/-- The real restriction `x ↦ Re f(x)` of a complex analytic `f` on `ℝ^d`. -/
noncomputable def realRestriction {d : ℕ} (f : (Fin d → ℂ) → ℂ) : (Fin d → ℝ) → ℝ :=
  fun x => (f fun i => (x i : ℂ)).re

/-- The real gradient vector `∇f(0)` of a complex analytic `f` that maps `ℝ^d` into
`ℝ`, read through the real part (Theorem 3.6). -/
noncomputable def gradientVec {d : ℕ} (f : (Fin d → ℂ) → ℂ) : Fin d → ℝ :=
  fun i => (gradDot f (Pi.single i (1 : ℝ))).re

/-- The Hessian `H_f(0)` of a complex analytic `f` that maps `ℝ^d` into `ℝ`, read
through its real restriction (Theorem 4.2). -/
noncomputable def hessianOfAnalytic {d : ℕ} (f : (Fin d → ℂ) → ℂ) :
    Matrix (Fin d) (Fin d) ℝ :=
  hessian (realRestriction f)

end Qatlib.Papers.QSpectralHess24.MainResults.Core
