/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

abbrev Dim (n : ℕ) : Type := Fin (2 ^ n)

abbrev State (n : ℕ) : Type := EuclideanSpace ℂ (Dim n)

abbrev Op (n : ℕ) : Type := State n →L[ℂ] State n

abbrev Ham (n : ℕ) : Type := Matrix (Dim n) (Dim n) ℂ

def IsHermitian (H : Ham n) : Prop := Hᴴ = H

def toOp (H : Ham n) : Op n := Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H

theorem norm_toOp (H : Ham n) : ‖toOp H‖ = ‖H‖ := rfl

def timeEvolution (H : Ham n) (t : ℝ) : Op n :=
  NormedSpace.exp ((-t) • (Complex.I • toOp H))

abbrev spectralNorm (H : Ham n) : ℝ := ‖H‖

def PolyBound (f : ℕ → ℝ) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, f n ≤ (c : ℝ) * ((n : ℝ) + 1) ^ k + (c : ℝ)

def PolyBoundedAt (n : ℕ) (v : ℝ) : Prop :=
  ∃ c k : ℕ, v ≤ (c : ℝ) * ((n : ℝ) + 1) ^ k + (c : ℝ)

def NonNegligibleAt (n : ℕ) (v : ℝ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ 1 / ((c : ℝ) * ((n : ℝ) + 1) ^ k) ≤ v

structure Algorithm (α : Type) where

  run : List ℕ → List (ℕ × α)

  steps : List ℕ → ℕ

def PolyTime {α : Type} (prog : Algorithm α) : Prop :=
  ∃ c k : ℕ, ∀ inp : List ℕ, prog.steps inp ≤ c * (inp.length + 1) ^ k + c

def rowEntries {α : Type} [Zero α] [DecidableEq α]
    (A : Matrix (Dim n) (Dim n) α) (i : Dim n) : List (ℕ × α) :=
  (Finset.univ.filter (fun j : Dim n => A i j ≠ 0)).toList.map (fun j => (j.val, A i j))

def RowSparse {α : Type} [Zero α] [DecidableEq α]
    (A : Matrix (Dim n) (Dim n) α) (D : ℕ) : Prop :=
  ∀ i : Dim n, (Finset.univ.filter (fun j : Dim n => A i j ≠ 0)).card ≤ D

def RowComputable {α : Type} [Zero α] [DecidableEq α]
    (A : Matrix (Dim n) (Dim n) α) : Prop :=
  ∃ prog : Algorithm α, PolyTime prog ∧ ∀ i : Dim n, prog.run [i.val] = rowEntries A i

structure Circuit (n : ℕ) where

  unitary : Op n

  size : ℕ

  contract : ∀ ψ : State n, ‖unitary ψ‖ ≤ ‖ψ‖

def PolySize (C : Circuit n) : Prop :=
  ∃ c k : ℕ, (C.size : ℝ) ≤ (c : ℝ) * ((n : ℝ) + 1) ^ k + (c : ℝ)

def PolySize3 (n : ℕ) (t α : ℝ) (C : Circuit n) : Prop :=
  ∃ c k : ℕ, (C.size : ℝ) ≤ (c : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ k + (c : ℝ)

def Simulatable (H : Ham n) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : Circuit n, PolySize3 n t α C ∧ ‖C.unitary - timeEvolution H t‖ ≤ α

def zeroState (n : ℕ) : State n :=
  EuclideanSpace.single ⟨0, Nat.two_pow_pos n⟩ (1 : ℂ)

def TransfersState (ψ φ : State n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : Circuit n, PolySize C ∧ ‖C.unitary ψ - φ‖ ≤ ε

def Generable (φ : State n) : Prop := TransfersState (zeroState n) φ

abbrev QSamples (φ : State n) : Prop := Generable φ

def rayleigh (H : Ham n) (ψ : State n) : ℝ := (⟪ψ, toOp H ψ⟫_ℂ).re

def IsGroundstate (H : Ham n) (ψ : State n) : Prop :=
  ‖ψ‖ = 1 ∧ ∀ φ : State n, ‖φ‖ = 1 → rayleigh H ψ ≤ rayleigh H φ

def GroundvalueZero (H : Ham n) : Prop :=
  ∀ ψ : State n, IsGroundstate H ψ → toOp H ψ = 0

def HasUniqueGroundstate (H : Ham n) (ψ : State n) : Prop :=
  IsGroundstate H ψ ∧
    ∀ φ : State n, IsGroundstate H φ → ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ

def SpectralGapAtLeast (H : Ham n) (ψ : State n) (γ : ℝ) : Prop :=
  IsGroundstate H ψ →
    ∀ φ : State n, ‖φ‖ = 1 → ⟪ψ, φ⟫_ℂ = 0 → γ ≤ rayleigh H φ - rayleigh H ψ

structure AdiabaticPath (n : ℕ) where

  H : ℝ → Ham n

  herm : ∀ s : ℝ, IsHermitian (H s)

  deriv : ℝ → Ham n

  hasDeriv : ∀ s : ℝ, HasDerivAt H (deriv s) s

  groundState : ℝ → State n

  uniqueGround : ∀ s : ℝ, HasUniqueGroundstate (H s) (groundState s)

  gap : ℝ → ℝ

  gap_spec : ∀ s : ℝ, 0 < gap s ∧ SpectralGapAtLeast (H s) (groundState s) (gap s)

  simulatable : ∀ s : ℝ, Simulatable (H s)

def AdiabaticCondition (P : AdiabaticPath n) (T ε : ℝ) : Prop :=
  ∀ s : ℝ, T * ε ≥ ‖P.deriv s‖ / (P.gap s) ^ 2

structure AdiabaticGenerator (n : ℕ) where

  path : AdiabaticPath n

  T : ℝ

  ε : ℝ

  T_pos : 0 < T

  ε_pos : 0 < ε

  adiabatic : AdiabaticCondition path T ε

  initial_preparable : Generable (path.groundState 0)

def AdiabaticGenerable (φ : State n) : Prop :=
  ∃ G : AdiabaticGenerator n, G.path.groundState 1 = φ

structure PromiseProblem where

  decide : List Bool → Bool

  yes : Set (List Bool)

  no : Set (List Bool)

  mem_yes : ∀ x, x ∈ yes ↔ decide x = true

  mem_no : ∀ x, x ∈ no ↔ decide x = false

structure SZKCertificate where

  rounds : ℕ

  completeness : ℝ

  soundness : ℝ

  verifierSize : List Bool → ℕ

  verifierPoly : ∃ c k : ℕ, ∀ x : List Bool,
    verifierSize x ≤ c * (x.length + 1) ^ k + c

  simulatorSize : List Bool → ℕ

  simulatorPoly : ∃ c k : ℕ, ∀ x : List Bool,
    simulatorSize x ≤ c * (x.length + 1) ^ k + c

  complete : 2 / 3 ≤ completeness

  sound : soundness ≤ 1 / 3

def InSZK (_L : PromiseProblem) : Prop := ∃ cert : SZKCertificate, 0 < cert.completeness

structure CQSInstance where

  err : ℝ

  err_nonneg : 0 ≤ err

  err_half : err ≤ 1 / 2

  nin : ℕ

  nout : ℕ

  gates : ℕ

  amp : State nout

structure CQSFamily where

  inst : ℕ → CQSInstance

  solver : ℕ → Bool

  polyGates : ∃ c k : ℕ, ∀ m : ℕ, (inst m).gates ≤ c * (m + 1) ^ k + c

structure CQSReduction (L : PromiseProblem) where

  family : CQSFamily

  index : List Bool → ℕ

  polyIndex : ∃ c k : ℕ, ∀ x : List Bool,
    index x ≤ c * (x.length + 1) ^ k + c

  decides : ∀ x : List Bool, family.solver (index x) = L.decide x

def CQSReducible (L : PromiseProblem) : Prop := Nonempty (CQSReduction L)

abbrev MC (n : ℕ) : Type := Matrix (Dim n) (Dim n) ℝ

def IsStochastic (M : MC n) : Prop := ∀ i : Dim n, (∑ j : Dim n, M i j) = 1

def IsReversible (M : MC n) (π : Dim n → ℝ) : Prop :=
  (∀ i : Dim n, 0 < π i) ∧ ∀ i j : Dim n, M i j * π i = M j i * π j

def HM (M : MC n) (π : Dim n → ℝ) : Ham n :=
  1 - (diagonal (fun i : Dim n => (Real.sqrt (π i) : ℂ))) *
      (M.map (algebraMap ℝ ℂ)) *
      (diagonal (fun i : Dim n => ((Real.sqrt (π i))⁻¹ : ℂ)))

def ketOfDist (π : Dim n → ℝ) : State n :=
  EuclideanSpace.equiv (Dim n) ℂ |>.symm (fun i => (Real.sqrt (π i) : ℂ))

structure StronglySamplable (M : MC n) (π : Dim n → ℝ) where

  stochastic : IsStochastic M

  reversible : IsReversible M π

  rowComputable : RowComputable M

  positive : ∀ i : Dim n, 0 < π i

  D : ℕ

  rowSparse : RowSparse M D

  DPoly : PolyBoundedAt n (D : ℝ)

def RapidlyMixing (M : MC n) (π : Dim n → ℝ) : Prop :=
  ∃ γ : ℝ, NonNegligibleAt n γ ∧ SpectralGapAtLeast (HM M π) (ketOfDist π) γ

def SlowlyVarying {T : ℕ} (π : Fin (T + 1) → Dim n → ℝ) : Prop :=
  ∀ t : Fin T, NonNegligibleAt n
    (∑ i : Dim n, Real.sqrt (π (Fin.castSucc t) i * π t.succ i))

end Qatlib.Papers.AdiabStateGen03.MainResults
