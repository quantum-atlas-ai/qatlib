/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Symmetric Hamiltonians and scheduled evolution

Defines spin matrices, symmetric Hamiltonian components, and the modified adiabatic
interpolation `symH` from [FarhiGoldstoneGutmann2002a]. Their complex embeddings form the
Hermitian path `p2H`.

The module specifies initial and target vectors, scheduled evolution, fidelities for modified
and straight paths, and the runtime-growth predicate `IsPolynomialBound`. It proves continuity,
Hermiticity, and unitarity for the modified scheduled evolution.

## Main statements

* `symH_isSymm`: Proves symmetry of the modified interpolation.
* `p2H_continuous`: Proves continuity of the complex Hamiltonian path.
* `evolutionOperator_unitary`: Proves unitarity for the modified scheduled evolution.

## References

* [Farhi et al., 2002][FarhiGoldstoneGutmann2002a]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
open scoped BigOperators Matrix

/-- The diagonal spin matrix with entry `n / 2 - k` at weight index `k`. -/
def Jz (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun k => (n : ℝ) / 2 - (k.val : ℝ))

/-- The spin raising matrix with entry `sqrt (l * (n - l + 1))` when `k + 1 = l`, and zero
otherwise. -/
def Jplus (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (fun k l =>
    if k.val + 1 = l.val then Real.sqrt ((l.val : ℝ) * ((n : ℝ) - (l.val : ℝ) + 1))
    else 0)

/-- The spin matrix `Jx`, defined as half the sum of `Jplus` and its transpose. -/
def Jx (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 / 2 : ℝ) • (Jplus n + (Jplus n)ᵀ)

/-- The real spin matrix `Jx n` is symmetric. -/
theorem Jx_isSymm (n : ℕ) : (Jx n).IsSymm := by
  unfold Jx
  exact (Matrix.isSymm_add_transpose_self (Jplus n)).smul _

/-- The diagonal spin matrix `Jz n` is symmetric. -/
theorem Jz_isSymm (n : ℕ) : (Jz n).IsSymm := by
  unfold Jz
  exact Matrix.isSymm_diagonal _

/-- The diagonal problem Hamiltonian whose weight-indexed entries are `hpEnergy n k`. -/
def symHP (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun k => hpEnergy (n : ℝ) (k.val : ℝ))

/-- The symmetric driver Hamiltonian `choose (n - 1) 2 • (n / 2 • 1 - Jx n)`, with real scalar
coefficients. -/
def symHB (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ((Nat.choose (n - 1) 2 : ℝ)) • (((n : ℝ) / 2) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - Jx n)

/-- The additional symmetric Hamiltonian `-2 * n` times the sum of `Jx * Jz` and its transpose. -/
def symHE (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (-2 * (n : ℝ)) • ((Jx n * Jz n) + (Jx n * Jz n)ᵀ)

/-- The diagonal problem Hamiltonian `symHP n` is symmetric. -/
theorem symHP_isSymm (n : ℕ) : (symHP n).IsSymm := by
  unfold symHP
  exact Matrix.isSymm_diagonal _

/-- The symmetric driver Hamiltonian `symHB n` is a symmetric matrix. -/
theorem symHB_isSymm (n : ℕ) : (symHB n).IsSymm := by
  unfold symHB
  exact ((Matrix.isSymm_one.smul _).sub (Jx_isSymm n)).smul _

/-- The additional Hamiltonian `symHE n` is a symmetric matrix. -/
theorem symHE_isSymm (n : ℕ) : (symHE n).IsSymm := by
  unfold symHE
  exact (Matrix.isSymm_add_transpose_self (Jx n * Jz n)).smul _

/-- The modified interpolation `(1 - s) • symHB n + s • symHP n + (s * (1 - s)) • symHE n`. -/
def symH (n : ℕ) (s : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 - s) • symHB n + s • symHP n + (s * (1 - s)) • symHE n

/-- The modified interpolation starts at the driver Hamiltonian. -/
@[simp] theorem symH_zero (n : ℕ) : symH n 0 = symHB n := by
  simp [symH]

/-- The modified interpolation ends at the problem Hamiltonian. -/
@[simp] theorem symH_one (n : ℕ) : symH n 1 = symHP n := by
  simp [symH]

/-- The modified interpolation is symmetric for every real parameter. -/
theorem symH_isSymm (n : ℕ) (s : ℝ) : (symH n s).IsSymm := by
  unfold symH
  have h1 : ((1 - s) • symHB n).IsSymm := (symHB_isSymm n).smul _
  have h2 : (s • symHP n).IsSymm := (symHP_isSymm n).smul _
  have h3 : ((s * (1 - s)) • symHE n).IsSymm := (symHE_isSymm n).smul _
  exact (h1.add h2).add h3

/-- The complex matrix obtained by embedding each entry of a real square matrix. -/
def toOperator {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) : Operator D :=
  A.map Complex.ofReal

/-- Embedding a real symmetric matrix into the complex matrices gives a Hermitian operator. -/
theorem toOperator_isHermitian {D : ℕ} {A : Matrix (Fin D) (Fin D) ℝ}
    (hA : A.IsSymm) : (toOperator A).IsHermitian := by
  ext i j
  simp [toOperator, Matrix.conjTranspose_apply, Matrix.map_apply, hA.apply i j,
    Complex.conj_ofReal]

/-- The complex operator obtained from the modified symmetric Hamiltonian `symH n s`. -/
def p2H (n : ℕ) (s : ℝ) : Operator (n + 1) :=
  toOperator (symH n s)

/-- The modified-path operator `p2H n s` is Hermitian for every real parameter. -/
theorem p2H_isHermitian (n : ℕ) (s : ℝ) : (p2H n s).IsHermitian :=
  toOperator_isHermitian (symH_isSymm n s)

/-- The modified-path operator depends continuously on the interpolation parameter. -/
theorem p2H_continuous (n : ℕ) : Continuous (fun s : ℝ => p2H n s) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h : (fun s : ℝ => p2H n s i j) =
      fun s =>
        (((1 - s) * (symHB n) i j + s * (symHP n) i j +
          (s * (1 - s)) * (symHE n) i j : ℝ) : ℂ) := by
    funext s
    simp [p2H, symH, toOperator, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [h]
  fun_prop

/-- The complex overlap `∑ i, star (φ i) * ψ i` of two finite vectors. -/
def overlap {D : ℕ} (φ ψ : Fin D → ℂ) : ℂ := ∑ i, star (φ i) * ψ i

/-- The squared complex norm of the overlap of two finite vectors. -/
def fidelity {D : ℕ} (φ ψ : Fin D → ℂ) : ℝ := Complex.normSq (overlap φ ψ)

/-- The computational basis vector at weight zero. -/
def hpGroundVec (n : ℕ) : Fin (n + 1) → ℂ :=
  fun k => if k.val = 0 then 1 else 0

/-- The symmetric plus-state vector with weight coefficient `sqrt (choose n k) / (sqrt 2) ^ n`. -/
def plusXVec (n : ℕ) : Fin (n + 1) → ℂ :=
  fun k => ((Real.sqrt (Nat.choose n k.val : ℝ) / (Real.sqrt 2) ^ n : ℝ) : ℂ)

/-- The time-ordered evolution from zero to `T` with generator `fun t => Complex.I • H t`. -/
def evolutionOperator {D : ℕ} (H : ℝ → Operator D) (T : ℝ) : Operator D :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
    (fun t => Complex.I • H t) 0 T

/-- The modified Hamiltonian path evaluated at the rescaled parameter `t / T`. -/
def p2Scheduled (n : ℕ) (T : ℝ) : ℝ → Operator (n + 1) :=
  fun t => p2H n (t / T)

/-- The squared overlap with `hpGroundVec n` after evolving `plusXVec n` along the modified
schedule for natural runtime `T`. -/
def p2Fidelity (n : ℕ) (T : ℕ) : ℝ :=
  fidelity (hpGroundVec n)
    (evolutionOperator (p2Scheduled n (T : ℝ)) (T : ℝ) *ᵥ plusXVec n)

/-- The complex straight interpolation between the symmetric driver and problem Hamiltonians. -/
def straightH (n : ℕ) (s : ℝ) : Operator (n + 1) :=
  toOperator ((1 - s) • symHB n + s • symHP n)

/-- The squared overlap with `hpGroundVec n` after evolving `plusXVec n` along the straight
schedule for natural runtime `T`. -/
def straightFidelity (n : ℕ) (T : ℕ) : ℝ :=
  fidelity (hpGroundVec n)
    (evolutionOperator (fun t => straightH n (t / (T : ℝ))) (T : ℝ) *ᵥ plusXVec n)

/-- The rescaled modified Hamiltonian is continuous in time for every real runtime parameter. -/
theorem p2Scheduled_continuous (n : ℕ) (T : ℝ) : Continuous (p2Scheduled n T) := by
  unfold p2Scheduled
  exact (p2H_continuous n).comp (by fun_prop : Continuous fun t : ℝ => t / T)

/-- The rescaled modified Hamiltonian is Hermitian at every time. -/
theorem p2Scheduled_isHermitian (n : ℕ) (T : ℝ) (t : ℝ) :
    (p2Scheduled n T t).IsHermitian := by
  unfold p2Scheduled
  exact p2H_isHermitian n (t/T)

/-- The time-ordered evolution along the modified schedule is a unitary matrix. See
[FarhiGoldstoneGutmann2002a]. -/
theorem evolutionOperator_unitary (n : ℕ) (T : ℝ) :
    evolutionOperator (p2Scheduled n T) T ∈ unitaryGroup (Fin (n+1)) ℂ := by
  unfold evolutionOperator
  exact Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
    (Fin (n+1)) (p2Scheduled n T) (p2Scheduled_continuous n T)
    (p2Scheduled_isHermitian n T) 0 T

/-- The condition that a natural-valued runtime is bounded by `C * (n + 1) ^ d` for some
positive natural `C` and natural `d`. -/
def IsPolynomialBound (T : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n : ℕ, T n ≤ C * (n + 1) ^ d

/-- The identically zero runtime function is polynomially bounded. -/
theorem isPolynomialBound_zero : IsPolynomialBound (fun _ => 0) :=
  ⟨1, 0, by norm_num, fun n => by simp⟩

end Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs
