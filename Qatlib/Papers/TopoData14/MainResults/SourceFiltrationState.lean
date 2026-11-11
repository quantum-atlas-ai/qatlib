/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceFiltrationState — exponential compression of the simplicial filtration

Lloyd--Garnerone--Zanardi, *Quantum algorithms for topological and geometric analysis of
big data*, fixed arXiv:1408.3106v1 (2014).

Section 2, Eqs. (2)--(4) (PDF p. 10): the simplex state at scale `ε` is
`|Ψ⟩^ε_ζ`, the filtration state over `m` grouping scales `ε_i` is
`|Φ⟩_ζ = (1/√(mn)) Σ_i |ε_i⟩|Ψ⟩^ε_ζ`, and the paper states that `log m` qubits register
the grouping scale, `n` qubits label the simplices, the state takes time
`O(ζ^{-1/2} n² log m)` to construct, while a classical description of the filtration
requires `O(2^n)` bits.

This file formalises the *counts* backing that compressed representation:

* `scaleRegisterQubits m = Nat.clog 2 m` — the number of bits/qubits needed to register
  one of `m` grouping scales, with `m ≤ 2^(scaleRegisterQubits m)`;
* `filtrationRegisterQubits n m = n + scaleRegisterQubits m`;
* `simplexLabelCount n = 2^n` — the number of possible simplex labels on `n` vertices,
  i.e. the number of bits a classical description must spend to record which simplices
  are present (one bit per possible simplex);
* the cost functions `simplexStatePreparationCost` and
  `filtrationStatePreparationCost`, with the printed multiplicative relation between them.

Boundary: this is a counting/cost model, not a unitary circuit. It does not construct
Grover search, the amplitudes of Eq. (2)--(4), nor the multi-scale superposition
operator. Those are the algorithmic objects the bound is about; the file records the
dimension bookkeeping the paper's compression claim consists of.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoData14.MainResults

open scoped Classical BigOperators

/-! ## Simplex labels and grouping-scale register -/

/-- The label of a simplex on `n` vertices is an `n`-bit string (its indicator over the
vertex set); there are `2^n` possible labels. Fixed arXiv:1408.3106v1, PDF p. 10:
"`n` qubits are required to label the simplices". -/
def simplexLabelCount (n : ℕ) : ℕ := Fintype.card (Fin n → Bool)

/-- Fixed arXiv:1408.3106v1, PDF p. 10: the number of possible simplex labels on `n`
vertices is `2^n`. -/
theorem simplexLabelCount_eq (n : ℕ) : simplexLabelCount n = 2 ^ n := by
  simp [simplexLabelCount]

/-- Number of qubits needed to register one of `m` grouping scales:
`⌈log₂ m⌉`, defined as `Nat.clog 2 m`. Fixed arXiv:1408.3106v1, PDF p. 10:
"`log m` qubits are required to register the grouping scale `ε`". -/
def scaleRegisterQubits (m : ℕ) : ℕ := Nat.clog 2 m

/-- Supports Eq. (4), fixed arXiv:1408.3106v1 (PDF p. 10): `⌈log₂ m⌉` qubits suffice to
address `m` grouping scales. -/
theorem le_two_pow_scaleRegisterQubits (m : ℕ) : m ≤ 2 ^ scaleRegisterQubits m :=
  Nat.le_pow_clog (by norm_num) m

/-- Fixed arXiv:1408.3106v1, PDF p. 10: the quantum filtration register consists of
`log m` scale qubits plus `n` simplex-label qubits. -/
def filtrationRegisterQubits (n m : ℕ) : ℕ := n + scaleRegisterQubits m

/-- The address space of the filtration register (`n + ⌈log₂ m⌉` qubits) covers all
`m · 2^n` (scale, simplex) pairs. Fixed arXiv:1408.3106v1, Eq. (4), PDF p. 10. -/
theorem filtrationRegister_dimension (n m : ℕ) :
    m * 2 ^ n ≤ 2 ^ filtrationRegisterQubits n m := by
  rw [filtrationRegisterQubits, Nat.pow_add]
  calc m * 2 ^ n = 2 ^ n * m := Nat.mul_comm m (2 ^ n)
    _ ≤ 2 ^ n * 2 ^ scaleRegisterQubits m :=
        Nat.mul_le_mul_left _ (le_two_pow_scaleRegisterQubits m)

/-- Fixed arXiv:1408.3106v1, Eq. (4) (PDF p. 10): the index set of the filtration state,
one register for the grouping scale (`Fin m`) and one `n`-bit simplex label (`Fin n → Bool`). -/
abbrev FiltrationIndex (n m : ℕ) := Fin m × (Fin n → Bool)

/-- Fixed arXiv:1408.3106v1, Eq. (4), PDF p. 10: the filtration state has exactly
`m · 2^n` computational-basis amplitudes. -/
theorem card_filtrationIndex (n m : ℕ) :
    Fintype.card (FiltrationIndex n m) = m * 2 ^ n := by
  simp [FiltrationIndex]

/-- Fixed arXiv:1408.3106v1, Eq. (4), PDF p. 10: the quantum filtration state of
`m` scales over `n`-vertex simplices fits in `n + ⌈log₂ m⌉` qubits. -/
theorem filtrationIndex_card_le_two_pow_qubits (n m : ℕ) :
    Fintype.card (FiltrationIndex n m) ≤ 2 ^ filtrationRegisterQubits n m := by
  rw [card_filtrationIndex]
  exact filtrationRegister_dimension n m

/-- A classical description of the simplicial complex records, for each of the `2^n`
possible simplices, whether it is present: `2^n` bits. Fixed arXiv:1408.3106v1,
PDF p. 10: "a classical description of the filtration of the simplicial complex
requires `O(2^n)` bits". -/
def classicalFiltrationBits (n : ℕ) : ℕ := 2 ^ n

/-- Fixed arXiv:1408.3106v1, PDF p. 10: the classical bit count is exactly the number
of possible simplex labels. -/
theorem classicalFiltrationBits_eq_simplexLabelCount (n : ℕ) :
    classicalFiltrationBits n = simplexLabelCount n := (simplexLabelCount_eq n).symm

/-- Supports Eq. (4), fixed arXiv:1408.3106v1 (PDF p. 10): `2 · n < 2^n` for `n ≥ 4`, so the
linear qubit count is exponentially below the classical bit count. -/
theorem two_mul_lt_two_pow (n : ℕ) (hn : 4 ≤ n) : 2 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hk2 : 2 ≤ 2 ^ k := by
        have h1 : (2 : ℕ) ^ 1 ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using h1
      rw [Nat.pow_succ]
      omega

/-- Fixed arXiv:1408.3106v1, PDF p. 10: if the `m` grouping scales are themselves
addressable in `n` bits (`m ≤ 2^n`) and `n ≥ 4`, then the filtration state's
`n + ⌈log₂ m⌉` qubits are strictly fewer than the `2^n` classical bits. This is the
paper's exponential compression statement. -/
theorem filtrationRegisterQubits_lt_classicalFiltrationBits
    (n m : ℕ) (hm : m ≤ 2 ^ n) (hn : 4 ≤ n) :
    filtrationRegisterQubits n m < classicalFiltrationBits n := by
  have hlog : scaleRegisterQubits m ≤ n := by
    rw [scaleRegisterQubits]
    exact Nat.clog_le_iff_le_pow (by norm_num) |>.mpr hm
  have hqubits : filtrationRegisterQubits n m ≤ 2 * n := by
    rw [filtrationRegisterQubits]
    omega
  have hpow := two_mul_lt_two_pow n hn
  rw [classicalFiltrationBits]
  omega

/-! ## Construction cost (Eqs. (2)--(4)) -/

/-- Cost of constructing one simplex state `|ψ⟩^ε_k` at scale `ε` to fraction `ζ`:
`O(n² ζ^{-1/2})`. Fixed arXiv:1408.3106v1, PDF p. 9--10. -/
def simplexStatePreparationCost (n : ℕ) (ζ : ℝ) : ℝ :=
  (n : ℝ) ^ 2 / Real.sqrt ζ

/-- Cost of constructing the filtration state over `m` grouping scales:
`O(ζ^{-1/2} n² log m)`. Fixed arXiv:1408.3106v1, Eq. (4) discussion, PDF p. 10. -/
def filtrationStatePreparationCost (n m : ℕ) (ζ : ℝ) : ℝ :=
  Real.log m * ((n : ℝ) ^ 2 / Real.sqrt ζ)

/-- Fixed arXiv:1408.3106v1, PDF p. 10: the filtration-state construction cost is the
per-scale simplex-state cost multiplied by the `log m` scale factor. -/
theorem filtrationStatePreparationCost_eq_simplexCost_mul_log
    (n m : ℕ) (ζ : ℝ) :
    filtrationStatePreparationCost n m ζ =
      Real.log m * simplexStatePreparationCost n ζ := rfl

/-- Fixed arXiv:1408.3106v1, PDF p. 10: the printed form
`ζ^{-1/2} n² log m` of the filtration-state construction cost. -/
theorem filtrationStatePreparationCost_eq_source (n m : ℕ) (ζ : ℝ) :
    filtrationStatePreparationCost n m ζ =
      (Real.sqrt ζ)⁻¹ * (n : ℝ) ^ 2 * Real.log m := by
  unfold filtrationStatePreparationCost
  rw [div_eq_mul_inv]
  ring

end Qatlib.Papers.TopoData14.MainResults

end
