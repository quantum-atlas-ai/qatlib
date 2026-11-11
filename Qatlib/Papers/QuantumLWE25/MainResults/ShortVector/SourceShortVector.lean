/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — short vectors in q-ary lattices (Lemma 18)

Fixed arXiv:2310.00644v2, Lemma 18, p.11 (§2.1, "q-ary lattices").

Source statement: for `q ≥ 2` and `m ≥ 2n log₂ q`, for all but at most a `q^{-0.16n}`
fraction of `A ∈ Z_q^{n×m}` one has `λ₁^∞(L_q(A)) ≥ q/4`, where
`L_q(A) = {Aᵀs + qℤ^m : s ∈ Z_q^n}`.

The proof (p.11) generalises [GPV08, Lemma 5.3] from prime `q` to arbitrary `q`: for
each nonzero `s`, `⟨a,s⟩ mod q` lands in `(-q/4, q/4)` with probability at most `2/3`
over `a`, hence `Aᵀs` is `∞`-short on at most `(2/3)^m ≤ q^{-1.16n}` of the matrices;
a union bound over the `q^n` secrets gives the claim.

The statement below is over the uniform matrix ensemble, with the "fraction" written
as `card(bad)/q^{nm}`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix

/-- The `q`-ary lattice `L_q(A) = {Aᵀs + q z : s ∈ Z_q^n, z ∈ ℤ^m}`, as a set of integer
vectors (paper p.11). -/
def qaryLattice {n m q : ℕ} [NeZero q] (A : Matrix (Fin n) (Fin m) (ZMod q)) : Set (Fin m → ℤ) :=
  {x | ∃ (s : Fin n → ZMod q) (z : Fin m → ℤ),
        ∀ j, (x j : ZMod q) = (Aᵀ *ᵥ s) j + (((q : ℤ) * z j : ℤ) : ZMod q)}

/-- The `ℓ∞` norm of an integer vector. -/
def linfNorm {m : ℕ} (x : Fin m → ℤ) : ℕ := Finset.univ.sup fun j => (x j).natAbs

/-- The `A`'s whose `q`-ary lattice fails `λ₁^∞(L_q(A)) ≥ q/4`: those admitting a nonzero
vector of `ℓ∞` norm `< q/4`. -/
def badMatrices (n m q : ℕ) [NeZero q] : Finset (Matrix (Fin n) (Fin m) (ZMod q)) := by
  classical
  exact Finset.univ.filter fun A =>
    ¬ ∀ x ∈ qaryLattice A, x ≠ 0 → (q : ℤ) ≤ 4 * (linfNorm x : ℤ)

/-- **Lemma 18, p.11.** If `q ≥ 2` and `m ≥ 2n log₂ q`, then the fraction of
`A ∈ Z_q^{n×m}` with `λ₁^∞(L_q(A)) ≥ q/4` is at least `1 - q^{-0.16n}`; equivalently
the bad fraction is at most `q^{-0.16n}`.

Gap: the counting argument on p.11 ("`Pr_{a₁}[s₁a₁+v mod q ∈ (-q/4,q/4)] ≤ 2/3`",
then a union bound over `s ∈ Z_q^n`) is elementary but needs the distribution of
`A ↦ Aᵀs` as a uniform `m`-fold product for each fixed nonzero `s`, plus the
independence across the `m` coordinates; the current model has the matrix ensemble as a
plain finite type, so it would first need `Pr_{A}(Aᵀs = y) = q^{-nm}`-style counting
lemmas. Candidate dependency: `ProbabilityCore.Concentration` finite-product union bounds. -/
def qary_shortest_vector_large {n m q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hm : 2 * n * Nat.log2 q ≤ m) : Prop := ((badMatrices n m q).card : ℝ) / (q : ℝ) ^ (n * m) ≤
      (q : ℝ) ^ (-(0.16 * (n : ℝ)))

end Qatlib.Papers.QuantumLWE25.MainResults
