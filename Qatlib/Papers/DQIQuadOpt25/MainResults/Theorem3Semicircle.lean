/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIQuadOpt25.MainResults.Source.AlgorithmModel
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DQIQuadOpt25 — Theorem 3 (semicircle law for the max-LINSAT DQI state)

Fixed arXiv:2510.08061v2, Theorem 3 and Eq. (8), p.4; statement of the
tridiagonal matrix and of `a_k`, `d` at pp.4–5; proof sketch p.5
(three steps) and full proof pp.12–14.

The theorem: let `f(x) = ∑_{i=1}^m f_i(B_i x)` be a max-LINSAT objective with
`B ∈ F_p^{m×n}`, `m > n`, and `|f_i^{-1}(+1)| = r` for every `i`.  Let
`s^{(m,ℓ)}` be the expected number of satisfied constraints of the string
obtained by measuring the degree-`ℓ` DQI state.  If `2ℓ+1 < d^⊥`, where `d^⊥`
is the minimum distance of the code `C^⊥ = {d ∈ F_p^m : Bᵀd = 0}`, then

  `⟨s^{(m,ℓ)}⟩ = mr/p + (√(r(p−r))/p) · w† A^{(m,ℓ,d)} w`   (Eq. (8))

where `w = (w_0, …, w_ℓ)`, `A^{(m,ℓ,d)}` is the `(ℓ+1)×(ℓ+1)` symmetric
tridiagonal matrix whose diagonal entries are `0, d, 2d, …, ℓd` and whose
entries on the `k`-th super/subdiagonal are `a_{k+1} = √((k+1)(m−k))`, with
`a_k = √(k(m−k+1))` and `d = (p−2r)/√(r(p−r))`.

Modelling notes.

* The distance condition `2ℓ+1 < d^⊥` is expressed as
  `MinDistanceExceeds B (2*ℓ+1)`: every nonzero codeword `d` in the kernel of
  `Bᵀ` has Hamming weight strictly greater than `2ℓ+1`.  (`Bᵀ` here is
  `B.transpose`, and `d : Fin m → F_p` is a length-`m` vector; the paper's
  `Bᵀd = 0` is `B.transpose.mulVec d = 0`.)
* `dqiExpectation inst P` is the expectation of the number of satisfied
  constraints when measuring the (unnormalised) DQI state
  `|P(f)⟩ = ∑_x P(f(x))|x⟩`: each `x` occurs with probability proportional to
  `P(f(x))²`, i.e.
  `(∑_x P(f(x))² · sat(x)) / (∑_x P(f(x))²)` (proof step 1, p.5).
* `IsKrawtchoukSystem m q ℓ K` records the two properties of the Krawtchouk
  polynomials used in the proof (step 3, pp.5, 13–14): `K_0 = 1`, orthonormality
  for the binomial inner product `⟨p,q⟩_binom = ∑_s p(s)q(s)N_binom(s)`, and the
  fact that multiplication by `s` is represented in the basis `K_0, …, K_ℓ` by
  the tridiagonal matrix `A^{(m,ℓ,d)}` — this is the three-term recurrence
  guaranteed by Favard's theorem, stated in the matrix form actually consumed by
  Eq. (8).  Constructing the Krawtchouk polynomials and deriving these
  properties (or the equivalent recurrence
  `sK_k(s) = √(q(1−q)(m−k)(k+1))K_{k+1}(s) + √(q(1−q)k(m−k+1))K_{k−1}(s) + (mq−k)K_k(s)`)
  is the formalisation gap of this file.
* `hP` is the expansion of the shifted/rescaled DQI polynomial `P*` in the
  Krawtchouk basis, `P*(s) = ∑_k w_k K_k(s)`, where `P*(s) = P(2s − m)`
  corresponds to `s` satisfied constraints (`f(x) = 2s − m`).

Results proved here:

* the identity `f(x) = 2·sat(x) − m` for sign-valued max-LINSAT constraints
  (`linsatObjective_eq_two_satCount_sub`);
* the algebraic identity `d·√(r(p−r)) = p − 2r` for `d = (p−2r)/√(r(p−r))`
  (`semicircleD_mul_sqrt`);
* the entry structure and symmetry of the tridiagonal matrix `A^{(m,ℓ,d)}`
  (`tridiagA_apply`, `tridiagA_symm`, `tridiagA_diag`, `tridiagA_super`,
  `tridiagA_sub`), matching the displayed matrix on p.4;
* the identity `a_{k+1} = √((k+1)(m−k))` spelling out the paper's `a_k` on the
  off-diagonal (`ak_succ`), and nonnegativity/nonvanishing of `a_k` on
  `1 ≤ k ≤ m` (`ak_nonneg`, `ak_pos`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults

open Qatlib.Papers.DQIQuadOpt25.MainResults.Source

/-! ## The code distance hypothesis and the DQI expectation -/

/-- The paper's condition `2ℓ + 1 < d^⊥`: every nonzero vector in the kernel of
`Bᵀ` (a codeword of `C^⊥`) has Hamming weight strictly greater than `t`. -/
def MinDistanceExceeds {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (t : ℕ) : Prop :=
  ∀ d : Fin m → ZMod p, d ≠ 0 → B.transpose.mulVec d = 0 → t < hammingWeight d

/-- The expected number of satisfied constraints after measuring the DQI state
`|P(f)⟩ = ∑_x P(f(x))|x⟩` of a max-LINSAT instance (Theorem 3, proof step 1,
p.5): the weighted average of `sat(x)` with weights `P(f(x))²`. -/
def dqiExpectation {p n m : ℕ} [NeZero p] (inst : LINSATInstance p n m)
    (P : Polynomial ℝ) : ℝ :=
  (∑ x : Fin n → ZMod p,
      (P.eval ((linsatObjective inst x : ℤ) : ℝ)) ^ 2 * (linsatSatCount inst x : ℝ))
    / (∑ x : Fin n → ZMod p,
        (P.eval ((linsatObjective inst x : ℤ) : ℝ)) ^ 2)

/-- For sign-valued max-LINSAT constraints the objective is twice the number of
satisfied constraints minus `m` (so `s` satisfied constraints give objective
`2s − m`, the substitution used in the proof of Theorem 3). -/
theorem linsatObjective_eq_two_satCount_sub {p n m : ℕ} (inst : LINSATInstance p n m)
    (hinst : ∀ i y, inst.f i y = 1 ∨ inst.f i y = -1) (x : Fin n → ZMod p) :
    linsatObjective inst x = 2 * (linsatSatCount inst x : ℤ) - (m : ℤ) := by
  unfold linsatObjective linsatSatCount
  exact sum_sign_eq_two_satCount_sub _ (fun i => hinst i (linsatArg inst x i))

/-! ## The coefficients `a_k` and `d` -/

/-- The off-diagonal coefficient `a_k = √(k(m−k+1))` of the matrix
`A^{(m,ℓ,d)}` (p.4). -/
def ak (m k : ℕ) : ℝ := Real.sqrt ((k : ℝ) * ((m : ℝ) - (k : ℝ) + 1))

/-- The entry `d = (p−2r)/√(r(p−r))` of `A^{(m,ℓ,d)}` (p.4). -/
def semicircleD (r p : ℝ) : ℝ := (p - 2 * r) / Real.sqrt (r * (p - r))

/-- The paper's off-diagonal coefficient at position `k+1` is
`a_{k+1} = √((k+1)(m−k))`. -/
theorem ak_succ (m k : ℕ) :
    ak m (k + 1) = Real.sqrt (((k : ℝ) + 1) * ((m : ℝ) - (k : ℝ))) := by
  unfold ak
  congr 1
  push_cast
  ring

/-- `a_k ≥ 0`. -/
theorem ak_nonneg (m k : ℕ) : 0 ≤ ak m k := Real.sqrt_nonneg _

/-- `a_k > 0` whenever `1 ≤ k ≤ m`. -/
theorem ak_pos {m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) : 0 < ak m k := by
  unfold ak
  apply Real.sqrt_pos.2
  have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have h2 : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
    have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    linarith
  nlinarith

/-- The defining identity of the entry `d = (p−2r)/√(r(p−r))`:
`d · √(r(p−r)) = p − 2r`. -/
theorem semicircleD_mul_sqrt {r p : ℕ} (hr0 : 0 < r) (hrp : r < p) :
    semicircleD (r : ℝ) (p : ℝ) * Real.sqrt ((r : ℝ) * ((p : ℝ) - (r : ℝ)))
      = (p : ℝ) - 2 * (r : ℝ) := by
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hpr : (r : ℝ) < (p : ℝ) := by exact_mod_cast hrp
  have hS : (0 : ℝ) < (r : ℝ) * ((p : ℝ) - (r : ℝ)) := mul_pos hr (by linarith)
  unfold semicircleD
  rw [div_mul_cancel₀ ((p : ℝ) - 2 * (r : ℝ))
    (b := Real.sqrt ((r : ℝ) * ((p : ℝ) - (r : ℝ))))
    (ne_of_gt (Real.sqrt_pos.2 hS))]

/-- `d` is real-valued and its sign is the sign of `p − 2r`: the paper's
`d = (p−2r)/√(r(p−r))`. -/
theorem semicircleD_eq {r p : ℕ} (_hr0 : 0 < r) (_hrp : r < p) :
    semicircleD (r : ℝ) (p : ℝ)
      = ((p : ℝ) - 2 * (r : ℝ)) / Real.sqrt ((r : ℝ) * ((p : ℝ) - (r : ℝ))) := rfl

/-! ## The tridiagonal matrix `A^{(m,ℓ,d)}` -/

/-- The symmetric tridiagonal matrix `A^{(m,ℓ,d)}` of Theorem 3 (p.4): diagonal
entries `0, d, 2d, …, ℓd` and entries `a_{k+1}` on the `k`-th super- and
subdiagonal, where `a_k = √(k(m−k+1))`. -/
def tridiagA (m ℓ : ℕ) (d : ℝ) : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (i.val : ℝ) * d
    else if i.val + 1 = j.val then ak m j.val
    else if j.val + 1 = i.val then ak m i.val
    else 0

/-- Entry formula of `A^{(m,ℓ,d)}` (definitional). -/
theorem tridiagA_apply (m ℓ : ℕ) (d : ℝ) (i j : Fin (ℓ + 1)) :
    tridiagA m ℓ d i j =
      (if i = j then (i.val : ℝ) * d
       else if i.val + 1 = j.val then ak m j.val
       else if j.val + 1 = i.val then ak m i.val
       else 0) := rfl

/-- Diagonal entries of `A^{(m,ℓ,d)}` are `k·d`. -/
theorem tridiagA_diag (m ℓ : ℕ) (d : ℝ) (i : Fin (ℓ + 1)) :
    tridiagA m ℓ d i i = (i.val : ℝ) * d := by
  rw [tridiagA_apply, if_pos rfl]

/-- Superdiagonal entries of `A^{(m,ℓ,d)}` are `a_{i+1}`. -/
theorem tridiagA_super (m ℓ : ℕ) (d : ℝ) (i j : Fin (ℓ + 1))
    (hij : i ≠ j) (h : i.val + 1 = j.val) :
    tridiagA m ℓ d i j = ak m j.val := by
  rw [tridiagA_apply, if_neg hij, if_pos h]

/-- Subdiagonal entries of `A^{(m,ℓ,d)}` are `a_{j+1}`. -/
theorem tridiagA_sub (m ℓ : ℕ) (d : ℝ) (i j : Fin (ℓ + 1))
    (hij : i ≠ j) (h : j.val + 1 = i.val) :
    tridiagA m ℓ d i j = ak m i.val := by
  have hne : ¬ i.val + 1 = j.val := by omega
  rw [tridiagA_apply, if_neg hij, if_neg hne, if_pos h]

/-- All other entries of `A^{(m,ℓ,d)}` vanish. -/
theorem tridiagA_off (m ℓ : ℕ) (d : ℝ) (i j : Fin (ℓ + 1))
    (hij : i ≠ j) (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) :
    tridiagA m ℓ d i j = 0 := by
  rw [tridiagA_apply, if_neg hij, if_neg h1, if_neg h2]

/-- `A^{(m,ℓ,d)}` is symmetric, as asserted on p.4. -/
theorem tridiagA_symm (m ℓ : ℕ) (d : ℝ) (i j : Fin (ℓ + 1)) :
    tridiagA m ℓ d i j = tridiagA m ℓ d j i := by
  by_cases hij : i = j
  · subst hij; rfl
  · by_cases h1 : i.val + 1 = j.val
    · have h2 : ¬ j.val + 1 = i.val := by omega
      simp only [tridiagA_apply, if_neg hij, if_neg (Ne.symm hij), if_neg h2, if_pos h1]
    · by_cases h2 : j.val + 1 = i.val
      · simp only [tridiagA_apply, if_neg hij, if_neg (Ne.symm hij), if_neg h1, if_pos h2]
      · simp only [tridiagA_apply, if_neg hij, if_neg (Ne.symm hij), if_neg h1, if_neg h2]

/-! ## The binomial inner product and the Krawtchouk input -/

/-- The binomial probability weight `N_binom(s) = C(m,s) q^s (1−q)^{m−s}`
(proof step 2, p.5), with `q = r/p` the probability that a random string
satisfies one constraint. -/
def binomWeight (m : ℕ) (q : ℝ) (s : ℕ) : ℝ :=
  (m.choose s : ℝ) * q ^ s * (1 - q) ^ (m - s)

/-- The Krawtchouk input of the proof of Theorem 3 (step 3, pp.5, 13–14):
a family `K : ℕ → ℕ → ℝ` of polynomials (in `s`) indexed by degree `k ≤ ℓ`,
which is `0`-th degree `1`, orthonormal for the binomial inner product, and for
which multiplication by `s` has the tridiagonal matrix `A^{(m,ℓ,d)}` in the
basis `K_0, …, K_ℓ`.  The third field is the matrix form of the three-term
recurrence relation (Favard's theorem); see the module note. -/
structure IsKrawtchoukSystem (m ℓ : ℕ) (q d : ℝ) (K : ℕ → ℕ → ℝ) : Prop where
  /-- `K_0 ≡ 1`. -/
  zero : ∀ s, K 0 s = 1
  /-- Orthonormality for the binomial inner product. -/
  orthonormal : ∀ i j : Fin (ℓ + 1),
    (∑ s ∈ Finset.range (m + 1), K i.val s * K j.val s * binomWeight m q s)
      = if i = j then 1 else 0
  /-- Multiplication by `s`, in the Krawtchouk basis, is the tridiagonal matrix
  `A^{(m,ℓ,d)}`: this is Eq. (8) in matrix form and is equivalent to the
  three-term recurrence relation of the Krawtchouk polynomials. -/
  mul_by_s : ∀ i j : Fin (ℓ + 1),
    (∑ s ∈ Finset.range (m + 1), (s : ℝ) * K i.val s * K j.val s * binomWeight m q s)
      = tridiagA m ℓ d i j

/-! ## Theorem 3 -/

/-- **Theorem 3 of arXiv:2510.08061v2, Eq. (8) (p.4).**

For a max-LINSAT instance with `B ∈ F_p^{m×n}`, `m > n`, all constraints
satisfied on exactly `r` of the `p` field elements (`1 ≤ r ≤ p−1`), and
`2ℓ + 1 < d^⊥` (minimum distance of the dual code `{d : Bᵀd = 0}`), the expected
number of satisfied constraints of the degree-`≤ ℓ` DQI state is

  `⟨s^{(m,ℓ)}⟩ = mr/p + (√(r(p−r))/p) · w† A^{(m,ℓ,d)} w`,

where `w` collects the coefficients of `P*` in the Krawtchouk basis,
`A^{(m,ℓ,d)}` is the symmetric tridiagonal matrix of `tridiagA`, `a_k = √(k(m−k+1))`
and `d = (p−2r)/√(r(p−r))`.

Formalisation status (statement-only definition).  Step 1 of the proof (the measured distribution
is `|P*(s)|²N(s)`, giving the weighted average of `dqiExpectation`) is built
into the definition of `dqiExpectation`.  Step 2 (the first `2ℓ+1` moments of
`N(s)` and `N_binom(s)` agree, from the distance hypothesis `hdist`) and step 3
(the Krawtchouk expansion, packaged as `IsKrawtchoukSystem`) are not proved:
step 2 needs the combinatorial count of `s`-satisfied strings across the
`2ℓ+1`-wise independent constraint family, and step 3 needs the construction of
the Krawtchouk polynomials together with their orthogonality and three-term
recurrence (Favard's theorem, cited as [7]; Krawtchouk polynomials, [11]).
The algebraic interface of the matrix `A^{(m,ℓ,d)}` — its entries, symmetry and
the coefficient identities — is proved above.  Once step 2 and the Krawtchouk
construction are available, the proof is: rewrite `dqiExpectation` as
`(∑_s s|P*(s)|²N(s)) / (∑_s |P*(s)|²N(s))`, replace `N` by `N_binom` by moment
matching, expand `P* = ∑ w_k K_k` and use `hK.orthonormal` (denominator `= 1`)
together with `hK.mul_by_s` and `hK.zero` to obtain
`∑_{i,j} w_i w_j A_{ij} + (mr/p)·∑_{i,j} w_i w_j δ_{ij}`. -/
def theorem3_semicircle
    {p m n ℓ : ℕ} [Fact p.Prime] (hmn : n < m)
    (inst : LINSATInstance p n m) (r : ℕ)
    (hr0 : 0 < r) (hrp : r < p)
    (hr : ∀ i, (Finset.univ.filter fun y : ZMod p => inst.f i y = 1).card = r)
    (hdist : MinDistanceExceeds inst.B (2 * ℓ + 1))
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ ℓ)
    (K : ℕ → ℕ → ℝ)
    (hK : IsKrawtchoukSystem m ℓ ((r : ℝ) / (p : ℝ)) (semicircleD (r : ℝ) (p : ℝ)) K)
    (w : Fin (ℓ + 1) → ℝ)
    (hP : ∀ s : ℕ, s ≤ m →
      P.eval (2 * (s : ℝ) - (m : ℝ)) = ∑ k : Fin (ℓ + 1), w k * K k.val s) : Prop := dqiExpectation inst P
      = (m : ℝ) * (r : ℝ) / (p : ℝ)
        + Real.sqrt ((r : ℝ) * ((p : ℝ) - (r : ℝ))) / (p : ℝ)
          * (w ⬝ᵥ (tridiagA m ℓ (semicircleD (r : ℝ) (p : ℝ))).mulVec w)

end Qatlib.Papers.DQIQuadOpt25.MainResults
