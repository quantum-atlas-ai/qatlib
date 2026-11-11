/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis12.MainResults.SourceTheorem9Corollary2

set_option backward.isDefEq.respectTransparency false

/-!
# GraphCollis12 — Lemma 7 (span program for the `deg(S) ≤ k` promise)

Fixed source: arXiv:1204.1527v1, §3, Lemma 7 (p.5):

> Lemma 7. Let `G` be a graph on `n` vertices and `k ∈ ℕ`, and consider the graph
> collision problem on `G` promised that the marked set `S` satisfies `deg(S) ≤ k`.
> (i) There is a span program for this promise problem with witness size at most
>     `√(2(n+k))`.
> (ii) There is a quantum algorithm with two-sided error at most `1/6` and query
>      complexity `O(√n + √k)`.

The construction (p.5): `H = ℂ^{{0,1}ⁿ}`, `|t⟩ = γ Σ_{z∈{0,1}ⁿ} |z⟩` with
`γ = ((n+k)/2)^{1/4}`, and `V_j⁰ = ∅`, `V_j¹ = {|s_j⁰⟩} ∪ {|s_i¹⟩ : i ∈ N(j)}`,
where `|s_jᵇ⟩ = Σ_{z : z_j = b} |z⟩`.  Witnesses:
* `x ∈ f⁻¹(1)`: an edge `ij` with `x_i=x_j=1`, `|t⟩ = γ|s_j⁰⟩ + γ|s_j¹⟩` (the two
  available vectors `|s_j⁰⟩ ∈ V_j¹`, `|s_j¹⟩ ∈ V_i¹`), cost `2γ² = √(2(n+k))`;
* `x ∈ f⁻¹(0)`: `|w'⟩ = |x⟩/γ`, orthogonal to `V_j^{x_j}` (independence of `S`),
  cost `(n - |S| + deg(S))/γ² ≤ (n+k)/γ² = √(2(n+k))`.

This file fixes the vector space, the span program, the witness predicates and the
witness-size statement.  The witness-size core `lemma7_witness_size` is registered
as a `Prop`-valued definition; mechanising the two computations above is a
substantive gap.  The query-complexity step (ii) is reduced to Reichardt's
Theorem 4 (paper Theorem 4) through the fully proved arithmetic lemma
`lemma7_query_from_witness`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Qatlib.Concepts.GraphQuery.EdgeQuery

namespace Qatlib.Papers.GraphCollis12.MainResults

/-- The Hilbert space `H = ℂ^{{0,1}ⁿ}` (paper p.5). -/
abbrev Vec (n : ℕ) := (Fin n → Bool) → ℂ

/-- `|s_jᵇ⟩ = Σ_{z : z j = b} |z⟩` (paper p.5). -/
def sVec {n : ℕ} (j : Fin n) (b : Bool) : Vec n :=
  fun z => if z j = b then 1 else 0

/-- `|t⟩ = γ Σ_z |z⟩` (paper p.5). -/
def tVec {n : ℕ} (γ : ℝ) : Vec n :=
  fun _ => (γ : ℂ)

/-- `γ = ((n+k)/2)^{1/4}` (paper p.5), written as a nested square root. -/
def gcGamma (n k : ℕ) : ℝ := Real.sqrt (Real.sqrt ((n + k : ℝ) / 2))

/-- The index set of `V_jᵇ`: empty for `b = 0`, and for `b = 1` the vector
`|s_j⁰⟩` together with `|s_i¹⟩` for each neighbour `i` of `j`. -/
def gcIdx {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) : Bool → Type
  | false => PEmpty
  | true => Unit ⊕ { i : Fin n // G.Adj j i }

/-- The vector at each index of `V_jᵇ`. -/
def gcVec {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    (b : Bool) → gcIdx G j b → Vec n
  | false, a => nomatch a
  | true, Sum.inl _ => sVec j false
  | true, Sum.inr p => sVec p.1 true

/-- `Fintype` for the index sets `V_jᵇ`. -/
instance gcIdxFintype {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) (b : Bool) :
    Fintype (gcIdx G j b) := by
  cases b
  · show Fintype PEmpty
    infer_instance
  · show Fintype (Unit ⊕ { i : Fin n // G.Adj j i })
    classical infer_instance

/-- A span program `(H, |t⟩; V_jᵇ)` in the sense of Definition 2 (p.3). -/
structure GCProgram (n : ℕ) where
  /-- the target vector `|t⟩`. -/
  target : Vec n
  /-- the index set of `V_jᵇ`. -/
  idx : Fin n → Bool → Type
  /-- `V_jᵇ` is finite. -/
  finIdx : ∀ j b, Fintype (idx j b)
  /-- the vector attached to each index of `V_jᵇ`. -/
  vec : ∀ (j : Fin n) (b : Bool), idx j b → Vec n

attribute [instance] GCProgram.finIdx

/-- The explicit Lemma 7 span program (paper p.5). -/
def gcProgram {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : GCProgram n :=
  { target := tVec (gcGamma n k)
    idx := gcIdx G
    finIdx := fun j b => gcIdxFintype G j b
    vec := gcVec G }

/-- Hilbert inner product `⟨v | w⟩ = Σ_z conj(v z) · w z`. -/
def inner {n : ℕ} (v w : Vec n) : ℂ :=
  ∑ z : Fin n → Bool, star (v z) * w z

/-- Positive witness of Definition 3 (p.3): `(c_j)` with
`|t⟩ = Σ_j Σ_{v ∈ V_j^{x_j}} c_j(v) |v⟩`. -/
def IsPosWitness {n : ℕ} (P : GCProgram n) (x : Fin n → Bool)
    (c : ∀ j : Fin n, P.idx j (x j) → ℂ) : Prop :=
  ∀ z, P.target z = ∑ j, ∑ a, c j a * P.vec j (x j) a z

/-- Positive witness size `Σ_j Σ_{v ∈ V_j^{x_j}} |c_j(v)|²`. -/
def posCost {n : ℕ} (P : GCProgram n) (x : Fin n → Bool)
    (c : ∀ j : Fin n, P.idx j (x j) → ℂ) : ℝ :=
  ∑ j, ∑ a, ‖c j a‖ ^ 2

/-- Negative witness of Definition 3 (p.3): `⟨t|w'⟩ = 1` and `⟨v|w'⟩ = 0` for
every `|v⟩ ∈ V_j^{x_j}`. -/
def IsNegWitness {n : ℕ} (P : GCProgram n) (x : Fin n → Bool) (w : Vec n) : Prop :=
  inner P.target w = 1 ∧ ∀ (j : Fin n) (b : Bool) (a : P.idx j b),
    x j = b → inner (P.vec j b a) w = 0

/-- Negative witness size `Σ_{j,b} Σ_{v ∈ V_jᵇ} |⟨v|w'⟩|²`. -/
def negCost {n : ℕ} (P : GCProgram n) (w : Vec n) : ℝ :=
  ∑ j, ∑ b : Bool, ∑ a : P.idx j b, ‖inner (P.vec j b a) w‖ ^ 2

/-- The span program `P` has witness size at most `B`: on every input of the
promise problem it has a positive/negative witness of cost at most `B`
(Definition 3, p.3). -/
def WitnessSizeAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (P : GCProgram n) (B : ℝ) : Prop :=
  (∀ x : Fin n → Bool, graphCollision (adjOf G) x = true →
      ∃ c : ∀ j : Fin n, P.idx j (x j) → ℂ, IsPosWitness P x c ∧ posCost P x c ≤ B) ∧
  (∀ x : Fin n → Bool, graphCollision (adjOf G) x = false →
      ∃ w : Vec n, IsNegWitness P x w ∧ negCost P w ≤ B)

/-! ### The numeric identities `2γ² = (n+k)/γ² = √(2(n+k))` -/

/-- `γ² = √((n+k)/2)`. -/
theorem gcGamma_sq (n k : ℕ) :
    (gcGamma n k) ^ 2 = Real.sqrt ((n + k : ℝ) / 2) := by
  unfold gcGamma
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]

/-- `2γ² = √(2(n+k))`: the positive-witness cost. -/
theorem two_mul_gcGamma_sq (n k : ℕ) :
    2 * (gcGamma n k) ^ 2 = Real.sqrt (2 * ((n + k : ℕ) : ℝ)) := by
  rw [gcGamma_sq]
  have h4 : Real.sqrt 4 = 2 := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ 4 by norm_num)
    have hnn := Real.sqrt_nonneg 4
    nlinarith
  have hsq : Real.sqrt (2 * ((n + k : ℕ) : ℝ)) = 2 * Real.sqrt (((n + k : ℕ) : ℝ) / 2) := by
    have h2 : 2 * ((n + k : ℕ) : ℝ) = 4 * (((n + k : ℕ) : ℝ) / 2) := by ring
    rw [h2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (((n + k : ℕ) : ℝ) / 2), h4]
  rw [hsq, show ((n : ℝ) + (k : ℝ)) / 2 = ((n + k : ℕ) : ℝ) / 2 from by push_cast; ring]

/-- `(n+k)/γ² = √(2(n+k))`: the negative-witness cost at the extreme point. -/
theorem div_gcGamma_sq (n k : ℕ) (hnk : 0 < n + k) :
    ((n + k : ℕ) : ℝ) / (gcGamma n k) ^ 2 = Real.sqrt (2 * ((n + k : ℕ) : ℝ)) := by
  set A : ℝ := ((n + k : ℕ) : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact_mod_cast hnk
  have hBpos : 0 < A / 2 := by positivity
  have hsqG : (gcGamma n k) ^ 2 = Real.sqrt (A / 2) := by
    rw [gcGamma_sq]
    congr 1
    rw [hAdef]
    push_cast
    ring
  have hsqrtA2 : Real.sqrt A = Real.sqrt 2 * Real.sqrt (A / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsqrt2A : Real.sqrt (2 * A) = Real.sqrt 2 * Real.sqrt A :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) A
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt2A' : Real.sqrt (2 * A) = 2 * Real.sqrt (A / 2) := by
    rw [hsqrt2A, hsqrtA2]
    have hre : Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt (A / 2))
        = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt (A / 2) := by ring
    rw [hre, h2]
  rw [hsqG, hsqrt2A']
  rw [div_eq_iff (Real.sqrt_pos.mpr hBpos).ne']
  have hsqB : Real.sqrt (A / 2) * Real.sqrt (A / 2) = A / 2 := Real.mul_self_sqrt hBpos.le
  nlinarith [hsqB]

/-- **Lemma 7(i)+(ii) witness-size core** (arXiv:1204.1527v1, §3 p.5).  On the
promise `deg(S) ≤ k`, the explicit span program `gcProgram G k` has witness size at
most `√(2(n+k))`.

Reconstruction of the paper's proof (p.5):
* `x` true: pick an edge `ij` with `x_i = x_j = 1`; the witness
  `γ|s_j⁰⟩ + γ|s_j¹⟩` (as coefficients `γ` on `V_j¹`'s `|s_j⁰⟩` and `V_i¹`'s
  `|s_j¹⟩`) has cost `2γ² = √(2(n+k))` (`two_mul_gcGamma_sq`);
* `x` false: the marked set is independent; `|w'⟩ = |x⟩/γ` is orthogonal to every
  `V_j^{x_j}` and has cost `(n - |S| + deg(S))/γ² ≤ (n+k)/γ² = √(2(n+k))`
  (`div_gcGamma_sq`), using `deg(S) ≤ k` and `|S| ≥ 0`.

**Status: statement registered as a `Prop`-valued definition; the proof is a
substantive gap.**  The two sum decompositions over the function space
`(Fin n → Bool) → ℂ` (the evaluation of `Σ_z sVec _ _ z`) and the double-counting
identity `Σ_j Σ_{i ∈ N(j)} [x i = 1] = Σ_{i ∈ S} deg(i) = degSum G S` are not yet
mechanised; the combinatorial/numeric parts are `two_mul_gcGamma_sq` and
`div_gcGamma_sq`.  Candidate reuse: `Fintype.sum_eq_single`, `Finset.sum_comm`,
`SimpleGraph.sum_degrees_eq_twice_card_edges`.  Suggested next tactics: build the
`γ`-coefficient family, then `Finset.sum_eq_single` twice for the positive case;
for the negative case `Finset.sum_comm` after rewriting `inner (sVec i true) w`,
then `Finset.sum_congr` over `markedSet`. -/
def lemma7_witness_size {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  WitnessSizeAtMost G (gcProgram G k) (Real.sqrt (2 * ((n + k : ℕ) : ℝ)))

/-- **Lemma 7(ii)** query-complexity arithmetic (p.5): Reichardt's Theorem 4
(paper Theorem 4) gives `q ≤ cR · wsize`, and `wsize ≤ √(2(n+k)) ≤ √2(√n+√k)`;
hence `q = O(√n + √k)`.  Fully proved. -/
theorem lemma7_query_from_witness {n : ℕ} (q cR : ℝ) (k : ℕ) (hcR : 0 < cR)
    (hq : q ≤ cR * Real.sqrt (2 * ((n + k : ℕ) : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ q ≤ C * (Real.sqrt (n : ℝ) + Real.sqrt (k : ℝ)) := by
  refine ⟨cR * Real.sqrt 2, by positivity, ?_⟩
  refine le_trans hq ?_
  have hnk : ((n + k : ℕ) : ℝ) ≤ (n : ℝ) + (k : ℝ) := by push_cast; linarith
  have hsqrt : Real.sqrt (2 * ((n + k : ℕ) : ℝ)) ≤
      Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (k : ℝ)) := by
    refine le_trans (Real.sqrt_le_sqrt (by linarith : 2 * ((n + k : ℕ) : ℝ) ≤
      2 * ((n : ℝ) + (k : ℝ)))) ?_
    have hsplit : Real.sqrt (2 * ((n : ℝ) + (k : ℝ))) ≤
        Real.sqrt (2 * (n : ℝ)) + Real.sqrt (2 * (k : ℝ)) := by
      have hx' : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
      have hy' : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
      have hsq : 2 * ((n : ℝ) + (k : ℝ)) ≤
          (Real.sqrt (2 * (n : ℝ)) + Real.sqrt (2 * (k : ℝ))) ^ 2 := by
        rw [add_sq, Real.sq_sqrt hx', Real.sq_sqrt hy']
        nlinarith [Real.sqrt_nonneg (2 * (n : ℝ)), Real.sqrt_nonneg (2 * (k : ℝ))]
      have hsum_nn : (0 : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + Real.sqrt (2 * (k : ℝ)) := by
        positivity
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hsum_nn] at h
    refine le_trans hsplit ?_
    rw [show Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) from
        Real.sqrt_mul (by norm_num) _,
      show Real.sqrt (2 * (k : ℝ)) = Real.sqrt 2 * Real.sqrt (k : ℝ) from
        Real.sqrt_mul (by norm_num) _]
    have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (k : ℝ)]
  calc cR * Real.sqrt (2 * ((n + k : ℕ) : ℝ))
      ≤ cR * (Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (k : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hsqrt (le_of_lt hcR)
    _ = cR * Real.sqrt 2 * (Real.sqrt (n : ℝ) + Real.sqrt (k : ℝ)) := by ring

end Qatlib.Papers.GraphCollis12.MainResults
