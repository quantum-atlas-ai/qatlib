/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DQIOptim24.MainResults.Source.Definitions
public import Qatlib.Concepts.CodingDecoding.DecoderCapacity.Basic
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section


set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIOptim24.MainResults

open Qatlib.Papers.DQIOptim24.MainResults.Source

/-- The Hadamard (QFT over `𝔽₂^n`) transform of a syndrome-basis state,
equation (140). -/
noncomputable def hadamardState {n : ℕ} (psi : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  fun x => ∑ y, sign2C (dot2 x y) * psi y

/-- The expected objective value `⟨f⟩` of the imperfect DQI state `|P_D(f)⟩` of
equation (171), measured in the computational basis. -/
noncomputable def imperfectExpected {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (v : Fin m → ZMod 2)
    {L : ℕ} (w : Fin (L + 1) → ℝ) : ℝ :=
  (∑ x : Fin n → ZMod 2, xorsatObjective B v x *
      Complex.normSq (hadamardState (imperfectState B decode v (L := L) w) x)) /
    (∑ x : Fin n → ZMod 2,
      Complex.normSq (hadamardState (imperfectState B decode v (L := L) w) x))

/-- Pointwise, the syndrome `Bᵀ y` agrees with the linear-map packaging
`syndromeLin B` used by the Frozen decoder-capacity statements. -/
theorem syndrome_eq_syndromeLin {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (y : Fin m → ZMod 2) : syndrome B y = syndromeLin B y := rfl

/-- Bridge, part 1 (paper Lemma 10.4 prerequisite, page 40): a
single-valued decoder cannot correctly recover two distinct errors with the same
syndrome, so the syndrome map is injective on `D_k`, the set of errors the
decoder recovers on the weight-`k` shell.  This is Frozen
`DecoderCapacity.correctErrors_injective` transported to `decodedShell`. -/
theorem decodedShell_syndrome_injective
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) :
    Set.InjOn (fun y => syndrome B y) (decodedShell B decode k) := by
  have h := Qatlib.Concepts.CodingDecoding.DecoderCapacity.correctErrors_injective
    (syndrome B) decode (shell (ZMod 2) m k)
  simpa [decodedShell,
    Qatlib.Concepts.CodingDecoding.DecoderCapacity.correctErrors] using h

/-- Bridge, part 2 (paper Lemma 10.4 prerequisite, page 40): the number of
errors recovered by an actual decoder on a shell is at most the size of the
syndrome image, `q ^ rank(Bᵀ)` with `q = 2`.  This is Frozen
`DecoderCapacity.decoder_capacity` transported to `decodedShell`. -/
theorem decodedShell_card_le_decoder_capacity
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) :
    (decodedShell B decode k).card ≤
      Fintype.card (ZMod 2) ^
        Module.finrank (ZMod 2) (LinearMap.range (syndromeLin B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Qatlib.Concepts.CodingDecoding.DecoderCapacity.decoder_capacity
    (ZMod 2) (Fin m) (Fin n) (syndromeLin B) decode (shell (ZMod 2) m k)
  have heq : decodedShell B decode k =
      Qatlib.Concepts.CodingDecoding.DecoderCapacity.correctErrors
        (syndromeLin B) decode (shell (ZMod 2) m k) := by
    simp only [decodedShell,
      Qatlib.Concepts.CodingDecoding.DecoderCapacity.correctErrors]
    refine Finset.filter_congr ?_
    intro y _
    rw [syndrome_eq_syndromeLin]
  rw [heq]
  exact h

/-- The satisfied-clause fraction of the imperfect DQI state, averaged over a
uniform `v`: since `s = (m + f)/2` for a max-XORSAT objective `f`, dividing by
`m` gives `(m + E_v ⟨f⟩) / (2m)`. -/
noncomputable def imperfectSatisfiedFraction {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) {L : ℕ}
    (w : Fin (L + 1) → ℝ) : ℝ :=
  (((m : ℝ) +
      (∑ v : Fin m → ZMod 2, imperfectExpected B decode v (L := L) w) /
        (Fintype.card (Fin m → ZMod 2) : ℝ)) / 2) / (m : ℝ)

/-- The best satisfied-clause fraction that DQI with a classical decoder
achieves on the instance `B`, ranging over the polynomial degree `ℓ`, the
decoder and the weight vector. -/
noncomputable def bestImperfectFraction {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) : ℝ :=
  sSup {f : ℝ | ∃ (L : ℕ) (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2))
      (w : Fin (L + 1) → ℝ), f = imperfectSatisfiedFraction B decode w}

/-- The `q`-ary analogue of the finite-size expectation of Lemma 9.2:
`q (m r / q + (√(r(q-r))/q) · wᵀ A^(q) w)` with `A^(q)` the tridiagonal matrix of
equation (268). -/
noncomputable def gprExpectedObjective (q m r L : ℕ) (w : Fin (L + 1) → ℝ) : ℝ :=
  (q : ℝ) * ((m : ℝ) * (r : ℝ) / (q : ℝ) +
    Real.sqrt ((r : ℝ) * ((q : ℝ) - (r : ℝ))) / (q : ℝ) *
      quadForm (tridiagonalQ ((q : ℝ) ^ m) L (dOfQR q m r)) w)

/-- Theorem 15.4 (page 68), equation (267).  Suppose an efficient algorithm
decodes `C⊥ = RM_q(u⊥, m)` out to `ℓ` errors and `2ℓ + 1 < d⊥`.  Then for a
`GPR(r, u, m, q)` instance DQI produces, in polynomial time, samples whose
expected objective value is

`q (m r / q + (√(r(q-r))/q) · λ_max^(q))`,

where `λ_max^(q)` is the largest eigenvalue of the tridiagonal matrix of
equation (268).  The Lean statement makes the last step explicit: when `w` is a
unit eigenvector of `A^(q)` with eigenvalue `lam`, the q-ary quadratic form
equals `lam`, so the finite-size expectation takes the displayed value.

Paper version: arXiv:2408.08292v5.  The eigenvalue substitution
`wᵀA^(q)w = λ_max` is proved here; the GPR/Reed–Muller code semantics and the
`2ℓ + 1 < d⊥` decoding hypothesis are the model interface of the paper and are
not rebuilt. -/
theorem theorem154_reed_muller_fraction
    (q r m L : ℕ) (_hq : 2 ≤ q) (_hr1 : 1 ≤ r) (_hrq : r < q) (_hL : L ≤ m / 2)
    (w : Fin (L + 1) → ℝ) (hw : ∑ k : Fin (L + 1), (w k) ^ 2 = 1)
    (lam : ℝ)
    (heig : Matrix.mulVec (tridiagonalQ ((q : ℝ) ^ m) L (dOfQR q m r)) w = lam • w) :
    gprExpectedObjective q m r L w =
      (q : ℝ) * ((m : ℝ) * (r : ℝ) / (q : ℝ) +
        Real.sqrt ((r : ℝ) * ((q : ℝ) - (r : ℝ))) / (q : ℝ) * lam) := by
  have hrow : ∀ k : Fin (L + 1),
      (∑ k' : Fin (L + 1),
        tridiagonalQ ((q : ℝ) ^ m) L (dOfQR q m r) k k' * w k') = lam * w k := by
    intro k
    have hk := congrFun heig k
    simpa [Matrix.mulVec, dotProduct] using hk
  have hquad : quadForm (tridiagonalQ ((q : ℝ) ^ m) L (dOfQR q m r)) w = lam := by
    unfold quadForm
    calc
      ∑ k : Fin (L + 1),
          w k * ∑ k' : Fin (L + 1),
            tridiagonalQ ((q : ℝ) ^ m) L (dOfQR q m r) k k' * w k'
          = ∑ k : Fin (L + 1), w k * (lam * w k) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [hrow k]
      _ = lam * ∑ k : Fin (L + 1), (w k) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
      _ = lam := by rw [hw, mul_one]
  unfold gprExpectedObjective
  rw [hquad]

/-- The three recorded satisfaction fractions of Table 1 (page 55), exactly as
encoded: DQI+BP `0.831`, simulated annealing at 8 s `0.764`, tailored classical
algorithm `0.88`. -/
theorem table1_recorded_values :
    tableDQIBP = 831 / 1000 ∧ tableSA8s = 764 / 1000 ∧ tableTailored = 88 / 100 := by
  refine ⟨rfl, rfl, rfl⟩

/-- §12 Table 1 comparison: simulated annealing at 8 s satisfies strictly fewer
constraints than DQI + belief propagation, while the tailored classical algorithm
satisfies strictly more.  This is the full content of the displayed comparison;
no statement is made about classical lower bounds. -/
theorem table1_classical_comparison :
    tableSA8s < tableDQIBP ∧ tableDQIBP < tableTailored := by
  constructor <;> norm_num [tableSA8s, tableDQIBP, tableTailored]

/-- Remark 5.2 boundary (page 13): the table separates the observed qualities
`0.764 < 0.831 < 0.88`; the middle value is the DQI + belief-propagation point,
so the tailored classical algorithm is better on this instance and simulated
annealing at 8 s is worse. -/
theorem table1_window :
    tableSA8s < tableDQIBP ∧ tableDQIBP < tableTailored ∧ tableDQIBP < 1 := by
  refine ⟨table1_classical_comparison.1, table1_classical_comparison.2, ?_⟩
  norm_num [tableDQIBP]

end Qatlib.Papers.DQIOptim24.MainResults
