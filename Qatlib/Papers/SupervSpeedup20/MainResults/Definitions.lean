/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime

set_option backward.isDefEq.respectTransparency false

/-!
# SupervSpeedup20 — source model for the supervised-learning speed-up paper

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020),
*"A rigorous and robust quantum speed-up in supervised machine learning"*.

This file fixes the paper-layer vocabulary used by the per-claim files in
`QuantumAlgorithmDev.Papers.SupervSpeedup20.MainResults`:

* `DlogWorld` — the multiplicative group `Z_p^*` of a fixed prime `p` with a
  chosen generator `g`, presented through the discrete-log equivalence
  `X ≃ ZMod (p-1)` (Section 2 of the paper; the equivalence exists exactly
  because `g` is a generator of the cyclic group).
* the concept class `C = {f_s}_{s ∈ Z_p^*}` of Definition 6 / Eq. (D8):
  `f_s` is `+1` on the cyclic interval `[s, s + (p-3)/2]` in log-coordinates;
* the quantum feature states `|φ(x)⟩` of Eq. (D9) and the halfspace state
  `|φ_s⟩` of Eq. (D10), represented as real coefficient vectors over the
  discrete-log index set; their Hilbert–Schmidt inner product is the
  overlap-squared quantity of Lemma 13;
* the SVM-QKE learning interface of Appendix C (a learner that receives a
  training set and measurement noise and returns a Boolean classifier);
* finite probability laws (`FinLaw`) used for the training-set and
  measurement-noise expectations of Lemmas 17–19 and Theorem 22.

The model is source-level: it states the mathematical objects the paper works
with and does not claim to implement the classical/quantum machines of
Appendices B–E.  Deep external results (Blum–Micali, Shor, the perturbation
bound Lemma 16 of [46], the fat-shattering bound Lemma 24 of [33]) are left to
the per-claim files with explicit `sorry` audits.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset
open scoped BigOperators Classical

/-! ## The discrete-log world and the concept class -/

/-- A fixed discrete-log world: the multiplicative group `Z_p^*` presented as a
finite type `X` together with the discrete-log equivalence to `ZMod N`,
`N = p - 1`.

The equivalence is the paper's notation `log_g`: it exists because the fixed
`g ∈ Z_p^*` is a generator of the cyclic group (Section 2).  All statements
below quantify over such a world, exactly as the paper fixes `(p, g)` and then
works with `Z_p^*`. -/
structure DlogWorld where
  /-- The prime modulus. -/
  p : ℕ
  /-- The group order `p - 1`. -/
  N : ℕ
  hp : p.Prime
  /-- `p` is an odd prime, so `(p-1)/2 ≥ 1`. -/
  h2 : 2 < p
  hN : N = p - 1
  /-- Carrier of the multiplicative group `Z_p^*`. -/
  X : Type
  instFintype : Fintype X
  instDecEq : DecidableEq X
  hNpos : 0 < N
  /-- Discrete logarithm to `ZMod N`; `logEquiv.symm y = g ^ y`. -/
  logEquiv : X ≃ ZMod N

attribute [instance] DlogWorld.instFintype DlogWorld.instDecEq

namespace DlogWorld

variable (W : DlogWorld)

/-- The order `N = p - 1` is nonzero, so `ZMod N` is a finite type. -/
instance instNeZeroN : NeZero W.N := ⟨Nat.pos_iff_ne_zero.mp W.hNpos⟩

/-- The carrier has exactly `N = p - 1` elements. -/
theorem card_X : Fintype.card W.X = W.N :=
  (Fintype.card_congr W.logEquiv).trans (ZMod.card W.N)

/-- The uniform mass `1/|Z_p^*| = 1/N`. -/
def uniformMass : ℝ := (W.N : ℝ)⁻¹

/-- The uniform mass `1/N` is positive. -/
theorem uniformMass_pos : 0 < W.uniformMass := by
  rw [uniformMass]
  exact inv_pos.mpr (by exact_mod_cast W.hNpos)

/-- `(p-1)/2 ≥ 1` for the odd prime `p`. -/
theorem N_div_two_pos : 0 < W.N / 2 := by
  have hp : 3 ≤ W.p := W.h2
  have h2le : 2 ≤ W.p - 1 := by omega
  rw [W.hN]
  exact Nat.div_pos h2le (by norm_num)

/-- The concept interval length `(p-1)/2` is at most `N`. -/
theorem half_le_N : W.N / 2 ≤ W.N := Nat.div_le_self _ _

end DlogWorld

/-! ## Cyclic intervals and the concept class -/

/-- The cyclic interval `{s, s+1, …, s+len-1}` in `ZMod N`
(used for both the concept half-space and the feature-state support). -/
def cyclicInterval (N : ℕ) (s : ZMod N) (len : ℕ) : Finset (ZMod N) :=
  (Finset.range len).image (fun (i : ℕ) => s + (i : ZMod N))

/-- Membership in a cyclic interval: `u = s + i` for some offset `i < len`. -/
theorem mem_cyclicInterval {N : ℕ} {s u : ZMod N} {len : ℕ} :
    u ∈ cyclicInterval N s len ↔ ∃ i, i < len ∧ u = s + (i : ZMod N) := by
  rw [cyclicInterval, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- A cyclic interval of length at most `N` has exactly `len` elements. -/
theorem cyclicInterval_card {N : ℕ} [NeZero N] {s : ZMod N} {len : ℕ}
    (hlen : len ≤ N) : (cyclicInterval N s len).card = len := by
  have hinj : Set.InjOn (fun i : ℕ => s + (i : ZMod N)) ↑(Finset.range len) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    have hmod : (i : ZMod N) = (j : ZMod N) := add_left_cancel hij
    have hval := congrArg ZMod.val hmod
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hlen),
      Nat.mod_eq_of_lt (lt_of_lt_of_le hj hlen)] at hval
    exact hval
  rw [cyclicInterval]
  exact (Finset.card_image_of_injOn hinj).trans (Finset.card_range len)

namespace DlogWorld

/-- Definition 6 / Eq. (D8): the concept `f_s` is `+1` exactly on the cyclic
half-interval `[s, s + (p-3)/2]`, i.e. on a set of `(p-1)/2 = N/2` log-values. -/
def conceptClass (W : DlogWorld) (s : ZMod W.N) : W.X → Bool :=
  fun x => decide (W.logEquiv x ∈ cyclicInterval W.N s (W.N / 2))

end DlogWorld

/-- The paper's label `y ∈ {-1, +1}` associated with a Boolean label. -/
def labelOf (b : Bool) : ℝ := if b then 1 else -1

/-- The paper's `±1` label squares to one. -/
theorem labelOf_sq (b : Bool) : labelOf b ^ 2 = 1 := by
  cases b <;> simp [labelOf]

/-! ## Finite probability laws -/

/-- A finite probability law `prob : Ω → ℝ` with nonnegative masses summing
to one.  The paper's training-set and measurement-noise laws are finite. -/
structure FinLaw (Ω : Type) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  sum_one : (∑ ω, prob ω) = 1

namespace FinLaw

variable {Ω : Type} [Fintype Ω]

/-- Probability of an event. -/
def probOf (L : FinLaw Ω) (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ∑ ω ∈ Finset.univ.filter P, L.prob ω

/-- Expectation of a real function. -/
def expect (L : FinLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, L.prob ω * f ω

/-- Probabilities of events are nonnegative. -/
theorem probOf_nonneg (L : FinLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    0 ≤ L.probOf P :=
  Finset.sum_nonneg fun ω _ => L.nonneg ω

/-- complement rule: `Pr[P] + Pr[¬P] = 1`. -/
theorem probOf_add_compl (L : FinLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    L.probOf P + L.probOf (fun ω => ¬ P ω) = 1 := by
  rw [probOf, probOf, Finset.sum_filter_add_sum_filter_not Finset.univ P L.prob]
  exact L.sum_one

/-- Monotonicity of expectation. -/
theorem expect_mono (L : FinLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    L.expect f ≤ L.expect g := by
  simp only [expect]
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (L.nonneg ω)

/-- Expectation of a constant. -/
theorem expect_const (L : FinLaw Ω) (c : ℝ) : L.expect (fun _ => c) = c := by
  simp only [expect]
  calc ∑ x, L.prob x * c = (∑ x, L.prob x) * c :=
        (Finset.sum_mul Finset.univ L.prob c).symm
    _ = c := by rw [L.sum_one, one_mul]

/-- A constant is pulled out of an expectation. -/
theorem expect_const_mul (L : FinLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    L.expect (fun ω => c * f ω) = c * L.expect f := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- Additivity of expectation. -/
theorem expect_add (L : FinLaw Ω) (f g : Ω → ℝ) :
    L.expect (fun ω => f ω + g ω) = L.expect f + L.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

/-- Expectation of a finite sum is the sum of expectations. -/
theorem expect_sum {ι : Type} (L : FinLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    L.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, L.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The expectation of the indicator of `P` is `Pr[P]`. -/
theorem expect_indicator (L : FinLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    L.expect (fun ω => if P ω then (1 : ℝ) else 0) = L.probOf P := by
  unfold expect probOf
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by by_cases h : P x <;> simp [h]

end FinLaw

/-- The uniform law on a nonempty finite type. -/
def uniformFinLaw (Ω : Type) [Fintype Ω] [Nonempty Ω] : FinLaw Ω where
  prob _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

namespace DlogWorld

variable (W : DlogWorld)

/-- The uniform distribution on `Z_p^*` (paper: `x ∼ U(Z_p^*)`). -/
def uniformLaw : FinLaw W.X where
  prob _ := W.uniformMass
  nonneg _ := W.uniformMass_pos.le
  sum_one := by
    rw [uniformMass, Finset.sum_const, Finset.card_univ, W.card_X, nsmul_eq_mul]
    have hN : (W.N : ℝ) ≠ 0 := by exact_mod_cast W.hNpos.ne'
    field_simp

/-- The uniform law assigns mass `1/N` to every group element. -/
theorem uniformLaw_prob (x : W.X) : W.uniformLaw.prob x = W.uniformMass := rfl

/-- Probability of an event under `x ∼ U(Z_p^*)`. -/
def PrUniform (P : W.X → Prop) [DecidablePred P] : ℝ :=
  W.uniformLaw.probOf P

/-- The uniform probability of the universal event is one. -/
theorem PrUniform_univ : W.PrUniform (fun _ => True) = 1 := by
  unfold PrUniform FinLaw.probOf
  rw [Finset.filter_true]
  exact W.uniformLaw.sum_one

end DlogWorld

/-! ## Feature vectors and the overlap computation of Lemma 13 -/

namespace DlogWorld

variable (W : DlogWorld)

/-- Euclidean inner product on the log-index space `ZMod N`. -/
def euclidInner (u v : ZMod W.N → ℝ) : ℝ := ∑ z, u z * v z

/-- The feature state `|φ(x)⟩` of Eq. (D9), written in log-coordinates
`t = log_g x`: the uniform superposition over the cyclic interval
`[t, t + 2^k)`, with coefficient `1/√(2^k)`. -/
def phiVec (k : ℕ) (t : ZMod W.N) : ZMod W.N → ℝ :=
  fun u => if u ∈ cyclicInterval W.N t (2 ^ k) then (Real.sqrt ((2 ^ k : ℕ) : ℝ))⁻¹ else 0

/-- The halfspace state `|φ_s⟩` of Eq. (D10): the uniform superposition over
the concept half-interval `[s, s + (N-1)/2]`, coefficient `1/√((p-1)/2)`. -/
def halfVec (s : ZMod W.N) : ZMod W.N → ℝ :=
  fun u => if u ∈ cyclicInterval W.N s (W.N / 2)
    then (Real.sqrt ((W.N / 2 : ℕ) : ℝ))⁻¹ else 0

/-- `Δ = 2^k / ((p-1)/2)`: the squared overlap of a bulk feature state with
the halfspace state, Definition 10 / Lemma 13 of the paper. -/
def delta (k : ℕ) : ℝ := ((2 ^ k : ℕ) : ℝ) / ((W.N / 2 : ℕ) : ℝ)

/-- The rank-one operator `|v⟩⟨v|`. -/
def rankOne (v : ZMod W.N → ℝ) : Matrix (ZMod W.N) (ZMod W.N) ℝ :=
  fun i j => v i * v j

/-- Hilbert–Schmidt inner product `Tr(Aᵀ B)`; this is the Euclidean inner
product of the Pauli/Bloch coefficient vectors (the Pauli basis is
orthonormal with respect to it). -/
def hsInner (A B : Matrix (ZMod W.N) (ZMod W.N) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The Hilbert–Schmidt inner product of two rank-one operators is the square
of the coefficient-vector inner product. -/
theorem hsInner_rankOne (v w : ZMod W.N → ℝ) :
    W.hsInner (W.rankOne v) (W.rankOne w) = W.euclidInner v w ^ 2 := by
  simp only [hsInner, rankOne, euclidInner, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end DlogWorld

/-! ## The sampling algorithm of Lemma 7 -/

namespace DlogWorld

variable (W : DlogWorld)

/-- The data distribution of a concept `f`: `x` uniform on `Z_p^*`, label
`f x`.  This is a law on pairs `(x, f x)`. -/
def dataLaw (f : W.X → Bool) (z : W.X × Bool) : ℝ :=
  if z.2 = f z.1 then W.uniformMass else 0

/-- The classical sampling algorithm of Lemma 7 / Eq. (B2): draw a uniform
seed `y ∈ Z_N`, output `(g^y, f_s(g^y))`.  The label is computed from the
known seed `y` by the interval test, never by inverting the discrete log. -/
def sampleFromSeed (f : W.X → Bool) (y : ZMod W.N) : W.X × Bool :=
  (W.logEquiv.symm y, f (W.logEquiv.symm y))

/-- The push-forward of the uniform seed law under `sampleFromSeed`. -/
def pushforward (f : W.X → Bool) (z : W.X × Bool) : ℝ :=
  ∑ y : ZMod W.N, if sampleFromSeed W f y = z then (W.N : ℝ)⁻¹ else 0

/-- **Lemma 7, distribution identity (source p. 10, Eq. (B2)).**  The sampler
`y ↦ (g^y, f_s(g^y))` induces exactly the data distribution: uniformly
distributed `x ∈ Z_p^*` with the correct label. -/
theorem pushforward_eq_dataLaw (f : W.X → Bool) (z : W.X × Bool) :
    W.pushforward f z = W.dataLaw f z := by
  obtain ⟨x, b⟩ := z
  have key : ∀ y : ZMod W.N,
      (if sampleFromSeed W f y = (x, b) then (W.N : ℝ)⁻¹ else 0) =
      (if y = W.logEquiv x ∧ b = f x then (W.N : ℝ)⁻¹ else 0) := by
    intro y
    by_cases hy : y = W.logEquiv x
    · subst hy
      by_cases hb : b = f x
      · simp [sampleFromSeed, hb]
      · have hne : sampleFromSeed W f (W.logEquiv x) ≠ (x, b) := by
          intro h
          apply hb
          have h2 := congrArg Prod.snd h
          simpa [sampleFromSeed, W.logEquiv.symm_apply_apply] using h2.symm
        simp [hne, hb]
    · have hne : sampleFromSeed W f y ≠ (x, b) := by
        intro h
        apply hy
        have h1 : W.logEquiv.symm y = x := by
          simpa [sampleFromSeed] using congrArg Prod.fst h
        have := congrArg W.logEquiv h1
        simpa using this
      simp [hne, hy]
  rw [pushforward, Finset.sum_congr rfl (fun y _ => key y)]
  by_cases hb : b = f x
  · have hsum : (∑ y : ZMod W.N,
        (if y = W.logEquiv x ∧ b = f x then (W.N : ℝ)⁻¹ else 0)) = (W.N : ℝ)⁻¹ := by
      rw [Finset.sum_eq_single (W.logEquiv x)]
      · simp [hb]
      · intro y _ hy
        simp [hy]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    simp [dataLaw, hb, DlogWorld.uniformMass]
  · have hsum : (∑ y : ZMod W.N,
        (if y = W.logEquiv x ∧ b = f x then (W.N : ℝ)⁻¹ else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      simp [hb]
    rw [hsum]
    simp [dataLaw, hb]

/-- The classical sampling algorithm of Lemma 7, together with its polynomial
cost annotation.  `cost n` bounds the number of elementary group/interval
operations at security parameter `n = log₂ p`. -/
structure ClassicalSampler (f : W.X → Bool) where
  seed : Type
  instFintype : Fintype seed
  instDecEq : DecidableEq seed
  run : seed → W.X × Bool
  /-- The induced law is exactly the data distribution. -/
  hlaw : ∀ z, (∑ y : seed, if run y = z then (Fintype.card seed : ℝ)⁻¹ else 0) =
    dataLaw W f z
  cost : ℕ → ℕ
  /-- The sampler runs in polynomial time in the security parameter. -/
  hcost : ∃ c k, ∀ n, cost n ≤ c * n ^ k + c

attribute [instance] ClassicalSampler.instFintype ClassicalSampler.instDecEq

/-- **Lemma 7 (source p. 10).**  For every concept `f_s ∈ C` there is a
classical sampling algorithm, polynomial in the security parameter, that
generates samples `(x, f_s(x))` with `x` uniformly random in `Z_p^*`. -/
theorem exists_classical_sampler (s : ZMod W.N) :
    ∃ _S : W.ClassicalSampler (W.conceptClass s), True := by
  refine ⟨{
    seed := ZMod W.N
    instFintype := inferInstance
    instDecEq := inferInstance
    run := sampleFromSeed W (W.conceptClass s)
    hlaw := ?_
    cost := fun n => 2 * n + 2
    hcost := ⟨2, 1, fun n => by simp⟩ }, trivial⟩
  intro z
  simpa [pushforward, DlogWorld.uniformMass, ZMod.card] using
    pushforward_eq_dataLaw W (W.conceptClass s) z

end DlogWorld

/-! ## Learning algorithms, accuracy and hardness -/

namespace DlogWorld

variable (W : DlogWorld)

/-- A classical learner: maps a training set of `m` labelled examples to a
Boolean hypothesis on `Z_p^*`.  `runtime m` is the algorithm's operation
count on training sets of size `m`. -/
structure Learner where
  predict : (m : ℕ) → (Fin m → W.X × Bool) → W.X → Bool
  runtime : ℕ → ℕ
  hpoly : ∃ c k, ∀ n, runtime n ≤ c * n ^ k + c

/-- Test accuracy of a hypothesis `h` for concept `f`, under `x ∼ U(Z_p^*)`. -/
def testAccuracy (f : W.X → Bool) (h : W.X → Bool) : ℝ :=
  ((Finset.univ.filter (fun x => h x = f x)).card : ℝ) / (W.N : ℝ)

/-- Test accuracy is nonnegative. -/
theorem testAccuracy_nonneg (f h : W.X → Bool) : 0 ≤ W.testAccuracy f h := by
  unfold testAccuracy
  positivity

/-- Test accuracy is at most one. -/
theorem testAccuracy_le_one (f h : W.X → Bool) : W.testAccuracy f h ≤ 1 := by
  unfold testAccuracy
  have hc : ((Finset.univ.filter (fun x => h x = f x)).card : ℝ) ≤ (W.N : ℝ) := by
    rw [← W.card_X]
    exact_mod_cast Finset.card_le_univ _
  have hN : (0 : ℝ) < (W.N : ℝ) := by exact_mod_cast W.hNpos
  rw [div_le_one hN]
  exact hc

/-- Probability that a predicate holds for a uniformly drawn labelled training
set `S : Fin m → Z_p^* × {±1}` (each coordinate iid uniform on `Z_p^*` with the
concept label).  Written as the exact uniform ratio so that it is defined for
every `m`, including `m = 0`. -/
def trainProb (m : ℕ) (P : (Fin m → W.X × Bool) → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card (Fin m → W.X × Bool) : ℝ)

/-- A learner achieves test accuracy `acc` with probability at least `2/3`
over random training samples (Theorem 1/2/8/22's success guarantee). -/
def AchievesTestAccuracy (L : Learner W) (f : W.X → Bool) (acc : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m →
    (2 / 3 : ℝ) ≤ W.trainProb m (fun S => acc ≤ W.testAccuracy f (L.predict m S))

/-- A hypothesis-class-independent `1/poly` advantage over random guessing:
there are `c, k` with `acc = 1/2 + 1/m^k` achievable with probability `2/3`
for every training-set size `m`. -/
def AchievesPolyAdvantage (L : Learner W) (f : W.X → Bool) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, 0 < m →
    (2 / 3 : ℝ) ≤ W.trainProb m
      (fun S => (1 / 2 : ℝ) + 1 / (m : ℝ) ^ k ≤ W.testAccuracy f (L.predict m S))

/-- A natural-number function computed by a polynomial-time Post–Turing
machine on the binary encoding of its input (the library's `BitMachine*`
model, imported from `Concepts.ClassicalTape.TapeCompilation`). -/
def PolyComputes (f : ℕ → ℕ) : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (out : Turing.TM0.Cfg (Option Bool) (Fin 2) → ℕ),
    Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachinePolynomialTime machine ∧
      ∀ n : ℕ,
        ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
          Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineAfter machine
            ((List.range (n + 1)).map (fun i => some (n.testBit i))) t = some c ∧
            Turing.TM0.step machine c = none ∧ out c = f n

/-- A canonical numeric code for a group element (`Fintype.equivFin`). -/
def codeOf (x : W.X) : ℕ := (Fintype.equivFin W.X x).val

/-- The group element with a given numeric code. -/
def decodeCode (n : ℕ) : W.X :=
  if h : n < Fintype.card W.X then (Fintype.equivFin W.X).symm ⟨n, h⟩
  else W.logEquiv.symm 0

/-- `DLP(p, g)` is polynomial-time solvable in this world: some polynomial-time
classical machine on the code of `y` outputs `log_g y`. -/
def SolvesDLP (W : DlogWorld) : Prop :=
  PolyComputes (fun n => (W.logEquiv (W.decodeCode n)).val)

/-- The paper's hardness assumption: DLP is not solvable in classical
polynomial time (Section 2 and Appendix B). -/
def ClassicallyHardDLP (W : DlogWorld) : Prop := ¬ W.SolvesDLP

/-- The learning problem `C` is classically learnable with a `1/poly`
advantage: some polynomial-time classical learner achieves
`1/2 + 1/poly(n)` test accuracy on every concept of `C`, with probability at
least `2/3` over random training samples. -/
def ClassicallyLearnable : Prop :=
  ∃ L : Learner W, ∀ s : ZMod W.N, W.AchievesPolyAdvantage L (W.conceptClass s)

end DlogWorld

/-! ## The SVM-QKE interface -/

namespace DlogWorld

variable (W : DlogWorld)

/-- A (finite) classifier produced by SVM-QKE. -/
structure SVMClassifier where
  predict : W.X → Bool

/-- The SVM-QKE learning algorithm of Appendix C: it receives a training set
and the finite measurement-noise outcome, estimates the kernel entries with
`shots` measurements per entry, solves the dual SVM, and returns a
classifier. -/
structure SVMQKE where
  Ω : Type
  instFintype : Fintype Ω
  instDecEq : DecidableEq Ω
  instNonempty : Nonempty Ω
  noiseLaw : FinLaw Ω
  shots : ℕ → ℕ
  runtime : ℕ → ℕ
  hshots : ∃ c k, ∀ m, shots m ≤ c * m ^ k + c
  hruntime : ∃ c k, ∀ m, runtime m ≤ c * m ^ k + c
  learn : (m : ℕ) → (Fin m → W.X × Bool) → Ω → SVMClassifier W

attribute [instance] SVMQKE.instFintype SVMQKE.instDecEq

/-- Success probability of SVM-QKE, jointly over the uniform random training
set and the finite measurement-noise law. -/
def jointSuccessProb (A : SVMQKE W) (m : ℕ) (s : ZMod W.N) : ℝ :=
  ∑ S : Fin m → W.X,
    ∑ ω : A.Ω,
      (Fintype.card (Fin m → W.X) : ℝ)⁻¹ * A.noiseLaw.prob ω *
        (if (0.99 : ℝ) ≤ W.testAccuracy (W.conceptClass s)
              (A.learn m (fun i => (S i, W.conceptClass s (S i))) ω).predict
         then 1 else 0)

end DlogWorld

/-! ## Ground-truth hyperplane and slack variables (Definition 15, Lemma 17) -/

namespace DlogWorld

variable (W : DlogWorld)

/-- The Euclidean score `⟨w, x̂⟩` of a hyperplane `w` on the Pauli/feature
vector of `x` (Eq. (D11)–(D13)); `x` is overloaded to its feature vector. -/
def score (w : ZMod W.N → ℝ) (t : ZMod W.N) : ℝ := W.euclidInner w (W.phiVec 0 t)

/-- Signed margin `y⟨w, x̂⟩` for label `y`. -/
def signedScore (w : ZMod W.N → ℝ) (b : Bool) (t : ZMod W.N) : ℝ :=
  labelOf b * W.score w t

/-- Definition 15: the ground-truth hyperplane, with the two source
properties `Pr[y⟨w*,x⟩ ≥ 1] = 1 − Δ` and `|y⟨w*,x⟩| ≤ 1` for every `x`. -/
structure GroundTruthHyperplane (s : ZMod W.N) (Δ : ℝ) where
  w : ZMod W.N → ℝ
  hprob : W.PrUniform (fun x => 1 ≤ W.signedScore w (W.conceptClass s x) (W.logEquiv x))
    = 1 - Δ
  hbound : ∀ t, |W.signedScore w (W.conceptClass s (W.logEquiv.symm t)) t| ≤ 1

/-- The slack variable `ξ* = max{1 − y⟨w*,x⟩, 0}` of Eq. (D23). -/
def slackOf (w : ZMod W.N → ℝ) (b : Bool) (t : ZMod W.N) : ℝ :=
  max (1 - W.signedScore w b t) 0

end DlogWorld

/-! ## Noisy halfspace learning problem (Lemma 14) -/

namespace DlogWorld

variable (W : DlogWorld)

/-- The four properties of the noisy halfspace learning problem of Lemma 14.
`margin` is the paper's `Δ/√(8 + 2Δ²)`. -/
structure NoisyHalfspaceProblem where
  /-- Ambient dimension (`4^n + 1` in the paper). -/
  dim : ℕ
  /-- Data vectors. -/
  Y : Type
  instFintype : Fintype Y
  instDecEq : DecidableEq Y
  vec : Y → Fin dim → ℝ
  lab : Y → Bool
  /-- Uniform distribution on the data space. -/
  unif : Y → ℝ
  hunif_nonneg : ∀ y, 0 ≤ unif y
  hunif_sum : (∑ y, unif y) = 1
  Δ : ℝ
  /-- 1. Unit-norm data vectors. -/
  unit : ∀ y, (∑ j, vec y j ^ 2) = 1
  /-- A ground-truth hyperplane with unit norm. -/
  w : Fin dim → ℝ
  wnorm : (∑ j, w j ^ 2) = 1
  /-- 2. Separability outside an `O(Δ)` margin, with probability `1 − Δ`. -/
  separable : (Finset.univ.filter (fun y =>
      Δ / Real.sqrt (8 + 2 * Δ ^ 2) ≤
        labelOf (lab y) * (∑ j, w j * vec y j))).sum unif = 1 - Δ
  /-- 3. Bounded distance to the hyperplane for every data point. -/
  bounded : ∀ y, |labelOf (lab y) * (∑ j, w j * vec y j)| ≤
    Δ / Real.sqrt (8 + 2 * Δ ^ 2)
  /-- Number of measurement shots `R`. -/
  shots : ℕ
  /-- 4. Noisy kernel entries `K' = K + e` with zero mean, bounded range and
  variance at most `1/R`.  (The independence of the `e_ij` is recorded as the
  finite product-law hypothesis in Lemma 19.) -/
  noiseBound : ℝ
  noiseMeanZero : Prop
  noiseVariance : noiseBound ≤ (shots : ℝ)⁻¹

end DlogWorld

end Qatlib.Papers.SupervSpeedup20.MainResults
