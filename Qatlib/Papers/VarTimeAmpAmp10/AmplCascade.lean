/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.CoherentStop
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The amplification cascade schedule (VTAA second executable slice)

Fixed source arXiv:1010.4458v2 (Ambainis, *Variable time amplitude amplification and a
faster quantum algorithm for solving systems of linear equations*): the round structure
of Algorithms 1–2 (the route from Algorithms 1–2 to Theorem 1), read on top of the coherent-stop
coherent stop marking `stopMark`.  Algorithm 1 builds each nested window block `B_i`
by continuing the underlying walk on the still-running branches only; Algorithm 2
amplifies each block with the least number of rounds lifting the window weight into
the band `1/(9m) ≤ (2k+1)² p ≤ 1/m`.  This slice formalizes exactly that schedule:
a window is a record carrying the stop predicate (the nested `H_i ⊆ H_j` sectors),
the continuation unitary that fixes already-stopped sectors pointwise (the §3.1
consistency requirement 3 at operator level), the per-window diffusion reflection,
and the repetition count.

The per-round operator identities are proved: one amplification step is the
reflection `refl` applied after the coherent stop marking `stopMark pred`, its action
on the three sectors of the coherent-stop decomposition is pinned down, the repetition
power and the composed window word are unitary, the whole cascade word equals the
explicitly stated flat reflection word, and nesting transports the marking action
along the schedule (later windows keep flipping earlier stopped sectors; earlier
markings never disturb branches still running at a later window).

The call count ν of the schedule is **derived, never prescribed**: `markCalls` sums
the repetition counts of the actual schedule, and `wordFactors_length` proves that
the flat reflection word realizes exactly ν amplification rounds plus one
continuation per window.  Algorithm 2's repetition policy is provided as the bridge
`bandReps p m` (the least `k` with `1/(9m) ≤ (2k+1)² p`), with the full band theorem
`bandReps_band`; `Qatlib.Papers.VarTimeAmpAmp10.AmplCascade.Window.ofBand` installs the derived count into a window.

Finally, the first success-probability recurrence of the Lemma 2/3 chain is proved
for the invariant two-sector plane: if the window reflection is `reflAbout ψ` (the
reflection about the window reference state) and `ψ = α • g + β • b` splits into
normalized stopped/running sector states, then one round maps the stopped mass `p`
to exactly `p * (3 - 4 * p)^2` (the `sin² 3θ` identity), and in the safe window
`p ≤ 1/4` the stopped mass at least quadruples.

Boundary (kept out of this slice on purpose): amplitude estimation (`Estimate`,
Algorithm 2's `p` is data here, not computed), the multi-round `(2k+1)`-fold growth
chain and the Lemma 2/3 products, the `T_av`/`T_max` cost model and any compilation;
no asymptotic O/Ω/Θ statement is made (DESIGN §12 items 2/4/8: finite identities are
exact algebra, a single coherent action is not a measurement, and this is a
conditional assembly, not a complete program).
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Papers.VarTimeAmpAmp10.CoherentStop
open scoped Matrix

-- The complex conjugate is the star ring endomorphism, available as `conj` in the
-- `ComplexConjugate` scope; this matches the `normSq` lemma statements.
open scoped ComplexConjugate

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.AmplCascade

variable {a w : ℕ}

/-! ### Windows: the round structure of Algorithms 1-2 -/

/-- One window of the amplification cascade: Algorithm 1's block structure plus
Algorithm 2's repetition count for that block. -/
structure Window (a w : ℕ) where
  /-- The stop predicate of the window: the addresses stopped by its end (the nested
  subspace `H_i` of §3.1, in address coordinates). -/
  pred : Addr a → Bool
  /-- The continuation unitary of the window: Algorithm 1's step "execute the walk
  from `2^{i-1}` to `2^i` on the parts where the outcome register is 2". -/
  cont : Matrix (OReg a w) (OReg a w) ℂ
  /-- The continuation is unitary. -/
  cont_uni : cont ∈ Matrix.unitaryGroup (OReg a w) ℂ
  /-- §3.1 consistency requirement 3 at operator level: the continuation fixes every
  already-stopped sector state pointwise (the stopped part does not change later). -/
  cont_fix : ∀ v : QState (OReg a w), v ∈ stopSub (w := w) pred → cont *ᵥ v = v
  /-- The per-window diffusion reflection alternating with the coherent stop marking
  inside each amplification round. -/
  refl : Matrix (OReg a w) (OReg a w) ℂ
  /-- The diffusion reflection is unitary. -/
  refl_uni : refl ∈ Matrix.unitaryGroup (OReg a w) ℂ
  /-- The number of amplification rounds of this window (Algorithm 2's `k`). -/
  reps : ℕ

/-- One amplification round of a window: the diffusion reflection applied after the
coherent stop marking of the coherent-stop operator (the oracle reflection of the round). -/
def stepOf (ω : Window a w) : Matrix (OReg a w) (OReg a w) ℂ :=
  ω.refl * stopMark ω.pred

/-- **Per-round unitarity.** One amplification round is unitary: it is a product of
two unitaries (the window reflection and the coherent stop marking). -/
theorem stepOf_uni (ω : Window a w) : stepOf ω ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  (Matrix.unitaryGroup (OReg a w) ℂ).mul_mem ω.refl_uni (stopMark_uni ω.pred)

/-- **Per-round identity, marked sector.** On a stopped-sector state one round acts
as the negated window reflection (the marking contributes the phase `-1`). -/
theorem stepOf_stopSub (ω : Window a w) {v : QState (OReg a w)}
    (hv : v ∈ stopSub ω.pred) : stepOf ω *ᵥ v = -(ω.refl *ᵥ v) := by
  rw [stepOf, ← Matrix.mulVec_mulVec, markStopSub ω.pred hv]
  funext r
  simp [Matrix.mulVec, dotProduct, mul_neg, Finset.sum_neg_distrib]

/-- **Per-round identity, running sector.** On a still-running flag-set state one
round acts as the plain window reflection (the marking is the identity there). -/
theorem stepOf_contSub (ω : Window a w) {v : QState (OReg a w)}
    (hv : v ∈ contSub ω.pred) : stepOf ω *ᵥ v = ω.refl *ᵥ v := by
  rw [stepOf, ← Matrix.mulVec_mulVec, markContSub ω.pred hv]

/-- **Per-round identity, auxiliary sector.** On a flag-unset state one round acts
as the plain window reflection. -/
theorem stepOf_aux (ω : Window a w) {v : QState (OReg a w)}
    (hv : v ∈ auxSub (a := a) (w := w)) : stepOf ω *ᵥ v = ω.refl *ᵥ v := by
  rw [stepOf, ← Matrix.mulVec_mulVec, markAuxSub ω.pred hv]

/-- The round word of a window: `reps` repetitions of the amplification round. -/
def roundOf (ω : Window a w) : Matrix (OReg a w) (OReg a w) ℂ :=
  (stepOf ω) ^ (ω.reps)

/-- **Round-word unitarity.** A power of a unitary round is unitary. -/
theorem roundOf_uni (ω : Window a w) : roundOf ω ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  Submonoid.pow_mem _ (stepOf_uni ω) ω.reps

/-- The window word: Algorithm 1's block — first the continuation on the running
branches, then the window's amplification rounds. -/
def windowWord (ω : Window a w) : Matrix (OReg a w) (OReg a w) ℂ :=
  roundOf ω * ω.cont

/-- **Window-word unitarity.** The composed window block is unitary. -/
theorem windowWord_uni (ω : Window a w) :
    windowWord ω ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  (Matrix.unitaryGroup (OReg a w) ℂ).mul_mem (roundOf_uni ω) ω.cont_uni

/-- **Continuation identity.** The window continuation fixes every stopped-sector
state of the window pointwise (Algorithm 1 acts only on the running branches). -/
theorem windowCont_fix (ω : Window a w) {v : QState (OReg a w)}
    (hv : v ∈ stopSub ω.pred) : ω.cont *ᵥ v = v :=
  ω.cont_fix v hv

/-! ### Nesting: the `H_1 ⊆ … ⊆ H_m` transport of the marking -/

/-- The stopped sector grows with the predicate: `f ⊆ g` pointwise implies
`stopSub f ≤ stopSub g`. -/
theorem stopSub_mono (f g : Addr a → Bool) (h : ∀ x, f x = true → g x = true) :
    stopSub (w := w) f ≤ stopSub (w := w) g := by
  unfold stopSub
  rw [Submodule.span_le]
  rintro s ⟨r, hr1, hrf, rfl⟩
  exact Submodule.subset_span ⟨r, hr1, h r.1 hrf, rfl⟩

/-- The running sector shrinks with the predicate: `f ⊆ g` pointwise implies
`contSub g ≤ contSub f`. -/
theorem contSub_anti (f g : Addr a → Bool) (h : ∀ x, f x = true → g x = true) :
    contSub (w := w) g ≤ contSub (w := w) f := by
  unfold contSub
  rw [Submodule.span_le]
  rintro s ⟨r, hr1, hrg, rfl⟩
  refine Submodule.subset_span ⟨r, hr1, ?_, rfl⟩
  cases hf : f r.1 with
  | false => rfl
  | true => exact absurd (h r.1 hf) (by rw [hrg]; simp)

/-- **Nesting transport, stopped.** A later window (whose predicate contains `f`)
keeps marking the `f`-stopped sector with the phase `-1`. -/
theorem markLater_stop {f g : Addr a → Bool} (h : ∀ x, f x = true → g x = true)
    {v : QState (OReg a w)} (hv : v ∈ stopSub f) : stopMark g *ᵥ v = -v :=
  markStopSub g (stopSub_mono f g h hv)

/-- **Nesting transport, running.** An earlier window's coherent stop marking fixes
pointwise the sector that is still running at a later window: the earlier marking
never disturbs branches that have not stopped yet. -/
theorem markEarlier_cont {f g : Addr a → Bool} (h : ∀ x, f x = true → g x = true)
    {v : QState (OReg a w)} (hv : v ∈ contSub g) : stopMark f *ᵥ v = v :=
  markContSub f (contSub_anti f g h hv)

/-- The §3.1 nesting of the stopped subspaces along the execution order of the
schedule: every earlier window's stopped set is contained in every later window's
stopped set (`H_1 ⊆ H_2 ⊆ … ⊆ H_m`). -/
def WindowsNested : List (Window a w) → Prop
  | [] => True
  | ω :: ws => (∀ ω' ∈ ws, ∀ x, ω.pred x = true → ω'.pred x = true) ∧ WindowsNested ws

/-- A nested window list remains nested after removing its first window. -/
theorem windowsNested_cons {ω : Window a w} {ws : List (Window a w)}
    (h : WindowsNested (ω :: ws)) :
    (∀ ω' ∈ ws, ∀ x, ω.pred x = true → ω'.pred x = true) ∧ WindowsNested ws := h

/-- **Cascade-level nesting transport, stopped.** In a nested schedule, every later
window keeps marking the first window's stopped sector with the phase `-1`. -/
theorem nested_cons_stop {ω : Window a w} {ws : List (Window a w)}
    (h : WindowsNested (ω :: ws)) {ω' : Window a w} (hω' : ω' ∈ ws)
    {v : QState (OReg a w)} (hv : v ∈ stopSub ω.pred) : stopMark ω'.pred *ᵥ v = -v :=
  markLater_stop (h.1 ω' hω') hv

/-- **Cascade-level nesting transport, running.** In a nested schedule, the first
window's stop marking fixes pointwise the sector that is still running at any later
window. -/
theorem nested_cons_cont {ω : Window a w} {ws : List (Window a w)}
    (h : WindowsNested (ω :: ws)) {ω' : Window a w} (hω' : ω' ∈ ws)
    {v : QState (OReg a w)} (hv : v ∈ contSub ω'.pred) : stopMark ω.pred *ᵥ v = v :=
  markEarlier_cont (h.1 ω' hω') hv

/-! ### The cascade word and the derived call count -/

/-- The cascade word: the total operator of the schedule, windows composed in
execution order (the first window's block acts first). -/
def cascadeWord : List (Window a w) → Matrix (OReg a w) (OReg a w) ℂ
  | [] => 1
  | ω :: ws => cascadeWord ws * windowWord ω

/-- The explicitly stated flat reflection word of the schedule: for each window (in
reverse execution order, so that later list factors act first, matching the matrix
product convention) the continuation factor followed by that window's repetition of
the amplification round. -/
def wordFactors : List (Window a w) → List (Matrix (OReg a w) (OReg a w) ℂ)
  | [] => []
  | ω :: ws => wordFactors ws ++ (List.replicate ω.reps (stepOf ω) ++ [ω.cont])

/-- The derived call count ν of the schedule: the number of amplification rounds
(stop marking + reflection steps) actually present in the cascade word, computed
from the schedule alone and never taken as an independent input. -/
def markCalls (ws : List (Window a w)) : ℕ := (ws.map Window.reps).sum

/-- Marking-query counts add when a window is prepended to a cascade. -/
theorem markCalls_cons (ω : Window a w) (ws : List (Window a w)) :
    markCalls (ω :: ws) = ω.reps + markCalls ws := by
  simp [markCalls]

/-- **Composition identity.** The cascade word equals the product of the explicitly
stated flat reflection word: the composed schedule is exactly the alternating word
of continuations and marking–reflection rounds, in execution order. -/
theorem cascadeWord_eq_word (ws : List (Window a w)) :
    cascadeWord ws = (wordFactors ws).prod := by
  induction ws with
  | nil => rfl
  | cons ω ws ih =>
    rw [cascadeWord, wordFactors, List.prod_append, List.prod_append, ih, windowWord,
      roundOf, List.prod_replicate, List.prod_cons, List.prod_nil, mul_one]

/-- **Cascade unitarity.** The whole cascade word is unitary: unitarity is preserved
through every window block and every repetition. -/
theorem cascadeWord_uni (ws : List (Window a w)) :
    cascadeWord ws ∈ Matrix.unitaryGroup (OReg a w) ℂ := by
  induction ws with
  | nil => exact Submonoid.one_mem _
  | cons ω ws ih => exact (Matrix.unitaryGroup (OReg a w) ℂ).mul_mem ih (windowWord_uni ω)

/-- **Derived call count.** The flat reflection word of the schedule contains
exactly `markCalls ws` amplification rounds plus one continuation per window: the
call count ν is the length count of the actual word, derived from the schedule. -/
theorem wordFactors_length (ws : List (Window a w)) :
    (wordFactors ws).length = markCalls ws + ws.length := by
  induction ws with
  | nil => rfl
  | cons ω ws ih =>
    rw [wordFactors, List.length_append, List.length_append, ih, List.length_replicate,
      List.length_cons, List.length_nil, markCalls_cons, List.length_cons]
    omega

/-! ### Algorithm 2's repetition policy: deriving the round count -/

/-- The Grover factor of `k` rounds: `(2k+1)²`, as a real number. -/
def ampFactor (k : ℕ) : ℝ := ((2 * k + 1 : ℕ) : ℝ) ^ 2

/-- Zero amplification repetitions have amplification factor one. -/
theorem ampFactor_zero : ampFactor 0 = 1 := by
  norm_num [ampFactor]

/-- Every natural number is bounded by its Grover factor: `n ≤ (2n+1)²`. -/
theorem le_ampFactor (n : ℕ) : (n : ℝ) ≤ ampFactor n := by
  have hexp : ampFactor n = ((2 : ℝ) * n + 1) * ((2 : ℝ) * n + 1) := by
    unfold ampFactor
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ (2 : ℝ) * n + 1 := by linarith
  have h2 : (n : ℝ) ≤ (2 : ℝ) * n + 1 := by linarith
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h4 : (n : ℝ) * 1 ≤ ((2 : ℝ) * n + 1) * ((2 : ℝ) * n + 1) :=
    mul_le_mul h2 h1 (by positivity) (by positivity)
  rw [hexp]
  linarith

/-- One more round costs at most a factor nine: `(2k+3)² ≤ 9 (2k+1)²`. -/
theorem ampFactor_succ (k : ℕ) : ampFactor (k + 1) ≤ 9 * ampFactor k := by
  have key : ((2 : ℝ) * k + 3) ^ 2 + 8 * k * (4 * k + 3) = 9 * ((2 : ℝ) * k + 1) ^ 2 := by
    ring
  have h8 : (0 : ℝ) ≤ 8 * (k : ℝ) * (4 * (k : ℝ) + 3) := by positivity
  have hexp : ampFactor (k + 1) = ((2 : ℝ) * k + 3) ^ 2 := by
    unfold ampFactor
    push_cast
    ring
  have hexp' : ampFactor k = ((2 : ℝ) * k + 1) ^ 2 := by
    unfold ampFactor
    push_cast
    ring
  rw [hexp, hexp']
  linarith

/-- Algorithm 2's repetition policy: the least round count `k` that lifts the window
weight `p` over the amplification threshold `1/(9m)`. -/
def bandReps (p : ℝ) (m : ℕ) : ℕ :=
  sInf {k : ℕ | 1 / (9 * (m : ℝ)) ≤ ampFactor k * p}

/-- Minimality: any round count reaching the threshold bounds the policy from below. -/
theorem bandReps_le (p : ℝ) (m : ℕ) {k : ℕ}
    (h : 1 / (9 * (m : ℝ)) ≤ ampFactor k * p) : bandReps p m ≤ k :=
  Nat.sInf_le h

/-- For a positive weight the threshold is reached: the policy is well defined. -/
theorem bandReps_exists (p : ℝ) (m : ℕ) (hp : 0 < p) :
    ∃ k : ℕ, 1 / (9 * (m : ℝ)) ≤ ampFactor k * p := by
  obtain ⟨N, hN⟩ := Real.instArchimedean.arch (1 / (9 * (m : ℝ))) hp
  obtain ⟨k, hk⟩ := Real.instArchimedean.arch (N : ℝ) (by norm_num : (0 : ℝ) < 1)
  rw [nsmul_one] at hk
  refine ⟨k, ?_⟩
  calc 1 / (9 * (m : ℝ)) ≤ (N : ℝ) * p := by rwa [nsmul_eq_mul] at hN
    _ ≤ ((k : ℝ)) * p := mul_le_mul_of_nonneg_right hk hp.le
    _ ≤ ampFactor k * p := mul_le_mul_of_nonneg_right (le_ampFactor k) hp.le

/-- The policy lands in the threshold: the amplified weight reaches `1/(9m)`. -/
theorem bandReps_spec (p : ℝ) (m : ℕ)
    (h : ∃ k : ℕ, 1 / (9 * (m : ℝ)) ≤ ampFactor k * p) :
    1 / (9 * (m : ℝ)) ≤ ampFactor (bandReps p m) * p := by
  have h' : {k : ℕ | 1 / (9 * (m : ℝ)) ≤ ampFactor k * p}.Nonempty := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, hk⟩
  exact Nat.sInf_mem h'

/-- Above the threshold no rounds are scheduled: Algorithm 2 keeps the block as is
when its weight already exceeds `1/(9m)`. -/
theorem bandReps_zero_of_lt (p : ℝ) (m : ℕ) (h : 1 / (9 * (m : ℝ)) < p) :
    bandReps p m = 0 := by
  have h0 : bandReps p m ≤ 0 := bandReps_le p m (by
    rw [ampFactor_zero, one_mul]
    exact h.le)
  exact Nat.le_zero.mp h0

/-- **The full band of Algorithm 2.** For a positive window weight that does not yet
exceed `1/(9m)`, the least round count reaching the threshold also stays under
`1/m`: the amplified weight `(2k+1)² p` lands in the band `[1/(9m), 1/m]`. -/
theorem bandReps_band {p : ℝ} {m : ℕ} (hm : 0 < m) (hp : 0 < p)
    (hpm : p ≤ 1 / (9 * (m : ℝ))) :
    1 / (9 * (m : ℝ)) ≤ ampFactor (bandReps p m) * p
      ∧ ampFactor (bandReps p m) * p ≤ 1 / (m : ℝ) := by
  have hex : ∃ k : ℕ, 1 / (9 * (m : ℝ)) ≤ ampFactor k * p := bandReps_exists p m hp
  have hlo := bandReps_spec p m hex
  refine ⟨hlo, ?_⟩
  rcases Nat.eq_zero_or_pos (bandReps p m) with h0 | h0
  · rw [h0, ampFactor_zero, one_mul] at hlo ⊢
    have hpe : p = 1 / (9 * (m : ℝ)) := le_antisymm hpm hlo
    rw [hpe]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 9 * (m : ℝ))
      (by exact_mod_cast hm)]
    norm_num
    exact_mod_cast by omega
  · have hsq : ampFactor (bandReps p m) ≤ 9 * ampFactor (bandReps p m - 1) := by
      have h2 := ampFactor_succ (bandReps p m - 1)
      rwa [Nat.sub_add_cancel h0] at h2
    have hlt : ampFactor (bandReps p m - 1) * p < 1 / (9 * (m : ℝ)) := by
      by_contra hc
      have hnot := (not_lt.mp hc)
      have hbad : bandReps p m ≤ bandReps p m - 1 := bandReps_le p m hnot
      omega
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    calc ampFactor (bandReps p m) * p ≤ 9 * (ampFactor (bandReps p m - 1) * p) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hsq hp.le
      _ ≤ 9 * (1 / (9 * (m : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hlt.le (by norm_num)
      _ = 1 / (m : ℝ) := by
          field_simp

/-- The window obtained by installing Algorithm 2's derived repetition count for the
weight `p` into an existing window, keeping its predicate, continuation and
reflection: the round count of a concrete schedule is computed by the policy, not
prescribed. -/
def Window.ofBand (m : ℕ) (p : ℝ) (ω : Window a w) : Window a w where
  pred := ω.pred
  cont := ω.cont
  cont_uni := ω.cont_uni
  cont_fix := ω.cont_fix
  refl := ω.refl
  refl_uni := ω.refl_uni
  reps := bandReps p m

/-- The band-selected window records the repetition count chosen from its mass. -/
@[simp]
theorem ofBand_reps (m : ℕ) (p : ℝ) (ω : Window a w) :
    (Window.ofBand m p ω).reps = bandReps p m := rfl

/-! ### The invariant plane: the first success-probability recurrence -/

/-- The finite set of flag-set basis outcomes at addresses stopped by `f`: the
coordinate model of the stopped sector of the coherent-stop decomposition. -/
def stopFinset (f : Addr a → Bool) : Finset (OReg a w) :=
  Finset.univ.filter fun r => r.2.1 = true ∧ f r.1 = true

/-- The outer product `|ψ⟩⟨ψ|` of a state, as a matrix. -/
def outerState (ψ : QState (OReg a w)) : Matrix (OReg a w) (OReg a w) ℂ :=
  Matrix.of fun r r' => ψ r * (starRingEnd ℂ) (ψ r')

/-- The reflection about the state `ψ`: `2 |ψ⟩⟨ψ| - 1`, the diffusion reflection of a
window whose reference state is `ψ`. -/
def reflAbout (ψ : QState (OReg a w)) : Matrix (OReg a w) (OReg a w) ℂ :=
  (2 : ℂ) • outerState ψ - 1

/-- A rank-one outer-product matrix acts by the corresponding overlap scalar. -/
theorem outerState_mulVec (ψ v : QState (OReg a w)) (r : OReg a w) :
    (outerState ψ *ᵥ v) r = ψ r * ∑ k, (starRingEnd ℂ) (ψ k) * v k := by
  simp only [outerState, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The outer product acts by the total pairing against the state. -/
theorem outerState_mulVec_eq (ψ v : QState (OReg a w)) (S : ℂ)
    (hS : ∑ k, (starRingEnd ℂ) (ψ k) * v k = S) :
    outerState ψ *ᵥ v = S • ψ := by
  funext r
  rw [outerState_mulVec, hS, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The reflection about `ψ` acts as twice the `ψ`-component along `ψ`, minus the
state itself. -/
theorem reflAbout_mulVec_eq (ψ v : QState (OReg a w)) (S : ℂ)
    (hS : ∑ k, (starRingEnd ℂ) (ψ k) * v k = S) :
    reflAbout ψ *ᵥ v = (2 * S) • ψ - v := by
  have h1 : reflAbout ψ *ᵥ v = (((2 : ℂ) • outerState ψ - 1) *ᵥ v) := rfl
  rw [h1, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    outerState_mulVec_eq ψ v S hS, smul_smul]

/-- The outer product `|ψ⟩⟨ψ|` is self-adjoint. -/
theorem outerState_conjT (ψ : QState (OReg a w)) :
    ((outerState ψ)ᴴ : Matrix (OReg a w) (OReg a w) ℂ) = outerState ψ := by
  ext r r'
  simp only [Matrix.conjTranspose_apply, outerState, Matrix.of_apply]
  rw [star_mul, starRingEnd_apply, starRingEnd_apply, star_star]

/-- The reflection about a state is self-adjoint. -/
theorem reflAbout_conjT (ψ : QState (OReg a w)) :
    ((reflAbout ψ)ᴴ : Matrix (OReg a w) (OReg a w) ℂ) = reflAbout ψ := by
  rw [reflAbout, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, outerState_conjT]
  congr 1
  norm_num [Complex.conj_ofReal]

/-- The conjugate pairing of a complex number is the cast of its squared norm. -/
theorem star_mul_self (x : ℂ) : (starRingEnd ℂ) x * x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h2 := Complex.normSq_eq_conj_mul_self (z := x)
  rw [Complex.normSq_eq_norm_sq] at h2
  rw [← h2]

/-- The outer product of a normalized state is a projection: `|ψ⟩⟨ψ|² = |ψ⟩⟨ψ|`. -/
theorem outerState_idem {ψ : QState (OReg a w)} (hψ : Normalized ψ) :
    outerState ψ * outerState ψ = outerState ψ := by
  have hEq : ∑ k, ‖ψ k‖ ^ 2 = 1 := hψ
  have hsum : ∑ k, (starRingEnd ℂ) (ψ k) * ψ k = 1 := by
    simp only [star_mul_self]
    rw [← Complex.ofReal_sum, hEq]
    push_cast
    rfl
  ext r r'
  simp only [Matrix.mul_apply, outerState, Matrix.of_apply]
  have hterm : ∀ k : OReg a w,
      (ψ r * (starRingEnd ℂ) (ψ k)) * (ψ k * (starRingEnd ℂ) (ψ r'))
        = ((starRingEnd ℂ) (ψ k) * ψ k) * (ψ r * (starRingEnd ℂ) (ψ r')) :=
    fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_mul, hsum, one_mul]

/-- The reflection about a normalized state is involutory. -/
theorem reflAbout_sq {ψ : QState (OReg a w)} (hψ : Normalized ψ) :
    reflAbout ψ * reflAbout ψ = 1 := by
  have hPP := outerState_idem hψ
  have hnum : ((2 : ℂ) * 2) = 4 := by norm_num
  have hexp : ((2 : ℂ) • outerState ψ) * ((2 : ℂ) • outerState ψ)
      = ((4 : ℂ)) • (outerState ψ * outerState ψ) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hnum]
  have h42 : ((4 : ℂ) • outerState ψ - (2 : ℂ) • outerState ψ)
      = (2 : ℂ) • outerState ψ := by
    rw [← sub_smul]
    norm_num
  unfold reflAbout
  rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, hexp, hPP, h42, sub_sub_cancel, one_mul]

/-- **Diffusion unitarity.** The reflection about a normalized state is unitary. -/
theorem reflAbout_uni {ψ : QState (OReg a w)} (hψ : Normalized ψ) :
    reflAbout ψ ∈ Matrix.unitaryGroup (OReg a w) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, reflAbout_conjT,
    reflAbout_sq hψ]

/-- A two-sector split state carries Born mass `‖α‖²` on the sector of `g` when the
complement state vanishes there, `g` vanishes off the sector, and `g` is normalized. -/
theorem measureProb_sector (S : Finset (OReg a w)) (α β : ℂ) (g b : QState (OReg a w))
    (hbS : ∀ r ∈ S, b r = 0) (hgS : ∀ r ∉ S, g r = 0) (hgN : ∑ r, ‖g r‖ ^ 2 = 1) :
    MeasureProb (α • g + β • b) S = ‖α‖ ^ 2 := by
  have hterm : ∀ r ∈ S, BornProb (α • g + β • b) r = ‖α‖ ^ 2 * ‖g r‖ ^ 2 := by
    intro r hr
    have hb0 : b r = 0 := hbS r hr
    unfold BornProb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb0, mul_zero, add_zero,
      norm_mul, mul_pow]
  unfold MeasureProb
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [Finset.sum_subset (fun r _ => Finset.mem_univ r)
    (fun r _ hr => by simp [hgS r hr])]
  rw [hgN, mul_one]

/-- **Marking on the invariant plane.** The coherent stop marking acts on the split
state `α • g + β • b` by negating the stopped-sector amplitude only. -/
theorem mark_split (f : Addr a → Bool) (α β : ℂ) (g b : QState (OReg a w))
    (hg : g ∈ stopSub f) (hb : b ∈ contSub f) :
    stopMark f *ᵥ (α • g + β • b) = (-α) • g + β • b := by
  rw [show stopMark f *ᵥ (α • g + β • b)
      = (stopMark f *ᵥ (α • g)) + (stopMark f *ᵥ (β • b)) from Matrix.mulVec_add _ _ _,
    Matrix.mulVec_smul, Matrix.mulVec_smul, markStopSub f hg, markContSub f hb]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- **The invariant-plane pairing.** For the split state `ψ = α • g + β • b` against
the marked state `(-α) • g + β • b`, the total pairing is `|β‖² - |α|²`: the stopped
and running sector states are orthogonal with unit norms. -/
theorem plane_overlap (f : Addr a → Bool) (α β : ℂ) (g b : QState (OReg a w))
    (hg : g ∈ stopSub f) (hb : b ∈ contSub f)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    ∑ k, (starRingEnd ℂ) ((α • g + β • b) k) * ((-α) • g + β • b) k
      = (((‖β‖ ^ 2 - ‖α‖ ^ 2 : ℝ) : ℂ)) := by
  have hzero : ∀ k : OReg a w,
      (starRingEnd ℂ) (g k) * b k = 0 ∧ (starRingEnd ℂ) (b k) * g k = 0 := by
    intro k
    by_cases hflag : k.2.1 = true
    · by_cases hf : f k.1 = true
      · have hbk : b k = 0 := contCoord f hb k (by simp [hflag, hf])
        simp [hbk]
      · have hgk : g k = 0 := stopCoord f hg k (by simp [hflag, hf])
        simp [hgk]
    · have hgk : g k = 0 := stopCoord f hg k (by simp [hflag])
      simp [hgk]
  have key : ∀ k : OReg a w,
      (starRingEnd ℂ) (α * g k + β * b k) * (-α * g k + β * b k)
        = -((starRingEnd ℂ) α * α) * ((starRingEnd ℂ) (g k) * g k)
          + (starRingEnd ℂ) β * β * ((starRingEnd ℂ) (b k) * b k) := by
    intro k
    rw [map_add, map_mul, map_mul]
    linear_combination ((starRingEnd ℂ) α * β) * (hzero k).1
      - ((starRingEnd ℂ) β * α) * (hzero k).2
  have hgsum : ∑ k, (starRingEnd ℂ) (g k) * g k = 1 := by
    simp only [star_mul_self]
    rw [← Complex.ofReal_sum, hgN]
    push_cast
    rfl
  have hbsum : ∑ k, (starRingEnd ℂ) (b k) * b k = 1 := by
    simp only [star_mul_self]
    rw [← Complex.ofReal_sum, hbN]
    push_cast
    rfl
  have hconv : ∀ k : OReg a w,
      (starRingEnd ℂ) ((α • g + β • b) k) * ((-α) • g + β • b) k
        = (starRingEnd ℂ) (α * g k + β * b k) * (-α * g k + β * b k) := fun k => rfl
  rw [Finset.sum_congr rfl fun k _ => hconv k, Finset.sum_congr rfl fun k _ => key k,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hgsum, hbsum,
    mul_one, mul_one]
  rw [← Complex.normSq_eq_conj_mul_self (z := α), ← Complex.normSq_eq_conj_mul_self (z := β),
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **One round on the invariant plane.** With the window reflection taken as the
reflection about the split state `ψ = α • g + β • b`, one amplification round maps
`ψ` to the split state with stopped amplitude `α (1 + 2 (|β|² - |α|²))` and running
amplitude `β (2 (|β|² - |α|²) - 1)`. -/
theorem plane_round (f : Addr a → Bool) (ψ : QState (OReg a w)) (α β : ℂ)
    (g b : QState (OReg a w)) (hsplit : ψ = α • g + β • b)
    (hg : g ∈ stopSub f) (hb : b ∈ contSub f)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    (reflAbout ψ * stopMark f) *ᵥ ψ
      = (α * (1 + 2 * (((‖β‖ ^ 2 - ‖α‖ ^ 2 : ℝ) : ℂ)))) • g
        + (β * (2 * (((‖β‖ ^ 2 - ‖α‖ ^ 2 : ℝ) : ℂ)) - 1)) • b := by
  rw [hsplit, ← Matrix.mulVec_mulVec, mark_split f α β g b hg hb,
    reflAbout_mulVec_eq _ _ _ (plane_overlap f α β g b hg hb hgN hbN)]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **First success-probability recurrence (Lemma 2/3 chain, first link).** For a
window whose diffusion reflection is the reflection about the normalized split state
`ψ = α • g + β • b` over the stopped/running sectors, one amplification round maps
the stopped mass `p` of `ψ` to exactly `p (3 - 4 p)²` — the `sin² 3θ` identity of the
per-window conditional amplitude growth. -/
theorem window_step_recurrence (ω : Window a w) {ψ : QState (OReg a w)} {α β : ℂ}
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ) (hsplit : ψ = α • g + β • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1)
    (hN : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    MeasureProb (stepOf ω *ᵥ ψ) (stopFinset ω.pred)
      = MeasureProb ψ (stopFinset ω.pred)
        * (3 - 4 * MeasureProb ψ (stopFinset ω.pred)) ^ 2 := by
  have hrw := plane_round ω.pred ψ α β g b hsplit hg hb hgN hbN
  have hbS : ∀ r ∈ stopFinset ω.pred, b r = 0 := by
    intro r hr
    rw [stopFinset, Finset.mem_filter] at hr
    obtain ⟨_, h1, h2⟩ := hr
    exact contCoord ω.pred hb r (by simp [h1, h2])
  have hgS : ∀ r ∉ stopFinset ω.pred, g r = 0 := by
    intro r hr
    exact stopCoord ω.pred hg r (fun h => hr (by
      rw [stopFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ r, h⟩))
  have hmass : MeasureProb ψ (stopFinset ω.pred) = ‖α‖ ^ 2 := by
    rw [hsplit]
    exact measureProb_sector (stopFinset ω.pred) α β g b hbS hgS hgN
  rw [hmass]
  rw [stepOf, hω, hrw]
  rw [measureProb_sector (stopFinset ω.pred) _ _ g b hbS hgS hgN]
  have hc : (1 : ℂ) + 2 * (((‖β‖ ^ 2 - ‖α‖ ^ 2 : ℝ) : ℂ))
      = ((3 - 4 * ‖α‖ ^ 2 : ℝ) : ℂ) := by
    have hinner : (1 : ℝ) + 2 * (‖β‖ ^ 2 - ‖α‖ ^ 2) = 3 - 4 * ‖α‖ ^ 2 := by linarith
    exact_mod_cast hinner
  rw [hc]
  have hz2 : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.normSq z := fun z => Complex.sq_norm z
  rw [hz2, Complex.normSq_mul, Complex.normSq_ofReal, ← hz2 α]
  ring

/-- **Safe-window growth (one round).** In the safe window `p ≤ 1/4` (the `k = 1`
instance of `(2k+1)θ ≤ π/2`), one amplification round at least quadruples the
stopped mass. -/
theorem window_step_growth (ω : Window a w) {ψ : QState (OReg a w)} {α β : ℂ}
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ) (hsplit : ψ = α • g + β • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1)
    (hN : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (hp : MeasureProb ψ (stopFinset ω.pred) ≤ 1 / 4) :
    4 * MeasureProb ψ (stopFinset ω.pred)
      ≤ MeasureProb (stepOf ω *ᵥ ψ) (stopFinset ω.pred) := by
  rw [window_step_recurrence ω hω hsplit hg hb hgN hbN hN]
  have hp0 : 0 ≤ MeasureProb ψ (stopFinset ω.pred) := measureProb_nonneg _ _
  have h34 : 2 ≤ 3 - 4 * MeasureProb ψ (stopFinset ω.pred) := by linarith
  nlinarith [hp0, h34, sq_nonneg (3 - 4 * MeasureProb ψ (stopFinset ω.pred) - 2)]

end Qatlib.Papers.VarTimeAmpAmp10.AmplCascade
