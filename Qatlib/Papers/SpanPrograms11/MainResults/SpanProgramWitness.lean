/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanPrograms11.MainResults.LearningGraphStages
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgramWitness — Theorem 3: the span program of a learning graph

Belovs, *Span Programs for Functions with Constant-Sized 1-certificates*,
fixed arXiv:1105.4024v1 (20 May 2011), PDF SHA-256
`315b5768c635ceee578e1ed2879a53a210c73c53a43bd0d0430041f9faa4e552`.

Section 3.3 proves Theorem 3 — for a learning graph of complexity `C` there is a bounded
error quantum query algorithm of complexity `O(C log m)` — by building a span program out of
the graph and computing the two witness sizes of §2.2. This file formalises that
construction and the two size computations.

The vector space of the span program has an orthonormal basis indexed by partial
assignments `σ : [n] → Option Bool` (the paper's `t_σ`, whose vertex `S` is the domain of
`σ`). For an arc `e` from `S` to `S ∪ {j}` of weight `w_e` the paper adds the two input
vectors `√w_e (t_σ - t_{σ∪{j↦b}})` for `b = 0,1`, labelled by the value of `x_j`
(Eq. (1)); `t_∅` is the target, and `t_σ` is a free input vector when `σ` is a
1-certificate.

The content formalised here is:

* negative witness size: on a 0-input the witness `⟨w', t_σ⟩ = [σ agrees with x]` is
  orthogonal to every available input vector and has size `Σ_e w_e`, the negative
  complexity (this is where `f(x) = 0` enters, through the hypothesis that no free vector
  agrees with `x`);
* positive witness size: on a 1-input the coefficients `p_e / √w_e` on the available input
  vectors reproduce the target `t_∅` — exactly when the flow is conservative away from the
  source, which is the form in which the paper's `Σ_e p_e²/w_e` is the witness size — and
  the coefficient norm is `Σ_e p_e²/w_e`, the positive complexity.

Boundary: the final step of Theorem 3 — that a span program of witness size `W` yields a
quantum algorithm of `O(W)` queries — is Theorem 1 of the paper, attributed to Reichardt
[10,11], and is not formalised here; neither is the encoding of `m`-ary variables, which
multiplies both sizes by `k = ⌈log m⌉` (recorded separately as the `k`-fold expansion of
the arc set).
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Qatlib.Papers.SpanPrograms11.MainResults

/-- Partial assignments `[n] → Option Bool`: the index of the basis vector `t_σ` of §3.3,
whose domain is the set of variables on which `σ` is defined. -/
abbrev Assn (ι : Type*) := ι → Option Bool

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The assignment that agrees with the input `x` on `S` and is undefined elsewhere. -/
def agreeing (x : ι → Bool) (S : Finset ι) : Assn ι :=
  fun i => if i ∈ S then some (x i) else none

/-- `σ` agrees with the input `x` on its domain. -/
def Agrees (x : ι → Bool) (σ : Assn ι) : Prop := ∀ i b, σ i = some b → b = x i

omit [Fintype ι] in
/-- Every canonical assignment agrees with its input, on its own domain. -/
theorem agrees_agreeing (x : ι → Bool) (S : Finset ι) : Agrees x (agreeing x S) := by
  intro i b hb
  unfold agreeing at hb
  split at hb
  · injection hb with h
    exact h.symm
  · exact absurd hb (by simp)

omit [Fintype ι] in
/-- The map `S ↦ (agree with x on S)` is injective: the domain is the support. -/
theorem agreeing_injective (x : ι → Bool) : Function.Injective (agreeing x) := by
  intro S T hST
  ext i
  have h := congrFun hST i
  simp only [agreeing] at h
  by_cases hi : i ∈ S <;> by_cases hT : i ∈ T
  · exact ⟨fun _ => hT, fun _ => hi⟩
  · rw [if_pos hi, if_neg hT] at h
    exact absurd h (by simp)
  · rw [if_neg hi, if_pos hT] at h
    exact absurd h.symm (by simp)
  · exact ⟨fun h' => absurd h' hi, fun h' => absurd h' hT⟩

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The endpoint set `S ∪ {j}` of an arc leaving `S` and loading `j` (§3.1). -/
def dst (src : E → Finset ι) (j : E → ι) (e : E) : Finset ι := insert (j e) (src e)

/-- The assignment "agree with `x` on `S`, set `j` to `b`, undefined elsewhere": the
`σ ∪ {j ↦ b}` of Eq. (1). -/
def arcAssn (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (e : E) (b : Bool) : Assn ι :=
  fun i => if i ∈ src e then some (x i) else if i = j e then some b else none

omit [Fintype ι] [Fintype E] [DecidableEq E] in
/-- `σ ∪ {j ↦ b}` agrees with `x` exactly when `b = x_j`. -/
theorem agrees_arcAssn_iff (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (e : E)
    (hj : j e ∉ src e) (b : Bool) :
    Agrees x (arcAssn x src j e b) ↔ b = x (j e) := by
  constructor
  · intro h
    have hb : arcAssn x src j e b (j e) = some b := by
      unfold arcAssn
      rw [if_neg hj, if_pos rfl]
    exact h (j e) b hb
  · intro hb i b' hb'
    unfold arcAssn at hb'
    by_cases hi : i ∈ src e
    · rw [if_pos hi] at hb'
      injection hb' with h
      exact h.symm
    · rw [if_neg hi] at hb'
      by_cases hij : i = j e
      · rw [if_pos hij] at hb'
        injection hb' with h
        rw [hij]
        exact h.symm.trans hb
      · rw [if_neg hij] at hb'
        exact absurd hb' (by simp)

omit [Fintype ι] [Fintype E] [DecidableEq E] in
/-- For `b = x_j` the arc's input vector is the one indexed by the canonical assignment of
the endpoint `S ∪ {j}`. -/
theorem arcAssn_eq_agreeing (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (e : E) :
    arcAssn x src j e (x (j e)) = agreeing x (dst src j e) := by
  funext i
  unfold arcAssn agreeing dst
  by_cases hi : i ∈ src e
  · rw [if_pos hi, if_pos (Finset.mem_insert_of_mem hi)]
  · rw [if_neg hi]
    by_cases hij : i = j e
    · rw [if_pos hij, if_pos (by rw [hij]; exact Finset.mem_insert_self _ _), ← hij]
    · rw [if_neg hij, if_neg (by
        intro hmem
        rw [Finset.mem_insert] at hmem
        exact hmem.elim hij hi)]

/-- The ambient inner product: coefficient-wise sum over the orthonormal basis `t_σ`. -/
def ip (u v : Assn ι → ℝ) : ℝ := ∑ σ, u σ * v σ

/-- The negative witness of §3.3: `⟨w', t_σ⟩ = 1` when `σ` agrees with the input. -/
def negWitness (x : ι → Bool) : Assn ι → ℝ := fun σ => if Agrees x σ then 1 else 0

/-- A single basis vector `t_σ`. -/
def basis (σ : Assn ι) : Assn ι → ℝ := fun τ => if τ = σ then 1 else 0

/-- The basis vectors of the orthonormal basis are orthogonal, so `⟨t_σ, f⟩ = f σ`. -/
theorem ip_basis (σ : Assn ι) (f : Assn ι → ℝ) : ip (basis σ) f = f σ := by
  unfold ip basis
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    simp [hτ]
  · intro h
    exact absurd (Finset.mem_univ σ) h

/-- Scaling a basis vector scales its inner product with `f` by the same factor. -/
theorem ip_smul_basis (c : ℝ) (σ : Assn ι) (f : Assn ι → ℝ) :
    ip (fun τ => c * basis σ τ) f = c * f σ := by
  unfold ip basis
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    simp [hτ]
  · intro h
    exact absurd (Finset.mem_univ σ) h

/-- The inner product is additive in its first argument. -/
theorem ip_sub (u v : Assn ι → ℝ) (f : Assn ι → ℝ) : ip (u - v) f = ip u f - ip v f := by
  unfold ip
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun σ _ => by simp [sub_mul]

/-- The input vector attached to arc `e` and label `b`: `√w_e (t_σ - t_{σ∪{j↦b}})`, Eq. (1). -/
def inVec (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (w : E → ℝ) (e : E) (b : Bool) :
    Assn ι → ℝ :=
  fun τ => Real.sqrt (w e) * basis (agreeing x (src e)) τ
    - Real.sqrt (w e) * basis (arcAssn x src j e b) τ

omit [Fintype E] [DecidableEq E] in
/-- The inner product of an input vector with the negative witness is `√w_e` times the
difference of the two witness values. -/
theorem ip_inVec_negWitness (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (w : E → ℝ)
    (e : E) (b : Bool) :
    ip (inVec x src j w e b) (negWitness x)
      = Real.sqrt (w e) * (negWitness x (agreeing x (src e))
          - negWitness x (arcAssn x src j e b)) := by
  unfold inVec
  rw [show (fun τ => Real.sqrt (w e) * basis (agreeing x (src e)) τ
          - Real.sqrt (w e) * basis (arcAssn x src j e b) τ)
        = (fun τ => Real.sqrt (w e) * basis (agreeing x (src e)) τ)
          - (fun τ => Real.sqrt (w e) * basis (arcAssn x src j e b) τ) from rfl]
  rw [ip_sub, ip_smul_basis, ip_smul_basis]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The available input vector of an arc — the one labelled by the actual value `x_j` — is
orthogonal to the negative witness of a 0-input. -/
theorem negWitness_available_orthogonal (x : ι → Bool) (src : E → Finset ι) (j : E → ι)
    (w : E → ℝ) (e : E) (hj : j e ∉ src e) :
    ip (inVec x src j w e (x (j e))) (negWitness x) = 0 := by
  rw [ip_inVec_negWitness]
  have h1 : negWitness x (agreeing x (src e)) = 1 := by
    unfold negWitness
    rw [if_pos (agrees_agreeing x (src e))]
  have h2 : negWitness x (arcAssn x src j e (x (j e))) = 1 := by
    unfold negWitness
    rw [if_pos ((agrees_arcAssn_iff x src j e hj (x (j e))).2 rfl)]
  rw [h1, h2]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The false input vector of an arc has inner product `√w_e` with the negative witness. -/
theorem negWitness_false_inner (x : ι → Bool) (src : E → Finset ι) (j : E → ι)
    (w : E → ℝ) (e : E) (hj : j e ∉ src e) :
    ip (inVec x src j w e (!x (j e))) (negWitness x) = Real.sqrt (w e) := by
  rw [ip_inVec_negWitness]
  have h1 : negWitness x (agreeing x (src e)) = 1 := by
    unfold negWitness
    rw [if_pos (agrees_agreeing x (src e))]
  have hne : (!x (j e)) ≠ x (j e) := by
    cases h : x (j e) <;> simp
  have h2 : negWitness x (arcAssn x src j e (!x (j e))) = 0 := by
    unfold negWitness
    rw [if_neg (fun hcon => hne ((agrees_arcAssn_iff x src j e hj (!x (j e))).1 hcon))]
  rw [h1, h2]
  ring

omit [Fintype E] [DecidableEq E] in
/-- A free input vector (a 1-certificate `t_σ`) of a 0-input is orthogonal to the negative
witness, since it cannot agree with the input: this is where `f(x) = 0` enters the proof of
Theorem 3. -/
theorem negWitness_free_orthogonal (x : ι → Bool) (σ : Assn ι) (hfree : ¬ Agrees x σ) :
    ip (basis σ) (negWitness x) = 0 := by
  rw [ip_basis]
  unfold negWitness
  rw [if_neg hfree]

omit [DecidableEq E] in
/-- The free input vectors contribute nothing to the negative witness size. -/
theorem negWitness_free_sum (x : ι → Bool) (Free : Assn ι → Prop) [DecidablePred Free]
    (hfree : ∀ σ, Free σ → ¬ Agrees x σ) :
    (∑ σ ∈ Finset.univ.filter Free, ip (basis σ) (negWitness x) ^ 2) = 0 := by
  refine Finset.sum_eq_zero fun σ hσ => ?_
  have h := negWitness_free_orthogonal x σ (hfree σ (Finset.mem_filter.1 hσ).2)
  rw [h]
  ring

omit [DecidableEq E] in
/-- §3.3, negative witness size: `Σ_e Σ_{b} ⟨input vector, w'⟩² = Σ_e w_e`, the negative
complexity of the learning graph. Together with `negWitness_free_sum` this is the full
negative witness size of the span program. -/
theorem negWitness_size (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (w : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hj : ∀ e, j e ∉ src e) :
    (∑ e, ∑ b : Bool, ip (inVec x src j w e b) (negWitness x) ^ 2) = ∑ e, w e := by
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_bool]
  have ha : ip (inVec x src j w e (x (j e))) (negWitness x) = 0 :=
    negWitness_available_orthogonal x src j w e (hj e)
  have hf : ip (inVec x src j w e (!x (j e))) (negWitness x) = Real.sqrt (w e) :=
    negWitness_false_inner x src j w e (hj e)
  cases hx : x (j e) with
  | false =>
      rw [hx] at ha
      rw [hx, Bool.not_false] at hf
      rw [ha, hf, Real.sq_sqrt (hw e)]
      ring
  | true =>
      rw [hx] at ha
      rw [hx, Bool.not_true] at hf
      rw [ha, hf, Real.sq_sqrt (hw e)]
      ring

/-- Flow through the vertices of the set `T` as sources. -/
def outFlow (src : E → Finset ι) (flow : E → ℝ) (T : Finset ι) : ℝ :=
  ∑ e, flow e * (if src e = T then 1 else 0)

/-- Flow through the vertices of the set `T` as targets. -/
def inFlow (src : E → Finset ι) (j : E → ι) (flow : E → ℝ) (T : Finset ι) : ℝ :=
  ∑ e, flow e * (if dst src j e = T then 1 else 0)

omit [Fintype ι] [DecidableEq E] in
/-- No transition ends at the empty vertex. -/
theorem inFlow_empty (src : E → Finset ι) (j : E → ι) (flow : E → ℝ) :
    inFlow src j flow ∅ = 0 := by
  unfold inFlow dst
  refine Finset.sum_eq_zero fun e _ => ?_
  have hne : insert (j e) (src e) ≠ (∅ : Finset ι) := by
    intro h
    have : j e ∈ (∅ : Finset ι) := by
      rw [← h]
      exact Finset.mem_insert_self _ _
    exact absurd this (by simp)
  rw [if_neg hne, mul_zero]

/-- The coefficient of the positive witness on the available input vector of arc `e`:
`p_e / √w_e` (§3.3, positive witness size). -/
def posCoeff (w flow : E → ℝ) (e : E) : ℝ := flow e / Real.sqrt (w e)

/-- The vector produced by the positive witness at basis element `t_τ`. -/
def posTarget (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (flow : E → ℝ)
    (τ : Assn ι) : ℝ :=
  ∑ e, flow e * ((if τ = agreeing x (src e) then 1 else 0)
    - (if τ = agreeing x (dst src j e) then 1 else 0))

omit [DecidableEq E] in
/-- The indicator of `agreeing x T = agreeing x S` is the indicator of `S = T`. -/
theorem agreeing_indicator (x : ι → Bool) (T S : Finset ι) :
    (if agreeing x T = agreeing x S then (1 : ℝ) else 0) = if S = T then 1 else 0 := by
  by_cases h : S = T
  · subst h
    simp
  · have hne : agreeing x T ≠ agreeing x S := by
      intro hcon
      exact h ((agreeing_injective x) hcon.symm)
    simp [h, hne]

omit [DecidableEq E] in
/-- On a canonical assignment the positive witness telescopes to the difference of the
out-flow and the in-flow of the corresponding vertex set. -/
theorem posTarget_agreeing (x : ι → Bool) (src : E → Finset ι) (j : E → ι) (flow : E → ℝ)
    (T : Finset ι) :
    posTarget x src j flow (agreeing x T) = outFlow src flow T - inFlow src j flow T := by
  unfold posTarget outFlow inFlow
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [agreeing_indicator x T (src e), agreeing_indicator x T (dst src j e)]
  ring

omit [DecidableEq E] in
/-- Off the image of the canonical assignments the positive witness vanishes. -/
theorem posTarget_of_forall_ne (x : ι → Bool) (src : E → Finset ι) (j : E → ι)
    (flow : E → ℝ) (τ : Assn ι) (hne : ∀ T, τ ≠ agreeing x T) :
    posTarget x src j flow τ = 0 := by
  unfold posTarget
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg (hne (src e)), if_neg (hne (dst src j e))]
  ring

omit [DecidableEq E] in
/-- §3.3, positive witness: with the flow satisfying conservation at every vertex other
than `∅` and unit intensity at `∅`, the coefficients `p_e / √w_e` on the available input
vectors reproduce the target `t_∅`. (This is the form in which `Σ_e p_e²/w_e` is the
positive witness size: the flow reaching a sink is not absorbed into a free vector.) -/
theorem positive_witness_target (x : ι → Bool) (src : E → Finset ι) (j : E → ι)
    (flow : E → ℝ) (hcons : ∀ T : Finset ι, T ≠ ∅ → inFlow src j flow T = outFlow src flow T)
    (hsrc0 : outFlow src flow ∅ = 1) (τ : Assn ι) :
    posTarget x src j flow τ = if τ = agreeing x ∅ then 1 else 0 := by
  by_cases h : ∃ T, τ = agreeing x T
  · obtain ⟨T, rfl⟩ := h
    rw [posTarget_agreeing]
    by_cases hT : T = ∅
    · subst hT
      rw [hsrc0, inFlow_empty]
      simp
    · have hne : agreeing x T ≠ agreeing x ∅ := by
        intro hcon
        exact hT ((agreeing_injective x) hcon)
      rw [hcons T hT, sub_self, if_neg hne]
  · push Not at h
    rw [posTarget_of_forall_ne x src j flow τ h, if_neg (h ∅)]

omit [DecidableEq E] in
/-- The squared norm of the positive-witness coefficients is `Σ_e p_e²/w_e`, the positive
complexity of the learning graph. -/
theorem positive_witness_size (w flow : E → ℝ) (hw : ∀ e, 0 < w e) :
    (∑ e, posCoeff w flow e ^ 2) = ∑ e, flow e ^ 2 / w e := by
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold posCoeff
  rw [div_pow, Real.sq_sqrt (le_of_lt (hw e))]

omit [DecidableEq E] in
/-- The `k`-fold expansion of the arc set of §3.3 (non-Boolean case): each arc is replaced
by a path of `k` arcs of the same weight and flow, so a sum over the expanded arc set is
`k` times the sum over the original one. -/
theorem expand_sum (k : ℕ) (f : E → ℝ) :
    (∑ p : E × Fin k, f p.1) = (k : ℝ) * ∑ e, f e := by
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

/-- The `k`-fold expansion multiplies both the negative and the positive complexity by `k`,
hence the complexity `sqrt(N P)` by `k`: this is the `log m` factor of Theorem 3. -/
theorem expand_complexity (k : ℕ) (N P : ℝ) :
    Real.sqrt (((k : ℝ) * N) * ((k : ℝ) * P)) = (k : ℝ) * Real.sqrt (N * P) := by
  rw [show ((k : ℝ) * N) * ((k : ℝ) * P) = (k : ℝ) ^ 2 * (N * P) by ring,
    Real.sqrt_mul (sq_nonneg (k : ℝ)) (N * P), Real.sqrt_sq (Nat.cast_nonneg k)]

omit [DecidableEq E] in
/-- The negative witness size `Σ_e w_e` is the negative complexity of the learning graph
read with unit transition lengths: this is the first half of Theorem 3's identity
"witness size = complexity". -/
theorem negWitness_size_eq_negativeComplexity (w : E → ℝ) :
    (∑ e, w e) = negativeComplexity Finset.univ (fun _ : E => (1 : ℝ)) w := by
  unfold negativeComplexity
  simp

omit [DecidableEq E] in
/-- The positive witness size `Σ_e p_e²/w_e` is the positive complexity of the learning
graph read with unit transition lengths: the second half of the identity behind Theorem 3. -/
theorem positive_witness_size_eq_positiveComplexity (w flow : E → ℝ) :
    (∑ e, flow e ^ 2 / w e)
      = positiveComplexity Finset.univ (fun _ : E => (1 : ℝ)) flow w := by
  unfold positiveComplexity
  simp

end Qatlib.Papers.SpanPrograms11.MainResults
