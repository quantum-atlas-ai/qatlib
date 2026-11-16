/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section


/-! # Literal legacy Boolean-tree data and genuine finite path arithmetic

The old source incorrectly identifies the v3 theorem numbering as v1. Both
primary PDFs have now been checked; fixed source correlation remains under
review. These data preserve the entire old mathematical vocabulary, including
its missing tree/mark and statistical/algorithm couplings. In particular the
pointwise asymptotic relations do not assert any uniform asymptotic bound.
No source-paper theorem is certified by this vocabulary alone.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.Models


open Matrix
open scoped BigOperators Classical

/-! ## Direct span programs (Definitions 2.1–2.3) -/

/-- Definition 2.1: a span program for a direct boolean function on `c` input
bits.  The target vector is normalized to `t = e₀`, `v : Fin C → Fin c → ℂ` are
the columns `v_j`, and `flip j` records whether the label of bit `j` is `x_j`
(`flip j = false`) or `x̄_j` (`flip j = true`). -/
structure DirectSpanProgram (c : ℕ) where
  /-- dimension `C` of the target/row space -/
  C : ℕ
  /-- the target row exists -/
  hC : 0 < C
  /-- columns `v_j ∈ ℂ^C` -/
  v : Fin C → Fin c → ℂ
  /-- label convention: the label `χ_j` is `x_j` xor `flip j` -/
  flip : Fin c → Bool

namespace DirectSpanProgram

variable {c : ℕ}

/-- The target index `0 : Fin C`. -/
def target (sp : DirectSpanProgram c) : Fin sp.C := ⟨0, sp.hC⟩

/-- Definition 2.1: the label `χ_j` of bit `j` is `x_j` when `flip j = false`
and its negation when `flip j = true`. -/
def chi (sp : DirectSpanProgram c) (x : Fin c → Bool) (j : Fin c) : Bool :=
  x j != sp.flip j

/-- The `i`-th row `r_i` of the matrix `A = (v_1, …, v_c)`. -/
def row (sp : DirectSpanProgram c) (i : Fin sp.C) : Fin c → ℂ := fun j => sp.v i j

/-- Definition 2.1: `f` is represented by `sp` when, for every input `x`,
`f x = true` holds exactly if the target `e₀` is a linear combination of the
columns whose labels `χ_j` are `1`. -/
def Represents (sp : DirectSpanProgram c) (f : (Fin c → Bool) → Bool) : Prop :=
  ∀ x : Fin c → Bool,
    (f x = true) ↔
      ∃ a : Fin c → ℂ,
        (∀ j, sp.chi x j = false → a j = 0) ∧
        (∀ i : Fin sp.C,
          (∑ j, a j * sp.v i j) = if i = sp.target then (1 : ℂ) else 0)

/-- The input `x⁰` at which every label `χ_j` is `0`: `x⁰_j = flip j`. -/
def endpointZero (sp : DirectSpanProgram c) : Fin c → Bool := fun j => sp.flip j

/-- The input `x¹` at which every label `χ_j` is `1`: `x¹_j = ¬ flip j`. -/
def endpointOne (sp : DirectSpanProgram c) : Fin c → Bool := fun j => !(sp.flip j)

/-- At `x⁰` all labels vanish. -/
@[simp] theorem chi_endpointZero (sp : DirectSpanProgram c) (j : Fin c) :
    sp.chi (sp.endpointZero) j = false := by
  simp [chi, endpointZero]

/-- At `x¹` all labels are one. -/
@[simp] theorem chi_endpointOne (sp : DirectSpanProgram c) (j : Fin c) :
    sp.chi (sp.endpointOne) j = true := by
  cases h : sp.flip j <;> simp [chi, endpointOne, h]

/-- The witness cost `Σ_j s_j |w_j|²` of Definition 2.2. -/
def witnessCost (s : Fin c → ℝ) (w : Fin c → ℂ) : ℝ :=
  ∑ j, s j * ‖w j‖ ^ 2

/-- Definition 2.2, `f x = 1` branch: vectors `w` with `w†r₀ = 1`,
`w†rᵢ = 0` (`i > 0`) and `w_j = 0` whenever `χ_j = 0`.  Uses the bilinear
form of the `w†rᵢ` constraints (see module docstring). -/
def trueWitnessSet (sp : DirectSpanProgram c) (x : Fin c → Bool) : Set (Fin c → ℂ) :=
  {w |
    (∑ j, w j * sp.v sp.target j = 1) ∧
    (∀ i : Fin sp.C, i ≠ sp.target → (∑ j, w j * sp.v i j) = 0) ∧
    (∀ j, sp.chi x j = false → w j = 0)}

/-- Definition 2.2, `f x = 0` branch: `w` is a combination of the rows with
coefficient `1` on `r₀`, and `w_j = 0` whenever `χ_j = 1`. -/
def falseWitnessSet (sp : DirectSpanProgram c) (x : Fin c → Bool) : Set (Fin c → ℂ) :=
  {w |
    ∃ α : Fin sp.C → ℂ,
      α sp.target = 1 ∧
      (∀ j, w j = ∑ i, α i * sp.v i j) ∧
      (∀ j, sp.chi x j = true → w j = 0)}

/-- Definition 2.2 (`f x = 1`): `wsize` with unit costs, as an infimum. -/
def wsizeTrue (sp : DirectSpanProgram c) (x : Fin c → Bool) : ℝ :=
  sInf (witnessCost (fun _ => (1 : ℝ)) '' sp.trueWitnessSet x)

/-- Definition 2.2 (`f x = 0`): `wsize` with unit costs, as an infimum. -/
def wsizeFalse (sp : DirectSpanProgram c) (x : Fin c → Bool) : ℝ :=
  sInf (witnessCost (fun _ => (1 : ℝ)) '' sp.falseWitnessSet x)

/-- The witness size `wsize(P_D, x)` of Definition 2.2 (unit costs). -/
def witnessSize (sp : DirectSpanProgram c) (f : (Fin c → Bool) → Bool)
    (x : Fin c → Bool) : ℝ :=
  if f x then sp.wsizeTrue x else sp.wsizeFalse x

/-- Definition 2.3: a node is trivial when `wsize(P_D, x) = 1`. -/
def Trivial (sp : DirectSpanProgram c) (f : (Fin c → Bool) → Bool)
    (x : Fin c → Bool) : Prop :=
  sp.witnessSize f x = 1

/-- A boolean function is constant when it takes a single value. -/
def IsConstant {c : ℕ} (f : (Fin c → Bool) → Bool) : Prop :=
  ∃ r : Bool, ∀ x, f x = r

end DirectSpanProgram

/-! ## `k`-fault trees (Definition 1.1, Definitions 2.3–2.4) -/

/-- A complete `c`-ary evaluation tree of depth `n` with the paper's node
designations and the integer `κ` of Definition 1.1.

Nodes at level `l` are indexed by the child path `Fin l → Fin c`; `input l h` is
the input `(x_1, …, x_c)` of the node reached by `h`. -/
structure FaultTree (c n : ℕ) where
  /-- the input vector `(x_1, …, x_c)` of the node reached by the path `h` -/
  input : (l : Fin (n + 1)) → (Fin l.val → Fin c) → (Fin c → Bool)
  /-- Definition 2.3 designation -/
  isTrivial : (l : Fin (n + 1)) → (Fin l.val → Fin c) → Bool
  /-- Definition 2.4 designation: `isStrong l h b` for the `b`-th child -/
  isStrong : (l : Fin (n + 1)) → (Fin l.val → Fin c) → Fin c → Bool
  /-- Definition 1.1 integer `κ` -/
  kappa : (l : Fin (n + 1)) → (Fin l.val → Fin c) → ℕ
  /-- every node has at least one strong child -/
  strong_exists : ∀ (l : Fin (n + 1)) (h : Fin l.val → Fin c), ∃ b, isStrong l h b = true
  /-- `κ = 0` at leaves -/
  kappa_leaf : ∀ (h : Fin n → Fin c), kappa ⟨n, Nat.lt_succ_self n⟩ h = 0
  /-- the Definition 1.1 recursion for `κ` -/
  kappa_step : ∀ (l : ℕ) (hl : l < n) (h : Fin l → Fin c),
    kappa ⟨l, Nat.lt_succ_of_lt hl⟩ h =
      (if isTrivial ⟨l, Nat.lt_succ_of_lt hl⟩ h then 0 else 1) +
        (Finset.univ.sup (fun b : Fin c =>
          if isStrong ⟨l, Nat.lt_succ_of_lt hl⟩ h b then
            kappa ⟨l + 1, Nat.succ_lt_succ hl⟩ (Fin.snoc h b) else 0))

/-- A tree satisfies the `k`-faults condition when `κ ≤ k` at every node
(Definition 1.1). -/
def FaultTree.KFault {c n : ℕ} (T : FaultTree c n) (k : ℕ) : Prop :=
  ∀ (l : Fin (n + 1)) (h : Fin l.val → Fin c), T.kappa l h ≤ k

/-- The first `l` coordinates of a root-to-leaf path. -/
def pathPrefix {c n : ℕ} (p : Fin n → Fin c) (l : Fin n) : Fin l.val → Fin c :=
  fun i => p ⟨i.val, Nat.lt_trans i.isLt l.isLt⟩

/-- A path that only takes strong child steps.  The `κ` recursion of
Definition 1.1 controls exactly these paths. -/
def FaultTree.StrongPath {c n : ℕ} (T : FaultTree c n) (p : Fin n → Fin c) : Prop :=
  ∀ l : Fin n,
    T.isStrong ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩ (pathPrefix p l) (p ⟨l.val, l.isLt⟩) = true

/-- The product of the witness sizes along the internal levels of a path: the
first-order query cost of Section 2.2 (`wsize = 1` at trivial nodes). -/
def pathProduct {c n : ℕ} (sp : DirectSpanProgram c) (f : (Fin c → Bool) → Bool)
    (T : FaultTree c n) (p : Fin n → Fin c) : ℝ :=
  ∏ l : Fin n,
    sp.witnessSize f (T.input ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩ (pathPrefix p l))

/-- The maximum path product over strong paths (the leading term of the
subformula complexity). -/
def strongPathMaxProduct {c n : ℕ} (sp : DirectSpanProgram c)
    (f : (Fin c → Bool) → Bool) (T : FaultTree c n) : ℝ :=
  sSup (Set.range (fun p : {p : Fin n → Fin c // T.StrongPath p} =>
    pathProduct sp f T p.val))

/-- The span-program query count of Section 2.2: `n²` times the leading path
product, which is what the paper bounds by `O(n² ω^k)`. -/
def treeQueryCount {c n : ℕ} (sp : DirectSpanProgram c) (f : (Fin c → Bool) → Bool)
    (T : FaultTree c n) : ℝ :=
  (n : ℝ) ^ 2 * strongPathMaxProduct sp f T

/-- The source constant `ω = max_x wsize(P_D, x)` of Theorem 1.2, as a supremum
over all inputs. -/
def omegaBound {c : ℕ} (sp : DirectSpanProgram c) (f : (Fin c → Bool) → Bool) : ℝ :=
  sSup (Set.range (fun x : Fin c → Bool => sp.witnessSize f x))

/-- The existence of hard base distributions `T_{k₀}` of depth `n₀` used by
Theorem B.1: a depth-`n₀` tree satisfying the `k₀`-fault condition. -/
def HasHardBaseDistributions (c k₀ n₀ : ℕ) : Prop :=
  ∃ T : FaultTree c n₀, T.KFault k₀

/-! ## Lemma C.1 — the division process  -/

/-- The prefix of an outcome path used by the adaptive choice `p_τ`. -/
def divisionPathPrefix {m : ℕ} (ω : Fin m → Bool) (τ : Fin m) : Fin τ.val → Bool :=
  fun i => ω ⟨i.val, Nat.lt_trans i.isLt τ.isLt⟩

/-- The multiplicative step `A_{τ+1} / A_τ`: `p_τ` on outcome `true`, `1 - p_τ`
on outcome `false`, where `p_τ` may depend on the whole previous path. -/
def stepFactor (p : (τ : ℕ) → (Fin τ → Bool) → ℝ) {m : ℕ} (ω : Fin m → Bool)
    (τ : Fin m) : ℝ :=
  if ω τ then p τ.val (divisionPathPrefix ω τ) else 1 - p τ.val (divisionPathPrefix ω τ)

/-- The ratio `A_m / A_0` for the outcome path `ω`. -/
def intervalRatio (p : (τ : ℕ) → (Fin τ → Bool) → ℝ) {m : ℕ}
    (ω : Fin m → Bool) : ℝ :=
  ∏ τ : Fin m, stepFactor p ω τ

/-- Every step factor lies in `[0, 1]` when `p` does. -/
theorem stepFactor_nonneg {m : ℕ} (p : (τ : ℕ) → (Fin τ → Bool) → ℝ)
    (hp : ∀ (τ : ℕ) (h : Fin τ → Bool), 0 ≤ p τ h ∧ p τ h ≤ 1)
    (ω : Fin m → Bool) (τ : Fin m) : 0 ≤ stepFactor p ω τ := by
  unfold stepFactor
  split_ifs with h
  · exact (hp τ.val (divisionPathPrefix ω τ)).1
  · have := (hp τ.val (divisionPathPrefix ω τ)).2
    linarith

/-- The ratio `A_m / A_0` is nonnegative. -/
theorem intervalRatio_nonneg {m : ℕ} (p : (τ : ℕ) → (Fin τ → Bool) → ℝ)
    (hp : ∀ (τ : ℕ) (h : Fin τ → Bool), 0 ≤ p τ h ∧ p τ h ≤ 1)
    (ω : Fin m → Bool) : 0 ≤ intervalRatio p ω := by
  unfold intervalRatio
  exact Finset.prod_nonneg (fun τ _ => stepFactor_nonneg p hp ω τ)

/-- Lemma C.1 (division process), arXiv:1101.0796v3, Appendix C.1
p. 16–17.

For an interval of length `A₀` divided by an *adaptive* sequence `p_τ ∈ [0,1]`
(`A_{τ+1} = p_τ A_τ` with probability `p_τ` and `(1-p_τ) A_τ` with probability
`1-p_τ`), and `0 < F < 1`, the probability that `A_m < F A₀` is less than
`2^m F`, uniformly over all choices of `p_τ`.

Formalisation of the source proof: each adaptive strategy is a map
`p : τ ↦ p_τ` on outcome prefixes; over the adaptive path weights on `Fin m → Bool`
there are at most `2^m` outcome intervals, and those with `A_m/A₀ < F` have
total mass `< 2^m F`.  The Lean proof runs exactly this argument: the tail mass
is `Σ_{ω : ratio < F} ratio`, bounded by `card ≤ 2^m` times `F` via
`Finset.sum_lt_sum`, `Finset.card_le_univ` and `Fintype.card_fun`. -/
theorem divisionBound (m : ℕ) (p : (τ : ℕ) → (Fin τ → Bool) → ℝ)
    (F : ℝ) (hF : 0 < F) :
    (∑ ω : Fin m → Bool, if intervalRatio p ω < F then intervalRatio p ω else 0)
      < (2 : ℝ) ^ m * F := by
  classical
  rw [← Finset.sum_filter]
  set s := (Finset.univ : Finset (Fin m → Bool)).filter (fun ω => intervalRatio p ω < F)
  rcases s.eq_empty_or_nonempty with hEmpty | hNonempty
  · rw [hEmpty]
    simp only [Finset.sum_empty]
    positivity
  · have hlt : Finset.sum s (fun ω => intervalRatio p ω) < (s.card : ℝ) * F := by
      have h2 : Finset.sum s (fun ω => intervalRatio p ω) < Finset.sum s (fun _ => F) := by
        apply Finset.sum_lt_sum
        · intro ω hω
          exact le_of_lt (Finset.mem_filter.mp hω).2
        · obtain ⟨ω₀, hω₀⟩ := hNonempty
          exact ⟨ω₀, hω₀, (Finset.mem_filter.mp hω₀).2⟩
      rwa [Finset.sum_const, nsmul_eq_mul] at h2
    have hcard : (s.card : ℝ) ≤ (2 : ℝ) ^ m := by
      have h1 : s.card ≤ Fintype.card (Fin m → Bool) := Finset.card_le_univ s
      have h2 : Fintype.card (Fin m → Bool) = 2 ^ m := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      rw [h2] at h1
      have h3 : ((s.card : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
      simpa [Nat.cast_pow] using h3
    exact lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_right hcard (le_of_lt hF))

/-! ## Lower-bound ledger (Definitions B.3, B.4, C.1, C.2) -/

/-- Definition C.1: the per-category exclusion-probability family
`p_cat(i, r)`, `i ∈ {1, …, ñ}`, `r ∈ {0,1}`, all nonnegative. -/
structure CategoryLedger (ntilde : ℕ) where
  /-- `p_cat(i, r)` for category `i` and root value `r` -/
  pcat : Fin ntilde → Bool → ℝ
  /-- the source probabilities are nonnegative -/
  nonneg : ∀ (i : Fin ntilde) (r : Bool), 0 ≤ pcat i r

namespace CategoryLedger

variable {ntilde : ℕ}

/-- `S = Σ_{i,r} p_cat(i,r)` of Appendix C. -/
def S (L : CategoryLedger ntilde) : ℝ := ∑ i, ∑ r, L.pcat i r

/-- `D = Σ_i |p_cat(i,0) − p_cat(i,1)|` of Appendix C. -/
def D (L : CategoryLedger ntilde) : ℝ := ∑ i, |L.pcat i true - L.pcat i false|

/-- `p_root(g, r) = Σ_i p_cat(g, i, r)` (Eq. (14)); only the ratio matters. -/
def proot (L : CategoryLedger ntilde) (r : Bool) : ℝ := ∑ i, L.pcat i r

/-- The confidence level `D / S` of Eq. (14). -/
def confidence (L : CategoryLedger ntilde) : ℝ := L.D / L.S

end CategoryLedger

/-- Definition B.4: `p ≲ q` means `p ≤ q · (1 + C β^α ñ^γ)` for fixed
`α > 0`, `γ < 0` and a factor `C` that may grow polynomially in `k`.  The
polynomial dependence on `k` is left implicit in `C`, exactly as in the source
(the constants are re-chosen at each induction step). -/
def AsymptLess (β : ℕ) (ntilde : ℝ) (p q : ℝ) : Prop :=
  ∃ C α γ : ℝ, 0 < α ∧ γ < 0 ∧ p ≤ q * (1 + C * (β : ℝ) ^ α * ntilde ^ γ)

/-- Definition B.4: the companion `p ≳ q`, i.e. `p ≥ q · (1 − C β^α ñ^γ)`. -/
def AsymptGreater (β : ℕ) (ntilde : ℝ) (p q : ℝ) : Prop :=
  ∃ C α γ : ℝ, 0 < α ∧ γ < 0 ∧ q * (1 - C * (β : ℝ) ^ α * ntilde ^ γ) ≤ p

/-- A finite probability space of hard-distribution trees, carrying the root
label, the number of leaf evaluations, and the induced category ledger.  The
tree law itself is the paper's `T_k` construction of Section B.2 and is not
re-formulated here; this structure is its carrier. -/
structure LowerBoundExperiment (ntilde : ℕ) where
  Ω : Type
  [fintype : Fintype Ω]
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum_one : (∑ ω, weight ω) = 1
  /-- the root value of the sampled tree -/
  rootValue : Ω → Bool
  /-- number of leaves the algorithm has evaluated -/
  evalCount : Ω → ℕ
  /-- the induced CategoryLedger -/
  ledger : Ω → CategoryLedger ntilde

namespace LowerBoundExperiment

variable {ntilde : ℕ}

/-- Probability of an event, as the total weight of its outcomes. -/
def prob (E : LowerBoundExperiment ntilde) (P : E.Ω → Prop) : ℝ := by
  classical
  letI := E.fintype
  exact Finset.sum (Finset.univ : Finset E.Ω) (fun ω => if P ω then E.weight ω else 0)

/-- The experiment is a weighted combination of `T_{k,0}` and `T_{k,1}`: both
root values carry positive mass (the weights may change between evaluations;
that is already allowed by the finite outcome space). -/
def IsRootMixture (E : LowerBoundExperiment ntilde) : Prop :=
  0 < E.prob (fun ω => E.rootValue ω = true) ∧
  0 < E.prob (fun ω => E.rootValue ω = false)

end LowerBoundExperiment

/-- The confidence upper bound `c_{k,l}` of Lemma B.1, Eq. (13):
`(8 n₀)^{k-l+1} ñ^{-3(k-l+1)/5} β^{4+6(k-l)}`. -/
def cKL (N n₀ k l β : ℕ) : ℝ :=
  (8 * (n₀ : ℝ)) ^ (k - l + 1) * (N : ℝ) ^ (-(3 : ℝ) * (k - l + 1) / 5) *
    (β : ℝ) ^ (4 + 6 * (k - l))

/-- Appendix C.2 experiment: the same finite probability space, now carrying
the three exception indicators `Type I`, `Type II` (lucky division) and
`Type III` (low bias ratio), and the level `l`. -/
structure ExceptionExperiment (ntilde : ℕ) where
  Ω : Type
  [fintype : Fintype Ω]
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum_one : (∑ ω, weight ω) = 1
  evalCount : Ω → ℕ
  /-- at least one exception occurred on a subtree -/
  oneException : Ω → Bool
  /-- a Type I exception (two subtree exceptions) occurred -/
  typeI : Ω → Bool
  /-- a Type III exception occurred -/
  typeIII : Ω → Bool
  /-- the iteration level `l` of Lemma B.1 -/
  level : ℕ

namespace ExceptionExperiment

variable {ntilde : ℕ}

/-- Probability of a Boolean event indicator. -/
def probBool (E : ExceptionExperiment ntilde) (b : E.Ω → Bool) : ℝ := by
  classical
  letI := E.fintype
  exact Finset.sum (Finset.univ : Finset E.Ω)
    (fun ω => if b ω = true then E.weight ω else 0)

end ExceptionExperiment

/-- A classical algorithm on the hard distribution, abstracted by its success
probability and its expected number of leaf evaluations (the two quantities the
lower bound constrains). -/
structure ClassicalTreeAlgorithm where
  /-- success probability on the hard distribution -/
  successProb : ℝ
  /-- expected number of leaf evaluations on the hard distribution -/
  expectedQueriesOnHard : ℝ
  successProb_nonneg : 0 ≤ successProb
  successProb_le_one : successProb ≤ 1

/-- The confidence level `|p_root(g,0) − p_root(g,1)| / (p_root(g,0) + p_root(g,1))`
of Definition B.3. -/
def confidenceLevel (p0 p1 : ℝ) : ℝ := |p0 - p1| / (p0 + p1)

/-- Definition C.2: the bias ratio `p_partial(g) / p_partial(a)`, given the
probability `pg` that the leaf value `r₀` obtains using only information from
leaves below the root `g`, and the probability `pa` using only leaves below the
subtree root `a`. -/
def biasRatio (pg pa : ℝ) : ℝ := pg / pa

/-- Definition C.2: a Type III exception at level `l`, with `β` the source
parameter: the bias ratio is below `2 β^{-3}`. -/
def IsTypeIII (β : ℕ) (pg pa : ℝ) : Prop :=
  biasRatio pg pa < 2 * (β : ℝ) ^ (-(3 : ℝ))

/-! ## Lemma C.3 helpers (subset mass) -/

/-- `Σ_{i ∈ W} b_i` for a subset `W ⊆ {1, …, N}` encoded as a boolean vector. -/
def subsetSum {N : ℕ} (b : Fin N → ℝ) (W : Fin N → Bool) : ℝ :=
  ∑ i, if W i then b i else 0

/-- The Bernoulli-`q` mass of a subset `W`. -/
def bernoulliMass {N : ℕ} (q : ℝ) (W : Fin N → Bool) : ℝ :=
  ∏ i, if W i then q else 1 - q

/-- The mass of subsets whose `b`-sum exceeds `β^k` (the probability bounded by
Lemma C.3). -/
def subsetTailMass {N : ℕ} (b : Fin N → ℝ) (β k : ℕ) : ℝ := by
  classical
  exact ∑ W : Fin N → Bool,
    if subsetSum b W > (β : ℝ) ^ k then bernoulliMass (((β : ℝ) ^ 2)⁻¹) W else 0


end Qatlib.Papers.BoolEvalTree11.MainResults.Models
