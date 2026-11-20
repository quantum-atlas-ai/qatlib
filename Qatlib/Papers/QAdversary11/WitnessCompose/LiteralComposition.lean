/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.SplitIfs

/-!
# Positive-input span-program composition with explicit outcome programs

[Kimmel2011QuantumAdversary], Lemma 3 and Eq. (9), pp. 6–7 in
[arXiv:1101.0797v5](https://arxiv.org/abs/1101.0797v5).

The positive witness infimum is infinite on rejecting inputs. The accepted
input hypothesis avoids applying a positive-witness bound of Eq. (9) when
the outer infimum is infinite and the inner cost is zero.

This reconstruction supplies actual literal-labelled inner programs for both
Boolean outcomes. The composed program is the finite block linear system
F a = t_F and G_(label c) w_c = a_c t_(label c), with literal-supported inner
coefficients. Thus its matrix and support are uniform in the input, and the
output is derived from actual supported linear solutions. Free outer
coefficients are constrained by every inner block and cannot alone produce
an output. The identity example has minimum charged energy exactly one.

The named positive theorem is retained with an explicit accepted-input
premise, finite input costs, and the two outcome programs as input data.
Both inequalities follow from actual witness infima; no minimizing witness
or energy-bound conclusion is assumed. The proof uses finite independent
infimum distributivity, so it does not assume attainment.

The result covers the positive-input inequalities of Eq. (9) for the
paired-program model. The primal/dual identification with a single source
program, the negative-input bound, partial domains, and Eq. (10) remain open
in this model.
-/

public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QAdversary11.WitnessCompose.LiteralComposition

/-- A finite span program whose columns are labelled by actual input literals. -/
structure LiteralProgram (n N M : ℕ) where
  mat : Matrix (Fin M) (Fin N) ℂ
  target : Fin M → ℂ
  bit : Fin N → Fin n
  polarity : Fin N → Bool

namespace LiteralProgram

variable {n N M : ℕ}

/-- A column is available precisely when its input literal is true. -/
def available (P : LiteralProgram n N M) (x : Fin n → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun c => x (P.bit c) = P.polarity c

/-- Actual supported solutions of the finite linear system. -/
abbrev WitnessSet (P : LiteralProgram n N M) (x : Fin n → Bool) : Type :=
  {w : Fin N → ℂ //
    (∀ c, c ∉ P.available x → w c = 0) ∧ P.mat *ᵥ w = P.target}

/-- The literal-labelled program accepts exactly the one-inputs of a Boolean function. -/
def Computes (P : LiteralProgram n N M) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, Nonempty (P.WitnessSet x) ↔ f x = true

/-- The squared amplitude of one witness coefficient. -/
def energy (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖z‖ ^ 2)

/-- The actual weighted energy of a supported witness. -/
def cost (P : LiteralProgram n N M) (s : Fin n → ℝ≥0∞) (x : Fin n → Bool)
    (w : P.WitnessSet x) : ℝ≥0∞ :=
  ∑ c ∈ P.available x, s (P.bit c) * energy (w.1 c)

/-- The positive witness size, defined by minimization of actual linear solutions. -/
def wsizeS (P : LiteralProgram n N M) (s : Fin n → ℝ≥0∞) (x : Fin n → Bool) : ℝ≥0∞ :=
  ⨅ w : P.WitnessSet x, P.cost s x w

/-- The unweighted positive witness size. -/
def wsize1 (P : LiteralProgram n N M) (x : Fin n → Bool) : ℝ≥0∞ :=
  P.wsizeS (fun _ => 1) x

/-- The squared amplitude is finite. -/
theorem energy_ne_top (z : ℂ) : energy z ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The unit scalar has positive unit energy. -/
@[simp] theorem energy_one : energy (1 : ℂ) = 1 := by
  dsimp [energy]
  rw [Complex.norm_def]
  simp

/-- Tensoring scalar coefficients multiplies their squared amplitudes. -/
theorem energy_mul (a b : ℂ) : energy (a * b) = energy a * energy b := by
  simp only [energy, Complex.norm_mul, mul_pow]
  exact ENNReal.ofReal_mul (sq_nonneg _)

end LiteralProgram

open LiteralProgram

variable {n m NF MF NG MG : ℕ}

/-- The reconstructed finite linear reduction. Each outer column carries a free
coefficient, and its inner block must produce that coefficient times the inner
target. These are linear equations of a single finite block matrix. -/
structure Composition (n m NF MF NG MG : ℕ) where
  outer : LiteralProgram n NF MF
  inner : Bool → LiteralProgram m NG MG

namespace Composition

/-- The free outer coefficients and the charged inner coefficients. -/
abbrev Coefficients (_P : Composition n m NF MF NG MG) :=
  (Fin NF → ℂ) × (Fin NF → Fin NG → ℂ)

/-- Supported solutions to the actual composed linear equations. -/
abbrev WitnessSet (P : Composition n m NF MF NG MG) (x : Fin n → Fin m → Bool) : Type :=
  {w : P.Coefficients //
    P.outer.mat *ᵥ w.1 = P.outer.target ∧
    (∀ c, (P.inner (P.outer.polarity c)).mat *ᵥ w.2 c =
      w.1 c • (P.inner (P.outer.polarity c)).target) ∧
    ∀ c j, j ∉ (P.inner (P.outer.polarity c)).available (x (P.outer.bit c)) →
      w.2 c j = 0}

/-- Acceptance is witnessed by the finite block system. -/
def Computes (P : Composition n m NF MF NG MG)
    (f : (Fin n → Fin m → Bool) → Bool) : Prop :=
  ∀ x, Nonempty (P.WitnessSet x) ↔ f x = true

/-- Every inner coefficient is charged according to its actual queried literal. -/
def cost (P : Composition n m NF MF NG MG) (s : Fin n → Fin m → ℝ≥0∞)
    (x : Fin n → Fin m → Bool) (w : P.WitnessSet x) : ℝ≥0∞ :=
  ∑ c, ∑ j ∈ (P.inner (P.outer.polarity c)).available (x (P.outer.bit c)),
    s (P.outer.bit c) ((P.inner (P.outer.polarity c)).bit j) * energy (w.1.2 c j)

/-- Positive witness size of the composed linear system. -/
def wsizeS (P : Composition n m NF MF NG MG) (s : Fin n → Fin m → ℝ≥0∞)
    (x : Fin n → Fin m → Bool) : ℝ≥0∞ :=
  ⨅ w : P.WitnessSet x, P.cost s x w

/-- On each outer available literal, an actual inner witness is supplied. -/
abbrev InnerWitnesses (P : Composition n m NF MF NG MG)
    (g : (Fin m → Bool) → Bool) (x : Fin n → Fin m → Bool) :=
  ∀ c : {c // c ∈ P.outer.available (fun i => g (x i))},
    (P.inner (P.outer.polarity c.1)).WitnessSet (x (P.outer.bit c.1))

/-- The explicit tensor witness used by span-program composition. -/
def lift (P : Composition n m NF MF NG MG)
    (g : (Fin m → Bool) → Bool) (x : Fin n → Fin m → Bool)
    (a : P.outer.WitnessSet (fun i => g (x i)))
    (v : P.InnerWitnesses g x) : P.WitnessSet x := by
  let w : Fin NF → Fin NG → ℂ := fun c =>
    if hc : c ∈ P.outer.available (fun i => g (x i)) then a.1 c • (v ⟨c, hc⟩).1
    else 0
  refine ⟨(a.1, w), a.2.2, ?_, ?_⟩
  · intro c
    dsimp [w]
    split_ifs with hc
    · rw [Matrix.mulVec_smul, (v ⟨c, hc⟩).2.2]
    · rw [a.2.1 c hc]
      simp
  · intro c j hj
    dsimp [w]
    split_ifs with hc
    · simp [(v ⟨c, hc⟩).2.1 j hj]
    · rfl

/-- Correct inner programs provide precisely the active inner witnesses. -/
theorem innerWitnesses_nonempty (P : Composition n m NF MF NG MG)
    (g : (Fin m → Bool) → Bool)
    (hG : ∀ b x, Nonempty ((P.inner b).WitnessSet x) ↔ g x = b)
    (x : Fin n → Fin m → Bool) : Nonempty (P.InnerWitnesses g x) := by
  classical
  refine ⟨fun c => Classical.choice ((hG _ _).2 ?_)⟩
  exact (Finset.mem_filter.mp c.2).2

/-- A nonzero scaled inner solution can be divided to yield a genuine inner witness. -/
def unscale (P : LiteralProgram m NG MG) (x : Fin m → Bool)
    (a : ℂ) (ha : a ≠ 0) (w : Fin NG → ℂ)
    (hw : P.mat *ᵥ w = a • P.target)
    (hs : ∀ j, j ∉ P.available x → w j = 0) : P.WitnessSet x := by
  refine ⟨a⁻¹ • w, ?_, ?_⟩
  · intro j hj
    simp [hs j hj]
  · rw [Matrix.mulVec_smul, hw, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- The constructed linear reduction computes the composed Boolean function;
neither the matrix equations nor the literal support inspect the answer. -/
theorem computes (P : Composition n m NF MF NG MG)
    (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool)
    (hF : P.outer.Computes f)
    (hG : ∀ b x, Nonempty ((P.inner b).WitnessSet x) ↔ g x = b) :
    P.Computes (fun x => f (fun i => g (x i))) := by
  intro x
  constructor
  · rintro ⟨w⟩
    apply (hF _).1
    refine ⟨⟨w.1.1, ?_, w.2.1⟩⟩
    intro c hc
    by_contra ha
    have hin := (hG (P.outer.polarity c) (x (P.outer.bit c))).1
      ⟨unscale (P.inner (P.outer.polarity c)) (x (P.outer.bit c))
        (w.1.1 c) ha (w.1.2 c) (w.2.2.1 c) (w.2.2.2 c)⟩
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩)
  · intro hx
    obtain ⟨a⟩ := (hF _).2 hx
    obtain ⟨v⟩ := innerWitnesses_nonempty P g hG x
    exact ⟨P.lift g x a v⟩

/-- The energy of the constructed witness is the sum of the actual tensor-block
energies, with zero blocks on unavailable outer literals. -/
theorem cost_lift (P : Composition n m NF MF NG MG)
    (g : (Fin m → Bool) → Bool) (x : Fin n → Fin m → Bool)
    (s : Fin n → Fin m → ℝ≥0∞)
    (a : P.outer.WitnessSet (fun i => g (x i)))
    (v : P.InnerWitnesses g x) :
    P.cost s x (P.lift g x a v) =
      ∑ c : {c // c ∈ P.outer.available (fun i => g (x i))},
        energy (a.1 c.1) *
          (P.inner (P.outer.polarity c.1)).cost (s (P.outer.bit c.1))
            (x (P.outer.bit c.1)) (v c) := by
  classical
  unfold cost
  rw [← Finset.sum_subset (Finset.subset_univ (P.outer.available (fun i => g (x i))))
    (by
      intro c _ hc
      simp [lift, hc, energy])]
  rw [Finset.sum_coe_sort_eq_attach]
  conv_lhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro c _
  simp [lift, c.2, LiteralProgram.cost, Pi.smul_apply, smul_eq_mul,
    energy_mul, Finset.mul_sum, mul_left_comm]

/-- Finite independent witness choices commute with taking infima of their
nonnegative energies. This proves the variational bound without assuming that
the infimum is attained. -/
theorem iInf_pi_sum {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [∀ i, Nonempty (W i)] (e : ∀ i, W i → ℝ≥0∞) :
    (⨅ v : (∀ i, W i), ∑ i, e i (v i)) = ∑ i, ⨅ w : W i, e i w := by
  classical
  rw [ENNReal.iInf_sum (by
    intro t v u
    refine ⟨fun i => if e i (v i) ≤ e i (u i) then v i else u i, ?_⟩
    intro i _
    dsimp
    split_ifs with hi
    · exact ⟨le_rfl, hi⟩
    · exact ⟨le_of_not_ge hi, le_rfl⟩)]
  apply Finset.sum_congr rfl
  intro i _
  apply le_antisymm
  · refine le_iInf fun w => ?_
    exact iInf_le_of_le (Function.update (fun j => Classical.choice (inferInstance : Nonempty (W j)))
      i w) (by simp)
  · exact le_iInf fun v => iInf_le _ (v i)

/-- The composed witness infimum is bounded by the outer infimum weighted by
the actual inner witness sizes. -/
theorem wsize_le_weighted (P : Composition n m NF MF NG MG)
    (g : (Fin m → Bool) → Bool)
    (hG : ∀ b x, Nonempty ((P.inner b).WitnessSet x) ↔ g x = b)
    (s : Fin n → Fin m → ℝ≥0∞) (x : Fin n → Fin m → Bool) :
    P.wsizeS s x ≤ P.outer.wsizeS
      (fun i => (P.inner (g (x i))).wsizeS (s i) (x i)) (fun i => g (x i)) := by
  classical
  unfold LiteralProgram.wsizeS
  refine le_iInf fun a => ?_
  let A := {c // c ∈ P.outer.available (fun i => g (x i))}
  have : ∀ c : A,
      Nonempty ((P.inner (P.outer.polarity c.1)).WitnessSet (x (P.outer.bit c.1))) := by
    intro c
    apply (hG _ _).2
    exact (Finset.mem_filter.mp c.2).2
  calc
    P.wsizeS s x ≤ ⨅ v : P.InnerWitnesses g x, P.cost s x (P.lift g x a v) :=
      le_iInf fun v => iInf_le _ _
    _ = ⨅ v : P.InnerWitnesses g x, ∑ c : A,
          energy (a.1 c.1) * (P.inner (P.outer.polarity c.1)).cost
            (s (P.outer.bit c.1)) (x (P.outer.bit c.1)) (v c) := by
      apply iInf_congr
      intro v
      exact cost_lift P g x s a v
    _ = ∑ c : A, energy (a.1 c.1) *
          (P.inner (P.outer.polarity c.1)).wsizeS
            (s (P.outer.bit c.1)) (x (P.outer.bit c.1)) := by
      rw [iInf_pi_sum (I := A)
        (W := fun c : A => (P.inner (P.outer.polarity c.1)).WitnessSet
          (x (P.outer.bit c.1)))
        (fun c w => energy (a.1 c.1) * (P.inner (P.outer.polarity c.1)).cost
          (s (P.outer.bit c.1)) (x (P.outer.bit c.1)) w)]
      apply Finset.sum_congr rfl
      intro c _
      exact (ENNReal.mul_iInf (fun h => (energy_ne_top (a.1 c.1) h).elim)).symm
    _ = P.outer.cost (fun i => (P.inner (g (x i))).wsizeS (s i) (x i))
          (fun i => g (x i)) a := by
      rw [LiteralProgram.cost,
        Finset.sum_coe_sort (s := P.outer.available (fun i => g (x i)))
          (f := fun c : Fin NF => energy (a.1 c) *
            (P.inner (P.outer.polarity c)).wsizeS
              (s (P.outer.bit c)) (x (P.outer.bit c)))]
      apply Finset.sum_congr rfl
      intro c hc
      have hp : g (x (P.outer.bit c)) = P.outer.polarity c :=
        (Finset.mem_filter.mp hc).2
      rw [hp, mul_comm]

end Composition

namespace LiteralProgram

/-- Finite input costs give finite energy to every actual finite witness. -/
theorem cost_ne_top {n N M : ℕ} (P : LiteralProgram n N M)
    (s : Fin n → ℝ≥0∞) (hs : ∀ i, s i ≠ ⊤) (x : Fin n → Bool)
    (w : P.WitnessSet x) : P.cost s x w ≠ ⊤ := by
  apply ENNReal.sum_ne_top.2
  intro c _
  exact ENNReal.mul_ne_top (hs _) (energy_ne_top _)

/-- On an accepted input, finite input costs give a finite witness infimum. -/
theorem wsize_ne_top {n N M : ℕ} (P : LiteralProgram n N M)
    (s : Fin n → ℝ≥0∞) (hs : ∀ i, s i ≠ ⊤) (x : Fin n → Bool)
    (hx : Nonempty (P.WitnessSet x)) : P.wsizeS s x ≠ ⊤ := by
  obtain ⟨w⟩ := hx
  exact ne_top_of_le_ne_top (P.cost_ne_top s hs x w) (iInf_le _ w)

/-- The outer variational cost is bounded by its unweighted cost times the
largest finite input cost. The accepted-input premise prevents the empty
positive-witness infimum from masquerading as a dual witness size. -/
theorem weighted_le_max {n N M : ℕ} (P : LiteralProgram n N M)
    (r : Fin n → ℝ≥0∞) (hr : ∀ i, r i ≠ ⊤) (x : Fin n → Bool)
    (hx : Nonempty (P.WitnessSet x)) :
    P.wsizeS r x ≤ P.wsize1 x * Finset.univ.sup r := by
  have hmax : Finset.univ.sup r ≠ ⊤ :=
    ((Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)).2
      (fun i _ => (hr i).lt_top)).ne
  change (⨅ w : P.WitnessSet x, P.cost r x w) ≤
    (⨅ w : P.WitnessSet x, P.cost (fun _ => 1) x w) * Finset.univ.sup r
  -- Nonemptiness is essential when the maximum cost is zero: it is passed
  -- explicitly to the zero-factor case of infimum distributivity.
  rw [ENNReal.iInf_mul' (fun h => (hmax h).elim) (fun _ => hx)]
  refine le_iInf fun w => ?_
  calc
    (⨅ v : P.WitnessSet x, P.cost r x v) ≤ P.cost r x w := iInf_le _ w
    _ ≤ ∑ c ∈ P.available x, Finset.univ.sup r * energy (w.1 c) := by
      apply Finset.sum_le_sum
      intro c _
      have hi : r (P.bit c) ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ _)
      simpa [mul_comm] using _root_.mul_le_mul_right hi (energy (w.1 c))
    _ = P.cost (fun _ => 1) x w * Finset.univ.sup r := by
      simp [cost, Finset.mul_sum, mul_comm]

end LiteralProgram

/-- Positive-input span-program composition for literal-labelled outer programs
and explicit inner programs for both Boolean outcomes. The output is derived
from the finite block reduction, and both energy inequalities are proved from
the underlying witness infima. Identifying the paired inner programs with a
single source span program's primal/dual convention is a separate source bridge. -/
theorem span_program_composition
    (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool)
    (F : LiteralProgram n NF MF) (G : Bool → LiteralProgram m NG MG)
    (hF : F.Computes f)
    (hG : ∀ b x, Nonempty ((G b).WitnessSet x) ↔ g x = b)
    (s : Fin n → Fin m → ℝ≥0∞) (hs : ∀ i j, s i j ≠ ⊤)
    (x : Fin n → Fin m → Bool) (hx : f (fun i => g (x i)) = true) :
    ∃ P : Composition n m NF MF NG MG,
      P.outer = F ∧ P.inner = G ∧ P.Computes (fun xv => f (fun i => g (xv i))) ∧
      P.wsizeS s x ≤ F.wsizeS
        (fun i => (G (g (x i))).wsizeS (s i) (x i)) (fun i => g (x i)) ∧
      F.wsizeS (fun i => (G (g (x i))).wsizeS (s i) (x i)) (fun i => g (x i)) ≤
        F.wsize1 (fun i => g (x i)) *
          Finset.univ.sup (fun i => (G (g (x i))).wsizeS (s i) (x i)) := by
  let P : Composition n m NF MF NG MG := ⟨F, G⟩
  refine ⟨P, rfl, rfl, Composition.computes P f g hF hG,
    Composition.wsize_le_weighted P g hG s x, ?_⟩
  apply F.weighted_le_max _ _ _ ((hF _).2 hx)
  intro i
  exact (G (g (x i))).wsize_ne_top (s i) (hs i) (x i) ((hG _ _).2 rfl)

/-- A nonconstant one-bit literal program with a nonzero target. -/
def bitProgram (b : Bool) : LiteralProgram 1 1 1 where
  mat := 1
  target := fun _ => 1
  bit := fun _ => 0
  polarity := fun _ => b

/-- The one-bit program accepts exactly its labelled literal. -/
theorem bitProgram_accepts (b : Bool) (x : Fin 1 → Bool) :
    Nonempty ((bitProgram b).WitnessSet x) ↔ x 0 = b := by
  constructor
  · rintro ⟨w⟩
    by_contra hx
    have hz : w.1 0 = 0 := w.2.1 0 (by simp [available, bitProgram, hx])
    have ho : w.1 0 = 1 := by
      have h := congrFun w.2.2 0
      simpa [bitProgram] using h
    exact zero_ne_one (hz.symm.trans ho)
  · intro hx
    refine ⟨⟨fun _ => 1, ?_, ?_⟩⟩
    · intro c hc
      have hc0 : c = 0 := Subsingleton.elim _ _
      subst c
      exact (hc (by simp [available, bitProgram, hx])).elim
    · simp [bitProgram]

/-- The actual composition of two one-bit identity problems. -/
def identityComposition : Composition 1 1 1 1 1 1 :=
  ⟨bitProgram true, bitProgram⟩

/-- The composed finite equations evaluate the input bit, so both acceptance
and rejection occur in the reconstructed model. -/
theorem identity_computes : identityComposition.Computes (fun x => x 0 0) := by
  apply Composition.computes identityComposition (fun y => y 0) (fun z => z 0)
  · intro x
    exact bitProgram_accepts true x
  · exact bitProgram_accepts

/-- Every accepting witness of the one-bit composition has positive unit
energy: the output cannot be obtained through a free coefficient alone. -/
theorem identity_witness_cost
    (w : identityComposition.WitnessSet (fun _ _ => true)) :
    identityComposition.cost (fun _ _ => 1) (fun _ _ => true) w = 1 := by
  have ha : w.1.1 0 = 1 := by
    have h := congrFun w.2.1 0
    simpa [identityComposition, bitProgram] using h
  have hi : w.1.2 0 0 = w.1.1 0 := by
    have h := congrFun (w.2.2.1 0) 0
    simpa [identityComposition, bitProgram] using h
  simp [Composition.cost, identityComposition, bitProgram, available, hi, ha]

/-- The actual minimum energy for the identity composition is one, providing
a satisfiable, nonzero-cost positive example for the model. -/
theorem identity_wsize :
    identityComposition.wsizeS (fun _ _ => 1) (fun _ _ => true) = 1 := by
  have : Nonempty (identityComposition.WitnessSet (fun _ _ => true)) :=
    (identity_computes _).2 rfl
  simp only [Composition.wsizeS, identity_witness_cost, ciInf_const]

/-- The same finite reduction rejects the opposite input. -/
theorem identity_rejects :
    ¬ Nonempty (identityComposition.WitnessSet (fun _ _ => false)) := by
  rw [identity_computes]
  simp

end Qatlib.Papers.QAdversary11.WitnessCompose.LiteralComposition
