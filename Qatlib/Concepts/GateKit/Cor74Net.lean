/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharp
public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpCount
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Concepts.GateKit.MultiControl

/-!
# GateKit compiled Corollary 7.4 networks

For [BarencoEtAl1995], Corollary 7.4 (quant-ph/9503016v1), the compilation
exposes its target gate word and equates its denotation with the source operation.
This module packages the construction (`cor74Blocks`/`cor74Word`) as an
explicit compiled network `Cor74Net`, bridges its compiled circuit to the basis-state matrix
denotation `Denote`, and states exact correctness against a positioning-free ideal
multi-controlled NOT matrix `mcnotMatrix`.

Interface position for the epsilon-approximate variant (deliberately not imported and
not implemented here): the exact correctness field of this module is the equality
`Denote 1 net.circ = mcnotMatrix net.m net.ctl net.tgt`; an approximate synthesis
would replace it by `‖Denote 1 net.circ − ideal‖ ≤ ε` together with an
`(240 * (m + 1) + 20) * depth`-shaped budget in the style of the public
`lemma7_8_with_tolerance`, and `Cor74Net` embeds no budget numbers so that the exact
and approximate variants can share this structure.

Relation to placed-wire gates: `mcnotMatrix` is defined
entrywise as the ideal conjunction toggle and is not tied to any placed-selected
basis. A placed-selected representation requires a separate change-of-basis proof.

## Main statements

* `denoteRefl`: the denotation of a compiled reflection word is its program matrix.
* `cor74NetMatrix`: the compiled Corollary 7.4 denotation equals `mcnotMatrix`.
* `cor74DenoteEq`/`cor74NetUni`: ket-level correctness and unitarity of the product.
* `cor7Net`: the seven-wire satisfiable instance on seven wires, repackaged as a `Cor74Net 7`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Matrix
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.QueryWords

namespace Qatlib.Concepts.GateKit

/-- The matrix denotation of a compiled reflection word is exactly its program matrix,
so the word-level `Denote` bridge and the public `reflectionProgramMatrix` agree on every
legal or illegal reflection word. -/
theorem denoteRefl {n : ℕ} (gs : List (ReflectionGate n)) :
    Denote (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) = reflectionProgramMatrix gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    show Denote (1 : Matrix (Reg n) (Reg n) ℂ)
        (Step.gate (reflectionGateMatrix g) :: reflectionCompile gs) = _
    rw [denote_gate, ih, reflectionProgramMatrix]

/-- A legal reflection word compiles to a unitary circuit of pure gate steps. -/
theorem reflUniCirc {n : ℕ} (gs : List (ReflectionGate n)) (h : reflectionLegal gs) :
    IsUnitaryCircuit (reflectionCompile gs) :=
  (local_reflection_gate_support_unitarity_counts n gs h).1

/-- A compiled Corollary 7.4 network: the control count, the control-wire family, the
borrowed spectator wire, and the target wire, with the separation hypotheses demanded
by the public construction. The compiled product itself is read off through the
`blocks`, `word`, and `circ` accessors. -/
structure Cor74Net (N : ℕ) where
  /-- Number of control wires, at least five. -/
  m : ℕ
  /-- The control-wire family. -/
  ctl : ℕ → Fin N
  /-- The borrowed spectator wire, distinct from target and controls. -/
  spc : Fin N
  /-- The target wire. -/
  tgt : Fin N
  /-- The control count is at least five. -/
  hm : 5 ≤ m
  /-- The controls are pairwise distinct. -/
  hinj : Set.InjOn ctl (Set.Iio m)
  /-- Every control differs from the spectator wire. -/
  hneS : ∀ i < m, ctl i ≠ spc
  /-- Every control differs from the target wire. -/
  hneT : ∀ i < m, ctl i ≠ tgt
  /-- The spectator and target wires differ. -/
  hst : spc ≠ tgt

/-- The Toffoli block ledger of a compiled Corollary 7.4 network. -/
noncomputable def Cor74Net.blocks {N : ℕ} (net : Cor74Net N) : List (ToffBlock N) :=
  cor74Blocks net.m net.ctl net.spc net.tgt

/-- The elementary reflection-gate word of a compiled Corollary 7.4 network: the
actual compiled product whose semantics and counts are measured. -/
noncomputable def Cor74Net.word {N : ℕ} (net : Cor74Net N) : List (ReflectionGate N) :=
  cor74Word net.m net.ctl net.spc net.tgt

/-- The circuit form of a compiled Corollary 7.4 network: pure gate steps, no oracle
queries. -/
noncomputable def Cor74Net.circ {N : ℕ} (net : Cor74Net N) : Circuit (Reg N) :=
  reflectionCompile net.word

/-- The ideal multi-controlled NOT matrix of `m` controls and target `tgt`, defined
entrywise as the permutation of the conjunction toggle; it is positioning-free, so no
placement of cross-block CNOT pairs is assumed. -/
noncomputable def mcnotMatrix {N : ℕ} (m : ℕ) (ctl : ℕ → Fin N) (tgt : Fin N) :
    Matrix (Reg N) (Reg N) ℂ :=
  Matrix.of fun x y =>
    if x = Function.update y tgt (y tgt ^^ noWorkPrefixAnd (fun i => y (ctl i)) m) then 1 else 0

/-- The ideal multi-controlled NOT matrix sends every computational basis ket to the
toggled ket. -/
theorem mcnot_ket {N : ℕ} (m : ℕ) (ctl : ℕ → Fin N) (tgt : Fin N) (x : Reg N) :
    ApplyGate (mcnotMatrix m ctl tgt) (Ket x) =
      Ket (Function.update x tgt (x tgt ^^ noWorkPrefixAnd (fun i => x (ctl i)) m)) := by
  funext y
  simp only [ApplyGate, mcnotMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single x
    (fun z _ hz => by rw [ket_ne hz, mul_zero])
    (fun hcon => absurd (Finset.mem_univ x) hcon)]
  rw [ket_self, mul_one]
  rfl

/-- Two finite matrices agreeing on every computational basis ket are equal. -/
private theorem matEqOfKets {I : Type*} [Fintype I] [DecidableEq I] (M N : Matrix I I ℂ)
    (h : ∀ j, M *ᵥ Ket j = N *ᵥ Ket j) : M = N := by
  ext i j
  have h2 := congrFun (h j) i
  simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using h2

/-- Exact correctness of the compiled Corollary 7.4 network: the denotation of the
actual compiled circuit equals the ideal multi-controlled NOT matrix. -/
theorem cor74NetMatrix {N : ℕ} (net : Cor74Net N) :
    Denote (1 : Matrix (Reg N) (Reg N) ℂ) net.circ = mcnotMatrix net.m net.ctl net.tgt := by
  refine matEqOfKets _ _ (fun x => ?_)
  show ApplyGate (Denote (1 : Matrix (Reg N) (Reg N) ℂ) net.circ) (Ket x)
      = ApplyGate (mcnotMatrix net.m net.ctl net.tgt) (Ket x)
  rw [← run_denote]
  show Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (cor74Word net.m net.ctl net.spc net.tgt)) (Ket x) = _
  rw [cor74Word_semantics net.m net.ctl net.spc net.tgt net.hm net.hinj net.hneS net.hneT
    net.hst x, mcnot_ket]

/-- Ket-level correctness of the compiled Corollary 7.4 network: applying the
denotation of the produced circuit to a basis ket toggles the target by the control
conjunction. -/
theorem cor74DenoteEq {N : ℕ} (net : Cor74Net N) (x : Reg N) :
    ApplyGate (Denote (1 : Matrix (Reg N) (Reg N) ℂ) net.circ) (Ket x) =
      Ket (Function.update x net.tgt
        (x net.tgt ^^ noWorkPrefixAnd (fun i => x (net.ctl i)) net.m)) := by
  rw [← run_denote]
  show Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (cor74Word net.m net.ctl net.spc net.tgt)) (Ket x) = _
  exact cor74Word_semantics net.m net.ctl net.spc net.tgt net.hm net.hinj net.hneS net.hneT
    net.hst x

/-- The denotation of the compiled Corollary 7.4 network is unitary: legality of the
produced word carries unitarity through the `Denote` bridge. -/
theorem cor74NetUni {N : ℕ} (net : Cor74Net N) :
    Denote (1 : Matrix (Reg N) (Reg N) ℂ) net.circ ∈ Matrix.unitaryGroup (Reg N) ℂ :=
  denote_unitary 1 (Submonoid.one_mem _)
    (reflUniCirc net.word
      (BarencoSharpCount.cor74Word_legal net.m net.ctl net.spc net.tgt net.hm net.hinj
        net.hneS net.hneT net.hst))

/-- Below seven the control-wire function of the seven-wire instance is the canonical
embedding. -/
theorem cor7ctl_lt (i : ℕ) (hi : i < 7) : cor7Ctl i = ⟨i, hi⟩ := by
  simp only [cor7Ctl, dite_eq_left hi]

/-- The five chosen control wires of the seven-wire instance are pairwise distinct below
five. -/
theorem cor7ctlInj : Set.InjOn cor7Ctl (Set.Iio 5) := by
  intro i hi j hj he
  simp only [Set.mem_Iio] at hi hj
  rw [cor7ctl_lt i (by omega), cor7ctl_lt j (by omega)] at he
  exact congrArg Fin.val he

/-- Every chosen control wire of the seven-wire instance differs from the borrowed spectator
wire. -/
theorem cor7ctlNeSpc : ∀ i < 5, cor7Ctl i ≠ cor7Spc := by
  intro i hi he
  rw [cor7ctl_lt i (by omega : i < 7)] at he
  have hv := congrArg Fin.val he
  dsimp only [cor7Spc] at hv
  omega

/-- Every chosen control wire of the seven-wire instance differs from the target wire. -/
theorem cor7ctlNeTgt : ∀ i < 5, cor7Ctl i ≠ cor7Tgt := by
  intro i hi he
  rw [cor7ctl_lt i (by omega : i < 7)] at he
  have hv := congrArg Fin.val he
  dsimp only [cor7Tgt] at hv
  omega

/-- The borrowed spectator wire and the target wire of the seven-wire instance are
distinct. -/
theorem cor7spcNeTgt : cor7Spc ≠ cor7Tgt := by
  intro he
  have hv := congrArg Fin.val (he : cor7Spc = cor7Tgt)
  dsimp only [cor7Spc, cor7Tgt] at hv
  omega

/-- The seven-wire Corollary 7.4 instance repackaged as a compiled network with
five controls. -/
def cor7Net : Cor74Net 7 where
  m := 5
  ctl := cor7Ctl
  spc := cor7Spc
  tgt := cor7Tgt
  hm := by omega
  hinj := cor7ctlInj
  hneS := cor7ctlNeSpc
  hneT := cor7ctlNeTgt
  hst := cor7spcNeTgt

/-- The word of the repackaged seven-wire instance is exactly the reflection word `cor7Word`. -/
theorem cor7NetWord : (cor7Net : Cor74Net 7).word = cor7Word := rfl

end Qatlib.Concepts.GateKit
