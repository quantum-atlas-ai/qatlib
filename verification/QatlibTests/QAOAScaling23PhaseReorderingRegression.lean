module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Papers.QAOAScaling23.PhaseCircuit.PhaseReordering

@[expose] public section

set_option autoImplicit false

namespace QatlibTests.QAOAScaling23

open Qatlib.Papers.QAOAScaling23.PhaseCircuit
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

/-- The first concrete qubit index. -/
def concreteQubit0 : Fin 4 := ⟨0, by norm_num⟩

/-- The second concrete qubit index. -/
def concreteQubit1 : Fin 4 := ⟨1, by norm_num⟩

/-- The third concrete qubit index. -/
def concreteQubit2 : Fin 4 := ⟨2, by norm_num⟩

/-- The fourth concrete qubit index. -/
def concreteQubit3 : Fin 4 := ⟨3, by norm_num⟩

/-- A genuine four-wire LABS coupling on a four-qubit register. -/
def concreteFourBody : FourBodyTerm 4 :=
  ⟨(concreteQubit0, concreteQubit1), (concreteQubit2, concreteQubit3)⟩

/-- The two-wire coupling at zero-based site `0` and lag `1` in Eq. (4). -/
def concreteTwoBody : WirePair 4 := (concreteQubit0, concreteQubit2)

/-- The concrete reordered pair is a list permutation, not a changed multiset. -/
theorem concrete_phase_perm :
    [Sum.inl concreteFourBody, Sum.inr concreteTwoBody].Perm
      [Sum.inr concreteTwoBody, Sum.inl concreteFourBody] :=
  List.Perm.swap _ _ _

/-- The concrete phase factors are unitary. -/
theorem concrete_phase_term_unitary :
    phaseTermMatrix (1 / 2 : ℝ) (.inl concreteFourBody) ∈
      Matrix.unitaryGroup (Reg 4) ℂ :=
  phaseTermMatrix_unitary _ _

/-- Reordering both concrete phase terms gives exactly the same matrix. -/
theorem concrete_phase_word_reordering :
    phaseWordMatrix (1 / 2 : ℝ)
        [Sum.inl concreteFourBody, Sum.inr concreteTwoBody] =
      phaseWordMatrix (1 / 2 : ℝ)
        [Sum.inr concreteTwoBody, Sum.inl concreteFourBody] :=
  phaseWordMatrix_perm _ concrete_phase_perm

/-- The uniform `L2Operator` estimate specializes to the concrete non-degenerate instance. -/
theorem concrete_phase_reordering_norm :
    ‖phaseWordMatrix (1 / 2 : ℝ)
        [Sum.inl concreteFourBody, Sum.inr concreteTwoBody] -
      phaseWordMatrix (1 / 2 : ℝ)
        [Sum.inr concreteTwoBody, Sum.inl concreteFourBody]‖ ≤ 1 := by
  obtain ⟨C, hC0, hC1, hbound⟩ := phase_reordering_norm_bound
  have hle := @hbound 4 (by norm_num) inferInstance (1 / 2 : ℝ)
    [Sum.inl concreteFourBody, Sum.inr concreteTwoBody]
    [Sum.inr concreteTwoBody, Sum.inl concreteFourBody] concrete_phase_perm
  exact hle.trans hC1

/-- The corrected greedy scheduler also preserves the concrete phase product. -/
theorem concrete_greedy_phase_word :
    phaseWordMatrix (1 / 2 : ℝ) (greedyOrder [concreteFourBody] [concreteTwoBody]) =
      phaseWordMatrix (1 / 2 : ℝ)
        [Sum.inl concreteFourBody, Sum.inr concreteTwoBody] :=
  greedy_phaseWordMatrix _ _ _

end QatlibTests.QAOAScaling23
