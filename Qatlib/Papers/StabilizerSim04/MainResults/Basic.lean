/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerRun
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizer
import Qatlib.Concepts.CliffordTheory.TableauSim
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StabilizerSim04.MainResults

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CliffordTheory.TableauSim
open Qatlib.Concepts.PauliClifford.ExactRank
open Matrix
open scoped Classical BigOperators

def KetZero (n : ℕ) : QState (Reg n) := Ket (ZeroStr n)

def standardDestabilizer (n : ℕ) : Tableau n n :=
  fun i => ⟨fun k => decide (k = i), fun _ => false, 0⟩

def standardStabilizer (n : ℕ) : Tableau n n :=
  fun i => ⟨fun _ => false, fun k => decide (k = i), 0⟩

def ZAt {n : ℕ} (a : Fin n) : PauliElem n :=
  ⟨fun k => if k = a then Pauli1.Z else Pauli1.I, 0⟩

def CliffordPrep {n : ℕ} (ψ : QState (Reg n)) : Prop :=
  ∃ gs : List (CliffordGate n),
    (∀ g ∈ gs, legalGate g) ∧ ψ = Uword gs *ᵥ KetZero n

def MeasuredCliffordPrep {n : ℕ} (ψ : QState (Reg n)) : Prop :=
  ∃ (prog : Program n n) (tape : List Bool) (result : PhysicalResult n n),
    physicalExecute prog (initial (standardStabilizer n) tape) (KetZero n) = some result ∧
      result.state = ψ

def StabilizerCountEq {n : ℕ} (ψ : QState (Reg n)) (k : ℕ) : Prop :=
  Nat.card {p : PauliElem n // op p *ᵥ ψ = ψ} = k

def DeterminedByPauliStabilizer {n : ℕ} (ψ : QState (Reg n)) : Prop :=
  ∀ φ : QState (Reg n), Normalized φ →
    (∀ p : PauliElem n, op p *ᵥ ψ = ψ ↔ op p *ᵥ φ = φ) →
      ∃ c : ℂ, c ≠ 0 ∧ φ = c • ψ

theorem mem_generatedGroup_of_mem {n : ℕ} {gs : List (PauliElem n)} {p : PauliElem n}
    (hp : p ∈ gs) : p ∈ generatedGroup gs :=
  ⟨[p], by simpa using! hp, by simp [pauliElem_one_mul]⟩

def GeneratesStabilizer {n : ℕ} (S : Tableau n n) (ψ : QState (Reg n)) : Prop :=
  ∀ p : PauliElem n, (op p *ᵥ ψ = ψ) ↔ p ∈ generatedGroup (tableauGenerators S)

def GeneratesPauliGroup {n : ℕ} (D S : Tableau n n) : Prop :=
  ∀ p : PauliElem n, p ∈ generatedGroup (tableauGenerators D ++ tableauGenerators S)

def TableauInvariant {n : ℕ} (D S : Tableau n n) (ψ : QState (Reg n)) : Prop :=
  (GeneratesStabilizer S ψ ∧ GeneratesPauliGroup D S) ∧
  (∀ i j : Fin n, pauliCommute (D i).decode (D j).decode) ∧
  (∀ h : Fin n, ¬ pauliCommute (D h).decode (S h).decode) ∧
  (∀ i h : Fin n, i ≠ h → pauliCommute (D i).decode (S h).decode)

def IsPureStabilizerGroup {n : ℕ} (G : Finset (PauliElem n)) : Prop :=
  (∀ p ∈ G, IsHermitianPauli p) ∧
  (∀ p ∈ G, ∀ q ∈ G, PauliElem.mul p q ∈ G) ∧
  (1 : PauliElem n) ∈ G ∧ G.card = 2 ^ n

def PureStabilizerStateCount (n : ℕ) : ℕ :=
  Nat.card {G : Finset (PauliElem n) // IsPureStabilizerGroup G}

def innerProduct {n : ℕ} (ψ φ : QState (Reg n)) : ℂ :=
  ∑ x : Reg n, star (ψ x) * φ x

def gateChain {n m : ℕ} : List (CliffordGate n) → Program n m
  | [] => .halt
  | g :: gs => .gate g (gateChain gs)

theorem Uword_cons {n : ℕ} (g : CliffordGate n) (gs : List (CliffordGate n)) :
    Uword (g :: gs) = Uword gs * cliffordGateOp n g := by
  have aux : ∀ A : Matrix (Reg n) (Reg n) ℂ,
      gs.foldl (fun U g => cliffordGateOp n g * U) A
        = gs.foldl (fun U g => cliffordGateOp n g * U) 1 * A := by
    intro A
    induction gs generalizing A with
    | nil => simp
    | cons g gs ih =>
        simp only [List.foldl_cons]
        rw [ih (cliffordGateOp n g * A), Matrix.mul_one, ih (cliffordGateOp n g),
          Matrix.mul_assoc]
  simp only [Uword, List.foldl_cons]
  rw [Matrix.mul_one, aux]

@[simp] theorem Uword_singleton {n : ℕ} (g : CliffordGate n) :
    Uword [g] = cliffordGateOp n g := by
  simp [Uword]

theorem physicalExecute_gateChain {n m : ℕ} (gs : List (CliffordGate n))
    (s : Machine n m) (ψ : QState (Reg n)) :
    ∃ m' : Machine n m,
      physicalExecute (gateChain gs) s ψ = some ⟨m', Uword gs *ᵥ ψ, 1⟩ := by
  induction gs generalizing s ψ with
  | nil =>
      exact ⟨s, by simp [gateChain, physicalExecute, Uword]⟩
  | cons g gs ih =>
      obtain ⟨m', hm'⟩ := ih (gateStep s g) (Uword [g] *ᵥ ψ)
      have hstate : Uword gs *ᵥ (Uword [g] *ᵥ ψ) = Uword (g :: gs) *ᵥ ψ := by
        rw [Matrix.mulVec_mulVec ψ (Uword gs) (Uword [g]), Uword_singleton, ← Uword_cons]
      refine ⟨m', ?_⟩
      simp only [gateChain, physicalExecute]
      rw [hm']
      simpa using! congrArg (fun v => some (PhysicalResult.mk m' v 1)) hstate

theorem theorem1_measurement_closure {n : ℕ} {ψ : QState (Reg n)}
    (h : CliffordPrep ψ) : MeasuredCliffordPrep ψ := by
  obtain ⟨gs, -, rfl⟩ := h
  obtain ⟨m', hm'⟩ := physicalExecute_gateChain (m := n) gs
    (initial (standardStabilizer n) []) (KetZero n)
  exact ⟨gateChain gs, [], ⟨m', _, 1⟩, hm', rfl⟩

def theorem1_four_conditions_statement : Prop :=
  ∀ (n : ℕ) (ψ : QState (Reg n)), Normalized ψ →
    (CliffordPrep ψ ↔ MeasuredCliffordPrep ψ) ∧
      (MeasuredCliffordPrep ψ ↔ StabilizerCountEq ψ (2 ^ n)) ∧
      (StabilizerCountEq ψ (2 ^ n) ↔ DeterminedByPauliStabilizer ψ)

theorem theorem1_determination_bridge {n : ℕ} (S : Tableau n n) {ψ : QState (Reg n)}
    (hS : ConsistentTableau S) (hind : IndependentGenerators (tableauGenerators S))
    (hgen : GeneratesStabilizer S ψ) (hNψ : Normalized ψ) :
    ∀ φ : QState (Reg n), Normalized φ →
      (∀ p : PauliElem n, op p *ᵥ ψ = ψ ↔ op p *ᵥ φ = φ) →
        ∃ c : ℂ, c ≠ 0 ∧ φ = c • ψ := by
  intro φ hNφ hset
  have hrow : ∀ a : Fin n, (S a).decode ∈ tableauGenerators S :=
    fun a => List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩
  have hmemψ : ψ ∈ codeSpace S := by
    rw [mem_codeSpace_iff]
    intro a
    exact (hgen (S a).decode).2 (mem_generatedGroup_of_mem (hrow a))
  have hmemφ : φ ∈ codeSpace S := by
    rw [mem_codeSpace_iff]
    intro a
    exact (hset (S a).decode).1
      ((hgen (S a).decode).2 (mem_generatedGroup_of_mem (hrow a)))
  exact unique_stabilizerState S hS (by simp [tableauGenerators]) hind ψ φ hmemψ hmemφ hNψ hNφ

theorem verifiedCliffordAction_word {n : ℕ} (g : CliffordGate n) (p : PauliElem n) :
    (verifiedCliffordAction g p).word = (cliffordAction g p).word := by
  cases g <;> rfl

theorem pauliCommute_verifiedCliffordAction {n : ℕ} (g : CliffordGate n)
    (hg : legalGate g) (p q : PauliElem n) :
    pauliCommute (verifiedCliffordAction g p) (verifiedCliffordAction g q) ↔
      pauliCommute p q := by
  have he := symplecticForm_cliffordAction g hg p q
  simp only [symplecticVec] at he
  simp only [pauliCommute, verifiedCliffordAction_word]
  rw [he]

theorem tableauCommutation_preserved {n : ℕ} (D S : Tableau n n) (g : CliffordGate n)
    (hg : legalGate g)
    (hDD : ∀ i j : Fin n, pauliCommute (D i).decode (D j).decode)
    (hDS : ∀ h : Fin n, ¬ pauliCommute (D h).decode (S h).decode)
    (hDS' : ∀ i h : Fin n, i ≠ h → pauliCommute (D i).decode (S h).decode) :
    (∀ i j, pauliCommute ((update g D) i).decode ((update g D) j).decode) ∧
      (∀ h, ¬ pauliCommute ((update g D) h).decode ((update g S) h).decode) ∧
      (∀ i h, i ≠ h →
        pauliCommute ((update g D) i).decode ((update g S) h).decode) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [show (update g D) i = (D i).update g from rfl,
      show (update g D) j = (D j).update g from rfl,
      decode_update g hg, decode_update g hg]
    exact (pauliCommute_verifiedCliffordAction g hg _ _).2 (hDD i j)
  · intro h
    rw [show (update g D) h = (D h).update g from rfl,
      show (update g S) h = (S h).update g from rfl,
      decode_update g hg, decode_update g hg]
    exact fun hc => hDS h ((pauliCommute_verifiedCliffordAction g hg _ _).1 hc)
  · intro i h hih
    rw [show (update g D) i = (D i).update g from rfl,
      show (update g S) h = (S h).update g from rfl,
      decode_update g hg, decode_update g hg]
    exact (pauliCommute_verifiedCliffordAction g hg _ _).2 (hDS' i h hih)

theorem stdDestab_word (n : ℕ) (i : Fin n) :
    (standardDestabilizer n i).decode.word = fun k => if k = i then Pauli1.X else Pauli1.I := by
  funext k
  by_cases h : k = i <;> simp [standardDestabilizer, Row.decode, letter, h]

theorem stdStab_word (n : ℕ) (i : Fin n) :
    (standardStabilizer n i).decode.word = fun k => if k = i then Pauli1.Z else Pauli1.I := by
  funext k
  by_cases h : k = i <;> simp [standardStabilizer, Row.decode, letter, h]

theorem sympX_stdDestabilizer (n : ℕ) (i : Fin n) :
    symplecticX (standardDestabilizer n i).decode.word =
      fun k => if k = i then (1 : ZMod 2) else 0 := by
  rw [stdDestab_word]; funext k
  by_cases h : k = i <;> simp [symplecticX, h]

theorem sympZ_stdDestabilizer (n : ℕ) (i : Fin n) :
    symplecticZ (standardDestabilizer n i).decode.word = fun _ => (0 : ZMod 2) := by
  rw [stdDestab_word]; funext k
  by_cases h : k = i <;> simp [symplecticZ, h]

theorem sympX_stdStabilizer (n : ℕ) (i : Fin n) :
    symplecticX (standardStabilizer n i).decode.word = fun _ => (0 : ZMod 2) := by
  rw [stdStab_word]; funext k
  by_cases h : k = i <;> simp [symplecticX, h]

theorem sympZ_stdStabilizer (n : ℕ) (i : Fin n) :
    symplecticZ (standardStabilizer n i).decode.word =
      fun k => if k = i then (1 : ZMod 2) else 0 := by
  rw [stdStab_word]; funext k
  by_cases h : k = i <;> simp [symplecticZ, h]

theorem booleanDot_zero_right (n : ℕ) (a : BooleanVec n) :
    booleanDot a (fun _ => (0 : ZMod 2)) = 0 := by
  simp [booleanDot]

theorem booleanDot_zero_left (n : ℕ) (a : BooleanVec n) :
    booleanDot (fun _ => (0 : ZMod 2)) a = 0 := by
  simp [booleanDot]

theorem booleanDot_delta (n : ℕ) (i j : Fin n) :
    booleanDot (fun k => if k = i then (1 : ZMod 2) else 0)
      (fun k => if k = j then (1 : ZMod 2) else 0) = if i = j then 1 else 0 := by
  rw [booleanDot]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro hn; exact absurd (Finset.mem_univ i) hn
  · have hz : ∀ x : Fin n,
        (if x = i then (1 : ZMod 2) else 0) * (if x = j then (1 : ZMod 2) else 0) = 0 := by
      intro x
      by_cases hx : x = i
      · subst hx; simp [h]
      · simp [hx]
    rw [Finset.sum_eq_zero (fun x _ => hz x), if_neg h]

theorem standardCommute_DD (n : ℕ) :
    ∀ i j : Fin n,
      pauliCommute ((standardDestabilizer n) i).decode ((standardDestabilizer n) j).decode := by
  intro i j
  simp only [pauliCommute, sympX_stdDestabilizer, sympZ_stdDestabilizer, symplecticForm]
  rw [booleanDot_zero_right, booleanDot_zero_left]
  simp

theorem standardAnticommute_DS (n : ℕ) :
    ∀ h : Fin n,
      ¬ pauliCommute ((standardDestabilizer n) h).decode ((standardStabilizer n) h).decode := by
  intro h
  simp only [pauliCommute, sympX_stdDestabilizer, sympZ_stdDestabilizer, sympX_stdStabilizer,
    sympZ_stdStabilizer, symplecticForm]
  rw [booleanDot_delta n h h, booleanDot_zero_right]
  simp

theorem standardCommute_DS' (n : ℕ) :
    ∀ i h : Fin n, i ≠ h →
      pauliCommute ((standardDestabilizer n) i).decode ((standardStabilizer n) h).decode := by
  intro i h hih
  simp only [pauliCommute, sympX_stdDestabilizer, sympZ_stdDestabilizer, sympX_stdStabilizer,
    sympZ_stdStabilizer, symplecticForm]
  rw [booleanDot_delta n i h, if_neg hih, booleanDot_zero_right]
  simp

theorem commutation_preserved_run {n : ℕ} (D S : Tableau n n) (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g)
    (hDD : ∀ i j, pauliCommute (D i).decode (D j).decode)
    (hDS : ∀ h, ¬ pauliCommute (D h).decode (S h).decode)
    (hDS' : ∀ i h, i ≠ h → pauliCommute (D i).decode (S h).decode) :
    (∀ i j, pauliCommute ((run gs D) i).decode ((run gs D) j).decode) ∧
      (∀ h, ¬ pauliCommute ((run gs D) h).decode ((run gs S) h).decode) ∧
      (∀ i h, i ≠ h → pauliCommute ((run gs D) i).decode ((run gs S) h).decode) := by
  induction gs generalizing D S with
  | nil => simpa [run] using! ⟨hDD, hDS, hDS'⟩
  | cons g gs ih =>
      have hg : legalGate g := hgs g List.mem_cons_self
      have hstep := tableauCommutation_preserved D S g hg hDD hDS hDS'
      exact ih (update g D) (update g S)
        (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
        hstep.1 hstep.2.1 hstep.2.2

theorem proposition3_commutation_invariants {n : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) :
    (∀ i j, pauliCommute ((run gs (standardDestabilizer n)) i).decode
        ((run gs (standardDestabilizer n)) j).decode) ∧
      (∀ h, ¬ pauliCommute ((run gs (standardDestabilizer n)) h).decode
        ((run gs (standardStabilizer n)) h).decode) ∧
      (∀ i h, i ≠ h → pauliCommute ((run gs (standardDestabilizer n)) i).decode
        ((run gs (standardStabilizer n)) h).decode) :=
  commutation_preserved_run (standardDestabilizer n) (standardStabilizer n) gs hgs
    (standardCommute_DD n) (standardAnticommute_DS n) (standardCommute_DS' n)

def proposition3_invariants_statement {n : ℕ} (gs : List (CliffordGate n)) : Prop :=
  TableauInvariant (run gs (standardDestabilizer n)) (run gs (standardStabilizer n))
    (Uword gs *ᵥ KetZero n)

def antipodal {n : ℕ} (i j : Fin (2 * n)) : Prop := (i.val + n) % (2 * n) = j.val

def MixedTableauCommutation {n : ℕ} (T : Tableau n (2 * n)) : Prop :=
  ∀ i j : Fin (2 * n), i ≠ j →
    (antipodal i j ↔ ¬ pauliCommute (T i).decode (T j).decode)

theorem mixed_state_unitary_step {n : ℕ} (T : Tableau n (2 * n))
    (hT : MixedTableauCommutation T) (g : CliffordGate n) (hg : legalGate g) :
    MixedTableauCommutation (update g T) := by
  intro i j hij
  rw [show (update g T) i = (T i).update g from rfl,
    show (update g T) j = (T j).update g from rfl,
    decode_update g hg, decode_update g hg,
    pauliCommute_verifiedCliffordAction g hg _ _]
  exact hT i j hij

theorem mixed_state_tableau_algorithm {n : ℕ} (T : Tableau n (2 * n))
    (hT : MixedTableauCommutation T) (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) :
    MixedTableauCommutation (run gs T) := by
  induction gs generalizing T with
  | nil => simpa [run] using! hT
  | cons g gs ih =>
      have hg : legalGate g := hgs g List.mem_cons_self
      have hrun : run (g :: gs) T = run gs (update g T) := rfl
      rw [hrun]
      exact ih (update g T) (mixed_state_unitary_step T hT g hg)
        (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))

def CircuitEquiv {n : ℕ} (gs1 gs2 : List (CliffordGate n)) : Prop := Uword gs1 = Uword gs2

theorem lemma5_tableaus_eq_of_actionWord_eq {n : ℕ} (gs1 gs2 : List (CliffordGate n))
    (h1 : ∀ g ∈ gs1, legalGate g) (h2 : ∀ g ∈ gs2, legalGate g) (T : Tableau n n)
    (h : ∀ p : PauliElem n, actionWord gs1 p = actionWord gs2 p) : run gs1 T = run gs2 T := by
  funext a
  have hdec : (run gs1 T a).decode = (run gs2 T a).decode := by
    rw [run_decode gs1 h1, run_decode gs2 h2, h]
  have := congrArg encode hdec
  simpa [encode_decode] using! this

def lemma5_tableau_equivalence_statement : Prop :=
  ∀ (n : ℕ) (gs1 gs2 : List (CliffordGate n)),
    (∀ g ∈ gs1, legalGate g) → (∀ g ∈ gs2, legalGate g) →
      (CircuitEquiv gs1 gs2 ↔
        (run gs1 (standardDestabilizer n) = run gs2 (standardDestabilizer n) ∧
          run gs1 (standardStabilizer n) = run gs2 (standardStabilizer n)))

def xMatrix {n m : ℕ} (t : Tableau n m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => if (t i).x j then 1 else 0

def hadamardPoints {n : ℕ} (mask : Fin n → Bool) (r : Row n) : Row n :=
  ⟨fun j => if mask j then r.z j else r.x j,
    fun j => if mask j then r.x j else r.z j, r.phase⟩

def lemma6_hadamard_full_rank_statement : Prop :=
  ∀ (n : ℕ) (t : Tableau n n), ConsistentTableau t →
    ∃ mask : Fin n → Bool,
      ∀ v : Fin n → ZMod 2,
        (∀ i, ∑ j, v j * xMatrix (fun a => hadamardPoints mask (t a)) i j = 0) → v = 0

def lemma7_symmetric_decomposition_statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)), Aᵀ = A →
    ∃ (Λ M : Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ i j, i ≠ j → Λ i j = 0) ∧ IsUnit M ∧ A + Λ = M * Mᵀ

def corollary9_gate_count_statement : Prop :=
  ∀ (n : ℕ) (gs : List (CliffordGate n)), (∀ g ∈ gs, legalGate g) →
    ∃ gs' : List (CliffordGate n),
      CircuitEquiv gs gs' ∧ gs'.length * Nat.log 2 n ≤ 4 * (n + 1) ^ 2

def isHadamard {n : ℕ} : CliffordGate n → Prop
  | .H _ => True
  | _ => False

def isCNOT {n : ℕ} : CliffordGate n → Prop
  | .CNOT _ _ => True
  | _ => False

def isPhase {n : ℕ} : CliffordGate n → Prop
  | .S _ => True
  | _ => False

def CanonicalCircuit {n : ℕ} (gs : List (CliffordGate n)) : Prop :=
  ∃ h1 c1 p1 c2 p2 c3 h2 p3 c4 p4 c5 : List (CliffordGate n),
    gs = h1 ++ c1 ++ p1 ++ c2 ++ p2 ++ c3 ++ h2 ++ p3 ++ c4 ++ p4 ++ c5 ∧
      (∀ g ∈ h1, isHadamard g) ∧ (∀ g ∈ c1, isCNOT g) ∧ (∀ g ∈ p1, isPhase g) ∧
      (∀ g ∈ c2, isCNOT g) ∧ (∀ g ∈ p2, isPhase g) ∧ (∀ g ∈ c3, isCNOT g) ∧
      (∀ g ∈ h2, isHadamard g) ∧ (∀ g ∈ p3, isPhase g) ∧ (∀ g ∈ c4, isCNOT g) ∧
      (∀ g ∈ p4, isPhase g) ∧ (∀ g ∈ c5, isCNOT g)

def theorem8_canonical_form_statement : Prop :=
  ∀ (n : ℕ) (gs : List (CliffordGate n)), (∀ g ∈ gs, legalGate g) →
    ∃ gs' : List (CliffordGate n), CanonicalCircuit gs' ∧ CircuitEquiv gs gs'

def proposition2_stabilizer_count_statement : Prop :=
  ∀ n : ℕ,
    PureStabilizerStateCount n =
      2 ^ n * ∏ k ∈ Finset.range n, (2 ^ (n - k) + 1)

def generatorMismatch {n : ℕ} (Gs Hs : List (PauliElem n)) : ℕ :=
  ((Gs.zip Hs).filter (fun q => decide (encode q.1 ≠ encode q.2))).length

def OppositeSignInGroups {n : ℕ} (Gs Hs : List (PauliElem n)) : Prop :=
  ∃ p : PauliElem n, p ∈ generatedGroup Gs ∧ negPauliElem p ∈ generatedGroup Hs

def inner_product_characterization_statement : Prop :=
  ∀ (n : ℕ) (ψ φ : QState (Reg n)),
    Normalized ψ → Normalized φ →
    ∀ (Gs Hs : List (PauliElem n)), Gs.length = n → Hs.length = n →
    (∀ p : PauliElem n, op p *ᵥ ψ = ψ ↔ p ∈ generatedGroup Gs) →
    (∀ p : PauliElem n, op p *ᵥ φ = φ ↔ p ∈ generatedGroup Hs) →
    (∀ Gs' Hs' : List (PauliElem n), Gs'.length = n → Hs'.length = n →
      (∀ p : PauliElem n, op p *ᵥ ψ = ψ ↔ p ∈ generatedGroup Gs') →
      (∀ p : PauliElem n, op p *ᵥ φ = φ ↔ p ∈ generatedGroup Hs') →
        generatorMismatch Gs Hs ≤ generatorMismatch Gs' Hs') →
    (OppositeSignInGroups Gs Hs → innerProduct ψ φ = 0) ∧
      (¬ OppositeSignInGroups Gs Hs →
        innerProduct ψ φ = (Real.sqrt 2 : ℂ) ^ (-(generatorMismatch Gs Hs : ℤ)))

theorem faster_simulation_space_bound {n m recordCount : ℕ} (hm : m ≤ n) :
    liveSpace n m recordCount ≤ spacePolynomial n + recordCount :=
  liveSpace_le hm

theorem faster_simulation_gate_bound {n m : ℕ} (hm : m ≤ n) :
    gateClock n m ≤ stepPolynomial n :=
  (clocks_le_stepPolynomial hm).1

theorem faster_simulation_measurement_bound {n m : ℕ} (hm : m ≤ n) :
    randomClock n m ≤ stepPolynomial n :=
  (clocks_le_stepPolynomial hm).2.1

theorem faster_simulation_time_space_bound {n m recordCount : ℕ} (hm : m ≤ n) :
    liveSpace n m recordCount ≤ spacePolynomial n + recordCount ∧
      randomClock n m ≤ stepPolynomial n :=
  ⟨liveSpace_le hm, (clocks_le_stepPolynomial hm).2.1⟩

theorem theorem4_gottesman_knill_in_xorL {n : ℕ} (program : Program n n) (t : Tableau n n)
    (tape : List Bool) (ψ : QState (Reg n))
    (hv : Program.Valid t program) (ht : ConsistentTableau t) (hn : Normalized ψ)
    (hψ : ψ ∈ codeSpace t) (hbudget : program.maxFairBits ≤ tape.length) :
    ∃ result : PhysicalResult n n,
      physicalExecute program (initial t tape) ψ = some result ∧
        result.machine.elapsed ≤ program.maxSteps * stepPolynomial n ∧
        result.machine.peakSpace ≤ spacePolynomial n + program.maxMeasurements := by
  obtain ⟨r, hr, -, -, -, -, htime, hspace⟩ :=
    frontier1 program t tape ψ (le_refl n) hv ht hn hψ hbudget
  exact ⟨r, hr, htime, hspace⟩

def StabilizerSimOutcome {n : ℕ} (prog : Program n n) (tape target : List Bool) : Prop :=
  ∃ result : PhysicalResult n n,
    physicalExecute prog (initial (standardStabilizer n) tape) (KetZero n) = some result ∧
      result.machine.outcomes = target

def BinarySystemConsistent {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : Fin n → ZMod 2) : Prop :=
  ∃ x : Fin n → ZMod 2, A.mulVec x = b

theorem standardStabilizer_consistent (n : ℕ) : ConsistentTableau (standardStabilizer n) := by
  constructor
  · intro a
    left
    rfl
  · intro a b
    rw [op_commute_iff]
    simp only [pauliCommute, sympX_stdStabilizer, sympZ_stdStabilizer, symplecticForm]
    rw [booleanDot_zero_right, booleanDot_zero_left]
    simp

theorem letter_false (b : Bool) : letter false b = if b then Pauli1.Z else Pauli1.I := by
  cases b <;> rfl

theorem ketZero_mem_codeSpace (n : ℕ) : KetZero n ∈ codeSpace (standardStabilizer n) := by
  rw [mem_codeSpace_iff]
  intro a
  have h := op_ZI_stabilizes_ket_zero (n := n)
    (fun k => letter false (decide (k = a)))
    (by
      intro k
      change letter false (decide (k = a)) = Pauli1.Z ∨
        letter false (decide (k = a)) = Pauli1.I
      rw [letter_false]
      by_cases hk : decide (k = a) <;> simp [hk])
  simpa [standardStabilizer, Row.decode, KetZero] using! h

theorem kn_simulation_polynomial_space {n : ℕ} (program : Program n n) (tape : List Bool)
    (hv : Program.Valid (standardStabilizer n) program)
    (hbudget : program.maxFairBits ≤ tape.length) :
    ∃ result : PhysicalResult n n,
      physicalExecute program (initial (standardStabilizer n) tape) (KetZero n) = some result ∧
        result.machine.peakSpace ≤ spacePolynomial n + program.maxMeasurements := by
  obtain ⟨r, hr, -, hspace⟩ :=
    theorem4_gottesman_knill_in_xorL program (standardStabilizer n) tape (KetZero n)
      hv (standardStabilizer_consistent n) (normalized_ket (ZeroStr n))
      (ketZero_mem_codeSpace n) hbudget
  exact ⟨r, hr, hspace⟩

def corollary_gottesman_knill_xorL_complete_statement {n : ℕ} : Prop :=
  (∀ (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2),
    ∃ (prog : Program n n) (tape : List Bool) (out : Bool),
      (StabilizerSimOutcome prog tape [out] ↔ BinarySystemConsistent A b)) ∧
    (∀ (prog : Program n n) (tape target : List Bool),
      prog.maxFairBits ≤ tape.length → StabilizerSimOutcome prog tape target →
        ∃ result : PhysicalResult n n,
          physicalExecute prog (initial (standardStabilizer n) tape) (KetZero n) = some result ∧
            result.machine.peakSpace ≤ spacePolynomial n + prog.maxMeasurements)

def sectionVIIBProbCost (m b d : ℕ) : ℕ := m * (2 ^ (d - 1) * 2 ^ (2 * b))

theorem tensor_product_initial_time (m b d : ℕ) :
    sectionVIIBProbCost m b d ≤ m * 2 ^ (2 * b + 2 * d) := by
  unfold sectionVIIBProbCost
  have h : 2 ^ (d - 1) ≤ 2 ^ (2 * d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc m * (2 ^ (d - 1) * 2 ^ (2 * b))
      = m * 2 ^ (2 * b) * 2 ^ (d - 1) := by ring
    _ ≤ m * 2 ^ (2 * b) * 2 ^ (2 * d) :=
        Nat.mul_le_mul_left _ h
    _ = m * 2 ^ (2 * b + 2 * d) := by
        rw [mul_assoc, ← Nat.pow_add]

def sectionVIICCost (b d n : ℕ) : ℕ :=
  4 ^ (2 * b * d) * n + 4 ^ (b * d) * (2 * n ^ 2)

theorem non_stabilizer_gate_simulation (b d n : ℕ) :
    sectionVIICCost b d n ≤ 2 * (4 ^ (2 * b * d) * (n + n ^ 2)) := by
  unfold sectionVIICCost
  have hexp : b * d ≤ 2 * b * d := by nlinarith [Nat.zero_le b, Nat.zero_le d]
  have hle : 4 ^ (b * d) ≤ 4 ^ (2 * b * d) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  calc 4 ^ (2 * b * d) * n + 4 ^ (b * d) * (2 * n ^ 2)
      ≤ 4 ^ (2 * b * d) * n + 4 ^ (2 * b * d) * (2 * n ^ 2) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) _
    _ = 4 ^ (2 * b * d) * (n + 2 * n ^ 2) := by ring
    _ ≤ 2 * (4 ^ (2 * b * d) * (n + n ^ 2)) := by
        have h : n + 2 * n ^ 2 ≤ 2 * (n + n ^ 2) := by nlinarith [Nat.zero_le n]
        have hm := Nat.mul_le_mul_left (4 ^ (2 * b * d)) h
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using! hm

end Qatlib.Papers.StabilizerSim04.MainResults
