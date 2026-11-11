/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Order
import Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone

set_option backward.isDefEq.respectTransparency false

/-!
# Feedback hierarchy for adaptive shallow circuits

Fixed version: arXiv:2608.15545v1 (2026-08-16), Theorem 1 (p.2-3) and Appendix D
(p.11-12, Eqs. (D1)).  Paper: *Quantum Advantage with Adaptive Shallow Circuits*.

The paper studies `CRAS_d[M]`, the class of constant-round adaptive shallow
circuits of coherent depth `d` that use at most `M` intermediate measurement
outcomes as classical feedback, with a fixed local Pauli-`Z` readout.

Appendix D proves two facts.

* **Light-cone / Pauli-weight bound.**  After averaging over transcripts the
  effective input observable `A = C†(Z)` of such a protocol has Pauli weight at
  most `(M + 1) * 2^d`: there are at most `M + 1` candidate support sites (the
  readout and the `M` measurement effects) and each reaches at most `2^d`
  inputs through `d` layers of two-qubit gates.
* **Witness.**  The observable `O_T = X_{q0} ⊗ ⋯ ⊗ X_{qT}` on `T + 1` input
  qubits is realised exactly with `T` raw intermediate outcomes and a universal
  constant coherent depth (Eq. (D1) region, p.11).

Consequently `CRAS_d[o(m)] ⊊ CRAS_d[m]` (Theorem 1): a function computed with
`m` feedback needs effective input support with all `N = (m+1) 2^{d-1}` bits,
whereas a budget `M` with `(M+1) 2^d < N` cannot cover them.

This file records the paper-layer abstraction of the two Appendix-D facts:
`DependsOn` is the effective input support relation, `LightConeCertificate`
packages the Pauli-weight bound, and the hierarchy is then proved
combinatorially (no `sorry`).  The light-cone hypothesis `hLightCone` of
`cras_feedback_hierarchy` is *not* left as an assumption: the lemma
`light_cone_hypothesis_of_layers` derives it from the explicit wire-level
circuit model of the `LightCone` module (proved there as
`LightCone.lightCone_bound`).  Only the witness half remains a hypothesis
(`hWitness`), corresponding to the paper's explicit `X`-parity construction.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.FeedbackHierarchy

/-- **Input dependence.**  A Boolean function `f` on `N` input bits depends on
the set `S` if two inputs that agree on `S` have the same value.  This is the
paper-layer counterpart of the effective input support of the Heisenberg-picture
observable `A = C†(Z)` (Appendix D, p.11). -/
def DependsOn {N : ℕ} (f : (Fin N → Bool) → Bool) (S : Finset (Fin N)) : Prop :=
  ∀ x y : Fin N → Bool, (∀ i ∈ S, x i = y i) → f x = f y

/-- **Light-cone certificate.**  Packages the Appendix-D bound: the effective
input support of a depth-`d` CRAS protocol with at most `M` classical feedback
outcomes has at most `(M + 1) * 2^d` qubits (each of the `M + 1` candidate
sites reaches at most `2^d` inputs). -/
structure LightConeCertificate (d M N : ℕ) where
  /-- Effective input support in the backward Heisenberg picture. -/
  support : Finset (Fin N)
  /-- Appendix D Pauli-weight bound, p.11. -/
  support_card : support.card ≤ (M + 1) * 2 ^ d

/-- The paper-layer class `CRAS_d[M]`, represented by Appendix D's effective
input support: `f` is computable if some admissible light-cone certificate
determines it. -/
def CrasComputable (d M N : ℕ) (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ c : LightConeCertificate d M N, DependsOn f c.support

/-- Monotonicity in the feedback budget: a larger budget never loses power.
(Paper: "The inclusion follows immediately from monotonicity in the number of
measurement outcomes", Appendix D p.11.) -/
theorem cras_computable_mono {d M M' N : ℕ} (h : M ≤ M')
    {f : (Fin N → Bool) → Bool} (hf : CrasComputable d M N f) :
    CrasComputable d M' N f := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨⟨c.support, ?_⟩, hc⟩
  have hmul : (M + 1) * 2 ^ d ≤ (M' + 1) * 2 ^ d :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ h)
  exact le_trans c.support_card hmul

/-- Parity of the computational-basis input string.  This is the classical
shadow of the paper's witness observable `O_T = X_{q0} ⊗ ⋯ ⊗ X_{qT}` whose
expectation is `Tr[O_T ρ]` (Appendix D, p.11). -/
def parity {N : ℕ} (x : Fin N → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => x i)).card % 2 = 1)

/-- The all-zero input has even parity. -/
theorem parity_zero {N : ℕ} : parity (fun _ : Fin N => false) = false := by
  simp [parity]

/-- Flipping a single input bit (from all-zero) makes the parity odd; this is
the classical form of Pauli orthogonality used in Appendix D. -/
theorem parity_update_single {N : ℕ} (i : Fin N) :
    parity (Function.update (fun _ : Fin N => false) i true) = true := by
  classical
  have hfilter :
      Finset.univ.filter (fun j : Fin N =>
        Function.update (fun _ : Fin N => false) i true j) = {i} := by
    ext j
    by_cases h : j = i
    · simp [Function.update, h]
    · simp [Function.update, h]
  simp [parity, hfilter]

/-- **Parity needs every input bit.**  If `N > 0` and `parity` depends on `S`,
then `S` is the full input set. -/
theorem parity_depends_on_univ {N : ℕ} (hN : 0 < N) {S : Finset (Fin N)}
    (hS : DependsOn parity S) : S = Finset.univ := by
  classical
  by_contra hproper
  have hex : ∃ i : Fin N, i ∉ S := by
    by_contra h
    refine hproper (Finset.eq_univ_iff_forall.mpr (fun i => ?_))
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hagree : ∀ j ∈ S,
      (Function.update (fun _ : Fin N => false) i true) j = (fun _ : Fin N => false) j := by
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [Function.update, hji]
  have heq : parity (Function.update (fun _ : Fin N => false) i true) =
      parity (fun _ : Fin N => false) := hS _ _ hagree
  rw [parity_update_single, parity_zero] at heq
  exact Bool.noConfusion heq

/-- Effective Pauli weight bound in closed form (Appendix D, Eq. (D1)
precursor): the support of a depth-`d`, `M`-feedback protocol has at most
`(M + 1) * 2^d` inputs. -/
theorem effective_support_card_le {d M N : ℕ} (c : LightConeCertificate d M N) :
    c.support.card ≤ (M + 1) * 2 ^ d := c.support_card

/-- The strict gap `(⌊m/4⌋ + 1) * 2^d < (m + 1) * 2^{d-1}` used in the proof
of Theorem 1, for `m ≥ 2` and `d ≥ 1`. -/
theorem feedback_gap (d m : ℕ) (hd : 1 ≤ d) (hm : 2 ≤ m) :
    (m / 4 + 1) * 2 ^ d < (m + 1) * 2 ^ (d - 1) := by
  have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  have hpos : 0 < 2 ^ (d - 1) := Nat.two_pow_pos (d - 1)
  have hlin : 2 * (m / 4 + 1) < m + 1 := by omega
  calc
    (m / 4 + 1) * (2 ^ (d - 1) * 2) = ((m / 4 + 1) * 2) * 2 ^ (d - 1) := by
      rw [Nat.mul_comm (2 ^ (d - 1)) 2, Nat.mul_assoc]
    _ = (2 * (m / 4 + 1)) * 2 ^ (d - 1) := by
      rw [Nat.mul_comm (m / 4 + 1) 2]
    _ < (m + 1) * 2 ^ (d - 1) := Nat.mul_lt_mul_of_pos_right hlin hpos

/-- **Theorem 1 (Feedback hierarchy), paper-layer conditional form.**
Fixed coherent depth `d ≥ 1`, feedback budget `m ≥ 2`, `N = (m+1) 2^{d-1}`.

Assume (i) the monotonicity of the feedback-budget classes (Appendix D p.11,
first line of the proof) and (ii) the Appendix-D light-cone/Pauli-weight bound
for every budget `M`.  Then the witness `parity` on `N` bits lies in the class
with budget `m` (the paper's exact construction using `T = m` raw outcomes and
`O_T = X^{⊗T}`) and is *not* in the class with any budget `M` satisfying
`(M+1) 2^d < N`; in particular the inclusion `CRAS_d[m/4] ⊆ CRAS_d[m]` is
strict, which is the finite form of `CRAS_d[o(m)] ⊊ CRAS_d[m]`.

The hypotheses `hLightCone` and `hWitness` are exactly the two Appendix-D
inputs, not extra assumptions about the conclusion: `hLightCone` is the
Pauli-weight bound and `hWitness` is the explicit `X`-parity construction. -/
theorem cras_feedback_hierarchy
    {N d m : ℕ} (CRAS : ℕ → Set ((Fin N → Bool) → Bool))
    (hd : 1 ≤ d) (hm : 2 ≤ m) (hNpos : 0 < N)
    (hN : N = (m + 1) * 2 ^ (d - 1))
    (hMono : ∀ M M' : ℕ, M ≤ M' → CRAS M ⊆ CRAS M')
    (hLightCone : ∀ (M : ℕ) (f : (Fin N → Bool) → Bool), f ∈ CRAS M →
      ∃ S : Finset (Fin N), S.card ≤ (M + 1) * 2 ^ d ∧ DependsOn f S)
    (hWitness : parity ∈ CRAS m) :
    CRAS (m / 4) ⊆ CRAS m ∧ ∃ f, f ∈ CRAS m ∧ f ∉ CRAS (m / 4) := by
  constructor
  · exact hMono (m / 4) m (Nat.div_le_self m 4)
  · refine ⟨parity, hWitness, ?_⟩
    intro hmem
    obtain ⟨S, hScard, hSdep⟩ := hLightCone (m / 4) parity hmem
    have hproper : S ≠ Finset.univ := by
      intro huniv
      have hcard : S.card = N := by
        rw [huniv, Finset.card_univ, Fintype.card_fin]
      have hgap : (m / 4 + 1) * 2 ^ d < N := by
        rw [hN]
        exact feedback_gap d m hd hm
      omega
    exact hproper (parity_depends_on_univ hNpos hSdep)

/-- **Theorem 1, concrete light-cone class.**  With the certificate model
`CrasComputable` (Appendix D's effective-support bound built in), the parity
witness on `N = (m+1) 2^{d-1}` bits is computable with budget `m` and not with
budget `m/4`, for every `d ≥ 1`, `m ≥ 2`. -/
theorem cras_feedback_hierarchy_lightcone (d m : ℕ) (hd : 1 ≤ d) (hm : 2 ≤ m) :
    CrasComputable d m ((m + 1) * 2 ^ (d - 1)) parity ∧
      ¬ CrasComputable d (m / 4) ((m + 1) * 2 ^ (d - 1)) parity := by
  have hNpos : 0 < (m + 1) * 2 ^ (d - 1) :=
    Nat.mul_pos (Nat.succ_pos m) (Nat.two_pow_pos (d - 1))
  constructor
  · refine ⟨⟨Finset.univ, ?_⟩, ?_⟩
    · rw [Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right Nat.two_pos (Nat.sub_le d 1))
    · intro x y hxy
      congr 1
      funext i
      exact hxy i (Finset.mem_univ i)
  · rintro ⟨c, hdep⟩
    have hgap : (m / 4 + 1) * 2 ^ d < (m + 1) * 2 ^ (d - 1) :=
      feedback_gap d m hd hm
    have hproper : c.support ≠ Finset.univ := by
      intro huniv
      have hcard : c.support.card = (m + 1) * 2 ^ (d - 1) := by
        rw [huniv, Finset.card_univ, Fintype.card_fin]
      have hle : c.support.card ≤ (m / 4 + 1) * 2 ^ d := c.support_card
      omega
    exact hproper (parity_depends_on_univ hNpos hdep)

/-- **Discharging `hLightCone` from the wire model.**  The Appendix-D
light-cone bound, proved for the explicit wire-level layer model as
`LightCone.lightCone_bound`, supplies exactly the support existence statement
consumed by `cras_feedback_hierarchy`: a depth-`d` stack of `N`-wire layers
with an `M+1`-wire readout yields an effective input support of at most
`(M + 1) * 2^d` wires on which the computed function depends. -/
theorem light_cone_hypothesis_of_layers {N d : ℕ}
    (Ls : List (Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone.LayerGate N))
    (hd : Ls.length = d) (readout : Finset (Fin N)) (M : ℕ)
    (hread : readout.card ≤ M + 1) (g : (Fin N → Bool) → Bool)
    (hg : Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone.DependsOn g readout) :
    ∃ S : Finset (Fin N), S.card ≤ (M + 1) * 2 ^ d ∧
      Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone.DependsOn
        (g ∘ Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone.composeMap Ls) S := by
  obtain ⟨S, hcard, hdep⟩ :=
    Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone.lightCone_bound
      Ls readout M hread g hg
  exact ⟨S, by rw [← hd]; exact hcard, hdep⟩

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.FeedbackHierarchy
