/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport

open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false

noncomputable def loadedDiagonal {N : ℕ} (p : Fin N → ℝ) : Qatlib.Foundations.PureStateMath.Operator N :=
  Matrix.diagonal fun i => (p i : ℂ)

noncomputable def classicalTV {N : ℕ} (p q : Fin N → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

noncomputable def repeatedChannel {N : ℕ} (T : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N) :
    ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N
  | 0 => Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel.id N
  | m + 1 => T.comp (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m)

@[simp] theorem repeatedChannel_zero {N : ℕ} (T : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (A : Qatlib.Foundations.PureStateMath.Operator N) : (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T 0).map A = A := rfl

@[simp] theorem repeatedChannel_succ {N : ℕ} (T : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (m : ℕ) (A : Qatlib.Foundations.PureStateMath.Operator N) :
    (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T (m + 1)).map A = T.map ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map A) := rfl

noncomputable def implementedRun {N : ℕ} (S : ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N) :
    ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N
  | 0 => Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel.id N
  | m + 1 => (S m).comp (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m)

@[simp] theorem implementedRun_zero {N : ℕ} (S : ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (A : Qatlib.Foundations.PureStateMath.Operator N) : (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S 0).map A = A := rfl

@[simp] theorem implementedRun_succ {N : ℕ} (S : ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (m : ℕ) (A : Qatlib.Foundations.PureStateMath.Operator N) :
    (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S (m + 1)).map A = (S m).map ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m).map A) := rfl

theorem loadedDiagonal_density {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    Qatlib.Foundations.PureStateMath.IsDensityOperator (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p) := by
  constructor
  · rw [Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal, Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast hp i
  · simp only [Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal, Matrix.trace_diagonal, ← Complex.ofReal_sum, hsum,
      Complex.ofReal_one]

theorem loadedDiagonal_halfTrace {N : ℕ} (p q : Fin N → ℝ) :
    Matrix.traceNorm (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p - Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal q) / 2 = Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.classicalTV p q := by
  have he : Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p - Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal q =
      Matrix.diagonal (fun i => ((p i - q i : ℝ) : ℂ)) := by
    simp only [Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal,
        Matrix.diagonal_sub, Complex.ofReal_sub]
  rw [he, Qatlib.Concepts.GibbsMetropolis.RationalBath.real_diagonal_traceNorm]
  rfl

private theorem halfTrace_triangle {N : ℕ} (A B C : Qatlib.Foundations.PureStateMath.Operator N) :
    Matrix.traceNorm (A - C) / 2 ≤
      Matrix.traceNorm (A - B) / 2 + Matrix.traceNorm (B - C) / 2 := by
  have h := Matrix.traceNorm_add_le (A - B) (B - C)
  rw [sub_add_sub_cancel] at h
  linarith

theorem paid_warm_transfer {N : ℕ} (T : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (p π : Fin N → ℝ) (m : ℕ) (Q : Qatlib.Foundations.PureStateMath.Operator N) (β : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (hπ : ∀ i, 0 ≤ π i) (hπSum : ∑ i, π i = 1)
    (hreference : Matrix.traceNorm ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal π) - Q) / 2 ≤ β) :
    Matrix.traceNorm ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p) - Q) / 2 ≤
      Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.classicalTV p π + β := by
  have hherm := (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal_density p hp hpSum).1.isHermitian.sub
    (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal_density π hπ hπSum).1.isHermitian
  have hc :=
      Qatlib.Concepts.ReferenceError.DensityToRaw.channel_hermitian_trace_contraction
      (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m) hherm
  rw [map_sub] at hc
  have ht := halfTrace_triangle ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p))
    ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal π)) Q
  have hload :=
      Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal_halfTrace p π
  linarith

theorem implementedRun_halfTrace_error {N : ℕ} (T : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (S : ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N) (η : ℝ) (m : ℕ)
    (hstep : ∀ j < m, ∀ ρ : Qatlib.Foundations.PureStateMath.Operator N, Qatlib.Foundations.PureStateMath.IsDensityOperator ρ →
      Matrix.traceNorm ((S j).map ρ - T.map ρ) / 2 ≤ η)
    (ρ : Qatlib.Foundations.PureStateMath.Operator N) (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ) :
    Matrix.traceNorm ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m).map ρ - (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map ρ) / 2 ≤
      (m : ℝ) * η := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hi := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self m)))
    let A :=
        (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m).map ρ
    let B :=
        (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map ρ
    have hA : Qatlib.Foundations.PureStateMath.IsDensityOperator A :=
        (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m).preservesDensity hρ
    have hB : Qatlib.Foundations.PureStateMath.IsDensityOperator B :=
        (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).preservesDensity hρ
    have hs := hstep m (Nat.lt_succ_self m) A hA
    have hc :=
        Qatlib.Concepts.ReferenceError.DensityToRaw.channel_hermitian_trace_contraction T
        (hA.1.isHermitian.sub hB.1.isHermitian)
    rw [map_sub] at hc
    have ht := halfTrace_triangle ((S m).map A) (T.map A) (T.map B)
    change Matrix.traceNorm ((S m).map A - T.map B) / 2 ≤ ((m + 1 : ℕ) : ℝ) * η
    change Matrix.traceNorm (A - B) / 2 ≤ (m : ℝ) * η at hi
    push_cast
    nlinarith

theorem paid_warm_implemented {N : ℕ} (T : Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N)
    (S : ℕ → Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel N N) (p π : Fin N → ℝ)
    (m : ℕ) (Q ρ : Qatlib.Foundations.PureStateMath.Operator N) (β η ηload : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (hπ : ∀ i, 0 ≤ π i) (hπSum : ∑ i, π i = 1)
    (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ)
    (hload : Matrix.traceNorm (ρ - Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p) / 2 ≤ ηload)
    (hstep : ∀ j < m, ∀ X : Qatlib.Foundations.PureStateMath.Operator N, Qatlib.Foundations.PureStateMath.IsDensityOperator X →
      Matrix.traceNorm ((S j).map X - T.map X) / 2 ≤ η)
    (hreference : Matrix.traceNorm ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal π) - Q) / 2 ≤ β) :
    Matrix.traceNorm ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m).map ρ - Q) / 2 ≤
      Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.classicalTV p π + β + ηload + (m : ℝ) * η := by
  have hpD :=
      Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal_density p hp hpSum
  have hw :=
      Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.paid_warm_transfer T p π m Q β hp hpSum hπ hπSum hreference
  have he :=
      Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun_halfTrace_error T S η m hstep ρ hρ
  have hc := Qatlib.Concepts.ReferenceError.DensityToRaw.channel_hermitian_trace_contraction (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m)
    (hρ.1.isHermitian.sub hpD.1.isHermitian)
  rw [map_sub] at hc
  have ht₁ := halfTrace_triangle ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.implementedRun S m).map ρ)
    ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map ρ) Q
  have ht₂ := halfTrace_triangle ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map ρ)
    ((Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.repeatedChannel T m).map (Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport.loadedDiagonal p)) Q
  linarith

end Qatlib.Concepts.MixedInstrument.Contraction.WarmStartErrorTransport
