/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# A common correctness contract for concrete CSS decoders

The certificate checks syndrome agreement and a weight bound for the actual
program output. It does not assume successful logical recovery. The main theorem
derives that property below half the distance, then connects it to the existing
recovery channel. The decoder's assigned `RecoveryProgram.decodeTime` values play no role
in these statements.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Concepts.ErrorCorrection.LogicalOps
open scoped Matrix

variable {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

/-- Checkable syndrome and weight obligations on a concrete decoder's bounded-error inputs. -/
structure DecoderCert {c : CssData ι κX κZ} (prog : RecoveryProgram c) (t : ℕ) : Prop where
  /-- The returned correction has the same syndrome as the input error. -/
  syndrome : ∀ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ t →
    pauliSyndrome c (prog.corr (pauliSyndrome c e)) = pauliSyndrome c e
  /-- The returned correction is no heavier than that input error. -/
  weight : ∀ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ t →
    pauliWeight (prog.corr (pauliSyndrome c e)).1 (prog.corr (pauliSyndrome c e)).2 ≤
      pauliWeight e.1 e.2

/-- A binary vector added to itself vanishes pointwise. -/
private theorem binary_self {α : Type*} (v : α → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

omit [DecidableEq κX] [DecidableEq κZ] in
/-- Syndrome and weight certificates imply logical correction below half the distance. -/
theorem cert_corrects (c : CssData ι κX κZ) (prog : RecoveryProgram c) (t : ℕ)
    (cert : DecoderCert prog t) (hd : ((2 * t + 1 : ℕ) : ℕ∞) ≤ cssDistance c) :
    CorrectsUpTo prog t := by
  intro e he
  have hs := cert.syndrome e he
  have hm := cert.weight e he
  have hz : c.hX *ᵥ (prog.corr (pauliSyndrome c e)).2 = c.hX *ᵥ e.2 :=
    congrArg Prod.fst hs
  have hx : c.hZ *ᵥ (prog.corr (pauliSyndrome c e)).1 = c.hZ *ᵥ e.1 :=
    congrArg Prod.snd hs
  have hs0 : pauliSyndrome c (residualLabel prog e) = (0, 0) := by
    change (c.hX *ᵥ (e.2 + (prog.corr (pauliSyndrome c e)).2),
      c.hZ *ᵥ (e.1 + (prog.corr (pauliSyndrome c e)).1)) = (0, 0)
    rw [Matrix.mulVec_add, Matrix.mulVec_add, hz, hx]
    exact Prod.ext (binary_self _) (binary_self _)
  have hw : pauliWeight (residualLabel prog e).1 (residualLabel prog e).2 ≤ 2 * t := by
    change pauliWeight (e.1 + (prog.corr (pauliSyndrome c e)).1)
      (e.2 + (prog.corr (pauliSyndrome c e)).2) ≤ 2 * t
    have ha := pauliWeight_add_le e.1 (prog.corr (pauliSyndrome c e)).1
      e.2 (prog.corr (pauliSyndrome c e)).2
    omega
  apply (distance_ge_iff c ((2 * t + 1 : ℕ) : ℕ∞)).mp hd _ hs0
  exact_mod_cast Nat.lt_succ_of_le hw

omit [Fintype κX] [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] in
/-- Global minimum-weight soundness supplies the weight part of a bounded certificate. -/
theorem cert_of_min (c : CssData ι κX κZ) (prog : RecoveryProgram c) (t : ℕ)
    (hs : ∀ e : PauliLabel ι,
      pauliSyndrome c (prog.corr (pauliSyndrome c e)) = pauliSyndrome c e)
    (hm : MinimumWeightSound prog) : DecoderCert prog t := by
  refine ⟨fun e _ => hs e, ?_⟩
  intro e _
  exact hm (pauliSyndrome c e) e rfl

/-- A certified bounded correction restores every code-state density after a bounded Pauli error. -/
theorem cert_density (c : CssData ι κX κZ) (prog : RecoveryProgram c) (t : ℕ)
    (cert : DecoderCert prog t) (hd : ((2 * t + 1 : ℕ) : ℕ∞) ≤ cssDistance c)
    (e : PauliLabel ι) (he : pauliWeight e.1 e.2 ≤ t)
    (ψ : (ι → ZMod 2) → ℂ) (hψ : ψ ∈ cssCodespace c) :
    recoveryChannel c prog (densityOf ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ)) =
      densityOf ψ :=
  recoveryChannel_corrects_density c prog e (cert_corrects c prog t cert hd e he) ψ hψ

end Qatlib.Concepts.ErrorCorrection.Recovery
