/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprCompiler

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Machine Execution

Coded Floor constructions for Effective Gauge.
Proves `floorUniformCodeRealizes_computable`, `computable_floorExprRawApprox`, `floorExprRawApprox_encoded`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- A computable producer of finite codes plus exact total realizations gives a
computable joint evaluator. The universal machine decodes the actual output. -/
theorem floorUniformCodeRealizes_computable {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    (generate : A → Nat.Partrec.Code) (hgenerate : Computable generate)
    (f : A → B → C) (hf : ∀ a, floorCodeRealizes (generate a) (f a)) : Computable₂ f := by
  apply Partrec.of_eq_tot
    ((Nat.Partrec.Code.eval_part.comp (hgenerate.comp Computable.fst)
      (Primrec.encode.to_comp.comp Computable.snd)).bind
        (Computable.decode.comp Computable.snd).ofOption.to₂)
  intro q
  simp [hf q.1 q.2,Encodable.encodek]

/-- The raw coded approximation is computable jointly in the expression code and the encoded
query. -/
theorem computable_floorExprRawApprox : Computable₂ floorExprRawApprox := by
  obtain ⟨basis,hbasis⟩ := floorExprMachineBasis_exists
  exact floorUniformCodeRealizes_computable (floorExprCompile basis) (computable_floorExprCompile basis)
    floorExprRawApprox (floorExprCompile_correct basis hbasis)

/-- One partial-recursive code takes an encoded expression–query pair and returns the encoded
rational approximation for that pair. -/
theorem floorExprRawApprox_encoded : ∃ c : Nat.Partrec.Code, ∀ n q,
    Nat.Partrec.Code.eval c (Encodable.encode (n,q))=
      Part.some (Encodable.encode (floorExprRawApprox n q)) := by
  obtain ⟨machine,hmachine⟩ := floorComputableFixedCode
    (fun p : ℕ × FloorExprQueryCode => floorExprRawApprox p.1 p.2) computable_floorExprRawApprox
  exact ⟨machine,fun n q => hmachine (n,q)⟩

/-- A computable generator specializes the approximation program to an expression code. The
generated program then returns the encoded approximation for every encoded query. -/
theorem floorExprUniformCompiler : ∃ generate : ℕ → Nat.Partrec.Code,
    Computable generate ∧ ∀ n q,
      Nat.Partrec.Code.eval (generate n) (Encodable.encode q)=
        Part.some (Encodable.encode (floorExprRawApprox n q)) := by
  obtain ⟨basis,hbasis⟩ := floorExprMachineBasis_exists
  exact ⟨floorExprCompile basis,computable_floorExprCompile basis,floorExprCompile_correct basis hbasis⟩

/-- At a coded point in the fundamental cube and for a decoded tolerance in `(0, 1]`, the decoded
rational output has absolute error at most that tolerance against the decoded jet expression at
the program amplitude. -/
theorem floorExprRawApprox_error (n : ℕ) (q : FloorExprQueryCode)
    (hX : InFundamentalCube (rationalSpatialPoint (floorPointCodeValue q.2.1)))
    (ht : 0<floorRationalCodeValue q.2.2) (ht1 : floorRationalCodeValue q.2.2 ≤ 1) :
    |(floorRationalCodeValue (floorExprRawApprox n q) : ℝ)-
      floorJetEval (floorProgramAmplitude q.1 : ℝ)
        (rationalSpatialPoint (floorPointCodeValue q.2.1)) (floorExprDecode n)| ≤
      (floorRationalCodeValue q.2.2 : ℝ) := by
  rw [floorExprRawApprox_value]
  exact floorJetApproximation_error _ _ _ hX _ ht ht1

/-- One fixed finite machine, every syntax code and legal query, and the error
of the same returned payload. No oracle premise is supplied by the caller. -/
theorem floorExprMachine_joint : ∃ machine : Nat.Partrec.Code, ∀ n q,
    InFundamentalCube (rationalSpatialPoint (floorPointCodeValue q.2.1)) →
    0<floorRationalCodeValue q.2.2 → floorRationalCodeValue q.2.2 ≤ 1 →
    Nat.Partrec.Code.eval machine (Encodable.encode (n,q))=
      Part.some (Encodable.encode (floorExprRawApprox n q)) ∧
    |(floorRationalCodeValue (floorExprRawApprox n q) : ℝ)-
      floorJetEval (floorProgramAmplitude q.1 : ℝ)
        (rationalSpatialPoint (floorPointCodeValue q.2.1)) (floorExprDecode n)| ≤
      (floorRationalCodeValue q.2.2 : ℝ) := by
  obtain ⟨machine,hmachine⟩ := floorExprRawApprox_encoded
  exact ⟨machine,fun n q hX ht ht1 => ⟨hmachine n q,floorExprRawApprox_error n q hX ht ht1⟩⟩

end Qatlib.Concepts.EffectiveGauge.CodedFloor
