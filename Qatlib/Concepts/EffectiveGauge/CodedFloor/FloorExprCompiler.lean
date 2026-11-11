/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprRawApprox

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Compiler

Coded Floor constructions for Effective Gauge.
Defines `floorExprCompileStep`, `floorExprCompileWith`, `floorExprCompile`.
Proves `computable_floorExprProductScale`, `computable_floorExprCompileStep`, `floorComputableCompileWith`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Static code construction: child programs are composed with the required
precision transformations, so no recursive source oracle is used at runtime. -/
def floorExprCompileStep (basis : FloorExprMachineBasis) (n : ℕ)
    (a b u : Nat.Partrec.Code) : Nat.Partrec.Code :=
  let tag := (n-1).unpair.1
  let p := (n-1).unpair.2
  let zeroProgram := Nat.Partrec.Code.const (Encodable.encode (floorRationalCodeNat 0))
  let half := Nat.Partrec.Code.curry basis.scale
    (Encodable.encode (floorRationalCodeInv (floorRationalCodeNat 2)))
  let product := Nat.Partrec.Code.curry basis.scale
    (Encodable.encode (floorExprProductScale p.unpair.1 p.unpair.2))
  [Nat.Partrec.Code.const (Encodable.encode (floorExprLiteralCode p)),
    Nat.Partrec.Code.curry basis.coordinate (Encodable.encode p),basis.parameter,
    Nat.Partrec.Code.curry basis.flat (Encodable.encode p),
    .comp basis.add (.pair (.comp a half) (.comp b half)),.comp basis.neg u,
    .comp basis.mul (.pair (.comp a product) (.comp b product)),
    .comp basis.sin (.pair (.comp u half) (.comp basis.tolerance half)),
    .comp basis.cos (.pair (.comp u half) (.comp basis.tolerance half))].getD tag zeroProgram

/-- General course-of-values construction, with all runtime behavior confined
to the finite programs returned by `step`. -/
def floorExprCompileWith (step : ℕ → Nat.Partrec.Code → Nat.Partrec.Code → Nat.Partrec.Code → Nat.Partrec.Code)
    (zeroProgram : Nat.Partrec.Code) (n : ℕ) : Nat.Partrec.Code :=
  if hn : n=0 then zeroProgram else
    let p := (n-1).unpair.2
    step n (floorExprCompileWith step zeroProgram p.unpair.1)
      (floorExprCompileWith step zeroProgram p.unpair.2) (floorExprCompileWith step zeroProgram p)
termination_by n
decreasing_by
  all_goals
    have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
    first
    | exact (Nat.unpair_left_le _).trans_lt hp
    | exact (Nat.unpair_right_le _).trans_lt hp
    | exact hp

/-- Definition of floor Expr Compile in the Coded Floor construction. -/
def floorExprCompile (basis : FloorExprMachineBasis) : ℕ → Nat.Partrec.Code :=
  floorExprCompileWith (floorExprCompileStep basis)
    (Nat.Partrec.Code.const (Encodable.encode (floorRationalCodeNat 0)))

/-- Original `computable_floorExprProductScale` guarantee for the `FloorExprCompiler` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprProductScale : Computable₂ floorExprProductScale := by
  have ha : Computable (fun q : ℕ × ℕ => floorRationalCodeNat (floorExprCodeBound q.1)) :=
    primrec_floorRationalCodeNat.to_comp.comp (computable_floorExprCodeBound.comp Computable.fst)
  have hb : Computable (fun q : ℕ × ℕ => floorRationalCodeNat (floorExprCodeBound q.2)) :=
    primrec_floorRationalCodeNat.to_comp.comp (computable_floorExprCodeBound.comp Computable.snd)
  exact primrec_floorRationalCodeInv.to_comp.comp (primrec_floorRationalCodeMul.to_comp.comp
    (Computable.const (floorRationalCodeNat 2))
    (primrec_floorRationalCodeAdd.to_comp.comp
      (primrec_floorRationalCodeAdd.to_comp.comp ha hb) (Computable.const (floorRationalCodeNat 1))))

/-- Original `computable_floorExprCompileStep` guarantee for the `FloorExprCompiler` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprCompileStep (basis : FloorExprMachineBasis) :
    Computable (fun q : ℕ × Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code =>
      floorExprCompileStep basis q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hn : Computable (fun q : ℕ × Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code => q.1) := Computable.fst
  have ha : Computable (fun q : ℕ × Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code => q.2.1) :=
    Computable.fst.comp Computable.snd
  have hb : Computable (fun q : ℕ × Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code => q.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hu : Computable (fun q : ℕ × Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code => q.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hparts := Computable.unpair.comp ((Primrec.nat_sub.to_comp).comp hn (Computable.const 1))
  have ht := Computable.fst.comp hparts
  have hp := Computable.snd.comp hparts
  have hprod := Nat.Partrec.Code.primrec₂_curry.to_comp.comp (Computable.const basis.scale)
    (Primrec.encode.to_comp.comp (computable_floorExprProductScale.comp
      (Computable.fst.comp (Computable.unpair.comp hp))
      (Computable.snd.comp (Computable.unpair.comp hp))))
  let half := Nat.Partrec.Code.curry basis.scale
    (Encodable.encode (floorRationalCodeInv (floorRationalCodeNat 2)))
  have hhalfA := Nat.Partrec.Code.primrec₂_comp.to_comp.comp ha (Computable.const half)
  have hhalfB := Nat.Partrec.Code.primrec₂_comp.to_comp.comp hb (Computable.const half)
  have hhalfU := Nat.Partrec.Code.primrec₂_comp.to_comp.comp hu (Computable.const half)
  have h0 := Nat.Partrec.Code.primrec_const.to_comp.comp
    (Primrec.encode.to_comp.comp (primrec_floorExprLiteralCode.to_comp.comp hp))
  have h1 := Nat.Partrec.Code.primrec₂_curry.to_comp.comp (Computable.const basis.coordinate)
    (Primrec.encode.to_comp.comp hp)
  have h3 := Nat.Partrec.Code.primrec₂_curry.to_comp.comp (Computable.const basis.flat)
    (Primrec.encode.to_comp.comp hp)
  have h4 := Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const basis.add)
    (Nat.Partrec.Code.primrec₂_pair.to_comp.comp hhalfA hhalfB)
  have h5 := Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const basis.neg) hu
  have h6 := Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const basis.mul)
    (Nat.Partrec.Code.primrec₂_pair.to_comp.comp
      (Nat.Partrec.Code.primrec₂_comp.to_comp.comp ha hprod)
      (Nat.Partrec.Code.primrec₂_comp.to_comp.comp hb hprod))
  have h7 := Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const basis.sin)
    (Nat.Partrec.Code.primrec₂_pair.to_comp.comp hhalfU
      (Computable.const (Nat.Partrec.Code.comp basis.tolerance half)))
  have h8 := Nat.Partrec.Code.primrec₂_comp.to_comp.comp (Computable.const basis.cos)
    (Nat.Partrec.Code.primrec₂_pair.to_comp.comp hhalfU
      (Computable.const (Nat.Partrec.Code.comp basis.tolerance half)))
  have hlist := Computable.list_cons.comp h0 (Computable.list_cons.comp h1
    (Computable.list_cons.comp (Computable.const basis.parameter) (Computable.list_cons.comp h3
      (Computable.list_cons.comp h4 (Computable.list_cons.comp h5 (Computable.list_cons.comp h6
        (Computable.list_cons.comp h7 (Computable.list_cons.comp h8 (Computable.const [])))))))))
  exact (Primrec.list_getD (Nat.Partrec.Code.const (Encodable.encode (floorRationalCodeNat 0)))).to_comp.comp hlist ht

/-- Original `floorComputableCompileWith` guarantee for the `FloorExprCompiler` construction; the complete source hypotheses are retained. -/
private theorem floorComputableCompileWith
    (step : ℕ → Nat.Partrec.Code → Nat.Partrec.Code → Nat.Partrec.Code → Nat.Partrec.Code)
    (hstep : Computable (fun q : ℕ × Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code =>
      step q.1 q.2.1 q.2.2.1 q.2.2.2)) (zeroProgram : Nat.Partrec.Code) :
    Computable (floorExprCompileWith step zeroProgram) := by
  have hn : Computable (fun q : Unit × List Nat.Partrec.Code => q.2.length) := Computable.list_length.comp Computable.snd
  have hp := (Computable.snd.comp Computable.unpair).comp
    (Primrec.nat_sub.to_comp.comp hn (Computable.const 1))
  have ha := (Primrec.list_getD zeroProgram).to_comp.comp Computable.snd ((Computable.fst.comp Computable.unpair).comp hp)
  have hb := (Primrec.list_getD zeroProgram).to_comp.comp Computable.snd ((Computable.snd.comp Computable.unpair).comp hp)
  have hu := (Primrec.list_getD zeroProgram).to_comp.comp Computable.snd hp
  have hs := hstep.comp (hn.pair (ha.pair (hb.pair hu)))
  have hg : Computable₂ (fun (_ : Unit) (history : List Nat.Partrec.Code) =>
      some (if history.length=0 then zeroProgram else
        step history.length (history.getD (history.length-1).unpair.2.unpair.1 zeroProgram)
          (history.getD (history.length-1).unpair.2.unpair.2 zeroProgram)
          (history.getD (history.length-1).unpair.2 zeroProgram))) := by
    have heq := (Primrec.beq.to_comp.comp hn (Computable.const 0))
    exact Computable.option_some.comp
      ((Computable.cond heq (Computable.const zeroProgram) hs).of_eq (fun q => by
        simp [Bool.cond_eq_ite]))
  have hf : Computable₂ (fun (_ : Unit) n => floorExprCompileWith step zeroProgram n) :=
    Computable.nat_strong_rec _ hg (by
      intro _ n
      simp only [List.length_map,List.length_range]
      by_cases hn : n=0
      · subst n
        rw [floorExprCompileWith,dif_pos rfl]
        simp
      · have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
        have ha := (Nat.unpair_left_le (n-1).unpair.2).trans_lt hp
        have hb := (Nat.unpair_right_le (n-1).unpair.2).trans_lt hp
        rw [if_neg hn,floorExprCompileWith,dif_neg hn]
        have hh (k : ℕ) (hk : k<n) :
            ((List.range n).map (floorExprCompileWith step zeroProgram)).getD k zeroProgram=
              floorExprCompileWith step zeroProgram k := by
          rw [List.getD_eq_getElem _ _ (by simpa using hk)]
          simp only [List.getElem_map,List.getElem_range]
        rw [hh _ ha,hh _ hb,hh _ hp])
  exact hf.comp (Computable.const ()) Computable.id

/-- Original `computable_floorExprCompile` guarantee for the `FloorExprCompiler` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprCompile (basis : FloorExprMachineBasis) : Computable (floorExprCompile basis) :=
  floorComputableCompileWith (floorExprCompileStep basis) (computable_floorExprCompileStep basis) _

/-- Original `floorExprCompile_correct` guarantee for the `FloorExprCompiler` construction; the complete source hypotheses are retained. -/
theorem floorExprCompile_correct (basis : FloorExprMachineBasis) (h : FloorExprMachineBasisCorrect basis)
    (n : ℕ) : floorCodeRealizes (floorExprCompile basis n) (floorExprRawApprox n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      intro q
      rw [floorExprCompile,floorExprCompileWith,dif_pos rfl]
      rw [Nat.Partrec.Code.eval_const]
      congr 1
      rw [floorExprRawApprox,floorExprRawApproxWith,dif_pos rfl]
      rfl
    · have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
      have ha := (Nat.unpair_left_le (n-1).unpair.2).trans_lt hp
      have hb := (Nat.unpair_right_le (n-1).unpair.2).trans_lt hp
      have hh : floorCodeRealizes
          (Nat.Partrec.Code.curry basis.scale (Encodable.encode (floorRationalCodeInv (floorRationalCodeNat 2))))
          floorExprHalfQuery :=
        floorCodeRealizes_curry h.scale (floorRationalCodeInv (floorRationalCodeNat 2))
      have hproduct : floorCodeRealizes
          (Nat.Partrec.Code.curry basis.scale
            (Encodable.encode (floorExprProductScale (n-1).unpair.2.unpair.1 (n-1).unpair.2.unpair.2)))
          (floorExprProductQuery (n-1).unpair.2.unpair.1 (n-1).unpair.2.unpair.2) :=
        floorCodeRealizes_curry h.scale _
      have h4 := floorCodeRealizes_comp h.add
        (floorCodeRealizes_pair (floorCodeRealizes_comp (ih _ ha) hh)
          (floorCodeRealizes_comp (ih _ hb) hh))
      have h5 := floorCodeRealizes_comp h.neg (ih _ hp)
      have h6 := floorCodeRealizes_comp h.mul
        (floorCodeRealizes_pair (floorCodeRealizes_comp (ih _ ha) hproduct)
          (floorCodeRealizes_comp (ih _ hb) hproduct))
      have h7 := floorCodeRealizes_comp h.sin
        (floorCodeRealizes_pair (floorCodeRealizes_comp (ih _ hp) hh)
          (floorCodeRealizes_comp h.tolerance hh))
      have h8 := floorCodeRealizes_comp h.cos
        (floorCodeRealizes_pair (floorCodeRealizes_comp (ih _ hp) hh)
          (floorCodeRealizes_comp h.tolerance hh))
      intro q
      conv_rhs => rw [floorExprRawApprox,floorExprRawApproxWith,dif_neg hn]
      rw [floorExprCompile,floorExprCompileWith,dif_neg hn]
      rw [floorExprCompileStep]
      dsimp only
      generalize ht : (n-1).unpair.1=tag
      by_cases htag : tag<9
      · interval_cases tag
        · simp [floorExprApproxOps,Nat.Partrec.Code.eval_const]
        · simpa [floorExprApproxOps] using (floorCodeRealizes_curry h.coordinate (n-1).unpair.2 q)
        · simpa [floorExprApproxOps] using h.parameter q
        · simpa [floorExprApproxOps] using (floorCodeRealizes_curry h.flat (n-1).unpair.2 q)
        · simpa [List.getD_cons_succ,List.getD_cons_zero,floorExprCompile,floorExprCompileStep,
            floorExprRawApprox,floorExprApproxOps] using h4 q
        · simpa [List.getD_cons_succ,List.getD_cons_zero,floorExprCompile,floorExprCompileStep,
            floorExprRawApprox,floorExprApproxOps] using h5 q
        · simpa [List.getD_cons_succ,List.getD_cons_zero,floorExprCompile,floorExprCompileStep,
            floorExprRawApprox,floorExprApproxOps] using h6 q
        · simpa [List.getD_cons_succ,List.getD_cons_zero,floorExprCompile,floorExprCompileStep,
            floorExprRawApprox,floorExprApproxOps] using h7 q
        · simpa [List.getD_cons_succ,List.getD_cons_zero,floorExprCompile,floorExprCompileStep,
            floorExprRawApprox,floorExprApproxOps] using h8 q
      · have h0 : tag≠0 := by omega
        have h1 : tag≠1 := by omega
        have h2 : tag≠2 := by omega
        have h3 : tag≠3 := by omega
        have h4 : tag≠4 := by omega
        have h5 : tag≠5 := by omega
        have h6 : tag≠6 := by omega
        have h7 : tag≠7 := by omega
        have h8 : tag≠8 := by omega
        rw [List.getD_eq_default _ _ (by simp; omega),Nat.Partrec.Code.eval_const]
        simp [floorExprApproxOps,h0,h1,h2,h3,h4,h5,h6,h7,h8]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
