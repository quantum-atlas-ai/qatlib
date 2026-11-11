/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalCodec
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceJets

/-!
# Paid Original Jet Codec

Raw Machine constructions for Effective Gauge.
Defines `Query`, `Reply`, `queryValue`.
Proves `queryValue_ofOriginal`, `replyValue_ofOriginal`, `vector3_entries`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open Qatlib.Concepts.BitWordCompiler

namespace PaidJetProtocol

/-- Data and hypotheses for Query in the Raw Machine construction. -/
structure Query where
  point : Vector RedundantRational.Frac 3
  alpha : Vector ℕ 3
  precision : ℕ

/-- Abbreviation for Reply in the Raw Machine construction. -/
abbrev Reply := Vector RedundantRational.Frac 3

/-- Definition of query Value in the Raw Machine construction. -/
def queryValue (q : Query) : OriginalJetQuery :=
  (((fun j => RedundantRational.value q.point[j.val]),fun j => q.alpha[j.val]),q.precision)

/-- Definition of query Of Original in the Raw Machine construction. -/
def queryOfOriginal (q : OriginalJetQuery) : Query :=
  ⟨Vector.ofFn (fun j => RedundantRational.ofRat (q.1.1 j)),Vector.ofFn q.1.2,q.2⟩

/-- Definition of reply Value in the Raw Machine construction. -/
def replyValue (reply : Reply) : Fin 3 → ℚ := fun j => RedundantRational.value reply[j.val]
/-- Definition of reply Of Original in the Raw Machine construction. -/
def replyOfOriginal (value : Fin 3 → ℚ) : Reply := Vector.ofFn (fun j => RedundantRational.ofRat (value j))

/-- Original `queryValue_ofOriginal` guarantee for the `PaidOriginalJetCodec` construction; the complete source hypotheses are retained. -/
theorem queryValue_ofOriginal (q : OriginalJetQuery) : queryValue (queryOfOriginal q)=q := by
  rcases q with ⟨⟨X,alpha⟩,b⟩
  simp only [queryValue,queryOfOriginal,Vector.getElem_ofFn,RedundantRational.value_ofRat]

/-- Original `replyValue_ofOriginal` guarantee for the `PaidOriginalJetCodec` construction; the complete source hypotheses are retained. -/
theorem replyValue_ofOriginal (value : Fin 3 → ℚ) : replyValue (replyOfOriginal value)=value := by
  funext j
  simp only [replyValue,replyOfOriginal,Vector.getElem_ofFn,RedundantRational.value_ofRat]

/-- Original `vector3_entries` guarantee for the `PaidOriginalJetCodec` construction; the complete source hypotheses are retained. -/
private theorem vector3_entries {α : Type} (xs : Vector α 3) :
    Vector.ofFn ![xs[0],xs[1],xs[2]]=xs := by
  apply Vector.ext
  intro i hi
  have h : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

/-- Definition of encode Query in the Raw Machine construction. -/
def encodeQuery (q : Query) : CanonicalCodec.Bits :=
  PaidRationalBridge.encode q.point[0]++(PaidRationalBridge.encode q.point[1]++
    (PaidRationalBridge.encode q.point[2]++(CanonicalCodec.natBits q.alpha[0]++
      (CanonicalCodec.natBits q.alpha[1]++(CanonicalCodec.natBits q.alpha[2]++CanonicalCodec.natBits q.precision)))))

/-- Definition of read Query in the Raw Machine construction. -/
def readQuery (bits : CanonicalCodec.Bits) : Option (Query × CanonicalCodec.Bits) := do
  let (x,tail) ← PaidRationalBridge.read bits
  let (y,tail) ← PaidRationalBridge.read tail
  let (z,tail) ← PaidRationalBridge.read tail
  let (a0,tail) ← CanonicalCodec.readNat tail
  let (a1,tail) ← CanonicalCodec.readNat tail
  let (a2,tail) ← CanonicalCodec.readNat tail
  let (b,tail) ← CanonicalCodec.readNat tail
  return (⟨Vector.ofFn ![x,y,z],Vector.ofFn ![a0,a1,a2],b⟩,tail)

/-- Definition of encode Reply in the Raw Machine construction. -/
def encodeReply (reply : Reply) : CanonicalCodec.Bits :=
  PaidRationalBridge.encode reply[0]++(PaidRationalBridge.encode reply[1]++PaidRationalBridge.encode reply[2])

/-- Definition of read Reply in the Raw Machine construction. -/
def readReply (bits : CanonicalCodec.Bits) : Option (Reply × CanonicalCodec.Bits) := do
  let (x,tail) ← PaidRationalBridge.read bits
  let (y,tail) ← PaidRationalBridge.read tail
  let (z,tail) ← PaidRationalBridge.read tail
  return (Vector.ofFn ![x,y,z],tail)

/-- Original `readQuery_complete` guarantee for the `PaidOriginalJetCodec` construction; the complete source hypotheses are retained. -/
theorem readQuery_complete (q : Query) (tail : CanonicalCodec.Bits) :
    readQuery (encodeQuery q++tail)=some (q,tail) := by
  cases q with
  | mk point alpha precision =>
    simp [readQuery,encodeQuery,List.append_assoc,PaidRationalBridge.read_complete,
      CanonicalCodec.readNat_complete,vector3_entries]

/-- Original `readReply_complete` guarantee for the `PaidOriginalJetCodec` construction; the complete source hypotheses are retained. -/
theorem readReply_complete (reply : Reply) (tail : CanonicalCodec.Bits) :
    readReply (encodeReply reply++tail)=some (reply,tail) := by
  simp [readReply,encodeReply,List.append_assoc,PaidRationalBridge.read_complete,vector3_entries]

/-- Full original rational points and all multi-indices/precisions are
covered. Prefix parsing does not certify a paid source caller or its clock. -/
theorem original_query_coverage (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ) (b : ℕ) :
    ∃ query : Query, queryValue query=((X,alpha),b) ∧
      ∀ tail, readQuery (encodeQuery query++tail)=some (query,tail) :=
  ⟨queryOfOriginal ((X,alpha),b),queryValue_ofOriginal _,readQuery_complete _⟩

/-- Original `original_reply_coverage` guarantee for the `PaidOriginalJetCodec` construction; the complete source hypotheses are retained. -/
theorem original_reply_coverage (value : Fin 3 → ℚ) :
    ∃ reply : Reply, replyValue reply=value ∧
      ∀ tail, readReply (encodeReply reply++tail)=some (reply,tail) :=
  ⟨replyOfOriginal value,replyValue_ofOriginal _,readReply_complete _⟩

end PaidJetProtocol
end Qatlib.Concepts.EffectiveGauge.RawMachine
