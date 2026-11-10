/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.ProdIncidence.ProductChain

structure Endpoints (v e : ℕ) where
  start : Fin e → Fin v
  finish : Fin e → Fin v

abbrev Vertex (v₁ v₂ : ℕ) := Fin v₁ × Fin v₂
abbrev Edge (v₁ e₁ v₂ e₂ : ℕ) := (Fin e₁ × Fin v₂) ⊕ (Fin v₁ × Fin e₂)
abbrev Face (e₁ e₂ : ℕ) := Fin e₁ × Fin e₂

def endpointLoad {v e : ℕ} (p : Endpoints v e) (a : Fin v) : ℕ :=
  (Finset.univ.filter fun i => p.start i = a).card +
    (Finset.univ.filter fun i => p.finish i = a).card

def boundary₁ {v₁ e₁ v₂ e₂ : ℕ} (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂) :
    Matrix (Vertex v₁ v₂) (Edge v₁ e₁ v₂ e₂) (ZMod 2)
  | a, .inl b => if a.2 = b.2 then
      (if a.1 = p.start b.1 then 1 else 0) +
        (if a.1 = p.finish b.1 then 1 else 0) else 0
  | a, .inr b => if a.1 = b.1 then
      (if a.2 = q.start b.2 then 1 else 0) +
        (if a.2 = q.finish b.2 then 1 else 0) else 0

def boundary₂ {v₁ e₁ v₂ e₂ : ℕ} (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂) :
    Matrix (Edge v₁ e₁ v₂ e₂) (Face e₁ e₂) (ZMod 2)
  | .inl a, b => if a.1 = b.1 then
      (if a.2 = q.start b.2 then 1 else 0) +
        (if a.2 = q.finish b.2 then 1 else 0) else 0
  | .inr a, b => if a.2 = b.2 then
      (if a.1 = p.start b.1 then 1 else 0) +
        (if a.1 = p.finish b.1 then 1 else 0) else 0

def productCss {v₁ e₁ v₂ e₂ : ℕ} (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂)
    (h : boundary₁ p q * boundary₂ p q = 0) :
    CssData (Edge v₁ e₁ v₂ e₂) (Vertex v₁ v₂) (Face e₁ e₂) where
  hX := boundary₁ p q
  hZ := (boundary₂ p q).transpose
  hcompat := by simpa only [Matrix.transpose_transpose] using h

end Qatlib.Concepts.ProdIncidence.ProductChain
