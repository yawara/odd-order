/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ZIrr

/-!
# Indexing irreducible characters

This module names the subtype of irreducible complex characters as a first-class
indexing type.  The initial Wave 1a statements used the raw subtype
`{φ : ClassFunction G ℂ // IsIrreducibleCharacter φ}` directly; naming it keeps
column orthogonality, Brauer permutation, and Peterfalvi §3 statements aligned.

This file does not prove existence or finiteness of the indexing type.  Those are
separate representation-theoretic facts.  It only provides a stable API for
statements that take an explicit `[Fintype (IrreducibleCharacter G)]`.

Reference issue: `issues/0021-peterfalvi-second-orthogonality.md`.
-/

namespace OddOrder.RepresentationTheory

variable (G : Type*) [Group G]

/-- The type of irreducible complex characters of `G`, as class functions. -/
abbrev IrreducibleCharacter :=
  {φ : ClassFunction G ℂ // IsIrreducibleCharacter φ}

/-- The trivial irreducible character of `G`. -/
def trivialIrreducibleCharacter : IrreducibleCharacter G :=
  ⟨trivialClassFunction G, trivialClassFunction_isIrreducible⟩

namespace IrreducibleCharacter

variable {G}

/-- The underlying class function of an irreducible character index. -/
abbrev toClassFunction (χ : IrreducibleCharacter G) : ClassFunction G ℂ :=
  χ.1

instance : Coe (IrreducibleCharacter G) (ClassFunction G ℂ) :=
  ⟨toClassFunction⟩

@[simp] theorem coe_trivialIrreducibleCharacter :
    ((trivialIrreducibleCharacter G : IrreducibleCharacter G) : ClassFunction G ℂ) =
      trivialClassFunction G :=
  rfl

@[simp] theorem coe_mk (φ : ClassFunction G ℂ) (hφ : IsIrreducibleCharacter φ) :
    ((⟨φ, hφ⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = φ :=
  rfl

@[simp] theorem isIrreducible (χ : IrreducibleCharacter G) :
    IsIrreducibleCharacter (χ : ClassFunction G ℂ) :=
  χ.2

@[simp] theorem mem_irreducibleCharacters (χ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ∈ irreducibleCharacters G :=
  χ.2

theorem mem_ZIrr (χ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ∈ ZIrr G :=
  IsIrreducibleCharacter.mem_ZIrr χ.2

@[ext] theorem ext {χ ψ : IrreducibleCharacter G}
    (h : (χ : ClassFunction G ℂ) = (ψ : ClassFunction G ℂ)) : χ = ψ :=
  Subtype.ext h

@[simp] theorem eta (χ : IrreducibleCharacter G) :
    (⟨(χ : ClassFunction G ℂ), χ.isIrreducible⟩ : IrreducibleCharacter G) = χ :=
  rfl

end IrreducibleCharacter

end OddOrder.RepresentationTheory
