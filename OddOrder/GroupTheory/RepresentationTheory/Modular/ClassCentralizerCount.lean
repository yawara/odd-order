/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A `p`-subgroup sees a conjugacy class only through its centraliser

A `p`-subgroup `P ≤ G` acts by conjugation on any conjugacy class `K` of `G`, and the fixed points
of that action are exactly `K ∩ C_G(P)`.  Since the orbits of a `p`-group have `p`-power size,

`|K| ≡ |K ∩ C_G(P)| (mod p)`.

This is the counting behind the easy half of Brauer's third main theorem: the central character of
the principal block is `λ_{B_0}(K̂) = |K|·1`, while the induced character of the principal block of
`H` reads `|K ∩ C_G(P)|·1`, and in characteristic `p` the congruence identifies them.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_conjClass_modEq_card_centralizer`
-/

namespace OddOrder.RepresentationTheory.Modular

open MulAction

/-- The elements of a conjugacy class of `G`, as a type. -/
abbrev ConjClassCarrier {G : Type*} [Group G] (C : ConjClasses G) : Type _ :=
  {g : G // ConjClasses.mk g = C}

variable {G : Type*} [Group G] {P : Subgroup G} {C : ConjClasses G}

/-- **`P` acts on a conjugacy class by conjugation.** -/
instance instMulActionConjClassCarrier : MulAction ↥P (ConjClassCarrier C) where
  smul u g := ⟨(u : G) * (g : G) * (u : G)⁻¹,
    (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(u : G)⁻¹, by group⟩)).trans g.2⟩
  one_smul g := Subtype.ext (by
    change ((1 : ↥P) : G) * (g : G) * (((1 : ↥P) : G))⁻¹ = (g : G)
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
  mul_smul u v g := Subtype.ext (by
    change ((u * v : ↥P) : G) * (g : G) * (((u * v : ↥P) : G))⁻¹
      = (u : G) * ((v : G) * (g : G) * (v : G)⁻¹) * (u : G)⁻¹
    push_cast
    group)

theorem coe_smul_conjClassCarrier (u : ↥P) (g : ConjClassCarrier C) :
    ((u • g : ConjClassCarrier C) : G) = (u : G) * (g : G) * (u : G)⁻¹ := rfl

/-- The fixed points of the conjugation action are the elements of the class that centralise
`P`. -/
theorem mem_fixedPoints_conjClassCarrier_iff (g : ConjClassCarrier C) :
    g ∈ fixedPoints ↥P (ConjClassCarrier C)
      ↔ (g : G) ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have hg := congrArg Subtype.val (h ⟨u, hu⟩)
    rw [coe_smul_conjClassCarrier] at hg
    calc u * (g : G) = u * (g : G) * u⁻¹ * u := by group
      _ = (g : G) * u := by rw [hg]
  · intro h u
    refine Subtype.ext ?_
    rw [coe_smul_conjClassCarrier, h (u : G) u.2]
    group

variable (P C)

/-- **`|K| ≡ |K ∩ C_G(P)| (mod p)`.**  The orbits of the `p`-group `P` acting by conjugation on
the class `K` have `p`-power size, and the fixed points are `K ∩ C_G(P)`. -/
theorem card_conjClass_modEq_card_centralizer [Finite G] {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p ↥P) :
    Nat.card (ConjClassCarrier C)
      ≡ Nat.card {g : G // ConjClasses.mk g = C ∧ g ∈ Subgroup.centralizer (P : Set G)}
        [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (fixedPoints ↥P (ConjClassCarrier C))
      = Nat.card {g : G // ConjClasses.mk g = C ∧ g ∈ Subgroup.centralizer (P : Set G)} :=
    Nat.card_congr
      ((Equiv.subtypeEquivRight fun g => mem_fixedPoints_conjClassCarrier_iff g).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _))
  rw [← hcard]
  exact hP.card_modEq_card_fixedPoints _

end OddOrder.RepresentationTheory.Modular
