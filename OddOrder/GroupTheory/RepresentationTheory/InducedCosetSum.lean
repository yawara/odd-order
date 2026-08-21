/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Induction of class functions as a sum over cosets (division-free)

**Navarro (8.1)**, generalized.  For `H ≤ G` and a class function `θ` of `H`, Navarro defines
the induced class function by

`θ^G(x) = |H|⁻¹ ∑_{y ∈ G} θ̇(y x y⁻¹)`,  where `θ̇` extends `θ` by zero off `H`,

and uses it for Brauer characters, which take values in the valuation ring `𝒪` of a
`p`-modular system.  That formula is awkward there: when `p ∣ |H|` the scalar `|H|` is **not**
invertible in `𝒪`, so the existing normalized `ClassFunction.induce` (which requires
`Invertible (Nat.card H : k)`) does not apply.

The fix is that the summand is constant on left cosets `yH` (`induceTerm_mul_mem`), so the sum
over `G` is `|H|` copies of a sum over `G ⧸ H`.  Taking *that* sum as the definition gives the
same values with **no division at all**, hence over an arbitrary `CommRing`:

`induceCoset H θ (x) = ∑_{c ∈ G ⧸ H} θ̇(y_c⁻¹ x y_c)`.

This is strictly more general than the book's `(8.1)`, which is stated for class functions on
the `p`-regular elements valued in a field of characteristic zero: nothing below needs
invertibility, a field, or characteristic zero.

## Relation to the book's normalization

The summand here is literally `ClassFunction.induceTerm`, the summand of the repository's
existing unnormalized `ClassFunction.induceSum`; the only difference is the index set (left
cosets rather than all of `G`).  Since the summand is constant on left cosets
(`induceTerm_mul_mem`, proved below), `induceSum = |H| • induceCoset` and hence
`induceCoset` agrees with the normalized `ClassFunction.induce` wherever the latter is defined.

⚠ Those two bridge lemmas are **not yet formalized** — only the definition and its
well-definedness are.  They are the immediate next step (issue 0188).

## Restriction to `p`-regular elements is automatic

Navarro's `θ̇` extends by zero off the `p`-regular part `H⁰`, not off `H`.  The two agree at
every conjugate of a `p`-regular element, because conjugation preserves `p`-regularity
(`OddOrder.GroupTheory.IsPRegular.conj`): for `p`-regular `x` one has
`y⁻¹ x y ∈ H⁰ ↔ y⁻¹ x y ∈ H`.  So no separate "`p`-regular induction" operator is needed —
`induceCoset` restricted to the `p`-regular elements *is* the book's `θ^G`.

## Main definitions

* `OddOrder.RepresentationTheory.ClassFunction.induceCosetTerm` — the coset-indexed summand
* `OddOrder.RepresentationTheory.ClassFunction.induceCoset` — the induced class function

## Main results

* `induceTerm_mul_mem` — the summand of `induceSum` is constant on left cosets, which is both
  what makes `induceCosetTerm` well defined and what will give the normalization bridge
* `induceCosetTerm_mk`, `induceCoset_apply` — computation rules
-/

namespace OddOrder.RepresentationTheory.ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k] {H : Subgroup G}

/-- The summand of `induceSum` is constant on the left coset `yH`: replacing `y` by `y * h`
with `h ∈ H` conjugates `y⁻¹ g y` by `h`, which preserves both membership in `H` and the value
of the `H`-class function `θ`. -/
theorem induceTerm_mul_mem (θ : ClassFunction ↥H k) (y : G) (h : ↥H) (g : G) :
    induceTerm H θ (y * (h : G)) g = induceTerm H θ y g := by
  classical
  have hrw : (y * (h : G))⁻¹ * g * (y * (h : G)) = (h : G)⁻¹ * (y⁻¹ * g * y) * (h : G) := by
    group
  by_cases hA : y⁻¹ * g * y ∈ H
  · have hB : (y * (h : G))⁻¹ * g * (y * (h : G)) ∈ H := by
      rw [hrw]; exact H.mul_mem (H.mul_mem (H.inv_mem h.2) hA) h.2
    rw [induceTerm_of_mem θ hB, induceTerm_of_mem θ hA]
    have hEq : (⟨(y * (h : G))⁻¹ * g * (y * (h : G)), hB⟩ : ↥H)
        = h⁻¹ * ⟨y⁻¹ * g * y, hA⟩ * h⁻¹⁻¹ := Subtype.ext (by simpa using hrw)
    rw [hEq]
    exact θ.property _ h⁻¹
  · have hB : (y * (h : G))⁻¹ * g * (y * (h : G)) ∉ H := by
      intro hcon
      rw [hrw] at hcon
      refine hA ?_
      have hEq : y⁻¹ * g * y
          = (h : G) * ((h : G)⁻¹ * (y⁻¹ * g * y) * (h : G)) * (h : G)⁻¹ := by group
      rw [hEq]
      exact H.mul_mem (H.mul_mem h.2 hcon) (H.inv_mem h.2)
    rw [induceTerm_of_not_mem θ hB, induceTerm_of_not_mem θ hA]

/-- The summand of `induceCoset`, as a function on the coset space `G ⧸ H`. -/
noncomputable def induceCosetTerm (H : Subgroup G) (θ : ClassFunction ↥H k) (g : G) :
    G ⧸ H → k :=
  fun c => Quotient.liftOn' c (fun y => induceTerm H θ y g) <| by
    rintro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * ((⟨a⁻¹ * b, hmem⟩ : ↥H) : G) := by
      change b = a * (a⁻¹ * b); group
    rw [hb, induceTerm_mul_mem θ a ⟨a⁻¹ * b, hmem⟩ g]

@[simp] theorem induceCosetTerm_mk (θ : ClassFunction ↥H k) (g y : G) :
    induceCosetTerm H θ g (QuotientGroup.mk y) = induceTerm H θ y g :=
  rfl

section Fin

variable [Fintype G] [DecidablePred (· ∈ H)] (H)

/-- **Navarro (8.1)** (division-free form).  The class function of `G` induced from a class
function `θ` of `H ≤ G`, as the sum of `θ̇(y⁻¹ · − · y)` over the left cosets `yH`.

Unlike `ClassFunction.induce` this needs no invertibility of `|H|`, so it is available over the
valuation ring of a `p`-modular system — the setting of Navarro's Brauer-character induction. -/
noncomputable def induceCoset (θ : ClassFunction ↥H k) : ClassFunction G k where
  val g := ∑ c : G ⧸ H, induceCosetTerm H θ g c
  property g h := by
    change (∑ c : G ⧸ H, induceCosetTerm H θ (h * g * h⁻¹) c)
      = ∑ c : G ⧸ H, induceCosetTerm H θ g c
    -- reindex by left translation `yH ↦ h⁻¹ y H`, exactly as in `induceSum`
    refine Fintype.sum_bijective (fun c : G ⧸ H => Quotient.liftOn' c
      (fun y => (QuotientGroup.mk (h⁻¹ * y) : G ⧸ H)) ?_) ?_ _ _ ?_
    · rintro a b hab
      have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      refine Quotient.sound' (QuotientGroup.leftRel_apply.mpr ?_)
      have hrw : (h⁻¹ * a)⁻¹ * (h⁻¹ * b) = a⁻¹ * b := by group
      rw [hrw]; exact hmem
    · constructor
      · rintro ⟨a⟩ ⟨b⟩ hab
        have hmem : (h⁻¹ * a)⁻¹ * (h⁻¹ * b) ∈ H :=
          QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
        refine Quotient.sound' (QuotientGroup.leftRel_apply.mpr ?_)
        have hrw : a⁻¹ * b = (h⁻¹ * a)⁻¹ * (h⁻¹ * b) := by group
        rw [hrw]; exact hmem
      · rintro ⟨b⟩
        refine ⟨QuotientGroup.mk (h * b), ?_⟩
        change (QuotientGroup.mk (h⁻¹ * (h * b)) : G ⧸ H) = QuotientGroup.mk b
        congr 1; group
    · rintro ⟨y⟩
      change induceCosetTerm H θ (h * g * h⁻¹) (QuotientGroup.mk y)
        = induceCosetTerm H θ g (QuotientGroup.mk (h⁻¹ * y))
      simp only [induceCosetTerm_mk]
      exact induceTerm_conj H θ y g h

@[simp] theorem induceCoset_apply (θ : ClassFunction ↥H k) (g : G) :
    induceCoset H θ g = ∑ c : G ⧸ H, induceCosetTerm H θ g c :=
  rfl

end Fin

end OddOrder.RepresentationTheory.ClassFunction
