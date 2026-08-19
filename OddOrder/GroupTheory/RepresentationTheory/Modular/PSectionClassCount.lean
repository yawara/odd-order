/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSection

/-!
# The `p`-sections partition the conjugacy classes

Navarro opens the proof of (5.12) with the count

`k(G) = ∑_{i=1}^{k} |IBr(C_G(x_i))|`,

where `x_1, …, x_k` represent the `G`-classes of `p`-elements: the elements `x_i y`, with `y`
running over the `p`-regular classes of `C_G(x_i)`, represent the classes of `G` exactly once.
That is the statement that makes the generalized decomposition matrix square.

Two halves:

* **one section** — the `G`-classes whose `p`-part class is `[x]` biject with the `p`-regular
  classes of `C_G(x)`, by `[y] ↦ [x y]`.  Surjectivity is the `p`/`p'` factorisation
  (`pPart_mul_pRegularPart`) after moving the `p`-part of a representative onto `x`; injectivity
  is `isConj_centralizer_of_isConj_mul`.
* **all sections** — `pPartClass` fibres `ConjClasses G` over the `p`-element classes.

No representatives of the `p`-element classes are chosen: the sum runs over the `p`-element
classes themselves and `Quotient.out` supplies the centralizer.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.sectionClassMap` — `[y] ↦ [x y]`
* `OddOrder.RepresentationTheory.Modular.pSectionClassEquiv` — it is a bijection

## Main results

* `OddOrder.RepresentationTheory.Modular.card_conjClasses_eq_sum_card_pRegularClass` —
  `k(G) = ∑_{[x] a p-element class} #cl(C_G(x)⁰)`
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-! ### The classes inside one `p`-section -/

section OneSection

variable (hp : p.Prime) {x : G} (hx : IsPElement p x)

omit [Finite G] in
include hp hx in
/-- **`(x y)_p = x`, read on classes.** -/
theorem pPartClass_mk_mul {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    pPartClass p (ConjClasses.mk (x * (y : G))) = ConjClasses.mk x := by
  rw [pPartClass_mk, pPart_mul_eq_of_isPElement hp
    ((Subgroup.mem_centralizer_iff.mp y.2) x rfl) hx (isPRegular_coe hy)]

include hp hx in
/-- **`[y] ↦ [x y]`**: a `p`-regular class of `C_G(x)` gives a `G`-class with `p`-part class
`[x]`. -/
noncomputable def sectionClassMap
    (c : {c : ConjClasses ↥(centralizerOf x) // IsPRegularClass p c}) :
    {C : ConjClasses G // pPartClass p C = ConjClasses.mk x} :=
  ⟨ConjClasses.mk (x * ((c.1.out : ↥(centralizerOf x)) : G)),
    pPartClass_mk_mul hp hx (isPRegular_out c.2)⟩

omit [Finite G] in
include hp hx in
/-- The value of `sectionClassMap` at a class given by a representative. -/
theorem sectionClassMap_mk {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    ((sectionClassMap hp hx ⟨ConjClasses.mk y, isPRegularClass_mk.mpr hy⟩ :
        {C : ConjClasses G // pPartClass p C = ConjClasses.mk x}) : ConjClasses G)
      = ConjClasses.mk (x * (y : G)) := by
  refine ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_mul_of_isConj x ?_)
  exact ConjClasses.mk_eq_mk_iff_isConj.mp (conjClasses_mk_out (ConjClasses.mk y))

omit [Finite G] in
include hp hx in
theorem sectionClassMap_injective : Function.Injective (sectionClassMap hp hx) := by
  intro c₁ c₂ h
  have hconj : IsConj (x * ((c₁.1.out : ↥(centralizerOf x)) : G))
      (x * ((c₂.1.out : ↥(centralizerOf x)) : G)) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h)
  obtain ⟨g, hg, hgy⟩ := isConj_centralizer_of_isConj_mul hp hx
    (isPRegular_coe (isPRegular_out c₁.2)) (isPRegular_coe (isPRegular_out c₂.2))
    (c₁.1.out).2 (c₂.1.out).2 hconj
  refine Subtype.ext ?_
  rw [← conjClasses_mk_out c₁.1, ← conjClasses_mk_out c₂.1]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr
    (isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext (by push_cast; exact hgy)⟩)

include hp hx in
theorem sectionClassMap_surjective : Function.Surjective (sectionClassMap hp hx) := by
  rintro ⟨C, hC⟩
  -- move the `p`-part of a representative onto `x`
  obtain ⟨h, hh⟩ : ∃ h : G, h * pPart p C.out * h⁻¹ = x := by
    refine isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ?_)
    rw [← pPartClass_mk, conjClasses_mk_out]
    exact hC
  set g : G := h * C.out * h⁻¹ with hgdef
  have hgfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hpg : pPart p g = x := by rw [hgdef, pPart_conj, hh]
  set y : G := pRegularPart p g with hydef
  have hyreg : IsPRegular p y := isPRegular_pRegularPart hp hgfin
  have hcomm : Commute x y := by
    rw [← hpg, hydef]
    exact (commute_pRegularPart_pPart g).symm
  have hymem : y ∈ centralizerOf x :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hcomm.eq
  have hfac : x * y = g := by rw [← hpg, hydef, pPart_mul_pRegularPart hp hgfin]
  refine ⟨⟨ConjClasses.mk ⟨y, hymem⟩,
    isPRegularClass_mk.mpr (isPRegular_coe_iff.mp hyreg)⟩, Subtype.ext ?_⟩
  rw [sectionClassMap_mk hp hx (isPRegular_coe_iff.mp hyreg)]
  change ConjClasses.mk (x * y) = C
  rw [hfac, hgdef]
  conv_rhs => rw [← conjClasses_mk_out C]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm

include hp hx in
/-- **The `G`-classes in the `p`-section of `x` are the `p`-regular classes of `C_G(x)`.**  This
is the bijection behind Navarro's count `k(G) = ∑_i |IBr(C_G(x_i))|`. -/
noncomputable def pSectionClassEquiv :
    {c : ConjClasses ↥(centralizerOf x) // IsPRegularClass p c}
      ≃ {C : ConjClasses G // pPartClass p C = ConjClasses.mk x} :=
  Equiv.ofBijective _ ⟨sectionClassMap_injective hp hx, sectionClassMap_surjective hp hx⟩

end OneSection

/-! ### Summing over all `p`-sections -/

/-- **`p`-part classes fibre the conjugacy classes.** -/
theorem card_conjClasses_eq_sum_card_pPartClass_fiber [Fintype (ConjClasses G)] :
    Nat.card (ConjClasses G)
      = ∑ D : ConjClasses G, Nat.card {C : ConjClasses G // pPartClass p C = D} := by
  have : ∀ D : ConjClasses G, Finite {C : ConjClasses G // pPartClass p C = D} := fun _ =>
    Subtype.finite
  rw [← Nat.card_sigma (β := fun D : ConjClasses G => {C : ConjClasses G // pPartClass p C = D})]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (pPartClass p)).symm

/-- **Navarro's count in the proof of (5.12)**: `k(G) = ∑_{[x]} #cl(C_G(x)⁰)`, the sum running
over the `G`-classes of `p`-elements.

`Quotient.out` supplies a representative of each `p`-element class; the summand is the number of
`p`-regular classes of its centralizer, which is `|IBr(C_G(x))|`
(`card_eq_card_pRegularClass`). -/
theorem card_conjClasses_eq_sum_card_pRegularClass (hp : p.Prime) [Fintype (ConjClasses G)]
    [DecidablePred (fun D : ConjClasses G => IsPElementClass p D)] :
    Nat.card (ConjClasses G)
      = ∑ D ∈ Finset.univ.filter (fun D : ConjClasses G => IsPElementClass p D),
          Nat.card {c : ConjClasses ↥(centralizerOf (Quotient.out D)) // IsPRegularClass p c} := by
  rw [card_conjClasses_eq_sum_card_pPartClass_fiber (p := p),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun D : ConjClasses G => IsPElementClass p D)]
  have hzero : ∀ D ∈ Finset.univ.filter (fun D : ConjClasses G => ¬ IsPElementClass p D),
      Nat.card {C : ConjClasses G // pPartClass p C = D} = 0 := by
    intro D hD
    have hD' : ¬ IsPElementClass p D := (Finset.mem_filter.mp hD).2
    have : IsEmpty {C : ConjClasses G // pPartClass p C = D} :=
      ⟨fun C => hD' (C.2 ▸ isPElementClass_pPartClass hp C.1)⟩
    exact Nat.card_of_isEmpty
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hD' : IsPElementClass p D := (Finset.mem_filter.mp hD).2
  have hout : IsPElement p (Quotient.out D) := by
    have hmk : IsPElementClass p (ConjClasses.mk (Quotient.out D)) := by
      rw [conjClasses_mk_out]; exact hD'
    exact isPElementClass_mk.mp hmk
  refine (Nat.card_congr ((pSectionClassEquiv hp hout).trans (Equiv.subtypeEquivRight ?_))).symm
  intro C
  rw [conjClasses_mk_out]

end OddOrder.RepresentationTheory.Modular
