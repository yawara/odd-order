/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands

/-!
# Peterfalvi Appendix III: uniqueness of the invariant two-summand split

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Theorem (e), p. 141, as used in Part II, Ch. I §3,
Lemma 5, p. 107.

Under a fixed-point-free action of `K` with `|K| = q - 1` on a finite group
`E`, an invariant subgroup of order `q` which differs from both members of a
complementary invariant pair of order-`q` normal subgroups maps isomorphically
and `K`-equivariantly onto each member: the projection onto one member is
executed through the quotient by the other member, and simplicity of every
order-`q` invariant subgroup (transitivity of `K` on its nonidentity
elements) makes the composite injective, hence bijective by cardinality.

Consequently two complementary invariant pairs are either equal as unordered
pairs or the members of the first pair are `K`-equivariantly isomorphic.
This is the uniqueness half of the equivalence (e): an
`IsomorphicOrderQModuleSplit` forces the summands of *any* other split of the
same invariant normal subgroup to be `K`-equivariantly isomorphic, which the
type-B recognition consumes on the canonical eigencoordinate split.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

universe uK uE uP

section QuotientProjection

variable {E : Type uE} [Group E]

/-- In a group whose elements commute, every subgroup is normal. -/
theorem normal_of_mul_comm (hcomm : ∀ x y : E, x * y = y * x) (U : Subgroup E) :
    U.Normal := by
  constructor
  intro n hn g
  have h : g * n * g⁻¹ = n := by
    rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]
  rwa [h]

/-- The kernel of the quotient map by `U₁` restricted to `V` is `U₁ ∩ V`. -/
theorem ker_mk'_comp_subtype (U₁ : Subgroup E) [U₁.Normal] (V : Subgroup E) :
    ((QuotientGroup.mk' U₁).comp V.subtype).ker = U₁.subgroupOf V := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply, Subgroup.mem_subgroupOf]
  exact QuotientGroup.eq_one_iff _

/-- Restricted to a subgroup disjoint from `U₁`, the quotient map by `U₁` is
injective. -/
theorem injective_mk'_comp_subtype_of_disjoint {U₁ V : Subgroup E} [U₁.Normal]
    (hdisj : Disjoint U₁ V) :
    Function.Injective ((QuotientGroup.mk' U₁).comp V.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_mk'_comp_subtype]
  exact Subgroup.subgroupOf_eq_bot.mpr hdisj

/-- Restricted to a subgroup covering `E` jointly with `U₁`, the quotient map
by `U₁` is surjective. -/
theorem surjective_mk'_comp_subtype_of_codisjoint {U₁ U₂ : Subgroup E}
    [U₁.Normal] (hsup : U₁ ⊔ U₂ = ⊤) :
    Function.Surjective ((QuotientGroup.mk' U₁).comp U₂.subtype) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U₁ q
  have hg : g ∈ U₁ ⊔ U₂ := hsup ▸ Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
  obtain ⟨u, hu, v, hv, rfl⟩ := hg
  refine ⟨⟨v, hv⟩, ?_⟩
  have hu1 : (QuotientGroup.mk' U₁) u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
  simp [map_mul, hu1]

/-- The quotient of a finite group by one member of a complementary pair has
the cardinality of the other member. -/
theorem card_quotient_of_isCompl [Finite E] {U₁ U₂ : Subgroup E} [U₁.Normal]
    (hcompl : IsCompl U₁ U₂) :
    Nat.card (E ⧸ U₁) = Nat.card ↥U₂ := by
  have hbij : Function.Bijective ((QuotientGroup.mk' U₁).comp U₂.subtype) :=
    ⟨injective_mk'_comp_subtype_of_disjoint hcompl.disjoint,
     surjective_mk'_comp_subtype_of_codisjoint
       (codisjoint_iff.mp hcompl.codisjoint)⟩
  exact (Nat.card_eq_of_bijective _ hbij).symm

end QuotientProjection

section EquivariantProjection

variable {K : Type uK} {E : Type uE} [Group K] [Group E]

/-- Transport a `K`-equivariant isomorphism between restricted actions along
equalities of the underlying subgroups. -/
def kEquivariantMulEquivCongr {rho : K →* MulAut E}
    {A B A' B' : Subgroup E} (hA : A = A') (hB : B = B')
    {hAinv : IsAInvariant rho A} {hBinv : IsAInvariant rho B}
    {hA'inv : IsAInvariant rho A'} {hB'inv : IsAInvariant rho B'}
    (e : KEquivariantMulEquiv hAinv.restrict hBinv.restrict) :
    KEquivariantMulEquiv hA'inv.restrict hB'inv.restrict := by
  subst hA
  subst hB
  exact e

/-- **Equivariant projection onto the quotient.**  An invariant subgroup
disjoint from an invariant normal subgroup `U₁` and of full quotient
cardinality maps isomorphically onto `E ⧸ U₁`, equivariantly for the induced
`K`-action. -/
noncomputable def quotientKEquivariantMulEquivOfDisjoint [Finite E]
    {rho : K →* MulAut E} {U₁ V : Subgroup E} [U₁.Normal]
    (hU₁inv : IsAInvariant rho U₁) (hVinv : IsAInvariant rho V)
    (hdisj : Disjoint U₁ V) (hcard : Nat.card ↥V = Nat.card (E ⧸ U₁)) :
    KEquivariantMulEquiv hVinv.restrict (quotientMulAutHom hU₁inv) where
  toMulEquiv := MulEquiv.ofBijective _
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨injective_mk'_comp_subtype_of_disjoint hdisj, hcard⟩)
  equivariant _ _ := rfl

end EquivariantProjection

section ThirdInvariant

variable {K : Type uK} {E : Type uE} [Group K] [Group E] [Finite E]

/-- A `K`-invariant subgroup of the same order as `V` under a fixed-point-free
action with `|K| = |V| - 1` is either equal to `V` or disjoint from `V`. -/
theorem disjoint_of_invariant_of_ne_of_card
    (rho : K →* MulAut E)
    (hfree : ∀ k : K, k ≠ 1 → ∀ x : E, rho k x = x → x = 1)
    {U V : Subgroup E} (hUinv : IsAInvariant rho U) (hVinv : IsAInvariant rho V)
    (hcardK : Nat.card K = Nat.card ↥V - 1)
    (hcard : Nat.card ↥U = Nat.card ↥V) (hne : V ≠ U) :
    Disjoint U V := by
  rcases invariant_eq_bot_or_top_of_fixedPointFree_card rho hfree hVinv hcardK
      (hVinv.subgroupOf hUinv) with hbot | htop
  · exact Subgroup.subgroupOf_eq_bot.mp hbot
  · exact absurd (Subgroup.eq_of_le_of_card_ge
      (Subgroup.subgroupOf_eq_top.mp htop) hcard.le) hne

/-- **Uniqueness of the invariant two-summand split** (Peterfalvi Appendix
III, Theorem (e), uniqueness half).  A third invariant subgroup of the
summand order, distinct from both members of a complementary invariant pair
of normal subgroups, forces the two members to be `K`-equivariantly
isomorphic: it projects isomorphically onto each member through the quotient
by the other. -/
theorem nonempty_kEquivariantMulEquiv_of_third_invariant
    (rho : K →* MulAut E)
    (hfree : ∀ k : K, k ≠ 1 → ∀ x : E, rho k x = x → x = 1)
    {U₁ U₂ V : Subgroup E} [U₁.Normal] [U₂.Normal]
    (hU₁inv : IsAInvariant rho U₁) (hU₂inv : IsAInvariant rho U₂)
    (hVinv : IsAInvariant rho V) (hcompl : IsCompl U₁ U₂)
    (hcardK : Nat.card K = Nat.card ↥V - 1)
    (hcardU₁ : Nat.card ↥U₁ = Nat.card ↥V)
    (hcardU₂ : Nat.card ↥U₂ = Nat.card ↥V)
    (hne₁ : V ≠ U₁) (hne₂ : V ≠ U₂) :
    Nonempty (KEquivariantMulEquiv hU₁inv.restrict hU₂inv.restrict) := by
  have hd₁ : Disjoint U₁ V :=
    disjoint_of_invariant_of_ne_of_card rho hfree hU₁inv hVinv hcardK hcardU₁ hne₁
  have hd₂ : Disjoint U₂ V :=
    disjoint_of_invariant_of_ne_of_card rho hfree hU₂inv hVinv hcardK hcardU₂ hne₂
  have hq₁ : Nat.card (E ⧸ U₁) = Nat.card ↥U₂ := card_quotient_of_isCompl hcompl
  have hq₂ : Nat.card (E ⧸ U₂) = Nat.card ↥U₁ := card_quotient_of_isCompl hcompl.symm
  let eV₁ : KEquivariantMulEquiv hVinv.restrict (quotientMulAutHom hU₂inv) :=
    quotientKEquivariantMulEquivOfDisjoint hU₂inv hVinv hd₂
      (by rw [hq₂, hcardU₁])
  let eU₁ : KEquivariantMulEquiv hU₁inv.restrict (quotientMulAutHom hU₂inv) :=
    quotientKEquivariantMulEquivOfDisjoint hU₂inv hU₁inv hcompl.disjoint.symm
      hq₂.symm
  let eV₂ : KEquivariantMulEquiv hVinv.restrict (quotientMulAutHom hU₁inv) :=
    quotientKEquivariantMulEquivOfDisjoint hU₁inv hVinv hd₁
      (by rw [hq₁, hcardU₂])
  let eU₂ : KEquivariantMulEquiv hU₂inv.restrict (quotientMulAutHom hU₁inv) :=
    quotientKEquivariantMulEquivOfDisjoint hU₁inv hU₂inv hcompl.disjoint
      hq₁.symm
  exact ⟨((eV₁.trans eU₁.symm).symm).trans (eV₂.trans eU₂.symm)⟩

end ThirdInvariant

section SplitEndpoint

variable {K : Type uK} {P : Type uP} [Group K] [Group P] [Finite P]

/-- **Peterfalvi Appendix III, Theorem (e), uniqueness half, split form.**
An equivariantly isomorphic split forces the summands of *any* split of the
same invariant normal subgroup to be `K`-equivariantly isomorphic.

Either the two splits agree as unordered pairs — in which case the summand
isomorphism transports directly — or some summand of the isomorphic split is
a third invariant subgroup, which projects isomorphically onto both summands
of the other split. -/
theorem OrderQModuleSplit.nonempty_summandEquiv_of_isomorphic
    {act : K →* MulAut P} {Z : Subgroup P} [Z.Normal]
    {hZinv : IsAInvariant act Z}
    (csplit : OrderQModuleSplit act Z hZinv)
    (isplit : IsomorphicOrderQModuleSplit act Z hZinv)
    (hfree : ∀ k : K, k ≠ 1 → ∀ x : P ⧸ Z,
      quotientMulAutHom hZinv k x = x → x = 1)
    (hcardK : Nat.card K = Nat.card ↥Z - 1)
    (hZnt : 1 < Nat.card ↥Z) :
    Nonempty (KEquivariantMulEquiv csplit.leftInvariant.restrict
      csplit.rightInvariant.restrict) := by
  classical
  have hcomm : ∀ x y : P ⧸ Z, x * y = y * x := csplit.quotientEA.comm
  haveI : (csplit.left).Normal := normal_of_mul_comm hcomm _
  haveI : (csplit.right).Normal := normal_of_mul_comm hcomm _
  have hcV₁ := isplit.split.leftCard
  have hcV₂ := isplit.split.rightCard
  have hcU₁ := csplit.leftCard
  have hcU₂ := csplit.rightCard
  have key : ∀ V : Subgroup (P ⧸ Z),
      IsAInvariant (quotientMulAutHom hZinv) V →
      Nat.card ↥V = Nat.card ↥Z → V ≠ csplit.left → V ≠ csplit.right →
      Nonempty (KEquivariantMulEquiv csplit.leftInvariant.restrict
        csplit.rightInvariant.restrict) := by
    intro V hVinv hVcard hne₁ hne₂
    exact nonempty_kEquivariantMulEquiv_of_third_invariant _ hfree
      csplit.leftInvariant csplit.rightInvariant hVinv csplit.complementary
      (by rw [hVcard]; exact hcardK) (hcU₁.trans hVcard.symm)
      (hcU₂.trans hVcard.symm) hne₁ hne₂
  have hVne : isplit.split.left ≠ isplit.split.right := by
    intro heq
    have hd : Disjoint isplit.split.right isplit.split.right := by
      have hdlr := isplit.split.complementary.disjoint
      rwa [heq] at hdlr
    have hbot := disjoint_self.mp hd
    rw [hbot, Subgroup.card_bot] at hcV₂
    omega
  by_cases h₁₁ : isplit.split.left = csplit.left
  · by_cases h₂₂ : isplit.split.right = csplit.right
    · exact ⟨kEquivariantMulEquivCongr h₁₁ h₂₂ isplit.summandEquiv⟩
    · by_cases h₂₁ : isplit.split.right = csplit.left
      · exact absurd (h₁₁.trans h₂₁.symm) hVne
      · exact key _ isplit.split.rightInvariant hcV₂ h₂₁ h₂₂
  · by_cases h₁₂ : isplit.split.left = csplit.right
    · by_cases h₂₁ : isplit.split.right = csplit.left
      · exact ⟨kEquivariantMulEquivCongr h₂₁ h₁₂ isplit.summandEquiv.symm⟩
      · by_cases h₂₂ : isplit.split.right = csplit.right
        · exact absurd (h₁₂.trans h₂₂.symm) hVne
        · exact key _ isplit.split.rightInvariant hcV₂ h₂₁ h₂₂
    · exact key _ isplit.split.leftInvariant hcV₁ h₁₁ h₁₂

end SplitEndpoint

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
