/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_ImprimitiveUBound
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import OddOrder.GroupTheory.RepresentationTheory.SemilinearFieldAut

/-!
# Peterfalvi (9.7.b) — the chief-factor Galois-field model

In Clifford case (b), the faithful image `Ū` of the `U`-action on the chief factor
`H̄ = H/H₀` acts irreducibly.  The shared Singer construction therefore identifies the additive
group of `H̄` with `GF(p^q)` and realizes `Ū` by multiplication.

This file constructs the actual field carrier and scalar embedding.  It does not use the legacy
opaque proposition `CliffordCaseBData.field_model`.
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory OddOrder.RepresentationTheory OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)
open scoped IsMulCommutative

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (9.7.b), faithful-image field model.**  The irreducible action of
`Ū = range(uActionHom)` on `H̄ = H/H₀` is multiplication on `GF(p^q)` through an injective
homomorphism. -/
theorem caseB_exists_galoisField_repr [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
    ∃ (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
      (μ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (GaloisField chief.p data.q)ˣ),
      Function.Injective μ ∧
      ∀ (u : ↥(MonoidHom.range (uActionHom data chief)))
        (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x) := by
  letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  haveI : chief.N.Normal := chief.N_normal
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  letI : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  haveI : Finite (↥data.H ⧸ chief.N) :=
    Finite.of_surjective (QuotientGroup.mk' chief.N)
      (QuotientGroup.mk'_surjective chief.N)
  letI : CommGroup ↥(MonoidHom.range (uActionHom data chief)) :=
    { (inferInstance : Group ↥(MonoidHom.range (uActionHom data chief))) with
      mul_comm := uActionHom_range_comm chief }
  have hcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q :=
    chiefFactor_quotient_card chief
  have hqpos : 0 < data.q := data.nontrivial.2.1.pos
  haveI hnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]
      exact Nat.one_lt_pow hqpos.ne' chief.p_prime.one_lt)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (MonoidHom.range (uActionHom data chief)).subtype J →
        J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply caseB.actsIrreducibly
    intro u
    exact hJ ⟨uActionHom data chief u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
  have hfaith : ∀ u : ↥(MonoidHom.range (uActionHom data chief)),
      (∀ x : ↥data.H ⧸ chief.N,
        (MonoidHom.range (uActionHom data chief)).subtype u x = x) → u = 1 := by
    intro u hu
    apply Subtype.ext
    ext x
    simpa using hu x
  obtain ⟨hsimple, hfaith'⟩ :=
    elabRepresentation_isSimpleModule_and_faithful
      (p := chief.p) (φ := (MonoidHom.range (uActionHom data chief)).subtype)
      hnt hirr hfaith
  haveI : Finite (elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asModule :=
    ‹Finite (↥data.H ⧸ chief.N)›
  have hcardM : Nat.card (elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asModule =
        chief.p ^ data.q := by
    calc
      Nat.card (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype).asModule =
          Nat.card (Additive (↥data.H ⧸ chief.N)) := rfl
      _ = Nat.card (↥data.H ⧸ chief.N) := Nat.card_congr Additive.toMul
      _ = chief.p ^ data.q := hcard
  have hq : data.q ≠ 0 := by
    exact data.nontrivial.2.1.ne_zero
  obtain ⟨e₀, μ, hμinj, hcompat⟩ :=
    @exists_galoisField_repr_of_faithful_irreducible chief.p _
      ↥(MonoidHom.range (uActionHom data chief))
      (elabRepresentation chief.p
        (MonoidHom.range (uActionHom data chief)).subtype).asModule
      inferInstance
      (Representation.instAddCommGroupAsModule
        (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype))
      (Representation.instModuleMonoidAlgebraAsModule
        (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype))
      inferInstance data.q hq hsimple hcardM hfaith'
  let e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q :=
    e₀
  refine ⟨e, μ, hμinj, ?_⟩
  intro u x
  have h := hcompat u
    (show (elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asModule from
        Additive.ofMul x)
  change e₀ ((elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype).asAlgebraHom
        (MonoidAlgebra.of (ZMod chief.p)
          ↥(MonoidHom.range (uActionHom data chief)) u) |>.toFun (Additive.ofMul x)) =
    ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
      e₀ (Additive.ofMul x) at h
  rw [Representation.asAlgebraHom_of] at h
  have happ : ((elabRepresentation chief.p
      (MonoidHom.range (uActionHom data chief)).subtype u).toFun
        (Additive.ofMul x)) = Additive.ofMul
          ((MonoidHom.range (uActionHom data chief)).subtype u x) :=
    elabRepresentation_apply chief.p
      (MonoidHom.range (uActionHom data chief)).subtype u x
  rw [happ] at h
  change e₀ (Additive.ofMul
      ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
    ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
      e₀ (Additive.ofMul x)
  exact h

/-- **Peterfalvi (9.7.b), the base-point normalized field model.**  The book takes for `φ` the
additive isomorphism `H̄ ≃+ F` determined by `h = s·φ(h)` for a chosen `s ∈ W̄₂^#`, so that
`φ(s) = 1`.  That normalization is what collapses the twist identity: substituting `h = s` into
`(φ(h)ψ(x))η(w) = (φ(h)η(w))ψ(w⁻¹xw)` yields `ψ(x)η(w) = ψ(w⁻¹xw)`, whence `η(w)` is
multiplicative against every scalar in `U*`.

The Singer construction of `caseB_exists_galoisField_repr` returns an *unnormalized* `e`;
rescaling by the unit `(e s)⁻¹` fixes that at no cost, since scalars commute past the rescaling
(`exists_normalized_of_scalar_model`).  Any `s ≠ 1` works here — the caller supplies the
`W₁`-fixed one from `W̄₂ = C_{H̄}(W₁)`, which is what makes `s^w = s` available downstream. -/
theorem caseB_exists_galoisField_repr_basePoint [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    {s : ↥data.H ⧸ chief.N} (hs : s ≠ 1) :
    letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
    ∃ (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
      (μ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (GaloisField chief.p data.q)ˣ),
      Function.Injective μ ∧
      (∀ (u : ↥(MonoidHom.range (uActionHom data chief)))
        (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x)) ∧
      e (Additive.ofMul s) = 1 := by
  letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨e, μ, hμinj, hcompat⟩ := caseB_exists_galoisField_repr chars caseB
  have hs0 : e (Additive.ofMul s) ≠ 0 := fun h =>
    hs (by simpa using e.injective (h.trans (map_zero e).symm))
  obtain ⟨e', hcompat', hnorm⟩ :=
    OddOrder.RepresentationTheory.exists_normalized_of_scalar_model
      (act := fun (u : ↥(MonoidHom.range (uActionHom data chief)))
        (x : Additive (↥data.H ⧸ chief.N)) =>
          Additive.ofMul ((MonoidHom.range (uActionHom data chief)).subtype u
            (Additive.toMul x)))
      e (fun u => μ u) (fun u x => hcompat u (Additive.toMul x)) hs0
  exact ⟨e', μ, hμinj, fun u x => hcompat' u (Additive.ofMul x), hnorm⟩

/-- **`U*` generates `F` additively** (Peterfalvi (9.7.b)): "Since `U` acts on `H̄` irreducibly,
`H̄` is a vector space over `F` of dimension 1 and the additive subgroup of `F` generated by
`U*` is `F`."

The abstract half — that the additive closure of a multiplicatively closed set is automatically
stable under that set, so irreducibility leaves it no room to be proper — is
`addSubgroup_closure_eq_top_of_irreducible`.  What this theorem contributes is the **transport**:
`caseB.actsIrreducibly` speaks about subgroups of `H̄`, while the abstract lemma wants `U*`-stable
*additive* subgroups of `F`.  Pulling an additive subgroup `A ≤ F` back along `e` gives a subgroup
`J ≤ H̄` (the group law of `H̄` is `e`-additively the one of `F`), and the compatibility
`e (u · x) = μ u * e x` turns `U*`-stability of `A` into `uActionHom`-invariance of `J`. -/
theorem caseB_addSubgroup_closure_scalarRange_eq_top [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
    (μ : ↥(MonoidHom.range (uActionHom data chief)) →*
      (GaloisField chief.p data.q)ˣ)
    (hcompat : ∀ (u : ↥(MonoidHom.range (uActionHom data chief)))
        (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x)) :
    AddSubgroup.closure
        (Set.range fun u : ↥(MonoidHom.range (uActionHom data chief)) =>
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q)) = ⊤ := by
  haveI := chief.N_normal
  refine OddOrder.RepresentationTheory.addSubgroup_closure_eq_top_of_irreducible
    ⟨1, by simp⟩ ?_ ?_
  · rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    exact ⟨u * u', by simp⟩
  · intro A hA
    -- Pull `A` back along `e`: a subgroup of `H̄`, since `e` carries the group law to `+`.
    let J : Subgroup (↥data.H ⧸ chief.N) :=
      { carrier := {x | e (Additive.ofMul x) ∈ A}
        one_mem' := by
          simp only [Set.mem_setOf_eq]
          rw [show Additive.ofMul (1 : ↥data.H ⧸ chief.N) = 0 from rfl, map_zero]
          exact A.zero_mem
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y from rfl, map_add]
          exact A.add_mem hx hy
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [show Additive.ofMul x⁻¹ = -Additive.ofMul x from rfl, map_neg]
          exact A.neg_mem hx }
    have hJinv : IsAInvariant (uActionHom data chief) J := by
      rw [isAInvariant_iff_smul_mem]
      intro a x hx
      change e (Additive.ofMul (uActionHom data chief a x)) ∈ A
      have hmem : uActionHom data chief a ∈ MonoidHom.range (uActionHom data chief) := ⟨a, rfl⟩
      rw [show (uActionHom data chief a x)
          = (MonoidHom.range (uActionHom data chief)).subtype ⟨_, hmem⟩ x from rfl,
        hcompat ⟨_, hmem⟩ x]
      exact hA _ ⟨_, rfl⟩ _ hx
    rcases caseB.actsIrreducibly J hJinv with hbot | htop
    · left
      refine le_antisymm (fun y hy => ?_) (fun y hy => by
        rw [AddSubgroup.mem_bot] at hy; exact hy ▸ A.zero_mem)
      obtain ⟨z, rfl⟩ := e.surjective y
      have hzJ : Additive.toMul z ∈ J := hy
      rw [hbot] at hzJ
      rw [AddSubgroup.mem_bot, show z = 0 from Subgroup.mem_bot.mp hzJ, map_zero]
    · right
      refine le_antisymm le_top (fun y _ => ?_)
      obtain ⟨z, rfl⟩ := e.surjective y
      exact (htop ▸ (Subgroup.mem_top (Additive.toMul z)) : Additive.toMul z ∈ J)

/-- **The `W₁`-action on the chief factor `H̄`** — the `W₁` analogue of `uActionHom`
(`ChiefFactorCore.lean`), both being restrictions of the full `UW₁`-action
`quotientMulAutHom chief.N_aInvariant` to a factor of `U ⊔ W₁`. -/
noncomputable def w1ActionHom {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →*
      MulAut (↥data.H ⧸ chief.N) :=
  (quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype

/-- **The map `η` of Peterfalvi (9.7.b)**: the `W₁`-action on `H̄` transported to the field model
by `e`, i.e. `η(w)` is the `e`-conjugate of `w`'s action — the book's defining property
`φ(h)η(w) = φ(h^w)`.

A priori `η(w)` is only an *additive* automorphism of `F`; the upgrade to a field automorphism is
the content of (9.7.b) and goes through `ringAutHomOfAddAutHom`.  `AddAut F` is an additive group
in mathlib, so the codomain is its multiplicative incarnation `Multiplicative (AddAut F)`. -/
noncomputable def caseB_etaHom {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q) :
    ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →*
      Multiplicative (AddAut (GaloisField chief.p data.q)) :=
  (((MulAutMultiplicative (GaloisField chief.p data.q)).toMonoidHom).comp
      (MulAut.congr (AddEquiv.toMultiplicativeRight e)).toMonoidHom).comp
    (w1ActionHom data chief)

/-- `η(w)` is literally `e`-conjugation of `w`'s action (definitional form). -/
theorem caseB_etaHom_apply' {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
    (w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    (y : GaloisField chief.p data.q) :
    Multiplicative.toAdd (caseB_etaHom (chief := chief) e w) y
      = e (Additive.ofMul (w1ActionHom data chief w (Additive.toMul (e.symm y)))) := rfl

/-- **The defining property of `η`** (Peterfalvi (9.7.b): `φ(h)η(w) = φ(h^w)`). -/
@[simp] theorem caseB_etaHom_apply {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
    (w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    (h : ↥data.H ⧸ chief.N) :
    Multiplicative.toAdd (caseB_etaHom (chief := chief) e w) (e (Additive.ofMul h))
      = e (Additive.ofMul (w1ActionHom data chief w h)) := by
  rw [caseB_etaHom_apply', e.symm_apply_apply]
  rfl

/-- The realized subgroup `C = C_U(H̄)` being trivial makes `uActionHom` injective. -/
theorem uActionHom_injective_of_cSub_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hC : cSub data chief = ⊥) : Function.Injective (uActionHom data chief) := by
  apply (uActionHom data chief).ker_eq_bot_iff.mp
  have hmap : ((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
      (data.typeP.U ⊔ data.typeP.W1).subtype = ⊥ := hC
  rwa [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _),
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hmap

/-- **Peterfalvi (9.7.b), original-`U` field model.**  If `C_U(H̄) = 1`, transport the faithful
image model along `U.subgroupOf (U ⊔ W₁) ≃ U`.  This is the form used by the §14 `S`-side after
the §13 conclusion `C = 1`. -/
theorem caseB_exists_galoisField_repr_of_cSub_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hC : cSub data chief = ⊥) :
    letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
    ∃ (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
      (μ : ↥data.typeP.U →* (GaloisField chief.p data.q)ˣ),
      Function.Injective μ ∧
      ∀ (u : ↥data.typeP.U) (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul
          (uActionHom data chief
            ((Subgroup.subgroupOfEquivOfLe
              (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).symm u) x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x) := by
  letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨e, μbar, hμbar, hcompat⟩ := caseB_exists_galoisField_repr chars caseB
  let eU := Subgroup.subgroupOfEquivOfLe
    (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)
  let toRange : ↥data.typeP.U →*
      ↥(MonoidHom.range (uActionHom data chief)) :=
    (uActionHom data chief).rangeRestrict.comp eU.symm.toMonoidHom
  let μ : ↥data.typeP.U →* (GaloisField chief.p data.q)ˣ := μbar.comp toRange
  have htoRange : Function.Injective toRange := by
    intro a b hab
    apply eU.symm.injective
    apply uActionHom_injective_of_cSub_eq_bot hC
    exact congrArg Subtype.val hab
  refine ⟨e, μ, hμbar.comp htoRange, ?_⟩
  intro u x
  have h := hcompat (toRange u) x
  change e (Additive.ofMul (uActionHom data chief (eU.symm u) x)) =
    ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
      e (Additive.ofMul x) at h
  simpa only [eU] using h

end OddOrder.Peterfalvi.S11
