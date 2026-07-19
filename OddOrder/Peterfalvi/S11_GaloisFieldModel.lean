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
