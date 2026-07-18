/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# Heredity of "`X/F(X)` is nilpotent" for subgroups and quotients

For a finite group `X` the condition that `X/F(X)` be nilpotent — equivalently, that `X`
have Fitting length at most two — passes to subgroups and to quotients.  Both directions
are proved here from a single criterion:

* `isNilpotent_quotient_fitting_of_isNilpotent_quotient` — if *some* normal nilpotent
  `K ⊴ X` has `X/K` nilpotent, then `X/F(X)` is nilpotent.  Indeed `K ≤ F(X)` by
  maximality of the Fitting subgroup (`Isaacs.Ch01.nilpotent_normal_le_fitting`), so
  `X/F(X)` is a quotient of `X/K` by Noether's third isomorphism theorem.

The two heredity statements are then obtained by exhibiting the right `K`:

* `isNilpotent_quotient_fitting_of_injective` (**subgroup heredity**) — for an injective
  `f : Y →* X`, take `K = ker (Y → X → X/F(X)) = f⁻¹(F(X))`.  It is nilpotent because `f`
  maps it into the nilpotent group `F(X)`, and `Y/K` embeds into `X/F(X)` by Noether's
  first isomorphism theorem.  (Textbook form: `Y ≤ X` with `Y/(F(X) ⊓ Y) ≅ YF(X)/F(X)`.)
* `isNilpotent_quotient_fitting_of_surjective` (**quotient heredity**) — for a surjective
  `f : X →* Y`, take `K = f(F(X))`.  It is nilpotent as an image of `F(X)`, and `Y/K` is a
  quotient of `X/F(X)`.

Three convenient shapes are stated as corollaries:
`isNilpotent_quotient_fitting_subgroup` (`H : Subgroup X`),
`isNilpotent_quotient_fitting_of_le` (`H ≤ K`, both subgroups of a common ambient group),
and `isNilpotent_quotient_fitting_quotient` (`N ⊴ X`).  Transport along an isomorphism
`e : Y ≃* X` is `isNilpotent_quotient_fitting_of_injective e.toMonoidHom e.injective`.

⚠ **The corollaries alone do not discharge BG Theorem 6.4's transports.**  Of the four the
induction performs, only `G₀ ⊓ S ≤ G₀` is a direct `_of_le` hit; the other three are
isomorphism-mediated and need `_of_injective`/`_of_surjective` together with a hom the *consumer*
must supply.  In particular the subgroup-side hypothesis "`(↥S ⧸ G₀.subgroupOf S)/F(…)` is
nilpotent" needs an **injective** hom `↥S ⧸ G₀.subgroupOf S →* G ⧸ G₀`.  Mathlib has the map
(`QuotientGroup.quotientMapSubgroupOfOfLe`) but **no injectivity lemma for it**, so that kernel
computation is a genuine remaining step — see issue 3026.

Note that `Isaacs.Ch01.fitting` is the subtype-level Fitting subgroup, so `F(Y)` for a
subgroup `Y` of `X` is `Isaacs.Ch01.fitting ↥Y`.  This is *not* the ambient-group
construction `fittingInAmbient` used in BG §15.

## Consumers

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_, Theorem 6.4 (p. 50): its
induction on `|G| + |H|` carries the hypotheses "`G₀/F(G₀)` and `(G/G₀)/F(G/G₀)` are
nilpotent" both to a subgroup (`L ⊔ H ≤ G`) and to a quotient (`G ⧸ N` for a minimal
normal `N`), which is exactly the pair of facts proved here.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {X Y : Type*} [Group X] [Group Y]

/-- **Fitting length two criterion.**  If `K` is a normal nilpotent subgroup of a finite
group `X` with `X/K` nilpotent, then `X/F(X)` is nilpotent.

By maximality of the Fitting subgroup (Isaacs Cor 1.28(b)) we have `K ≤ F(X)`, so
Noether's third isomorphism theorem presents `X/F(X)` as the quotient
`(X/K)/(F(X)/K)` of the nilpotent group `X/K`. -/
theorem isNilpotent_quotient_fitting_of_isNilpotent_quotient [Finite X] (K : Subgroup X)
    [K.Normal] [Group.IsNilpotent K] (h : Group.IsNilpotent (X ⧸ K)) :
    Group.IsNilpotent (X ⧸ Ch01.fitting X) := by
  haveI := h
  exact Group.nilpotent_of_mulEquiv
    (QuotientGroup.quotientQuotientEquivQuotient K (Ch01.fitting X)
      Ch01.nilpotent_normal_le_fitting)

/-- **Subgroup heredity of a nilpotent Fitting quotient.**  If `X` is finite with `X/F(X)`
nilpotent and `f : Y →* X` is injective, then `Y/F(Y)` is nilpotent.

Take `K := ker ((X → X/F(X)) ∘ f) = f⁻¹(F(X))`.  Its image `f(K) ≤ F(X)` is nilpotent and
`f` is injective, so `K` is nilpotent; and `Y/K ≅ range` inside the nilpotent `X/F(X)`, so
`Y/K` is nilpotent.  Now apply
`isNilpotent_quotient_fitting_of_isNilpotent_quotient`. -/
theorem isNilpotent_quotient_fitting_of_injective [Finite X] (f : Y →* X)
    (hf : Function.Injective f) (h : Group.IsNilpotent (X ⧸ Ch01.fitting X)) :
    Group.IsNilpotent (Y ⧸ Ch01.fitting Y) := by
  haveI : Finite Y := Finite.of_injective f hf
  haveI := h
  haveI : Group.IsNilpotent ↥(Ch01.fitting X) := Ch01.fitting.isNilpotent
  obtain ⟨φ, hφ⟩ :
      ∃ φ : Y →* X ⧸ Ch01.fitting X, φ = (QuotientGroup.mk' (Ch01.fitting X)).comp f :=
    ⟨_, rfl⟩
  have hker : φ.ker = (Ch01.fitting X).comap f := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hmap : (φ.ker).map f ≤ Ch01.fitting X := by
    rw [hker]
    exact Subgroup.map_comap_le _ _
  haveI : Group.IsNilpotent ↥((φ.ker).map f) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hmap)
  haveI : Group.IsNilpotent ↥φ.ker :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective φ.ker f hf).symm
  have hquot : Group.IsNilpotent (Y ⧸ φ.ker) :=
    Group.nilpotent_of_mulEquiv (QuotientGroup.quotientKerEquivRange φ).symm
  exact isNilpotent_quotient_fitting_of_isNilpotent_quotient φ.ker hquot

/-- **Quotient heredity of a nilpotent Fitting quotient.**  If `X` is finite with `X/F(X)`
nilpotent and `f : X →* Y` is surjective, then `Y/F(Y)` is nilpotent.

Take `K := f(F(X))`.  It is normal (image of a normal subgroup under a surjection) and
nilpotent (image of the nilpotent `F(X)`), and `Y/K` is a quotient of `X/F(X)` since
`X → Y → Y/K` is surjective and kills `F(X)`.  Now apply
`isNilpotent_quotient_fitting_of_isNilpotent_quotient`. -/
theorem isNilpotent_quotient_fitting_of_surjective [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) (h : Group.IsNilpotent (X ⧸ Ch01.fitting X)) :
    Group.IsNilpotent (Y ⧸ Ch01.fitting Y) := by
  haveI : Finite Y := Finite.of_surjective f hf
  haveI := h
  haveI : Group.IsNilpotent ↥(Ch01.fitting X) := Ch01.fitting.isNilpotent
  haveI : ((Ch01.fitting X).map f).Normal := (Ch01.fitting.normal X).map f hf
  haveI : Group.IsNilpotent ↥((Ch01.fitting X).map f) :=
    Group.nilpotent_of_surjective (f.subgroupMap (Ch01.fitting X))
      (MonoidHom.subgroupMap_surjective f _)
  have hle : Ch01.fitting X ≤
      ((QuotientGroup.mk' ((Ch01.fitting X).map f)).comp f).ker := by
    intro x hx
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_of_mem f hx
  have hsurj : Function.Surjective (QuotientGroup.lift (Ch01.fitting X)
      ((QuotientGroup.mk' ((Ch01.fitting X).map f)).comp f) hle) := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := hf y'
    exact ⟨(x : X ⧸ Ch01.fitting X), by simp⟩
  have hquot : Group.IsNilpotent (Y ⧸ (Ch01.fitting X).map f) :=
    Group.nilpotent_of_surjective _ hsurj
  exact isNilpotent_quotient_fitting_of_isNilpotent_quotient ((Ch01.fitting X).map f) hquot

/-- Subgroup heredity in the shape `H : Subgroup X`: if `X/F(X)` is nilpotent then so is
`H/F(H)`. -/
theorem isNilpotent_quotient_fitting_subgroup [Finite X] (H : Subgroup X)
    (h : Group.IsNilpotent (X ⧸ Ch01.fitting X)) :
    Group.IsNilpotent (↥H ⧸ Ch01.fitting ↥H) :=
  isNilpotent_quotient_fitting_of_injective H.subtype H.subtype_injective h

/-- Subgroup heredity for two subgroups of a common ambient group: if `H ≤ K` and
`K/F(K)` is nilpotent, then `H/F(H)` is nilpotent. -/
theorem isNilpotent_quotient_fitting_of_le {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hle : H ≤ K)
    (h : Group.IsNilpotent (↥K ⧸ Ch01.fitting ↥K)) :
    Group.IsNilpotent (↥H ⧸ Ch01.fitting ↥H) :=
  isNilpotent_quotient_fitting_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle) h

/-- Quotient heredity in the shape `N ⊴ X`: if `X/F(X)` is nilpotent then so is
`(X/N)/F(X/N)`. -/
theorem isNilpotent_quotient_fitting_quotient [Finite X] (N : Subgroup X) [N.Normal]
    (h : Group.IsNilpotent (X ⧸ Ch01.fitting X)) :
    Group.IsNilpotent ((X ⧸ N) ⧸ Ch01.fitting (X ⧸ N)) :=
  isNilpotent_quotient_fitting_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) h

end OddOrder.GroupTheory
