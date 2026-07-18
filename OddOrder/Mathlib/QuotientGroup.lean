/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Injectivity of the maps induced on subgroup quotients

Mathlib defines `QuotientGroup.quotientMapSubgroupOfOfLe`, the map
`A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B` induced by inclusions `A' ≤ B'` and `A ≤ B`,
but proves nothing about its kernel.  This file supplies the missing kernel computation and
the resulting injectivity criterion.

## Main results

* `QuotientGroup.ker_quotientMapSubgroupOfOfLe` — the kernel is the image of `B'.subgroupOf A`
  in `A ⧸ A'.subgroupOf A`.  (Elementwise: a coset `a (A' ⊓ A)` dies exactly when `a ∈ B'`.)
* `QuotientGroup.quotientMapSubgroupOfOfLe_injective_iff` — the map is injective **iff**
  `A ⊓ B' ≤ A'`.  Given `h' : A' ≤ B'` this says `A ⊓ A' = A ⊓ B'`, i.e. `A'` is already the
  full trace of `B'` on `A`; nothing of `B'` is picked up when passing from `A'` to `B'`
  inside `A`.  In particular the criterion always holds when `A' = B'`.
* `QuotientGroup.map_subgroupOf_subtype_injective` — the concrete consequence used
  downstream: for `S N : Subgroup G` with `N ⊴ G`, the map
  `↥S ⧸ N.subgroupOf S →* G ⧸ N` induced by `S.subtype` is injective.  This is the
  second isomorphism theorem read as an embedding `S/(S ⊓ N) ↪ G/N`; mathlib's
  `QuotientGroup.quotientInfEquivProdNormalQuotient` gives the isomorphism onto `SN/N`
  but not the embedding into `G/N` itself.

Note that the second bullet does *not* subsume the third: `quotientMapSubgroupOfOfLe`
lands in a quotient of a subgroup type `↥B`, so specialising `B := ⊤` would still leave a
transport across `↥(⊤ : Subgroup G) ≃* G` to perform.  The third statement is therefore
proved directly from `QuotientGroup.map`, whose kernel here is *definitionally*
`N.subgroupOf S`.

## Consumers

`OddOrder.GroupTheory.FittingHeredity.isNilpotent_quotient_fitting_quotient_subgroupOf`, and
through it the induction of Bender–Glauberman Theorem 6.4 (see issue 3026), which must carry
the hypothesis "`(G/G₀)/F(G/G₀)` is nilpotent" from `G` to a subgroup `S ≤ G`.
-/

namespace QuotientGroup

variable {G : Type*} [Group G]

/-- The kernel of `QuotientGroup.quotientMapSubgroupOfOfLe h' h` is the image of
`B'.subgroupOf A` under the projection `A → A ⧸ A'.subgroupOf A`.

Elementwise, the coset of `a : A` dies in `B ⧸ B'.subgroupOf B` exactly when `(a : G) ∈ B'`. -/
@[to_additive /-- The kernel of `QuotientAddGroup.quotientMapAddSubgroupOfOfLe h' h` is the
image of `B'.addSubgroupOf A` under the projection `A → A ⧸ A'.addSubgroupOf A`. -/]
theorem ker_quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G}
    [(A'.subgroupOf A).Normal] [(B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
    (quotientMapSubgroupOfOfLe h' h).ker
      = (B'.subgroupOf A).map (QuotientGroup.mk' (A'.subgroupOf A)) := by
  -- `quotientMapSubgroupOfOfLe` is by definition `QuotientGroup.map` along `Subgroup.inclusion`,
  -- so `QuotientGroup.ker_map` applies; it remains to identify the comap.
  have hcomap : (B'.subgroupOf B).comap (Subgroup.inclusion h) = B'.subgroupOf A := by
    ext a
    simp [Subgroup.mem_subgroupOf]
  calc (quotientMapSubgroupOfOfLe h' h).ker
      = ((B'.subgroupOf B).comap (Subgroup.inclusion h)).map
          (QuotientGroup.mk' (A'.subgroupOf A)) := QuotientGroup.ker_map _ _ _ _
    _ = (B'.subgroupOf A).map (QuotientGroup.mk' (A'.subgroupOf A)) := by rw [hcomap]

/-- **Injectivity criterion for `QuotientGroup.quotientMapSubgroupOfOfLe`.**  The induced map
`A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B` is injective exactly when `A ⊓ B' ≤ A'`.

Since `h' : A' ≤ B'` is part of the data, the condition says `A ⊓ A' = A ⊓ B'`: passing from
`A'` to the larger `B'` collapses nothing extra inside `A`.  It holds trivially when
`A' = B'`. -/
@[to_additive /-- **Injectivity criterion for
`QuotientAddGroup.quotientMapAddSubgroupOfOfLe`.**  The induced map is injective exactly when
`A ⊓ B' ≤ A'`. -/]
theorem quotientMapSubgroupOfOfLe_injective_iff {A' A B' B : Subgroup G}
    [(A'.subgroupOf A).Normal] [(B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
    Function.Injective (quotientMapSubgroupOfOfLe h' h) ↔ A ⊓ B' ≤ A' := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_quotientMapSubgroupOfOfLe, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
  -- The goal is now `B'.subgroupOf A ≤ A'.subgroupOf A ↔ A ⊓ B' ≤ A'`.
  constructor
  · intro hle a ha
    have hmem : (⟨a, ha.1⟩ : ↥A) ∈ A'.subgroupOf A :=
      hle (by rw [Subgroup.mem_subgroupOf]; exact ha.2)
    rwa [Subgroup.mem_subgroupOf] at hmem
  · intro hle x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hle ⟨x.2, hx⟩

/-- The map `A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B` is injective as soon as
`A ⊓ B' ≤ A'`; see `quotientMapSubgroupOfOfLe_injective_iff`. -/
@[to_additive /-- The map `A ⧸ A'.addSubgroupOf A →+ B ⧸ B'.addSubgroupOf B` is injective as
soon as `A ⊓ B' ≤ A'`. -/]
theorem quotientMapSubgroupOfOfLe_injective {A' A B' B : Subgroup G}
    [(A'.subgroupOf A).Normal] [(B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B)
    (hAB : A ⊓ B' ≤ A') : Function.Injective (quotientMapSubgroupOfOfLe h' h) :=
  (quotientMapSubgroupOfOfLe_injective_iff h' h).2 hAB

/-- **The second isomorphism theorem as an embedding.**  For `S N : Subgroup G` with `N ⊴ G`,
the map `↥S ⧸ N.subgroupOf S →* G ⧸ N` induced by `S.subtype` is injective.

Its kernel is by definition `N.comap S.subtype = N.subgroupOf S`, i.e. exactly what has been
quotiented out.  Textbook form: `S/(S ∩ N) ≅ SN/N ≤ G/N`. -/
@[to_additive /-- **The second isomorphism theorem as an embedding.**  For `S N : AddSubgroup G`
with `N` normal, the map `↥S ⧸ N.addSubgroupOf S →+ G ⧸ N` induced by `S.subtype` is
injective. -/]
theorem map_subgroupOf_subtype_injective (S N : Subgroup G) [N.Normal] :
    Function.Injective (QuotientGroup.map (N.subgroupOf S) N S.subtype le_rfl) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
  -- `N.comap S.subtype` *is* `N.subgroupOf S`.
  exact le_rfl

end QuotientGroup

