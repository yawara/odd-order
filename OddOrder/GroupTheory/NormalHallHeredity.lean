/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Index

/-!
# Heredity of the normal Hall condition for subgroups and quotients

A subgroup `K` of `G` is a *Hall subgroup* exactly when its order and its index are coprime,
`Nat.Coprime (Nat.card ↥K) K.index`.  This π-free spelling — as opposed to the π-indexed
`OddOrder.Isaacs.Ch03.IsHallSubgroup` — is the right one whenever the set of primes is not
named, which is the case for the normal Hall subgroup `G₀` appearing in the hypotheses of
Bender–Glauberman Theorem 6.4.  The π-indexed notion implies this one by the existing
`Ch03.IsHallSubgroup.coprime_index`; the converse holds for `π = (Nat.card ↥K).primeFactors`
but is not needed downstream and so is not stated here.

For a **normal** `K` this condition passes to subgroups and to quotients, because in both
cases the order can only shrink through a divisor and the index can only shrink through a
divisor:

* `coprime_card_index_comap_of_injective` — along an injective `f : Y →* G` the order of
  `f⁻¹(K)` divides `|K|` (it embeds into `K`), and its index equals the relative index
  `K.relIndex f.range`, which divides `K.index` because `K` is normal
  (`Subgroup.relIndex_dvd_index_of_normal`).  Textbook form: `[S : K ⊓ S] = [KS : K]`
  divides `[G : K]`.
* `coprime_card_index_map_of_surjective` — along a surjective `f : G →* Y` the order of
  `f(K)` divides `|K|` (`Subgroup.card_map_dvd`) and its index divides `K.index`
  (`Subgroup.index_map_dvd`).  Normality of `K` is not needed for this half.

Both are stated at the level of a group homomorphism rather than for a fixed subgroup or
quotient, so that isomorphism-mediated transports (compose with `e.toMonoidHom`) are covered
as well; this follows the pattern of `OddOrder.GroupTheory.FittingHeredity`.

The two shapes actually consumed downstream are packaged, together with the normality half,
as `normal_coprime_card_index_subgroupOf` (transport to `S : Subgroup G`, using
`K.subgroupOf S = K.comap S.subtype`) and `normal_coprime_card_index_map_mk'` (transport to
`G ⧸ N`).  Note `Subgroup.inf_subgroupOf_right` identifies `(K ⊓ S).subgroupOf S` with
`K.subgroupOf S`, so the first of these is the textbook statement "`K ⊓ S` is a normal Hall
subgroup of `S`".

No finiteness hypothesis is needed: `Nat.card` and `Subgroup.index` return `0` in the
infinite case and all the divisibilities above hold unconditionally.

## Consumers

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Theorem 6.4 (p. 50): the induction on `|G| + |H|` carries the hypothesis "`G₀` is a normal
Hall subgroup of `G`" both to a subgroup (`L ⊔ H ≤ G`) and to a quotient (`G ⧸ N` for a
minimal normal `N`).  The companion Fitting-quotient half of the same transport is
`OddOrder.GroupTheory.FittingHeredity`.
-/

namespace OddOrder.GroupTheory

variable {G Y : Type*} [Group G] [Group Y]

/-- **Subgroup heredity of the Hall condition.**  If `K ⊴ G` has order coprime to its index
and `f : Y →* G` is injective, then `f⁻¹(K)` has order coprime to its index in `Y`.

The order of `K.comap f` divides `|K|` because `f` embeds it into `K`, and its index is the
relative index `K.relIndex f.range` (`Subgroup.index_comap`), which divides `K.index` since
`K` is normal (`Subgroup.relIndex_dvd_index_of_normal`).  In textbook form, for `S ≤ G` this
is `[S : K ⊓ S] = [KS : K]`, a divisor of `[G : K]`. -/
theorem coprime_card_index_comap_of_injective {K : Subgroup G} [K.Normal]
    (hK : Nat.Coprime (Nat.card ↥K) K.index) (f : Y →* G) (hf : Function.Injective f) :
    Nat.Coprime (Nat.card ↥(K.comap f)) (K.comap f).index := by
  have hcard : Nat.card ↥(K.comap f) ∣ Nat.card ↥K :=
    calc Nat.card ↥(K.comap f)
        = Nat.card ↥((K.comap f).map f) :=
          Nat.card_congr (Subgroup.equivMapOfInjective _ f hf).toEquiv
      _ ∣ Nat.card ↥K := Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
  have hindex : (K.comap f).index ∣ K.index := by
    rw [Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal K f.range
  exact (hK.coprime_dvd_left hcard).coprime_dvd_right hindex

/-- **Quotient heredity of the Hall condition.**  If `K ≤ G` has order coprime to its index
and `f : G →* Y` is surjective, then `f(K)` has order coprime to its index in `Y`.

Both halves are plain divisibility: `Subgroup.card_map_dvd` and `Subgroup.index_map_dvd`.
Normality of `K` is not needed here. -/
theorem coprime_card_index_map_of_surjective {K : Subgroup G}
    (hK : Nat.Coprime (Nat.card ↥K) K.index) (f : G →* Y) (hf : Function.Surjective f) :
    Nat.Coprime (Nat.card ↥(K.map f)) (K.map f).index :=
  (hK.coprime_dvd_left (Subgroup.card_map_dvd K f)).coprime_dvd_right (K.index_map_dvd hf)

/-- **Transport of a normal Hall subgroup to a subgroup**, in the shape consumed by the
induction of BG Theorem 6.4: if `K` is a normal Hall subgroup of `G` and `S ≤ G`, then
`K.subgroupOf S` is a normal Hall subgroup of `↥S`.

Since `Subgroup.inf_subgroupOf_right` gives `(K ⊓ S).subgroupOf S = K.subgroupOf S`, this is
the textbook statement "`K ⊓ S` is a normal Hall subgroup of `S`". -/
theorem normal_coprime_card_index_subgroupOf {K : Subgroup G} [K.Normal]
    (hK : Nat.Coprime (Nat.card ↥K) K.index) (S : Subgroup G) :
    (K.subgroupOf S).Normal ∧
      Nat.Coprime (Nat.card ↥(K.subgroupOf S)) (K.subgroupOf S).index :=
  ⟨inferInstance, coprime_card_index_comap_of_injective hK S.subtype S.subtype_injective⟩

/-- **Transport of a normal Hall subgroup to a quotient**, in the shape consumed by the
induction of BG Theorem 6.4: if `K` is a normal Hall subgroup of `G` and `N ⊴ G`, then
`KN/N` is a normal Hall subgroup of `G ⧸ N`. -/
theorem normal_coprime_card_index_map_mk' {K : Subgroup G} (hKnormal : K.Normal)
    (hK : Nat.Coprime (Nat.card ↥K) K.index) (N : Subgroup G) [N.Normal] :
    (K.map (QuotientGroup.mk' N)).Normal ∧
      Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' N)))
        (K.map (QuotientGroup.mk' N)).index :=
  ⟨hKnormal.map _ (QuotientGroup.mk'_surjective N),
    coprime_card_index_map_of_surjective hK _ (QuotientGroup.mk'_surjective N)⟩

end OddOrder.GroupTheory
