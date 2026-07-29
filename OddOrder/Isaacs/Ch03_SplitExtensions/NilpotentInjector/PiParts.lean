/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.HallNilpotent

/-!
# 冪零部分群の `π`-部分

Isaacs Problem 3C.8 (nilpotent injector の共役性) の準備。冪零部分群 `N ≤ G` は
各素数集合 `π` について一意の Hall `π`-部分群を持ち、それは `N` に正規である
(issue 9213 の `IsHallSubgroup.normal_of_isNilpotent`)。3C.8 の証明はこの
「`π`-部分」を素数ごとに動かすので、**`G` の部分群としての `π`-部分**を扱う述語
`IsNilpotentPiPart` を導入する (`↥N` の部分群として扱うと共役の追跡が煩雑になる)。

## Main results

- `IsNilpotentPiPart` — `A` が `N` の Hall `π`-部分であること。
- `exists_isNilpotentPiPart` — 可解なら存在。
- `IsNilpotentPiPart.le_normalizer` — `N` 冪零なら `N ≤ N_G(A)`。
- `IsNilpotentPiPart.unique` — `N` 冪零なら一意。
- `IsNilpotentPiPart.sup_eq` — `π`-部分と `π'`-部分は `N` を生成する。
- `IsNilpotentPiPart.commute` — 両者は元ごとに可換。
- `IsNilpotentPiPart.map_conj` — 共役同変。
- `nilPiPart` — 関数版 (一意性から上限で選ぶ) と `nilPiPart_map_conj`。
- `le_nilPiPart_of_isPiGroup` — `π`-部分は `N` の `π`-部分群をすべて含む。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.8 準備: 冪零部分群の π-部分 -/

variable {G : Type*} [Group G]

/-- **冪零部分群の `π`-部分**: `A ≤ N` が `↥N` の中で `π`-Hall 部分群であること。

`N` が冪零なら一意に定まり (`IsNilpotentPiPart.unique`)、`N` に正規
(`IsNilpotentPiPart.le_normalizer`)。 -/
def IsNilpotentPiPart (N A : Subgroup G) (π : Set ℕ) : Prop :=
  A ≤ N ∧ IsHallSubgroup π (A.subgroupOf N)

theorem IsNilpotentPiPart.le {N A : Subgroup G} {π : Set ℕ} (h : IsNilpotentPiPart N A π) :
    A ≤ N := h.1

/-- `π`-部分は `π`-群。 -/
theorem IsNilpotentPiPart.isPiGroup {N A : Subgroup G} {π : Set ℕ}
    (h : IsNilpotentPiPart N A π) : Subgroup.IsPiGroup π A := by
  intro p hp
  refine h.2.1 p ?_
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv]

/-- `π`-部分の相対指数の素因子は `π` を避ける。 -/
theorem IsNilpotentPiPart.relIndex_no_pi {N A : Subgroup G} {π : Set ℕ}
    (h : IsNilpotentPiPart N A π) : ∀ p ∈ (A.relIndex N).primeFactors, p ∉ π := h.2.2

/-- 位数と相対指数から `π`-部分性を復元する。 -/
theorem isNilpotentPiPart_of_card_of_relIndex {N A : Subgroup G} {π : Set ℕ} (hAN : A ≤ N)
    (hcard : Subgroup.IsPiGroup π A) (hidx : ∀ p ∈ (A.relIndex N).primeFactors, p ∉ π) :
    IsNilpotentPiPart N A π := by
  refine ⟨hAN, ?_, hidx⟩
  intro p hp
  refine hcard p ?_
  rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv]

/-- **存在**: 有限可解群の部分群は任意の `π` について `π`-部分を持つ (`hall_E_exists`)。 -/
theorem exists_isNilpotentPiPart [Finite G] [IsSolvable G] (N : Subgroup G) (π : Set ℕ) :
    ∃ A : Subgroup G, IsNilpotentPiPart N A π := by
  obtain ⟨L, hL⟩ := hall_E_exists (G := ↥N) π
  refine ⟨L.map N.subtype, Subgroup.map_subtype_le L, ?_⟩
  rwa [show (L.map N.subtype).subgroupOf N = L from
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L]

/-- **正規性** (issue 9213): `N` が冪零なら `π`-部分は `N` に正規。 -/
theorem IsNilpotentPiPart.le_normalizer [Finite G] {N A : Subgroup G} {π : Set ℕ}
    (hN : Group.IsNilpotent ↥N) (h : IsNilpotentPiPart N A π) :
    N ≤ Subgroup.normalizer (A : Set G) := by
  haveI := hN
  haveI : (A.subgroupOf N).Normal := h.2.normal_of_isNilpotent
  exact Subgroup.le_normalizer_of_normal_subgroupOf h.1

/-- **一意性**: `N` が冪零なら `π`-部分は一意。 -/
theorem IsNilpotentPiPart.unique [Finite G] {N A B : Subgroup G} {π : Set ℕ}
    (hN : Group.IsNilpotent ↥N) (hA : IsNilpotentPiPart N A π)
    (hB : IsNilpotentPiPart N B π) : A = B := by
  haveI := hN
  haveI : (A.subgroupOf N).Normal := hA.2.normal_of_isNilpotent
  have hsub : A.subgroupOf N = B.subgroupOf N :=
    IsHallSubgroup.eq_of_normal hA.2 hB.2 inferInstance
  have := congrArg (Subgroup.map N.subtype) hsub
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at this

/-- **分解**: `π`-部分と `π'`-部分は `N` を生成する。 -/
theorem IsNilpotentPiPart.sup_eq [Finite G] {N A B : Subgroup G} {π : Set ℕ}
    (hA : IsNilpotentPiPart N A π) (hB : IsNilpotentPiPart N B πᶜ) : A ⊔ B = N := by
  have htop : A.subgroupOf N ⊔ B.subgroupOf N = ⊤ :=
    sup_eq_top_of_isHallSubgroup_compl hA.2 hB.2
  have hmap := congrArg (Subgroup.map N.subtype) htop
  rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap

/-- **可換性**: `N` が冪零なら `π`-部分と `π'`-部分は元ごとに可換。 -/
theorem IsNilpotentPiPart.commute [Finite G] {N A B : Subgroup G} {π : Set ℕ}
    (hN : Group.IsNilpotent ↥N) (hA : IsNilpotentPiPart N A π)
    (hB : IsNilpotentPiPart N B πᶜ) : ∀ x ∈ A, ∀ y ∈ B, Commute x y := by
  haveI := hN
  intro x hx y hy
  have hcomm := commute_of_isHallSubgroup_of_isHallSubgroup_compl (G := ↥N) hA.2 hB.2
    ⟨x, hA.1 hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hB.1 hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
  have hval : (x : G) * y = y * x := by
    have := congrArg (Subtype.val : ↥N → G) hcomm
    simpa using this
  exact hval

/-- 共役は相対指数を保つ。 -/
theorem relIndex_map_conj [Finite G] {A N : Subgroup G} (hAN : A ≤ N) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).relIndex (N.map (MulAut.conj g).toMonoidHom)
      = A.relIndex N := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ N.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hAN
  have hA : (A.map (MulAut.conj g).toMonoidHom).index = A.index :=
    Subgroup.index_map_equiv A (MulAut.conj g)
  have hN : (N.map (MulAut.conj g).toMonoidHom).index = N.index :=
    Subgroup.index_map_equiv N (MulAut.conj g)
  have h1 := Subgroup.relIndex_mul_index hle
  have h2 := Subgroup.relIndex_mul_index hAN
  rw [hA, hN] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (h1.trans h2.symm)

/-- **共役同変**: `π`-部分の共役は共役の `π`-部分。 -/
theorem IsNilpotentPiPart.map_conj [Finite G] {N A : Subgroup G} {π : Set ℕ}
    (h : IsNilpotentPiPart N A π) (g : G) :
    IsNilpotentPiPart (N.map (MulAut.conj g).toMonoidHom)
      (A.map (MulAut.conj g).toMonoidHom) π := by
  refine isNilpotentPiPart_of_card_of_relIndex (Subgroup.map_mono h.1) ?_ ?_
  · intro p hp
    refine h.isPiGroup p ?_
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hp
  · intro p hp
    refine h.relIndex_no_pi p ?_
    rwa [relIndex_map_conj h.1 g] at hp

/-- 共役部分群の冪零性。 -/
theorem isNilpotent_map_conj {N : Subgroup G} (hN : Group.IsNilpotent ↥N) (g : G) :
    Group.IsNilpotent ↥(N.map (MulAut.conj g).toMonoidHom) :=
  haveI := hN
  Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective N (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)

/-- **冪零部分群の `π`-部分 (関数版)**: 一意性があるので上限で選んでよい。

`N` が冪零 (かつ環境が有限可解) なら `IsNilpotentPiPart N (nilPiPart N π) π`
(`isNilpotentPiPart_nilPiPart`)。素数ごとに `π`-部分を動かす 3C.8 の帰納で、
`π`-部分を**関数として**扱えるようにするための定義。 -/
def nilPiPart (N : Subgroup G) (π : Set ℕ) : Subgroup G :=
  sSup {A : Subgroup G | IsNilpotentPiPart N A π}

theorem nilPiPart_eq [Finite G] {N A : Subgroup G} {π : Set ℕ}
    (hN : Group.IsNilpotent ↥N) (hA : IsNilpotentPiPart N A π) : nilPiPart N π = A := by
  have hset : {B : Subgroup G | IsNilpotentPiPart N B π} = {A} := by
    ext B
    exact ⟨fun hB => IsNilpotentPiPart.unique hN hB hA, fun hB => hB ▸ hA⟩
  rw [nilPiPart, hset, sSup_singleton]

theorem isNilpotentPiPart_nilPiPart [Finite G] [IsSolvable G] {N : Subgroup G} (π : Set ℕ)
    (hN : Group.IsNilpotent ↥N) : IsNilpotentPiPart N (nilPiPart N π) π := by
  obtain ⟨A, hA⟩ := exists_isNilpotentPiPart N π
  rw [nilPiPart_eq hN hA]
  exact hA

/-- **極大性**: `N` 冪零で `A ≤ N` が `π`-群なら `A ≤ nilPiPart N π`。

`N` の `π`-部分は `↥N` の中で正規 Hall `π`-部分群なので、`π`-部分群をすべて含む
(`isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer`)。 -/
theorem le_nilPiPart_of_isPiGroup [Finite G] [IsSolvable G] {N A : Subgroup G} {π : Set ℕ}
    (hN : Group.IsNilpotent ↥N) (hAN : A ≤ N) (hA : Subgroup.IsPiGroup π A) :
    A ≤ nilPiPart N π := by
  have hpart := isNilpotentPiPart_nilPiPart (N := N) π hN
  haveI : ((nilPiPart N π).subgroupOf N).Normal := hpart.2.normal_of_isNilpotent
  have hsub : A.subgroupOf N ≤ (nilPiPart N π).subgroupOf N := by
    refine isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer hpart.2
      (Subgroup.IsPiGroup.subgroupOf hAN hA) ?_
    rw [Subgroup.normalizer_eq_top (H := (nilPiPart N π).subgroupOf N)]
    exact le_top
  intro x hx
  exact (Subgroup.mem_subgroupOf (H := nilPiPart N π) (K := N) (h := ⟨x, hAN hx⟩)).mp
    (hsub (Subgroup.mem_subgroupOf.mpr hx))

/-- `π`-部分は共役同変 (関数版)。 -/
theorem nilPiPart_map_conj [Finite G] [IsSolvable G] {N : Subgroup G} (π : Set ℕ)
    (hN : Group.IsNilpotent ↥N) (g : G) :
    nilPiPart (N.map (MulAut.conj g).toMonoidHom) π
      = (nilPiPart N π).map (MulAut.conj g).toMonoidHom :=
  nilPiPart_eq (isNilpotent_map_conj hN g) ((isNilpotentPiPart_nilPiPart π hN).map_conj g)

end -- 3C.8 準備

end OddOrder.Isaacs.Ch03
