/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group

/-!
# Holomorph `Hol(G) = G ⋊ Aut(G)`

`Aut(G)` の `G` への自然な作用による半直積。mathlib には無いので導入する
(issue 9214 で claim)。

## 主結果

* `Holomorph G` — `SemidirectProduct G (MulAut G) (MonoidHom.id (MulAut G))`。
* `Holomorph.normal_range_inl` — `G` の像 `inl.range` は `Hol(G)` で正規
  (`rightHom` のカーネルだから)。
* `Holomorph.conj_inl` — `inr σ` による共役は `σ` の作用そのもの。
* `Holomorph.normal_iff_characteristic` ⭐ — `inl.range` に含まれる部分群 `K` が
  `Hol(G)` で正規 ⟺ `K.comap inl` が `G` で **characteristic**。

## 使いどころ

Isaacs Problem 9A.8 (書籍 p. 277, characteristically simple な有限群は同型な単純群の
直積) の書籍 hint が「`G ⋊ Aut(G)` を考えよ」。`inl.range` が `Hol(G)` の極小正規部分群に
なるので Lemma 9.6 を当てると「abelian か semisimple」の二分が得られる。

## 実装ノート

`Hol(G)` の中での共役は `SemidirectProduct.inl_aut`:
`inl (φ σ x) = inr σ * inl x * inr σ⁻¹`。ここで `φ = MonoidHom.id (MulAut G)` なので
`φ σ = σ`, すなわち **`inr σ` による共役がそのまま `σ` の作用**になる。これが
「`Hol(G)`-normal ⟺ characteristic」の中身で, 一般の元 `y = inl a * inr σ` による共役は
`y (inl x) y⁻¹ = inl (a · σ(x) · a⁻¹)` と分解する (`Aut` 部分が characteristic 性,
`G` 部分が normal 性に対応)。
-/

namespace OddOrder.GroupTheory

open Subgroup SemidirectProduct

variable (G : Type*) [Group G]

/-- **Holomorph** `Hol(G) = G ⋊ Aut(G)` (`Aut(G)` は `G` に自然に作用する)。 -/
abbrev Holomorph : Type _ := SemidirectProduct G (MulAut G) (MonoidHom.id (MulAut G))

namespace Holomorph

variable {G}

/-- `G` の像は `Hol(G)` で正規 (`rightHom : Hol(G) →* Aut(G)` のカーネル)。 -/
instance normal_range_inl : ((inl : G →* Holomorph G)).range.Normal := by
  rw [range_inl_eq_ker_rightHom]
  infer_instance

/-- `inr σ` による共役は `σ` の作用そのもの (`φ = id` だから)。 -/
theorem conj_inl (σ : MulAut G) (x : G) :
    (inr σ : Holomorph G) * inl x * (inr σ)⁻¹ = inl (σ x) := by
  rw [← map_inv]
  exact (inl_aut (φ := MonoidHom.id (MulAut G)) σ x).symm

/-- 一般の元 `y ∈ Hol(G)` による `inl x` の共役: `y (inl x) y⁻¹ = inl (a σ(x) a⁻¹)`
(`a = y.left`, `σ = y.right`)。 -/
theorem conj_inl_general (y : Holomorph G) (x : G) :
    y * inl x * y⁻¹ = inl (y.left * (y.right x) * y.left⁻¹) := by
  conv_lhs => rw [← inl_left_mul_inr_right y]
  calc (inl y.left * inr y.right : Holomorph G) * inl x * (inl y.left * inr y.right)⁻¹
      = inl y.left * ((inr y.right) * inl x * (inr y.right)⁻¹) * (inl y.left)⁻¹ := by group
    _ = inl y.left * inl (y.right x) * (inl y.left)⁻¹ := by rw [conj_inl]
    _ = inl (y.left * (y.right x) * y.left⁻¹) := by simp

/-- **核心の対応** ⭐: `inl.range` に含まれる部分群が `Hol(G)` で正規 ⟺ 対応する `G` の
部分群が characteristic。 -/
theorem normal_iff_characteristic {K : Subgroup (Holomorph G)}
    (hK : K ≤ (inl : G →* Holomorph G).range) :
    K.Normal ↔ (K.comap (inl : G →* Holomorph G)).Characteristic := by
  constructor
  · intro hnormal
    rw [Subgroup.characteristic_iff_map_le]
    rintro σ _ ⟨x, hx, rfl⟩
    have hmem : (inl x : Holomorph G) ∈ K := hx
    have := hnormal.conj_mem _ hmem (inr σ)
    rwa [conj_inl] at this
  · intro hchar
    have := hchar
    have : (K.comap (inl : G →* Holomorph G)).Normal := inferInstance
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨x, rfl⟩ := hK hn
    have hxK : x ∈ K.comap (inl : G →* Holomorph G) := hn
    have hσ : y.right x ∈ K.comap (inl : G →* Holomorph G) :=
      Subgroup.characteristic_iff_map_le.mp hchar y.right ⟨x, hxK, rfl⟩
    have hconj : y.left * (y.right x) * y.left⁻¹ ∈ K.comap (inl : G →* Holomorph G) :=
      ‹(K.comap (inl : G →* Holomorph G)).Normal›.conj_mem _ hσ y.left
    rw [conj_inl_general]
    exact hconj

instance [Finite G] : Finite (Holomorph G) :=
  Finite.of_equiv (G × MulAut G) (equivProd (φ := MonoidHom.id (MulAut G))).symm

theorem range_inl_ne_bot [Nontrivial G] : ((inl : G →* Holomorph G)).range ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  intro hbot
  have hmem : (inl x : Holomorph G) ∈ ((inl : G →* Holomorph G)).range := ⟨x, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx (by simpa using congrArg SemidirectProduct.left hmem)

end Holomorph

/-- **Characteristically simple** (Isaacs p. 277): 非自明で, characteristic 部分群が
`1` と `G` だけ。 -/
def IsCharacteristicallySimple : Prop :=
  Nontrivial G ∧ ∀ K : Subgroup G, K.Characteristic → K = ⊥ ∨ K = ⊤

namespace Holomorph

variable {G}

/-- **`G` が characteristically simple なら `inl.range` は `Hol(G)` の極小正規部分群**
(の minimality 部分): `inl.range` に含まれる `Hol(G)`-正規部分群は `⊥` か `inl.range`。 -/
theorem eq_bot_or_eq_range_inl_of_normal (h : IsCharacteristicallySimple G)
    {K : Subgroup (Holomorph G)} (hnormal : K.Normal)
    (hle : K ≤ ((inl : G →* Holomorph G)).range) :
    K = ⊥ ∨ K = ((inl : G →* Holomorph G)).range := by
  have hK : K = (K.comap (inl : G →* Holomorph G)).map (inl : G →* Holomorph G) :=
    (Subgroup.map_comap_eq_self hle).symm
  rcases h.2 _ ((normal_iff_characteristic hle).mp hnormal) with hbot | htop
  · left
    rw [hK, hbot, Subgroup.map_bot]
  · right
    rw [hK, htop, ← MonoidHom.range_eq_map]

end Holomorph

end OddOrder.GroupTheory
