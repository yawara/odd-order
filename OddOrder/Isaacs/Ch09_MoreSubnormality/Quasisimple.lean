/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Isaacs Ch. 9 — §9A: quasisimple groups (pp. 271-273)

Isaacs, *Finite Group Theory* (AMS GSM 92), Ch. 9 "More on Subnormality" 冒頭.
Bender の generalized Fitting subgroup `F*(G)` に向けた quasisimple 群の基礎:

- `IsQuasisimple`: `G` が **quasisimple** ⟺ `G` が perfect かつ `G/Z(G)` が simple
  (書籍 p. 272 の定義そのまま; `G/Z(G)` は自動的に nonabelian simple になる).
- **Lemma 9.1** (`not_isMulCommutative_of_isSimpleGroup_quotient_center`,
  `isQuasisimple_commutator`, `commutatorQuotientCenterEquiv`): `G/Z(G)` が simple なら
  `G/Z(G)` は nonabelian, `G'` は perfect (よって quasisimple), かつ `G'/Z(G') ≅ G/Z(G)`.
- **Lemma 9.2** (`IsQuasisimple.normal_le_center` / `IsQuasisimple.quotient`):
  quasisimple `G` の proper normal subgroup は central, nonidentity 商は quasisimple.

有限性は仮定しない (Isaacs は有限群の本だが §9A のこの部分は一般に成立する).
component / layer / `F*(G)` は後続 leaf (`Components.lean` 以降) で扱う.

## 実装ノート

書籍の Lemma 9.1 は `G'''` の非自明性経由で `G'' = G'` を出すが、ここでは商
`G/Z(G)` 側で完結する短い route を採る: `Z := Z(G)` への射影 `π` で
`π(G') = commutator (G/Z) = ⊤` (simple nonabelian なので全体), よって
`π(⁅G',G'⁆) = ⁅⊤,⊤⁆ = ⊤`, すなわち `⁅G',G'⁆ ⊔ Z = ⊤`. 一般補題
`commutator_le_of_sup_center_eq_top` (「normal `N` が `N ⊔ Z(G) = ⊤` を満たせば
`G' ≤ N`」= 「中心的補部分をもつ商は可換」) を `N := ⁅G',G'⁆` に適用して
`G' ≤ ⁅G',G'⁆` を得る. 同じ一般補題が Lemma 9.2(a) も処理する.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped IsMulCommutative commutatorElement Pointwise

/-- **Quasisimple group** (Isaacs p. 272): `G` は perfect かつ `G/Z(G)` が simple.
`G/Z(G)` は自動的に nonabelian になる
(`not_isMulCommutative_of_isSimpleGroup_quotient_center`). -/
structure IsQuasisimple (G : Type*) [Group G] : Prop where
  isPerfect : Group.IsPerfect G
  isSimpleGroup_quotient : IsSimpleGroup (G ⧸ center G)

variable {G : Type*} [Group G]

section /- 9A 補助: 可換性と commutator の一般補題 -/

/-- 可換群からの全射があれば値域も可換. -/
theorem isMulCommutative_of_surjective {H : Type*} [Group H] [IsMulCommutative G]
    (f : G →* H) (hf : Function.Surjective f) : IsMulCommutative H :=
  IsMulCommutative.of_comm fun x y => by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mul_comm' a b]

/-- 中心の像が全体になる準同型があれば、値域の群は可換. Lemma 9.1/9.2 で
「simple 商が中心的部分群の像で覆われる」ケースを矛盾に落とすための一般補題. -/
theorem isMulCommutative_of_map_center_eq_top {H : Type*} [Group H] {f : G →* H}
    (h : (center G).map f = ⊤) : IsMulCommutative H :=
  IsMulCommutative.of_comm fun x y => by
    have hx : x ∈ (center G).map f := h ▸ Subgroup.mem_top x
    have hy : y ∈ (center G).map f := h ▸ Subgroup.mem_top y
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha b]

/-- 全射準同型は中心を中心の中へ写す. -/
theorem map_center_le_center_of_surjective {H : Type*} [Group H] {f : G →* H}
    (hf : Function.Surjective f) : (center G).map f ≤ center H := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro h
  obtain ⟨g, rfl⟩ := hf h
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]

/-- 群同型は中心を中心へ写す. -/
theorem map_center_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  refine le_antisymm (map_center_le_center_of_surjective e.surjective) fun h hh => ?_
  refine ⟨e.symm h, Subgroup.mem_center_iff.mpr fun g => e.injective ?_, e.apply_symm_apply h⟩
  simp only [map_mul, MulEquiv.apply_symm_apply]
  exact Subgroup.mem_center_iff.mp hh (e g)

/-- 可換群の commutator subgroup は自明. -/
theorem commutator_eq_bot_of_isMulCommutative [IsMulCommutative G] :
    commutator G = ⊥ := by
  rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' g₁ g₂))

/-- commutator subgroup が自明なら可換. -/
theorem isMulCommutative_of_commutator_eq_bot (h : commutator G = ⊥) :
    IsMulCommutative G :=
  IsMulCommutative.of_comm fun x y => by
    have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
      rw [← h, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

/-- normal `N` と中心の join が全体なら, `G/N` は可換, すなわち `G' ≤ N`.
(Isaacs 9.1/9.2 で繰り返し使う「中心的補部分をもつ商は可換」の形.) -/
theorem commutator_le_of_sup_center_eq_top {N : Subgroup G} (hN : N.Normal)
    (h : N ⊔ center G = ⊤) : commutator G ≤ N := by
  haveI := hN
  have hcover : (center G).map (QuotientGroup.mk' N) = ⊤ := by
    have hmap := congrArg (Subgroup.map (QuotientGroup.mk' N)) h
    have hNbot : N.map (QuotientGroup.mk' N) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' N).symm.le
    rw [Subgroup.map_sup, hNbot, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
    exact hmap
  haveI : IsMulCommutative (G ⧸ N) := isMulCommutative_of_map_center_eq_top hcover
  have hmapcomm : (commutator G).map (QuotientGroup.mk' N) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← _root_.commutator_def,
      commutator_eq_bot_of_isMulCommutative]
  have hle := (Subgroup.map_eq_bot_iff _).mp hmapcomm
  rwa [QuotientGroup.ker_mk'] at hle

/-- `G/Z(G)` が simple のとき, 中心に含まれない normal subgroup は中心との join が全体.
(`Z(G)` が maximal normal であることの実働形.) -/
theorem normal_sup_center_eq_top (hs : IsSimpleGroup (G ⧸ center G)) {N : Subgroup G}
    (hN : N.Normal) (hnle : ¬N ≤ center G) : N ⊔ center G = ⊤ := by
  haveI := hs
  have hmapne : N.map (QuotientGroup.mk' (center G)) ≠ ⊥ := fun hbot =>
    hnle fun n hn => by
      have hmem : (QuotientGroup.mk' (center G)) n ∈ N.map (QuotientGroup.mk' (center G)) :=
        Subgroup.mem_map_of_mem _ hn
      rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hmem
      exact hmem
  have hnormal : (N.map (QuotientGroup.mk' (center G))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact absurd h hmapne
  · have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' (center G))) h
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap

end

section /- 9A: Lemma 9.1 (p. 272) -/

/-- **Isaacs Lemma 9.1 (第 1 主張)**: `G/Z(G)` が simple なら nonabelian.
(simple abelian だと巡回なので, center 商が巡回 ⇒ `G` 可換 ⇒ 商が自明で矛盾.) -/
theorem not_isMulCommutative_of_isSimpleGroup_quotient_center
    (hs : IsSimpleGroup (G ⧸ center G)) :
    ¬IsMulCommutative (G ⧸ center G) := by
  intro hcomm
  haveI := hs
  haveI := hcomm
  haveI : IsCyclic (G ⧸ center G) := IsSimpleGroup.isCyclic
  haveI : IsMulCommutative G :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' (center G))
      (QuotientGroup.ker_mk' (center G)).le
  have hZ : center G = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun g =>
      Subgroup.mem_center_iff.mpr fun h => mul_comm' h g
  have hone : ∀ q : G ⧸ center G, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) q
    exact (QuotientGroup.eq_one_iff x).mpr (by rw [hZ]; exact Subgroup.mem_top x)
  obtain ⟨q₁, q₂, hne⟩ := exists_pair_ne (G ⧸ center G)
  exact hne ((hone q₁).trans (hone q₂).symm)

/-- nonabelian simple 商は perfect: `commutator (G/Z(G)) = ⊤`. -/
theorem commutator_quotient_center_eq_top (hs : IsSimpleGroup (G ⧸ center G)) :
    commutator (G ⧸ center G) = ⊤ := by
  haveI := hs
  have hnorm : (commutator (G ⧸ center G)).Normal := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_normal ⊤ ⊤
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact absurd (isMulCommutative_of_commutator_eq_bot h)
      (not_isMulCommutative_of_isSimpleGroup_quotient_center hs)
  · exact h

/-- **Isaacs Lemma 9.1 補助**: `G/Z(G)` が simple なら, `G'` の射影は商全体
(nonabelian simple 群はその commutator が全体). -/
theorem map_commutator_eq_top_of_isSimpleGroup_quotient_center
    (hs : IsSimpleGroup (G ⧸ center G)) :
    (commutator G).map (QuotientGroup.mk' (center G)) = ⊤ := by
  rw [_root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← _root_.commutator_def,
    commutator_quotient_center_eq_top hs]

/-- **Isaacs Lemma 9.1 (第 2 主張の核)**: `G/Z(G)` が simple なら `⁅G',G'⁆ = G'`
(`G'` は perfect). -/
theorem commutator_commutator_eq_commutator (hs : IsSimpleGroup (G ⧸ center G)) :
    ⁅commutator G, commutator G⁆ = commutator G := by
  have hmap : Subgroup.map (QuotientGroup.mk' (center G)) ⁅commutator G, commutator G⁆ = ⊤ := by
    rw [Subgroup.map_commutator, map_commutator_eq_top_of_isSimpleGroup_quotient_center hs,
      ← _root_.commutator_def, commutator_quotient_center_eq_top hs]
  have hsup : ⁅commutator G, commutator G⁆ ⊔ center G = ⊤ := by
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' (center G))) hmap
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap
  refine le_antisymm ?_ (commutator_le_of_sup_center_eq_top
    (Subgroup.commutator_normal (commutator G) (commutator G)) hsup)
  exact Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ =>
    Subgroup.commutator_mem_commutator (Subgroup.mem_top g₁) (Subgroup.mem_top g₂)

/-- **Isaacs Lemma 9.1**: `G/Z(G)` が simple なら `G'` は perfect. -/
theorem isPerfect_commutator (hs : IsSimpleGroup (G ⧸ center G)) :
    Group.IsPerfect ↥(commutator G) :=
  Subgroup.isPerfect_iff.mpr (commutator_commutator_eq_commutator hs)

/-- `G/Z(G)` が simple なら `G' ⊔ Z(G) = ⊤` (`G'` は中心の外に出て商全体を覆う). -/
theorem commutator_sup_center_eq_top (hs : IsSimpleGroup (G ⧸ center G)) :
    commutator G ⊔ center G = ⊤ := by
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' (center G)))
    (map_commutator_eq_top_of_isSimpleGroup_quotient_center hs)
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap

/-- 合成 `↥G' →* G ⧸ Z(G)` は全射 (`G' ⊔ Z(G) = ⊤` から). -/
theorem commutator_subtype_comp_mk'_surjective (hs : IsSimpleGroup (G ⧸ center G)) :
    Function.Surjective
      ((QuotientGroup.mk' (center G)).comp (commutator G).subtype) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center G) q
  have hg : (g : G) ∈ ((commutator G : Set G) * (center G : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge)]
    exact_mod_cast (commutator_sup_center_eq_top hs).symm ▸ Subgroup.mem_top g
  obtain ⟨n, hn, z, hz, rfl⟩ := hg
  refine ⟨⟨n, hn⟩, ?_⟩
  have hz1 : QuotientGroup.mk' (center G) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  change QuotientGroup.mk' (center G) n = QuotientGroup.mk' (center G) (n * z)
  rw [map_mul, hz1, mul_one]

/-- **Isaacs Lemma 9.1 補助**: `G/Z(G)` が simple なら `Z(G') = Z(G) ∩ G'`.
(`⊇` は明らか. `⊆` は: `Z(G')` の像は simple 商の normal subgroup で, `⊤` なら商が
可換になって矛盾するから `⊥`.) -/
theorem center_commutator_eq_subgroupOf (hs : IsSimpleGroup (G ⧸ center G)) :
    center ↥(commutator G) = (center G).subgroupOf (commutator G) := by
  haveI := hs
  set ψ : ↥(commutator G) →* G ⧸ center G :=
    (QuotientGroup.mk' (center G)).comp (commutator G).subtype with hψdef
  have hψ : Function.Surjective ψ := commutator_subtype_comp_mk'_surjective hs
  have hker : ψ.ker = (center G).subgroupOf (commutator G) := by
    ext x
    simp [hψdef, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  refine le_antisymm ?_ ?_
  · have hnorm : ((center ↥(commutator G)).map ψ).Normal :=
      Subgroup.Normal.map inferInstance ψ hψ
    rcases hnorm.eq_bot_or_eq_top with h | h
    · have hle := (Subgroup.map_eq_bot_iff _).mp h
      rwa [hker] at hle
    · exact absurd (isMulCommutative_of_map_center_eq_top h)
        (not_isMulCommutative_of_isSimpleGroup_quotient_center hs)
  · intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz w)

/-- **Isaacs Lemma 9.1 (第 3 主張)**: `G/Z(G)` が simple なら `G'/Z(G') ≅ G/Z(G)`. -/
noncomputable def commutatorQuotientCenterEquiv (hs : IsSimpleGroup (G ⧸ center G)) :
    (↥(commutator G) ⧸ center ↥(commutator G)) ≃* (G ⧸ center G) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [center_commutator_eq_subgroupOf hs]
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff])).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (commutator_subtype_comp_mk'_surjective hs))

/-- **Isaacs Lemma 9.1 (総合形)**: `G/Z(G)` が simple なら `G'` は quasisimple. -/
theorem isQuasisimple_commutator (hs : IsSimpleGroup (G ⧸ center G)) :
    IsQuasisimple ↥(commutator G) where
  isPerfect := isPerfect_commutator hs
  isSimpleGroup_quotient := by
    haveI := hs
    exact (commutatorQuotientCenterEquiv hs).isSimpleGroup

end

section /- 9A: Lemma 9.2 (p. 272) と quasisimple の基本 API -/

/-- quasisimple 群は nontrivial. -/
theorem IsQuasisimple.nontrivial (hq : IsQuasisimple G) : Nontrivial G := by
  haveI := hq.isSimpleGroup_quotient
  obtain ⟨q₁, q₂, hne⟩ := exists_pair_ne (G ⧸ center G)
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective (center G) q₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk'_surjective (center G) q₂
  exact ⟨g₁, g₂, fun h => hne (by rw [h])⟩

/-- quasisimple 群の中心は proper. -/
theorem IsQuasisimple.center_ne_top (hq : IsQuasisimple G) : center G ≠ ⊤ := by
  intro h
  haveI := hq.isSimpleGroup_quotient
  have hone : ∀ q : G ⧸ center G, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) q
    exact (QuotientGroup.eq_one_iff x).mpr (by rw [h]; exact Subgroup.mem_top x)
  obtain ⟨q₁, q₂, hne⟩ := exists_pair_ne (G ⧸ center G)
  exact hne ((hone q₁).trans (hone q₂).symm)

/-- quasisimple 群は nonabelian. -/
theorem IsQuasisimple.not_isMulCommutative (hq : IsQuasisimple G) :
    ¬IsMulCommutative G := fun _ =>
  hq.center_ne_top ((Subgroup.eq_top_iff' _).mpr fun g =>
    Subgroup.mem_center_iff.mpr fun h => mul_comm' h g)

/-- **Isaacs Lemma 9.2 (第 1 主張)**: quasisimple 群の proper normal subgroup は central. -/
theorem IsQuasisimple.normal_le_center (hq : IsQuasisimple G) {N : Subgroup G}
    (hN : N.Normal) (hne : N ≠ ⊤) : N ≤ center G := by
  by_contra hnle
  have hsup := normal_sup_center_eq_top hq.isSimpleGroup_quotient hN hnle
  have hle := commutator_le_of_sup_center_eq_top hN hsup
  rw [hq.isPerfect.commutator_eq_top] at hle
  exact hne (top_le_iff.mp hle)

/-- **Isaacs Lemma 9.2 (第 2 主張)**: quasisimple 群の nonidentity 商は quasisimple. -/
theorem IsQuasisimple.quotient (hq : IsQuasisimple G) {N : Subgroup G}
    (hN : N.Normal) (hne : N ≠ ⊤) : IsQuasisimple (G ⧸ N) := by
  haveI := hN
  haveI := hq.isPerfect
  have hNZ : N ≤ center G := hq.normal_le_center hN hne
  haveI hZbar : ((center G).map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  have e := QuotientGroup.quotientQuotientEquivQuotient N (center G) hNZ
  haveI := hq.isSimpleGroup_quotient
  haveI hsimp : IsSimpleGroup ((G ⧸ N) ⧸ (center G).map (QuotientGroup.mk' N)) :=
    e.isSimpleGroup
  refine ⟨inferInstance, ?_⟩
  have hcenter : center (G ⧸ N) = (center G).map (QuotientGroup.mk' N) := by
    refine le_antisymm ?_ (map_center_le_center_of_surjective (QuotientGroup.mk'_surjective N))
    have hnorm2 : ((center (G ⧸ N)).map
        (QuotientGroup.mk' ((center G).map (QuotientGroup.mk' N)))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hnorm2.eq_bot_or_eq_top with h | h
    · have hle := (Subgroup.map_eq_bot_iff _).mp h
      rwa [QuotientGroup.ker_mk'] at hle
    · exfalso
      have hcomm : IsMulCommutative ((G ⧸ N) ⧸ (center G).map (QuotientGroup.mk' N)) :=
        isMulCommutative_of_map_center_eq_top h
      haveI := hcomm
      exact not_isMulCommutative_of_isSimpleGroup_quotient_center hq.isSimpleGroup_quotient
        (isMulCommutative_of_surjective e.toMonoidHom e.surjective)
  exact (QuotientGroup.quotientMulEquivOfEq hcenter).isSimpleGroup

/-- quasisimple 性は群同型で移る. -/
theorem IsQuasisimple.of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (hq : IsQuasisimple G) : IsQuasisimple H := by
  refine ⟨?_, ?_⟩
  · haveI := hq.isPerfect
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · haveI := hq.isSimpleGroup_quotient
    exact ((QuotientGroup.congr (center G) (center H) e (map_center_mulEquiv e)).symm).isSimpleGroup

end

end OddOrder.Isaacs.Ch09
