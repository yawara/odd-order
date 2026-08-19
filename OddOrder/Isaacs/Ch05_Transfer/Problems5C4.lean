/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import OddOrder.GroupTheory.CardSupInf
import OddOrder.GroupTheory.CyclicSubgroupUniqueness
import OddOrder.Isaacs.Ch05_Transfer.Problems5C

/-!
# Isaacs Problem 5C.4 — Z-群の部分群 (p. 163)

**Problem 5C.4**: `G` の Sylow 部分群がすべて巡回 (mathlib の `IsZGroup`) なら,
`|G|` の任意の約数 `m` に対し位数 `m` の部分群が存在し, かつ位数 `m` の部分群は
互いに `G`-共役である。

本ファイルは **存在部分**を扱う。骨格は mathlib の Z-群 API:

* `IsZGroup.isCyclic_commutator` — `G' = commutator G` は巡回
* `IsZGroup.isCyclic_abelianization` — `G/G'` は巡回
* `IsZGroup.coprime_commutator_index` — `gcd(|G'|, |G : G'|) = 1` (つまり `G'` は正規 Hall)

したがって `m ∣ |G|` は `m = m₁ · m₂` (`m₁ ∣ |G'|`, `m₂ ∣ |G : G'|`) と一意分解でき,
巡回群 `G'` の位数 `m₁` の部分群 `M` (正規) と, Schur–Zassenhaus 補群 `H ≅ G/G'` (巡回) の
位数 `m₂` の部分群 `H₂` を取って `K := H₂ ⊔ M` とすればよい。
-/

namespace OddOrder.Isaacs.Ch05

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

section /- 5C.4: Z-群の部分群 (p. 163) -/

/-- 正規部分群 `N` の特性部分群を `G` 側へ押し出したものは `G` で正規。 -/
theorem mem_normalizer_of_normal {M : Subgroup G} [M.Normal] (g : G) :
    g ∈ Subgroup.normalizer ((M : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact (inferInstance : M.Normal).conj_mem _ hy g
  · intro hy
    have h := (inferInstance : M.Normal).conj_mem _ hy g⁻¹
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h

theorem normal_map_subtype_of_characteristic {N : Subgroup G} [N.Normal] {M : Subgroup ↥N}
    [M.Characteristic] : (M.map N.subtype).Normal :=
  ⟨fun _x hx g => conj_mem_map_subtype_of_characteristic (mem_normalizer_of_normal g) hx⟩

/-- Z-群の Schur–Zassenhaus 補群は `G/G'` と同型ゆえ巡回。 -/
theorem isCyclic_of_isComplement'_commutator [Finite G] [IsZGroup G] {H : Subgroup G}
    (hH : Subgroup.IsComplement' (commutator G) H) : IsCyclic ↥H := by
  have : IsCyclic (G ⧸ commutator G) := IsZGroup.isCyclic_abelianization
  set f : ↥H →* G ⧸ commutator G := (QuotientGroup.mk' (commutator G)).comp H.subtype with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk'] at hy
    have hmem : (y : G) ∈ (commutator G : Subgroup G) ⊓ H := ⟨hy, y.2⟩
    rw [hH.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (s := commutator G) q
    obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 g
    refine ⟨h, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype, ← hnh]
    rw [QuotientGroup.eq]
    have hcon := (inferInstance : (commutator G).Normal).conj_mem _ n.2 (h : G)⁻¹
    rwa [show (h : G)⁻¹ * (n : G) * (h : G)⁻¹⁻¹ = (h : G)⁻¹ * ((n : G) * (h : G)) by group]
      at hcon
  exact isCyclic_of_surjective (MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.toMonoidHom
    (MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.surjective

/-- ⭐ **Isaacs Problem 5C.4 (存在)**: `G` の Sylow 部分群がすべて巡回なら, `|G|` の任意の
約数 `m` に対し位数 `m` の部分群が存在する。

**証明**: `N := G'` は巡回な正規 Hall 部分群 (`IsZGroup.coprime_commutator_index`) なので
`m = gcd(m,|N|) · gcd(m,|G:N|)` と分解する (`Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`)。
巡回群 `N` には位数 `m₁ := gcd(m,|N|)` の部分群 `M` が一意に存在し (`cyclic` ゆえ特性,
したがって `G` で正規)、Schur–Zassenhaus 補群 `H ≅ G/N` は巡回なので位数
`m₂ := gcd(m,|G:N|)` の部分群 `H₂` を持つ。`M ⊓ H₂ ≤ N ⊓ H = ⊥` より
`|H₂ ⊔ M| = m₂ · m₁ = m`。 -/
theorem exists_subgroup_card_eq_of_isZGroup [Finite G] [IsZGroup G]
    {m : ℕ} (hm : m ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card ↥K = m := by
  classical
  have : IsCyclic ↥(commutator G) := IsZGroup.isCyclic_commutator G
  have hcop : Nat.Coprime (Nat.card ↥(commutator G)) (commutator G).index :=
    IsZGroup.coprime_commutator_index G
  have hmul : Nat.card ↥(commutator G) * (commutator G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hdec : Nat.gcd m (Nat.card ↥(commutator G)) * Nat.gcd m (commutator G).index = m :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr (by rw [hmul]; exact hm)
  -- `M ≤ G'` : 位数 `m₁`
  obtain ⟨M', hM'⟩ := exists_subgroup_card_eq_of_isCyclic
    (C := ↥(commutator G)) (Nat.gcd_dvd_right m (Nat.card ↥(commutator G)))
  have : M'.Characteristic := characteristic_of_isCyclic M'
  have : (M'.map (commutator G).subtype).Normal := normal_map_subtype_of_characteristic
  have hMcard : Nat.card ↥(M'.map (commutator G).subtype)
      = Nat.gcd m (Nat.card ↥(commutator G)) := by
    rw [← hM']
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective M' _ (Subgroup.subtype_injective _)).toEquiv.symm
  -- `H` : Schur–Zassenhaus 補群 (巡回), その中の位数 `m₂` の部分群 `H₂`
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have : IsCyclic ↥H := isCyclic_of_isComplement'_commutator hH
  have hHcard : Nat.card ↥H = (commutator G).index := by
    have h := hH.card_mul_card
    rw [← hmul] at h
    have hpos : 0 < Nat.card ↥(commutator G) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h
  obtain ⟨H₂', hH₂'⟩ := exists_subgroup_card_eq_of_isCyclic (C := ↥H)
    (d := Nat.gcd m (commutator G).index)
    (by rw [hHcard]; exact Nat.gcd_dvd_right m (commutator G).index)
  have hH₂card : Nat.card ↥(H₂'.map H.subtype) = Nat.gcd m (commutator G).index := by
    rw [← hH₂']
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective H₂' _ (Subgroup.subtype_injective _)).toEquiv.symm
  -- `K := H₂ ⊔ M`
  refine ⟨H₂'.map H.subtype ⊔ M'.map (commutator G).subtype, ?_⟩
  have hdisj : H₂'.map H.subtype ⊓ M'.map (commutator G).subtype = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    have hyH : y ∈ H := Subgroup.map_subtype_le _ hy1
    have hyN : y ∈ commutator G := Subgroup.map_subtype_le _ hy2
    have : y ∈ (commutator G : Subgroup G) ⊓ H := ⟨hyN, hyH⟩
    rwa [hH.disjoint.eq_bot] at this
  rw [card_sup_eq_mul_of_disjoint_normal hdisj, hH₂card, hMcard, mul_comm]
  exact hdec

/-! ### 5C.4 共役性 -/

/-- Z-群では, 部分群 `K` と `G' = commutator G` の交わりの位数は `gcd(|K|, |G'|)`。

`G'` は正規 Hall (`gcd(|G'|, |G:G'|) = 1`) なので `|K|` の `G'`-部分は交わりに全部入る。
第二同型定理 `|K ⊔ G'| · |K ⊓ G'| = |K| · |G'|` から `|K| = f · d`
(`d := |K ⊓ G'|`, `f := |K ⊔ G'| / |G'| ∣ |G:G'|`) を得, `gcd(|K|,|G'|) = d · e` と書くと
`e` は `|G'|` と `|G:G'|` の両方を割るので `e = 1`。 -/
theorem card_inf_commutator [Finite G] [IsZGroup G] (K : Subgroup G) :
    Nat.card ↥(K ⊓ commutator G) = Nat.gcd (Nat.card ↥K) (Nat.card ↥(commutator G)) := by
  have hcop : Nat.Coprime (Nat.card ↥(commutator G)) (commutator G).index :=
    IsZGroup.coprime_commutator_index G
  have hmulG : Nat.card ↥(commutator G) * (commutator G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hsup := card_sup_mul_card_inf_eq K (commutator G)
  obtain ⟨f, hf⟩ : Nat.card ↥(commutator G) ∣ Nat.card ↥(K ⊔ commutator G) :=
    card_dvd_card_of_le le_sup_right
  have hNne : Nat.card ↥(commutator G) ≠ 0 := Nat.card_pos.ne'
  have hdne : Nat.card ↥(K ⊓ commutator G) ≠ 0 := Nat.card_pos.ne'
  -- `f ∣ |G : G'|`
  have hfidx : f ∣ (commutator G).index := by
    have h1 : Nat.card ↥(K ⊔ commutator G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [hf, ← hmulG] at h1
    exact (mul_dvd_mul_iff_left hNne).mp h1
  -- `f * d = |K|`
  have hfd : f * Nat.card ↥(K ⊓ commutator G) = Nat.card ↥K := by
    rw [hf] at hsup
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hNne) ?_
    calc Nat.card ↥(commutator G) * (f * Nat.card ↥(K ⊓ commutator G))
        = Nat.card ↥(commutator G) * f * Nat.card ↥(K ⊓ commutator G) := by ring
      _ = Nat.card ↥K * Nat.card ↥(commutator G) := hsup
      _ = Nat.card ↥(commutator G) * Nat.card ↥K := by ring
  -- `d ∣ gcd`, 商 `e` は 1
  obtain ⟨e, he⟩ : Nat.card ↥(K ⊓ commutator G) ∣
      Nat.gcd (Nat.card ↥K) (Nat.card ↥(commutator G)) :=
    Nat.dvd_gcd (card_dvd_card_of_le inf_le_left) (card_dvd_card_of_le inf_le_right)
  have heN : e ∣ Nat.card ↥(commutator G) :=
    dvd_trans ⟨Nat.card ↥(K ⊓ commutator G), by rw [he]; ring⟩
      (Nat.gcd_dvd_right (Nat.card ↥K) (Nat.card ↥(commutator G)))
  have hef : e ∣ f := by
    have h1 : Nat.card ↥(K ⊓ commutator G) * e ∣ Nat.card ↥(K ⊓ commutator G) * f := by
      rw [← he, mul_comm (Nat.card ↥(K ⊓ commutator G)) f, hfd]
      exact Nat.gcd_dvd_left _ _
    exact (mul_dvd_mul_iff_left hdne).mp h1
  have he1 : e = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd heN (hef.trans hfidx))
  rw [he, he1, mul_one]

/-- Z-群の同位数の 2 つの部分群は `G'` との交わりが一致し, それは `G` で正規。 -/
theorem inf_commutator_eq_of_card_eq [Finite G] [IsZGroup G] {K₁ K₂ : Subgroup G}
    (h : Nat.card ↥K₁ = Nat.card ↥K₂) :
    K₁ ⊓ commutator G = K₂ ⊓ commutator G := by
  have : IsCyclic ↥(commutator G) := IsZGroup.isCyclic_commutator G
  have hcard : Nat.card ↥((K₁ ⊓ commutator G).subgroupOf (commutator G))
      = Nat.card ↥((K₂ ⊓ commutator G).subgroupOf (commutator G)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        K₁ ⊓ commutator G ≤ commutator G)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        K₂ ⊓ commutator G ≤ commutator G)).toEquiv,
      card_inf_commutator, card_inf_commutator, h]
  have hsub := cyclic_subgroup_eq_of_card_eq hcard
  have := Subgroup.subgroupOf_inj.mp hsub
  rwa [inf_assoc, inf_idem, inf_assoc, inf_idem] at this

/-- `K ⊓ G'` は `G` で正規 (`G'` 巡回ゆえその部分群は特性)。 -/
theorem normal_inf_commutator [Finite G] [IsZGroup G] (K : Subgroup G) :
    (K ⊓ commutator G).Normal := by
  have : IsCyclic ↥(commutator G) := IsZGroup.isCyclic_commutator G
  have : ((K ⊓ commutator G).subgroupOf (commutator G)).Characteristic :=
    characteristic_of_isCyclic _
  have hmap : ((K ⊓ commutator G).subgroupOf (commutator G)).map (commutator G).subtype
      = K ⊓ commutator G :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  exact hmap ▸ normal_map_subtype_of_characteristic

/-- `N ≤ L`, `N` 正規なら `|L/N| · |N| = |L|` (商への射の像の位数)。 -/
theorem card_map_mk'_mul_card [Finite G] {N L : Subgroup G} [N.Normal] (hNL : N ≤ L) :
    Nat.card ↥(L.map (QuotientGroup.mk' N)) * Nat.card ↥N = Nat.card ↥L := by
  have hrange : ((QuotientGroup.mk' N).comp L.subtype).range = L.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ((QuotientGroup.mk' N).comp L.subtype).ker = N.subgroupOf L := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hiso := QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' N).comp L.subtype)
  have h1 : Nat.card ↥(L.map (QuotientGroup.mk' N)) = (N.subgroupOf L).index := by
    rw [← hrange, ← Nat.card_congr hiso.toEquiv, hker]
    rfl
  have h2 : Nat.card ↥(N.subgroupOf L) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  rw [h1, ← h2, mul_comm]
  exact Subgroup.card_mul_index _

/-- Z-群の同位数の 2 つの部分群は `G'` との結びが一致する (`G/G'` は巡回で
同位数の部分群は一意)。 -/
theorem sup_commutator_eq_of_card_eq [Finite G] [IsZGroup G] {K₁ K₂ : Subgroup G}
    (h : Nat.card ↥K₁ = Nat.card ↥K₂) :
    K₁ ⊔ commutator G = K₂ ⊔ commutator G := by
  have : IsCyclic (G ⧸ commutator G) := IsZGroup.isCyclic_abelianization
  have hNne : Nat.card ↥(commutator G) ≠ 0 := Nat.card_pos.ne'
  -- `|K₁ ⊔ G'| = |K₂ ⊔ G'|`
  have hsupcard : Nat.card ↥(K₁ ⊔ commutator G) = Nat.card ↥(K₂ ⊔ commutator G) := by
    have h1 := card_sup_mul_card_inf_eq K₁ (commutator G)
    have h2 := card_sup_mul_card_inf_eq K₂ (commutator G)
    rw [card_inf_commutator, h] at h1
    rw [card_inf_commutator] at h2
    have hgne : Nat.gcd (Nat.card ↥K₂) (Nat.card ↥(commutator G)) ≠ 0 := by
      simp [Nat.gcd_eq_zero_iff, Nat.card_pos.ne']
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hgne) ?_
    rw [h1, h2]
  -- 商での像が等しい
  have himg : (K₁ ⊔ commutator G).map (QuotientGroup.mk' (commutator G))
      = (K₂ ⊔ commutator G).map (QuotientGroup.mk' (commutator G)) := by
    refine cyclic_subgroup_eq_of_card_eq ?_
    have e1 := card_map_mk'_mul_card (N := commutator G) (L := K₁ ⊔ commutator G) le_sup_right
    have e2 := card_map_mk'_mul_card (N := commutator G) (L := K₂ ⊔ commutator G) le_sup_right
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNne) ?_
    rw [e1, e2, hsupcard]
  -- comap で戻す
  have hcomap : ∀ K : Subgroup G, Subgroup.comap (QuotientGroup.mk' (commutator G))
      ((K ⊔ commutator G).map (QuotientGroup.mk' (commutator G))) = K ⊔ commutator G := by
    intro K
    refine Subgroup.comap_map_eq_self ?_
    rw [QuotientGroup.ker_mk']
    exact le_sup_right
  rw [← hcomap K₁, himg, hcomap K₂]

/-- Z-群の部分群 `K` は `|K| = |K ⊓ G'| · f`, `|K ⊔ G'| = |G'| · f` (`f ∣ |G : G'|`) と分解する。 -/
theorem exists_index_factor [Finite G] [IsZGroup G] (K : Subgroup G) :
    ∃ f : ℕ, f ∣ (commutator G).index ∧
      Nat.card ↥(K ⊔ commutator G) = Nat.card ↥(commutator G) * f ∧
      Nat.card ↥K = Nat.card ↥(K ⊓ commutator G) * f := by
  have hmulG : Nat.card ↥(commutator G) * (commutator G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hsup := card_sup_mul_card_inf_eq K (commutator G)
  obtain ⟨f, hf⟩ : Nat.card ↥(commutator G) ∣ Nat.card ↥(K ⊔ commutator G) :=
    card_dvd_card_of_le le_sup_right
  have hNne : Nat.card ↥(commutator G) ≠ 0 := Nat.card_pos.ne'
  refine ⟨f, ?_, hf, ?_⟩
  · have h1 : Nat.card ↥(K ⊔ commutator G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [hf, ← hmulG] at h1
    exact (mul_dvd_mul_iff_left hNne).mp h1
  · rw [hf] at hsup
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hNne) ?_
    calc Nat.card ↥(commutator G) * Nat.card ↥K
        = Nat.card ↥K * Nat.card ↥(commutator G) := by ring
      _ = Nat.card ↥(commutator G) * f * Nat.card ↥(K ⊓ commutator G) := hsup.symm
      _ = Nat.card ↥(commutator G) * (Nat.card ↥(K ⊓ commutator G) * f) := by ring

/-- ⭐ **Isaacs Problem 5C.4 (共役性)**: `G` の Sylow 部分群がすべて巡回なら, 同位数の
2 つの部分群は `G`-共役。

**証明** (商群を経由しない経路): `N := G'` は巡回な正規 Hall。
`M := K_i ⊓ N` は両者で一致し (`inf_commutator_eq_of_card_eq`) `G` で正規,
`L := K_i ⊔ N` も一致する (`sup_commutator_eq_of_card_eq`, `G/N` 巡回)。
`|K_i| = |M| · f` で `f ∣ |G:N|` なので `gcd(f, |N|) = 1`。`K_i` 自身も Z-群なので
位数 `f` の部分群 `Q_i ≤ K_i` を持ち (存在部分の再利用), `Q_i ⊓ N = ⊥`,
`|Q_i| · |N| = |L|` より `Q_i` は `↥L` の中で正規 Hall `N` の**補群**。
Schur–Zassenhaus 共役性で `Q₁^n = Q₂` (`n ∈ N`) となり, `K_i = Q_i ⊔ M` かつ `M` 正規
なので `K₁^n = K₂`。 -/
theorem exists_conj_of_card_eq_of_isZGroup [Finite G] [IsZGroup G] {K₁ K₂ : Subgroup G}
    (h : Nat.card ↥K₁ = Nat.card ↥K₂) :
    ∃ g : G, K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  classical
  have : IsCyclic ↥(commutator G) := IsZGroup.isCyclic_commutator G
  have hcop : Nat.Coprime (Nat.card ↥(commutator G)) (commutator G).index :=
    IsZGroup.coprime_commutator_index G
  have hM := inf_commutator_eq_of_card_eq h
  have hL := sup_commutator_eq_of_card_eq h
  obtain ⟨f, hfidx, hfL, hfK₁⟩ := exists_index_factor K₁
  obtain ⟨f', hf'idx, hf'L, hf'K₂⟩ := exists_index_factor K₂
  have hff' : f = f' := by
    have hE : Nat.card ↥(commutator G) * f = Nat.card ↥(commutator G) * f' := by
      rw [← hfL, hL, hf'L]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hE
  subst hff'
  have hfN : Nat.Coprime f (Nat.card ↥(commutator G)) :=
    (Nat.Coprime.coprime_dvd_left hfidx hcop.symm)
  -- 位数 `f` の部分群 `Q_i ≤ K_i` (存在部分の再利用)
  have hQex : ∀ K : Subgroup G, f ∣ Nat.card ↥K → ∃ Q : Subgroup G, Q ≤ K ∧ Nat.card ↥Q = f := by
    intro K hfK
    obtain ⟨Q', hQ'⟩ := exists_subgroup_card_eq_of_isZGroup (G := ↥K) hfK
    refine ⟨Q'.map K.subtype, Subgroup.map_subtype_le _, ?_⟩
    rw [← hQ']
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective Q' _ (Subgroup.subtype_injective _)).toEquiv.symm
  obtain ⟨Q₁, hQ₁K, hQ₁card⟩ := hQex K₁ ⟨_, by rw [hfK₁]; ring⟩
  obtain ⟨Q₂, hQ₂K, hQ₂card⟩ := hQex K₂ ⟨_, by rw [hf'K₂]; ring⟩
  -- `Q_i ⊓ N = ⊥`
  have hQdisj : ∀ Q : Subgroup G, Nat.card ↥Q = f → Disjoint Q (commutator G) := by
    intro Q hQ
    exact Subgroup.disjoint_of_coprime_natCard (by rw [hQ]; exact hfN)
  -- `Q_i ≤ L` かつ `Q_i` は `↥L` の中で `N` の補群
  have hNL : commutator G ≤ K₁ ⊔ commutator G := le_sup_right
  have : ((commutator G).subgroupOf (K₁ ⊔ commutator G)).Normal :=
    Subgroup.normal_subgroupOf
  have hcardN' : Nat.card ↥((commutator G).subgroupOf (K₁ ⊔ commutator G))
      = Nat.card ↥(commutator G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hidxN' : ((commutator G).subgroupOf (K₁ ⊔ commutator G)).index = f := by
    have hc := Subgroup.card_mul_index ((commutator G).subgroupOf (K₁ ⊔ commutator G))
    rw [hcardN', hfL] at hc
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc
  have hcompl : ∀ Q : Subgroup G, Q ≤ K₁ ⊔ commutator G → Nat.card ↥Q = f →
      Subgroup.IsComplement' ((commutator G).subgroupOf (K₁ ⊔ commutator G))
        (Q.subgroupOf (K₁ ⊔ commutator G)) := by
    intro Q hQL hQ
    have hcardQ' : Nat.card ↥(Q.subgroupOf (K₁ ⊔ commutator G)) = f := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv, hQ]
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · rw [hcardN', hcardQ', ← hfL]
    · rw [Subgroup.disjoint_def]
      intro x hx1 hx2
      have hx1' : (x : G) ∈ commutator G := hx1
      have hx2' : (x : G) ∈ Q := hx2
      exact Subtype.ext (Subgroup.disjoint_def.mp (hQdisj Q hQ) hx2' hx1')
  have hQ₁L : Q₁ ≤ K₁ ⊔ commutator G := hQ₁K.trans le_sup_left
  have hQ₂L : Q₂ ≤ K₁ ⊔ commutator G := hL ▸ hQ₂K.trans le_sup_left
  -- Schur–Zassenhaus 共役性
  obtain ⟨n, hnN, hconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime
      (by rw [hcardN', hidxN']; exact hcop.coprime_dvd_right hfidx)
      (Or.inl inferInstance) (hcompl Q₁ hQ₁L hQ₁card) (hcompl Q₂ hQ₂L hQ₂card)
  refine ⟨(n : G), ?_⟩
  -- `Q₁^n = Q₂` を `G` へ持ち上げる
  have hcomm : (K₁ ⊔ commutator G).subtype.comp (MulAut.conj n).toMonoidHom
      = ((MulAut.conj (n : G)).toMonoidHom).comp (K₁ ⊔ commutator G).subtype := by
    ext y
    simp
  have hQconj : Q₁.map (MulAut.conj (n : G)).toMonoidHom = Q₂ := by
    have := congrArg (Subgroup.map (K₁ ⊔ commutator G).subtype) hconj
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hQ₁L, Subgroup.map_subgroupOf_eq_of_le hQ₂L] at this
    exact this
  -- `K_i = Q_i ⊔ M`
  have hKeq : ∀ (K Q : Subgroup G), Q ≤ K → Nat.card ↥Q = f →
      Nat.card ↥K = Nat.card ↥(K ⊓ commutator G) * f → Q ⊔ (K ⊓ commutator G) = K := by
    intro K Q hQK hQ hKf
    have : (K ⊓ commutator G).Normal := normal_inf_commutator K
    have hdisj : Q ⊓ (K ⊓ commutator G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact Subgroup.disjoint_def.mp (hQdisj Q hQ) hx.1 hx.2.2
    have hcard : Nat.card ↥(Q ⊔ (K ⊓ commutator G)) = Nat.card ↥K := by
      rw [card_sup_eq_mul_of_disjoint_normal hdisj, hQ, hKf, mul_comm]
    exact Subgroup.eq_of_le_of_card_ge (sup_le hQK inf_le_left) (le_of_eq hcard.symm)
  have hK₁eq := hKeq K₁ Q₁ hQ₁K hQ₁card hfK₁
  have hK₂eq := hKeq K₂ Q₂ hQ₂K hQ₂card hf'K₂
  have : (K₁ ⊓ commutator G).Normal := normal_inf_commutator K₁
  have hMconj : (K₁ ⊓ commutator G).map (MulAut.conj (n : G)).toMonoidHom
      = K₁ ⊓ commutator G :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_of_normal _)
  calc K₁.map (MulAut.conj (n : G)).toMonoidHom
      = (Q₁ ⊔ (K₁ ⊓ commutator G)).map (MulAut.conj (n : G)).toMonoidHom := by rw [hK₁eq]
    _ = Q₁.map (MulAut.conj (n : G)).toMonoidHom
          ⊔ (K₁ ⊓ commutator G).map (MulAut.conj (n : G)).toMonoidHom :=
        Subgroup.map_sup _ _ _
    _ = Q₂ ⊔ (K₂ ⊓ commutator G) := by rw [hQconj, hMconj, hM]
    _ = K₂ := hK₂eq

end

end OddOrder.Isaacs.Ch05
