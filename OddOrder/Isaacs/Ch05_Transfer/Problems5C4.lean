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
theorem normal_map_subtype_of_characteristic {N : Subgroup G} [N.Normal] {M : Subgroup ↥N}
    [M.Characteristic] : (M.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hg : g ∈ Subgroup.normalizer ((N : Subgroup G) : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (inferInstance : N.Normal).conj_mem _ hy g
    · intro hy
      have h := (inferInstance : N.Normal).conj_mem _ hy g⁻¹
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h
  exact conj_mem_map_subtype_of_characteristic hg hx

/-- Z-群の Schur–Zassenhaus 補群は `G/G'` と同型ゆえ巡回。 -/
theorem isCyclic_of_isComplement'_commutator [Finite G] [IsZGroup G] {H : Subgroup G}
    (hH : Subgroup.IsComplement' (commutator G) H) : IsCyclic ↥H := by
  haveI : IsCyclic (G ⧸ commutator G) := IsZGroup.isCyclic_abelianization
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
  haveI : IsCyclic ↥(commutator G) := IsZGroup.isCyclic_commutator G
  have hcop : Nat.Coprime (Nat.card ↥(commutator G)) (commutator G).index :=
    IsZGroup.coprime_commutator_index G
  have hmul : Nat.card ↥(commutator G) * (commutator G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hdec : Nat.gcd m (Nat.card ↥(commutator G)) * Nat.gcd m (commutator G).index = m :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr (by rw [hmul]; exact hm)
  -- `M ≤ G'` : 位数 `m₁`
  obtain ⟨M', hM'⟩ := exists_subgroup_card_eq_of_isCyclic
    (C := ↥(commutator G)) (Nat.gcd_dvd_right m (Nat.card ↥(commutator G)))
  haveI : M'.Characteristic := characteristic_of_isCyclic M'
  haveI : (M'.map (commutator G).subtype).Normal := normal_map_subtype_of_characteristic
  have hMcard : Nat.card ↥(M'.map (commutator G).subtype)
      = Nat.gcd m (Nat.card ↥(commutator G)) := by
    rw [← hM']
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective M' _ (Subgroup.subtype_injective _)).toEquiv.symm
  -- `H` : Schur–Zassenhaus 補群 (巡回), その中の位数 `m₂` の部分群 `H₂`
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  haveI : IsCyclic ↥H := isCyclic_of_isComplement'_commutator hH
  have hHcard : Nat.card ↥H = (commutator G).index := by
    have h := hH.card_mul
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

end

end OddOrder.Isaacs.Ch05
