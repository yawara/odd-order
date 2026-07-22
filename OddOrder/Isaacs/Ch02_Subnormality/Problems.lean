/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Isaacs Chapter 2 — Problems §2A (Subnormality)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 2 "Subnormality" の章末演習 §2A
(pp. 53-54)。部分正規性 (`Subgroup.IsSubnormal`, mathlib inductive) の基本性質を扱う。

方針は Ch.1 の `Ch01_Sylow/Problems.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch02

section /- Problems 2A: Subnormality basics (pp. 53-54) -/

/-- **Isaacs Problem 2A.3(a)**. `H` が部分正規で `|G : H|` と `|K|` が互いに素ならば `K ≤ H`。

`H.IsSubnormal` の帰納法。`H = ⊤` は自明。step (`H' ≤ K'`, `K'` 部分正規, `H' ⊴ K'`, IH) では
`|G:K'| ∣ |G:H'|` ゆえ IH で `K ≤ K'`。次に商 `K' / H'` への像 `K.subgroupOf K' ↦ mk'` の位数は
`|K|` (`card_map_dvd` + `subgroupOfEquivOfLe`) と `|K':H'|` (`card_subgroup_dvd_card`) の両方を割り、
`|K':H'| ∣ |G:H'|` は `|K|` と互いに素ゆえ像の位数 `= 1`、したがって `K.subgroupOf K' ≤ H'.subgroupOf K'`、
`K'.subtype` で押し戻して `K ≤ H'`。 -/
theorem le_of_isSubnormal_of_coprime_index {G : Type*} [Group G] [Finite G] {K : Subgroup G} :
    ∀ {H : Subgroup G}, H.IsSubnormal → (H.index).Coprime (Nat.card K) → K ≤ H := by
  intro H hH
  induction hH with
  | top => exact fun _ => le_top
  | @step H' K' hle hsubK' hN ih =>
    intro hcop
    have hcopK' : (K'.index).Coprime (Nat.card K) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.index_dvd_of_le hle) hcop
    have hKK' : K ≤ K' := ih hcopK'
    haveI := hN
    -- `|K':H'| = (H'.subgroupOf K').index ∣ |G:H'|` は `|K|` と互いに素
    have hidxdvd : (H'.subgroupOf K').index ∣ H'.index :=
      Subgroup.relIndex_dvd_index_of_le hle
    have hcopIdx : ((H'.subgroupOf K').index).Coprime (Nat.card K) :=
      Nat.Coprime.coprime_dvd_left hidxdvd hcop
    -- `K.subgroupOf K'` の `K' / H'` への像は自明
    have himg : (K.subgroupOf K').map (QuotientGroup.mk' (H'.subgroupOf K')) = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      refine Nat.eq_one_of_dvd_coprimes hcopIdx ?_ ?_
      · rw [Subgroup.index_eq_card]
        exact Subgroup.card_subgroup_dvd_card _
      · exact (Subgroup.card_map_dvd _ _).trans
          (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKK').toEquiv))
    -- 像 `⊥` ⟹ `K.subgroupOf K' ≤ ker = H'.subgroupOf K'`
    have hle' : K.subgroupOf K' ≤ H'.subgroupOf K' := by
      rw [← QuotientGroup.ker_mk' (H'.subgroupOf K')]
      intro x hx
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← himg]
      exact Subgroup.mem_map_of_mem _ hx
    -- `K'.subtype` で押し戻して `K ≤ H'`
    calc K = (K.subgroupOf K').map K'.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKK']
      _ ≤ (H'.subgroupOf K').map K'.subtype := Subgroup.map_mono hle'
      _ = H' := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 in
/-- 部分正規部分群 `H` について `O_π(↥H)` を `G` へ押し出すと `O_π(G)` を超えない。`IsSubnormal` の
構造帰納 (motive を `(oPiCore π ↥H).map H.subtype ≤ oPiCore π G` とすると step の IH が上の `K'` に
ついてで整合する)。top は `oPiCore.map_le_of_surjective`、step は同型
`(subgroupOfEquivOfLe hle).symm` で `oPiCore π ↥H'` を `oPiCore π ↥(H'.subgroupOf K')` に移送
(`oPiCore.map_eq_of_mulEquiv`)、`characteristic_map_subtype_normal` で `↥K'` 正規、`le_oPiCore` で
`≤ oPiCore π ↥K'`、`H.subtype = K'.subtype ∘ (subgroupOf).subtype ∘ e.symm` で合成して IH。 -/
theorem oPiCore_map_subtype_le_of_isSubnormal {G : Type*} [Group G] [Finite G] {π : Set ℕ} :
    ∀ {H : Subgroup G}, H.IsSubnormal → (oPiCore π ↥H).map H.subtype ≤ oPiCore π G := by
  intro H hH
  induction hH with
  | top =>
    exact oPiCore.map_le_of_surjective π (⊤ : Subgroup G).subtype
      (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  | @step H' K' hle hsubK' hN ih =>
    haveI := hN
    set e := Subgroup.subgroupOfEquivOfLe hle with he
    have htrans : (oPiCore π ↥H').map (e.symm : ↥H' →* ↥(H'.subgroupOf K'))
        = oPiCore π ↥(H'.subgroupOf K') := oPiCore.map_eq_of_mulEquiv π e.symm
    haveI hnorm : ((oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype).Normal :=
      characteristic_map_subtype_normal (oPiCore π ↥(H'.subgroupOf K'))
    have hpi : Subgroup.IsPiGroup π
        ((oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype) := fun q hq =>
      oPiCore.isPiGroup π q
        (by rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hq)
    have hle_oPiK' : (oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype
        ≤ oPiCore π ↥K' := Subgroup.IsPiGroup.le_oPiCore hpi
    have hcomp : H'.subtype
        = (K'.subtype.comp (H'.subgroupOf K').subtype).comp
          (e.symm : ↥H' →* ↥(H'.subgroupOf K')) := by
      ext h; rfl
    have hmapeq : (oPiCore π ↥H').map H'.subtype
        = ((oPiCore π ↥(H'.subgroupOf K')).map (H'.subgroupOf K').subtype).map K'.subtype := by
      rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, htrans]
    rw [hmapeq]
    exact (Subgroup.map_mono hle_oPiK').trans ih

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 in
/-- **Isaacs Problem 2A.1**. 有限群 `G` の部分正規 π-部分群 `K` は π-radical `O_π(G)` に含まれる。
`↥K` は π-群なので `O_π(↥K) = ⊤`、`oPiCore_map_subtype_le_of_isSubnormal` で
`K = (O_π ↥K).map K.subtype ≤ O_π(G)`。系として二つの部分正規 π-部分群の生成する部分群も π-群
(ともに `O_π(G)` に含まれ `O_π(G)` は π-群)。 -/
theorem le_oPiCore_of_isSubnormal_of_isPiGroup {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {K : Subgroup G} (hK : K.IsSubnormal) (hπ : Subgroup.IsPiGroup π K) : K ≤ oPiCore π G := by
  have h := oPiCore_map_subtype_le_of_isSubnormal (π := π) hK
  have htop : oPiCore π (↥K) = ⊤ := by
    refine top_le_iff.mp (Subgroup.IsPiGroup.le_oPiCore (H := (⊤ : Subgroup ↥K)) (fun q hq => ?_))
    exact hπ q (by rwa [Subgroup.card_top] at hq)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

open OddOrder.Isaacs.Ch01 in
/-- 正規部分群 `N` の位数が `|G : H|` と互いに素ならば `N ≤ H`。`|H⊔N : H|` は `card_mul_card_inf`
(正規積公式) より `|N|` を割り、また `|G : H|` も割る (`relIndex_dvd_index_of_le`) ので互いに素で `= 1`、
したがって `H⊔N = H`、`N ≤ H`。 -/
theorem coprime_normal_le {G : Type*} [Group G] [Finite G] {N H : Subgroup G} [N.Normal]
    (hcop : Nat.Coprime (Nat.card ↥N) H.index) : N ≤ H := by
  have hlag : H.relIndex (H ⊔ N) * Nat.card ↥H = Nat.card ↥(H ⊔ N) := by
    rw [Subgroup.relIndex,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ N)).toEquiv]
    exact Subgroup.index_mul_card (H.subgroupOf (H ⊔ N))
  have hcmi : Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
    have h := card_mul_card_inf H N
    rwa [← Subgroup.mul_normal H N] at h
  have hkey : H.relIndex (H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥N := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥H)) ?_
    rw [← mul_assoc, mul_comm (Nat.card ↥H) (H.relIndex (H ⊔ N)), hlag, hcmi]
  have hdN : H.relIndex (H ⊔ N) ∣ Nat.card ↥N := ⟨Nat.card ↥(H ⊓ N), hkey.symm⟩
  have hdidx : H.relIndex (H ⊔ N) ∣ H.index := Subgroup.relIndex_dvd_index_of_le le_sup_left
  have hd1 : H.relIndex (H ⊔ N) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdN hdidx
  have hcardeq : Nat.card ↥(H ⊔ N) = Nat.card ↥H := by rw [← hlag, hd1, one_mul]
  exact le_sup_right.trans (Subgroup.eq_of_le_of_card_ge le_sup_left hcardeq.le).ge

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 in
/-- **Isaacs Problem 2A.3(b)**. `K` が部分正規で `|G : H|` と `|K|` が互いに素ならば `K ≤ H`。
`π := |K| の素因数集合` とおくと `K` は π-群、2A.1 で `K ≤ O_π(G)`。`O_π(G)` は正規 π-群で、その位数の
素因数は `π ⊆ |K| の素因数`、`|G:H|` は `|K|` と互いに素ゆえ `|O_π(G)|` とも互いに素、`coprime_normal_le`
で `O_π(G) ≤ H`、したがって `K ≤ H`。 -/
theorem le_of_isSubnormal_of_coprime_index' {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hK : K.IsSubnormal) (hcop : (H.index).Coprime (Nat.card ↥K)) : K ≤ H := by
  set π : Set ℕ := ↑(Nat.card ↥K).primeFactors with hπdef
  have hπK : Subgroup.IsPiGroup π K := fun q hq => Finset.mem_coe.mpr hq
  have hKoP : K ≤ oPiCore π G := le_oPiCore_of_isSubnormal_of_isPiGroup hK hπK
  have hsub : (Nat.card ↥(oPiCore π G)).primeFactors ⊆ (Nat.card ↥K).primeFactors := fun q hq =>
    Finset.mem_coe.mp (oPiCore.isPiGroup π q hq)
  have hcopOP : Nat.Coprime (Nat.card ↥(oPiCore π G)) H.index := by
    rw [← Nat.disjoint_primeFactors (Nat.card_pos (α := ↥(oPiCore π G))).ne'
      Subgroup.index_ne_zero_of_finite]
    exact Finset.disjoint_of_subset_left hsub hcop.symm.disjoint_primeFactors
  exact hKoP.trans (coprime_normal_le hcopOP)

end

end OddOrder.Isaacs.Ch02
