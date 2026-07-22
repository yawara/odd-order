/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow.Main

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

end

end OddOrder.Isaacs.Ch02
