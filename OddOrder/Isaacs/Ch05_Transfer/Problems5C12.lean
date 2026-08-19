/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5C
import OddOrder.Isaacs.Ch05_Transfer.Problems5C11

/-!
# Isaacs Problem 5C.12 — 巡回 Sylow と指数が `p` で割れる正規部分群 (p. 164)

**主張**: `G` の Sylow `p`-部分群 `P` が巡回で, `N ⊴ G` の指数が `p` で割れるなら,
`N` は正規 `p`-補群をもつ。

**証明**: `Y := N ⊔ P` (= `NP`) とおく。

* `Y/N` は `P` の像なので**可換**, すなわち `⁅Y, Y⁆ ≤ N`。
* `p ∤ |G:Y|` (`P ≤ Y` で `P` は Sylow) なので `|N:Y 内| · |G:Y| = |G:N|` から
  **`p ∣ |Y : N|`**、したがって `p ∣ |↥Y : (commutator ↥Y)|`。
* `↥Y` の Sylow `p`-部分群は `P` (巡回) なので **Isaacs Thm 5.17** が使え、上の割り切れから
  第 2 の選択肢が潰れて **`p ∤ |commutator ↥Y| = |⁅Y,Y⁆|`**。
* `⁅N,N⁆ ≤ ⁅Y,Y⁆` ゆえ `p ∤ |commutator ↥N|`、とくに `↥N` の Sylow `p`-部分群 `Q` に対し
  `commutator ↥N ⊓ Q = ⊥` (位数が互いに素)。
* **Problem 5C.1** (`hasNormalPComplement_of_commutator_inf_sylow_eq_bot`) より `N` は正規
  `p`-補群をもつ。

⭐ `N` が完全群 (`N = N'`) の場合も込みで一様に効くのがこの論法の要点。`N` 自身に Thm 5.17 を
当てるだけでは (完全群では `|N:N'| = 1` ゆえ) 何も出ない — `P` 全体を含む `Y = NP` に上げるのが鍵。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

variable {G : Type*} [Group G]

section /- 5C.12: 巡回 Sylow と指数が `p` で割れる正規部分群 (p. 164) -/

/-- `N ⊴ G` と可換部分群 `A` の join の交換子部分群は `N` に含まれる (`(NA)/N` は `A` の像で可換)。 -/
theorem commutator_sup_le_of_normal_of_commutative {N A : Subgroup G} [N.Normal]
    (hA : ∀ x y : ↥A, x * y = y * x) : ⁅N ⊔ A, N ⊔ A⁆ ≤ N := by
  classical
  have hmapN : N.map (QuotientGroup.mk' N) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' N).ge
  have habel : (A.map (QuotientGroup.mk' N)) ≤
      Subgroup.centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hA ⟨b, hb⟩ ⟨a, ha⟩))
  have hbot : (⁅N ⊔ A, N ⊔ A⁆).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_sup, hmapN, bot_sup_eq,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact habel
  have hle := (Subgroup.map_eq_bot_iff _).mp hbot
  rwa [QuotientGroup.ker_mk'] at hle

/-- **Isaacs Problem 5C.12** (p. 164) ⭐: `G` の Sylow `p`-部分群が巡回で `N ⊴ G` の指数が
`p` で割れるなら, `N` は正規 `p`-補群をもつ。 -/
theorem hasNormalPComplement_of_isCyclic_sylow_of_dvd_index [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic ↥(P : Subgroup G)] {N : Subgroup G} [N.Normal]
    (hpN : p ∣ N.index) :
    HasNormalPComplement p ↥N := by
  classical
  set Y : Subgroup G := N ⊔ (P : Subgroup G) with hY
  have hNY : N ≤ Y := le_sup_left
  have hPY : (P : Subgroup G) ≤ Y := le_sup_right
  -- `⁅Y, Y⁆ ≤ N` (`Y/N` は `P` の像で可換)
  have hcommY : ⁅Y, Y⁆ ≤ N := commutator_sup_le_of_normal_of_commutative
    (fun x y => (IsCyclic.commGroup (α := ↥(P : Subgroup G))).mul_comm x y)
  -- `p ∣ |Y : N|`
  have hYidx : ¬ p ∣ Y.index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hPY))
  have hrelp : p ∣ N.relIndex Y := by
    have hmul : N.relIndex Y * Y.index = N.index := Subgroup.relIndex_mul_index hNY
    exact ((Nat.Prime.dvd_mul Fact.out).mp (hmul ▸ hpN)).resolve_right hYidx
  -- `↥Y` に Thm 5.17 を適用: `p ∤ |commutator ↥Y|`
  have hcyc : IsCyclic ↥((P.subtype hPY : Sylow p ↥Y) : Subgroup ↥Y) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPY).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPY).symm.surjective
  have hcommYle : (_root_.commutator ↥Y) ≤ N.subgroupOf Y := by
    rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator]
    exact hcommY
  have hidxdvd : (N.subgroupOf Y).index ∣ (_root_.commutator ↥Y).index :=
    Subgroup.index_dvd_of_le hcommYle
  have hnotdvdY : ¬ p ∣ Nat.card (_root_.commutator ↥Y) := by
    rcases isaacs_thm_5_17 (G := ↥Y) (P.subtype hPY) with h | h
    · exact h
    · exact absurd (hrelp.trans hidxdvd) h
  -- `⁅N, N⁆ ≤ ⁅Y, Y⁆` から `p ∤ |commutator ↥N|`
  have hmapN : Nat.card (_root_.commutator ↥N) = Nat.card ↥(⁅N, N⁆ : Subgroup G) := by
    rw [← Subgroup.map_subtype_commutator N,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective N)]
  have hmapY : Nat.card (_root_.commutator ↥Y) = Nat.card ↥(⁅Y, Y⁆ : Subgroup G) := by
    rw [← Subgroup.map_subtype_commutator Y,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
  have hNYcomm : (⁅N, N⁆ : Subgroup G) ≤ ⁅Y, Y⁆ := Subgroup.commutator_mono hNY hNY
  have hnotdvdN : ¬ p ∣ Nat.card (_root_.commutator ↥N) := by
    rw [hmapN]
    exact fun h => hnotdvdY (hmapY ▸ h.trans (Subgroup.card_dvd_of_le hNYcomm))
  -- Sylow `p`-部分群との交わりが自明 ⟹ Problem 5C.1
  obtain ⟨QQ⟩ := (inferInstance : Nonempty (Sylow p ↥N))
  refine hasNormalPComplement_of_commutator_inf_sylow_eq_bot QQ (Subgroup.card_eq_one.mp ?_)
  have h1 : Nat.card ↥(_root_.commutator ↥N ⊓ (QQ : Subgroup ↥N)) ∣
      Nat.card (_root_.commutator ↥N) := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(_root_.commutator ↥N ⊓ (QQ : Subgroup ↥N)) ∣
      p ^ (Nat.card ↥N).factorization p := QQ.card_eq_multiplicity ▸
    Subgroup.card_dvd_of_le (inf_le_right : _ ≤ (QQ : Subgroup ↥N))
  by_contra hne
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  have hrp : r = p :=
    (Nat.prime_dvd_prime_iff_eq hr Fact.out).mp (hr.dvd_of_dvd_pow (hrdvd.trans h2))
  exact hnotdvdN (hrp ▸ hrdvd.trans h1)

end

end OddOrder.Isaacs.Ch05
