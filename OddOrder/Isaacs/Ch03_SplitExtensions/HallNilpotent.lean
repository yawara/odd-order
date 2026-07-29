/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Nilpotent
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Hall 部分群と冪零性

有限**冪零**群の `π`-Hall 部分群は必ず正規である。冪零群の Sylow 部分群が正規である
(mathlib `Sylow.normal_of_normalizerCondition`) ことの Hall 版で、証明の骨格も同じ:

1. `π`-Hall 部分群 `H` を正規化する `π`-部分群は `H` に含まれる
   (`isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer`) — `N ⊔ H` の位数が
   `|N|·|H|` を割るので `π`-群になり、Hall の極大性で `N ⊔ H = H`。
2. ゆえに `N_G(H)` は自己正規化 (`IsHallSubgroup.normalizer_normalizer`) —
   `g ∈ N_G(N_G(H))` なら `H^g` は `N_G(H)` 内の `π`-部分群なので 1 で `H^g ≤ H`,
   位数が等しいので `H^g = H`。
3. 冪零群は正規化条件を満たす (`Group.normalizerCondition_of_isNilpotent`) ので
   自己正規化部分群は `⊤` のみ、すなわち `N_G(H) = ⊤` で `H ⊴ G`
   (`IsHallSubgroup.normal_of_isNilpotent`)。

系として、冪零群の `π`-Hall と `π'`-Hall は元ごとに可換
(`commute_of_isHallSubgroup_of_isHallSubgroup_compl`)。冪零群は Sylow 部分群の直積である
という事実の Hall 版で、Isaacs Problem 3C.7 (Carter 部分群) の共役性の証明で
`C = C_p × C_{p'}` を得るのに使う (issue 9213 / 1055)。

## Main results

* `isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer` — `π`-Hall を正規化する
  `π`-部分群はその中にある (冪零性不要)。
* `IsHallSubgroup.normalizer_normalizer` — `N_G(N_G(H)) = N_G(H)` (冪零性不要)。
* `IsHallSubgroup.normal_of_isNilpotent` — 冪零群の Hall 部分群は正規。
* `commute_of_isHallSubgroup_of_isHallSubgroup_compl` — 冪零群の `π`-Hall と
  `π'`-Hall は元ごとに可換。
-/

namespace OddOrder.Isaacs.Ch03

open scoped Pointwise

variable {G : Type*} [Group G]

section /- 3C: Hall theory (pp. 83-88) -/

/-- **`π`-Hall 部分群を正規化する `π`-部分群はその中にある。**

`N` が `H` を正規化するので `↑(N ⊔ H) = ↑N · ↑H` (集合積) となり、
`|N ⊔ H| · |N ⊓ H| = |N| · |H|` から `|N ⊔ H|` は `|N|·|H|` を割る。
よって `N ⊔ H` は `π`-群で、`π`-Hall の極大性 (`IsHallSubgroup.card_dvd_of_isPiGroup`)
から `|N ⊔ H| = |H|`、すなわち `N ⊔ H = H`。

`H` 自身が正規な場合が `Subgroup.IsPiGroup.normal_le_hall` の双対
(`OddOrder.BG.Ch3.S12.isPiSubgroup_le_of_normal_isHall`) で、本補題はその一般化
(`H.Normal` を `N ≤ N_G(H)` に弱めた)。 -/
theorem isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer [Finite G] {π : Set ℕ}
    {H N : Subgroup G} (hH : IsHallSubgroup π H) (hN : Subgroup.IsPiGroup π N)
    (hle : N ≤ Subgroup.normalizer (H : Set G)) : N ≤ H := by
  -- `N` が `H` を正規化するので join の台集合は集合積。
  have hcoe : ((N ⊔ H : Subgroup G) : Set G) = (N : Set G) * (H : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right N H hle
  have hSup_pi : Subgroup.IsPiGroup π (N ⊔ H : Subgroup G) := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, -⟩ := hq
    have h_card_eq : Nat.card ↥(N ⊔ H : Subgroup G) * Nat.card ↥(N ⊓ H : Subgroup G)
        = Nat.card ↥N * Nat.card ↥H := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card N H
      rwa [← hcoe] at h_hk
    have h_dvd_prod : q ∣ Nat.card ↥N * Nat.card ↥H := by
      rw [← h_card_eq]
      exact hq_dvd.mul_right _
    rcases hq_prime.dvd_mul.mp h_dvd_prod with hN_dvd | hH_dvd
    · exact hN q (Nat.mem_primeFactors.mpr ⟨hq_prime, hN_dvd, Nat.card_pos.ne'⟩)
    · exact hH.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hH_dvd, Nat.card_pos.ne'⟩)
  have h_card_dvd : Nat.card ↥(N ⊔ H : Subgroup G) ∣ Nat.card ↥H :=
    hH.card_dvd_of_isPiGroup hSup_pi
  have h_card_eq : Nat.card ↥(N ⊔ H : Subgroup G) = Nat.card ↥H :=
    Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd)
      (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective le_sup_right))
  have h_sup_eq : (N ⊔ H : Subgroup G) = H :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right h_card_eq.le).symm
  intro x hx
  have hx_sup : x ∈ (N ⊔ H : Subgroup G) := Subgroup.mem_sup_left hx
  rwa [h_sup_eq] at hx_sup

/-- **`π`-Hall 部分群の正規化子は自己正規化**: `N_G(N_G(H)) = N_G(H)`。

mathlib の `Sylow.normalizer_normalizer` の Hall 版。`g ∈ N_G(N_G(H))` とすると
`H^g ≤ (N_G H)^g = N_G(H)` で、`H^g` は `|H^g| = |H|` ゆえ `π`-群。
`isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer` で `H^g ≤ H`、位数が等しいので
`H^g = H`、すなわち `g ∈ N_G(H)`。 -/
theorem IsHallSubgroup.normalizer_normalizer [Finite G] {π : Set ℕ} {H : Subgroup G}
    (hH : IsHallSubgroup π H) :
    Subgroup.normalizer ((Subgroup.normalizer (H : Set G) : Subgroup G) : Set G)
      = Subgroup.normalizer (H : Set G) := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  -- `g` は `M := N_G(H)` を正規化する。
  have hgM : (Subgroup.normalizer (H : Set G)).map (MulAut.conj g)
      = Subgroup.normalizer (H : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  -- `H^g ≤ M^g = M`.
  have hconj_le : H.map (MulAut.conj g) ≤ Subgroup.normalizer (H : Set G) := by
    calc H.map (MulAut.conj g)
        ≤ (Subgroup.normalizer (H : Set G)).map (MulAut.conj g) :=
          Subgroup.map_mono Subgroup.le_normalizer
      _ = Subgroup.normalizer (H : Set G) := hgM
  -- `|H^g| = |H|`, so `H^g` is a `π`-group.
  have hcard : Nat.card ↥((H.map (MulAut.conj g) : Subgroup G)) = Nat.card ↥H := by
    apply Subgroup.card_map_of_injective
    exact (MulAut.conj g).injective
  have hconj_pi : Subgroup.IsPiGroup π (H.map (MulAut.conj g) : Subgroup G) := by
    intro p hp
    rw [hcard] at hp
    exact hH.1 p hp
  -- `H^g ≤ H` and cardinalities agree, so `H^g = H`, i.e. `g ∈ N_G(H)`.
  have hle : H.map (MulAut.conj g) ≤ H :=
    isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer hH hconj_pi hconj_le
  have heq : H.map (MulAut.conj g) = H :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

/-- **有限冪零群の `π`-Hall 部分群は正規** (issue 9213)。

冪零群は正規化条件 (`Group.normalizerCondition_of_isNilpotent`) を満たすので、
自己正規化部分群は `⊤` のみ。`IsHallSubgroup.normalizer_normalizer` より
`N_G(H)` は自己正規化なので `N_G(H) = ⊤`、すなわち `H ⊴ G`。

mathlib の `Sylow.normal_of_normalizerCondition` (Sylow 版) の Hall 一般化。 -/
theorem IsHallSubgroup.normal_of_isNilpotent [Finite G] [Group.IsNilpotent G] {π : Set ℕ}
    {H : Subgroup G} (hH : IsHallSubgroup π H) : H.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  exact normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := G)) _ hH.normalizer_normalizer

/-- **冪零群の `π`-Hall と `π'`-Hall は元ごとに可換**。

両者とも正規 (`IsHallSubgroup.normal_of_isNilpotent`) で、位数が互いに素ゆえ交わりは自明。
`Subgroup.commute_of_normal_of_disjoint` で結論。

Isaacs Problem 3C.7 (Carter 部分群) の共役性で `C = C_p × C_{p'}` を得るのに使う。 -/
theorem commute_of_isHallSubgroup_of_isHallSubgroup_compl [Finite G] [Group.IsNilpotent G]
    {π : Set ℕ} {S Q : Subgroup G} (hS : IsHallSubgroup π S)
    (hQ : IsHallSubgroup {p | p ∉ π} Q) :
    ∀ x ∈ S, ∀ y ∈ Q, Commute x y := by
  haveI := hS.normal_of_isNilpotent
  haveI := hQ.normal_of_isNilpotent
  -- `|S|` は `π`-数, `|Q|` は `π'`-数なので互いに素。
  have hcop : Nat.Coprime (Nat.card ↥S) (Nat.card ↥Q) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hq_dvd
    exact hQ.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩)
      (hS.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩))
  exact fun x hx y hy =>
    Subgroup.commute_of_normal_of_disjoint S Q inferInstance inferInstance
      (Subgroup.disjoint_of_coprime_natCard hcop) x y hx hy

end -- 3C

end OddOrder.Isaacs.Ch03
