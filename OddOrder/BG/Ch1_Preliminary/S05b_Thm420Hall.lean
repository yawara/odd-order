/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups

/-!
# BG Theorem 4.20(c) — descending Hall radicals

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), §4 Theorem 4.20(c) (pp. 35-36, mmd L1764) の Hall-radical 形の系。

Theorem 4.20(c) は「solvable odd `X` with `r(F(X)) ≤ 2` は素数昇順の特性 Sylow 列を持つ」
(`exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two`)。その列の「大きい素数側の
切片」を直接 Hall radical として取り出したのが本ファイルの主結果
`isHall_oPiCore_of_isUpperSet_of_rank_fitting_le_two`: **上方閉な素数集合 `π`
(`IsUpperSet π`) に対し `O_π(X)` は `X` の (正規・特性) Hall `π`-部分群**。

BG Theorem 11.7 (`S11_MsigmaANormal`) が要求する形
「`τ = {q ∈ π(E) | q > p}` に対し `K = O_τ(E)` が Hall `τ` ∧ `O_{τ∪{p}}(E)` が
normal Hall `τ∪{p}`」は、`π := {q | p < q}` / `π := {q | p ≤ q}` (どちらも上方閉) への
2 回の適用で得られる。raw series (`CharacteristicSylowSeriesPackage`) はラベルの順序を
露出しないため、ここでは series を経由せず §5 の最小素数エンジン
`hasNormalPComplement_minFac_of_rank_fitting_le_two` を直接反復する。

実装 (強帰納法 on `|X|`): `p := minFac |X|`。`p ∈ π` なら上方閉性より `π(X) ⊆ π` で
`X` 自体が `π`-群、`O_π(X) = ⊤`。`p ∉ π` なら正規 `p`-補群 `N` (最小素数エンジン) に
帰納法を適用し、`O_π(↥N).map N.subtype` が `X` の正規 Hall `π`-部分群
(`N.index` は `p`-冪で `π` を避ける) であることから `O_π(X)` 自身と一致する
(`≤` は正規 `π`-部分群の `O_π` 吸収、`≥` は Hall 位数の整除)。
-/

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch1.S04

/-- **BG Theorem 4.20(c), Hall-radical form**: let `X` be a finite solvable group of odd
order with `r(F(X)) ≤ 2`, and let `π` be an upward-closed set of naturals (`IsUpperSet π`,
e.g. `{q | t ≤ q}` or `{q | t < q}`). Then the radical `O_π(X)` is a Hall `π`-subgroup
of `X` — the "large-prime segment" of the descending Sylow tower of Theorem 4.20(c).

Strong induction on `|X|`, iterating the minimal-prime normal-complement engine
`hasNormalPComplement_minFac_of_rank_fitting_le_two`: with `p := minFac |X|`, either
`p ∈ π` (then all of `π(X)` lies in `π` by upward closure and `O_π(X) = ⊤`), or the
canonical normal `p`-complement `N` carries the inductive Hall radical, whose image in
`X` is a normal Hall `π`-subgroup and hence equals `O_π(X)`. -/
theorem isHall_oPiCore_of_isUpperSet_of_rank_fitting_le_two
    {X : Type*} [Group X] [Finite X] [Group.IsSolvable X] (hodd : Odd (Nat.card X))
    (hrank : rank ↥(Ch01.fitting X) ≤ 2) {π : Set ℕ} (hπ : IsUpperSet π) :
    Ch03.IsHallSubgroup π (Ch03.oPiCore π X) := by
  classical
  suffices H : ∀ n : ℕ, ∀ (Y : Type _) [Group Y] [Finite Y] [Group.IsSolvable Y],
      Nat.card Y = n → Odd (Nat.card Y) → rank ↥(Ch01.fitting Y) ≤ 2 →
      Ch03.IsHallSubgroup π (Ch03.oPiCore π Y) from
    H (Nat.card X) X rfl hodd hrank
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Y _ _ _ hcard hodd' hrank'
    -- the order part is unconditional: `O_π(Y)` is a `π`-group.
    refine ⟨fun r hr => Ch03.oPiCore.isPiGroup π r hr, ?_⟩
    by_cases hY1 : Nat.card Y = 1
    · -- trivial group: the index divides `1`.
      intro r hr
      exfalso
      have hdvd : (Ch03.oPiCore π Y).index ∣ 1 := hY1 ▸ Subgroup.index_dvd_card _
      rw [Nat.dvd_one.mp hdvd] at hr
      simp at hr
    have : Nontrivial Y := by
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      have := Nat.card_pos (α := Y)
      omega
    have hp_prime : (Nat.minFac (Nat.card Y)).Prime := Nat.minFac_prime hY1
    set p := Nat.minFac (Nat.card Y) with hpdef
    have : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd : p ∣ Nat.card Y := Nat.minFac_dvd _
    by_cases hpπ : p ∈ π
    · -- minimal prime in `π`: all of `π(Y)` lies in `π`, so `O_π(Y) = ⊤` has index `1`.
      have hY_pi : Ch03.Subgroup.IsPiGroup π (⊤ : Subgroup Y) := by
        intro r hr
        have hr' : r ∈ (Nat.card Y).primeFactors := by
          rwa [Nat.card_congr (Subgroup.topEquiv (G := Y)).toEquiv] at hr
        exact hπ (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hr').two_le
          (Nat.dvd_of_mem_primeFactors hr')) hpπ
      have htop : Ch03.oPiCore π Y = ⊤ :=
        top_le_iff.mp (Ch03.Subgroup.IsPiGroup.le_oPiCore hY_pi)
      intro r hr
      exfalso
      rw [htop, Subgroup.index_top] at hr
      simp at hr
    · -- `p ∉ π`: peel the canonical normal `p`-complement `N` and recurse.
      obtain ⟨N, hN_normal, hN_compl⟩ :=
        hasNormalPComplement_minFac_of_rank_fitting_le_two (G := Y) hodd' hrank'
      have := hN_normal
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p Y))
      have hNidx : N.index = Nat.card ↥(P : Subgroup Y) := (hN_compl P).symm.index_eq_card
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
      -- `|N| < |Y| = n` (the Sylow `p`-subgroup is nontrivial).
      have hNcard_lt : Nat.card ↥N < n := by
        have hmul : Nat.card ↥N * N.index = Nat.card Y := Subgroup.card_mul_index N
        have hidx1 : 1 < N.index := by
          rw [hNidx]
          refine lt_of_lt_of_le hp_prime.one_lt (Nat.le_of_dvd Nat.card_pos ?_)
          rw [P.card_eq_multiplicity]
          exact dvd_pow_self p (hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd).ne'
        rw [← hcard, ← hmul]
        exact lt_mul_of_one_lt_right Nat.card_pos hidx1
      -- inductive Hall radical of `↥N`.
      have hNodd : Odd (Nat.card ↥N) := hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
      have hNrank : rank ↥(Ch01.fitting ↥N) ≤ 2 :=
        rank_fitting_le_two_of_normal_subgroup hrank'
      obtain ⟨hHallN_pi, hHallN_idx⟩ := IH (Nat.card ↥N) hNcard_lt ↥N rfl hNodd hNrank
      -- its image `HN` in `Y` is a normal Hall `π`-subgroup of `Y`.
      set HN : Subgroup Y := (Ch03.oPiCore π ↥N).map N.subtype with hHNdef
      have hHN_normal : HN.Normal := by rw [hHNdef]; infer_instance
      have hHN_card : Nat.card ↥HN = Nat.card ↥(Ch03.oPiCore π ↥N) := by
        rw [hHNdef, Subgroup.card_map_of_injective N.subtype_injective]
      have hHN_pi : ∀ r ∈ (Nat.card ↥HN).primeFactors, r ∈ π := by
        rw [hHN_card]; exact hHallN_pi
      have hHN_le_N : HN ≤ N := by rw [hHNdef]; exact Subgroup.map_subtype_le _
      have hHN_idx : ∀ r ∈ HN.index.primeFactors, r ∉ π := by
        have hrel : (HN.subgroupOf N).index * N.index = HN.index :=
          Subgroup.relIndex_mul_index hHN_le_N
        have hrel_eq : HN.subgroupOf N = Ch03.oPiCore π ↥N := by
          rw [hHNdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
        intro r hr
        obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
        rw [← hrel] at hr_dvd
        rcases hr_prime.dvd_mul.mp hr_dvd with h1 | h2
        · exact hHallN_idx r (Nat.mem_primeFactors.mpr ⟨hr_prime, hrel_eq ▸ h1,
            Subgroup.index_ne_zero_of_finite⟩)
        · -- `r ∣ N.index = |P| = p ^ k` forces `r = p ∉ π`.
          have hrp : r = p := by
            rw [hNidx, hk] at h2
            exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp
              (hr_prime.dvd_of_dvd_pow h2)
          exact hrp ▸ hpπ
      -- a normal `π`-subgroup lies in `O_π(Y)`; the Hall property bounds `O_π(Y)` back.
      have hHN_le_core : HN ≤ Ch03.oPiCore π Y :=
        Ch03.Subgroup.IsPiGroup.le_oPiCore hHN_pi
      have hcore_card_dvd : Nat.card ↥(Ch03.oPiCore π Y) ∣ Nat.card ↥HN :=
        Ch03.IsHallSubgroup.card_dvd_of_isPiGroup ⟨hHN_pi, hHN_idx⟩
          (fun r hr => Ch03.oPiCore.isPiGroup π r hr)
      have hcore_eq : HN = Ch03.oPiCore π Y :=
        Subgroup.eq_of_le_of_card_ge hHN_le_core (Nat.le_of_dvd Nat.card_pos hcore_card_dvd)
      rw [← hcore_eq]
      exact hHN_idx

end OddOrder.BG.Ch1.S05
