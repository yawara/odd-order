/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Isaacs Problems 6A.6 / 6A.11 — Lemma 6.5 の仮説 (TI 条件) をめぐる演習 (書籍 pp. 185-186)

Lemma 6.5 の仮説は **TI 条件** `A ⊓ A^g = 1` (`g ∉ A`) であり, そのとき
`X = notConjugateSet A` (`A` の非単位元に共役でない元全体) は `|X| = |G : A|` をみたす。

⚠ 書籍の Note のとおり, これらの問題では **Frobenius の定理 (`X` が部分群であること) は
使ってはならない**。以下の証明も使っていない。

## 6A.6

**主張**: `A > 1`, `B > 1` がともに `G` で Lemma 6.5 の仮説をみたすなら, ある `g ∈ G` で
`A ⊓ B^g > 1`。

**証明** (hint の `X`, `Y` を使う計数): もし全ての `g` で `A ⊓ B^g = 1` なら, `A` の非単位元は
`B` の非単位元と共役になれないので `X ∪ Y = G`。一方 `1 ∈ X ⊓ Y` なので
`|G| + 1 ≤ |X| + |Y| = |G:A| + |G:B| ≤ |G|/2 + |G|/2 = |G|` で矛盾。

## 6A.11

**主張**: `A ≤ G` が Lemma 6.5 の仮説をみたす ⟺ `A` の任意の非自明部分群 `T` について
`N_G(T) ⊆ A`。

**証明**:
* (⟹) `1 ≠ T ≤ A`, `g ∈ N_G(T)` なら `1 ≠ T ≤ A ⊓ A^g` なので TI から `g ∈ A`。
* (⟸) `D := A ⊓ A^g ≠ 1` とする。`1 ≠ T ≤ D` について `N_G(T) ≤ A` かつ
  (`g⁻¹Tg ≤ A` に仮説を使って) `N_G(T) ≤ A^g`, ゆえに **`N_G(T) ≤ D`**。
  素数 `p ∣ |D|` を取り, **`D` に含まれる `p`-部分群のうち極大なもの `P`** を取ると
  (Cauchy で非自明なものが存在), `P` は実は **`G` の Sylow `p`-部分群**: `P < S ∈ Syl_p(G)`
  なら `↥S` の冪零正規化条件で `y ∈ N_S(P) ∖ P` が取れ, `y ∈ N_G(P) ≤ D` ゆえ
  `P ⊔ ⟨y⟩ ≤ S ⊓ D` が `P` より大きい `D` 内 `p`-部分群になって極大性に矛盾。
  `P ≤ A` と `g⁻¹ • P ≤ A` はともに `G` の Sylow ゆえ `A` の Sylow `p`-部分群なので
  Sylow C (`exists_mem_smul_sylow_eq`) で `k ∈ A` があって `k • P = g⁻¹ • P`,
  つまり `g k ∈ N_G(P) ≤ A` ⟹ `g ∈ A`。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.6 / 6A.11: Lemma 6.5 の TI 仮説 (pp. 185-186) -/

variable {G : Type*} [Group G]

theorem one_mem_notConjugateSet (A : Subgroup G) : (1 : G) ∈ notConjugateSet A := by
  intro a ha hane hconj
  exact hane (by simpa using hconj)

/-- **Isaacs Problem 6A.6** (p. 185) ⭐: `A > 1`, `B > 1` がともに Lemma 6.5 の TI 仮説を
みたすなら, ある `g` で `A ⊓ B^g > 1`。 -/
theorem exists_inf_conj_ne_bot_of_TI [Finite G] {A B : Subgroup G}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hATI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥)
    (hBTI : ∀ g : G, g ∉ B → B ⊓ (MulAut.conj g • B) = ⊥) :
    ∃ g : G, A ⊓ (MulAut.conj g • B) ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  -- `X ∪ Y = G`: `x` が `A` の非単位元とも `B` の非単位元とも共役なら矛盾
  have hcover : notConjugateSet A ∪ notConjugateSet B = (Set.univ : Set G) := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_contra hx
    rw [Set.mem_union] at hx
    push Not at hx
    obtain ⟨hxA, hxB⟩ := hx
    simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hxA hxB
    obtain ⟨a, ha, hane, hcja⟩ := hxA
    obtain ⟨b, hb, hbne, hcjb⟩ := hxB
    -- `a` と `b` は共役: `a = h b h⁻¹`
    obtain ⟨h, hh⟩ := isConj_iff.mp (hcjb.trans hcja.symm)
    refine hane ?_
    have hmem : a ∈ A ⊓ (MulAut.conj h • B) := by
      refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change (MulAut.conj h).symm a ∈ B
      rw [MulAut.conj_symm_apply, ← hh]
      simpa [mul_assoc] using hb
    rw [hcon h, Subgroup.mem_bot] at hmem
    exact hmem
  -- `1 ∈ X ⊓ Y`
  have hone : (1 : G) ∈ notConjugateSet A ∩ notConjugateSet B :=
    ⟨one_mem_notConjugateSet A, one_mem_notConjugateSet B⟩
  -- 計数
  have hXcard : (notConjugateSet A).ncard = A.index := card_notConjugateSet_eq_index A hATI
  have hYcard : (notConjugateSet B).ncard = B.index := card_notConjugateSet_eq_index B hBTI
  have hunion := Set.ncard_union_add_ncard_inter (notConjugateSet A) (notConjugateSet B)
    (Set.toFinite _) (Set.toFinite _)
  rw [hcover, Set.ncard_univ, hXcard, hYcard] at hunion
  have hinter : 0 < (notConjugateSet A ∩ notConjugateSet B).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, hone⟩
  -- `|A| ≥ 2` から `2 · |G:A| ≤ |G|`, 同様に `B`
  have hcardA : 2 * A.index ≤ Nat.card G := by
    have hmul : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
    have h2 : 2 ≤ Nat.card ↥A := by
      rcases Nat.lt_or_ge (Nat.card ↥A) 2 with h | h
      · exact absurd (Subgroup.card_eq_one.mp (by
          have := Nat.card_pos (α := ↥A); omega)) hA
      · exact h
    calc 2 * A.index ≤ Nat.card ↥A * A.index := Nat.mul_le_mul_right _ h2
      _ = Nat.card G := hmul
  have hcardB : 2 * B.index ≤ Nat.card G := by
    have hmul : Nat.card ↥B * B.index = Nat.card G := Subgroup.card_mul_index B
    have h2 : 2 ≤ Nat.card ↥B := by
      rcases Nat.lt_or_ge (Nat.card ↥B) 2 with h | h
      · exact absurd (Subgroup.card_eq_one.mp (by
          have := Nat.card_pos (α := ↥B); omega)) hB
      · exact h
    calc 2 * B.index ≤ Nat.card ↥B * B.index := Nat.mul_le_mul_right _ h2
      _ = Nat.card G := hmul
  omega

/-! ### 6A.11: TI 仮説の正規化群による特徴づけ -/

/-- **6A.11 (⟹)**: TI 仮説をみたす `A` では, 非自明部分群の正規化群は `A` に含まれる。 -/
theorem normalizer_le_of_TI {A : Subgroup G}
    (hATI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥)
    {T : Subgroup G} (hT : T ≠ ⊥) (hTA : T ≤ A) :
    Subgroup.normalizer T ≤ A := by
  intro g hg
  by_contra hgA
  refine hT (le_antisymm ?_ bot_le)
  rw [← hATI g hgA]
  refine le_inf hTA fun x hx => ?_
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj g).symm x ∈ A
  rw [MulAut.conj_symm_apply]
  exact hTA (((Subgroup.mem_normalizer_iff''.mp hg) x).mp hx)

/-! ### 6A.11 (⟸): TI 仮説の十分性 -/

theorem conj_smul_eq_map (g : G) (K : Subgroup G) :
    MulAut.conj g • K = K.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- 共役による正規化群の移送: `N(g • T) = g • N(T)`。 -/
theorem normalizer_conj_smul (g : G) (T : Subgroup G) :
    Subgroup.normalizer ((MulAut.conj g • T : Subgroup G) : Set G)
      = MulAut.conj g • Subgroup.normalizer (T : Set G) := by
  rw [conj_smul_eq_map g T, conj_smul_eq_map g (Subgroup.normalizer T)]
  exact (Subgroup.map_equiv_normalizer_eq T (MulAut.conj g)).symm

theorem conj_inv_smul_smul (g : G) (K : Subgroup G) :
    MulAut.conj g⁻¹ • (MulAut.conj g • K) = K := by
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

theorem conj_smul_inv_smul (g : G) (K : Subgroup G) :
    MulAut.conj g • (MulAut.conj g⁻¹ • K) = K := by
  rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

/-- `P` が `G` の Sylow `p`-部分群で `P ≤ H`, `g • P ≤ H` なら, ある `k ∈ H` で `k • P = g • P`
(`↥H` での Sylow C を `map_conj_smul` で `G` に降ろす — Problem 1C.1 と同じ transport)。 -/
theorem exists_mem_smul_sylow_eq {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G)
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) {g : G}
    (hgPH : (↑(g • P) : Subgroup G) ≤ H) :
    ∃ k : G, k ∈ H ∧ (k • P : Sylow p G) = g • P := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥H) (P.subtype hPH) ((g • P).subtype hgPH)
  refine ⟨(k : G), k.2, ?_⟩
  have hAB : MulAut.conj (k : ↥H) • ((P : Subgroup G).subgroupOf H)
      = (MulAut.conj g • (P : Subgroup G)).subgroupOf H := by
    have h := congrArg (fun S : Sylow p ↥H => (S : Subgroup ↥H)) hk
    simpa only [Sylow.coe_subgroup_smul, Sylow.coe_subtype] using h
  apply Sylow.ext
  rw [Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul]
  have h := congrArg (Subgroup.map H.subtype) hAB
  rwa [Ch01.map_conj_smul, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr
      (by rw [Sylow.coe_subgroup_smul] at hgPH; exact hgPH),
    show (H.subtype k : G) = ↑k from rfl] at h

/-- **6A.11 (⟸)**: `A` の非自明部分群の正規化群がすべて `A` に含まれるなら, `A` は Lemma 6.5 の
TI 仮説をみたす。

`D := A ⊓ A^g ≠ 1` として (1) `1 ≠ T ≤ D` で `N_G(T) ≤ D`, (2) `D` に含まれる極大 `p`-部分群
`P` は `G` の Sylow `p`-部分群, (3) `P` と `g⁻¹ • P` に `A` の中での Sylow C を使う。 -/
theorem TI_of_normalizer_le [Finite G] {A : Subgroup G}
    (hnorm : ∀ T : Subgroup G, T ≠ ⊥ → T ≤ A → Subgroup.normalizer T ≤ A) :
    ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥ := by
  classical
  intro g hgA
  by_contra hD
  set D : Subgroup G := A ⊓ (MulAut.conj g • A) with hDdef
  -- (1) `1 ≠ T ≤ D` について `N_G(T) ≤ D`
  have hnormD : ∀ T : Subgroup G, T ≠ ⊥ → T ≤ D → Subgroup.normalizer T ≤ D := by
    intro T hTne hTD
    refine le_inf (hnorm T hTne (hTD.trans inf_le_left)) ?_
    have hTgA : T ≤ MulAut.conj g • A := hTD.trans inf_le_right
    have hT'A : MulAut.conj g⁻¹ • T ≤ A := by
      have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff
        (a := MulAut.conj g⁻¹)).mpr hTgA
      rwa [conj_inv_smul_smul] at h
    have hT'ne : (MulAut.conj g⁻¹ • T : Subgroup G) ≠ ⊥ := by
      intro h
      refine hTne ?_
      have h2 := congrArg (fun S : Subgroup G => MulAut.conj g • S) h
      rwa [conj_smul_inv_smul, Subgroup.smul_bot] at h2
    have h3 := hnorm _ hT'ne hT'A
    rw [normalizer_conj_smul] at h3
    have h4 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr h3
    rwa [conj_smul_inv_smul] at h4
  -- (2) `D` に含まれる極大 `p`-部分群は `G` の Sylow `p`-部分群
  have hDcard : Nat.card ↥D ≠ 1 := fun h => hD (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hDcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) p hpD
  have hxD : (x₀ : G) ∈ D := x₀.2
  have hxord : orderOf (x₀ : G) = p := by rw [Subgroup.orderOf_coe]; exact hx₀
  have hQ₀p : IsPGroup p (Subgroup.zpowers (x₀ : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxord, pow_one]
  have hQ₀D : Subgroup.zpowers (x₀ : G) ≤ D := Subgroup.zpowers_le.mpr hxD
  have hQ₀ne : Subgroup.zpowers (x₀ : G) ≠ ⊥ := by
    intro h
    have hx1 : (x₀ : G) ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at hx1
    rw [hx1, orderOf_one] at hxord
    exact hp.one_lt.ne' hxord.symm
  obtain ⟨P, hQP, hPmax⟩ := Finite.exists_le_maximal
    (p := fun K : Subgroup G => IsPGroup p K ∧ K ≤ D) ⟨hQ₀p, hQ₀D⟩
  have hPp : IsPGroup p P := hPmax.1.1
  have hPD : P ≤ D := hPmax.1.2
  have hPne : P ≠ ⊥ := fun h => hQ₀ne (le_bot_iff.mp (h ▸ hQP))
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hPeq : P = (S : Subgroup G) := by
    by_contra hne
    have hlt : P < (S : Subgroup G) := lt_of_le_of_ne hPS hne
    haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
    have hlt2 : P.subgroupOf (S : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact fun h => hlt.ne (le_antisymm hPS h)
    have hgrow := Group.normalizerCondition_of_isNilpotent _ hlt2
    rw [← Subgroup.subgroupOf_normalizer_eq hPS] at hgrow
    obtain ⟨y0, hy0mem, hy0notin⟩ := SetLike.exists_of_lt hgrow
    have hyN : (y0 : G) ∈ Subgroup.normalizer P := Subgroup.mem_subgroupOf.mp hy0mem
    have hyS : (y0 : G) ∈ (S : Subgroup G) := y0.2
    have hynotP : (y0 : G) ∉ P := fun h => hy0notin (Subgroup.mem_subgroupOf.mpr h)
    have hyD : (y0 : G) ∈ D := hnormD P hPne hPD hyN
    have hP'S : P ⊔ Subgroup.zpowers (y0 : G) ≤ (S : Subgroup G) :=
      sup_le hPS (Subgroup.zpowers_le.mpr hyS)
    have hP'le := hPmax.2 ⟨S.isPGroup'.to_le hP'S,
      sup_le hPD (Subgroup.zpowers_le.mpr hyD)⟩ le_sup_left
    exact hynotP (hP'le ((le_sup_right : Subgroup.zpowers (y0 : G) ≤ _)
      (Subgroup.mem_zpowers _)))
  -- (3) `S` と `g⁻¹ • S` はともに `A` に含まれる `G` の Sylow `p`-部分群 ⟹ Sylow C
  have hSne : (S : Subgroup G) ≠ ⊥ := hPeq ▸ hPne
  have hSA : (S : Subgroup G) ≤ A := hPeq ▸ (hPD.trans inf_le_left)
  have hSgA : (↑((g⁻¹ : G) • S) : Subgroup G) ≤ A := by
    rw [Sylow.coe_subgroup_smul, ← hPeq]
    have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr
      (hPD.trans inf_le_right)
    rwa [conj_inv_smul_smul] at h
  obtain ⟨k, hkA, hkeq⟩ := exists_mem_smul_sylow_eq S hSA hSgA
  have hgk : (g * k) • S = S := by rw [mul_smul, hkeq, smul_inv_smul]
  have hgkN : g * k ∈ Subgroup.normalizer (S : Subgroup G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hgk
  have hgkA : g * k ∈ A := hnorm _ hSne hSA hgkN
  exact hgA (by simpa using A.mul_mem hgkA (A.inv_mem hkA))

/-- **Isaacs Problem 6A.11** (p. 186) ⭐: `A ≤ G` が Lemma 6.5 の TI 仮説をみたすことと,
`A` の任意の非自明部分群 `T` について `N_G(T) ⊆ A` となることは同値。 -/
theorem TI_iff_forall_normalizer_le [Finite G] (A : Subgroup G) :
    (∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) ↔
      ∀ T : Subgroup G, T ≠ ⊥ → T ≤ A → Subgroup.normalizer T ≤ A :=
  ⟨fun hTI _ hT hTA => normalizer_le_of_TI hTI hT hTA, TI_of_normalizer_le⟩

end

end OddOrder.Isaacs.Ch06
