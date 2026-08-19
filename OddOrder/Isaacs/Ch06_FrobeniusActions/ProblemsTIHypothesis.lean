/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch05_Transfer.Basic
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Isaacs Problems 6A.6 / 6A.7 / 6A.11 — Lemma 6.5 の仮説 (TI 条件) の演習 (書籍 pp. 185-186)

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

## 6A.7

**主張**: `A` が `G` で Lemma 6.5 の仮説をみたし `A ⊆ H ⊆ G` のとき, (a) `A^g ⊓ H > 1` なら
`g ∈ H`; (b) `H ⊴ G` なら `H = G` (⚠ (b) は `A > 1` が要る)。

**証明** (hint どおり): `A` と `A^g ⊓ H` はともに **`H` の中で** TI 仮説をみたす
(`TI_subgroupOf_of_TI` / `TI_subgroupOf_conj_of_TI`) ので **6A.6** を `↥H` で使うと
`k ∈ H` で `A ⊓ (A^g)^k > 1`, すなわち `A ⊓ A^{kg} > 1` ⟹ TI から `k g ∈ A ⊆ H` ⟹ `g ∈ H`。
(b) は `H ⊴ G` なら `A^g ≤ H` なので `A^g ⊓ H = A^g ≠ 1` に (a) を使う。

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
    simp only [notConjugateSet, Set.mem_ofPred_eq, not_forall, not_not] at hxA hxB
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
  have : Fact p.Prime := ⟨hp⟩
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
    have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
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

/-! ### 6A.7: `A ≤ H ≤ G` での TI 仮説 -/

/-- 共役は `subgroupOf` と交換する (`k ∈ H` のとき)。 -/
theorem conj_smul_subgroupOf {H : Subgroup G} (k : ↥H) (A : Subgroup G) :
    MulAut.conj k • (A.subgroupOf H) = (MulAut.conj (k : G) • A).subgroupOf H := by
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Ch01.map_conj_smul, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    show (H.subtype k : G) = (k : G) from rfl, Subgroup.smul_inf,
    Subgroup.conj_smul_eq_self_of_mem k.2]

/-- TI 仮説は中間群 `H` に遺伝する (`A` そのもの)。 -/
theorem TI_subgroupOf_of_TI {A H : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) (k : ↥H)
    (hk : k ∉ A.subgroupOf H) :
    (A.subgroupOf H) ⊓ (MulAut.conj k • (A.subgroupOf H)) = ⊥ := by
  rw [conj_smul_subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
    hATI (k : G) (by rwa [Subgroup.mem_subgroupOf] at hk)]
  simp

/-- TI 仮説は中間群 `H` に遺伝する (`A` の共役 `A^g` の側)。 -/
theorem TI_subgroupOf_conj_of_TI {A H : Subgroup G} {g : G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) (k : ↥H)
    (hk : k ∉ (MulAut.conj g • A).subgroupOf H) :
    ((MulAut.conj g • A).subgroupOf H) ⊓
      (MulAut.conj k • ((MulAut.conj g • A).subgroupOf H)) = ⊥ := by
  have hkA : g⁻¹ * (k : G) * g ∉ A := by
    intro h
    refine hk ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm (k : G) ∈ A
    rwa [MulAut.conj_symm_apply]
  have hstep : (MulAut.conj g • A) ⊓ (MulAut.conj ((k : G) * g) • A)
      = MulAut.conj g • (A ⊓ MulAut.conj (g⁻¹ * (k : G) * g) • A) := by
    rw [Subgroup.smul_inf, ← mul_smul, ← map_mul]
    congr 2
    group
  rw [conj_smul_subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
    ← mul_smul, ← map_mul, hstep, hATI _ hkA, Subgroup.smul_bot]
  simp

/-- **Isaacs Problem 6A.7(a)** (p. 186) ⭐: `A` が `G` で Lemma 6.5 の TI 仮説をみたし
`A ≤ H ≤ G` のとき, `A^g ⊓ H > 1` なら `g ∈ H`。

hint どおり `A` と `A^g ⊓ H` がともに `H` の中で TI 仮説をみたすことを見て **6A.6** を `H` で使う。 -/
theorem mem_of_conj_inf_ne_bot [Finite G] {A H : Subgroup G} (hAH : A ≤ H)
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {g : G} (hne : (MulAut.conj g • A) ⊓ H ≠ ⊥) : g ∈ H := by
  classical
  -- `A' := A.subgroupOf H`, `B' := (A^g).subgroupOf H` はともに `↥H` で非自明かつ TI
  have hBne : ((MulAut.conj g • A).subgroupOf H) ≠ ⊥ := by
    intro h
    refine hne ?_
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at this
  have hAgne : (MulAut.conj g • A : Subgroup G) ≠ ⊥ := by
    intro h
    exact hBne (by rw [h]; simp [Subgroup.subgroupOf])
  have hAne : A ≠ ⊥ := by
    intro h
    exact hAgne (by rw [h, Subgroup.smul_bot])
  have hA'ne : (A.subgroupOf H) ≠ ⊥ := by
    intro h
    refine hAne (le_antisymm (fun x hx => ?_) bot_le)
    have hxH : x ∈ H := hAH hx
    have : (⟨x, hxH⟩ : ↥H) ∈ A.subgroupOf H := hx
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  obtain ⟨k, hk⟩ := exists_inf_conj_ne_bot_of_TI (G := ↥H) hA'ne hBne
    (fun x hx => TI_subgroupOf_of_TI hATI x hx)
    (fun x hx => TI_subgroupOf_conj_of_TI hATI x hx)
  -- `A ⊓ A^{kg} ≠ ⊥` から TI で `k g ∈ A ≤ H`
  have hkey : A ⊓ (MulAut.conj ((k : G) * g) • A) ≠ ⊥ := by
    intro h
    refine hk ?_
    rw [conj_smul_subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
      ← mul_smul, ← map_mul, h]
    simp
  have hmem : (k : G) * g ∈ A := by
    by_contra hnotmem
    exact hkey (hATI _ hnotmem)
  have : (k : G)⁻¹ * ((k : G) * g) ∈ H := H.mul_mem (H.inv_mem k.2) (hAH hmem)
  simpa using this

/-- **Isaacs Problem 6A.7(b)** (p. 186): `A > 1` が TI 仮説をみたし `A ≤ H ⊴ G` なら `H = G`。

⚠ `A ≠ ⊥` は書籍では Lemma 6.5 の文脈から暗黙 (`A = 1` なら任意の正規部分群が反例)。 -/
theorem eq_top_of_normal_of_TI [Finite G] {A H : Subgroup G} (hAne : A ≠ ⊥) (hAH : A ≤ H)
    [H.Normal] (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) : H = ⊤ := by
  refine le_antisymm le_top fun g _ => ?_
  refine mem_of_conj_inf_ne_bot hAH hATI (g := g) ?_
  -- `A^g ≤ H^g = H` なので `A^g ⊓ H = A^g ≠ ⊥`
  have hsub : (MulAut.conj g • A : Subgroup G) ≤ H := by
    have h1 : (MulAut.conj g • A : Subgroup G) ≤ MulAut.conj g • H :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hAH
    rwa [Subgroup.Normal.conj_smul_eq_self g H] at h1
  rw [inf_eq_left.mpr hsub]
  intro h
  refine hAne ?_
  have hb := congrArg (fun S : Subgroup G => MulAut.conj g⁻¹ • S) h
  rwa [conj_inv_smul_smul, Subgroup.smul_bot] at hb

/-- **Isaacs Problem 6A.10(a) の前半** (p. 186): TI 仮説の下で, `A` に含まれる極大な
`p`-部分群 `P` (≠ 1) は `G` の Sylow `p`-部分群である。

`P < S ∈ Syl_p(G)` なら `↥S` の冪零正規化条件で `y ∈ N_S(P) ∖ P` が取れ, 6A.11 から
`y ∈ N_G(P) ≤ A` なので `P ⊔ ⟨y⟩ ≤ A ⊓ S` が `P` より大きい `A` 内の `p`-部分群になり
極大性に矛盾。 -/
theorem exists_sylow_coe_eq_of_maximal_pGroup_of_TI [Finite G] {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hPmax : Maximal (fun K : Subgroup G => IsPGroup p ↥K ∧ K ≤ A) P) (hPne : P ≠ ⊥) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  classical
  obtain ⟨S, hPS⟩ := hPmax.1.1.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : P < (S : Subgroup G) := lt_of_le_of_ne hPS (fun h => hne h.symm)
  have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt2 : P.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hlt.ne (le_antisymm hPS h)
  have hgrow := Group.normalizerCondition_of_isNilpotent _ hlt2
  rw [← Subgroup.subgroupOf_normalizer_eq hPS] at hgrow
  obtain ⟨y0, hy0mem, hy0notin⟩ := SetLike.exists_of_lt hgrow
  have hyN : (y0 : G) ∈ Subgroup.normalizer P := Subgroup.mem_subgroupOf.mp hy0mem
  have hyS : (y0 : G) ∈ (S : Subgroup G) := y0.2
  have hynotP : (y0 : G) ∉ P := fun h => hy0notin (Subgroup.mem_subgroupOf.mpr h)
  have hyA : (y0 : G) ∈ A := normalizer_le_of_TI hATI hPne hPmax.1.2 hyN
  have hP'S : P ⊔ Subgroup.zpowers (y0 : G) ≤ (S : Subgroup G) :=
    sup_le hPS (Subgroup.zpowers_le.mpr hyS)
  have hP'le := hPmax.2 ⟨S.isPGroup'.to_le hP'S,
    sup_le hPmax.1.2 (Subgroup.zpowers_le.mpr hyA)⟩ le_sup_left
  exact hynotP (hP'le ((le_sup_right : Subgroup.zpowers (y0 : G) ≤ _)
    (Subgroup.mem_zpowers _)))

/-- **Isaacs Problem 6A.10(b) の前半** (p. 186): `A > 1` が Lemma 6.5 の TI 仮説をみたすなら
`G' A = G`。

`G'` を含む部分群は正規なので **6A.7(b)** (`eq_top_of_normal_of_TI`) が直ちに使える。 -/
theorem commutator_sup_eq_top_of_TI [Finite G] {A : Subgroup G} (hAne : A ≠ ⊥)
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) :
    commutator G ⊔ A = ⊤ := by
  have hnorm : (commutator G ⊔ A).Normal := by
    constructor
    intro h hh g
    have hc : g * h * g⁻¹ * h⁻¹ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
    have heq : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
    rw [heq]
    exact Subgroup.mul_mem _ ((le_sup_left : commutator G ≤ commutator G ⊔ A) hc) hh
  exact eq_top_of_normal_of_TI hAne (le_sup_right : A ≤ commutator G ⊔ A) hATI

/-- **Isaacs Problem 6A.10(a) の後半** (p. 186): TI 仮説の下で `A` は `A` の**任意の**部分群に
おける `G`-fusion を制御する (とくに (a) の Sylow `p`-部分群 `P` において)。

`1 ≠ x ∈ H ≤ A` が `g x g⁻¹ = y ∈ A` なら `conj_mem_iff_of_TI` から `g ∈ A` 自身が
共役元として使える。 -/
theorem controlsFusionIn_of_TI {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {H : Subgroup G} (hHA : H ≤ A) : A.ControlsFusionIn H := by
  rintro x y hx hy ⟨g, hg⟩
  rcases eq_or_ne x 1 with rfl | hxne
  · exact ⟨1, A.one_mem, by simpa using hg⟩
  refine ⟨g, ?_, hg⟩
  by_contra hgA
  have hmem : y ∈ A ⊓ (MulAut.conj g • A) := by
    refine Subgroup.mem_inf.mpr ⟨hHA hy, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm y ∈ A
    rw [MulAut.conj_symm_apply, ← hg]
    simpa [mul_assoc] using hHA hx
  rw [hATI g hgA, Subgroup.mem_bot] at hmem
  refine hxne ?_
  rw [hmem] at hg
  have h2 := congrArg (fun z : G => g⁻¹ * z * g) hg
  simpa [mul_assoc] using h2

/-- **Isaacs Problem 6A.10(b) 後半の易しい向き**: `A' ≤ G' ⊓ A`
(TI 仮説なしに成り立つ; 逆向き `G' ⊓ A ≤ A'` は fusion 制御 (a) と focal subgroup が要る)。 -/
theorem commutator_self_le_inf_commutator (A : Subgroup G) :
    ⁅A, A⁆ ≤ commutator G ⊓ A :=
  le_inf (Subgroup.commutator_mono le_top le_top)
    (Subgroup.commutator_le.mpr fun _ ha _ hb =>
      A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb))

/-- 有限群 `H` の部分群 `K` が, どの素数 `p` についても `H` の Sylow `p`-部分群をすべて含むなら
`K = ⊤`。

「有限群は Sylow 部分群たちで生成される」の指数版: `p ∣ |H : K|` なら `p` の全 multiplicity が
`|K|` を割ることと合わせて `p^(n+1) ∣ |H|` となり, `n = (|H|).factorization p` の最大性に反する。 -/
theorem eq_top_of_forall_sylow_le {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (hK : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p H), (P : Subgroup H) ≤ K) : K = ⊤ := by
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have hfp : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  have hcard : Nat.card ↥(P : Subgroup H) = p ^ (Nat.card H).factorization p :=
    P.card_eq_multiplicity
  have h1 : Nat.card ↥(P : Subgroup H) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le (hK p hfp P)
  have h2 : Nat.card ↥K * K.index = Nat.card H := Subgroup.card_mul_index K
  have h1' : p ^ (Nat.card H).factorization p ∣ Nat.card ↥K := by rw [← hcard]; exact h1
  have h3 : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card ↥K * K.index := by
    rw [pow_succ]; exact mul_dvd_mul h1' hdvd
  rw [h2, Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne'] at h3
  omega

/-- `↥A` の交換子群を `G` へ押し出すと `⁅A, A⁆`。 -/
theorem map_commutator_subtype (A : Subgroup G) :
    (commutator ↥A).map A.subtype = ⁅A, A⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, A.range_subtype]

/-- **Isaacs Problem 6A.10(b) の後半** (p. 186): TI 仮説の下で `G' ⊓ A ≤ A'`。

**証明**: `H := G' ⊓ A` の各 Sylow `p`-部分群 `Q` を取る。`Q ≤ A` なので `Q` を含む `↥A` の
Sylow `p`-部分群 `S` があり, (a) 前半 (`exists_sylow_coe_eq_of_maximal_pGroup_of_TI`) から
`P := S` は `G` の Sylow `p`-部分群でもある。焦点部分群定理 (Isaacs Thm 5.21) で
`Q ≤ G' ⊓ P = P.focalSubgroup` であり, (a) 後半の fusion 制御
(`controlsFusionIn_of_TI`) で `P.focalSubgroup` は `↥A` の中で計算した焦点部分群の像に等しい。
後者は `A' ⊓ S ≤ A'` に含まれる。ゆえに全ての Sylow が `A'` に入り, 上の指数論法で
`H ≤ A'`。 -/
theorem commutator_inf_le_commutator_self_of_TI [Finite G] {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) :
    commutator G ⊓ A ≤ ⁅A, A⁆ := by
  classical
  have hkey : (⁅A, A⁆).subgroupOf (commutator G ⊓ A) = ⊤ := by
    refine eq_top_of_forall_sylow_le fun p hfp Q => ?_
    -- `Q` を `G` の部分群として見る
    have hQ'A : (Q : Subgroup ↥(commutator G ⊓ A)).map (commutator G ⊓ A).subtype ≤ A := by
      rintro _ ⟨z, _, rfl⟩; exact z.2.2
    have hQ'C : (Q : Subgroup ↥(commutator G ⊓ A)).map (commutator G ⊓ A).subtype
        ≤ commutator G := by
      rintro _ ⟨z, _, rfl⟩; exact z.2.1
    have hQ'p : IsPGroup p ↥((Q : Subgroup ↥(commutator G ⊓ A)).map
        (commutator G ⊓ A).subtype) :=
      IsPGroup.of_equiv Q.isPGroup'
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective (commutator G ⊓ A)))
    have hQAp : IsPGroup p ↥(((Q : Subgroup ↥(commutator G ⊓ A)).map
        (commutator G ⊓ A).subtype).subgroupOf A) :=
      IsPGroup.of_equiv hQ'p (Subgroup.subgroupOfEquivOfLe hQ'A).symm
    obtain ⟨S, hS⟩ := hQAp.exists_le_sylow
    intro q hq
    have hq' : (q : G) ∈ (Q : Subgroup ↥(commutator G ⊓ A)).map
        (commutator G ⊓ A).subtype := ⟨q, hq, rfl⟩
    have hqS : (⟨(q : G), hQ'A hq'⟩ : ↥A) ∈ (S : Subgroup ↥A) := hS hq'
    rcases eq_or_ne (S : Subgroup ↥A) ⊥ with hSbot | hSne
    · rw [hSbot, Subgroup.mem_bot] at hqS
      have : (q : G) = 1 := congrArg Subtype.val hqS
      change (q : G) ∈ ⁅A, A⁆
      rw [this]; exact one_mem _
    -- `P := S` を `G` の部分群として見ると `G` の Sylow `p`-部分群
    have hPA : (S : Subgroup ↥A).map A.subtype ≤ A := by
      rintro _ ⟨z, _, rfl⟩; exact z.2
    have hPcomap : ((S : Subgroup ↥A).map A.subtype).subgroupOf A = (S : Subgroup ↥A) :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective A) _
    have hPne : (S : Subgroup ↥A).map A.subtype ≠ ⊥ := by
      intro h
      exact hSne (by rw [← hPcomap, h]; simp [Subgroup.subgroupOf])
    have hPmax : Maximal (fun K : Subgroup G => IsPGroup p ↥K ∧ K ≤ A)
        ((S : Subgroup ↥A).map A.subtype) := by
      refine ⟨⟨IsPGroup.of_equiv S.isPGroup'
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective A)), hPA⟩, ?_⟩
      rintro K ⟨hKp, hKA⟩ hPK x hx
      have hKAp : IsPGroup p ↥(K.subgroupOf A) :=
        IsPGroup.of_equiv hKp (Subgroup.subgroupOfEquivOfLe hKA).symm
      have hSK : (S : Subgroup ↥A) ≤ K.subgroupOf A := fun z hz => hPK ⟨z, hz, rfl⟩
      have heq : K.subgroupOf A = (S : Subgroup ↥A) := S.3 hKAp hSK
      exact ⟨⟨x, hKA hx⟩, heq ▸ (show (⟨x, hKA hx⟩ : ↥A) ∈ K.subgroupOf A from hx), rfl⟩
    obtain ⟨T, hT⟩ := exists_sylow_coe_eq_of_maximal_pGroup_of_TI hATI hPmax hPne
    -- 焦点部分群定理 + fusion 制御
    have hqfoc : (q : G) ∈ ((S : Subgroup ↥A).map A.subtype).focalSubgroup := by
      rw [← hT, ← Subgroup.commutator_inf_eq_focalSubgroup T, hT]
      exact ⟨hQ'C hq', ⟨_, hqS, rfl⟩⟩
    rw [← Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn hPA
      (controlsFusionIn_of_TI hATI hPA), hPcomap] at hqfoc
    obtain ⟨z, hz, hzq⟩ := hqfoc
    rw [← Subgroup.commutator_inf_eq_focalSubgroup S] at hz
    change (q : G) ∈ ⁅A, A⁆
    rw [← hzq, ← map_commutator_subtype A]
    exact ⟨z, hz.1, rfl⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥(commutator G ⊓ A)) ∈ (⁅A, A⁆).subgroupOf (commutator G ⊓ A) := by
    rw [hkey]; trivial
  exact hmem

/-- **Isaacs Problem 6A.10(b)** (p. 186) ⭐: TI 仮説の下で `G' ⊓ A = A'`。 -/
theorem inf_commutator_eq_commutator_self_of_TI [Finite G] {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥) :
    commutator G ⊓ A = ⁅A, A⁆ :=
  le_antisymm (commutator_inf_le_commutator_self_of_TI hATI)
    (commutator_self_le_inf_commutator A)

end

end OddOrder.Isaacs.Ch06
