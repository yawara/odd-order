/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# Isaacs Ch. 9 — §9B: nilpotent residual `S^∞`, Lemma 9.15, Corollary 9.16 (pp. 279–281)

Wielandt automorphism tower theorem (Thm 9.10) に向けた §9B 前半の下部構造.

- `nilpotentResidual S` = **`S^∞`** (Isaacs p. 279): ambient lower central series
  `S.lowerCentralSeries n` の全項の交わり. 有限群では antitone 列が安定するので
  final term に一致し (`exists_lowerCentralSeries_eq_nilpotentResidual`),
  「商を nilpotent にする最小の正規部分群」を与える
  (`nilpotentResidual_le_iff_isNilpotent_map`).
- **Lemma 9.15** (`nilpotentResidual_top_eq_of_isSubnormal_sup_nilpotent`):
  `G = SF`, `S ◁◁ G`, `F ◁ G`, `F` nilpotent ⇒ `G^∞ = S^∞`.
  相対形 `nilpotentResidual_sup_eq_of_isSubnormal` (`(S ⊔ F)^∞ = S^∞`) も提供.
- **Corollary 9.16** (`fitting_le_normalizer_nilpotentResidual`):
  `S ◁◁ G` ⇒ `F(G) ≤ N_G(S^∞)`.

## 実装ノート

- 書籍の `S^∞` は「`S/N` が nilpotent となる最小の `N ◁ S`」(lower central series の
  final term). mathlib v4.30 系の ambient-valued
  `Subgroup.lowerCentralSeries : Subgroup G → ℕ → Subgroup G` の上で `⨅ n` として
  定義すると, Isaacs の部分群レベルの操作 (9.15 の `M = S(F ∩ M)` 等) が型を跨がずに
  書ける. `↥S` 側の定義との一致は `map_nilpotentResidual` (有限性から系列が安定する
  ため, 単射に限らず任意の準同型で `map` と可換) が保証する.
- 9.15 の帰納法は Components.lean の Thm 9.4 と同じ「`Nat.card G ≤ n` の `n` で帰納,
  `∀ G` を内側に量化」パターン. proper normal `M ⊇ S` の存在は mathlib
  `IsSubnormal.exists_normal_and_le_and_lt_top_of_ne`.
- ⚠ mmd 抽出 (L5069, L5075) は 9.15/9.16 の仮定を `S ◁ G` と誤抽出しているが,
  PDF 原文 (p. 280) は `S ◁◁ G` (subnormal). 本ファイルは PDF に従う.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

universe u

variable {G : Type*} [Group G]

section /- 9B: nilpotent residual S^∞ の定義と基本 API (p. 279) -/

/-- **Nilpotent residual** `S^∞` (Isaacs p. 279): lower central series の全項の交わり
(ambient `Subgroup G` 値). 有限群では final term に一致する
(`exists_lowerCentralSeries_eq_nilpotentResidual`). -/
def nilpotentResidual (S : Subgroup G) : Subgroup G :=
  ⨅ n, S.lowerCentralSeries n

theorem nilpotentResidual_le_lowerCentralSeries (S : Subgroup G) (n : ℕ) :
    nilpotentResidual S ≤ S.lowerCentralSeries n :=
  iInf_le _ n

theorem nilpotentResidual_le (S : Subgroup G) : nilpotentResidual S ≤ S :=
  nilpotentResidual_le_lowerCentralSeries S 0

theorem nilpotentResidual_mono {S T : Subgroup G} (h : S ≤ T) :
    nilpotentResidual S ≤ nilpotentResidual T :=
  le_iInf fun n => (nilpotentResidual_le_lowerCentralSeries S n).trans
    (Subgroup.lowerCentralSeries_mono n h)

/-- `S` は `S^∞` を正規化する (各 `S.lowerCentralSeries n` を正規化するから). -/
theorem le_normalizer_nilpotentResidual (S : Subgroup G) :
    S ≤ Subgroup.normalizer (nilpotentResidual S : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [nilpotentResidual, Subgroup.mem_iInf]
  exact forall_congr' fun n =>
    Subgroup.mem_normalizer_iff.mp (S.self_le_normalizer_lowerCentralSeries n hx) h

instance nilpotentResidual.characteristic (S : Subgroup G) [S.Characteristic] :
    (nilpotentResidual S).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  rw [nilpotentResidual, Subgroup.comap_iInf]
  exact iInf_congr fun n => Subgroup.characteristic_iff_comap_eq.mp inferInstance φ

/-- `S ◁ G` ならば各 `S.lowerCentralSeries n ◁ G` (正規部分群同士の交換子は正規). -/
theorem lowerCentralSeries_normal (S : Subgroup G) [hS : S.Normal] (n : ℕ) :
    (S.lowerCentralSeries n).Normal := by
  induction n with
  | zero => exact hS
  | succ d hd =>
    rw [Subgroup.lowerCentralSeries_succ]
    haveI := hd
    infer_instance

instance nilpotentResidual.normal (S : Subgroup G) [S.Normal] :
    (nilpotentResidual S).Normal :=
  Subgroup.normal_iInf_normal fun n => lowerCentralSeries_normal S n

/-- 有限部分群の包含は card の逆包含と併せて等号 (mathlib 不在の小補題;
`Subgroup.eq_top_of_le_card` の相対版). -/
theorem eq_of_le_of_card_le {H K : Subgroup G} [Finite K] (hle : H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) : H = K := by
  have h1 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 : H.subgroupOf K = ⊤ :=
    Subgroup.eq_top_of_le_card _ (h1.symm ▸ hcard)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h2)

/-- 有限群では lower central series は安定し, `S^∞` は final term に一致する. -/
theorem exists_lowerCentralSeries_eq_nilpotentResidual [Finite G] (S : Subgroup G) :
    ∃ n, S.lowerCentralSeries n = nilpotentResidual S := by
  obtain ⟨n, hn⟩ := Nat.sInf_mem
    (s := Set.range fun n => Nat.card (S.lowerCentralSeries n)) ⟨_, 0, rfl⟩
  refine ⟨n, le_antisymm (le_iInf fun m => ?_) (iInf_le _ n)⟩
  rcases le_total m n with hmn | hnm
  · exact S.lowerCentralSeries_antitone hmn
  · exact (eq_of_le_of_card_le (S.lowerCentralSeries_antitone hnm)
      (hn.le.trans (Nat.sInf_le ⟨m, rfl⟩))).ge

/-- `S^∞` は任意の準同型の像と可換 (有限性から系列が安定するため, 単射性不要). -/
theorem map_nilpotentResidual [Finite G] {K : Type*} [Group K] (f : G →* K)
    (S : Subgroup G) :
    (nilpotentResidual S).map f = nilpotentResidual (S.map f) := by
  obtain ⟨n, hn⟩ := exists_lowerCentralSeries_eq_nilpotentResidual S
  refine le_antisymm (le_iInf fun m => ?_) ?_
  · rw [← S.map_lowerCentralSeries f m]
    exact Subgroup.map_mono (iInf_le _ m)
  · calc nilpotentResidual (S.map f)
        ≤ (S.map f).lowerCentralSeries n := iInf_le _ n
      _ = (S.lowerCentralSeries n).map f := (S.map_lowerCentralSeries f n).symm
      _ = (nilpotentResidual S).map f := by rw [hn]

/-- `↥M` 内で計算した `(⊤)^∞` を `M.subtype` で押すと ambient の `M^∞`. -/
theorem map_subtype_nilpotentResidual_top [Finite G] (M : Subgroup G) :
    (nilpotentResidual (⊤ : Subgroup ↥M)).map M.subtype = nilpotentResidual M := by
  rw [map_nilpotentResidual, ← MonoidHom.range_eq_map, Subgroup.subtype_range]

/-- `↥M` 内で計算した `(S.subgroupOf M)^∞` を `M.subtype` で押すと ambient の `S^∞`
(`S ≤ M` のとき). -/
theorem map_subtype_nilpotentResidual_subgroupOf [Finite G] {S M : Subgroup G}
    (h : S ≤ M) :
    (nilpotentResidual (S.subgroupOf M)).map M.subtype = nilpotentResidual S := by
  rw [map_nilpotentResidual, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h]

/-- `S^∞ ≤ N` ⟺ `S` の `G ⧸ N` での像が nilpotent (`N ◁ G`, 有限群).
「`S^∞` は商を nilpotent にする最小の正規部分群」の形式化. -/
theorem nilpotentResidual_le_iff_isNilpotent_map [Finite G] {S N : Subgroup G}
    [N.Normal] :
    nilpotentResidual S ≤ N ↔ Group.IsNilpotent (S.map (QuotientGroup.mk' N)) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_lowerCentralSeries_eq_nilpotentResidual S
    refine (Subgroup.isNilpotent_iff_lowerCentralSeries _).mpr ⟨n, ?_⟩
    rw [← S.map_lowerCentralSeries, hn, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h
  · intro h
    obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries _).mp h
    rw [← S.map_lowerCentralSeries, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hn
    exact (iInf_le _ n).trans hn

theorem nilpotentResidual_eq_bot_iff [Finite G] {S : Subgroup G} :
    nilpotentResidual S = ⊥ ↔ Group.IsNilpotent S := by
  rw [Subgroup.isNilpotent_iff_lowerCentralSeries]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_lowerCentralSeries_eq_nilpotentResidual S
    exact ⟨n, hn.trans h⟩
  · rintro ⟨n, hn⟩
    exact le_bot_iff.mp ((iInf_le _ n).trans_eq hn)

/-- nilpotent 部分群の像は nilpotent (lower central series の像で直接; 有限性不要). -/
theorem isNilpotent_map {K : Type*} [Group K] (f : G →* K) {S : Subgroup G}
    (h : Group.IsNilpotent S) : Group.IsNilpotent (S.map f) := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries S).mp h
  exact (Subgroup.isNilpotent_iff_lowerCentralSeries _).mpr
    ⟨n, by rw [← S.map_lowerCentralSeries, hn, Subgroup.map_bot]⟩

end

section /- 9B: Lemma 9.15 と Corollary 9.16 (pp. 280-281) -/

/-- **Dedekind / modular law** (正規側が外の summand の変種): `S ≤ M`, `F ◁ G` ⇒
`M ⊓ (S ⊔ F) = S ⊔ (F ⊓ M)`.

`OddOrder.Mathlib` の `inf_sup_eq_sup_inf_of_normal_of_le` は正規部分群が `≤ M` 側の
変種で, ここでは外側 summand `F` が正規 (mathlib の `IsModularLattice (Subgroup G)`
instance は `CommGroup` 限定なので order 版 `sup_inf_assoc_of_le` は使えない). -/
theorem inf_sup_eq_sup_inf_of_le_of_normal {S F M : Subgroup G} [F.Normal]
    (hSM : S ≤ M) :
    M ⊓ (S ⊔ F) = S ⊔ F ⊓ M := by
  apply le_antisymm
  · rintro x ⟨hxM, hxSF⟩
    obtain ⟨s, hs, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxSF
    have hfM : f ∈ M := by
      have : s⁻¹ * (s * f) ∈ M := M.mul_mem (M.inv_mem (hSM hs)) hxM
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem_sup hs ⟨hf, hfM⟩
  · exact le_inf (sup_le hSM inf_le_right) (sup_le_sup_left inf_le_left S)

/-- Lemma 9.15 の帰納核: `Nat.card G ≤ n` の有限群で `S ◁◁ G`, `F ◁ G` nilpotent,
`S ⊔ F = ⊤` ⇒ `G^∞ = S^∞`. `∀ G` を内側に量化して `n` で帰納 (Thm 9.4 と同型). -/
private theorem nilpotentResidual_top_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      ∀ {S F : Subgroup G}, S.IsSubnormal → F.Normal → Group.IsNilpotent F →
        S ⊔ F = ⊤ → nilpotentResidual (⊤ : Subgroup G) = nilpotentResidual S := by
  induction n with
  | zero =>
    intro G _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro G _ _ hcard S F hS hFnormal hFnilp hSF
    rcases eq_or_ne S ⊤ with rfl | hStop
    · rfl
    haveI := hFnormal; haveI := hFnilp
    -- proper normal `M ⊇ S` を取る (S ◁◁ G, S ≠ ⊤)
    obtain ⟨M, hMnormal, hSM, hMlt⟩ := hS.exists_normal_and_le_and_lt_top_of_ne hStop
    haveI := hMnormal
    -- Dedekind: `M = S(F ∩ M)`
    have hM_eq : S ⊔ F ⊓ M = M := by
      rw [← inf_sup_eq_sup_inf_of_le_of_normal hSM, hSF, inf_top_eq]
    -- 帰納法の適用先 `↥M` の card 減少
    have hMcard : Nat.card ↥M ≤ n := by
      have hlt : Nat.card ↥M < Nat.card G :=
        lt_of_not_ge fun hge => hMlt.ne (Subgroup.eq_top_of_le_card _ hge)
      omega
    -- `(F ⊓ M).subgroupOf M` は normal & nilpotent
    have hFM_normal : ((F ⊓ M).subgroupOf M).Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      exact hFnormal.comap M.subtype
    have hFM_nilp : Group.IsNilpotent ((F ⊓ M).subgroupOf M) := by
      haveI : Group.IsNilpotent ((F ⊓ M).subgroupOf F) := inferInstance
      haveI : Group.IsNilpotent ↥(F ⊓ M) :=
        Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hsup' : S.subgroupOf M ⊔ (F ⊓ M).subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hSM inf_le_right, hM_eq, Subgroup.subgroupOf_self]
    -- 帰納法: `↥M` で `M^∞ = S^∞`
    have hIH := IH ↥M hMcard hS.subgroupOf hFM_normal hFM_nilp hsup'
    have hMres : nilpotentResidual M = nilpotentResidual S := by
      have h := congrArg (Subgroup.map M.subtype) hIH
      rwa [map_subtype_nilpotentResidual_top,
        map_subtype_nilpotentResidual_subgroupOf hSM] at h
    -- `G/M^∞ = M̄ F̄` は nilpotent normal ふたつの積 ⇒ nilpotent ⇒ `G^∞ ≤ M^∞`
    have hle : nilpotentResidual (⊤ : Subgroup G) ≤ nilpotentResidual M := by
      set π := QuotientGroup.mk' (nilpotentResidual M) with hπ
      haveI : (M.map π).Normal := hMnormal.map π (QuotientGroup.mk'_surjective _)
      haveI : (F.map π).Normal := hFnormal.map π (QuotientGroup.mk'_surjective _)
      haveI : Group.IsNilpotent (M.map π) :=
        nilpotentResidual_le_iff_isNilpotent_map.mp le_rfl
      haveI : Group.IsNilpotent (F.map π) := isNilpotent_map π hFnilp
      have hMF : M ⊔ F = ⊤ := top_le_iff.mp (hSF ▸ sup_le_sup_right hSM F)
      have hsupQ : M.map π ⊔ F.map π = ⊤ := by
        rw [← Subgroup.map_sup, hMF]
        exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)
      have hQnilp : Group.IsNilpotent (G ⧸ nilpotentResidual M) := by
        have h := Ch01.sup_isNilpotent_of_normal_nilpotent (M.map π) (F.map π)
        rw [hsupQ] at h
        exact Group.isNilpotent_top.mp h
      rw [nilpotentResidual_le_iff_isNilpotent_map,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      exact Group.isNilpotent_top.mpr hQnilp
    -- `M^∞ ≤ G^∞` は単調性; 合わせて結論
    exact (le_antisymm hle (nilpotentResidual_mono le_top)).trans hMres

/-- **Isaacs Lemma 9.15** (p. 280): `G = SF`, `S ◁◁ G`, `F ◁ G`, `F` nilpotent ならば
`G^∞ = S^∞`. (mmd は仮定を `S ◁ G` と誤抽出; PDF 原文は `S ◁◁ G`.) -/
theorem nilpotentResidual_top_eq_of_isSubnormal_sup_nilpotent [Finite G]
    {S F : Subgroup G} (hS : S.IsSubnormal) [hFn : F.Normal]
    [hFnilp : Group.IsNilpotent F] (hSF : S ⊔ F = ⊤) :
    nilpotentResidual (⊤ : Subgroup G) = nilpotentResidual S :=
  nilpotentResidual_top_aux (Nat.card G) G le_rfl hS hFn hFnilp hSF

/-- Lemma 9.15 の相対形: `S ◁◁ G`, `F ◁ G` nilpotent ならば `(S ⊔ F)^∞ = S^∞`.
Cor 9.16 / Cor 9.18 はこの形で使う. -/
theorem nilpotentResidual_sup_eq_of_isSubnormal [Finite G] {S F : Subgroup G}
    (hS : S.IsSubnormal) [hFn : F.Normal] [hFnilp : Group.IsNilpotent F] :
    nilpotentResidual (S ⊔ F) = nilpotentResidual S := by
  set T := S ⊔ F with hT
  haveI : (F.subgroupOf T).Normal := hFn.comap T.subtype
  haveI : Group.IsNilpotent (F.subgroupOf T) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hsup' : S.subgroupOf T ⊔ F.subgroupOf T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have h := nilpotentResidual_top_eq_of_isSubnormal_sup_nilpotent
    (G := ↥T) hS.subgroupOf hsup'
  have h' := congrArg (Subgroup.map T.subtype) h
  rwa [map_subtype_nilpotentResidual_top,
    map_subtype_nilpotentResidual_subgroupOf le_sup_left] at h'

/-- **Isaacs Corollary 9.16** (p. 281): `S ◁◁ G` ならば `F(G) ≤ N_G(S^∞)`.

証明: Lemma 9.15 (相対形) で `S^∞ = (S F(G))^∞`, これは `S F(G)` が正規化し
(`le_normalizer_nilpotentResidual`), `F(G) ≤ S F(G)`. -/
theorem fitting_le_normalizer_nilpotentResidual [Finite G] {S : Subgroup G}
    (hS : S.IsSubnormal) :
    Ch01.fitting G ≤ Subgroup.normalizer (nilpotentResidual S : Set G) := by
  have h915 : nilpotentResidual (S ⊔ Ch01.fitting G) = nilpotentResidual S :=
    nilpotentResidual_sup_eq_of_isSubnormal hS
  calc Ch01.fitting G ≤ S ⊔ Ch01.fitting G := le_sup_right
    _ ≤ Subgroup.normalizer (nilpotentResidual (S ⊔ Ch01.fitting G) : Set G) :=
        le_normalizer_nilpotentResidual _
    _ = Subgroup.normalizer (nilpotentResidual S : Set G) := by rw [h915]

end

end OddOrder.Isaacs.Ch09
