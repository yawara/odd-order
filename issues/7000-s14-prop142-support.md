---
id: 7000
slug: s14-prop142-support
title: "§14 Prop 14.2 support leaf: κ ∃→∀ upgrade + ActsPrimeOn 共役不変性 (F→H handshake)"
created: 2026-06-15
---

# §14 Prop 14.2 support leaf: κ ∃→∀ upgrade + ActsPrimeOn 共役不変性 (F→H handshake)

## 背景

BG §14 は **Prop 14.2 を通る funnel**(14.3→14.13 が全部 14.2 経由)で、§15(G)/§16/`sectionSixteenHypothesis`
= FT spine の全下流がこの 1 keystone に gate されている。Prop 14.2 は case-τ₃/case-τ₁ の 2 branch assembly で、
H(lane-h)が所有・assembly 中だが「dedicated session 向き」と判断して保留していた。

H の notes(`notes/bg/s14_typeP_counting.md`「case-τ₃ / case-τ₁ branch 詳細プラン」)は、両 branch の
**共通の鍵 = κ の ∃→∀ upgrade** と書き、その「最大の friction = 未特定の cyclic-Sylow/Hall repo helper」と
記録していた。**hub 調査(2026-06-15)で、この machinery は既に repo に存在することが判明**:

- `OddOrder.BG.Ch3.S10.isCyclic_of_pRank_le_one`(S10_LocalCriteria:57)= rank-1 odd p-group ⟹ cyclic。
- `cyclicSylow_actsPrime`(S13_PrimeAction:299)= cyclic Sylow ⟹ ActsPrimeOn(`.2` 成分が ActsPrimeOn）。
- `Msigma_inf_centralizer_conj_ne_bot`(S14_TypePCounting:150、H 直近 landing)= 核の M-共役不変性。

⟹ Prop 14.2 は「新規 theory」でなく「既存 machinery の assembly」。残る新規補題 = ∃→∀ upgrade + ActsPrimeOn 共役不変性。
これを **F が別 leaf に切り出し**、H が cite して branch を assembly する分担。

## やること(F = lane-f 所有)

新 leaf(例 `OddOrder/BG/Ch3_MaximalSubgroups/S14_Prop142Support.lean` または §13 隣接の置き場)で:

- [ ] **ActsPrimeOn 共役不変性**: `N ◁ M`, `m ∈ M`(または m∈N(X) 相当)で `ActsPrimeOn N X → ActsPrimeOn N (X^m)`
      に相当する補題。`ActsPrimeOn N X := ∀ g∈X, g≠1 → fixedByElement N g = fixedBy N X`(S13_PrimeAction:75)。
      §13非依存・汎用。H notes の `conj_smul_eq_self_of_mem_normalizer` / `centralizer_map_conj` 等が部品。
- [ ] **κ の ∃→∀ upgrade(κ-free 版で)**: 素数 p で `pRank M p ≤ 1`(= r_p=1)のとき、M の位数 p 部分群
      (= `⟨x⟩ ∈ ℰ_p¹(M)`)は全て M-共役 — `isCyclic_of_pRank_le_one`(各 Sylow-p cyclic)+ cyclic 群の位数 p
      部分群一意 + Sylow 共役。⟹ `∃ P∈ℰ_p¹(M), C_{Mσ}(P)≠1 → ∀ P∈ℰ_p¹(M), C_{Mσ}(P)≠1`
      (核補題 `Msigma_inf_centralizer_conj_ne_bot` で C 不変)。
- [ ] **circular import 回避**: `kappa` は S14_TypePCounting(H 所有)で定義 ⟹ **leaf は κ を使わず「pRank ≤ 1 の素数 p」で述べる**。
      H 側が κ⊆τ₁∪τ₃ ⟹ r_p≤1 で wrap。これで leaf は S14 の **下**に置け、H が `import` 1 行追加で cite。
- [ ] 必要なら付随補題: cyclic 群の位数 p 部分群一意性、Sylow-p 共役の transport、E-setup card facts(E₃≠⊥)など
      H の branch プランで要るもの(`notes/bg/s14_typeP_counting.md` 参照)。

## 完了条件

- 上記 support 補題が新 leaf に sorry-free + axiom-clean で landing(`#print axioms` 確認)。
- leaf が root closure 内(`OddOrder.lean` import + AxiomsCheck 登録)。
- H が `S14_TypePCounting` から cite できる signature であること(H と notes 経由で同期)。
- full build green。

## 参照

- H notes: `notes/bg/s14_typeP_counting.md`「case-τ₃ / case-τ₁ branch 詳細プラン」「核補題 friction」
- 機械: `S10_LocalCriteria.isCyclic_of_pRank_le_one` / `S13_PrimeAction.cyclicSylow_actsPrime` /
  `S14_TypePCounting.Msigma_inf_centralizer_conj_ne_bot`
- 所有境界: F = 新 leaf のみ。`S14_TypePCounting.lean`(Prop 14.2 本体)は H 所有 = cite/import のみ、編集しない。
