---
id: 2001
slug: bg-appb-b3-b4-puig-theorem
title: "BG App.B Lemma B.3 + Theorem B.4 (= Thm 6.2 代替)"
created: 2026-05-29
---

# BG App.B Lemma B.3 + Theorem B.4 (= Thm 6.2 代替)

## 背景

issue 2000 で **App.B 定義 + Lemma B.1(a)-(g) + B.2** が完成 (`OddOrder/BG/AppB_Puig.lean`,
sorry-free, axiom-clean)。A.5 (`thmA5_part1/part2`, issue 0049) も完成済。これにより
**Lemma B.3 + Theorem B.4 が ready-now**。

**Theorem B.4(a) は BG Thm 6.2 (Glauberman Z(J)) の代替** (BG L4691 "serves as a substitute
for Theorem 6.2")。Isaacs FGT が Z(J) 定理を省く (p.217) ため、no-Gorenstein 方針下では
これが Thm 6.2 一般形の唯一の自己完結ルート。**クリティカルパス**: B.4 → BG Thm 6.2 一般形 →
§7 (Thompson 推移性) → §8-§16。

方針正本: `notes/bg/appB_puig.md`「実装状況 (2026-05-29)」+ 「Lem B.3 / Thm B.4 詳解」、
`notes/meta/log/bg_s6_appAB_route_2026_05_28.md`。原文: `references/bg/local-analysis.mmd`
L4644-4757 (Lem B.3 = L4644-4684, Thm B.4 = L4686-4757)。

## やること

> **設計正本**: `bg-appb-b3b4-design` workflow (run wf_06198d42-7bc, 10 agent, スカウト→合成→
> adversarial 検証) が確定した順序付き設計。lemma 署名・proof sketch・引用補題・risk は当該出力参照。

### 前提インフラ (`AppB_Puig.lean` 末尾, A.5 非依存) — ✅ 完成

- [x] `abelian_le_lNIn` (B.1(e) を `H ≤ N_G(A)` 一般化) + `lRelIn_le_iSup_pgroup_normalized` (thmA5 橋渡し)
- [x] **相対 B.1(f)**: `le_normalizer_map_subtype_of_normal` / `centralizer_inf_le_of_self_centralizing` /
      `centralizer_lNIn_inf_le` / `centralizer_lStarIn_inf_le` (Ch06 self-centralizing を `↥H` で再利用 + map subtype transport)
- [x] **相対 B.2**: `lRelIn_le_lRelIn` (ambient 一般化) + `b2_*` 相対化 + `lOddIn_eq_of_lOddIn_le_relative`
- [x] **φ-同変 + characteristic**: `lRelIn_map_equiv` / `lNIn_map_equiv` /
      `lNIn_characteristic_of_characteristic` / `lOddIn_characteristic_of_characteristic`

### Lemma B.3 (mmd L4644-4684, `AppB_PuigB3B4.lean`) — ✅ 完成

- [x] `b3_interleave` (帰納核 `L_{2n}(S)⊆L_{2n}(T)⊆L_{2n+1}(T)⊆L_{2n+1}(S)`, 偶段 = `thmA5_part2`)
- [x] `b3_chain` (`L_*(S)⊆L_*(T)⊆L(T)⊆L(S)`)。AxiomsCheck 登録済, 標準3公理。

### Theorem B.4(b) (mmd L4689-4762) — ⏳ 残作業 (本 issue の主目標)

> **2026-05-30 進捗 (overnight 自走)**: Step2 + normalizer 基盤 完成・コミット済。**設計の高リスク
> transport 群 (`lRelIn_subgroupOf`/`lNIn_subgroupOf`/`lOddIn_subgroupOf`/`lOddIn_subgroupOf_characteristic`,
> ~60行) は不要化** — 代わりに **共役同変ルート** `normalizer_le_normalizer_lOddIn`
> (`N_G(H) ⊆ N_G(L(H))` 任意 H, `lNIn_map_equiv` + `map_conj_eq_iff_mem_normalizer`) で
> Step3 の `N_G(C∩S) ⊆ N_G(L(C∩S))` を直接供給する。

- [x] `Z(L(S))` 定義 (`zCenterLOdd`) + keystone bridge `zCenterLOdd_eq_centralizer_inf` (`Z(L(H))=C_G(L(H))⊓L(H)`)
- [x] **Step2** `zCenterLOdd_sylow_le_zCenterLOdd_opCore` (`Z(L(S)) ⊆ Z(L(T))`)
- [x] **normalizer 基盤**: `lOddIn_map_equiv` / `map_conj_eq_iff_mem_normalizer` / `normalizer_le_normalizer_lOddIn` (共役同変)
      + `normalizer_le_normalizer_map_of_characteristic` (S7D1 port, center 段用)
- [x] **`normalInf_isSylow`** (+`_coe`): `Sylow p G` と normal `N` で `(↑Q⊓N).subgroupOf N` が `Sylow p ↥N`
      (`IsPGroup.toSylow`; index 義務は新補題 `relIndex_inf_eq_relIndex_sup` = 第2同型の指数版で `¬p∣relIndex` を `Q.not_dvd_index` に還元)。
- [x] **Step3** (FINAL 内 inline): `Y=Z(L(T))` Normal (`haveI ...Normal := inferInstance` + `unfold zCenterLOdd`),
      `Y⊆L_*(S)` は新補題 `zCenterLOdd_isMulCommutative` + `abelian_le_lNIn` + `exists_lStarIn_eq`,
      `thmA5_part1` (P=Y) → `L(S)≤C`; `lOddIn_eq_of_lOddIn_le_relative` で `L(C∩S)=L(S)`;
      `normalizer_le_normalizer_lOddIn (C∩S)` ∘ hLeq で `N_G(C∩S) ⊆ N_G(L(S))`。
- [x] **Step4** (FINAL 内 inline): Frattini `Sylow.normalizer_sup_eq_top` (normalInf_isSylow) →
      `N_G(C∩S)⊔C=⊤`; 吸収 `C=C_G(Y)·(C∩S)` (mk' の ker=C_G(Y) ルート, `c*s⁻¹` 直接で符号罠回避) → `C_G(Y)⊔N_G(C∩S)=⊤`。
- [x] **FINAL** `zCenter_lOdd_normal_of_oPiCore_eq_bot`: `⊤=C_G(Y)⊔N_G(C∩S)≤N_G(Z)` で `Z.Normal`。
      左枝 `C_G(Y)≤C_G(Z)≤N_G(Z)` (Z⊆Y); 右枝 `N_G(C∩S) ⊆ N_G(L(S)) ⊆ N_G(Z)`
      (後者 = `normalizer_le_normalizer_map_of_characteristic`)。AxiomsCheck 登録済, 標準3公理。**✅ 完成 (commit c7acf6a)**。

> **2026-05-30 完成**: B.4(b) 全 Step が sorry-free, `lake build OddOrder` green, 標準3公理のみ。
> `set` は Y/C/CapS にのみ使用 (C₀=C_G(Y) は `centralizer` 頭で保持 = A.5 出力の quotient instance 解決のため明示)。
> 設計の transport 群は不要のまま (共役同変ルートで完結)。残: **B.4(a) → issue 2002**。

### B.4(a) + Thm 6.2 一般形 — → **issue 2002 に分離**

- B.4(a) `G = O_{p'}·N_G(Z(L(S)))` は異群 iso `φ:G≃*H` 共変性が必要 (検証で BLOCKED) → **issue 2002**。
- BG Thm 6.2 一般形 `Z(L(S))·O_{p'} ⊴ G` の接続も 2002 (または直後の別 issue)。

## 完了条件

- 上記 B.3 / Thm B.4(a)(b) すべて sorry-free, `lake build OddOrder` green,
  `OddOrder/AxiomsCheck.lean` に登録し標準 3 公理のみ。
- Thm 6.2 一般形への接続を最低限 statement レベルで用意 (証明は本 issue or 直後の別 issue)。

## 参照

- ⭐ **別セッション引き継ぎ (B.4(b) 残作業の自己完結手順書)**: [`notes/bg/appB_b4b_handoff.md`](../../notes/bg/appB_b4b_handoff.md)
  — normalInf_isSylow / Step3 / Step4 / FINAL の署名・sketch・FIX・落とし穴・先例を全転記。**B.4(b) 再開時はまずこれを読む。**
- 前提 (完成済): issue 2000 (B.1/B.2), issue 0049 (`thmA5_part1/part2`)。
- `notes/bg/appB_puig.md` (Lem B.3 詳解 L174-208, Thm B.4 4-Step 詳解 L212-322)。
- `OddOrder/BG/AppB_Puig.lean`: `lRelIn_top_le_lRelIn` (B.4 Step3 の `L(C∩S)=L(S)` に再利用),
  `lOddIn_eq_of_lOddIn_le` (= B.2), `centralizer_lNIn_le` (絶対 B.1(f), 相対版の雛形)。
- `OddOrder/BG/AppA_PStability.lean`: `thmA5_part1` (L2062), `thmA5_part2` (L2099)。
- 原文 `references/bg/local-analysis.mmd` L4644-4757。
