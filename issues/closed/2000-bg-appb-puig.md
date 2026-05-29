---
id: 2000
slug: bg-appb-puig
title: "BG App.B Puig L(S): 定義 + Lemma B.1(a)-(g) + Lemma B.2"
created: 2026-05-29
---

# BG App.B Puig L(S): 定義 + Lemma B.1(a)-(g) + Lemma B.2

## 背景

BG Thm 6.2 (Glauberman Z(J)) は Isaacs FGT が省く (p.217) ため、no-Gorenstein
方針下では **BG App.B (Puig L(S)) こそが Thm 6.2 の唯一の自己完結代替**。本 issue は
その基盤 = `L(S)` 系の定義 + Lemma B.1 + Lemma B.2 を実装する。

方針正本: `notes/meta/bg_s6_appAB_route_2026_05_28.md`、per-section: `notes/bg/appB_puig.md`。
原文: `references/bg/local-analysis.mmd` L4517-4642 (定義 + B.1 + B.2)。

**スコープ限定**: A.5 (`thmA5`, issue 0049) に依存しない部分のみ。Lemma B.3 / Theorem B.4
は A.5 を消費するので **本 issue 対象外** (A.5 完成後の別 issue)。これにより 0049 と完全並行・無競合。

## やること

- [x] `OddOrder/BG/AppB_Puig.lean` 新規作成 (namespace `OddOrder.BG.AppB`)、import 追加 (AppA 前例に倣い `OddOrder/AxiomsCheck.lean` 経由 = `OddOrder.lean` から推移的に到達 + `#assert_only_allowed_axioms` で axiom-clean を CI ガード)
- [x] 定義: `lRelIn`/`lRel` (= `L_G(X)`), `lNIn`/`lN` (= `L_n(G)`), `lOddIn`/`lOdd` (= `L(G)`), `lStarIn`/`lStar` (= `L_*(G)`)
- [x] Lemma B.1(a) 反変単調 (`lRel` antitone)
- [x] Lemma B.1(b) chain (偶増加 / 奇減少 / 偶 ≤ 奇)
- [x] Lemma B.1(d) `L_*(H) ⊆ L(H)` (`lStarIn_le_lOddIn`)
- [x] Lemma B.1(c) 停留 (有限 subgroup lattice の WellFounded)
- [x] Lemma B.1(e) abelian normal ⊆ L_i (i>0)
- [x] Lemma B.1(f) p-群で L_i ⊇ C_G(L_i) ⊇ Z(G) (極大 abelian normal の self-centralizing 経由)
- [x] Lemma B.1(g) L_G(L_*)=L, L_G(L)=L_*
- [x] Lemma B.2 `H ⊇ L(G) ⇒ L(G)=L(H)` (`lOddIn_eq_of_lOddIn_le`)

## 完了条件

- 上記すべて sorry-free、`lake build OddOrder` green、`#print axioms` で標準 3 公理のみ。

## 参照

- 並行 (A.5 待ち、本 issue 対象外): Lemma B.3 / Theorem B.4 (= Thm 6.2 代替) → issue 0049 完成後
- `notes/meta/bg_s6_appAB_route_2026_05_28.md`、`notes/bg/appB_puig.md`
- テンプレ: `OddOrder/GroupTheory/ThompsonSubgroup.lean` (J(S) の停留 / char 構造)
- self-centralizing の核: `OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial`
