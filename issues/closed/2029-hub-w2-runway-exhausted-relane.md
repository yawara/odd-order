---
id: 2029
slug: hub-w2-runway-exhausted-relane
title: "HUB: lane-h W2 (S14_MaximalI) ungated runway 再枯渇 — relane 要請"
created: 2026-06-27
---

# HUB: lane-h W2 (S14_MaximalI) ungated runway 再枯渇 — relane 要請

> **ユーザー裁可で起票** (2026-06-27, lane-h 再開²): theorem88_dichotomy の win 後、
> lane-h W2 (S14_MaximalI) の ungated 群論 runway が再枯渇。ユーザーが選択肢「hub に relane 要請」を採択。

## 背景

lane-h = W2 = `OddOrder/Peterfalvi/S14_MaximalI.lean` (relane #12、issue 0081)。
2026-06-27 の手動再開で main から **16 commit 合流** (lane-c 退役で 4→3 レーン、lane-f が
W1 §16 を大幅前進)。合流 upstream の consumer-wiring 機会を1件拾って完遂:

- **✅ `theorem88_dichotomy` を honest 構成化** (commit `3ec86cc9`, bare sorry 除去)。
  合流した lane-f の `OddOrder.BG.Ch4.S14.typeP_duality` の第1連言
  `IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)` (κ-Hall K が M' を
  complement、Pf (8.8.b1)) が `Theorem88CaseBData.S_compl` そのものと判明 → `by_cases hall`
  → 非 type-I 極大 → type-P → S/双対 M* に duality を2回適用 → `Theorem88CaseBData` 完全構成。
  helper `isTypeNonI_of_isTypeP` 追加。`theorem88_dichotomy`/`theorem88_caseB_holds` 共に
  sorry-free body (残 hard content は cite した `typeP_duality`/`proposition_type_classification`
  = lane-f issue 8015 に bottom-out)。full build 3884 green / AxiomsCheck OK / count-sorry 125→124。

## runway 再枯渇の評価 (S14_MaximalI 残 sorry の gating)

theorem88_dichotomy 後、S14_MaximalI の残 sorry は**全て char/§8/§10 gated**で ungated 群論ゼロ:

| 行 | 書籍 | gating |
|---|---|---|
| (12.2)-(12.5) | char (Clifford/直交性/ρ-reduction) | lane-b |
| (12.6) `sibleyTarget_frobI` | Sibley/Dade `SibleyDadeHypothesis` (6.8) full | lane-b |
| (12.10) `witness_L_frobenius` | char (11.9.c) + §8 (9.7.b/8.6.a) | lane-b |
| (12.11) `intersection_complement_structure` | char + 未抽出 §8 (8.13.c1) | lane-b |
| (12.12) `complement_cyclic_order_dvd` | **§8-free 核 `isCyclic_and_card_dvd_of_fpf_conj_elemAbelian` は既に DONE**。残 wiring の FPF 入力 = (12.10) char/§8 gated、p+1 refinement = (12.9)/(12.11) gated | lane-b |
| (12.14)-(12.16) | char/Dade (ρ_M 整数性/反例核) | lane-b |
| exists_typeICovering `isTI` | §8 (8.13.c1)+(2.3)、`FittingIsTI` は型 I で普遍真でない (TypeFData.alternative 非TI disjunct) ゆえ還元不可、bare 維持が正 | lane-b §8 |
| exists_typeICovering branch-selection | BG §16 (8.8.a)。`bgTheoremE_cover_data` (S10、lane-b 所有・それ自体 sorry) の `BGTheoremENonTypeICovering` が「W=非type-I極大の normalizer」を field 化していない → `hall` から直接矛盾不可 = 構造強化要 | lane-b §10 |

**∴ S14_MaximalI に lane-h が clean に着手できる ungated・uncollided・FT-path タスクは現存せず。**
残りは全て lane-b (Pf §10-13 char / §8 / §10 `bgTheoremE_cover_data`) gated。これは過去複数回
記録した lane-h の構造的 starvation (FT frontier が char 飽和、ungated group theory が希少) の
再現 ([[ft-four-fronts-w1-w4]] / lane-h topic file の resume¹⁴/¹⁵/2023/2026 履歴)。

## やること (hub への依頼)

- [ ] lane-h を以下のいずれかに routing する hub 判断:
  - **(A) 別の ungated・非衝突・FT-path セグメントへ relane** (もし存在すれば)。現状 lane-f が
    BG §14-16 を active 所有、lane-b が Pf §10-13 char を所有ゆえ、lane-h が衝突なく入れる
    ungated group-theory セグメントの所在は hub 視点で要判断。
  - **(B) await + consumer-wiring 体制を公式化**: lane-b の char/§8 landing 時に lane-h が
    §12 consumer-wiring を機会的に拾う (今日の theorem88_dichotomy がこのパターン)。
    具体的トリガ = (12.10) `witness_L_frobenius` の char 核 / (8.13.c1) §8 / `bgTheoremE_cover_data`
    強化のいずれかが lane-b で landing したら lane-h 自動再開。
  - **(C) 3→2 レーンへの再集約** 等の構造判断 (lane-c 退役と同型、もし lane-h の独立価値が
    継続的に低いと判断するなら)。

## 完了条件

hub が lane-h の次タスク (relane 先 or await 体制 or 集約) を LAUNCH.md / issue で明示。
本 issue が `issues/closed/` へ移動 (lane-h 自己復帰モニターのトリガ)。

## 参照

- 正本: issue 0081 (W2 進捗ログ、2026-06-27 再開² entry に詳細) / `notes/meta/ft_frontier_remap_2026_06_25.md`
- 本セッション commit: `3ec86cc9` (theorem88_dichotomy honest 構成) / `c469e0f3` (issue 0081 doc)
- lane-h topic: memory `lane-h-driving-wielandt-91.md` 2026-06-27 entry
- 関連 HUB issue (過去の同型 starvation): 2021 / 2023 / 2026 / 2027
- 主所有: `OddOrder/Peterfalvi/S14_MaximalI.lean` のみ (W2)

## ✅ RESOLUTION (2026-06-27, ユーザー裁可「await + consumer-wiring を公式化」)

hub が lane-h の 3 選択肢を提示 (AskUserQuestion) → ユーザー裁可 = **option (B) await + consumer-wiring を公式化**。

- **lane-h = W2 (S14_MaximalI) を保持**、ただし **await + consumer-wiring モードに公式移行**。独立駆動はしないが、
  上流 (lane-b char/§8、lane-f BG) landing で §12 consumer-wiring が開いたら機会的に拾う (今 tick の
  theorem88_dichotomy がこのパターン)。
- **再開トリガ** (S14_MaximalI の consumer-wiring が開く landing): (12.10) `witness_L_frobenius` char 核 (lane-b) /
  (8.13.c1) §8 (lane-b) / `bgTheoremE_cover_data` 強化 (lane-b S10) / lane-f BG §16-15 の duality/分類 clean 化。
- **平常は自己復帰モニターで待機** (投機的 scaffold は作らない [[scaffold-sorry-free-not-done]])。トリガ長期不在で
  実質ゼロ稼働が続けば HUB issue で報告 (3→2 集約の再検討材料)。
- **所有 = S14_MaximalI のみ不変** ⟹ cron 監視マップ無改訂 (lane-h は引き続き f/b/h の監視対象)。
- lane-h LAUNCH.md に await 公式化バナー設置済。close。

(3→2 集約 [option C] や投機的 W1 producer [option A, lane-c rank-1 と同じ moot リスク] は不採択。)
