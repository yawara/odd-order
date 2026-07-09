---
id: 78
slug: s16-mainresults-split
title: "S16_MainResults split — 2614行 (>1500), lane-f active frontier (Prop 16.1 bridges)"
created: 2026-06-23
---

# S16_MainResults split — 2614行 (>1500), lane-f active frontier (Prop 16.1 bridges)

## 背景

size-watch (2026-06-23): `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean` が **2614 行** (>1500)。
lane-f の active frontier (Prop 16.1 forward bridges = `proposition_type_classification` の 7 残 bridge:
hFI/hP1neIIIIV/hP1eqV/hIF/hIIP2/hIIIIVP1/hVP1, issue 8015) ゆえ、分割は **active frontier と衝突しない
凍結境界待ち**。lane-f が Prop 16.1 bridges を一段落させたら hub が prefix-split (Theorem A-E 等の凍結クラスタを
上流 leaf へ、Prop 16.1/Thm I/II の active 部を残す)。

## 完了条件

frozen 境界で prefix-split し、各 leaf <1500 行 (or active leaf のみ frontier に残す)。実施 owner = hub。

## 🧾 注記 (2026-07-02 hub 全体レビュー): trigger 発火

- **trigger 成立**: issue 8015 (Prop 16.1 forward bridges) は closed、lane f は退役済
  (3 レーン体制 a/b/c、正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)、BG 側
  frontier は凍結 ⟹ 凍結境界は自由に取れる。
- 行数 refresh: `S16_MainResults.lean` = **6007 行** (2026-07-02)。
- 優先度 = hygiene-only (BG 凍結クラスタの粒度整理)。実施 owner = hub (prefix-split)。
- (冒頭の空 scaffold template block は本レビューで除去済。)

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - TaxonomyOutput.lean (1505 行)
  - TheoremsAE.lean (2209 行)
  - TypeBridges.lean (3088 行)
