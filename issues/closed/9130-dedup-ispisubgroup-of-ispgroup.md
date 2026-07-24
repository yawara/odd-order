---
id: 9130
slug: dedup-ispisubgroup-of-ispgroup
title: "isPiSubgroup_of_isPGroup_of_mem を GroupTheory へ集約 (BG の重複を削除)"
created: 2026-07-18
---

# isPiSubgroup_of_isPGroup_of_mem を GroupTheory へ集約 (BG の重複を削除)

## 採番の経緯

当初 9128 で採番したが、並行レーンが同じ 9128 (`9128-psu-simplicity`) を先に main へ
merge していたため 9130 に振り直した (SEQUENCE.9000 の merge conflict で発覚)。
先行 commit `b00ad49f3` のメッセージは旧番号 9128 を参照している。

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

`isPiSubgroup_of_isPGroup_of_mem` (`p`-群 + `p ∈ π` ⇒ `π`-部分群) を
**`OddOrder/GroupTheory/OpResidual.lean`** (= `Subgroup.IsPiSubgroup` の定義元、
import graph の最下層) に追加した (2026-07-18, lane a)。

理由: Isaacs Ch09 の Thm 9.23 で必要になったが、既存の実装は
`OddOrder/BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean:129` にあり、
**BG は Isaacs の下流**なので import できなかった。3 つ目のコピーを作るより
canonical home に置く方が正しいと判断。

新規 import は不要 (`Mathlib.GroupTheory.Sylow` が既に `IsPGroup` を供給)。

## やること

- [ ] `BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean:129` の
      `isPiSubgroup_of_isPGroup_of_mem` を削除し、`Subgroup.` 版を使うよう
      呼び出し側 (S12_Lemma128 / S12_Corollary129 / S12_Theorem127 の 4 箇所ほか) を更新。
- [ ] 名前空間の差 (`BG.Ch3.S12.` vs `Subgroup.`) に注意 — 呼び出しは
      `Subgroup.isPiSubgroup_of_isPGroup_of_mem` になる。
- [ ] full build + AxiomsCheck で回帰なしを確認。

## 注意

BG レーンの所有ファイルなので、実施は BG 担当レーン (または hub) が行う。
lane a は canonical 版を追加するところまで。

## ⚠ 追記 (2026-07-18): 3 つ目の重複が判明

`OddOrder/GroupTheory/SubgroupInAmbient.lean:147` に
`isPiSubgroup_singleton_of_isPGroup` (`IsPGroup q ↥H → IsPiSubgroup {q} H`) が
**既にあった**。これは今回追加した一般版 `isPiSubgroup_of_isPGroup_of_mem` の
singleton 特殊化 (`isPiSubgroup_of_isPGroup_of_mem hH rfl` で得られる)。

つまり現状 3 箇所に同内容がある:
1. `GroupTheory/OpResidual.lean` — `isPiSubgroup_of_isPGroup_of_mem` (一般 π、今回追加、canonical)
2. `GroupTheory/SubgroupInAmbient.lean:147` — `isPiSubgroup_singleton_of_isPGroup` (singleton)
3. `BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean:129` — 一般 π (BG ローカル)

**反省**: lane a は Thm 9.23 step (v) の実装時に (2) を見落とし、
既に import していたファイルの中に使える補題があったのに一般版を新設した。
一般版そのものは BG の重複解消に資するので残す価値があるが、
着手前の grep が singleton 形を拾えていなかった (検索語が `_of_mem` 寄りだった)。

- [ ] (2) を (1) の系に置換するか、単に (1) へ寄せて削除する。

---

## 🧭 HUB RULING (2026-07-22): 9159 と統合実施 (owner = hub)

9159 の HUB RULING を参照 — 両 dedup は hub が quiet window で 1 コミット同時実施。

---

## 📝 2026-07-24 hub 更新 — 9159 は abbrev で close、本 issue に残る作業

- BG 側の重複定義は解消済み (定義 census で `isPiSubgroup_of_isPGroup_of_mem` は
  OpResidual の 1 本のみ、BG の 16 hits は全て caller)。
- 9159 (述語重複) は `Subgroup.IsPiGroup := IsPiSubgroup` の abbrev 化で close。
- **本 issue の残り (lemma 3 重複の集約)**:
  1. `Subgroup.isPiSubgroup_of_isPGroup_of_mem` (OpResidual :58、canonical)
  2. `Ch03.Subgroup.IsPiGroup.of_isPGroup_of_mem` (Theorem315 :454、abbrev 経由で同内容)
  3. `isPiSubgroup_singleton_of_isPGroup` (SubgroupInAmbient :147、singleton 特殊化、参照 20)
  (2)(3) を (1) へ寄せて削除 or 系化。参照 20+ の repoint を含む mechanical 作業 —
  quiet window の別 wave で実施。alias `Subgroup.IsPiGroup` の全面 textual 置換 (478 サイト)
  も同 wave 候補 (upstream 適性; 急がない)。

---

## ✅ 2026-07-24 close — 補題 trio 集約完了 (hub)

- (2) `Ch03.Subgroup.IsPiGroup.of_isPGroup_of_mem` を**削除** (canonical (1) と statement 同一の
  純重複)。caller 4 箇所 (Theorem315 内 1 + S7C_ThompsonPComplement 3) を
  `Subgroup.isPiSubgroup_of_isPGroup_of_mem` へ repoint。
- (3) `isPiSubgroup_singleton_of_isPGroup` は **1 行の系**に置換
  (`isPiSubgroup_of_isPGroup_of_mem hH rfl`; caller 19 箇所は無変更 — 慣用名として保持、
  重複証明本体は消滅)。
- BG 側の重複 (発端) は既に解消済みだったことを census で確認済 (前回注記)。
- leaf build green (2391 jobs)、full --strict gate は wave 末尾。
- 残る optional 作業 (急がない・upstream 時): alias `Subgroup.IsPiGroup` の全面 textual 置換
  478 サイト (closed/9159 の注記参照)。close。
