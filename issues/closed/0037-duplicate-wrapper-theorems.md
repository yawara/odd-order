---
id: 37
slug: duplicate-wrapper-theorems
title: "重複 theorem (純粋リネーム wrapper) を削除する"
created: 2026-05-27
---

# 重複 theorem (純粋リネーム wrapper) を削除する

## 背景

CLAUDE.md "ラッパー方針" 節は **本リポジトリ内の既存 theorem を引数・型そのまま
で純粋リネームする wrapper を書かない** と明示している (mathlib wrapper の禁止と
同じ原則を repo 内の既存 theorem にも適用). 教科書間対応 (BG/Peterfalvi ↔
Isaacs / shared module) は docstring または `notes/` の対応表に記録し, Lean 本体
では既存 theorem を直接呼ぶのが規約.

repo 全体 (54 ファイル, 約 51K 行) を grep し, **public/private 問わず** 同一文の
重複定理を探したところ, 純粋リネーム wrapper が **6 件** 検出された. いずれも
proof body が `:= OddOrder.〈別 namespace〉.SAME_NAME args` の 1 行で, 仮定特殊化
も引数順入れ替えも無い (= CLAUDE.md の許容例外 "引数順 / convention 適応" "仮定
特殊化" "章内 2 回以上呼ぶ慣用名" のいずれにも該当しない).

検出されなかったもの:
- BG/Peterfalvi → mathlib 直接 wrapper (検出方法は in-repo に限定したのと, そも
  そも mathlib wrapper は別系統で監視されている).
- 同一文の non-wrapper 重複 (= 別 proof で同じ statement を 2 回証明している例
  は無し).

参考までに **意図的な特殊化 wrapper** (CLAUDE.md 例外に該当, 削除対象外) は
docstring で明示的に正当化されている:
- [S01_Solvable.lean:984](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:984)
  `hall_higman_solvable_specialization` — `IsSolvable G` instance + π = {p}
  specialization と docstring に明記.

## やること

### 削除対象 (6 件)

各 wrapper の callsite を 直接呼び出しに置換 → wrapper 本体を削除 → `lake build
OddOrder` で確認. 1 件 1 commit を推奨 (CLAUDE.md commit 規約).

- [x] **#1** [S01_Solvable.lean:521-525](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:521)
  `quotient_frattini_isElementaryAbelian`
  → [FrattiniPGroup.lean:161](OddOrder/GroupTheory/FrattiniPGroup.lean:161)
  `OddOrder.GroupTheory.IsPGroup.quotient_frattini_isElementaryAbelian`
  - 同一 statement, body は `:= OddOrder.GroupTheory.IsPGroup.quotient_frattini_isElementaryAbelian hR`
  - **caller**: 外部 0 件 (`S01_Solvable.lean` 内でのみ宣言, 同ファイル内に caller
    も無し).
- [x] **#2** [S01_Solvable.lean:531-535](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:531)
  `isElementaryAbelian_of_frattini_eq_bot`
  → [FrattiniPGroup.lean:188](OddOrder/GroupTheory/FrattiniPGroup.lean:188)
  - 同一 statement, body は 1 行直呼び出し
  - **caller**: 同ファイル [L558](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:558) で 1 回
    (`frattini_eq_bot_iff_isElementaryAbelian` 内). 置換要.
- [x] **#3** [S01_Solvable.lean:569-573](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:569)
  `commutator_sup_pow_closure_le_frattini`
  → [FrattiniPGroup.lean:211](OddOrder/GroupTheory/FrattiniPGroup.lean:211)
  - 同一 statement, body は 1 行直呼び出し
  - **caller**: 同ファイル [L629](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:629) で 1 回
    (`commutator_sup_pow_closure_eq_frattini` 内). 置換要.
- [x] **#4** [S03_PreliminaryCharacter.lean:98-109](OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean:98)
  `card_realIrreducibleCharacters_eq_one_of_odd_card`
  → [BrauerPermutation.lean:347](OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean:347)
  `OddOrder.RepresentationTheory.card_realIrreducibleCharacters_eq_one_of_odd_card`
  - 同一 statement, body は 1 行直呼び出し
  - **caller**: 外部 0 件.
- [x] **#5** [S03_PreliminaryCharacter.lean:115-127](OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean:115)
  `not_isReal_of_ne_trivial_irreducible_of_odd_card`
  → [BrauerPermutation.lean:383](OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean:383)
  `OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card`
  - 名前が微妙に違う (`_irreducible_` が挿入されている) が, 仮定・結論ともに完全
    一致. body は 1 行直呼び出し.
  - **caller**: 外部 0 件.
- [x] **#6** [Ch07/Main.lean:3532-3539](OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:3532)
  `normalizer_map_of_coprime_kernel`
  → [Ch02/Main.lean:2957](OddOrder/Isaacs/Ch02_Subnormality/Main.lean:2957)
  `OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel`
  - 同一 statement (Ch02 側は `_hP_neBot` と underscore, Ch07 側は使う形だが
    値は wrapper 内で透過). body は 1 行直呼び出し.
  - **caller**: 同ファイル 2 箇所 ([L3577](OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:3577)
    と [L3644](OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:3644)). L3577 はすでに
    Ch02 を直呼びしている (wrapper を経由していない) ので置換不要,
    L3644 のみ Ch07 wrapper 経由. 置換要.

### 後始末

- [x] wrapper 削除後, 教科書名 ↔ shared module 名の対応を docstring または
  `notes/` の対応表に残す (CLAUDE.md 規約).
  - BG §1 Lem 1.7 (b)(c)(d) ↔ `OddOrder.GroupTheory.IsPGroup.*`: 
    `notes/bg/s01_solvable.md` (or section docstring at the wrapper site).
  - Peterfalvi (1.1) ↔ `OddOrder.RepresentationTheory.*Brauer*`:
    `notes/peterfalvi/s03_preliminary_character.md`.
  - Isaacs Lem 7.7 (a) ↔ Lem 2.17: Ch07 Main.lean の §7B 冒頭 docstring.
- [x] `lake build OddOrder` をクリーンで通す.

## 完了条件

- 上記 6 件の wrapper が repo から消えている.
- caller がすべて元の theorem を直接呼んでいる.
- `lake build OddOrder` が通る.
- 教科書 ↔ shared module 対応が docstring / notes に記録されている.

## 参照

- CLAUDE.md "ラッパー方針" 節 ("同じ原則は **本リポジトリ内の既存 theorem** に
  も適用する").
- memory `feedback_no_mathlib_wrapper.md` (mathlib wrapper 禁止の原則, in-repo
  にも拡張).
- `notes/meta/lean_formalization_tips.md` §2.7 (wrapper 例外条件).
- 検出方法: `grep -rEn '^  OddOrder\.' OddOrder/ --include='*.lean'` で 1 行直呼び
  出し body を抽出 → 各 callsite の statement を上流 theorem と比較.

## 🧾 注記 (2026-07-02 hub 全体レビュー)

- **#6 は削除済**: `normalizer_map_of_coprime_kernel` は
  `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean` から既に消えている (grep 0 hits,
  2026-07-02 確認)。残対象は **#1–#5 のみ**。
- **#1–#5 の line 番号は drift**: 現在は #1–#3 が `S01_Solvable.lean:1595/1605/1643` 付近、
  #4–#5 が `S03_PreliminaryCharacter.lean:138/155` 付近。**実行時に必ず再 grep** して
  callsite を確認すること (本文の行番号を信用しない)。

## 完了メモ (2026-07-15)

#1–#5 の wrapper を削除し、残る内部 callsite を shared theorem の直接参照へ置換した。
BG Lemma 1.7 と shared Frattini API の対応は §1C docstring、Peterfalvi (1.1) と shared
Brauer-permutation API の対応は module docstring と
`notes/peterfalvi/s03_preliminary_character.md` に記録した。2026-07-02 注記は `Main.lean`
のみを確認しており、file split 後の leaf に #6 wrapper が残っていたため、これも削除して
2 callsite を Ch02 の shared theorem 直参照へ置換した。

検証: focused build、`lake build OddOrder OddOrder.AxiomsCheck` (4234 jobs)、
`OddOrder.feitThompson` の axiom allowlist check がすべて成功。
