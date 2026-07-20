---
id: 136
slug: lint-deferred-import-and-generalization
title: "lint wave の繰延 2 件: Mathlib.Tactic import 絞り込み (要フルビルド) + AppD hne 一般化"
created: 2026-07-20
---

# lint wave の繰延 2 件

2026-07-20 夜の lint wave (issue 0123, commit `35b2750d1`) で**成果としては妥当だが
lint commit に混ぜられない**と判断して revert した 2 件。**破棄ではなく繰延**なのでここに保存する。

---

## ① `S05_GridTrichotomy` の `import Mathlib.Tactic` 絞り込み

### 現状

`OddOrder/Peterfalvi/S05_GridTrichotomy.lean:8` の `import Mathlib.Tactic` に対し
mathlib の linter が「Files in mathlib cannot import the whole `Mathlib.Tactic` folder.
Doing so would cause imports to be unnecessarily slow.」を出している。

⚠ `import Mathlib.Tactic` は**リポジトリ全体でこの 1 箇所のみ** (`grep -rn "^import Mathlib.Tactic$" OddOrder`)。
つまりこの 1 行が全 spine に mathlib の全 tactic を流し込んでいる。**ビルド時間の観点でも
直す価値がある**。

### なぜ前回失敗したか (再挑戦する人は必読)

エージェントは file 内の tactic を census して 7 module に絞り、
`Mathlib.Tactic.{Common,FieldSimp,Linarith,LinearCombination,NormNum,Positivity,Ring}` に置換。
leaf build と**直接 importer 3 本** (S05_SigmaTrichotomy / S05_GridRigidity /
S06_CertainTypeIsometry) が green だったので FIXED と報告した。

**これは構造的に不十分**。実際には:

* この import を落とすと下流 **265 module** (`OddOrder.FeitThompson`・`OddOrder.AxiomsCheck`・
  Pf S08–S16 全部を含む) の閉包から **1,908 module** が消える。
* 具体的な破断: `Mathlib.Tactic.NormNum.Prime` が到達不能になり
  `OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean:614` と
  `.../CaseBOrder.lean:86` の `(by norm_num : ¬ Nat.Prime 4)` が落ちる
  (`Mathlib.Tactic.NormNum` 本体には Prime 拡張が入っていない)。
* **leaf build は下流 262 module を elaborate しないので、原理的にこれを検出できない。**

### 正しい手順

1. 絞り込み候補を決める (前回の 7 module + 下流が要求するものを足す)。
2. **必ずフルビルド `lake build OddOrder` で検証する** — leaf build は根拠にならない。
3. 落ちたら足りない module を足して再フルビルド。⚠ 1 回 10〜16 分なので、
   足りない分は事前に静的に洗い出すと速い。具体的には、この import を落として
   到達不能になる `Mathlib.Tactic.*` の一覧を出し、下流で使われている tactic
   (`norm_num` 拡張・`decide`・`polyrith` 等) と突き合わせる。
4. hub の合流 gate と衝突しないよう、**レーンが静かなタイミング**でやる
   (フルビルド中に他レーンをマージすると切り分けが効かない)。

---

## ② `AppD/MaximalSylowIntersection` の `hne` 一般化

### 内容

`OddOrder/BG/AppD_CNGroups/MaximalSylowIntersection.lean:323` の

```lean
include hyp hQP hne hmax hM_ge hM_core in
theorem inf_eq_oPiCore_of_maximal …
```

から `hne : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥` を外せる (= 仮説不要)。
lint wave 中にエージェントが実際にやり、**ビルドが通り、唯一の caller**
(`isThreeStepGroup_and_inf_eq_oPiCore`, 同 file :424) の更新も済んでいた。

### なぜ revert したか

これは linter が求めた修正ではなく (linter の指摘は「自動 include された section variable が
未使用」)、**数学的仮説の削除 = statement 変更**。lint commit に混ぜると
「意味保存のみ」という wave の不変条件が崩れ、後から revert / review しづらくなる。

### なぜ捨てないか

CLAUDE.md「特殊化債務 (`formalized_specialized`) はできる限り一般化する」に**合致する
本物の一般化**。教科書 (BG App.D) が `P ∩ Q ≠ 1` を課しているかを確認した上で、
**単独の commit** として入れ直すのが正しい。

### 手順

1. BG App.D の該当箇所を PDF で読み、`hne` が書籍の仮説かどうかを確認する
   (書籍が課しているなら「repo が強すぎる」のではなく単に証明で使っていないだけ ⟹
   それでも外してよいが docstring に「書籍は仮説として挙げるが証明に不要」と注記する)。
2. `include` から外し、caller を更新し、**フルビルド**で検証。
3. 単独 commit。lint とは混ぜない。
