# 9209 — 第二同型定理の位数式を Isaacs Ch05 の上流へ

**claim**: lane a (9200 band) / **状態**: landing 済 (2026-07-26)

## 目的

`OddOrder/GroupTheory/CardSupInf.lean` (新 leaf, mathlib のみに依存, `OddOrder.lean` 配線済):

* `card_sup_mul_card_inf_eq` — `N` 正規なら `|H ⊔ N| · |H ⊓ N| = |H| · |N|`
* `card_sup_eq_mul_of_disjoint_normal` — `H ⊓ N = ⊥` なら `|H ⊔ N| = |H| · |N|`

## 経緯 (着手前検索の結果)

同内容が repo 内に既に 3 か所あったが、**どれも Isaacs Ch05 から使えなかった**:

1. `OddOrder/GroupTheory/CNGroupStructure.lean` の public `card_sup_mul_card_inf_eq` —
   ただし同ファイルは `OddOrder.Isaacs.Ch06_FrobeniusActions.Main` を import するので
   **Ch05 が import すると循環**する。
2. `OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean` の
   `card_sup_eq_card_mul_card_of_disjoint_normal'` / `card_sup_eq_mul_of_le_normalizer_of_disjoint'`
   — どちらも `private` (CLAUDE.md「`private` をファイル跨ぎで使わない」) かつ下流。
3. `OddOrder/Isaacs/Ch03_SplitExtensions/Problems3B.lean` に同じ計算が 2 か所インラインで
   書き下されている (`hNHcard`, `hcardK`)。

⟹ mathlib しか import しない最上流 leaf に置き直した。証明は 1 の再利用 (同一 repo 内)。

## hub 判断待ち (重複解消)

`CNGroupStructure.card_sup_mul_card_inf_eq` の削除 + 本 leaf への redirect、
`OddComplement.lean` の private 2 本の redirect、`Problems3B.lean` のインライン 2 か所の
置換。いずれも下流 build が通るかの確認が要るので lane a では触らず hub に委ねる。

## 消費点

Isaacs Problem 5C.4 (issue 1055) — Z-群で位数 `m` の部分群を
`H₂ ⊔ M` (`M` 正規, `H₂ ⊓ M = ⊥`) として構成し位数を数える。
