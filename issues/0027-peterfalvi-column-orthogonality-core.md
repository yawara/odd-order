---
id: 27
slug: peterfalvi-column-orthogonality-core
title: "Peterfalvi Part I: column orthogonality cases の proof core を証明する"
created: 2026-05-26
---

# Peterfalvi Part I: column orthogonality cases の proof core を証明する

## 背景

`issues/0021-peterfalvi-second-orthogonality.md` から分割した proof core。
public API の `column_orthogonality_diag`, `column_orthogonality_conj`,
`column_orthogonality_not_conj` は `column_orthogonality_cases` から導く形に整理済み。

残る hard proof は、character table の invertibility / matrix algebra から
`column_orthogonality_cases` を証明する部分。
これは Brauer permutation lemma と Peterfalvi §3 (1.2) の共通依存になる。

## やること

- [x] `IrreducibleCharacter G` と `ConjClasses G` の finite cardinal/indexing をそろえる。
- [x] first orthogonality から character-table matrix の row orthogonality を statement 化する。
- [x] square/invertible matrix argument で、weighted row orthogonality input から
  square-indexed column diagonal/off-diagonal relation を導く。
- [x] square-indexed column relation を conjugacy-class indexed pairing と
  element representative pairing へ戻す。
- [ ] finite/indexing と weighted row orthogonality input を public
  `column_orthogonality_cases` の仮定へ供給する。
- [ ] conjugate/non-conjugate cases を `column_orthogonality_cases` に戻して `sorry` を消す。

## 2026-05-26 update

- raw column sum に `characterTableColumnPairing g h` という名前を付けた。
- `characterTableRowPairing` and `CharacterTableRowOrthogonality` を追加し、
  matrix proof core が使う row-side input を statement 化した。
- `characterTableColumnPairing_of_isConj_left/right` and
  `characterTableColumnPairing_conj_left/right` を追加し、column pairing の
  conjugacy invariance を unfold せずに使えるようにした。
- `CharacterTableIndexing` を追加し、row 側 `IrreducibleCharacter G` と
  column 側 `ConjClasses G` の `Fintype` と cardinal equality をひとつの
  data にまとめた。
- `characterTableEntry` and `characterTableClassColumnPairing` を追加し、
  matrix proof core が conjugacy class indexed columns を直接参照できるようにした。
- `CharacterTableIndexing.rowColumnEquiv`, `characterTableMatrix`, and
  `characterTableSquareMatrix` を追加し、cardinality equality から determinant /
  invertibility 用の正方行列へ reindex する橋を用意した。
- `characterTableDeterminant` and `CharacterTableMatrixInvertible` を追加し、
  row orthogonality から det nonzero を示す次段の interface を固定した。
- `conjugacyClassSize`, `characterTableWeightedRowPairing`, and
  `CharacterTableWeightedRowOrthogonality` を追加し、first orthogonality を
  class-weighted matrix row Gram の形で使うための interface を固定した。
- `characterTableClassSizeSquareMatrix`, `characterTableSquareWeightedRowPairing`,
  and `characterTableWeightedRowGramMatrix` を追加し、row Gram を
  `A * W * Aᴴ` として明示した。
- `characterTableDeterminant_ne_zero_of_weightedRowOrthogonality` を追加し、
  class-weighted row orthogonality から character-table determinant nonzero
  (`CharacterTableMatrixInvertible`) までを `sorry` なしで接続した。
- `conjugacyClassSize_mk_mul_card_centralizer` and
  `card_centralizer_eq_card_div_conjugacyClassSize_cast` を追加し、conjugacy
  class size と `|C_G(g)|` の変換を column diagonal 用 API として固定した。
- `characterTableSquareMatrixInvertibleOfDet`,
  `characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality`, and
  `characterTableClassSizeSquareMatrix_mul_conjTranspose_eq_inv_mul_cardDiagonal`
  を追加し、row Gram identity の左側 character-table factor を逆行列で消す
  matrix algebra bridge を固定した。
- `characterTableClassColumnPairingOfIndexing` and
  `characterTableSquareColumnPairing` を追加し、class-indexed column pairing と
  square reindexed matrix の column Gram を相互変換できるようにした。
- `characterTableClassColumnPairingOfIndexing_mk`,
  `characterTableClassColumnPairingOfIndexing_eq_columnPairing_representatives`, and
  `characterTableSquareColumnPairing_eq_columnPairing_representatives` を追加し、
  matrix/class indexed column pairing を既存の element representative API に戻せるようにした。
- `conjugacyClassSize_pos` を追加し、class-size division で使う非零性を再利用可能にした。
- `characterTableClassSizeSquareMatrix_mul_columnGram_eq_cardDiagonal` and
  `conjugacyClassSize_mul_characterTableColumnGram_apply` を追加し、
  row Gram の cancel bridge から `W * (Aᴴ A) = |G| I` とその entrywise 形までを
  `sorry` なしで接続した。
- `characterTableConjTranspose_mul_squareMatrix_apply_eq_star_squareColumnPairing` を追加し、
  matrix column Gram convention と既存 `characterTableSquareColumnPairing` convention の
  complex conjugation bridge を固定した。
- `characterTableSquareColumnPairing_diag_of_weightedRowOrthogonality` and
  `characterTableSquareColumnPairing_eq_zero_of_ne_of_weightedRowOrthogonality` を追加し、
  weighted row orthogonality input の下で square-indexed column relation を取り出せるようにした。
- `characterTableClassColumnPairingOfIndexing_diag_of_weightedRowOrthogonality`,
  `characterTableClassColumnPairingOfIndexing_eq_zero_of_ne_of_weightedRowOrthogonality`,
  `characterTableColumnPairing_diag_of_weightedRowOrthogonality`,
  `characterTableColumnPairing_conj_of_weightedRowOrthogonality`, and
  `characterTableColumnPairing_not_conj_of_weightedRowOrthogonality` を追加し、
  square-indexed relation を conjugacy-class indexed pairing と element representative
  pairing に戻した。
- `column_orthogonality_cases` の proof core は named column pairing を結論にする形へ整理した。
- public API の raw sum theorem は `characterTableColumnPairing_diag`,
  `characterTableColumnPairing_conj`,
  `characterTableColumnPairing_not_conj` から `sorry` なしで導く形にした。

## 完了条件

- `OddOrder.RepresentationTheory.column_orthogonality_cases` から `sorry` が消える。
- `lake build OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0021-peterfalvi-second-orthogonality.md`
- downstream: `issues/0022-peterfalvi-brauer-permutation.md`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
