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
- [ ] square/invertible matrix argument で column orthogonality を導く。
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
- `column_orthogonality_cases` の proof core は named column pairing を結論にする形へ整理した。
- public API の raw sum theorem は `characterTableColumnPairing_diag`,
  `characterTableColumnPairing_conj`,
  `characterTableColumnPairing_not_conj` から `sorry` なしで導く形にした。

## 2026-05-26 update — 残 blocker 詳細 (deep dive)

`column_orthogonality_cases` を実際に sorry-free にするのに残るギャップを sub-agent 調査で詳細化:

1. **signature に `[Finite G]` を追加** — 現在は `[Fintype (IrreducibleCharacter G)]` のみ.
   RHS の `Nat.card (Subgroup.centralizer ({g} : Set G))` と matrix square 議論には
   `[Finite G]` が必要. 3 つの named corollary も同様.
2. **`CharacterTableIndexing G` を構成する補題が無い**:
   matrix 全部品が `idx : CharacterTableIndexing G` パラメータ. これを構成するには
   classical な **`Nat.card (IrreducibleCharacter G) = Nat.card (ConjClasses G)`** が必要だが
   mathlib v4.29.1 にも本 repo にも無い. `BrauerPermutation.lean:208` も同じ gap.
3. **`CharacterTableWeightedRowOrthogonality idx` のコンストラクタが無い**:
   `characterTableClassSizeSquareMatrix_mul_conjTranspose_eq_inv_mul_cardDiagonal` は
   これを仮定として取るが, mathlib `FDRep.char_orthonormal` から作る bridge が無い.
   - `IrreducibleCharacter G` → simple `FDRep ℂ G` 関数 (Classical.choice on existential)
   - 異なる `IrreducibleCharacter` ⇒ 同型でない FDRep simples (so `char_orthonormal` が δ)
   - universe 整合 (`IsIrreducibleCharacter` Type 0 vs `FDRep` parameterized universe)
   - `χ(g⁻¹) = star (χ(g))` (`[IsAlgClosed ℂ]` + finite-order ⇒ root of unity)
   が必要.
4. **`IsIrreducibleCharacter` ↔ `FDRep.Simple` の接続が wire されていない**:
   `ZIrr.lean:94` は `Representation.IsIrreducible` 経由, `FDRep.char_orthonormal` は
   `CategoryTheory.Simple` 経由. これら 2 つの同値性 lemma が無い.

**推定**: 残作業 200-400 行, 少なくとも 1 件の新規 connector ファイル.
sub-agent 結論: 4 件の blocker は **structural (pre-proof gaps)** で「gymnastics」ではない.

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
