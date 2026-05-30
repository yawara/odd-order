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
- [x] 条件付き theorem として `column_orthogonality_cases` と同じ primitive cases
  shape へ束ねる。
- [x] finite/indexing と row orthogonality input を public
  `column_orthogonality_cases` の仮定へ供給する (2026-05-30, 下記参照)。
- [x] conjugate/non-conjugate cases を `column_orthogonality_cases` に戻して `sorry` を消す
  (= 無条件 public 定理 3 本を新ファイルで提供, 2026-05-30)。

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
- `column_orthogonality_cases_of_weightedRowOrthogonality` を追加し、条件付き版を
  final `column_orthogonality_cases` と同じ pair-of-cases shape に束ねた。
- `conjClassesSigmaCarrierEquiv`,
  `classFunction_innerSum_eq_sum_conjClasses`,
  `characterTableWeightedRowPairing_eq_innerSum`, and
  `CharacterTableWeightedRowOrthogonality.ofRowOrthogonality` を追加し、
  ordinary row orthogonality から matrix proof core が要求する
  class-weighted row orthogonality input までを `sorry` なしで接続した。
- `column_orthogonality_cases_ofRowOrthogonality` を追加し、conditional
  primitive cases theorem の入力を weighted row orthogonality から ordinary
  row orthogonality まで下げた。
- `column_orthogonality_cases` の proof core は named column pairing を結論にする形へ整理した。
- public API の raw sum theorem は `characterTableColumnPairing_diag`,
  `characterTableColumnPairing_conj`,
  `characterTableColumnPairing_not_conj` から `sorry` なしで導く形にした。

### Remaining input-supply blockers

`column_orthogonality_cases_ofRowOrthogonality` is now the closest `sorry`-free
entry point to the public theorem.  Closing `column_orthogonality_cases` requires:

- a `CharacterTableIndexing G` package from the public assumptions, i.e. a finite
  `IrreducibleCharacter G` indexing plus
  `Fintype.card (IrreducibleCharacter G) = Fintype.card (ConjClasses G)`;
- `CharacterTableRowOrthogonality (G := G)`.  mathlib has
  `Representation.char_orthonormal`, but the local `IrreducibleCharacter` API still
  needs the bridge from witness representations to equality of class functions /
  representation equivalence before this can be used directly.  The conventions
  also differ: mathlib's theorem uses `χ(g) * ψ(g⁻¹)`, while local
  `ClassFunction.inner` uses Peterfalvi's `χ(g) * star (ψ g)`, so the bridge also
  needs the finite complex character identity `ψ(g⁻¹) = star (ψ g)`.

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

## 2026-05-30 update — 無条件化 landed, close

issue 0048 が completeness core + count (`card_irreducibleCharacter_eq`) +
`CharacterTableIndexing.ofFinite'` / `instCharacterTableIndexingOfFinite` を
sorry-free + axiom-checked で landing 済み (commits 5936a36, c562f17)。これで
2026-05-26 deep dive が挙げた 4 blocker (indexing 構成 / weighted row orthogonality
コンストラクタ / `IsIrreducibleCharacter`↔simple / count) が全て解消した。

**無条件 public 定理 3 本を新ファイルに追加** (sorry-free, axiom = {propext, Classical.choice,
Quot.sound}):

- file: `OddOrder/GroupTheory/RepresentationTheory/ColumnOrthogonality.lean`
  (imports `CharacterCompleteness` + `CharacterRowOrthogonality`; SecondOrthogonality より
  **downstream**。SecondOrthogonality 自体は count を import できない upstream なので、
  無条件版は必ず新規 downstream ファイルになる)。
- 定理:
  - `column_orthogonality_diagonal (g : G)` : `∑_{χ∈Irr} χ(g)·star(χ(g)) = |C_G(g)|`
  - `column_orthogonality_conjugate (hgh : IsConj g h)` : `∑ χ(g)·star(χ(h)) = |C_G(g)|`
  - `column_orthogonality_not_conjugate (hgh : ¬IsConj g h)` : `∑ χ(g)·star(χ(h)) = 0`
  - いずれも typeclass 仮定は `[Group G] [Finite G]` のみ。`idx`/`hrow` は撤去。
- 証明 = `column_orthogonality_{diag,conj,not_conj} instCharacterTableIndexingOfFinite
  weightedRowOrthogonality_ofFinite`。後者は
  `CharacterTableWeightedRowOrthogonality.ofRowOrthogonality … characterTableRowOrthogonality_holds`。
  summation index の `Fintype` 差は `Subsingleton (Fintype _)` で吸収
  (`sum_irreducibleCharacter_idx_eq`)。
- `OddOrder.lean` と `OddOrder/AxiomsCheck.lean` に追加 (3 本とも allowlist-only を
  `#assert_only_allowed_axioms` で確認)。

注: 旧 `column_orthogonality_cases` 系 (idx/hrow を取る条件付き版) は
`SecondOrthogonality.lean` にそのまま残る (matrix proof core として有用)。無条件化は
それらを「呼び出し側で discharge」する形なので、upstream に sorry は元々無く、新規追加も無し。

## 完了条件 (達成)

- [x] public column orthogonality が `idx`/`hrow` 無し (`[Finite G]` のみ) で sorry-free。
- [x] `lake build OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality` が通る。
- [x] `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。
- [x] `lake build OddOrder` 全体が通る。
- [x] AxiomsCheck で 3 本とも allowlist-only。

## 参照

- parent: `issues/0021-peterfalvi-second-orthogonality.md`
- downstream: `issues/0022-peterfalvi-brauer-permutation.md`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
