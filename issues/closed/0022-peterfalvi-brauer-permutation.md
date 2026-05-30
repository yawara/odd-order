---
id: 22
slug: peterfalvi-brauer-permutation
title: "Peterfalvi Part I: Brauer permutation lemma stubを解消する"
created: 2026-05-25
---

# Peterfalvi Part I: Brauer permutation lemma stubを解消する

## 背景

Peterfalvi §3 (1.1) と §6 (4.5.b) で使う Brauer permutation lemma
([Is] Thm 6.32) の stub を解消する。通常は second orthogonality /
character table の可逆性を使うため、issue 0021 の後続として扱う。

## やること

- [x] `ConjClasses.inv` / `ConjClasses.IsReal` API が proof に十分か確認する。
- [x] `OddOrder.RepresentationTheory.brauer_permutation_lemma` を `sorry` なしにする。
      (元から sorry-free だが 5 個の条件付き引数を取る形だった。2026-05-30 に **無条件版**
      `brauer_permutation_lemma'` を追加し全引数を `[Finite G]` から discharge。)
- [x] Peterfalvi §3 (1.1) 用の odd-order specialization を追加するか、別 issue に切る。
- [x] §6 (4.5.b) で再利用できる statement 名と namespace を維持する。

## 2026-05-25 update

- class-side odd-order API を追加:
  - `ConjClasses.eq_one_of_isConj_inv_of_odd_card`
  - `ConjClasses.eq_one_of_isReal_of_odd_card`
  - `ConjClasses.card_realClasses_eq_one_of_odd_card`
- これで Brauer permutation lemma の後に必要になる
  `Nat.card { C : ConjClasses G // ConjClasses.IsReal C } = 1` 側は
  `sorry` なしで利用できる。
- character-side の「実既約は trivial のみ」は
  `card_realIrreducibleCharacters_eq_one_of_odd_card` で cardinal 形まで追加した。
  unique real character が trivial character であることの明示は、trivial-character
  API の後続として残す。

## 2026-05-26 update

- `RealIrreducibleCharacter G` と `ConjClasses.RealClass G` を名前付き型にした。
- `brauer_permutation_lemma` は
  `Nat.card (RealIrreducibleCharacter G) = Nat.card (ConjClasses.RealClass G)`
  という readable な statement に揃えた。
- Peterfalvi §3 側に (1.1) の cardinal form
  `OddOrder.Peterfalvi.S03.card_realIrreducibleCharacters_eq_one_of_odd_card`
  を追加した。
- `trivialClassFunction`, `trivialIrreducibleCharacter`,
  `trivialRealIrreducibleCharacter` を追加し、Brauer odd-order specialization
  から `realIrreducibleCharacter_eq_trivial_of_odd_card` と
  `not_isReal_of_ne_trivial_of_odd_card` を導いた。
- Peterfalvi §3 側にも (1.1) の pointwise form
  `not_isReal_of_ne_trivial_irreducible_of_odd_card` を追加した。
- Brauer lemma の proof 本体は引き続き `issues/0027-peterfalvi-column-orthogonality-core.md`
  の character-table invertibility に依存する。

## 2026-05-30 update — 無条件化完了 → close

issue 0048 (`|Irr G| = |ConjClasses G|` + `instCharacterTableIndexingOfFinite`) が landed した
ことで `idx`/`hrow` が `[Finite G]` から無条件供給できるようになり、残る gate は複素共役置換
`σ : χ ↦ χ̄` の構成のみだった。新 downstream ファイル
`OddOrder/GroupTheory/RepresentationTheory/BrauerPermutationUnconditional.lean` で discharge:

- **`Representation.IsIrreducible.dual`** (新規, mathlib 未収録): 有限次元既約表現の双対 (反傾) は
  既約。証明は部分表現の `Submodule.dualAnnihilator` / `dualCoannihilator` による反変順序同型
  `Subrepresentation.dualOrderIso : Subrepresentation ρ.dual ≃o (Subrepresentation ρ)ᵒᵈ` を構成し、
  `OrderIso.isSimpleOrder_iff` + `OrderDual.instIsSimpleOrder` で `IsSimpleOrder` を移送。
  annihilator が `G`-stable を保つことは `dual_apply`/`Module.Dual.transpose_apply` で
  `(ρ.dual g f) w = f (ρ g⁻¹ w)` と展開して確認。
- **`IsIrreducibleCharacter.conj`**: `φ̄` は双対表現 `ρ.dual` の指標
  (`χ̄(g) = star χ(g) = χ(g⁻¹) = χ_{ρ*}(g)`, `character_inv` + `Representation.char_dual`)。
- **`IrreducibleCharacter.conjPerm G`**: `χ ↦ ⟨χ.conj, _⟩`. involutive (`conj_conj`)。
- **`conjPerm_eq_self_iff`** (= `h_real_irr`) / **`conjPerm_compat`** (`χ̄(C)=χ(C⁻¹)`, `character_inv`)。
- **`brauer_permutation_lemma'`** (無条件): `[Finite G]` のみ。`instCharacterTableIndexingOfFinite`
  + `CharacterTableWeightedRowOrthogonality.ofRowOrthogonality characterTableRowOrthogonality_holds`
  + 上記 σ を `brauer_permutation_lemma` に供給。
- **`card_realIrreducibleCharacters_eq_one_of_odd_card'`**: 奇数位数で real Irr = 1 (Peterfalvi §3 (1.1))。

AxiomsCheck に `brauer_permutation_lemma'` を追加 — allowlist `{propext, Classical.choice, Quot.sound}`
の 3 公理のみ依存を確認 (sorryAx 無し)。`lake build OddOrder` green。issue close。

なお `BrauerPermutation.lean` の従来の `brauer_permutation_lemma` (5 引数版) と
`*_of_odd_card` 系はそのまま (条件付きだが sorry-free)。S08 用にはどちらでも呼べる。

## 完了条件

- [x] `BrauerPermutation.lean` の `brauer_permutation_lemma` から `sorry` が消える
      (元から sorry-free; 加えて無条件版 `brauer_permutation_lemma'` を提供)。
- [x] `lake build OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation` が通る。
- [x] `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る
      (line 188 の `sibleySetup_is_coherent` sorry は本 issue と無関係の別件)。

## 参照

- parent: `issues/0020-peterfalvi-part1-character-stubs.md`
- depends on: `issues/closed/0021-peterfalvi-second-orthogonality.md`
- depends on: `issues/0027-peterfalvi-column-orthogonality-core.md`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s06_dade_certain_subgroup.md`
