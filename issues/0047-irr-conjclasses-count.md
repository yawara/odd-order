---
id: 47
slug: irr-conjclasses-count
title: "RepTheory: |Irr G| = |ConjClasses G| (square character-table count)"
created: 2026-05-29
---

# RepTheory: |Irr G| = |ConjClasses G| (square character-table count)

## 背景

`CharacterTableIndexing G` (= 正方指標表 = 行 `IrreducibleCharacter G`, 列 `ConjClasses G`,
`card_eq`) は issues 0027 (column orthogonality) / 0022 (Brauer permutation) を
**無条件化**するために必須。`card_eq` がまさに `|Irr G| = |ConjClasses G|`。

`≤` 方向は **2026-05-29 に sorry-free + axiom-checked で landed**
(`card_irreducibleCharacter_le`, `CharacterCount.lean`)。残るは **`≥` 方向 (completeness)**:
既約指標が類関数空間を張ること。mathlib v4.30 に無し (Wedderburn-Artin はあるが
group-algebra center の class-sums 基底 / 指標↔単純加群の数え上げは無い)。

## 現状 (2026-05-29, branch chartable-bridge)

既に landed (sorry-free, axiom-checked):
- `character_inv` : χ(g⁻¹) = star(χ g) (CharacterConjugate.lean, 既存)
- `irreducibleCharacter_inner` / `characterTableRowOrthogonality_holds` (CharacterRowOrthogonality.lean)
- `classFunctionEquivConjClasses`, `finrank_classFunction` (= #ConjClasses),
  `linearIndependent_irreducibleCharacter`, `finite_irreducibleCharacter`,
  `card_irreducibleCharacter_le` (CharacterCount.lean)
- `classFunctionOperator` `T_ρ f = ∑_g f(g)•ρ(g)` + `classFunctionOperator_comm`
  (intertwiner) (CharacterCompleteness.lean)

## やること (Route B = analytic completeness; foundation を最大活用)

- [x] (foundation) `≤` 方向 + 類関数空間の次元 + 線形独立 + 有限性
- [x] `classFunctionOperator` + intertwiner lemma
- [ ] **Schur**: ρ 既約 ⇒ `T_ρ f = c • id` (mathlib `Representation.IsIrreducible.finrank_intertwiningMap_self = 1`
      を使い, intertwiner が 1 次元空間 = span{id} の元であることから). `IntertwiningMap` API 要調査。
- [ ] **scalar = 0**: `c` を trace で取り出し `trace (T_ρ f) = ∑_g f(g) χ_ρ(g)`,
      `f ⊥ Irr G` (= `inner f χ = 0` 全 χ) から `c = 0`。conjugate convention (character_inv) に注意。
- [ ] **completeness**: `f ⊥ Irr G ⇒ f = 0`。
      `T_ρ f` は中心元 `Φf = ∑ f(g)•single g ∈ Z(ℂ[G])` の作用。各単純加群で 0 ⇒
      semisimple (Maschke) より regular module `ℂ[G]` の simple submodule の sup = ⊤ で 0 ⇒
      `Φf • 1 = Φf = 0` ⇒ f = 0。mathlib `IsSemisimpleModule` の
      "⊤ = sSup simple submodules" 系 lemma の有無を要調査 (DFinsupp 直和分解を避けたい)。
- [ ] **span = ⊤**: completeness より, 任意 f = ∑_χ (f,χ)χ + r で r ⊥ Irr ⇒ r = 0 ⇒ f ∈ span。
      `finite_irreducibleCharacter` で有限和が使える。
- [ ] **count**: span = ⊤ + 線形独立 ⇒ 既約指標は基底 ⇒ `Nat.card Irr = finrank CF = #ConjClasses`。
- [ ] `CharacterTableIndexing.ofFinite` で `idx : CharacterTableIndexing G` を `[Finite G]` から構成。
- [ ] 0027: `column_orthogonality_cases` + 3 corollary から `idx`/`hrow` 仮定を落として無条件化 → close。
- [ ] 0022: 加えて複素共役置換 σ (χ ↦ χ̄, dual rep) の構成 + h_real_irr/h_compat → close。

### Route A (代替, Wedderburn) — mathlib support は多いが absent piece も多い
`ℂ[G] ≃ₐ ∏ Mₙᵢ(ℂ)` (mathlib `exists_algEquiv_pi_matrix_of_isAlgClosed`) ⇒ #factors。
要 build: center of ∏Mₙ = ∏ℂ (dim = #factors), `finrank Z(ℂ[G]) = #ConjClasses`
(class-sums 基底, MonoidAlgebra center criterion = fiddly), #simple modules = #factors,
#Irr = #simple (char↔simple bijection)。Route B より長いチェーン。

## 完了条件

- `Nat.card (IrreducibleCharacter G) = Nat.card (ConjClasses G)` (`[Finite G]`) が sorry-free。
- `CharacterTableIndexing G` が `[Finite G]` から構成できる。
- AxiomsCheck に追加して allowlist のみ依存を確認。
- (downstream) 0027 / 0022 が無条件化されて close できる。

## 参照

- depends-on (foundation): commits 44b8fd4, d5a8133, 8cacc84 (branch chartable-bridge)
- unblocks: `issues/0027-peterfalvi-column-orthogonality-core.md`,
  `issues/0022-peterfalvi-brauer-permutation.md`
- memory: `scaffold-sorry-free-not-done.md` (これらが conditional scaffold である理由)
- mathlib: `RepresentationTheory/Character.lean` (`char_orthonormal`, `char_iso`),
  `RepresentationTheory/Irreducible.lean` (`finrank_intertwiningMap_self`,
  `irreducible_iff_isSimpleModule_asModule`), `RepresentationTheory/Maschke.lean`,
  `RingTheory/SimpleModule/WedderburnArtin.lean`
- files: `OddOrder/GroupTheory/RepresentationTheory/Character{Conjugate,RowOrthogonality,Count,Completeness}.lean`
