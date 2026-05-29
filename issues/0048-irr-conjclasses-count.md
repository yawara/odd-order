---
id: 48
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
- [x] **Schur**: `classFunctionOperator_eq_smul_id` (T_ρ f = c•id) — mathlib
      `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed` で
      自己 intertwiner = `algebraMap ℂ _ c` = `c•1`。`classFunctionIntertwiner` で
      `classFunctionOperator` を `IntertwiningMap ρ ρ` に梱包。(commit a7197cb)
- [x] **scalar = 0**: `trace_classFunctionOperator` (trace = ∑ f(g)χ_ρ(g)) +
      `classFunctionOperator_eq_zero_of_sum_eq_zero` (∑ f(g)χ_ρ(g)=0 ⇒ T_ρ f=0;
      c·finrank=trace=0, finrank>0)。(commit a7197cb)
- [x] **universe transfer**: `exists_isIrreducibleCharacter_eq` — 任意 universe の有限次元既約
      σ に対し ∃ χ∈Irr, χ=σ.character。`IsIrreducibleCharacter` が Type 0 carrier しか
      量化しないので Fin n→ℂ へ transport (`transportRep`/`transportRep_character`/
      `transportRep_isIrreducible`)。(commit 729175d)
- [x] **orthogonality ⇒ sum=0**: `classFunctionInv` (g↦f g⁻¹) +
      `sum_classFunctionInv_character_eq_zero` (f⊥Irr ⇒ ∀ f.d.既約σ, ∑ f(g⁻¹)χ_σ(g)=0)。
      (commit, 2026-05-30)
- [ ] **completeness core** (`f ⊥ Irr G ⇒ f = 0`) — **残ブロッカー**。設計確定:
      reg := `Representation.ofMulAction ℂ G G`、`Ti := classFunctionIntertwiner (classFunctionInv f) reg`、
      `Ti_mod := equivLinearMapAsModule reg reg Ti : reg.asModule →ₗ[ℂ[G]] reg.asModule`。
      `IsSemisimpleModule ℂ[G] reg.asModule` (Maschke instance, 要 `[Finite G]`+`NeZero (Nat.card G:ℂ)`) と
      `IsSemisimpleModule.sSup_simples_eq_top` + `sSup_le` で「全 simple 部分加群 ≤ ker Ti_mod ⇒ ker=⊤ ⇒ Ti_mod=0」
      (`LinearMap.ker_eq_top`)。最後に `Ti_mod (single 1 1)=∑ f(g⁻¹)•single g 1=0` から Finsupp 係数抽出で finv=0 ⇒ f=0。
      **未解決ギャップ**: simple ℂ[G]-部分加群 W に対し「W 上の表現が既約 ∧ その指標が Irr に入り ∧
      T が W 上で消える (`classFunctionOperator_eq_zero_of_sum_eq_zero` + `sum_classFunctionInv...`)」
      を結ぶブリッジ。2 経路:
      (a) `Representation.ofModule ↥W` (既約は `isSimpleModule_iff_irreducible_ofModule` で無料) だが
          carrier が `RestrictScalars ℂ ℂ[G] ↥W` で `FiniteDimensional` instance + 作用関係が addEquiv 経由で煩雑;
      (b) `(subrepresentationSubmoduleOrderIso.symm W).toRepresentation` (carrier は素直な ℂ-部分空間) だが
          atom→`IsIrreducible toRepresentation` の橋 (asModule 構造一致) を自前で要証明。
      どちらも ~40-60 行の sub-object ブリッジ補題が必要 (mathlib に直接対応なし)。
- [ ] **span = ⊤** / **count** (`Nat.card Irr = #ConjClasses`) / `CharacterTableIndexing.ofFinite`
      (count を `hcard` に供給するだけ。既存 def)。
- [ ] 0027: `column_orthogonality_cases_ofRowOrthogonality (ofFinite count) characterTableRowOrthogonality_holds`
      で無条件化 (downstream の新定理; upstream の sorry は無し) → close。
- [ ] 0022: 加えて複素共役置換 σ → close。

### 2026-05-30 技術メモ (継続者向け)

**`asModule` 型シノニムの instance 解決の罠** (重要): `reg.asModule` 等の `Representation.asModule`
に対する `Module ℂ[G] _` / `IsSimpleModule ℂ[G] _` の instance は、**型注釈 (`haveI : IsSimpleModule ℂ[G] σ.asModule := …`)
で書くと再探索が走り失敗する**。mathlib 同様 `set_option backward.isDefEq.respectTransparency false in` を
宣言に付ける、かつ baked instance (lemma の戻り値型に埋まったもの) を使う / `IsSimpleModule.congr` 等で
型注釈を避けると通る。`transportRep_isIrreducible` 参照。`equivLinearMapAsModule` の戻り値は instance が
ベイク済みなので注釈なしで使える。

**確認済み mathlib API**: `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`,
`Representation.IntertwiningMap.equivLinearMapAsModule`, `LinearEquiv.conjRingEquiv`, `LinearMap.trace_conj'`,
`Module.finBasis`, `IsSimpleModule.congr`/`LinearEquiv.isSimpleModule_iff`/`isSimpleModule_iff_isAtom`,
`Maschke: instance IsSemisimpleModule k[G] V` (`[Group G][Field k][Finite G][NeZero (Nat.card G:k)]`),
`IsSemisimpleModule.sSup_simples_eq_top`, `Representation.ofMulAction`/`ofMulAction_single`/
`ofMulActionSelfAsModuleEquiv`, `Representation.single_smul`, `Representation.ofModule`/
`isSimpleModule_iff_irreducible_ofModule`, `Subrepresentation.{toRepresentation,asSubmodule,ofSubmodule',
subrepresentationSubmoduleOrderIso}`, `LinearMap.ker_eq_top`, `Module.finrank_pos`, `Finsupp.single_eq_same`.

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
