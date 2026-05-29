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
(`card_irreducibleCharacter_le`, `CharacterCount.lean`)。`≥` 方向 (completeness) の
**解析的コア `classFunction_eq_zero_of_orthogonal` (`f ⊥ Irr ⇒ f=0`) は 2026-05-30 に landed**
(sorry-free, axiom = {propext, Classical.choice, Quot.sound})。残りは span=⊤ / count の機械的接続。
mathlib v4.30 に直接の数え上げは無し (Wedderburn-Artin はあるが
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
- [x] **completeness core** (`f ⊥ Irr G ⇒ f = 0`) — **landed (sorry-free, axiom-checked)**
      2026-05-30, `classFunction_eq_zero_of_orthogonal` (CharacterCompleteness.lean)。
      reg := `Representation.ofMulAction ℂ G G`、`Ti := equivLinearMapAsModule reg reg
      (classFunctionIntertwiner (classFunctionInv f) reg)`。`IsSemisimpleModule.sSup_simples_eq_top`
      + `sSup_le` で「全 simple ℂ[G]-部分加群 N ≤ ker Ti ⇒ ker=⊤ ⇒ Ti=0」(`LinearMap.ker_eq_top`)。
      最後に `Ti (single 1 1)` の係数抽出 (`LinearMap.sum_apply`/`Finset.sum_apply'`/`Finset.sum_ite_eq'`)
      で `f(g⁻¹)=0` ⇒ `f=0`。採用ブリッジ = **route (b)**: `(ofSubmodule' N).toRepresentation`。
      補題 `ofSubmodulePrime_coe_smul` (asModule の `single g a` 作用 = `ρ` 制限, `single_smul` 2 回 + `rfl`),
      `ofSubmodulePrimeAsModuleEquiv` (`↥N ≃ₗ[ℂ[G]] σN.asModule`, 恒等写像; `↥N` と `↥σN.toSubmodule` は
      **同一型 (rfl)**, `map_smul'` は `Subtype.ext`+`Submodule.coe_smul`+上記補題),
      `ofSubmodulePrime_isIrreducible` (`irreducible_iff_isSimpleModule_asModule` →
      `(equiv).isSimpleModule_iff.mp inferInstance`), `classFunctionOperator_ofSubmodulePrime_coe`
      (operator 値ブリッジ, 各項 `(σN g w).val = reg g w.val` は `rfl`)。
      **diamond 回避の要点** (継続者向け): (1) `IsSimpleModule.congr` は asModule の
      `AddCommMonoid` diamond (`deriving` 由来 vs `AddCommGroup.toAddCommMonoid`) で application
      type mismatch → 代わりに `LinearEquiv.isSimpleModule_iff.mp` を使う (exact が defeq で吸収);
      (2) `IsSemisimpleModule ℂ[G] reg.asModule` / `sSup_simples_eq_top` の `Module ℂ[G] reg.asModule`
      合成は **直接 `inferInstance` で失敗**(同 diamond)→ `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule reg |>.mp inferInstance` で得る
      (Maschke `IsSemisimpleRepresentation` instance, 要 `[Finite G]`+`NeZero`)+ 宣言全体に
      `set_option backward.isDefEq.respectTransparency false`; (3) `reg` は `let`(not `set`)。
- [x] **span = ⊤** / **count** (`Nat.card Irr = #ConjClasses`) / `CharacterTableIndexing.ofFinite`
      — **landed (sorry-free, axiom-checked) 2026-05-30** (CharacterCompleteness.lean, section
      `Count` + `TableIndexing`)。count は completeness の解析的コアから直接導出: 内積写像
      `innerAgainstIrreducibleCharacters : ClassFunction G ℂ →ₗ[ℂ] (Irr G → ℂ)`, `f ↦ (χ ↦ (f,χ))`
      は `inner` が第 1 引数線形 (`inner_add_left`/`inner_smul_left`) なので well-defined。
      `classFunction_eq_zero_of_orthogonal` で **単射** ⇒
      `#ConjClasses = finrank (ClassFunction) ≤ finrank (Irr→ℂ) = #Irr`
      (`LinearMap.finrank_le_finrank_of_injective` + `finrank_classFunction` +
      `Module.finrank_fintype_fun_eq_card`)。`≤` は `card_irreducibleCharacter_le` で
      `le_antisymm`。span=⊤ は count=finrank + 線形独立 + `[Nonempty]` (= `trivialIrreducibleCharacter`)
      ⇒ `LinearIndependent.span_eq_top_of_card_eq_finrank`。`CharacterTableIndexing.ofFinite'`
      (G) `[Finite G]` は `ofFinite` の `hcard` を count で供給。`instCharacterTableIndexingOfFinite`
      も追加 (無条件 instance)。AxiomsCheck に
      `classFunction_eq_zero_of_orthogonal` / `card_irreducibleCharacter_eq` /
      `span_irreducibleCharacter_eq_top` を追加 (all 3-axiom allowlist)。
- [x] 0027: **無条件化 landed + closed (2026-05-30)**。新 downstream ファイル
      `ColumnOrthogonality.lean` に `column_orthogonality_{diagonal,conjugate,not_conjugate}`
      (`[Finite G]` のみ) を sorry-free で追加。`instCharacterTableIndexingOfFinite` +
      `CharacterTableWeightedRowOrthogonality.ofRowOrthogonality characterTableRowOrthogonality_holds`
      で `idx`/`hrow` を discharge。AxiomsCheck で allowlist-only 確認。
- [x] 0022: **無条件化 landed + closed (2026-05-30)**。複素共役置換 σ を新 downstream ファイル
      `BrauerPermutationUnconditional.lean` で構成 (`Representation.IsIrreducible.dual` 経由)、
      `brauer_permutation_lemma'` (`[Finite G]` のみ) を sorry-free で追加。AxiomsCheck allowlist-only。

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

## CLOSED — 2026-05-30 (全完了条件達成, adversarial review 検証済)

4 件の完了条件すべて達成・検証済 (`notes/meta/peterfalvi_overnight_undefined.md`):

- [x] `card_irreducibleCharacter_eq [Finite G] : Nat.card (IrreducibleCharacter G) =
  Nat.card (ConjClasses G)` sorry-free (`CharacterCompleteness.lean`)。
- [x] `CharacterTableIndexing.ofFinite'` / `instCharacterTableIndexingOfFinite` で
  `[Finite G]` から構成可能。
- [x] AxiomsCheck: `card_irreducibleCharacter_eq` / `classFunction_eq_zero_of_orthogonal`
  / `span_irreducibleCharacter_eq_top` が 3-axiom allowlist のみ依存
  (`lake build OddOrder.AxiomsCheck` green で確認)。
- [x] downstream 0027 (column orthogonality) / 0022 (Brauer permutation) 無条件化 + close。

statement faithfulness 確認済: `IrreducibleCharacter` / `IsIrreducibleCharacter` は
非 vacuous な実定義、`card_irreducibleCharacter_eq` は仮定を隠さない真の Isaacs Thm 2.8。
**conditional scaffold ではない**。

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
