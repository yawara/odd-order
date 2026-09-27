# mathlib v4.33.0 → v4.34.1 移行記録

2026-09-27 実施 (branch `mathlib-v434`、issue [0189](../../issues/closed/0189-mathlib-v434-bump.md))。

## pin

| | 旧 | 新 |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.33.0` | `leanprover/lean4:v4.34.1` |
| mathlib `rev` | `db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`) | `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1` = `stable`) |

drift = **1,032 commits** (v4.33 の 2.2 倍)、mathlib 側 5,318 file / +96k −62k。
v4.34.1 は 2026-09-24 リリース。v4.35.0 は rc3 止まりなので CLAUDE.md の「rc には当てない」に従い対象外。

### 事前実測 (両 tag を展開して機械照合)

| 項目 | 値 |
|---|---|
| 我々の直 import 面 | 408 module 中 **269 (66%)** が変更対象、削除 0、**deprecated module 2** |
| mathlib の新規 deprecated | 706 宣言 |
| Lean core の新規 deprecated | 165 宣言 |
| 同名のまま文が変わった補題 (repo が踏みうるもの) | 機械照合で 26 候補 → 実害 7 |

⚠ **静的照合の盲点**: 名前の再利用 (`Finsupp.mapDomain_apply` / `Equiv.setCongr`) と添字規約の変更
(`List.TFAE.out`) には deprecated 属性が付かないので、deprecated 一覧では拾えない。
**同名宣言の文 (statement) を両 tag で比較**する照合が有効だった (手順は末尾)。

## 最大の破壊的変更 — Lean core の if-then-else 補題の改名

Lean #14501 (`since := "2026-07-21"`) で次が deprecated になった (同じ文の新名がある)。
lint 純ゼロ gate なので全面改名 (**2,403 箇所**、コメント・docstring 内の言及を含む)。

| 旧 | 新 | 箇所 |
|---|---|---|
| `if_pos` | `ite_eq_left` | 945 |
| `if_neg` | `ite_eq_right` | 1,235 |
| `dif_pos` | `dite_eq_left` | 107 |
| `dif_neg` | `dite_eq_right` | 74 |
| `if_true` | `ite_true` | 23 |
| `if_false` | `ite_false` | 19 |

新名は 4〜6 文字長いので **100 桁を超えた 54 行を折返した** (リポジトリの慣行 = タクティク列 +2)。
機械折返しは `⟨…⟩` の内側で切ることがあるので、目視で 10 箇所ほど手直しした。

## 名前の変更 (機械リネーム)

- `TensorProduct.induction_on` → **`TensorProduct.inductionOn`** (36 箇所)。**`zero` ケースが消えた**
  (新版は `tmul`/`add` のみ)。さらに `@[induction_eliminator]` が付いたので、`using` 無しの素の
  `induction z with` も `| zero` を受け付けない (2 箇所、`AbsolutelyIrreducible`)。
- `Subgroup.normalizer_inf_normalizer_le_normalizer_sup` → `Subgroup.inf_normalizer_le_normalizer_sup` (17)
- `List.prod_eq_pow_card` → `List.prod_eq_pow_length` (1)
- deprecated module: `Mathlib.Data.Complex.Basic` → `Mathlib.Basic.Complex.Basic` (7)、
  `Mathlib.Data.Finite.Prod` → `Mathlib.Basic.Finite.Prod` (2) (mathlib が `Mathlib/Basic/` を新設)

## ビルドでのみ露見した破壊 (4 ラウンド、18 module)

| 変更 | 症状 | 対応 |
|---|---|---|
| **`List.TFAE.out` が 1-indexed に** | `.out 0 3` は "TFAE indices start at 1" で落ちる。**`.out 1 2` は黙って別の命題になる** | 全 23 箇所の添字を +1 |
| **`Finsupp.mapDomain_apply` の名前再利用** | 単射版は `mapDomain_apply_of_injective` へ改名、旧名は一般形 (`= x.sum …`) に再利用 → 型エラー | 2 箇所を改名 |
| **`Equiv.setCongr` の名前再利用** | 旧 `Equiv.setCongr (h : s = t) : s ≃ t` は **`Set.equivOfEq`** へ。旧 `Equiv.Set.congr (e : α ≃ β)` が新 `Equiv.setCongr` に | 14 箇所を `Set.equivOfEq` に |
| `Subgroup.isMulCommutative_closure` の仮説が `S.Pairwise Commute` に | 仮説に `x ≠ y` binder が増え、ゴールが `Commute x y` になる (**`simpa` は `Commute` を展開しない** → `exact` に) | 10 箇所 |
| `isIntegral_algebraMap_iff` | 単射性の明示引数 → `[FaithfulSMul A B]` instance | 3 |
| `DoubleCoset.eq` / `out_eq'` | `H K` が implicit に。`mk_out_eq_mul` の結論が `∃ h ∈ H, ∃ k ∈ K, …` に | 3 |
| `Nat.multiplicity_eq_factorization` | `n ≠ 0` 仮説が消滅 | 4 |
| `IsWellFounded` | deprecated (`WellFounded` を使え) | `wellFounded_lt` に (1) |
| `Representation.isTrivial_def` | `@[simp]` が外れた → trivial 表現の指標計算が `simp` で閉じない | simp 引数に明示 (3) |
| import 構造 | `IsArtinian` / `isArtinian_of_tower` / `WellFoundedLT (Submodule F V)` が推移 import されなくなった | `Mathlib.RingTheory.Artinian.Module` を明示 import (2) |
| `convert` が以前より多く閉じる | 後続の `congr 1` が `No goals` | 削除 (1) |
| header linter の書き直し | module docstring が import より前にあると警告 | `S09_BetaDecompOrthogonality` の冒頭を標準形に |

## linter の変更

- 標準セット内で **`linter.style.nativeDecide` → `linter.style.native`** に改名 (`decide +native` も検出)。
  repo は使っていないので影響なし。
- **`linter.internalConstructors` が新設** (`defValue := true`、**error** を出す)。`_mkInternal` 構成子の
  参照を禁止する (主に圏論の `Hom._mkInternal`、`Rep`)。repo 影響なし。
- `linter.style.header` が大幅に書き直された (上表の 1 件)。

## 同時に入れたリファクタ

1. **互換フラグの棚卸し** — v4.33 で入れた per-declaration 互換フラグ
   `set_option backward.isDefEq.respectTransparency false in` (269 箇所) を v4.34.1 上で 1 本ずつ判定。
   mathlib 自身も同フラグを 6,909 → 4,569 に減らしている。file ごとに全フラグを外して個別
   elaborate し、エラー/警告が出た宣言にだけ戻す方式で **269 → 231** (20 file / 38 箇所が不要)。
2. **upstream 化・既存 mathlib との重複の解消** (v4.34.1 の新宣言と repo の宣言名を機械照合 +
   docstring の「mathlib に無い」主張をサブエージェントで全件検証):
   - `Subgroup.normal_of_le_center` が **v4.34 で mathlib に入った** → repo 内の**同一補題 8 本**
     (Isaacs Ch03/05/06/10、GroupTheory 3 本、Higman 1 本) を削除して置換。
   - `IsCyclic.subgroup_eq_iff_card_eq` (v4.34 新設、位数が等しい部分群は一致) が
     repo の `subgroup_eq_of_card_eq_prime_of_isCyclic` (素数位数限定の弱い版) を包含 → 削除して置換。
   - `Subgroup.centralizer_le_normalizer` (v4.30 から mathlib にある) の自前コピー 2 本
     (`Isaacs.Ch04.centralizer_le_normalizer_subgroup` / `Isaacs.Ch07.centralizer_le_normalizer`) を削除。
   - `Subgroup.isMulCommutative_closure` の一般化で不要になった自前
     `isMulCommutative_closure_of_forall_commute` を削除。
   - `commutator_bot_left_eq` は mathlib `Subgroup.commutator_bot_left` の薄いラッパーだったので削除。
3. **repo 内の重複の解消** (今回の改修で触れた file に限る):
   - `isMulCommutative_sup_of_le_centralizer` の**逐語コピー 3 本** (GroupTheory / BG §15 / Higman private)
     を `OddOrder/Mathlib/Subgroup.lean` の `Subgroup.isMulCommutative_sup_of_le_centralizer` に一本化。
   - 「有理代数的整数は整数」の独立な証明 2 本のうち `exists_int_of_isIntegral_of_mem_range_rat` を
     `isIntegral_rat_imp_int` からの導出に置換。
4. **"Try this" 提案の解消** — ビルドログに出ていた 14 件 (`ring` が失敗して `ring_nf` に
   フォールバック 7 件 → `ring_nf`/`rfl`、`rw [h]; assumption` → `rwa [h]` 6 件、ほか)。
5. **stale docstring** — 「mathlib v4.29.1 / v4.30.0-rc2 に不在」系の主張 56 行を v4.34.1 で全件
   再確認し、ラベルを更新。うち**事実誤り 5 件**を訂正 (`Subgroup.piCore` は存在しない、
   `MonoidHom.CentralProduct` は存在しない、`Subgroup.normalizer` は集合を取る、
   `S02_RepresentationsBasic` で repo 宣言が "mathlib ✓" と表示されていた、名前の誤記 2 件)。
6. **モジュール分割** — `S08_XBlockCounting` は改名の折返しで 1486 → 1490 行と上限 1500 の直前に
   なったので、中心交換子への制限・直交性の補題群を新 leaf `S08_CentralCommutatorRestriction` に
   移した (依存関係の無いまとまりを主題で切り出し、module 名は不変)。

## 手順 (再現用)

```bash
# 1. pin
printf 'leanprover/lean4:v4.34.1\n' > lean-toolchain
# lakefile.toml の mathlib rev を tag v4.34.1 の SHA に
lake update mathlib          # lake-manifest.json 更新 + toolchain + cache get (所要 ~1.5 分)

# 2. 影響の事前見積り
git -C .lake/packages/mathlib archive v4.33.0 Mathlib | tar -x -C <dir>/ml433
git -C .lake/packages/mathlib archive v4.34.1 Mathlib | tar -x -C <dir>/ml4341
#   (a) deprecated 属性付き宣言を namespace 追跡つきで抽出し、新規分を repo の token と照合
#   (b) 同名宣言の statement を両 tree で比較し、文が変わったものを repo の token と照合  ← 名前再利用はここでしか拾えない
#   (c) Lean core (~/.elan/toolchains/*/src/lean) にも (a) を適用 (if_pos 系はここ)
#   (d) repo の直 import のうち `deprecated_module` になったものを列挙

# 3. 機械リネームを全部当ててから 1 回ビルド
# 4. 失敗 module を直して再ビルド (深い直列依存のため 4 ラウンド、各 2〜15 分)
# 5. 互換フラグの棚卸し: file ごとに外して `lean` で個別 elaborate (依存は green 済み)
# 6. lake build OddOrder → bin/check-warnings --strict → bin/count-sorry → bin/check-links / check-doc-names
```

⚠ **ビルド中に `lake env lean` を多数並列で走らせない**。Lake の起動処理が走行中の `lake build` と
競合し、ビルドの 1 module あたりの間隔が 15 秒 → 1 分に落ちた。並列の個別 elaborate は
`LEAN_PATH=$(lake env printenv LEAN_PATH)` を一度だけ取り、`lean` を直接起動する (競合が消えた)。

## 最終状態

| gate | 結果 |
|---|---|
| `lake build OddOrder` | **green** (5,566 jobs = 新 leaf 分 +1。上流変更後のフル再ビルド 13 分 18 秒) |
| `bin/check-warnings --strict` | **非 sorry 警告ゼロ / PANIC ゼロ** |
| AxiomsCheck | **OK** (6,030 件の `#assert_only_allowed_axioms` がすべて allowlist 内) |
| `bin/count-sorry` | **0** (非退行) |
| `bin/check-links` | 0 broken / 806 markdown files |
| `bin/check-doc-names` | 0 unresolved / 1,720 Lean files (gate 自体のキャッシュ無しモードの不具合も修正) |
| 変更規模 | 434 Lean file / +3,033 −3,221 (branch 全体 440 file / +3,132 −3,237) |

commit 構成 (branch `mathlib-v434`):

1. `9c16ef869` bump + 強制修正 (機械リネーム・ビルドで露見した破壊)
2. `2f507e069` 互換フラグ 269 → 231
3. `5a48263c6` 重複補題の解消 + Try-this 提案の解消
4. `481a23dbe` 「mathlib に不在」主張の再検証と事実誤りの訂正
5. `8989131f8` `S08_XBlockCounting` の分割
6. `8ad92814b` `bin/check-doc-names` の修正
