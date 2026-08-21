# mathlib v4.32.2 → v4.33.0 移行記録

2026-08-20 実施 (branch `mathlib-v433`、issue [0183](../../issues/closed/0183-mathlib-v433-bump.md))。

## pin

| | 旧 | 新 |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.32.2` | `leanprover/lean4:v4.33.0` |
| mathlib `rev` | `905b95818eb32af7874a58b427f50c1711a5e96c` | `db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0` = `stable`) |

drift = **470 commits**。Lean v4.33.0 final は 2026-08-10 リリース、mathlib `stable` も同日同 tag。
CLAUDE.md の「**final を待って上げる** (rc に当てない)」方針どおり rc はスキップした。

### 事前実測 (両 tag を展開して機械照合)

| 項目 | 値 |
|---|---|
| 我々の直 import 面 | 407 module 中 **260 (64%)** が変更対象 (v4.32 系は 30%) |
| upstream の削除 | 宣言 1430 / うち deprecated alias 826。v4.33 で新規 deprecated 758 |
| repo が踏む名前 | 21 名前 / 1,938 箇所 / 371 file |

## 最大の破壊的変更 — Lean 4.33 の `isDefEq` がトランスパレンシーを尊重

Lean 4.33 で defeq 判定が transparency 設定を尊重するようになり、`rfl` / `simp` の閉じ判定・
`rw` の照合・instance 合成が **semireducible な定義を勝手に展開しなくなった**。upstream 自身が
互換フラグ `set_option backward.isDefEq.respectTransparency false in` を **10,906 箇所** (v4.32.2 は
5,606) で使って移行しており、本リポジトリでも同じ手段を採った (**269 箇所 / 156 file**、
うち `.types` 版が 2)。

典型的な症状 (すべて本リポで発生):

- `Tactic 'rewrite' failed: Did not find an occurrence of the pattern` — 見た目は一致しているのに
  照合が失敗する (`⟦Quotient.out ?q⟧`、`QuotientGroup.map ?N ?M ?f ?h ↑?x`、`Subgroup.mem_map` 等)。
  `GroupTheory/Coset/Defs.lean` の `leftRel`/`rightRel` が `implicit_reducible` →
  **`instance_reducible`** に変わったのが商群まわりの主因。
- `Type mismatch: After simplification, term ... has type X but is expected to have type Y`
  (`simpa using h` が閉じなくなる)
- `failed to synthesize instance` / `decide` が `Decidable` を作れない
- エラーメッセージに `Note: The target expression is not type-correct under the 'implicit'
  transparency level` が付くものは確実にこの系統。

**方針**: 教科書的な内容に関わらない純粋な defeq 問題は upstream と同じ互換フラグで解決し、
証明の書き換えはしない (mathlib 側が同じ扱いをしているので upstream 適性も損なわない)。

### ⚙ 必要箇所の特定手順 (逐次ビルドを避ける)

素朴に「フルビルド → 最初のエラーを直す」を繰り返すと、深い直列依存 (Peterfalvi S11→S16) では
**1 ラウンドで 1 module しか進まない**。実際 25 ラウンド回して 5,168/5,490 で頭打ちになった。
そこで次の 3 段階に切り替えた:

1. **lakefile に一時的なグローバル互換フラグ** (`weak.backward.isDefEq.respectTransparency = false`)
   を置いてフルビルドを通し、全 module の olean を作る。
   ⚠ グローバルにすると**逆に壊れる箇所**が出る (`PRank` の whnf タイムアウト、simp が進み過ぎて
   `No goals` になる 20 箇所ほど)。そこは一時的に `= true` のカウンターフラグで凌ぐ。
2. **全 1,705 file を `lake env lean` でフラグ無し個別 elaborate** (並列 12)。依存の olean は
   既にあるので、どの file のどの行がフラグを要するかが**一度に全部**分かる。
   実測 **47 file / 120 箇所**だけだった (所要 ~15 分、CPU 140 分)。
3. 検出箇所に per-declaration フラグを入れ、**グローバルフラグとカウンターフラグを撤去**して
   再検査 → フルビルド。

この手順なら「グローバルに緩めっぱなし」にせず、mathlib と同じ per-declaration 粒度に落とせる。

## 名前の変更 (機械リネーム 1,917 箇所 / 373 file)

### solvable API が `Group` 名前空間へ (2026-07-16/17)

| 旧 | 新 | 箇所 |
|---|---|---|
| `IsSolvable` | `Group.IsSolvable` | 1306 |
| `solvable_of_solvable_injective` | `Group.isSolvable_of_isSolvable_injective` | 98 |
| `IsSolvable.commutator_lt_top_of_nontrivial` | `Group.IsSolvable.commutator_lt_top_of_nontrivial` | 58 |
| `solvable_of_surjective` | `Group.isSolvable_of_surjective` | 54 |
| `isSolvable_of_comm` | `Group.isSolvable_of_comm` | 46 |
| `solvable_of_ker_le_range` | `Group.isSolvable_of_ker_le_range` | 28 |
| `IsSolvable.commutator_lt_of_ne_bot` | `Group.IsSolvable.commutator_lt_of_ne_bot` | 6 |
| `isSolvable_def` | `Group.isSolvable_def` | 2 |
| `not_solvable_of_mem_derivedSeries` | `not_isSolvable_of_mem_derivedSeries` | 1 |
| `subgroup_solvable_of_solvable` | **alias 無しで削除** (instance 化)。本リポでは docstring 参照のみ | 2 |

`_root_.IsSolvable` の deprecated alias は残っているので**ビルドは通るが警告**になる。
本リポは lint 純ゼロ gate なので全面改名が必須だった。

### `setOf` → `ofPred` (2026-07-09)

`Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (301 箇所)、`Set.toFinset_setOf` → `Set.toFinset_ofPred` (5)、
`Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot` (1)。

### `restrict` → `domRestrict` (2026-07-19) ⚠ 名前の再利用に注意

- 補題は deprecated alias 付き: `MonoidHom.ker_restrict` → `ker_domRestrict`、
  `restrict_range` → `domRestrict_range`、`restrict_apply` → `domRestrict_apply`。
- **`MonoidHom.restrict` (定義本体) は alias 無しで消え、同じ名前が別の関数
  (`Set.MapsTo` から作る両側制限) に再利用された**。したがって `f.restrict H` は
  「deprecated 警告」ではなく **型エラー**になる (`Subgroup G` を渡したのに `Set.MapsTo` を要求される)。
  本リポの被弾は 10 箇所 (`ProblemsProductMultiplier` / `ProblemsCenterIndex` / `CNGroupStructure`)。
  自前補題 `ker_restrict_fst`/`ker_restrict_snd` も `ker_domRestrict_fst`/`_snd` に改名した。

### `Ideal.mul_le_left` と `Ideal.mul_le_right` が入れ替わった

v4.32.2: `mul_le_left : I * J ≤ J` / `mul_le_right : I * J ≤ I` (後者に `IsTwoSided`)
→ v4.33.0 で**名前が交換**された。deprecated alias が無いので静かに型エラーになる。

### `MonoidAlgebra.induction_on`

- ケース名 `hM` / `hadd` / `hsmul` → **`of` / `add` / `smul`** (48 箇所 / 13 file)
- motive の名前付き引数 `(p := …)` → **`(motive := …)`** (2 箇所)

### その他

`QuadraticMap.{smul,sum,zero,sub}_apply` (protected alias 化)、`LinearEquiv.ofLinear` → `ofLinearMap`、
`Finsupp.mapDomain_notin_range` → `mapDomain_of_notMem_range`。

## linter の変更

- **`linter.style.haveILetI` が新設され `defValue := true`** — `mathlibStandardSet` には
  入っていないが**既定で有効**なので、opt-in の有無に関わらず効く。「ゴールが Prop なら
  `haveI`/`letI` でなく `have`/`let` を使え」。本リポでは **12,169 箇所**を機械置換した
  (14,508 → 2,339)。⚠ 1 箇所だけ `letI` が universe level 推論に必須で、
  `set_option linter.style.haveILetI false in` の per-decl 例外にした
  (`Peterfalvi/Appendices/Suzuki/PSU3SectionFourIntrinsic.lean`)。
  ⚠ 罠: セット所属だけ見て「新規 linter の波は来ない」と判断すると外す。`defValue` を見ること。
- **`linter.ambiguousOpen`** — `namespace OddOrder.Isaacs.Ch03` の内側の `open Subgroup` が
  自前の `OddOrder.Isaacs.Ch03.Subgroup` と mathlib の `_root_.Subgroup` で曖昧、と警告。
  計 17 file を `open _root_.OddOrder.Isaacs.Ch03.Subgroup …` 等に明示化 (現行の解決先を保存)。
  `Representation` / `Matrix` でも同型の衝突が出た。
- `linter.style.show` は実装が info-tree 後処理から tactic elaborator へ変わったが、意味は同じ。

## simp / tactic の正規化が変わって「余分になった」ステップ

`rw` 連鎖や `simp` が以前より多く閉じるようになり、後続タクティクが `No goals to be solved` /
`` `group` made no progress `` になる箇所があった。いずれも**余分なステップの削除**で解決:

- `AugmentationIdeal`: `rw [...]` の後の `with_unfolding_all rfl` (2 箇所)
- `CyclicGenerated`: `rw [...]` の後の `rfl` (2 箇所)
- `AppC_LemmaC3_NormalForms`: `simp [map_inv]` の後の `group` (2 箇所)
- `StepFive`: `hcompl.card_mul_card` は `Nat.card ↥S` 形なので `simp only [SetLike.coe_sort_coe]`
  が不要に (3 箇所)

⚠ **落とし穴**: `linter.unusedSimpArgs` の指摘は、その宣言が**別の理由で失敗している間は
信用できない** (タクティクがその引数に到達していないだけ)。実際 2 度、指摘に従って
削除したら「その引数が無いと閉じない」ことが判明して差し戻した。エラーが消えてから対処すること。

## 同時に入れたリファクタ

1. **R1 — 自前命名の追随** (347 箇所): mathlib が `solvable_*` → `isSolvable_*` に寄せたのに合わせ、
   自前宣言 18 本を改名した。結論が `IsSolvable` のもの (`solvable_of_lt_top` →
   `isSolvable_of_lt_top` 等) と、仮説として使っているもの (`_of_solvable` → `_of_isSolvable`) を
   区別し、名前が「結論が IsSolvable」に読めてしまう 3 本
   (`solvable_minimal_normal_isAbelian` 等) は `_of_isSolvable` を後置する形に直した。
   prose として「solvable」を使っている名前 (`hall_higman_solvable_specialization`,
   `narrow_sylow_solvable_structure`, `solvable_structure_of_pRank_le_two`) は据え置き。
   ⚠ 機械リネームの正規表現で**直前のドットを許さない**と `Ch01.foo` / `hG.foo` のような
   修飾付き参照を取りこぼす (279 箇所を後から拾い直した)。
2. **R2 — `OddOrder/Mathlib/` shim の棚卸し** (93 宣言): v4.33 の全宣言と機械照合した結果、
   **upstream 化されたものは無かった** (同名ヒットは `Finsupp.mapDomain_surjective` /
   `Subalgebra.centralizer_sup` など別名前空間の別物)。削除候補ゼロ。
3. **R4 — stale docstring**: 削除された `Nat.succ_mul_choose_eq` への参照を
   `Nat.choose_succ_right_eq` に更新、`subgroup_solvable_of_solvable` (instance 化で消滅) への
   言及を書き換え。

R3 (3 つ目の類和 `OddOrder.GroupAlgebra.classSum` の統合) は設計判断を含むため別 issue に繰延。

## 手順 (再現用)

```bash
# 1. pin
printf 'leanprover/lean4:v4.33.0\n' > lean-toolchain
# lakefile.toml の mathlib rev を tag v4.33.0 の SHA に
lake update mathlib          # lake-manifest.json 更新 + cache get

# 2. 影響の事前見積り (両 tag を展開して名前を機械照合)
git -C .lake/packages/mathlib fetch origin refs/tags/v4.33.0:refs/tags/v4.33.0
git -C .lake/packages/mathlib archive v4.32.2 Mathlib | tar -x -C /tmp/ml432
git -C .lake/packages/mathlib archive v4.33.0 Mathlib | tar -x -C /tmp/ml433
#   → deprecated 属性付き宣言と削除宣言の FQN 差分を取り、repo の使用箇所と突き合わせる

# 3. 機械リネームを全部当ててから 1 回ビルド (エラー収集を 1 パスに集約)
# 4. エラーを分類 → defeq 系は互換フラグ、名前系は置換、余分ステップは削除
# 5. lake build OddOrder → bin/check-warnings --strict → AxiomsCheck → bin/count-sorry
```

⚠ **フルビルドは高価なので、機械的な修正はすべて当ててから 1 回だけ回す**。エラー箇所が
判明した後の反復は `lake build <Module>` (依存はビルド済みなので数秒) で行う。深い直列依存で
1 ラウンド 1 module しか進まなくなったら、上の「⚙ 必要箇所の特定手順」に切り替える。

## 最終状態

| gate | 結果 |
|---|---|
| `lake build OddOrder` | green (5,489 jobs) |
| `bin/check-warnings --strict` | 非 sorry 警告ゼロ |
| AxiomsCheck | OK (elaboration 時ガード) |
| `bin/count-sorry` | 0 (非退行) |
| 変更規模 | 1,293 file / +14,106 −13,817 |
