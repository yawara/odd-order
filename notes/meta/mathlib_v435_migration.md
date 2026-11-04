# mathlib v4.34.1 → v4.35.0 移行記録 + Lean module system への移行

2026-11-04〜05 実施 (branch `mathlib-v435`、issue [0190](../../issues/closed/0190-mathlib-v435-module-system.md))。

## pin

| | 旧 | 新 |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.34.1` | `leanprover/lean4:v4.35.0` |
| mathlib `rev` | `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`) | `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0` = `stable`) |

drift = **651 commits** (v4.34 の 0.6 倍)。v4.35.0 は 2026-10-13 リリース。v4.36.0 は rc2 止まりなので
CLAUDE.md の「rc には当てない」に従い対象外。

## 版上げと module 化は切り離せない

mathlib v4.35.0 は lakefile に **`requiresModuleSystem := true`** を新設した。Lake はこれを見て、
`module` ヘッダの無い file が mathlib を import するたびに (import 1 行ごとに) warning を出す
(`fetchImportInfo`、`Lake/Build/Module.lean`)。本リポは lint 純ゼロ gate (`bin/check-warnings
--strict`) なので、**版上げだけでは CI が赤になる**。

そこで版上げの commit では lakefile に一時的に **`allowNonModules = true`** (Lake の正式な opt-out、
`LeanConfig.allowNonModules`) を置き、次の module 化の commit でそれを外して逆に
**`requiresModuleSystem = true`** を立てた。以後は非 module の file が混入すると (自パッケージ内でも)
Lake が warning を出し、gate が赤になる。

## commit 構成

| commit | 内容 | 検証 |
|---|---|---|
| 版上げ (非 module のまま) | pin、API 変更・deprecated・lint の追従 | フルビルド + `--strict` + AxiomsCheck 6,030 |
| module 化 | 全 1,721 file のヘッダ変換、不足 import 24 行、`private` 解除 94 宣言 | 同上 |
| import 整理 | `lake shake` 2 回で不動点、`-- shake: keep` 規約、AxiomsCheck の直接 import | 同上 + shake 提案ゼロ |
| 互換フラグの棚卸し | `respectTransparency` 231 → 227 | 同上 |
| 重複解消 | v4.35 で入った補題との重複 4 件、陳腐化 docstring 1 件 | 同上 |
| 重複解消 (既存) | mathlib と文・引数とも同一の自前定理 17 件 | 同上 |

## 1. 版上げで壊れた箇所

### 事前の機械照合 (両 tag を展開)

| 項目 | 値 |
|---|---|
| mathlib の新規 deprecated で repo が踏むもの | 11 名 (約 340 箇所) |
| 同名のまま文が変わった宣言で repo が踏むもの | 18 候補 → 実害 5 (下表) |
| deprecated module | 1 (`Mathlib.Data.Setoid.Basic` → `Mathlib.Order.Setoid.Basic`) |
| Lean core の変更 | repo への影響なし |

### API 変更 (ビルドで確認、5 ラウンド)

| 変更 | 対応 |
|---|---|
| **`IsSimpleGroup.eq_bot_or_eq_top_of_normal` の正規性が instance 引数に** (`∀ H, H.Normal → …` → `∀ (H) [H.Normal], …`) | 約 70 箇所。明示の正規性証明が識別子/`inferInstance`/`‹›` なら外す (局所仮定は既に local instance)。部分群を `_` にしていた 18 箇所は名指しに、`normalizer_eq_top_iff.mp …` を直接渡していた箇所は `have :=` で文脈に入れる |
| `Subgroup.Normal.eq_bot_or_eq_top`: `{H} (Hn : H.Normal)` → `(H) [H.Normal]` | 4 箇所 |
| `Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top` の `IsMulCommutative` が instance に | 2 箇所 |
| `Subgroup.card_dvd_of_surjective` の準同型が暗黙引数に | 7 箇所 (`(f := …)` で渡す) |
| **`Subgroup.FG` / `AddSubgroup.FG` が `IsMulFG` / `IsAddFG` (部分群上の class) の abbrev に** | 分解・構成は `AddSubgroup.isAddFG_iff` (Finset 形) 経由 (`FiniteIndexAnnihilator`) |
| `Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic` が軽量化され、`Subgroup.isCyclic` / `isCyclic_of_injective` 等は `…Cyclic.Subgroup` へ | import を差し替え (2 file) |
| `ULift.ext` の `x y` が暗黙に | 3 箇所 |
| elaboration の変化: `hc.dvd_of_dvd_mul_left (by rwa [mul_comm] at h)` が通らなくなった (文は不変) / `congr 1` が `Finset.filter` のゴールまで閉じるように | 引数を直接渡す / 後続の `exact` を削除 |

⚠ 自前の `IsChiefFactor` にも同名のフィールド `eq_bot_or_eq_top_of_normal` (明示の正規性引数を取る) が
あり、機械置換が 2 箇所誤爆した (受け手の型を見ずに置換したため)。受け手で絞り込んで戻した。

### deprecated の置換 (11 名、約 340 箇所)

`SetLike.{exists_of_lt, not_le_iff_exists, lt_iff_le_and_exists, le_def}` → `IsConcreteLE.*`
(`le_def` は `le_iff`)、`MonoidHom.coe_coe` → `coe_ofClass`、`HasEnoughRootsOfUnity.exists_primitiveRoot`
→ `exists_isPrimitiveRoot`、`MulEquiv.coe_monoidHom_{trans,refl}` → `toMonoidHom_*`、
`AlgEquiv.coe_ringEquiv` → `coe_toRingEquiv`、`AlternatingMap.smul_apply` → `smul_apply`、
`Group.nilpotencyClass_eq_quotient_center_plus_one` → `…_add_one`。
ビルドログの位置情報 (file:line:col) から置換し、ビルド未到達の file は完全名の置換で補った。

### linter の変化

- **`unusedFintypeInType` / `unusedDecidableInType` が 1 本の linter に統合された** (mathlib #44436)。
  その結果 `set_option linter.unused…InType false in` は**コマンドの最外側にあるときだけ**効く。
  `omit … in` の内側に置いていた抑制 18 件 (8 file) が効かなくなり、警告になった。抑制を `omit` の
  外側へ移して解消 (抑制理由のコメントは一緒に移動)。
- unused tactic linter が新たに no-op 14 件 (`rfl` / `exact` / `ring` / `<;>` / `first` の常に失敗する
  選択肢) と未使用 simp 引数 1 件を検出。

## 2. module 化

### 形

mathlib の多数派 (4,936 file) と同じ形にした: copyright → `module` → `public import …` → module doc →
`@[expose] public section` (直後の `noncomputable section` は `@[expose] public noncomputable section` に
統合)。import 行だけの再エクスポート hub (29 file) には section を置かない。`@[expose]` で def の中身を
下流に見せるので、下流から見た挙動は非 module 時代と変わらない。

### ビルド前に olean から算出したもの

module は import 先の **public import の閉包**しか見えない (非 module の file は推移閉包を全部読む)。
そこで非 module ビルドの olean から、変換後に壊れる箇所を先に計算した (道具は末尾)。

- **不足 import**: 各 file が実際に使う module (定数参照 + 記法・タクティクの使用記録 `extraModUses`、
  `lake shake` の `calcNeeds` と同じ計算) から、変換後に見えなくなるものだけを足した。**23 file / 24 行**
  だけで済んだ (`Mathlib.GroupTheory.Commutator.Finite` ×7 など)。Lean core の組込み
  (`push_cast` の meta 使用記録 `Lean.Meta.Tactic.NormCast` など) は import 不要なので除外した。
- **`private` の解除**: 公開される文・expose される def 本体・その中のタクティク証明から参照される
  `private` 宣言を、解除の連鎖 (解除した def の本体がまた別の private を参照する) を不動点まで追って
  列挙した。**94 宣言 / 38 file** (theorem 42、def・abbrev・instance 53)。

### ビルドで判明したもの (4 ラウンド)

| 症状 | 原因 | 対応 |
|---|---|---|
| `Unknown identifier` + 「private declaration … would need to be public」 | 予測 v1 が解除の連鎖を 1 段しか追っていなかった | 予測を不動点版に直して再適用 |
| 同名 `localH78` / `localBD` が「already declared」 | S09 の 3 file に同一内容の private abbrev が重複しており、公開すると衝突 | 型・値の一致を確認し、上流の 1 本に寄せて下流の写しを削除 |
| `rfl` が `(0 : GaloisField 2 n) + 0 = 0` を閉じない | mathlib の非公開 def の中身は開けない | `exact add_zero 0` |
| 暗黙引数が決まらず「tactic execution is stuck」 | (elaboration 順の変化) | `(Y := …)` を明示 |
| dsimp 系 simp 補題の private 参照 | 項に残らないので予測できない | 公開 |
| AxiomsCheck の補助 def | `elab` は meta コードなので、呼ぶ def も meta が要る | `meta def` に |

懸念していた mathlib の非公開 def (`Commute` / `SemiconjBy` など 2,983 個) は、`rfl` で中身を開く 1 箇所
以外は問題にならなかった (`rw [Commute, SemiconjBy]` も通る)。

AxiomsCheck は module 境界越しでも `sorryAx` を検出できる (axiom は olean 書き出し時に宣言ごとに
事前計算される、`exportedAxiomsExt`)。事前試行で確認済み。

## 3. `lake shake` による import 整理

v4.35 同梱の `lake shake` (module 専用) で全 file の import を整理した。2 回当てて不動点
(`lake shake OddOrder` の提案ゼロ) まで回した。

| | import 行 | public | private | 中央値/file |
|---|---|---|---|---|
| module 化直後 | 6,303 | 6,296 | 7 | 2 |
| shake 後 | 14,099 | 4,728 | 9,371 | 7 |

行数が増えるのは、これまで public import の連鎖で暗黙に届いていたものを各 file が直接 import する
ようになるため (mathlib と同じ書き方)。private import は下流の公開スコープに伝播しない。

### shake の盲点 (`-- shake: keep` で保護)

shake は olean の定数参照と使用記録から判定するので、次を見落として import を消す。適用後の
ビルドで 1 層ずつ露見した (6 ラウンド)。

| 盲点 | 件数 | 対応 |
|---|---|---|
| **expose される def 本体の中の証明が使う import** — shake は証明の依存を private と判定するが、expose 本体は公開スコープで elaborate される | 150 箇所 / 107 file (olean から一括算出) | `public import … -- shake: keep (…)` に昇格 |
| 再エクスポート専用 hub (自分では何も使わない) | 29 + AxiomsCheck | `module -- shake: keep-all` |
| `example` でしか使わない | 3 file | `-- shake: keep` |
| `export` の対象 | 1 | 同上 |
| `letI` で束ねた `abbrev` が文から展開されて項に残らない | 2 file | 同上 (public) |
| `simp` の congr 集合に入る `@[congr]` 補題 (`Path.exists_congr` / `types_congr_hom`) が、expose 本体の中では「Unknown constant」になる | 2 file | 定義 module を public import |
| 名前空間ごと import が外れ、使っていない `open X` が `unknown namespace` で落ちる (`open A B` だと後続の `B` も開かれず連鎖的に落ちる) | 25 箇所 | 死んだ名前空間を `open` から削除 |
| AxiomsCheck の検査対象が中間 hub の private import の先に入り見えなくなる | 384 module | AxiomsCheck が定義 module を直接 import |
| import 集合が変わって instance 探索が時間切れ | 1 | 型を明示 |

その他: import 行が増えて 1,500 行を超えた 2 file を分割 (`S13_FittingHallInvariance` /
`S12_MaximalIII_IV_V_Core.ConjugationOrbits`)、`DadeContradiction` 末尾の `#print axioms` 5 本を
AxiomsCheck の検査に移した (shake が対象の import を消したため。検査として効くようにもなった)。

## 4. 互換フラグと重複

- `set_option backward.isDefEq.respectTransparency false in` を 1 本ずつ要否判定: 231 → 227
  (Higman 3 / Suzuki 1 が不要に)。144 file の個別 elaborate が並列 8 本で 2 分。
- v4.35 で入った定理名 2,123 件と自前の宣言を、文の完全一致 (宇宙変数・束縛変数名を正規化) と名前の
  一致で突き合わせた。v4.35 由来の重複は 4 件 (`Subgroup.isCoatom_iff_index_prime` = Isaacs
  Problem 1D.6、`Subgroup.isCoatom_of_index_prime` ×2、`MulAction.stabilizer_subgroupOf`)。
- 同じ照合で、v4.34 以前から mathlib と文が完全一致する自前定理が 32 件見つかった。うち引数の明示/
  暗黙まで同一の 17 件 (純粋な名前違いのラッパー) を削除して mathlib を使うようにした。残り 15 件は
  引数を instance 化・暗黙化した「規約の適応」(CLAUDE.md「ラッパー方針」の許容例外) と、意図的な
  実演定理 `theoremC_sl2` なので残した。
- 「mathlib に無い」と書いた docstring 19 件を v4.35.0 のソースで再検証。陳腐化は 1 件
  (`MulAut.congr` は既にあった) で修正した。

## `lake check` (CI には入れない判断)

v4.35 の Lake には `lake check` がある: bwrap の sandbox 内で既定 target をビルドし、export を kernel で
再検査して標準外の axiom を検出する (`--paranoid` で lean4lean / nanoda なども併用)。検査の強さは
AxiomsCheck (flagship 6,034 定理の axiom 集合) より上だが、sandbox 内でプロジェクトを丸ごとビルド・
export・再検査するので重く、push ごとの CI には向かない。CI は従来どおり build + AxiomsCheck + lint
gate とし、`lake check` はリリースや外部提出 (Palomar の提出リポが odd-order を依存に取る場合など) の
前に手動で回す選択肢として残す (bwrap はこのマシンに入っている)。

## 実測した効果

- **証明の中身だけを直すと、下流は再ビルドされない**。重複解消 (証明内の補題差し替え 7 file) の再ビルドは
  19 秒、`module -- shake: keep-all` の注釈付け (30 file) は 19 秒。非 module 時代は上流 file の編集で
  下流が全部ビルドし直しだった。
- 個別 elaborate が速い (import 先の公開部分しか読まない)。互換フラグの棚卸し 144 file が 2 分。
- フルビルド (fresh, `.lake/build` を消してから): **17 分 48 秒 / 5,593 jobs** (別プロジェクトのビルドと
  マシンを共有した状態での実測。CPU 時間 143 分)。全 1,723 file が module。

## 手順 (再現用)

```
# 1. pin を上げ、lakefile に一時的に allowNonModules = true。lake update mathlib
# 2. 影響の事前見積り (v434 note と同じ: deprecated / 同名宣言の文の比較 / deprecated module)
# 3. 予測できる API 変更を当ててからフルビルド。失敗 module を直して再ビルド (5 ラウンド)
# 4. 非 module ビルドの olean から:
#    - 不足 import: Needs.lean (定数参照 + extraModUses) → missing.py (変換後の public 閉包と比較)
#    - private の解除: Privs.lean (公開文・expose 本体・その中の証明からの private 参照を不動点まで)
# 5. ヘッダ変換 (modulize.py: module / public import / @[expose] public section)、
#    AxiomsCheck の meta def、lakefile を requiresModuleSystem = true に → ビルドで残りを直す
# 6. hub に module -- shake: keep-all → lake shake --fix OddOrder → ビルドで盲点を潰す
#    (expose 本体の証明が使う import は Exposed.lean で一括算出して public 昇格) → shake を不動点まで
# 7. lake build OddOrder → bin/check-warnings --strict → AxiomsCheck → bin/count-sorry →
#    lake shake OddOrder (提案ゼロ) → bin/check-links / bin/check-doc-names
```

道具 (`Needs.lean` / `Privs.lean` / `Exposed.lean` / `missing.py` / `modulize.py` / `deadopen.py`) は
使い捨てとして repo には入れていない。考え方は上記のとおりで、次に同種の移行をするときは
`lake shake` の `calcNeeds` (`Lake/CLI/Shake.lean`) を出発点にすればよい。
