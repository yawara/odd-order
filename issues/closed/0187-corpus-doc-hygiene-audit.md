---
id: 187
slug: corpus-doc-hygiene-audit
title: "現行コーパスの品質作業: 陳腐化 docstring / 実在しない宣言名 / import 衛生"
created: 2026-08-20
---

# 現行コーパスの品質作業: 陳腐化 docstring / 実在しない宣言名 / import 衛生

## 背景

FT 本体 + 3 冊 + Navarro Ch.1–7 (Z\*-定理, [0186](0186-glauberman-zstar-theorem.md)) が
揃い、コーパスは 1,709 leaf / 818k 行になった。この規模になると **docstring が実体から drift
する**のが実害になる:

- 存在しない宣言名を「Main results」に並べた module docstring を読んだ後続セッションが grep
  して見つからず、frontier を誤診する ([[verify-port-state-by-number-not-coq-name]] の逆方向)。
- 「まだ axiom で残っている」「gate が N 件残る」「X は sorried」といった **doneness の主張**が
  古いまま残ると、既に済んだ仕事を再着手させる。CLAUDE.md の「陳腐化 docstring は見つけたら直す」
  (2026-07-21 ユーザー方針) の一括適用。
- issue を `git mv` で `closed/` へ動かすと、その issue 内の相対リンクが全部死ぬ (`../OddOrder/…`
  が 1 階層足りなくなる)。closed issue は後続が読む記録なので、リンクが死んでいると追跡できない。

## やること

- [x] **import 衛生の全数チェック** — orphan leaf (root `OddOrder.lean` から到達不能な module)、
      重複 import 行、`import Mathlib.Tactic` 丸 import、root 自己 import
- [x] **実在しない宣言名 (Lean docstring)** — `lake env lean` で `OddOrder` の全定数名
      (352,597 件) をダンプし、doc comment 内のバッククォート識別子と照合。
      - 完全修飾 `OddOrder.…` 参照の全数照合
      - `## Main results` / `## Main definitions` 箇条書きの全数照合
      - 宣言型 snake_case 識別子 (`_` 2 個以上) の全数照合、Coq 名 (`coq/` に実在) を除外
- [x] **陳腐化した doneness 主張** — 「sorried」「axiom として残る」「gate が残る」と書かれた
      宣言を `#print axioms` とリポジトリ全体の実 sorry 数で実測し、事実と食い違うものを訂正
- [x] **backtick 内のファイルパス** — リンクでない `` `OddOrder/…/Foo.lean` `` 表記の実在確認
- [x] **markdown リンクの全数チェック** — 追跡下の全 `*.md` (802 件) の相対リンクを解決

## 完了条件

- 実在しない宣言名を指す Lean docstring 参照が 0 件
  (残るのは Coq 名 / 仮説 binder 名 / 明示的に「かつて存在した」と書かれた履歴参照のみ)
- 壊れた markdown リンクが 0 件 (`bin/check-links` が exit 0)
- `lake build OddOrder` green + 非 sorry 警告 0
- 両 checker が clean tree で green、故意に壊すと red になることを確認済

## 結果 (2026-08-21)

### import 衛生 — 問題なし

| チェック | 結果 |
|---|---|
| orphan leaf (`OddOrder.lean` から到達不能) | **0** / 1,717 module |
| 同一ファイル内の重複 import 行 | **0** |
| `import Mathlib.Tactic` (丸 import) | **0** ([0136](0136-lint-deferred-import-and-generalization.md) で完済済) |
| leaf からの `import OddOrder` (root 自己 import) | **0** |

### 実在しない宣言名 — 24 件を訂正

照合の正本は `lake env lean` で `OddOrder` 環境から書き出した全定数名。
名前空間の取り違えが最多 (ファイル名を名前空間の一部だと思い込む型)。

| ファイル | 誤 | 正 |
|---|---|---|
| `BG/AppC_LemmaC2.lean` | `OddOrder.BG.AppC.GlaubermanNorton` | `OddOrder.BG.AppC_GlaubermanNorton` |
| `BG/AppD_CNGroups/SylowTI.lean` (4 箇所) | `OddOrder.BG.AppD.{Basic,MaximalSylowIntersection}` | `OddOrder.BG.AppD_CNGroups.*` |
| `BG/Ch1_Preliminary/S04_SmallRankBasic.lean` | `OddOrder.BG.Ch1.{thompson_critical_omega,burnside_operator}` | `OddOrder.BG.Ch1.S01.*` |
| 同上 | `exists_normal_isElementaryAbelian_card_prime_sq_of_omega1_center_not_isCyclic` | `..._of_prime_sq_dvd_card_omega1Center` |
| `BG/Ch1_Preliminary/S03g_Thm310Module.lean` | `prime_card_and_finrank_of_elemAbelian_aux` | `prime_card_and_finrank_of_elemAbelian` |
| `GroupTheory/RepresentationTheory/InducedIrreducible.lean` | `OddOrder.RepresentationTheory.induce_apply_one` | `...ClassFunction.induce_apply_one` |
| `GroupTheory/RepresentationTheory/SylowTICongruence.lean` | `OddOrder.AlgInt.isIntegral_rat_imp_int` | `OddOrder.RepresentationTheory.*` |
| `GroupTheory/RepresentationTheory/WielandtElabBridge.lean` | `...CoprimeFrobeniusAction.wielandt_fixedPoint_frobenius` | `OddOrder.GroupTheory.*` |
| `Isaacs/Ch02_Subnormality/Main.lean` | `normal_sylow_image_under_surjective` | `normal_sylow_image_of_surjective` |
| `Isaacs/Ch03_SplitExtensions/ProblemsFaithfulOrbit.lean` | `opCore_eq_bot_of_injective` | `opCore_semidirectProduct_eq_bot` |
| `Isaacs/Ch04_Commutators/Mann.lean` (3 箇所) | `OddOrder.GroupTheory.CriticalSubgroup.*` | `OddOrder.GroupTheory.*` |
| `Isaacs/Ch04_Commutators/ProblemsMaximalClass.lean` | `nilpotencyClass_le_of_card_eq_pow` | `nilpotencyClass_le_of_card_eq_prime_pow` |
| `Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean` | `OddOrder.GroupTheory.Subgroup.thompsonJ_eq_of_le_of_le` | `Subgroup.thompsonJ_eq_of_le_of_le` |
| `Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean` (3 箇所) | `step4_5_LA_eq_top_and_Abar_card_eq_p` / `step8_normal_via_thm75` / `step8_pullback` | `step4_5_normal_J_hypotheses` / `step8a_PBar_normal_GBar` / `step8b_pullback_normal_P` |
| `Mathlib/QuotientGroup.lean` | `OddOrder.GroupTheory.FittingHeredity.isNilpotent_quotient_fitting_quotient_subgroupOf` | `OddOrder.GroupTheory.*` |
| `Mathlib/SchurZassenhausConj.lean` | `mk'_comp_conj` | `mk'_comp_conj_eq` |
| `AxiomsCheck.lean` | `orbit_eq_univ_of_odd_of_card_eq_three` | `orbit_eq_of_odd_of_subset_card_three` |
| `Peterfalvi/S08_CaseBSeedGlue.lean` | `caseBXimg_seam_all_Yset` | `caseB_member_seam_all_Yset` |
| `Peterfalvi/S08_Theorem62_63_Standalone.lean` | `OddOrder.Peterfalvi.S08.six_two` | `...S08.SibleyDadeHypothesis.six_two` |
| `Peterfalvi/S11_NineElevenPairAdjoin.lean` | `coherent_extension_cross_orthogonal` | `SOf_coherent_extension_cross_orthogonal` |
| `Peterfalvi/S16_PairingCoherence.lean` (2 箇所) | `zeta_ne_conj` / `hypothesis79_of_nonconjugate` | `h78_zeta_ne_conj` / `hypothesis79OfNonconjugate` |

残った未解決トークンは**すべて正当**: Coq 名 (`coq/` に実在, 19 件)、仮説 binder 名
(`hB_not_fixes` = `AppE_PropE4` の引数 等)、明示的に「削除済」と書かれた履歴参照
(`coherence_adjoin_or_equal_degree` / `witness_psi_degree` / `fitting_lt_derived` 等)、
`scoped[OddOrder.Conjugation]` の scope 名、`private` 宣言 (`OddOrder.BG.AppA.stabilityLiftAux`)。

### 陳腐化した doneness 主張 — `#print axioms` + sorry 実測で 30 箇所訂正

**決め手は「リポジトリ全体の実 sorry が 0」**。`bin/count-sorry` と独立の comment-strip 実測
(1,717 file) の両方が 0 を返し、フルビルドも `declaration uses 'sorry'` を 1 件も出さない。
⟹ **現在形で「X は sorried」と書いている docstring は、例外なく嘘になっている** —
cite できる sorried な対象がそもそも存在しない。個別 triage でなく一括で確定できた。

疑わしい宣言 27 本を 1 本の `#print axioms` バッチで検証 (全て `[propext, Classical.choice,
Quot.sound]`)。主なもの:

| 主張 | 実測 | 対応 |
|---|---|---|
| `S7B2_NormalJClose.lean`: 「残りを 3 つの focused **axiom** に分割、後続セッションが discharge」 | ファイル内 `axiom` **0 件**、`normal_J` は sorry-free + axiom-clean | 3 名の実名へ訂正 + 「axiom」表現を全廃 |
| `S15_Gate3.lean` (13.17.a/b): 「Skeleton status (Phase 2) … **4 つの gate が残る**」 | `exists_typeI_maximal_overNormalizer_U` は `[propext, Classical.choice, Quot.sound]` | 「全 gate 解消済」へ訂正、各 gate の解消元を明記 |
| `FongSwan.lean`: 「**⚠ Duplication flag** — private な BG 側と ~30 行の証明が重複」 | 定義は `GroupTheory/SolvablePrimeIndex.lean` の 1 本のみ ([9111](9111-dedup-prime-index-solvable.md) で統合済)、両者とも呼ぶだけ | 統合済の記述へ差し替え |
| `Theorem152Helpers.lean`: 「(sorried, general) `mf_hall_centralizer_control`」 | axiom-clean | 「then-sorried … since proved」 |
| `S10_StructureSetup.lean`: 「(sorried, lane-f W1) `proposition_type_classification`」 | axiom-clean | 同上 |
| `reconciled_typePData_T` を「sorried」と呼ぶ 6 箇所 (S15/S16) | axiom-clean | 「then-sorried」(経路の履歴としては正しいので保持) |
| `HypothesisBasics.lean`: 「generic sorried `chief_H0_eq_bot`」 | 実名は `chief_H0_eq_bot_of_noncoherent`、axiom-clean | 名前 + 状態の両方を訂正 |
| `S12_TypeIICrossIsometryPair.lean`: `typeII_HU_frobenius_of_coherent_aux` | 環境に不在 (retired) | 「retired」と明記 |
| `S06_Thm64.lean`: 「場合 2 は**未証明**」「現状 `step` は未証明」 | `thm64_case_fitting_primes_subset` / `thm64_step` とも実在・axiom-clean (`S06_Thm64Case2.lean` が `step` を供給) | 証明済へ訂正 |
| `S13_Orthogonality.lean`: 「The sole sorried-cite is the caseA refuter」 | 同ファイル L176 が既に「re-measured 2026-07-27、caseA は no longer gated」と自己訂正済 | 冒頭を実体に合わせた |
| `S12_Noncoherence.lean`: 「three gate lemmas **sorried pending issue 2022**」 | issue 2022 は closed、file は sorry-free | 「since proved」へ |
| `RankOneAffineModel.lean`: 「`Q₈` case sorried inside」 | Q₈ は Z\*-定理 ([0186](0186-glauberman-zstar-theorem.md)) で landing 済 | 過去形へ |
| `S14_MaximalI/*` (4 箇所): 「pinned **sorried** §8/§9 obligation」 | 上流は全て証明済。「pinned」= 仮説パラメータ化という設計自体は現存 | 「explicit hypothesis として pinned (上流は証明済)」へ。`WitnessSylowCyclic` には「リポジトリが sorry-free になったので pinning は discharge 可能かもしれない」と事実として付記 |
| `S15_Gate3.lean` L26 / `PairStructure.lean` / `KeyInequality.lean` / `SubgroupL.lean` / `S15_CaseACoherence.lean` / `S15_CharacterDegreeSupply.lean` / `S15_SAndTBasic.lean` (2) | いずれも axiom-clean | 「then-sorried」「since proved」へ |

**訂正しなかったもの (実測して正しいと確認)**: Isaacs Ch.5/Ch.10 の「`M(G)` の universal object
は未実装」「pretransfer の合成 (5A.3 c/d) は未実装」「Maschke の `ZMod p`-加群化は未実装」は
**現在も真** (環境ダンプに該当定数なし; [9206](9206-schur-multiplier-infrastructure.md) は
「universal object はどの演習にも不要だった」で close)。`S10_ForwardFromKeystone.lean` の
「de-axiomatized」、`S7B2` の「nothing is axiomatized」等は自己否定形なので正しい。
`S14_TypePCounting` の「mis-encoded sorried surface … was deleted」は履歴として正しい。

### markdown リンク — 230 → 0

- 217 件が `issues/closed/` — `git mv` で 1 階層下がったのに相対パスが据え置きだったもの
  (`../OddOrder/…` → `../../OddOrder/…`、`closed/NNNN-….md` → sibling 直参照)。
  `.lean:123` の行番号サフィックス付きも解決対象にした。
- notes 側は `notes/meta/log/` へ移動した監査ノートへの旧パス、`file:///Users/ywr/…` の
  別マシン絶対 URL、`0147-q8-brauer-suzuki-navarro.md` → `0147-q8-modular-char-theory-frozen.md`
  の改名など。
- 書き換えは **候補パスが実在するときだけ**適用し、fenced code block 内は触らない。
- 数式が markdown リンク構文に見えていただけの偽陽性 (`[Finite G](hp_odd)` 型) は、
  `bin/check-links` が inline code span と fenced block を無視するようにして除外。
  実体が壊れていた 3 件 (`closed/0126*.md` の glob 表記、`s08_6_8_assembly_plan.md` の
  `ℤ[R(x)](R(x)=…)` 等) は本文側を直してゼロにした。
- backtick 内のファイルパス (リンクでない `` `OddOrder/…/Foo.lean` `` 表記) も別途走査し、
  live doc の実体ずれ 20 件を修正 (`OddOrder/RepresentationTheory/…` → `GroupTheory/` 欠落、
  `notes/bg/s08_fitting.md` → `s08_fitting_max.md`、`issues/…` の closed/ 移動、
  `CLAUDE.md` の `bin/pdf-glyph-join.py` → `references/bin/…`)。残るのは
  「形式化先 (予定)」「配置案」等と明示された計画記述のみ。

## 参照

- CLAUDE.md「陳腐化 docstring は見つけたら直す」(2026-07-21) / [[feedback-fix-stale-docstrings-on-sight]]
- CLAUDE.md「新 leaf は同じ commit で `OddOrder.lean` に配線」(2026-07-20, [0135](0135-orphan-leaf-build-gate.md))
- 直前の tracker: [0186](0186-glauberman-zstar-theorem.md) (Glauberman Z\*-定理)
