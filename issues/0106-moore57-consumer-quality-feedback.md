---
id: 106
slug: moore57-consumer-quality-feedback
title: "moore57 (下流 consumer) からの品質 feedback — 汎用 infra の配置・API 形の改善カタログ"
created: 2026-07-10
---

# moore57 (下流 consumer) からの品質 feedback

**発信元**: moore57 (本 repo を Lake dep として消費する sibling project)。pin `a8b7a411` への
bump (moore57 issue 0052) 完了後、5224-commit delta の新 infra を「採用調査 + 品質評価」
した際の findings。**work order ではない** — 優先順位・実施判断は odd-order 側 (hub) に委ねる。
FT-path レーンの frontier を妨げない粒度 (ほぼ全て leaf/API 整理) を選んで記載。

**総括**: 検査した主要 10 定理は**全て transitive axiom-clean** (propext/Classical.choice/
Quot.sound のみ) で数学的品質は高い。改善余地は一貫して「**配置** (generic が重い特化
file に埋まる) と「**API の出し方** (private helper / 選言形 / 欠落 adapter)」。

## P1 — 実害の出た配置・API 問題

### 1. ClassSumCongruence.lean (1833 行) から generic 群論を抽出

`GroupTheory/RepresentationTheory/ClassSumCongruence.lean` は本体 (Peterfalvi 6.7 系
class-sum 合同) に加え、class sum と無関係な汎用補題を同居させている。**下流が
`card_dvd_of_stabilizer_eq_bot` (L406) を使おうとすると rep theory + 複素解析
(`Analysis.Complex.Polynomial`) + 整閉包/分数体の transitive closure を丸ごと引き込む**
ため、moore57 は import を断念し proof shape だけ複製した (moore57 commit `f52350a4`)。
2000 行天井にも近く、抽出は file-size 対策を兼ねる。抽出候補:

- `card_dvd_of_stabilizer_eq_bot` (406) / `card_dvd_of_no_nontrivial_fixed` (417)
  → 軽量 GroupAction module へ (必要 import は `GroupAction.Quotient` のみ)
- `mk_inv_eq_of_mk_eq` (314) → ConjClasses module (docstring 自認の import-cycle 回避局所コピー)
- `mem_sylow_of_mem_normalizer_of_isPGroup` (522) → Sylow/PGroup module
- `card_class_eq_index_centralizer` (664), `coprime_card_class_card_sylow` (712) → 共役類 module
- `isIntegral_of_pow_eq_one` (1173), `all_eq_one_of_norm_eq_one_of_sum_eq_card` (1255),
  `isIntegral_rat_imp_int` (1446) → `Algebra/AlgInt` 系

**mathlib upstream 候補** (odd-order は PR 凍結中なので将来メモ): mathlib は
`MulAction.selfEquivOrbitsQuotientProd` (同値) までで **card-dvd 系はない**。
`card_dvd_of_stabilizer_eq_bot` + `card_dvd_of_no_nontrivial_fixed` を
`Mathlib/GroupTheory/GroupAction/Quotient.lean` の直後に `@[to_additive]` つきで
置くのが自然な upstream 形。

### 2. Theorem131 (Isaacs 1.31): n_q 計数 helper が private で実 consumer が使えない

実例: moore57 の order-275 (=5²·11) 排除は「**Sylow-11 側**が正規」(n₁₁=1) を要するが、
公開 API は選言 `(∃ Sylow p 正規) ∨ (∃ Sylow q 正規)` のみで、Sylow-5 枝を取ったとき
先へ進めない (drop-in 失敗、手書き 30 行の n₁₁=1 導出が残存)。改善案 (いずれか):

- `card_sylow_{p,q}_of_card_eq_sq_mul_prime` (L39/53, 現 private) を公開する
- または sharpened 直接形を追加: `p < q` かつ `¬ q ∣ p^2 - 1` (⟺ q > p+1 相当) ⟹
  **Sylow q 正規** (選言なし)。`_gt` の証明の中にある内容そのもの。
- p³q 版は helper が公開 (`card_sylow_p_of_card_eq_cube_mul_prime` 等) で p²q 版だけ
  private という visibility 不統一もある。

## P2 — API 完備化 (下流が使う直前で止まる箇所)

### 3. CyclicPermEigenCount: 一般 count の公開 + partial-period orbit 補題

- 真に再利用可能な「dim E_{ζ^m} = #(寄与軌道)」の一般形が flagship
  `finrank_eigenspace_fixed_succ` (BG 2.11 特化: 固定点 1 + 残り全部自由軌道) の
  `count` block 内 (L295–345 相当) に**インライン埋没**。公開 lemma 化を提案。
- `repr_sum_fourier_self_free` は **full-period (size h) 軌道のみ**対応。size d ∣ h の
  partial-period 軌道の対角 Fourier 係数 (`ord(ζ^m) ∣ d` なら d、else 0) の補題が欠落 —
  混在軌道 (moore57 の order-35: sizes 5/7/35) への適用はここで止まる。
- 全て存在形 `hmon : ∃ a, (T^k)(b c) = a • b (σ^k c)` 経由なので、素の置換行列用の
  `a = 1` adapter (または cocycle 律つき weight 関数化) があると plug-and-play になる。
- 局所 helper の mathlib 重複疑い: `sum_pow_val_eq_zero` (非自明指標の和=0)、
  `orbitSetoid` (`MulAction.orbitRel` 相当)、`perm_pow_val_add` 等。

### 4. CyclotomicCharacterCongruence: (1.10) の 2 綴りと合成 corollary

- (1.10.b) が **NumberField 版** `int_dvd_of_zeta_sub_one_dvd` (header で宣伝) と
  **ℂ 版** `int_dvd_of_one_sub_primRoot_dvd` (docstring 自認「実際に使う形」) の 2 綴りで、
  import 重量が大きく違うのに相互参照がない。両 docstring に「NumberField が既に
  あるのでなければ ℂ 版を使え」の注記を。
- (1.10.a) `exists_integral_apply_sub_of_commute` は `(1−ε)·z` 分解で止まり、
  `n : ℤ` への `p ∣ n` 着地 corollary (a+b の合成) が未輸出 — 全 consumer が再接着する。
- `IsCharacter` 版と `ZIrr` 版の厳密特化ペアが 2 組 (`exists_int_prod_*` /
  `one_le_prod_normSq_*`) — 片方から導出して半減可。
- Galois-fixedness block (`hpowN`/`hσval`/`hstep`, ~40 行) が 3 定理にコピペ — 抽出可。
- `exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed` の docstring が動機に挙げる
  (13.10) の平均化形 (`(1/|G|)·Σ‖λ‖²` の有理性/整数性) が未提供。

## P3 — 小物

5. **二重 qualified namespace wart**: `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom`
   (Ch04 namespace 内で Ch03 qualified head 宣言)。`CoprimeFixedPoints.lean:158` の
   `local notation3` 回避や下流 (moore57 ThreeGroupOnFiveGroup) の full-qualified 呼びを
   強いている。定義サイトで単一 namespace に。
6. `fixedSubgroup` (CoprimeAction) は mathlib 級の一般性なのに API が 2 本
   (`mem_`/`antitone`) のみ。`fixedSubgroup_bot = ⊤` / `MulAction.fixedPoints` との関係等。
7. `wielandt_card_combine` は純 ℕ 算術で群論 file に同居 — 下層へ沈める余地。
8. 文書の所在ずれ: `elabSubmoduleSubgroupEquiv` は棚卸し類で S02_FixedSubmodules と
   記載されがちだが実体は `GroupTheory/RepresentationTheory/AInvariantSubrep.lean:37`。
   なお実体は mathlib 3 行合成なので、これだけ欲しい下流は局所再導出が軽い
   (AInvariantSubrep 経由は Wielandt closure を引き込む)。
9. docstring 言語の不統一 (CoprimeAction/Theorem131 = 日本語, CoprimeFixedPoints = 英語)。
   mathlib-compat 志向なら proof-facing docstring は英語収束が望ましい。

## 参考: moore57 側の採用実績 (consumer reality)

- 採用済: `card_dvd_of_stabilizer_eq_bot` の proof shape (統合 refactor、上記 §1)。
- HOLD (トリガー付き): Isaacs 3.14 norm 族 (要 ℚ-character→`ClassFunction G ℂ` bridge)、
  CyclicPermEigen 中間層 (要 §3 の partial-period 補題)、(1.10) 系 (自前 Frobenius 合同で
  現需要は充足)、Theorem131 (§2 解消後)。
- 評価詳細: moore57 `plans/reference/research_oddorder_main_usable_theorems.md`
  「2026-07-10 続: 採用判定」節。
