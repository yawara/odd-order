---
id: 3027
slug: appe-e4-tier2-group-refutation
title: "BG E.4 Tier 2: Q₆ Lazard 群を Lean 構築し printed E.4 を群レベルで反証"
created: 2026-07-21
---

# BG E.4 Tier 2: 群レベル反証 (ユーザー指示 2026-07-21「Tier 2 も進めてください」)

Tier 1 (`AppE_FiliformCounterexample.lean`, Lie 環核心) の残ギャップ = Lazard 転送を消す:
Q₆ の Lazard 群 S を Lean の `Group` として実構築し、repo の `RegularOperatorSetup` を
instantiate して **printed E.4 の statement そのものの否定**を証明する。

## 設計 (確定)

- **直接多項式法則** (semidirect タワーでなく): `V = Fin 6 → ZMod 197` 上の truncated BCH。
- ⭐ **基底 rescale `diag(1,1,2,12,24,720)` で全係数が小整数化** (≤15)。これにより全恒等式
  (結合法則含む) が **ℤ 係数多項式恒等式**になり、素の `ring` で閉じる。
  `reduce_mod_char` (数値 literal 還元のみで ring 連動なし) も `field_simp` (入れ子除算を
  クリアしきれない) も**不要になった** — 両方実測で不採用。
- 導出 = truncated enveloping algebra U(L)/(weight>5) の PBW straightening で
  `log(exp x · exp y)` (scratchpad `derive_group_law.py` / `emit_scaled.py`)。
  Friedrichs 判定 (log が Lie 元) が内部整合性チェック。assoc/unit/inv/power/grading を
  ℚ 上で記号検証してから転記。Lean が全て再検証するので sympy は scaffolding。
- 群は `@[ext] structure Q6 where co : V` (Pi 型の commutator-bracket instance との衝突回避
  と同型の理由で Mul instance 衝突回避)。`Group.ofLeftAxioms`。
- `x^n = n•x` (`co_pow`) ⟹ exponent 197・orderOf・zpowers が自明化。
- B = `Multiplicative (ZMod 49)`、act = βAut^val (β は Tier 1 の対角写像を再利用、
  hom 性は grading ゆえ ℤ[ζ]-ring 恒等式 = 素の ring)。

## WP status

- ✅ **WP1 (sympy 導出+検証)**: scaled 整数法則・commutator・全構造の記号検証済。
  centralizer 三角構造は Lie 側と同型: `comm(x,e4) = (0,…,0,30x₀)` (T={x₀=0})、
  `comm(x,(0,0,0,0,s,t)) = (0,…,0,30sx₀)` (Z₂ 面)、`φ(x,v)−φ(v,x)` 三角、
  `comm(eB,e2) = (0,0,0,6,6,90) ≠ 0`。
- ✅ **WP2 (群構築)**: `AppE_FiliformGroup.lean` green + axiom-clean。gmul_assoc (ring)、
  Q6 Group instance、card 197⁶、co_pow、exponent 197、orderOf vg/e5g = 197、
  bg*e2g ≠ e2g*bg (decide)。
- ✅ **WP3 (部分群層)** (commit f672afae4): `co_zpow`、`mem_zpowers_vg_iff`/`_e5g_iff`、
  `mem_center_iff` (Z(S) = e₅-line)、`commute_vg_iff` → **`centralizer_zpowers_vg`**
  (C_S(R₀) = R₀ ⊔ R₁)、`disjoint_zpowers_vg_e5g`、**`plane_mul_comm`** (平面元は
  中心的 e₅ 補正を左に置いて可換 — 4 重 BCH 展開を single-depth で回避する要)、
  Z₂(S) = e₄–e₅ 平面 (両側)、T = C_S(Z₂) = {x₀=0}、
  `centralizer_upperCentralSeries_two_not_abelian` (Q6 レベル反証)。
- ✅ **WP4 (B 作用)** (commit bd564448f): `gmul_beta` (grading → ring 一発)、
  `βAut : MulAut Q6` (逆 = β⁴⁸)、`act : Mult (ZMod 49) →* MulAut Q6`
  (val + pow_eq_pow_mod)、`act_regular` (fpf)、`βAut_pow_seven_smul_zpowers_vg` +
  `act_A_fixes_zpowers_vg` (stabilizer + map_zpow)、`act_not_fixes_zpowers_vg`、
  card 3 種 (|R₀|=|R₁|=197, |A|=7)。
- ✅ **WP5 (組立)**: `AppE_FiliformRefutation.lean` (AppE_FurtherResults import を隔離):
  **`q6Setup : RegularOperatorSetup Q6 (Multiplicative (ZMod 49)) 197 7`** (全 field 実データ)、
  `omega_q6_eq_top`、`card_omega_ge` (197⁶ ≥ 197⁴)、`omegaEquiv` + comap 転送、
  `q6_centralizer_not_mulCommutative`、**headline `printed_propE4_false`**
  (sorried E.4 と同形の全称文の否定、universe 0)。OddOrder.lean 配線 +
  AxiomsCheck 8 件登録済。

## 参照
- 正本 note: `notes/bg/appE_e4_counterexample_2026_07_21.md`
- Tier 1: issue 3021 (55)。hdc 追加版 E.4 の証明 (別作業) = issue 9402。

## 2026-07-21 中断点 (ユーザー指示「きりのいいところで区切って」)

**WP1-2 完了・commit `ddab0d742` で区切り** (群構築の中核 = 最難関は突破済)。
次セッションの入口 = **WP3**: `co_zpow` → zpowers 特徴付け → `Commute x vg` の三角 solve
(centralizer_eq) → Disjoint → gcomm 座標公式 (Z₁/Z₂ 上界)。
**公式・導出スクリプトの永続正本 = `notes/bg/appE_e4_tier2_group_law.md`**
(scratchpad は揮発性のため移設済)。WP5 の headline は別 leaf
`AppE_FiliformRefutation.lean` に置く (AppE_FurtherResults の重 import を隔離)。
