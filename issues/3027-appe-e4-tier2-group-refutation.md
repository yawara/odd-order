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
- ⬜ **WP3 (部分群層)**: zpowers vg の元の特徴付け (`co_zpow`)、centralizer_eq
  (`C(vg) = zpowers vg ⊔ zpowers e5g`、三角 solve)、Disjoint、Z(S)/Z₂(S) 座標特定
  (`mem_upperCentralSeries_succ_iff` + comm 公式)、T = {x₀=0}。
- ⬜ **WP4 (B 作用)**: βAut : MulAut Q6 (逆 = ζ^{49−w} 対角)、act : Mult (ZMod 49) →* MulAut、
  A = zpowers (ofAdd 7)、A_card=7、fpf (Tier 1 の beta_iterate_fixed_eq_zero 再利用)、
  A_fixes_R₀ (β⁷ = ζ⁷ スカラー)、¬B_fixes (Tier 1 beta_not_fixes_v)。
- ⬜ **WP5 (組立)**: 別 leaf `AppE_FiliformRefutation.lean` (AppE_FurtherResults import は
  重いのでこの leaf に隔離): RegularOperatorSetup instance、Omega = ⊤、
  Nat.card ↥⊤ = 197⁶ ≥ 197⁴、upperCentralSeries ↥⊤ 2 の上界 (topEquiv comap +
  comm 公式)、**headline `printed_propE4_false : ¬ ∀ …`** (sorried E.4 と同形の全称文の否定)、
  AxiomsCheck 登録、note/survey 更新。

## 参照
- 正本 note: `notes/bg/appE_e4_counterexample_2026_07_21.md`
- Tier 1: issue 3021 (55)。hdc 追加版 E.4 の証明 (別作業) = issue 9402。
