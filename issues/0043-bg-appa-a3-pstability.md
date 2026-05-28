---
id: 43
slug: bg-appa-a3-pstability
title: "BG App.A Thm A.3 (non-p-stable + O_p(G)=1 ⇒ |G| even) + IsPStable 定義"
created: 2026-05-28
---

# BG App.A Thm A.3 (non-p-stable + O_p(G)=1 ⇒ |G| even) + IsPStable 定義

## 背景

issue [#0041](closed/0041-bg-appa-a2-dim-reduction.md) で A.1 / dim reduction / A.2
を sorry-free で実装完了 ([`OddOrder/BG/AppA_PStability.lean`](../OddOrder/BG/AppA_PStability.lean))。
次は **A.3**(BG mmd L4476, = Gorenstein 3.8.3 の弱化形)で App.A の連鎖を進める:

```
Thm 6.2 ⟸ App.B B.4 ⟸ A.5 ⟸ A.4(c) ⟸ A.3 [本 issue] ⟸ A.2 ✅ ⟸ A.1 ✅
```

依存閉包・ゲート構造は
[`notes/meta/bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md)
§0.2 参照. mini-roadmap は
[`notes/bg/appA_pstability.md`](../notes/bg/appA_pstability.md).

## 現状 (handoff 用、2026-05-29 更新)

[`OddOrder/BG/AppA_PStability.lean`](../OddOrder/BG/AppA_PStability.lean) ~L545-770
に以下を実装済:

- **`IsPStable p G`** def (`b8ab8a9`): alg-closed char-p faithful rep で p-element の
  quadratic min poly が無いという Gorenstein 1968 p.105 定義. `O_p(G) = 1` /
  `p odd` は使う側で hypothesis として渡す.
- **共役元 helpers** (`7b6158f`): `y := g x g⁻¹` (Baer-Suzuki が出す) と x の関係を 4 補題化:
  - `representation_conj_sub_one`: `ρ(gxg⁻¹) - 1 = ρg (ρx - 1) ρg⁻¹`
  - `representation_conj_quadratic`: `(ρx - 1)² = 0 ⇒ (ρ(gxg⁻¹) - 1)² = 0`
  - `representation_conj_ne_one`: `ρx ≠ 1 ⇒ ρ(gxg⁻¹) ≠ 1`
  - `isPGroup_zpowers_conj`: `IsPGroup p ⟨x⟩ ⇒ IsPGroup p ⟨gxg⁻¹⟩`
- **Step 5 用 single-step coprime action** (`96b447e`, 2026-05-29):
  新 module [`OddOrder/GroupTheory/RepresentationTheory/CoprimeActionTrivial.lean`](../OddOrder/GroupTheory/RepresentationTheory/CoprimeActionTrivial.lean) (147 行)
  に `coprime_action_trivial_step` sorry-free 実装。`G` 有限,
  `(|G| : F) ≠ 0`, `W ≤ V` 上 + `V/W` 上自明 ⇒ `V` 全体に自明。
  Maschke 不要の直接展開 (`T := ρ g - 1`, `(1+T)^(orderOf g) = 1 + (orderOf g) • T`,
  `(orderOf g : F) ≠ 0` から `T = 0`).
- **`thmA3` statement** + **Step 1-3** (`33bb1df`, `1921dec`):
  ```lean
  theorem thmA3 [Finite G] (_hp_odd : p ≠ 2)
      (h_Op_trivial : OddOrder.Isaacs.Ch01.opCore p G = ⊥)
      (h_not_pstable : ¬ IsPStable p G) :
      ¬ Odd (Nat.card G) := by
    intro hodd
    -- ✅ Step 1: ¬ IsPStable を unfold + push Not で証人 ⟨F, V, ρ, hfaithful,
    --    x, hxp, hxsq, hxne⟩ を取り出す
    -- ✅ Step 2: Baer-Suzuki で ∃ g, ⟨x, gxg⁻¹⟩ 非 p-群 (h_pair_not_pgroup)
    -- ✅ Step 3: y := gxg⁻¹ ∈ K (= conjugacy class of x) も同性質
    --    (hysq, hyne, hyp from helpers); H := closure {x,y}, hH_not_pgroup,
    --    hxH, hyH ∈ H 准備
    -- 🚧 Step 4-8: h_two_dvd : 2 ∣ |G| を sorry で残し、hodd と矛盾で閉じる
    have h_two_dvd : 2 ∣ Nat.card G := by sorry
    exact hodd.not_two_dvd_nat h_two_dvd
  ```

残 sorry の中身は下記「やること」 Step 4-8. import 済: `Mathlib.LinearAlgebra.*`,
`OddOrder.BG.Ch1_Preliminary.S02_Representations`, `OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector`,
`OddOrder.Isaacs.Ch02_Subnormality.Main`. `lake build OddOrder.BG.AppA_PStability` green
(thmA3 の `h_two_dvd` sub-sorry のみ警告).

## やること

### 0. ✅ 完了済 (`b8ab8a9` + `33bb1df` + `7b6158f` + `1921dec`)

下記 1, 2 (def + statement), Step 1-3 (witness + Baer-Suzuki + y ∈ K), および
共役元 4 助補題は実装済. 詳細は上記「現状」. 残 = Step 4-8 = `h_two_dvd : 2 ∣ |G|` 1 sorry.

### 1. `IsPStable` 定義 (新規)

Gorenstein の p-stability 定義 (G p.105) を `OddOrder.BG.AppA` に追加:

> Let `G` be a group with no nontrivial normal `p`-subgroups (= `O_p(G) = 1`), `p` odd.
> A faithful representation `φ` of `G` on a vector space `V` over `GF(p^n)` (≅ alg closure
> base change) is `p`-stable if no `p`-element of `(G)φ` has a quadratic minimal polynomial.
> `G` is `p`-stable if all such faithful representations are `p`-stable.

Lean signature (案):

```lean
def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    (ρ : Representation F G V), Function.Injective ρ →
    ∀ x : G, IsPGroup p (Subgroup.zpowers x) →
      ((ρ x : Module.End F V) - 1) ^ 2 = 0 → ρ x = 1
```

別解: 「`G has no nontrivial normal p-subgroups`」をどう扱うかは選択肢:
(a) `IsPStable` の前提に組み込む / (b) 別 hypothesis として A.3/A.4 で渡す.
**推奨 (b)** (def シンプル + Isaacs/BG ↔ mathlib 整合).

### 2. Thm A.3

```lean
theorem thmA3 {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    {G : Type*} [Group G] [Finite G]
    (h_Op : (opCore p G : Subgroup G) = ⊥)   -- "no nontrivial normal p-subgroups"
    (h_not_pstable : ¬ IsPStable p G) :
    ¬ Odd (Nat.card G)
```

### 3. 証明 = Gorenstein 8.3 翻訳 (using A.2 in place of 8.1)

Gorenstein 8.3 proof (mmd L2290–) 翻訳:

1. ✅ `¬ IsPStable p G` を unfold ⇒ ∃ ρ faithful + ∃ x p-element (≠ 1) with
   `(ρ x - 1)^2 = 0` (quadratic min poly).
2. ✅ `K := x` の conjugacy class. 全ての K の元は同じ性質 (= `representation_conj_*`,
   `isPGroup_zpowers_conj` 4 補題、`7b6158f`).
3. ✅ **Baer-Suzuki (Gorenstein 8.2)** で `O_p(G) = 1` + K で「全 pair が p-群を生成」が
   不可能 ⇒ ∃ y ∈ K, `⟨x, y⟩` は p-群でない. `y := g x g⁻¹` を set + 助補題で
   `hysq, hyne, hyp` 取得、`H := closure {x, y}` で `hH_not_pgroup`, `hxH`, `hyH`
   ∈ H 准備 (`1921dec`).
   - repo: `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` (= 単一元 form, `Main.lean:2134`)
4. 🚧 `H := ⟨x, y⟩` 非 p-群、`ρ_H : Representation F H V` (= ρ.comp H.subtype.toMonoidHom)
   は faithful (since ρ faithful + H ↪ G ↪ End V).
5. 🚧 **H-invariant chain** `V = V_1 ⊋ V_2 ⊋ ... ⊋ V_{m+1} = 0` with H 作用が
   各 `V_i / V_{i+1}` 上既約. 構成 = `V` finite-dim + 再帰的 maximal proper sub。
   mathlib `RingTheory.SimpleModule` / `Order.JordanHolder.CompositionSeries` を
   Submodule lattice 上で具体化。
6. 🚧 `N_i := ker(H → End(V_i/V_{i+1}))`. ∃ i, `N_i ⊊ H`.
   - 反例: 全 N_i = H ⇒ H 全要素が全 V_i/V_{i+1} 上自明作用. H の任意の `p'`-部分群
     も自明作用 → ρ faithful より p'-部分群 = 1 ⇒ H は p-群、矛盾 (= Gorenstein Thm 3.4
     翻訳: `coprime_action_trivial_of_trivial_on_quotients`, Maschke ベース)。
7. 🚧 `H/N_i` の faithful irreducible action on `V_i/V_{i+1}`. x, y のイメージ x̄, ȳ
   は quadratic minpoly (= `(ρ̄ x̄ - 1)^2 = 0`, ρ̄ x̄ ≠ 1).
   - x̄ = 1 仮定 ⇒ H̄ = ⟨ȳ⟩ p-group, alg-closed char p faithful irreducible 不可能
     (= Gorenstein Thm 1.2 = repo `PGroupFixedVector.invariants_ne_bot` 帰結:
     `IsPGroup.faithful_irreducible_in_charP_trivial`) ⇒ H̄ = 1, N_i = H と矛盾。
8. 🚧 **A.2 適用**: `H/N_i = ⟨x̄, ȳ⟩` 忠実既約二次 ⇒ `|H/N_i|` 偶 ⇒ 2 ∣ |H/N_i| ∣ |H| ∣ |G|
   ⇒ `hodd : Odd |G|` と矛盾 ∎

### 必要な mathlib / repo API

- ✅ `Subgroup.opCore` + `opCore.normal` (repo Ch01)
- ✅ `baerSuzuki_pCore` (repo Ch02 lean-eval, 単一元 form)
- ✅ A.2 = `quadratic_two_generated_irreducible_finrank_eq_two` (本 repo AppA)
- ✅ 共役元 4 助補題 (`representation_conj_*`, `isPGroup_zpowers_conj`, 本 repo AppA)
- ❌ H-invariant chain + quotient representation (新規構築 or mathlib)
  - mathlib: `RingTheory.SimpleModule` (`IsSimpleModule`) + `Order.JordanHolder.CompositionSeries`
- ❌ Quotient representation `H/N → End_F (V_i/V_{i+1})` (新規)
  - 既存 `Representation.quotientToInvariants` は invariants quotient で別物
- ❌ p'-subgroup acts trivially on filtration quotients ⇒ acts trivially on V
  (= Gorenstein Thm 3.4 翻訳、`Mathlib.RepresentationTheory.Maschke` ベース)
- ❌ p-group faithful irreducible in char p ⇒ trivial (= Gorenstein Thm 1.2,
  `PGroupFixedVector.invariants_ne_bot` + irreducible 仮定で短い帰結)

## 完了条件

- `IsPStable` 定義 + `thmA3` を `OddOrder/BG/AppA_PStability.lean` 末尾に追加
- sorry/axiom 無し
- `lake build` green
- docstring に `**BG Thm A.3** (= Gorenstein 3.8.3 weakening, mmd L4476)` トレーサビリティ
- notes/bg/appA_pstability.md の状態を更新

## 参照

- BG mmd L4476: A.3 statement
- Gorenstein mmd L2288 (Thm 8.3 statement), L2290+ (proof), L2204 (Thm 8.1 = repo A.2)
- repo: `OddOrder.BG.AppA.quadratic_two_generated_irreducible_finrank_eq_two`
  ([AppA_PStability.lean](../OddOrder/BG/AppA_PStability.lean))
- repo: `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` (Ch02 Main.lean L2134)
- closed issue [#0041](closed/0041-bg-appa-a2-dim-reduction.md)
- notes: [`appA_pstability.md`](../notes/bg/appA_pstability.md),
  [`bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md)
