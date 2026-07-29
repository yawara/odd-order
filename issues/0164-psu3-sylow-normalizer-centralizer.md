---
id: 164
slug: psu3-sylow-normalizer-centralizer
title: "PSU(3,ℓ) の Sylow 2-正規化群: C_{D₀}(Ω₁(S₀)) ≠ 1 (書籍が \"as can be checked\" で省略)"
created: 2026-07-29
---

# PSU(3,ℓ) の Sylow 2-正規化群: `C_{D₀}(Ω₁(S₀)) ≠ 1`

## 書籍 (Peterfalvi Part II, Ch. III §1, Proposition, p. 117)

> But, if `G₀ = PSU(3, ℓ)`, `S₀` is a Sylow `2`-subgroup of `G₀` and
> `N_{G₀}(S₀) = S₀ ⋊ D₀`, then, **as can be checked**, `C_{D₀}(Ω₁(S₀)) ≠ 1`.

`Ch.III §1 Proposition` の case (2) と case (3) の両方で `PSU(3,ℓ)` 分岐を排除するために使う。
**書籍はこの計算を実行していない**。

## 現状 (2026-07-29)

* **case (2) では不要になった** — `natCard_inf_centralizer_le_sq`
  (`|C_Q(P)| ≤ |C_{Q₀}(P)|²`) が `CentralizerPSUData.natCard_cQ_eq_cQ0_cube`
  (`= |C_{Q₀}(P)|³`) と矛盾するので、位数の数え上げで代替した ([issue 0163](0163-pf-part2-ch3-s1-trichotomy.md))。
* **case (3) では代替不可** — case (3) の分岐は実際に PSU で、
  `|C_Q(P)| = |C_{Q₀}(P)|³` が成り立つ。`W = 1` の仮定が本質的に効く箇所。
  ⟹ **`W ≠ 1` (Prop の case (3) 後半) がこの計算に gate されている**。

## 必要なもの

1. **Ch.I §2 Prop 3 + Galois**: `W = 1` なら `V` は `Q₀ ≅ 𝔽_q` 上の体自己同型群として作用し、
   `C_V(C_{Q₀}(P)) = P` (`C_{Q₀}(P)` は `P` の固定体)。
   repo: `exists_semilinear_equiv` (`SemilinearRealization.lean:339`) が半線形実現を持つ。
   Galois 対応は mathlib の有限体 Galois 理論 (`GaloisField`, `Polynomial.Galois*`) を使う。
2. **`PSU(3,ℓ)` の構造計算**: `S₀ ∈ Syl₂(PSU(3,ℓ))`、`N(S₀) = S₀ ⋊ D₀` について
   `C_{D₀}(Ω₁(S₀)) ≠ 1`。
   repo の `GroupTheory/SpecificGroups/ProjectiveUnitary/**` は
   `RootGroup` / `Borel` / `Bruhat` / `StandardGenerators` / `Simplicity` を持つので、
   `S₀ = RootGroup n`、`D₀ = torus` の形で計算できるはず
   (Suzuki 側の `standardRootTorus_actsRegularlyOnInvolutions` が良い雛形)。
   ⚠ ただし Suzuki の torus は involutions 上**正則**に作用する (= 中心化群は自明) のに対し、
   PSU では `C_{D₀}(Ω₁(S₀)) ≠ 1` が主張なので、torus の作用の**核が非自明**であることを示す。
3. `F/Z(F) ≅ PSU(3,ℓ)` と `N_{G₀}(S₀)` の対応を repo の `CentralizerPSUData` に繋ぐ。

## 完了条件

`SecondCaseHypothesis` の下で「`W = 1` ⟹ PSU 分岐は起きない」が sorry-free で landing し、
[issue 0163](0163-pf-part2-ch3-s1-trichotomy.md) の `W ≠ 1` が閉じる。

## 参照

* 書籍 p. 117 = `references/peterfalvi/pages/peterfalvi-p117.png`
* 消費点 = [issue 0163](0163-pf-part2-ch3-s1-trichotomy.md) case (3) の `W ≠ 1`


## 数学的な中身を実測で確定 (2026-07-29)

repo の PSU モデル (`GroupTheory/SpecificGroups/ProjectiveUnitary/**`) を読んで、
`C_{D₀}(Ω₁(S₀)) ≠ 1` が**具体的な有限体の計算に落ちる**ことを確認した。

### モデル

* `S₀ = RootGroup n` = `{(a, b) ∈ 𝔽_{ℓ²}² | b + b* = a·a*}` (`RootGroup.lean:43`)、
  ここで `ℓ = 2^n`、`star = Frobenius` (`t* = t^ℓ`)。
* `Ω₁(S₀) = {u | u.fst = 0}` = `{(0, b) | b + b* = 0}` (トレース 0 の第 2 座標)。
* トーラスの作用 `scalePoint c u` は `fst ↦ c·(u.fst)`、`snd ↦ N(c)·(u.snd)`
  (`N(c) = c·c* = c^{1+ℓ}` = `torusWeight`)。
* `D₀ = PSUTorusParameter n = range (t ↦ t^{2ℓ−1})`
  (`StandardGenerators.lean:312`; 指数 `2·2^n − 1` は `t ↦ (t*)²/t`)。

### 計算

`c ∈ D₀` が `Ω₁(S₀)` を中心化する ⟺ `N(c) = 1` ⟺ `c^{ℓ+1} = 1`。

`c = t^{2ℓ−1}` と書くと、`𝔽_{ℓ²}^×` は位数 `ℓ²−1` の巡回群で
`(2ℓ−1)(ℓ+1) = 2ℓ² + ℓ − 1 ≡ ℓ + 1 (mod ℓ²−1)` ゆえ **`c^{ℓ+1} = t^{ℓ+1}`**。

⟹ **`t` を位数ちょうど `ℓ+1` に取れば `c = t^{2ℓ−1}` は `Ω₁(S₀)` を中心化する**。
`c ≠ 1` は `(ℓ+1) ∤ (2ℓ−1)` から: `2ℓ−1 = 2(ℓ+1) − 3` なので
`(ℓ+1) ∣ (2ℓ−1) ⟺ (ℓ+1) ∣ 3 ⟺ ℓ ≤ 2`。
**Peterfalvi の設定では `data.one_lt_n` (= `n > 1`、`CentralizerPSURoot.lean` で使用済) より
`ℓ = 2^n ≥ 4`** なので `c ≠ 1`。∎

⚠ 対比: Suzuki 側のトーラスは involutions 上**正則**に作用する
(`standardRootTorus_actsRegularlyOnInvolutions`) = 中心化群が自明。
PSU 側では norm の核 (位数 `ℓ+1`) が効いて非自明になる — これが分岐を分ける本質。

## 残る作業 = 橋渡し

上の計算 (ungated、~100 行) に加えて:

1. **Ch.I §2 Prop 3 + Galois**: `W = 1` ⟹ `V` は `Q₀ ≅ 𝔽_q` 上の体自己同型群として作用し、
   `C_V(C_{Q₀}(P)) = P` (`C_{Q₀}(P)` は `P` の固定体)。
   repo: `exists_semilinear_equiv` (`SemilinearRealization.lean:339`)。
2. **`CentralizerPSUData` との接続**: `F/Z(F) ≅ PSU(3,ℓ)` のとき、
   `C_S(P)` が `S₀` に、`V` の像が `D₀` に対応することを示し、
   上の非自明な `c` を `V ∖ P` の元に引き戻して (1) と矛盾させる。

⟹ **(2) が本 issue の主要な形式化コスト**。(1) と PSU の計算はいずれも見通しが立っている。
