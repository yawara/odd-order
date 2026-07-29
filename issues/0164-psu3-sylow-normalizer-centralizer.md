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

## ✅ PSU の計算は完了 (2026-07-29)

新 leaf `GroupTheory/SpecificGroups/ProjectiveUnitary/TorusCentralizer.lean`:

| 定理 | 内容 |
|---|---|
| `natCard_units_field` | `\|𝔽_{ℓ²}^×\| = 2^{2n} − 1` |
| `exists_ne_one_mem_psuTorus_torusWeight_eq_one` | 行列式 1 のトーラスに norm 1 の非自明な元 |
| `exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one` | **その元は `Ω₁(S₀)` を各点固定 = `C_{D₀}(Ω₁(S₀)) ≠ 1`** |

AxiomsCheck 登録済、sorry ゼロ。

## 残る作業 = 橋渡し

上の計算に加えて:

1. **Ch.I §2 Prop 3 + Galois**: `W = 1` ⟹ `V` は `Q₀ ≅ 𝔽_q` 上の体自己同型群として作用し、
   `C_V(C_{Q₀}(P)) = P` (`C_{Q₀}(P)` は `P` の固定体)。
   repo: `exists_semilinear_equiv` (`SemilinearRealization.lean:339`)。
2. **`CentralizerPSUData` との接続**: `F/Z(F) ≅ PSU(3,ℓ)` のとき、
   `C_S(P)` が `S₀` に、`V` の像が `D₀` に対応することを示し、
   上の非自明な `c` を `V ∖ P` の元に引き戻して (1) と矛盾させる。

⟹ **(2) が本 issue の主要な形式化コスト**。(1) と PSU の計算はいずれも見通しが立っている。


## 橋渡しの入口を特定 (2026-07-29)

`C_{D₀}(Ω₁(S₀))` の非自明元 `d` を repo の言葉に引き戻す道筋:

1. `d` は `G₀ = F/Z(F)` の元で `Ω₁(S₀)` を中心化する。
   `CentralizerPSUData.cQEquivRoot : ↥(Q.subgroupOf C_G(P)) ≃* RootGroup data.n`
   が **`C_Q(P) ↔ S₀`** を与えるので、`Ω₁(S₀) ↔ C_{Q₀}(P)`。
2. `d` を `F ≤ C_G(P)` の元 `x` に持ち上げると `x` は `C_{Q₀}(P) ∋ s` を中心化する。
3. ⟹ **`x ∈ C_G(s) ≤ H`** — repo に `centralizer_le_H_of_mem_Q`
   (`Basic.lean:557`, Ch.I §3 Prop 1(b)) が在る。**これが入口**。
4. `d ∈ D₀` は奇位数 (Sylow 2 の補群)、`Theorem C` より `Q` は 2-群なので
   `H = Q ⋊ D` で `D` は Hall 2'-部分群 ⟹ `x` は `D` の共役に入る。
   `x` は `s` を中心化するので `V = C_D(s)` 側に落とす議論が要る。
5. すると `x ∈ V ∖ P` が `C_{Q₀}(P)` を中心化し、Galois の
   `C_V(C_{Q₀}(P)) = P` に矛盾 ⟹ PSU 分岐は起きない。

⟹ 残るのは **(a) Galois の `C_V(C_{Q₀}(P)) = P`** (`W = 1` + Ch.I §2 Prop 3
`exists_semilinear_equiv`) と **(b) 上の 4 = `C_H(s)` の Hall 分解**。


## Galois パートの mathlib API (2026-07-29 実測)

`C_V(C_{Q₀}(P)) = P` の中身は**有限体の Galois 基本定理**:
`Q₀ ≅ F` (位数 `q = 2^m`) 上で `V` は `RingAut F` の部分群として作用し
(Ch.I §2 Prop 3 = `exists_semilinear_equiv`)、`C_{Q₀}(P)` は `P` の固定体。

* **mathlib の本体**: `IntermediateField.fixingSubgroup_fixedField`
  (`FieldTheory/Galois/Basic.lean:274`)
  — `[FiniteDimensional F E]` の下で `fixingSubgroup (fixedField H) = H`。
  `H : Subgroup (E ≃ₐ[F] E)` なので `F := ZMod 2`、`E := F` (有限体)。
* **`RingAut F` → `F ≃ₐ[ZMod 2] F` の変換**: `AlgEquiv.ofRingEquiv`
  (`Algebra/Algebra/Equiv.lean:625`)。`commutes'` は素体上自動
  (`ZMod 2` からの環準同型は一意)。
* 有限体は `ZMod 2` 上有限次元なので `FiniteDimensional` は自動。

⟹ Galois パートは **API が揃っている**。残る実装コストは
`exists_semilinear_equiv` の出力 (`νe : Vbar ≃* A`) を上の形に繋ぐ配線と、
`W = 1 ⟹ V ≃ Vbar` (忠実性)。
