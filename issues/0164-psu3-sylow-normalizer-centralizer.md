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

## ✅ 2026-07-29 セッション: 4 部品が landing + 閉じ方が確定

### landing した部品 (すべて sorry ゼロ・AxiomsCheck 登録済)

| 部品 | 場所 | 内容 |
|---|---|---|
| RingAut 版 Galois 対応 | `Algebra/FixedPointsGalois.lean` (新) | `fixer (F^B) = B` (Artin の数え上げ)、`mem_of_fixes_fixedPoints` |
| `C_V(C_{Q₀}(P)) = P ⊔ W` | `Peterfalvi/Appendices/Suzuki/GaloisCentralizer.lean` (新) | 書籍の `= P` は `W = ⊥` の系 |
| PSU の Sylow 一般版 | `.../ProjectiveUnitary/TorusCentralizer.lean` | `exists_ne_one_odd_centralizing_involutions_of_sylowTwo` |
| 中心的交換子の位数 | `GroupTheory/CentralCommutatorPower.lean` | `⁅x,y⁆ ∈ Z`, `gcd(|Z|, orderOf y) = 1` ⟹ `Commute x y` |

⚠ 併せて `FirstCaseHypothesis.W_mem_centralizes_Q0` を `Hypothesis.W_centralizes_Q0`
として `KCyclic.lean` に上げ、重複を解消した。

### 閉じ方が確定した (書籍の行間を全部埋めた)

`hWcube : |Q| = |Q₀|³ → W ≠ ⊥` を `W = ⊥` の背理法で示す。`P ≤ V` を素数位数に取り
Ch. I §3 Prop 1(c) の三分岐 (`centralizer_trichotomy_of_induction`) を回す:

* **Sz 分岐** — `distinguishedProduct_order = 5` だが case (3) は `st` 位数 3
  (`orderOf_st_eq_three_of_card_cube`) ⟹ 矛盾。**易**
* **PSL(2,ℓ) 分岐** — `natCard_cQ_eq_field = natCard_cQ0_eq_field` ⟹
  `C_Q(P) = C_{Q₀}(P) ≤ Q₀`。一方 Wielandt (9.1) の
  `wielandt_fixedPoint_trivial_U_fixed` (`GroupTheory/WielandtFixedPoint.lean`,
  **既に repo にある**) を Frobenius 群 `[K,P] ⋊ P` の `Q/Q₀` への作用に当てると
  `|Q/Q₀| = |C_{Q/Q₀}(P)|^{|P|}` で `Q/Q₀ ≠ 1` ゆえ `C_{Q/Q₀}(P) ≠ 1`。
  coprime 作用で `C_{Q/Q₀}(P) = C_Q(P)Q₀/Q₀ = 1` ⟹ 矛盾。
  **要るもの**: (i) `[K,P] ⋊ P` が Frobenius、(ii) `[K,P]` が `Q/Q₀` 上 fixed-point-free。
* **PSU(3,ℓ) 分岐** — 下記の連鎖。

### PSU 分岐の連鎖 (`cQEquivRoot` との整合性は**不要**だと判明)

当初は `cQEquivRoot` と `residualQuotientEquiv` の compatibility field が要ると考えたが、
**`RootGroup n` が `standardPermGroup n` の Sylow 2 (`standardRootSylow`, 既存)** なので
「任意の Sylow 2 版」(今回 landing) を使えば整合性を経由せずに済む:

1. `F := primeComplementResidual 2 (C_G(P))`、`G₀ := F/Z(F) ≅ standardPermGroup n`
   (`residualQuotientEquiv`)。
2. **`Z(F)` は奇位数** — `C_Q(P)` が `C_G(P)` の Sylow 2 で、その像が `G₀` の Sylow 2 と
   同位数だから。⟸ **未形式化、次の部品**
3. `C_Q(P)` の像 `S₀` は `G₀` の Sylow 2 ⟹
   `exists_ne_one_odd_centralizing_involutions_of_sylowTwo` が
   `d ≠ 1`, 奇位数, `Ω₁(S₀)` を中心化、を与える。
4. `d` を `F` の**奇位数**の元 `x` に持ち上げる (`Z(F)` 奇 + `d` 奇)。`x ∉ Z(F)`。
5. `y ∈ C_{Q₀}(P)` に対し `⁅x, y⁆ ∈ Z(F)` かつ `y` は 2-元 ⟹
   `commute_of_commutatorElement_mem_of_coprime_natCard` で **`x` は `C_{Q₀}(P)` を中心化**。
6. 特に `x ∈ C_G(s) ≤ H` (`centralizer_le_H_of_mem_Q`, Ch. I §3 Prop 1(b))。
   `Q₀ ≤ C_G(Q)` (`Q0_le_centralizer_Q`) より `C_H(s) = Q·V`、
   さらに coprime 作用で `C_{QV}(P) = C_Q(P)·V`。⟹ `x = y₀ v` (`y₀ ∈ C_Q(P)`, `v ∈ V`)。
7. `y₀ ∈ Q₀ ≤ C_G(Q)`… は `C_{Q₀}(P)` を中心化するので、`x` が中心化する ⟺ `v` が中心化する。
   ⟹ `v ∈ C_V(C_{Q₀}(P)) = P` (**今回 landing した Galois**、`W = ⊥`)。
8. すると `G₀` での `x` の像 = `y₀` の像 (∵ `v ∈ P ∩ F ≤ Z(F)`) で、これは `S₀` の元 = **2-元**。
   しかし `d = x` の像は**奇位数で ≠ 1**。⟹ 矛盾。∎

### 次の部品 (この順)

1. `Z(F)` が奇位数 (上記 2)
2. `C_H(s) = Q·V` と `C_{QV}(P) = C_Q(P)·V` (上記 6)
3. PSU 分岐の組み立て (上記 1–8)
4. PSL 分岐の Frobenius/Wielandt (上記)
5. `W_ne_bot_of_card_cube` を組んで `trichotomy` の `hWcube` 仮説を除去 → 0163 を閉じる
