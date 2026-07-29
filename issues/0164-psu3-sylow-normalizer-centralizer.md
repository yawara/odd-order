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

1. ~~`Z(F)` が奇位数~~ ✅ `CentralizerPSUData.odd_natCard_center_residual`
   (`StructureOfH/PSUCentre.lean`) + 一般補題 `Sylow.not_dvd_natCard_of_natCard_eq`
2. ~~`C_H(s) = Q·V`~~ ✅ `inf_centralizer_distinguishedInvolution_eq_sup` /
   `exists_mem_Q_mem_V_of_mem_H_of_commute_distinguishedInvolution` (`QStructure.lean`)、
   および `W = 1 ⟹ V 可換` = `isMulCommutative_V_of_W_eq_bot` /
   `V_le_centralizer_of_le_V_of_W_eq_bot` (`GaloisCentralizer.lean`)。
   ⚠ 当初想定した coprime 分解 `C_{QV}(P) = C_Q(P)·V` は**不要だった** —
   `V ≤ C_G(P)` から `q = x v⁻¹ ∈ C_G(P)` が直ちに出る。
3. ~~**PSU 分岐の組み立て**~~ ✅ `CentralizerPSUData.false_of_W_eq_bot`
   (`StructureOfH/PSUCentre.lean`) — **書籍の "as can be checked" が閉じた**
4. **PSL 分岐** ← 現在地 (下記の通り Wielandt 2 回で済むと判明)
5. `W_ne_bot_of_card_cube` を組んで `trichotomy` の `hWcube` 仮説を除去 → 0163 を閉じる

### PSL 分岐は Wielandt (9.1) を 2 回当てるだけでよい (2026-07-29 判明)

書籍は「`[K,P] ⋊ P` は Frobenius で `[K,P]` が `S/Q₀` 上 fpf ⟹ `C_{S/Q₀}(P) ≠ 1`」と
`S/Q₀` への作用で議論するが、**`C_{S/Q₀}(K) = 1` を出すのが面倒**。
`Q` と `Q₀` に直接 Wielandt を当てる方が短い:

* `wielandt_fixedPoint_trivial_U_fixed` (kernel が fpf ⟹ `|H| = |C_H(E)|^{|E|}`) を
  Frobenius 群 `[K,X] ⋊ X` の **`Q` への作用**と **`Q₀` への作用**に当てる:
  - `|Q| = |C_Q(X)|^p`
  - `|Q₀| = |C_{Q₀}(X)|^p`
* PSL 分岐は `natCard_cQ_eq_field` = `natCard_cQ0_eq_field` ⟹ `|C_Q(X)| = |C_{Q₀}(X)|`
* ⟹ `|Q| = |Q₀|`。しかし case (3) は `|Q| = |Q₀|³` なので `|Q₀|² = 1`、
  `two_le_card_Q0` に矛盾。∎

**進捗 (2026-07-29)**: 汎用部品
`OddOrder.GroupTheory.natCard_eq_pow_natCard_inf_centralizer_of_kernel_fpf`
(`GroupTheory/WielandtFixedPoint.lean`) を landing。
既存の `frobenius_kernel_centralizes_of_complement_fpf` と対になる
**ambient-subgroup 版**で、`U ⊔ E ≤ N_G(N)` の Frobenius 作用と
「kernel `U` が `N` 上 fpf」から `|N| = |C_N(E)|^{|E|}` を出す。
⟹ 残りは `[K,X] ⋊ X` の Frobenius 構造を組むだけ。

必要な入力はすべて repo に在る:
* `K` は巡回 (`K_isCyclic`)、`K ⊓ V = ⊥` (`K_inf_V_eq_bot`) ⟹ `X ⊓ K = ⊥`
* `K` は `Q` 上 fpf (`Q_inf_centralizer_eq_bot_of_mem_KSet` / `conjQByK_fixed_eq_one`)
* `[K,X] ≠ 1`: さもなくば `X ≤ C_V(K) = W = ⊥` で `X ≠ ⊥` に矛盾
* `K` 巡回 + coprime 作用 ⟹ `⁅K, X⁆ ⊓ C_G(X) = ⊥`
  (`BG.Ch3.commutator_inf_centralizer_eq_bot_of_isCommutative`,
  `S13_Corollary132.lean:273`; Peterfalvi Appendices は既に BG Ch1/Ch2/Ch3 を import 済)
* `X` は素数位数なので `Isaacs.Ch06.isFrobeniusGroup_of_prime_complement_fixedFree`
  (`FrobeniusGroup.lean:258`) で `IsFrobeniusGroup` が直接組める
  (要 `IsComplement'` + `⁅K,X⁆ ≠ ⊥` + fpf)

### Sz 分岐は `st` の位数で即死

`CentralizerSuzukiData.distinguishedProduct_order = 5` vs case (3) の
`orderOf_st_eq_three_of_card_cube` = 3。

### ⚠ 組み立ての簡略化: 持ち上げは**任意の逆像でよい** (2026-07-29)

当初「`d` を奇位数の元 `x ∈ F` に持ち上げる」と書いたが、**`x` の位数は使わない**。
矛盾は最後に `d = image(q)` (`q` は 2-元) と「`d` は奇位数 ≠ 1」の衝突で出るので、
`d` の位数だけが効く。⟹ 中心拡大での奇位数持ち上げ補題は不要。

確定した組み立て (`X` が書籍の `P`):

1. `S := C_Q(X)` は `C = C_G(X)` の Sylow 2 かつ `F` の Sylow 2、その像 `T` は
   `F/Z(F) ≅ standardPermGroup n` の Sylow 2。
2. `exists_ne_one_odd_centralizing_involutions_of_sylowTwo` を `T` に当てて
   `d ≠ 1`, 奇位数, `T` の involution を全部中心化、を得る。
3. `d` の**任意の**逆像 `x ∈ F` を取る (`d ≠ 1` ⟹ `x ∉ Z(F)`)。
4. `y ∈ C_{Q₀}(X)` は 2-元でその像は `T` の involution ⟹ `⁅x, y⁆ ∈ Z(F)`。
   `Z(F)` 奇 (部品 1) + `commute_of_commutatorElement_mem_of_coprime_natCard`
   ⟹ **`x` は `C_{Q₀}(X)` を中心化**。
5. 特に `Commute x s` ⟹ `x ∈ C_G(s) ≤ H` (`centralizer_le_H_of_mem_Q`) ⟹
   `x = q v` (`q ∈ Q`, `v ∈ V`; 部品 2)。
6. `V ≤ C_G(X)` (部品 2) ⟹ `q = x v⁻¹ ∈ Q ⊓ C = C_Q(X) ≤ F`、また `v ∈ F`。
7. `q ∈ Q` は `Q₀ ⊇ C_{Q₀}(X)` を中心化する (`Q0_le_centralizer_Q`) ので、
   `v` も `C_{Q₀}(X)` を中心化 ⟹ `v ∈ C_V(C_{Q₀}(X)) = X ⊔ W = X` (Galois, `W = ⊥`)。
8. `X ≤ Z(C)` かつ `F ≤ C` ⟹ `X ⊓ F ≤ Z(F)` ⟹ `image(v) = 1` ⟹ `d = image(q)`。
   `q` は 2-群 `C_Q(X)` の元だから `d` の位数は 2 冪。`d` は奇位数 ≠ 1 ⟹ 矛盾。∎


## ⚠ PSL 分岐: `⁅K,X⁆ ⋊ X` の Frobenius 性は無条件では成り立たない (2026-07-29 発見)

書籍 p.117 は「`[K,P] ⋊ P` is a Frobenius group」と無条件で書くが、**これは
`p ∤ q₀ − 1` (`q₀ = |C_{Q₀}(P)|`) と同値**で、Ch. III §1 の仮説からは出てこない。
体モデルで正確に計算した:

* `K ≅ Fˣ` (巡回, 位数 `q − 1`; `K` は `Q₀^#` 上正則 = Singer cycle)
* `W = 1` のとき `V ≅ A ≤ Gal(F/𝔽₂)`、`X` は `Gal(F/F₀)` (`F₀ = F^X`, `|F₀| = q₀`,
  `[F : F₀] = p`)
* `σ ∈ X` は `k ↦ k^{q₀}` なので `⁅k, σ⁆ = k^{q₀−1}`
  ⟹ `⁅K, X⁆ = K^{q₀−1}` (位数 `(q−1)/(q₀−1) = 1 + q₀ + … + q₀^{p−1}`)
* `C_K(X) = F₀ˣ` (位数 `q₀ − 1`)
* `K` は巡回なので `C_{⁅K,X⁆}(X) = 1 ⟺ gcd(q₀−1, (q−1)/(q₀−1)) = 1`。
  `1 + q₀ + … + q₀^{p−1} ≡ p (mod q₀−1)` より
  **`gcd = gcd(q₀−1, p)`、すなわち Frobenius ⟺ `p ∤ q₀ − 1`**

**具体的な破れ**: `p = 3`, `q₀ = 4` (`m₀ = 2`), `q = 4³ = 64`, `|K| = 63 = 3²·7`。
`C_K(X)` は位数 3、`⁅K,X⁆` は位数 21 でこれを含む ⟹ Frobenius でない。
`X` は `Gal(F₆₄/F₂) ≅ ℤ/6` の位数 3 の部分群として実在しうる。

⟹ **Ch. II (First Case) では問題にならない**: そこは step (1) で `|Q₀| = 2^p`
(`q₀ = 2`) なので `q₀ − 1 = 1` で自動的に `p ∤ q₀ − 1`。書籍が Ch. III でも
同じ言い回しを使ったのは、この差を見落としているか、別の理由で
`p ∤ q₀ − 1` が従うか、のどちらか。

### 次に調べること

1. Ch. III §1 の他の仮説 (case (3): `|Q| = |Q₀|³`, `Q` は Suzuki 2-群, `st` 位数 3,
   PSL 分岐の `C_Q(X) = C_{Q₀}(X)`) から `p ∤ q₀ − 1` が出るか。
2. 出ないなら、PSL 分岐を別ルートで潰す。手掛かり: PSL 分岐では
   `C_Q(X) = C_{Q₀}(X) ≤ Q₀` なので coprime 作用で **`X` は `Q/Q₀` 上
   fixed-point-free**。`|Q/Q₀| = q²` で `X` の位数は `p` だから
   `p ∣ q² − 1` などの算術制約が出る。ここを詰める。
3. `Q₀` 側の `|Q₀| = |C_{Q₀}(X)|^p` は **Artin (`finrank_fixedSet`) から
   Frobenius 抜きで出る**ので、そこは問題ない。


## ⚠⚠ さらに悪い: type C/D では `p ∣ q₀ − 1` が**導ける** (2026-07-29)

上の「Frobenius ⟺ `p ∤ q₀ − 1`」に対し、**PSL 分岐 + type C/D では逆向きの
`p ∣ q₀ − 1` が実際に従う**。つまり書籍の主張はこの場合に**成り立たない**。

導出:

1. PSL 分岐は `natCard_cQ_eq_field` = `natCard_cQ0_eq_field` = `ℓ = q₀` なので
   `C_Q(X) = C_{Q₀}(X) ≤ Q₀`。
2. coprime 作用 (`X` 奇位数 `p`, `Q` は 2-群) で
   `C_{Q/Q₀}(X) = C_Q(X)Q₀/Q₀ = 1` ⟹ **`X` は `M := Q/Q₀` 上 fpf**。
3. `K` も `M` 上 fpf: `C_Q(k) = 1` (`conjQByK_fixed_eq_one`) と coprime 作用から
   `C_{Q/Q₀}(k) = C_Q(k)Q₀/Q₀ = 1`。
   `K` は巡回で位数 `q − 1 = 2^m − 1`、`ord_{2^m−1}(2) = m` なので忠実既約
   `𝔽₂[K]`-加群の次元は `m`。`dim M = 2m` ⟹ `M = M₁ ⊕ M₂`、各 `|Mᵢ| = q`
   (書籍が type C/D について述べている `S/Q₀ = X ⊕ Y` と一致)。
4. `X` は `K` を正規化するので `K`-部分加群の集合を置換する。`Mᵢ` が非同型なら
   `{M₁, M₂}` を置換し、`p` は奇なので**各 `Mᵢ` を保つ** (書籍の議論そのもの)。
5. `X` は `M` 上 fpf ⟹ `M₁` 上も fpf ⟹ `M₁ ∖ {0}` の軌道は全て長さ `p`
   ⟹ `p ∣ |M₁| − 1 = q − 1 = q₀^p − 1`。Fermat で `q₀^p ≡ q₀ (mod p)` ゆえ
   **`p ∣ q₀ − 1`**。

⟹ この場合 `C_K(X)` (位数 `q₀ − 1`) は位数 `p` の元を含み、それは `⁅K,X⁆` の中に
あるので `C_{⁅K,X⁆}(X) ≠ 1` — **`⁅K,X⁆ ⋊ X` は Frobenius でない**。
書籍の「But `[K,P] ⋊ P` is a Frobenius group」はここで破綻している。

### 評価

* **Ch. II (First Case) では正しい**: `|Q₀| = 2^p` すなわち `q₀ = 2` なので
  `q₀ − 1 = 1`。書籍は Ch. III で同じ言い回しを流用したと思われる。
* 結論 (`W ≠ 1`) 自体が誤りとは限らない — **別ルートが要る**。

### 別ルートの候補 (次に試す)

(a) `p ∣ q₀ − 1` から直接矛盾を出す。手掛かり: `X` と `C_K(X)` の位数 `p` の元は
    可換で `V ⊓ K = 1` なので `D` は `(ℤ/p)²` を含む。`D` の構造 (`D = K ⋊ V`,
    `K` 巡回, `V` 巡回, `W = C_V(K) = 1`) と両立するか。
    ⚠ `W = 1` は「`V` の非自明元は `K` を中心化しない」であって
    「`K` の非自明元は `V` を中心化しない」ではない点に注意。
(b) type B を別扱いにする (書籍も case (3) 前半で type B と C/D を分けている)。
(c) `M₁ ≅ M₂` の場合 (書籍は非同型を主張するが、それ自体 Higman の分類由来)
    を潰す。
(d) 最終手段: 原文の行間を ChatGPT (最強モデル) に投げる
    ([[feedback-ask-chatgpt-for-elided-gaps]])。


## ✅ 正しいルートが判明: Frobenius でなく **Hilbert 90 (半線形写像の固定点)** (2026-07-29)

書籍の `[K,P] ⋊ P` Frobenius は不要かつ (type C/D で) 偽だが、**結論
`C_{S/Q₀}(P) ≠ 1` 自体は正しく、別の理由で出る**。

### 議論

`M := Q/Q₀` (case (3) で位数 `q²`、`Q₀ = Φ(Q) = Z(Q) = Ω₁(Q)` ゆえ基本可換)。

1. `K` は `M` 上 fpf (`C_Q(k) = 1` + coprime 作用で `C_{Q/Q₀}(k) = C_Q(k)Q₀/Q₀ = 1`)。
2. `K` は巡回で位数 `q − 1 = 2^m − 1`。fpf ⟹ `𝔽₂[K]`-加群としての既約成分は
   すべて**忠実**、忠実既約の次元は `ord_{2^m−1}(2) = m`。`dim M = 2m` ⟹
   斉次成分は 1 個 (両既約が同型) か 2 個 (非同型)。
3. `X` は `K` を正規化するので斉次成分を置換する。`|X| = p` は**奇**、成分は
   高々 2 個 ⟹ **各成分を保つ**。
4. 各斉次成分 `N` は体 `F_N = End_{𝔽₂[K]}(既約)` (位数 `2^m`) 上のベクトル空間で、
   `X` はその上に **`q₀`-半線形**に作用する (`x k x⁻¹ = k^{q₀}` だから)。
5. **位数 `p` の半線形写像は必ず非零固定点を持つ** (Hilbert 90 / Lang)。
   1 次元の場合は初等的: `x(v) = c·v^{q₀}` と書くと
   `x^p = 1 ⟺ c^{(q−1)/(q₀−1)} = 1`、一方
   `∃v≠0, x(v) = v ⟺ c^{-1} ∈ (Fˣ)^{q₀−1} ⟺ c^{(q−1)/(q₀−1)} = 1`。
   **両者は同じ条件**なので `x^p = 1` から固定点の存在が従う
   (`Fˣ` は巡回で `(q₀−1) ∣ (q−1)` という初等的事実だけ)。
6. ⟹ `C_M(X) ≠ 1`。しかし PSL 分岐では `C_Q(X) = C_{Q₀}(X) ≤ Q₀` から
   coprime 作用で `C_M(X) = 1`。**矛盾**。∎

### なぜ書籍の Frobenius が要らないか

Frobenius 群 `[K,P] ⋊ P` + kernel fpf ⟹ `C_M(P) ≠ 1` という定理 (Wielandt 9.1) を
使う代わりに、**`K` の作用が `M` に体構造を入れる**ことを使う。後者は
`K` が fpf かつ巡回であることだけから出るので、`p` と `q₀ − 1` の互いに素性が要らない。

### 形式化コスト

* 斉次成分の分解と `End_{𝔽₂[K]}(既約) = 体` (Schur + 有限可除環は体) — 新規
* 半線形写像の固定点 (step 5) — `Fˣ` 巡回の初等的計算に落ちる
* すでに repo にあるもの: `K` の fpf (`conjQByK_fixed_eq_one`)、
  coprime 作用の `C_{G/N}(A) = C_G(A)N/N`、`Q₀ = Φ(Q)` 系

⟹ 新規インフラは「`𝔽₂[K]`-加群の斉次分解 + 半線形固定点」。
`SemilinearRealization.lean` が `Q₀` について同型のことをやっているので、
そこの部品 (`exists_semilinear_field_model` 等) が流用できる可能性が高い。**次はここを実測**。


## 実装への申し送り: mathlib の該当 API (2026-07-29 実測)

Hilbert 90 の部分を実装するときの候補:

* `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`
  - `exists_div_of_norm_eq_one (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) : ∃ β : Lˣ, x = β / g β` — **古典形そのもの**。
    ただし `L/K` を Galois 拡大として据える必要があり、`Algebra.norm` 経由。
* `Mathlib/FieldTheory/Finite/GaloisField.lean`
  - `FiniteField.norm_surjective` / `FiniteField.unitsMap_norm_surjective`
    — 有限体のノルムは全射。初等ルートを採るならこれが鍵。
  - `FiniteField.frobeniusAlgEquivOfAlgebraic` +
    `bijective_frobeniusAlgEquivOfAlgebraic_pow` — Gal が Frobenius で生成される。

**初等ルート (基礎体を据えずに済む)**: `φ : Fˣ →* Fˣ`, `b ↦ b · (σ b)⁻¹` の像は
巡回群 `Fˣ` の位数 `(q−1)/(s−1)` の唯一の部分群 (`s = |F₀|`,
`q = s^n`, `n = orderOf σ`; `q = s^n` は既存の `finrank_fixedSet` = Artin から)。
`T v = c · σ v` が非零固定点を持つ ⟺ `c ∈ Im φ`。
`T^n = id ⟺ N(c) = 1` で、`Im φ ≤ ker N` は自明。残るのは `|ker N| = |Im φ|`
すなわち **ノルムの全射性**だけ ⟹ `FiniteField.norm_surjective` を使うか、
`σ = Frobenius^k` から `N(c) = c^{(q−1)/(s−1)}` を出す。

⟹ 新 leaf `OddOrder/Algebra/SemilinearFixedPoint.lean` の想定サイズは 80–150 行。
その後に `Q/Q₀` の `𝔽₂[K]`-加群構造 (斉次分解 + `End(既約) = 体`) が要る
— これは `SemilinearRealization.lean` (Q₀ について同じことをしている, 400 行) の
規模感。**次セッションはここから**。
