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


## ✅ 代数的な核が完成 (2026-07-29)

`Algebra/SemilinearFixedPoint.lean` (新 leaf, sorry ゼロ, AxiomsCheck 登録済):

| 定理 | 内容 |
|---|---|
| `RingAut.exists_pow_eq` | 有限体の自己同型は `x ↦ x^s` (素体上で自動的に代数同型 + Gal は Frobenius 生成) |
| `exists_pow_eq_of_pow_natCard_div_eq_one` | 有限巡回群で `d ∣ N`, `x^(N/d) = 1` ⟹ `x` は `d` 乗 |
| `RingAut.exists_ne_zero_mul_pow_eq` | **Hilbert 90**: `\|F\| = s^n` + `c` の `s`-ノルム 1 ⟹ `v ↦ c·v^s` は非零固定点を持つ |

⟹ 書籍の誤った Frobenius 主張を置き換える**代数側は完済**。
`p ∤ q₀−1` はどこにも要らない。

### 残り (群論側の配線)

1. `Q/Q₀` に `𝔽₂[K]`-加群構造を入れる (`K` の共役作用)。
2. `K` が `Q/Q₀` 上 fpf であること: `C_Q(k) = 1` (`conjQByK_fixed_eq_one`) +
   coprime 作用の `C_{G/N}(a) = C_G(a)N/N`。
3. 斉次分解: `K` 巡回 + fpf ⟹ 既約成分は忠実で次元 `m`、`dim = 2m` ゆえ成分は高々 2。
   `X` は奇位数なので各成分を保つ。
4. 成分上で `X` が半線形 (`x k x⁻¹ = k^{q₀}`) — ここで `exists_pow_eq` を使い
   `End(既約) ≅ 𝔽_{2^m}` 上の `q₀`-半線形写像として `exists_ne_zero_mul_pow_eq` を適用。
5. ⟹ `C_{Q/Q₀}(X) ≠ 1`。PSL 分岐の `C_Q(X) ≤ Q₀` と矛盾。
6. Sz 分岐は `st` 位数 5 vs 3 で即死。PSU 分岐は完済。
7. 3 分岐が揃えば `W_ne_bot_of_card_cube` → `trichotomy` の `hWcube` 除去 → 0163 完了。

⚠ 3 の「`End(既約) ≅ 体`」と 1 の加群構造が最大の残作業。
`SemilinearRealization.lean` が `Q₀` について同じ構成 (`exists_semilinear_field_model`)
をしているので、そこから流用できるか実測するのが次の一手。


## 群論側の実測: repo に既に在るもの / 残る難所 (2026-07-29)

`StructureOfH/TwoKSubgroups.lean` (959 行) が case (3) 用に既に持っている:

* `IsKSubgroupSquare X` — `Q₀ ≤ X ≤ Q`, `K`-不変, `|X| = q²`
  (= `S/Q₀` の位数 `q` の `𝔽₂[K]`-部分加群を引き戻したもの)
* `exists_kSubgroupSquare_complement` — **operator Maschke**: `A ≤ D` 不変な `N` から
  同じく `A` 不変な補元 `N'` (`N ≠ N'`) を作る
* `exists_two_kSubgroups_unique_of_card_cube` — **非 type B なら K-部分群はちょうど 2 つ**
  (3 つ目があると Higman Thm (e) で type B になる)
* `conj_mem_of_unique_of_le_V` — 一意なら「`P` が `X`, `Y` を正規化する」

⟹ **非 type B の PSL 分岐は書籍の経路がそのまま通る**: 2 つの `K`-部分群は `X` 不変で、
その `N/Q₀` (位数 `q`, `K`-既約) の上で `X` は半線形に作用するので
`exists_ne_zero_mul_pow_eq` (Hilbert 90, 1 次元版) が `C_{N/Q₀}(X) ≠ 1` を与える。

### ⚠ 残る難所: **type B + PSL 分岐**

type B では `S/Q₀` は isotypic で **`K`-部分群が `q+1` 個**ある (書籍 p.117 が
そう書いている; `ℙ¹(𝔽_q)` の点の数)。すると:

* `X` (位数 `p`) は `q+1` 個を置換し、固定点の個数 ≡ `q+1 (mod p)`。
  `p ∤ q+1` なら固定される `K`-部分群があり 1 次元 Hilbert 90 が使える。
  **`p ∣ q+1` のときが問題** (Fermat で `p ∣ q₀+1` と同値)。
* このとき `M = Q/Q₀` は `E = 𝔽_{2^m}` 上 2 次元で `X` は半線形。固定点非零は
  **Lang / Speiser (GL₂ の Hilbert 90)** が要る — 1 次元版では足りない。
* 書籍の type B 用の逃げ道「`P` centralizes an element of order 4 in `S`」は
  **PSL 分岐では使えない**: PSL 分岐は `C_S(P)` が基本可換 (位数 4 の元が無い)。

### 次の一手の候補

(a) 非 type B の PSL 分岐だけ先に閉じる (書籍経路 + 1 次元 Hilbert 90)。
(b) type B かつ `p ∣ q₀+1` の場合を潰す: `X` は `M` 上 fpf で
    `F₀`-線形 (`σ` は `F₀` 上恒等) なので `M` は `F₀[ℤ/p]`-加群、
    `dim_{F₀} M = 2p`、非自明既約の次元は `d₀ = ord_p(q₀)`。
    `d₀ ∣ 2p` かつ `d₀ ∣ p−1` ⟹ `d₀ ∣ 2`。ここから先を詰める。
(c) Lang/Speiser (GL_n 版 Hilbert 90) を形式化する。


## 🎯 PSL 分岐の完全な議論が確定 — 2 ルートは**相補的** (2026-07-29)

行き詰まりだと思っていた「type B + `p ∣ q+1`」は、実は**書籍の Frobenius ルートが
使える唯一の場合**だった。`p ∣ q₀ − 1` で場合分けすると議論が閉じる。

設定: case (3), `W = 1`, `X ≤ V` 位数 `p` (奇), PSL 分岐。
Artin (`finrank_fixedSet`) より `q = q₀^p` (`q = |Q₀|`, `q₀ = |C_{Q₀}(X)|`)。
PSL 分岐より `C_Q(X) = C_{Q₀}(X) ≤ Q₀`。

### 場合 1: `p ∤ q₀ − 1` — **書籍の Frobenius ルート**

このとき `C_{⁅K,X⁆}(X) = 1` (既に示した同値性) なので `⁅K,X⁆ ⋊ X` は Frobenius 群。
`K` は `Q` 上 fpf (`conjQByK_fixed_eq_one`) だから kernel `⁅K,X⁆` も fpf。
Wielandt (9.1) の ambient 版 `natCard_eq_pow_natCard_inf_centralizer_of_kernel_fpf` を
`Q` と `Q₀` に当てると

  `|Q| = |C_Q(X)|^p`,  `|Q₀| = |C_{Q₀}(X)|^p`

で `C_Q(X) = C_{Q₀}(X)` だから `|Q| = |Q₀|`。case (3) の `|Q| = |Q₀|³` と
`2 ≤ |Q₀|` に矛盾。∎

### 場合 2: `p ∣ q₀ − 1` — **Hilbert 90 ルート**

`q₀ − 1 ∣ q − 1` なので `p ∣ q − 1`。すると `p ∣ q + 1` なら `p ∣ 2` で `p` 奇に反するので
**`p ∤ q + 1`**。

`Q/Q₀` の位数 `q` の `K`-部分加群の個数は **2 個 (非 isotypic) か `q+1` 個 (isotypic)**
のいずれかで、`p` はそのどちらも割らない (`p` 奇ゆえ `p ∤ 2`、上より `p ∤ q+1`)。
⟹ 位数 `p` の `X` はそれらを置換して**必ず固定する**ものがある。

固定された `N/Q₀` (位数 `q`, `K`-既約) の上で `X` は `q₀`-半線形に作用するので
`RingAut.exists_ne_zero_mul_pow_eq` (Hilbert 90, 1 次元版) より `C_{N/Q₀}(X) ≠ 1`。
しかし PSL 分岐の `C_Q(X) ≤ Q₀` と coprime 作用から `C_{Q/Q₀}(X) = 1`。矛盾。∎

### 意義

* **Lang/Speiser (GL₂ 版 Hilbert 90) は要らない** — 2 次元の困難な場合は
  ちょうど Frobenius ルートが使える場合と一致する。
* 書籍の議論は**間違いではなく不完全**だった: `p ∤ q₀ − 1` のときは正しく、
  `p ∣ q₀ − 1` のときに別の理由 (Hilbert 90) が要る。
  Ch. II では `q₀ = 2` なので常に場合 1。

### 形式化の残り

1. 場合 1: `⁅K,X⁆ ⋊ X` の `IsFrobeniusGroup` 構成
   (`isFrobeniusGroup_of_prime_complement_fixedFree` + BG の
   `commutator_inf_centralizer_eq_bot_of_isCommutative`; 部品は揃っている)
   + `natCard_eq_pow_natCard_inf_centralizer_of_kernel_fpf` の適用 2 回。
2. 場合 2: `Q/Q₀` の `K`-部分加群の個数が 2 か `q+1`、`X` が固定するものの存在、
   その上での半線形性 (`End_K(既約) ≅ 𝔽_q`) と `exists_ne_zero_mul_pow_eq` の適用。
   `TwoKSubgroups.lean` の `IsKSubgroupSquare` / operator Maschke /
   `conj_mem_of_unique_of_le_V` が土台。
3. Artin から `q = q₀^p` (= `|Q₀| = |C_{Q₀}(X)|^p`) を出す配線
   (`finrank_fixedSet` + `GaloisCentralizer.lean` の半線形モデル)。


## 進捗: PSL 分岐 case 1 が完済 (2026-07-29)

`StructureOfH/WielandtOnQ.lean` に landing (sorry ゼロ, AxiomsCheck 登録済):

* `isFrobeniusGroup_commutator_K_sup` — `p ∤ |K|` のとき `⁅K,X⁆ ⋊ X` は Frobenius
* `natCard_eq_pow_natCard_inf_centralizer` — Wielandt `|N| = |C_N(X)|^{|X|}`
  (H-不変な 2-部分群 `N ≤ Q` すべて)

⟹ **case 1 (`p ∤ q₀−1`) の数学は完済**。残るのは:

* (α) `p ∤ q₀−1 ⟹ p ∤ |K|` の配線 (`|K| = q−1` = `card_K_eq_card_Q0_sub_one`,
  `q = q₀^p` + Fermat)
* (β) case 2 (`p ∣ q₀−1`): `X` が固定する `K`-部分加群の存在 + その上の半線形性
  + `exists_ne_zero_mul_pow_eq`
* (γ) Artin から `q = q₀^p` (= `|Q₀| = |C_{Q₀}(X)|^p`) を出す配線
* (δ) 3 分岐の組み立てと `hWcube` の除去

### 全体の進捗表

| 部品 | 状態 |
|---|---|
| PSU 分岐 (書籍の "as can be checked") | ✅ `CentralizerPSUData.false_of_W_eq_bot` |
| Sz 分岐 | 未 (`st` 位数 5 vs 3 で即死、易) |
| PSL 分岐 case 1 (`p ∤ q₀−1`) | ✅ 数学完済 (配線 α 残) |
| PSL 分岐 case 2 (`p ∣ q₀−1`) | 代数側 ✅ (Hilbert 90) / 群論側 β 残 |
| Galois `C_V(C_{Q₀}(P)) = P ⊔ W` | ✅ |
| Artin `q = q₀^p` | 配線 γ 残 |
| 組み立て | δ 残 |


## 進捗表 (2026-07-29 セッション終盤)

| 部品 | 状態 | 場所 |
|---|---|---|
| PSU 分岐 (書籍の "as can be checked") | ✅ | `PSUCentre.lean` `CentralizerPSUData.false_of_W_eq_bot` |
| PSL 分岐 case 1 (`p ∤ q₀−1`) | ✅ end-to-end | `WielandtOnQ.lean` `false_of_natCard_cQ_eq_cQ0_of_card_cube` |
| PSL 分岐 case 2 (`p ∣ q₀−1`) | 代数 ✅ / 群論 β 残 | `SemilinearFixedPoint.lean` (Hilbert 90) |
| Sz 分岐 | 組み立て時に `st` 位数 5 vs 3 で即死 | — |
| Galois `C_V(C_{Q₀}(P)) = P ⊔ W` | ✅ | `GaloisCentralizer.lean` |
| Artin `\|Q₀\| = \|C_{Q₀}(X)\|^{\|X\|}` | ✅ | `GaloisCentralizer.lean` `natCard_Q0_eq_pow_of_W_eq_bot` |
| Fermat 橋 (`p ∤ q₀−1 ⟹ p ∤ \|K\|`) | ✅ | `WielandtOnQ.lean` `coprime_natCard_K_of_not_dvd` |
| 組み立て δ | 残 | `Trichotomy.lean` の `hWcube` 除去 |

### 残り β の内訳 (case 2 の群論配線)

`p ∣ q₀−1` ⟹ `p ∣ q−1` ⟹ `p ∤ q+1`。`Q/Q₀` の位数 `q` の `K`-部分加群は
2 個か `q+1` 個で `p` はどちらも割らないので `X` は必ずどれかを固定する。
その固定された `N/Q₀` の上で:

1. `End_{𝔽₂[K]}(N/Q₀) ≅ 𝔽_q` (Schur + 有限可除環は体) — **新規**
2. `X` が `q₀`-半線形に作用 (`x k x⁻¹ = k^{q₀}`) — `exists_pow_eq` を使う
3. `exists_ne_zero_mul_pow_eq` を適用して `C_{N/Q₀}(X) ≠ 1`
4. PSL 分岐の `C_Q(X) ≤ Q₀` + coprime 作用の `C_{Q/Q₀}(X) = 1` と矛盾

土台: `TwoKSubgroups.lean` の `IsKSubgroupSquare` / operator Maschke /
`exists_two_kSubgroups_unique_of_card_cube` / `conj_mem_of_unique_of_le_V`。


## β の再設計: **加群論は要らない** — `K` が正則に作用することを使う (2026-07-29)

「`End_{𝔽₂[K]}(N/Q₀) ≅ 𝔽_q` (Schur + Wedderburn)」は**不要**だった。

`K` は `N/Q₀` (位数 `q`) 上 fpf で `|K| = q − 1 = |(N/Q₀) ∖ {1}|` なので、
`K` は `(N/Q₀) ∖ {1}` 上 **正則 (regular)** に作用する。基点 `ω₀` を取ると
`Ω := (N/Q₀) ∖ {1}` は `K` と同一視でき、`X` の作用は

  `k ↦ α(k) · c`   (`α(k) = x k x⁻¹`, `c` は `x · ω₀ = c · ω₀` で決まる)

になる。固定点があること ⟺ `c⁻¹ ∈ Im(k ↦ k⁻¹ α(k))`。
`x^p = 1` は `x^p` が `k ↦ k · N(c)` (`N(c) = ∏_{i<p} α^i(c)`) なので `N(c) = 1`。

⟹ **β は「巡回群 `K` に対する Hilbert 90 (`ker N = Im(k ↦ k⁻¹α(k))`)」に帰着**。
加群の斉次分解も `End = 体` も要らない。

## ⚠ 現行 `exists_ne_zero_mul_pow_eq` は一般の `σ` を覆っていない

現行版の仮説は `Nat.card F = s ^ n` (`σ x = x^s`)。しかし応用では `σ` は
`Gal(F/F₀)` の**生成元**であって Frobenius そのものとは限らない:
`σ = Frob_{F₀}^j` (`gcd(j, p) = 1`) なので `s = q₀^j` で、
`|F| = q₀^p ≠ s^p = q₀^{jp}` (`j ≠ 1` のとき)。⟹ そのままでは適用できない。

### 一般形とその証明

**必要な形**: 有限体 `F`, `σ : RingAut F`, `n = orderOf σ`,
`N(c) = ∏_{i<n} σ^i(c)`。このとき `ker N = Im(a ↦ a · σ(a)⁻¹)` (Fˣ 内)。

* `Im ⊆ ker N` は自明 (`N ∘ σ = N`)。
* `|Im| = (Q−1)/(s₀−1)` (`s₀ = |F^σ|`; `ker(a ↦ a σ(a)⁻¹) = (F^σ)ˣ`)。
* `|ker N| = (Q−1)/|Im N|` かつ `Im N ⊆ (F^σ)ˣ` ⟹ `|ker N| ≥ |Im|`。
* 等号には **ノルムの全射性** `FiniteField.norm_surjective` が要る
  (`Mathlib/FieldTheory/Finite/GaloisField.lean`)。
  そのためには `Algebra.norm (F^σ) = ∏_{i<n} σ^i` の同一視 (Galois 拡大の
  ノルム = 自己同型の積) を経由する。

⟹ **次の一手**: `SemilinearFixedPoint.lean` に一般形を足す。
`FixedPoints.subfield ⟨σ⟩ F` を基礎体に据えて `IsGalois` を出し
(`FixedPoints.normal` / `isSeparable` の instance は mathlib にある)、
`Algebra.norm_eq_prod_automorphisms` 系で積表示に直し、
`FiniteField.norm_surjective` を使う。想定 150–250 行。
現行の `s`-冪版は特殊化として残す (`|F| = s^n` を満たす場合には短い)。


## ✅ 穴の回避策: **`X` の生成元を選び直す** (2026-07-29)

前節の「一般形 Hilbert 90 が要る」は**回避できる**。一般形も
`FiniteField.norm_surjective` も要らない。

問題は「`x` が誘導する `σ` が `Frob_{F₀}` そのものとは限らない
(`σ = Frob_{F₀}^j`)」ことだった。しかし `X` は素数位数 `p` の巡回群なので
**生成元を取り替えればよい**:

1. `B` = `X` の `RingAut F` での像 (位数 `p`)。
   Artin の `fixer_fixedSet` (既に landing 済) より **`B = fixer (fixedSet B)`**。
2. `F₀ := fixedSet B` は位数 `q₀` の部分体なので、`τ : a ↦ a^{q₀}` は `F₀` を
   各点固定する ⟹ **`τ ∈ fixer (fixedSet B) = B`**。
3. `q₀ < q` なら `τ ≠ 1`、`|B| = p` は素数 ⟹ **`τ` は `B` を生成**。
4. ⟹ `X` の生成元 `x'` で、誘導する自己同型がちょうど `τ` になるものが取れる。
5. その `x'` に対しては `s = q₀` で `|F| = q₀^p = s^p` なので
   **現行の `exists_ne_zero_mul_pow_eq` がそのまま使える**。
   `X = ⟨x'⟩` だから `C_M(X) = C_M(x')` で情報は失われない。

⟹ β は「生成元の取り替え + 既存の 1 次元 Hilbert 90 + `K` の正則作用」で閉じる。
新規の重い代数 (Schur / Wedderburn / Lang / ノルム全射性) は**一切不要**。

### β の実装手順 (確定版)

1. ~~`exists_frobenius_generator`~~ ✅ **`RingAut.exists_generator_pow_natCard_fixedSet`**
   (`SemilinearFixedPoint.lean`): `B ≤ RingAut F` が素数位数 `p` なら
   `a ↦ a^{|F^B|}` が `B` の生成元で `|F| = |F^B|^p`。
   ⟸ `s ∣ |F|` から `s` は標数の冪 → Frobenius の冪 → `fixer_fixedSet` で `B` に属する
   → 非自明 (さもなくば `Fˣ` の生成元の位数が `s−1` 以下) → 素数位数。
2. `K` の `(N/Q₀) ∖ {1}` 上の正則性 (fpf + 位数一致)。
3. 基点を取って `Ω ≅ K` とし、`x'` の作用を `k ↦ α(k)·c` の形にする。
4. `x'^p = 1` から `N(c) = 1`、`exists_ne_zero_mul_pow_eq` で固定点を得る。
5. `C_{Q/Q₀}(X) ≠ 1` ⟹ PSL 分岐の `C_Q(X) ≤ Q₀` と矛盾。


## ✅ β step 2-3 は既存の `exists_field_semilinear` で済む (2026-07-29)

`Peterfalvi/Appendices/SemilinearField.lean` の
**`exists_field_semilinear`** (Appendix I Prop 2(a)+(b)) が丸ごと使える:

```
(hE : IsElementaryAbelian p E) (ψ : T →* MulAut E)   -- T は可換有限群
(hirr : ∀ U, IsAInvariant ψ U → U = ⊥ ∨ U = ⊤)
⟹ ∃ F 体, Module F (Additive E), finrank F (Additive E) = 1, |F| = |E| ∧
   ∀ g : MulAut E, (g が T-作用を正規化) → ∃ σ : F ≃+* F, g が σ-半線形
```

`E := N/Q₀`, `T := K`, `ψ` = 共役作用 とすればよい:

* `hirr`: `K` は `E` 上 fpf で `|K| = q−1 = |E ∖ {1}|` ⟹ 軌道は 1 個 ⟹
  非自明な不変部分群は `E∖{1}` を丸ごと含む ⟹ `⊤`。
* `g` := `x'` の `E` 上の作用。`x` が `K` を正規化するので条件を満たす。
* `finrank F E = 1` なので基底 `e₀` を取ると `x'(a • e₀) = σ(a)·c • e₀`
  (`c` は `x'(e₀) = c • e₀` で決まる) ⟹ 座標で `a ↦ c · σ(a)`
  = **`exists_ne_zero_mul_pow_eq` の形そのもの**。

⟹ β の残りは「`X` 不変な `K`-部分群 `N` の取得」(`TwoKSubgroups.lean` の
`exists_two_kSubgroups_unique_of_card_cube` + `conj_mem_of_unique_of_le_V`、
および isotypic 側は `p ∤ q+1` からの固定点数え上げ) と、上の配線だけ。
**新規の重い代数はもう無い。**


## ⚠ 抽象補題には `σ ≠ 1` が要る (2026-07-29)

「`E` 上の素数位数 `p` の自己同型 `g` は非自明な固定点を持つ」は**そのままでは偽**。

`finrank F E = 1` なので基底 `e₀` を取ると `g(a • e₀) = σ(a)·c • e₀`
(`g(e₀) = c • e₀`)。もし **`σ = 1`** なら `g` は `F`-線形、すなわち `c ∈ Fˣ` による
スカラー倍で、`a·c = a` の非零解は無い ⟹ `C_E(g) = 1`。
(`σ = 1` は「`g` が `End_T(E) = F` と可換」= 「`g` 自身がスカラー」の場合。)

### 本件では `σ ≠ 1` が保証される

`σ` は `F` への `g` の共役作用で、`T = K` の像 (= スカラー `Fˣ`) の上では
`k ↦ x k x⁻¹` に一致する。もし `σ = 1` なら `x` は `K` を中心化し
`x ∈ C_V(K) = W = ⊥` となって `x ≠ 1` に矛盾。
⟹ **`W = 1` がここでも効く** (Galois の箇所とは別の使われ方)。

### 抽象補題の確定形

```
(hE : IsElementaryAbelian p₀ E) [Nontrivial E]
(ψ : T →* MulAut E) (hψ : Function.Injective ψ)   -- T 可換有限
(hirr : ∀ U, IsAInvariant ψ U → U = ⊥ ∨ U = ⊤)
{g : MulAut E} (hgord : orderOf g = p) (hp : p.Prime)
{cT : T ≃* T} (hcT : ∀ t, ψ (cT t) = g * ψ t * g⁻¹) (hcTne : cT ≠ 1)
⟹ ∃ e ≠ 1, g e = e
```

証明手順:
1. `exists_field_semilinear` で `F`, `finrank F E = 1`, `σ` を得る。
2. `cT ≠ 1` + `ψ` 単射 ⟹ `σ ≠ 1` ⟹ `B := ⟨σ⟩` は位数 `p`。
3. `exists_generator_pow_natCard_fixedSet` で `B` の標準生成元 `τ` (`a ↦ a^s`,
   `|F| = s^p`) を取り、`σ = τ^j` (`gcd(j,p) = 1`) から
   **`g` を `g^{j'}` に取り替える** (`jj' ≡ 1 mod p`)。`⟨g⟩` は不変なので
   固定点集合も不変。
4. `g^{j'}` は `τ`-半線形。基底座標で `a ↦ c·τ(a) = c·a^s`。
   `(g^{j'})^p = 1` から `N(c) = c^{(|F|−1)/(s−1)} = 1`。
5. `exists_ne_zero_mul_pow_eq` で非零固定点 ⟹ 非自明な `e ∈ E` で `g e = e`。


## 実装メモ: `AddAut M` の群構造は自動で入らない (2026-07-29)

抽象補題を `T : AddAut M`, `T ^ p = 1` で書こうとしたが、
`[AddCommGroup M]` だけでは `HPow (AddAut M) ℕ` / `OfNat (AddAut M) 1` が
合成できなかった (`Mathlib.Algebra.Group.End` を import しても同じ)。

⟹ **`Function.iterate` で書く**のが確実:

* 仮説を `hTp : ∀ x, T^[p] x = x` (`T : M ≃+ M`) にする。
* 生成元の取り替えも iterate で済む: `T' := T^[j']` の固定点 `x` は
  `T = (T')^[j'']` (`j' j'' ≡ 1 mod p`) だから `T` の固定点でもある
  — 群構造は不要で、必要なのはこの一方向だけ。
* 半線形性 `T (a • x) = σ a • T x` から
  `T^[n] (a • x) = (σ^[n] a) • T^[n] x` を帰納で出す。

この形なら `exists_generator_pow_natCard_fixedSet` +
`exists_ne_zero_mul_pow_eq` に繋がる。**次セッションはこの形で書き直す。**
(今回の draft は sorry を残さないよう撤収済み。)


## 進捗表 (2026-07-29 セッション終了時)

### 代数側: **完済**

| 定理 | 場所 |
|---|---|
| `RingAut.fixer_fixedSet` / `finrank_fixedSet` | `Algebra/FixedPointsGalois.lean` |
| `RingAut.exists_pow_eq` | `Algebra/SemilinearFixedPoint.lean` |
| `exists_pow_eq_of_pow_natCard_div_eq_one` | 同上 |
| `RingAut.exists_ne_zero_mul_pow_eq` (Hilbert 90) | 同上 |
| `RingAut.exists_generator_pow_natCard_fixedSet` | 同上 |
| **`exists_ne_zero_fixed_of_semilinear`** | 同上 (β の核) |

### 群論側

| 部品 | 状態 |
|---|---|
| PSU 分岐 (書籍の "as can be checked") | ✅ `CentralizerPSUData.false_of_W_eq_bot` |
| PSL 分岐 case 1 (`p ∤ q₀−1`) | ✅ `false_of_natCard_cQ_eq_cQ0_of_card_cube` |
| Galois `C_V(C_{Q₀}(P)) = P ⊔ W` | ✅ |
| Artin `\|Q₀\| = \|C_{Q₀}(X)\|^{\|X\|}` | ✅ |
| Fermat 橋 / Frobenius 構成 / Wielandt | ✅ |
| **PSL 分岐 case 2 の配線** | 残 |
| **3 分岐の組み立て (`hWcube` 除去)** | 残 |

### 残り 2 件の内訳

**(β-wire)** `N/Q₀` を `CommGroup` として作り、`K` の共役作用
`ψ : ↥K →* MulAut (N/Q₀)` を組んで `exists_field_semilinear` に渡す。
`hirr` は `K` fpf + `|K| = |N/Q₀| − 1` から (軌道が 1 個)。
得た半線形性を `exists_ne_zero_fixed_of_semilinear` に渡して
`C_{N/Q₀}(X) ≠ 1`、PSL 分岐の `C_Q(X) ≤ Q₀` と矛盾。
⚠ `σ ≠ 1` は `W = ⊥` + `x ≠ 1` から (`x ∈ C_V(K) = W`)。

**(δ)** `X` 不変な `K`-部分群 `N` の取得 (`TwoKSubgroups.lean` の
`exists_two_kSubgroups_unique_of_card_cube` + `conj_mem_of_unique_of_le_V`;
isotypic 側は `p ∤ q+1` からの固定点数え上げ) と、
Sz 分岐 (`st` 位数 5 vs 3) を含む 3 分岐の組み立て。
