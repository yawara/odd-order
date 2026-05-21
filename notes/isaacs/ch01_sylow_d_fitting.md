# Isaacs §1D Fitting Subgroup `F(G)` — 設計ノート

**スコープ**: Isaacs §1D の主要新規実装、Phase 1 で mathlib に無く本プロジェクト
初の本格的な新規定義。形式化先: [`OddOrder/Isaacs/Ch01_Sylow.lean`](../../OddOrder/Isaacs/Ch01_Sylow.lean) §1D 内。
親ノート: [`ch01_sylow.md`](ch01_sylow.md).

## Isaacs における定義 (本書 p.27 §1D)

> We define the **Fitting subgroup** of `G`, denoted `F(G)`, to be the product of
> the subgroups `O_p(G)` as `p` runs over the prime divisors of `|G|`.

ここで `O_p(G) := ⋂ Syl_p(G)` は `G` の唯一最大の正規 `p`-部分群 (Problem 1B.2 の結論)。

**Cor 1.28** (主結果): `F(G)` は正規かつ冪零であり、`G` の任意の正規冪零部分群を含む
唯一最大の正規冪零部分群。

## 前提として必要になる先行アイテム

| 番号 | 内容 | 状態 |
|---|---|---|
| Lemma 1.27 | 互いに素な位数を持つ有限正規部分群族の積は直積 ⇒ 位数は積に等しい | TODO |
| Thm 1.26   | 有限 G が冪零 ⇔ 全 Sylow が正規 ⇔ G が Sylow の (内部) 直積 | TODO |
| `O_p(G)` 定義 | `iInf` over `Sylow p G` で部分群として定義 | 未定義 |
| `O_p(G)` 性質 | `O_p` は最大の正規 `p`-部分群 (Problem 1B.2) | TODO |

`O_p` も mathlib 未収載。Phase 1 の早い段階で `Subgroup.opGroup` (仮) として置く必要あり。

## 定義方針の選択肢

### Approach A (Isaacs 流: `sup` of `O_p` 群族)

```lean
/-- The Fitting subgroup of `G`: the supremum of `O_p(G)` over all primes `p`. -/
noncomputable def fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ p ∈ {p : ℕ | p.Prime}, opCore p G
```

* **長所**: Isaacs 本文と 1-1 対応。`O_p` 自体が独立して有用。Cor 1.28 の冪零性は
  Thm 1.26 (4 ⇒ 5: 全 Sylow 正規 ⇒ Sylow の直積) を `fitting G` 自身に適用すれば従う。
* **短所**: 先に `O_p` の定義 + Problem 1B.2 を片付ける必要があり、依存が深い。

### Approach B (構造的: 全冪零正規部分群の `sup`)

```lean
noncomputable def fitting (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
```

* **長所**: 「最大正規冪零」という普遍性が定義に直接書ける。
* **短所**: この `sSup` 自身が再び正規冪零であることの証明が非自明
  (Cor 1.29: `K, L` 正規冪零 ⇒ `KL` 正規冪零 が必要だが、これは Cor 1.28 自身から従うので循環)。
  実は Isaacs では Cor 1.28 を経由して Cor 1.29 を出す。
  Approach B を直接示すには「sSup が冪零」を別ルートで示す必要があり、
  結局 Approach A 経由が自然。

### 採用: Approach A

理由: Isaacs の論証構造に忠実。`O_p` も独立した有用定義になる。

## 必要な定義/補題の系列 (実装順)

```
1. opCore : ℕ → ∀ G : Group, Subgroup G
   ─ 定義: ⨅ P : Sylow p G, (P : Subgroup G)
   ─ 別表記: (sInf {(P : Subgroup G) | P ∈ Sylow p G})

2. opCore_normal      : (opCore p G).Normal
   ─ 共役で Sylow の集合が保たれることから

3. opCore_isPGroup    : IsPGroup p (opCore p G)
   ─ 任意 Sylow ⊆ p-群 で iInf ⊆ Sylow

4. opCore_le_sylow    : opCore p G ≤ (P : Subgroup G)  for any P : Sylow p G

5. opCore_is_max_normal_pSubgroup :
     ∀ N : Subgroup G, N.Normal → IsPGroup p N → N ≤ opCore p G
   ─ Isaacs Problem 1B.2; N ⊆ ⋂ Syl_p(G) は N が各 Sylow に含まれることから.

──────────────────────────────────────────────────────────

6. coprimeOrderProductDirect (Isaacs Lemma 1.27):
     ∀ X : Set (Subgroup G), (∀ Y ∈ X, Y.Normal) →
     (∀ Y₁ Y₂ ∈ X, Y₁ ≠ Y₂ → Nat.Coprime (Nat.card Y₁) (Nat.card Y₂)) →
     ∃ d : DirectProductLike, ... ∧ |⨆ X| = ∏ ...
   ─ mathlib `Subgroup.iSupIndep_of_coprime_card` あたりに既にあるかも?
     要 grep.

──────────────────────────────────────────────────────────

7. nilpotent_iff_all_sylow_normal (Isaacs Thm 1.26 (1)⇔(4)):
     [Finite G] → (Group.IsNilpotent G ↔ ∀ p, [Fact p.Prime] →
       ∀ P : Sylow p G, (P : Subgroup G).Normal)
   ─ mathlib `Group.isNilpotent_iff_sylow_normal`? 要 grep.

8. nilpotent_of_internal_direct_product_of_sylows (Isaacs Thm 1.26 (5)⇒(1)).

──────────────────────────────────────────────────────────

9. fitting : Subgroup G
   ─ 定義: ⨆ p prime, opCore p G  (素因数だけに渡る sup でも sSup でもよい)

10. fitting_normal     : (fitting G).Normal
11. fitting_isNilpotent : Group.IsNilpotent (fitting G)  (Thm 1.26 経由)

12. nilpotent_normal_le_fitting (Isaacs Cor 1.28 主要部):
     ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → N ≤ fitting G
   ─ N が冪零 ⇒ N の Sylow が N で正規 ⇒ G で特性的, 即ち正規 ⇒ N の各 Sylow ⊆ O_p(G) ⊆ fitting.

13. fitting_is_max_normal_nilpotent : fitting G が最大の正規冪零部分群.
14. (Cor 1.29) nilpotent_normal_mul_nilpotent_normal_is_nilpotent
     ─ Cor 1.28 から直結.
```

## mathlib 偵察結果 (2026-05-21, Explore agent)

**実装簡略化の主要発見**:

| 項目 | mathlib | 影響 |
|---|---|---|
| Lemma 1.27 (互いに素 ⇒ 直積) | `Subgroup.independent_of_coprime_order` @ NoncommPiCoprod.lean:305 | step 6 は薄いラッパー |
| Thm 1.26 全体 ((1)⇔(4)⇔(5)) | `isNilpotent_of_finite_tfae` @ Nilpotent.lean:941 | **step 7, 8 不要** |
| (4)⇒(5) の具体的同型 | `Sylow.directProductOfNormal` @ Sylow.lean:774 | TFAE 内部で活用 |
| p-群 ⇒ 冪零 | `IsPGroup.isNilpotent` @ Nilpotent.lean:904 | step 11 で `opCore` の冪零性に使用 |
| 部分群の冪零継承 | instance `Subgroup.isNilpotent` @ Nilpotent.lean:477 | step 5 相当を自動化 |
| 商の冪零継承 | instance `nilpotent_quotient_of_nilpotent` @ Nilpotent.lean:582 | 補助 |
| p-部分群 → Sylow 含有 | `IsPGroup.exists_le_sylow` @ Sylow.lean:159 | step 5 (`opCore` 最大性) の core |
| 互いに素素 p-群間の disjoint | `IsPGroup.disjoint_of_ne` @ PGroup.lean:304 | `opCore` 間直接性 |
| 正規 Sylow ⇒ 特性的 | `Sylow.characteristic_of_normal` @ Sylow.lean:736 | step 12 補助 |

**結論**:
- 新規実装の山は **step 1–5 (opCore 系) と step 9–13 (Fitting 系)** のみ。
- step 7, 8 は TFAE 1 行で代替。
- step 6 は wrapper で完了。

更新後の実装順:

```
1. opCore : ℕ → ∀ G, Subgroup G   定義: ⨅ P : Sylow p G, ↑P
2. opCore_normal, opCore_isPGroup, opCore_le_sylow, opCore_max_normal_pSubgroup
3. fitting : Subgroup G   定義: ⨆ p ∈ primeFactors |G|, opCore p G
4. fitting_normal, fitting_isNilpotent (← TFAE と IsPGroup.isNilpotent から)
5. nilpotent_normal_le_fitting (Cor 1.28 主要部)
6. (系) nilpotent_normal_mul_is_nilpotent (Cor 1.29)
```

## ファイル分割

§1D が大きくなりそうなので、現在の `Ch01_Sylow.lean` 内で 1500 行を超えたら
[CLAUDE.md](../../CLAUDE.md) の規約通り `Ch01_Sylow/` ディレクトリに分割する。
分割時の候補:

```
OddOrder/Isaacs/Ch01_Sylow/
├── A_Counting.lean    -- 1A
├── B_SylowE.lean      -- 1B
├── C_SylowCD.lean     -- 1C
├── D_Fitting.lean     -- 1D ← Fitting の本体
├── E_SmallOrder.lean  -- 1E (Thm 1.35 含む)
├── F_Brodkey.lean     -- 1F
└── G_ChermakDelgado.lean -- 1G
```

§1D に着手して 500-800 行を超えそうな見立てがついた段階で分割を実施 (先回りはしない)。

## 未解決の疑問

* `O_p(G)` の表記。mathlib 流に `Subgroup.opCore p G` が良いか、`OddOrder.O_p G` のような
  global 名にするか. **暫定**: `Subgroup.opCore p G` (将来 mathlib に投げやすい形)。
* `fitting` を `Subgroup.fitting` として `Subgroup` namespace に入れるか、
  `G` を引数にする global 関数にするか. **暫定**: `Subgroup.fitting G` (CLAUDE.md
  の "将来 `Subgroup.fitting` へリネーム可能な形" に従う)。
* Lemma 1.27 が mathlib に既存だった場合、自前定義は避ける。要 grep.
