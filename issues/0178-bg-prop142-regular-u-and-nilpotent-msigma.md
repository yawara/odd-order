---
id: 178
slug: bg-prop142-regular-u-and-nilpotent-msigma
title: "BG Prop 14.2: (a) の regular action on U と (g) の M_sigma nilpotent が未形式化"
created: 2026-08-08
---

# BG Prop 14.2: (a) の regular action on `U` と (g) の `M_σ` nilpotent が未形式化

## 位置づけ — BG 逐条監査 ([0177](0177-bg-full-formalization.md)) で見つかった**唯一の真の未形式化**

§1-§13 (127 件) + §14 前半の監査で見つかった問題は**すべて packaging 差か stale 注記**
(実体は在る) だった。本 issue はそれと違い、**書籍の主張が repo のどこにも無い** 2 件。

⚠ 「notes に deferred と書いてあった」ではなく、**概念形の grep で全 repo を走査して不在を確認**
した (BG 監査では「deferred 注記の 8 割が stale」だったので、注記は根拠にしない)。

## 未形式化の 2 件

書籍 Prop 14.2 (p. 106、`M ∈ 𝓜_𝒫`、`K` = Hall `κ(M)`-部分群、`K* = C_{M_σ}(K)`、
`U` = Hall `(κ(M) ∪ σ(M))'`-部分群):

### (1) 条項 (a) の後半

> The group `K` acts in a prime manner on `M_σ` **and acts regularly on some abelian Hall
> `(κ(M) ∪ σ(M))'`-subgroup `U` of `M`. (Thus `U M_σ` is a normal complement of `K` in `M`.)**

* **前半** (prime manner on `M_σ`) は `typeP_structure` の第 1 連言として在る ✅
* **後半** (`U` が abelian / `K` が `U` に regular / `U M_σ` が `K` の normal complement) が無い
* ⚠ `typeP_structure` は `U` の Hall 性を**仮説 `_hU` として受け取り、しかも使っていない**
  (アンダースコア付き)

### (2) 条項 (g) の第 3 主張

> If `M ∈ 𝓜_{𝒫₂}`, i.e. `U ≠ 1`, then `σ(M) = β(M)`, `K` has prime order, **and `M_σ` is a
> nilpotent TI-subgroup of `G`**.

* `σ(M) = β(M)` ✅ / `|K|` prime ✅ / `M_σ` が TI ✅ — いずれも `typeP_structure` に在る
* **`M_σ` が nilpotent** だけが無かった

### ✅ (g) は 2026-08-08 に解決 — `S14.typeP2_Msigma_isNilpotent`

書籍の証明どおり: `U ≠ 1` ⟹ `E` は kernel `U` の Frobenius 群 ⟹ **Lemma 14.1** が
`C_{M_σ}(U) = 1` と `M_σ` 冪零の両方を与える。repo には部品がすべて在った:

* `E23_ne_bot_of_isTypeP2_caseTau1` — type-`P₂` ⟹ `U = E₂E₃ ≠ ⊥`
* `Msigma_centralizer_E23_eq_bot_of_caseTau1` — `U ≠ ⊥` ⟹ `C_{M_σ}(U) = 1` **かつ `M_σ` 冪零**
  (Lemma 14.1 を `|U|` の素数に適用したもの)
* `κ ∩ τ₃ ≠ ∅` のケースは `kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E` で
  type `P₁` を強制し `IsTypeP2` と矛盾 ⟹ 起こりえない

⟹ 欠けていたのは**この 3 つを繋ぐ endpoint だけ**だった。AxiomsCheck 登録済・axiom-clean。

### 🚨 起票時の見込み違いを訂正 (2026-08-08)

起票時に「下流 `AppE_CorollaryE5` / `AppE_E5Counting` の仮説 `hMσnil` を実証明に置換できる」
と書いたが、**これは誤り**。AppE の `hMσnil` は **Corollary 15.9 の状況** ——
15.9(a) が `M ∈ 𝓜_F`、15.9(b) が「`M` は Frobenius 群」を与えるので `M_σ` は
**Frobenius kernel として冪零** —— から来ており、type-`P₂` 経路とは別物。
(15.9 では `N` の側が `𝓜_{𝒫₂}`。) ⟹ **AppE は unblock されない**。

⚠ 教訓: 「仮説 `h` が下流に在る」ことを grep で見つけても、**その `h` がどの定理から来る
はずかを書籍で確認する**まで「閉じれば置換できる」と書かない。

## 確認の手順 (再現可能)

```bash
# (1) regular action on U
grep -rn "ActsRegularlyOn" OddOrder/BG/Ch4_FamilyOfMaximal/ --include=*.lean
#   → E₁/E₃ 相手の regular しか無く、K が U に regular という結論は存在しない

# (2) M_σ nilpotent
grep -rn "Group.IsNilpotent ↥(.*Msigma" OddOrder/BG/ --include=*.lean
#   → AppE_CorollaryE5 / AppE_E5Counting の **仮説** (hMσnil) としてしか現れない
```

## 書籍の証明の所在

BG p. 106-109 (pdftotext L5698-5734)。`E`, `E₁`, `E₂`, `E₃` を §12 のとおり `E ⊇ K` に取り、
Lemma 12.1 から始まる。⟹ **§12 の `SubgroupESetup` 機構がそのまま使える**はずで、
repo は既に `exists_subgroupESetup_with_le` を持っている (`typeP_structure` が使っている)。

## 作業単位

1. ~~**(g) の `M_σ` nilpotent**~~ ✅ **2026-08-08 完了** (`S14.typeP2_Msigma_isNilpotent`)。
2. ⬜ **(a) 後半** — `U` の abelian 性 + `K` の regular 作用 + `U M_σ` が normal complement。

## 参照

- 親 issue: [0177](0177-bg-full-formalization.md)
- 実体: `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/ElemAbelianNeighbor.lean`
  (`typeP_structure`; docstring に本 issue の内容を明記済)
- 書籍: `references/bg/local-analysis.pdf` p. 106

## 🔴 優先度の根拠 (2026-08-08 追記): この gap は BG 主定理 **Theorem A(3)(4)** そのもの

issue 0177 の Theorems A-E 監査で、Theorem A の 8 条項を §10-§15 の結果に還元したところ:

| Thm A | 内容 | 下敷き | 状態 |
|---|---|---|---|
| **(3)** | `K M_σ` は `M` 内に **`K`-不変な補群 `U`** を持ち `U M_σ ⊴ M = K U M_σ` | **Prop 14.2(a) 後半** | 🔴 本 issue |
| **(4)** | 各 `k ∈ K^#` で **`C_U(k) = 1`** | **Prop 14.2(a) 後半** | 🔴 本 issue |

他の 6 条項 ((1)(2)(5)(6)(7)(8)) はすべて被覆済。⟹ **Theorem A を書籍の形で述べるには
本 issue を閉じる必要がある**。周辺的な条項の欠落ではない。

`M_σ` の冪零性 (条項 (g)) も同様に、下流 `AppE_*` が仮説として取っている。
