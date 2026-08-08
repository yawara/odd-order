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
* **`M_σ` が nilpotent** だけが無い
* ⚠ **下流 `AppE_CorollaryE5.lean` / `AppE_E5Counting.lean` は
  `Group.IsNilpotent ↥(Msigma M)` を仮説 `hMσnil` として取っている** —
  CLAUDE.md が警告する「hard content を未充足の仮説に hoist する」形になっている
  ([[scaffold-sorry-free-not-done]])。⟹ **これを閉じると下流の仮説が実証明に置換できる**。

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

1. **(g) の `M_σ` nilpotent を先に** — 下流 (AppE) の仮説を実証明に置換できるので価値が明確。
   Thm 12.5(a) (`Msigma_nilpotent_of_tau2`) が `τ₂(M) ≠ ∅` の場合の `M_σ` 冪零を既に与えている
   ので、type-`P₂` の場合にそれが使えるか (あるいは `σ = β` 経由の別ルートか) を先に確認する。
2. **(a) 後半** — `U` の abelian 性 + `K` の regular 作用 + `U M_σ` が normal complement。

## 参照

- 親 issue: [0177](0177-bg-full-formalization.md)
- 実体: `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/ElemAbelianNeighbor.lean`
  (`typeP_structure`; docstring に本 issue の内容を明記済)
- 書籍: `references/bg/local-analysis.pdf` p. 106
