---
id: 1048
slug: pf-10-11-typeii-second-assertion
title: "(10.11) 第 2 主張 (型 II の H 構造 + 𝒮 coherent) を形式化"
created: 2026-07-20
---

# (10.11) 第 2 主張 (型 II の H 構造 + 𝒮 coherent) を形式化

## 書籍 (PDF p.63 = 章 PDF p.6 で確定, 2026-07-20)

> **(10.11)** Suppose that case (b) of Theorem (8.8) holds. Then `|W₁|` and `|W₂|` are prime.
> **If `M` is a maximal subgroup of `G` of Type II, then, in the notation of Hypotheses (9.2)
> and (9.5), `H` is an elementary abelian group of order `p^q`, where `p = |W₂|`, and the set
> `𝒮` of Hypothesis (9.5) is coherent.**
>
> *Proof.* The first assertion follows from (8.6.a) and Theorem (10.10). Suppose that `M` is of
> Type II. By (9.3), `|H| = p^q`, where `p = |W₂|`. As `p` is prime, (9.4) and (9.6) then show
> that `H₀ = 1` and that `H` is elementary abelian. Since `M` is of Type II, `U` is abelian and
> so `C′ = 1` and `𝒮(H₀C′) = 𝒮`. Thus, **by (9.11)**, `𝒮` is coherent.

⚠ **`pdftotext` は §10 章で文字バラけして使用不能** (§9 と同じ症状)。原文は PDF 画像で読むこと。

## repo の現状 (2026-07-20 実測)

- **第 1 主張は完了**: `S12.theorem88_caseB_prime_orders` (S12_MaximalIII_IV_V.lean:1673)。
- **第 2 主張は未形式化**。⚠ frontier note の「type-II 残余は §15 の S/T pair instance のみ」は
  **stale** — 本 session で `S11.typeII_nineEleven_coherent` が landed したので、(9.2)/(9.5) の
  記法のまま直接述べられるようになった (§15 経由である必要がなくなった)。

## 部品はすべて在る (実測済)

| 書籍のステップ | repo |
|---|---|
| (9.3) 型 II で `\|H\| = \|W₂\|^q` | `S11.typeII_III_IV_order_relations` の第 1 連言肢 (WielandtSetup.lean:633) |
| (9.6) `\|H̄\| = p^q` | `S11.chiefFactor_quotient_card` / `chiefFactor_basic` (CliffordData.lean:409) |
| (9.4) `\|H\| = p^q·\|H₀\|` | `ChiefFactorData.quotient_order` |
| `\|W₂\|` 素 | (10.11) 第 1 主張 `theorem88_caseB_prime_orders`、または型 II 側の (8.6.a) |
| 型 II ⟹ `U` abelian | `TypeIIData.U_commutative` |
| `C ≤ U` | `S11.cSub_le_U` |
| (9.11) 型 II | ⭐ `S11.typeII_nineEleven_coherent` (本 session) |

## 着手順

1. **`H₀ = 1`**: `\|W₂\|^q = \|H\| = chief.p^q · \|H₀\|` に一意分解を当てる —
   `\|W₂\| = r` 素・`chief.p = p` 素なら `p^q ∣ r^q ⟹ p = r`、ゆえに `\|H₀\| = 1`。
   併せて `chief.p = \|W₂\|` (型 II 版の `typeIII_IV_p_eq_W2` 相当) が出る。
2. **`H` elementary abelian of order `p^q`**: `H₀ = 1` から `H ≅ H/H₀` で
   `ChiefFactorData.quotient_elementaryAbelian` を移す。
3. **`C′ = 1`**: 型 II の `U` abelian + `cSub_le_U` ⟹ `cprimeSub data chief = ⊥`。
4. **`𝒮(H₀C′) = 𝒮`**: `sOf data (⊥ ⊔ ⊥) = sSet data` (`sOf`/`sSet` の定義から。既存補題があるか要確認)。
5. **coherence**: `S11.typeII_nineEleven_coherent` を 1-4 で書き換えて `𝒮` の coherence に。

⚠ 5 の入力 ((8.15)/(4.6) の Dade データ `h46`/`dd`/`hdd` + pin) は型 III/IV 経路と同じくパラメータ。
書籍もそこは Hypothesis (9.5) の standing hypothesis なので忠実。

## 完了条件

(10.11) 第 2 主張が Hypotheses (9.2)/(9.5) の記法で述べられ、axiom-clean で landing。
frontier note の §10 行と「推奨着手順 8」を訂正する。

## 参照

- 書籍 PDF `references/peterfalvi/pdf/04.12_pp_58_63_*.pdf` p.6 (= 書籍 p.63)
- `issues/closed/1045-pf-9-11-section9-level.md` ((9.11) §9 化 + 型 II instance)
- `notes/peterfalvi/frontier_measured_2026_07_19.md` §10 行 (要訂正)
