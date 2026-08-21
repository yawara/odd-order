---
id: 166
slug: pf-part2-ch3-s3-case-ab-conclusion
title: "Peterfalvi Part II, Ch. III §3 冒頭: case (a)/(b) から Theorem A の結論 (G₀ ⊴ G)"
created: 2026-07-29
---

# Peterfalvi Part II, Ch. III §3 冒頭: case (a)/(b) から Theorem A の結論

## 背景

[issue 0165](0165-pf-part2-ch3-s2-order-five.md) で Ch. III §2 の Proposition
(`case (b) ⟹ (SK) ∪ (SKtS) ≤ G`, repo = `Hypothesis.typeASubgroup`) が landing した。
文書順で次は **Ch. III §3 (pp. 119–121)**。その冒頭段落が §2 の成果を消費する:

> Assume that case (a) or (b) of the proposition in §1 holds. Then
> `G₀ = (SK) ∪ (SKtS)` is a subgroup of `G` (§2 and Chapter I, §3, Lemma 4).
> Also, `G = H ∪ (HtS) = ⟨G₀, V⟩` and `V` normalizes `S`, `K` and `t` whence
> `G₀ ⊴ G` and `|G/G₀| = |V|`. The conclusion of Theorem A now follows from
> Chapter I, §3, Proposition 2. Therefore, we assume henceforth that
>
> **(C2)** `S` is a Suzuki 2-group of type B, `st` has order 3 and `W ≠ 1`.

つまりこの段落は **case (a) と case (b) を消して (C2) に絞る**。これが済むと
§3 本体 (pp. 119–121 の Proposition = `S₁ ⋊ K₁W₁` モデル) に入れる。

正本ページ = `references/peterfalvi/pages/peterfalvi-p{119,120,121}.png`。

## repo 側の既存部品 (2026-07-29 実測)

| 必要なもの | 所在 |
|---|---|
| 担体 `(SK) ∪ (SKtS)` | `StructureOfH/OrderFiveSubgroup.lean` `orderFiveCarrier` |
| case (b) の部分群 | `StructureOfH/CaseBStructure.lean` `typeASubgroup` (0165) |
| case (a) の部分群 | `OrderThreePSL.lean` `orderThreeGeneratedSubgroup` + `coe_orderThreeGeneratedSubgroup_eq_Q0K_union_Q0KtQ0` (Ch. I §3 Lemma 4) |
| case (a) は `Q = Q₀` | `WNeBot.trichotomy` の第 1 枝 (`Q_eq_Q0_and_orderOf_st_of_commute`) |
| `G = H ∪ H t Q` | `CanonicalForm.lean` `exists_canonicalForm` |
| `H = Q · D` | `Basic.lean` `Q_mul_D_eq_H` |
| **`D = V ⊔ K`** | `StructureOfH/LinearCharacter.lean` `V_sup_K_eq_D`, `card_D_eq` |
| `K ⊓ V = ⊥` | `KCyclic.lean` `K_inf_V_eq_bot` / `CentralizerNormalizer.lean` `V_inf_K_eq_bot` |
| `V` は `t` を中心化 | `Basic.lean` `commute_t_of_mem_V` |
| `V ≤ D` は `Q`, `K` を正規化 | `Q_normal_in_H` / `conj_mem_K_of_mem_D` |
| `Q ⊓ D = ⊥`, `t ∉ H` | `Basic.lean` `Q_inf_D_eq_bot`, `t_not_mem_H` |
| **Ch. I §3 Prop 2** | `InductionNonSimple.lean` `theoremAConclusion_of_not_simple (hG : ¬ IsSimpleGroup G) (ind)` |
| `V ≠ ⊥` (case (a)/(b) 側) | `SecondCaseHypothesis.V_ne_bot` |

## 設計 (紙で確認済)

担体だけで書けるので **case (a)/(b) を区別せず** 1 本にまとめる:

```
theorem theoremAConclusion_of_orderFiveCarrier_subgroup
    (G₀ : Subgroup G) (hG₀ : (G₀ : Set G) = hyp.orderFiveCarrier)
    (hV : hyp.V ≠ ⊥) (ind : TheoremAInductionBelow G Ω) :
    Nonempty (TheoremAConclusion G Ω)
```

証明の段:

1. **`Q ≤ G₀`, `K ≤ G₀`, `t ∈ G₀`** — 担体の 2 セルから即 (`q = q·1`, `k = 1·k`,
   `t = 1·1·t·1`)。
2. **`G₀ ⊔ V = ⊤`** — `H = Q·D` と `D = V ⊔ K` から `H ≤ G₀ ⊔ V`、
   `g ∉ H` は `exists_canonicalForm` で `x t y` (`x ∈ H`, `y ∈ Q`)。
3. **`V` が担体を正規化** — `v q v⁻¹ ∈ Q`, `v k v⁻¹ ∈ K`, `v t v⁻¹ = t`。
4. **`G₀ ⊴ G`** — 正規化群が `G₀ ⊔ V = ⊤` を含む。
5. **`G₀ ⊓ V = ⊥`** — `v ∈ V ≤ D` が `q k` なら `q = v k⁻¹ ∈ Q ⊓ D = ⊥` で `v = k ∈ K ⊓ V = ⊥`。
   右セルは `t ∉ H` から `H` と交わらない。⟹ `V ≠ ⊥` と合わせて **`G₀ ≠ ⊤`**。
6. `Q ≠ ⊥` (∵ `2 ≤ |Q₀|`) から `G₀ ≠ ⊥`。⟹ `¬ IsSimpleGroup G`。
7. `theoremAConclusion_of_not_simple` に流す。

`|G/G₀| = |V|` (= `G = G₀V` と `G₀ ⊓ V = ⊥`) は結論には不要だが、書籍の主張なので
安く出るなら添える。

## やること

- [ ] 新 leaf `StructureOfH/CaseABConclusion.lean`
- [ ] 上の 1–7
- [ ] case (a) 側の橋渡し (`Q = Q₀` のとき `orderThreeGeneratedSubgroup` の担体が
      `orderFiveCarrier` に一致)
- [ ] `SecondCaseHypothesis` レベルで「case (a) or (b) ⟹ TheoremAConclusion」
- [ ] AxiomsCheck 登録 + `OddOrder.lean` 配線

## 完了条件

`SecondCaseHypothesis` の trichotomy の case (a)/(b) から `Nonempty (TheoremAConclusion G Ω)`
が sorry-free で出る。以後 §3 本体は (C2) だけを仮定できる。

## 参照

* pp. 119–121 = `references/peterfalvi/pages/peterfalvi-p{119,120,121}.png`
* 上流 = [0165](0165-pf-part2-ch3-s2-order-five.md)
* 下流 = §3 本体 (`S₁ ⋊ K₁W₁` モデル, pp. 119–121) → Ch. IV (PSU(3,q) の特徴付け)

## 進捗 (2026-07-29)

新 leaf **`StructureOfH/CaseABConclusion.lean`** (sorry ゼロ):

| 定理 | 内容 |
|---|---|
| `mem_orderFiveCarrier_of_mem_{Q,K}` / `t_mem_orderFiveCarrier` | `Q`, `K`, `t` は担体に入る |
| `conj_mem_orderFiveCarrier_of_mem_V` | `V` が担体を正規化 |
| `H_le_orderFiveCarrier_sup_V` | `H = Q·D`, `D = V ⊔ K` から `H ≤ ⟨G₀, V⟩` |
| **`orderFiveCarrier_sup_V_eq_top`** | `G = ⟨G₀, V⟩` (`exists_canonicalForm`) |
| **`normal_of_orderFiveCarrier`** | `G₀ ⊴ G` |
| **`eq_one_of_mem_V_of_mem_orderFiveCarrier`** | `G₀ ∩ V = 1` |
| **`theoremAConclusion_of_orderFiveCarrier_subgroup`** | `V ≠ 1` ⟹ `¬ IsSimpleGroup G` ⟹ Theorem A の結論 |
| `theoremAConclusion_of_caseB` | case (b) 版 (`coe_typeASubgroup` 経由) |
| `coe_orderThreeGeneratedSubgroup_eq_orderFiveCarrier` | case (a) (`S = Q₀`) で Ch. I §3 Lemma 4 の担体が一致 |
| `theoremAConclusion_of_caseA` | case (a) 版 |

⚠ `|G/G₀| = |V|` は結論に不要なので未形式化 (`G₀ ⊓ V = ⊥` と `G₀ ⊔ V = ⊤` から出る)。

### ✅ trichotomy 配線も完了

`WNeBot.lean` の `trichotomy` の case (b) 枝に `Nat.card ↥Q = Nat.card ↥Q0 ^ 2` を
1 本足した (分岐条件 `natCard_Q_eq_sq_or_cube` の sq 側そのもので、証明側は `hsq` を渡すだけ)。
`trichotomy` にはまだコード上の消費者が無かったので影響なし。

**`SecondCaseHypothesis.theoremAConclusion_or_caseC2`** —

```
Nonempty (TheoremAConclusion G Ω) ∨ (IsTypeB ↥S ∧ orderOf (st) = 3 ∧ W ≠ ⊥)
```

⟹ **§3 本体以降は (C2) だけを仮定してよい**ことが形式化された。

## ✅ CLOSED (2026-07-29)

完了条件「trichotomy の case (a)/(b) から `Nonempty (TheoremAConclusion G Ω)` が
sorry-free で出る」を満たした (`SecondCaseHypothesis.theoremAConclusion_or_caseC2`)。
以後 §3 本体は (C2) だけを仮定できる。

次は **§3 本体** (pp. 119–121 の Proposition = `S ⋊ KW ≅ S₁ ⋊ K₁W₁` モデル)。
