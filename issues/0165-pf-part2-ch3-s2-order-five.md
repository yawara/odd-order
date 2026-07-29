---
id: 165
slug: pf-part2-ch3-s2-order-five
title: "Peterfalvi Part II, Ch. III §2: (SK) ∪ (SKtS) は G の部分群 (case (b), st の位数 5)"
created: 2026-07-29
---

# Peterfalvi Part II, Ch. III §2: (SK) ∪ (SKtS) は G の部分群 (case (b), st の位数 5)

## 背景

[issue 0163](closed/0163-pf-part2-ch3-s1-trichotomy.md) / [0164](closed/0164-psu3-sylow-normalizer-centralizer.md)
で Ch. III §1 の Proposition が**仮説ゼロ**で landing した (`SecondCaseHypothesis.trichotomy`)。
文書順で次は **Ch. III §2 (p. 118–119)**。

> **Proposition.** If case (b) of the proposition of §1 holds, then `(SK) ∪ (SKtS)`
> is a subgroup of `G`.

case (b) = 「`S` は type A の Suzuki 2-群、`st` の位数 5、`W = 1`」。
Theorem C の後 `S = Q` (`sylowTwoOfQ_eq_Q`)。

正本ページ = `references/peterfalvi/pages/peterfalvi-p{118,119}.png`
(text は数式が壊れているのでページ画像で確定した)。

## 書籍の証明の構造

`tSt ⊆ SKtS` を示せば十分。`x ∈ S^#` に対し `txt ∉ H ∪ (Ht) ∪ (tH)` なので
Ch. I §1 Prop 4(a) (canonical form, repo = `existsUnique_canonicalForm`) から

  `t x t = g(x) · h(x) · t · f(x)`,  `f(x), g(x) ∈ S^#`, `h(x) ∈ D`

が一意に決まる。示すべきは **`h(x) ∈ K` (∀ x ∈ S^#)**。

1. **(1) `K`-同変性**: `a ∈ K` に対し `t x^a t = a t x t a⁻¹` (`t` は `K` を反転) を
   canonical form に直して
   `f(x^a) = f(x)^{a⁻¹}`, `g(x^a) = g(x)^{a⁻¹}`, `h(x^a) = a h(x) a`。
   ⟹ `K`-軌道の代表系だけ見ればよい。
   repo: `canonicalForm_conj_eq` (`DistinguishedInvolution.lean:159`) がこの形の核。
2. **(2)(3) 構造方程式**: `tst = r⁻¹ t r` (`structure_equation`)。`st` の位数 5 から
   `r` の位数は 4。`trt = rts`, `t r⁻¹ t = s t r⁻¹`。
   ⟹ `h(s) = h(r) = h(r⁻¹) = 1`。
3. **(4) 主計算**: `k ∈ K^#`, `ℓ ∈ K` を `s k s k⁻¹ = s^ℓ` (= `ℓ⁻¹ s^k ℓ`?) で定めると
   `t (r r^{-k}) t = r r^{-ℓ⁻¹} ℓ² k² t r^{ℓ⁻¹k⁻²} r^{-k⁻¹}` となり
   `f(rr^{-k}) = r^{ℓ⁻¹k⁻²} r^{-k⁻¹}`, `g(rr^{-k}) = r r^{-ℓ⁻¹}`,
   **`h(rr^{-k}) = ℓ² k² ∈ K`**。
4. **軌道代表系**: `s, r, r⁻¹, {r r^{-k} : k ∈ K^#}` が `S^#` の `K`-軌道の代表系。
   個数は `|S^#|/|K| = q + 1 = |K^#| + 3`。⟹ 「互いに `K`-共役でない」だけ示せばよい。
   - `r` の位数 4 と `|K|` 奇 ⟹ `s, r, r⁻¹` は相異なる軌道。
   - `k ∈ K^#` で `r r^{-k} = z ∈ Q₀` なら `(r²)^k = (r^k)² = (rz)² = r²` で矛盾
     ⟹ `r r^{-k}` の位数は 4 ⟹ `s` と非共役。
   - `f(rr^{-k})`, `g(rr^{-k})` の位数 4 ⟹ (1)(3) から `r`, `r⁻¹` と非共役。
   - **`rr^{-k₁}` 同士が非共役** (p.119): `S/Q₀ ≅ 𝔽_q`, `K ≅ 𝔽_q^×` の同一視
     (Appendix I Prop 2 — repo は `exists_field_semilinear_with_scalar` /
     **`exists_field_realization_K`** (0164 で新設) が使える) の下で `α : S → 𝔽_q`
     を通し (5)(6)(7) を得て `x_i = ℓ_i⁻¹(k_i⁻¹+1)`, `y_i = k_i⁻¹ + ℓ_i` が一致、
     `(x_i+1)k_i⁻¹ = x_i y_i + 1` から `x_i ≠ 1` なら `k₁ = k₂`。
     `x_i ≠ 1` (= `ℓ⁻¹(k⁻¹+1) ≠ 1`) は背理法: `α(f g) = 0` ⟹ `fg ∈ Q₀` かつ
     `(t r r^{-k} t)² = g t (fg)^h t f` で `t(fg)^h t ∈ I ∩ (G−H)`, `fg ∈ I ∩ H` の
     involution 積が involution になり矛盾。

## repo 側の既存部品 (2026-07-29 実測)

| 必要なもの | 所在 |
|---|---|
| canonical form `g = x t y` の存在・一意 | `CanonicalForm.lean` `exists_canonicalForm` / `canonicalForm_unique` / `existsUnique_canonicalForm` |
| `t` が `K` を反転 (`tkt = k⁻¹`) | `Basic.lean` `KSet` 定義 + `DistinguishedInvolution.lean` `t_conj_eq_inv_of_mem_KSet` / `mul_t_eq_of_mem_KSet` / `t_mul_eq_of_mem_KSet` |
| canonical form の `K`-共役 | `DistinguishedInvolution.lean` `canonicalForm_conj_eq` |
| 構造方程式 `tst = r⁻¹tr` + 一意性 | `DistinguishedInvolution.lean` `structure_equation` / `eq_distinguishedPair_of_structure` |
| `t` が `D` を正規化 | `Basic.lean:384` (`D.map (MulAut.conj t) = D`) |
| `H = Q ⋊ D` 分解 | `Basic.lean` `Q_mul_D_eq_H` / `Q_inf_D_eq_bot` |
| `S = Q` (Theorem C 後) | `Trichotomy.lean` `sylowTwoOfQ_eq_Q`, `isPGroup_two_Q` |
| `K` は `Q₀^#` 上正則 / `S/Q₀` 上正則 | `KCyclic.lean` `conjQ0bar_transitive`, `ActualKActor.lean` |
| `𝔽_q` 同一視 (Appendix I Prop 2) | `StructureOfH/FieldRealizationK.lean` `exists_field_realization_K` |
| `st` の位数 5 (case (b)) | `Trichotomy.lean` (`orderOf_st_eq_five_of_isSuzuki2Group`) |

## やること

- [x] `txt ∉ H ∪ Ht` (`x ∈ Q^#`)
- [x] `f, g : Q^# → Q^#`, `h : Q^# → D` の定義と一意性 (canonical form + `H = Q ⋊ D`)
- [x] (1) の `K`-同変性
- [x] (3) `trt = rts` / `tr⁻¹t = str⁻¹` と `h(s)=h(r)=h(r⁻¹)=1`
- [x] `r² ≠ 1` (`st` 位数 5 から)
- [x] (4) の主計算 ⟹ `h(rr^{-k}) = ℓ²k² ∈ K`
- [ ] `ℓ` の存在 (`K` は `Q₀^#` 上正則) と `rr^{-k} ∈ Q^#`
- [ ] `r` の位数がちょうど 4 (Suzuki 2-群は指数 4)
- [ ] 軌道代表系の非共役性 (前半 3 件)
- [ ] p.119 の `rr^{-k₁}` 同士の非共役性 (体同一視 + involution の矛盾)
- [ ] `(SK) ∪ (SKtS)` が部分群

## 進捗 (2026-07-29)

新 leaf **`StructureOfH/TConjugateTriple.lean`** (sorry ゼロ、AxiomsCheck 登録済):

| 定理 | 内容 |
|---|---|
| `t_conj_notMem_H_of_mem_Q` / `t_conj_notMem_mul_t` | `txt ∉ H`, `txt ∉ Ht` |
| `existsUnique_tConjTriple` | `txt = g·h·t·f` の存在・一意 |
| `tConjLeft` / `tConjMiddle` / `tConjRight` (+ `tConjTriple_spec`, `tConjTriple_eq_of`) | 書籍の `g` / `h` / `f` |
| `tConjTriple_conj` | **(1)** `f(xᵃ)=f(x)^{a⁻¹}`, `g(xᵃ)=g(x)^{a⁻¹}`, `h(xᵃ)=a h(x) a` |
| `t_conj_mul` | `t` 共役の乗法性 (汎用) |
| `structureConjugator_ne_one` | `r ≠ 1` |
| `t_conj_structureConjugator{,_inv}` | **(3)** `trt = rts`, `tr⁻¹t = str⁻¹` |
| `tConjTriple_{distinguishedInvolution,structureConjugator,structureConjugator_inv}` | `h(s)=h(r)=h(r⁻¹)=1` |
| `sq_st_eq_conj_structureConjugator` | `(st)² = (st)^r` |
| `structureConjugator_sq_ne_one` | `orderOf (st) = 5 ⟹ r² ≠ 1` |
| **`t_conj_structureConjugator_mul_conj_inv`** | **(4)** 主計算 (`h(rr^{-k}) = ℓ²k²`) |

⚠ (4) の証明で `k`, `ℓ` の可換性は**不要**だった (両辺とも
`r ℓ r⁻¹ · t · r ℓ⁻¹ k⁻¹ r⁻¹ k⁻¹` に正規化される)。

### 次の一手

1. **`ℓ` の存在**: `k ∈ K^#` に対し `s·(ksk⁻¹) ∈ Q₀^#` なので `K` の `Q₀^#` 上の正則性
   (`KCyclic.lean` `conjQ0bar_transitive` / `ActualKActor.lean`) から一意な `ℓ ∈ K` で
   `sksk⁻¹ = ℓ⁻¹ s ℓ`。`K` (部分群) を使うので `KCyclic` の import が要る。
2. **`rr^{-k} ∈ Q ∖ {1}`**: `r ∈ Q`, `K ≤ D` は `Q` を正規化。`≠ 1` は
   「`r r^{-k} = z ∈ Q₀` なら `(r²)^k = (rz)² = r²` で `K` の自由作用に矛盾」(p.118)。
3. **`orderOf r = 4`**: `r² ≠ 1` + Suzuki 2-群の指数 4 (`Z(Q) = Ω₁(Q) = Q₀`,
   `Q/Z(Q)` 基本可換)。
4. 軌道代表系の非共役性 → 体同一視 (p.119) → 部分群。

## 完了条件

`case (b) ⟹ (SK) ∪ (SKtS) ≤ G` が sorry-free で landing、AxiomsCheck 登録。

## 参照

* p. 118–119 = `references/peterfalvi/pages/peterfalvi-p{118,119}.png`
* 上流 = [0163](closed/0163-pf-part2-ch3-s1-trichotomy.md) / [0164](closed/0164-psu3-sylow-normalizer-centralizer.md)
* 下流 = Ch. III §3 (p. 119–121, `KW` の `S` への作用) — case (a)/(b) が
  片付くと (C2) が残り、そこから PSU(3,q) の特徴付け (Ch. IV) へ
