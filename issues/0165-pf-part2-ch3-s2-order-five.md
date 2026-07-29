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


## 追加進捗 + 残作業の設計 (2026-07-29 第 2 セッション)

### landing 済 (追加分)

| 定理 | 内容 |
|---|---|
| `eq_of_mul_eq_mul_of_mem_Q_mem_D` | `H = Q ⋊ D` 分解の一意性 |
| `structureConjugator_mul_conj_inv_{mem,ne_one}` | `rr^{-k} ∈ Q ∖ {1}` |
| `exists_mem_KSet_conj_distinguishedInvolution` | `ℓ` の存在 (`ℓ ≠ 1` 込み) |
| `exists_tConjMiddle_eq` | `h(rr^{-k}) = ℓ²k²` |
| `tConjMiddle_conj_mem_K` | `h(x) ∈ K` が `K`-軌道に沿って伝播 |
| `tConjMiddle_*_mem_K` (4 種) | 代表系の各元で `h ∈ K` |
| `orbitReprSet` + `tConjMiddle_mem_K_of_orbitReprSet_covers` | 代表系を集合化し、**「覆う」ことだけを残ギャップに切り出した** |
| `FreeActionOrbitCount.exists_mem_orbit_of_card_mul_eq` | 自由作用 + `\|R\|·\|Γ\| = \|S\|` ⟹ `R` は全軌道に当たる (汎用) |

⚠ 書籍が `rr^{-k} ≠ 1` に使う議論は不要だった — `C_Q(k) = 1` で直接。

### 残ギャップ = `hcover` (`orbitReprSet` が全 `K`-軌道に当たる) だけ

`exists_mem_orbit_of_card_mul_eq` に流すには **(A) `\|orbitReprSet\| = q+1`** と
**(B) 互いに非共役** が要る。実際に必要な補題を書き下すと:

**(A) 濃度** (`\|K\| = q−1` なので `3 + (q−2) = q+1`)
* `k ↦ r r^{-k}` は `K` 上単射 — `r r^{-k₁} = r r^{-k₂}` ⟹ `k₂k₁⁻¹` が `r` を中心化
  ⟹ `C_Q(·) = 1` で `k₁ = k₂`。**自由作用だけで済む**。
* `r r^{-k} ∉ Q₀` (`k ≠ 1`) — 書籍どおり: `r r^{-k} = z ∈ Q₀` なら `z` は `Q` の中心元で
  `z² = 1` ゆえ `(r^k)² = (zr)² = r²`、すなわち `k` が `r² ≠ 1` を中心化 ⟹ `k = 1`。
  ⟹ `≠ s`。(`r² ≠ 1` は landing 済)
* `r r^{-k} ≠ r` は `r ≠ 1` から即。`r r^{-k} ≠ r⁻¹` は位数 (4 vs 2) で、**`r⁴ = 1` が要る**。
* `s ≠ r`, `s ≠ r⁻¹`, `r ≠ r⁻¹` はすべて `r² ≠ 1` から。

**(B) 非共役**
* `r`, `r⁻¹`: `r⁻¹ = r^a` (`a ∈ K`) なら `a` の位数 `n` は奇で
  `r = r^{aⁿ} = r^{(−1)ⁿ} = r⁻¹` ⟹ `r² = 1`。**書籍の「`\|K\|` は奇」がここ**。
* `s` と `r r^{-k}`: `Q₀` は `K`-不変で `s ∈ Q₀`, `r r^{-k} ∉ Q₀`。
* `r`/`r⁻¹` と `r r^{-k}`: (1) より `f(r^a) = a f(r) a⁻¹ = a s a⁻¹ ∈ Q₀`、一方
  `f(rr^{-k})` は書籍によれば `(r r^{-kℓ})^{ℓ⁻¹k⁻²}` で位数 4 ⟹ `∉ Q₀`。
  ⚠ この同一視には `K` の可換性 (cyclic) が要る。
* **`r r^{-k₁}` 同士** — p.119 の体同一視 (5)(6)(7)。ここが最大の残作業。

### 先に要る補助事実

* **`r⁴ = 1`**: case (b) は type A の Suzuki 2-群で `Z(Q) = Ω₁(Q) = Q₀`,
  `Q/Z(Q)` 基本可換 ⟹ `r² ∈ Q₀` ⟹ `r⁴ = 1`。repo で type A についてこれが
  出ているか要実測 (`ActualCenter.lean` / `TypeBFromW.lean` / `Higman` 側)。
* **`|Q| = |Q₀|²`**: case (b) は `natCard_Q_eq_sq_or_cube` の sq 側。
* **`K` の `Q^#` への自由な共役作用を `MulAction` として据える** (
  `exists_mem_orbit_of_card_mul_eq` の適用形)。


## 🎯 非共役性の設計が確定 — 書籍の位数論法を `Q₀`-所属テストで置換 (2026-07-29)

書籍 p.118 は `r` と `f(rr^{-k})` の**位数 4** で代表系を分離するが、
**「`Q₀` に属すか」で判定する方が短く、必要な入力は `r² ≠ 1` だけ**
(`r⁴ = 1` = Suzuki 2-群の指数 4 は**要らない**)。

### landing 済 (この設計の基礎)

| 定理 | 内容 |
|---|---|
| `structureConjugator_notMem_Q0` | `r ∉ Q₀` (`Q₀` の元は 2 乗 1) |
| `structureConjugator_mul_conj_inv_notMem_Q0` | **`rr^{-k} ∉ Q₀`** (`k ≠ 1`) — `z ∈ Q₀` は `Q` の中心的 involution ゆえ `(r²)^k = (zr)² = r²`、`C_Q(k) = 1` で `r² = 1` に矛盾 |
| `structureConjugator_mul_conj_inv_injective` | `k ↦ rr^{-k}` は単射 (自由作用のみ) |

### 残る分離 (すべて設計済)

| 対 | 方法 | 状態 |
|---|---|---|
| `s` vs `r` / `r⁻¹` / `rr^{-k}` | `Q₀` は `K`-不変、`s ∈ Q₀`、他は `∉ Q₀` | 補題 `conj_mem_Q0_of_mem_KSet` を書くだけ |
| `r` vs `r⁻¹` | `r⁻¹ = r^a` なら `a` の位数 `n` が奇 ⟹ `r = r^{aⁿ} = r^{(−1)ⁿ} = r⁻¹` ⟹ `r² = 1` | 反復の帰納 (~25 行) |
| `r` vs `rr^{-k}` | (1) より `f(r^a) = a s a⁻¹ ∈ Q₀`、一方 **`f(rr^{-k}) = k (r r^{-(kℓ)⁻¹})⁻¹ k⁻¹ ∉ Q₀`** | (4) の `f` 成分を export すれば従う |
| `r⁻¹` vs `rr^{-k}` | 同様に `g(r⁻¹) = s ∈ Q₀`、`g(rr^{-k}) = r r^{-ℓ⁻¹} ∉ Q₀` (`ℓ ≠ 1` は landing 済) | `g` 成分を export すれば従う |
| `rr^{-k₁}` vs `rr^{-k₂}` | **p.119 の体同一視 (5)(6)(7)** | ← 唯一の実質的残作業 |
| `rr^{-k} ≠ r⁻¹` (濃度用) | `k⁻¹r⁻¹k = r⁻²` は位数を保たない (`orderOf r` は 2 冪、`r² ≠ 1`) | 短い |

⚠ `f(rr^{-k}) = k (r r^{-(kℓ)⁻¹})⁻¹ k⁻¹` の導出 (可換性不要):
(4) の `f = (k²ℓ) r (k²ℓ)⁻¹ · k r⁻¹ k⁻¹` を `k` で戻すと `w r w⁻¹ · r⁻¹` (`w = kℓ`)、
これは `(r · w r⁻¹ w⁻¹)⁻¹ = (r r^{-w⁻¹})⁻¹`。`kℓ ≠ 1` は `f ≠ 1` から。
⟹ **(4) の三成分すべてを export する補題**を足すのが次の一手。


## 進捗 (2026-07-29 第 2 セッション末)

**非共役性は 1 対を残して全部 landing**:

| 対 | 定理 | 状態 |
|---|---|---|
| `s` vs `r` / `r⁻¹` / `rr^{-k}` | `conj_distinguishedInvolution_mem_Q0` + `..._ne_structureConjugator_mul_conj_inv` | ✅ |
| `r` vs `r⁻¹` | `structureConjugator_not_conj_inv` (`|K|` 奇の反復) | ✅ |
| `r` vs `rr^{-k}` | `conj_structureConjugator_ne_mul_conj_inv` (`f` + `Q₀`) | ✅ |
| `r⁻¹` vs `rr^{-k}` | `conj_structureConjugator_inv_ne_mul_conj_inv` (`g` + `Q₀`) | ✅ |
| **`rr^{-k₁}` vs `rr^{-k₂}`** | p.119 の体同一視 (5)(6)(7) | ❌ **唯一の残り** |

補助として `exists_tConjTriple_eq` (三成分の export)、`conj_mem_Q0_of_mem_KSet`、
`tConjLeft/tConjRight_..._notMem_Q0` も landing 済。

### 次セッションの入口 (順に)

1. **`rr^{-k} ≠ r⁻¹`** (濃度用): `k⁻¹r⁻¹k = r⁻²` は位数を保たない
   (`orderOf r` は 2 冪で `r² ≠ 1` ⟹ `orderOf (r²) = orderOf r / 2`)。
2. **`|orbitReprSet| = q + 1`**: 上の distinctness 群 + `structureConjugator_mul_conj_inv_injective`。
3. **p.119**: `S/Q₀ ≅ 𝔽_q`, `K ≅ 𝔽_q^×` の同一視 (`exists_field_realization_K` が使える) の下で
   `α : S → 𝔽_q` を通し、(1)+(4) から (5) `1+k₂ = a(1+k₁)`, (6) `ℓ₂k₂ = aℓ₁k₁`,
   (7) `ℓ₂⁻¹k₂⁻² + k₂⁻¹ = a⁻¹(ℓ₁⁻¹k₁⁻² + k₁⁻¹)` を得る。
   `x_i = ℓ_i⁻¹(k_i⁻¹+1)`, `y_i = k_i⁻¹+ℓ_i` として (5)/(6) と (6)·(7) から
   `x₁ = x₂`, `y₁ = y₂`、`(x_i+1)k_i⁻¹ = x_i y_i + 1` で `x_i ≠ 1` なら `k₁ = k₂`。
   `x_i ≠ 1` は「`α(fg) = 0` ⟹ `fg ∈ Q₀` かつ `(t rr^{-k} t)² = g t (fg)^h t f`、
   `t(fg)^h t ∈ I ∩ (G−H)` と `fg ∈ I ∩ H` の involution 積が involution」で矛盾。
4. `exists_mem_orbit_of_card_mul_eq` に流して `hcover` ⟹ §2 Proposition 完成。


## 数え上げの足場が landing + 不変量による一括分離のアイデア (2026-07-29)

新 leaf **`StructureOfH/OrderFiveOrbits.lean`**:

* `OrbitReprIndex := Fin 3 ⊕ {k : ↥K // k ≠ 1}` / `orbitRepVal` (書籍の代表族)
* `orbitRepVal_{mem_Q, ne_one, mem_orbitReprSet}` / `card_K_ne_one`
* **`card_orbitReprIndex_mul_card_K_succ`** — `|ι|·|K| + 1 = |Q|`
  (case (b) の `|Q| = q²` と `|K| = q−1` から `(q+1)(q−1)+1 = q²`)

`GroupTheory/FreeActionOrbitCount.lean` に汎用判定を 2 本:
* `exists_mem_orbit_of_card_mul_succ_eq` — **不動点 1 個 + それ以外自由**版
  (`Option (ι × Γ) → S` が単射 ⟹ 全射)。`K` の `Q` への共役作用そのものの形。
* `exists_mem_orbit_of_card_mul_eq_index` — 添字版 (不動点なし)

### 残る `hrep` (代表が互いに非共役) を**不変量 1 本**で処理する設計

`y ∈ Q^#` に対し 3 つの `K`-軌道不変量 `(y ∈ Q₀, g(y) ∈ Q₀, f(y) ∈ Q₀)` を取る
(`Q₀` は `K`-不変、`f`,`g` は (1) で同変)。値は

| 代表 | `y ∈ Q₀` | `g(y) ∈ Q₀` | `f(y) ∈ Q₀` |
|---|---|---|---|
| `s` | ✓ | — | — |
| `r` | ✗ | ✗ (`g(r) = r`) | ✓ (`f(r) = s`) |
| `r⁻¹` | ✗ | ✓ (`g(r⁻¹) = s`) | ✗ (`f(r⁻¹) = r⁻¹`) |
| `rr^{-k}` | ✗ | ✗ | ✗ |

**4 つの値がすべて異なる** ので、族間の非共役は 16 通りの場合分けでなく
この不変量の比較 1 本で済む。族内 (`rr^{-k₁}` vs `rr^{-k₂}`) だけが p.119。

⟹ 次の一手: `orbitReprSet_covers` を
`exists_mem_orbit_of_card_mul_succ_eq` + 上の不変量 + p.119 を仮説にして組む。


## `orbitRepVal_pairwise` が landing — 残りは p.119 と最終組み立てのみ (2026-07-29)

`OrderFiveOrbits.lean`:

* `structureConjugator_inv_notMem_Q0` / `not_conj_distinguishedInvolution_of_notMem_Q0` /
  `not_conj_of_notMem_Q0_distinguishedInvolution`
* **`orbitRepVal_pairwise`** — 代表族が互いに `K`-非共役 (16 場合を
  `fin_cases` で列挙し、既存の 4 本の分離補題と `Q₀` テストで消化)。
  **仮説は `hpair` (`rr^{-k₁}` 同士、p.119) だけ**。

### 残り 2 点

1. **p.119** = `hpair`:
   `a⁻¹ (r r^{-k₁}) a = r r^{-k₂}` (`a, k₁, k₂ ∈ K^#`) ⟹ `k₁ = k₂`。
   `exists_field_realization_K` で `S/Q₀ ≅ 𝔽_q`, `K ≅ 𝔽_q^×` に落とし、(1)+(4) から
   (5)(6)(7) を出す。`x_i ≠ 1` の背理法で `fg ∈ Q₀` と involution 積の矛盾。
2. **最終組み立て** (短い):
   `letI : MulAction ↥K ↥Q := MulAction.compHom _ hyp.conjQByK` を据えて
   `exists_mem_orbit_of_card_mul_succ_eq` に
   `rep := fun i => ⟨orbitRepVal i, orbitRepVal_mem_Q i⟩`, `e := 1`,
   `hfree := conjQByK_fixed_eq_one`, `hrepne := orbitRepVal_ne_one`,
   `hrep := orbitRepVal_pairwise`, `hcard := card_orbitReprIndex_mul_card_K_succ`
   を渡し、`tConjMiddle_mem_K_of_orbitReprSet_covers` に接続
   (`orbitRepVal_mem_orbitReprSet` が橋渡し)。
