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


## 🎯 §2 Proposition が p.119 の 1 点に完全還元 (2026-07-29)

`OrderFiveOrbits.lean`:

* `orbitReprSet_covers` — `exists_mem_orbit_of_card_mul_succ_eq` に
  `MulAction ↥K ↥Q := MulAction.compHom _ conjQByK` を据えて適用。
* **`tConjMiddle_mem_K`** — `∀ x ∈ Q^#, h(x) ∈ K`。
  仮説は `r² ≠ 1`、`|Q| = |Q₀|²`、および `hpair` (p.119) の 3 つだけ。

⟹ **§2 Proposition の内容はこれで尽きる** (`txt = g(x)h(x)t f(x)` で `h(x) ∈ K` が
`tSt ⊆ SKtS`)。残るのは:

* **`hpair`** = p.119 の体計算 (`a⁻¹ (rr^{-k₁}) a = rr^{-k₂} ⟹ k₁ = k₂`)
* `(SK) ∪ (SKtS)` が実際に部分群であることの組み立て (`tSt ⊆ SKtS` からの一般論)
* case (b) から `r² ≠ 1` (= `structureConjugator_sq_ne_one` + `orderOf_st_eq_five_of_isSuzuki2Group`)
  と `|Q| = |Q₀|²` (= `natCard_Q_eq_sq_or_cube` の sq 側) を供給する配線

## 部分群性 `(SK) ∪ (SKtS) ≤ G` の閉包計算 (2026-07-29 に手で確認、未形式化)

`tConjMiddle_mem_K` (`txt = g·h·t·f`, `h ∈ K`) から `G₀ = SK ∪ SKtS` の閉包が出る。
`S = Q` (Theorem C)、`K ≤ D` は `Q` を正規化、`t` は `K` を反転 (`tkt = k⁻¹`)。
以下 `q, q', q₃ ∈ Q`, `k, k' ∈ K`。

* `(SK)(SK) ⊆ SK` — `SK` は部分群 (`K` が `Q` を正規化)。
* `(SK)(SKtS) ⊆ SKtS` — `q k q' k' = q (k q' k⁻¹)(k k') ∈ SK`。
* `(SKtS)(SK) ⊆ SKtS` — `q k t q₀ k' = q k (t k' t) t (k'⁻¹ q₀ k') = q (k k'⁻¹) t (k'⁻¹ q₀ k')`。
* `(SKtS)(SKtS) ⊆ SK ∪ SKtS` — 中央が `t q₂ k' t`。
  - `q₂ = 1`: `t k' t = k'⁻¹` ⟹ 全体は `q (k k'⁻¹) q₃ ∈ SK`。
  - `q₂ ≠ 1`: `t q₂ t = g h t f` (`h ∈ K`) ⟹ `t q₂ k' t = g h t f k'⁻¹`、
    かつ `t f k'⁻¹ q₃ = k' t (k' f k'⁻¹ q₃)` ⟹
    全体は `(q (k g k⁻¹) k) · (h k') · t · (k' f k'⁻¹ q₃) ∈ S K t S`。
* 逆元: `(q k t q')⁻¹ = q'⁻¹ (t k⁻¹ t) t q⁻¹ = q'⁻¹ k t q⁻¹ ∈ SKtS`。

⟹ 形式化は `Set` の積で書くか、`Subgroup.closure` で作って両包含を示す。~200 行の見込み。

## 現状まとめ (2026-07-29 セッション末)

`tConjMiddle_mem_K_of_orderOf_st_eq_five` まで landing。**§2 の残りは 2 点だけ**:

1. **`hpair` = p.119 の体計算** (本 issue の唯一の実質的数学的残作業)
2. `(SK) ∪ (SKtS)` が部分群であることの組み立て (上の閉包計算、機械的)

## ✅ 部分群性が landing — §2 の残りは p.119 の 1 点のみ (2026-07-29)

新 leaf `StructureOfH/OrderFiveSubgroup.lean`:

* `orderFiveCarrier` — 集合 `(SK) ∪ (SKtS)` (`S = Q`)
* **`orderFiveSubgroup`** — `h(x) ∈ K` (∀ x ∈ Q^#) を仮定して `Subgroup G` を構成
  (4 種の積 + 逆元をすべて明示的な witness で)
* `coe_orderFiveSubgroup`

⟹ **§2 Proposition の残りは `hpair` (p.119 の体計算) だけ**。
`hpair` が入れば `tConjMiddle_mem_K_of_orderOf_st_eq_five` → `orderFiveSubgroup` で完結する。

## p.119 (`hpair`) の完全な設計 (2026-07-29 に紙で検証)

### 必要な同一視

`S/Q₀` を `𝔽_q`、`K` を `𝔽_q^×` と同一視し、`K` の `S/Q₀` への作用が乗法になるようにする
(Appendix I Prop 2)。case (b) では `|S| = q²`, `|Q₀| = q` なので `|S/Q₀| = q`、
`K` は自由 (`C_Q(k) = 1` + coprime) で `|K| = q−1` ⟹ `(S/Q₀)^#` 上推移的 ⟹ 既約。
⟹ **`exists_field_realization_K` の `S/Q₀` 版**が要る (既存版は `Q₀` について)。
`α : S → 𝔽_q` を標準全射とし、`α(r) = 1` になるよう基底を取る (`r ∉ Q₀` ゆえ可能)。

⚠ `ℓ_i` も**この同一視で** `𝔽_q^×` の元と見る (書籍もそう扱っている)。
`ℓ` の定義 `s k s k⁻¹ = s^ℓ` は `Q₀` 側だが、(5)(6)(7) では `ℓ` は独立変数として扱われ、
`k` との関係は使われない。

### 3 本の関係式 (`a ∈ K`, `k₁, k₂ ∈ K^#`, `rr^{-k₂} = (rr^{-k₁})^a`)

* **(5)** `α` を `rr^{-k₂} = (rr^{-k₁})^a` に: `1 + k₂ = a(1 + k₁)`
  (`α(rr^{-k}) = α(r) + k·α(r⁻¹) = 1 + k`、標数 2 で `α(r⁻¹) = α(r)`)
* **(6)** `h(rr^{-k₂}) = a·h(rr^{-k₁})·a` に `μ : K ≅ 𝔽_q^×` を: `ℓ₂²k₂² = a²ℓ₁²k₁²`、
  標数 2 で 2 乗は単射ゆえ `ℓ₂k₂ = aℓ₁k₁`
* **(7)** `f(rr^{-k₂}) = a·f(rr^{-k₁})·a⁻¹` に `α` を:
  `ℓ₂⁻¹k₂⁻² + k₂⁻¹ = a⁻¹(ℓ₁⁻¹k₁⁻² + k₁⁻¹)`

### 体の代数 (紙で検証済)

`x_i := ℓ_i⁻¹(k_i⁻¹ + 1)`, `y_i := k_i⁻¹ + ℓ_i` とおくと

* (5)/(6) 辺々割って `x₁ = x₂` (∵ `(1+k)/(ℓk) = ℓ⁻¹(k⁻¹+1)`)
* (6)·(7) 辺々掛けて `y₁ = y₂` (∵ `ℓk(ℓ⁻¹k⁻² + k⁻¹) = k⁻¹ + ℓ`)
* **恒等式** `(x+1)k⁻¹ = xy + 1` — 標数 2 で展開して検算済:
  `xy = ℓ⁻¹k⁻² + k⁻¹ + ℓ⁻¹k⁻¹ + 1`, `(x+1)k⁻¹ = ℓ⁻¹k⁻² + ℓ⁻¹k⁻¹ + k⁻¹`
* ⟹ `(x+1)k₁⁻¹ = (x+1)k₂⁻¹`、`x ≠ 1` なら `k₁ = k₂` ∎

### `x ≠ 1` (`ℓ⁻¹(k⁻¹+1) ≠ 1`) の背理法

`x = 1` すなわち `ℓ = k⁻¹ + 1` と仮定。すると
`α(f(rr^{-k})·g(rr^{-k})) = ℓ⁻¹k⁻² + k⁻¹ + 1 + ℓ⁻¹ = (k⁻¹+1)(1 + ℓ⁻¹(k⁻¹+1)) = 0`
なので `fg ∈ Q₀`。一方 `rr^{-k}` は位数 4 なので `(t rr^{-k} t)² = g t (fg)^h t f ≠ 1`、
すなわち `fg ≠ 1` かつ `t(fg)^h t · fg` が involution。
しかし `t(fg)^h t ∈ I ∩ (G − H)` と `fg ∈ I ∩ H` なので矛盾
(`H` の involution と `G−H` の involution の積は involution になれない)。

### 形式化の順序 (見積り 500 行超・複数セッション)

1. `S/Q₀` の体実現 (`exists_field_realization_K` の `M := Q ⧸ Z(Q)` 版)。
   `HilbertNinetyOnQ.lean` の `U`/`M` 設定がそのまま使える。
2. `α` の加法性と `K`-同変性、`α(r) = 1` の正規化。
3. (5)(6)(7) の導出 (`tConjTriple_conj` (1) と `exists_tConjTriple_eq` (4) を `α`/`μ` で送る)。
4. 体の代数 (上の 3 段、`field_simp` + `ring` で行けるはず)。
5. `x ≠ 1` の involution 論法 (`t_mul_mul_t_notMem_H` 系が土台)。

## p.119 の第 1・2 段が landing (2026-07-29 セッション末)

`Appendices/SemilinearField.lean` (抽象・再利用可能):

* **`Huppert.exists_field_scalar_realization`** — 自由作用 + `|T| = |E| − 1` ⟹
  `E` は体 `F` (`|F| = |E|`) 上の直線、`T` はスカラー、`μ : T ≃* Fˣ` は全単射
* **`Huppert.exists_field_coordinate_realization`** — さらに基底を選んで
  **`α : Additive E ≃+ F`** を取り、`α (ψ t y) = μ t · α y` を得る
  (= p.119 の `α`)

### 次セッションの入口

1. `M := ↥Q ⧸ Z(↥Q)` に `exists_field_coordinate_realization` を適用する配線。
   入力は `hQEA` (基本可換; `HilbertNinetyOnQ.lean` の `hQEA` と同型)、
   `K` の自由性 (`hKfree` 経由、`exists_mem_inf_centralizer_not_mem_Q0_of_orbit` の
   `hfree` がそのまま使える)、および `|K| = |M| − 1`
   (`|M| = |Q|/|Z(Q)| = q²/q = q`, `|K| = q−1`)。
   `CommGroup M` は `hQEA.comm` から `letI`。
2. `α(r) = 1` の正規化 (α は全単射なので `α(r) ≠ 0` を単位に取り直す、
   あるいは `α` を `α(r)⁻¹` 倍する)。
3. (5)(6)(7) の導出 → 体の代数 → `x ≠ 1` の involution 論法。

## 🎯 §2 Proposition が landing — `hpair` 解消 (2026-07-29 第 3 セッション)

新 leaf 2 本で p.119 を完走した。

### `StructureOfH/QuotientFieldCoordinate.lean`

* `exists_quotient_field_coordinate` — case (b) の `|Q| = |Q₀|²` と `Z(Q) = Q₀` から
  中心商 `M = Q/Z(Q)` は `|Q₀|` 個の元をもち `|K| = |M| − 1`。`K` の自由作用と合わせて
  `Huppert.exists_field_coordinate_realization` が適用でき、p.119 の `α` が
  **`β : G → F`** (`Q` 上加法的・核は `Q₀`・`β(a⁻¹ y a) = γ a · β y`・`(2:F) = 0`) として得られる。
  `γ : K ≃* Fˣ` は `μ` の逆 (書籍の作用 `x ↦ a⁻¹ x a` に合わせた向き)。

### `StructureOfH/OrderFivePairing.lean`

| 定理 | 内容 |
|---|---|
| `eq_of_charTwo_pairing` | (5)(6)(7) + `x ≠ 1` ⟹ `k₁ = k₂` (体の代数) |
| `eq_of_sq_eq_sq_of_charTwo` / `charTwo_pairing_degenerate` | 2 乗の単射性 / `x = 1` ⟹ `α(fg) = 0` |
| `sq_mem_Q0_of_mem_Q` / `mul_comm_of_mem_K` / `eq_one_of_sq_eq_one_of_mem_K` | 補助 |
| **`tConjRight_mul_tConjLeft_notMem_Q0`** | `f g ∉ Q₀` (= 書籍の `x ≠ 1`) |
| `coord_one` / `coord_inv` / `coord_conj{,_inv}` / `coord_tConjTriple_values` | 座標の基本性質と 3 因子の値 |
| **`structureConjugator_mul_conj_inv_pairwise`** | **`hpair` (p.119)** |
| **`tConjMiddle_mem_K_of_case_b`** | `∀ x ∈ S^#, h(x) ∈ K` |
| **`caseBSubgroup`** + `coe_caseBSubgroup` | **`(SK) ∪ (SKtS) ≤ G`** |

⚠ 書籍 p.119 の `x ≠ 1` は「`H` の involution と `G−H` の involution の積」で議論するが、
実際には**標準形の一意性 1 本**で済んだ:
`t w² t = (t w t)² = g · (t (fg)^h t) · f` の両辺を標準形の一意性で比べると `h(w²) = h(z)`
(`z = (fg)^h`)。`H` の involution は全て `K`-共役なので `z = (w²)^c`、よって
`h(z) = c h(w²) c`、`h(w²) ∈ K` と `K` の奇位数可換性から `c = 1`、つまり `z = w²`。
すると左因子が `g(w²) = g · g(w²)` で `g = 1` となり矛盾。

⚠ 座標の正規化 `α(r) = 1` は**不要**だった (`α(r)` が全式で約分される)。

フルビルド green (4928 jobs)、AxiomsCheck OK、lint --strict 0 件。

## 残り = case (b) から仮説を供給する配線だけ

`caseBSubgroup` は `hZQ0` / `hQEA` / `hKfree` / `hQcard` / `h5` を仮説に取る。
`WNeBot.lean` の `SecondCaseHypothesis.trichotomy` の case (b) は
**`IsTypeA ↥Q ∧ orderOf (st) = 5 ∧ W = ⊥`** なので、供給すべきは

| 仮説 | 供給元 | 状態 |
|---|---|---|
| `h5` | trichotomy case (b) | ✅ |
| `hQcard : \|Q\| = \|Q₀\|²` | `natCard_Q_eq_sq_or_cube` の sq 側 (case (b) の分岐条件そのもの) | ✅ |
| `hKfree` | `kfree_mod_Q0_of_center_eq hZQ0` | ✅ (`hZQ0` から) |
| **`hZQ0 : Z(Q) = Q₀`** | `center_Q_eq_Q0_subgroupOf_of_sq_eq_one` + **`TypeAData.sq_eq_one_of_mem_center`** | ❌ 未 (type B/C/D はある) |
| **`hQEA : Q/Z(Q)` 基本可換** | type A モデル (`x² = inl(q(…))`, `[Q,Q] ≤ ker rightHom = inl.range ≤ Z`) | ❌ 未 |

`TypeAData.sq_eq_one_of_mem_center` は `ModelCenters.lean` の type B/C/D と同じ形で、
必要な `typeAQuadraticMap_radical_eq_zero` は
`q(a) = a·φ(a)` の極形式 `B(w,v) = wφ(v) + vφ(w)` について
`v = 1` から `φ(w) = w`、次に `w(φ(v)+v) = 0` と `φ ≠ 1` から `w = 0`。
