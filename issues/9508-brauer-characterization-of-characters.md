---
id: 9508
slug: brauer-characterization-of-characters
title: "Brauer's characterization of characters (Brauer–Tate) — Navarro (2.15)/(2.16)/(3.16) の前提"
created: 2026-08-05
---

# Brauer's characterization of characters (Brauer–Tate) — Navarro (2.15)/(2.16)/(3.16) の前提

## 背景

[9506](9506-modular-p-modular-system.md) (Q₈ Brauer–Suzuki の spine = Navarro Ch.1–7) の
**唯一残った本質的な上流前提**。BS 証明 p.141-142 の中核は「列 `D^t_j` が整数列である」ことに
依存しており、それは basic set への変換行列 `U` の整数性 = Navarro **(3.16)** に帰着する。
(3.16) のブロック局所化は段 205-206 で済んでいるので、残るのは (2.16) 本体:

> **(2.16)** `φ ∈ IBr(G)` は `{χ⁰ : χ ∈ Irr(G)}` の **ℤ**-結合である。

Navarro の証明は **(2.15)** (`θ ∈ ℤ[Irr(G)] ∪ ℤ[IBr(G)]` なら `θ̂ (x) := θ(x_{p'})` と
`θ̃` は generalized character) 経由で、(2.15) は **Brauer's characterization of characters**
だけに依存する (原文 p.28: elementary subgroup `P × Q` 上では `θ̂|_{P×Q} = 1_P × θ_Q`、
`θ̃|_{P×Q} = (|G|_p/|P|)(ρ_P × θ_Q)` と明示計算で終わる)。

⚠ **実測 (2026-08-05)**: Brauer induction / 指標判定は **mathlib にも本リポにも無い**
(`Mathlib/RepresentationTheory/` に該当なし、repo grep もヒット無し)。⟹ 共有インフラとして建てる。

### 原典 (証明を読む先)

出典は Isaacs *Character Theory of Finite Groups* Thm 8.4 だが**手元に無い**。
**Gorenstein 1968 §4.7 (書籍 pp.160–170) に Brauer–Tate の完全な簡略証明がある**ので
そちらを正本にする (BG の行間を埋める用途と同じ posture = 参照のみ・形式化対象ではない)。
ページ画像を references に取得済: `references/gorenstein/pages/gorenstein-p{159..172}.png`
(PDF ページ = 書籍ページ + 19)。

Gorenstein の構成 (記号: `ch(G)` = generalized characters, `v(G) = Σ_{E ∈ 𝓔} ch(E)^*`,
`R = ℤ[ω]` (`ω` = 原始 `|G|` 乗根), `ch_R`/`v_R` は係数を `R` に拡げたもの):

| 番号 | 内容 |
|---|---|
| Lemma 7.2 | **projection formula** `(φ·(θ|_H))^* = φ^* · θ` (純粋な計算) |
| Lemma 7.3 | `v(G)` は `ch(G)` のイデアル |
| Lemma 7.4 | `m·1_G ∈ v_R(G)` ⟹ `m·1_G ∈ v(G)` (`1,ω,…,ω^{n-1}` が `ch(G)` 上一次独立 ⟹ `ch(G) ∩ v_R(G) = v(G)`) |
| Lemma 7.5 | `χ ∈ ch_R(G)` が整数値なら `χ mod p` は各 **p-class** 上で一定 |
| Lemma 7.6 | **核心の構成**: `U = ⟨u⟩` (`u` = `p'`-元), `P ∈ Syl_p(C_G(U))` に対し `ψ ∈ ch_R(U × P)` で `ψ^*` が (i) 整数値 (ii) `u` の p-class の外で 0 (iii) `ψ^*(u) = |C_G(u) : P| ≢ 0 mod p` |
| Lemma 7.7 | 整数値類関数で全値が `|G|` で割れるものは `v_R(G)` に入る |
| Lemma 7.8 | 各 `p` に対し `χ ∈ v_R(G)` 整数値で `χ ≡ 1 mod p` |
| Lemma 7.9 | `|G| = m p^a`, `(m,p)=1` ⟹ `m·1_G ∈ v(G)` |
| Lemma 7.10 | **`v(G) = ch(G)`** (`m_i = |G|/p_i^{a_i}` が互いに素 ⟹ `1_G ∈ v(G)`) |
| Thm 7.11 | elementary 群の既約指標は**線形**指標から誘導される |

⚠ **Thm 7.11 は不要** — 我々が要るのは Lemma 7.10 (「任意の既約指標から誘導」版) までで、
「線形指標で足りる」という強化は使わない。

### Brauer's characterization 本体

`θ` が類関数で、すべての elementary `E ≤ G` について `θ|_E ∈ ch(E)` ならば `θ ∈ ch(G)`:
`θ = θ · 1_G = θ · Σ c_i φ_i^* = Σ c_i (φ_i · (θ|_{E_i}))^* ∈ v(G) = ch(G)` (Lemma 7.2 + 7.10)。

## アーキテクチャ判断 (2026-08-05)

**モジュラー stack の `K` 側で建てる** (ℂ 側の Peterfalvi stack ではない)。理由:

- 消費者 (2.15)/(2.16)/(3.16) は `𝒪`/`K = Frac 𝒪`/`ResidueField 𝒪` と Wedderburn 分裂
  `e : K[G] ≃ₐ ∏ M_{m_i}(K)` の言語で書かれている。ℂ 側 (`ClassFunction G ℂ`, `IsCharacter`,
  `ZIrr G`) から橋渡しするには「標数 0 の分裂体上の指標表は体に依らない」という別の大仕事が要る。
- `K` 側には既に土台が揃っている (**実測**):
  - `Modular/OrdinaryColumnOrthogonality`: `equivConjClasses e : ι' ≃ ConjClasses G`、
    `characterMatrix` `X` とその逆 `W` (`X·W = 1`, `W·X = 1`) ⟹ **行・列両方の直交関係**。
    双線型版 (`χ(g⁻¹)`、複素共役でなく) なので一般の `K` でそのまま通る。
  - `Modular/OrdinaryDecomposition`: `exists_ordinary_decomposition` = 任意の有限次元表現は
    ブロック単純加群の直和 ⟹ 「指標は `Irr` の **ℕ**-結合」。
  - `ClassFunction.induce` (`RepresentationTheory/InducedCharacter`) は係数環 `k : CommRing` で
    generic なのでそのまま使える。
- `Ind` が指標を指標に送ることは**証明しなくてよい**: `ch(G) = {θ : ⟨θ,χ_i⟩ ∈ ℤ ∀ i}` と
  **Frobenius 相互律** (類関数の恒等式、純粋な計算) から `Ind(ch(H)) ⊆ ch(G)` が出る。
  ⟹ 誘導加群 `K[G] ⊗_{K[H]} V` を構成してトレースを計算する必要がない (最大の節約)。

`K` への追加仮説: **原始 `exp G` 乗根 (または `|G|` 乗根) を含む**こと。Lemma 7.5/7.6 が
巡回群の線形指標を使うため。BS で使う具体系 (`PadicComplexSystem` の `𝓞_ℂ_[p] ⊂ ℂ_p`) は
すべての 1 の冪根を含むので充足可能。

## やること

- [ ] **段 A**: `K` 側 generalized character `ch(G)` の定義と基本性質
      (`ℤ`-span of `ordinaryCharacter e i` / 内積の整数性による特徴づけ / `Res` で閉じる)
- [ ] **段 B**: `Ind`/`Res` の Frobenius 相互律と projection formula (Gorenstein Lemma 7.2)
      を `K` 係数の類関数で。`Ind(ch(H)) ⊆ ch(G)` (段 A の特徴づけ経由)
- [ ] **段 C**: `v(G)` の定義とイデアル性 (Lemma 7.3)、`R = ℤ[ω]` 係数版と Lemma 7.4
- [ ] **段 D**: Lemma 7.5 (p-class 上の mod p 一定性)
- [ ] **段 E**: Lemma 7.6 (核心の構成)
- [ ] **段 F**: Lemma 7.7–7.10 ⟹ `v(G) = ch(G)`
- [ ] **段 G**: Brauer's characterization 本体
- [ ] **段 H**: Navarro (2.15) → (2.16) → (3.16) (ブロック局所化は段 205-206 の型を反復)
- [ ] **段 I**: `PrincipalBlockBasicSet` の `U` を ℤ 値に戻し、9506 の BS 本証明へ供給

## 完了条件

`v(G) = ch(G)` と Brauer's characterization が sorry-free で、Navarro (2.16)/(3.16) が
そこから導かれ、`principalBasicSetMatrix` の整数性が使える形になること。
build green + AxiomsCheck 登録 + sorry 非退行。

## 参照

- 親: [9506](9506-modular-p-modular-system.md) / [0147](0147-q8-modular-char-theory-frozen.md)
- 原典: Gorenstein 1968 §4.7 (書籍 pp.160–170、`references/gorenstein/pages/`)、
  Navarro pp.27–28 ((2.14)–(2.17)、`references/navarro/pages/navarro-p0{27,28}.png`)
- 既存土台: `OddOrder/GroupTheory/RepresentationTheory/Modular/OrdinaryColumnOrthogonality.lean`,
  `Modular/OrdinaryDecomposition.lean`, `RepresentationTheory/InducedCharacter.lean`
