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

- [x] **段 A** (2026-08-05, `RepresentationTheory/VirtualCharacter.lean`): 分裂データを持たない
      `virtualCharacters K H : AddSubgroup (H → K)` (= `ch(H)`)。`IsRepCharacter` は標準空間
      `Fin n → K` 上の表現の指標として定義し (universe 単一化)、`isRepCharacter_of_finite`
      (基底を取って `transportRepresentation` で移送) で一般性を回復。`1 ∈`・テンソル積による
      積閉性・群準同型による引き戻し (`Res` がその特殊化)。
- [x] **段 B** (2026-08-05, `VirtualCharacterPairing.lean` + `VirtualCharacterInduction.lean`):
      `charPairing K a b = (1/|G|) Σ_g a(g⁻¹)b(g)`、`charPairing_isRepCharacter`
      (= `dim Hom_{KG}(V,W)`、mathlib `card_inv_mul_sum_char_mul_char_eq_finrank`)、
      `charPairing_mem_intRange`。`extendByZero` / `induceFun`、
      `induceFun_mul_restrict` (= **Lemma 7.2** projection formula)、
      `charPairing_induceFun` (= **Frobenius 相互律**)。
      ⚠ `Ind(ch(H)) ⊆ ch(G)` は「ch(G) の内積による特徴づけ」が要るので段 C 以降に回す
      (特徴づけには `G` の分裂 `e` が必要 — 非分裂だと `⟨χ_i,χ_i⟩ = dim End > 1` になりうる)。
- [x] **段 C 前半** (2026-08-05, `BrauerInductionIdeal.lean` + `Modular/VirtualCharacterSplitting.lean`):
      `inducedVirtualCharacters K 𝒳` (= `v(G)`) と **Lemma 7.3** (`ch(G)` のイデアル)。
      族 `𝒳` は elementary に固定せず**パラメータ**にした。
      分裂 `e` を通した `ch(G)` の特徴づけ: `charPairing_wedderburnRepresentation` (直交正規性、
      既存の第一直交関係の読み替え) / `exists_eq_sum_wedderburnRepresentation` (ブロック指標が
      類関数を張る) / `eq_sum_charPairing_wedderburnRepresentation` (`θ = Σ_i (θ,χ_i)χ_i`) /
      `eq_of_charPairing_eq` / `mem_virtualCharacters_iff` / **`induceFun_mem_virtualCharacters`**
      (`Ind_H^G(ch(H)) ⊆ ch(G)`、Frobenius で H 側に移して分裂不要の整数性) /
      `inducedVirtualCharacters_le_virtualCharacters` (`v(G) ⊆ ch(G)`)。
      併せて段 B の仮説を `[CharZero K]` → `[Invertible (Nat.card G : K)]` に緩和。
- [x] **段 C 後半** (2026-08-05, `Modular/BrauerInductionDescent.lean`): `adjoinSpan ω M` (= `ℤ[ω]·M`)、
      正規形 `exists_sum_pow_smul_of_mem_adjoinSpan`、power basis の `K` への移送
      (`coe_adjoin_powerBasis_basis` / `exists_intCast_sum_pow` /
      `eq_zero_of_sum_intCast_pow_eq_zero`)、**Lemma 7.4** =
      `mem_inducedVirtualCharacters_of_mem_adjoinSpan` (`ch(G) ∩ v_R(G) = v(G)`)。
      - **実装した設計**: 係数抽出を **`charPairing` 経由**にすると降下が軽くなる。
        `θ ∈ ch(G)` かつ `θ = Σ_{j<n} ω^j • u_j` (`u_j ∈ v(G)`) とすると、双線型性から
        `(θ,χ_i) = Σ_j ω^j (u_j,χ_i)` で `(u_j,χ_i) = b_{ij} ∈ ℤ`、`(θ,χ_i) = α_i ∈ ℤ`。
        `{ω^j}_{j<n}` の **ℤ-一次独立**から `b_{i0} = α_i`・`b_{ij} = 0 (j≥1)` ⟹
        `u_0` と `θ` は全 `χ_i` との内積が一致 ⟹ `eq_of_charPairing_eq` で `θ = u_0 ∈ v(G)`。
        ⟹ 必要なのは **`{ω^j}_{j<n}` が `ℤ[ω]` の ℤ-基底**であること (張る + 独立) だけで、
        `Irr(G)` の一次独立性は別途要らない (展開補題が代行)。
      - `v_R(G) ⊆ W := {Σ_{j<n} ω^j • u_j | u_j ∈ v(G)}` は `W` が加法部分群で生成元を含むことから。
      - power basis は mathlib `Algebra.adjoin.powerBasis' (hx : IsIntegral ℤ ω)`
        (`FieldTheory/Minpoly/IsIntegrallyClosed`) を `↥(Algebra.adjoin ℤ {ω}) ↪ K` で K へ移送。
      - **調査済 (2026-08-05)**: 降下 (`ch(G) ∩ v_R(G) = v(G)`) の鍵 = 「`1,ω,…,ω^{n−1}` が
        `ℤ[ω]` の ℤ-基底」。mathlib に **`Algebra.adjoin.powerBasis' (hx : IsIntegral R x) :
        PowerBasis R (Algebra.adjoin R {x})`** (`FieldTheory/Minpoly/IsIntegrallyClosed.lean`)
        があり、`R = ℤ` (integrally closed)・`S = K` (domain, char 0) で使える。
        `ω^N = 1` (`N = |G|`) から `IsIntegral ℤ ω` は `X^N − 1` が monic で即。
      - ⚠ 代替案 (`R` を `{ω^j : j < N}` の ℤ-span に取る) は **不可**: 生成系が ℤ-独立でないので
        `v_R = ⊕_j ω^j v` の直和分解が壊れ、降下が成立しない。
      - ⚠ R 層そのものを回避する案も検討したが**不可**: Lemma 7.6 の `ψ = Σ_i ζ^{-i} ψ_i`
        (= `|U|·1_{uP}`) は ℤ 係数では書けず (`⟨ψ,ψ_i⟩ = ζ^{-i} ∉ ℤ`)、ℤ 係数に留めると
        台が「ℤ-類」に粗くなって Lemma 7.7 (任意の整数値類関数の展開) が壊れる。
- [x] **段 D 完了** (2026-08-05): Lemma 7.5 (整数値 `χ ∈ ch_R(G)` は各 **p-class** 上で mod p 一定)。
      - **用途**: Lemma 7.8 で「`ζ_j` が p-class `L_j` 上で mod p 一定かつ p と素」を使うところ。
        7.6/7.7 では使わない。
      - **前半** `RepresentationTheory/CharacterEigenvalues.lean`: `A^m = 1` のとき
        `tr(A^k) = Σ_ζ dim(eigenspace A ζ)·ζ^k`、指標版、`character_mem_adjoin`。
        ⚠ **重複度を `ρ g` のものに固定して `k` に依らない形**にしたのが要点。
        却下した 2 案: (a) `tr(A^p) ≡ (tr A)^p` (repo に `OddOrder.trace_pow_prime` は在るが
        標数 `p` の成分が要り `G`-不変 `ℤ[ω]`-束の構成が必要)、(b) 原文どおり `χ|_Y` を
        `Irr(Y)` 展開 (巡回部分群ごとの分裂データが要る)。
      - **中盤** `Modular/CyclotomicIntegerModP.lean`: `adjoinPrimeIdeal ω p`、`ℤ ∩ pℤ[ω] = pℤ`、
        `CharP (ℤ[ω]/p) p` (素数性は不要と判明したので仮説から落とした)。
      - **後半(1)** `Modular/CyclotomicModEq.lean`: `CyclotomicModEq ω p x y ↔ x−y ∈ p·ℤ[ω]` と
        その算術 (同値関係/加法/`ℤ[ω]` 元倍/有限和、freshman's dream、Fermat、`Int.ModEq` への降下)。
        `(-x)^{p^s} ≡ -(x^{p^s})` は `x + (-x) = 0` に freshman's dream を当てて **`p = 2` 込みで
        一様に**出る (`p^s` の偶奇の場合分けが不要)。
      - **後半(2)** `Modular/CharacterPClassCongruence.lean`: 真の指標での核心
        `character_pow_prime_pow` → `AddSubgroup.closure_induction` 2 段で `ch_R(G)` へ →
        `exists_pow_prime_pow_eq_pRegularPart` (`y^{p^s} = (p'-部分)^{p^s}`) →
        `intModEq_of_mem_adjoinSpan` = **Lemma 7.5** 本体。
- [x] **段 E 完了** (2026-08-05): Lemma 7.6 の核心構成。leaf 5 本:
      - `RepresentationTheory/UnitCharacter.lean`: `λ : H →* Kˣ` からの 1 次元表現、
        等比数列和 `Σ_{i<n} ζ^{-i} x^i = n·[x = ζ]`、`fibreIndicator_mem_adjoinSpan`
        (`n·1_{λ⁻¹(ζ)} ∈ ch_R(H)`)。⚠ 原文の「`P` を核に含む既約指標**全体**」でなく
        **`λ` 1 本とその冪**で足りるので、巡回群の指標群の構成が不要になる。
      - `GroupTheory/CosetInvariantCard.lean`: `A·P ⊆ A` なら `|P| ∣ |A|`。
      - `RepresentationTheory/InducedIndicator.lean`: `(Ind_H^G (c·1_S))(y) = (c/|H|)·σ(y)`
        と **(i)** の整数性。⚠ 誘導和を `x⁻¹ y x` の向きで読むと計数集合が**右**移動で閉じ、
        mathlib の `G ⧸ P` (左剰余類) にそのまま乗る。
      - `RepresentationTheory/PRegularCosetCount.lean`: **(ii)** (可換 `p'`×`p` 分解の一意性)
        と **(iii)** (`σ(u) = |C_G(u)|`; 位数の乗法性で `v = 1`)。
      - `RepresentationTheory/PRegularCosetCharacter.lean`: `λ` の構成。
        ⚠ **巡回群の指標論を使わない** — `h = u^a v` で `u^a` が `p'`-部分に強制されるので
        `a` が `mod n` で一意になり `λ h := ζ^a` が準同型になる。
      - `RepresentationTheory/PRegularCosetInduction.lean`: 組み立て = **Lemma 7.6** 本体。
- [x] **段 F 完了** (2026-08-05): Lemma 7.7–7.10 ⟹ **`v(G) = ch(G)`**
      - [x] **準備 1** `GroupTheory/PRegularCosetSubgroup.lean`: `pRegularProd u P hcomm` = `⟨u⟩P`
        (⚠ **ℤ 冪**で定義 — ℕ 冪だと `inv_mem'` に `0 < orderOf u` が要り `Finite G` が def の
        引数に混ざって下流の `omit` が詰まる) と `card_pRegularProd` (`|⟨u⟩P| = orderOf u·|P|`)。
        段 E が仮説として受けていた `hgen` / `hcard` を構成的に供給する。
      - [x] **準備 2** `RepresentationTheory/InducedAdjoinSpan.lean` + `induceFun` の線形性:
        `Ind_H^G(ch_R(H)) ⊆ v_R(G)` (Lemma 7.6 の `ψ` は `ch(H)` でなく `ch_R(H)` に居る)。
      - [x] **Lemma 7.6 パッケージ** `RepresentationTheory/PClassIndicator.lean`:
        `exists_pClassIndicator`。`ζ := ω^(N/orderOf u)`、`H = ⟨u⟩P = pRegularProd`、`𝒳` は
        `IsElementaryFamily` (全ての `p` と `⟨u⟩P` を含む族) として仮説化。
        結論に**類関数性**も入れた (7.7/7.8 とも代表元での値を類全体へ広げるので毎回要る;
        支持補題 `conjugateCount_conj`)。
      - [x] **Lemma 7.7** `RepresentationTheory/DivisibleClassFunction.lean`:
        `mem_adjoinSpan_inducedVirtualCharacters_of_card_dvd`。`p > |G|` を取ると
        (i) 全元が `p`-正則 ⟹ p-class = 共役類、(ii) `P = ⊥` が許容、が同時に潰れる。
        係数 `θ(C.out)/|G| · [G : C_G(C.out)]` は整数。
      - [x] **Lemma 7.8** `Modular/BrauerInductionTheorem.lean`: `exists_congr_one_mod_prime`。
        p-正則類ごとに `P ∈ Syl_p(C_G(u_C))` ⟹ `χ_C(u_C) = [C_G(u_C):P]` が `p` と素
        (Sylow の位数 = `ordProj[p]` ⟹ 指数 = `ordCompl[p]`)、Bézout で mod `p` の逆元。
        代表元の外へは**段 D の Lemma 7.5** で広げる ⟹ `v_R(G) ⊆ ch_R(G)` が要り
        (`adjoinSpan_mono` + 分裂 `e` 経由)、7.8 以降は `Modular` 名前空間。
      - [x] **Lemma 7.9** `zsmul_one_mem_inducedVirtualCharacters`: `ζ = χ^{p^a}` は
        `mul_mem_adjoinSpan_inducedVirtualCharacters` (= 7.3 の `ℤ[ω]` 係数版) で `v_R(G)` に留まり、
        `ζ ≡ 1 (mod p^a)` は mathlib `dvd_sub_pow_of_dvd_sub` 一発。`m(1−ζ)` に 7.7、最後に段 C 降下。
      - [x] **Lemma 7.10** `inducedVirtualCharacters_eq_virtualCharacters` = **`v(G) = ch(G)`**。
        `{k : ℤ | k·1_G ∈ v(G)}` は ℤ のイデアルで全素数 `q` の `ordCompl[q] |G|` を含み、gcd は 1
        (共通素因数 `q` ⟹ `q ∣ ordCompl[q] |G|` で矛盾)。Bézout は Finset 帰納で 2 元ずつ、
        添字を `insert 2 (primeFactors |G|)` に取ると `|G| = 1` も一様に落ちる。
- [x] **段 G 完了** (2026-08-05): Brauer's characterization 本体
      `mem_inducedVirtualCharacters_of_restrict` — 類関数 `θ` の `𝒳` の各元への制限が仮想指標なら
      `θ ∈ v(G)`。`θ = 1_G · θ` に**段 B の Lemma 7.2** (projection formula) を当てるだけ。
      ⚠ `θ` の類関数性は落とせない (projection formula がそれを要求する)。
      ⚠ Thm 7.11 は予定どおり**不要**だった。
- [ ] **段 H**: Navarro (2.15) → (2.16) → (3.16) (ブロック局所化は段 205-206 の型を反復)

  **原文の確定** (2026-08-05, `references/navarro/pages/navarro-p0{27,28}.png` を読了):
  - `θ̃(x) = p^a θ(x)` (`x ∈ G⁰`)・0 (それ以外)、`θ̂(x) = θ(x_{p'})` (`x ∈ G`)。
  - **(2.15)**: `θ ∈ ℤ[Irr(G)] ∪ ℤ[IBr(G)]` ⟹ `θ̂` と `θ̃` は generalized character。
    証明は「指標判定より `E = P × Q` (P は p-群, Q は p'-群) 上で見ればよく、
    `θ̂|_{P×Q} = 1_P × θ_Q`、`θ̃|_{P×Q} = (|G|_p/|P|)(ρ_P × θ_Q)`」。
    ⟹ **本質は `θ_Q ∈ ch(Q)` (Q は p'-群) だけ** ((2.2.d)+(2.12))。
  - **(2.16)**: `(φ̂)⁰ = φ` と (2.15) から即。**`θ̃` は (2.16) には不要**
    (原文も「`θ̃` は後で使う」と書いている) ⟹ **`θ̂` だけ作ればよい**。

  - [x] **H1 完了** (2026-08-05, `GroupTheory/PRegularProjection.lean`): `E = ⟨u⟩P` 上の `p'`-射影。
  - ⚠ **単一指数 `M` で書けるのが鍵**: `M ≡ 0 (mod |E|_p)`, `M ≡ 1 (mod |E|_{p'})` (CRT) を取ると
    **全ての `z ∈ E` で `z_{p'} = z^M`** (`z_p^M = 1`・`z_{p'}^M = z_{p'}`)。
  - `(xy)^M = x^M y^M` は `x = u^a v` と `u` の中心性で `P` 上の問題に落ち、`P` は
    `q`-群なので **`q = p` なら `v^M = 1`・`q ≠ p` なら `v^M = v`** の 2 択で両方 hom。
    ⟹ **冪零群の Sylow 分解 (mathlib `Sylow.directProductOfNormal`) を使わずに済む**。
  - `π` の像 `E' := π.range` は全元が `p`-正則 ⟹ Cauchy で `p ∤ |E'|` = **p'-群**。
  - ⟹ `θ̂|_E = (θ|_{E'}) ∘ π` で `comp_mem_virtualCharacters` (段 A) に乗る。
  - ⚠ `θ|_E ∈ ch(E)` ではない — 落とす先は **`E'` (p'-部分)** であって `E` ではない。

  - [ ] **H2** (段 H の実質) = **Navarro (2.12)**: `Q` が `p'`-群 ⟹ `IBr(Q) = Irr(Q)`
    (よって `θ ∈ ℤ[IBr(G)]` の制限 `θ|_Q` は `ch(Q)` に入る)。

    **設計調査 (2026-08-05、実測込み)**。潰した近道 2 本を先に記録する:

    - ❌ **「`E_{p'}` は巡回だから easy」は成立しない**。`E = ⟨u⟩P` が `q`-elementary のとき
      `E_{p'}` が巡回になるのは **`q = p` のときだけ** (`E_{p'} = ⟨u⟩`)。`q ≠ p` では
      `E_{p'} = ⟨u_{p'}⟩ × P` で `P` は非可換な `q`-群でありうる。
      巡回なら Brauer 指標は `φ|_{⟨z⟩} = Σ_ζ d_ζ λ_ζ` (`λ_ζ : z^j ↦ ζ̂^j` は `K` 上の線形指標) で
      即終わるが、一般の `p'`-群ではこれが効かない。
    - ❌ **`p`-elementary だけで済ませる route も不可**。Lemma 7.9 (素数 `p`) が使う族は
      「全巡回部分群 + `p`-elementary」だけで、どちらも `p'`-部分が巡回 ⟹ `m_p θ̂ ∈ ch(G)`
      (`p ∤ m_p`) までは巡回だけで出る。しかし `θ̂ ∈ ch(G)` に上げるには
      「`ℤIBr(G)/ℤ{χ⁰}` が `p`-群」= **`det C` が `p` 冪** (Brauer) が要り、
      それは (2.16) と circular になりうるので短くならない。
      (なお `Φ_φ⁰ = Σ_μ c_{μφ} μ` から `ℤIBr/L` は `det C` で消えることは出る。)

    ⟹ **採用 route = `p'`-群の Cartan 行列が単位行列**であることを示し、段 204 の
    `BrauerFromOrdinary` (`a_χ = Σ_τ d_{χτ}[τ,μ₀]⁰`) の係数を `a_χ = d_{χμ₀} ∈ ℕ` に落とす。

    **H2 の分解** (repo の既存 stack を使う):
    - **H2a**: `p ∤ |Q|` ⟹ `k[Q]` は半単純。mathlib の Maschke
      (`instance : IsSemisimpleRing k[G]`、仮説 `[Finite G] [NeZero (Nat.card G : k)]`) がそのまま。
      `NeZero (Nat.card Q : k)` は `p ∤ |Q|` と `CharP k p` から。
    - **H2b**: `k` 代数閉なら `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` で
      分裂 `π : k[Q] ≃ₐ ∏_j M_{n_j}(k)` を**構成**でき、`ker π = ⊥ = J(k[Q])`。
      ⟹ H2/H3 は分裂データを仮説で受けずに済む (代わりに `[IsAlgClosed (ResidueField 𝒪)]`)。
      ⚠ BS の具体系 `PadicComplexSystem` の剰余体は `F̄_p` = 代数閉 ✓
      (`SplittingSystem p n = 𝕎(GF(p^φ(n)))` は代数閉でないので、そちらでは使えない)。
    - **H2c**: `C = I`。数え上げで出る:
      `Σ_j n_j² = |Q| = Σ_i m_i²` (両側の Wedderburn) と `m_i = Σ_j d_{ij} n_j` から
      `Σ_{j,j'} c_{jj'} n_j n_{j'} = Σ_j n_j²`、各 `c_{jj} ≥ 1` (正則指標の比較で列が非零)
      かつ `c_{jj'} ≥ 0` ⟹ 全項が潰れて `c_{jj} = 1`, `c_{jj'} = 0`。
    - **H2d**: `C = I` ⟹ `C⁻¹ = ([τ,μ]⁰) = I` ⟹ 段 204 の `a_χ = d_{χμ₀} ∈ ℕ`。
      `p'`-群では全元が `p`-正則なので `χ⁰ = χ` ⟹ `φ = Σ_χ d_{χφ} χ ∈ ch(Q)`。
    - **H2e**: 制限。`θ|_Q` は制限加群の Brauer 指標 = `IBr(Q)` の **ℕ**-結合。

    ⟹ **H2 は複数 session 規模**。上流から H2a → H2b → H2c → H2d → H2e。

  - [ ] **H3**: (2.15) の組み立て (`θ̂ ∈ ch(G)`、`φ ∈ IBr(G)` の場合のみ)。
  - [ ] **H4**: (2.16) = `φ = Σ_χ a_χ χ⁰` (`a_χ ∈ ℤ`)。`φ̂ ∈ ℤ[Irr(G)]` を `G⁰` に制限するだけ。
  - [ ] **H5**: (3.16) = ブロック局所化 (段 205-206 の型を ℤ 係数で反復)。
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
