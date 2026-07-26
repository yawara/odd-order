---
id: 152
slug: pf-97a-sharpen-block-scalar-order
title: "Pf (9.7)(a) を書籍の `a = |U : C_U(H₁)|` 形へ鋭化 (現状は `p−1` 形)"
created: 2026-07-26
---

# Pf (9.7)(a) を書籍の `a = |U : C_U(H₁)|` 形へ鋭化 (現状は `p−1` 形)

## 書籍 (p. 51, `references/peterfalvi/pdftotext/04.11_*.txt`)

> **(9.7)** One of the following two cases holds.
> **(a)** `H` is the direct product of `q` groups `H_i` (1 ≤ i ≤ q) of order `p` normalized by
> `U`; moreover `{H_i | 1 ≤ i ≤ q} = {H_1^w | w ∈ W_1}`.  **Let `a = |U : C_U(H_1)|`.  Then `a`
> divides `p − 1`, `U/C_U(H_i)` is cyclic of order `a` for all `i`, and `U` is isomorphic to a
> subgroup of the direct product of `q − 1` cyclic groups of order `a`.**

## repo の現状 (2026-07-26 実測)

`(p − 1)` を per-factor の位数に使った**弱い形**しか無い:

| repo | statement |
|---|---|
| `RepresentationTheory.card_dvd_pred_pow_of_blocks` | `|U| ∣ (p − 1)^n` |
| `RepresentationTheory.card_le_cyclotomicQuotient_of_blocks` | `|U| ≤ (p^q − 1)/(p − 1)` |
| `S11.caseA_u_dvd_pred_pow` | `u ∣ (p − 1)^{q−1}` |
| `S11.caseA_u_le_cyclotomicQuotient` | `u ≤ (p^q − 1)/(p − 1)` |

`a` は現れず、「`U/C_U(H_i)` が**全ての `i` で**位数 `a` の巡回群」も無い。
`a ∣ p − 1` は `im(φ_1) ≤ (ZMod p)ˣ` から自明に出るが、statement として無い。

⟹ これは書籍 gap でなく **repo 側の特殊化債務**
([[repo-stronger-hypothesis-is-specialization-not-gap]] の逆向き = 結論が弱い側)。
下流 ((13.13) の 2-part 除去、`u` bound) は弱い形で足りているが、CLAUDE.md
「特殊化債務はできる限り一般化する」の対象。

## 鍵となる観察 — 必要な入力は既に在る

書籍が `a` で済むのは**ブロックが `W₁`-共役だから** (`{H_i} = {H_1^w}`)。repo にも在る:

* `S11.caseA_wOrbit` (`CuS0.lean:701`) — `w ↦ S₀^w`、`W₁` を `U ⊔ W₁` の中で実現した族
* `caseA_wOrbit_one` / `caseA_wOrbit_iSup` / `caseA_wOrbit_iSupIndep` — 生成と独立性

## 実施プラン

1. **`im(φ_w) = im(φ_1)`**: `φ_w(u) = lineScalarChar (S₀^w) u` は `φ_1(w⁻¹ u w)` に等しい。
   `U ⋊ W₁` (Frobenius) ゆえ `w` は `U` を正規化し、`u ↦ w⁻¹ u w` は `U` の自己同型
   ⟹ 像が一致する。
2. `a := Nat.card (im φ_1)` と置くと `a = |U : ker φ_1| = |U : C_U(H_1)|`、
   `a ∣ p − 1` は `im φ_1 ≤ (ZMod p)ˣ` の Lagrange。
   `U/C_U(H_i)` が位数 `a` の巡回群であることは `im φ_i ≤ (ZMod p)ˣ` (巡回) + step 1。
3. **ratio embedding の終域を鋭化**: 現行 `ψ : U ↪ ∏_{i≥1} (ZMod p)ˣ`
   (`caseA_exists_blockScalarRatioEmbedding`) は `u ↦ (φ_i(u) φ_0(u)⁻¹)_i`。
   step 1 より両因子が同じ巡回群 `im φ_1` に居るので、終域を `∏_{i≥1} (im φ_1)` に絞れる
   ⟹ `|U| ∣ a^{q−1}`、これが書籍の「位数 `a` の巡回群 `q−1` 個の直積の部分群」。
4. 既存の `card_{dvd,le}_*_of_blocks` は step 3 の系として残す (下流の signature 不変)。

## 完了条件

`a` を明示に持つ書籍どおりの statement が sorry-free で、既存の `u` bound がその系として
出ること。AxiomsCheck 登録。フルビルド green + `--strict` 警告ゼロ + sorry 非退行。

## 参照

* 書籍: Peterfalvi (9.7)(a), p. 51 (ページ画像を切り出したら
  `references/peterfalvi/pages/peterfalvi-p051.png` に残す)
* `OddOrder/GroupTheory/RepresentationTheory/TypePGaloisUBound.lean`
  (`card_dvd_pred_pow_of_blocks`, `card_le_cyclotomicQuotient_of_blocks`)
* `OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean`
  (ratio embedding の core), `LineScalarCharacter.lean` (`lineScalarChar`)
* `OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean` (`caseA_*`)
* `OddOrder/Peterfalvi/S11_MaximalII_III_IV/CuS0.lean` (`caseA_wOrbit`)
