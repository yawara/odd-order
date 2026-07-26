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

---

## 📐 実測の訂正 (2026-07-26) — `a`-torsion 形は既に在った

起票時に見落としていた: `RepresentationTheory.exists_blockScalarRatioEmbedding_of_blocks_pow_eq_one`
(`TypePGaloisUBound.lean:65`) が既に **`a`-torsion 形の埋め込み**を与えている
(`∃ ψ, Injective ψ ∧ ∀ u i, (ψ u i)^a = 1`、docstring も「Peterfalvi (9.7)(a), order-`a`
refinement」と明記)。⟹ 欠けていたのは**位数の割り切り**の側だけだった。

## ✅ step 3 完了 (2026-07-26)

共通像 `A ≤ 𝔽_p^×` を明示に取る形を追加:

| 新規 | statement |
|---|---|
| `RepresentationTheory.card_dvd_pow_card_of_block_scalars_mem` | 全ブロックスカラーが `B ≤ A` に値を取れば `|Ū| ∣ |B|^n` (終域の corestrict) |
| `RepresentationTheory.card_subgroup_dvd_card` | `|B| ∣ |A|` (Lagrange) — `A = 𝔽_p^×` で書籍の `a ∣ p−1` |
| `RepresentationTheory.card_dvd_blockScalarOrder_pow_of_blocks` | (9.7)(a) の書籍 `a`-形入口: `|U| ∣ |A|^n ∧ |A| ∣ p−1` |

`A = ⊤` で従来の `card_dvd_pred_pow_of_blocks` に戻るので下流は不変。AxiomsCheck 登録済
(3 axiom)。フルビルド green (4798 jobs)、`--strict` 警告ゼロ、sorry 非退行。

## 残り (step 1–2)

`A = im φ₁` を **`W₁`-共役から produce する S11 側**の step:

1. `im(φ_w) = im(φ_1)` — `φ_w(u) = φ_1(w⁻¹ u w)` と `U ⋊ W₁` の正規化性から。
   `caseA_wOrbit` (`CuS0.lean:701`) がブロック族 `w ↦ S₀^w` を持っているので、
   `lineScalarChar (S₀^w)` と `lineScalarChar S₀ ∘ conj w⁻¹` の一致を示すのが核。
2. `a := Nat.card (im φ₁) = |U : C_U(H₁)|` を pin し、
   `card_dvd_blockScalarOrder_pow_of_blocks` に流し込む。

これで `caseA_u_dvd_pred_pow` の `a`-鋭化版が出る。

## 🔀 経路変更 (2026-07-27) — 表現論の plumbing が不要になった

step 1-2 を「ブロックを表現として同型に組む」で進める予定だったが、`Subrepresentation` /
`Additive` / instance 罠の多い領域で重い。**`𝔽_p^×` が巡回**であることを使うと丸ごと回避できる:

* 有限巡回群では**部分群は位数で決まる** (`OddOrder/Mathlib/CyclicSubgroupUnique.lean` 新設:
  Lagrange で `B ≤ (n-torsion)`、`IsCyclic.card_pow_eq_one_le` で torsion ≤ `|B|` ⟹ 一致。
  ⟹ `Subgroup.eq_of_card_eq_of_isCyclic`)。
* ⟹ ブロックごとの像が「一致する」ことを直接示す代わりに、**位数が等しい**ことだけ示せばよい
  (`card_dvd_blockScalarRange_pow_of_blocks_card_eq`)。

⟹ **S11 側に残るのは純群論だけ**: 共役 `g_j` が `C_Ū(S₀)` を `C_Ū(Hpart j)` に写す
⟹ 指数が等しい ⟹ `|im φ_j| = |im φ_0|`。`|im φ| = |Ū : ker φ|` と
`ker φ = C_Ū(block)` は `card_lineScalarChar_range_eq_index` / `lineScalarChar_ker_eq` で済。

### generic 側の完成品 (すべて axiom-clean)

| 定理 | 内容 |
|---|---|
| `lineScalarChar_comp_of_equivariant` | 同変同型に沿った scalar character の移送 |
| `lineScalarChar_range_eq_of_equivariant` | σ 全射なら像一致 (共役ルート) |
| `GroupTheory.eq_powMonoidHom_ker_card` | 有限巡回群で部分群 = 自分の位数の torsion |
| `GroupTheory.Subgroup.eq_of_card_eq_of_isCyclic` | 位数一致 ⟹ 部分群一致 |
| `card_dvd_blockScalarOrder_pow_of_blocks` | 共通像 `A` から `|U| ∣ |A|^n ∧ |A| ∣ p−1` |
| `card_dvd_blockScalarRange_pow_of_blocks` | 像一致版 |
| `card_dvd_blockScalarRange_pow_of_blocks_card_eq` | **位数一致版** (S11 が使う入口) |
| `card_lineScalarChar_range_eq_index` / `lineScalarChar_ker_eq` | `a = |U : C_U(H₁)|` の pin |

### 残り

S11 の `caseA` で `Hpart_orbit` から「指数が等しい」を出し、
`card_dvd_blockScalarRange_pow_of_blocks_card_eq` に流して `caseA_u_dvd_a_pow` を得る。

## ✅ generic 側 完了 (2026-07-27)

群論の核も揃った (`OddOrder/Mathlib/Subgroup.lean`):

| 定理 | 内容 |
|---|---|
| `Subgroup.ptStabOfMulAut φ J` | `MulAut` 作用で `J` を各点固定する**作用側**の部分群 (`fixedPointsOfMulAut` の双対) |
| `Subgroup.ptStabOfMulAut_smul` | `σ` が `g` 共役を実装 ⟹ `ptStab φ (g • J) = σ (ptStab φ J)` |
| `Subgroup.index_ptStabOfMulAut_smul` | ⟹ 指数が等しい |
| `Subgroup.index_ptStabOfMulAut_subtype_smul` | **消費者向け**: `Ū ≤ MulAut G`、`g` が `Ū` を正規化するだけで指数一致 (σ は内部構成) |

⟹ S11 側が供給すべきものは **2 つだけ**:

1. `g_j := quotientMulAutHom chief.N_aInvariant (caseA.orbitRep j)` が
   `Ū = range (uActionHom data chief)` を正規化すること
   — `quotientMulAutHom` が準同型ゆえ `g_j * quotientMulAutHom v * g_j⁻¹ =
   quotientMulAutHom (orbitRep j * v * (orbitRep j)⁻¹)` で、
   `U ⊴ U ⊔ W₁` (`(typeP_uW1_frobenius data.typeP hU).isNormal`) から従う。
2. `ker (lineScalarChar (B j)) = ptStabOfMulAut Ū.subtype (Hpart j)` の同一視
   (`lineScalarChar_ker_eq` + `Hpart` の carrier)。

そこから `card_lineScalarChar_range_eq_index` → 位数一致 →
`card_dvd_blockScalarRange_pow_of_blocks_card_eq` で `caseA_u_dvd_a_pow` が出る。

## ⚠ 最終組み立ての設計 (2026-07-27) — `hconst` を `have` に hoist してはいけない

S11 の `caseA_exists_blockScalarRatioEmbedding` から `hconst` (§9 の crux、80 行) を
`have` に hoist して 2 箇所で使い回そうとしたが、**instance diamond で失敗**した:

```
(B 0).toRepresentation :
  @Representation (ZMod p) _ _ CommRing.toCommSemiring.toSemiring ...
但し期待される型は
  @Representation (ZMod p) _ _ Field.toSemifield.toDivisionSemiring.toSemiring ...
```

原因: 元の証明は `refine exists_blockScalarRatioEmbedding_of_blocks … ?_` の形なので、
`hBcard` / `hconst` の型が**generic 補題の signature から降りてくる**。`have hBcard := …` と
自分で書くと `Semiring (ZMod p)` への経路が別になり `finrank_eq_one_of_card_eq_prime` 経由で
食い違う ([[lean-instance-defeq-traps]])。試行は revert 済、tree green。

### ⟹ 正しい設計: generic 側で束ねる

S11 の証明本体 (`refine … ?_ ?_` + `intro u hscal` + 80 行) を**そのまま保ち**、
generic 側に 2 つの結論を同時に返す補題を置く:

```lean
theorem blockScalarFacts_of_blocks (ρ) (B) (hBcard)
    (hcard : ∀ i, Nat.card (range φ_i) = Nat.card (range φ_0))
    (hconst : …) :
    (∃ ψ : U →* (Fin n → (ZMod p)ˣ), Function.Injective ψ)
      ∧ Nat.card U ∣ Nat.card (range φ_0) ^ n
      ∧ Nat.card (range φ_0) ∣ p - 1
```

こうすれば S11 側は `refine blockScalarFacts_of_blocks … ?_ ?_` となり、`hcard` と `hconst`
の**両方の目標が signature から完全に elaborate された形で降りてくる**ので diamond が起きない。
`hcard` の目標は `ker (lineScalarChar (B i)) = ptStabOfMulAut Ū.subtype (Hpart i)` を経由して
`Subgroup.index_ptStabOfMulAut_subtype_smul` + `range_uActionHom_conj_mem` で閉じる
(すべて landed 済)。

---

# ✅ 完了 (2026-07-27)

## 到達点

```lean
theorem OddOrder.Peterfalvi.S11.caseA_blockScalarFacts … :
    (∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ), Function.Injective ψ)
      ∧ ∃ a : ℕ, a ∣ chief.p - 1 ∧ chars.u ∣ a ^ (data.q - 1)
```

第 2 結論が**書籍 p.51 の (9.7)(a) そのもの** — 「`a = |U : C_U(H₁)|` は `p − 1` を割り、
`U` は位数 `a` の巡回群 `q − 1` 個の直積の部分群と同型」。repo はこれまで粗い
`u ∣ (p−1)^{q−1}` 形しか持っていなかった。

既存の `caseA_exists_blockScalarRatioEmbedding` は `.1` の射影として残したので**下流は不変**。

## 証明の筋 (書籍どおり)

1. ブロックは `W₁`-移動 `Hpart j = w_j • S₀` (`caseA.Hpart_orbit`)
2. `w_j` は `Ū` を正規化する (`range_uActionHom_conj_mem`; `uActionHom` は
   `quotientMulAutHom` の `U` への制限 + `U ⊴ U W₁`)
3. ⟹ 各点固定化群 `C_Ū(Hpart j)` が `Ū`-共役 ⟹ **指数一致**
   (`Subgroup.index_ptStabOfMulAut_subtype_smul`)
4. `ker (lineScalarChar (block)) = C_Ū(block)` (`ker_lineScalarChar_aInvariantSubrep`) と
   `|im φ| = |Ū : ker φ|` ⟹ ブロックスカラー像の**位数一致**
5. `𝔽_p^×` は巡回ゆえ位数一致 ⟹ **像そのものが一致**
   (`Subgroup.eq_of_card_eq_of_isCyclic`)
6. ⟹ ratio embedding が `(位数 a の巡回群)^{q−1}` に落ちる
   (`card_dvd_blockScalarRange_pow_of_blocks_card_eq`)

## 途中で当たった罠と回避

`hconst` (§9 の crux、80 行) を呼び出し側の `have` に hoist すると、`Semiring (ZMod p)` への
instance 経路が `CommRing` 経由と `Field` 経由に割れて `Representation` の型が食い違う
([[lean-instance-defeq-traps]])。⟹ **generic 側で 2 結論を束ねる**
(`blockScalarFacts_of_blocks`) ことで、S11 の証明本体を保ったまま全目標の型を signature から
降ろす設計にした。

## 新規追加 (すべて axiom-clean)

| 場所 | 定理 |
|---|---|
| `Mathlib/CyclicSubgroupUnique.lean` (新設) | `eq_powMonoidHom_ker_card`, `Subgroup.eq_of_card_eq_of_isCyclic` |
| `Mathlib/Subgroup.lean` | `ptStabOfMulAut`, `ptStabOfMulAut_smul`, `index_ptStabOfMulAut_smul`, `index_ptStabOfMulAut_subtype_smul` |
| `RepresentationTheory/LineScalarCharacter.lean` | `lineScalarChar_comp_of_equivariant`, `lineScalarChar_range_eq_of_equivariant` |
| `RepresentationTheory/AInvariantSubrep.lean` | `ker_lineScalarChar_aInvariantSubrep` |
| `RepresentationTheory/TypePGaloisUBound.lean` | `card_dvd_blockScalarOrder_pow_of_blocks`, `card_dvd_blockScalarRange_pow_of_blocks{,_card_eq}`, `card_lineScalarChar_range_eq_index`, `lineScalarChar_ker_eq`, `blockScalarFacts_of_blocks` |
| `Peterfalvi/S11_ImprimitiveUBound.lean` | `range_uActionHom_conj_mem{,_inv}`, `caseA_blockScalarFacts` |

フルビルド green (4799 jobs)、AxiomsCheck OK、`--strict` 警告ゼロ、sorry 非退行。
