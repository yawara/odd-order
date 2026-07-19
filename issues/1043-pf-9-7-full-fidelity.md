---
id: 1043
slug: pf-9-7-full-fidelity
title: "(9.7) の完全形式化: (a) order-a 巡回埋め込み / (b) W₁ ≅ Aut F 節"
created: 2026-07-19
---

# (9.7) の完全形式化: (a) order-a 巡回埋め込み / (b) W₁ ≅ Aut F 節

frontier_measured_2026_07_19.md §9 行の狭さ 2 点の解消。書籍 statement は PDF p.51-52 で
確定済 (2026-07-19):

> **(9.7)** One of the following two cases holds.
> **(a)** H̄ is the direct product of q groups H_i (1 ≤ i ≤ q) of order p normalized by U;
> moreover {H_i} = {H₁^w | w ∈ W₁}. Let a = |U : C_U(H₁)|. Then a ∣ p − 1, U/C_U(H_i) is
> **cyclic of order a** for all i, and Ū is isomorphic to a subgroup of the direct product of
> **q − 1 cyclic groups of order a**.
> **(b)** U acts irreducibly on H̄. There is a field F of cardinality p^q and a subgroup U* of
> F* such that **(H̄ ⋊ Ū) ⋊ W₁ ≅ (F ⋊ U*) ⋊ (Aut F)** (H̄ ↔ F additive, Ū ↔ U*, W₁ ↔ Aut F)。
> Furthermore Ū is cyclic, and **u ⊥ (p − 1) and u ∣ (p^q − 1)/(p − 1)**.

## 現状 (実測 2026-07-19)

- 二分岐 `clifford_dichotomy` (CuS0.lean:1811) は axiom-clean。
- `CliffordCaseAData` (ChiefFactorCore.lean:1222) は既に **S0 (orbit 生成元) + orbitRep +
  Hpart_orbit (UW₁-移動性) + a (= |range aInvariantRestrictAut S0|, a_dvd_p_sub_one)** を保持。
- (a) の埋め込み `caseA_exists_blockScalarRatioEmbedding` (S11_ImprimitiveUBound.lean:265) は
  codomain `Fin (q−1) → (ZMod p)ˣ` — order-a 情報を落としている ((14.6) が必要とする形でない)。
- (b) は `caseB_exists_galoisField_repr` (S11_GaloisFieldModel.lean:31) = (e : H̄ ≃+ GF(p^q),
  μ : Ū ↪ GF(p^q)ˣ, compat) まで。**W₁ 側 (η : W₁ ≅ Aut F) は皆無**。
- **✅ 2026-07-19: 抽象層の order-a 強化を先行 land** —
  `exists_blockScalarRatioEmbedding_of_blocks_pow_eq_one`
  (OddOrder/GroupTheory/RepresentationTheory/TypePGaloisUBound.lean)。
  hpow (全 block scalar char が a-torsion) から `∀ u i, (ψ u i)^a = 1` 付き埋め込み。

## 進捗

- **✅ 2026-07-19 (a) 完了** (S11_ImprimitiveUBound.lean、全宣言 axiom-clean):
  - step 1: `lineScalarChar_aInvariantSubrep_ker_eq` + `card_range_lineScalarChar_aInvariantSubrep`
    (kernel 一致 → 第一同型定理で像位数一致)
  - step 2: `caseA_card_range_restrictAut_Hpart` (書籍「|U/C_U(H_i)| = a for all i」;
    MulAut.conjNormal 共役で kernel cardinality 不変)
  - step 3: `caseA_pow_a_eq_one` (**exp(Ū) ∣ a** — 各 block scalar が a-torsion → u^a が
    全 summand 固定 → span + 忠実性で u^a = 1) +
    `caseA_exists_blockScalarRatioEmbedding_orderA` (order-a 埋め込み本体; 既存 crux を
    複製せず exponent 経由で導出)
  - 残る (a) の小片: 「U/C_U(H_i) は **cyclic** of order a」の cyclic 側の明示
    (MulAut(位数 p 巡回群) が巡回 ⟹ 部分群巡回; 位数 = a は step 2 で済)。

## (a) 残り: concrete bridge (S11 側)

1. **S0-block の scalar char 像の位数 = a**: `a_eq_card_restrictAut_range` (a = |range
   (aInvariantRestrictAut S0_aInvariant)|) と `lineScalarChar` の range card を橋渡し。
   位数 p の部分群上で MulAut ↥S0 ≅ (ZMod p)ˣ と scalar 作用の対応 (LineScalarCharacter.lean
   に `lineScalarChar_injective` 系あり — range card 一致 lemma を足す)。
2. **全 block への transport**: `Hpart_orbit : Hpart j = φ(orbitRep j) • S0` の共役で
   作用が intertwine (orbitRep j ∈ U ⊔ W₁、U ⊴ UW₁ ゆえ U-作用が U-作用に移る; (9.8.c)
   の surjectivity 工事に同型の議論があるはず — 着手時に grep してから)。像の位数不変。
3. **wire**: `caseA_exists_blockScalarRatioEmbedding_orderA` を
   `exists_blockScalarRatioEmbedding_of_blocks_pow_eq_one` 経由で。hpow は 1+2 から
   (Lagrange: 像の位数 = a ⟹ 値^a = 1)。
4. **「U/C_U(H_i) は cyclic of order a」**: cyclic = (ZMod p)ˣ の部分群 (lineScalarChar 像) と
   U/C_U(H_i) の同型 (first iso; `index_cuInHu_subgroupOf_uInHu_eq_a` が S0 版) + order a は 1+2。

## (b) η : W₁ ≅ Aut F — 書籍 p.52 の証明 (2026-07-19 に PDF p.52 で全文確定)

⚠ この節の pdftotext 抽出 (`04.11_pp_50_57_*.txt`) は**文字単位でバラけていて使い物にならない**
(`( 9 . 1 )` のように 1 文字ずつ空白挿入)。**PDF ページ画像を Read するのが唯一の正本**
(章 PDF は pp.50-57 ゆえ 書籍 p.52 = PDF p.3)。

書籍の骨格 (k = 1 の場合):

> F = End_{𝔽_p[U]}(H̄) は Schur の補題で有限体。Ū 可換ゆえ ψ : Ū ≅ U* ≤ F* が
> hψ(x) = h^x で定まる。U 既約ゆえ **H̄ は F 上 1 次元**、かつ **U* が F を加法生成**。
> (9.6) より s ∈ W̄₂^# が取れる。**φ : H̄ ≃+ F を h = sφ(h) で定める** (⟹ φ(s) = 1)。
> すると φ(h^x) = φ(h)ψ(x)。w ∈ W₁ に対し η(w) を φ(h)η(w) = φ(h^w) で定める。
> h^{xw} = (h^w)^{w⁻¹xw} から (φ(h)ψ(x))η(w) = (φ(h)η(w))ψ(w⁻¹xw)。
> **h = s を代入すると φ(s) = 1 かつ s^w = s ゆえ ψ(x)η(w) = ψ(w⁻¹xw)**。
> よって全 h で (φ(h)ψ(x))η(w) = (φ(h)η(w))(ψ(x)η(w))。U* が加法生成ゆえ η(w) ∈ Aut F。
> U* ≤ F* ゆえ U* 巡回・u ∣ p^q − 1。W₁ が Ū に fpf ゆえ U* ∩ 𝔽_p = 1、
> 従って u ⊥ (p−1) かつ u ∣ (p^q−1)/(p−1)。

### 進捗

- **✅ 抽象層 (乗法性の格上げ)** — `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean`
  - `addEquiv_mul_of_mul_scalars`: 生成的スカラー集合上の乗法性 → 全乗法性
    (固定 t に対し `{t' | α (t*t') = α t * α t'}` が加法部分群)。
  - `ringEquivOfAddEquivOfMulScalars` / `ringAutHomOfAddAutHom` / `_injective`:
    `W →* RingAut F` への packaging。
    ⚠ 本 pin では `AddAut` が**加法**群ゆえ source は `Multiplicative (AddAut F)`
    (repo 既存イディオム = PRank.lean / AppC_NormSet.lean と同じ)。
- **✅ counting 段 (|Aut F| = q)** — 同ファイル
  - `ringAutMulEquivAlgAut : RingAut F ≃* (F ≃ₐ[ZMod p] F)` (素体は自動固定)。
  - `natCard_ringAut_eq_finrank` (有限体上の有限拡大は自動 Galois) →
    `natCard_ringAut_galoisField : Nat.card (RingAut (GaloisField p q)) = q`。
  - ⚠ 同型の橋が Suzuki 付録の証明内に `let` で埋まっていた → dedup issue **9164**。
- **✅ base point 正規化** — `S11_GaloisFieldModel.lean`
  - `exists_normalized_of_scalar_model` (抽象層; M には `Add` しか要求しない)。
  - `caseB_exists_galoisField_repr_basePoint`: compat を保ったまま `e (ofMul s) = 1` を追加。
    s ≠ 1 なら任意 — W₁-固定な s の供給は呼び出し側。

### 残り (着手順)

1. **s ∈ W̄₂^# の供給**: `C_{H̄}(W₁)` は repo では `act.fixedByE`
   (`act = typeP_quotientCoprimeAction …`, `WielandtSetup.lean:726`)。
   `coprimeFrobeniusChiefFactor_card` (`WielandtSetup.lean:766`) の第 2 成分が
   `Nat.card ↥act.fixedByE = chief.p` を与えるので、`Subgroup.exists_ne_one` で
   s ≠ 1 を取り、**s が W₁-固定** (fixedSubgroup の定義) を同時に持ち出す。
2. **U* の加法生成**: `AddSubgroup.closure (μ '' univ) = ⊤`。
   μ-像は乗法閉ゆえ加法閉包は U*-安定 (`AddSubgroup.closure_induction`) で、
   標数 p ゆえ自動的に 𝔽_p-部分空間 → `caseB.actsIrreducibly` で ⊥ or ⊤、
   1 ∈ U* かつ 1 ≠ 0 ゆえ ⊤。**⚠ 既約性は H̄ 側の subgroup で述べられている**
   (`actsIrreducibly : ∀ J : Subgroup (H̄), IsAInvariant (uActionHom …) J → J = ⊥ ∨ J = ⊤`)
   ので、e で F 側の AddSubgroup に移す転送が要る。
3. **η の定義 + twist**: W₁-作用は
   `(quotientMulAutHom chief.N_aInvariant).comp (W1.subgroupOf (U ⊔ W1)).subtype`
   (**専用の名前は repo に無い** — `uActionHom` の W₁ 版を新設するのが自然)。
   twist の群版は既に `uActionHom_conjNormal` (`S11_ImprimitiveUBound.lean:~100`) にある:
   `uActionHom (conjNormal l x) = q(l) * uActionHom x * q(l)⁻¹`。
4. **組み立て**: 1-3 → `ringAutHomOfAddAutHom` → 単射 (|W̄₂| = p < p^q ゆえ W₁ は H̄ に忠実)
   → `natCard_ringAut_galoisField` で onto。
5. **系**: u ⊥ (p−1) / u ∣ (p^q−1)/(p−1)。
   ⚠ **これは `CliffordCaseBData` の既存フィールド `u_coprime_p_sub_one` /
   `u_dvd_norm_quotient` として既に仮定されている** — (9.7.b) を実証明したら
   これらを carrier の仮説から**導出**に格下げできるかを別途検討 (特殊化債務の解消)。
- **抽象層の置き場**: SingerField.lean の `exists_galoisField_repr_of_faithful_irreducible` の
  拡張として「semilinear extension lemma」(加法自己同型 + scalar-orbit 乗法性 + scalar が
  加法生成 ⟹ ring 自己同型) を `OddOrder/GroupTheory/RepresentationTheory/` の新 leaf に。

## 完了条件

(a) `caseA_exists_blockScalarRatioEmbedding_orderA` + per-block cyclic-of-order-a、
(b) η : W₁ ≃* (F ≃+* F 群) onto + u ⊥ (p−1) ∣ (p^q−1)/(p−1) が axiom-clean で land し、
frontier note §9 行が「済」になること。

## 参照

- 書籍 pp. 51-52 (04.11 PDF pages 2-3) / Coq PFsection9.v:442-484 (`psi`)
- OddOrder/GroupTheory/RepresentationTheory/TypePGaloisUBound.lean (抽象層、強化済)
- OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean / S11_GaloisFieldModel.lean /
  S11_MaximalII_III_IV/ChiefFactorCore.lean (CliffordCaseAData)
- notes/peterfalvi/frontier_measured_2026_07_19.md §9 行
