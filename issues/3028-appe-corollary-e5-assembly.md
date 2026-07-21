---
id: 3028
slug: appe-corollary-e5-assembly
title: "BG Cor E.5 組立 — (E.29)-(E.32) + (ii)∧hdc⟹(i) + §14 counting"
created: 2026-07-21
---

# BG Cor E.5 組立 — (E.29)-(E.32) + (ii)∧hdc⟹(i) + §14 counting

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

corrected E.4 landing (issues 3021/9402, commits 3b89360e3/2e6b7829c) により App.E の残る
主結果 = **Cor E.5** のみ (`AppE_FurtherResults.lean:1685` の sorry、halt は
`(i) ∨ ((ii) ∧ hdc)` に改訂済)。原文 = BG pp. 164-166 (pdftotext L8278-)。
⚠ p.166 の最終 counting display は pdftotext が OCR 崩れ → **PDF ページ画像で確定すること**。

## 前提の形式化状況 (2026-07-21 実測、全て sorry-free)

- Cor 15.9 = `centralizer_escape_final_local` (S16_MainResults/TaxonomyOutput.lean:688) —
  結論 = IsTypeF M ∧ ¬FittingIsTI M ∧ IsTypeP2 N ∧ (cyclic E, Frobenius M = M_σ ⋊ E)
- Prop 16.1 taxonomy = TaxonomyOutput.lean (S16 全体 sorry-free)
- Thm 12.7 = S12_Theorem127.lean (a)(b)(c)(e)
- Prop 3.9 = Ch1_Preliminary/S03g_Thm310.lean:44
- Lemma 14.5(a)(b)(c) = Conjugacy145C.lean (`xRsub_disjoint`/`Mtilde_disjoint`) +
  SigmaLengthOne.lean (`sigmaSaturation_Rsub_count`)
- Thm 14.7 = TypePDuality.lean (全 clause 群) / Prop 14.2 = Basics/TypePDuality
- E.3 = AppE_{RegularOperator,ExponentP,SemidirectFrattini} / corrected E.4 = AppE_PropE4

⟹ **E.5 は ungated な純組立** (ただし multi-session 級)。

## WP 分解 (上流優先)

1. **WP1 (E.29)/(E.30)**: 15.9 証明内部 (`signalizer_structure_of_mem_sigmaSharp` 系) から
   C_{N_σ}(x) > 1 / M∩N が N_σ の complement / |K₁| prime / R ≤ U₁ (abelian normal
   complement to K₁ in M∩N) を抽出・補題化。R = O_p(M)∩N = C_{O_p(M)}(x)。
2. **WP2 (E.31)/(E.32)**: Thm 12.7 + (E.30) → R₀ = O_p(F(N)) ⊴ N, |R₀| = p,
   R = R₀ × (R∩E₀); Prop 3.9 → R∩E₀ cyclic; (E.32) ⟨x⟩ = C_R(N_σ) = R₀, K₁ ⊴ R₀ 正規化。
3. **WP3 setup 実体化**: `RegularOperatorSetup (O_p(M)) E p |K₁|` を構成 (A := K₁ 像,
   act := conjugation, R₀ := ⟨x⟩, regularity = Frobenius complement の fpf)。
4. **WP4 (ii)∧hdc ⟹ (i)**: E.3 → S = Ω₁(O_p(M)) exponent p; (ii) → |S| ≥ p⁴;
   corrected E.4 の対偶 ((ii) は T = C_S(Z₂(S)) char・abelian・index p の存在と矛盾) →
   E が R₀ を固定 → E = K₁ → |M/M'| = |E| = |K₁| prime。hdc は (ii) 側 conjunct から供給。
5. **WP5 §14 counting**: (E.33) = 14.5、(E.34) = 14.7(e)(a) + short argument、
   4 族の 𝒱_G 和 > |G| で矛盾。display は PDF p.166 画像で確定してから。

## leaf 方針

新 leaf `OddOrder/BG/AppE_CorollaryE5.lean` (import: AppE_PropE4 + S14/S16 hub)。
E.4 と同じパターン: 完成時に AppE_FurtherResults の sorried statement を削除し
「下流で証明」コメントに置換。新 leaf は同 commit で OddOrder.lean に配線。

## 2026-07-21 WP1 ✅ + WP2 設計確定 (lane c)

**WP1 landed**: `e5_neighbour_data` (`AppE_CorollaryE5.lean`, commit 3f3d70d88, sorry-free)。
(E.29) bundle = TypeP2 N / C_{N_σ}(x)≠⊥ / complement / K₁ (素数位数 Hall κ(N)) /
U₁ = E₂⊔E₃ (abelian Hall (κ∪σ)ᶜ、K₁ 正規化、≠⊥)。

**原文確定 (PDF p.165 = PDF page 178、画像読了)**:
- (E.30) `R = O_p(M) ∩ (M∩N) = O_p(M) ∩ N = C_{O_p(M)}(x)`
- (E.31) `R₀ = O_p(F(N)) ⊴ N, |R₀| = p, C_{O_p(M)}(x) = R = R₀ × (R∩E₀)` (E₀ = R₀ の
  complement in M∩N)、R∩E₀ regular on N_σ → Prop 3.9 で cyclic
- (E.32) `⟨x⟩ = C_R(N_σ) = R₀ ⊴ N`、K₁ が R₀ 正規化
- (ii)⟹(i): "p ∈ τ₂(M)" と印刷されているが **τ₂(N) と読む** (x ∈ M_σ ⟹ p ∈ σ(M)、
  τ₂(M)∩σ(M)=∅ で矛盾; signalizer の hxtau2' が p ∈ τ₂(N) を供給、r(R)=2 はここから)
- (E.33) `|𝒞_G(L̃)| = (|L_σ|−1)|G:L| = |G|(1/|L:L_σ| − 1/|L|)`、nonconjugate L で disjoint
- (E.34) `|𝒞_G(Ẑ)| = (1 − 1/k − 1/k* + 1/(kk*))|G|` (Ẑ = K₁K* − K₁∪K*, K* = C_{N_σ}(K₁),
  k=|K₁|, k*=|K*|)、𝒞_G(L̃) と disjoint

**(E.30) の "Hence" の実内容 (形式化ルート確定)**:
1. `M∩N = K₁ ⊔ U₁`: `subgroupE_basic hG hsetup` の `E = E₁ ⊔ E₂ ⊔ E₃` (TheoremsAE.lean:1034
   の内部 have と同じ projection `.2.2.2.2.1.1`) + sup_assoc。
2. `U₁ ⊴ M∩N`: K₁ ≤ N(U₁) (hK₀NU₀) + U₁ ≤ N(U₁) → sup ≤ normalizer。
3. **absorption** `P ≤ U₁` (P = O_p(M)∩N, p ∈ (κ∪σ)ᶜ(N)): 商論法 — M∩N/U₁ は K₁ の像で
   生成 = κ-群; P の像は (κ∪σ)ᶜ-群かつ κ-群 → trivial → P ≤ U₁ (~15 行、generic 化候補)。
   p ∈ (κ∪σ)ᶜ(N) は 15.9 の hrκσ'N ブロック (r := p, τ₂→∉σ, τ₂≠τ₁,τ₃→∉κ) を replay。
4. `x ∈ O_p(M)`: 15.9 の Frobenius 構造 (M = M_σ ⋊ E) + `frobeniusKernelIsNilpotent`
   (BG Thm 3.7) → M_σ nilpotent → x (p-元) ∈ O_p(M_σ) ≤ O_p(M)。
   ⚠ `Msigma_isNilpotent` (S11:708) は Hypothesis111 が要るので使わない。
   O_p(M_σ) ≤ opiCoreInG {p} M の橋: O_p(M_σ) char M_σ ⊴ M → normal p-subgroup ≤ O_p(M)。
5. (E.30) ⊆ 側: u ∈ O_p(M)∩N → u ∈ U₁ (3.) かつ x ∈ O_p(M)∩N ≤ U₁ (4. + x∈C(x)≤N) →
   U₁ abelian → u ∈ C(x)。⊇ 側: C(x) ≤ N (signalizer) で自明。
6. Sylow-ness `O_p(M)∩N = Hall {p} (M∩N)` は必要になった時点で
   (`piSubgroup_le_opiCoreInG_of_isHall` 系 + O_p(M) が M の Sylow p — M_σ nilpotent +
   p ∈ σ(M) + E が σ'-群)。

**次段 (WP2 実装)**: 上記 1-5 を `AppE_CorollaryE5.lean` に実装 ((E.30) lemma)。その後
(E.31) = Thm 12.7 (S12_Theorem127.lean) の該当 clause 適用、(E.32)、WP3 の setup 構成。
