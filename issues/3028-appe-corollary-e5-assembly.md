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
