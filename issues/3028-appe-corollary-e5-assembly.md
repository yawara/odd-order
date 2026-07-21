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

## 2026-07-21 WP2 ✅ + ⚠ 新規上流 prerequisite 発見: **Cor 15.9(c) が未形式化** (WP2.5)

**WP2 landed** (commits 712b60cbe / b8c6cd0ce、全 sorry-free):
- `mem_opiCoreInG_singleton_of_nilpotent` (p-元の O_p 吸収、W = M_σ 用)
- `e5_neighbour_data` に `M ⊓ N = K₁ ⊔ U₁` conjunct 追加
- `mem_kappa_sigma_compl_of_mem_tau2` / `le_of_isPGroup_of_not_dvd_relIndex` (generic)
- `e5_R_eq_centralizer` = **BG (E.30)** ✅

**⚠ WP3 の前に必要な新規上流 (WP2.5)**: E.5 冒頭の (E.28) recap
`|E∩N| = |N/N'|, N_E(⟨x⟩) ⊆ E∩N, N ∈ ℳ_𝒫₂, p ∈ τ₂(N)` (PDF p.164 = page 177 画像確認) は
**BG Cor 15.9(c)** (printed: "for a suitable choice of a complement E to M_σ in M ...
(c) r ∈ τ₂(N), N_E(⟨x_r⟩) ⊆ E∩N, and |E∩N| = |N/N'|")。repo の
`centralizer_escape_final_local` は **(a)(b) のみ** (TaxonomyOutput.lean:666- の докstring
明記; Coq `nonFtype_signalizer_base` BGsection15.v:1399 も (a)(b))。
⚠ 2026-07-07 に「N_G(⟨x⟩) ≤ E⊓N」版 conjunct が unsound として削除された経緯あり (issue
9017 #19) — sound な (c) は **N_E** (E 内正規化群) かつ **suitable E** (E の再選択が入る)。

- (c) の用途: WP3 の A := K₁ ≤ E 整列と WP4 終端の「E = K₁」比較。構造的に必須。
- BG の (c) 証明 = 15.9 証明後半 (15.4)-(15.5)... (§16 側、pdftotext L6391-)。R = Sylow r
  of M∩N (= N の Sylow r でもある) を経由して E を再選択。
- Coq 側の対応物確認が次の一手: BGsection15/16 で Feit–Thompson (1991) clause (c) 相当
  (`FT_signalizer` 系 / `nonFtype_signalizer` 続き) を grep。
- 置き場所: S16 (TaxonomyOutput の続き or 新 sibling leaf)。lane c は §16 割当済なので
  territory 問題なし。9500 claim 不要 (App.E assembly の一部、issue 3028 で追跡)。

**改訂 WP 順**: WP2.5 (15.9(c)) → WP3 (setup 構成) → WP4 ((ii)∧hdc⟹(i)) → WP5 (counting)。

## 2026-07-21 WP2.5 設計確定 (15.9(c) 証明の完全読解、pdftotext L6415-6435 + PDF p.123)

**⭐ Coq 裁定**: BGsection15.v:1396-1398 のコメントで **Coq は (c) を意図的に drop**
("not used later" — Coq は App.E を形式化しないため)。(c) の形式化は本 repo が初。

**BG の (c) 証明の骨格** (そのまま形式化ルート):
1. (15.2) `K₁R` 非冪零 → `K₁ ⊄ M_σ` (M_σ 冪零ゆえ) → `K₁ ∩ M_σ = 1` → `|K₁| ∉ σ(M)`
   → K₁ は σ(M)'-群。(15.2) 自体 = C_R(K₁) ≤ C_{U₁}(K₁) = 1 + R ≠ 1 (rank 2) から
   「冪零群の正規部分群は中心と交わる」で矛盾させる。
2. **E の再選択**: 既存 15.9(b) の complement E₀ に Hall 共役 (`hall_D`、M solvable) を
   当て、K₁ ≤ E := E₀^m。cyclic/complement/Frobenius は共役で保存。
3. `N_G(⟨x⟩) ≤ N`: C_G(x) ≤ N_G(⟨x⟩) < G (G simple、⟨x⟩ ≠ 1)、ℳ(C_G(x)) = {N}
   (signalizer 一意性) → N_G(⟨x⟩) の入る maximal = N。
4. **`E ⊓ N = K₁`**: K₁ ≤ E∩N ≤ M∩N = K₁ ⊔ U₁; E cyclic → E∩N abelian → E∩N ≤
   C_{M∩N}(K₁) = K₁ (∵ (15.4) C_{U₁}(K₁) = 1 の分解論法)。⊇ は選択。
5. `N_E(⟨x⟩) ⊆ E∩N` は 3. から自明 (N_E ≤ E ∧ ≤ N_G(⟨x⟩) ≤ N)。
6. `|E∩N| = |N/N'|` は **E.5 では省略可** (WP4 は E∩N = K₁ だけ消費; counting は k = |K₁|
   を直接使う)。Lean statement には入れない (必要になれば別途)。

**⭐ WP4 への波及**: E.4 対偶で E が R₀ = ⟨x⟩ を固定 → E ≤ N_G(⟨x⟩) ≤ N →
E = E∩N = K₁ → |M/M'| = |E| = |K₁| prime が即納 ((i) 完成)。

**要部品 (現状)**:
- (15.4) `C_{U₁}(K₁) = ⊥`: BG Prop 14.2(g) 由来。repo 形式化の所在は次 iteration で
  実測 (候補: S14 Basics/ElemAbelianNeighbor の 14.2(g) 群、または typeP2 系から再導出)。
- `hall_D` (Isaacs Ch3 Basic.lean:1682) = K₁ を含む Hall σ' の存在 ✓
- Frobenius 構造の共役輸送 (IsFrobeniusGroup + IsComplement' の MulAut.conj 版) — 既存
  API を確認、無ければ小補題。
- 置き場所: `AppE_CorollaryE5.lean` 内 (`e5_exists_suitable_complement`)。S16 の
  centralizer_escape_final_local は変更しない (出力を消費するだけ)。

**statement 案**:
```
theorem e5_exists_suitable_complement ... (K₁ 側仮説 + 15.9 出力仮説) :
  ∃ E : Subgroup G, E ≤ M ∧ IsComplement' ((Msigma M).subgroupOf M) (E.subgroupOf M) ∧
    IsCyclic ↥E ∧ IsFrobeniusGroup ↥M ((Msigma M).subgroupOf M) (E.subgroupOf M) ∧
    K₁ ≤ E ∧ E ⊓ N = K₁
```

## 2026-07-21 WP2.5 ✅ (commits 7feb5c372 / 1d9243637、全 sorry-free)

- `inf_eq_kappaHall_of_le_cyclic`: E∩N = K₁ collapse (Commute API + mul_normal 分解 +
  Thm A(4) C_{U₁}(k₀) = ⊥)。
- `e5_exists_suitable_complement`: Hall 共役 (hall_D/hall_C) で E を K₁ ⊇ に再選択、
  complement/cyclic/Frobenius を共役輸送 (isFrobeniusGroup_map_equiv + Mσ' conj 不変)。
- ⟹ **BG Cor 15.9(c) 完全形式化** (初機械化)。

### 次 = WP3 入力の残り導出

1. `hK₁σ'` (K₁ が σ(M)'-群): K₁ ⊓ M_σ = ⊥ 経由 — 冪零 M_σ 内 coprime-order 可換
   (x ∈ U₁ ⊓ C(k₀) = ⊥ 矛盾、issue 記載済ルート)。|K₁| ≠ p は p ∉ κ(N) から。
2. Thm A(4) 適用形: `typeP_hall_inf_centralizer_kappaElement_eq_bot` (KappaHallCommutator:856)
   を N に適用 (IsCyclic ↥K₁ は |K₁| prime から)。inf_eq_kappaHall の hCU₁ 供給元。
3. (E.31)/(E.32): Thm 12.7(b)(e) を N の esetup で適用 (canonical line A₀ = R₀ = ⟨x⟩)。
   WP3 setup フィールド (R₀_card/R₁_cyclic/centralizer_eq/A_fixes_R₀/A_regular) の供給源。
4. WP4 短縮確認済: E.4 対偶 → E ≤ N_G(⟨x⟩) ≤ N → E = E∩N = K₁ → |M/M'| = |E| prime。

## 2026-07-21 WP3 入力ほぼ完備 (commits 65fbe8c49 / 309f148f9 / a6a2117ea / 18227e575)

- `commute_of_orderOf_prime_ne` (generic 冪零 coprime-commute) + `e5_kappaHall_inf_Msigma_eq_bot`
- `e5_kappaHall_pi_sigma_compl` (hK₁σ' glue)
- `e5_opiCore_sylow_card` / `e5_exists_sylow_eq_opiCore` (**O_p(M) = Sylow p of G**)
- `e5_zpowers_eq_canonical_line` (**(E.32) 核**: ⟨x⟩ = A₀、N ≤ N_G(⟨x⟩)、N_σ ≤ C_G(⟨x⟩))

全 sorry-free。**WP3 setup 残り**: (E.31) 後半 — C_{O_p(M)}(x) = R₀ × (R∩E₀) 分解と
R∩E₀ cyclic (Prop 3.9、regular on N_σ)。これが setup の R₁/centralizer_eq/R₀_disjoint_R₁
を供給。その後 act (E の conj 作用の MulAut 化)・A := K₁ 像・p_not_dvd_card_B (E は
σ(M)'-群 + p ∈ σ(M))・A_regular (Frobenius fpf) を束ねて RegularOperatorSetup 構成。

## 2026-07-21 (E.31) ルート確定 (iteration 15 調査)

**BG Thm 12.7 の全 clause 形式化済みと確認** — (d) = `exists_complement_of_canonical_line`
(S12_Theorem127d.lean:164; E₀ ≤ E, A₀ ⊓ E₀ = ⊥, A₀ ⊔ E₀ = E)。(E.31) の形式化ルート:

1. E₀ := 12.7(d) を N-esetup に適用 (hMnorm = 12.7(b) の N ≤ N_G(A₀)、hprime_eq = 12.7(a))。
2. **R = A₀ ⊔ (R ⊓ E₀)** (R := O_p(M) ⊓ N = C_{O_p}(x)、A₀ = ⟨x⟩): A₀ ⊴-in-E
   (E = M∩N ≤ N ≤ N_G(A₀)) → mul_normal で set 積分解 (inf_eq_kappaHall と同型の論法)。
   disjoint: A₀ ⊓ (R∩E₀) ≤ A₀ ⊓ E₀ = ⊥。
3. **R∩E₀ regular on N_σ**: y ∈ (R∩E₀)^# の p-冪位数 → order-p 元 y' ∈ ⟨y⟩ ≤ E₀、
   ⟨y'⟩ ≠ A₀ (E₀ ⊓ A₀ = ⊥) → 12.7(c) 二分律 hdich → C_{N_σ}(⟨y'⟩) = ⊥ → C_{N_σ}(y) = ⊥。
4. **cyclic**: Prop 3.9 = `isCyclic_of_isPGroup_of_isFrobeniusAction` (S03g_Thm310.lean:55、
   conj 作用の MulDistribMulAction 化 + IsFrobeniusAction; 適用例 = S12_Theorem1212b.lean:224)。
   Nontrivial N_σ = Msigma_ne_bot。p odd = |G| odd。
5. **R₁ ≠ ⊥**: R は N の Sylow p (p-part 一致、p ∉ σ(N)) + pRank N p = 2 (τ₂) →
   R noncyclic (pRank_eq_of_le_of_not_dvd_index で rank 転送) → R ⊋ A₀。

setup フィールド対応: centralizer_eq = 2 (subgroupOf ↥O_p 化)、R₁_cyclic = 4、
R₀_disjoint_R₁ = 2、R₁_ne_bot = 5。

## 2026-07-21 WP3 ✅ + WP4 前半 ✅ (commits f3047221c / a5f5b90bf / 3e4ac514e / 7a2496198 / 3e9d5856b)

- `e5_centralizer_decomposition` = **(E.31)** ✅ (12.7(d) E₀ + mul_normal 分解 + 12.7(c)
  regular + Prop 3.9 cyclic)
- `e5Setup` = **RegularOperatorSetup (O_p(M), K₁, E) 構成** ✅ (term-mode structure literal、
  ⚠ tactic-def だと data 射影が簡約せず E.4 適用不能 — refactor 済、rfl 射影補題付き)
- `exists_normal_abelian_index_prime_of_card_le_cube` = WP4(a) (|S| ≤ p³ は (ii) 違反)
- `e5_normal_abelian_of_not_fixes` = **WP4(b1)**: corrected E.4 が e5Setup に発火、
  ¬fixes → (ii) 否定の witness (T = C_S(Z₂S) char→normal)

**残 WP4(b2)**: (ii)∧hdc ⟹ (i) 最終束ね — hcard4 (WP4(a) 対偶) → by_contra で b1 →
∀b fixes → E ≤ N_G(⟨x⟩) ≤ N (hNxN は仮説、最終組立で ℳ(C_G(x))={N} + G simple から) →
E = E⊓N = K₁ → derivedInG M = M_σ (Msigma_le_derived + M⧸Mσ' card k prime cyclic abelian
→ commutator ≤ Mσ') → index = k prime。
**残 WP5**: counting (E.33)/(E.34) — 新 sibling leaf に置く (本 leaf 1137 行)。

## 2026-07-21 ⭐⭐ WP4 完了 (commit 82c8d9451) — (ii)∧hdc ⟹ (i) 完全証明

`e5_card_omega_ge_of_ii` + `e5_derived_index_eq_of_ii_hdc` (全 sorry-free)。
corrected E.4 対偶 → E fixes ⟨x⟩ → E = E⊓N = K₁ → M' = M_σ → index = k prime。
leaf は 1290 行 — **WP5 は新 sibling leaf** (`AppE_E5Counting.lean` 予定) に置く。

### 残 WP5 の構成
1. **最終組立 glue**: E.5 仮説ブロック → e5_derived_index の全仮説導出
   (e5_neighbour_data / e5_R_eq_centralizer / e5_kappaHall_* / e5_opiCore_sylow /
   e5_zpowers_eq_canonical_line / e5_centralizer_decomposition / suitable complement を連鎖;
   新規 = hNxN: N_G(⟨x⟩) ≤ N — C_G(x) ≤ N_G(⟨x⟩) < G (G simple、zpowers ≠ ⊤) +
   ℳ(C_G(x)) = {N}; hMσnil: 15.9 の Frobenius kernel + isNilpotent 転送; p ∈ τ₂(N) は
   hxtau2' から orderOf x = p で単素数化; hRnoncyc: R = O_p⊓N Sylow-p-of-N + pRank 2)。
2. **(E.33)/(E.34) counting**: Lemma 14.5/14.7 ベース、Ẑ = K₁K* − K₁∪K*、4 族の
   𝒞_G 和 > |G| 矛盾。PDF p.166 の s-display は OCR 崩れ → 画像確認済み分 (E.33)(E.34) +
   最終不等式は p.166 パラグラフを PDF で精読してから。
3. E.5 statement (AppE_FurtherResults:1685 sorried) を新 leaf の証明で置換 (E.4 パターン:
   FurtherResults 側は削除+コメント、または sorried のまま新 leaf で本体)。

## 2026-07-21 WP5 glue 調査 (iteration 22): hMσnil の供給経路

⚠ `frobeniusKernelIsNilpotent` (BG Thm 3.7) は**素数位数 complement 限定** — E は cyclic だが
素数位数とは限らないため直接不適。`Msigma_nilpotent_of_tau2` は p ∈ τ₂(M) 前提で不適
(E.5 の M は p ∈ σ(M))。候補経路:
1. **Prop 16.1 の TypeIData 経由**: 15.9 → IsTypeF M → (Prop 16.1 taxonomy) TypeIData M。
   `TypeIData.typeF : TypeFData M` の H (= M_F) の nilpotency フィールド + H = M_σ 同定
   (TypeF は M_F = M_σ; 対応 lemma を TaxonomyOutput/TypeBridges で探す)。
2. 15.9 内部の "M_σ nilpotent" 導出 (Cor 14.12 = typeP2_neighbor_is_typeF 系) の再利用 —
   nilpotency を conclusion に持つ public lemma があるか TheoremsAE を精査。
3. hNxN 用部品は確定済: centralizer_zpowers_eq_singleton'.symm + mathlib
   `Subgroup.centralizer_le_normalizer` + G simple (zpowers ≠ ⊤: cyclic→solvable→notSolvable
   矛盾) + ℳ(C_G(x)) = {N}。
4. hRnoncyc: R = O_p⊓N は N の Sylow p (p-part: |N| = |N_σ|·|M∩N|、p ∤ |N_σ|) +
   pRank N p = 2 (τ₂) + pRank 転送 (pRank_eq_of_le_of_not_dvd_index) → rank 2 → noncyclic
   (rank ≥ 2 → ¬cyclic: 対応 lemma 要確認、tau1_pRank_eq_one の逆向き系)。

WP5 glue は新 leaf `AppE_E5Counting.lean` 予定 (未作成 — 実体ができる iteration で作成+配線)。
