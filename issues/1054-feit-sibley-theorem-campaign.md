---
id: 1054
slug: feit-sibley-theorem-campaign
title: "FeitSibley Theorem (feit_sibley_coherence): 8 ステップ campaign 計画"
created: 2026-07-21
---

# FeitSibley Theorem (feit_sibley_coherence): 8 ステップ campaign 計画

FeitSibley.lean 最後の sorry。Peterfalvi App.IV Theorem (pp. 146–150):
**d odd ⟹ 𝒮 は Lemma 2(b) の isometry τ = Ind_H^G に関して coherent**
(`Nonempty (IsCoherent hyp.tau hyp.Sset hyp.A)`)。原文全 8 ステップを 2026-07-21 に
PDF ページ画像で全読了・確定済み (本 issue が原文構造の正本 digest)。多 session campaign。

## 原文の証明構造 (pp. 146–150, PDF 実読による確定)

**Remark (p.145 末尾)**: |𝒮(Q')| ≥ 2 — O_{2'}(Q₁) ⋊ D が odd Frobenius なので
χ ∈ 𝒮(Q') ⟹ χ̄ ∈ 𝒮(Q'), χ̄ ≠ χ。Lemma 1(b) (= `coherentEqualDegree`,
CoherenceUnion.lean:298) で 𝒮(Q') coherent (全員 degree d: Q/Q' abelian ⟹ φ linear ⟹
Ind φ の degree = d)。

**(1)** |Q₁| が 2 素数で割れる ⟹ 𝒮(S') coherent。
chief factor 帰納: Q₂ ⊆ [Q₁,Q₁], Q₂ ⊴ H, 𝒮(S'Q₂) coherent と仮定 (Q₂ minimal に取れば
Q₂ = 1 で結論)、Q₃ ⊴ Q₂ で Q₂/Q₃ chief factor of H。𝒮(S'Q₃) not coherent なら
Lemma 1(a) で ψ ∈ 𝒮(S'Q₃): Σ_{χ∈𝒮(S'Q₂)} χ(1)² ≤ 2dψ(1)。
LHS = |H/S'Q₂| − |H/S'Q₁| = d|S/S'|(|Q₁/Q₂|−1) (**度数二乗和 = 指数差** counting、
要新補題)。(1.1): |Q₁/Q₂|−1 ≤ 2ψ(1)。Z/Q₃ := Z(Q₁/Q₃)、ψ(1) = dφ(1),
φ ∈ Irr(Q/S'Q₃), [Is] Cor 2.30 (= `exists_degree_sq_le_index`,
SchurCenterBound.lean:194) で φ(1)² ≤ |Q/SZ|: (1.2) ψ(1)² ≤ d²|Q₁/Z|。
Q₁ nilpotent ⟹ (Q₂/Q₃)∩(Z/Q₃) ≠ 1、chief ⟹ Q₂ ⊆ Z、2 素数 ⟹ Q₂ ⊊ Z。
(1.1)+(1.2): |Z/Q₂|(|Q₁/Q₂|−2) < 4d²。f.p.f. ⟹ |Z/Q₂| ≥ d+1, |Q₁/Q₂| ≥ (d+1)²
⟹ (d+1)²−2 < 4d ⟹ d ≤ 2 矛盾。

**(2)** 𝒮(S') coherent ⟹ 𝒮 coherent。S' ≠ 1 と仮定してよい。(1) 同型の帰納を S 側:
S₁ ⊆ S', S₁ ⊴ H, 𝒮(S₁) coherent、S₂ ⊴ S₁ chief factor S₁/S₂。not coherent なら
d|S/S₁|(|Q₁|−1) = Σ_{𝒮(S₁)} χ(1)² ≤ 2dψ(1)。Z/S₂ := Z(S/S₂)、S₁ ⊆ Z (S nilpotent)、
ψ(1) = dφ(1), φ(1)² ≤ |S/Z|·|Q₁/Z(Q₁)| ≤ |S/S₁|·|Q₁/Z(Q₁)|
⟹ |S/S₁|·|Z(Q₁)|(|Q₁|−2) < 4d²。**d odd** + f.p.f. ⟹ |Z(Q₁)| ≥ 2d+1
⟹ |S/S₁| < 4d²/(4d²−1) < 2 矛盾。

**還元宣言**: (1)(2) より以後 **Q₁ は non-abelian p-群, p 奇素数** と仮定。
⚠ ここが 2(c) の `Odd |Q₁|` 仮定の充足点 (issue 1053)。abelian Q₁ / d even の場合は
p.150 末尾 Remark (別掲、|𝒮| ≥ 2 条件付き)。

**(3)** 1 ≠ Z ⊴ H, Z ⊆ Z(Q₁) ⟹ 𝒳 = 𝒮 − 𝒮(Z) coherent。
まず 𝒳₁ = 𝒳 ∩ 𝒮(S') coherent: |𝒳₁| ≥ 2 (Z ≠ 1 + **Lemma 2(c)** で χ̄ ≠ χ)。
𝒳₁ = {χ₁,...,χ_r} 昇順。χᵢ = Ind_H(φᵢ), φᵢ ∈ Irr(S/S' × Q₁) ⟹ χᵢ(1) = d·p^{kᵢ} 形。
Σ_{1≤j<i} χⱼ(1)² = |H/S'| − |H/S'Z| − Σ_{i≤j≤r} χⱼ(1)² の両辺可除性
(LHS は d² で、RHS は φᵢ(1)² で割れる; φᵢ(1)² ≤ |Q₁/Z(Q₁)| ≤ |Q₁/Z| [Is] 2.30) から
(3.1): χᵢ(1)² ∣ Σ_{j<i} χⱼ(1)² (1 < i ≤ r)。
k := max{i : χᵢ(1) = χ₁(1)}: k ≥ 2 (2(c) で χ̄₁ ≠ χ₁ 同 degree)、{χ₁..χ_k} coherent
(Lemma 1(b))。i > k: 2χ₁(1)χᵢ(1) < pχ₁(1)χᵢ(1) ≤ χᵢ(1)² ≤ Σ_{j<i} χⱼ(1)² ⟹
Lemma 1(a) 連鎖 adjoin で 𝒳₁ coherent。
次に S' ≠ 1 のとき (2) 型帰納で 𝒳 ∩ 𝒮(S₁) → 𝒳 ∩ 𝒮(S₂): ψ = Ind_Q^H(λθ) 形,
Z ⊄ Ker θ。Ind_H(1_{S/S₂}·θ) ∈ 𝒳₁ ⟹ χ(1) ∣ ψ(1)。Lemma 1(a) で
d|S/S₁|·|Q₁/Z|(|Z|−1) ≤ 2χ₁(1)ψ(1)、χ₁(1)² ≤ d²|Q₁/Z(Q₁)| ≤ d²|Q₁/Z|,
ψ(1)² ≤ d²|S/S₁|·|Q₁/Z| (S₁/S₂ ⊆ Z(S/S₂)) ⟹ |S/S₁|(|Z|−1)² ≤ 4d²。
f.p.f. on Z ⟹ |Z| ≥ 2d+1 ⟹ |S/S₁| ≤ 1 矛盾。

**(4) Notation**: 𝒴 := 𝒮(Q') = {η₁,...,η_m} (Remark で coherent, m ≥ 2)。
Z := [Q₁,Q₁] ∩ Z(Q₁) ≠ 1 (Q₁ non-abelian p-群)。𝒳 = 𝒮 − 𝒮(Z) = {χ₁,...,χ_n} 昇順、
aᵢ := χᵢ(1)/χ₁(1) ∈ ℤ ((3) の p 冪形)。𝒳 ∩ 𝒴 = ∅。coherence witness:
Ind(χᵢ − aᵢχ₁) = eᵢ − aᵢe₁, Ind(ηⱼ − η₁) = e'ⱼ − e'₁ (eᵢ, e'ⱼ ∈ ±Irr(G))。

**(5)** ∀i,j: (eᵢ, e'ⱼ) = 0。等長性から (eᵢ−aᵢe₁, e'₂−e'₁) = 0、
λ := (eᵢ−aᵢe₁, e'₁) = (eᵢ−aᵢe₁, e'₂) ≠ 0 と仮定 ⟹ aᵢ = 1, λ = ±1,
eᵢ−e₁ = λ(e'₁+e'₂) → degree-0 で e'₁(1) = 0 矛盾。

**(6)** χ₁(1) =: ad。∃ v ∈ ℤ[Irr G], λ ∈ ℤ:
Ind(χ₁ − aη₁) = −a e'₁ + λ Σᵢ e'ᵢ + v, (v, e'ᵢ) = 0
((Ind(χ₁−aη₁), Ind(ηᵢ−η₁)) = a for i > 1 から)。
**a ∣ λ ⟹ 𝒮 coherent**: λ = ax → 1+a² = (v,v)+a²(x−1)²+(m−1)x²a² →
(x−1)²+(m−1)x² ≤ 1+1/a², a > 1 (𝒳∩𝒴=∅) ⟹ x = 0 (x=1∧m=2 は e' 符号差し替えで還元)
⟹ λ = 0, (v,v) = 1, Ind(χ₁−aη₁) = v − ae'₁ ⟹ −1 = (e₂,v)−(e₁,v) ⟹ v = e₁ or −e₂
(後者は n = 2 で符号差し替え) ⟹ Ind(χ₁−aη₁) = e₁ − ae'₁ ⟹ τ は χᵢ ↦ eᵢ, ηⱼ ↦ e'ⱼ で
𝒳 ∪ 𝒴 上一貫 (ℤ[𝒳∪𝒴]° を {χᵢ−aᵢχ₁} ∪ {ηⱼ−η₁} ∪ {χ₁−aη₁} が生成) → 𝒳∪𝒴 coherent。
仕上げ: ψ ∈ 𝒮(S') − (𝒳₁∪𝒴) を Lemma 1(a) で adjoin ((3.1) 型可除 + 2η₁(1)ψ(1) <
pη₁(1)ψ(1) ≤ ψ(1)² ≤ Σ_{𝒳₁} < Σ_{𝒳₁∪𝒴} χ(1)²) → 𝒮(S') coherent → (2) で 𝒮 coherent。

**(7)** ψ ∈ Irr(G) constant on Z^#, z ∈ Z^# ⟹ **ψ(z) ≡ ψ(1) (mod |Q|)**
(合同 = (x−y)/|Q| が代数的整数; ψ(z) ∈ ℤ は constant 性から)。
ω := central character (ω(K̂_s) = |K_s|ψ(x_s)/ψ(1))。
(7.1) ω(K̂ᵢ)ω(K̂ⱼ) = Σ_s a_{ijs}ω(K̂_s) (構造定数 K̂ᵢK̂ⱼ = Σ a_{ijs}K̂_s)。
(7.2): Kᵢ∩Z^# ≠ ∅, Kⱼ∩Z^# ≠ ∅ のとき ψ(1)ω(K̂ᵢ)ω(K̂ⱼ) ≡ Σ_{s: K_s∩Z≠∅} ψ(1)a_{ijs}ω(K̂_s):
K_s ∩ Z = ∅ の項は、Q が X := {(u,v) | u∈Kᵢ∩(何か), v∈Kⱼ, uv∈K_s} に共役で f.p.f. 作用
(w ∈ Q^#, u^w = u, v^w = v ⟹ u,v ∈ C_G(w) ⊆ H (Q TI + N まわり) ⟹ u,v ∈ Kᵢ∩H ⊆ Z
(Z ⊴ H, Q TI) ⟹ uv ∈ Z 矛盾) ⟹ |Q| ∣ |X| = a_{ijs}|K_s| ⟹ ψ(1)a_{ijs}ω(K̂_s)
= a_{ijs}|K_s|ψ(x_s) ≡ 0。
ψ constant on Z^# ⟹ α := ω(K̂_s) は K_s∩Z^# ≠ ∅ で s に独立。
(7.3) ψ(1)α² ≡ ψ(1)(a_{ij0} + a_{ij}α) (K₀ = {1})。**d odd** ⟹ K₁∩Z^# ≠ ∅,
K₂ := (K₁)⁻¹ が取れて (i,j) = (1,1), (1,2) 適用:
(7.4) ψ(1)a₁₁α ≡ ψ(1)(|G:Q| + a₁₂α)。ψ = 1_G で a₁₁ ≡ 1 + a₁₂ (mod |Q|)
(Q Hall ⟹ |G:Q| は mod |Q| 可逆)。⟹ ψ(1)α ≡ ψ(1)|G:Q|、α = |G:Q|ψ(z)/ψ(1) 代入
⟹ |G:Q|ψ(z) ≡ |G:Q|ψ(1) ⟹ ψ(z) ≡ ψ(1) (mod |Q|)。
**独立性高: 汎用 class-algebra 補題として RepresentationTheory 新 leaf
(CentralCharacterCongruence.lean 等)**。前提: ω の値の代数的整数性 (central character
標準事実) の repo 内所在要確認、無ければ新設。

**(8) Conclusion**: (5)+(6) ⟹ (Res_H e'₁, χᵢ − aᵢχ₁) = 0 (i ≥ 2),
(Res_H e'₁, χ₁ − aη₁) = λ − a ⟹ Res_H e'₁ = (λ+aμ)Σᵢ aᵢχᵢ/… 正確には
Res_H e'₁ = (λ+aμ)Σ_{i=1}^n aᵢχᵢ + χ' (χ' ⊥ 全 χᵢ)、μ := (Res e'₁, η₁) − 1。
**Σ aᵢχᵢ = (ρ_H − ρ_{H/Z})/(da)** (正則指標差; 𝒳 = Z-非自明 kernel 側の全既約と重複度)。
Z ⊆ Ker χ' (χ' の成分は 𝒳 外 = 𝒮(Z)∪(Irr−𝒮) 側)。z ∈ Z^# 評価:
e'₁(z) − e'₁(1) = (λ+aμ)(−|H|/(da)) = −|Q|(λ/a + μ)。(7) を ±e'₁ に適用
(e'₁ は Z^# 上 constant: 上式が z に独立) ⟹ λ/a + μ の代数的整数性 ⟹ a ∣ λ ⟹ (6)。

## 形式化アーキテクチャ

- **新 leaf**: `OddOrder/Peterfalvi/Appendices/FeitSibleyTheorem.lean` (steps 1–3
  reduction 補題群; 2000 行超なら dir 化) +
  `OddOrder/GroupTheory/RepresentationTheory/CentralCharacterCongruence.lean` (step 7 汎用形)。
  **新 leaf は同 commit で OddOrder.lean に配線** (issue 0135)。
- 既存インフラ対応:
  - Lemma 1(a) = `coherent_adjoin_of_degree_bound` (FeitSibley.lean, issue 1049)
  - Lemma 1(b) = `coherentEqualDegree` (S07_Coherence/CoherenceUnion.lean:298)
  - [Is] Cor 2.30 = `exists_degree_sq_le_index` (SchurCenterBound.lean:194)
  - 度数二乗和: **InflationCharacter.lean にほぼ完備** (2026-07-21 偵察):
    `sumInflatedDegreeSq` (:401, Σ_{N⊆Ker} χ(1)² 型) / `sumNonInflatedDegreeSq` (:480) /
    `sumNonInflatedDegreeSq_eq_index_mul` (:507, K-相対版 — 𝒮(R) 和 = 指数差はこれで) /
    `sumNonInflatedDegreeMulChar_of_mem` (:540, z ∈ N^# での Σχ(1)χ(z) — **step (8) の
    ρ_H − ρ_{H/Z} 評価がこれ**) / `inflate` 全単射 (:185–295)。新設はほぼ不要の見込み、
    次 iteration で正確な statement を読んで Remark + (1) から着手。
  - coherence base+adjoin 連鎖 = CoherenceUnion.lean:1408/1591
  - central character ω = 所在確認 (無ければ新設; mathlib の integrality と接続)
- **作業順 (上流優先+文書順)**: ①度数二乗和 counting 補題 ((1)(2)(3)(6) 全部で使う) →
  ② Remark (𝒮(Q') coherent, m ≥ 2) → ③ (1) → ④ (2) → ⑤ (3) → ⑥ (7) (独立、並行可) →
  ⑦ (4)(5)(6) → ⑧ (8) assembly。

## 進捗 (2026-07-21, FeitSibleyTheorem.lean)

- [x] **Remark 完結**: `ssetOf_Qder_coherent` (d0d1ada95) — 𝒮(Q') coherent
  (仮定: d odd + |Q₁| odd + 非空)。`ssetOf_Qder_nonempty` (3bd71cd5b) で非空は
  `S ⊔ Q' < Q` に還元済み (endgame で Q₁ 非自明 p-群から導出)。
- [x] 支持層: S'/Q' 定義・Q'⊴H・S⊴Q・S⊔Q'⊴Q・[H:Q]=d・𝒮(Q') の degree=d
  (`apply_one_eq_d_of_mem_SsetOf_Qder`)・A-support・2(b) isometry ブリッジ・
  (5.2.d/e) difference image 群・`leKer_induce_Qder_of_forall`。
- [x] **2-kernel counting** (1dfea8ba3): `sum_degreeSq_ker_subset_not_subset` —
  Σ_{N⊆ker, M⊄ker} χ(1)² = |K⧸N| − |K⧸N⊔M| (汎用)。
- [x] 𝒮(R) 和ブリッジ (556867bcc): `leKer_iff_subset_characterKernel` +
  `sum_degreeSq_SsetOf` (filter-Finset 形 = Lemma 1(a) の enumeration に直結)。
- [x] f.p.f. 下界 (0ed24f513): `d_dvd_card_sub_one_of_le_Q1` / `d_add_one_le_card_of_le_Q1` /
  `two_mul_d_add_one_le_card_of_le_Q1` (conj MulAction inline 構成 +
  FreeActionOrbitCount.dvd_card_sub_one_of_free_off_unique_fixed)。
- [x] `exists_apply_one_eq_d_mul`: ∀ χ ∈ 𝒮, χ(1) = d·m (m ≥ 1) — 1(a) anchor 可除性。
- [ ] **次 = reduction (1) 本体**。2026-07-21 偵察で判明した組み立てルート:
  - **連鎖 adjoin エンジンは既存**: `coherentPairChain` (S07_Coherence/CoherenceUnion.lean:1602,
    base + per-pair step ⟹ pairUnion 全体 coherent) + `pairUnion_eq_of_cover` (分解証明) +
    `exists_monotoneDegreeEnum` (:1436, 度数昇順 enumeration) +
    `two_mul_lt_sq_of_primePow_gap` (NormInequalities.lean:796, 度数 gap 算術)。
  - **1 ステップ補題の形**: 𝒮(S'Q₂) coherent ⟹ 𝒮(S'Q₃) coherent は、
    𝒮(S'Q₃) = 𝒮(S'Q₂) ∪ (新規共役対) に分解し coherentPairChain。各 step は
    Lemma 1(a) (coherent_adjoin_of_degree_bound) — anchor = 度数 d の member
    (𝒮(Q') ⊆ 𝒮(S'Q₂): S'Q₂ ⊆ [Q,Q] = Q' より) + d ∣ 全度数 (exists_apply_one_eq_d_mul)。
  - **反例抽出 (原文の ψ)**: ¬coherent ⟹ 連鎖の最初の失敗 step で 1(a) の
    非度数仮定は全部立つので度数 bound が破れる: 2dψ(1) ≥ Σ_{base} χ(1)²
    (= |H/S'Q₂|−|H/S'Q₁| via sum_degreeSq_SsetOf)。以降 (1.1)(1.2) の算術は
    exists_degree_sq_le_index + two_mul_d_add_one 系で閉じる。
  - 残る未整備: chief factor (Q₂/Q₃, Z/Q₃ = Z(Q₁/Q₃)) の商レベル中心性の取り回しと、
    ψ(1) = dφ(1) の φ ∈ Irr(Q/S'Q₃) 具体化 ([Is] 2.30 の section 版 =
    InflationCharacter の degree_sq_le_index_of_central_quotient :361 が使えるはず)。
  - (5f2ff15b1) `ssetOf_antitone` + `sup_Sder_le_Qder` 済み。
    `exists_monotoneDegreeEnum` (CoherenceUnion:1436) は任意有限族の度数昇順
    enumeration (Injective + cover + Re-monotone) を返す — 分解の並べ替えに直用可。
  - **⚠ 統計 fidelity フラグ (2026-07-21)**: 原文 (1) の結末「(d+1)²−2 < 4d whence
    d ≤ 2, contradiction」は **d = 1 で矛盾にならない** (2 < 4 真)。d odd + d ≤ 2 は
    d = 1 を残す ⟹ reduction 補題は 1 < d (実質 d ≥ 3) を仮定に持つのが honest。
    **d = 1 は Theorem assembly 側で別扱い**: D = 1 ⟹ H = Q ⟹ τ = Ind_Q^Q = id で
    𝒮 の coherence は自明 (id 拡張)。statement 設計時に d = 1 分岐を忘れないこと。
  - **1 ステップ補題 statement 案**:
    `ssetOf_coherent_step (hd : Odd hyp.d) (hd1 : 1 < hyp.d) (hQ1odd) {Q₂ Q₃}
    (hQ₂der : Q₂ ≤ ⁅Q₁,Q₁⁆) (hQ₃ : Q₃ ≤ Q₂) (正規性: Q₂,Q₃ ⊴ H 要素形)
    (hchief : Q₂/Q₃ chief in H — 使う帰結は「Q₂/Q₃ ∩ Z(Q₁/Q₃) ≠ 1 ⟹ Q₂ ≤ Z」なので
    最初から「hZcap : Q₂ ≤ Z where Z/Q₃ := Z(Q₁/Q₃) 引き上げ」形で持つのが楽)
    (h2primes : |Q₁| に 2 素因数 ⟹ Q₂ ⊊ Z の supply)
    (hcoh₂ : Nonempty (IsCoherent τ (SsetOf (Sder ⊔ Q₂)) A))
    : Nonempty (IsCoherent τ (SsetOf (Sder ⊔ Q₃)) A)`。
    証明: by_contra → coherentPairChain の対偶で最初の失敗 step の ψ (度数昇順 ⟹
    ψ は失敗時点の最小未 adjoin 度数) → 1(a) の非度数仮定は全部無条件に立つ
    (orthonormal/共役対/A-support/可除性 = 部品済み) ⟹ 度数 bound 破れ:
    Σ_{𝒮(S'Q₂)} χ(1)² ≤ 2dψ(1) → (1.1)(1.2) 算術 → f.p.f. 下界 → d ≤ 2 → hd1+hd 矛盾。
  - **(2026-07-21 1(a) 引数精読の帰結) 次の必須部品 = full-𝒮 S07.Hypothesis**:
    `coherent_adjoin_of_degree_bound` は ambient family の
    `S07.Hypothesis (S := hyp.Sset) hyp.A` を第 1 引数に取る (𝒮(Q') 版とは別物)。
    構成は ssetOf 版 (ssetOfQderDifferenceImage 系) の鏡映で:
    (a) `conj_mem_Sset` (𝒮 の共役閉性 — conj_mem_SsetOf_Qder の Qder 節を落とすだけ)、
    (b) **一般共役対 support 補題**: χ ∈ 𝒮 ⟹ (χ̄−χ).support ⊆ A — 度数相等は
    χ̄(1) = star(χ(1)) = χ(1) (exists_apply_one_eq_d_mul で χ(1) = d·m 実数) + off-Q 消滅
    (diff_support_subset_A_of_mem_SsetOf_Qder の一般化; apply_one_eq_d を使わない版)、
    (c) tau_isometry_diff: 既存 tau_inner_eq_of_supported_SsetOf_Qder の Sset 版
    (同じ証明 — span mono を外すだけ)、(d) difference_image: ssetOfQderDifferenceImage の
    Sset 版 (keystone 差の supported-span 帰属を (b)(c) で)。
    その後 1(a) の残引数: hχdeg は exists_apply_one_eq_d_mul (a := m)、
    hdiffasuppχ (χ − a•anchor の support) は同度数 scaled diff の A-support
    (既存 hdegdiffsupp 論法)、htau1_memaχ は tau_mem_ZIrr、
    hDeg = 2a < Σ (degMem/d)² が counting との接続点。
  - (b3734e2d6) **full-𝒮 S07.Hypothesis 完成** (`ssetS07Hypothesis`)。
  - **pairUnion 機構の正確な形 (2026-07-21 精読)**: `pairSet pair j = {(pair j).1, (pair j).2}`、
    `pairUnion_succ_eq_union_pair`、`mem_pairUnion` (base ∨ ∃ j < N)、
    `pairUnion_eq_of_cover (hS₀ : S₀ ⊆ X) (hpairs : ∀ j < N, pairSet ⊆ X)
    (hcover : ∀ χ ∈ X, base ∨ pair) : pairUnion S₀ pair N = X`。
    engine 適用は `(pairUnion_eq_of_cover ...) ▸ coherentPairChain S₀ pair h0 N hstep`。
    **残る構成タスク**: 共役対 enumeration `pair : ℕ → CF × CF` の構築 —
    𝒮(S'Q₃) − 𝒮(S'Q₂) は共役閉 (conj_mem_Sset + LeKer の conj 不変性) かつ実指標なし
    (2(c)) なので {χ, χ̄}-軌道の代表系を度数順に取る。CoherenceUnion の (6.6) 最終定理
    (:1640 以降) が同じ構成をどう扱っているか (pairing を仮定に取るか構成するか) を
    次に読むこと — 構成済みならそれを流用、仮定型なら代表系選択 (Finset 帰納 or
    exists_monotoneDegreeEnum + 偶数個ペアリング) を新設。
  - **(2026-07-21 確認済) (6.6) 最終定理 `peterfalvi_66_coherence_of_X` (CoherenceUnion:1711)
    は pairing (S₀/pair/N/covers) を仮定に取る** — 構成は無い。加えて
    `coherentOfPairChainCover` (:1641, covers+h0+hstep ⟹ IsCoherent X) と
    `pairUnion_eq_of_enumCover` (:1665, index-level cover 版) が組み立てを担う。
    ⟹ **新設すべきは共役対分解補題** `exists_conjPair_decomposition`:
    Y ⊇ B (両方共役閉、Y 有限、Y 実指標なし) ⟹ ∃ N pair,
    (∀ j < N, (pair j).2 = (pair j).1.conj ∧ pairSet ⊆ Y ∧ pairSet ∩ B = ∅) ∧
    (∀ χ ∈ Y, χ ∈ B ∨ ∃ j < N, χ ∈ pairSet pair j) ∧ pairwise-disjoint ∧
    度数単調 ((pair j).1 の度数が j に単調 — per-step hDeg で「累積 ⊇ それ以下の度数全部」
    に使う)。構成 = (Y − B).ncard の強帰納: 最小度数の χ を取り (χ, χ̄) を先頭に、
    Y − B − {χ,χ̄} で再帰 (Y−B は共役閉: Y, B 両方の共役閉性から; χ̄ ≠ χ は no-real)。
    実装は List (CF × CF) を返す補助関数 + pair := fun j => l.getD j default が楽。
    FeitSibleyTheorem.lean に汎用形 (Hypothesis 非依存、Set (ClassFunction L ℂ) レベル)
    で置く — hub 判断で S07_Coherence 側へ移設可。

### 進捗追記 (2026-07-21 後半セッション)

- [x] **反例抽出機構 3 点セット完成** (FeitSibleyTheorem.lean):
  `exists_conjPair_pairUnion_eq` (:959, 共役対分解 — 強帰納構成) +
  `exists_first_incoherent_step` (:1048) + `sq_ratio_sum_le_of_adjoin_incoherent`
  (:1590, 下記供給表の実装) + **`exists_counterexample_of_not_coherent` (:1698,
  統合形)**: B ⊆ Y ⊆ 𝒮 (B coherent 共役閉, Y 非 coherent) ⟹ ∃ ψ ∈ Y, a > 0, m:
  ψ(1) = d·a ∧ (∀x∈B, x(1) = d·m(x)) ∧ Σ_B m² ≤ 2a。
- [x] **(1.1) counting bound** `card_quot_sub_le_of_forall_deg_of_sum_le` (:1315):
  上の m/a データ + sum_degreeSq_SsetOf_toFinset から |H⧸R| − |H⧸R⊔Q₁| ≤ d²·2a。
- [x] **(1.2) degree bound** `exists_deg_sq_le_of_mem_SsetOf` (:840): ψ ∈ 𝒮(R),
  R ≤ D₀ ≤ Q, D₀/R 中心 ⟹ ψ(1) = d·a, a² ≤ [Q-in-H : D₀-in]。
- [x] **quotient f.p.f. 下界** (FeitSibleyReductions.lean 新 leaf):
  `mem_of_inv_mul_conj_mem_of_ne_one` / `d_dvd_card_quotient_sub_one_of_le_Q1` /
  `d_add_one_le_card_quotient_of_le_Q1` (D-不変 section N < W ≤ Q₁ ⟹ |W⧸N| ≥ d+1)。
- [x] **(1.1) index 算術ブリッジ** (FeitSibleyReductions.lean): `Q1_inf_sup_eq`
  (Q₁ ⊓ (A'⊔B') = B'; S'Q₂ と SZ の両用) / `card_quot_eq_card_quot_Q1_mul`
  (|H⧸R| = |Q₁⧸Q₂|·|H⧸RQ₁|) / `d_dvd_card_quot_sup_Q1` /
  `card_quot_Q1_sub_one_le_of_card_quot_sub_le` (**|Q₁⧸Q₂| − 1 ≤ d·c 抽出**)。
- [x] **step 補題完成** `ssetOf_coherent_step` (bc53bd165, FeitSibleyReductions.lean):
  𝒮(S'Q₂) coherent + chief データ (Q₃ ≤ Q₂ ≤ Z ≤ Q₁, ⁅Z,Q₁⁆ ⊆ Q₃, Q₂ ⊊ Z,
  D-不変性, |Q₁⧸Q₂| ≥ (d+1)²) ⟹ 𝒮(S'Q₃) coherent。中心性入力 (旧 1)・算術 (旧 4)
  込みで一括組立。d=1 も `false_of_reduction_one_bounds` が消化 (hd1 不要)。
  併せて `conj_mem_SsetOf` (一般 R) / `Q1der_le_Q1`。
- [x] **2素数下界完成** `d_add_one_sq_le_card_quot_of_two_primes` (febb04202):
  nilpotent Q₁ + p ≠ r ∣ |Q₁| + D-不変 Q₂ ≤ ⁅Q₁,Q₁⁆ ⟹ (d+1)² ≤ |Q₁⧸Q₂|。
  中間 M = ⁅Q₁,Q₁⁆·N_p (正規 p-補群、Isaacs Ch05 `hasNormalPComplement_of_isNilpotent`
  + `map_mulAut_of_normal_pcomplement` で D-不変)。両側 properness は
  `commutator_sup_normal_pcomplement_ne_top` (K/N_p が nontrivial perfect p-群になり
  可解性と矛盾) を p と r で 1 回ずつ。Sylow 直積分解は不要だった。
  (旧 3 |Z⧸Q₂| ≥ d+1 は `d_add_one_le_card_quotient_of_le_Q1` 直用で step 補題内で解決済。)
- [x] **reduction (1) 完結** `ssetOf_sder_coherent_of_two_primes` (190ce7830,
  新 leaf FeitSibleyInduction.lean 710 行, OddOrder.lean 配線済, sorry-free):
  d odd + |Q₁| odd + Q₁ nilpotent + 2 素数 ∣ |Q₁| ⟹ 𝒮(S′) coherent。
  部品: base 恒等式 `Qder_eq_sup_Sder_commutator` / Normal 変換 3 種 /
  `centralLift` (Z の要素的構成) + H-不変性 / `exists_minimal_conjInvariant_between`
  (chief 選択) / `minimal_le_centralLift` (中心交差) / `primaryLift` +
  `not_centralLift_le_minimal` (Z ⊄ Q₂、p-primary part が chief を割る) /
  `prime_dvd_card_quotient_of_le_commutator` + `exists_center_pow_prime_eq_one_of_dvd` /
  S⊴H mirror 群 (`S_normal_in_H` 等) / 強帰納 skeleton
  `ssetOf_sup_sder_coherent_of_conjInvariant`。
- [x] **centralLift 機構の W-一般化** (43db54a05): `centralLiftIn`/`primaryLiftIn`/
  `minimal_le_centralLiftIn` — reduction (2) の S 側 (Z/S₂ = Z(S/S₂)) で再利用可能に。
  薄いラッパー無し、Q₁ 消費側は直接更新。
- [x] **reduction (2) 完結** `sset_coherent_of_ssetOf_sder_coherent` (debb1b3e7,
  新 leaf FeitSibleyReductionTwo.lean 651 行, 配線済, sorry-free):
  𝒮(S′) coherent + d odd + |Q₁| odd + Q₁ nilpotent + hlt ⟹ 𝒮 coherent。
  部品 (全 first-shot green): S側 index ブリッジ `card_quot_sup_Q1_eq_d_mul`
  (|H⧸A′Q₁| = d·|S⧸A′|) / counting 抽出 (|S⧸S₁| 因子保持) / 直積 index
  `index_subgroupOf_sup_prod_eq` / `centerLiftQ1` (= centralLiftIn Q₁ ⊥) +
  `two_mul_d_add_one_le_card_centerLiftQ1` (|Z(Q₁)| ≥ 2d+1) / 中心対 split
  `commutator_mem_of_central_pair` / 算術 `false_of_reduction_two_bounds`
  (m·zc(q₁−2) < 4d² vs ≥ 8d²−2) / step `ssetOf_S_coherent_step` / 帰納
  `ssetOf_coherent_of_le_sder` (minimal_le_centralLiftIn W:=S, S_nilpotent 使用)。
  (1)+(2) 合成で「2素数 ∣ |Q₁| ⟹ 𝒮 coherent」が閉じた。
- [x] **還元宣言の分岐 composer** (a08484247): `sset_coherent_of_two_primes`
  ((1)+(2) 合成) + `sset_coherent_of_commutator_Q1_eq_bot` (abelian 分岐:
  Q′ = S′ → Remark → (2))。`nontrivial_Q1` / `sup_S_Qder_lt_Q` を抽出
  (hlt は nilpotency のみから導出可能に)。**d=1 特例は (1)(2) では不要と確定**
  (false_of_reduction_one/two_bounds が d ≥ 1 で閉じる鋭形)。
  残る分岐 = Q₁ non-abelian p-群 → (3)–(8)。最終 assembly はさらに
  hnil (Thompson, Isaacs Ch06 KernelNilpotent — d > 1 時; d = 1 時の nilpotency は
  別途 — 要検討) と hQ1odd の供給、および素因数 1 個/2 個の場合分け
  (Nat.card の primeFactors) を要する。⚠ hQ1odd は Hypothesis fields から導出
  不能の疑い — feit_sibley_coherence の statement (hd のみ) と原文 p.145 仮定
  ブロックの照合が必要 (PDF 実読、統計 fidelity)。
- [x] **原文照合完了 (2026-07-21, PDF pp.144–147 実読)**:
  - **p.144 仮定ブロックは repo Hypothesis と完全一致** (|Q₁| odd は書籍にも無い)。
  - **hQ1odd 張力の確定**: 2(c) 証明の「odd order group Q₁D」は書籍側の飛躍
    (issue 1053 裁定済: 2(c) は explicit hQ1odd、Theorem は d odd のみ据え置き・
    還元後導出)。⚠ ただし現形式化の (1)(2) は counterexample 抽出の共役対機構経由で
    hQ1odd を要求 — 書籍の (1)(2) は 1(a) を対無しで 1 枚ずつ adjoin するので
    hQ1odd 不要 (Remark も O_{2'}(Q₁)⋊D で careful)。**最終 assembly の
    ≥2素数/abelian 分岐で |Q₁| even のケースが現機構では閉じない**。解決候補:
    (i) 1(a) の pair-free 化 + no-real 依存の除去 (書籍忠実、機構再作業大)、
    (ii) 最終 statement に hQ1odd 追加 (1053 裁定の変更 — hub/ユーザー相談要)、
    (iii) even ケースの vacuity 証明 (ambient TI から — 未検証、1053 も未検証と記載)。
    **(3)–(8) は p-群文脈で hQ1odd = (p 奇素数の冪) が正当に立つため非ブロック**。
    最終 assembly 時に再訪。
- [x] **(3) 部品①②完了**: ① min-degree pair 分解 (221a24dad)。
  ② p-冪度数 `exists_apply_one_eq_d_mul_pow` (472161e43, 新 leaf
  FeitSibleyReductionThree.lean 345 行, sorry-free): 𝒮(S′) の度数 = d·p^k。
  ルートは CT 3.12 回避 — Schur スカラー (mod-kernel, inflate 経由) の単位乗法則
  + IsComplement.equiv でのノルム折り畳みで **Res_{Q₁} φ が既約** ⟹ deg ∣ |Q₁|。
  汎用部品: `exists_unit_mul_eq_of_le_center` /
  `isIrreducibleCharacter_restrict_of_isComplement'` (hyp 非依存、upstream 適性)。
- [x] **正方向 adjoin wrapper 完成** `coherent_insert_pair_of_two_mul_lt_sum`
  (357db2805): 1(a) 共役対 packaging の正方向・一般 anchor (d·m₀) 版。
  2m₀a < Σm² + m₀ ∣ 全度数/a ⟹ S₁∪{χ,χ̄} coherent。旧対偶 packaging は
  この 1 行系に書き直し (~55 行 dedup)。⚠ 形式化済 1(a) は integer-ratio 形
  なので hmdvd (anchor ∣ 各 member 度数) が必要 — Part A では全度数 d·p^k で
  anchor = 最小冪ゆえ自動成立。
- [x] **⭐ Part A 完成** (16f981b02, 2026-07-21): `xsetOf_sder_coherent`
  (FeitSibleyReductionThree.lean, sorry-free) — d odd + Q₁ p-群 +
  ⊥ ≠ Z ≤ Z(Q₁) (H-不変 = Normal instance 供給) ⟹ 𝒳₁ = XsetOf S′ Z coherent。
  部品 3 commit: ① 𝒳₁ setup (efe2353f8): XsetOf 定義/共役閉/counting
  Σ = |H⧸R|−|H⧸RZ| + T 因数分解 d·|S⧸A′|·|Q₁⧸Z|·(|Z|−1) + 非空 +
  odd_card_Q1_of_isPGroup。② (3.1) 数値核 (b9b66410a):
  two_mul_pow_lt_of_pow_dvd (2·p^{k₀+k} < p^{k₀+k+1} ≤ p^{2k} ≤ s) +
  pow_dvd_sum_pow (p^{2k} ≤ |Q₁⧸Z| ⟹ p^{2k} ∣ Σ p^{2kₓ}; coprime d 約分) +
  d_mul_sum_pow_eq (指数単位 counting, ℕ)。③ chain (16f981b02):
  coherent_of_subset_constant_degree (1(b) subfamily 形 — S07.Hypothesis を
  𝒮-toolkit restriction で構成) + choose! 指数関数 + min-degree pair 分解 +
  coherentPairChain + wrapper。(1.2) は exists_deg_sq_le_of_mem_SsetOf
  (D₀ = S⊔Z, 中心性 = commutator_mem_sup_Sder_of_central at Q₃ = ⊥)。
  ⚠ 実装知見: IsCoherent は Type (data) — ∃/Nonempty の destructuring は
  Prop-valued have 内へ隔離、step 出力は Nonempty.some。
  `(p ^ k : ℝ)` は `(↑p)^k` に elaborate される (↑(p^k) と別形) — wrapper
  との突き合わせは外側 cast 形 `((p ^ k : ℕ) : ℝ)` で統一。
- [x] **Part B 前提 ①: rational 1(a) (issue 1050) 完了** (c1f50cc5a, 2026-07-22)。
  原文 p.147 精読で確定: (3) 後半の 1(a) 適用は **anchor = Ind(1_{S/S₂}·θ) ∈ 𝒳₁**
  (θ = ψ の Q₁-isotypic 成分、**ψ ごとに anchor が変わる**)、可除性は
  anchor(1) = d·θ(1) ∣ ψ(1) = d·e·θ(1) のみ (e = 重複度)。base 𝒳∩𝒮(S₁) の
  member 度数 d·λ(1)·θ_x(1) は anchor で割れない ⟹ integer-ratio 1(a) では
  閉じない (1049 時の判断の修正)。1(a) から hdvd、wrapper から hmdvd を除去済み。
  不等式は原文どおり Σ ≤ 2·χθ(1)·ψ(1)、χθ(1)² ≤ d²|Q₁/Z| は χθ ∈ 𝒳₁ ゆえ
  Part A と同じ exists_deg_sq_le_of_mem_SsetOf (D₀ = S⊔Z) で出る。
- [x] **Part B 前提 ②: Q₁-side anchor 部品** (FeitSibleyQ1Component.lean,
  8bf1d7d2c + 4d1ce38b6): exists_restrict_eq_nsmul (Res_{Q₁}φ = e·θ、
  Clifford 単一軌道 + Q-共役自明) / q1Proj + surjective / restrict_compHom_q1Proj
  (Res θ~ = θ) / compHom_q1Proj_apply_of_mem_S (S-part kernel)。
  既約性は IsIrreducibleCharacter.compHom_of_surjective 合成。
- [x] **Part B 本体 1: anchor 構成パッケージ完成** (a404d0fbe, sorry-free):
  `exists_anchor_of_mem_XsetOf` (Q1Component leaf): ψ ∈ XsetOf R Z (Z ≤ Q₁,
  Z の H-共役不変性を要素形で) ⟹ ∃ χθ ∈ XsetOf Sder Z, tθ e > 0:
  χθ(1) = d·tθ ∧ ψ(1) = d·(e·tθ)。懸念だった (iv) Z ⊄ ker(Ind θ~) は
  **forall_eq_one_of_leKer (R = Z) の対偶で閉じた — Mackey 評価不要**。
  支持: leKer_induce_of_forall (R-一般順方向転送、FeitSibleyTheorem)。
- [x] **⭐ Part B 本体 2〜5 完成 = reduction (3) 完結** (FeitSibleyXsetInduction.lean,
  sorry-free, OddOrder.lean 配線済)。設計どおり全 first-shot に近い形で landing:
  - **3 算術** `false_of_xset_induction_bounds` (前 commit 2c52bbd42): m·qz·(z−1) ≤
    d·2·tθ·a + tθ² ≤ qz + a² ≤ m·qz + z ≥ 2d+1 + m ≥ 2 ⟹ False。
  - **counting bridge** `xset_counting_le_of_sum_le`: sum_degreeSq_XsetOf_eq_mul
    (= d·|S⧸S₁|·|Q₁⧸Z|·(|Z|−1)、d は 1 個) + 反例 Σm² ≤ 2tθa の ℂ→ℝ 変換で
    h1 (|S⧸S₁|·|Q₁⧸Z|·(|Z|−1) ≤ d·2tθa) を供給。d² 対 d の 1 個キャンセルが要点。
  - **step** `xsetOf_S_coherent_step`: by_contra → exists_counterexample_anchored
    (B₀ = 𝒳(S′,Z) anchor, B = 𝒳(S₁,Z), Y = 𝒳(S₂,Z)) → h1 counting +
    h2 anchor (D₀ = S⊔Z, index_subgroupOf_sup_S_eq → tθ² ≤ |Q₁⧸Z|) +
    h3 ψ (D₀ = ZS⊔Z, index_subgroupOf_sup_prod_eq → a² ≤ |S⧸ZS|·|Q₁⧸Z| ≤ |S⧸S₁|·)
    + h4 f.p.f. (two_mul_d_add_one_le_card_of_le_Q1、|Z| odd = Q₁ odd の約数) +
    h5 (|S⧸S₁| ≥ 2) → false_of_xset_induction_bounds。(2)(3)(4) は reduction (2)
    step の忠実な鏡映 (SsetOf→XsetOf、固定 Z、anchor 版抽出)。
  - **induction** `xsetOf_coherent_of_le_sder`: ssetOf_coherent_of_le_sder の鏡映。
    Sder → ⊥ を |Sder|−|S₃'| 強帰納、exists_minimal_conjInvariant_between +
    centralLiftIn S S₃' (= ZS) + minimal_le_centralLiftIn。⚠ Normal instance の
    形: `((S₁⊔Z)`-in-`H)` は counting 用に **sup-of-subgroupOf** 形が要る →
    (S₁-in-H).Normal + (Z-in-H).Normal の component を渡して sup-of-normals
    auto-instance に組ませる (subgroupOf_H_normal_of_conj_mem は subgroupOf-of-sup
    形を返すので直接は型不一致)。ZS⊔Z は index_prod 用に subgroupOf-of-sup 形で明示。
  - **descent** `xset_coherent_of_xsetOf_sder_coherent`: S₃ = ⊥ で 𝒳(⊥,Z) = 𝒮−𝒮(Z)。
  - **⭐ reduction (3) 統合** `xset_coherent_of_le_center_Q1`: Part A
    (xsetOf_sder_coherent) + Part B descent の合成 — Q₁ p-群 + d odd +
    ⊥ ≠ Z ≤ Z(Q₁) (H-不変) ⟹ 𝒳 = XsetOf ⊥ Z coherent。**これが (3) の deliverable**。
- [ ] **(4)〜(8) endgame — 着手** (新 leaf FeitSibleyEndgame.lean, 2026-07-22)。
  原文 pp.148-150 を PDF ページ画像で再読了、冒頭 digest と完全一致を確認
  (p.148 = (5)末尾+(6)、p.149 = (7) 全文、p.150 = (8))。
  - [x] **(6) 整数核** `x_eq_zero_or_x_one_of_norm_identity` (sorry-free):
    1 + a² = (v,v) + a²(x−1)² + (m−1)x²a²、(v,v) ≥ 0、a ≥ 2、m ≥ 2 ⟹
    x = 0 ∨ (x=1 ∧ m=2)。整数性 (a² ≥ 4 で bracket ≤ 1) + interval_cases。
    (v,v)=1 の抽出や x=1,m=2 の符号差し替え還元は assembly 側 ((6) 本体)。
  - [x] **(4) Notation setup — Z 構成 + 𝒳/𝒴 coherence 完了** (7be8d3d7e + 759d2788a,
    sorry-free): endgameZ := ⁅Q₁,Q₁⁆ ⊓ C_G(Q₁)。4 性質 (le_Q1 / centralizes
    ⁅z,y⁆=1 / ne_bot / conj_mem H-不変)。
    - ne_bot: normal_inf_center_nontrivial (Isaacs Ch01) で ↥Q₁ レベル
      [Q₁,Q₁]⊓Z(Q₁) ≠ 1 → map_eq_bot_iff + ker_subtype で G レベルへ (単射)。
      ⚠ 名前空間は OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial (full path)。
    - conj_mem: ⁅Q₁,Q₁⁆ は Q1_map_conj_eq(既存 FeitSibleyInduction) + map_commutator、
      C_G(Q₁) は Commute.map (conj h)。⚠ rw[mem_centralizer_iff] は coe 不一致で
      失敗 → mem_centralizer_iff_commutator_eq_one の .mp/.mpr 項適用が robust。
    - endgame_Xset_coherent: reduction (3) 供給 → 𝒳 = XsetOf ⊥ Z coherent。
      Normal 3 点 (Sder/Z/S H-不変を subgroupOf_H_normal_of_conj_mem + conj_mem_sup)。
    - 𝒴 = 𝒮(Q′) coherence = 既存 ssetOf_Qder_coherent 直用 (ラッパー不要)。
  - [x] **(4) witness 抽出完了** (coherent_extension_eq_zsmul_irr, sorry-free):
    coherence hcoh + χ ∈ S 既約 ⟹ ∃ ε∈{±1} ξ∈Irr(G): hcoh.extension χ = ε•ξ。
    ⟨eχ,eχ⟩=1 (extension_inner_eq + IsIrreducibleCharacter.inner_self_eq_one) +
    eχ∈ZIrr (extension_mem_ZIrr) → **既存** exists_zsmul_irreducibleCharacter_of
    _inner_self_one (InducedIrreducible.lean:751; norm-1⟹±Irr、新設不要だった)。
    χ ∈ zSpan S = Submodule.subset_span。eᵢ/e′ⱼ 両方をこれで抽出。
  - [x] **⭐ (5) 完結** `cross_extension_inner_eq_zero` (FeitSibleyEndgame.lean,
    sorry-free, 2026-07-22): disjoint coherent 族 X,Y ⊆ 𝒮 の一般形 —
    (E χ, E′ η) = 0 ∀χ∈X ∀η∈Y。仮定: X anchor χ₁ + scaled diff A-supported
    (∀φ∈X ∃a>0, φ−a•χ₁ ∈ ℤ[X,A])、X 第 2 元 χ₂≠χ₁、Y 等度数 diff
    (∀ψ∈Y, ψ−η₁ ∈ ℤ[Y,A])、Y 第 2 元 η₂≠η₁。部品 4 補題:
    - `cross_inner_extension_diff_eq_zero`: 両 extension が τ に supported diff 上
      一致 (extends_on_supported + map_sub/map_nsmul) → **大域等長は既存
      `tau_inner_eq_of_supported_Sset`** (FeitSibleyTheorem:1464、zSupportedSpan
      mono で X,Y → 𝒮 に持ち上げ) → H 側で 4 cross 項が Sset_pairwiseOrthogonal
      で消滅。
    - `cross_inner_extension_diff_right_eq_zero` (λ=0 核): by_contra λ≠0 →
      witnesses (coherent_extension_eq_zsmul_irr ×4) → λ≠0 が ξ′₁,ξ′₂ ∈ {ξχ,ξ₁}
      を強制 (ξ′₁≠ξ′₂, ξχ≠ξ₁ は lattice 等長) → 2 case とも
      `eq_zero_of_signed_degree_relations` (純 ℂ 算術核、f₁/f₂ swap で共用) で
      ξχ(1) = 0 → 度数正値と矛盾。**書籍の aᵢ=1 抽出・e′₁(1)=0 経路は不要**
      (3 関係式から直接 D₂=0 が出る鋭形; linear_combination 2 発)。
    - `cross_inner_extension_diff_any_eq_zero`: η₁ 値 0 + cross 等長で全 j へ転送。
    - anchor 消滅 (χ₂ 使用): t=(Eχ₁,E′η)≠0 → ξ′=ξ₁ → (Eχ₂,E′η)=0=a₂t → 矛盾。
    汎用部品: `inner_zsmul_irreducible_eq` (⟨ε•ξ,ε′•ξ′⟩=εε′δ、ZIrrFourier
    upstream 候補)。⚠ Lean 実装知見: 識別子に `λ` 不可 (予約トークン) /
    ite を含む have statement には proof 冒頭 `classical` 必須 (無いと Decidable
    が sorry に落ちて "ring failed ... = sorry" の不可解エラー) / `omit ... in` は
    docstring の**前**。
    (4)(5) の endgame 組み立てでは X = 𝒳 (aᵢ = p-冪比, exists_apply_one_eq_d_mul_pow)、
    Y = 𝒴 = 𝒮(Q′) (全員 degree d)、hdisj = XsetOf の ¬LeKer Z vs Q′⊇Z... の
    supported-diff 仮定充足は (6) assembly 側で供給。
  - [ ] **(6) 本体**: Ind(χ₁−aη₁)=−a·e′₁+λΣe′ᵢ+v、(v,e′ᵢ)=0 → norm 展開で
    x_eq_zero_or_x_one_of_norm_identity 適用 → a∣λ ⟹ 𝒮∪𝒴 coherent (τ が
    χᵢ↦eᵢ,ηⱼ↦e′ⱼ で一貫) → Lemma 1(a) で 𝒮(S′) → (2) で 𝒮。
    - [x] **pairing 恒等式 2 本** (2026-07-22, sorry-free): `tau_scaled_diff_inner_self`
      ((τδ,τδ) = 1+a²、δ = χ−a•η₁ A-supported、coherence 不要) +
      `tau_scaled_diff_inner_extension_diff` ((τδ, e′ⱼ−e′₁) = a、j>1)。
      どちらも tau_inner_eq_of_supported_Sset 直用 + Sset_pairwiseOrthogonal。
    - [x] **Bessel 分解 2 本** (2026-07-22, sorry-free, generic Γ):
      `inner_sub_sum_inner_smul_eq_zero` (残差 ⊥ wₖ) +
      `inner_self_eq_residual_add_sum_inner_mul_star` ((u,u) = (v,v) + Σtⱼ·star tⱼ、
      有限正規直交族)。ZIrrFourier upstream 候補。⚠ inner_sum_left/right・
      inner_conj_symm は OddOrder.RepresentationTheory 直下 (ClassFunction. でない、
      mathlib _root_.inner_conj_symm と ambiguity → full path)。
      CharacterPsiDecomposition は (5.4) 特化形で流用不可と確認。
    - [x] **norm identity λ 形完成** `exists_lambda_norm_identity` (2026-07-22,
      sorry-free): ∃ lam ∈ ℤ: (u,E′η) = lam (∀η≠η₁)、(u,E′η₁) = lam−a、
      ∃ nvv ≥ 0: 1+a² = nvv + (lam−a)² + (Y.ncard−1)·lam²。
      構成: lam := c(η₁)+a (c = choose 整数係数を dite 全域化)、Bessel 適用、
      erase η₁ で和分割、mem_ZIrr_inner_self_eq_sum_sq で nvv。
      ⚠ set u の罠: set は現 goal を u に畳むが、**後から作る have/補題適用の
      statement は tau 形のまま** — goal 側 rw [← hu] は不要 (むしろ失敗)、
      補題結果は rw [hu] で tau 形に開いてから exact。
      m≥2 不要 (m=1 でも真)。Set.ncard_eq_toFinset_card は ℕ で先に rw。
    - [x] **𝒳 側 keystone pairing** `tau_keystone_inner_extensionX_diff`
      (2026-07-22, sorry-free): (u, eᵢ − aᵢe₁) = −aᵢ (6a の X 鏡映)。
    - [ ] **(6) 組み立て設計 (2026-07-22 固定; 次 session はここから)**:
      1. [x] **witness 正規化補題完成** `exists_normalized_witness_of_dvd`
         (2026-07-22, sorry-free)。⚠ Lean 知見: `rcases hmem with rfl | rfl` は
         h : η = η₂ で **η₂ 側を subst 消去**する (RHS 優先) — 後続タクストで
         η₂ を参照するなら h 保持 + rw [h]。x_eq_zero 適用は (a := (a:ℤ))
         (m := ...) 明示 (mod_cast が metavar で詰まる)。仕様:
         (P1) ∀η∈Y, w η − w η₁ = τ(η−η₁); (P2) union 直交正規·±Irr·∈ZIrr;
         (P3) (u, w η) = 0 (η≠η₁) ∧ (u, w η₁) = −a。
         構成: x_eq_zero_or_x_one_of_norm_identity で分岐。x=0 → w := E′ 値。
         x=1∧m=2 → **swap+negate**: w η₁ := −E′η₂, w η₂ := −E′η₁ (dite)。
         swap が (P1) を保つのは m=2 に限る (w η₂ − w η₁ = E′η₂ − E′η₁ ✓)。
         **中間の IsCoherent Y 再証明は不要** — 下流は w 関数だけ消費する。
      2. [x] **v 分析完成** (2026-07-22, sorry-free): `keystone_residual_props` +
         **`exists_X_witness_assignment`** — (v,Eχ₁) の 3 分岐 (v = Eχ₁ →
         E-値そのまま / (v,Eχ₁) = −1 → χ₂ 経由で 4a₂² = 1 矛盾 / (v,Eχ₁) = 0 →
         全 χ'≠χ₁ で a' = 1 ∧ Eχ' = −v、swap 割当 wXχ₁ = v, wXχ'≠χ₁ = −Eχ₁)。
         出力 6 clauses: ZIrr / 単位ノルム / X-直交 / 𝒴-witness cross-直交 /
         X-差関係 (∀ 有効 a') / keystone wXχ₁ − a•(w η₁) = τ(χ₁ − a•η₁)。
         ⚠ Lean 知見: ℂ に nlinarith/linarith 不可 → ε²=1 系は
         linear_combination (係数 = 相手の ε² 等) / `first | norm_num | ...` は
         norm_num が goal を False に「進捗」させ成功扱いになる罠 → 符号抽出は
         linear_combination (εv·h'' − ε'·hεv2 型) が robust / 混合 smul の
         加群等式は `module` タクティク / a' 一意性は degree at 1 (happly1 +
         hval_eq、hone : χ₁−1•χ₁ ∈ supported)。
         旧設計メモ: 前半 = `keystone_residual_props`
         (2026-07-22, sorry-free): v := u + a•(w η₁) について (v,v) = 1 /
         v ∈ ZIrr / v ⊥ 全 w(𝒴) / (v, Eχ') = a'·((v,Eχ₁) − 1) (χ'≠χ₁,
         a'-supported diff)。後半 [ ] = ±Irr 抽出 + 3 分岐 + wX 割当構成
         (下記設計、次 iteration): v := u + a•(w η₁)、(v,v) = 1 (norm identity, nvv=1)、
         v ∈ ZIrr → ±Irr (exists_zsmul_irreducibleCharacter_of_inner_self_one)。
         (v, Eχ') − a'(v, Eχ₁) = −a' (tau_keystone_inner_extensionX_diff +
         (5) で (w η₁, Eχ') = 0) → 整数値分析: (v,Eχ₁) = 1 → v = Eχ₁ /
         (v,Eχ₁) = 0 → ∀χ'≠χ₁: a' = 1 ∧ v = −Eχ' → n = 2 (相異なる χ' が
         全部 −v) → X 側 swap+negate (a₂ = 1 は conj 対で成立) /
         (v,Eχ₁) = −1 → |−2a'| ≤ 1 矛盾。
         出力: X-witness 割当 wX (P1-X: wX χ − aᵪ wX χ₁ = τ(χ−aᵪχ₁)) +
         **keystone (P4): wX χ₁ − a•(w η₁) = u = τ(χ₁ − a•η₁)**。
      3. 前半 [x] **span 転送ヘルパー 4 本完成** (2026-07-22, sorry-free,
         generic Γ→Δ、SpanTransport section): `inner_map_eq_on_zSpan`
         (member gram 保存 ⟹ ℤ[T] 全体で等長) / `map_mem_ZIrr_on_zSpan` /
         `exists_int_inner_of_mem_zSpan` (整係数) / `eq_sum_inner_smul_of_mem_zSpan`
         (再構成 φ = Σ(φ,μ)•μ、有限直交正規 T)。すべて Submodule.span_induction
         (cases mem/zero/add/smul; smul は ← Int.cast_smul_eq_zsmul 経由)。
         中盤 [x] **extension 写像完成** (2026-07-22, sorry-free):
         `memberAssignmentMap s W := Σ_{μ∈s} (innerLeftℤ μ).smulRight (W μ)`
         (⚠ innerLeftℤ の namespace は S07.IntegralCharacterMap) +
         `memberAssignmentMap_apply` + `memberAssignmentMap_apply_of_mem`
         (直交正規 collapse F μ₀ = W μ₀) + `zsmul_mem_zSupportedSpan` (閉包;
         zero/add/sub は DifferenceImage に既存)。
         後半 [x] **IsCoherent 組立本体完成** = `isCoherent_of_memberAssignment`
         (2026-07-22, sorry-free, FeitSibleyEndgame.lean SpanTransport 節, generic Γ/Δ):
         有限直交正規 S、直交正規 ℤ[Irr]-値割当 W、共通 anchor η₁∈S、各 μ∈S に
         `∃ b:ℕ, μ−b•η₁ supported ∧ W μ−(b:ℂ)•W η₁ = τ(μ−b•η₁)` ⟹ IsCoherent τ S A。
         **設計改良 = 単一 anchor η₁ + 合成 b_μ**: 書籍の X/Y 二重 anchor (χ₁, η₁) を
         「全 member を η₁ に還元した合成差分 μ−b_μ•η₁」に畳んで uniform 化 —
         X の χ は b_χ = a_χ·a (χ−a_χχ₁ と a_χ(χ₁−aη₁) の和; assembly 側で供給)。
         extension := **memberAssignmentMap s W** (E₀ = 0, 残差は zSpan 上 0)。
         - extension_inner_eq/mem_ZIrr = inner_map_eq_on_zSpan / map_mem_ZIrr_on_zSpan
           + member collapse (W-gram: hWnorm/hWorth/hWZIrr)。
         - **extends_on_supported = 生成引数** (実装確定ルート): supported φ を
           整係数再構成 φ=Σc_μ•μ (eq_sum_inner_smul + exists_int_inner)、degree-0
           (φ 1=0 ∵ 1∉A, μ 1=b_μ·η₁ 1) で **anchor 係数 Σc_μ b_μ=0** (η₁ 1≠0)、
           ⟹ φ=Σc_μ•(μ−b_μ•η₁) が生成元の整結合 → memberAssignmentMap と τ が
           各生成元 (map_sub/map_nsmul/collapse + hbeq) で一致 → calc で φ 全体へ。
           **equalizer submodule を明示的に作らず calc 一発で閉じた** (両写像とも
           ℤ-linear ゆえ decomposition に map_sum/map_zsmul を流すだけ)。
         - nonzero = 仮定 hnz (assembly 側で η₂−η₁ 等を供給)。
         ⚠ 実装知見: IsCoherent は Type ⟹ `noncomputable def` (theorem 不可) /
         IntegralCharacterMap は full path (OddOrder.Peterfalvi.S07) 要 /
         nsmul↔ℂ-smul 橋 = Nat.cast_smul_eq_nsmul、nsmul↔zsmul 橋 = 同 (ℤ 版)。
      4. [x] **(6) 統合完成** = `union_coherent_of_lambda_dvd` (2026-07-22, sorry-free,
         **新 leaf FeitSibleyUnionCoherence.lean 192 行**, OddOrder.lean 配線済)。
         a∣λ + (4) データ (X/Y disjoint coherent, χ₁∈X, η₁∈Y, a≥2, m≥2, keystone
         χ₁−a•η₁ supported, λ norm-identity data) ⟹ IsCoherent τ (X∪Y) A。
         組立: exists_normalized_witness_of_dvd (w) → exists_X_witness_assignment (wX)
         → 合成 W (`if μ∈X then wX μ else w μ`) → isCoherent_of_memberAssignment。
         合成差分 = 単一 anchor η₁: η∈Y は b=1、χ∈X は b=a_χ·a
         (χ−a_χa•η₁ = (χ−a_χ•χ₁)+a_χ•(χ₁−a•η₁), P1-X+keystone を τ 線形で合成)。
         ⚠ 実装知見: IsCoherent は Type ⟹ ∃ witness は Classical.choose で取り出し
         (obtain 不可、Exists.casesOn は Prop のみ); **choose_spec を set の前に**取らないと
         properties が hwex.choose を参照して set 済 w と syntactic mismatch /
         inner_conj_symm は OddOrder.RepresentationTheory full path (mathlib と ambiguous) /
         混合 nsmul/ℂ-smul の加群等式は push_cast + module。
      5. その後: 1(a) adjoin で 𝒮(S′) coherent → (2) で 𝒮 → (iii) 分岐完成。
      (7) class-algebra 合同は独立 — (6) 統合が済んだので (7)→(8) で a∣λ を出して
      union_coherent_of_lambda_dvd に供給、その後 step 5 の adjoin/(2)。
  - [ ] **(7)** class-algebra 合同 (独立、並行可): ψ constant on Z^# ⟹
    ψ(z)≡ψ(1) mod|Q|。
    **⭐ スコープ確定 (2026-07-22 偵察): 新規 class-algebra 構築は不要 — 既存 machinery
    の再インスタンス化。** `peterfalvi_67` (ClassSumAlgebra.lean:127) が (7) の合同
    そのもの (`ρ.character z ≡ ρ.character 1 [ALGMOD |P|]`) を、中心指標 constancy +
    TI + `a₁₁≡1+a₁₂` から `peterfalvi_673` 経由で導出済。全下位部品が存在:
    - `classSum`/`classSumCoeff`/`classSum_mul` (構造定数 = (7.1)、ClassSumCongruence.lean)
    - `classSumCoeff_self_one_eq_zero` (hreal で a₁₁₀=0) / `classSumCoeff_self_inv_one_eq_card`
      (a₁₂₀=|C₁|) / `peterfalvi_673_combine/cancel/final` ((7.3)(7.4) 算術)
    - `card_dvd_classSumCoeff_of_fixedPointFree` (**完全汎用**: 任意有限部分群 P の
      f.p.f. 共役作用で |P| ∣ classSumCoeff = (7.2) の核) / 中心指標整数性
      `nonidentityZClassCoeffSum_isIntegral` / `character_isIntegral`。
    **唯一の差分 = P Sylow (mod |P|) vs Q Hall (mod |Q|)**。Sylow 依存は 2 箇所のみ:
    ① `fixedPointFree_classPair_of_isTISubset` (ClassSumCongruence.lean:491、Sylow P の
       p-element 論法で「x∈P^# が (u,v) を固定 ⟹ u,v∈Z」を出す) →
       **Q の TI 構造 (Q_trivial_intersection) を使う Hall 変種を新設**が要 (これが主タスク)。
    ② `coprime_card_class_card_sylow` (|C₁| と |P| の coprime) → Q Hall では
       |C₁|=|G:C_G(z)| と |Q| の coprime を別途 (Q Hall + z∈Z⊆Q の C_G(z)⊇Q から)。
    ⟹ 実装 = **`peterfalvi_67` の Hall-TI 版** (`peterfalvi_67_hall` 等) を
    ClassSumAlgebra または新 leaf に。①の f.p.f. Hall 変種 (~60-100 行) + coprime
    補題 + peterfalvi_67 の assembly を Q で再展開 (~40 行)。**中心指標・class algebra・
    代数的整数はすべて既存** — 「無ければ新 leaf」は不要と確定。
    次 iteration: App.IV endgame の Q/Z/TI が peterfalvi_67 の引数 (hZP/hZnormal/hti/
    hPz/hreal/hconst/hone) をどう供給するか (Hypothesis field からの導出) を確定してから
    Hall 変種を書く。⚠ hconst の「N∩C_G card 定数」条件と hone の供給が endgame 側で
    どう出るか要精査 (原文 (7) の d odd 使用箇所 = K₁∩Z^#≠∅ の存在)。
    **Hall f.p.f. 変種の設計確定 (2026-07-22 偵察)** — Sylow proof
    (ClassSumCongruence.lean:491-588) の 2 Sylow-step を差し替えるだけ:
    - `Q_trivial_intersection : ∀ x∉H, Q ⊓ Q.map(conj x) = ⊥` (FeitSibley.lean:267) が
      TI の正本。x∈Q^# を y が中心化 ⟹ x∈Q ⊓ Q^{y⁻¹} nontrivial ⟹ y∈H
      (**C_G(x)⊆H**; 既に近い補題が FeitSibley.lean:521-532 = TI overlap 消化)。
      これが Sylow の `hcent_le` (→N_G(P)) を H に置換する部分。
    - Sylow の `mem_sylow_of_mem_normalizer_of_isPGroup` (y∈N かつ p-元 ⟹ y∈P) の Hall 版 =
      「y∈H かつ y が π(Q)-元 ⟹ y∈Q」(正規 Hall は全 π-元を含む)。Hall infra は
      `Isaacs/Ch03_SplitExtensions/Theorem315.lean` (IsHallSubgroup/IsPiGroup/
      card_dvd_of_isPiGroup)。⚠ 正規 Hall ⟹ 全 π-元包含 が repo に無ければ小補題新設
      (Q ⊴ H + coprime index、共役類の π-元 order は |Q| を割る)。
    - coprime |C₁| |Q|: z∈Z⊆Z(Q₁) は Q=S×Q₁ を中心化 (S_commutes_Q1 + Z⊆Z(Q₁)) ⟹
      **Q⊆C_G(z)** ⟹ |C₁|=|G:C_G(z)| ∣ |G:Q|、Q Hall ⟹ coprime(|G:Q|,|Q|)。
    残りの TI/Z⊴H/共役鎖 (hZconj/hmem_Z の骨格) は Sylow 版と同一 (汎用)。
    ⟹ **`peterfalvi_67_hall` を lane-a leaf に新設** (既存 shared lemma は read only、
    peterfalvi_673 + card_dvd_classSumCoeff_of_fixedPointFree を cite)。~100-150 行見込。
    **⭐ TI input 準備済**: `isTISubset_Q_sdiff_one` (FeitSibley.lean:525) =
    `IsTISubset (Q\{1}) H` が既存 (peterfalvi_67 の hti に対応、normalizer→H)。
    **実行可能設計 = 4 sub-lemma (次 turn はこれを順に書くだけ)**:
    1. `mem_Q_of_mem_H_of_orderOf_coprime` (~15 行): y∈H かつ coprime(orderOf y, |H:Q|)
       ⟹ y∈Q。証明: H⧸Q で orderOf(mk y) ∣ orderOf y かつ ∣ |H:Q| (Lagrange)、
       coprime ⟹ orderOf(mk y)=1 ⟹ mk y=1 ⟹ y∈Q (QuotientGroup.eq_one_iff)。
       (Q ⊴ H = Q_subgroupOf_H_normal は既存)。
    2. `fixedPointFree_classPair_hall` (~70 行): ClassSumCongruence.lean:491 の Sylow proof
       を写経し 2 点差替 — `hcent_le` の N_G(P)→H (isTISubset_Q_sdiff_one 直用)、
       `mem_sylow_of_mem_normalizer_of_isPGroup`→上記 1 (y は zi∈Z⊆Q に共役 ⟹
       orderOf y=orderOf zi ∣ |Q| coprime |H:Q|)。hZconj は Z⊴H (subgroupOf) から。
    3. `coprime_classCard_Q` (~15 行): z∈Z⊆Z(Q₁) が Q=S×Q₁ 中心化 (S_commutes_Q1) ⟹
       Q ⊆ C_G(z) ⟹ |C₁|=|G:C_G(z)| ∣ |G:Q| coprime |Q| (Q Hall = coprime_Q_D + |H:Q|)。
    4. `peterfalvi_67_hall` (~40 行): ClassSumAlgebra.lean:127 peterfalvi_67 を写経、
       P→Q、上記 2/3 を Sylow 版の差替に。中心指標 collapse
       (centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset) が Sylow P を
       取るか要確認 — 取るなら汎用 TI 版も要 (ClassSumCongruence 側、shared claim)。
    ⚠ 4 の collapse 補題が Sylow 依存なら shared-infra 追加 (9200 claim)。まず署名確認。
    **⭐ 署名確認済 (2026-07-22): collapse は Sylow 依存** —
    `centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset`
    (ClassSumCongruence.lean:1577) は `(P : Sylow p G)` を取り modulus = `Nat.card P`。
    内部で `centralCharacterOfRep_classSum_mul_cong_of_isTISubset` →
    `fixedPointFree_classPair_of_isTISubset` (Sylow) を使う。⟹ **(7) Hall 版は純 lane-a
    leaf で完結しない — shared class-algebra infra の Hall 変種を要す**。
    **確定した architecture (次 turn の実行計画)**:
    - **9200 claim** を立てる (shared-infra、レーン別サブバンド a=9200)。着手前に
      `ls issues/9*.md` で重複 scan (現状 9130/9159/9164/9318 = 別件)。
    - **方式 = 汎用化 (既存 Sylow 版を壊さない追加)**: collapse/mul_cong/f.p.f. の
      「一般部分群 P + f.p.f. を仮説に取る」版を ClassSumCongruence/ClassSumAlgebra に
      **新規追加** (既存 Sylow 版は f.p.f. を fixedPointFree_classPair_of_isTISubset で
      供給する薄い wrapper に後退させられるが、無理に触らず追加のみでよい)。
      核 `card_dvd_classSumCoeff_of_fixedPointFree` は既に f.p.f. を仮説に取る汎用形
      ゆえ、その上の mul_cong/collapse も f.p.f. 仮説版に一般化するのは機械的。
    - その上で lane-a leaf に Hall f.p.f. (sub-lemma 2) + peterfalvi_67_hall (sub-lemma 4)
      を組む。sub-lemma 1 (mem_Q_of_orderOf_coprime) と 3 (coprime_classCard_Q) は
      lane-a leaf で自足。
    ⟹ 見込 = shared 側 汎用化 ~80 行 (9200) + lane-a 側 Hall 組立 ~100 行。
    hub 調整: 9200 claim は additive (既存 Sylow 版不変) ゆえ低リスク。
  - [ ] **(8)** Conclusion: (5)+(6)+(7) で a∣λ を証明し (6) を閉じる。
    Res_H e′₁ = (λ+aμ)Σaᵢχᵢ + χ′、Σaᵢχᵢ=(ρ_H−ρ_{H/Z})/(da)、z∈Z^# 評価 +
    (7) を ±e′₁ に適用 → λ/a+μ 代数的整数 → a∣λ。
  作業順: (7) は独立ゆえ (4)(5)(6) と並行可。それ以外は (4)→(5)→(6)→(8)。
- [ ] 旧記録: **Part A 本体組み立て** (2026-07-21 設計固定、この順):
  1. **𝒳₁ setup**: XsetOf 定義 (SsetOf Sder ∩ {¬LeKer Z})。共役閉 ✓ conj 既存 2 条件
     保存。no-real: |Q₁| = p^n 奇 (p=2 なら Q1_not_two_group と矛盾で p 奇 —
     hQ1odd を hp/hQ1p から導出する小補題)。counting:
     Σ_{𝒳₁} χ(1)² = |H⧸S′-in| − |H⧸(S′⊔Z)-in| (sum_degreeSq_ker_subset_not_subset
     直用、ただし SsetOf 版のような filter-set ブリッジ (𝒳₁ 版の
     leKer_iff/sum_degreeSq_XsetOf) を新設)。T = d·|S⧸S′|·|Q₁⧸Z|·(|Z|−1) 因数分解
     (card_quot_eq_card_quot_Q1_mul at R = S′⊔Z, S′⊔Z⊔Q₁ = S′⊔Q₁ +
     card_quot_sup_Q1_eq_d_mul)。非空/≥2: T > 0 (Z ⊄ S′: Z∩S = ⊥, Z ≠ ⊥) +
     no-real 対。
  2. **(3.1) 数値核** (ℕ): 全度数 d·p^{k_x}、step χ の k > 全 B の k₀。
     p^{2k} ∣ T (φ² = p^{2k} ≤ p-冪 |Q₁⧸Z| ⟸ 2.30 ⟹ ∣) かつ
     p^{2k} ∣ Σ_{未収載} (k_x ≥ k) ⟹ p^{2k} ∣ d²·Σ_{S₁}m² の d² 約分で
     p^{2k} ∣ Σ_{S₁}m² ⟹ Σm² ≥ p^{2k} = p^k·p^k ≥ p·p^k... ⟹ 2·p^{k₀}·p^k <
     Σm² (p ≥ 3) — wrapper の hlt 形そのもの。
  3. **chain 組み立て**: B := 等度数最小セグメント (coherentEqualDegree で coherent、
     ≥2 は conj 対)。exists_conjPair_pairUnion_eq (min-degree 版) を (Y := 𝒳₁, B) に
     適用 → coherentPairChain (CoherenceUnion:1602) の hstep に wrapper を供給。
     min 句から「未収載度数 ≥ 現 step 度数」「S₁ 内度数 ≤ 現 step 度数」を抽出。
  4. その後 Part B ((2) 鏡映の 𝒳-相対版、issue 記載済) → (4)–(8)。
  旧設計メモ:
  1. **𝒳-族**: 𝒳 ∩ 𝒮(R) = {χ ∈ Irr H | R ⊆ ker, Z ⊄ ker} (Z ≤ Z(Q₁) ⟹ 自動的に ∈ 𝒮)。
     counting は既存 `sum_degreeSq_ker_subset_not_subset` (N=R-in, M=Z-in) が直用可:
     Σ = |H⧸R| − |H⧸R⊔Z|。
  2. **p-冪度数**: χ ∈ 𝒮(S′) ⟹ χ(1) = d·p^k。Q/S′ で S/S′ が中心 ⟹
     deg φ ∣ |Q₁| = p^n (中心指数可除性 — repo の所在確認: SchurCenterBound 周辺、
     無ければ [Is] 中心可除性を新設)。
  3. **(3.1) 可除性**: χᵢ(1)² ∣ Σ_{j<i} χⱼ(1)² — d² ∣ LHS (全項 d²·p-冪²)、
     φᵢ(1)² ∣ RHS (|H⧸S′|−|H⧸S′Z| = d|S/S′||Q₁/Z|(|Z|−1) で φᵢ(1)² ≤ |Q₁/Z|
     両方 p-冪 ⟹ ∣; j ≥ i 項は sorted で φᵢ² ∣ φⱼ²)、gcd(d,p)=1 で合成。
  4. **Part A (𝒳₁ coherent)**: base = 等度数セグメント {χ₁..χ_k} (2c で k ≥ 2、
     `coherentEqualDegree`)。i > k: 2χ₁(1)χᵢ(1) < pχ₁(1)χᵢ(1) ≤ χᵢ(1)² ≤ Σ_{j<i}
     ((3.1)+正値、p ≥ 3)。⚠ 反例抽出は **accumulated 和** (base 制限しない) が要る —
     `sq_ratio_sum_le_of_adjoin_incoherent` を直接使い (exists_counterexample の
     B-制限を経ない)、pair 分解の**度数単調性**が必要 (`exists_conjPair_pairUnion_eq`
     が単調 enumeration を返すか要確認; 返さなければ度数昇順版に強化)。
  5. **Part B (S′ ≠ 1, 𝒳 へ拡張)**: (2) 鏡映帰納の 𝒳-相対版。counting =
     d|S/S₁||Q₁/Z|(|Z|−1) (二重 kernel 和)。anchor = Ind(1·θ) ∈ 𝒳₁ (χ(1) ∣ ψ(1) は
     等値)。χ₁(1)² ≤ d²|Q₁/Z| + ψ(1)² ≤ d²|S/S₁||Q₁/Z| (S₁/S₂ ⊆ Z(S/S₂)) ⟹
     |S/S₁|(|Z|−1)² ≤ 4d²、|Z| ≥ 2d+1 (two_mul_d_add_one_le_card_of_le_Q1、
     Z ⊴ H D-inv ✓)、|S/S₁| ≥ 2 ⟹ 矛盾。算術は false_of_reduction_two_bounds 型の
     新変種。
  6. 新 leaf `FeitSibleyReductionThree.lean` (配線同 commit)。
  7. **偵察結果 (2026-07-21)**: (a) 中心指数可除性 deg φ ∣ [G:Z] ([Is] CT Thm 3.12
     相当) は repo 未発見 — `exists_natDegree_charValue_one_dvd_card` (deg ∣ |G|) のみ。
     p-冪度数には「S/S′ 中心 ⟹ deg ∣ |Q₁|」級が必要 → 新設候補
     (direct-product Irr 分解 or Ito 型; まず mathlib
     `Character.degree_dvd_index_center`? を leansearch で確認)。
     (b) ✅ **完了 (221a24dad)**: `exists_conjPair_pairUnion_eq` を min-degree 版に
     in-place 強化 (第 3 句: 各 step の pair.1 は未収載 Y-元中で度数実部最小;
     Set.exists_min_image 選択)。
     (c) **② 中心指数可除性の確定ルート (2026-07-21 設計)**: 一般 CT 3.12 は不要。
     φ ∈ Irr(Q-in) が S-部分を mod-kernel 中心に持つとき
     (`exists_central_linear_restriction` SchurCenterBound:242 が入口)、
     s ∈ S はスカラー作用 ⟹ |φ(s·y)| = |φ(y)| ⟹
     1 = (1/|Q|)Σ_{q}|φ|² = (1/|Q₁|)Σ_{y∈Q₁}|φ(y)|² = ⟨Res_{Q₁}φ, Res_{Q₁}φ⟩
     (q = s·y の一意分解で和を折り畳む) ⟹ **Res_{Q₁-in} φ 既約** ⟹
     deg φ = deg(Res φ) ∣ |Q₁| = p^n (exists_natDegree_charValue_one_dvd_card)。
     新補題は「S′ ⊆ ker φ ⟹ Res_{Q₁} φ 既約 + deg φ ∣ |Q₁|」の形で
     FeitSibleyReductionThree.lean に。(1)(2) より以後 Q₁ = non-abelian p-群
  (p 奇素数) と仮定してよい: assembly 分岐は (i) |Q₁| 2素数 → (1)+(2) 済,
  (ii) Q₁ abelian → Q′ = S′ ⟹ Remark 𝒮(Q′) = 𝒮(S′) coherent → (2) 済,
  (iii) Q₁ non-abelian p-群 → (3)–(8) 本線。d=1 分岐 (τ=id 自明) と
  hnil/hQ1odd の上流供給 (Thompson/KernelNilpotent + odd) も assembly 側。
  (3) = 1 ≠ Z ⊴ H, Z ⊆ Z(Q₁) ⟹ 𝒳 = 𝒮 − 𝒮(Z) coherent (issue 冒頭 digest 参照)。
  **実装部品リスト (2026-07-21 精査)**:
  1. S 側 index ブリッジ: |H⧸(A′⊔Q₁)-in| = d·|S⧸A′| (A′ ≤ S; [H:A′] の
     2 通りの塔で cancellation) — counting 抽出「m(q₁−1) ≤ 2da、m = |S⧸S₁| を保持」用。
     既存 card_quot_eq_card_quot_Q1_mul (hinf: Q₁⊓S₁ = ⊥ via S⊓Q₁=⊥) と合成。
  2. 直積 index 分解: [Q-in : (A′⊔B′)-in] = |S⧸A′|·|Q₁⧸B′| (A′ ≤ S, B′ ≤ Q₁;
     relIndex 塔 (A′⊔B′) ≤ (A′⊔Q₁) ≤ Q + 第二同型 (Q1_inf_sup_eq 流用))。
  3. 中心対 split: x ∈ Z_S ⊔ Z_{Q₁}, q ∈ Q ⟹ ⁅x,q⁆ ∈ S₂ (⁅Z_S,S⁆ ⊆ S₂ +
     ⁅Z_{Q₁},Q₁⁆ = 1; commutator_mem_sup_Sder_of_central の鏡映)。
     Z_{Q₁} := centralLiftIn Q₁ ⊥ (= Z(Q₁) の引き上げ)。
  4. |Z(Q₁)| ≥ 2d+1: two_mul_d_add_one_le_card_of_le_Q1 (既存, FeitSibleyTheorem)
     を centralLiftIn Q₁ ⊥ に適用 (非自明性 = nilpotent center_ne_bot、D-不変 ✓)。
  5. 算術 `false_of_reduction_two_bounds`: m(q₁−1) ≤ 2da + a² ≤ m·qz +
     q₁ = qz·zc + zc ≥ 2d+1 + m ≥ 2 ⟹ False (m·zc(q₁−2) < 4d² vs
     ≥ 2(4d²−1); m ≥ 2 は S₁ ≤ [S,S] ⊊ S から)。
  6. S 側 step 補題 (ssetOf_coherent_step の鏡映; anchor は 𝒮(Q′) ⊆ 𝒮(S₁)
     via S₁ ≤ Sder ≤ Qder) + S 側帰納 (minimal_le_centralLiftIn W:=S,
     S_nilpotent field 使用; hZQ₂ 相当は不要 — (2) は Z の properness を使わない)。
  7. reduction (2) 最終形: 𝒮(S′) coherent ⟹ 𝒮 = 𝒮(⊥) coherent。
  S 側の同型帰納: S₁ ⊴ H, S₁ ≤ S′, 𝒮(S₁) coherent、S₂ chief。
  counting は d·|S⧸S₁|·(|Q₁|−1) = Σ 型 (sum_degreeSq_SsetOf の R = S₁ 版、
  R⊔Q₁ の index)。(1.2) 対応は φ(1)² ≤ |S/Z|·|Q₁/Z(Q₁)|
  (Z/S₂ := Z(S/S₂)、S nilpotent は構造体 field S_nilpotent ✓)。
  **d odd + f.p.f. ⟹ |Z(Q₁)| ≥ 2d+1** (two_mul_d_add_one_le_card_of_le_Q1 系)。
  算術: |S/S₁|·|Z(Q₁)|(|Q₁|−2) < 4d² ⟹ |S/S₁| < 2 矛盾。
  step/帰納機構は (1) の鏡映 — centralLift の S 版 (⁅z,s⁆ ∈ S₂ 条件) が要る。
  その後: 還元宣言 (Q₁ = p-群 non-abelian へ) → (3) → (4)–(6) → (7) → (8)。
  設計メモ (旧、参考):
  - **目標形**: `ssetOf_sder_coherent_of_two_primes : Odd d + Odd |Q₁| + nilpotent Q₁ +
    (p ≠ r ∣ |Q₁|) ⟹ 𝒮(S') coherent`。帰納: 全 H-不変 Q₃ ≤ ⁅Q₁,Q₁⁆ について
    𝒮(S'Q₃) coherent を |⁅Q₁,Q₁⁆⧸Q₃| (または |⁅Q₁,Q₁⁆|−|Q₃|) の強帰納で。
    Q₃ = ⁅Q₁,Q₁⁆ base = Remark (`ssetOf_Qder_coherent`) + **要新補題
    `Qder = Sder ⊔ ⁅Q₁,Q₁⁆`** (直積の導来分解; commutator_mem_sup_Sder_of_central の
    論法流用)。Q₃ ⊊ ⁅Q₁,Q₁⁆ なら Q₂ := Q₃ 上最小の H-不変 (有限格子で存在) →
    Q₂/Q₃ chief → step 補題。
  - **chief ⟹ Q₂ ≤ Z 供給**: Z := Z(Q₁/Q₃) の引き上げ。Q₂/Q₃ ⊴ Q₁/Q₃ nontrivial
    ⟹ 中心と交わる (`exists_mem_center_of_normal_ne_bot_of_isNilpotent`,
    Isaacs Ch04 Mann.lean:577)。交差は H-不変 ⟹ 最小性で Q₂/Q₃ ⊆ Z(Q₁/Q₃)。
  - **hZQ₂ (¬ Z ≤ Q₂) 供給**: Q₂/Q₃ ≤ Z(Q₁bar) abelian ⟹ 最小性で Q₂/Q₃ は
    単素数 q-群 (primary 成分は characteristic)。一方 |Z(Q₁bar)| は p, r 両方で
    割れる (正規 Sylow ⊓ center ≠ ⊥, `IsPGroup.normal_inf_center_nontrivial`
    Isaacs Ch01) ⟹ Z(Q₁bar) は q-群でない ⟹ Z ⊄ Q₂。
  - **hnil (Q₁ nilpotent) の上流供給**: d > 1 なら D f.p.f. ⟹ Q₁⋊D Frobenius ⟹
    Thompson (Isaacs Ch06 KernelNilpotent.lean) で Q₁ nilpotent。d = 1 は
    H = Q, τ = id で coherence 自明の別分岐。Odd |Q₁| の供給も同様に assembly 側。
  - Normal instance 供給: (Sder⊔Q₂/Q₃).subgroupOf H 等は H-不変性 (Q₂ ⊴ H) +
    Sder ⊴ H (S ⊴ H char) から要素形→instance 変換補題経由。

### 反例中核補題の供給表 (2026-07-21 固定; 実装済 = sq_ratio_sum_le_of_adjoin_incoherent)

`not_hDeg_of_step_incoherent` 案: S₁ ⊆ 𝒮 共役閉・有限、anchor χ₀ ∈ S₁ (χ₀(1) = d)、
χ ∈ 𝒮, χ ∉ S₁, χ̄ ∉ S₁、hcoh : S₁ coherent、hfail : ¬(S₁ ∪ {χ,χ̄}) coherent ⟹
Σ_{x∈S₁} (x(1)/d)² ≤ 2a (実数、χ(1) = a·d)。1(a) 対偶で、引数供給:
- hyp := ssetS07Hypothesis hd hQ1odd / h1A := one_notMem_A
- enumeration: ι := ClassFunction ↥H ℂ, s := hS₁fin.toFinset, χmem := id,
  degMem := fun x => if h : x ∈ 𝒮 then (exists_apply_one_eq_d_mul h).choose * d else 0
  … ではなく **degMem x := (χ(1) の実部を Nat 化)** は不安定なので
  choose ベース: `degMem x := d * m_x` (m_x = choose)。hdegMem = choose_spec、
  hdvd = ⟨m_x⟩ (d ∣ d·m_x)、hdegpos (anchor: m=1)。
- hχχ/hχbarχbar = hself (irreducibleCharacter_inner_eq_ite if_pos)
- hχ_S1/hχbar_S1 = Sset_pairwiseOrthogonal + freshness (χ ≠ x ∀x∈S₁ from χ∉S₁;
  χ̄ ≠ x from χ̄∉S₁)
- hdiffsuppχ = conj_diff_support_subset_A_of_mem_Sset
- hmemortho/hmemconjortho = pairwise + no-real (x̄ ≠ x)
- hmembarS1 = S₁ 共役閉 / hcover = toFinset 全射 (mem_toFinset)
- hmemdiffsupp = conj_diff_support (member 版) / hdegdiffsupp =
  scaled_diff_support_subset_A_of_mem_Sset (7c8775769; 度数一致 d·(d·mᵢ) = (d·mᵢ)·d)
- hχdeg = exists_apply_one_eq_d_mul (a := m_χ) / hdiffasuppχ = scaled 版 n=1
  (one_smul glue) / htau1_memaχ = tau_mem_ZIrr (sub_mem span + nsmul_mem)
- 結論: hfail (coherent_adjoin_of_degree_bound … hDeg) の対偶 → ¬hDeg → push_neg
  → Σ ≤ 2a。
その後 (1.1): Σ_{S₁}(x(1)/d)² ≥ Σ_{𝒮(S'Q₂)}(…)² = (|H⧸…| − |H⧸…|)/d²
(sum_degreeSq_SsetOf; base ⊆ S₁ 単調) — ℂ→ℝ 変換は度数が実 (d·m) なので
(x(1))² の Re で。

### (1.2) の適用設計 (2026-07-21 固定)

`degree_sq_le_index_of_central_quotient` (InflationCharacter.lean:361) 確認済み:
`(φ : Irr G₀) (D) (hND : N ≤ D) (hker : N ⊆ ker φ) (hcentral : D.map (mk' N) ≤ center (G₀⧸N))
⟹ ∃ e, φ(1) = e ∧ e² ≤ D.index`。
(1.2) への適用: ψ ∈ 𝒮(S'Q₃) を 2(a) で ψ = Ind_Q^H φ' (φ' ∈ Irr(Q-in-H), ψ(1) = d·a,
a = φ'(1) — exists_apply_one_eq_d_mul の choose と同一視) に分解し、G₀ := ↥(Q-in-H)、
N := (Sder⊔Q₃)-in-Q (φ' が S'Q₃ 上定数 = forall_eq_one_of_leKer_Qder の一般 R 版が要る —
現行は Qder 固定なので R-パラメタ化した `forall_eq_one_of_leKer` に一般化するか、
kernel 経由で直接)、D := (S ⊔ Z)-in-Q、hcentral : (SZ)/(S'Q₃) が Q/(S'Q₃) の中心 —
これが chief-factor 側の唯一の群論的入力 (Z/Q₃ := Z(Q₁/Q₃) の引き上げ + S-部分は
Q = S×Q₁ の直積性から S/(S∩…) が commute…)。結論 a² ≤ [Q:SZ]-in = |Q₁/Z| 型。
⟹ 実装順: ① forall_eq_one_of_leKer_Qder の R-一般化 (R ≤ Q, R ⊴ H 要素形仮定で
同証明)、② hcentral を仮定に持つ (1.2) 補題 (中心性は reduction assembly 側で
Z の定義から供給)、③ (1.1)+(1.2)+f.p.f. 下界の算術合成 → d ≤ 2。

## 完了条件

`feit_sibley_coherence` sorry-free + axiom-clean + build green。
中間 milestone ごとに step 単位 commit。

## 参照

- 原文 `references/peterfalvi/pdf/09.0_pp_144_150_The_Feit-Sibley_Theorem.pdf` pp.146–150
  (**pdftotext は文字散乱で使用不可 — PDF ページ画像を読むこと**)
- issue 1049 (L1a) / 1051 (L2a) / 1052 (L2b) / 1053 (L2c)
- Coq 対応なし (odd-order は Peterfalvi Part I のみ; App.IV は Part II 用)
