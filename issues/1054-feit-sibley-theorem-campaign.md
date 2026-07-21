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

## 完了条件

`feit_sibley_coherence` sorry-free + axiom-clean + build green。
中間 milestone ごとに step 単位 commit。

## 参照

- 原文 `references/peterfalvi/pdf/09.0_pp_144_150_The_Feit-Sibley_Theorem.pdf` pp.146–150
  (**pdftotext は文字散乱で使用不可 — PDF ページ画像を読むこと**)
- issue 1049 (L1a) / 1051 (L2a) / 1052 (L2b) / 1053 (L2c)
- Coq 対応なし (odd-order は Peterfalvi Part I のみ; App.IV は Part II 用)
