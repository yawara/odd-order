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

## 完了条件

`feit_sibley_coherence` sorry-free + axiom-clean + build green。
中間 milestone ごとに step 単位 commit。

## 参照

- 原文 `references/peterfalvi/pdf/09.0_pp_144_150_The_Feit-Sibley_Theorem.pdf` pp.146–150
  (**pdftotext は文字散乱で使用不可 — PDF ページ画像を読むこと**)
- issue 1049 (L1a) / 1051 (L2a) / 1052 (L2b) / 1053 (L2c)
- Coq 対応なし (odd-order は Peterfalvi Part I のみ; App.IV は Part II 用)
