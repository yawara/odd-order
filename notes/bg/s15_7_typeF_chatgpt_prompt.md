# ChatGPT prompt: BG Thm 15.7 type-F case M' = F(M) (elided step)

Sent 2026-06-21 (lane-f). Gap: type-F F(M) ⊆ M', elided in BG ("(c)(d) follow from Cor 15.5 + Lem 12.1").

---

I am formalizing the Bender-Glauberman book "Local Analysis for the Odd Order Theorem" (LMS LNS 188) in Lean 4. I am stuck on an elided step in the proof of Theorem 15.7, specifically for the type-F case. Please reconstruct the argument rigorously, citing the BG results used at each step.

SETTING. G is a minimal simple group of odd order, M a maximal subgroup. Notation: M_sigma is the sigma-Hall normal subgroup, M_F the largest nilpotent normal Hall subgroup, M' = [M,M], F(M) the Fitting subgroup of M, and kappa(M), tau_1, tau_2, tau_3, beta(M), sigma(M); the supporting subgroup setup E = E_1 E_2 E_3 with M = M_sigma E and M_sigma cap E = 1 (Section 12).

Theorem 15.7 assumes F(M) is NOT a TI-subgroup of G. Conjunct (c) asserts M' = F(M) = M_sigma times O_{sigma(M)'}(F(M)).

I am in the type-F case: kappa(M) is empty, i.e. K = 1 (the cyclic Hall kappa-subgroup is trivial), so M = U M_sigma with U the Hall (kappa cup sigma)'-complement, which equals E here.

WHAT I HAVE ALREADY ESTABLISHED (BG-faithful):
- (15.7 a,b) M is in M_F cup M_{P1}, and H := M_F = M_sigma.
- (15.7, the E_3 = 1 step) E_3 = 1, so E = E_1 E_2 with E_1 cyclic and E_2 normal in E (Lemma 12.1).
- (Cor 15.5 b) F(M) = M_sigma times Y, where Y = O_{sigma(M)'}(F(M)) is a cyclic tau_2(M)-subgroup.
- (Lemma 15.1 a) M_sigma is contained in M' and M'/M_sigma is abelian.
- (Lemma 12.19) E' = [E,E] centralizes the Hall beta(M)'-subgroup of M_sigma; and pi(M_sigma) cap beta(M) is empty (this is exactly the rank-core input of 15.7), so the beta'-Hall of M_sigma is all of M_sigma, hence E' centralizes M_sigma.
- Therefore M' = M_sigma join E' (the derived-subgroup decomposition M' = M_sigma join [E,E]), and since E' centralizes M_sigma and E' cap M_sigma = 1, in fact M' = M_sigma times E'.
- Hence M' is nilpotent normal (a direct product of the nilpotent M_sigma = M_F and the nilpotent E'), so M' is contained in F(M), which gives E' contained in Y.

THE GAP. To get M' = F(M) I need the reverse inclusion F(M) contained in M', equivalently Y contained in M', equivalently Y contained in E' (since Y is a sigma'-group and M' = M_sigma times E'). Writing the tau_2-part of E as E_2, this is equivalent to E_2 contained in E' (so that the tau_2-group Y has trivial image in M/M', which is isomorphic to U^{ab} which is isomorphic to E/E'). It is also equivalent to C_M(M_sigma) contained in M_sigma (M_sigma self-centralizing in M), equivalently C_E(M_sigma) = 1 (E acts fixed-point-freely on M_sigma, i.e. M is a Frobenius group with kernel M_sigma so F(M) = M_sigma and Y = 1).

Crucially, BG's Corollary 15.5(d) proves F(M) contained in M' but ONLY for K not equal to 1 (the type-P case), via the argument "K is a tau_2(M)'-group and M/M' is isomorphic to K, hence M' contains Y". For type-F (K = 1) that argument is unavailable, and BG's Theorem 15.7 proof merely states "(c) and (d) follow from Corollary 15.5 and Lemma 12.1" without spelling out the type-F case.

QUESTION. Please reconstruct rigorously why M' = F(M) in the type-F case. Equivalently, prove one of: (i) O_{sigma(M)'}(F(M)) contained in M'; (ii) C_M(M_sigma) contained in M_sigma; (iii) C_E(M_sigma) = 1, i.e. M is a Frobenius group with kernel M_sigma; (iv) E_2 contained in E'. Please give every inference step and cite the BG results used (e.g. Lemma 12.1, Corollary 12.6, Theorem 12.5, Theorem 12.12, Lemma 15.1, Theorem 15.2, Lemma 14.1, Proposition 14.2, plus any Section 1-10 facts). If the cleanest route is to first prove M is Frobenius with kernel M_sigma for type-F, please derive that and explain why it holds.

---

## ChatGPT 回答の要約 + 検証 (2026-06-22, Pro 拡張, 思考 23m43s)

**核心 (lane-f が独立検証 → 正しい)**: type-F の `M'=F(M)` は **`C_Y(E₁)=1` (E₁ が τ₂-Fitting 因子
Y=O_σ'(F(M)) 上で固定点自由) 一点に等価**。
- M'=H×E', F(M)=H×Y (H=MF=Mσ), E'≤Y。Y=C_E(H) (F(M)=H·C_M(H) の σ'-部分; F(M)∩E=C_E(H))。
- E=E₂⋊E₁ (E₃=1), E₂ abelian (Cor 12.10b), Y⊆E₂ (τ₂-Hall of E)。
- Prop 1.6(d) coprime: Y=C_Y(E₁)×[Y,E₁], [Y,E₁]≤[E₂,E₁]=E'。
- ⟹ M'=F(M) ⟺ Y=E' ⟺ Y≤E' ⟺ **C_Y(E₁)=1**。
- **M'≤F(M) は導出可能** (M'=H×E' nilpotent normal)。**F(M)≤M' = C_Y(E₁)=1 が gap**。

**「C_Y(E₁)=1 は引用補題から導出不能」** (ChatGPT, 各補題を吟味):
- Cor 12.6(d) は E₃# 上 (E₃=1 で vacuous)、(e) は C_{E₁}(A) の Mσ 作用 (Y でない)。
- Thm 12.5 は rank-2 A の Mσ 作用 (E₁↷Y でない)。Lem 14.1 / Prop 14.2 は type-P。Thm 15.2 は MF≠Mσ。

**私の旧診断 "C_E(Mσ)=1 (Frobenius)" は過剰**: ChatGPT が明確化 — C_E(H)=E' が正しい等価条件で、
C_E(H)=1 (faithful action ≠ pointwise FPF) は strictly stronger。Frobenius (C_H(e)=1 ∀e) はさらに強い。
BG も Thm 12.12 は E₀≤E (≠E) で HE₀ Frobenius、Cor 15.9 で初めて M Frobenius (但し τ₂=∅ で E₂=1 後)。

**⚠ 未検証 (hallucination 兆候)**: 「MathComp odd-order 形式化が同じ defect を見つけ M'≤F(M) に弱めた」
は引用元が偽 (Ethiopian digital library) ゆえ**鵜呑み不可**。数学的論証 (補題不足 + abstract H⋊E local
model) 自体は妥当だが、これは minimal-simple 環境での反例でない (uniqueness 等で C_Y(E₁)=1 が出る余地)。
⟹ 等式が「真だが難 (minimal-simple 固有の深い fact)」か「genuine overstatement」かは**未解決**。

**Lean 方針**: (a) M'≤F(M) は landed piece から証明可 (~40行, E-setup+Lem12.19+直積)、
(b) 等式 residual = `C_Y(E₁)=1` (Y≤M') に厳密化。statement を `≤` に弱めるかは要ユーザー判断
(MathComp 確認 or minimal-simple 深掘り)。`fitting_not_ti_cases` は consumer ゼロゆえ緊急性低。
