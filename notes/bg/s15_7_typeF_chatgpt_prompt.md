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

## ✅ 解決済み (2026-06-22, workflow `wddw8y3qt` で MathComp を curl 独立検証 + 数学核を独立再導出)

**provenance の明確化**: ChatGPT (GPT-5 Pro, 23m43s) 回答は「MathComp が等式を弱めた」と述べたが
**引用元として偽 source「Ethiopian digital library」を hallucinate** した。⟹ ChatGPT の source 主張は
鵜呑み不可。**だが MathComp の事実自体は workflow が実 repo を curl して独立に確定** (下記)。よって
**この発見は settled-CONFIRMED** (ChatGPT 経由でなく一次ソースで裏付け済み)。

**MathComp 一次ソース確認 (curl `math-comp/odd-order` master `theories/BGsection15.v`)**:
定理 `nonTI_Fitting_structure` (header L939) の conjunct (c) は逐語:
```coq
(*c*) M^`(1) \subset 'F(M) /\ M`_\sigma \x 'O_\sigma(M)^'('F(M)) = 'F(M),   (* L944 *)
```
= **包含 `M^'(1) ⊆ 'F(M)`** ∧ 直積分解。さらに形式化者の**明示コメント (L916-922) が smoking gun**:
> We had to change the statement of the Theorem, because the first equality of part (c) does not
> appear to be valid: if M is of type F, we know very little of the action E1 on the Sylow subgroups
> of E2, and so E2 might have a Sylow subgroup that meets F(M) but is also centralised by E1 and
> hence intersects M' trivially; luckily, only the inclusion M' ⊆ F(M) seems to be needed in the sequel.

これは私の `C_Y(E₁)≠1` 機序そのもの (E₂ の Sylow が E₁ に中心化され [E₂,E₁]=E'=M'∩E₂ の外)。
コメント L923-938 は B&G の他の修正も列挙 (12.6(d) 誤用 / X₁≠Z₀ 強化 / Lem 10.13(b) 極大性 / 等)。
下流使用 L1248, L1488。

**数学核 (workflow 独立再導出 → 全 step CONFIRMED)**: M'=F(M)⟺Y⊆E'⟺C_Y(E₁)=1 の各 step (E'⊆Y 常成立、
converse は Prop 1.6(d) を E₁↷E₂ 全体に適用) airtight、C_Y(E₁)=1 は引用補題から導出不能と確定。

**Lean 修正 DONE** (`6b82e6c6`): `fitting_not_ti_cases` conjunct (c) を `derivedInG M = fittingInAmbient M`
→ `derivedInG M ≤ fittingInAmbient M` に弱め (MathComp 包含に一致)。type-P1 実証明、type-F は ungated
residual (単一 sorry `S15_MF:7871`、W=Mσ Hall plumbing のみ)。記録は memory `bg-15-7-c-overstatement` +
issue 7007 + docstring に整合。**⚠ 再 cite 時の注意**: MathComp の事実は本物だが、ChatGPT が付けた source
は偽だった — MathComp を引くときは一次ソース (BGsection15.v) を参照すること。
