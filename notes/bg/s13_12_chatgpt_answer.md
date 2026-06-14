# ChatGPT 回答 — BG Lemma 13.12 省略再構成 (検証済, 2026-06-15 lane-f)

> 出典: ChatGPT (§13 chat, 思考 12m23s)。prompt = `s13_12_chatgpt_prompt.md`。
> 検証 = 私が全 step を dep 署名と照合・OK。raw 回答は ChatGPT tab に保存。
> ⟹ 13.12 の formalization に進める。M\*-setup + A\*-construction + Hall conjugacy が要。

## 結論: BG は P≤E₁ を仮定しない。M には Hall 共役、M\* には complement 選択で対処。

### 1. P ⊄ C_E(A) (背理法 C_{M_σ}(P)≠1 のもと)
- 12.6(a): A ◁ E (⟹ C_E(A) ◁ E)。
- P が固定 E₁ に入っていない場合: **E 内 Hall 共役** `∃ e∈E, P^e ≤ E₁` (可解 E の Hall τ₁ 部分群は共役)。
  P≤C_E(A) と仮定 → P^e≤C_E(A) (C_E(A)◁E) かつ P^e≤E₁ → x∈(P^e)#⊆C_{E₁}(A)# に 12.6(e) で
  C_{M_σ}(x)=1 → C_{M_σ}(P^e)=1 → C_{M_σ}(P)=C_{M_σ}(P^e)^{e⁻¹}=1 (M_σ◁M, e∈M)、矛盾。
  ∴ P ⊄ C_E(A)。**conj 不変**ゆえ結論は元の P について成立 (A^e=A)。
  - Lean: E₁ を P 含むよう取る or Hall 共役を挿入。Hall 共役は `S12.exists_subgroupESetup_with_le` 系
    or mathlib Hall 共役 (可解群)。

### 2. |Y|=q + ℳ(C_G(Y))={M}
- Y=C_A(P): C_A(P)≠1 (hyp), P⊄C_E(A) ⟹ C_A(P)≠A。A≅(ℤ/q)² を 𝔽_q-2次元空間、P 互いに素 (p≠q)
  線形作用 ⟹ 固定部分空間 C_A(P) は 1次元 ⟹ |Y|=q, Y∈ℰ_q¹(A)。12.6(a) で q-line of E = line of A
  ⟹ Y∈ℰ_q¹(E)。Y≤C_E(P)。
- **Thm 13.4** (p∈τ₁, P∈ℰ_p¹(E), r=q, R=Y∈ℰ_q¹(C_E(P))) ⟹ C_{M_σ}(P)≤C_{M_σ}(Y)。
  C_{M_σ}(P)≠1 ⟹ C_{M_σ}(Y)≠1。
- **12.6(c)** (Y∈ℰ¹(A), C_{M_σ}(Y)≠1) ⟹ ℳ(C_G(Y))={M}。 [accessor `.2.2.1`]

### 3. M\*∈ℳ(N_G(A)), case p∈τ₂(M\*) → 矛盾
- 12.6(b): N_G(A)⊄M ⟹ M\*≠M。A◁E, P≤E ⟹ P≤N_G(A)≤M\*。
- **12.11**: q∈σ(M\*)−β(M\*) [.1]; π(E/C_E(A))⊆τ₁(M\*)∪τ₂(M\*) [.2.1]。P⊄C_E(A)⟹p∣|E/C_E(A)|
  ⟹ p∈τ₁(M\*)∪τ₂(M\*)。
- p∈τ₂(M\*) と仮定:
  - (i) p∉σ(M\*) ⟹ P は σ(M\*)'-部分群。M\* の Hall complement E\*⊇P (`exists_subgroupESetup_with_le`)。
  - (ii) p∈τ₂(M\*) ⟹ ∃A\*∈ℰ_p²(E\*) (M\*-版 §12; `exists_mem_elemAbelianOfRank_two_le_of_tau2` 系)。
    12.6(a)/M\*: ℰ_p¹(E\*)=ℰ¹(A\*) ⟹ P≤A\*。
  - (iii) A≤M\* かつ q∈σ(M\*) ⟹ A≤M\*_σ ⟹ Y=C_A(P)≤M\*_σ ⟹ 1<Y≤C_{M\*_σ}(P)。
  - (iv) **12.6(c)/M\*** (A\*, line P, C_{M\*_σ}(P)≠1) ⟹ ℳ(C_G(P))={M\*}。
  - (v) C_{M_σ}(P)≠1 ⟹ ∃z≠1∈C_G(P)∩M_σ; ℳ(C_G(P))={M\*}⟹C_G(P)≤M\* ⟹ z∈M_σ∩M\* ⟹ ≠1。
    **Thm 12.5(e)** (M\*∈ℳ(A), M\*≠M) ⟹ M_σ∩M\*=1、矛盾。[accessor `.2.2.2.2.1`]
  - ∴ p∈τ₁(M\*)。

### 4. case p∈τ₁(M\*) → 矛盾 (13.6/M\*)
- (i) p∉σ(M\*) ⟹ Hall complement E\*⊇P、その τ₁-piece E₁\*⊇P (M\* 内 Hall; **P を共役しない**、
  M\* の補群+piece の選択)。⟹ 1<P≤E₁\* (13.6 の要求)。
- (ii) q∈σ(M\*), A≤M\* q-群 ⟹ A≤M\*_σ ⟹ Y≤M\*_σ, |Y|=q ⟹ Y∈ℰ_q¹(C_{M\*_σ}(P))。
  (13.6 が M\*_σ の Sylow q S を要求するなら Y≤S を Sylow 包含で取る。)
- (iii) **13.6/M\*** (1<P≤E₁\*, q∈σ(M\*), Y∈ℰ_q¹(C_{M\*_σ}(P))) ⟹ ℳ(C_G(Y))={M\*}。
  step2 の ℳ(C_G(Y))={M} と合わせ {M}={M\*} ⟹ M=M\*、矛盾 (M\*≠M)。
- ∴ C_{M_σ}(P)=1。∎

## Lean 化メモ
- statement に [Fact p.Prime] [Fact q.Prime] 追加 (deps が要求; τ-def は pRank ベース)。issue 2006 注記。
- M\*-setup = `S12.exists_subgroupESetup` / `exists_subgroupESetup_with_le` (P≤E\* 指定)。
- 12.6 = `S12.elemAb_normal_in_E_of_tau2` (.1.1=A◁E, .2.2.1=(c), .2.2.2.2.1=(e)); 12.11 =
  `S12.tau2_transfer_to_maximal` (.1, .2.1); 12.5(e)=`S12.Msigma_nilpotent_of_tau2 .2.2.2.2.1`;
  13.4=`S13.centralizer_le_centralizer_of_tau1`; 13.6=`S13.maximalContaining_eq_singleton_of_E1`.
- A\* 構成 = `exists_mem_elemAbelianOfRank_two_le_of_tau2` 系 (M\* に対し)。
