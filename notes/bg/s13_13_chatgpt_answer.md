# ChatGPT 回答 — BG Lemma 13.13 省略再構成 (検証済, 2026-06-15 lane-f)

> 出典: ChatGPT (§13 chat, 思考 11m21s)。prompt = `s13_13_chatgpt_prompt.md`。検証 = 私が全 step 照合 OK。
> ⟹ 13.13 (最後の §13 lemma) を formalize 可。13.12 完成済を使う。背理法 (p∈τ₂(M*) を否定)。

## 設定
p∈τ₁(M)∪τ₃(M), P∈ℰ_p¹(E), C_{M_σ}(P)≠1, M*∈ℳ(N_G(P))。結論 p∈σ(M*)。

### 0. 初期還元
- **Lem 12.2(a)** (`S12_ECore` prime_mem_sigma_or_tau2 系): p∈σ(M*)∪τ₂(M*)。τ₂(M*) を背理法で排除。
- **Lem 12.2(b)** (`S12_ExceptionalBridge` τ₁∪τ₃-case `not_conj_of_mem_tau1_union_tau3_of_normalizer_le`):
  p∈τ₁∪τ₃ ⟹ M* は M と非共役。
- q∈π(C_{M_σ}(P)), Q∈ℰ_q¹(C_{M_σ}(P)); Q≤M_σ ⟹ q∈σ(M); **Thm 13.9** (`S13_Theorem1310.sigma_disjoint_of_nonconjugate`,
  σ(M)∩σ(M*)=∅) ⟹ q∉σ(M*)。q≠p (q∈σ(M), p∉σ(M))。

### 1. 「P∈E₁ or E₃」= 場合分け (M 内)
- **p∈τ₃**: P≤E₃ 自動 (P は p-群, p∈τ₃, E₃=Hall τ₃ ⟹ E/E₃ で像自明 ⟹ P≤E₃)。共役不要。
- **p∈τ₁**: P≤E₁ とは限らない → **E 内 Hall 共役** `∃e∈E, P^e≤E₁` (13.12 の `exists_conj_le_tau1_piece` 再利用)。
  Q≤C_{M_σ}(P) ⟹ Q^e≤C_{M_σ}(P^e); 13.6 を (P^e,Q^e) に適用 → ℳ(C_G(Q^e))={M} → 共役戻し ℳ(C_G(Q))={M}。

### 2. p∈τ₃ 枝: Cor 13.11 で C_G(Q)≤M
- P≤E₃, P≠1 ⟹ **E₃≠1**。x∈P#⊆E₃#, Q≤C_{M_σ}(P)≤C_{M_σ}(x), Q≠1 ⟹ C_{M_σ}(x)≠1 ⟹ **E₃ not regular on M_σ**。
- **Cor 13.11(a)(c)** (`E3_not_regular_consequences` 完成済): E₁≠1, E prime on M_σ。
- E prime ⟹ C_{M_σ}(P)=C_{M_σ}(x)=C_{M_σ}(E)=C_{M_σ}(E₁) (E₁≠1)。Q≤C_{M_σ}(E₁)。
- r∈π(E₁), P'∈ℰ_r¹(E₁): 1<P'≤E₁, Q∈ℰ_q¹(C_{M_σ}(P')) (Q≤C_{M_σ}(E₁)≤C_{M_σ}(P')), q∈σ(M) ⟹
  **13.6** (`maximalContaining_eq_singleton_of_E1`) ⟹ ℳ(C_G(Q))={M} ⟹ **C_G(Q)≤M**。
- (両枝で C_G(Q)≤M。)

### 3. E*⊇PQ + A∈ℰ_p²(E*)
- P,Q≤M* (P≤N_G(P)≤M*; Q≤C_G(P)≤N_G(P)≤M*)。P,Q 可換 (Q≤C_G(P)), p≠q ⟹ PQ=P×Q 位数 pq。
  p,q∉σ(M*) ⟹ PQ は σ(M*)'-部分群 ⟹ Hall complement E*⊇PQ (`exists_subgroupESetup_with_le` の PQ 版;
  hP_pi を PQ に拡張: PQ の prime factors = {p,q} ⊆ σ(M*)ᶜ)。
- A∈ℰ_p²(E*) (`exists_elemAb_rank_two_le_E_of_tau2` for M*, p∈τ₂(M*)); 12.6(a)/M* ⟹ P≤A。

### 4. A⊄C_{E*}(Q)
- 仮に A≤C_{E*}(Q) ⟹ A≤C_G(Q)≤M ⟹ rank-2 elem-ab p ≤ M、**r_p(M)=1 に矛盾** (p∈τ₁∪τ₃ ⟹ Sylow-p of M
  は E₁/E₃ cyclic 経由で cyclic; pRank=1)。∴ [A,Q]≠1。

### 5. endgame: 12.10(c) + 13.12/M* + 12.9(c)
- **Cor 12.10(c)** (`S12_Corollary1210`): π(E*/C_{E*}(A))⊆τ₁(M*)。[A,Q]≠1 ⟹ q∈π(E*/C_{E*}(A)) ⟹ **q∈τ₁(M*)**。
- **P=C_A(Q)**: 1<P≤C_A(Q), [A,Q]≠1 ⟹ C_A(Q)<A, A=(ℤ/p)² ⟹ |C_A(Q)|=p ⟹ P=C_A(Q) (線形代数)。
- **13.12/M*** (役割 rename: p↦q∈τ₁(M*), P↦Q, q↦p∈τ₂(M*), A↦A∈ℰ_p²(E*), C_A(Q)=P≠1) ⟹ **C_{M*_σ}(Q)=1**。
- **Cor 12.9(c)** (`S12_Corollary129`): A₁=C_A(Q)=P で N_G(P)⊄M* (or C_G(P)⊄M*; C_G≤N_G)。
  M*∈ℳ(N_G(P)) (N_G(P)≤M*) と矛盾。∴ p∈σ(M*)。∎

## Lean 化メモ
- statement に [Fact p.Prime] 追加 (q は π(C_{M_σ}(P)) から取り Fact 構成可、または都度)。issue 2006 注記済。
- 再利用: `exists_conj_le_tau1_piece` (13.12 の helper), `conj_smul_centralizer`, `exists_subgroupESetup_with_le`,
  `SubgroupESetup.conj'`, Cor 13.11 (`E3_not_regular_consequences`), 13.12 (`Msigma_centralizer_eq_bot_of_tau1_tau2`),
  13.6, 13.9, Cor 12.6(a), Cor 12.9(c), Cor 12.10(c), Lem 12.2(a)(b)。
- dep 署名要確認: Cor 12.9 (S12_Corollary129:103), Cor 12.10 (S12_Corollary1210:151), Lem 12.2(a) (S12_ECore:1221),
  Lem 12.2(b) τ₁∪τ₃ (S12_ExceptionalBridge:319)。
- 大物: τ₃ 枝の 13.11 適用 (E₃ non-regular の導出) + E*⊇PQ (PQ=P×Q の σ' 性 + Hall) + 13.12/M* の役割 rename。
