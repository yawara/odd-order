# BG Theorem 13.10 — ChatGPT reconstruction + verification (2026-06-15, Lane F)

ChatGPT (Pro, ~18min thinking) を Chrome MCP 経由で投げた回答。プロンプト = `s13_10_chatgpt_prompt.md`。
**全 step を自前で検証済(下記 ✅/⚠)。** 回答原文は ChatGPT conversation に保存。

## GAP A ✅ 検証OK — 重要な訂正: Q は **M の Sylow-q**、12.18 **branch-2** を使う

**核心**: 教科書の Q(E₃ の full Sylow-q)は **実は M の Sylow-q**。よって 12.18 branch-2 が発火
し、`M_α≠1` を出力(branch-1 の `M_α≠⊥` 仮定は不要)。M_α≠1 は standing fact ではなく、
この Q が Syl_q(M) であることから出る。

**`Q ∈ Syl_q(M)` の証明** (verified):
- `q ∈ τ₃(M)`, `τ₃∩σ=∅` ⟹ `q ∉ σ(M)`。`M_σ=O_{σ(M)}(M)` は σ(M)-群 ⟹ `q ∤ |M_σ|`。
- `M = M_σ E`, `M_σ∩E=1` ⟹ `|M| = |M_σ|·|E|` ⟹ `|M|_q = |M_σ|_q·|E|_q = |E|_q`。
- `E₃` = E の Hall τ₃-部分群, `q∈τ₃` ⟹ `|E|_q = |E₃|_q`。Q = full Sylow-q of E₃ ⟹ `|E₃|_q=|Q|`。
- ∴ `|M|_q = |Q|` かつ Q≤M は q-群 ⟹ `Q ∈ Syl_q(M)`。
- ⟹ **私の Brick 1 (rank-1 Q) は full Sylow-q of E₃ に改修必須**(C_Q(P)=⊥ には indecomposability)。

"(13.5)" = **displayed equation** `Q=C_Q(P)[Q,P]=[Q,P]⊆E'`(Theorem 13.5 ではない)。

## GAP B ✅ 検証OK — witness は a∈C_{M_α}(P)、xy approach は誤り

私(と prompt)の xy approach は誤り(P が Q に regular ⟹ x,y 非可換 ⟹ ⟨xy⟩≠⟨x,y⟩)。正しい:
- `C_{M_α}(P)≠1` ⟹ ∃ `a≠1, a∈M_α⊓C(P)`。`M_α≤M_σ` (Thm 10.2 = `Malpha_le_Msigma`) ⟹ a∈M_σ。
- `C_{M_α}(PQ)=1` ⟹ a は Q を中心化しない(さもなくば a∈M_α⊓C(P)⊓C(Q)=C_{M_α}(PQ)=1)。
  ⟹ ∃ `y∈Q#, [a,y]≠1`。
- `x∈P#`: `C_{M_σ}(x)=C_{M_σ}(P)` (|P|=p)。`a∈C_{M_σ}(x)` (a∈M_σ かつ a が P∋x 中心化)。
- `a∉C_{M_σ}(y)` (a∈M_σ, a が y 非中心化)。
- x,y∈(E₁E₃)# (x∈P≤E₁, y∈Q≤E₃) で `C_{M_σ}(x)≠C_{M_σ}(y)` ⟹ E₁E₃ は M_σ に prime でない。
- 13.7 の対偶 + E₁≠1 ⟹ (a) E₁ が E₃ に regular。
- Lean-friendly variant: x∈P#, a∈C(x), a∉C(xy) (∵(xy)^a=x·y^a≠xy)。x,xy∈(E₁E₃)#, prime なら
  C_{M_σ}(x)=C_{M_σ}(xy) 矛盾。可換性不要。**こちらを採用予定**(y∈E₃ も x,y版も可)。

## GAP C ✅ 構造OK — 13.8 の第2部分群 = 元の Q

- **Q (= Syl_q(M))**: N_G(Q)≤M* (M*∈ℳ(N_G(Q))), E≤N_G(Q)≤M* (Q char in E₃◁E) ⟹ Q≤M∩M*。
  任意 q-subgroup of M∩M* ≤ M, |·|≤|Q| ⟹ `Q∈Syl_q(M∩M*)`。C_Q(P)=1, P-inv。← 第2部分群。
- **Q\***: ¬(b) ⟹ C_{M_σ}(E₃)≠1 (13.3b)。q*∈π(C_{M_σ}(E₃)), Q*=E-inv Syl_q* of C_{M_σ}(E₃)。
  `C_{M_σ}(E₃)=C_{M_σ}(Q)` (E₃ prime on M_σ + Q≤E₃ nontrivial)。
  `C_{M_σ}(Q)=M_σ∩M*`: ⊆ via C_{M_σ}(Q)≤N_G(Q)≤M*; ⊇ via Cor 13.2(a) (Q が M_σ∩M* 中心化)。
  ⟹ Q* Syl_q*(M_σ∩M*)。`M∩M*=(M_σ∩M*)E`, q*∈π(M_σ), E は σ'-群 ⟹ Q*∈Syl_q*(M∩M*)。
- **N_G(Q*)⊆M**: (13.5) `Q=[Q,P]⊆E'` + 12.19 (E' が M_σ の Hall β'-部分群を中心化) ⟹
  `q*∈β(M)` ∨ `Q* Syl_q* of M_σ`。 q*∈β: Prop 10.14(d)。 q*∉β: Q* Syl of M_σ ⟹ Syl of M
  (q*∈σ, M_σ Hall σ) ⟹ σ(M) 定義で N_G(Syl)≤M, 共役で N_G(Q*)≤M。
- **C_{Q*}(P)=1**: q*∈β: ⚠ `Q*≤M_α` (β⊆α) を主張 — **要精査**(Sylow-q* of M_σ が α-core に入る根拠;
  branch2 の α=β を使う?)。Q*≤C_{M_σ}(Q)⟹Q* が Q 中心化 ⟹ C_{Q*}(P)≤C_{M_α}(P)∩C_{M_α}(Q)=
  C_{M_α}(PQ)=1。 q*∉β: Q* σ-subgroup, ℳ(Q*)≠{M} (Q*≤M*≠M) ⟹ Lemma 13.6 ⟹ C_{Q*}(P)=1。
- **p∈τ₁(M\*)**: Q*≤M_σ∩M*, C_{Q*}(P)=1 ⟹ [M_σ∩M*,P]≠1 ⟹ Lemma 13.1(a)。
- **13.8** に Q, Q* 投入 ⟹ 矛盾 ⟹ (b)。

## 形式化計画 (revised)
1. **indecomposability helper**: cyclic q-group Q + coprime P-action + ¬(Q≤C(P)) ⟹ Q⊓C(P)=⊥。
   道具: `commutator_inf_centralizer_eq_bot_of_isCommutative` + cyclic「2非自明部分群は交わる」
   (`line_le_zpowers_in_cyclic` 系)。
2. **Brick 1 改修**: full Sylow-q of E₃ + C_Q(P)=⊥ + P≤N(Q) + q∈τ₃ + **Q∈Syl_q(M)**。
   q:=minFac(|⁅E₃,P⁆|), ¬(Q≤C(P)) via Syl_q(⁅E₃,P⁆)≤Q≠⊥ + ⁅E₃,P⁆⊓C(P)=⊥。
3. **(a)+(c)**: 12.18 branch-2 (Q∈Syl_q(M)) ⟹ M_α≠1, C_{M_α}(P)≠1, C_{M_α}(PQ)=1。
   (c)=M_α≤M_σ。(a)=GAP B not-prime + 13.7 対偶。
4. **(b)**: GAP C endgame (Q*, 13.8)。⚠ q*∈β枝の Q*≤M_α を要精査。

### 進捗 (2026-06-15 Lane F /loop, このセッション)
- ✅ commit `a978a3dd`: cyclic helpers `line_le_of_ne_bot_of_le_cyclic` +
  `inf_centralizer_eq_bot_of_coprime_cyclic` (indecomposability)。
- **次イテレーションの起点 = GAP A の A.2 (Q∈Syl_q(M)) factorization**。ツール確定:
  - `card_Msigma_mul_card_E h : |M_σ|·|E| = |M|` (S12_ECore:243)。
  - `q∤|M_σ|` (q∉σ): M_σ factorization パターン = S10_BetaRadical:282-293 / 327-332
    (`(card Msigma).factorization q` 経由)。q∉σ→q∉π(M_σ)。要 helper or inline。
  - `(card E).factorization q = (card E₃).factorization q` (E₃ Hall τ₃, q∈τ₃):
    Hall factorization。`h.E₃_hall` + subgroupOf card。S12_E:175 パターン。
  - ⟹ `(card M).factorization q = (card E₃).factorization q`。
  - full Sylow Q := `(Sylow q ↥E₃).map E₃.subtype`; `card Q = q^(v_q|E₃|)`;
    rank-1 Brick 1 の Q'(order q)≤Q + `inf_centralizer_eq_bot_of_coprime_cyclic` で C_Q(P)=⊥;
    `eq_of_le_of_isPGroup_card_eq_factorization` (13.9 brick) で Q maximal q-subgroup of M。
- 手順: 全 Sylow brick (Q∈Syl_q(M)+C_Q(P)=⊥) → 12.18 branch-2 → M_α≠1 等 → (c) +
  GAP B not-prime → (a) → GAP C → (b) → 13.11。

### 進捗² (2026-06-15 Lane F /loop, cont.)
- ✅ commit `5dd5b286`: `factorization_M_eq_E3_of_mem_tau3` (GAP A の A.2)。
- ✅ commit `7e8766ed`: `exists_tau3_sylowM_regular_of_not_centralize` (GAP A 完了 —
  Q∈Syl_q(M) かつ C_Q(P)=⊥; full build 緑 3813)。⟹ **12.18 branch-2 への入口が揃った**。
- **次 = (c)+(a)**: full-Sylow brick の Q で M* 抽出 (`exists_maximal_over_normalizer_not_conj_of_le_E3`)
  → `tau1_Malpha_interaction` branch-2 で `M_α≠1 ∧ C_{M_α}(P)≠1 ∧ C_{M_α}(P⊔Q)=1`。
  - (c): `C_{M_α}(P)≠1` + `Malpha_le_Msigma` ⟹ `S10.Msigma M ⊓ C(P) ≠ ⊥`。
  - GAP B not-prime → (a): `a∈C_{M_α}(P), a≠1` (a∈M_σ, a が P 中心化)。`C_{M_α}(P⊔Q)=1` ⟹ ∃y∈Q#,
    a∉C(y)。x∈P#: a∈C_{M_σ}(x)。a∉C_{M_σ}(y)。x,y∈(E₁⊔E₃)# で fixedByElement 不一致 ⟹
    ¬ActsPrimeOn M_σ (E₁⊔E₃)。`E1E3_actsPrime` の対偶 (mt) + E₁≠⊥ (P≠⊥) ⟹ (a)。
  - 12.18 の正確な引数 = `tau1_Malpha_interaction hG h.mem_maximal hqp hpτ1 hP hPM hQM hQne hQq hQinv hCQP hMNQ |>.2 hQsyl`
    (branch-2、`.2` + `hQsyl`=Q maximal q-subgroup of M)。hMNQ = M* 抽出から `≠{M}`。
- 次々 = (b) GAP C (Q*, 13.8) → 13.11。

### 進捗³ (2026-06-15 Lane F /loop, cont.²) — GAP A/B 完了, 13.10 (a)+(c) 証明済
- ✅ `b7fdd250` `malpha_centralizer_facts_of_not_centralize` (12.18 branch-2)。
- ✅ `f1834ba1` `not_actsPrime_Msigma_of_malpha_facts` (GAP B)。
- ✅ `a0994d55` 13.10 **(a)+(c) 証明完了**; statement に **p.Prime 付与**(`elemAbelianOfRank` は
  合成数 p を許す[Z/p²]ので BG ℰ_p¹[p素数]に faithful 化; 下流参照ゼロゆえ安全)。残 sorry =
  13.10 (b) [GAP C] + 13.11。full build 緑 3813。
- **次 = (b) GAP C** (S13_PrimeActionTransition.lean の 13.10 内 `· -- (b)` の sorry):
  ¬(E₃ reg on M_σ) → 矛盾。手順 (notes 上記 GAP C 節):
  1. witness P (∈ℰ_p¹,¬centralize) で full-Sylow brick → q,Q∈Syl_q(M),C_Q(P)=⊥,Q≤E₃。
  2. M*抽出 (`exists_maximal_over_normalizer_not_conj_of_le_E3`) → M*,N(Q)≤M*,M*≠M。
  3. 仮定 ¬(E₃ reg M_σ) ⟹ C_{M_σ}(E₃)≠1 (`cyclicSylow_actsPrime hG h |>.2` = E₃ prime; ¬reg)。
  4. q*∈π(C_{M_σ}(E₃)); Q*=E-inv Syl_q*(C_{M_σ}(E₃)); C_{M_σ}(E₃)=C_{M_σ}(Q) (E₃ prime+Q⊆E₃≠1);
     =M_σ∩M* (Cor13.2a `tau13_pSubgroup_centralizes .1` ⊇ ; ⊆ via N(Q)≤M*)。
  5. Q*∈Syl_q*(M∩M*)。(13.5)[Q=[Q,P]⊆E'… 要 displayed eq の Lean 形]+12.19 → q*∈β ∨ Q* Syl(M_σ)
     → N(Q*)⊆M (Prop10.14d `normalizer_le_of_nontrivial_beta_subgroup` / σ-def)。
  6. C_{Q*}(P)=1 (q*∈β: Q*≤M_α[要精査]+Q* cent Q ⟹ ⊆C_{M_α}(PQ)=1; q*∉β: 13.6 ℳ(Q*)≠{M})。
  7. [M_σ∩M*,P]≠1 ⟹ 13.1(a) p∈τ₁(M*) ⟹ 13.8 `forbidden_config_impossible` (Q,Q* 両 maximal)。
  ⚠ 要 E-invariant Sylow 抽出 + C_{M_σ}(E₃)=C_{M_σ}(Q) + (13.5) Lean 形 + q*∈β枝 Q*≤M_α。最難。

### 進捗⁴ (2026-06-15 Lane F /loop, cont.³) — GAP C preliminaries 完了
- ✅ `8a7888c0` `centralizer_Msigma_eq_of_le_E3_of_actsPrime` (C1: C_{M_σ}(E₃)=C_{M_σ}(Q), E₃ prime+Q≤E₃≠⊥)。
- ✅ `4359f48a` `inf_Msigma_Mstar_eq_centralizer_Q` (C2: M_σ∩M*=C_{M_σ}(Q), Cor13.2a+C(Q)≤N(Q)≤M*)。
  ⟹ **C1+C2: `C_{M_σ}(E₃) = M_σ∩M*`** 確立。
- 🔑 **真 Lemma 12.19** = `S12_E:269` `**BG Lemma 12.19**` (E' が M_σ の Hall β'-部分群中心化);
  wrapper = `derivedE_centralizes_betaComplement hG h` (S13_PrimeAction:938 で使用例)。
  ⚠ 「`beta_complement_normalizer_derived_contains_sylow`」は **Cor 10.9(a)(3)** であって 12.19 ではない。
- 🔑 **GAP C step 5 の precedent** = `exists_E1inv_sylow_centralizing_derivedE` (S13_PrimeAction:930):
  q∉β(M) で E₁-inv Sylow-q of M_σ ⊆ C_G(E') を構成 (12.19 + `exists_aInvariant_sylow_subgroup`)。
  Q* (q*∉β) はこれと同型に「Q* が M_σ の Sylow」を出せる。q*∈β は Prop10.14(d)。
- **次イテレーション = GAP C coupled core** (13.10 内 `· -- (b)` の sorry を埋める, ~100 行):
  witness P → full-Sylow brick (q,Q∈Syl_q(M),C_Q(P)=⊥,Q≤E₃,hQsyl) → M*抽出 →
  ¬reg ⟹ C_{M_σ}(E₃)≠1 (`cyclicSylow_actsPrime hG h |>.2` で E₃ prime) → C1+C2 で =M_σ∩M* →
  q*∈π, Q*=E-inv Sylow-q* of M_σ∩M* (要 `exists_aInvariant_sylow_subgroup` on M_σ∩M*) →
  Q*∈Syl_q*(M∩M*) → step5 (12.19 dichotomy → N(Q*)⊆M) → step6 (C_{Q*}(P)=1) →
  13.1(a) p∈τ₁(M*) → 13.8 `forbidden_config_impossible` (Q,Q* 両 maximal q-/q*-subgroup of M⊓M*)。
  ⚠ 最難 sub-step: Q*∈Syl_q*(M∩M*) の factorization, step5 dichotomy, step6 q*∈β枝 Q*≤M_α。

### 進捗⁵ (2026-06-15 Lane F /loop, cont.⁴) — GAP C construction bricks 完了
- ✅ `8a7888c0` C1 + `4359f48a` C2 + `35993790` D1
  (`exists_Einvariant_sylow_inf_Msigma_Mstar`: E-inv Sylow-q* of M_σ∩M*, card=q*^(v_q*|M_σ∩M*|))。
- **残り = GAP C analytical core (D2–D5)**, 13.10 内 `· -- (b)` の sorry を埋める:
  - **D2 `Q*∈Syl_q*(M∩M*)`**: v_q*(|M∩M*|)=v_q*(|M_σ∩M*|)。M∩M*=(M_σ∩M*)E (Dedekind, E≤M*);
    q*∈π(M_σ)⊆σ, E は σ'-群 ⟹ q*-part は M_σ∩M* から。`eq_of_le_of_isPGroup_card_eq_factorization`。
    (factorization_M_eq_E3 brick と同型の論法。Dedekind = `Subgroup.sup_inf_...`?要確認)
  - **D3 `N(Q*)⊆M`**: (13.5)[Q=[Q,P]⊆E', C_Q(P)=⊥ から coprime cover] + 12.19
    (`derivedE_centralizes_betaComplement`: E' が M_σ の Hall β'-部分群 W 中心化) ⟹
    q*∈β ∨ Q* Syl(M_σ)。q*∈β: `normalizer_le_of_nontrivial_beta_subgroup` (Prop10.14d)。
    q*∉β: Q* Syl(M_σ) (W に Q* が入る, precedent `exists_E1inv_sylow_centralizing_derivedE` 同型)
    → q*∈σ, M_σ Hall σ ⟹ Q* Syl(M) → σ-def で N(S)⊆M, 共役 → N(Q*)⊆M。
  - **D4 `C_{Q*}(P)=⊥`**: q*∈β: Q*≤M_α (β⊆α; ⚠ Sylow-q* of M_σ が α-core か要精査) + Q* cent Q
    ⟹ C_{Q*}(P)≤C_{M_α}(P)∩C_{M_α}(Q)=C_{M_α}(P⊔Q)=1 (12.18 package の hCMαPQ)。
    q*∉β: Q* σ-subgroup, ℳ(Q*)≠{M} (Q*≤M*≠M) ⟹ Lemma 13.6 (`centralizer_sylow_inf_eq_bot`系
    or maximalContaining_eq_singleton 系) ⟹ C_{Q*}(P)=⊥。
  - **D5 assembly**: 13.1(a) `mem_tau1_Mstar_of_einvariant_sylow` で p∈τ₁(M*) → 13.8
    `forbidden_config_impossible` (Q: hQsyl で maximal q of M⊓M*; Q*: D2 で maximal q* of M⊓M*;
     両 C(P)=⊥; N(Q)≤M*, N(Q*)≤M; P≤N(Q),N(Q*))。13.9 endgame の `forbidden_config_impossible`
     呼び出しが template (但し 13.9 は Q=Q*=S、ここは別 Q,Q*)。
  ⚠ D3/D4 が最難 (12.19/13.6 dichotomy)。fresh context 推奨。

### 進捗⁶ (2026-06-15 Lane F /loop, cont.⁵) — D2 完了
- ✅ `8e6e35d6` D2 `sylow_Msigma_Mstar_maximal_in_inf` (Q* maximal q*-subgroup of M∩M*;
  σ-subgroup ≤ M_σ 経由で Dedekind 回避)。GAP C は construction(C1/C2/D1)+ maximality(D2)完了。
- **残り = D3 (N(Q*)⊆M) / D4 (C_{Q*}(P)=⊥) / D5 (13.8 assembly)**:
  - **D3a 前提 (13.5) `Q ≤ derivedInG E`**: `le_commutator_of_coprime_inf_centralizer_eq_bot`
    (S08:1424, B=P[solvable],Y=Q,P≤N(Q),coprime,Q⊓C(P)=⊥ ⟹ Q≤⁅P,Q⁆) + ⁅P,Q⁆≤⁅E,E⁆=derivedInG E
    (P,Q≤E, commutator mono)。clean brick 候補。
  - **D3 本体 (q*∉β枝)**: 12.19 `derivedE_centralizes_betaComplement` → W (Hall β' of M_σ, E'⊆C(W));
    Q≤E' ⟹ Q⊆C(W) ⟹ W⊆C(Q), W⊆M_σ ⟹ W⊆M_σ∩M*(=C_{M_σ}(Q)); q*∉β ⟹ W の q*-part full
    ⟹ v_q*(M_σ∩M*)=v_q*(M_σ) ⟹ Q* full Sylow of M_σ ⟹ (q*∈σ,M_σ Hall) Q* Sylow of M ⟹
    σ-def で N(Q*)⊆M。(q*∈β枝): `normalizer_le_of_nontrivial_beta_subgroup` (Prop10.14d)。
  - **D4**: q*∉β: Q* σ-subgroup, ℳ(Q*)≠{M} ⟹ Lemma 13.6。q*∈β: Q*≤M_α (要 M_α Hall α =
    `isHall_Msigma_Malpha .2` で α-subgroup≤M_α) + Q*⊆C(Q) ⟹ C_{Q*}(P)⊆C_{M_α}(P⊔Q)=1。
  - **D5**: `mem_tau1_Mstar_of_einvariant_sylow` (p∈τ₁M*) + `forbidden_config_impossible` (13.8)。
  ⚠ D3 本体の 12.19 W-factorization が最難。fresh context で。

### 🎉🎉 進捗⁷ (2026-06-15 Lane F /loop, cont.⁶) — Thm 13.10 COMPLETE
- ✅ `509be28d` D3a (13.5 `Q≤derivedInG E`) + `ae0b50ce` D3b (12.19 W-factorization) +
  `ddeb3a3c` D4 (`Q*⊓C(P)=⊥` β-dichotomy) + `90df362c` D3 (`N(Q*)⊆M` β-dichotomy) +
  `289bd623` **13.10 (b) 本体 = Lemma 13.8 で矛盾 → Thm 13.10 (a)(b)(c) 全完成**。
- full build 緑 3813 / AxiomsCheck OK。**§13 endgame の残り実 sorry は Cor 13.11 のみ**。
- ⚠ 知見: helper の **未使用 implicit prime `{q}[Fact q.Prime]`** は call site で metavariable 化し
  `Fact` typeclass resolution を stuck させる(C1/D3/D4 で発生・削除した)。未使用の setup implicit
  `E E₁ E₂` も `rw` で metavariable 化(C1)。helper は使う変数だけ implicit に。

### Cor 13.11 `E3_not_regular_consequences` 計画 (mmd L3732-3741)
仮説: E₃≠⊥, ¬ActsRegularlyOn(M_σ,E₃)。結論 (a)E₁≠⊥ ∧ (b)E=E₁⊔E₃ ∧ (c)ActsPrimeOn(M_σ,E) ∧
(d)∀ X∈ℰ¹(E),X≤E → E≤N(X)。
- (a)(b): Cor 12.6(d) で τ₂(M) empty → Lemma 12.1 / `SubgroupESetup.eq_sup`(+E₂=⊥) で E=E₁⊔E₃,
  E₁≠⊥。`E_eq_sup_of_E3_centralizer` 系 (13.7 work) が近い。要 τ₂ empty 補題特定。
- **E₁ ¬reg on E₃**: 13.10 の対偶 — ¬(E₃ reg on M_σ) ⟹ ¬∃P∈ℰ_p¹(E₁) not-centralizing
  ⟹ ∀ P centralize E₃ ⟹ E₁ centralizes E₃ ⟹ (E₃≠⊥) E₁ ¬reg on E₃。
- (c): `E1E3_actsPrime hG h hE1ne (E₁ ¬reg on E₃)` = E₁E₃ prime on M_σ; E=E₁⊔E₃ ((b)) ⟹ E prime。
- (d): ∀P∈ℰ_p¹(E₁) centralize E₃ + E=E₁⊔E₃ + E₁,E₃ cyclic + E₃◁E ⟹ ℰ¹(E) 正規。要設計。
⚠ 13.10 の対偶適用に p.Prime 必要(13.10 hP/(c) は p 素数版に修正済)。X∈ℰ¹(E) の p も素数化注意。
