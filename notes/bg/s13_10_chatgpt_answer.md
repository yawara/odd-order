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
