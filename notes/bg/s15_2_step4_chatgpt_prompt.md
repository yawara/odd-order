# ChatGPT consult — BG Theorem 15.2 step 4 (F(M) = Q·C_M(Q)) reconstruction

Sent 2026-06-16 (lane-g). Math reconstruction gap: mmd L4196-4198 "Prop 1.5(d) yields
F(M)=QC_M(Q)=C_M(Q̄)=C_{M_σ}(Q̄)⊂M_σ". Need the elided derivation, esp. C_M(Q) ⊆ F(M).

## Prompt

I'm formalizing Bender–Glauberman, "Local Analysis for the Odd Order Theorem", Theorem 15.2, in
Lean 4 and need help reconstructing one elided step. Please give a rigorous, self-contained
derivation citing only standard finite solvable group theory.

Setup. G is a minimal simple group of odd order (every proper subgroup is solvable). M is a maximal
subgroup of G. Write sigma = sigma(M) for the relevant prime set and M_sigma = O_sigma(M), the
normal sigma-core of M. We are in the case where M_sigma is NOT nilpotent. Established facts at this
point:
- q is a prime, Q = O_q(M) (largest normal q-subgroup of M), and q is in sigma.
- M_sigma / Q is nilpotent.
- D is a nilpotent complement to Q in M_sigma: M_sigma = QD, Q ∩ D = 1, and gcd(|Q|,|D|) = 1
  (Q is the q-part, D the q'-part of M_sigma); D is isomorphic to M_sigma/Q, hence nilpotent.
- Q0 = C_Q(D) is a proper subgroup of Q (proper because M_sigma is non-nilpotent).
- Qbar := Q/Q0 is a chief factor (a minimal normal subgroup of N_M(Q0)/Q0), an elementary abelian
  q-group, and C_{Qbar}(D) = 1.

Available tool (Bender–Glauberman Proposition 1.5(d)). If A is a coprime operator group on a
solvable group X (so gcd(|A|,|X|)=1) and H is an A-invariant normal subgroup of X, then
C_{X/H}(A) is the image of C_X(A) in X/H.

Claim to reconstruct (verbatim from the text). "Since D is nilpotent, but M_sigma is not,
Proposition 1.5(d) yields F(M) = Q C_M(Q) = C_M(Qbar) = C_{M_sigma}(Qbar), properly contained in
M_sigma." (F(M) = Fitting subgroup of M.)

My questions (please prove each rigorously and explicitly):
1. Why is F(M) = Q · C_M(Q)? Equivalently, why is C_M(Q) ⊆ F(M)? (I can already show
   F(M) = Q × O_{q'}(F(M)) and O_{q'}(F(M)) ⊆ C_M(Q); the gap is the reverse inclusion
   C_M(Q) ⊆ F(M).)
2. Why C_M(Q) = C_M(Qbar)?
3. Why C_M(Qbar) = C_{M_sigma}(Qbar), i.e. why does centralizing Qbar force an element of M into
   M_sigma?
4. How exactly is Proposition 1.5(d) applied (which group X, operator group A, normal subgroup H)?

Please name the standard facts you use (coprime action, the P×Q lemma / Thompson's lemma, Fitting
subgroup properties, the self-centralizing property C_M(F(M)) ⊆ F(M) for solvable M, etc.), at the
level of detail needed to formalize the argument.

## Answer (ChatGPT 最強モデル, 思考 5m45s, 2026-06-16 — 人手検証済, 正しい)

**核心 verdict**: 表示された連鎖 `F(M) = Q C_M(Q) = C_M(Q̄) = C_{M_σ}(Q̄)` は **listed hypotheses だけからは導けない**。
追加で **BG 固有の補題 `C_M(Q̄) ≤ M_σ`** が必要（標準可解群論では出ない；ChatGPT が反例提示:
`M = (C₇⋊C₃) × (C₃₁⋊C₅)`, σ={3,7}, M_σ=C₇⋊C₃ — listed 仮説を全部満たすが `C_M(Q̄)=C_M(Q)=Q×H ⊄ M_σ`,
`F(M)=Q×C₃₁`, ゆえ `C_M(Q) ⊄ F(M)`）。**私の連鎖読みの訂正**: `C_M(Q)=C_M(Q̄)` は一般に偽
（Q は Q̄=Q/Q0 を中心化するが Q 自身は非可換可）; 正しくは `Q·C_M(Q) = C_M(Q̄)`（Q 因子が効く）。

**質問への回答 (listed 仮説下)**: (1) `F(M)=Q C_M(Q)` 導けない・`C_M(Q)≤F(M)` は反例で偽 / (2)
`C_M(Q)=C_M(Q̄)` でなく `Q C_M(Q)=C_M(Q̄)`（+追加仮説）/ (3) `C_M(Q̄)=C_{M_σ}(Q̄)` 導けない・反例で偽 /
(4) Prop 1.5(d) は `X=Q, A=⟨d⟩≤D, H=Q0` で適用 → `C_D(Q̄)=C_D(Q)` を示すため。

**検証済み論証（`C_M(Q̄)≤M_σ` を仮定すれば連鎖成立）**:
1. **標準ピース `C_D(Q̄)=C_D(Q)`** (Prop 1.5d): d∈D が Q̄=Q/Q0 を中心化 ⟹ `C_{Q/Q0}(d)=Q/Q0`
   → Prop 1.5(d) (X=Q, A=⟨d⟩ coprime, H=Q0) で `C_{Q/Q0}(d)=C_Q(d)Q0/Q0` → `Q=C_Q(d)Q0`
   → Q0=C_Q(D)≤C_Q(d) ゆえ `Q=C_Q(d)` → d が Q 中心化。⟹ `C_D(Q̄)=C_D(Q)`。【§14-非依存・即形式化可】
2. **M_σ 内**: `C_{M_σ}(Q̄) = Q C_D(Q̄) = Q C_D(Q) = Q×C_D(Q)`（Q が Q̄ 中心化 [Q,Q]≤Q0;
   Q q-群・C_D(Q) q′-群・互いに中心化ゆえ direct product, nilpotent）。これは normal nilpotent ⟹ `⊆ F(M)`。
3. **逆**: F(M)≤M_σ ∧ Q≤F(M) ∧ F(M) nilpotent ⟹ F(M) は chief factor Q/Q0 を中心化（nilpotent 群は
   含む chief factor を中心化）⟹ `F(M)≤C_{M_σ}(Q̄)`。∴ `F(M)=C_{M_σ}(Q̄)=Q C_D(Q)`。
4. **追加仮説 `C_M(Q̄)≤M_σ`** で `C_M(Q̄)=C_{M_σ}(Q̄)=F(M)`。∴ `C_M(Q)⊆C_M(Q̄)=F(M)`（= (g) ⊇）。

**形式化 split (ChatGPT 推奨)**:
- `coprime_centralizes_quotient_of_Q0 : d∈D → d∈C_D(Q/Q0) → d∈C_D(Q)`（Prop 1.5d、§14-非依存、landable）
- BG 固有 `centralizer_Qbar_le_Msigma : C_M(Q/Q0) ≤ M_σ`（σ-uniqueness 構造由来、別途 source/forward-input）
- 連鎖組立（手順 2-4）→ `C_M(Q)⊆F(M)` → 既存 skeleton `fittingInAmbient_eq_sup_centralizer_inf_of_inputs`
  の `hcent` を discharge。

**⟹ 既存 (g)-equality skeleton（hcent = C_M(Q)⊆F(M)）は正しい入力を取っている**。次の層 = `C_M(Q̄)≤M_σ`
+ 連鎖で hcent を埋める（手順 1 は今 landable; 手順 2-3 は coprime/nilpotent-chief-factor 機械; `C_M(Q̄)≤M_σ`
は genuine BG gap で forward-input 化）。
