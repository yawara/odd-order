---
id: 1013
slug: s09-section7-certificate-discharge
title: "lane b §7 redirect: (7.7.a)/(7.8.c) certificate を coherence から discharge"
created: 2026-06-30
---

# lane b §7 redirect: (7.7.a)/(7.8.c) certificate を coherence から discharge

## 背景 (ユーザー裁可 2026-06-30)

lane b は §12 (12.16) Dade tower の ψ-construction を完了
(`exists_witness_dadeNotation` で ψ=χ^{τ₁} 構築、he/hM も real)。残る
`CounterexampleDadeData` の **hB = (7.8.b) lower bound は `Hypothesis78` の
certificate (7.8.c.i) を要し、これは project 全体の hard floor** (lane γ
`exists_MHypothesis` も同じ理由で defer)。ユーザーが「§7 hard floor を解消」を選択
(loop⁴⁸ AskUserQuestion)。

## hard floor の正体

`S09_NonexistenceCertain.lean` (= 教科書 §7 ρ-machinery、(7.1)-(7.11)) は
**ほぼ完全 sorry-free**。ただし 2 つの深い定理が **構造の certificate field
(carried obligation)** として baked-in:

- **`Hypothesis76.chiRho_decomp` (7.7.a)** (S09:1073): `χ^ρ(x) = Σ_{i≥1} c̄_i/‖ζ_i‖² ζ_i(x)`
  for x∈A。証明 = CF(L,A)-basis argument (ψ_i=ζ_i−d_iζ_0 が span、内積 c_j=(ψ_j,χ^ρ) で
  χ^ρ を A 上で線形決定)。原文 mmd `04.9` L54-72 (p.39)。
- **`Hypothesis78.chiRho_eq_inner_beta` (7.8.c.i)** (S09:1465): χ⊥S^ν, x∈A で
  `χ^ρ(x) = star(β,χ)`。証明 = (7.7) を ζ_0=ζ, ζ_1=Ind 1_H で適用 (c_1=(β,χ), c_i=0 for i≥2)。
  原文 mmd `04.9` L103-107 (p.40)。

これらが carried field ゆえ、**coherence から `Hypothesis76`/`Hypothesis78` を構成**するには
これらを証明する必要がある。これが lane b/γ 両方の hB を unblock する根本対処。

## ⚠ S09 concurrency

S09 は別セッションが活発に編集中 (「Add S09 coherent family decomposition assembly」等 =
(7.11) 非存在 assembly、family inequality 経由)。certificate discharge とは別部分だが**同一ファイル**。
**方針: S09 を直接編集せず、新ファイル (または S07 coherence 系) で certificate proof を
standalone theorem として証明**し、衝突を避ける。頻繁に `git merge main` で再同期。

## やること (上流→下流)

- [ ] **(7.7.a)** `chiRho_decomp` を Hypothesis76 の他 field (zeta/d/psi_support/hyp71) から導く
      standalone theorem を新ファイルで証明 (CF(L,A)-basis argument)。鍵: ψ_i span CF(L,A)、
      `chiRho_adjoint` (S09 既存) で c_j=(ψ_j,χ^ρ)、基底係数 b_j=c̄_j/‖ζ_j‖²。
- [ ] **(7.8.c.i)** `chiRho_eq_inner_beta` を (7.7.a) + Hypothesis78 の他 field から導く。
- [ ] (7.8.a)/(7.8.b) は既に S09 で sorry-free (issue 2024) — 確認のみ。
- [ ] discharge 後: lane b の `exists_counterexample_dade_data` の hB を構成
      (Hypothesis78 for L を build → `NormEstimates.zetaNuRho_norm_sq_ge` cite)。

## 完了条件

`Hypothesis76`/`Hypothesis78` が coherence + 族データから (certificate を assume せず) 構成可能になり、
lane b (12.16) hB と lane γ (14.11) の h78 obligation が discharge 可能になる。

## 注意 (規模)

(7.7.a) の basis argument は CF(L,A) の線形代数 + Dade isometry adjoint を要する深い指標論。
multi-iteration。原文 mmd `04.9` L54-109 + coq `PFsection7.v` (proof strategy) を併読。

## 進捗ログ

### 2026-06-30 (loop¹⁰–¹³): (7.7.a) general foundation 4 lemma 完成

新ファイル `OddOrder/Peterfalvi/S09_CertificateDischarge.lean` に (7.7.a) basis argument の
general tool を sorry-free 構築 (S09 直接編集なし、衝突回避):
- `induce_restrict_eq_index_smul` (commit b607f7be): K◁L + ψ が K 外で消える → Ind Res ψ = [L:K]•ψ。
- `eq_induce_restrict_of_supported` (4d6f2b09): CF(L,A) ⊆ image(induce K) (ψ=Ind(e⁻¹ Res ψ))。
- `inner_self_eq_zero` (6f81457f): class function 内積の pos-def (⟨η,η⟩=0→η=0、Σ|η|²=0 経由)。
- `eq_zero_of_mem_span_orthogonal` (b87c5e8a): uniqueness — η∈span S ∧ η⊥S → η=0 (span_induction)。

**残 (structural、族依存)**:
- **族構成**: ζ_i = Ind_K^L θ_i (Irr K の L-orbit 代表)。distinctness / orthogonality
  ((Ind θ_i, Ind θ_j)=δ for distinct orbits、Mackey/Frobenius) / ψ_i=ζ_i−d_iζ_0 spanning CF(L,A)。
  これが (7.7.a) chiRho_decomp の本体 assembly に必要な残部 (general tool は揃った)。
- **chiRho_decomp assembly**: 上記 + uniqueness で χ^ρ = Σ c̄_i/‖ζ_i‖² ζ_i on A。
- **chiRho_eq_inner_beta (7.8.c.i)**: (7.7.a) を ζ_0=ζ, ζ_1=Ind 1_H で適用。

**realism**: 族構成 (orthogonality + spanning) が残る山。general foundation は完了。
