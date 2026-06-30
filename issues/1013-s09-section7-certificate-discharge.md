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

### 2026-06-30 (loop¹⁴): ⭐ 訂正 — 族直交性 machinery は既存 (§7 discharge は tractable)

**重要訂正**: 「Mackey/誘導指標直交性は repo 不在 (API gap)」は**誤り**。
`OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean` に既存:
- `card_smul_restrict_induce`: **Mackey restriction** (正規部分群) `|H|•Res_H(Ind θ)=Σ_x conjBy x⁻¹ θ`。
- `inner_induce_eq_zero_of_not_conj` (L151): **非共役 irreducible の誘導は直交** `⟨Ind θ, Ind ψ⟩=0`
  (θ,ψ が distinct G-orbit)。← 族 ζ_i の **pairwise orthogonality** がこれで即。
- `card_mul_inner_self_induce_eq_card_inertia` (L172): `‖Ind θ‖²=[I_G(θ):H]` (族ノルム)。

つまり族構成の核 (orthogonality + norms) は揃っている。残:
- **族列挙**: ζ_i = Ind θ_i (Irr H の G-orbit 代表、distinct)。conjByOrbit/inertia machinery 既存。
- **ψ_i spanning CF(L,A)**: image-form spanning (eq_induce_restrict_of_supported) + 族が Ind range を覆う。
- **determination**: 直交性 + uniqueness (eq_zero_of_mem_span_orthogonal) + Gram で χ^ρ=Σ c̄_i/‖ζ_i‖² ζ_i。

**改訂 realism**: §7 discharge は当初評価の「巨大 API-gap mountain」でなく **tractable な multi-iteration build**
(核 machinery 既存)。次イテレーション = determination または族 Gram を既存直交性で構築。

### 2026-06-30 (loop再開後): ⭐ (7.7.a) determination 定理 `chiRho_decomp_proof` 完成

§7 hard floor の概念的核を達成。`S09_CertificateDischarge.lean` に (7.7.a) basis argument 全体を
sorry-free 構築 (commit 2d37fd94 まで):
- determination toolkit: spanning identity / image-form spanning / inner pos-def / uniqueness /
  supportedProj / inner_supportedProj / **eq_zero_on_A_of_inner_zero** (determination uniqueness step)。
- Gram: **inner_psi_zeta** (entry δ_{ji}‖ζ_j‖²) / **inner_psi_candidate** (sum) / **inner_psi_candidate_eq**
  (candidate 側 = c_j)。
- **chiRho_decomp_proof**: `Hypothesis76.chiRho_decomp` (7.7.a) の内容を、直交族 ζ + ψ_i spanning CF(L,A)
  + A conj-invariant を**仮説に取る形**で証明。candidate と χ^ρ が spanning {ψ_j} に同じ内積 c_j
  (chiRho_adjoint vs inner_psi_candidate_eq) → 差が直交 → eq_zero_on_A で A 上消滅。

**残**:
- **族構成** (chiRho_decomp_proof の仮説を供給): ζ_i = Ind_K^L θ_i (Irr K の G-orbit 代表)。
  orthogonality = `inner_induce_eq_zero_of_not_conj` (既存) / spanning = eq_induce_restrict + degree-0
  reduction / supported = psi_support。これで Hypothesis76 を concrete 族から構成し chiRho_decomp を discharge。
- **chiRho_eq_inner_beta (7.8.c.i)**: (7.7.a) を ζ_0=ζ, ζ_1=Ind 1_H で適用 (c_1=(β,χ), c_i=0)。

### 2026-06-30 (loop 継続): ⭐⭐ (7.7.a) discharge 完成 — chiRho_decomp_induced

**(7.7.a) の hard math 完全 sorry-free 完成。** 族構成 + determination + consolidation
全達成 (commits 57dca9c1→6859c397, S09 直接編集なし):

- **spanning** (`induce_mem_span_induce_irr`/`supported_mem_span_induce_irr`): CF(L,A) ⊆
  span{Ind θ:θ∈Irr K} (span_irreducibleCharacter_eq_top + induce 線形性)。
- **suppliers**: `induce_family_orthogonal_of_injective` (injective⟹horth via
  induce_eq_induce_iff_conj 対偶)、`supported_mem_span_psi` (covering+degree⟹hspan)、
  `induce_apply_one_ne_zero` (degree well-def)。
- **族列挙** `exists_distinct_induced_family`: distinct 誘導族を Finset.equivFin で列挙、
  injective + covering を供給。
- **capstone** `chiRho_decomp_induced`: chiRho_decomp_proof を具体族に特化、horth/hspan を
  injective/covering から導出。残入力は A⊆K^# の幾何 (hAK_off/hA_one/hAconj) のみ。
  S09 構造にも subgroupOf にも非依存 ⟹ S09 並行編集に robust。

**残 (mechanical wiring + 別 certificate)**:
- **Hypothesis76 constructor** (subgroupOf 配線): K=H.subgroupOf L で chiRho_decomp_induced を
  cite し Hypothesis76 を (7.1)+H◁L+A=H\{1}+IsDadeIsometry から構成 (certificate 不要)。
  bridges: subgroupOf normality / mem_subgroupOf 経由の hAK_off/hA_one/hAconj /
  induce_eq_zero_of_not_mem_normal (zeta vanish) / induce_diff_support (psi_support)。
- **(7.8.c.i)** `chiRho_eq_inner_beta`: (7.7.a) を ind1H/zetaDistinct で適用 + τ↔ν coherence
  collapse (χ⊥S^ν)。τ=ν on ℤ[S] 関係が要追加 (Hypothesis78 の nu field + coherence)。より深い。

### 2026-06-30 (loop 継続²): ⭐⭐⭐ Hypothesis76 constructor 完成 — hypothesis76OfDade

**(7.7.a) 主目標 完全達成** (commit 7ef9d236、axiom-clean: [propext, Classical.choice,
Quot.sound] のみ、sorryAx なし)。`hypothesis76OfDade` が Hypothesis76 を
**certificate を assume せず** (7.1)+H◁L+A=H\{1}+IsDadeIsometry から構成。
全 13 field 構成、chiRho_decomp は chiRho_decomp_induced で discharge。

- `DistinctInducedFamily` 構造体 + `distinctInducedFamily` data def (∃ でなく data;
  Type 値 Hypothesis76 構成内で projection 可能。∃ 版は corollary)。
- `subgroupOf_normal_of_conj`、bridges (mem_subgroupOf/K-normality/induce vanish/diff_support)。

**これで (7.7.a) discharge は完全に閉じた** (Hypothesis76 が (7.1) データから構成可能)。

**残 = (7.8.c.i) のみ** (これが (12.16) hB の最終 blocker):
- `chiRho_eq_inner_beta` (Hypothesis78 certificate)。χ⊥S^ν で (7.7.a) 分解が単一 β 項に collapse。
- **要追加入力**: τ↔ν coherence agreement `(τ ψ_i, χ) = (ν ψ_i, χ)` (= τ=ν on ℤ[S])。
  これは Hypothesis78 の bare field でなく **coherence statement** (§8 Dade=coherent extension)。
  (7.7.a) が induced-family 構造を要したのと同様、(7.8.c.i) は coherence agreement を要する。
- **設計**: `chiRho_eq_inner_beta_of_coherence` standalone (chiRho_decomp_induced + coherence
  agreement → collapse)。collapse algebra + index bookkeeping (ind1H/zetaDistinct/ζ_0) が山。
- **coherence agreement の所在 (調査済)**: `IsCoherent.tau1_agrees : tau1 (χ−χ.conj) = τ (χ−χ.conj)`
  (S07_Coherence.lean:1171) が Dade τ ↔ coherent extension τ₁ の agreement。S08_CoherenceCore.lean に
  `coherentYset.extension` / `inner_tau_eq_inner_restrict` (差 χ−aη の τ-内積を restrict 内積に) 多数。
  Hypothesis78 の `nu` field は coherent extension に対応するが、τ との agreement (= (τψ_i,χ)=(νψ_i,χ))
  は bare field でない → discharge theorem の hypothesis に取る (S08 の tau1_agrees 系を供給元に)。
  原文 mmd 04.9 L103-107 (7.8.c の (7.7) 適用 ζ_0=ζ,ζ_1=Ind 1_H)。S09 docstring (1419-1421) が
  「coherence-based derivation from (7.7.a) ... not yet formalized」と明記 = 既知 gap。
