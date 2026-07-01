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

### 2026-06-30 (loop 継続³): (7.8.c) core 5 lemma 完成 + 詳細 proof 確定

原文 (7.8.c) proof 完全解読 (mmd 04.9 L103-107): (7.7) を **ζ_0=ζ (zetaDistinct),
ζ_1=Ind 1_H** で適用 → c_1=(β,χ), c_i=0 (i≥2)。生存項 (c̄_1/‖ζ_1‖²)ζ_1(x) は
**ζ_1(x)=‖ζ_1‖²=e** (x∈A、Ind 1_H の特殊性) ゆえ c̄_1=star(β,χ) に collapse。

**(7.8.c) の reusable core を全 sorry-free 構築** (commits c5eec18c→95f79715):
- `conjBy_trivialClassFunction` / `induce_trivialChar_apply_eq_index` ((Ind 1_K)(x)=[L:K] for
  x∈K) / `induce_trivialChar_normSq_eq_index` (‖Ind 1_K‖²=[L:K]、inertia(1_K)=⊤+card_top)。
- `sum_collapse_to_single`: (7.7.a) 和で c_i が i₁ 以外消滅 + ζ_{i₁}(x)=‖ζ_{i₁}‖² なら star(c_{i₁})。
- `inner_sub_smul_left_eq_zero`: χ⊥{a,b} ⟹ (a−d•b,χ)=0 (coherence 係数消滅核)。

**残 = 大 assembly `chiRho_eq_inner_beta_induced`** (chiRho_decomp_induced と parallel な standalone):
入力 = H71, K, θ (rep family, inj+cover), ind1H/zetaDistinct, **hzeta_ind1H: θ ind1H=trivial**,
degree 関係, **ν + coherence agreement** `(ζ_i−d_iζ_zd)^τ=νζ_i−d_i•νζ_zd` (i≠ind1H),
**χ⊥S^ν** `inner χ (νζ_i)=0` (i≠ind1H), geometric facts。証明 =
(1) family を **Equiv.swap 0 zetaDistinct** で permute → chiRho_decomp_induced 適用 (ζ'_0=ζ_zd)、
(2) i₁=swap(ind1H) (≠0 ∵ ind1H≠zd)、(3) c'_i=0 (i≠i₁) via inner_sub_smul_left_eq_zero、
(4) c'_{i₁}=(β,χ) (d'_{i₁}=1 ∵ degree)、(5) building blocks で ζ'_{i₁}(x)=‖ζ'_{i₁}‖²=K.index、
(6) sum_collapse_to_single → star(β,χ)。次に `hypothesis78OfDade` constructor で配線
(hyp76 を hypothesis76OfDade で構築 ⟹ zeta=Ind∘θ、ind1H/zetaDistinct 設定、ν+agreement 入力)。

### 2026-07-01 (loop 継続⁴): ⭐⭐⭐ (7.8.c.i) formula discharge 完成 — chiRho_eq_inner_beta_induced

**(7.8.c.i) certificate formula を sorry-free + axiom-clean で証明** (commit 32ede97d、
[propext, Classical.choice, Quot.sound] のみ)。permutation を回避する設計:
**区別された ζ を index 0 に固定** (Ind 1_K は ind1H≠0)。証明 =
chiRho_decomp_induced ((7.7.a)) → sum_collapse_to_single で ind1H 項に collapse
(非 ind1H 係数 = hagree (coherence τ=ν on S 差分) + hortho (χ⊥S^ν) +
inner_sub_smul_left_eq_zero で消滅; ζ_{ind1H}=Ind 1_K ゆえ building blocks で hcrux)。
結論 χ^ρ(x) = star((ζ_{ind1H}−d_{ind1H}ζ_0)^τ, χ)。

**§7 hard floor の core math 完成**: (7.7.a) chiRho_decomp_induced + (7.8.c.i)
chiRho_eq_inner_beta_induced + hypothesis76OfDade、全 axiom-clean。

**残 = `hypothesis78OfDade` constructor (最終 integration)**:
- 入力 = H71+hτ+H◁L+A=H\{1} (hyp76OfDade 経由) + coherence data (S coherent の ν +
  agreement + 区別された ζ∈S∩Irr L of degree e)。
- **family arrangement**: chiRho_eq_inner_beta_induced は index 0=区別 ζ を要求。
  distinctInducedFamily は任意順 → swap(0, j_ζ) で ζ-rep を index 0 に配置 (j_ζ=ζ の index)。
  ind1H = swap(0,j_ζ) j_triv (j_triv = Ind 1_K の index、∃ ∵ trivial の orbit={trivial})。
- 全 Hypothesis78 field 構築 + chiRho_eq_inner_beta_induced で certificate discharge。
- これで Hypothesis78 構成可能 → (12.16) hB + lane γ (14.11) h78 unblock。
- **代替検討**: (7.8.b) `zetaNuRho_norm_sq_ge` も formula discharge 可能か (full Hyp78 構成回避)。
  hB が要するのは (7.8.b) ゆえ、(7.8.b) を直接 formula 化できれば constructor 不要かも。次回精査。

### 2026-07-01 (loop 継続⁵): landscape 確定 + (7.8.c.i) toolkit 完備 + 残務 map

**(7.8.c.i) toolkit 完備** (commit 132c7d8f): `induce_family_comp_perm_injective/covering` 追加。
これで chiRho_eq_inner_beta_induced (index-0 formula) + 再添字付け primitive が揃い、§12 calc は
Equiv.swap 0 j で区別 ζ を index 0 配置 → 適用可能。constructor (hypothesis78OfDade) は不要に
(§12 calc が inline 構成、formula を cite)。

**重要な landscape 発見**:
- **最終 consumer = `exists_counterexample_dade_data` (S14:2740) は単一 giant sorry** —
  CounterexampleDadeData の全 ~24 field (witness L 構成 + Dade τ₁ + coherent S + ψ=χ^{τ₁} +
  norm bounds hA/hB/hC + 整数/次数 facts) を産出する (12.16) 本体の山。hB=(7.8.b) は単なる
  1 field (`1-e/kH ≤ normRho` の実不等式)。§7 norm estimates はその ingredient。
- **§7 floor 残 = (7.8.a)+(7.8.b)** (coherence-dependent、meaty だが tractable):
  既存機構 (7.7.b) `chiRho_norm_sq_double_sum` (S09:90) + (2.7) `chiRho_adjoint` (S09:335) +
  Hyp78 helpers (beta/weightedNuSum/zetaNuRho/zetaNuRhoNormSq/kernelOrder/complementIndex/
  smallIndex) 全在。(7.8.a) BetaDecomp (orth_one: S^ν⊥1_G + 整数 a/残余 Γ 分解) →
  (7.8.b) NormEstimates (‖ζ^{νρ}‖²≥1-e/h via (7.7.b)+(7.8.a)+coefficient 計算 c_1=a,c_2=1)。
- **完成済 (全 axiom-clean、reusable)**: (7.7.a) chiRho_decomp_induced + hypothesis76OfDade +
  (7.8.c.i) chiRho_eq_inner_beta_induced + toolkits。lane γ (14.11 h78) も §7 を共有消費。
- **次**: (7.8.a) → (7.8.b) formula discharge (上流順)。両者は ν の coherence ((2.7)+orthonormality)
  を入力に取る形 (carrier-conditional)。

### 2026-07-01 (loop 継続⁶): (7.8.a) orth_one の完全 proof map + honest ingredient 1 件

**(7.8.a) orth_one (S^ν⊥1_G) の carrier-conditional proof を完全に map した** (tractable):
`(ν ζ_i, 1_G)=0` (i≠ind1H) の導出 =
1. coherence agreement `ν ζ_i − d_i ν ζ_0 = (ζ_i−d_iζ_0)^τ` (ζ_0=区別 ζ) で
   `(ν ζ_i,1_G) = ((ζ_i−d_iζ_0)^τ,1_G) + d_i(ν ζ_0,1_G)`。
2. `((ζ_i−d_iζ_0)^τ,1_G) = (ζ_i−d_iζ_0, (1_G)^ρ)` [`chiRho_adjoint` (2.7)、S09:335 既存]
   `= (ζ_i−d_iζ_0, 1_L)` [`chiRho_constOne` (S09:500): (1_G)^ρ=1 on A 既存 + support-inner fact]
   `= 0` [`inner_induce_constOne_eq_zero` 本commit、ζ_i,ζ_0 は非主誘導 ⊥1_L]。
3. `d_i(ν ζ_0,1_G) = 0` [coherence input `(ζ^ν,1_G)=0`、区別 ζ の像 ⊥1_G]。

**honest §7 ingredient `inner_induce_constOne_eq_zero` 完成** (commit 3c3069f2):
θ≠1_K で (Ind θ,1_L)=0。orth_one step 2 の核。**残 helper = support-restricted inner**
(`(α,ψ)=(α,ψ')` if ψ=ψ' on supp α) + **coherence inputs 2 件** (agreement + (ζ^ν,1_G)=0)。

**状況整理 (honest)**: §7 floor の **reusable hard math は完了** ((7.7.a) chiRho_decomp_induced +
hypothesis76OfDade + (7.8.c.i) chiRho_eq_inner_beta_induced + 全 toolkit/building blocks、
全 axiom-clean、lane γ 14.11 とも共有)。残 (7.8.a)/(7.8.b) は **§8-coherence carrier-conditional
な grind** (ν の (2.7)-agreement + ζ^ν⊥1_G + 整数 a を入力に取る; これらは Hypothesis78.nu の
bare field でなく §8 coherence primitive)。最終 consumer = exists_counterexample_dade_data
(giant §12 sorry)。carrier-conditional discharge は hyp76OfDade と同様 legitimate
(§7 reasoning は実証明、§8 primitive のみ入力)。

### 2026-07-01 (loop 継続⁷): (7.8.a) orth_one discharge + lane-b-tractable 境界の確定

**(7.8.a) orth_one field を carrier-conditional に discharge** (commits 5d98039d, 411d4df4):
- `inner_eq_of_eqOn_support` (support-inner)、`inner_tau_supported_constOne` ((2.7)-for-1_G:
  ⟨α^τ,1_G⟩=⟨α,1_L⟩)、`inner_induce_constOne_eq_zero` (非主誘導⊥1_L)。
- `betaDecomp_orth_one`: agreement (hagree) + (ζ_0^ν,1_G)=0 (hzeta0nu) から ∀i≠ind1H で
  (ζ_i^ν,1_G)=0。**入力は simple coherence primitive のみ** (hoisting でない)。

**⚠ lane-b-tractable 境界の確定 (重要)**: 残 BetaDecomp field (整数 a / Gamma / **Gamma_orth_nu**
/ beta_eq) と (7.8.b) norm bounds は **§5/§8 coherence STRUCTURE を要し carrier-conditional 化
できない**。Gamma_orth_nu = ⟨Γ,ζ_i^ν⟩=0 は ⟨β,ζ_i^ν⟩ (= (ζ_ind1H−ζ_0)^τ と ζ_i^ν の内積、
ζ_i^ν の ρ-projection 経由) + 整数 a の特定値を要し、**これは hard content そのもの** (入力に
取れば hoisting = 禁止 [[scaffold-sorry-free-not-done]])。根本原因 = **Hypothesis78.nu が
abstract free field** (nu_isometry のみ; 実 §8 coherent extension と非接続) ゆえ ν の
integer-coefficient structure / (β,ζ^ν) 関係が無い。

**完了に要する cross-lane integration**: (a) Hypothesis78.nu を実 §8 coherent extension に接続
(S09 structure 変更、並行編集注意) **or** (b) §8 coherence machinery が (β,ζ^ν) 関係を直接供給。
→ **lane-b 単独で §7 floor を閉じる tractable 部分は orth_one まで**。残は §8 coherence
(Pf §1-9 spine、実質 sorry-free のはずだが Hypothesis78.nu との接続が未) との integration。

### 2026-07-01 (loop 継続⁸): ⭐ 自己訂正 — (7.8.a) Gamma_orth_nu は **tractable** (τ isometry 経由)

**前回の「Gamma_orth_nu は §8-integration blocked」評価は ERROR だった** ((7.8.c) の (β,χ)
ρ-formula と (7.8.a) の (β,ζ^ν) を混同; 後者は ρ 不要)。原文 (7.8.a) proof (mmd L63-72) 精読で確定:
`(β, φ^ν − (φ(1)/e)ζ^ν) = (β, (φ−(φ(1)/e)ζ)^τ)` [coherence agreement] `= ((Ind1H−ζ)^τ, (φ−cζ)^τ)`
[β=(Ind1H−ζ)^τ] `= (Ind1H−ζ, φ−cζ)` [**IsDadeIsometry.inner_eq** (τα,τβ)=(α,β)、S04:3720 既存]
`= φ(1)/e` [family 直交性]。これと (β,ζ^ν)=a−1 から (β,φ^ν)=(φ(1)/e)·a、よって a_φ=a·φ(1)/(e‖φ‖²)、
Gamma_orth_nu (⟨Γ,φ^ν⟩=0) が出る。**ρ は一切不要**。

**(7.8.a) は carrier-conditional に tractable** (入力 = coherence agreement のみ; IsDadeIsometry +
nu_isometry (Hyp78 field) + family 直交性 (induce_family_orthogonal) は既存)。orth_one と同様
legitimate (hoisting でない、§7 reasoning 実証明)。整数 a = (β,ζ^ν)+1 ∈ ℤ は β,ζ^ν virtual char
から (integrality 別途)。残構築 = family-diff 内積 + (β,ζ_i^ν) 計算 + a + Γ + 全 orthogonality。
区別 ζ∈Irr L (‖ζ‖²=1) の irreducibility が family setup property。

### 2026-07-01 (loop 継続⁹⁻): (7.8.a) orthogonality 全 field 完成 + (7.8.b) scoping + 戦略 checkpoint

**(7.8.a) BetaDecomp の orthogonality 3 field を全て carrier-conditional に discharge** (axiom-clean):
`betaDecomp_orth_one` (S^ν⊥1_G) + `betaDecomp_gamma_orth_nu` (Γ⊥S^ν) + `betaDecomp_gamma_orth_one`
(Γ⊥1_G)。computation ingredient: inner_eq_of_eqOn_support / inner_tau_supported_constOne /
inner_induce_constOne_eq_zero / inner_induce_trivialChar_constOne_eq_one / inner_family_diff /
inner_beta_nuDiff / inner_beta_nu_eq / inner_weightedNuSum_nu / induce_apply_one_star。
`beta_eq` は Γ 定義から trivial。**S09_CertificateDischarge.lean = 47 宣言, 1272 行, 全 sorry-free。**

**§7 floor の現況 (honest, ~20 loop 後)**:
- ✅ **完了 (reusable, axiom-clean)**: (7.7.a) chiRho_decomp_induced + hypothesis76OfDade、
  (7.8.c.i) chiRho_eq_inner_beta_induced + reindexing toolkit、(7.8.a) orthogonality 全 field +
  全 computation ingredient。lane γ 14.11 も共有消費。
- 🔒 **残 (7.8.b) NormEstimates は深く gated**: zetaNuRho_norm_sq_ge (‖ζ^{νρ}‖²≥1−e/h) は
  **H78-level** (chiRho_norm_sq_double_sum (7.7.b、S09:1336) を χ=ζ^ν に適用、ν 経由) +
  **整数 a∈ℤ** (ν→ℤ[Irr] integrality に gated、(7.8.a) の agreement より深い) +
  **degree-sum (1.5.d) Σθ(1)²=|H|** (repo/mathlib に未在、foundational gap) + quadratic
  (S09 normQuadraticCorrection_nonneg 既存) を要す。(7.8.a) より substantially 深い。
- 🔗 **実 consumption は H78 construction (hypothesis78OfDade) に gated**: chiRho_eq_inner_beta_induced
  を cite して H78 を構成 → lane γ 14.11 h78 unblock + (12.16) hB 経路。要 family arrangement
  (区別 ζ を index 0; reindexing primitive 既存 + hypothesis76OfFamily refactor) + coherence
  agreement carrier 入力。

**次の戦略 fork** (lane b 自律判断 = hypothesis78OfDade integration を優先):
chiRho_eq_inner_beta_induced を **consumable にする** (H78 構成 → lane γ unblock) が最高価値。
path = hypothesis76OfFamily (hyp76OfDade を θ パラメタ化 refactor) → 区別 ζ を index 0 配置
(induce_family_comp_perm) → hypothesis78OfDade (全 H78 field + certificate)。次 loop で着手。

### 2026-07-01 (loop 継続¹¹⁻): hypothesis78OfDade 完成 — H78 構成可能 (issue 核 達成)

**`hypothesis78OfDade` 完成** (S09_CertificateDischarge.lean, 55 宣言, 全 sorry-free, axiom-clean):
`Hypothesis78` 全体を (7.1)/(7.6) データ + coherence 入力から構成、**(7.8.c.i) certificate を
assume せず** `chiRho_eq_inner_beta_induced` で discharge。

途中で抽出した再利用部品:
- **`hypothesis76OfFamily`**: hypothesis76OfDade を任意 inj+cover 族 θ でパラメタ化 (区別 ζ を
  index 0 に配置した族で H76 構成可能に)。hypothesis76OfDade は薄い wrapper。
- **sharp-support 幾何 5 lemma** (`mem_supportInSubgroup_sharp_iff` 他、section SharpSupport):
  A=H\{1} ↔ K=H.subgroupOf L の K\{1} 翻訳。hypothesis76OfFamily の inline を de-dup + H78 でも再利用。

**hypothesis78OfDade の入力** (全て legitimate carrier-conditional、hoisting でない):
H71, hτ (IsDadeIsometry), H◁L, A=H^#, 族 θ+hinj+hcover, 度数比 d+psi_support+hdeg, ind1H+区別 0,
hzeta_ind1H (θ_ind1H=trivial), hdeg_match (ζ_0(1)=ζ_ind1H(1) ⟹ d_ind1H=1), ν+nu_isometry,
hagree (§8 coherent extension の family-diff agreement)。certificate は (7.8.c.i) 機械で自動。

**証明 bridge の要点** (将来 §12/§16 consumer が H78 を inline 構成する際の参考):
(1) `hyp76.hyp71 = H71` を rfl で還元してから rw → chiRho_eq_inner_beta_induced 発火。
(2) `congrArg star (congrArg (inner · χ) (congrArg H71.τ ?_))` で SupportedClassFunction 同値に帰着。
(3) `Subtype.ext` + `rw[hd1, one_smul]` + `rfl` で d_ind1H•ζ_0 → ζ_0 を橋渡し。
⚠ `.zeta` projection の rw は diff_support 依存で motive 不正 → `.hyp71` のみ rw し congrArg で処理。

**issue 1013 の核 達成**: H78 (=§7 floor、(12.16) hB / lane γ (14.11) h78 が cite) が
(7.1)+coherence のみから **certificate 仮定なし**で構成可能。残 = (7.8.b) NormEstimates
(深く gated: a∈ℤ + degree-sum) + 実 consumer (exists_MHypothesis / §12 calc) が hypothesis78OfDade を呼ぶ統合。

### 2026-07-01 (loop 継続¹²⁻): (7.8.b) 全 infrastructure 在庫確認 — 「深く gated」評価を訂正

⭐ **前回までの「(7.8.b) は a∈ℤ + degree-sum が repo 未在で深く gated」は誤りだった**。徹底調査の結果、
(7.8.b) NormEstimates を組むのに必要な部品は **すべて repo に既存**:

- **degree-sum (1.5.d)** `Σθ(1)²=|G|`: `sumIrreducibleDegreeSq` + `sumNontrivialIrreducibleDegreeSq`
  (`ColumnOrthogonality.lean`, Burnside identity)。
- **整数性** `inner_mem_ZIrr_int` (`InducedCharacter.lean:716`): virtual char (∈ZIrr) の内積 ∈ ℤ。
- **β∈ZIrr** cascade (`S09_NonexistenceCertain.lean:1499-1540`):
  `beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible` / `sourceDiff_mem_ZIrr_of_irreducible` 他。
- **ν preserves ZIrr** `nu_mem_ZIrr_of_isCoherent` (`S09_NonexistenceCertain.lean:2073`):
  coherent extension は ℤ[S]→ZIrr G。
- **virtual 保存** `PreservesVirtualCharacters`/`FullDadeIsometryData` (S04 (2.6.b)/(2.9))。
- **(7.7.b) double-sum** `chiRho_norm_sq_double_sum` (`S09_NonexistenceCertain.lean:1336`)。
- **quadratic** `normQuadraticCorrection_nonneg_of_smallIndex` (S09)。
- **(7.8.a) orthogonality** `betaDecomp_orth_one`/`_gamma_orth_nu`/`_gamma_orth_one` (本ファイル、済)。

**既存の BetaDecomp/NormEstimates producer は無い** (grep 確認、重複なし)。

**(7.8.b) 残 build path (全部 buildable)**:
1. **BetaDecomp 構成** (H78 から): `a:ℤ` = `inner_mem_ZIrr_int (beta_mem_ZIrr…) (nu_mem_ZIrr…)` の m+1、
   `Gamma` = β−(1_G−ζ_0^ν+a•W) residual、orth フィールドは betaDecomp_* (本ファイル) を H78 へ
   bridge (hypothesis78OfDade と同じ rfl-還元 + congrArg 技法)、`beta_eq` は abel。
2. **NormEstimates**: `zetaNuRho_norm_sq_ge` = chiRho_norm_sq_double_sum を ζ^ν に適用し
   ‖ζ^{νρ}‖²=ua²−2va+w (u=(1/e)(1−1/h),v=1/h,w=1−e/h)、degree-sum で係数確定、a∈ℤ+u≥2v(⟺h≥2e+1)
   で quadratic ua²−2va≥0 ⟹ ≥w=1−e/h。`gamma_norm_sq_le` も同様。

次 loop = BetaDecomp 構成に着手 (上流; NormEstimates の前提)。

### 2026-07-01 (loop 継続¹³⁻): exists_betaDecomp_a 完成 + ⚠ whnf-wall アーキ知見

✅ **`exists_betaDecomp_a`** (S09_CertificateDischarge.lean、sorry-free、commit df88bb94):
(7.8.a) 係数 `a = (β, ζ_0^ν) + 1 ∈ ℤ`。β は `beta_mem_ZIrr_of_sourceDiff_mem_ZIrr` ((2.6.b))、
ζ_0^ν は coherence carrier、`inner_mem_ZIrr_int` で内積∈ℤ。orthogonality (betaDecomp_*) と併せ
**(7.8.a) の math content 完備** (family-level lemma 群)。

⚠ **whnf-wall 知見 (重要、downstream アーキを再方向づけ)**: `betaDecompOfDade` を
`(hypothesis78OfDade …).BetaDecomp` を返す coupled constructor として組もうとして **whnf timeout
(>1,000,000 heartbeats)** に到達。原因 = `BetaDecomp` の field 型が `(hyp78).hyp76.n`
(Fin (n+1) の index) を要し、これが **hypothesis78OfDade → hypothesis76OfFamily の 2 段の巨大
tactic def (set/classical/have wrapper) を unfold** するため事実上 non-terminating。

**アーキ含意**:
- hypothesis78OfDade/hypothesis76OfFamily は **H78 を「構成可能」にする**(issue 核、達成)が、
  その出力を **deep-project する downstream 構成は coupled には組めない**。
- downstream (BetaDecomp/NormEstimates) は **(a) consumer が H78 を inline 構築(族データを
  scope に持ち、私の family-level lemma を cite)** するか、**(b) H78 を抽象的に carry し
  deep-project しない**(lane γ MHypothesis.h78 field の carry はこちら、問題なし)で扱う。
- 私の **family-level lemma 群 (chiRho_eq_inner_beta_induced, betaDecomp_*, exists_betaDecomp_a,
  sharp-support 5 lemma)** が deliverable。coupled constructor は作らない。

**次 (7.8.b)**: family-level の bound `‖ζ^{νρ}‖² ≥ 1−e/h` を `chiRho_norm_sq_double_sum` (7.7.b) +
`sumNontrivialIrreducibleDegreeSq` (degree-sum) + a∈ℤ + quadratic で組む(H78-coupling を避け、
族データ θ/ν/a で直接)。consumer が inline で使う。

### 2026-07-01 (loop 継続¹⁴⁻): (7.8.b) 教科書 roadmap 確定 + 設計の機微

**(7.8.b) は `zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq` (S09:2655) で
identification `zetaNuRhoNormSq = normQuadraticCorrection + (1−e/h)` に還元済**
(残りの quadratic≥0 は `normQuadraticCorrection_nonneg_of_smallIndex` で済)。
よって残 = この **identification** (double-sum 計算) のみ。

**教科書 (7.8.b) 証明** (04.9.mmd) の正確な roadmap:
- (7.7) を **ζ_0 ∈ S−{ζ} (≠ 区別 ζ)**, ζ_1=Ind 1_H, ζ_2=ζ, χ=ζ^ν で適用。
- 係数: **c_1 = (β+(ζ−d_1ζ_0)^τ, ζ^ν) = a−1+1 = a** (ζ_1=Ind 1_H 項、β 経由)、
  **c_2 = ((ζ−d_2ζ_0)^τ, ζ^ν) = 1** (ζ_2=ζ)、**c_i = 0 (i>2)**。
- (7.7.b) で **‖ζ^{νρ}‖² = ua²−2va+w**、u=(1/‖ζ_1‖⁴)(‖ζ_1‖²−ζ_1(1)²/(eh))=(1/e)(1−1/h)、
  v=(1/(‖ζ_1‖²‖ζ_2‖²))ζ_1(1)ζ_2(1)/(eh)=1/h、w=(1/‖ζ_2‖⁴)(‖ζ_2‖²−ζ_2(1)²/(eh))=1−e/h。
- ‖Γ‖²=e−1 は `e+1=‖β‖²=1+(a−1)²+a²Σφ(1)²/(e²‖φ‖²)+‖Γ‖²` + (1.5.d) Σθ(1)²=h−1。

⚠ **設計の機微 (要対処)**: 教科書は (7.7) の参照 ζ_0 を **S−{ζ}** に取る (clean c_i=a,1,0)。
だが `chiRho_norm_sq_double_sum` は **H76 の ζ_0 = zeta 0** を参照に使い、
hypothesis78OfDade は **zetaDistinct=0 (ζ_0=区別 ζ)** に設定。→ 2 案:
- **(A)** my ζ_0=ζ のまま messy c_i (c_ind1H=a−1, c_i=−d_i) で計算。族は pairwise 直交
  (`induce_family_orthogonal`: Ind 1_H ⊥ Ind θ も含む、Frobenius で θ≠1_H ゆえ 0) なので
  double-sum は Σ|c_i|²/‖ζ_i‖² − (1/|L|)|Σc_iζ_i(1)/‖ζ_i‖²|² に簡約、ua²−2va+w に一致するはず。
- **(B)** 別 H76' を ζ_0'∈S−{ζ} で `hypothesis76OfFamily` 構成し clean c_i。

次 loop = (A) で identification 構築に着手 (再 indexing 不要、既存 H78 で直接; 族直交
+ degree-sum + c_i 同定 + 代数)。multi-turn の見込み。

### 2026-07-01 (loop 継続¹⁵⁻): (7.8.b) collapse 完成 + case-A 代数 fully mapped + (1.5.d) 前提特定

✅ **building blocks 完成**: `cCoeff_nu_zeta_zero_eq_neg_d` (c_i=−d_i)、
`cCoeff_nu_zeta_zero_ind1H_eq` (c_ind1H=(β,ζ_0^ν)=a−1)、`chiRho_norm_sq_collapse`
(double-sum → Σ|c_i|²/N_i − (1/|L|)|Σc_iζ_i(1)/N_i|²、族直交)。全 sorry-free。

**case-A 代数を完全に導出** (ζ_0=ζ=区別、zetaDistinct=0 は certificate が要求するので固定):
c_ind1H=a−1, c_i=−d_i (i≠0,ind1H), d_i=P_i/e, N_ind1H=‖Ind 1_H‖²=e, P_ind1H=P_0=e。
G := Σ_{φ∈S∖{ζ}} φ(1)²/‖φ‖² と置くと:
- Term1 = (a−1)²/e + G/e²、Q = (a−1) − G/e、|L|=eh。
- ‖ζ^{νρ}‖² = Term1 − |Q|²/(eh) は **G = e(h−1) − e²** を代入して ua²−2va+w に一致 (要検算)。

🔑 **残の鍵 = (1.5.d) S-degree-sum bridge**: `Σ_{φ∈S} φ(1)²/‖φ‖² = e(h−1)`
(= e·Σ_{θ∈Irr H,θ≠1}θ(1)²、誘導指標の orbit/Clifford 構造で `sumNontrivialIrreducibleDegreeSq`
に橋渡し)。**repo に未在** (誘導指標 degree/norm の orbit 関係、substantial prerequisite)。
教科書は (7.8.c.i) で ζ_0=ζ、(7.8.b) で ζ_0∈S−{ζ} と **参照を部分ごとに変える** (case B clean)
が、formalization は H76 の ζ_0 固定ゆえ certificate と整合する case A 一択、よって G が要る。

⚠ **lane γ の indChainDecomposition 機構** (S09:1574+、IsCoherent extension の chain 分解、
`re_eq_one_sub_sum_sq` で Σd² 計算) が並行存在。(7.8.b) NormEstimates producer は未在
(重複なし) だが、indChain は (7.8.a/b) norm の別アプローチ。統合の余地あり。

次 = (7.8.b) 代数 assembly (degree facts + G を hypothesis に取り collapse+c_i から ua²−2va+w)
を構築 (G は (1.5.d) carrier 入力、別途 bridge)。または (1.5.d) bridge を先に。multi-turn。

### 2026-07-01 (loop 継続¹⁶⁻): 🎯 (7.8.b) 代数+identification チェーン完全 — 残 (1.5.d) のみ (S08-accessible)

**(7.8.b) の代数+identification チェーンが完全に揃った** (全 sorry-free、S09_CertificateDischarge):
```
cCoeff_nu_zeta_zero_eq_neg_d / _ind1H_eq  (c_i 同定: c_i=−d_i, c_ind1H=(β,ζ_0^ν)=a−1)
  → chiRho_norm_sq_collapse  (double-sum → 対角 + rank-1、族直交)
  → sum_diag_split_ind1H / term1_eval_generic / rank1_eval_generic / rank1_eval_Y_generic  (sum 評価)
  → normEstimate_matching  (ring-verified: t₁−X²/eh = ua²−2va+w、G=e(h−1)−e² 代入)
  → zetaNuRho_inner_eq_cexpr  (ℂ-level: inner = (a−1)²/e + G/e² − ((a−1)−G/e)²/|L|)
  → cexpr_re_eq_normQuad  (.re + matching bridge)
  → zetaNuRhoNormSq_eq_normQuad  (identification: zetaNuRhoNormSq = normQuadraticCorrection + (1−e/h))
```
既存 `zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq` に渡せば **(7.8.b) lower bound**。

**残るは (1.5.d) G 値一点** (= zetaNuRho_inner_eq_cexpr の G を establish):
`G = Σ_{i≠0,ind1H} ζ_i(1)²/‖ζ_i‖² = e(h−1) − e²`。**path 確定 (S08 機構で buildable)**:
- **S08 `sum_div_normSq_induce_kernelFilter_eq` (CorePart1、S09 の closure に在=import 不要) を A=⊥ で適用**:
  filter `(⊥⊆Ker θ) ∧ θ≠1` は ⊥⊆Ker 自明ゆえ θ≠1 に簡約、|K/⊥|=|K|、K.index=[↥L:K]=e。
  → `Σ over (distinct-induced θ≠1) χ(1)²/‖χ‖² = e·(|K|−1) = e(h−1)`。
- **family↔image reindexing** (substantial): my family-index sum `Σ_{i≠ind1H}` (DistinctInducedFamily
  enumeration、hinj/hcover) = S08 image sum (θ≠1)。{ζ_i : i≠ind1H} = {induce θ : θ≠1} を hcover+hinj+
  ind1H↔trivial で示し Finset.sum_image で reindex。
- → `Σ_{i≠ind1H} = e(h−1)`、ζ_0 項 (e²) を引いて `G = e(h−1)−e²`。

次 = (1.5.d) 構築 (A=⊥ specialization → reindexing)。これが (7.8.b) 唯一残る実質数学。

### 2026-07-01 (loop 継続²¹⁻): ✅ (7.8.b) ζ-bound 完全 discharge — `normEstimates_of_source_orthogonal` の hzeta gap 閉鎖

**(7.8.b) の最終 assembly が完成** (commit 3969b134, full build green 3889 jobs)。(1.5.d) trio
(`induce_degree_sum_bot`→`family_degree_sum`→`family_degree_sum_Ioi`、先行 commit) に続き、
h_inner producer + keystone + 直接 bound の 3 定理を追加:

```
zetaNuRho_inner_eq_cexpr_H78  (ℂ h_inner: zeta 0 版 lemma を H78.zetaNuRho へ lift、
                               zetaDistinct=0、G=family_degree_sum_Ioi 値、|L|=Lagrange)
  → zetaNuRhoNormSq_eq_normQuad_of_facts  (keystone: zetaNuRhoNormSq = normQuadCorr + (1−e/h))
  → zetaNuRhoNormSq_ge_of_facts  (smallIndex 非負性 → 1−e/h ≤ ‖ζ_0^{νρ}‖²)
```

**核心の発見**: γ-side は既に完全実装済 (`gammaNormSq_eq_of_source_orthogonal` /
`normEstimates_of_source_orthogonal`、S09:3241/3270)。後者は `hzeta : zetaNuRhoNormSq =
normQuadCorr + (1−e/h)` を**未証明仮説**として待っていた。my `zetaNuRhoNormSq_eq_normQuad_of_facts`
がこの `hzeta` そのものを産出 → **完全な (7.8.b) NormEstimates (ζ 下界 + Γ 上界) が構成可能
仮説のみから閉じる**。downstream は `normEstimates_of_source_orthogonal ...
(zetaNuRhoNormSq_eq_normQuad_of_facts ...)` で full NormEstimates を得る。

**producer の仮説 (全て family constructor から構成可能、whnf-wall 回避で抽象 H78 設計)**:
hzd(=0,rfl)・horth(族直交)・hc_ind1H/hc_rest(coherence agreement→c_i 同定、`cCoeff_nu_zeta_zero_*`)・
hd(degree ratio,`zeta_one_eq_d_mul`)・hN_ind1H/hP_ind1H(‖Ind 1_H‖²=Ind 1_H(1)=e,
`induce_trivialChar_normSq/apply_eq_index`)・hGsum((1.5.d),`family_degree_sum_Ioi`)・hsmall(2e+1≤h)。

(7.8.b) は実質数学 (norm identity) として **完了**。残 = (7.8.a) 側の `BetaDecomp` constructor
producer (a の整数性は `exists_betaDecomp_a` 済、decomp 自体の field 充足) と、これら facts を
concrete Dade family で discharge する glue (上流、family constructor は zeta=induce が rfl)。

### 2026-07-01 (loop 継続²²⁻): (7.8.a) BetaDecomp constructor 着手 — orth lemma を抽象族へ一般化

(7.8.b) discharge 完了後、§7 残 = **(7.8.a) BetaDecomp constructor** (abstract H78 から、
whnf-wall 回避設計)。BetaDecomp 3 orth field を induce 固有から抽象族 `ζ` へ一般化中
(commit 04eb7910、2/3 完了): `betaDecomp_orth_one_gen` (S^ν⊥1_G)・`betaDecomp_gamma_orth_one_gen`
(Γ⊥1_G、`⟨β,1_G⟩=1` を hβ1 として家族非依存化)。既存 induce 版は gen を instantiate に refactor。

**次 = `betaDecomp_gamma_orth_nu` (Γ⊥S^ν) の一般化** = 5-lemma cascade を抽象 ζ へ:
`inner_family_diff` (⟨ζ_ind1H−ζ_0, ζ_i−d_iζ_0⟩=star(d_i)‖ζ_0‖²、horth で induce_family_orthogonal
置換) → `inner_beta_nuDiff` (⟨β,ζ_i^ν−d_iζ_0^ν⟩、hτ.inner_eq+hagree、ζ 抽象化) → `inner_beta_nu_eq`
(⟨β,ζ_j^ν⟩=star(d_j)·a、hζ0norm) + `inner_weightedNuSum_nu` (⟨W,ζ_j^ν⟩=ζ_j(1)/ζ_0(1)、horth/hN/hz0
で induce 固有事実置換) → `betaDecomp_gamma_orth_nu_gen`。induce 固有事実 (induce_family_orthogonal_of_injective
/induce_norm_ne_zero/induce_apply_one_ne_zero/induce_apply_one_star) を仮説化。

**その後 = `betaDecompOfFacts (H78) (hzd:zetaDistinct=0) (facts) : H78.BetaDecomp`**:
ζ:=H78.hyp76.zeta で 3 gen lemma を instantiate (whnf-wall なし: H78 は変数)。Gamma:=H78.beta−(1_G−ν(ζ_0)
+a•H78.weightedNuSum)、a=exists_betaDecomp_a、beta_eq=by abel、hW は weightedNuSum 定義+hzd で。
→ full (7.8.a). 最終 = concrete Dade family で全 facts discharge する bundling (whnf-wall 根治、別途)。

### 2026-07-01 (loop 継続²³⁻): ✅ (7.8.a) BetaDecomp constructor 完成 — (7.8.a)+(7.8.b) 両者が抽象 H78 で discharge

cascade 一般化 (commit 023febd9: inner_family_diff_gen → inner_beta_nuDiff_gen → inner_beta_nu_eq_gen
/ inner_weightedNuSum_nu_gen → betaDecomp_gamma_orth_nu_gen) に続き、**`betaDecompOfFacts`**
(commit bd8babcb) で (7.8.a) BetaDecomp 全体を抽象 H78 から構成可能仮説のみで構成。3 orth gen lemma
を ζ:=H78.hyp76.zeta で instantiate、4 proof field を discharge (Γ=explicit residual、a=integer)。
**whnf-wall 回避**: H78 が抽象変数ゆえ projection が巨大 def を unfold しない。

**現状**: (7.8.a) BetaDecomp と (7.8.b) NormEstimates の両者が abstract H78 レベルで構成可能仮説のみ
から discharge 済 (γ-side `normEstimates_of_source_orthogonal` は既存; ζ-side は
`zetaNuRhoNormSq_eq_normQuad_of_facts`; (7.8.a) は `betaDecompOfFacts`)。§7 の数学的内容は完了。

**残る唯一の §7 frontier = concrete bundling (whnf-wall 根治)**: `hypothesis78OfDade` 出力の
concrete H78 に対し、上記 producer の facts (horth/hN/hz0/hP_real/hagree/hzeta0nu/hzeta_orth_one/
hβ1/hζ0norm/a + (7.8.b) facts) を充足する glue。facts 自体は family (zeta=induce) から rfl/standard
だが、concrete `hypothesis78OfDade` の `.hyp76.n` projection が型に出て whnf-wall。
**根治候補**: (1) hypothesis76OfFamily/hypothesis78OfDade を tactic-block から clean structure literal へ
refactor (field を別 lemma に抽出) し projection を cheap 化、(2) H78+BetaDecomp+NormEstimates を
n free のまま 1 構成で束ねる bundle def。次イテレーションで consumer (exists_MHypothesis /
exists_counterexample_dade_data) の必要シェイプを確認してから着手。

### 2026-07-01 (loop 継続²³⁻ cont): 🎯 FT-path 接続確認 — consumer = exists_counterexample_dade_data (S14:2740, sorry)

§7 producer の実 consumer を特定。`counterexample_contradiction` (12.16, S14:2753) は
`exists_counterexample_dade_data` (S14:2740, **現状 sorry**) から `CounterexampleDadeData` を得て
`counterexample_contradiction_of_facts` に渡す。`CounterexampleDadeData` (S14:2701) のフィールド:
- **`hB : (1:ℝ) − (e:ℝ)/kH ≤ normRho`** = まさに my (7.8.b) ζ-bound `zetaNuRhoNormSq_ge_of_facts`
  (e=complementIndex, kH=kernelOrder=h, normRho=‖ζ_0^{νρ}‖²)。
- `hA : (kK−kKp)/kM * mval² ≤ normRhoM` = Γ/ρM bound (γ-side)。
- 他: hε/hψ (§12 char)、he (3≤e)、h2e (2e≤p+1)、h_const/h_psix/h_psig_int (12.14/12.15)、
  hkKp/hkM/hkH/hidx/hM (index 不等式)、hC (capstone < 1)。

→ **次フェーズ = exists_counterexample_dade_data sorry の discharge** (FT-path payoff)。
docstring (S14:2729) 指示: witness L (type I by 12.10) の Hypothesis(78) 構築 + Dade τ₁ + coherent
family S (12.6) + DadeNotation (12.13) → 各 field を §12 定理 (psi_constant_on_xK 12.14 /
rhoM_integer_values 12.15 / intersection_complement_structure 12.11) + §7 norm estimates
(`NormEstimates` / `zetaNuRhoNormSq_ge_of_facts` for hB) で discharge。whnf-wall は hB の
concrete fact 充足で再来 → ここで根治 (clean literal / bundle) が必要。(12.6)/(12.10)/(12.11) は
signature contract 経由 cite。これが §7→§12→(12.16)→FT の実接続。

### 2026-07-01 (loop 継続²⁴⁻): ⭐ whnf-wall は幻だった + betaDecompOfDade (concrete (7.8.a))

**whnf-wall の再検証で否定**: probe (variable inputs で `hypothesis78OfDade` 適用→projection) により
`.hyp76.n` / `.hyp76.zeta` / `.nu` / `.hyp76.hyp71` / `.ind1H` / `.zetaDistinct` がすべて default
heartbeats で `rfl` projection 可能と実証。従来「`.hyp76.n` が巨大 tactic def を unfold して
>1M heartbeats」は誤りで、旧 `betaDecompOfDade` failure は coupled tactic 固有の問題だった。
**concrete instantiation は wall-free**。

✅ **`betaDecompOfDade` (commit 5c80fedb)**: `hypothesis78OfDade` 出力 concrete H78 に
`betaDecompOfFacts` を適用し (7.8.a) BetaDecomp を構成。facts discharge:
- family 直交/ノルム/degree-real = induce 補題 (`induce_family_orthogonal_of_injective` /
  `induce_norm_ne_zero` / `induce_apply_one_ne_zero` / `induce_apply_one_star`) を defeq で。
- coherence agreement: 供給 hagree (passed-d) を computed-d (`H78.hyp76.d i = ζ_i(1)/ζ_0(1)`, hdeq)
  へ `Subtype.ext` で輸送 (dependent subtype の motive 破綻を回避: show を induce 形で書き
  post-`rw [hdeq i]` が syntactic rfl になるよう)。
- ⟨β,1_G⟩=1 内部計算 (beta_def + inner_tau_supported_constOne + induce 補題)。
- 残 genuine §7 入力 = hzeta0nu (ζ_0^ν⊥1_G)・hζ0norm (‖ζ_0‖²=1)・整数 a/ha。

**concrete path 開通**: `hypothesis78OfDade` → concrete H78 → `betaDecompOfDade` → BetaDecomp。
**次 = NormEstimates concrete** (同パターンで (7.8.b) producer `zetaNuRhoNormSq_eq_normQuad_of_facts`
+ γ-side を concrete H78 へ; facts は同様に induce で discharge) → **`exists_counterexample_dade_data`
(S14:2740 sorry) 接続** (witness L の H78 構築 + CounterexampleDadeData.hB=my (7.8.b) bound)。
full build 3889 jobs 緑、AxiomsCheck OK。

### 2026-07-01 (loop 継続²⁵⁻): §12 consumer survey + complementIndex bridge (concrete (7.8.b) 着手)

**§12 consumer の状態**: `exists_counterexample_dade_data` (S14:2740, **sorry**) は (12.16)
`counterexample_contradiction` の deep obligation で、`CounterexampleDadeData` (S14:2701) を構築。
依存する §12 lemma の多くが sorry: `witness_L_frobenius` (12.10, 2024)・
`intersection_complement_structure` (12.11, 2070)・`psi_constant_on_xK` (12.14, 2502)・
`rhoM_integer_values` (12.15, 2511)。§12 は `Hypothesis L`/`DadeNotation`/`Coherence` 構造を使い、
my §7 `Hypothesis78` と直結しない (bridge 未在)。full integration は deep な別フェーズ。

**`CounterexampleDadeData` フィールド→source**: hB (1−e/kH≤normRho) = **my (7.8.b) ζ-bound**、
hA = Γ/ρM (γ-side)、hε/hψ=§12 char、he/h2e=12.12 degree、h_const=12.14、h_psig_int=12.15、
hk*/hidx/hM=index 不等式、hC=capstone。

**着手: concrete (7.8.b)**。`complementIndex_eq_subgroupOf_index` (commit de0ac155) =
`e = (H.subgroupOf L).index` bridge (induce-index → complement-index)。**次 = `zetaNuRhoNormSqGeOfDade`**
(betaDecompOfDade と同パターン、concrete (7.8.b) ζ-bound): hBD:=betaDecompOfDade、
`zetaNuRhoNormSq_ge_of_facts` へ facts 供給 — hzd=rfl、horth=induce 直交、
hc_ind1H=cCoeff_nu_zeta_zero_ind1H_eq+ha (hBD.a=a)、hc_rest=cCoeff_nu_zeta_zero_eq_neg_d
(hagree を psiSupp/computed-d 形へ Subtype.ext 変換、betaDecompOfDade の hagree' と同)、
hd_real/hP_real=induce_apply_one_star、hd=ζ_i(1)/e (ζ_0(1)=ζ_ind1H(1)=e via zeta_one_eq_ind1H_one)、
hN_ind1H/hP_ind1H=induce_trivialChar_normSq/apply_eq_index + complementIndex_eq_subgroupOf_index、
hGsum=family_degree_sum_Ioi (hz0_deg=ζ_0(1)=e from zeta_one_eq_ind1H_one、hz0_norm=hζ0norm)、hsmall。
betaDecompOfDade で landing 実証済 = 既知 feasible。

### 2026-07-01 (loop 継続²⁶⁻): ✅ concrete §7 (7.8) producer 完備 — betaDecompOfDade + zetaNuRhoNormSqGeOfDade

`zetaNuRhoNormSqGeOfDade` (commit 400aa905): Dade family → concrete H78 に対し (7.8.b) ζ-bound
`1−e/h ≤ ‖ζ_0^{νρ}‖²` を産出 (= `CounterexampleDadeData.hB`)。`betaDecompOfDade` +
`zetaNuRhoNormSq_ge_of_facts` を bundle、(7.8.b) facts を全 discharge (係数同定 cCoeff_nu_zeta_zero_*
+ Subtype.ext で hagree を computed-d 形へ / reality induce_apply_one_star / degree ratio
zeta_one_eq_ind1H_one / index facts induce_trivialChar_* + complementIndex_eq_subgroupOf_index /
(1.5.d) family_degree_sum_Ioi)。2 build cycle で landing。

**§7 (7.8) は abstract + concrete 共に完備**:
- abstract: betaDecompOfFacts (7.8.a) / zetaNuRhoNormSq_eq_normQuad_of_facts (7.8.b keystone) +
  既存 normEstimates_of_source_orthogonal (γ-side)。
- concrete (Dade family): betaDecompOfDade (7.8.a BetaDecomp) / zetaNuRhoNormSqGeOfDade (7.8.b hB)。

**残る FT-path = §12 integration (別フェーズ、deep)**: `exists_counterexample_dade_data` (S14:2740 sorry)
で `CounterexampleDadeData` を組む。必要:
1. **§12 `Hypothesis L`/`Coherence`/`DadeNotation` → §7 `hypothesis78OfDade` 入力の bridge** (構造変換、
   witness-L H78 を構築するため。現状 bridge 未在 = 鍵)。
2. CounterexampleDadeData の各 field: hB=zetaNuRhoNormSqGeOfDade、hA=γ-side、hε/hψ/he/h2e/h_const/
   h_psix/h_psig_int/hk*/hidx/hM/hC=§12 (12.12/12.14/12.15 等、多くが sorry)。
§12 sorry (witness_L_frobenius 12.10 / intersection_complement_structure 12.11 / psi_constant_on_xK
12.14 / rhoM_integer_values 12.15) が gating。次イテレーション = §12 Coherence→Hypothesis78 bridge の
feasibility 調査 + 着手。

### 2026-07-01 (loop 継続²⁷⁻): §12 Coherence→Hypothesis78 bridge 解析 — ℤ/ℚ-linearity の核心 difficulty + 解法

§7 producer を (12.16) consumer に繋ぐ bridge `Hypothesis L` (+`IsCoherent`) → `hypothesis78OfDade`
を精査。判明した構造と difficulty:

**既存の足場**:
- `Hypothesis.toHypothesis71` (S14:110) = §12 `Hypothesis L` → §7 `S09.Hypothesis71` (済、docstring も
  「7.8.b を L に適用可能にする」と明記)。
- `witness_L_coherent` (S14:2061) = `IsCoherent hyp.tau hyp.Sset hyp.A` (Nonempty)。
- `IsCoherent` (S07:1596): `extension : IntegralCharacterMap L G` (=ν)、`extends_on_supported`
  (ν φ = τ φ for φ∈zSupportedSpan)、`extension_inner_eq` (zSpan 上 isometry)、`extension_mem_ZIrr`。

**核心 difficulty (ℤ vs ℚ linearity)**: `IntegralCharacterMap = CF→ₗ[ℤ]CF` は **ℤ-線形**。だが
`hypothesis78OfDade.hagree` = `τ(ζ_i − d_i ζ_0) = ν(ζ_i) − d_i•ν(ζ_0)` は `d_i=ζ_i(1)/ζ_0(1)∈ℚ` の
非ℤ結合。`extends_on_supported` は zSupportedSpan (=ℤ-span∩supported) 上のみ → ψ_i=ζ_i−d_iζ_0 は
ℚ結合ゆえ直接適用不可。

**解法 path**: **ℤ結合** `ζ_0(1)•ζ_i − ζ_i(1)•ζ_0 ∈ ℤ[S]` (degree は整数) は supported (=ζ_0(1)•ψ_i)
かつ ℤ-span ゆえ zSupportedSpan ∈ → `ν = τ` 適用可。degree の natCast-smul は nsmul に等しく ℤ-線形
が効く (ν((n:ℂ)•x)=(n:ℂ)•ν x, n:ℕ; mathlib `map_natCast_smul` 等)。両辺を ζ_0(1)(≠0) で割れば ψ_i
agreement 取得。

**bridge の残り部品** (全て multi-lemma、次フェーズ):
1. 上記 coherence-agreement lemma (ℤ結合→割算→ψ_i hagree)。
2. `toHypothesis71.τ` (DadeMap) ↔ `hyp.tau` (IntegralCharacterMap) の同一視 (IsCoherent は hyp.tau、
   hagree は H71.τ)。
3. Sset 列挙 → Fin (n+1) family (hinj/hcover/ind1H; distinctInducedFamily 利用)。
4. `typeIA L hyp.typeI = (hyp.H : Set G) \ {1}` (A 一致、(12.1)/(8.3) fact)。
5. degree data (d/hdeg/hdeg_match)。
→ 揃えば `hypothesis78OfDade` で witness-L H78 構築 → betaDecompOfDade/zetaNuRhoNormSqGeOfDade で
BetaDecomp/hB。次イテレーション = 部品1 (coherence-agreement lemma) から着手。

### 2026-07-01 (loop 継続²⁷⁻ cont): §12 bridge crux RESOLVED — hyp.tau は ℂ-線形 (keystone landed)

前記 ℤ/ℚ-linearity difficulty を解決。`dadeIntegralCharacterMap` (=hyp.tau) の定義 (S07:5272) は
`(LinearMap.exists_extend hyp.dadeLinearMap (k:=ℂ)).choose.restrictScalars ℤ` = **ℂ-線形** Dade map
拡張を ℤ-線形として読んだもの。∴ underlying map は ℂ-線形、`τ(c•x)=c•τ x` (c:ℂ) 成立。
`dadeIntegralCharacterMap_smul_complex` (commit 87dcbd03) がこれを供給。

**hagree 導出 path (確定)**: ζ_i,ζ_0∈S、整数次数 m_i=ζ_i(1),m_0=ζ_0(1)、d_i=m_i/m_0。
ℤ結合 c:=m_0•ζ_i − m_i•ζ_0 = m_0•(ζ_i−d_iζ_0) は supported (=m_0•ψ_i) かつ ℤ-span ∈ →
`extends_on_supported`: ν c = τ c。ℤ-線形 decompose + m_0 で除算 → `ν ζ_i − d_i ν ζ_0 = τ ζ_i − d_i τ ζ_0`。
ℂ-linearity (`dadeIntegralCharacterMap_smul_complex`): `τ(ζ_i−d_iζ_0)=τ ζ_i − d_i τ ζ_0`。
両者で `τ(ζ_i−d_iζ_0) = ν ζ_i − d_i ν ζ_0` = hagree。

⚠ **S14/S16 とも type-I family の hagree (coherence agreement) は未構築** (S16.toFamilyHypothesis71
は Hypothesis71 止まり、(7.8) は NormEstimates を carrier 扱い)。本 bridge が初。

**次 = coherence_hagree lemma** (上記 path を Lean 化): IsCoherent + 整数次数 + supported から hagree。
その後 part 2-5 (τ↔H71.τ 同一視 / Sset→Fin family / typeIA=H^# / degree) → witness-L Hypothesis78
構築 → betaDecompOfDade/zetaNuRhoNormSqGeOfDade で BetaDecomp/hB → CounterexampleDadeData。

### 2026-07-01 (loop 継続²⁸⁻²⁹): §12 bridge parts 1+2+4 完成

§12→§7 Dade bridge を部品単位で構築 (各 1-2 build cycle, full build 緑):
- keystone `dadeIntegralCharacterMap_smul_complex` (commit 87dcbd03): hyp.tau の ℂ-linearity。
- part 1 `coherence_hagree` (f2ce7b25): IsCoherent から (7.8.a) agreement (IntegralCharacterMap レベル)。
- parts 1+2 `coherence_hagree_dadeMap` (200fe2a5): agreement を DadeMap 形へ (= hypothesis78OfDade の hagree)。
  [上記 3 つは S09_CertificateDischarge]
- part 4 `Hypothesis.typeIA_eq_sharp` (399c33c5, **S14**): typeIA L = H^# (= hAH)。typeI_frobenius
  (proven) + Frobenius centralizer_kernel_le。

⚠ **hub dedup task**: `centralizerSupport_sharpSubgroup_eq_of_frobenius` (S16:2584, pure GT) を
S14 が cite できない (S16 は S14 下流) ため typeIA_eq_sharp 内で再導出。共有ファイル
(MaximalSubgroupType, IsFrobeniusGroup 既 import) へ hoist すれば S14/S16 両用で dedup 可能。

**残 bridge parts** (witness-L Hypothesis78 assembly へ): part 3 (Sset→Fin (n+1) family:
distinctInducedFamily で hinj/hcover/ind1H、Sset={induce θ|θ≠1} は trivial 抜き) / part 5
(degrees d/hdeg/hdeg_match) / hnu_isometry (IsCoherent.extension_inner_eq) / H71+hτ
(toHypothesis71 + IsDadeIsometry)。**assembly は S14 に S09_CertificateDischarge を import して**
hypothesis78OfDade を呼ぶ (S14 が consumer exists_counterexample_dade_data の home)。

### 2026-07-01 (loop 継続³⁰⁻): §12 bridge 残部品の精査 + family-isometry supplier

bridge 残部品を精査し、必要な入力と障害を確定:
- ✅ `coherence_extension_inner_eq_on_family` (commit 12b657ea): IsCoherent から family-level isometry
  ⟨ν ζ_i, ν ζ_j⟩=⟨ζ_i,ζ_j⟩。
- ✅ 区別 char (zetaDistinct=0, 次数 [L:K]) は `exists_distinguished_char hyp` (S14:2402, proven) で取得可
  (χ∈Sset, χ(1)=(typeF.H.subgroupOf L).index)。χ=induce(linear θ_0)。
- ⚠ **nu_isometry interface 問題**: hypothesis78OfDade の nu_isometry field は global (∀ φ ψ) だが
  §12 coherent ν は family span 上のみ isometry。全使用箇所が family-level ゆえ field を
  `∀ i j, ⟨ν(zeta i),ν(zeta j)⟩=⟨zeta i,zeta j⟩` へ弱める refactor が必要 (~6-8 sites, contained:
  constructor=hypothesis78OfDade のみ、consumer 全て my §7 files)。**次フェーズ最初の step**。
- 残: family construction (θ_0=区別 char rep at 0、trivial at ind1H≠0、cover/inj は
  distinctInducedFamily ベース + 2-member 配置) / hζ0norm (‖χ‖²=1、L Frobenius ゆえ Ind θ
  (θ≠1) irreducible) / hzeta0nu (⟨ν χ,1_G⟩=0) / degrees (hdeg/hdeg_match) / H71+hτ
  (toHypothesis71) / assembly (S14 に S09_CertificateDischarge import)。
- 注: full (12.16) は別途 §12 char sorry (psi_constant_on_xK 12.14 / rhoM_integer_values 12.15 /
  intersection_complement_structure 12.11) が gating。

bridge progress: keystone (ℂ-linearity) + parts 1/2 (coherence agreement DadeMap 形) + part 4
(typeIA=H^#) + family-isometry。**hard math content 完了**、残は構造 refactor + family 構成 +
char-theory 入力 (Frobenius-induction irreducible)。

### 2026-07-01 (loop 継続³¹⁻): §12 bridge ingredient 一覧 完備 — hζ0norm supplier landed

`inner_self_induce_eq_one_of_frobeniusGroup` (commit 73a241ea, InducedIrreducible): Frobenius 群で
非自明既約の誘導 ‖Ind θ‖²=1 → hypothesis78OfDade の hζ0norm。これで bridge の全 ingredient が
所在確定:
- hagree: `coherence_hagree_dadeMap` ✓
- nu_isometry (family-level): `coherence_extension_inner_eq_on_family` ✓ (⚠ field 弱化 refactor 必要)
- hAH (typeIA=H^#): `Hypothesis.typeIA_eq_sharp` ✓
- hζ0norm (‖ζ_0‖²=1): `inner_self_induce_eq_one_of_frobeniusGroup` ✓
- 区別 char χ(1)=[L:K]: `exists_distinguished_char` ✓
- Frobenius-induce-irreducible: `isIrreducibleCharacter_induce_of_frobeniusGroup` ✓
- H71+hτ: `Hypothesis.toHypothesis71` ✓ (IsDadeIsometry from fullDadeIsometryData)
- Frobenius 構造: `typeI_frobenius` ✓

**残 (assembly フェーズ)**:
1. **nu_isometry field 弱化** (Hypothesis78 の global → `∀ i j, i≠ind1H → j≠ind1H → ...`、
   ~6-8 sites、pre-existing gamma-side consumer の rw に ≠ind1H proof を thread; shared
   S09_Nonexistence ゆえ atomic + 注意)。これが唯一の真の refactor。
2. **family 構成** (distinctInducedFamily ベース、区別 char rep を index 0、trivial を ind1H≠0 に配置、
   cover/inj 保存; 2-member 配置の intricate 構成)。
3. hzeta0nu (⟨ν χ, 1_G⟩=0、非自明 coherent image ⊥ 1_G)。
4. degrees (d/hdeg/hdeg_match)。
5. assembly: S14 に S09_CertificateDischarge import → hypothesis78OfDade で witness-L H78 →
   betaDecompOfDade/zetaNuRhoNormSqGeOfDade。
注: full (12.16) は別途 §12 char sorry (12.11/12.14/12.15) が gating。

### 2026-07-01 (loop 継続³²⁻): nu_isometry 弱化を試行→revert (delicate γ-side proof を破壊)

§12 bridge 唯一の真の refactor = `Hypothesis78.nu_isometry` field の global→family-level 弱化を試行。
field + nu_zeta_inner_self_eq_one(+_of_irreducible, +callers) + weightedNuSum collapse sites を編集。
**結果: weightedNuSum collapse proof (S09_Nonexistence 3154/3159) が破壊** — `rw [H78.nu_isometry,
horth i (by simpa [hs] using hi) ...]` の chain が global nu_isometry の rw 挙動に微妙に依存しており、
indexed 版 + horth の simpa が S metavar で type mismatch。delicate な pre-existing (7.8.b) γ-side
proof ゆえ revert (build green 維持)。

**教訓 + 解法 path**:
- 弱化は fragile (delicate γ-side proof に波及)。careful にやるなら horth 引数を explicit
  `Finset.mem_erase.mpr ⟨hine, mem_univ⟩` 化 + 各 collapse proof の rw chain を再理解して修正 (高リスク)。
- **より clean = option F (global isometry 供給)**: field を global のまま保ち、§12 bridge では
  coh.extension に family 上一致する **global-isometric ν'** を hypothesis78OfDade に供給。{ζ_i} は
  一次独立 (distinct Frobenius-induced irreducible) で coh.extension が Gram 行列保存
  (extension_inner_eq) ゆえ、family span 上の等長を global unitary へ拡張可能 (Gram-Schmidt /
  orthonormal completion、intricate だが delicate proof に触れない)。hagree/hζ0norm/hzeta0nu は
  ν' = coh.extension on family ゆえ成立。
- どちらも intricate。次フェーズで careful に。§7 floor + bridge hard content + 全 ingredient は完成
  (keystone/coherence_hagree/coherence_hagree_dadeMap/typeIA_eq_sharp/coherence_extension_inner_eq_on_family/
  inner_self_induce_eq_one_of_frobeniusGroup)。assembly のみ残。

### 2026-07-01 (loop 継続³³): nu_isometry 弱化 ✅ DONE (前回の "fragile" は誤診断)

前回 "delicate γ-side proof を破壊" と判断して revert したが、**真因は私の書いた `hine` helper
`(Finset.mem_erase.mp (by simpa [hs] using hi)).1` が ambient Finset を metavar に残し simpa が
over-simplify していただけ**。`Finset.ne_of_mem_erase (hs ▸ hi)` に直すと weightedNuSum collapse
proof は無傷で通る。さらに option F (global isometry) は **存在しない可能性** (isometric embedding
`CF(L)→CF(G)` だが dim CF(L) > dim CF(G) があり得る) ゆえ弱化は必須と確定。

弱化を完遂 (commit ea61e2a4): field を family 形
`∀ i j, i≠ind1H → j≠ind1H → (ν(ζi),ν(ζj))=(ζi,ζj)` にし、全 consumer を threading:
- S09_Nonexistence: nu_zeta_inner_self_eq_one(+_of_irr), zetaImage_*, weightedNuSum collapse ×2。
- S09_Cert 8 lemma: inner_weightedNuSum_nu_gen/_nu, betaDecomp_gamma_orth_nu_gen/_nu,
  cCoeff_nu_zeta_zero_eq_neg_d (+`0≠ind1H`), hypothesis78OfDade/betaDecompOfDade/zetaNuRhoNormSqGeOfDade。
- `nu_isometry := hnu_isometry` の defeq (`hyp76.zeta i ≡ induce (H.subgroupOf L) (θ i)`) OK、
  cCoeff の h0ind は `Ne.symm hind1H` で供給。full build 3889 green。

**hypothesis78OfDade は coherence_extension_inner_eq_on_family がそのまま供給できる family-isometry を
受け取る形になった**。残りの bridge assembly: (b) family 構成 (θ_0=distinguished, ind1H≠0 で trivial)、
(c) hzeta0nu, (d) degrees、(e) S14 で witness-L 組み立て。教訓: "fragile" 判定は真因 (helper の書き方) を
特定してから; 弱化必須性は dimension argument で確認。[[feedback-no-avoiding-hard-parts]]

### 2026-07-01 (loop 継続³⁴): bridge 部品 (b) family 構成 ✅ exists_placed_induced_family

§12 bridge の family 構成 (part b) を landing (commit 6ceea07b): `exists_placed_induced_family`
は distinctInducedFamily を reindex し θ 0 を distinguished (Ind(θ0)=χ_dist)、ind1H≠0 を trivial
(θ ind1H=1_K) に配置 (inj/cover 保存)。trivial の fibre は inertia-stable ゆえ rep が 1_K 自身、
swap 0 j_dist で distinguished を 0 へ、j_dist≠j_triv は χ_dist≠Ind 1_K から。

§12 で確認した assembly target: `Hypothesis L → toHypothesis71 → hypothesis78OfDade →
Hypothesis78.NormEstimates (7.8.b)` で CounterexampleDadeData.hB (=`1−e/kH≤normRho`) を産む。
endpoint `exists_counterexample_dade_data` (S14:2740 sorry) は 25-field 構造で hB は 1 field。
lane-b の clean な貢献 = standalone hB-producer (Hypothesis L から (7.8.b) bound)。残り bridge 部品:
(c) degree facts (d/psi_support/hdeg/hdeg_match for placed family)、(d) hagree (coh から、
coherence_hagree_dadeMap)、(e) ν=coh.extension + hnu_isometry=coherence_extension_inner_eq_on_family、
(f) hypothesis78OfDade 組み立て→zetaNuRhoNormSqGeOfDade→normRho/kH/e 同定。

### 2026-07-01 (loop 継続⁶): ⭐⭐⭐ witness `Hypothesis78` 組み立て完成 — witness_L_hypothesis78

**(12.16) hB の keystone = witness L の (7.8) 構造構成を完全 sorry-free 達成** (S14_MaximalI.lean、
証明 body は sorry-free; 継承 sorryAx は `witness_L_coherent`=(12.6)/(12.1) 上流 gate のみ)。
残務 map の (c)-(f) を全て discharge:

`witness_L_hypothesis78 (hG) (data : RankTwoWitnessData) : ∃ hyp : Hypothesis data.L,
  Nonempty (Hypothesis78 G (typeIA data.L hyp.typeI) data.L)`

`hypothesis78OfDade` を witness L の 3 材料から組み立て:
- **coherence** (`witness_L_coherent` の coh): ν=`coh.extension`、hnu_isometry=
  `coherence_extension_inner_eq_on_family coh (hSmem i) (hSmem j)`、hagree=
  `coherence_hagree_dadeMap hyp.dadeData.dade hyp.hconj coh …` (m0=1, mi=deg θ_i via
  `irreducibleCharacter_apply_one_eq_pos_natCast`)。
- **placed family** (`exists_witness_placed_family`): θ/ind1H/hdeg0/htriv/hinj/hcover。
- **structural bridges** (新規 proof):
  - hAH = `Hypothesis.typeIA_eq_sharp` (A(L)=H#)。
  - hHnorm = subgroupOf-normality (`hKnormal.conj_mem` + `mem_subgroupOf`)。
  - hSmem (θ_i≠1_K for i≠ind1H via hinj) ⟹ Ind θ_i∈Sset。
  - d_i=θ_i(1)、hdeg (`induce_apply_one`+hdeg0)、hdeg_match (`induce_trivialChar_apply_eq_index`)、
    psi_support (`induce_diff_support`+`mem_supportInSubgroup_sharp_subgroupOf_iff`)。

**axiom 状態**: 自 body sorry-free。`#print axioms` の唯一の sorryAx = `witness_L_coherent`
経由 (`frobenius_typeI_coherent`=(12.6) Frobenius coherence + `hypothesis_of_typeIData`=(12.1)
Dade support、いずれも §7/§10 上流 gate)。`hypothesis78OfDade`/`coherence_hagree_dadeMap`/
`exists_witness_placed_family` は全 axiom-clean。CLAUDE.md「signature 正なら sorried 上流を
cite して下流実証明」に合致。full build 3889 green (~63s)。

**残 = hB 不等式の産出** (次増分): witness_L_hypothesis78 の bridge を再利用し、
(7.8.b) 固有入力 4 つを追加 → `zetaNuRhoNormSqGeOfDade` で `1-e/kH ≤ normRho` を産出:
- **hζ0norm** `⟨Ind θ_0, Ind θ_0⟩=1` (Ind θ_0=χ_dist 既約; L=H⋊U Frobenius ゆえ nontrivial θ の誘導は既約)。
- **hzeta0nu** `⟨ν(Ind θ_0), constOne⟩=0` (coherent 像は 1_G に直交; §7 coherence orthogonality)。
- **a/ha** `exists_betaDecomp_a` (hdiffZ: Ind θ_{ind1H}−Ind θ_0∈ZIrr L、hζ0nuZ: ν(Ind θ_0)∈ZIrr G)。
- **hsmall** `H78.smallIndex` (index smallness; def 要確認)。
その後 hC ((7.3)+(8.17))・他 field と合わせ `exists_counterexample_dade_data` (S14:2779 sorry)。

### 2026-07-01 (loop 継続⁷): hB 完成マップ確定 + Frobenius size 補題 + hzeta0nu crux 特定

witness_L_hypothesis78 を踏まえ hB=(7.8.b) `1 - e/kH ≤ normRho` (`zetaNuRhoNormSqGeOfDade`
S09:2347 で産出) の残 4 入力を精査。**3 つは tractable、1 つ (hzeta0nu) が genuine gap**:

- ✅ **hζ0norm** `⟨Ind θ_0, Ind θ_0⟩=1`: `inner_self_induce_eq_one_of_frobeniusGroup`
  (InducedIrreducible.lean:477、docstring が「§12 type-I coherent family」用と明記) で即。
- ✅ **hsmall** `2e+1≤h` (= `H78.smallIndex`): 一般補題
  **`frobenius_two_mul_card_complement_add_one_le_card_kernel`** (S14 新規、axiom-clean) で証明。
  奇位数 Frobenius 群で |A| | |N|-1 (`IsFrobeniusGroup.card_kernel_modEq_one`=Isaacs 6.1) +
  |N| 奇 ⟹ |N|-1 偶 ⟹ 奇約数 |A| は半分以下 ⟹ 2|A|+1≤|N|。witness 適用は
  N=H.subgroupOf L, A=C (共に奇 ∵ odd G の section)、complementIndex=|C| (IsComplement' card 分解)。
- ✅ **a/ha** `exists_betaDecomp_a` (S09:1668): hdiffZ=Ind θ_{ind1H}−Ind θ_0∈ZIrr L
  (`induce_mem_ZIrr` InducedCharacter:792 ×2)、hζ0nuZ=ν(Ind θ_0)∈ZIrr G (`coh.extension_mem_ZIrr`)。
  hypothesis76OfFamily.zeta i = Ind θ_i (defeq、alignment OK)。
- 🛑 **hzeta0nu** `⟨ν(Ind θ_0), constOne G⟩=0` = **genuine gap**。
  - ν(Ind θ_0) は norm-1 virtual char (isometry `extension_inner_eq` + hζ0norm) = ±既約。
    ⟨ν ζ_0,1_G⟩=0 ⟺ ν(ζ_0)≠±1_G。
  - **isometry+hagree だけでは不足**: hagree から ⟨ν ζ_i,1_G⟩=d_i·c (c=⟨ν ζ_0,1_G⟩) が全 i で従うが
    (τ image ⊥1_G via `inner_tau_supported_constOne` + ⟨ψ_i,1_L⟩=0)、norm 制約
    Σd_i²|c|²≤1 は c=0 を強制しない。差 ζ_0−ζ_{ind1H} も ζ_{ind1H}=Ind 1_K∉zSpan S ゆえ
    zSupportedSpan に入らず extends_on_supported 使えず。
  - **要る machinery = coherent extension の nonprincipality/degree 保存** (ν(χ)(1)=χ(1)=e≥3 なら
    ν(ζ_0)≠±1_G で即)。抽象 `IsCoherent` (nonzero/extension/inner_eq/extends_on_supported/mem_ZIrr)
    に degree 保存も nonprincipality も **無い**。`frobenius_typeI_coherent`/retarget/CoherenceWiring も
    degree 保存 lemma 無し (grep 済)。→ coherence-core を強化する新 §7 定理が必要 (lane-a coherence
    machinery と overlap 可能性)。**hB の唯一の残 blocker**。

**次増分**: (a) witness instantiation で `frobenius_...le_card_kernel` を H78.smallIndex に接続
(IsComplement' card 分解 + subgroupOf card equiv)、(b) hζ0norm/a·ha を wire、(c) hzeta0nu を
coherence degree 保存で discharge (deep) → `zetaNuRhoNormSqGeOfDade` で hB 産出 →
`exists_counterexample_dade_data` (S14 sorry) の hB field。hC=(7.3)+(8.17) は別途。

### 2026-07-01 (loop 継続⁷ 補足): hzeta0nu root-cause 確定 = IsCoherent が ⊥1_G を捨てている

hzeta0nu の根本原因を特定。Peterfalvi の coherence (5.x) は本来 ℤ[S]→ℤ[Irr G] を
**1_G の直交補空間**へ写す (S は 1_L に直交する induced-from-nontrivial ばかり、Dade isometry が
⊥1_G の空間に landing、coherent 拡張がそれを保つ)。しかし本 repo の `IsCoherent` (S07:1596) は
**isometry + extends-Dade + ZIrr-codomain のみ保持し、⊥1_G を落としている** (nonzero/extension/
extension_inner_eq/extends_on_supported/extension_mem_ZIrr の 5 field に ⊥1_G も degree 保存も無い)。
coherence 産出経路 `frobenius_typeI_coherent`→`coherent_of_sibleyTarget`→`nonempty_coherent_of_sibley`
(S08 Sibley/(6.8)) も抽象 IsCoherent を返すのみ (⊥1_G は construction 内で成立するが露出せず)。

**⟹ hzeta0nu は抽象 IsCoherent から原理的に導けない** (isometry は degree/principal 成分を決定しない;
hagree からは ⟨ν ζ_i,1_G⟩=d_i·c しか出ず c=0 を強制できない、証明済)。

**修正の 2 択**:
- (a) **共有 `IsCoherent` に field 追加** (`extension_orthogonal_constOne` or degree 保存
  `extension_apply_one_eq`) + Sibley 構成 (`nonempty_coherent_of_sibley`)・galoisTransport で証明。
  = 最もクリーンで全 coherence consumer に裨益するが **shared-structure signature 変更** (全 constructor
  更新要、他レーン=lane-a/c の coherence 利用に影響) → **CLAUDE.md「signature 無断変更=STOP」に該当、
  hub/ユーザー裁可が要る設計判断**。
- (b) **Sibley 構成から standalone lemma** で witness の ν(Ind θ_0) ⊥1_G を直接証明 (IsCoherent に
  触れず additive)。lane-b-local だが S08 case-B coherence extension machinery への deep dive を要する。

→ hzeta0nu は hB の唯一の残 blocker。上記設計判断を要するため次アクションとして flag。

### 2026-07-01 (loop 継続⁸): ✅ hzeta0nu 実証明 — 前回の「設計判断要」flag は premature だった

**前回 (継続⁷ 補足) の root-cause 分析が第3 route を見落としていた**。「抽象 IsCoherent は ⊥1_G を
落とすので (a) shared structure field 追加 (signature 変更=STOP) か (b) S08 Sibley deep dive」の
2択で flag したが、**複素共役 ζ̄_0 を第二の同次数メンバーに使う** clean route を見落とし。
奇位数ゆえ Ind θ_0 は非実 (`not_isReal_of_ne_trivial_of_odd_card'`) → ζ̄_0=Ind θ̄_0∈S は ζ_0 と
distinct・同次数 e。⟨ν ζ_0,1_G⟩=⟨ν ζ̄_0,1_G⟩=c (Dade ⊥1 on 差)、両像 norm-1 ±既約、c=±1 なら両方
±1_G で ⟨ν ζ_0,ν ζ̄_0⟩=⟨ζ_0,ζ̄_0⟩=0 に矛盾 ⟹ c=0。IsCoherent 変更も S08 dive も不要。

**landed (commit 58de8be2, 全 axiom-clean, full build 3890 green)**:
- `inner_constOne_eq_zero_of_orthonormal_pair` (S09_Cert): 純線形代数 core。
- `coherence_extension_orthogonal_constOne` (S09_Cert): 抽象 IsCoherent 版 (coherence_hagree で ⊥1)。
- `inner_induce_conj_eq_zero_of_frobenius_of_odd` (S14, 汎用再利用可 = lane γ 14.11 も): 奇 Frobenius
  ⟨Ind θ, Ind θ̄⟩=0。**明示 instance binder** で whnf-cheap (FiniteInduce scope 内は coset-sum coercion
  が whnf 爆発 1.6M 要 → 抽出で 12s、[[lean-finiteinduce-scope-whnf-extract]])。
- `witness_L_hzeta0nu` (S14): witness L distinguished θ_0 に配線。body sorry-free (継承 sorryAx は
  typeIA_eq_sharp=(12.1) 支持同一視の別 gate のみ、⊥1_G content は完全 sorry-free)。

**残 = hB producer 組み立て** (task): `zetaNuRhoNormSqGeOfDade` に witness_L_hzeta0nu(hzeta0nu) +
hζ0norm (inner_self_induce_eq_one_of_frobeniusGroup) + a/ha (exists_betaDecomp_a) + hsmall
(frobenius_two_mul_card_complement_add_one_le_card_kernel) を供給 → CounterexampleDadeData.hB。
その後 exists_counterexample_dade_data の他 field (§12 char sorry: 12.11/12.14/12.15) が gating。
