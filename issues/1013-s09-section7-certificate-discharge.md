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
