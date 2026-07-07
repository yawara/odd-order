---
id: 9017
slug: bg-15-9-centralizer-escape-multi-consumer
title: "shared-infra: BG Cor 15.9 (centralizer_escape_final_local) + Thm 15.8 — S16 escape package + Pf §13 S-instance TI-set の multi-consumer gate"
created: 2026-07-06
---

# shared-infra claim: BG §15 Cor 15.9 (Sibley/FT escape package) — S16 + Pf §13 の multi-consumer gate

> **claim-before-build (lane b, issue 1017 /loop から派生)**。BG §15 の残 bare sorry
> `centralizer_escape_final_local` (BG Cor 15.9) が **2 クラスタ**から consume される cross-cluster
> gate と判明。lane b (Pf §13 coherence) と lane c (S16) が共に下流。**現状どのレーンも未 claim** (9000 scan 済)。
> owner/分担は hub 裁定。本 issue = gate の可視化 + dedup。

## ⚖️ HUB RULING (2026-07-06 夕, レーン分担監査 + ユーザー裁可「b の drift 追認」) — **owner = lane b**

7-agent レーン分担監査 (branch tip code-level 検証 + adversarial critic) で、BG §15/§16 が
「**共有凍結**」と誤ラベルされたまま **計 4 bare sorry** (`S15_MF.lean` の Thm 15.8 `tau2_transfer_constraint`
+ Cor 15.9 `centralizer_escape_final_local`、`S16_MainResults.lean` の 2 本) を残し、b の Pf §13 coherence
(1017 G2) と BG-side S16 endgame の**両方を binding する真の bottleneck** かつ **どのレーンも正式 owner でない**
と確定。b は既に本 chain を ad-hoc に drive 済 (更新 #1/#2: chain BOUNDED を確定・`card_kappaHall_prime_of_isTypeP2`
landed) ⟹ **trajectory 保全としてこの drift を追認、BG §15/§16 node の owner = lane b** (ユーザー裁可 2026-07-06)。

**裁定内容**:
1. **owner = lane b**。`OddOrder/BG/Ch4_FamilyOfMaximal/{S15_MF.lean §15.8/15.9 部, S16_MainResults.lean}` の
   BG §15/§16 残 sorry は **b の active territory** (merge_monitor 🔒 マップ + owned_re を更新、「BG=共有凍結」は
   この node について解除)。他 BG/** は従来どおり共有凍結。
   - **carve-out 拡張 (2026-07-06 合流 tick)**: `S14_TypePCounting.lean` の Cor 14.12 (`typeP2_neighbor_is_typeF`
     + 新 `_of_mem` variant、Thm 15.8 が要する `K⊆F(E)` export) も **b territory に拡張**。既存 theorem の
     signature 保持・sorry 2→2 regression なし・他 owner なし・new axiom なしを hub が検証 → 軌道保全 (STOP でない)。
     b は今後 §14 への追加編集を hub に proactive flag すること (今回は事後追認)。
2. **Thm 15.8 `tau2_transfer_constraint` の signature 訂正を承認** (更新 #2 coordination point (ii))。現 signature は
   `H` を `hHtau` のみで導入し M との signalizer-neighbour link を欠く = **unsound (tau2 H={|K|} 導出不能)**、
   かつ **consumer 0**。Coq 準拠 (Mstar/U/r/R/H∈𝓜(N(R)) witness bind) への訂正は「unsound carrier の是正 + consumer 0」
   ゆえ STOP 条件でなく**推奨**。b は訂正後の sound signature で build してよい (訂正内容は本 issue に記録)。
3. **S16→S15 architectural hoist を承認** (更新 #1/#2 coordination point (iii))。`typeF_frobenius_of_tau2_prime_free`
   を S16_Lemma1413 から S15 上流へ hoist (or Cor 15.9 relocate)。BG-side S16 は本裁定で **b 所有**ゆえ import cycle
   解消の hoist は b の territory 内 (lane c の Peterfalvi `S16_NonExistenceG.lean` には**跨らない** — critic 検証:
   c の所有 file は本 escape node を参照 0)。
4. **prime-TI (9014) / §5 coherence (1017-arith) は本 gate ではない** (監査で code-verified: PrimeTIResidue.lean /
   S07_Subcoherent.lean 共 0-sorry、Merge 'b' で landed)。1017 が ~23 iteration 後に収束した先が本 node。

## 何が gate か

**`centralizer_escape_final_local` (`OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean:9407`) = BG Cor 15.9**
(mmd L4240、"final local landing point for a centralizer escaping M — Sibley/Feit–Thompson package used by §16")。
現状 **bare `sorry`** (L9421)。statement: escaping `x ∈ σ-sharp(M)` (`C_G(x) ⊄ M`)、signalizer `N`
(¬type-F) から `IsTypeF M ∧ ¬FittingIsTI M ∧ IsTypeP2 N ∧ ∃ Frobenius complement E, r ∈ tau2 N, …`。

隣接: **`tau2_transfer_constraint` (`S15_MF.lean:9397`) = BG Thm 15.8** (mmd L4264) も **bare sorry** — Cor 15.9 の
上流 (tau2 transfer)。

## 2 consumer (cross-cluster)

1. **BG side (lane c 領域)**: `exists_RData_escape_structure` (`S16_MainResults.lean:5695`) が L5764 で
   `centralizer_escape_final_local` を直接 cite → S16 の RData escape 構造 (`#print axioms` sorryAx-tainted)。
2. **char side (lane b 領域、issue 1017)**: Pf §13 S-instance coherence の `tau1S_apply_induce_sub` (dade=Ind on
   A(S)) は `IsTISubset (honestTypeP2ASet S) S` に還元 (Rung B、commit d375f39c、sorry-free)。その
   escaping-exclusion (Coq `FTtypeP_facts` (e) PFsection13.v:224-234 port) の **case IsTypeP2 N** が
   `exists_RData_escape_structure` 経由で本 sorry に gated。

⟹ **本 gate を閉じると S16 の escape package と Pf §13 coherence の dade=Ind が同時に honest 化** (high-leverage)。

## やること

- [ ] **BG Thm 15.8 `tau2_transfer_constraint`** (S15_MF:9397) を build (mmd L4264、tau2(H) nonempty ⟹
      tau2(M)=∅ ∧ q=|K| prime ∧ tau2(H)={q})。
- [ ] **BG Cor 15.9 `centralizer_escape_final_local`** (S15_MF:9407) を build (mmd L4240、Sibley package)。
      依存: Thm 15.8 + §15 の他 machinery (要 scope)。
- [ ] **`FTtype1_Frobenius` kernel-regularity analogue** (case IsTypeF N): repo type-F `N` は
      `frobenius_HU0 : IsFrobeniusGroup (H⊔U0) H U0` のみ (global Frobenius 無) → Coq FT-type-1 の
      kernel-regularity 矛盾に対応する repo 補題を build (or type-F ⟹ global Frobenius bridge)。
- [ ] ⟹ Pf §13 側 (issue 1017 G2): 上を IsTISubset(A(S)) の escaping-exclusion に wire →
      `∀a, dadeHypS.H a=⊥` → bridge (A₁=A(S)) で dade=Ind → tau1S_apply_induce_sub honest 化。

## 完了条件

`centralizer_escape_final_local` + `tau2_transfer_constraint` の sorry が消える (S16 escape package honest 化)
かつ Pf §13 側で `IsTISubset (honestTypeP2ASet S) S` が sorry-free に landing (issue 1017 G2 解消)。

## 参照

- mmd: BG Cor 15.9 (L4240)、Thm 15.8 (L4264)。Coq: `BGsummaryII` / `FTsupport_facts` (c4) /
  `Frobenius_of_typeF` / `typePF_exclusion` (PFsection13.v:224-234)。
- repo landed (char-side wiring 完備): `sInstance_dade_eq_induce_of_supported_trivial_H` (bridge, cd6beac7)、
  TI-set reduction 4 lemma (d375f39c)、`signalizer_structure_of_mem_sigmaSharp` (S16:271 sorry-free)、
  `isTypeF_iff_not_isTypeP` (S14:169 sorry-free)。
- issue 1017 更新 #20-#23 (full trace)。

## 2026-07-06 更新 #1 (lane b, /loop) — Cor 15.9 dependency map 確定 + spine 2 補題 landed、真の gate = Thm 15.8 + 構造 refactor

subagent が mmd (L4298-4326) + Coq (`nonFtype_signalizer_base` BGsection15.v:1399) + repo §15 精査。**Cor 15.9
spine の 2 sub-lemma landed sorry-free** (S15_MF、build GREEN 3120 jobs、axiom-clean):
`normalizer_fittingInG_le_self` (N_G(F(M))≤M) + `not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le`
(x∈F(M)#,C_G(x)⊄M ⟹ ¬FittingIsTI M = mmd L4320 opening step)。

**Cor 15.9 dependency map**:
| sub-lemma | status |
|---|---|
| signalizer context (14.4) {N}=𝓜(C_G(x))、N type-P2、r∈τ2(N)∩σ(M) | **EXISTS** `signalizer_structure_of_mem_sigmaSharp` (S16、sorry-free) |
| M∈𝓜_𝓕 from Cor 14.12 (escape ⟹ M type-F) | **MISSING** (Coq `P2type_signalizer`) |
| F(M) not TI | **LANDED** (本更新) |
| τ2(M)=∅ (Thm 15.8) | **SORRY** `tau2_transfer_constraint` (S15_MF:9397) |
| E cyclic (Thm 15.7(d)) | PARTIAL |
| M Frobenius (kernel M_σ, cyclic compl) | **EXISTS but S16-downstream** `typeF_frobenius_of_tau2_prime_free` (S16_Lemma1413、import cycle) |
| P2+τ2=∅ collapse | **EXISTS** sorry-free |

**⟹ Cor 15.9 の 2 真 gate**: **(a) `tau2_transfer_constraint` (Thm 15.8)** = deep bare sorry、要 BG §12
prereq (ℰ²(D)/Cor 12.6/Uniqueness Theorem q∉β(G)/Thm 12.13 nonabelian Q; subagent 曰く「several §12 prereq は
既存」) — **次 build target**。**(b) 構造 refactor**: M-Frobenius builder `typeF_frobenius_of_tau2_prime_free`
が S16 downstream ゆえ Cor 15.9 (S15) から cite 不可 (import cycle) → S16→S15 hoist or Cor 15.9 relocate =
**hub-level 裁定** (lane c の S16 に跨る)。⚠ 本 chain は BG §12→§15 の major multi-session 群論 sub-project、
multi-consumer — hub は allocation (lane b 継続 vs 専用 BG lane vs lane c) を裁定可。lane b は policy 通り
ungated upstream を descend+build 継続中。

次: `tau2_transfer_constraint` (Thm 15.8) の §12 prereq を inventory → build。

## 2026-07-06 更新 #2 (lane b, /loop) — ★★BG §15 chain は BOUNDED (foundations 全存在)、Thm 15.8 blocker = signature gap

subagent inventory: **BG Thm 15.8 の §12 prereq は全て sorry-free 既存** — ℰ²(D) (`exists_elemAb_rank_two_le_E_of_tau2` S12_Theorem127:86) / Cor 12.6(a)(b) (S12_Corollary126:68/156/295) / **Uniqueness Thm 9.6 `q∉β(G)` (`tau2_not_beta`、make-or-break piece 存在)** / Thm 12.13 (`nonabelian_pgroup_isUniquelyMaximal` S12_Theorem1213:862) / Lemma 12.17 (S12_Lemma1217) / Cor 9.2 / Thm 12.7(b) / Thm 14.7(f) (`typeP_structure` P2 clause)。⟹ **chain は bottomless でない、foundational gap 無**。

**landed (本更新、sorry-free)**: `card_kappaHall_prime_of_isTypeP2` (S15_MF、Thm 15.8 第一行 |K|=q prime)。

**★Thm 15.8 の真 blocker = signature gap (foundational でない)**: repo の `tau2_transfer_constraint` は `H` を
`hHtau:(tau2 H).Nonempty` のみで導入、**M との signalizer-neighbour link 無** (Coq は `H∈𝓜(N(R))`)。⟹
`tau2 H={|K|}` は現状 **導出不能・close は unsound**。fix: (1) Cor 14.12 (`typeP2_neighbor_is_typeF` S14:11396)
の dropped 2 clauses (`K⊆F(H∩M*)` + `H∩M*=σ(H)'-complement`) を **S15_MF に再derive** (S14 は active BG §14
work 中ゆえ territorial 回避、"derivable if needed" 記載)。(2) `tau2_transfer_constraint` signature を Coq 準拠に
**訂正** (Mstar/U/r/R/H∈𝓜(N(R)) witness bind; **code consumer 0 ゆえ安全、unsound statement の訂正**)。(3) 既存
§12 infra で Thm 15.8 を prove。

**coordination points (hub 可視化)**: (i) S14_TypePCounting は active (回避で再derive)、(ii) Thm 15.8 signature
訂正 (unsound→sound、consumer 0)、(iii) **Cor 15.9 は Thm 15.8 に加えて S16→S15 architectural hoist
(`typeF_frobenius_of_tau2_prime_free` を S16 から S15 上流へ) が要 = lane c S16 に跨る hub-level 裁定**。
chain は bounded ゆえ lane b が Thm 15.8 まで build 継続 (multi-consumer、high-leverage)、Cor 15.9 の hoist は hub 裁定待ち。

次: Thm 15.8 を build (dropped clauses 再derive + signature 訂正 + §12 assembly)。

## 2026-07-06 更新 #3 (lane b, /loop 再開) — ★訂正: β theory は既存 (subagent の「absent」は Coq名grep miss)、Thm 15.8 は tractable

前 subagent の「`tau2_not_beta` / global β は repo 不在」は **誤り** ([[verify-port-state-by-number-not-coq-name]] の
罠、本 project 再発)。**β-radical theory は BG §10 に完全形式化済**: `S10.beta M` (`S10_BetaRadicalGlobal.lean` +
`S10_BetaRadicalCore.lean`)、`S10.mem_beta_iff`、`S10.Mbeta_isPiGroup`、Lemma 10.8(c)
`derived_msigma_hasNormalPComplement_of_not_mem_beta`、`isNarrow_sylow_of_not_mem_beta`。S12/S13 で多用
(S12_E:359 `q∉S10.beta M`・S12_Proposition1215:672/701 `r,q∉S10.beta`・S13_Theorem1310:808
`factorization_inf_centralizer_Q_eq_of_not_beta` が inline 導出済)。⟹ Thm 15.8 の `q∉β(G)` (Uniqueness Thm)
step は **既存 S10.beta machinery で導出可**、foundational gap 無。

**⟹ Thm 15.8 の真の残 blocker は 1 点のみ = §14 Cor 14.12 (`typeP2_neighbor_is_typeF`) の dropped 2 clauses
(`K⊆F(H∩M*)` / `H∩M*=σ(H)'-complement`) の re-export** (S14 内部 Mstar-依存 ~400行ゆえ S14 signature 拡張が要、
S15 で再derive 不能)。これは **actively-worked S14_TypePCounting への additive edit = coordination**。加えて Cor 15.9
は S16→S15 hoist (hub-level)。⟹ **chain 全体は tractable、残るは 2 つの cross-lane coordination のみ (S14 re-export +
S16→S15 hoist) = hub-territory** ([[hub-arbitrates-cross-lane-autonomously]])。lane b の unilateral 部分
(char-side wiring + sound signature + spine 補題 + β 確認) は完遂。hub は S14 拡張 + S16→S15 hoist の allocation を裁定可。

## 2026-07-06 更新 #4 (lane b, /loop 再開) — ★S14 export 完了 + Thm 15.8 Phase A landed (sorry-free) + 前 inventory の naming-trap 訂正

**⚠ 前 subagent inventory ("8 lemmas NOT YET PORTED") は STALE な docstring の parrot で誤り** ([[verify-port-state-by-number-not-coq-name]]
の罠、本 issue でも再発)。BG 番号 + descriptive 名で直接検証したところ **Thm 15.8 の machinery はほぼ全て repo に存在** (更新 #2 の慎重 inventory と一致)。

### 2 commit landed (build green, sorry-free)
1. **`typeP2_neighbor_is_typeF_of_mem`** (S14_TypePCounting、103c4a8a): Cor 14.12 を **H-parameterized** 化 + dropped
   2 clauses を export = **`∃ E E₁ E₂ E₃, SubgroupESetup H E… ∧ K≤E ∧ K⊆F(E)`**。内部で既に確立済 (`hEsetup`+`hsK_FE`)
   だったので additive。従来の ∃-form `typeP2_neighbor_is_typeF` は coatom で H を選ぶ薄い wrapper として残置 →
   S16 の 2 consumer 不変。**「S14 で再derive 不能」だった dropped clauses は export で解決**(更新 #3 の懸念は解消、S14 signature 拡張のみで足りた)。
2. **`exists_rank2_elemAb_le_centralizer_kappa_of_tau2`** (S15_MF、75006c8e): **Thm 15.8 Phase A** (Coq `cKA` まで)。
   `SubgroupESetup H` + `K⊆F(E)` + prime `q₁∈τ₂(H)` → `∃ A∈ℰ²_{q₁}(E), A≤E ∧ A⊆C(K)`。

### 検証済 Coq→repo 補題マップ (Thm 15.8 `tau2_P2type_signalizer` の残 Phase B/C/D)
| Coq step | repo lemma (verified present) |
|---|---|
| `Ptype_structure` (prime q) | `card_kappaHall_prime_of_isTypeP2` (S15_MF、既 landed) / `S14.typeP_structure` |
| `ex_tau2Elem` | `S12.exists_elemAb_rank_two_le_E_of_tau2` (SubgroupESetup 取る) |
| `tau2_compl_context` (A⊴E) | `S12.elemAb_normal_in_E_of_tau2` (S12_Corollary126:379) |
| `sigma'_nil_abelian` | `S12.nilpotent_sigmaComplement_abelian` (S12_Corollary1210:158).1 |
| `tau2_not_beta` (q∉β) | `S12.tau2_prime_mem_sigma_diff_beta` (S12_Lemma1211:390、q∈σ(Mst)\β(Mst) 形) |
| `Ptype_embedding` (L=M* 構造) | `S14.typeP_duality` (S14 で使用中) |
| Cor 12.6(a)(b) | `S12_Corollary126` (`centralizer_le_E_of_tau2` 等) |
| `Fcore_structure` (M*_σ nil / Sylow Q⊆F) | S15_MF `maxNilpotentNormalHall_*` + Thm 15.2 machinery |
| Uniqueness Thm 9.6 (`cent_uniq_Uniqueness`) | `BG/Ch2_Uniqueness/S09_Theorem91` |
| `nonabelian_pgroup_isUniquelyMaximal` (Thm 12.13) | `S12_Theorem1213` |
| `nonabelian_tau2` (τ₂(H)={q}, |X|=q) | `S12.tau2_singleton_of_nonabelianSylow` (S12_Theorem127d:550、大 bundle) |
| `Ptype_cyclics` (K≠1, K⊆(L_σ)') | `S14.typeP_structure` / Ptype cyclic clause |
| `kappa_structure` / `kappa_compl_context` (τ₂(M)=∅) | `S14.kappa_*` 系 |
| `pprod_focal_coprime` (Q nonabelian) | 要 grep (focal/coprime、§12 内) |

### 残 Thm 15.8 (Phase B/C/D、= 一続きの assembly、次 iteration)
- **B**: A⊆C(K)⊆M* (`sAL`、hMstar から C(K)⊆Mstar) → A⊆M*_σ (Cor 12.6(b)) → L-structure (`typeP_duality`) →
  q,q1∈σ(L)、Q=O_q(L) Sylow → **def_q1: q1=q** (Uniqueness `cent_uniq_Uniqueness` + Q∈𝒰) → **τ₂(H)={q}**。
- **C**: P1maxL / nilLs (Fcore_structure) / K⊆(L_σ)' (Ptype_cyclics) / Q nonabelian (pprod_focal) / |X|=q
  (`tau2_singleton_of_nonabelianSylow`)。
- **D**: X≠K → X⊄M → C(U)⊄M → **τ₂(M)=∅** (`kappa_compl_context` + tau2_compl_context)。
これらは standalone helper に切りにくい一続きの論証ゆえ、Thm 15.8 本体を inline で assemble する (Phase A helper を cite)。
- **Cor 15.9** (`centralizer_escape_final_local`): Coq `nonFtype_signalizer_base` (BGsection15:1399)。
  `FT_signalizer_context` (Thm 14.4) → `typeP2_neighbor_is_typeF_of_mem` (M∈𝓜_𝓕) → **Thm 15.8** で E2=1 →
  Thm 15.7 (`nonTI_Fitting_structure`) で E3=1/cyclic → Frobenius M。S16→S15 hoist は **b 所有** (S16_MainResults も b) ゆえ territory 内。

## 2026-07-06 更新 #5 (lane b, /loop) — ★Thm 15.8 Phase D core landed sorry-free (2 補題) + ★composite-label finding

commit `f82e4c7e` (S15_MF、build GREEN full 3933 jobs、axiom-clean = [propext, Classical.choice, Quot.sound]、real sorry count 2→2 不変)。Phase D (Coq BGsection15.v:1383-1392 の `apply/pgroupP` τ₂(M)=∅ step) の**再利用可能 core を実証明**:

1. **`centralizer_kappaCompl_le_of_mem_tau2`** (S15_MF:9614): 型-P2 の abelian (κ∪σ)'-Hall `U` + κ-Hall `K` (K≤N(U)) について、各 prime `r∈τ₂(M)` (r∣|U|) で **`C_G(U) ≤ M`**。証明 = Coq 準拠に既存 machinery を assemble: r∈(κ∪σ)' (κ⊆τ₁∪τ₃ pRank≤1 vs τ₂ pRank 2 ⟹ r∉κ) → E-setup E⊇U (`exists_subgroupESetup_with_le`) → B∈ℰ²_r(E) (`exists_elemAb_rank_two_le_E_of_tau2`) → B⊴E (`elemAb_normal_in_E_of_tau2`) + C_G(B)≤E≤M (Cor 12.6b `centralizer_le_E_of_tau2`) → ↥E 内で **B⊆U** (`Subgroup.IsPiGroup.normal_le_hall` = Coq `normal_sub_max_pgroup`; B.subgroupOf E は normal (κ∪σ)'-subgroup、U.subgroupOf E は (κ∪σ)'-Hall (hU から `relIndex_mul_relIndex` で ↥E に transfer)) → C_G(U)⊆C_G(B)⊆M。
2. **`not_prime_mem_tau2_of_centralizer_kappaCompl_not_le`** (S15_MF:9633): escape witness `¬(C_G(U)≤M)` から **`∀ r, r.Prime → r∉τ₂(M)`**。prime r∈τ₂ は r∣|M| (`S09.mem_primeFactors_card_of_pos_pRank`) + r∈(κ∪σ)' ⟹ r∣|U| (Hall index) で上の core を適用 → 矛盾。

⟹ **Phase D は「escape witness さえ得れば prime τ₂(M) は空」まで landed** (last-mile engine 完成、gated endpoint pattern)。残 gate = escape witness `¬(C_G(U)≤M)` を Phase B/C から得る deep 部分。

### ★重要 finding: literal `tau2 M = ∅` は Coq より強い (composite-label)
repo の `tau2 M = {p | p∉σ M ∧ pRank M p = 2}` は **ℕ 上** (素数限定でない)。Coq `\tau2` は nat_pred で暗黙に prime 限定ゆえ Coq `\tau2(M) =i ∅` は prime のみ主張。**repo の literal `tau2 M = ∅` は composite p も排除する必要があり、Coq より真に強い**。composite odd p (例 p=15: A=C₃×C₃×C₅×C₅, |A|=225=15², log₁₅225=2 で pRank=2 が abstract には成立) は `pRank M p=2` を持ちうる ⟹ `p∈τ₂ M`。`centralizer_kappaCompl_le_of_mem_tau2` は `[Fact r.Prime]` (ℰ² 抽出) を要すゆえ composite に直接適用不能。⟹ **full theorem の `tau2 M=∅` は (a) prime 側 = 本 helper で閉じる、(b) composite 側 = 別途「型-P2 の M で composite p は pRank≠2」を要する** (S12 の τ₂-primality 慣例と同根、要 group-theory)。**次 session は conclusion を `∀ p, p.Prime → p∉τ₂ M` の prime 形に緩めるか、composite 排除補題を別途 build するか要判断** (consumer 0 ゆえ downstream 破壊なし; ただし Cor 15.9 が literal を要するなら composite 側も要)。

### 残 Thm 15.8 gate (次 iteration、= Phase B/C の deep 一続き)
- escape witness = Phase C の X⊄M (X=A⊓C(H_σ), |X|=q) + X⊆C(H_σ)⊆C(U) (U⊆H_σ)。
- Phase C = |X|=q + τ₂(H)={q} (`tau2_singleton_of_nonabelianSylow` を neighbour H に適用、要 ∃ Sylow-q G nonabelian)。
- **def_q1 (q1=q)** = Uniqueness Theorem (Q∈𝒰 + A⊆C(Q) coprime ⟹ H=L 矛盾)。Q∈𝒰 は Coq では `Ptype_structure` の Sylow に対する rank3_Uniqueness (BGsection12.v:2642)。repo `S14.typeP_structure` は Q∈𝒰 clause を直接 export せず ⟹ rank-3 uniqueness or nonabelian 経由が要。
- Q nonabelian = `Msigma_inf_conj_inf_derived_eq_bot` (S12_Lemma1217:150) + focal/coprime。
これらは L-structure (`typeP2_partner_structure_of_mem` = 既 landed Phase B) の上に積む deep assembly。standalone 化しにくく inline assemble 要 (更新 #4 の評価と一致)。

## 2026-07-06 更新 #6 (lane b, /loop) — prime-form restatement 完了 + 残 = B/C middle (def_q1)

**landed 追加** (build green, sorry 2 不変):
- `typeP2_partner_structure_of_mem` (98ebe90a): Phase B foundation (M* partner 構造)。
- `centralizer_kappaCompl_le_of_mem_tau2` + `not_prime_mem_tau2_of_centralizer_kappaCompl_not_le`
  (f82e4c7e, subagent): **Phase D core** — escape witness `C_G(U)⊄M` から prime-form `∀ p prime, p∉τ₂(M)`。
- **prime-form restatement** (b8f6f10c): `tau2_transfer_constraint` を Coq 準拠の prime-限定形に訂正。
  ★composite finding: repo `tau2 M = {p | p∉σ ∧ pRank=2}` は ℕ-valued (`IsElementaryAbelian p := abelian
  ∧ x^p=1` が composite 指数を許す ⟹ 例 p=15 が C₃²×C₅² 経由で pRank=2)。literal `tau2 M=∅`/`={q}` は
  Coq (τ₂=素数集合) より強く ℰ²-論証で証明不能。→ hyp `∃ p prime ∈ τ₂(H)`、concl `(∀ p prime, p∉τ₂(M)) ∧
  ∃ q, q.Prime ∧ |K|=q ∧ q∈τ₂(H) ∧ (∀ p prime ∈ τ₂(H), p=q)`。**S12_Theorem127/127d の確立済み convention と一致**
  (consumer 0、9017 ruling の Coq-conformance 訂正範囲内)。⚠ **ℕ-valued tau2 def は latent shared-infra
  観点** = global に def を prime-restrict するのが deeper fix (hub 判断、当面は conclusion 側 convention で回避)。

**残 = B/C middle** (一続きの assembly、Phase D core が消費する escape witness を生む):
- sLq1 (`q1∈σ(M*)`、Coq 1307-1314: contra via `sigma'2Elem_tau2`+`tau2_compl_context`) → `A⊆M*_σ`。
- `Q:=O_q(M*)` Sylow (Coq 1317-1326, `Fcore_structure`/Thm 15.2)。
- **def_q1 (q1=q) = 主 blocker**: `Q∈𝒰` が `S14.typeP_structure` から未 expose (前 subagent 確認)。route:
  Q nonabelian (`Msigma_inf_conj_inf_derived_eq_bot` S12_Lemma1217:150 / Lemma 12.17) → `Q∈𝒰`
  (`nonabelian_pgroup_isUniquelyMaximal` S12_Theorem1213:862 / Thm 12.13) → Uniqueness Thm (S09) で H=M* 矛盾。
- τ₂(H)={q} (`tau2_singleton_of_nonabelianSylow` S12_Theorem127d:550、Q nonabelian 供給)。
- X=C_A(H_σ)、|X|=q、X≠K → X⊄M → **escape witness `C_G(U)⊄M`** (Phase D core へ)。

## 2026-07-06 更新 #7 (lane b, subagent orchestration) — B/C middle: 4 step を sorry-free 化、Step 4 (Q nonabelian) の blocker を精密特定

**landed 追加** (build green 3120 jobs, sorry 2 不変、S15_MF):
- `partner_kappaHall_le_Msigma_of_isTypeP2` (63f682f4): **Step 1** (Coq `sKLs`/`sLq`, :1300-1307) —
  partner 構造から `K ≤ M*_σ` かつ `q:=|K| ∈ σ(M*)`。
- `eq_of_uniquelyMaximal_centralized_by_rank2_le` (63f682f4): **def_q1 uniqueness engine** (:1329-1338) —
  `Q∈𝒰` + `A∈ℰ²_{q₁}`(A≤C(Q)) + A≤H + A≤M* ⟹ H=M*。★key finding: **`cent_uniq_Uniqueness` =
  `OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank`** (S09_Corollaries:35, BG Cor 9.2):
  `L∈𝒰` + `K≤C_G(L)` + `rank K≥2` ⟹ `K∈𝒰`。これで def_q1 の uniqueness 側は完全に repo 内で閉じる。
- `mem_tau2_of_elemAb_rank_two_le_E` (c1729716): **= Coq `sigma'2Elem_tau2`** (BGsection12.v:209、
  repo に**存在しなかった**converse) — σ(M)'-Hall E-setup 内の rank-2 elem-ab `A≤E` (prime p) ⟹ `p∈τ₂(M)`。
  `SubgroupESetup.mem_tau_union_of_mem_primeFactors` + `le_pRank` で τ₁/τ₃ 排除。
- `exists_sylow_eq_opiCore_of_mem_sigma_of_msigma_nilpotent` (c1729716): **Step 3 の nilpotent case のみ**
  (Coq `Fcore_pcore_Sylow` の `defLF` branch, :1317-1324) — `q∈σ(M)` + `M_σ` nilpotent ⟹ `Q=O_q(M)` は
  M の Sylow-q (∃ Sylow witness)。`oPiCore_isHall_of_isNilpotent` + `Msigma_subgroupOf_isHall` + index tower +
  既存 `exists_sylow_eq_opiCore`。
- `mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa` (d6d4280d): **Step 2 完全版** (Coq `sLq1`/`sALs`,
  :1307-1316) — M* type-P + K≤M*_σ + q∈σ(M*) + rank-2 `A∈ℰ²_{q₁}`(A≤C(K),A≤M*) ⟹ `q₁∈σ(M*)` ∧ `A≤M*_σ`。
  上の `mem_tau2_of_elemAb_rank_two_le_E` + `centralizer_le_E_of_tau2` で矛盾を組む。

### ★★ Step 4 (Q nonabelian) の PRECISE BLOCKER = BG Lemma 6.5(a) 未 port
Coq `not_cQQ` (BGsection15.v:1358-1367) は `abelian Q ⟹ K=1` (contra `ntK`) を **focal-coprime 定理**で証明:
```
apply: contra ntK => cQQ; rewrite -subG1 -(derG1P cQQ) -subsetIidl.
rewrite -(pprod_focal_coprime defLs) ?subsetIidl ?pcore_normal //.  -- ← ここ
by rewrite coprime_sym (coprimeSg sKQ) ?coprime_pcoreC.
```
`pprod_focal_coprime` = **BG Lemma 6.5(a)** (BGsection6.v:138): coprime product `G=U·H` (H Hall) で
`H ∩ G' = H ∩ U'`。数学的内容: `M*_σ=O_{q'}(M*_σ)·Q` (Q Sylow-q) で `Q∩(M*_σ)' = Q∩(O_{q'})'·Q'`。
Q abelian ⟹ Q'=1 ⟹ `Q∩(M*_σ)' = Q∩(O_{q'})' = 1` (q-group ∩ q'-group) ⟹ `K⊆Q∩(M*_σ)'=1`。

**repo 状態**: 一般 Focal Subgroup Theorem (`Isaacs.Ch05.commutator_inf_eq_focalSubgroup` = Thm 5.21、
`G'∩P = P.focalSubgroup` for P Sylow) は**存在**。しかし **coprime-product 特殊形 BG Lemma 6.5(a)
(`Q∩G'=Q∩U'` for `G=U·Q` coprime, Q Hall) は未 port** (BG §6 は FT 経路の必要分のみ port 済で 6.5 は未着手)。
これは genuine な未形式化 prerequisite (research gap でなく形式化労力 — Coq/BG に証明あり)。
加えて Coq は `sKLs': K⊆(M*_σ)'` (`Ptype_cyclics hallKs`) も使う — これも要確認 (typeP1 だと
`typeP1_msigma_eq_derivedInG` で M*_σ=M*' だが K⊆(M*_σ)' は別)。

**依存連鎖**: Step 4 が Step 5 (`Q∈𝒰` via `nonabelian_pgroup_isUniquelyMaximal` — Q nonabelian のみ要、
Sylow 不要!) → escape witness (`tau2_singleton_of_nonabelianSylow` part(c): C_G(X)⊄M) → def_q1 完成 →
Phase D core 消費 を全て gate。⟹ **B/C middle の残り全体が Step 4 = BG Lemma 6.5(a) port に依存**。

**次アクション候補** (hub 判断): (a) BG §6 の Lemma 6.5(a) `pprod_focal_coprime` を Isaacs Ch05 focal から
port (shared-infra、複数 BG consumer: S12 Cor 12.16 も使用) → 9000 issue で claim。(b) それまで Step 4-6 は
inline sorried-cite skeleton で前倒し。Step 1/2/3(nilpotent)/def_q1-engine の 5 helper は既に sorry-free 着地済。

## 2026-07-06 更新 #8 (lane b, /loop) — ★★訂正: BG Lemma 6.5(a) は既存 (#7 の「未 port」は naming-trap 誤診断)

更新 #7 subagent の「Step 4 blocker = BG Lemma 6.5(a) `pprod_focal_coprime` は未 port の real API gap」は **誤り** ([[verify-port-state-by-number-not-coq-name]] の罠、本セッション 3 度目)。BG Lemma 6.5(a) は **既に port 済**:
**`OddOrder.BG.Ch1.S06.inf_commutator_eq_of_coprime`** (`S06_Additional.lean:485`、docstring「**BG Lemma
6.5(a)** (mmd L2054): G 可解, K⊴G, G=KU, H≤U, (|H|,|K|)=1 ⟹ H∩G' = H∩U'」、sorry-free theorem)。
signature: `[IsSolvable G] {K U H} [K.Normal] (hKU : K⊔U=⊤) (hHU : H≤U) (hcop : Coprime |H| |K|) :
H ⊓ commutator G = H ⊓ ⁅U,U⁆`。subagent は `pprod_focal`/`focal`/`coprime` で grep して `inf_commutator_*` を miss。

⟹ **B/C middle は blocked でない — buildable**。残り (def_q1 engine `eq_of_uniquelyMaximal_centralized_by_rank2_le`
+ Steps 1-3 は landed):
- **Step 4 (Q nonabelian)**: ↥(M*_σ) 内で `inf_commutator_eq_of_coprime` (G:=M*_σ, K:=O_{q'}(M*_σ), U:=Q=O_q).
  Q abelian ⟹ Q∩(M*_σ)' = Q∩⁅Q,Q⁆ = Q∩1 = 1 ⟹ K ⊆ Q∩(M*_σ)' = 1 矛盾 (K≠1)。
- **二次 prereq `K ⊆ (M*_σ)'`** (Coq `sKLs'`/`Ptype_cyclics`): repo で要確認 (naming-trap 警戒 — 概念で検索)。
  `S10_LocalLemmasCore:480` に `IsCyclic (C(M_σ)⊓K⊓derivedInG M)` 系あり、`typeP_structure` clause か小 derivation。
- **Step 5 (Q∈𝒰)**: `nonabelian_pgroup_isUniquelyMaximal` (S12_Theorem1213:862、Q nonabelian のみ要、Q Sylow 不要)。
- **Step 6**: def_q1 (engine が Q∈𝒰 消費) + τ₂(H)={q} (`tau2_singleton_of_nonabelianSylow`) + escape witness `C_G(U)⊄M` → Phase D core。

## 2026-07-07 更新 #9 (lane b, /loop) — Step 4 + Step 6-def_q1 を sorry-free 着地; 残 gap を確定

更新 #8 の方針に沿って **2 つの genuine sorry-free engine を landed** (S15_MF.lean、real sorry count 2 不変、
build 3120 jobs OK):

- **`partner_opiCore_nonabelian`** (Step 4, Coq `not_cQQ`): `L` maximal, `q∈σ(L)`, `L_σ` nilpotent,
  `|K|=q`, `K≤O_q(L)`, `K≤(L_σ)'` ⟹ `¬IsMulCommutative ↥(opiCoreInG {q} L)`。↥(L_σ) 内で
  `oPiCore_sup_compl_eq_top` (L_σ=O_{q'}·Q) + `inf_commutator_eq_of_coprime` (BG 6.5(a)):
  Q abelian ⟹ K = K⊓(L_σ)' = K⊓⁅Q,Q⁆ = ⊥ 矛盾。
- **`le_centralizer_opiCore_of_msigma_nilpotent`** (Step 6 def_q1-centralize, Coq `sub_nilpotent_cent2`):
  `L_σ` nilpotent, `q∈σ(L)`, `A≤L_σ` が `q₁`-group で `q₁≠q` ⟹ `A ≤ C_G(O_q(L))`。↥(L_σ) 内で
  既存 `commutator_eq_bot_of_isNilpotent_of_normal_isPGroup` (S15:3703) で `⁅Q̄,Ā⁆=⊥`。

**確定した残り deep gap (full assembly を gate、この 1 sorry)**:
1. **`M*` type-P1** (Coq `P1maxL`): `q∉β(G)` (=`¬idealPrime q G`、`tau2_prime_mem_sigma_diff_beta` 内の
   `hqideal` 系で `tau2` から取得可) + `Ptype_structure` の「¬P1⟹q∈β」節。repo に P-type→P1 の
   clean lemma 無 (`isTypeP1_of_mf_ne_msigma` は逆向き)。type-P1 が (a) `M*_σ` nilpotent (Coq `nilLs`、
   `Fcore_structure` M_F 構造定理経由 — S16:2353 が「deeper unformalized」と記録) と
   (b) `M*'=M*_σ` (`typeP1_msigma_eq_derivedInG`、これは repo に有) を与える。(b) + `K=M*_σ⊓C(Ks)≤M*''`
   (`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` を `typeP_duality` complement に適用) ⟹
   `K⊆(M*_σ)'` = Step 4 の `hKderiv` 入力。
2. **escape witness `C_G(U)⊄M`** (Coq `not_sCUM`): `X=C_A(H_σ)`, `|X|=q` (`tau2_singleton_of_nonabelianSylow`),
   `X≠K`, `X⊄M` (`sdprod_sigma`/`eq_mmax` + κ-Hall 極大性), `X≤C(U)` (U⊆H_σ)。

`K≤O_q(M*)` (Coq `sKQ`) は routine (`isPiGroup_le_of_normal_isHallSubgroup` で normal Sylow が吸収)。
`Ptype_cyclics` の `K⊆(M*_σ)'` 自体は上記 route (2nd-derived + typeP1) で導出可、独立 port 不要。

**⟹ B/C middle 全体は「M* type-P1 (⟹ nilpotency) + escape witness」の 2 点に帰着**。両方 `Fcore_structure`/
`Ptype_structure`-P1 系の未形式化内容に依存。conditional assembly helper (この 2 点を hypothesis 化して残りを
sorry-free chain) も検討したが、`K⊆(M*_σ)'` 導出が type-P1 経由でさらに複雑化するため、clean な 2 engine を
優先 landing (fragile な 100+行 assembly で build を壊すより doneness 判定に忠実)。

## 2026-07-06 更新 #10 (lane b, /loop) — ★★訂正: Thm 15.2 も既存 (#9 gap(1) は naming-trap)、Thm 15.8 は完全 assemblable

更新 #9 subagent の「gap(1) = `Fcore_structure` (Thm 15.2) は repo analog 無し」は **誤り** (本セッション 4 度目の
naming-trap [[verify-port-state-by-number-not-coq-name]])。**Thm 15.2 は既存**: `mf_ne_msigma_typeP1_structure`
(`S15_MF.lean:6769`、mmd L4190-4202、docstring「Theorem 15.2 の構造内容は built」S15_MF:1783) + `isTypeP1_of_mf_ne_msigma`
(S15_MF:2098)。加えて `Msigma_nilpotent_of_tau2` (Thm 12.5、M_σ nilpotent from τ₂ witness) も存在。

⟹ **Thm 15.8 は missing theorem 無し、既存 machinery で完全 assemblable**。全 landed helper (Phase A/B + Steps 1-4 +
def_q1 engine `eq_of_uniquelyMaximal_centralized_by_rank2_le` + Step 6 core `le_centralizer_opiCore_of_msigma_nilpotent`
+ Step 4 `partner_opiCore_nonabelian` + Phase D core `not_prime_mem_tau2_of_centralizer_kappaCompl_not_le`) と、
以下の verified lemma で最終 assembly:

**残り assembly step (全 piece 特定済み、naming-trap 訂正済)**:
1. **M* type-P1** (Coq `P1maxL`): q∉β(M*) + `typeP_structure` (P2 でない ⟹ q∈β の対偶)。q∉β(M*) は Coq `b'q` =
   `tau2_not_beta` (q1∉β(G)) を σ(M*) 経由で。β theory = `S10.beta` (既存, `mem_beta_iff` 等)。
2. **M*_σ nilpotent** (Coq `nilLs`): M_F=M_σ ⟺ nilpotent (`maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`);
   M_F≠M_σ なら `mf_ne_msigma_typeP1_structure` (Thm 15.2) が q∈β(M*) を出す ⟹ b'q と矛盾 ⟹ M_F=M_σ ⟹ nilpotent。
3. **K ⊆ (M*_σ)'**: `Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` (subagent 確認、Ptype_cyclics 相当)。
4. Q=O_q(M*) Sylow (`exists_sylow_eq_opiCore_of_mem_sigma_of_msigma_nilpotent`、step 2 の nilpotent 供給)。
5. Q nonabelian (`partner_opiCore_nonabelian`、step 3 の K⊆(M*_σ)' 供給)。
6. Q∈𝒰 (`nonabelian_pgroup_isUniquelyMaximal`、Q nonabelian のみ要)。
7. def_q1 (q1=q): by_contra q1≠q → `le_centralizer_opiCore_of_msigma_nilpotent` (A≤C(Q)) → engine
   `eq_of_uniquelyMaximal_centralized_by_rank2_le` (H=M*) → H≠M* 矛盾。
8. τ₂(H)={q} prime 形 + **escape witness `C_G(U)⊄M`**: `tau2_singleton_of_nonabelianSylow` (S12_Theorem127d:550)
   の出力 X=A⊓C(H_σ) (|X|=q, X⊄M via ℰ¹ escaping clause) から、U⊆H_σ が X を中心化 ⟹ C_G(U)⊄M。
9. 最終 tuple: `card_kappaHall_prime` + `not_prime_mem_tau2_of_centralizer_kappaCompl_not_le` (escape witness) +
   q∈τ₂(H) + singleton。

**教訓**: 本 chain で subagent が 4 回 naming-trap で「missing」誤診断 (Ptype_embedding/tau2_not_beta/6.5(a)/Fcore_structure)。
全て既存だった。最終 assembly は上記 verified 名で intricate だが完全に構築可能。

## 2026-07-07 更新 #11 (lane b, /loop 再開) — ★★訂正: update #10「完全 assemblable」は over-optimistic、真の gate = uniqQ (type-P Sylow→𝒰 clause) の 1 点

update #10 の「Thm 15.8 は既存 machinery で完全 assemblable」は **circularity を見落としていた**。Coq `tau2_P2type_signalizer` (BGsection15.v:1262-1392) を repo 補題 availability と突き合わせて精査した結果、以下を確定:

### 真の依存グラフ (repo 補題ベース)
- **def_q1 (q1=q)** ← **uniqQ (Q=O_q(L)∈𝒰)** が必須。
- repo で `IsUniquelyMaximal Q` を得る route は **`nonabelian_pgroup_isUniquelyMaximal` (Q nonabelian 要) のみ** (grep 済、type-P Sylow→𝒰 の clean lemma は不在)。
- **Q nonabelian (`not_cQQ`)** ← nilLs (L_σ nilpotent) + sKLs' (K⊆(L_σ)')。
- **nilLs / P1maxL / sKLs'(via defL')** は Coq で**すべて def_q1 に依存** (b'q_L = q∉β(L) 経由)。
⟹ **nonabelian route は circular** (def_q1→uniqQ→Q-nonab→nilLs→b'q_L→def_q1)。update #10 の reorder (nilLs→Q-nonab→uniqQ→def_q1) はこの circularity ゆえ**成立しない**。

### Coq が circularity を破る方法 = repo に欠けている clause
Coq は uniqQ を **`Ptype_structure` の Sylow→𝒰 clause** (BGsection12、`[_ _ _ [_ uniqQ _] _]`, L1330-1333) から得る: 「type-P L の q-Sylow Q (q∈π(Ks)) は 𝒰」。これは **sylQ のみに依存** (nilLs/def_q1 不要)。**repo `typeP_structure` (S14:2336-2347) はこの clause を expose していない** (6 conjunct を確認: prime action / Kstar≠⊥ / N_M(X)=K⊔Kstar / conj-triv / P2⟹σ=β∧TISubset / 𝓜(C(X))={M} / Kstar≠M_σ — Sylow→𝒰 は無い)。

### さらに update #10 step 7 の誤り (L_σ vs F(L))
def_q1 の A⊆C(Q) centralization は Coq (L1337) で **`Fitting_nil L` (= F(L) nilpotent、常に真)** + `sQFL`(Q⊆F(L)) + `sAFL`(A⊆F(L)) を使う。update #10 が指定した `le_centralizer_opiCore_of_msigma_nilpotent` (**L_σ nilpotent 要**) ではない。⟹ この step は **nilLs 不要**で closable (F(L) nilpotent 版の小 helper を作るだけ)。

### ⟹ 真の gate = uniqQ (type-P Sylow→𝒰) の 1 点のみ、残りは全 closable
非 circular ordering: **sylQ** (Thm 15.2 `mf_ne_msigma_typeP1_structure` の complement 構造から抽出) → **uniqQ [=唯一の deep gate]** → def_q1 (F(L) nilpotent, coprime) → b'q_L → P1maxL → nilLs → defL' → sKLs' → not_cQQ (`partner_opiCore_nonabelian`) → oX=q (`tau2_singleton_of_nonabelianSylow`, Q⊆Sylow-q-of-G nonabelian) → escape witness (同 lemma の ℰ¹ escaping clause + U⊆H_σ) → τ₂(M)=∅ prime 形 (`not_prime_mem_tau2_of_centralizer_kappaCompl_not_le`)。

**次アクション**: `tau2_transfer_constraint` を上記 ordering で assemble し、uniqQ を **精密に stated な sorried keystone lemma `sylow_typeP_isUniquelyMaximal` (Coq `Ptype_structure` uniqQ component、BGsection12) として isolate**、残りは sorry-free。これは doneness 前進 (opaque bare sorry → full honest assembly + 精密に特定された 1 keystone)。keystone (type-P Sylow→𝒰) の port は次の独立 unit (deep BG §12)。

## 2026-07-07 更新 #12 (lane b, /loop) — ★★Thm 15.8 assembled sorry-free、3 keystone isolate → 1 (B) を実証明で閉じ 2 残 (A/C)

**`tau2_transfer_constraint` (BG Thm 15.8) は sorry-free 着地** (S15_MF、build GREEN 3120 jobs、
axiom = `[propext, sorryAx, Classical.choice, Quot.sound]` = 標準 3 + keystone 由来 sorryAx、新 axiom 無)。
Coq `tau2_P2type_signalizer` の spine を非circular ordering で inline assemble (subagent orchestration +
hub 検証): sylQ → uniqQ[keystone] → def_q1 (F(L) nilpotent) → b'q → P1maxL[keystone B→閉] → nilLs
(Thm 15.2 contrapositive) → sKLs' → not_cQQ (`partner_opiCore_nonabelian`) → oX/singleton
(`tau2_singleton_of_nonabelianSylow`) → escape witness (κ-Hall 極大性) → τ₂(M)=∅。

### 新 helper (sorry-free)
- **`le_centralizer_opiCore_of_fittingInAmbient_nilpotent`** (S15_MF:10041): def_q1 の A≤C(Q) を
  **F(L) nilpotent (常に真、`fittingInG_isNilpotent`)** 経由で導く = **def_q1/nilLs circularity を破る鍵**
  (更新 #11 の finding を実装; `le_centralizer_opiCore_of_msigma_nilpotent` の F(L) 版)。
- `typeP2_partner_structure_of_mem` を `Ks ≤ Mstar` も返すよう拡張。

### keystone 3 本 → B を閉じ 2 残
更新 #11 の「真の gate = uniqQ 1 点」は **不完全だった** (subagent が full 依存解析で 3 clause を検出):
- **Keystone A `typeP_partner_sylow_uniquelyMaximal_bundle`** (S15_MF:10111、**sorried**): Coq
  `Ptype_structure`/`Fcore_structure` の sAFL+sylQ+**uniqQ** (type-P L の q-Sylow Q は 𝒰) bundle。
  **真の deep gate** = repo `typeP_structure` 非expose の Sylow→𝒰 clause (更新 #11 通り)。sylQ 非nilpotent
  case も Thm 15.2 (`mf_ne_msigma_typeP1_structure`) から Sylow witness 抽出が要ゆえ bundle。
- **Keystone B `typeP_isTypeP1_of_not_mem_beta`** (S15_MF:10137、**✅ 実証明で閉じた**): subagent は
  「typeP_structure 6 conjunct から recover 不能」としたが**誤り**。type-P L → P1∨P2
  (`isTypeP_iff_isTypeP1_or_isTypeP2`)、P2 なら conjunct 5 (`IsTypeP2⟹σ=β`) で σ(L)=β(L)、q∈σ(L) と
  q∉β(L) が矛盾 → ¬P2 → P1。署名に `Ks ≤ L` 追加のみで sorry-free。
- **Keystone C `signalizer_msigma_sup_inf_partner_eq`** (S15_MF:10160、**sorried**): `H_σ ⊔ (H∩M*) = H`
  (Coq `sdprod_sigma maxH hallD`, D=H∩L)。escape witness の hneqXK で使用。repo `typeP2_neighbor_is_typeF_of_mem`
  (Cor 14.12) は **generic σ(H)'-E-setup を返し H∩M* と同定しない** → S14 neighbour lemma を強化して
  「H∩M* が σ(H)'-Hall」を expose すれば閉じる (S14 territory 内)。

### 残 = 2 keystone port + Cor 15.9
- **Keystone A** = deep §12 `Ptype_structure` の Sylow-uniqueness clause の port (最重要 gate)。
- **Keystone C** = S14 `typeP2_neighbor_is_typeF_of_mem` を強化し H∩M* を σ(H)'-Hall として expose。
- **Cor 15.9** (`centralizer_escape_final_local`、S15_MF:10595 依然 sorried): Thm 15.8 (now assembled) を
  cite して E2=1 → Thm 15.7 (E3=1/cyclic) → Frobenius M。`typeF_frobenius_of_tau2_prime_free` の
  S16→S15 hoist が要 (b territory)。live consumer = S16_MainResults:5764 `exists_RData_escape_structure`。
