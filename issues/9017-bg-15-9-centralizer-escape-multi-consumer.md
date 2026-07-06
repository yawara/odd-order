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
