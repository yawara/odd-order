---
id: 2022
slug: general-six-two-cross-lane
title: "general six_two (6.2 bound for reducible induced members) — cross-lane gate for §6 producer"
created: 2026-06-23
---

# general six_two (6.2 bound for reducible induced members) — cross-lane gate for §6 producer

> 🧾 (2026-07-02 hub): 本文の旧 lane 名 (lane-h 等) は stale — **現 owner = lane b** (§6/coherence infra、正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)。

## 背景

lane-h relane #7 (issue 2021 RESOLVED) で §6 coherence producer を生産。Pf §11/§13 consumer
(`S13.coherent_S_of_coherent_SH0C` (6.3) / `S13.coherent_quotient_bound` (6.2)) が要求する
**general Hypothesis (6.1) 形** (K=M' solvable, H=HC nilpotent, K≠H) の (6.2)/(6.3) 標準形 assembly を
新 leaf `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean` に生産した (commit `27019099`, `0aec0d82`):

- `S07.IsCoherent.subset` (coherence monotonicity) ✅ sorry-free
- `S08.six_three_descent` (general (6.3) minimal-A descent, K≠H) ✅ sorry-free
- `S08.six_three_index_bound_general` (general (6.3) per-step index bound) ✅ sorry-free

**両 consumer obligation は単一の gate `general six_two` に reduce 済**。

調査の結論 (notes/peterfalvi/s06_standalone_62_63_producer.md §4):
general (6.2)/(6.3) の PIECES は既に general 形で `S08_CoherenceCorePart1/2` に存在し
(`coherentDegreeSumBound_of_not_coherent` = (5.6) contrapositive over `S04.Hypothesis`、
`theta_degree_le_index_mul_sqrt_index` = θ-bound、degree-sum、nilpotent-central、√-arithmetic 全 general)、
フル assembled な `six_two`/`six_three` (CorePart2) は SibleyDadeHypothesis (K=H) 上。lane-h は K≠H 分離の
assembly を完了した。**唯一残る深い gate が general `six_two`**。

## やること

- [ ] **general `six_two`** を生産: K solvable normal + induced family `S = {Ind_K^L θ}` (可約 member 含む)
      に対する (6.2) bound `|K:A| − 1 ≤ 2|L:C|√|C:D|` (および C=D 特殊化 `|K:A|−1 ≤ 2|L:C|`)。
- [ ] これを `six_three_index_bound_general` に食わせて `six_three_descent` の `h62` を discharge、
      lane-c の §11 obligation を完全 unblock。

## なぜ cross-lane か

general `six_two` の核 = `coherentDegreeSumBound_of_not_coherent` ((5.6) contrapositive、general 既存) の
**orthonormality / support / generation 仮説を induced family の可約 member について discharge** すること。

- Sibley 版 (`six_two_index_bound`) は `hF : IsFrobeniusGroup L H W₁` で "Ind_K^L θ は irreducible" を保証し
  これらの仮説を `sMember_index_le_two_psi` で discharge する。
- §11 設定 (K=M' solvable) では family に可約 member (μⱼ column 等) が含まれ、その (5.2.d) R(χ) 構造は
  **§10-12 の muGrid / columnSum 機構** (S10/S12, lane-b/c 領域) で扱われる。
- ⟹ general `six_two` は §5 ((5.6) hyps) + §10-12 (family の可約 member 構造) に entangle し、
  lane-h の §6/§8 単独スコープでは閉じない。

## 完了条件

- general `six_two` (上記) が sorry-free で landed し、`six_three_index_bound_general` 経由で
  `six_three_descent` の `h62` が実 discharge される。
- lane-c が `S13.coherent_S_of_coherent_SH0C` / `coherent_quotient_bound` を本 producer cite で閉じられる
  (別途 lane-c 側で SOf/Sset の pin = §6 への bridge が要; notes §6 参照)。

## 参照

- producer note: `notes/peterfalvi/s06_standalone_62_63_producer.md` (§4 design question RESOLVED, §6 bridge, §7-8 残作業)
- producer leaf: `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean`
- general pieces: `OddOrder/Peterfalvi/S08_CoherenceCorePart1.lean`
  (`coherentDegreeSumBound_of_not_coherent`:2451, `theta_degree_le_index_mul_sqrt_index`:557,
  `sum_div_normSq_induce_kernelFilter_eq`:2526, `exists_coherentBreakPair`:952)
- Sibley assembled: `OddOrder/Peterfalvi/S08_CoherenceCorePart2.lean` (`six_two`:3786, `six_three`:3924)
- consumer: `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean` (`coherent_S_of_coherent_SH0C`:188, `coherent_quotient_bound`:215)
- relane #7 / lane state: issue 2021 (RESOLVED), [[lane-h-driving-wielandt-91]]

## 2026-06-23 HUB 応答 — cite-policy で進行、reassignment 不要

hub 監査: 本件は reassignment あおぎでなく cross-lane 依存の文書化と判断。**lane-h は relane #7 継続のまま
general six_two を自 leaf (S08_Theorem62_63_Standalone) で生産**する。方針:
1. **§10-12 muGrid/columnSum (S10/S12) の既存 lemma を cite** して可約 member の R(χ) / orthonormality /
   support / generation 仮説を discharge ([[feedback-cite-sorried-lemmas-if-signature-correct]]; sorried sig でも可)。
2. 必要な §10-12 signature が **未 export / 未 stated** なら、lane-b (S12 owner) / lane-c に **targeted な
   signature 要請 issue** を立て、当面は sorried cite で general six_two の assembly を先に積む (手を止めない)。
3. 既存 S10/S12/S05-S08 本体は触らず cite のみ・生産は自 leaf 隔離 (lane-b/c 復帰時の衝突回避)。
本 issue は tracking として open 維持 (general six_two landing で close)。

## 2026-06-23 lane-h resume — general six_two ASSEMBLED, gate narrowed to `h56` (lane-b/c)

hub 方針通り、§10-12 muGrid に gated な reducible-member 核を clean oracle に isolate し、それ以外の
general (6.2) を**全実証明**した。`OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean` に landed
(全 sorry-free + axiom-clean + AxiomsCheck 登録、full build 3883 green):

- `map_mk'_le_center_iff` — 中心性 ⟺ commutator 条件。
- **`inducedMember_re_le_general`** — (6.2) θ-degree bound `ψ(1) ≤ |L:C|√|C:D|` for `ψ = Ind_K^L θ`
  from a **solvable** kernel `K ⊋ C`, **自由 section `B ≤ D ≤ C ≤ K`** (Clifford a-half via general
  `theta_degree_le_index_mul_sqrt_index`, 中心性は `subgroupOfEquivOfLe` で ↥C→↥(C.subgroupOf K) transport)。
  ← Sibley は central case K=C のみ。
- **`six_two_general`** — (6.2) real-inequality `|K:A|−1 ≤ 2|L:C|√|C:D|`, **自由 C,D**, oracle `h56` から導出。
  **両 §11 obligation を直接 served**: 11.3 = (C,D)=(H,A) (→ `six_three_index_bound_general` の `h62`)、
  11.4 = (C,D)=(HC,HC) (`√1=1` → `|M':H₁|−1≤2|M:HC|`)。
- **`six_three_of_six_two_oracle`** — **single-cite (6.3) producer** for §11/§13 (11.3):
  `six_three_descent ∘ six_three_index_bound_general ∘ six_two_general(C=H,D=A)` を bundle。

⟹ **両 §11 obligation は `six_two_general` で served、残は単一の per-section `h56`** のみ。**`h56` =
solvable kernel の (5.6) norm-weighted coherence bound = lane-b/c ask** (下記)。

### lane-b/c への targeted 要請 (`h56` の signature)

`six_three_of_six_two_oracle` (および `six_two_general`) が要求する per-section oracle。各 section
`B ≤ A ≤ H₁` (`A ⧸ B` central in `H ⧸ B`, `S(A)` coherent, `S(B)` not coherent) に対し:

```lean
∃ θ : IrreducibleCharacter ↥K,
  (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
  (Nat.card (↥K ⧸ A.subgroupOf K) : ℝ) - 1 ≤ 2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re
```

= break member `ψ = Ind_K^L θ ∈ S(B)` (θ∈Irr K trivial-on-B) で `|K:A| − 1 ≤ 2ψ(1)`。これは
case-B `S08_Theorem63.sSubFiltration_sum_le_two_psi_caseB` (Sibley nilpotent kernel H + Hypothesis46) の
**general solvable kernel `K = M'` 版**。核 = `coherentDegreeSumBound_of_not_coherent` ((5.6)
contrapositive, general 既存) の orthonormality/support/generation 仮説を可約 induced member の
constituent (= §10-12 muGrid/columnSum) で discharge すること。**lane-h §6/§8 スコープ外、lane-b/c 領域。**

本 issue は open 維持 (`h56` landing で close)。lane-h の producer 側は完了。

## 2026-07-05 lane-a — h56 は lane-a frontier に編入 (両 (11.8) 残 gate の共通上流)

**Ownership 更新**: 2026-07-04/05 再々編で §9-13 char 核 + S08 非-coherence-glob (`S08_Theorem62_63_Standalone`
含む) = **lane a**。ヘッダの「現 owner = lane b (07-02)」は stale。h56 の実体 (§10-12 muGrid/columnSum
構造) も a 所有。⟹ **h56 = lane-a の次 frontier** (charParam_d_modEq_one 完了後の上流優先)。

**なぜ今 h56 か**: (11.8) の残 2 gates の共通上流。
- gate 2 `card_SHCSet_filter_eq_charParam_n` ((11.8.1) n-count) は (11.6) C=U' (U/C abelian order u) を
  経由 ⟸ (11.5) M''=HC ⟸ (11.4)+(11.3) ⟸ **h56** (S13 の該当 4 定理は全 sorry、
  `six_three_of_six_two_oracle`/`six_two_general` cite + h56 供給 + S13.SOf pin で閉じる)。
- gate 3 `coherent_Sset_of_column_identities` ((11.8.6) τ₂) の S₂-coherence ((11.7)) も (11.5) 構造 +
  (9.11) を要する。
- Coq 対応: (11.3)=FTtype34_noncoherence / (11.4)=bounded_proper_coherent / (11.5)=FTtype34_der2 /
  (11.6)=FTtype34_facts (PFsection11.v:205-350)。**(11.3) は (9.11) 不要** (bounded_seqIndD_coherence
  (6.3) + (10.8) proven のみ) — S13 docstring の「(11.7) 経由」読みは Coq route でバイパス可。

**Coq model (h56 の中身)**: PFsection6 `coherent_seqIndD_bound` (6.2) は break-member を直接見つけるの
でなく **`extend_coherent` (5.4) induction**: S(A)-coherent から S(B) の pair {ψ,ψ*} を 1 つずつ吸収、
全部吸収できれば S(B) coherent (unless 枝)、失敗点 ψ で extend_coherent の norm-sum bound 反転が
`|K:A|−1 ≤ 2|L:C|√|C:D|` を与える (`sum_seqIndD_square` + `irr1_bound_quo`)。
⟹ Lean h56 = `coherentDegreeSumBound_of_not_coherent` ((5.6) contrapositive, CorePart1:2451,
general 済) の**仮説 discharge for solvable-K induced family**: orthonormality/support/generation を
可約 member (= μ-column sums) 込みで。2026-07-05 の `muGrid_column_sum_mem_sOf_H0_and_reducible`
(S12_Section9Counts) で「可約 member = column sums、source = chiRestrict、pairwise distinct」の
enumeration が整った — これが (5.2.d) R(χ)-構造 discharge の素材。

**次 iteration 手順 (lane a)**:
1. `coherentDegreeSumBound_of_not_coherent` (CorePart1:2451) の正確な仮説リストを読み、
   solvable-K family での discharge 計画を立てる (Coq PFsection5 (5.6) 証明と併読)。
2. h56 を `S08_Theorem62_63_Standalone` (a 所有) に landing → `six_three_of_six_two_oracle` 完全 discharge。
3. S13 side: SOf free field を induced-family filter に pin (enrich) → (11.3)/(11.4) を producer cite で
   閉じ、(11.5)/(11.6) を assembly。
4. gate 2 n-count: (11.6) U/C abelian order u + M/HC Frobenius (`frobMtilde` 相当は
   `typeP_uW1_frobenius` 系) + Ind-linear irreducibility で S1 count = (u−1)/q = n。

## 2026-07-05 lane-a: h56 producer 完成 — `exists_source_index_le_two_psi_of_break` (S08_SixTwoGeneral)

**abstract 層は閉じた。** 新 leaf `OddOrder/Peterfalvi/S08_SixTwoGeneral.lean` (全実証明 sorry-free +
axiom-clean, commits 51d1d54f / 10a7e8f4 / 32c7ece4 / 82d570f3):

- `inducedKernelFamily K X` = S(X) (Coq seqIndD): mem/antitone/finite/conj-closed/anchor +
  **直交性・実正 norm・real-freeness (奇数位数)** — 可約 μ-column member 込みで全部実証明。
- `exists_coherentBreakPair_union`: **A'/B 包含なし** の first-obstruction ((11.4) の
  (H₁,H₀C) 対応; chain を Sa ∪ Sb 上で走らせ IsCoherent.subset で落とす)。
- P1 `inducedKernelFamily_degreeSqNormReBound_of_break_k`: weighted engine
  (`coherentDegreeSqNormBound_of_not_coherentW_k`, 既存・完成済だった) への plumbing 全 discharge
  (Gram / deg 比 / K^#-support / ZIrr integrality / 生成 2 条)。
- P2 `inducedKernelFamily_SA_sum_le_two_psi_k`: + B2 → |L:K|(|K:A'|−1) ≤ 2ψ(1)χ₁(1)。
- **P3 `exists_source_index_le_two_psi_of_break` = h56 producer**: 結論が
  `six_three_of_six_two_oracle`/`six_two_general` の h56 oracle と一致
  (∃θ ∈ Irr K trivial-on-B, |K:A'|−1 ≤ 2(Ind θ)(1).re)。

**残 = S13 instantiation のみ (次 frontier)**。P3 の §11-side hypotheses:
1. **hanchor**: irreducible degree-|L:K| member of S(A') — W₁ が K/A' の linear char に非自明に
   作用する事実 (K=M', L=M, |L:K|=q)。Frobenius W₁-action (8.4.d 系) から。
2. **hdatum**: break Da + per-member R(χ)-分解 (coherent extension と両立、Da family と直交)。
   - irreducible member: `memberExtensionDecomposition` (CorePart1) の適用で一般 discharge
     可能な見込み (per-member 事実は family 層で証明済) — まずここから。
   - **μ-column member: 本丸。** hS₁coh.extension(μⱼ) の multiplicity-free 性 = (11.8.6)/(5.8) 型
     uniqueness。S12 muGrid (`muGrid_column_sum_mem_sOf_H0_and_reducible` ほか) +
     grid 直交性が素材。任意の coherent extension に対する statement が要る点に注意
     (hdatum は witness ∀-quantified)。
3. routine: hKsupp (K^# ⊆ Dade support set — §9/§10 の A(M) 定義確認), h1A, hSBne
   (= B ⊊ K solvable の linear char, `exists_inducedKernelFamily_member_degree_index` 流用),
   hodd (M ≤ G 奇数)。
4. S13 の SOf free field を `inducedKernelFamily (M'.subgroupOf M)`-形に pin
   (§9 の sOf は「H ⊄ ker」filter 付き = S − S(H); §11 の S は full family — S(H) 部分の
   合流に注意, (11.2) remark)。τ free field = dadeIntegralCharacterMap の形に pin
   (S12 側の (9.5)/(10.x) Dade hypothesis instance を確認)。

作業順 (上流優先): 2 の irreducible-member 分枝 → 3 routine pins → 1 anchor → 2 の μ-column
(最深, S12 grid 併用) → 4 pin + (11.3)/(11.4) 閉じ。

## 2026-07-05 lane-a (loop 2): hdatum の irr-irr 対角を一般 discharge — 残 = μ-column pair のみ

commit 54bf51db (S08_SixTwoGeneral 追記, sorry-free):
`inducedKernelFamily_memberDatum_of_irreducible` (member D + coupling) /
`inducedKernelFamily_breakDa_of_irreducible` (break Da, tau1=τ 定義的) /
`inducedKernelFamily_memberDatum_orthogonal_breakDa_of_irr_irr` (両者の直交性 = hdatum ∃D 節
の irr×irr 完全 discharge) + `exists_anchor_of_linear_of_inertia_eq` (hanchor ← inertia 条件)
+ `inducedKernelFamily_nonempty_of_commutator_ne_top` (hSBne)。

**S13 の hdatum 残 obligation (更新)**:
- break = μ-column の Da (ψaux = a·χ₁): grid 供給 (caseB の columnDecompositionTau 相当を
  §11 grid で)。
- member = μ-column の D (ψ=0, tau1 = hS₁coh.extension): **(5.8)-型 uniqueness が本丸**
  (任意 coherent extension で μⱼ ↦ ±Σωᵢₖ 形; S12 grid + (11.8.6) 論法)。
- 直交性 (irr×col, col×irr, col×col): grid の R(μ) family と Dade R(χ) family の
  imageSet-level 直交。
- 注: helpers は imageFamily を**等式で expose** (subtype 第2成分) — S13 は rewrite で
  接続する (obtain 分解で fvar 化させると whnf 爆発、直接 projection + .2.1/.2.2 を使う)。

hanchor の §11 discharge 素材: W₁ の M'/A' linear char への作用が非自明
(inertia θ = M' なる linear θ) — (8.4.d) W₁ fixed-point-free on (HC)/M'' 系から。

## 2026-07-05 lane-a (loop 3): routine pins 全 discharge — S13_SixTwoBridge (commit afed3a1f)

新 leaf `S13_SixTwoBridge.lean` で h56 producer の routine pins を S12.Hypothesis で実証明:
hKsupp = `mderivSharp_subset_A0` (**決め手: 既存 `typePA_eq_sharpSubgroup_derivedInG` で
A(M) = (M')^# ちょうど** → A₀ ⊇ (M')^#) / h1A = `one_notMem_A0` / hodd =
`card_odd_of_isMinimalSimpleOdd` / family 一致 = `inducedFamily_eq_inducedKernelFamily_bot`
(§10 pin 済み S = inducedKernelFamily K ⊥、K = (derivedInG M).subgroupOf M)。

S12 Dade context は完全 pin 済み確認: hyp.tau = dadeIntegralCharacterMap hyp.dadeData.dade
(= S04.Hypothesis G (typePA0 M) M) + hyp.hconj — producer 要求と一致 (τ/A0 の S13 free field
pin はこの実体で行う)。

**h56 残 obligation (最終形)**:
1. S12.Hypothesis 上の fully-pinned producer wrapper (機械的、instance 束ね)。
2. anchor: inertia θ = M' なる linear θ (trivial on A') — W₁ 作用非固定。
3. hdatum の μ-column pairs (break-Da / member-D / 直交性) — S12 grid + (5.8) 型 uniqueness。

## 2026-07-05 lane-a (loop 4): anchor 前提 2 点 landing (27b065b8)

`isTypeIIIorIV` (type V 排除 = (10.10) sorried-cite; AxiomsCheck 登録は (10.10) closure 後) +
`coprime_card_W1_derived` ((|W₁|,|M'|)=1 完全実証明: H 側 typeP_coprime_H_uW1 + U 側 Frobenius)。
inertia 核の設計 fix: **w = k·w₁ᵃ 分解で primality 不要** (内部自己同型は abelianization 上自明)。
実装部品: coprime_fixedPoints_quotient_of_coprime_normal (3.28) / map_mul_of_apply_one_eq_one /
centralizer_W1 + W2_le (→ secondDerived ⊆ commutator 翻訳) / subgroup_le_inertia / M_complement 分解。

## 2026-07-05 lane-a (loop 5): anchor 完全 discharge — (8.4.d) inertia 実証明

`inertia_eq_derived_of_linear` (非自明 linear θ の inertia = M'; FPF-injective-surjective route,
hom 構造不要) + `exists_anchor` (S(A') の irreducible degree-|M:M'| anchor, ∀ A' with
proper-commutator quotient)。**h56 の残 = hdatum の μ-column pairs のみ** (次 frontier):
break-Da (column) / member-D (column, (5.8) 型 extension-uniqueness) / 直交性 (col 絡み) —
S12 muGrid 素材との接続。producer wrapper への anchor 配線 + (11.3)/(11.4) skeleton も可。

## 2026-07-05 lane-a (loop 6): producer 精錬 + S13 SOf pin (c58f80c3)

`exists_source_index_le_two_psi_of_ne_top` (anchor/hSBne 自動 discharge — 残 = hdatum +
coherence dichotomy のみ) + S13.Hypothesis に **SOf_eq field 追加 = SOf pin 実現** (S(X) =
inducedKernelFamily M' (X.subgroupOf M); constructor 未存在で既存破壊なし) + [finiteG] field。
次: (11.4) wiring (named hdatum obligation `sixTwoDecompositionData` 起こし + (6.2) 算術) →
その後 hdatum μ-column 本体 (S12 grid)。

## 2026-07-05 lane-a (loop 7): (6.2)-§11 が単一 named obligation に集約

`sixTwoDecompositionData` (named sorried — h56 チェーン唯一の sorry、μ-column datum) +
`exists_source_of_coherence_dichotomy` + `six_two_dichotomy_bound` (任意 (C,D) section で
(6.2) bound、consumer-ready)。次: (11.4) HC-instantiation + index 算術 / (11.3) 6.3-route /
datum の μ-column 本体。

## 2026-07-05 lane-a (loop 8): (11.4) 群論前提 landing

C_normalized_by_M field (S11 cSub = C_U(H̄) ≠ (11.2) C = C_U(H) の確認込み) + H₀C/HC 正規性
一式 + **H_not_le_H0C** (normal_mul 分解)。残: trace-ne-⊤ 2 行 + hcentral (H'≤H₀ route) +
index 算術 + (11.4) glue → その後 μ-column datum。

## 2026-07-05 lane-a (loop 9): (11.4) 前提完了 — ⁅HC,HC⁆ ⊆ H₀C

H0C_trace_ne_top / commutator_mem_H0 (elementary abelian 経由) / commutator_HC_mem_H0C
(H·C 分解 + Commute swap)。残 (11.4): hcentral wrapper + H₁-trace-ne-⊤ + index 算術 + glue。

## 2026-07-05 lane-a (loop 10): hcentral 完了 — (11.4) 残は index 算術 + glue のみ

trace_ne_top_of_lt_derived / HC_quotient_H0C_comm / HC_central_condition (Normal は
instance-arg)。(11.4) glue の全数学的前提が揃った — 残 = relIndex 変換 (relIndex_subgroupOf /
relIndex_mul_relIndex / card_W1_eq_derived_index) + |HC| = |H||C| (disjoint sup card) + 適用。

## 2026-07-05 lane-a (loop 11): **(11.4) 閉了** — coherent_quotient_bound 実証明

bare sorry 撤去 (依存 = sixTwoDecompositionData のみ)。index 算術 (card_HC /
HC_relIndex_derived / HC_trace_index) + glue。instance desync は legacy binder 削除で解決。
次候補: (11.5) HC_le_secondDerived ((11.4) 消費、(5.7)+(11.1)/(9.6) 算術) or (11.3) 6.3-route
or μ-column datum 本体。

## 2026-07-05 lane-a (loop 12): (11.5) 準備 — M''-正規性 + (5.7) named

le_normalizer_secondDerived (pointwise_smul 既存活用) + secondDerived_coherent (named sorried;
配線先 = coherentEqualDegree_fromDade)。(11.5) 残: FPF-dvd (W1_dvd_index_of_fixedPoints_le
再利用可、hfix = W2_le 直) + C<U (U_noncentral_on_quotient 経由) + tower + glue。
open named sorries: sixTwoDecompositionData (μ-column) / secondDerived_coherent ((5.7) 配線) /
coherent_S_of_coherent_SH0C ((11.3) = 6.3-route、producer 部品は全て揃済)。

## 2026-07-05 lane-a (loop 13): (11.5) 部品完了 — C⊊U + FPF-dvd

C_lt_U (U_noncentral_on_quotient 経由; MulAut-coe は defeq-change で) +
q_dvd_secondDerived_relIndex_HC_sub_one (W1_dvd_index_of_fixedPoints_le 再利用)。
残 = 純算術 glue (tower + (11.4)@M'' + 奇偶) → HC_le_secondDerived 閉了へ。

## 2026-07-05 lane-a (loop 14): **(11.5) 閉了** — M'' = HC 完成

HC_le_secondDerived 実証明 (relIndex=1 化 + (11.4)@M'' + tower + FPF-dvd + 奇偶)。
secondDerived_eq_HC 自動完成。残 named: sixTwoDecompositionData / secondDerived_coherent /
coherent_S_of_coherent_SH0C。(11.6) 消費側の再点検 or (5.7) 配線が次。

## 2026-07-05 lane-a (loop 15): (11.6) C = U' 閉了

- `exists_mul_of_mem_sup_of_normalized` (sup 分解 helper 公開化) +
  `secondDerived_le_H_sup_derivedU` (M'' ≤ H ⊔ U'; mk' mod-H 計算) +
  `C_eq_derivedU` (C ≤ HC = M'' ≤ H⊔U', H⊓U=⊥ で H-部分消去)。
- `core_structure` (11.6) 残 = conjunct 1 (H は p-群; (9.3) U centralizes O_{p'}(H) 要)
  + conjunct 3 (H₀ = H'; BG 1.6(d) 要)。commit 426b995c。

## 2026-07-05 lane-a (loop 16-19): **(11.6) H は p-群 閉了** + C=U' 済

- loop 15: C = U' (M'' ≤ H⊔U' 経由)。loop 16-19: S13_CoreStructure leaf 新設、
  (9.3) 転写 → O_{q'} ≤ C_H(U) → R=O_{p'}(H) 定義 → M'' ≤ O_p⁅R,R⁆ ⊔ U' →
  R perfect → R=⊥ → IsPGroup p H。commits ef7d40d5/e3d4707b/8e302745/(this)。
- core_structure 残 = H₀ = H' conjunct のみ (BG 1.6(d) + (11.5))。

## 2026-07-05 lane-a (loop 20): **(11.6) 完全閉了** — core_structure sorry-free

- H₀ = H' 閉: K₁=⁅H,M'⁆ bound + trap + H̄ 上 BG 1.6(d)
  (fixedPoints ⊓ actionCommutator = ⊥)。4 clause 全実証明。
- 次 (文書順): (11.7) H_elementaryAbelian (|H|=p^q, H₀=1)。
  quotient_order |H| = p^q·|H₀| + (11.6) H₀=H' + p-群機構が材料。

## 2026-07-05 lane-a (loop 21): (5.7) instance 配線完了

- `secondDerived_coherent` 実証明: `SOf_secondDerived_eq` (S(M'') = 次数-w₁ 既約
  部分族; (8.4.d) inertia + kernel⟺linear) → `SHC_isCoherent` transport。
- 残 sharp sorry: `charValue_one_eq_one_of_commutator_le_ker` (G' ⊆ ker → 次数 1、
  汎用) — 次 iteration。その先: (11.3) coherent_S_of_coherent_SH0C (6.3-route) /
  (11.7) H₀=1 (symplectic) / sixTwoDecompositionData。commit e07728c0。

## 2026-07-05 lane-a (loop 22): charValue_one… 閉 — S13_MaximalIII_IV 残 sorry は (11.3) のみ

- G' ⊆ ker → 次数 1 は既存 `apply_one_eq_one_of_subset_characterKernel_of_
  isMulCommutative_quotient` (InflationCharacter) で 4 行。(5.7) 配線 sorry-free。
- S13_MaximalIII_IV の実 sorry = `coherent_S_of_coherent_SH0C` ((11.3), 6.3-route) 1 点。
  次: S08_Theorem62_63_Standalone の `six_three_of_six_two_oracle` を
  (L,K,M,H,H₁) = (M,M',⊥,HC,H₀C)-trace で実体化 (hbound=(9.6)+(11.1), h56=dichotomy)。
  commit ca5f866b。

## 2026-07-05 lane-a (loop 23-25): **(11.3) 閉了** — S13_MaximalIII_IV bare sorry 0

- 6.3-route 完成: card_H0C/H0C_relIndex_HC/p_q_distinct_odd_primes/HC_isNilpotent
  → six_three_of_six_two_oracle 実体化 (h56 = exists_source_of_coherence_dichotomy)。
- §11 チェーン (11.3)/(11.4)/(11.5)/(11.6)/(5.7)-instance 全て S13 層実証明。
  残 upstream named: sixTwoDecompositionData (μ-column) / no_typeV_maximal (10.10) /
  S12 producer 層。S13 内残 = (11.7) H₀=1 (symplectic) + (11.8) 系。
- commits 53e4e59f / f91534f3 / (this)。

## 2026-07-05 lane-a (loop 26): sixTwoDecompositionData 骨格化

- irr×irr は S08 helpers で全放電。残 = μ-column 2 named
  (sixTwoDecompositionData_of_reducible_break / sixTwoMemberDatum_of_reducible_member)。
  材料: S12 muGrid + muGrid_column_sum_mem_sOf_H0_and_reducible + (5.8)。

## 2026-07-05 lane-a (loop 27): μ-column 分岐 attack plan (恒久 handoff)

**残 2 named** (S13_SixTwoBridge):
`sixTwoDecompositionData_of_reducible_break` / `sixTwoMemberDatum_of_reducible_member`。

### 中身の設計 (調査済)

対象 = `CharacterPsiDecomposition τ ψ (a•χ₁)` の構成 (S07_Coherence:1212):
fields = imageFamily R(ψ) (orthonormal, (ψ−ψ̄)^τ = Σ) / tau1 / lattice-relative
isometry (zSpan {χ−χ̄, χ−ψ}) / tau1_agrees / tau1_image ((χ−ψ)^τ₁ = X−Y) /
coeff (X ∈ ℤ[R]) / Y ⊥ R。

**可約 member/break φ の正体**: `muGrid_column_sum_mem_sOf_H0_and_reducible`
(S12_Section9Counts:171) — φ = Σ_i muGrid i k (列和)、φ(1) = q·u
(reducible_mem_sOf_H0_apply_one_eq_qu:143)。

**鍵材料**:
- `CharacterParameters.alpha i j = mu i j − δ•mu i 0 − n•zeta`
  (S12_Core:2793) with `alpha_support ⊆ A0` (S12_Core:3491) —
  これが列の (5.2.d) 差分データ = R(ψ)-像の素材。
- irr 版の構成体 `decompositionDaFromDadeOfDiff` /
  `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`
  (S08_SixTwoGeneral) の列和版を作る:
  (ψ − a•χ₁)^τ の R(χ₁)-係数分解を α-params の
  τ-像直交性で。member-D の extension 一致は (5.8)
  (extension uniqueness; hS₁coh.extension) — S07 の
  `IsCoherent.extension` API と `tau1_agrees`-clause。
- Coq 対応: PFsection11 の `redPmu`-まわり (cohS1 消費部)。

### 手順案 (次セッション)
1. S12_Core の CharacterParameters を bridge の Hypothesis から
   取得する経路確認 (mkSection11CharacterData:55 →
   toCertainTypeHypothesis 系; muGrid は hyp.muGrid hG hG.odd)。
2. 列和 ψ の (ψ − ψ̄) を α-params 差で表す補題 (両列 k, w2−k?
   ψ̄ = 列 −k ✓ conj-grid 対応 grep: muGrid_conj)。
3. imageFamily: dadeOrthonormalCharacterImageFamilyOfDiff の
   列和版 or 直接 OrthonormalCharacterImageFamily 構成。
4. member-D (可約 χ): D.tau1 χ = extension χ は列和の
   coherence-extension 値 = Σ extension(成分)-linearity。


### 追記 (loop 27 調査続き): 既存インフラは想定より進んでいる

- `Hypothesis.exists_conj_column` (S12_Core:5148): (Σ_i μ_ij).conj = Σ_i μ_ij'
  (j' ≠ 0, j) — ψ̄-列対応は既製。
- docstring 言及: `tau_muGrid_columnSum_diff` (k = j') が列の
  OrthonormalCharacterImageFamily の image_eq (τ(μ_j − μ̄_j) = Σ R(μ_j)) を供給
  = imageFamily-core は組み立て可能。
- muGridAlpha_inner_muColumn_(self_)sub_conj / …_tau_inner_… 系 (S12_Core:3722-4150)
  が R(ψ)-直交性計算の大半をカバー。
- 残り本体: CharacterPsiDecomposition の tau1 (lattice-relative isometry) を
  列和 ψ に対して与える部分 = (5.2) 的 τ₁-構成。irr 版
  `decompositionDaFromDadeOfDiff` の内部を読み、列版に一般化するのが次の実作業。

### 追記 2 (loop 28): columnImageFamily 既存 — 分岐は plumbing に帰着

- `Hypothesis.columnImageFamily` (S12_Core:5301) — 列 μ_j の bundled
  OrthonormalCharacterImageFamily (hyp.tau 版) が**完全既存**。
  R(μ_j) = {δω_ij^σ} ∪ {−δω_ij'^σ}; image_eq = exists_conj_column +
  tau_muGrid_columnSum_diff + columnRImage_sum。
- `decompositionDaFromDadeOfDiff` の本体 = `CharacterPsiDecomposition.ofProjection`
  (S07) は **generic** (imageFamily + lattice-isometry + agreement + ZIrr + 3 直交)。
- **残 plumbing**:
  (a) member-D (可約 χ, ψ-slot 0): ofProjection with columnImageFamily;
      tau1 := hS₁coh.extension 系 (irr 版 memberDatum_of_irreducible の内部と同型;
      extension_inner_eq で lattice-isometry)。
  (b) break-Da (可約 ψ): ofProjection with columnImageFamily (ψ, a•χ₁);
      直交 3 点は muGridAlpha_inner_* 系。
  (c) columnImageFamily の引数 (params : CharacterParameters hyp /
      coh : CoherentHypothesis hyp params / hmu / hos / hzS / hδ...) を
      sixTwo*-named の文脈 (hS₁coh のみ) からどう供給するかが本丸:
      (11.8)-consumer 側では mkSection11CharacterData / toCertainTypeHypothesis
      経由で構築済みのはず → その組を bridge の Hypothesis (S12.Hypothesis) から
      再構成する producer を先に確認 (grep CoherentHypothesis 構成子)。
      注意: tau_muGrid_columnSum_diff が coh を要求 — S₁-coherence でなく
      グローバル (10.2-10.5) パッケージ。sixTwoDecompositionData の呼び出し文脈
      ((11.4)/(11.3) 消費時) にそれが立つかの検証が次の第一手。

### 追記 3 (loop 29): ⚠ CoherentHypothesis = S 全体 coherence (10.4.b) — 供給不可の可能性

- `CoherentHypothesis hyp params` の唯一 field = `IsCoherent hyp.tau hyp.Sset hyp.A0`
  (S12_Core:2810) — **(10.8) S_not_coherent で否定される側の作業仮定**。
  sixTwo* の文脈 (S₁-coherence のみ、S-full は偽) では直接供給できない。
- 帰結: columnImageFamily / tau_muGrid_columnSum_diff の coh-依存が
  (a) 本質 (alignedOmegaSigmaGrid の σ-整列が τ₁=coh.extension 依存定義) か
  (b) 過剰要求 (Dade τ の supported-計算だけで済む) かの検証が次の第一手。
  (b) なら coh-free 版 tau_muGrid_columnSum_diff' を切り出して
  columnImageFamily を S₁-文脈に移植。(a) なら Peterfalvi (11.8) の
  τ₂ (S(C)−S(HC)-extension) 相当で σ-整列を再定義する必要 — (9.11)/(11.8)
  の subfamily-coherence 経由。Coq PFsection11 の cohS1-消費部
  (FTtype345_noncoherent 系) の該当行間を精読すること。
- いずれにせよ irr×irr-放電済み skeleton は不変; named 2 点の中身のみの問題。

### 追記 4 (loop 30): coh-依存の実質判定 — (10.2) 経由で本質的、ただし一般化の形が見えた

- 依存鎖: tau_muGrid_columnSum_diff → tau_muGrid_column_diff →
  `alpha_tau_image` (S12_Core:4856)。後者の結論自体が
  τ(α_ij) = δ(ω_ij^σ − ω_i0^σ) − n·**coh.tau1 ζ** ((10.2)) — τ₁ = ℤ[S]-extension
  で ζ・μ を通す導出。列差 (α_ij − α_ik) で ζ^{τ₁}-項は相殺 (だから
  columnSum_diff の式は ζ-free)。
- 一般化方針: alpha_tau_image を「S-full coherence」でなく
  「{関連 μ_ij 行, ζ} ⊇ を含む部分族 S' の coherence」でパラメタ化した
  coh'-版に切り出せるかが鍵。ただし sixTwoDecompositionData の S₁ は
  chain-任意で μ-成分を含む保証なし → **Peterfalvi (11.8) が可約 member を
  どう chain に通すかの行間** = Coq PFsection11 の該当部
  (cohS1 消費、redPmu/FTtype345 系, L216 以降) の精読が次セッション第一手。
- 現状整理: named 2 点の充足は「(10.2)-式の S₁-文脈版」一点に集約された。

### 追記 5 (loop 31): ★Coq 精読の結論 — 正しい設計 = FTtypeP_subcoherent 移植

- Coq `subcoherent S tau R` (PFsection5:486) = **coherence-free** の (5.2)-carrier:
  全 member ξ ∈ S (可約含む!) に R ξ ⊆ ℤ[irr G] orthonormal +
  **τ(ξ − ξ̄) = Σ_{α∈R ξ} α** + cross-直交 (e)。
- 供給元 = `FTtypeP_subcoherent` (PFsection9:1506 域, cyclicTI-σ 経由) —
  **coherence 不要**。部分族へは `subset_subcoherent` で制限
  (PFsection11: scohS1/scohS2/scohM'' 全部これ)。
- repo 検証: `alignedOmegaSigmaGrid` (S12_Core:1293) は §6 host
  (toCertainTypeHypothesis = cyclicTI) 由来で **coherence-free** ✓。
  coh-依存は alpha_tau_image ((10.2)-式) の導出経路だけ。
- **次セッションの方針**: FTtypeP_subcoherent-analog を repo に建てる:
  τ(μ_j − μ̄_j) = δ(Σω_j^σ − Σω_j'^σ) を **coh-free** で直接証明
  (列差は A0-supported (同次数) → Dade-supported-計算 + cyclicTI-σ 同定;
  PFsection9 の FTtypeP_subcoherent 証明の該当部を行間ソースに)。
  それで columnImageFamily の coh-free 版が立ち、named 2 点は
  ofProjection-plumbing に落ちる。alpha_tau_image 経由は捨てる。

### 追記 6 (loop 32): coh-free 直接証明の部品所在 (§6 layer)

- `S06_CertainTypeIsometry`: `certainTypeOmegaSigma` (σ-像 def, coh-free) +
  `tau_toDadeMap_apply_of_mem` (:378) + `tau_toDadeMap_sum` (:767) +
  `certainTypeOmegaSigma_inner` — §6 Dade-τ の supported-値計算 API 一式。
- `S06_MuColumnBridge.induce_omegaColumnDiff_mu_diff` ((4.3.b)):
  Ind_W^L(ω_ij − ω_0j) = δ_j(μ_ij − μ_0j) — 誘導側恒等式。
- **次の第一手 (実作業)**: これらで
  `tau_muGrid_row_diff_cohFree : hyp.tau (μ_ij − μ_ik) = δ·(ω_ij^σ − ω_ik^σ)`
  (j,k ≠ 0, 同 i 行) を S12 側に直接証明する
  (support = alpha_support の差 / τ-値 = tau_toDadeMap_apply_of_mem を
  muGrid-def (toCertainTypeHypothesis 経由) に沿って評価)。
  成功すれば columnSum_diff の coh-free 版 → columnImageFamily' → named 2 点。
  PFsection9 FTtypeP_subcoherent の該当証明部を並走参照。

### 追記 7 (loop 32 続): ★★ (4.8)(3) は §6 で coh-free 完全証明済み

- `certainType_diff_dade_eq` (S06_CertainTypeIsometry:643):
  **(μ_ij − μ_ik)^τ = δ_j·(ω_ij^σ − ω_ik^σ) — 証明済・coherence 不要**
  (σ-係数 grid の (3.7)/(3.8) trichotomy で ψ=0; host h.tau.toDadeMap 版)。
- よって残 plumbing の核心 = **host τ ↔ hyp.tau の橋**:
  hyp.muGrid/alignedOmegaSigmaGrid は toCertainTypeHypothesis-host で定義済 →
  certainType_diff_dade_eq を hyp.tau 版
  `tau_muGrid_row_diff_cohFree` に翻訳する agreement lemma
  (h.tau.toDadeMap vs dadeIntegralCharacterMap hyp.dadeData — 既存の
  agreement を grep: tau_muGrid_columnSum_diff の証明が結局
  何で host-τ を hyp.tau に接続していたかを alpha_tau_image 内部で確認)。
- その後: 列和へ Finset.sum (既存 columnSum_diff の骨格流用) →
  columnImageFamily の coh-free 版 → ofProjection → named 2 点閉。

### 追記 8 (loop 33): 橋は不要 — tau_muGridAlpha_eq の証明形を ζ-free で mirror する

- `tau_muGridAlpha_eq` (S12_Core:4789) の証明は §6-host 橋を使わず
  **hyp.tau-level で (4.8)-型論法を再演**している:
  ‖X‖²=2 + X ∈ ℤIrr + V-vanish + σ-係数 grid (3.7)/(3.8) trichotomy
  (部品: muGridAlpha_tau_X_inner / exists_alignedOmegaSigmaGrid_chiFam_family /
  typePData_toTICyclicHypothesis / canonicalFullDadeApp / tau1_zeta_vanishes…)。
  coh は −n·ζ^{τ₁} 項の処理にだけ入る。
- **確定レシピ**: `tau_muGrid_row_diff_cohFree (i) (hj0) (hk0) (hjk) :
  hyp.tau (μ_ij − μ_ik) = δ • (ω^σ_ij − ω^σ_ik)` を同じ骨格で ζ-free に書く:
  * 支持: α_ij − α_ik = μ_ij − μ_ik (alpha_def; ζ 消滅) → alpha_support 差
  * ‖μ_ij − μ_ik‖² = 2: grid 成分は既約・相異 (muGrid 直交補題群) →
    Dade 等長で τ-像も norm 2、ℤIrr ✓
  * V-vanish: (4.8) step (4) 型 — ω^σ 側は certainTypeOmegaSigma_apply_of_mem_V
    の aligned-版 (exists_alignedOmegaSigmaGrid_chiFam_family + chiFam-V-値)
  * trichotomy 部は tau_muGridAlpha_eq の該当ブロックをそのまま流用
    (ζ-項が無い分単純化)
- そこから列和 (Finset.sum) → coh-free columnImageFamily → ofProjection →
  named 2 点。全行程が既存部品の組替えで閉じる見込み。

### 追記 9 (loop 34): 実装直前 — 全部品 coh-free 確認済み、組み立てレシピ最終形

`tau_muGrid_row_diff_cohFree` の材料 (全て存在・coh-free):
- V-値 leg: `tau_muGridAlpha_apply_eq_on_typePV` (S12_Core:~4600 手前, coh 無し!) —
  行差では leg_j − leg_k で ζ^τ₁-値も相殺 → hψV。
- norm-2: muGrid_inner_self / muGrid_inner_cross_column (2095/2125) →
  ⟨μdiff, μdiff⟩ = 2 → Dade 等長 (supported: params.alpha_support の差 +
  alpha_def で μ_ij − μ_ik = α_ij − α_ik) → ⟨X,X⟩ = 2。
- ZIrr: dadeIntegralCharacterMap_mem_ZIrr_of_supported (S07)。
- engine: `eq_smul_chiFam_diff_of_vanishOnV` (S05_SigmaTrichotomy:153) via
  tic := typePData_toTICyclicHypothesis + app := canonicalFullDadeApp +
  P := exists_alignedOmegaSigmaGrid_chiFam_family (行 i 固定; P j ≠ P k)。
- 署名案: (hG) (hyp) (hodd) (params) (hmu : params.mu = muGrid)
  (hδpm) (hδj) (i) (hj0 hk0 hjk) : hyp.tau (μ_ij − μ_ik)
  = (params.delta:ℂ) • (ω^σ_ij − ω^σ_ik)。
- 完了後: Finset.sum で列和 → columnImageFamily の coh-free 版
  (image_eq を新恒等式+exists_conj_column で) → named 2 点 =
  ofProjection + hS₁coh.extension (member-D) / muGridAlpha_inner 系 (直交)。

## 2026-07-05 lane-a (loop 35): ★tau_muGrid_row_diff 実証明 — coh-free 要石完成

- (μ_ij − μ_ik)^τ = δ(ω^σ_ij − ω^σ_ik) を CoherentHypothesis なしで閉了。
  レシピ通り (追記 9)。次 = 列和版 (Finset.sum) → coh-free columnImageFamily
  → sixTwoDecompositionData named 2 点の plumbing。

## 2026-07-05 lane-a (loop 36): coh-free 列インフラ完成

- tau_muGrid_columnSum_diff_cohFree + columnImageFamilyCohFree 閉。
  残 = named 2 点の ofProjection plumbing (追記 8-9 のレシピ後半)。

### 追記 10 (loop 37): plumbing の threading 設計 (確定)

- **S13.Hypothesis は `params : CharacterParameters base` field を既に持つ** (S13:111)。
  ただし pin (params.mu = muGrid 等) が無い。muGrid は (hG hodd)-引数依存だが
  IsMinimalSimpleOdd/Odd は Prop → proof-irrelevant → ∀-量化 field で pin 可能:
  `params_mu_eq : ∀ hG hodd, params.mu = base.muGrid hG hodd` /
  `params_delta_sign : ∀ hG hodd j ≠ 0, base.muColumnSign hG hodd j = params.delta` /
  (hzS/hz1 は params.zeta_mem/zeta_degree 系 field が既にあるか確認)。
  S13.Hypothesis は constructor 未作成 (要再確認: grep mk/toS13) なら field 追加安全。
- **署名 threading**: sixTwoDecompositionData と exists_source_of_coherence_dichotomy
  (S13_SixTwoBridge, S12-hyp-level) に (params) (pins...) 引数を追加 →
  S13-消費点 (exists_source_index_le_two_psi_of_ne_top 経由 (11.4)/(11.3)) で
  hyp.params + 新 pin-fields から供給。
- その上で named 2 点の本体: ψ-可約 → ψ = Σ_i muGrid i k (要: 可約 member の
  列同定 lemma — sOf-membership から k の存在; S12_Section9Counts 331/395/428 の
  params-引数付き補題群が材料) → columnImageFamilyCohFree → ofProjection
  (tau1 := hS₁coh.extension-系, lattice-isometry = extension_inner_eq) +
  直交 3 点 (muGridAlpha_inner_muColumn_* 系)。

## 2026-07-05 lane-a (loop 38): params threading 完了

- bridge 5 署名 + S13 消費 2 点に params+pins 貫通 (build green)。
- named 2 点の本体着手条件が整った: 分岐内で params/hmu/hδj/hδpm/hzS/hz1 が
  手元にある。次 = ψ-可約の列同定 → columnImageFamilyCohFree → ofProjection。

### 追記 11 (loop 39): (9.8) 分類の抽出目標を特定

- `muGrid_column_sum_mem_sOf_H0_and_reducible` (S12_Section9Counts:171) の証明**内部**に
  「{S(H₀) の可約 member} の ncard = w₂−1」+ 列和 w₂−1 本の単射性 + ⊆ が既在
  (Set.eq_of_subset_of_ncard_le で集合相等)。
- **次の実作業**: この内部ステップを public に抽出:
  `theorem reducible_mem_sOf_H0_eq_muGrid_columnSum (hred : ¬IsIrr φ)
   (hφ : φ ∈ sOf … H0) : ∃ k ≠ 0, φ = ∑ i, muGrid i k`。
  さらに bridge-family 側 (inducedKernelFamily K B の可約 member) から
  sOf-H₀-membership への還元 (可約 Ind θ は自動的に S(H₀)-member —
  (9.8.a); 要確認/形式化) を挟んで named 2 点の ψ-列同定が完了する。

## 2026-07-05 lane-a (loop 40): (9.8) 分類 public 抽出完了

- reducible_mem_sOf_H0_eq_muGrid_columnSum 閉 (build green)。
  ψ-列同定の主部品完成。残 = family-bridge (inducedKernelFamily ↔ sOf) +
  ofProjection 組み立て。

### 追記 12 (loop 42): ★家族整合の解析 — U-side 可約は Frobenius-FPF で不可能

- 事実確認 (Coq): repo `inducedKernelFamily` = Coq `S_ X = seqIndD HU M HU X`
  (noncontainment = θ≠1) ✓ 健全。textbook-𝒳 (H ⊄ ker) = Coq `calS`
  (M`_\s-slot) は別物で、S_ ⊋ calS (H ⊆ ker θ の U-side member を含む)。
- (9.8)-列分類は sOf (𝒳-form) 側で証明済 → bridge-family の可約 ψ に適用する
  には「可約 → H ⊄ ker θ」が必要。
- **鍵**: U-side (H ⊆ ker θ) の可約 = θ が M-invariant (inertia_eq_top_of_
  induceHU_not_irreducible :5021) → θ̄ ∈ Irr(Ū) が W₁-固定・非自明。
  だが U⋊W₁ は Frobenius (typeP_uW1_frobenius) → W₁ は U# に FPF →
  Brauer permutation で Irr(U)∖{1} にも固定点なし → 矛盾。
  ∴ **可約 member は自動的に H ⊄ ker** → sOf-transport → 列分類 OK。
- 次の実装: `inducedKernelFamily_reducible_H_not_le_ker` (Brauer-FPF;
  部品: BrauerPermutationUnconditional + typeP_uW1_frobenius +
  inertia_eq_top…) → sOf-⊥-transport lemma → ψ-同定完成 →
  ofProjection 組み立て (columnImageFamilyCohFree)。

## 2026-07-05 lane-a (loop 43): bridge-family 直接分類 閉 — ψ-列同定完成

- reducible_mem_inducedKernelFamily_eq_muGrid_columnSum (θ≠1 で trivial-列排除、
  𝒳-条件・Brauer-FPF・sOf-transport 全て不要の最短路)。
- 残 = named 2 点の ofProjection 最終組み立て (columnImageFamilyCohFree +
  hS₁coh.extension-τ₁ + muGridAlpha_inner_* 直交)。

### 追記 13 (loop 44): break-Da の ofProjection invocation recipe (完全形)

`sixTwoDecompositionData_of_reducible_break` の Da-半分 (実装可能形):

1. `obtain ⟨k, hk0, rfl⟩ := hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum
   hG htype hnt chief hψB hψred` — ※ htype/hnt/chief を named-sorry 署名に追加要
   (S13-消費側: hyp.type_alt-isTypeIIIorIV / typePNontrivialCore_of / hyp.chief +
   setup_typeP_eq-transport — S13.Hypothesis の chief は s11Setup-上; bridge は
   toTypesIIIIIIVSetup htype hnt-上 → ChiefFactorData の transport が一点残る。
   代替: named-sorry に (chief : ChiefFactorData (toTypesIIIIIIVSetup htype hnt))
   を引数追加し S13 側で構築供給)。
2. ψ̄-列: `obtain ⟨k', hk'0, hk'k, hconj⟩ := hyp.exists_conj_column hG hG.odd hk0`。
3. `Da := OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
   (hyp.columnImageFamilyCohFree hG hmu hzS hz1 hzconj?? — hzconj 引数残存注意
   (cohFree 版に hzconj が残っているか確認; 残っていれば pin 追加 or 除去)
   hδpm hδj hk0 hk'0 hk'k.symm?? (hjj' : j≠j') hconj)
   hyp.tau (dade-preserve) rfl (ZIrr) ⟨3 inners⟩` — 各 obligation:
   - htau1_inner_eq: S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
     (set = {ψ−ψ̄, ψ−a•χ₁}; supports: 前者 = 列差 (classification 後は
     inducedKernelFamily_conjDiff_support or α-support-差), 後者 =
     S08.inducedKernelFamily_scaledDiff_support (hKsupp = mderivSharp_subset_A0))
   - htau1_agrees: rfl (tau1 := hyp.tau)
   - htau1_mem: dadeIntegralCharacterMap_mem_ZIrr_of_supported + (列和∈ZIrr:
     sum of muGrid-irr; χ₁: S08.inducedKernelFamily_mem_ZIrr)
   - 3 inners: S08.inducedKernelFamily_pairwise_orthogonal (ψ,χ₁ 相異: ψ∉S₁∋χ₁;
     ψ,ψ̄ 相異: hasNoReal or 列≠) + smul-線形。
   - τ-型合わせ: hyp.tau vs dadeIntegral-式 = def-rfl (have := rfl-conversion)。
4. member-∀-clause: χ irr → 新 narrower named `sixTwoMemberDatum_vs_columnDa`
   (D := memberDatum-machinery; Orthogonal via
   orthogonal_of_signedDifference_inner_eq_zero (S07:674) — source-inner:
   family-pairwise-orthogonal の 4-cross); χ reducible → χ も列 → 列-列直交
   (columnRImage_inner の cross-列版 or muGridAlpha_inner_muColumn 系)。

member-clause の Orthogonal-def 階層 (OrthonormalCharacterImageFamily.Orthogonal
vs CharacterDifferenceImage.Orthogonal) の突合が実装時の最初の確認点。

## 2026-07-05 lane-a (loop 46): ★break-Da 実構成完了

- ofProjection 組み立て成功 (全 obligation family-level 放電 — 追記 13 recipe 通り、
  ただし支持は α-計算不要で scaledDiff_support に一本化できた)。
- 残 sorry = member-∀-clause (可約 break の Da に対する各 χ ∈ S₁ の D):
  irr-χ は memberDatum-machinery + R(χ)⊥R(列) (源 4-cross 直交 → signedDifference
  経由); 可約-χ は列-列。+ sixTwoMemberDatum_of_reducible_member (対 irr-break)。

### 追記 14 (loop 47): ⚠ member-clause の無条件直交は過強 (要 statement 修正)

- Coq (5.2.e): `orthogonal phi (xi::xi^*) -> orthogonal (R phi) (R xi)` —
  **条件付き** (4-cross 直交が前提)。
- 現 sixTwoDecompositionData の member-∀-clause は ∀χ∈S₁ 無条件で
  D.imageFamily ⊥ Da.imageFamily を要求。だが χ = μ_i₀k (ψ-列の既約成分)
  ∈ S₁ の場合 ⟨χ, ψ⟩ = 1 ≠ 0 で、R(χ) と R(列) は ω^σ_i₀k-成分を共有し
  直交は**偽**になり得る → 現形の named-sorry は充足不能の疑い。
- **次の第一手**: exists_source_index_le_two_psi (bridge の
  fully-pinned producer) の証明内で hdatum の D-直交がどう消費されるか
  精査 → (a) 条件付き (⟨χ,ψ⟩=0 ∧ ⟨χ,ψ̄⟩=0 前提) に obligation を
  弱める statement 修正 (エンジン側が当該 χ にしか使わないはず;
  S08 の重み付き (5.6) Gram-計算部を確認) or (b) エンジン再導出。
  irr-irr 放電 (…orthogonal_breakDa_of_irr_irr) は無条件で通っていた —
  そこでは ψ 既約で χ,ψ 相異なら family-pairwise が 4-cross を自動供給
  していた (列 ψ では成分-重なりが破る)。修正は可約-break 分岐にのみ影響。
- break-Da 構成 (loop 46) 自体は影響なし (Da-半分は健全)。

### 追記 15 (loop 48): ✓ 追記 14 の懸念は解消 — 無条件 obligation は健全、証明形確定

- **反例は成立しない**: χ ∈ S₁ は族 member (Ind-form)。μ_ik-entry は可約 Ind の
  既約成分であって族 member ではない。さらに次数で χ ≠ μ_ik が強制される:
  irr-member 次数 = q·θ(1) ≡ 0 (mod q) vs d ≡ 1 (mod q)
  (charParam_d_modEq_one) → 相異既約 → ⟨χ, μ_ik⟩ = 0 (全 i,k)。
  よって (5.2.e)-前提 (4-cross) は文脈内で常に成立 → 無条件 member-clause 健全。
- **per-pair R(χ)-elt ⊥ ω^σ_ik の証明形 (pigeonhole)**:
  1. ⟨τ(χ−χ̄), τ(μ_ik − μ_ik')⟩ = ⟨χ−χ̄, μ_ik − μ_ik'⟩ = 0
     (両 supported + dade-preserve; 源は上記 per-entry 直交)。
  2. τ(rowdiff) = δ(ω_ik − ω_ik') (tau_muGrid_row_diff!)。
  3. R(χ) の底既約は 2 個; ω_ik が共有されると仮定 → 各 k'≠k で
     ⟨…⟩=0 から ω_ik' も共有 → w₂−1 ≥ 2 個の相異 ω を 2-成分が
     カバー不能 (w₂ ≥ 3) → 矛盾 → 共有なし → ⟨α, ω^σ_ik⟩ = 0 ✓。
- 実装順: (i) per-entry ⟨χ, μ_ik⟩ = 0 lemma (次数 mod q);
  (ii) pigeonhole per-pair lemma; (iii) member-D 組み立て
  (memberDatum_of_irreducible + Orthogonal-per-pair) — 可約-χ は
  列-列 cross (muGrid_inner_cross_column 直接)。

### 追記 16 (loop 51): (ii) の正道 = trichotomy 直接適用 (Bessel-3 は p=3 で不足)

- 追記 15 の pigeonhole は **p = 3 で破綻** (非零列 2 本しかなく 3-等係数が組めない)。
  Bessel-3 補題 (inner_eq_zero_of_three_equal_coeff) は残すが (ii) には使わない。
- **正道**: T := τ(χ−χ̄) は V 上消える (χ は M'-誘導 → χdiff|_V = 0
  (V ∩ M' = ∅: V-元は mod M' で W₁-非自明像) + τ の A0-値保存
  (V ⊆ typePA0)) → S05 σ-係数 grid (3.7)-分離 + ‖T‖² = 2 +
  (3.8) trichotomy (w₁, w₂ ≥ 3 で constant-row/column とも norm > 2 ✗)
  → **全 σ-係数 0** = T ⊥ 全 ω^σ_ik ✓ (p = 3 安全)。
- 実装: S06:643 `certainType_diff_dade_eq` の endgame ブロック
  (grid_trichotomy + grid_no_constant_column 両向き +
  certainType_diff_dade_eq_of_all_sigmaCoeff_zero:556) を
  「X vanish-on-V + ⟨X,X⟩ = 2 → ∀ P, ⟨X, chiFam P⟩ = 0」形の
  reusable lemma に S05/S12 レベルで切り出し、T に適用。
  V-vanish の部品: tau_toDadeMap_apply_of_mem (S06:378) の
  hyp.tau-版 (dade-値保存) + typePV ∩ M' = ∅
  (typePData_typePV_not_mem_derived — S12-Core に既出 (10.5)-ζ-vanish
  の部品として言及あり)。

## 2026-07-05 lane-a (loop 52): sigmaCoeff_eq_zero_of_vanishOnV 閉 (S05 engine)

- (ii) 核心: norm-2 V-消滅 → 全 σ-係数 0 (NC≤2 既存補題 + trichotomy 両向き)。
- 残: T := τ(χ−χ̄) 文脈適用 (V-vanish 供給) → ⟨T, ω^σ⟩ = 0 → R(χ)⊥R(列)
  (constituent 引数は per-pair: R-elt = ±X±-部分の直交は… ⟨T,ω⟩=0 から
  ofDiff-R-elts の ω-成分 0 を出す小 step 要確認) → member-D 組立。

### 追記 17 (loop 53): member-clause 全部品既存確認 — 残りは純組み立て

- `tau_zeta_sub_conj_vanishes_on_typePV` (S12:4613) は **ζ 専用でなく任意
  inducedFamily-irr member で成立する形で既に証明済** → T := τ(χ−χ̄) の
  V-消滅は即 cite。
- `inner_left_eq_zero_of_inner_sub_eq_zero` (S12:4637) = per-part 射影補題
  (a−b ⊥ s, 各 norm-1 → a ⊥ s) — 追記 15 の constituent-懸念を直接解決。
- 組み立て (次 iteration):
  A. `tau_chidiff_inner_alignedOmega_eq_zero`: T-vanish (上記) + T∈ℤIrr +
     ⟨T,T⟩=2 (χ irr-nonreal family-pairwise) → loop-52 engine
     (sigmaCoeff_eq_zero_of_vanishOnV, tic := typePData_toTICyclicHypothesis,
     app := canonicalFullDadeApp) → ∀pq sigmaCoeff = 0 → P-enum
     (exists_alignedOmegaSigmaGrid_chiFam_family) で ⟨T, ω^σ_ik⟩ = 0。
     (sigmaCoeff pq 定義 = ⟨·, chiFam pq⟩ の突合のみ注意)
  B. per-pair: D-R-elt (OfDiff ±部分, a−b = T) + 射影補題 + ⟨T,ω⟩=0
     → ⟨R-elt, ω⟩ = 0 → ±δ-smul で columnRImage-elt へ。
  C. sixTwoMemberDatum_of_reducible_member / break の member-∀ とも:
     D := memberDatum_of_irreducible (tau1-ext ✓) + B の Orthogonal;
     可約-χ は D := (列-Da-mirror, ψ-slot 0) + 列-列直交
     (alignedOmegaSigmaGrid_inner の cross)。

## 2026-07-05 lane-a (loop 54): (A) 閉 — ⟨χdiff^τ, ω^σ⟩ = 0 (一般既約 member)

- 全部品既存の組み立てで一発 (inner_self のみ inline)。
- 残: (B) inner_left_eq_zero_of_inner_sub_eq_zero で
  OfDiff-R-elt ⊥ ω^σ → columnRImage-elt (±δ-smul) →
  (C) member-D (irr: memberDatum_of_irreducible + B;
  可約: 列-列 = alignedOmegaSigmaGrid_inner cross)。

## 2026-07-05 lane-a (loop 55): (B) 閉 — R-element 単位の直交確立

- elt_inner_eq_zero (β := T−α 補部構成 + 射影補題)。(A)+(B) で
  ⟨D-R-elt, ω^σ⟩ = 0 完成。残 = (C): columnRImage-elt = ±δ•ω への
  smul-変換 + Orthogonal-def 束ね + memberDatum_of_irreducible 接続 +
  可約-χ 側 (列-列)。

## 2026-07-05 lane-a (loop 56): 可約 member-D 実構成 (2 micro-goal 残し)

- ofProjection + extension-τ₁ 組み立て成功。park 2 点:
  (1) Orthogonal: per-pair = columnRImage 分解 (Finset.mem_image, ±δ•ω 2-case)
      → inner-smul → conj_symm → (B) elt_inner_eq_zero (R := breakDa.1.imageFamily,
      hT2 = hψT2 (証明済 in-context!), hTs = (A) tau_chidiff_inner_alignedOmega
      (hψind hψirr, 各 (i,kχ/kχ')), s-facts = alignedOmegaSigmaGrid_inner self +
      mem_ZIrr)。
  (2) tau1-rfl: `hS₁coh✝` 二重 fvar 現象 — rw-flow 後も残存。fresh 診断:
      (a) 単独最小再現 (b) ofProjection_tau1 @[simp] 補題新設で rw-close 試行
      (c) statement 側の hS₁coh-依存 ∃ を Da-引数化する再定式化。

### 追記 18 (loop 57): member-D Orthogonal 閉 — 残 = tau1-rfl fvar 謎 1 点

- Orthogonal per-pair 実証明完了 ((A)+(B) 通り)。
- tau1-rfl: goal の hS₁coh✝ は rename_i で確認した同型 IsCoherent の別 fvar。
  set-ext fold でも解消せず (goal 側 fvar が現 hS₁coh でない)。
  fresh 診断案: (i) 各 tactic 直後に goal-fvar を probe して二重化点を特定
  (rw-at-hyps の revert 連鎖 or set の abstraction が疑い);
  (ii) 回避: 証明冒頭で `obtain ⟨ne, ext, hie, hos, hmz⟩ := hS₁coh` と
  即分解し ext-fvar 単独で全構成 (IsCoherent を早期に開けば以後の
  依存が単純 fvar になり fold 齟齬が消えるはず) — 有望。

## 2026-07-05 lane-a (loop 58): ★named 片方完全閉 — member_of_reducible_member sorry-free

- tau1-rfl は hS₁coh 冒頭分解で解決 (Lean 教訓を commit message に記録)。
- 残 = sixTwoDecompositionData_of_reducible_break 内の member-∀ 1 sorry:
  irr-χ: memberDatum_of_irreducible + 直交-vs-列 ((A)-for-χ + (B)-on-D(χ)-family
  で ⟨D-elt, ω⟩=0 → ±δ-smul); 可約-χ: 今回の構成の写し + 列-列直交
  (kχ ≠ kψ from χ≠ψ; aligned-inner cross)。全部品 in-context。

## 2026-07-05 lane-a (loop 59): ★★(5.2.d) 完結 — sixTwoDecompositionData 全象限実証明

- break 定理の member-∀ 節 (最後の sorry) を一発 green で閉鎖 (commit 1732c7c2):
  - irr-χ: memberDatum_of_irreducible → D + tau1-clause; 直交は (B) elt_inner_eq_zero
    (R := D.imageFamily) + (A) tau_chidiff_inner_alignedOmega_eq_zero + hT2 (χ 版 norm-2)。
    β = ±δ•ω は inner_smul_right (star 込みで c 一括) — neg_smul 分解不要。
  - 可約-χ: loop 58 構成の写し (hS₁coh 分解→subst hχcol→列 family ofProjection→rfl)。
    列-列直交: {kχ, kχ'} vs {k, k'} の 4 不一致は S₁ 帰属で導出
    (kχ≠k: χ∈S₁ vs ψ∉S₁ / kχ≠k': ψ̄∉S₁ / kχ'≠k, kχ'≠k': conj-closure)。
    per-pair は inner_smul_left + inner_smul_right + alignedOmegaSigmaGrid_inner if_neg。
- **S13_SixTwoBridge.lean = sorry 0**。assembly sixTwoDecompositionData は
  irr×irr (S08 general) / irr-break×red-member (loop 58) / red-break×全 member (今回)
  の全象限実証明で完結。issue 2022 の h56/(5.2.d) grid obligation 閉。
- 残る §11-チェーン上流: S13_CoreStructure の (11.7) H_elementaryAbelian +
  (11.8) block (orthogonality_setup / not_orthogonal_mu0_sub_zeta)。

## 2026-07-05 lane-a (loop 60): (11.7) 着手 — case-(b) parity kernel 完成 (issue 9012)

- (11.7) 調査: 教科書 = 交代形式 2 分岐; Coq FTtype34_Fcore_kernel_trivial = 純群論再構成
  (D = Q-coset commutator; Galois case は extraspecial + odd |Hhat| 矛盾)。
- mathlib に交代形式偶数次元定理なし → 指標 route 採用: repo 既存の
  sq_finrank_eq_card_quotient_center (Gor 5.5.5, class-2 一般) + 新設 faithful-存在で
  「class-2, |Z|=p, |P|=p^{q+1} → q 偶」を実証明 (ClassTwoSquareIndex.lean, commit 12aca9b8)。
- (9.7) 部品確認済み: chiefFactor_clifford_U_dichotomy (U-既約 ∨ S₀ 位数 p)、
  CliffordCaseAData (Hpart ⊕分解 + orbitRep + iSupIndep) が S11 に実在。
- 残 = S13 側 frame: Q ◁ H (index p in H₀) 構成 → Khat = H/Q class-2 化 →
  case (b): Z(Khat) = H0hat (U-既約性) → kernel 適用; case (a): φ_w 指標の w-鎖論法。

## 2026-07-05 lane-a (loop 61): (11.7) frame 3 補題 (S13_ElementaryAbelianKernel 新設)

- [K,N] < N (nilpotent) / index-p normal Q ([BG] 1.22 相当) / K/Q class-2 構造
  (N̂ 位数 p = Ĥ' ≤ Z(Ĥ)) を S11 generic level で sorry-free 化。
- 発見: N̂ の中心性は [K,N] ≤ Q から直接出る (Coq の meet-center 論法・p-群性不要)。
- 残: case (b) = Z(Ĥ) = N̂ の U-invariance 転送 (typeP_quotientCoprimeAction の
  φ.comp U.subtype 形; Q は U-pointwise-fixed ゆえ U-invariant) → parity kernel;
  case (a) = φ_w 鎖。両 case とも hUcent (U centralizes H₀, S13 側 U_centralizes_H0)
  を入力仮定に取る generic 形で書く。

## 2026-07-05 lane-a (loop 62): (11.7) case (b) 完全閉鎖 — chiefKernel_caseB_false

- U-既約分岐を generic (data, chief) level で sorry-free 化 (commit 参照)。
- 技術メモ: IsAInvariant の • は change で map 化 (quotientMulAutHom の def と同型);
  pointwise-smul の hom-algebra rw は toMonoidEnd 形に阻まれる → 要素ベース le_antisymm が正解。
  π-同変性は QuotientGroup.induction_on + rfl (apply lemma が rfl なので)。
- 残: case (a) φ_w-鎖 (CliffordCaseAData ではなく raw S₀ dichotomy 分岐から直接;
  W₁-orbit 生成 + LineScalarCharacter 系で φ_w 構成) → master → S13 instantiation。

## 2026-07-05 lane-a (loop 63): (11.7) case (a) 道具箱 6 補題 (commit b52ca1f8)

- class-2 交換子計算 (中心 drop ×2 / 積展開 / 冪双線形 ×2) + order-p exponent +
  closure 可換性を kernel file に sorry-free 追加。
- case (a) 本体の設計確定: S₀-exponent 関数 e : U → ℕ (mod p) に全 translate の作用が
  e(a⁻¹ua) で還元される (T_a = φa•S₀ 上の u-exponent = e(a⁻¹ua))。D ≠ 1 の pair (a,b) から
  e(v)·e(c⁻¹vc) ≡ 1 (c := a⁻¹b) → v ↦ c-conj 置換の鎖 + c 奇数位数 (c ∈ ⟨c²⟩) で
  e ≡ e∘conj → e² ≡ 1 → e ≡ 1 (odd) → U が全 translate を固定 → fixedSubgroup = ⊤ ↯
  U_noncentral_on_quotient。D 全消滅側は commute_all_of_closure_eq_top で Ĥ 可換 ↯ |Ĥ'| = p。
- 次 iteration: この設計で chiefKernel_caseA_false を実装。

## 2026-07-05 lane-a (loop 64): (11.7) case (a) endgame 補題 (caseA_fixed_contradiction)

- 「U が S₀ pointwise 固定 → False」を実証明 (translate へは conj-返しで伝播、
  span = ⊤、(9.4.b) と矛盾)。
- 残り = chain 部: 非可換 pair (x̂,ŷ) ∈ S_gen² → c := ⁅x̂,ŷ⁆ ∈ N̂ order p →
  σu-固定 + 双線形性で ē₀(a⁻¹ua)·ē₀(b⁻¹ub) = 1 → c-conj 鎖 (奇数位数) → ē₀ ≡ 1 → hfix。
  + S_gen closure = ⊤ (π-lift 帰納) + hDall dichotomy + Ĥ frame 再利用の main 組立。

## 2026-07-05 lane-a (loop 65): (11.7) chain 算術 + closure 引き戻し (commit 129e7536)

- chain_exponent_eq_one (f∘σ 反転 → σ 奇数冪で f²≡1 → d 奇数で x = (x²)^k·x = 1) と
  closure_preimage_eq_top_of_closure_eq_top を sorry-free 化。
- main 組立の設計メモ (次 iteration):
  1. Ĥ frame (case b と同じ Q/N̂/π/σ/hπσ) を再構築
  2. S_gen := π ⁻¹' (⋃ a, ↑(φa • S₀)); 1 ∈ ⋃ (S₀ ∋ 1); closure = ⊤ (span → closure union =
     iSup: Subgroup.iSup_eq_closure or closure_iUnion_coe + 引き戻し補題)
  3. by_cases 全 pair Commute → commute_all → Ĥ 可換 ↯ |Ĥ'| = p
  4. else: pair x̂ ŷ (π x̂ ∈ φa•S₀, π ŷ ∈ φb•S₀), c := ⁅x̂,ŷ⁆ ≠ 1 ∈ N̂ 中心, orderOf c = p
  5. e₀ choice (exists_pow_eq_of_mapsTo_of_card_prime on S₀; hS₀inv smul_mem);
     transfer: σu x̂ = x̂^{e₀(a⁻¹ua)}·ẑ (π-同変 + ker π = N̂ 中心) → 双線形で
     c = c^{e₀(a⁻¹ua)·e₀(b⁻¹ub)} → ZMod p 等式 ē₀(a⁻¹ua)·ē₀(b⁻¹ub) = 1
  6. f v := ē₀(⟨a⁻¹va⟩)?? — 実際は g := fun v : ↥Usub => ē₀(conjA v) で hrel:
     v ↦ a v a⁻¹ 代入で f v · f (σ_c v) = 1 (σ_c = conj by c := a⁻¹b in MulAut ↥Usub;
     m := orderOf... |L| 奇数冪); chain_exponent_eq_one → ē₀∘conjA ≡ 1 → ē₀ ≡ 1
     (conjA 全単射) → hfix (s^{e₀v} = s from ≡1 + order p) → caseA_fixed_contradiction。
  - f の乗法性: s₀ 生成元 + pow_eq_pow_iff_modEq + ZMod.natCast_eq (mod p 抽出)。


## 2026-07-05 lane-a (loop 66): exponent bundle (exists_exponent_fun_of_card_prime)

- (i) p∤e (ii) 冪表示 (iii) mod-p 乗法性 (iv) ≡1→固定 を 1 補題に束ねた (commit 参照)。
- main 組立に必要な部品はこれで全て: frame (loop 61-62 流用) / S_gen closure (loop 65) /
  exponent bundle (今回) / chain (loop 65) / endgame (loop 64) / 双線形 (loop 63)。
- 次 iteration = chiefKernel_caseA_false 本体 (設計は loop 65 ログの 6 ステップ)。

## 2026-07-05 lane-a (loop 67): full build 検証 + main 組立 handoff

Full build 3928 jobs green (2m11s)。(11.7) の残作業 = 以下の 2 定理のみ:

### A. chiefKernel_caseA_false (S13_ElementaryAbelianKernel.lean, CaseA section 内に追加)

署名 = chiefKernel_caseB_false と同型だが hirr の代わりに
(S₀ : Subgroup (↥data.H ⧸ chief.N)) (hS₀ne : S₀ ≠ ⊥)
(hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction …).φ.comp (…).U.subtype) S₀)
(hS₀card : Nat.card ↥S₀ = chief.p) + (hGodd : Odd (Nat.card G)) を取る。False を結論。

手順 (全部品はファイル内に既存):
1. case-b と同じ frame を再構築: Q (exists_normal_subgroup_index_prime) →
   quotient_classTwo_structure → π/hπmk/hπker → hQinv → σ := quotientMulAutHom hQinv →
   hπσ (帰納+rfl)。σ は N̂ を pointwise 固定 (hUcent 降下; hπker 経由の要素計算)。
2. e-bundle: exists_exponent_fun_of_card_prime chief.p_prime hS₀card
   (φ := (typeP_quotientCoprimeAction …).φ.comp (…).U.subtype)
   (hmem := fun v s hs => IsAInvariant.smul_mem hS₀inv v hs) → ⟨e, hep, he, hemul, hefix⟩。
3. S_gen := (π : Ĥ →* H̄) ⁻¹' (⋃ a, ((quotientMulAutHom chief.N_aInvariant a) • S₀ : Set _));
   1 ∈ ⋃ (a := 1 で S₀.one_mem; smul-membership は ⟨1, S₀.one_mem, map_one …⟩);
   closure (⋃) = ⊤: iSup_smul_eq_top_of_irreducible + Subgroup.iSup_eq_closure
   (name 要確認; ⨆ = closure (⋃ coe) の変換) → closure_preimage_eq_top_of_closure_eq_top
   (π 全射 = QuotientGroup.map_surjective or mk-lift) → closure S_gen = ⊤。
4. by_cases hDall : ∀ x ∈ S_gen, ∀ y ∈ S_gen, Commute x y
   - true: commute_all_of_closure_eq_top → 可換 → commutator Ĥ = ⊥ (case-b の J=⊤ 分岐末尾と
     同じ: eq_bot_iff + commutator_le + mem_center) ↯ hcommHat + hNhatCard (card p ≠ 1)。
   - false: push_neg → ⟨x̂, hx, ŷ, hy, hnc⟩; hx : π x̂ ∈ ⋃ → ⟨a, hxa⟩; hy → ⟨b, hyb⟩。
5. c := ⁅x̂,ŷ⁆: c ≠ 1 (commutatorElement_eq_one_iff_mul_comm + hnc); c ∈ N̂
   (hcommHat ▸ commutator_mem: ⁅x̂,ŷ⁆ ∈ ⁅⊤,⊤⁆ = commutator = N̂); c 中心 (hNhatLe);
   orderOf c = p (N̂ card p, c ≠ 1: orderOf ∣ p prime, ≠ 1 — subtype 経由 loop 66 と同型)。
6. 各 u : ↥Usub で: σu x̂ = x̂ ^ e (conjA a u) * ẑ 形:
   - conjA a u : ↥Usub := ⟨a⁻¹ * ↑u * a, by simpa using hUnorm.conj_mem ↑u u.2 a⁻¹⟩
   - π (σu x̂) = φ'u (π x̂) (hπσ) = φ'(conj 分解): φ'u (φa s) 転送は endgame 補題内の計算と同じ
     (map_mul + MulAut.mul_apply + he (conjA a u) s hs) → = (π x̂)^{e (conjA a u)}
   - ẑ := (x̂ ^ e (conjA a u))⁻¹ * σu x̂ ∈ ker π = N̂ (map_mul/map_pow で計算) → 中心。
   - σu c = ⁅σu x̂, σu ŷ⁆ (map_commutatorElement) = ⁅x̂^k * ẑ...⁆ — 表示を x̂^k * ẑ に直すには
     σu x̂ = x̂^k * ẑ (mul_inv_cancel 変形)。中心 drop ×2 (commutatorElement_mul_center_left/right)
     → ⁅x̂^k, ŷ^l⁆ → 冪双線形 ×2 → c^{k*l}。
   - σu c = c (σ の N̂-pointwise 固定) → c = c^{kl} → orderOf c = p ∣ kl - 1 →
     ZMod p: (e (conjA a u) : ZMod p) * (e (conjA b u)) = 1
     (pow_eq_pow_iff_modEq at exponents 1 vs kl + ZMod.natCast_eq_natCast_iff; kl ≥ 1 注意 —
     c^1 = c^{kl} 形で扱えば subtraction 不要)。
7. chain: f : ↥Usub → ZMod p := fun v => e (conjA a v); σ_c := MulAut conj by (a⁻¹ * b) on ↥Usub
   (MulAut.conjNormal?? — ↥Usub は abstract group なので MulAut.conj (c : ↥Usub)?? 注意:
   conj は L-元 a⁻¹b による ↥Usub 上の自己同型 — L が Usub を正規化 → 構成は
   (typeP 側) … 素直には: ↥Usub の元でなく L-元による conj なので MulEquiv を手書き:
   σc : ↥Usub ≃* ↥Usub := ⟨fun v => ⟨(a⁻¹*b)⁻¹ * ↑v * (a⁻¹*b), …⟩, …⟩ か、
   MulAut.conjNormal ((a⁻¹*b) : ↥L) (H := Usub) — conjNormal : L →* MulAut ↥Usub ✓ これで OK
   (Usub.Normal instance = hUnorm)。向き (c⁻¹vc vs cvc⁻¹) は 6 の等式に合わせて調整。
   - hrel: (†) を u := ⟨a v a⁻¹⟩ 代入 → f v * f (σc v) = 1 (loop 65 設計通り)。
   - m := Nat.card ↥L (σc^m = 1: (conjNormal)^m = conjNormal (c^m) = conjNormal 1 = 1 via
     pow_card_eq_one; hmodd : Odd (Nat.card ↥L) from hGodd.of_dvd_nat)。
   - hAodd : Odd (Nat.card ↥Usub) 同様。
   - hne : f v ≠ 0 (hep + ZMod.natCast_zmod_eq_zero_iff_dvd: (n : ZMod p) = 0 ↔ p ∣ n)。
   - hmul : f (u*v) = f u * f v — 注意! f = e ∘ conjA a は e の乗法性 + conjA a が
     群準同型 (conjA a (u*v) = conjA a u * conjA a v ✓ subtype ext で) から。
   - chain_exponent_eq_one → f ≡ 1 → e (conjA a v) ≡ 1 ∀v → v' := conjA a v は v を走ると
     全 ↥Usub を走る (conjA a 全単射: inverse = conjA a⁻¹) → e ≡ 1 on ↥Usub
   - hefix → ∀ v s ∈ S₀, φ'v s = s → caseA_fixed_contradiction chief hS₀ne hfix。

### B. master + S13 instantiation (次々 iteration)

- chiefKernel_eq_bot: by_contra + chiefFactor_clifford_U_dichotomy chief → case b / case a。
  q-odd は hGodd.of_dvd_nat (card_subgroup_dvd) で W₁ から。
- S13_CoreStructure.H_elementaryAbelian: hpK = (hyp.H_isPGroup hG を chief.p に変換 —
  hyp.p = base.w2 vs chief.p: chief.typeIII_IV_p_eq_W2 hyp.type_alt : Nat.card W₂ = chief.p と
  hyp.p = Nat.card W₂ (w2 def) で一致); hNcomm from H0_eq_Hprime + H0_eq + map-injective;
  hUcent from U_centralizes_H0 (G-level → action-level 変換; typeP_conjAction_apply で coe 計算);
  setup_typeP_eq 転送に注意。結論 3 conjuncts: N = ⊥ → H ≅ H̄ (QuotientGroup.quotientBot 経由
  or H0_eq + card) で elementary abelian + card p^q。
