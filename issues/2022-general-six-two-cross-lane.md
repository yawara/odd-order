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
