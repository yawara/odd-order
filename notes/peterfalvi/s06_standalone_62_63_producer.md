# Pf §6 standalone (6.2)/(6.3) coherence producer — lane-h relane #7 (issue 2021)

> 割当: 2026-06-23 relane #7 (origin/main `4e4c5ca7`, issue 2021 RESOLVED)。lane-h = Pf §6
> coherence producer。lane-c の `S13_MaximalIII_IV` が cite する coherence obligation の
> **standalone 版**を §6/§8 機構から生産する (producer[lane-h] → consumer[lane-c S13])。
> このノートは本タスクの scoping + 中心 design question + plan の正本。

## 1. consumer (lane-c S13 のローカル obligation) — 生産先 signature

`OddOrder/Peterfalvi/S13_MaximalIII_IV.lean`:

- **Thm 6.3** `coherent_S_of_coherent_SH0C` (S13:188): `S(H₀C) coherent ⟹ S coherent`。
  = Pf (6.3) を (L,K,M,H,H₁)=(§13 の M, M', 1, HC, H₀C) で適用。`_hcoh : Nonempty (S07.IsCoherent
  hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)` → `Nonempty (S07.IsCoherent hyp.base.tau hyp.base.Sset
  hyp.base.A0)`。obligation signature には (6.3.a) nilpotent / (6.3.c) index bound は無い → lane-c が
  wiring で §13 facts ((9.6)/(11.1) 等) から供給する想定。
- **Thm 6.2** `coherent_quotient_bound` (S13:215): `S(H₁) coherent (H₁◁M, H₁<M') ⟹ |M':H₁| ≤ 2q|U:C|+1`。
  = Pf (6.2) の §13 instance。`hH1_norm`/`hH1_lt`/`hcoh` 前提 → `H1.relIndex (derivedInG M) ≤
  2 * hyp.q * hyp.C.relIndex hyp.U + 1`。

両者の coherence data = `hyp.base : S12.Hypothesis M` の `tau`/`Sset`/`A0` (下記 §3)。

## 2. Pf 原文 (6.2)/(6.3) — `references/peterfalvi/04.8_pp_30_37_*.mmd`

**Hypothesis (6.1)** (L4): Hypothesis (C) [§5 の filtration/coherence 仮説、要特定] + K solvable
normal subgroup of L + `S = {Ind_K^L θ | θ∈Irr K, θ≠1}`。`S(A) = {Ind_K^L θ | A⊆Ker θ, θ≠1}` (A◁L, A⊆K)。

**(6.2)** (L7-22): (6.1) + [A⊊K, B⊂D⊂C⊂K, D/B⊂Z(C/B), S(A) coherent, S(B) not] ⟹
`2|L:C|·√|C:D| ≥ |K:A|−1`。
証明: (C.b) で S₁,S₂={ψ,ψ̄}, S(A)⊆S₁⊆S(A)∪S(B), S₁ coherent, S₁∪S₂ not。K solvable ⟹ K/A に
degree-1 非自明既約 ⟹ S(A) は degree |L:K| の char を含む ⟹ |L:K| ∣ ψ(1)。**Theorem (5.6)** で
`2ψ(1)|L:K| ≥ ∑_{χ∈S₁} χ(1)²/‖χ‖² ≥ ∑_{χ∈S(A)} χ(1)²/‖χ‖²`。(C.c,d) で
`∑_{χ∈S(A)} χ(1)²/‖χ‖² = |L:K|∑_{θ∈T}θ(1)² = |L:K|(|K:A|−1)`。⟹ `2ψ(1) ≥ |K:A|−1`。
ψ=Ind θ で **θ(1) ≤ |K:C|√|C:D|** (Theorem (C) の degree bound) ⟹ ψ(1) ≤ |L:C|√|C:D| ⟹ 結論。

**(6.3)** (L24-48): (6.1) + [M⊂H₁⊂H⊂K, **(a) H/M nilpotent**, (b) S(H₁) coherent,
(c) |H:H₁|>4|L:K|²+1] ⟹ S(M) coherent。
証明: (b) で minimal A◁L (M⊂A⊂H₁, S(A) coherent)。A≠M と仮定。maximal B◁L (M⊂B⊊A)。H/M nilpotent ⟹
(A/B)∩Z(H/B)≠1、B 極大性で A/B⊂Z(H/B)。**(6.2) を C=H,D=A** で適用: `2|L:H|√|H:A| ≥ |K:A|−1`。
x=|H:A| とおくと `2|L:K||K:H|√x ≥ |K:H|x−1` ⟹ `2|L:K| ≥ √x−1/√x` ⟹ `x−2+1/x ≤ 4|L:K|²`。
(c) で x≥|H:H₁|>1 ⟹ |H:H₁|−1 ≤ x−1 ≤ 4|L:K|²、(c) と矛盾。∴ A=M、S(M) coherent。□

## 3. 既存機構 (building blocks)

### (6.2) core = `S08_Theorem63.lean` (`SibleyDadeHypothesis G L H` 形)
- `sum_re_div_normSq_SsubFiltration_eq` : `∑_{χ∈S(A)} χ(1)²/‖χ‖² = |L:H|·(|H:A|−1)` (= 6.2 の
  degree-square sum 恒等式; ここ H = (6.1) の K)。
- `exists_SsubFiltration_member_degree_index` : S(A) は degree |L:H| の member を含む。
- `sSubFiltration_sum_le_two_psi_caseB` (+ `_columnBreak`) : S₁ coherent が break {ψ,ψ̄} で拡張不能 ⟹
  `|L:H|·(|H:A|−1) ≤ 2·ψ(1)·η(1)` (case (c2))。= (6.2) 証明の core 不等式。

### Theorem (5.6) = `S07_RetargetScaled.lean` (5.6.3 reducible break) + S07_Coherence (orthonormal break)
coherence extension の不等式。(6.2) の `2ψ(1)|L:K| ≥ ∑χ(1)²/‖χ‖²` の source。

### `SibleyDadeHypothesis` (`S08_CoherenceCorePart1.lean:3265`) = Hypothesis (6.8)/(6.4) 形
fields: W1, H (≠⊥, normal, **nilpotent**), `split : L = H ⋊ W1` (complement), L odd, H^# TI in G,
dade datum, S = {Ind_H^L θ | θ≠1}, cases = (c1) Frobenius L=H⋊W1 ∨ (c2) Hypothesis46 (|W₂| prime,
W₂⊆[H,H], coprime |H||W1|)。**⚠ kernel H は nilpotent + complement を要求** (= (6.8) 特殊形)。

### §12/§13 coherence setup = general (6.1) 形 (NOT SibleyDadeHypothesis)
`S12.Hypothesis M` (`S12_MaximalIII_IV_V.lean:119`): `dadeData : S10.DadeSupportHypothesisData M
(typePA0 M typeP)` → `tau`/`Sset`/`A0` を honest projection で定義。`CertainTypeHypothesis (typePA0
M typeP) M` 利用可 (S12:734)。coherence = `IsCoherent hyp.tau hyp.Sset hyp.A0` (5.1)。

## 4. 🔑 中心 design question — **RESOLVED (2026-06-23 実装セッション)**

scoping 時の design question (「既存 core は SibleyDadeHypothesis 形、§13 は general (6.1) 形」) を
実コード精査で**確定・訂正**した。結論:

**general (6.2)/(6.3) の PIECES は既に general 形で `S08_CoherenceCorePart1`/`Part2` に存在する。
欠けていたのは "K (solvable induced-family kernel) を H (nilpotent middle group) から分離した
assembly" だけ。** (A)/(C) という二択でなく、**(A′) 既存 general ピースを K≠H で組み直す**が正解だった。

確認した general ピース (いずれも SibleyDadeHypothesis 非依存):
- `coherentDegreeSumBound_of_not_coherent` (CorePart1:2451) = **(5.6) contrapositive**。`S04.Hypothesis
  G A L` + Dade map 上で general (consumer の `tau = dadeIntegralCharacterMap` と整合)。多数の
  orthonormality/support/generation 仮説を取る。
- `theta_degree_le_index_mul_sqrt_index` (CorePart1:557) = **(6.2) θ-bound** `θ(1)≤|K:C|√|C:D|`、
  general (Thm C は既に完全形式化済; scoping 時「要特定」としたが repo に実在)。
  `characterKernel_restrict_subgroupOf` (:596) が "θ trivial on B"→"Res_C θ trivial on B∩C" を bridge。
- `sum_div_normSq_induce_kernelFilter_eq` (CorePart1:2526) = **degree-square sum**、H.Normal+A.Normal のみ。
- `exists_coherentBreakPair` (CorePart1:952) = **(6.2) dichotomy (C.b)**、`τ`+Sa/Sb 上で general。
- (6.3) descent ピース: `isNilpotent_normal_inf_center_ne_bot` (1100) / `exists_maximal_normal_between`
  (1149) / `normal_central_of_maximal_normal_below` (1175) / `degreeBound_le_of_sqrt_bound` (2798) /
  `six_three_HH1_le` (2862) = nilpotent-central + maximal-B + √-arithmetic、全 general。

**フル assembled な `six_two`/`six_three` (CorePart2:3786/3924) は SibleyDadeHypothesis (K=H) 上**で、
その SibleyDade 依存は実質 **(1) H_nilpotent と (2) `hF : IsFrobeniusGroup L H W₁`** のみ。`hF` が
"induced member Ind_K^L θ は irreducible" を与え (5.2) 仮説 (orthonormality 等) を discharge する
(`sMember_index_le_two_psi`)。§13 の K=M' solvable では member が reducible になり得て、ここが唯一の深い gap。

### 🔻 真の残 gate = general `six_two` (reducible induced member の (6.2) bound)

K solvable で member が可約な場合の (6.2) bound = `coherentDegreeSumBound_of_not_coherent` の
orthonormality/generation 仮説の discharge。これは §5 coherence theory を可約 member へ広げる作業で、
**§10-12 の muGrid/columnSum 機構 (lane-b/c 領域) と絡む**。lane-h の §6/§8 スコープ単独では閉じない。
→ この 1 点を `six_three_descent` の `h62` oracle として露出 (honest gate、sorry でなく仮説)。

## 5. 実装済み (2026-06-23, commit `27019099`) — 新 leaf `S08_Theorem62_63_Standalone.lean`

sorry-free + axiom-clean + AxiomsCheck 登録済 (`IsCoherent.subset` / `six_three_descent`、3 標準 axiom のみ)。

1. **`S07.IsCoherent.subset`** (monotonicity): `IsCoherent τ S A` + `S' ⊆ S` + nonzero supported
   witness ⟹ `IsCoherent τ S' A`。同じ extension が `Submodule.span_mono` + `zSupportedSpan_mono_left`
   で restrict、nonzero witness のみ再供給。(5.1) 述語の general 単調性 (従来欠落)。`noncomputable def`
   (IsCoherent は data 構造)。
2. **`S08.six_three_descent`** (general (6.1) 形 (6.3) の minimal-A descent): K solvable normal +
   H≤K nilpotent (K≠H 可) + M≤H₁<H + S(H₁) coherent + |H:H₁|>4|L:K|²+1 ⟹ S(M) coherent。
   (6.2) index bound を `h62` oracle として取り、それ以外 (minimal A / maximal B / S(B) not coherent /
   A/B⊆Z(H/B) / [K/A,K/A]≠⊤ from K solvable) を完全証明。SibleyDade `six_three` の K=H 固定を K≠H に分離
   = §13 が要求する形 ((6.3) を (L,K,M,H,H₁)=(M,M',1,HC,H₀C) で適用)。

## 6. producer → consumer bridge (lane-c S13 への handoff)

lane-c が S13 obligation を discharge する手順:

- **`coherent_S_of_coherent_SH0C` (11.3 = (6.3))**: **`six_three_of_six_two_oracle` を一本 cite**。
  K=`(derivedInG M).subgroupOf M` (=M', solvable), H=`HC.subgroupOf M`/相当 (nilpotent),
  M=⊥ (1), H₁=H₀C, τ=`hyp.base.tau`, A0=`hyp.base.A0` で適用。producer 内部で C=H,D=A を instantiate 済。
  - 要 bridge: `SOf ⊥ = hyp.base.Sset` (= S = S(1)) と `SOf H0C` が consumer の `hyp.SOf H0C` に一致。
    現状 S13 の `SOf` は free field ゆえ lane-c は `SOf X = inducedFamily filter` に pin する enrich が要る
    (または `hyp.SOf` を本 producer の SOf に合わせる)。
  - 要供給: per-section `h56` ((5.6) muGrid bound, lane-b) と hbound (6.3.c、(9.6)/(11.1) から)。
- **`coherent_quotient_bound` (11.4 = (6.2), C=D=HC)**: **`six_two_general` を直接 cite** (C:=HC, D:=HC で
  `D.subgroupOf C = ⊤` → √|C:D|=√1=1) で `|M':H₁|−1 ≤ 2|M:HC|`、§11 identity 2|M:HC|=2q|U:C| で結論。
  centrality は `HC/B central in HC/B` (= HC/B abelian, 適切な B で). ✅ **`six_two_general` 自由 C,D 化済で直接対応**。

**両 obligation とも general `six_two` で served、残 gate は per-section `h56` ((5.6) muGrid, lane-b/c) のみ。**

## 7. 次ステップ

1. ✅ **DONE (commit `0aec0d82`)** — **general `six_three_index_bound`** =
   `six_three_index_bound_general` (本 leaf、sorry-free+axiom-clean+AxiomsCheck登録)。general `six_two`
   の real-inequality (C=H,D=A: |K:A|−1 ≤ 2|L:H|√|H:A|) から |H:H₁|≤4|L:K|²+1 を導出。index 変換は
   `Subgroup.relIndex_mul_relIndex` (A≤H≤K) + `Subgroup.relIndex_mul_index` (H≤K) → `six_three_HH1_le`。
   ⟹ `six_three_descent` の `h62` を埋める道具が揃い、**両 §11 obligation は general `six_two` 一点に reduce**。
2. ✅ **DONE (2026-06-23 resume, commit pending)** — **general `six_two` ASSEMBLED** =
   `six_two_general` (本 leaf、sorry-free+axiom-clean+AxiomsCheck登録)。Peterfalvi (6.2) 証明の
   **break-pair より下流を一般に実証明**し、唯一残る reducible-member sensitive な (5.6) 核を clean な
   oracle `h56` に isolate。具体的に landed (全 axiom-clean):
   - `map_mk'_le_center_iff` — `D.map(mk' N) ≤ Z(Γ/N) ⟺ ∀d∈D,∀g, ⁅g,d⁆∈N` (中心性の commutator 特徴付け)。
   - `inducedMember_re_le_general` — **(6.2) θ-degree bound for solvable kernel**, **自由 section
     B≤D≤C≤K** で `ψ(1) ≤ |L:C|√|C:D|` (ψ=Ind_K^L θ, θ∈Irr K trivial-on-B)。Sibley central case (K=H=C,
     `psi_degree_le_of_source_central`) と違い K⊋C ゆえ **Clifford a-half が必要** → general
     `theta_degree_le_index_mul_sqrt_index` に CK=C.subgroupOf K, NB=(B.subgroupOf K).subgroupOf CK,
     DK=(D.subgroupOf K).subgroupOf CK を供給。中心性は `subgroupOfEquivOfLe : ↥(C.subgroupOf K) ≃* ↥C`
     (underlying ↥L 元保存) で ↥C→↥CK transport、index は `relIndex_subgroupOf` で `|CK|=|K:C|`/`|DK|=|C:D|`、
     kernel は `characterKernel_restrict_subgroupOf`。
   - `six_two_general` — (6.2) real-inequality **`|K:A|−1 ≤ 2|L:C|√|C:D|` (自由 C,D)** を `h56` oracle から
     導出 (θ-bound + arithmetic)。**両 §11 obligation を直接 served**: 11.3 は (C,D)=(H,A) で
     `six_three_index_bound_general` の `h62` に一致、11.4 は (C,D)=(HC,HC) (√1=1) で `|M':H₁|−1≤2|M:HC|`。
   - `six_three_of_six_two_oracle` — **single-cite (6.3) producer**: `six_three_descent ∘
     six_three_index_bound_general ∘ six_two_general(C=H,D=A)` を bundle。lane-c は **これ一本を cite**して
     per-section `h56` を供給するだけ。**チェーン全体が型整合することを検証済**。
3. 🔻 **唯一残 gate = `h56`** ((5.6) break-member oracle, **lane-b/c**): 各 section B≤A≤H₁ (A/B central in
   H/B, S(A) coherent, S(B) not) に対し break θ∈Irr K (trivial-on-B) で `|K:A|−1 ≤ 2(Ind_K^L θ)(1).re`。
   = 一般 solvable K の (5.6) norm-weighted coherence bound = case-B `sSubFiltration_sum_le_two_psi_caseB`
   の **solvable-kernel 版** (§10-12 muGrid/columnSum, lane-b/c)。**lane-h §6/§8 スコープ外**。issue 2022 で要請。
4. ⚠ 規約: §5-§8 既存本体は触らず cite のみ、生産は本 leaf に隔離 (lane-b 復帰時衝突回避)。維持。

## 8. producer 完成度サマリ (2026-06-23 resume²)

lane-h §6/§8 スコープで生産可能な (6.2)/(6.3) 標準形 assembly は**完全完了**:
- `S07.IsCoherent.subset` (monotonicity) ✅
- `S08.six_three_descent` (general (6.3) minimal-A descent, K≠H) ✅
- `S08.six_three_index_bound_general` (general (6.3) per-step index bound) ✅
- `S08.map_mk'_le_center_iff` (中心性 commutator 特徴付け) ✅
- `S08.inducedMember_re_le_general` (general (6.2) θ-degree bound, 自由 section B≤D≤C≤K,
  Clifford a-half + ↥C→↥CK centrality transport) ✅
- `S08.six_two_general` (general (6.2) real-inequality `|K:A|−1≤2|L:C|√|C:D|`, 自由 C,D, → `h56` oracle) ✅
- `S08.six_three_of_six_two_oracle` (single-cite (6.3) producer, h56 → S(M) coherent) ✅
全て sorry-free + axiom-clean (3 標準 axiom) + AxiomsCheck 登録、full build 3883 green。
**両 §11 consumer obligation は `six_two_general` で直接 served** (11.3=(C,D)=(H,A) via
`six_three_of_six_two_oracle` / 11.4=(C,D)=(HC,HC)) — 残 gate は単一の per-section `h56`
((5.6) muGrid bound for solvable K) のみ。これは genuine cross-lane (§10-12, lane-b/c)、lane-h scope
では閉じない。残 = `h56` (lane-b/c) + lane-c の wiring (cite + SOf を induced-family に pin + h56 供給)。
