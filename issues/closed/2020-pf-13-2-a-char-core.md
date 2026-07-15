---
id: 2020
slug: pf-13-2-a-char-core
title: "Pf (13.2.a) character core: card_kappaHall_lt_of_isTypeP1 (lane-b §10-11)"
created: 2026-06-23
---

# Pf (13.2.a) character core — `card_kappaHall_lt_of_isTypeP1`

> 宛先 = lane-b (Peterfalvi §10–§11 character)。発信 = lane-h (relane #4)。
> lane↔lane sync は notes/issue 経由 ([[cross-lane-sync-via-notes]])。

## 背景: relane #4 で (13.2.a) を wire 完了、残るは character 核

relane #4 (issue 2019+4009) で lane-h が Pf **(13.2.a)「q<p ⟹ S は Type II (=type-P₂)」** を担当。
**型判定の skeleton と配線は完了** (`OddOrder/FeitThompson.lean`):

- `isTypeP2_of_typeP_kappaHall_lt` (下記 obligation 以外 sorry-free): 型-P の S が
  `|K| < |K*|` ⟹ `IsTypeP2 S`。証明 = S type-P ⟹ P₁∨P₂ (`isTypeP_iff_isTypeP1_or_isTypeP2`)、
  P₁ 枝を obligation で排除、P₂ を残す。
- `Section16MaximalPair.S_typeP2 : IsTypeP2 S` field を新設、producer
  `section16MaximalPair_of_isMinimalSimpleOdd` で fill。
- ⟹ **`mp.S_typeP2` が available** ⟹ lane-c の §15 carrier wiring (step 3,
  `exists_typePData_W1_eq_of_isTypeP2` を `mp.S` に適用) が unblock (issue 4009 完了条件達成)。

## 残 obligation = character 核 (lane-b 領域)

```lean
-- OddOrder/FeitThompson.lean
theorem card_kappaHall_lt_of_isTypeP1 (hG : IsMinimalSimpleOdd G)
    {S K Kstar : Subgroup G} (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S)
    (hKS : K ≤ S) (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := <left unproved>
```

**数学的内容** (Pf (13.2.a) 証明の 1 行目): 型-P の S が type-P₁ (= Type III/IV/V) なら、その κ-Hall
因子 K は dual 因子 K* = M_σ(S)⊓C(K) より**大きい** (`|K*| < |K|`)。Peterfalvi 記法で
`q=|W₁|=|K|`, `p=|W₂|=|K*|` ゆえ「S が Type III ⟹ q > p」。

**証明の出典** (Pf §13 = `references/peterfalvi/04.15_*`, (13.2.a) proof):
- **Theorem (10.10)** (Pf §10 = repo S12): G は Type V の極大部分群を持たない ⟹ type-P₁ の S は
  Type III/IV に限定。
- **(11.9.b)** (Pf §11 = repo S13, Hypothesis (11.2) = Type III/IV): 文字集合 `S(HC)` 上の
  coherence / norm 不等式から `q > p`。

⟹ これは Pf §10–§11 の **character 理論** (coherence + Dade isometry norm bound)。repo 未形式化、
lane-b 領域。文献に証明あり ([[feedback-dont-mislabel-formalization-as-research]]) = 形式化労力。

**discharge target の所在 (lane-h 調査)**: (11.9) は repo **S13 `final_typeIII_conclusions`**
(`S13_MaximalIII_IV.lean:386`、lane-h 所有、現 sorried) が
`hyp.q > hyp.p ∧ hyp.caseB_of_97 ∧ IsTypeIII M` を結論 (= q>p の char 核)。但し single-maximal
`Hypothesis M` (= Hyp (11.2)) + `OrthogonalityData hyp` (char data) を前提とする。⟹ `card_kappaHall_lt_of_isTypeP1`
(pair level) への接続 bridge = [pair の type-P1 S → S の Hypothesis(11.2) 構成 (要 (10.1)+(10.10) Type III/IV
判定)] + [`OrthogonalityData` 構成 (char)] + [hyp.q/hyp.p ↔ |K|/|K*| 同定] で、bridge 自体も char-gated。
∴ 当 obligation は **fresh sorry のまま** が clean (接続層に sorry を移すと char infra 構築が二重化)。
`final_typeIII_conclusions` の sorry-free 化 (lane-b char) が本命。

## やること

- [ ] `card_kappaHall_lt_of_isTypeP1` を sorry-free 化 (Pf 10.10 + 11.9.b の形式化、または既存
      lane-b char API を cite)
- [ ] 完了後 `mp.S_typeP2` が axiom-clean になるか確認 (現状は character sorry に gated)

## 完了条件

`card_kappaHall_lt_of_isTypeP1` が sorry-free。完了で **Pf (13.2.a) 全体が unconditional** になり、
`Section16MaximalPair.S_typeP2` (= POLE-1 critical path) が axiom-clean になる。

## 参照

- 現 obligation: `OddOrder/FeitThompson.lean` `card_kappaHall_lt_of_isTypeP1` (本セッション landing)
- 消費: `isTypeP2_of_typeP_kappaHall_lt` → `Section16MaximalPair.S_typeP2` →
  lane-c §15 `basic_structure` carrier wiring (`exists_typePData_W1_eq_of_isTypeP2`)
- 関連: issue 4009 (carrier wiring gate, CLOSED relane #4), issue 2019 (lane-h starve, CLOSED),
  issue 2018 (§13 char gate map), issue 2010 (Pf §10-13 cite-split)
- 原典: Pf (13.2.a)/(10.10)/(11.9.b) = `references/peterfalvi/04.15_*` / `04.12_*` / `04.13_*`
- repo 対応: (10.10)→S12, (11.7)/(11.9)→S13 (lane-h 所有、構造片は landed、character 核は未)

## 2026-06-23 REASSIGN (relane #6、ユーザー裁可、issue 4011) — lane-b → lane-c

hub 統合レビューで lane-c の §15 枯渇 → ユーザー裁可「char ボトルネック支援に再配置」。
本 obligation (card_kappaHall_lt_of_isTypeP1、POLE-1 残バレ sorry) を **lane-c が引き取り**
(FeitThompson def 単位 C=tp+card_kappaHall)。証明 = `no_typeV_maximal` (S12:5767、Thm 10.10) cite +
S13 (11.9.b) coherence/norm cite で (13.2.a) reduction。S13 も lane-c 所有 (issue 2018 移譲) ゆえ
(11.9.b) signature 整備も lane-c 内で可能。宛先 lane-b → **lane-c**。

## 2026-06-23 lane-c (relane #6): Type-V 排除を honest 実証明、gate を (11.9.b) III/IV 核に narrow

lane-c が char ボトルネック支援 (relane #6, issue 4011) で本 obligation を引き取り。**(13.2.a) 証明の
Type-V 排除ステップを sorry-free 実証明** (commit `eeb489f9`):
- `card_kappaHall_lt_of_isTypeP1` は型辞書 `proposition_type_classification` (cite) + `no_typeV_maximal`
  (Thm (10.10), proven) で「type-P₁ ⟹ M_F≠M_σ ⟹ Type III/IV」を実証明 → **sorry-free**。
- 残 char 核を **`card_kappaHall_lt_of_isTypeIIIorIV`** (FeitThompson、新 faithful obligation) に localize:
  `Type III/IV → |K*|<|K|` (= (11.9.b) coherence/norm on S(HC))。**これが lane-b の残タスク** (P₁→III/IV に narrow 済)。

⟹ lane-b は `IsTypeP1` 全体でなく **Type III/IV 限定の (11.9.b) (q>p)** を埋めればよい (Type V は処理済)。
S13 `final_typeIII_conclusions` (11.9) が `q>p` を与えるので、char API landing 後そこに wire 可能。

## 2026-06-25 lane-b (relane #9, W3): coherence-free (10.9) landed — (11.9.b) `q>p` の半分

W3 (= lane-b、正本 `notes/meta/ft_frontier_remap_2026_06_25.md`) 再開。残 char 核 =
`card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson:426, Pf (11.9.b) "type III/IV ⟹ q>p")。
textbook 証明 = "follows from (10.9) and (11.8)"。

**landed (commit このコミット、full build 3884 green)**:
- `S05.TICyclicHypothesis.ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast` — 一般 Bessel NC bound
  `sigmaNC ψ ≤ ‖ψ‖²`。**axiom-clean、AxiomsCheck 登録**。
- `S12.inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` + `…residual_alignedOmegaSigma_inner_eq_zero…`
  — **coherence-free (10.9)** (σ-coeff 形 + 直交補形)。既存 `orthogonality_of_w1_lt_w2` は
  `coh : CoherentHypothesis` 要 → (10.8) で S 非 coherent ゆえ (11.9.b) に使えなかった障害を解消。
  NC bound を Bessel 化、row-branch 排除を `NC≥w₂>w₁+1` で coh-free 化。新規 sorry なし
  ([[feedback-cite-sorried-lemmas-if-signature-correct]]、sorryAx は既存 §10 carrier 由来 = 既存 (10.9) と同 taint)。

**残 Part 3 ((11.9.b) 完成 → 当 obligation)** — 詳細 = `notes/peterfalvi/s10_13_maximal_structure.md` §11:
1. ∃ ζ ∈ S(HC) of degree w₁ (genuine §11 fact、(10.2) の S(HC) 版)。
2. **genuine (11.8)** = de-opacify `S13.notOrthogonalFormula` + 実証明 ((11.8.1)-(11.8.6)、deep、**主負荷**)。
3. reduction: coherence-free (10.9) [residual ⊥] vs (11.8) [¬⊥] 矛盾 ⟹ w₁>w₂。
4. carrier 構成 (`exists_hypothesis_of_typeIIIorIVorV`) + q=w₁=|K|, p=w₂=|K*| 翻訳。

⟹ (11.9.b) の **(10.9)-half は完成**、残 = (11.8)-half (genuine de-opacify + 証明) + reduction wiring。

## 2026-06-25 lane-b (cont.): (11.8) missing page 復元 + full proof 文書化 + norm lemma 抽出

`card_kappaHall` の唯一の deep gate = genuine (11.8)。mmd `04.13` の (11.8.1)-(11.8.4) は
`[MISSING_PAGE_FAIL:3]` (p.66) で欠落していたため **PDF (pages 2-3) から復元** ([[nougat-missing-page-recovery]])。
**正本ノート新設: `notes/peterfalvi/s13_11_8_orthogonality.md`** に (11.8.1)-(11.8.6) 全文 + 形式化プラン +
carrier bridge 調査を記録。

**(11.8) の構造 (要点)**: S₁=S(HC) は定数次数 q の既約 (u−1)/q 個 ((U/C)⋊W₁ Frobenius) ⟹ **(5.7)
`coherent_of_constant_degree` で coherent** (τ₁ 取得)。証明は背理法: residual が直交すると仮定 → (11.8.4)
で `(μ₀−ζ)^τ=∑ω_{i0}^σ−ζ^{τ₁}` 正規化 (← landed (10.9) 直結) → (11.8.6) で S(C) coherent → **(11.3)
`S_H0C_not_coherent` (✅ proven) と矛盾**。残 gate = §9 (9.8/9.9/9.11) carrier + S(HC)/S₂ 材料化。

**code 増分 (commit)**: `S12.inner_muColumnZero_sub_zeta_self` (= ‖μ₀−ζ‖²=w₁+1、(10.9) から抽出、
(11.8.4) で再利用)。(10.9) を本 lemma cite に refactor (de-dup)。

**carrier bridge**: |K|=w₁ ✅ (`card_kappaHall_eq_derived_index`+`card_W1_eq_derived_index`、両者 M' complement)。
|Kstar|=w₂ は type-P duality (`card_kappaHall_sup_Kstar`+|K⊔Kstar|=|W|) 経由。∃ζ∈S(HC) degree-w₁ は自動。

## 2026-06-26 lane-b (W3): bare FT sorry ELIMINATED — carrier translation fully wired

**`card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson:426) is no longer a bare sorry.** `FeitThompson.lean`
is now **sorry-free in its own body** (grep: 0 real sorries). The唯一の残 FT-path char gate は
`S12.exists_zeta_residual_not_orthogonal` (= genuine Peterfalvi (11.8)) に isolate された。full build 3884 green。

**landed (this commit)**:
- **`card_Msigma_inf_centralizer_eq_card_W2`** (FeitThompson.lean、**axiom-clean**、AxiomsCheck 登録):
  type-P 極大 S・κ-Hall K (cyclic)・任意 TypePData d で `|M_σ(S) ⊓ C(K)| = |W₂| = w₂`。
  これが `|Kstar|=w₂` carrier bridge の **完全証明** (旧 note の「type-P duality 経由」予想を、より直接的な
  centralizer 論法で実証)。証明: `W₂ = M' ⊓ C(W₁)` (`centralizer_W1`) を `W₂ ≤ M_F ≤ M_σ ≤ M'`
  (`W2_le`/`H_eq`/`maxNilpotentNormalHall_le_Msigma`/`Msigma_le_derived`) で sandwich → `M_σ ⊓ C(W₁) = W₂`;
  K と W₁ は M' (normal Hall) の complement ゆえ S-共役 (Schur–Zassenhaus `exists_conj_of_coprime`);
  `M_σ ⊓ C(K)` を共役 (M_σ は S-不変) で `W₂` に移し card 一致。**char 不要の純群論**。
  helper 2 本 (`centralizer_eq_of_generator`、`map_subtype_conj_smul`、private)。
- **`S12.exists_zeta_residual_not_orthogonal`** (genuine (11.8) obligation, sorried) + **`S12.w2_lt_w1_of_hypothesis`**
  (sorry-free wrapper、(11.8) + 既存 reduction `w2_lt_w1_of_residual_not_orthogonal` を結合)。
- **`card_kappaHall_lt_of_isTypeIIIorIV` の実証明**: `typeP_duality` で `IsCyclic K`、
  `exists_hypothesis_of_typeIIIorIVorV` で hyp 構成、`|K|=w₁` (`card_kappaHall_eq_derived_index` +
  `card_W1_eq_derived_index`)、`|Kstar|=w₂` (bridge)、`w2_lt_w1_of_hypothesis` で締結。

**意義 (sorry 数でなく実質)**: `|Kstar|=w₂` は W3 critical path の群論ゲートだったが、これで完全に閉じた
(axiom-clean)。残 W3 = **genuine (11.8) の単一 char obligation** (`exists_zeta_residual_not_orthogonal`、
S12、lane-b)。これは documented "main load" (11.8.1)-(11.8.6) = §9 char counting + S(HC)/τ₁ materialization
依存の deep multi-step。詳細 = `notes/peterfalvi/s13_11_8_orthogonality.md`。

## bridge-enabled next step (recorded 2026-06-26)

The new `card_Msigma_inf_centralizer_eq_card_W2` (|K*|=w₂) directly enables proving
`S10.exists_typeII_maximal_with_w2_of_typeP` (S10:148, the (8.8) Type-II partner, **on FT path** —
consumed by S11 (9.3) / S12 (10.3) `w2_prime`): the `typeP_duality` partner `Mstar` is Type II with
`[Mstar:Mstar'] = |Kstar| = |W₂|`. To land it: (1) **relocate the bridge** from `FeitThompson` to `S10`
(upstream; S10 transitively imports its deps via `S16_MainResults`; better reusable home), then
FeitThompson + AxiomsCheck cite `S10.card_Msigma_inf_centralizer_eq_card_W2`; (2) get
`BG.Ch4.S14.IsTypeP M` (= κ≠∅, **distinct** from `Nonempty (TypePData M)`) from M type III/IV/V via
non-I (`notTypeI_imp_typeP` + type exclusivity); (3) cite `proposition_type_classification` (W1, sorried)
twice — M not P₂ (⟹ partner is P₂) and P₂ partner ⟹ Type II. This swaps the current "gated on
theorem88_caseB_holds (W2)" sorry for "gated on proposition_type_classification (W1, actively-worked) +
axiom-clean bridge" — a cleaner gate. Distinct unit; not started.

## 2026-06-26 (cont.): bridge-enabled `exists_typeII_maximal_with_w2_of_typeP` LANDED

The "next step" above is **done**. `S10.exists_typeII_maximal_with_w2_of_typeP` (S10:148, (8.8)
Type-II partner, FT-path — consumed by S11 (9.3) `typeIIIorIV_W2_prime` / S12 (10.3) `w2_prime`) is
now **sorry-free** (S10 real sorry 12→11). full build 3884 green.

- **Relocated** `card_Msigma_inf_centralizer_eq_card_W2` (+ 2 helpers) from `FeitThompson` to `S10`
  (upstream/reusable home; FeitThompson + AxiomsCheck re-cite `S10.card_Msigma_inf_centralizer_eq_card_W2`,
  still axiom-clean + registered).
- **Proof** = `typeP_duality` partner `Mstar` + bridge: M type III/IV/V ⟹ IsTypeP1 (via
  `proposition_type_classification`) ⟹ κ≠∅ + ¬P₂; κ-Hall K via `hall_E_exists`; duality disjunction
  ⟹ P₂ Mstar ⟹ IsTypeII Mstar; `[Mstar:Mstar']=|K*|` (`card_kappaHall_eq_derived_index`) `=|W₂|`
  (bridge). Cites sorried `proposition_type_classification` (W1, lane-f, actively-closed) —
  **swaps the old "gated on theorem88_caseB_holds (W2)" for the cleaner W1 gate + axiom-clean bridge**.

## 2026-06-26 lane-b (W3): frontier re-targeting — true upstream keystone = (10.8), now structured

**Re-targeting (correction to the W3 frontier map).** The live memory listed the W3 gate as
`S12.exists_zeta_residual_not_orthogonal` (= Pf (11.8)) + `no_typeV`. Dependency tracing shows the
**true upstream keystone is Pf (10.8) `S12.S_not_coherent`** (`S` not coherent): it is cited by
**both** (11.3) `S13.S_H0C_not_coherent` (which feeds (11.8)) **and** (10.10) `no_typeV_maximal`.
(10.8) was itself a single opaque `sorry`. By document order + upstream-first, (10.8) — not (11.8) —
is the correct W3 target.

Moreover the §9 Clifford counts (9.8)/(9.9)/(9.10) that (11.8) ultimately needs are stated against
the **opaque, never-constructed** carrier `S11.Section11CharacterData` (`S`/`SOf`/`tau` are free
fields with no producer), so (11.8) is doubly blocked at the §9 root. (10.8)'s machinery, by
contrast, is largely in place (the arithmetic closer and (10.6.b) are proven; §7 (7.5)/(7.8.b) live
in S09), so (10.8) is the actionable upstream piece.

**Landed (commit 664a158b): (10.8) structured into Peterfalvi's faithful 3-part decomposition.**
`S_not_coherent` is now a **sorry-free assembly**:
- `typeII_noncoherence_arithmetic` (pure-ℚ closer, pre-proven) wired;
- `(10.3)` params + `CoherentHypothesis` built genuinely from the coherence assumption;
- `w₁ ≥ 3` (|W₁| odd + ≠⊥, derived without the FiniteInduce-scoped `tic` to dodge the
  explicit-vs-scoped `Fintype G` clash) and `w₂ ≥ 1` proven inline;
- two gates isolated precisely:
  * `Hypothesis.card_derived_ge` : `(2w₁+1)·w₂ ≤ |M'|` — **routine group theory** (W₁-on-M'/M'' FPF
    via `caseB_W1_dvd_index_of_centralizer_le` + `commutator_subgroupOf_self`/`map_commutator`
    transport + W₂⊆M''; mechanism fully scoped in `notes/peterfalvi/s12_10_8_noncoherence.md`);
  * `typeII_coherence_contradiction_estimate` : `∃ u≥7, 1−1/w₁−1/u < w₁w₂/|M'|` — **the single
    genuine remaining §10 character gate** (§7 norm-counting: (7.5)+(7.8.b)+(10.6.b)+TI-counting,
    needs (10.7) `typeII_derived_frobenius` for the Type-II partner's `UW₂` Frobenius).

`no_typeV_maximal`/`S_H0C_not_coherent` unchanged (cite (10.8) by signature). full build 3884 green.
正本 = `notes/peterfalvi/s12_10_8_noncoherence.md`.

**Next (W3, priority order)**: (1) discharge `card_derived_ge` (mechanical, scoped); (2) `(10.7)`
`typeII_derived_frobenius` (partner Frobenius, upstream of the estimate); (3) the §7 estimate
`typeII_coherence_contradiction_estimate` (the genuine §10 analytic heart). Separately, (11.8)
remains blocked on materializing the §9 `Section11CharacterData` carrier.

## 2026-06-26 lane-b (cont.): card_derived_ge PROVEN — (10.8) は §7 gate 単独に

`Hypothesis.card_derived_ge` (`(2w₁+1)·w₂ ≤ |M'|`) を**完全証明** (commit b9314c52)。
W₁ の `↥(M'.subgroupOf M)` 上 FPF conjugation (`S08.caseB_W1_dvd_index_of_centralizer_le`,
axiom-clean) + M' solvable-nontrivial による `⁅H,H⁆<⊤` + `W₂⊆M''` + `index_mul_card`。
sorryAx は共有上流 `typePData_W1_hall_coprime` のみ。S08_CaseBEndgame を S12 に import (acyclic)。

⟹ **(10.8) `S_not_coherent` の残 sorry は genuine な §7 norm-counting 推定
`typeII_coherence_contradiction_estimate` 単独** (算術 closer + 構造的下界 + params/coh は全 genuine)。
**次手 = (10.7) `typeII_derived_frobenius` (partner Frobenius、§7 estimate の上流) → §7 estimate 本体**
(Hypothesis71/78 instance を §10 Type-II partner に構築 + (7.5)+(7.8.b)+(10.6.b)+TI-counting)。

## 2026-06-27 lane-b (W3): (10.8) estimate decomposed — analytic chain + V^G TI-counting landed

`typeII_coherence_contradiction_estimate` (the sole remaining S12 gate of (10.8)) is **Peterfalvi's
chain (04.12 lines 79-99)**, not one opaque step.  Two genuinely-provable pieces are now **proven,
sorry-free, full build green** (commit on lane-b, `S12_MaximalIII_IV_V.lean`):

- **`typeII_coherence_estimate_chain`** — pure-ℚ analytic combination (lines 87-99): from the §7
  output (line 87) + TI-counting bound + `|S|=|H||U|w₂`, derives `1−1/w₁−1/u < w₁w₂/|M'|`.
- **`typePData_card_W`** (`|W|=w₁w₂`), **`typePData_typePV_ncard`** (`|V|=w₁w₂−w₁−w₂+1`),
  **`typePData_W_normalizes_typePV`** (W-stab of V), **`typePData_conjClassSet_typePV_ncard`**
  (`|V^G|=|G:W|·(w₁w₂−w₁−w₂+1)`, via `ncard_conjClassSet_of_isTISubset` + existing `typePData_V_ti`).

These are fundamental reusable type-P torus facts (ω-grid on W=W₁×W₂, (4.5) reducibles, A_0(M)⊇V^G).

**Estimate now reduces precisely to**:
- **(A) §7 output (line 87)** = (7.5)+(7.8.b)+(10.6.b) for (M, A(M)) — needs a `S09.Hypothesis71`
  instance for (M, A(M)).  Feasible: §7 (7.1)-(7.8) sorry-free in S09; §10 `Hypothesis.tau` is a
  genuine Dade map for A_0(M); `S10.dadeSupportHypotheses_typeP` gives the A(M) Dade data;
  `HConjInvariant`-for-A(M) resolvable via `S04.HConjInvariant.restrict` (A(M)⊆A_0(M)).  **Cleanest
  next upstream step.**
- **(B1) inclusion G₁ ⊆ (H#)^G ∪ V^G** — gated on **(10.7) `typeII_derived_frobenius`**, itself
  §9-blocked (Peterfalvi's (10.7) proof cites (9.8.b)/(9.9.b)/(9.10) against the opaque
  `S11.Section11CharacterData` carrier — same root as (11.8); no structural shortcut, since
  `TypeFData.frobenius_HU0` only gives `H⊔U₀` Frobenius, not full `[S,S]`).
- **(B2) (H#)^G count** — partner analogue of the V^G count, once partner H#-TI + N_G(H#)=S available.

正本ノート = `notes/peterfalvi/s12_10_8_noncoherence.md` (2026-06-27 section).

## 2026-06-27 lane-b (W3, cont.): (8.16) `N_G(A(M))=M` proven — §7 input self-contained

Continuing the (10.8) `no_typeV` path (the other on-path W3 obligation besides (11.8)).  The §7
estimate input (A) had an upstream prerequisite carried as a *free parameter*: the `M`-stability
`hN : N_G(A(M)) = M` of `toHypothesis71` / `toFamilyHypothesis71`.  **Now proven** as
`S12.Hypothesis.normalizer_typePA_eq` (Peterfalvi (8.16), axiom-clean, full build 3884 green):

- From the carried `N_G(A_0(M)) = M` (`hyp.dadeData.normalizer_eq`, `A_0(M) = A(M) ∪ V^G`): `A(M)` is
  `M`-invariant and `V^G = 𝒞_G(V)` is conjugation-invariant under all of `G` (new reusable
  `OddOrder.GroupTheory.mem_conjClassSet_conj_iff`), so `N_G(A(M)) ⊆ N_G(A_0(M)) = M ⊆ N_G(A(M))`.
- `toHypothesis71` / `toFamilyHypothesis71` now derive `hN` internally ⟹ the (7.5) family inequality
  for `(M, A(M))` (Pf (10.8) line 81) is applicable directly from the genuine `Hypothesis`.

This is a genuine upstream prerequisite of the honest (10.8) §7 estimate (not a sorry-count change).
正本 = `notes/peterfalvi/s12_10_8_noncoherence.md` (2026-06-27 cont. section).  Remaining (10.8) §7:
`S09.Hypothesis78` (7.8.b) instance for `M` + the line-83 norm assembly; (10.7)/(11.8) stay §9-blocked
on the `S11.Section11CharacterData` carrier (the W3 keystone).

## 2026-06-27 lane-b (W3, cont.²): §7-estimate inputs rounded out; (7.8.b) config clarified

Continuing the (10.8) §7 side.  Two more genuine inputs proven (axiom-clean, full build 3884 green):
- `typePA_eq_sharpSubgroup_derivedInG`: **`A(M) = (M')#`** (the centralizer-support def collapses on
  `(M')#`).  ⟹ `A = H#` with `H = M'` normal — **corrects** the earlier "A ≠ H#" finding; the (7.8.b)
  `Hypothesis78` for `(M, A(M))` is the `H = M'` instance.
- `Hypothesis.card_typePA_div_card_lt_inv_w1`: `|A(M)|/|M| < 1/w₁` (line-87 strict bound).

With the earlier `normalizer_typePA_eq` (8.16), the §7 input side of (10.8) is now: (7.5)-for-`(M,A(M))`
applicable (line 81), `card_derived_ge`, the G₀-drop, the ℚ chain, and the line-87 arithmetic — all
proven.  **The one genuine remaining §7 piece** = the (7.8.b) `Hypothesis78` instance for `(M, A(M))`,
`H = M'` (family `inducedFamily M`, `ν = coh.tau1`, the (7.7.a)/(7.8.c.i) certificates = the deep part).
After that the line 81→87 assembly is mechanical; the final contradiction still needs `hB` (TI-counting)
which is §9-blocked via (10.7) — the `S11.Section11CharacterData` carrier (W3 keystone, shared with
(11.8)).  正本 = `notes/peterfalvi/s12_10_8_noncoherence.md` (2026-06-27 cont.² section).

## 2026-06-27 lane-b (W3, cont.³): §7 input prerequisites COMPLETE

`inner_tau1_zeta_self_eq_one` (‖ζ^{τ₁}‖²=1) landed.  **All (10.8) §7 *inputs* are now proven**
(normalizer_typePA_eq/typePA=(M')#/card_typePA_div/inner_tau1/card_derived_ge/G₀-drop/ℚ chain).
The line-83 assembly is fully scoped & mechanical (Finset bookkeeping; see note).  Two deep gates
remain, both isolated: (7.8.b) Hypothesis78 instance for (M,A(M)) H=M' (the (7.7.a)/(7.8.c.i)
certificates) — cleanest next target; and hB TI-counting (§9-blocked via (10.7), the
S11.Section11CharacterData carrier = W3 keystone, shared with (11.8)).  正本 =
notes/peterfalvi/s12_10_8_noncoherence.md (2026-06-27 cont.³).

## 2026-06-27 lane-b (W3, cont.⁴): line 83 PROVEN

`chiRhoNormSq_zeta_le_line83` landed (the mechanical (7.5)+G₀-drop step, full build 3884 green).
**The entire mechanical/arithmetic spine of (10.8) is now proven** (lines 79-83 + the line-87
arithmetic + the ℚ chain + the closer).  The two remaining gates are exactly: (7.8.b) `‖ζ^{τ₁,ρ}‖²`
lower bound (the `Hypothesis78` instance for (M,A(M)), H=M' — config fixed, (7.7.a)/(7.8.c.i)
certificates are the content) and `hB` TI-counting (§9-blocked via (10.7), the
`S11.Section11CharacterData` carrier = W3 keystone, shared with (11.8)).  正本 =
notes/peterfalvi/s12_10_8_noncoherence.md (2026-06-27 cont.⁴).

## 🧾 注記 (2026-07-02 hub 全体レビュー): 宛先更新

- 3 レーン再編 (正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`) 後の宛先:
  **`S12.exists_zeta_residual_not_orthogonal` (= genuine Pf (11.8)) は lane a の 11.8
  frontier** (S12_MaximalIII_IV_V.lean:2645; **live plan =
  `notes/peterfalvi/s13_11_8_orthogonality.md`**)。本 issue 中の「lane-b (W3)」宛先は
  stale — (11.8) の進行は上記 note を正とする。
- 本 issue は **`card_kappaHall_lt_of_isTypeP1` (FeitThompson.lean:473) の tracker として
  open 維持** (obligation は未 discharge、(11.8)/(10.10) 経由の背景分析は有効)。
