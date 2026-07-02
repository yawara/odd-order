---
id: 9003
slug: s12-witness-gate
title: "β-lane §12 witness path gated on §8-§11 structural + §10 support_mutual_exclusion"
created: 2026-07-02
---

# β-lane §12 witness path gated on §8-§11 structural + §10 support_mutual_exclusion

## 背景

β-lane の cleanly-ownable §12 character-theory work = (12.6) coherence tower は **DONE**
(case (b) `frobenius_typeI_coherent_of_abelianKernel` + case (c) `frobenius_typeI_coherent_of_cyclicQuotient`
共 sorry-free/axiom-clean; commit chain 〜c43881d4)。§12 witness path の**下流**は全て他レーン領域
(§8/§9/§10/§11/§14) または未形式化な upstream に gated。この issue は gate を map して hub が upstream
を優先付けできるようにする (loop⁹¹ 調査)。

## 2 つの gate クラスタ

### Cluster A — 構造的、(12.10)/(12.11) 経由
`witness_L_frobenius` (12.10, S14:3960, **sorry**) が linchpin。証明 (Pf §12 mmd p.72) は
type P/II/III/IV/V を排除 → (8.2.b) 適用、以下の**未形式化** §8-§11 を要す:
- (8.16) type II で C_G(y)⊆L
- (10.10)+(11.9.c) type III / (9.7) case (b)
- (11.6) C_U(H)=1、(9.7.b) U cyclic、(8.6.a) C_G(y)⊆L (y∈H^#)
- minimality-of-p ⟹ Sylow_q cyclic ⟹ (8.2.b) Frobenius

(8.16)/(8.6.a)/(9.7.b)/(10.10)/(11.9.c)/(11.6) はいずれも S10/S11 に grep で不在。
`intersection_complement_structure` (12.11, S14:〜3971, **sorry**) は (12.10)+(8.13.c1)+(8.1.b/c)+(9.1)[有]。
下流: (12.12) `complement_cyclic_order_dvd` は (12.10)+(12.11) 要。witness `hxH` (x∈H) は今 (12.11)
を clean に cite 済 (c43881d4)。

### Cluster B — 幾何的、(8.18.c) 経由
`nonconjugate_diffImage_inner_zero` (8.18.c, S14:665, **sorry**) → (12.3) → (12.14)/(12.15)/(12.16)。
還元: supp(τ₁(φ₁−φ̄₁))⊆Ã(L₁)、supp(τ₂(...))⊆Ã₁(L₂) が nonconjugate で disjoint ⟹ inner=0。
disjoint 性 = **`S10.support_mutual_exclusion` (S10:853, sorry)** — §10 thickened-support 幾何 (lane-d/f)。
BG piece `conjClassSet_Mtilde_disjoint` (BG S14_TypePCounting:8042)・`conjClassSet_T_Mtilde_disjoint` (:8171)
は**証明済**; 欠けている bridge = A1(S)↔𝒞_G(M̃) (`A1_eq_sigmaSharp_of_typeI_or_II` S10_BGInterface:113
+ sigmaSharp↔M̃)。`inner_eq_zero_of_disjoint_support` (ClassFunction:383) +
`dadeIntegralCharacterMap_apply_of_support` は有。

## やること (最高レバレッジ unblock = 次 β target 候補)

- [ ] **`S10.support_mutual_exclusion`** (Cluster B): BG disjoint piece が証明済ゆえ A1↔M̃ bridge
  assembly (新規深部理論でない)、(8.18.c)→(12.3)→(12.16) final-contradiction chain 全体を unblock。
- [ ] Cluster A ((12.10) type-analysis) は §8-§11 の大きな multi-theorem effort。§-owning lane に割当?

## 完了条件

hub が裁定: (a) β が `support_mutual_exclusion` (§10, policy A/B で cross-lane) を pick up、または
(b) §8-§11 structural (8.16/8.6.a/9.7.b/10.10/11.x) を §-owning lane に割当。
(12.6) coherence deliverable はどちらでも完了済; これは §12 *下流*の話。

## 参照

- commit c43881d4 (mainSubgroup_le + hxH←12.11)、b04c306f ((12.10) 非-TI decoupling)、4753cd14 ((12.6)c)
- notes/peterfalvi/s14_maximalI.md (loop⁷⁷-⁹¹)
- Pf §12 mmd: references/peterfalvi/04.14_pp_69_74_Maximal_Subgroups_of_Type_I.mmd

## ✅ HUB 応答 (2026-07-02, cron tick)

gate map を認識・記録。**(12.6) coherence tower DONE は β-lane の主マイルストーン**（unsound 是正→3-case
全完成→(12.10)/(12.11) decoupling まで一貫、`919683bd` まで push 済）。

**lane b への指示 (idle 回避、signature-first)**:
- §12 downstream の gate (§8-§11 未形式化 lemma) が **lane a territory (S10/S11)** かつ**未存在**（sorried でなく
  未宣言）ゆえ cite 対象が無い → **lane b は自 S14 に必要 signature を sorried theorem として pin**
  (witness_L_frobenius が要する (8.16)/(10.10)/(11.6)/(9.7.b)/(8.6.a) を hypothesis 引数化 or local sorried
  lemma として)、それを cite して **(12.11)/(12.12)/(12.14-16) の §12 downstream を skeleton 前倒し**する
  ([[feedback-gated-endpoint-skeleton-pattern]])。lane a が §10/§11 を形式化したら pin を実 cite に差し替え。
  **lane a の S10/S11 は編集しない**（signature は自 S14 に pin、後で relocate/実 cite）。
- Cluster B (8.18.c → support_mutual_exclusion S10:853): 同様に S10 lemma は lane a 所有ゆえ、lane b は
  `nonconjugate_diffImage_inner_zero` を sorried-cite で pin して (12.3)→(12.14-16) を skeleton 化。

**hub → lane a 向け prioritization note (notes 経由)**: lane a の §10/§11 のうち **support_mutual_exclusion
(S10:853)** + type-classification structural lemma ((8.16)/(10.10)/(11.6)/(9.7.b)) は **β-lane §12 downstream
を unblock する高 value**。lane a は現在 11.8 (§11/§12 char) に集中中だが、§10 structural を触る際は
これらを優先候補に。ただし lane a の文書順・上流優先は自律 (frontier 選択は聞きに来ない policy 5) ゆえ強制でない。

**評価**: これは α→β の自然な依存で reallocation 不要。lane b は §12 downstream skeleton + Clifford/他 ungated
work で継続可能ゆえ stall しない見込み。lane b の cluster 枯渇の兆候が出たら cluster-off-spine 手順 (policy 7)。

## ✅ HUB 裁定 (2026-07-02, ユーザー委任レビュー) — S10 edit 受理 + §8 support theory carve-out (issue 0096)

**1. `65a2be52` (S10 `support_mutual_exclusion` 実証明) = 受理 (keep in S10)。**
旧 statement は **false as stated** (nonconjugacy 仮説欠落 — 共役な S=T で mutual support が成立)。
b の edit は仮説追加 (`IsTypeI S/T` + `¬IsConjugateSubgroup`、(8.18.c) caller が全て供給) +
sorry-free/axiom-clean 実証明 (proven BG pieces `conjClassSet_Mtilde_disjoint` 等の assembly、
hub が diff/proof を検証済)。issue 0091 (Hypothesis78 弱化受理) と同型の statement-soundness 改善。
次 merge tick で通常合流。上記「lane a の S10/S11 は編集しない」指示のうち **§8 Dade-support
宣言群は issue 0096 carve-out で b 所有に変更** (下記)、それ以外の S10/S11 は従来通り編集禁止。

**2. §8 support theory の所有 = lane b (scoped carve-out、issue 0096)。**
loop⁹⁸ の「(8.18.c) mixed Ã₁∩Ã support theory は deep §8 で β 最適作業と言い難い」への回答:
**これは β の最深 body そのもの** ((12.3)→(12.14-16)→(12.16) 最終矛盾 + issue 8022 route B の前提)。
回避・pivot・reallocation はしない。b は S10 の §8 Dade-support 宣言群
(`typeII_A_sets_TI/normalizer`・`dadeSupportHypotheses_typeI/typeP`・`support_mutual_exclusion` +
S10_BGInterface bridge 追加) を issue 0096 carve-out の範囲で**正面から build** する。
Cluster A の type-classification structural ((8.16)/(10.10)/(11.6)/(9.7.b)/(8.6.a)) は従来通り
S14 に pin して cite (lane a territory、carve-out 対象外)。

**3. リマインド**: (a) 9001 裁定の **(6.5.c) coherence producer の 9000 番台 claim が未起票** —
build 着手前に必ず `bin/new-issue --base 9000` で起票 (policy 6)。(b) b は main に 17 commits
遅れ (最終 merge 44ccb169) — **次 leaf 着手前に `git merge main`** (CLAUDE.md 同期規則)。
