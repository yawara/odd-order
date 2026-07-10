---
id: 1020
slug: s12-108-relayering-102circle
title: "(10.8) hB の配線設計 — pair-route (10.7)' の (13.2.a) 循環発見 + 書籍 DAG 復元 3 phase 計画"
created: 2026-07-11
---

# (10.8) hB の配線設計 — (13.2.a) 循環の発見と 3 phase 計画

**lane a 設計記録 (2026-07-11 /loop)。⚠ 本 issue の循環発見は (10.8)/(11.8) 系 sorry を
埋める全員に関係 — hB を pair-(10.7)' cite で埋めるのは論理循環で不可。**

## 状況 ((10.8) の残り = hB 1 点)

`typeII_coherence_contradiction_estimate` (S12_MaximalBasic:828, sorry :876) は
hA (line-83 + (7.8.b) `chiRhoNormSq_zeta_ge_line78`) と hS/hu (partner 分解 +
`exists_typeII_partner_card_U_ge_seven`) が**証明済**。残 = **hB**
`g1g ≤ (|S_F|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)`:
- 数学 (Pf p.60 lines 89-91): x ∈ G₁ → a := w₁-素数冪 part (prime order, x ∈ C(a))
  → (8.11)[**今日 6b08f22d で閉鎖**] H Hall → a ~ H# 元 → (8.6.a) C_G(a) ⊆ S →
  x ∈ C_S(a) → x ∈ HU なら **(10.7)** Frobenius kernel property で x ∈ H /
  x ∈ S−HU なら (2.1) で x ~ V 元 ⟹ **G₁ ⊆ (H#)^G ∪ V^G** → union-bound 計数
  (TI 不要、≤ 方向は N_G(H)=S / N_G(V) ⊇ W の軌道数上界で足りる) → ℚ 算術。
- 部品状況: V^G 側 ncard = `typePData_conjClassSet_typePV_ncard` (S12_Core:772、済)。
  (8.6.a)/(2.1)/Hall-共役/covering 本体 = 未 (Phase 2)。

## ⚠⚠ 発見: pair-route (10.7)' cite は論理循環

import 位相: MaximalBasic は pair leaf (`S12_TypeIICrossIsometryPair`) の**上流**
(FTS ← S13_CoreStructure ← S12_MaximalIII_IV_V ← … ← MaximalBasic) → cite 不能。
さらに taint 追跡で**論理循環**を確認:

```
(10.8) hB → [cite したい] (10.7)' typeII_HU_frobenius_of_coherent'
  → exists_reconciled_conj_typePData_S → isTypeP2_of_typeP_kappaHall_lt (13.2.a, FTS:703)
    ├→ card_kappaHall_lt_of_isTypeP1 (FTS:684) → no_typeV_maximal (10.10) → S_not_coherent (10.8) → hB ← 循環!
    └→ card_kappaHall_lt_of_isTypeIIIorIV (11.9.b, FTS:624) → (11.8) route → …残 sorry に (10.8) を含む ← 循環!
```

現在の acyclicity は hB ほか sorry が cut point になっているだけ。**書籍では循環しない**:
book-(10.7) は (13.2.a) を使わず §8/§9/§5 のみ ((13.2.a) は §13 で (10.10) の後)。
循環の根 = repo pair-route が M-seed relabel に (13.2.a) を使ったこと (9079 P3/P4 の
「既知 taint 継承」の正体)。

## 復元計画 (書籍 DAG: (8.8)ThmC → (10.7) → (10.8) → (10.10) → (11.x) → (13.2.a))

**Phase 1 — pair route の de-taint (a 所有、着手可)**: M-seeded pair producer 群
(exists_section16MaximalPair_data_around/_around + S_typeP2 pin) の
`isTypeP2_of_typeP_kappaHall_lt` 使用を **`theoremC_paired_structure` の P₂-disjunction
`(IsTypeP2 M ∨ IsTypeP2 Mstar)` (TheoremsAE:967、axiom-clean 実測済!) +
`not_isTypeP2_of_isTypeIII_or_IV_or_V` (clean、landed)** に置換。
⟹ (10.7)' が真に axiom-clean 化 (現 taint は 13.2.a 経由のみ)。

**Phase 2 — hB cover-bound engine (a 所有、Phase 1 と独立に着手可)**: MaximalBasic に
hypothesis-parameterized 版
`typeII_partner_G1_cover_bound (hfrob : IsFrobeniusGroup (derivedInG S) …) : g1g ≤ …`
を実証明 (covering + 計数 + 算術の本物の数学は全部ここ)。estimate は
`hfrob`-parameterized 版 `…_of_partner_frobenius` を並設 (現行 statement は不変のまま
sorried 維持、consumer 移行後に deprecate)。

**Phase 3 — relayering (hub 調整含む、Phase 1-2 後)**: 新 leaf `S12_Noncoherence.lean`
(pair leaf import) に無条件 estimate + S_not_coherent + no_typeV_maximal を移設。
FTS の (13.2.a) trio (card_kappaHall_lt_of_isTypeP1 / isTypeP2_of_typeP_kappaHall_lt /
card_kappaHall_lt_of_isTypeIIIorIV) は Phase 1 後の残消費を調査の上、§13 層下流へ移設
(S15/S16 = lane b/c の消費があれば repoint、hub flag)。FTS は char-free packaging
(ThmC ベース) に純化。

## 参照
- 9079 (pair route、(10.7)' landed) / 9080 ((8.17) mis-layering、同型の発見)
- notes/peterfalvi/s12_10_8_noncoherence.md 2026-07-06 audit (prime-TI 必要説は
  pair route で supersede 済; 本 issue が現行正)
- 6b08f22d ((8.11) 閉鎖 = hB の入力)

## 2026-07-11 tick² — Phase 1 の精密化 (K_lt_Kstar 依存の実測)

**確認事実**:
- (13.2.a) の term 消費 = 2 点のみ: GridTranspose:617 (M-seeded producer の hlt 導出) +
  FTS:760 (canonical producer の S_typeP2 fill)。
- M-seeded producer の **P₂-pin は既に clean** (`typeP_duality` の disjunction
  `hP2disj.resolve_left hnotP2` — Thm C 置換すら不要)。dirty なのは
  **`K_lt_Kstar` field の fill のみ** (|K(S)| < |W₁(M)| = order↔P₂ 相関 = (13.2.a) そのもの、
  M-seeded では labelling 自由度が無く回避不能)。
- canonical producer は逆配置: order = labelling で free / S_typeP2 = (13.2.a)。
  ⟹ **structure が (order, P₂) の相関を同時要求する限り、どちらかの producer 経路で
  (13.2.a) が必須** — 相関自体が (13.2.a) の内容だから。
- (10.7)' chain は K_lt_Kstar を**実消費**する: (i) tp-producer
  `section16TypePStructure_of_isMinimalSimpleOdd` (FTS:1026) が components 呼び出しに
  `mp.K_lt_Kstar` を渡す (q<p labelling)、(ii) `Section16TypePStructure.W1_eq_K_and_W2_eq_Kstar`
  (FTS:1202) のラベル一致算術 (|K|=q の pin) — pair lemmas の hSW1/hSW2 供給元。
- **q<p は Pf §13 の章規約** (本では (13.2.a) の後で初めて確立)。§16 packaging
  (Section16TypePStructure) がそれを field 化し、pair-route (10.7)' が §10 の身分で
  消費しているのが anachronism の正体。

**Phase 1 改訂 (1a = 本命)**: pair-(10.7)' chain の **q<p-free 化**:
- `Section16MaximalPairCore` split (K_lt_Kstar 抜き; `extends` で現行互換)。
- pair lemmas の W-block pin を `W1_eq_K_and_W2_eq_Kstar` (order-matching) から
  **construction-level pin** (typePData_of_kappaHall_hallComplement は `.W₁ = mp.K` を
  直接与える — order-free) に差し替え。tp packaging の q<p を chain から外す。
- M-seeded producer は Core を emit (完全 clean) + `.toFull` 拡張 lemma ((13.2.a) cite、
  order が要る消費者用に分離)。
- 影響調査 TODO: pair leaves 内の `W1_eq_K_and_W2_eq_Kstar` / `tp.q`/`tp.p` 投影の全数、
  S15/S16 (b/c) の Section16MaximalPair ⟨⟩-constructor / K_lt_Kstar / q_lt_p 使用。

**着手順の判断**: Phase 2 (hB cover-bound engine、hypothesis-parameterized) は
taint と独立な純 genuine math で設計リスクなし → **次 tick は Phase 2 から**
(Phase 1a の refactor は影響全数調査と併せて fresh context で)。

## 2026-07-11 tick⁸ — ★★ Phase 2 完結 (hB の数学が全て landed)

`Hypothesis.g1_div_le_of_partner` (MaximalBasic、axiom-clean) が estimate の
hB sorry と同形の ℚ 不等式を hypothesis-parameterized で完全証明。積み上げ
(全て axiom-clean、commits 20d5db9a…d9502c0a + 本 commit):
V-capture / Hall 共役 / 被覆コア / union-bound 計数 (generic + H#) /
W-分解 / V-order / 支持制限 (Ã₀∩cop ⊆ Ã) / Nat-count bound / ℚ 除算。

**Phase 3 (次)**: 供給 8 hypothesis の discharge を pair leaf 下流の新 leaf
(S12_Noncoherence) で:
- hprime = w₂ prime (dII.common / theorem88_caseB_prime_orders 系)
- hcop = typePData_W1_hall_coprime
- hHall = (8.11) hall_maxNilpotentNormalHall_and_mainSubgroup (閉鎖済!)
- hcent = (8.6.a) — 要 port 確認 (§8 の type-II TI clause)
- hfrobcap = (10.7)' typeII_HU_frobenius_of_coherent' の kernel-centralizer 帰結
  (IsFrobeniusGroup.centralizer_kernel_le、subgroupOf 橋)
- hW1card/hW2card/hWcard = pair の W-block pin (mp.Kstar_eq 系 +
  card_mul_eq_of_disjoint_sup_le_isCyclic (FTS:1167))
+ estimate/S_not_coherent の hypothesis-parameterized 変種を MaximalBasic に
  並設 → 無条件版を S12_Noncoherence で (13.2.a)-circle 回避 (Phase 1a) と併せて。

## 2026-07-11 tick⁹ — Phase 3 前半完了: S_not_coherent_of_partner が axiom-clean

- **parameterized 変種 2 本 landed** (MaximalBasic、共に sorryAx なし):
  `typeII_coherence_contradiction_estimate_of_partner` (hB = g1_div_le_of_partner で実 discharge) +
  **`S_not_coherent_of_partner`** — (10.8) 本体が partner 供給 modulo で完全証明。
- **供給 ledger (実測済)**:
  - hcent ((8.6.a)) = `typeII_centralizer_le_of_mem_mainSubgroup` (S14 WitnessSylowCyclic:929、
    **axiom-clean 実測**) or 直接 `typeP_core_centralizer_le_of_mem_fitting` + H_eq。
  - hHall = (8.11) (6b08f22d 閉鎖済) + H_eq/mainSubgroup .II 変換。
  - hprime = hW1card ▸ hyp.w2_prime。hcop = typePData_W1_hall_coprime。
  - hfrobcap = (10.7)' typeII_HU_frobenius_of_coherent' +
    IsFrobeniusGroup.centralizer_kernel_le の subgroupOf 橋 (機械的、pair leaf 下流)。
  - hW2card/hWcard/hSidx/hU7 = **pair-linkage** (M-seeded mp: mp.Kstar = hyp.typeP.W1 literal、
    dataS.W2 = mp.Kstar pin (tp.Sdata_W2_eq 系)、|mp.K| = w₂ の同定は
    K_eq + M-side centralizer_W1 の reconcile — 要小組立)。
- **次 = S12_Noncoherence.lean** (pair leaf import の新 leaf): 供給組立 →
  無条件 S_not_coherent-v2。その際 (13.2.a)-circle (Phase 1a) に注意 —
  v2 の証明が K_lt_Kstar 系を経由しないよう M-seeded route の clean 部分のみ使う。

## 2026-07-11 tick¹⁰ — pair-linkage 核 landed + 移行 cascade の精密化

- `typePData_Msigma_inf_centralizer_W1_eq_W2` (K = W₂ literal 同定、axiom-clean、a2ff7e87)。
- **⚠ v2 組立の taint 分析 (実装前に確定)**: 現 M-seeded mp-producer で v2 を組むと
  K_lt_Kstar fill → (13.2.a) → **no_typeV_maximal 依存**が v2 に入る ⟹
  no_typeV_maximal 自身は v2 へ migrate 不能 (依存順)。⟹ **Phase 1a (Core-split、
  K_lt_Kstar-free M-seeded producer) は v2 の前提**であって後回し不可。
- **(11.3) 消費者も上流**: S_H0C_not_coherent (S13_Lemmas113To115) は FTS 上流 →
  v2 直 cite 不能。(11.8)-capstone 側の migration も Phase 3 後半に含む
  (capstone chain の discharge 位置を pair-leaf 下流へ)。
- 順序確定: **Phase 1a → v2 (S12_Noncoherence) → (10.10)-v2 → FTS (13.2.a)-trio
  relayer + S15/S16 repoint (hub 調整) → (11.3)/(11.8) 側 migration**。

## 2026-07-11 tick¹¹ — Phase 1a 前半完了 (切断点 landed)

- **Section16MaximalPairCore split** (0e5a0bb1): K_lt_Kstar を extends 層へ、
  下流 (pair leaves / S15 / S16 / FeitThompson) 全て無変更 green。
- **exists_section16MaximalPairCore_around axiom-clean 実測** — M-seeded pair が
  (13.2.a) なしで構成可能に。消費面測定: pair chain の mp-投影は全て Core fields
  (K_lt_Kstar 投影ゼロ、tp 使用は around 系のみ)。
- 残: chain retarget (seeded/reconcile/at_pair/(10.7)' の binder を Core へ +
  isCyclic_K/Kstar Core 版) → (10.7)' taint 再測 → v2 組立へ。

## 2026-07-11 tick¹² — ★★★ Phase 1a 完了: (10.7)' が完全 axiom-clean

chain retarget (5d8bc991) で `typeII_HU_frobenius_of_coherent'` の sorryAx が消滅
([propext, Classical.choice, Quot.sound] 実測)。(13.2.a) 循環は切断され、書籍 DAG
((10.7) ⊥ (13.2.a)) が repo で回復。下流 (FTS/S15/S16/FeitThompson) 無変更 green。

**次 = v2 組立 (S12_Noncoherence.lean、全部品 clean)**:
Core_around (mp.Kstar = hyp.typeP.W1 literal) + K = W₂ 同定
(typePData_Msigma_inf_centralizer_W1_eq_W2 → mp.K = hyp.typeP.W2 literal) +
reconcile (dataS.W1 = mp.K / W2 = mp.Kstar) + (10.7)'-kernel 橋 (hfrobcap) +
(8.11)/(8.6.a)/w2_prime/hall_coprime → S_not_coherent_of_partner 適用。
