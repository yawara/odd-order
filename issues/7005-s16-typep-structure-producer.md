---
id: 7005
slug: s16-typep-structure-producer
title: "Section16Inputs: section16TypePStructure producer (BG §14, lane-f)"
created: 2026-06-18
---

# Section16Inputs: section16TypePStructure producer (BG §14, lane-f)

## 背景

2026-06-18 post-§14 監査で判明した真の long pole = `Section16Inputs` producer の分配
(skeleton commit `80f9aa39`)。本 issue は BG §14 type-P duality 担当ブロック。
**`typeP_duality` は既に proved** (`S14_TypePCounting.lean:7961`, sorry-free + axiom-clean)
ゆえ、本 producer はその proved 定理を cite して構成できる見込み = 良い lead-in。

## やること

- [ ] `section16TypePStructure_of_isMinimalSimpleOdd hG mp : Section16TypePStructure mp`
      (`OddOrder/FeitThompson.lean:272`, 現 `sorry`) を実証明化する。
- [ ] 入力 = 極大対 `mp : Section16MaximalPair G` (lane-g が構成)。
- [ ] 内容 = 型 P 双対構造: `W1 W2 W U V : Subgroup G`、`W = mp.S ⊓ mp.T = W1 ⊔ W2` cyclic、
      `W1 ⊓ W2 = ⊥`、`W1`/`W2` の可換性、導来部分群分解 `S_deriv_eq_PU`/`T_deriv_eq_QV`、
      `W1`/`W2` の正規化条件、素数 `q p` と counting params `u v c d` + 位数等式 + `q_lt_p`。
- [ ] feeder = BG §14 `typeP_duality` (`S14_TypePCounting.lean:7961`) — W cyclic, W₁/W₂,
      補 U/V, counting を供給。`q_lt_p` は (14.1) 由来。

## 完了条件

`section16TypePStructure_of_isMinimalSimpleOdd` の `sorry` が消え、`lake build OddOrder` 緑。

## 進捗 (2026-06-18 lane-f, 後刻) — ✅ 逆包含 (gap B) landing 完了

hub REASSIGN #2 (option 1「難所に正面」) を受け、**逆包含 `M ⊓ Mstar ≤ K ⊔ Kstar`
(= BG Thm 14.7(4) / Thm C(6) / Thm I(2) の `S ∩ T = W`) を完全形式化**
(`aa177257`, sorry-free + axiom-clean, AxiomsCheck 登録済):

- 新 leaf `OddOrder/BG/Ch4_FamilyOfMaximal/S16_PairIntersection.lean`、定理
  `OddOrder.BG.Ch4.S16.typeP_pair_inf_eq : M ⊓ Mstar = K ⊔ Kstar`。
- canonical packaging (typeP_duality の `∃!` 出力 = `Mstar` maximal/type-P/non-conj、
  `Kstar ≤ Mstar`、`Kstar` Hall κ(Mstar)、`K = Msigma Mstar ⊓ C(Kstar)`、`IsCyclic Z`) を
  そのまま入力に取る → consumer から直接呼べる。
- 証明 = mmd L4063 (Thm 14.7 end-of-proof): Step1 `Msigma M ⊓ Mstar = Kstar`
  (σ-decomposition: `⁅W,K⁆ ⊆ Msigma M ⊓ Msigma Mstar = ⊥`) + Step2 (Prop 14.2(b1) +
  cyclic Kstar の characteristic line `X*`)。
- **caveat 回避確認**: prerequisite (Prop 14.2(b1)/(f)、Thm 13.9、typeP_self_member、
  eq_of_card_eq_prime_of_le_isCyclic) は全て既形式化。未形式化 §16 theory (Prop 16.1 等)
  には bottom-out しなかった。

**残 (gap A = lane-g/hub 領域)**: 元の型欠陥は未解消。`Section16MaximalPair` は依然 partner を
共役までしか固定せず、producer `section16TypePStructure_of_isMinimalSimpleOdd` は本補題が
あっても**まだ discharge できない**。次手 = lane-g が `Section16MaximalPair` を本補題で enrich
(W=S∩T cyclic + dichotomy clause 復活) → そこで初めて typeP producer が discharge 可能。

---

## 調査結果 (2026-06-18 lane-f) — ⚠ 現仕様では sorry-free 化が原理的に不可能

精査の結果、**前提「proved `typeP_duality` を cite すれば構成可」は不正確**で、producer は
`Section16MaximalPair` の現定義のもとでは sorry-free 化できない。3 点で検証済み:

1. **病的 mp が `Section16MaximalPair` 公理を満たす（partner が共役までしか固定されない）**:
   covering 条件 `theorem88_caseB` は「各極大は type-I か S か T に**共役**」としか言わない。
   真の partner を `Mstar`、`T' := Mstar^g`（非自明な共役）とすると `T'` も全公理を満たす:
   maximal ✓ / `T' ≠ S` ✓ / `IsTypeNonI T'`（type-P は共役不変）✓ /
   `one_typeII`（`IsTypeP2 Mstar → IsTypeII Mstar` が共役不変）✓ /
   `theorem88_caseB`（共役類は同じ）✓。しかし `mp.S ⊓ T' = S ⊓ Mstar^g` は一般に位数 `qp`
   の cyclic ではない ⟹ 強制された `W = mp.S ⊓ mp.T` が `W_cyclic` + `W_eq_join`(q<p の素数 2 個)
   を満たせない。**∴ producer の出力型は入力公理より真に強く、証明不能**。

2. **gap B（逆包含 = `W = S ∩ T`）が repo に未形式化**: `typeP_duality` は forward
   `K ⊔ Kstar ≤ M ⊓ Mstar` のみ供給（`K ≤ M`, `Kstar ≤ Msigma M ≤ M`, かつ `K ⊔ Kstar ≤ Mstar`
   = S14:4616/6910）。逆 `M ⊓ Mstar ≤ K ⊔ Kstar`（= `W = S ∩ T`）は**どこにも無い**。
   近い `typeP_normalizer_inf_eq`(S14:4684) は `N_G(X) ⊓ M = K ⊔ Kstar` で別物。

3. **`W = W₁ × W₂ = S ∩ T` は Peterfalvi (13.1) の standing hypothesis**
   (`references/peterfalvi/04.15…The_Subgroups_S_and_T.mmd:5`、"Taking (12.17) into account"):
   対 (S,T) の存在と交差構造は **BG §8 (8.8.b) + §10-13 の構造定理の出力**であり、
   `Section16MaximalPair.theorem88_caseB` は (8.8.b) の **covering disjunction のみ**を捉え、
   W=S∩T cyclic 構造・`S=(P⋊U)⋊W₁` 分解・normalizer 条件を**落としている**。

**根本原因**: skeleton split (`80f9aa39`) が `Section16MaximalPair` を (8.8.b) の covering 部分
だけで定義し、構造部分（W=S∩T cyclic, U/V 分解, normalizer）を tp 側に置いたが、tp は mp から
それを**復元できない**（情報が構造境界で失われる）。`derived_decomposition`
(`derivedInG_eq_Msigma_sup_derivedInG_complement` S14:7720) と counting (Lagrange) は available
だが、W=S∩T が無い限り U/V を pin できず連鎖して全 field が落ちる。

**選択肢**（hub 判断）:
- (A) `Section16MaximalPair` を (8.8.b) の構造出力（W=S∩T cyclic + 分解 + normalizer）まで richen
  → 義務は mp producer (lane-g) に移動（やはり §8/§13 構造論の形式化が必要、総量不変）。
- (B) mp+tp を 1 producer に再統合し pairing witness を内部保持（W=S∩T を内部で構成）。
- (C) tp を honest localized sorry のまま据え置き（gated-endpoint-skeleton の趣旨どおり）、
  lane-f を真に unblocked なタスクへ re-task。
- (D) lane-f が gap B の逆包含 `M ⊓ M* ≤ K ⊔ K*`（§8/§13 構造論）を新 leaf で正面形式化
  — 但し gap A（pinning）は残り、単独では producer を discharge しない。

## 参照

- skeleton commit `80f9aa39`、`OddOrder/FeitThompson.lean:196` (`structure Section16TypePStructure mp`),
  `:272` (producer)
- 既証明 input: `OddOrder.BG.Ch4.S14.typeP_duality` (`S14_TypePCounting.lean:7961`)
- 病的 mp の典拠: `S16_MainResults.lean:1014-1050` (Theorem I で S=非I極大→typeP→partner Mstar 構成)
- standing hypothesis: `references/peterfalvi/04.15_pp_75_86_The_Subgroups_S_and_T.mmd:5` ((13.1)(a)(b))
- 関連: 8014 (maximalPair, lane-g, 上流) / 1004 (character_data, lane-b, 下流) / 2009 (POLE-2, lane-h)
- 旧タスク Wielandt (9.1) `CoprimeAction.lean` は orphaned 判定で park (issue 7004 は据え置き)
