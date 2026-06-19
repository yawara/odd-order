# Pf (13.17) 構造論プログラム — 方針① (lane-h, 2026-06-19)

> POLE-2 (`field_normalizer_structure`) は `exists_LHypothesis` 経由で Pf **(13.17)**
> `typeII_overNormalizer_frobenius` を cite する。(13.17) は gated-endpoint skeleton 化済
> (`0d99daf1`): `sorry`-free assembly が (12.7) `S14.typeI_frobenius` を cite + 2 faithful
> obligation に分離。本プログラム = その 2 obligation を**深い §13 構造論**で埋める計画。
> 正本 issue = `issues/pending/2009-s16-field-normalizer-pole2.md`。

## ゴールと分担原則

(13.17) の 2 obligation を「H 単独の構造論 + 既存 infra cite + sorried §13 producer cite
(安定 signature) + 新規 reusable 形式化」で証明する。**char/Dade 本体 (basic_structure の
char fields 等) は Lane B 領域**で、cite はするが unconditional 化は B 待ち。

## 検証済み infra (cite 可、再導出不要)

- **SZ 補元共役**: `OddOrder.Isaacs.Ch03.exists_conj_le_of_isComplement'_of_coprime`
  (Main:1223) — 正規部分群 + 補元 + coprime ⟹ 補元は共役。
- **normalizer 同変性**: repo `normalizer_conj_smul` (S12_ExceptionalBridge:266) + mathlib
  `Subgroup.map_normalizer_eq_of_bijective`。
- **maxNNH 同変性**: `maxNilpotentNormalHall_pointwise_smul` (本セッション landing, axiom-clean)。
- **coprime→disjoint**: `IsPGroup.le_or_disjoint_of_coprime` (P は p-群)。
- **type-data**: `TypePData.derived_complement` (P ⊓ typeP.U = ⊥ in derived) +
  `TypePNontrivialCore` (typeP.U ≠ ⊥) + `M_complement` (W1 が derived を補完)。
- **Frobenius 機構**: Isaacs Ch06 `FrobeniusGroup` / `FrobeniusActionTI`。

## crux base = hyp.U coherence (Phase 0)

**問題**: Hypothesis は `hyp.U` を `S_deriv_eq_PU : derivedInG S = P ⊔ U` (**join のみ**) で制約し、
complement (`P ⊓ U = ⊥`) も S の type-data `typeP.U` との一致も pin しない。一方 obligation ① の
L~S 除外は `¬ N_G(hyp.U) ≤ S` (type-II 性) を要し、`IsTypeII.normalizer_not_le` は `typeP.U` についてのみ。
`typeP.U` は complement・≠⊥ (上記 type-data) だが `hyp.U` がそれに pin されていない (under-constraint)。

**解決オプション**:
- (a) `P ⊓ hyp.U = ⊥` を §13 card 論で導出: `|derivedInG S| = |P|·|U| = p^q·u·c` を示す → join + card 一致
  で disjoint。要 §13 card 事実 (basic_structure |P|=p^q cite + |derivedInG S| の評価)。深いが H 可能性あり。
- (b) **Hypothesis faithfulness enrich** (F と協調): `hyp.U` を complement に pin
  (`P ⊓ U = ⊥` or `(IsTypeII data).typeP.U = hyp.U` フィールド追加)。carrier 変更 = FeitThompson の
  `sectionSixteenHypothesis_of_inputs` producer 要対応 (F 領域)。faithful 改善。
- **次の一手** = (a) の feasibility 調査 (|derivedInG S| 評価が cite で出るか) → 不可なら (b) を F に提案。

## Phase 構成 (依存順)

### Phase 0 — hyp.U coherence (上記)。obligation ① の base。
### Phase 1 — coherence bridge (obligation ① の L~S 除外) [Phase 0 後]
hyp.U complement → SZ 共役 `hyp.U ~ typeP.U` (S 内, `exists_conj_le_of_isComplement'_of_coprime`)
→ normalizer 同変性 + `normalizer_not_le` で `¬ N_G(hyp.U) ≤ S`。
### Phase 2 — obligation ① `exists_typeI_maximal_overNormalizer_U` (13.17.a/b)
- C1 存在: `∃ maximal L ⊇ N_G(U)` (N_G(U)≠⊤ ← typeP.U≠⊥ coherence + G simple) = `Finite.exists_le_maximal`。
- C2 type-I: `hyp.theorem88_caseB L hLmax` trichotomy + Phase 1 (L~S 除外) + L~T 除外
  (|L_F|=q^p [T-side cite] → W₁⊆L_F → [U,W₁]=1, (13.2.a) UW₁ Frobenius 矛盾)。
- C3 U⊆L_F: (8.17.a) |L_F| coprime to q → W₁∩L_F=1; U∩L_F=1 なら UW₁ FPF → (9.1) 矛盾 [§8/§9 cite]。
### Phase 3 — Huppert [H] V.8.18 (H 単独・並列可・obligation ② を de-risk)
奇数位数 Frobenius complement ⟹ 素数位数部分群正規 (Z-群構造)。自己完結古典、Isaacs Ch06 Frobenius
機構から形式化。**repo 不在**ゆえ新規。reusable。
### Phase 4 — obligation ② `typeI_overNormalizer_complement` (13.17.c) [Phase 3 後]
complement E (⊇W₁) は odd Frobenius complement → Phase 3 で素数位数正規 → E⊆N_G(W₁)⊆QW₂ [(13.16) cite]
→ Sylow cyclic [BG 3.9 `S03g_Thm310`] → E=W₁ or |E|=pq=W₁W₂^y。W₁ 枝は (14.5) 除外。

## leaf 分類

| leaf | 種別 | 手段 |
|---|---|---|
| hyp.U coherence (P⊓U=⊥) | **crux base** | (a) §13 card 導出 or (b) F 協調 enrich |
| SZ bridge → ¬N_G(U)≤S | H 単独 | 既存 infra cite |
| ∃ maximal L⊇N_G(U) | H 単独 | exists_le_maximal |
| trichotomy glue → type-I | H 単独 | theorem88_caseB + rule-outs |
| Huppert [H] V.8.18 | H 単独・新規 | Isaacs Ch06 から形式化 |
| 補元 E 構造 (Phase 4) | H 単独 | Huppert + cite |
| \|P\|=p^q, (8.17.a), (9.1), \|L_F\|=q^p, (13.16) | cite sorried §13 | 安定 signature |
| basic_structure char fields 等 | **Lane B** | Dade 待ち (cite のみ) |

## 次の一手 (優先順)

1. **Phase 0 (a)**: `P ⊓ hyp.U = ⊥` の §13 card 導出 feasibility 調査 (`|derivedInG S|` 評価)。
   可なら Phase 1 へ直結。不可なら (b) を F に提案 (cross-lane)。
2. **Phase 3 (Huppert [H] V.8.18)**: Phase 0 と独立・H 単独で並行着手可。obligation ② を de-risk。
3. Phase 0 解決後 → Phase 1 → 2、Phase 3 後 → 4。
