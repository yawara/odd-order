---
id: 3000
slug: bg-appc-normset
title: "BG Appendix C: finite-field norm-set argument (Lemmas C.1-C.3, Theorem C)"
created: 2026-06-04
---

# BG Appendix C: finite-field norm-set argument (Lemmas C.1-C.3, Theorem C)

## 背景

下流監査 (`notes/meta/s16_appc_downstream_audit_2026_06_04.md`) で、`feitThompson` 最終矛盾 (`nonexistence_of_G`)
が消費する 2 gap のうち **`AppC.theoremC : FieldNormalizerData → p ≤ q`** が唯一の実質的下流ターゲットと特定。
これは BG Appendix C (mmd L4855-5005) の有限体 norm-set 論法 (Lemmas C.1-C.3)。BG §7-16 / Pf §10-16 と非交差で
進められる。実装計画 = `notes/bg/appC_normset_plan.md`。

## やること

実装先 `OddOrder/BG/AppC_NormSet.lean` (namespace `OddOrder.BG.AppC.NormSet`, mathlib-only leaf)。
実 `GaloisField p q = 𝔽_{p^q}` 上で norm `N(x)=∏_{i<q}x^{p^i}` と `E={a|N(a)=N(2-a)=1}` を materialize。

- [x] 基盤: `normN` / `normSetE` 定義 + **Remark (I)** `conditionA_iff_not_dvd` (条件A ⟺ q∤(p-1), axiom-clean, AxiomsCheck 登録) — 2026-06-04 commit
- [x] **Lemma C.1** `lemmaC1` (E=E⁻¹ ∧ |E|≥2 ⟹ p≤q) — **完成・sorry-free・axiom-clean・AxiomsCheck 登録** (2026-06-04 commit 32ae2f4)。τ-反復 `tauIter`/`dSeq`/`normN_dSeq_eq_one` (telescoping) + `natCast_pow_pPow` + degree-q Frobenius 多項式根数 (`natDegree_prod`/`card_roots'`/`CharP.natCast_injOn_Iio`)。
- [x] **Lemma C.2 (q=3)** — **完成** (2026-06-04 commit 5268ce0, sorry-free, axiom-clean, AxiomsCheck 登録):
  `exists_mem_normSetE_three` (∃a∈𝔽_{p³}, N(a)=N(2-a)=1 ∧ a≠1) + lemmaC2 q=3 分岐配線。
  pigeonhole → 既約 → root∈𝔽_{p³} (AdjoinRoot iso) → Frobenius 軌道 {a,aᵖ,aᵖ²} 相異 (root∉𝔽_p +
  Frobenius 固定点=𝔽_p) → fCubic.map=∏(X-a^{p^i}) (roots multiset 同定) → eval 0/2 で normN 読み取り。
  helpers: `aeval_pow_p`/`exists_root_fCubic`/`root_not_mem_range`/`mem_range_of_pow_p_eq_self`/`fCubic_monic`/`normN_three`。
- [x] **Remark (VII)** norm-one subgroup `U`: `normN` と `Algebra.norm` の bridge
  `normN_eq_algebraMap_norm`、`normOneUnits`、`mem_normOneUnits_iff_normN`、
  `normOneUnits_card : |U| = (p^q - 1)/(p - 1)` を追加し、AxiomsCheck 登録。
- [x] **C.2 structure-constant bridge**: `normOnePairSet` と
  `normOnePairSet_ncard_eq_normSetE_ncard` を追加。`|E|` を `u+v=2` を満たす
  norm-one unit pairs の個数として同一視し、q≥5 の Frobenius 群 class-sum 計算への入口を materialize。
- [ ] **Lemma C.2 (q≥5)**: Frobenius 群 H=P⋊U の指標論 (構造定数 e=|E|, 直交関係で下界)。**別 infra・重 (multi-session)**。
- [ ] **Lemma C.3** (E=E⁻¹): 群論的 generator-relation (Step1-4)。仮説(B)=群G埋め込み必須 ⟹ FieldNormalizerData materialize と共有 (半上流)。
- [ ] **Theorem C** assembly + 既存 scaffold `AppC.theoremC` への配線 (FieldNormalizerData.field_model materialize)。

## 完了条件

`AppC.theoremC` が sorry-free (Lemmas C.1-C.3 + 配線完成)。`nonexistence_of_G` の BG 側 gap が閉じる。
段階的に C.1 → C.2(q=3) → C.2(q≥5) → C.3 → assembly。

## 参照

- 計画: `notes/bg/appC_normset_plan.md`
- 監査: `notes/meta/s16_appc_downstream_audit_2026_06_04.md`
- 原典: BG mmd `references/bg/local-analysis.mmd` L4855-5005
- 既存 scaffold: `OddOrder/BG/AppC_FinalContradiction.lean` (theoremC/NormSetData/HypothesisB, opaque)
