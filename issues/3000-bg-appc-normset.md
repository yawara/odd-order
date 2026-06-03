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
- [~] **Lemma C.2 (q=3)**: 前半 ✅ (2026-06-04 commits 6f5324d/793d0ec): `exists_rootFree_cubic`
  (pigeonhole ∃c 無根) + `fCubic`/`fCubic_natDegree`(=3)/`fCubic_irreducible`。**残**: 持ち上げ
  (AdjoinRoot で root∈F_{p³} + Frobenius 軌道因数分解 + normN=-fCubic(0)/fCubic(2)) ~200行。詳細=plan note 「残作業 breakdown (A)」。
- [ ] **Lemma C.2 (q≥5)**: Frobenius 群 H=P⋊U の指標論 (構造定数 e=|E|, 直交関係で下界)。別 infra・重。
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
