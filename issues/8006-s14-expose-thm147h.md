---
id: 8006
slug: s14-expose-thm147h
title: "Lane H: typeP_duality に Thm 14.7(h) (M=KM', K∩M'=1) 露出要請 (Lane G §15 cascade gate)"
created: 2026-06-15
---

# Lane H: typeP_duality に Thm 14.7(h) (M=KM', K∩M'=1) 露出要請

## 背景 (cross-lane interface request: G → H)

Lane G が §14 interface 上で BG §15 cascade（Cor 15.6 / Lemma 15.1）を組もうとして判明した
**interface gap**。BG Cor 15.6 の証明 (mmd L4232) は冒頭で

> By Theorem 14.7(h), `M = KM'` and `K ∩ M' = 1`. Therefore, by Lemma 6.3, `K* ⊆ M''`.

を使う。すなわち **Thm 14.7(h) の `M = KM', K∩M'=1`** が Cor 15.6 conjunct 4 (`K*⊆M''`) と
Lemma 15.1(a)(b) の両方に必須。しかし現 `typeP_duality` (S14_TypePCounting.lean:531) の結論は
`∃! Mstar, … ∧ IsCyclic(K⊔Kstar) ∧ IsTISubset(zTilde) ∧ (P2 M ∨ P2 Mstar) ∧ 共役被覆` で、
**(h) `M=KM', K∩M'=1` を露出していない**。

**workaround も塞がれている**: Lane G の Lemma 15.1 K≠⊥ 節は既に `IsComplement' (M') K` を露出済だが、
それを発火させる `K ≠ ⊥` を type-P から導けない。`IsTypeP M = (kappa M).Nonempty` だが
**raw `kappa M` は合成数を含みうる**（`pRank M 4 = 1` が `ℤ/2×ℤ/2` で成立しうる等; §14 コードは
κ/τ 使用時に常に `[Fact p.Prime]` を明示仮定している）。ゆえ `p∈κ → p.Prime → p∣|K|` の素直な
導出が不可能。これは §12/§14 の κ/τ prime-性ハンドリング（Lane F/H 領域）であり、Lane G が
re-derive すべきでない。

## やること (Lane H)

- [ ] `typeP_duality` (Thm 14.7) の結論に **(h)** を追加（Cor 15.6/Lemma 15.1 が直接 cite できる形で）:
  ```
  Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧   -- M = K M'
  Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M))
  ```
  coprime は `K∩M'=1` + κ/κ' Hall から従う; Lane G の engine
  `Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` がこの 2 つを仮説に取る。
- [ ] **代替**: §14 内で `IsTypeP M → IsHallSubgroup (kappa M) (K.subgroupOf M) → K ≠ ⊥`
  を提供（Lane G の Lemma 15.1 K≠⊥ 節を発火させられる）。**ただし (h) 直接露出の方が
  Lemma 15.1 も同時に unblock するので望ましい。**

## 完了条件

`typeP_duality`（または同等の §14 interface 補題）が type-P `M` に対し `M=KM'`/`K∩M'=1`/coprime を
露出し、Lane G の Cor 15.6 conjunct 4 が `Msigma_inf_centralizer_le_derivedDerived_of_isComplement'`
への単一 cite で閉じる。

## 参照

- Lane G 側準備済: `S15_MF.typeP_kstar_in_mf_of_inputs` (skeleton, hcompl/hcop を仮説に取る)、
  `Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` (conjunct-4 engine)、
  Lemma 15.1 K≠⊥ 節の `IsComplement'`+coprime 露出、Cor 15.5 の hFcyc 露出 (`08e7dc5c`)。
- mmd: `references/bg/local-analysis.mmd` Cor 15.6=L4228 (証明 L4232)、Thm 14.7=L3890。
- gap 分析: `notes/bg/s15_16_audit.md` §9（Cor 15.6 cite map）。
