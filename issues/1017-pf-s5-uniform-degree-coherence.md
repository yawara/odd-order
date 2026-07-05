---
id: 1017
slug: pf-s5-uniform-degree-coherence
title: "Pf §5 uniform_degree_coherence + subcoherence — (10.7)/(10.8)/typeII の欠落 prereq"
created: 2026-07-05
---

# Pf §5 uniform_degree_coherence + subcoherence — (10.7)/(10.8)/typeII の欠落 prereq

> **hub 調整依頼 (shared coherence infra)**。lane-a group-theory + gate-1 完遂後、char endgame の
> 最上流 (10.8) `typeII_coherence_contradiction_estimate` を subagent 精査 (2026-07-05) →
> **§5 coherence 不在で BLOCKED** と確定。coherence infra は lane-b carve-out (S07) だが本体不在ゆえ
> 帰属/着手を hub 裁定。詳細 = `notes/peterfalvi/s13_11_8_orthogonality.md` update²⁴。

## 背景 (subagent 精査、確定)

char endgame の (10.8) `typeII_coherence_contradiction_estimate` (S12_MaximalIII_IV_V:453) =
Coq `FTtype345_noncoherence_main` (PFsection10.v:668-815)、2-sided pincer
`1−1/w₁−1/|U| < w₁w₂/|M'|`:
- **line-87 side (7.8.b)**: **assemblable** — `hypothesis78OfDade` (S09_CertificateDischarge:1637)
  + `zetaNuRhoNormSqGeOfDade` (:2406) + `card_derived_ge` proven。
- **hB side (10.7)**: **BLOCKED** — `typeII_derived_frobenius` (S12:47) 自身 sorry、root cause =
  **§5 の欠落**:
  - **`uniform_degree_coherence`** (Pf §5.x: uniform-degree seqInd family は coherent) — **不在**。
  - **`subcoherent` / `FTtypeP_subcoherent` R-datum** (Pf §5.x subcoherence) — **不在**。
  - `IsTypeF (derivedInG S)` → 完全 `[S,S]=H⋊U` Frobenius factorization の upgrade
    (`TypeIIData` は `derived_typeF` のみ、`TypeFData.frobenius_HU0` は `H⊔U₀` (U₀ exponent-proxy)
    止まりで (10.7) の完全 factorization 無)。

**★ 従来 notes の誤診断訂正**: (10.7)/hB は「§9-blocked (Section11CharacterData 未構成)」ではない
— `mkSection11CharacterData` (S12_Section9Counts:57) で構成済、Coq `Frob_der1_type2` (10.7) は §9
counts 不使用 (4-elt uniform family T2 の `uniform_degree_coherence` で local partner coherence 構築)。

## やること

- [ ] **§5 `uniform_degree_coherence`** 実装 (Pf §5.x、Dade isometry/coherence 基盤上、Coq
      PFsection5 の `uniform_degree_coherence` 対応)。
- [ ] **§5 `subcoherent` / `FTtypeP_subcoherent` R-datum** 実装 (Coq PFsection5 subcoherence)。
- [ ] 上を用いて (10.7) `typeII_derived_frobenius` (S12:47) を証明 (Coq `Frob_der1_type2`,
      PFsection10.v:549-658 mirror)。
- [ ] (8.8) enrich: `exists_typeII_maximal_with_w2` を M↔S partner counts (|H|/|S|/|V|/|W|,
      S_F#-TI) を出す形に強化 (`ub_G1` 用)。
- [ ] ⟹ (10.8) `typeII_coherence_contradiction_estimate` を close (line-87 assemblable + hB)。

## 完了条件

`typeII_coherence_contradiction_estimate` の sorry が消える (⟹ (10.8) S_not_coherent の char gate
解消 → (11.5)/(11.7)/gate-1 の char-gating + exists_zeta の一 dep 解消)。

## 参照

- notes/peterfalvi/s13_11_8_orthogonality.md update²⁴ (精査全文)、s12_10_8_noncoherence.md
- Coq: PFsection10.v:668-815 (FTtype345_noncoherence_main)、549-658 (Frob_der1_type2)、
  PFsection5.v (uniform_degree_coherence, subcoherent)
- stale docstring 修正候補: S12_Core:2836 (`exists_typeII_maximal_with_w2_of_typeP` は proven,
  「sorry」記述 stale)。
