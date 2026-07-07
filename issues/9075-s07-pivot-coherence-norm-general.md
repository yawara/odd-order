---
id: 9075
slug: s07-pivot-coherence-norm-general
title: "S07 (5.7) norm-general uniform coherence: pivot_coherence port (lane-a claim)"
created: 2026-07-08
---

# S07 (5.7) norm-general uniform coherence: pivot_coherence port (lane-a claim)

## claim (lane-a, 2026-07-08)

**lane a が build する** (caseB (9.11) の唯一の残 gap を閉じる shared S07 infra)。
重複防止のための claim。b の caseA (S11_NineElevenCoherence) は irr-only 版
(`coherent_subset_of_constant_degree`, landed) + weighted adjoin を使う設計で非衝突
(base S1 = deg-qa 既約)。

## 背景 (発見 2026-07-08, 1019 update⁸⁵)

- Coq (9.11) `Ptype_core_coherence` の **Galois(=caseB) 枝は
  `apply: uniform_degree_coherence scohS0` — 家族 𝒮(H₀C′) 全体 (可約 μ 込み) に一発**
  (PFsection9.v:1510-1513)。count・pair-chain・anchor 不要。
- Coq `uniform_degree_coherence` (PFsection5.v:1234) は **norm N 一般**
  (N = ⟨χ₁,χ₁⟩、R-datum size 2N、:1256-1264)。
- Lean 港 `coherent_of_constant_degree` / `coherent_subset_of_constant_degree` は
  **norm-1 (irr) 限定** (`hirr : ⟨ζ,ζ⟩ = 1`) — 制限 port。
- ⟹ lane-a の caseB fold が要求する **hDeg (2 < |irr-cut|) は route 人工物**
  (Coq/教科書が証明しない count; |cut| = 2 corner で偽の恐れ)。§9 count で埋めるのは誤り。
  正 = norm-general (5.7) を port して全族適用。

## やること

1. **`pivotCoherence`** (Coq `pivot_coherence` PFsection5.v:588 の S07 版):
   pairwise-orthogonal S + pivot η₁ ∈ S + ζ₁ ∈ ℤ[Irr G] + (∀ η ∈ S∖{η₁}: η(1) = η₁(1)
   [uniform 特化 a≡1] ∧ ⟨τ(η−η₁), ζ₁⟩ = −⟨η₁,η₁⟩) + ⟨ζ₁,ζ₁⟩ = ⟨η₁,η₁⟩ → IsCoherent。
   **明示式で構成** (基底 freeness 不要): `ν φ := s(φ) • ζ₁ + τ(φ − s(φ) • η₁)`、
   `s(φ) := ∑ᵢ ⟨φ,ηᵢ⟩/Nᵢ` (pairwise 直交で ℤ[S] 上 ℤ-値 = 係数和)。
   - extends: φ ∈ ℤ[S,A] → φ(1)=0 → s(φ)=0 → νφ = τφ (即)。
   - inner_eq: 展開 + pivot 条件 + supported-span isometry。
   - ZIrr: ζ₁ ∈ ℤ[Irr G] + hZIrr (τ(a−b) ∈ ℤ[Irr G])。
2. **(5.7) norm-general 版** `coherent_of_constant_degree_normGeneral`:
   ζ₁ の構成 (Coq :1265-1330 haveX = subcoherent_split/norm (5.4) minimality、
   X = R(χ₁) の半分和、⟨X⟩=N、XDspec ∀ξ ⟨X, τ(χ₁−ξ)⟩=N)。
   degenerate case S = {χ₁,χ̄₁}: X := take N (R χ₁)。
3. caseB 適用: 𝒮(H₀C′) 全体 (hunif [landed] + pairwise-orthogonal
   [inducedKernelFamily_pairwise_orthogonal] + conj-closed [sOf_closedUnderConjugate] +
   no-real [odd] + R-datum [S06.certainTypeR (μ) / Dade decomposition (irr)]) →
   `caseB_coherent_sOf_H0Cprime` を rewire (hDeg 引数を撤去)。

## 完了条件

caseB (9.11) `caseB_coherent_sOf_H0Cprime` が hDeg 無しで閉じ、fold 版は下流互換のため
残置 or 撤去 (assembly 差し替え)。#print axioms で §13 core gate 以外 sorry-free。

## 参照

- issues/1019 update⁸⁵ / Coq PFsection5.v:588 (pivot), :1234 (5.7), :863/:881 ((5.4))
- PFsection9.v:1510-1513 (Galois 枝)
