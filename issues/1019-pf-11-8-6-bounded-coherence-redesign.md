---
id: 1019
slug: pf-11-8-6-bounded-coherence-redesign
title: "Pf (11.8.6): uniform-degree 設計 over-strong (非Galoisで偽) → bounded_seqIndD_coherence redesign"
created: 2026-07-07
---

# Pf (11.8.6): uniform-degree 設計 over-strong (非Galoisで偽) → bounded_seqIndD_coherence redesign

## 背景 (lane-a, 2026-07-07 code-level 確証)

(11.8.6) capstone `Hypothesis.coherent_Sset_of_column_identities` (S12_MaximalIII_IV_V.lean) の
`hgen` bullet は `hgen_of_S2_uniform_degree` + `Sset_diff_SHCSet_apply_one_eq_qu`
(= `∀ y ∈ Sset\SHCSet, y 1 = qu`、`Sset = inducedFamily M`) に依存する。
この **uniform-degree qu 主張 (irr-side, S12:3915 の sorry) は非Galois type III/IV で偽**。

### 偽である code-level 確証 (Coq 精読)
- **Coq (9.8) `typeP_nonGalois_characters` (PFsection9.v:845-855)**: 非Galois では
  `a := |U : C_U(x)|` かつ **`a > 1`** (L855 `a_gt1`)。(d) `irr_qa := [zeta∈irr M | zeta 1 == (q·a)]`
  の count ≥ `(p-1)|U| / (a²|U'|)` ≥ 1 ⟹ **degree `q·a` (a>1, ≠ w₁, generically ≠ u) の irreducible が
  `S_H0U' ⊆ inducedFamily` に存在**。
- これらは `inducedFamily M`-member (`Ind_{M'} θ`, θ deg a, θ≠1)、degree `qa ≠ w₁` ⟹ `∉ SHCSet` ⟹
  `∈ Sset\SHCSet`、degree `qa ≠ qu`。∴ `∀ y ∈ Sset\SHCSet, y 1 = qu` の**反例**。
- **Coq (9.9) `typeP_Galois_characters` (PFsection9.v:1258-1264)**: Galois では X_H0C' は degree ちょうど
  `u` (qa なし) ⟹ uniform-qu は **Galois 限定で真**。type III/IV は非Galois もあり得る
  (PFsection11.v:428 `gal'M : ~~ typeP_Galois`)。

### 正しい機構 = `bounded_seqIndD_coherence` (Pf (6.x))
Coq (11.3) `FTtype34_noncoherence` (PFsection11.v:206-223) は uniform-degree を**使わない**:
`coherent(S_H0C) --[bounded_seqIndD_coherence]--> coherent(S_1) --[(10.8) 矛盾]`。
`bounded_seqIndD_coherence` (PFsection6.v:115): `M<|L,H<|L,H1<|L` + `M⊆H1⊆H⊆K` + `nilpotent(H/M)` +
`coherent(S H1)` + `|H:H1| > 4|L:K|²+1` ⟹ `coherent(S M)`。小さい族 S_H0C の coherence を
**nilpotency + size bound** で大きい族 S_1 (= inducedFamily) に拡張 (degree 均一性は不要)。

## やること (redesign、lane-a 次 iteration)

- [ ] `bounded_seqIndD_coherence` (Pf (6.x)) の repo 状態確認。土台 = S08_CoherenceCorePart2 の
      (6.7)/(6.8) degree-sum bound (`∑χ(1)² ≤ 2a`、`:2815`/`:3339`/`:3399`)。未 port なら port。
- [ ] `coherent_Sset_diff_SHCSet` (S12:4044 sorry) を **S(C) / S_H0C** (C-kernel 付き狭い族) に narrow
      (現 inducedFamily\SHCSet は広すぎ = qa を含む)。
- [ ] capstone を bounded-coherence route に redesign: S_H0C coherence → `bounded_seqIndD_coherence` で
      inducedFamily coherence。`hgen_of_S2_uniform_degree` / `Sset_diff_SHCSet_apply_one_eq_qu`
      (Galois 限定でしか真でない) を置換。

## 保全 (redesign 後も再利用する landed 成果)

- `exists_muGrid_column_eq_of_inducedFamily_reducible` (commit 0969af79、axiom-clean): reducible
  `inducedFamily`-member = nonzero μ-column ∈ sOf H0。**正しい定理** (μ-column は genuinely deg qu)。
- `inducedFamily_reducible_apply_one_eq_qu` (同 commit、sorry-free): reducible → deg qu。真。
- ψ₀ column witness (commit 18344eb5): μ-column ∈ Sset\SHCSet ∈ D。真。
- `SHC_isCoherent` / union-glue API 等の S₁ coherence 基盤。

## 完了条件

`card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson の唯一 bare sorry) が honest に close される
capstone を bounded-coherence route で構築 (uniform-degree の偽 sorry を排除)。

## 参照

- notes/peterfalvi/s13_11_8_orthogonality.md update³⁷
- Coq: PFsection9.v:845 (9.8), :1258 (9.9); PFsection11.v:206 (11.3); PFsection6.v:115 (bounded coherence)
- S12_MaximalIII_IV_V.lean: `Sset_diff_SHCSet_apply_one_eq_qu` (:3904 irr-side sorry),
  `coherent_Sset_of_column_identities` (:4188 capstone), `hgen_of_S2_uniform_degree` (:4098)
