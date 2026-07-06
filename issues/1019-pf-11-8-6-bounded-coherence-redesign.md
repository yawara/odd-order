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

## ✅ 検証 (2026-07-07、ユーザー「先に検証」要請、独立 3 角度で確定)

1. **★ smoking gun — Coq が uniform-degree を使わない**: `FTtypeP_subcoherent` 経由で
   **`scoh1 : subcoherent (S_ 1) tau R`** (PFsection11.v:104) — S_1 は **subcoherent** (Pf (5.x) の弱い構造)
   としてのみ扱われ、uniform-degree でも coherent でもない。(11.3) はそこから `bounded_seqIndD_coherence`
   で coherent(S_1) を導く。**(11.8)/(11.3) を type III/IV で形式化した本家 (Gonthier et al.) が
   uniform-degree を採らない** = それが type III/IV で成立しない決定的証拠 (成立するなら簡単なので使ったはず)。
2. **a ≠ u が genuine**: `u := |Ubar|` (PFsection9.v:203)、`a := |U : C_U(H1|'Q)|` (:331/:846) は別量。
   非Galois で `a > 1` (:855 `a_gt1`)。(9.8)(c) は degree-qu 既約、(9.8)(d) は degree-qa 既約 (a>1) を
   同時に与える (両方 `S_H0U'⊆inducedFamily`、両方 > w₁=q ゆえ ∉ SHCSet、qa≠qu) ⟹ S_1\SHC は非均一。
3. **Galois gating 無し**: Coq §11 の (11.3)/`scoh1` は無条件 (Galois 仮定なし; :428/:1139 の Galois 言及は
   別の structural 補題内)。repo (11.8) `Hypothesis` にも Galois field 無し。∴ `Sset_diff_SHCSet_apply_one_eq_qu`
   は無条件主張ゆえ非Galois で**無条件に偽**。(S12 の "Galois-equivariance" 言及は複素共役×τ の別概念、無関係。)

⟹ finding 確定。uniform-degree route は放棄し bounded-coherence route へ。

## 🔍 SCOPE 調査 (2026-07-07、ユーザー「まず scope 調査」要請) — ★ 大 port 不要、redesign は小さい

**当初「bounded_seqIndD_coherence を port する大仕事」と見積もったが、既に repo にある**と判明:

- **bounded-coherence 本体 = `S08.six_three_of_six_two_oracle` (Pf (6.2)/(6.3)) は完全 sorry-free**
  (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。size bound (11.4) `coherent_quotient_bound`
  + `four_mul_sq_add_one < p^q` も landed。
- **拡張 `S13.coherent_S_of_coherent_SH0C`** (`coherent(S(H₀C)) → coherent(inducedFamily)`) は**配線済み・
  本体 sorry-free**。`six_three_of_six_two_oracle` に `(K,H,M,H₁)=(M',HC,⊥,H₀C)` を instantiate + nilpotency
  + size bound + (5.6) break-member oracle を供給。
- `coherent_S_of_coherent_SH0C` の transitive sorryAx は **`exists_source_of_coherence_dichotomy` (§11
  (5.6) dichotomy 供給)** 経由 = **別 gate** (bounded-coherence 機構ではない)。
- `S13.S_H0C_not_coherent` も配線済み (= `coherent_S_of_coherent_SH0C` + `S12.S_not_coherent`)。
  `S_not_coherent` (10.8) は別途 sorried (既知 deep gate)。

### ⟹ redesign の正体 = capstone を **S(H₀C) 族に re-target** (uniform-degree は S(H₀C) で真)
Peterfalvi の本当の `S₂ = S(H₀C) − S(HC)` は **狭い C-kernel 族**で、そこでは uniform degree qu が
**genuinely 真** (`S11.forall_mem_sOf_H0C_apply_one_eq_qu`: 𝒮(H₀C) 全member が degree qu; qa 既約は
**広い inducedFamily 側**に居て S(H₀C) の外)。∴ repo の誤りは「uniform-degree を inducedFamily に適用」
だけで、**S(H₀C) に適用すれば正しい**。

redesign 手順 (bounded、multi-session port ではない):
1. capstone `coherent_Sset_of_column_identities` を **`coherent(hyp.SOf hyp.H0C)` を結論**する版に re-target
   (現 inducedFamily 版を置換)。union-glue (ν/hmixed/hDτ/coherentUnion) は S(H₀C)=S(HC)∪(S(H₀C)−S(HC))
   に適用。uniform-degree は `forall_mem_sOf_H0C_apply_one_eq_qu` (S(H₀C) で真) で供給。
2. `coherent_S_of_coherent_SH0C` (配線済) で inducedFamily coherence に拡張 → `S_not_coherent` 矛盾。
   or 直接 `S_H0C_not_coherent` と矛盾。
3. **再利用**: reducible-inclusion (landed)、ψ₀ witness、union-glue、bounded-coherence (全て既存)。
   **新規に偽の uniform-degree-on-inducedFamily を証明する必要は消える** (S(H₀C) で真になる)。

**工数見積り: 1–2 focused session** (capstone chain の family 差し替え + S(H₀C) uniform-degree の配線)。
当初の「multi-session port」から大幅縮小。残る deep gate (§11 (5.6) dichotomy / (10.8)) は本 redesign の
外 (既存 sorry、別途)。

## 参照

- notes/peterfalvi/s13_11_8_orthogonality.md update³⁷
- Coq: PFsection9.v:845 (9.8), :1258 (9.9); PFsection11.v:206 (11.3); PFsection6.v:115 (bounded coherence)
- S12_MaximalIII_IV_V.lean: `Sset_diff_SHCSet_apply_one_eq_qu` (:3904 irr-side sorry),
  `coherent_Sset_of_column_identities` (:4188 capstone), `hgen_of_S2_uniform_degree` (:4098)
