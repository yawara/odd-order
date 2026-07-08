---
id: 1019
slug: pf-11-8-6-bounded-coherence-redesign
title: "Pf (11.8.6): uniform-degree 設計 over-strong (非Galoisで偽) → bounded_seqIndD_coherence redesign"
created: 2026-07-07
---

# Pf (11.8.6): uniform-degree 設計 over-strong (非Galoisで偽) → bounded_seqIndD_coherence redesign

> ## ⚠⚠ CURRENT STATE (2026-07-09 lane-a 再開時 code-level 検証) — 本 issue 後半 (update⁴⁶〜⁵⁴) は STALE
> **redesign は実質完遂**。実コード検証で判明した正確な現状 (update⁴⁶〜⁵⁴ の「Ptype_core_* scaffold landed」
> 主張は git log -S で **一度もコミットされておらず実体ゼロ** — 診断 doc のみで、その後 caseB uniform-degree
> route が supersede した):
> - **caseB (9.7.b) coherence = sorry-free 完成**: `S13.caseB_coherent_sOf_H0Cprime` /
>   `caseB_coherent_sOf_H0C` (S13_CoreStructure、`uniform_degree_coherence_of_families` engine 経由)。
> - **caseA (9.7.a) = lane-b へ handoff 済** (HUB RULING 0101): `caseA_coherent_sOf_H0Cprime_of_refuter`
>   (S11_NineElevenCaseA, lane-b 所有) が maximality **refuter** 節に還元済 (sorry-free)。
> - **world-bridge + capstone = 完成**: `coherent_sOf_H0C` (unconditional, S13_Orthogonality) +
>   `coherent_SOf_H0C_of_column_identities` + `exists_zeta_residual_not_orthogonal_H0C` +
>   `w2_lt_w1_of_hypothesis_H0C`。spine は `OddOrder/FeitThompson.lean` で S13 route に再配線済 (0 bare)。
> - **残 spine sorry = 3 本 (全て cross-lane、S13_Orthogonality)**: (1) caseA refuter `(by sorry)` (:130,
>   lane-b S11) / (2) `hmixed` (6.7) image-side 直交 (:295, §14 Sibley) / (3) `hbridge_τ` (5.8) μ-column
>   image pin (:316, §14/§9)。
> - **vestigial (証明しない、consumer 0)**: S13_CoreStructure の `OrthogonalityData`-based 3 sorry
>   (`orthogonality_setup`:1359 / `not_orthogonal_mu0_sub_zeta`:1378 / `final_typeIII_conclusions`:1618)。
>
> ⟹ **lane-a の (11.8.6) producer work は完遂**。次目標 = **W2 (9000 typeP_Galois instance tail)** へ pivot
> (HUB RULING 0101 点5 + `notes/meta/ft_endgame_plan_2026_07_07.md` R1)。本 issue 後半は歴史記録として残置。

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

## 🏗️ 実装計画 (2026-07-07、ユーザー「redesign に着手」) — architecture 確定 + foundation 確認済

### 確認済 (sorry-free、redesign の土台)
- `S08.six_three_of_six_two_oracle` (bounded-coherence) — sorry-free ✅
- `S11.forall_mem_sOf_H0C_apply_one_eq_qu` (S(H₀C) 全member degree qu) — **sorry-free** ✅ (load-bearing)
- `S13.coherent_S_of_coherent_SH0C` (S(H₀C)→inducedFamily coherence) — 本体 sorry-free (S13、transitive
  sorry は §11 (5.6) dichotomy = 別 gate)

### ⚠ import 制約 (確定)
- (11.8) endgame `exists_zeta_residual_not_orthogonal` + `w2_lt_w1_*` は **S12** (consumer = FeitThompson:649
  `S12.w2_lt_w1_of_hypothesis`)。bounded-coherence の `coherent_S_of_coherent_SH0C`/`S_H0C_not_coherent`
  は **S13** (下流) → **S12 から直接呼べない (循環)**。
- ただし oracle 本体 `six_three_of_six_two_oracle` は **S08 (S12 上流)** ゆえ S12 から使用可。
- `exists_zeta` は既に `hM2 : secondDerivedInAmbient M = H ⊔ (U ⊓ C_G(H))` を保持 ⟹ C = U⊓C_G(H) は S12 で表現可。
  H0C = chief.H0 ⊔ C。`inducedFamily_eq_inducedKernelFamily_bot` (S12) で SOf ⊥ = inducedFamily。

### 実装ステップ (S12 内で完結、次 iteration)
1. **S12 bounded-coherence bridge** `coherent_inducedFamily_of_coherent_sOf_H0C` を新設 (S13
   `coherent_S_of_coherent_SH0C` の S12 版): `coherent(inducedKernelFamily M' (H0C.subgroupOf M))` →
   `six_three_of_six_two_oracle` (K=M', H=HC, M=⊥, H₁=H0C) → `coherent(inducedFamily M)`。
   要 S12 で: (a) HC/H0C の subgroup 表現 + normality、(b) hbound `4q²+1 < p^q` (= `|HC:H0C|=p^q` +
   `prime_pow_gt_four_mul_sq_add_one`; `|HC:H0C|=p^q` を S12 で導出 or chief から)、(c) h56 = (5.6)
   dichotomy (`hyp.exists_source_of_coherence_dichotomy`、S12 method、既存)。**S13 版をテンプレに移植**。
2. **capstone を S(H₀C) union-glue に re-target**: `coherent_SH0C_of_column_identities` (現
   `coherent_Sset_of_column_identities` を置換 or 併設): S(H₀C) = S(HC) ∪ (S(H₀C)−S(HC)) を union-glue。
   uniform-degree は `forall_mem_sOf_H0C_apply_one_eq_qu` (S(H₀C) で真) で供給 (現 `Sset_diff_SHCSet_apply_one_eq_qu`
   の inducedFamily 版=偽 を置換)。ν/hmixed/hDτ/reducible-inclusion/ψ₀ は再利用。
3. **`exists_zeta_residual_not_orthogonal` を再配線**: column identities → step2 で coherent(S(H₀C)) →
   step1 bridge で coherent(inducedFamily) → `S_not_coherent` 矛盾。
4. 旧 uniform-degree-on-inducedFamily 足場 (`Sset_diff_SHCSet_apply_one_eq_qu` irr-side sorry 等) を撤去。

**工数: 1–2 session。** step 1 (bridge) が最初の buildable。難所は step 1(b) の `|HC:H0C|=p^q` の S12 導出。

### ★ architecture 決定 (2026-07-07 追調査): endgame を **S13 へ移す**のが clean
step 1(b) の `|HC:H0C| = p^q` = `S13.H0C_relIndex_HC` (S13:630) は `hyp.s11Setup`/`hyp.H0C`/`hyp.HC`
に依存 = **S13-locked** (S12 で純粋 replicate すると H0C/HC/s11Setup setup + `H0C_relIndex_HC` の
再導出が要り重い)。∴ S12 内 replicate より **endgame を S13 に移設**が clean:
- `exists_zeta_residual_not_orthogonal` + `w2_lt_w1_of_residual_not_orthogonal` + `w2_lt_w1_of_hypothesis`
  を **S13 に移設** (S12 の column-identity 機構は `hyp.base` 経由で呼ぶ)。consumer = FeitThompson:649 を
  `S13.w2_lt_w1_of_hypothesis` に更新 (1 箇所)。
- S13 では `coherent_S_of_coherent_SH0C` / `S_H0C_not_coherent` / `SOf` / `H0C` / `forall_mem_sOf_H0C_apply_one_eq_qu`
  が全て可用 ⟹ 「column identities → coherent(S(H₀C)) → coherent_S_of_coherent_SH0C → coherent(inducedFamily)
  → S_not_coherent」を素直に組める (S12 facts の再導出不要)。
- 移設は大きめだが機械的 (`hyp.` → `hyp.base.`)。column identities → coherent(S(H₀C)) の union-glue
  (narrow 族、uniform-degree 真) が genuine な新規部分。
- 代替 (S12 replicate) は `H0C_relIndex_HC` 等の S13 facts port が必要でむしろ重い ⟹ 移設を採る。

**次 iteration = S13 に (11.8) endgame を移設 + narrow-族 union-glue で coherent(S(H₀C)) を構成。**

## 🔬 update³⁸ (2026-07-07 lane-a) — Coq 精読 + 族構造 code-level 確定 → SCOPE 訂正 + Route 確定

上記 SCOPE (「uniform-degree qu は S(H₀C) で genuinely 真・1-2 session」) を Coq PFsection11.v 精読
+ S11 族構造の subagent 精査で検証した結果、**方向は正しいが SCOPE は楽観的**と判明。訂正:

### ① Coq (11.8) の権威的構造 (PFsection11.v)
- `S1 := S_ HC` (deg q, `cohS1` via `uniform_degree_coherence`)、`S2 := seqIndD HU M H H0C`
  (`defS2`, = `sOf(H0C)`, deg qu)。**`S(H₀C) = S1 ⊔ S2`** (H≤ker で分割)。
- **★ `cohS2` (S2 coherence) は `subset_coherent (Ptype_core_coherence)` = (9.11)/(11.7) 経由で、
  `uniform_degree_coherence` を使わない。** uniform-degree は `cohS1` (S(HC)) 専用。
- (11.3) `FTtype34_noncoherence` (~coherent S_H0C) は `bounded_seqIndD_coherence` で直接 = Lean
  `S13.S_H0C_not_coherent` (配線済)。
- (11.8) `FTtype34_not_ortho_cycTIiso` は Coq では **per-ζ α-grid 直接計算** (「rearranged」)。
  Peterfalvi 本 (11.8.6) = 「coherent(S(H₀C)) 構成 → (11.3) 矛盾」= 現 Lean が踏襲する版。

### ② 族構造 verdict (code-level 確定)
- `cSub` = **C = C_U(H̄)** (chief-factor H̄ 上の U-action の kernel; S11:1660)。`cprimeSub` = **[C,C] =
  derivedInG(cSub)** ⊊ cSub (S11:1677)。`uprimeSub` = U' = [U,U]。**U' ≤ C** (`uprimeSub_le_cSub`)。
  cSub ≠ cprimeSub (proper)、cprimeSub と uprimeSub は order 関係なし。
- **degree-qa 非Galois既約 (9.8.d) は `𝒮(H₀U')` に属し `𝒮(H₀C)` から除外** (`hcuZetaPair_induceHU_mem_sOf`
  S11:9710 → H₀U')。qa-source は U' を kill するが larger C を generically kill しない (C ⊋ U')。
- `caseA_character_counts` (c): 𝒮(H₀C) 既約は degree **qu** (regular source) / (d): qa 既約は larger
  𝒮(H₀U') (non-regular θ₁)。**disjoint parametrization** ⟹ **𝒮(H₀C) は両ケースで uniform-qu** (qa 除外)。

### ③ ★ SCOPE 訂正 — narrow-族の uniform-qu は真だが case-A ∀-lemma は未証明の §9 obligation
`forall_mem_sOf_H0C_apply_one_eq_qu` (S11:8211) は **case-B 専用** (`CliffordCaseBData` = 既約 U-action)。
case-A では: reducible → `caseA_reducible_induceHU_apply_one_eq_qu` (S11:13010, ✅)、∃-irreducible-qu →
`caseA_exists_irreducible_sOf_H0C` (S11:13139, ✅) のみ。**case-A の `∀ φ∈sOf(H0C) irr, φ 1=qu` は未証明**
(counts (c) から assemble 可能な見込みだが genuine §9 work)。⟹ redesign は「偽の wide uniform-degree を
**真の narrow uniform-degree** に置換」= honest。ただし case-A ∀-uniform-qu 自体が §9 obligation。

### ④ ★ Route 判断 (lane-a 自律裁定) = Route 1 (narrow 族 + Book union-glue 維持)
- **Route 1 (採用)**: capstone を `sOf(H0C)` に re-target、現 glue 機構 (`coherent_Sset_of_glued` /
  `exists_glue_nu` / `hgen_of_S2_uniform_degree`) を **narrow S2=sOf(H0C) に適用**。narrow-族は sound
  (qa 除外で uniform-qu 真)、既存 α-grid inner lemma 投資を再利用、rewrite 最小。case-A ∀-uniform-qu は
  honest §9 obligation として correct-signature で cite/prove。
- **Route 2 (却下)**: Coq の per-ζ core-coherence route (uniform-degree 回避)。両ケースで確実だが
  glue 機構の major rewrite で現投資を破棄 → narrow-族が sound な今は不要。
- ⚠ **訂正 (caseA_character_counts 精査)**: 上で「数学的に qa 除外ゆえ両ケース uniform」と書いたのは
  **過剰主張**。`caseA_character_counts` (S11:13898) は case-A で SOf(H0C) の (b) reducible=qu + (c)
  **∃**-irreducible=qu のみ与え、(d) qa 既約は **larger 𝒮(H₀U')** に置く。**`∀ φ∈SOf(H0C) irr, deg qu`
  は無い**。qa-source は U' を kill するが「C (⊋U') を kill するか」= C-族 SOf(H0C) に qa が入るかは
  **未形式化・真偽未確定** (deep §9)。∴ **Route 1 の narrow uniform-degree は「qa が C を kill しない」
  という未証明命題に依存** — 真なら §9 obligation、偽なら narrow 族でも false-hoist。Coq が S2 に
  uniform-degree を使わず core-coherence を使う事実がこの不確実性と整合。
- ⟹ **修正した進め方**: Route 1 の uniform-degree に commit せず、**route-independent で sound な piece
  を先に**: ① `S(HC)` coherence = (5.7) `SHC_isCoherent` (landed) ② `sOf(H0C)` coherence = (9.11)
  `coherent_H0C_commutator` (core-coherence, carrier obstruction 別途) ③ world-bridge 分解
  `S13.SOf(H0C) = SHCSet ⊔ sOf(H0C)` (★ enabler = `huSub_eq_derivedInG_subgroupOf` S11:1505 で
  HU=M' 確定 → sOf⊆SOf の induce-transport が tractable)。case-A uniform-qu の真偽は並行して §9 で解決
  (それが真なら Route 1 の generation、偽なら Coq per-ζ / core-coherence generation)。

### ⑥ ✅ landed (2026-07-07, commit e1ef5bdb) — step ③ subset 方向
`S13.Hypothesis.sOf_subset_SOf` (`sOf hyp.s11Setup Y ⊆ hyp.SOf Y`) sorry-free。`rw [← hHU]`
(HU=M' carrier 一致) で witness=χ、θ≠trivial=xiSet の H⊄ker、kernel=xiOf、induce-eq=`induceHU_eq_induce`。
予測した induce-transport の motive 障害は発生せず (carrier rw 成功)。**残 world-bridge = 逆方向**
(`SOf(H₀C)` の member が SHCSet か sOf(H₀C) に入る H≤ker 分割 = decomposition)。次候補 = 逆方向 or
step① SHC coherence を SOf-版に接続。

### ⑤ 訂正後の実装 sequence (deeper than 1-2 session; multi-part)
1. **case-A/B ∀-uniform-qu on `sOf(H0C)`** (S11): case-split (`CliffordCaseAData`∨`CliffordCaseBData`
   dichotomy) → caseB `forall_mem_sOf_H0C_apply_one_eq_qu` / caseA reducible+irreducible。← genuine §9。
2. **world-bridge 分解 `S13.SOf(H0C) = SHCSet ⊔ sOf(H0C)`** (S12:4055 で未形式化と明記): S11 `sOf` ↔
   S13 `SOf`(=inducedKernelFamily M') の identification + H≤ker 分割。← genuine bridge work。
3. **capstone re-target** `coherent_SOf_H0C_of_column_identities` (S13): S07 engine
   `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` を (SHCSet, sOf(H0C)) に適用。
   uniform-qu = step①、S2 coherence = (9.11) `coherent_H0C_commutator` (core-coherence)、hmixed/hDτ =
   §14-gated (narrow 族)。
4. **endgame 移設 S12→S13**: `exists_zeta_residual_not_orthogonal` + `w2_lt_w1_of_hypothesis` を S13 へ
   (`w2_lt_w1_of_residual_not_orthogonal` は S12 に残置、S13 から cite)。coherent(SOf(H0C)) →
   `S_H0C_not_coherent` と直接矛盾。FeitThompson:649 を `S13.w2_lt_w1_of_hypothesis` に更新 (S13.Hypothesis
   を `exists_hypothesis_of_isTypeIIIorIV` で構築、hM2/hHcard transport)。
5. 旧 wide uniform-degree 足場 (`Sset_diff_SHCSet_apply_one_eq_qu` irr-side sorry 等) を撤去。

## 参照

- notes/peterfalvi/s13_11_8_orthogonality.md update³⁷
- Coq: PFsection9.v:845 (9.8), :1258 (9.9); PFsection11.v:206 (11.3); PFsection6.v:115 (bounded coherence)
- S12_MaximalIII_IV_V.lean: `Sset_diff_SHCSet_apply_one_eq_qu` (:3904 irr-side sorry),
  `coherent_Sset_of_column_identities` (:4188 capstone), `hgen_of_S2_uniform_degree` (:4098)

## 🔬 update³⁹ (2026-07-07 lane-a /loop) — ★ world-bridge 集合等式 COMPLETE (逆方向 landed)

step ③ の逆方向 (covering) を landing (commit f3d93d1a、S13、axiom-clean)。subset 方向
(`sOf_subset_SOf`, e1ef5bdb) と合わせ **world-bridge の集合等式が完成**:

- **`S13.Hypothesis.SOf_H0C_eq_SOf_HC_union_sOf`**: `SOf(H₀C) = SOf(HC) ∪ sOf(H₀C)`
  (Peterfalvi の `S(H₀C) = S₁ ⊔ S₂`, S₁=S(HC), S₂=𝒮(H₀C))。source θ を `H ≤ Ker θ` で分割:
  H≤ker → HC=H⊔C ≤ Ker θ → SOf(HC); H⊄ker → θ∈𝒳 → sOf(H₀C)。逆向き = kernel antitone +
  `sOf_subset_SOf`。carrier transport は subset 方向と同型に `← hHU` で huSub world 統一。
  **route-independent で sound** (uniform-degree の偽 route に非依存 = ④ の懸念を回避; SOf(HC)
  形なので degree/irreducibility を主張せず純 kernel-bookkeeping)。
- **前提 infra (foundational, hoist candidate → S03)**: `characterKernel_mul_mem` /
  `characterKernel_inv_mem` / `characterKernelSubgroup` — genuine character の kernel が subgroup。
  `rep_eq_id_of_character_eq_one` (χ_ρ(g)=χ_ρ(1) → ρ g = id) 経由。HC=H⊔C の join を単一 kernel
  条件に押し込むのに必要だった (既存に無かった)。

### 次 step の precise map (残 = 全て deep §9 or §14-gated)
world-bridge が済んだので capstone re-target (step ③→④) に必要な残ピース:
1. **coherent(SOf(HC))** = landed `SHC_isCoherent` (SHCSet 上) を **SOf(HC) 上**に移す =
   **`SHCSet = SOf(HC)` identification** (deep §9/§11、ungated だが要証明)。真である根拠:
   SOf(HC) の source θ は HC=H·C を kill → M'/HC ≅ U/C で factor、U/C は abelian
   (`derivedU_le_C` = U'≤C landed ⟹ U/C は U/U' の商) ⟹ θ linear (deg 1) ⟹ Ind θ deg q。
   Ind θ irreducible = Clifford (type-P inertia=M')。⟹ SOf(HC) = deg-q irreducibles = SHCSet。
   ← **次の ungated 上流候補** (Clifford irreducibility + linear-source が repo にあるか要確認)。
2. **coherent(sOf(H₀C))** = (9.11) `S11.coherent_H0C_commutator` = **§14-gated**
   (`sibleyTarget_H0C := sorry`, issue 7001)。sorried-cite。
3. **union-glue** (SHCSet/SOf(HC), sOf(H₀C)) の hmixed/hDτ = §14/BG §15-gated。
4. capstone `coherent_SOf_H0C_of_column_identities` (S13) → `S_H0C_not_coherent` 矛盾 + endgame 移設。

## 🔬 update⁴⁰ (2026-07-07 lane-a /loop) — ★ capstone gate 構造を code-level 確定: coherent(SOf(HC)) は sorry-free 到達可能

world-bridge (update³⁹) 後、capstone re-target に必要な coherence 入力を精査。**旧 update³⁹ の
「SHCSet↔SOf(HC) は deep §9」評価は過小**: 前セッションが既に土台を landing 済で、
**coherent(SOf(HC)) は sorry-free に到達可能**と判明。

### ★ 既存 (sorry-free、prior lane-a): SOf(M'') = SHCSet + coherent
- **`S13.Hypothesis.SOf_secondDerived_eq`** (S13:1047, axiom-clean): `SOf(M'') = SHCSet`
  (= degree-w₁ 既約 subfamily)。証明は `inertia_eq_derived_of_linear` (linear char の Clifford irr) +
  `charValue_one_eq_one_of_commutator_le_ker` (M''≤ker → linear)。← **Clifford-irr 機構は在った**。
- **`S13.Hypothesis.secondDerived_coherent`** (S13:1103, axiom-clean): `coherent(SOf(M''))`
  = `SHC_isCoherent` を `SOf_secondDerived_eq` で rewrite。

### ★ coherent(SOf(HC)) の sorry-free path (次 iteration で build)
`SOf(HC) ⊆ SOf(M'')` (antitone、`M''⊆HC` = `secondDerived_le_HC` **sorry-free**) + `secondDerived_coherent`
[sorry-free] + **IsCoherent subset-restriction**。⟹ coherent(SOf(HC)) は M''=HC gate 不要で sorry-free。
- **build 手順** (~40-50 行):
  1. `isCoherent_of_subset` (S07.IsCoherent の restriction): `IsCoherent τ S A → S'⊆S →
     (∃φ∈zSupportedSpan S' A, φ≠0) → IsCoherent τ S' A`。extension 同一、inner_eq/extends/mem_ZIrr は
     `Submodule.span_mono` (zSpan=span ℤ) + `zSupportedSpan_mono_left` (S07:96) で restrict。
  2. nonzero witness (SOf(HC)): `exists_inducedKernelFamily_member_degree_index` (S08:142、要
     `[((HC.subgroupOf M).subgroupOf K).Normal]` = `HC_subgroupOf_normal.subgroupOf` +
     `commutator(K/HC)≠⊤` = M''≤HC ⟹ ⊥ かつ HC⊊M'=HU via `C_lt_U`) で deg-w₁ member ζ →
     `inducedKernelFamily_hasNoRealCharacters` で ζ≠ζ.conj → `inducedKernelFamily_conjDiff_support`
     (S08:286) で ζ-ζ.conj ∈ zSupportedSpan A₀、≠0。
- **注**: world-bridge は `SOf(HC)` 形が正 (H≤ker part は SOf(M'') でなく SOf(HC); SOf(M'')=SHCSet は
  H を kill しない deg-w₁ 既約も含むため SOf(H0C) に非包含 → `SOf(H0C)=SOf(M'')∪sOf(H0C)` は偽)。

### capstone re-target `coherent_SOf_H0C_of_column_identities` (S13) の残 gate
1. **coherent(SOf(HC))** = ↑ sorry-free path (次 iteration)。
2. **coherent(sOf(H0C))** = (9.11) `S11.coherent_H0C_commutator` = §14-gated (`sibleyTarget_H0C` sorry、
   ⚠ S07_Subcoherent note で likely-UNSOUND 指摘あり = issue 7001; 本来 (9.11) Ptype_core_coherence
   8-step induction で honest 化すべき)。sorried-cite。
3. **union-glue** (SHCSet/SOf(HC), sOf(H0C)) の hmixed/hDτ = §14/BG §15-gated。
4. `SOf_H0C_eq_SOf_HC_union_sOf` (update³⁹ landed) で SOf(H0C)=SOf(HC)∪sOf(H0C) に書き換え → union-glue →
   coherent(SOf(H0C)) → `coherent_S_of_coherent_SH0C` → inducedFamily → `S_not_coherent` 矛盾 + endgame 移設。

⟹ **本 session landed**: world-bridge 集合等式 (update³⁹) + characterKernel subgroup infra。
**次 = coherent(SOf(HC)) sorry-free build (path 確定) → capstone skeleton (gate 2/3 は sorried-cite)。**

## 🔬 update⁴¹ (2026-07-07 lane-a /loop) — ★ S₁-side 完成: coherent(S(HC)) + S₁-identification landed

update⁴⁰ の path 通り **coherent(S(HC)) を sorry-free landing**、加えて S₁-identification も landing。
world-bridge の **S₁ = S(HC) 側は coherence + 構造同定が完了**、残る障害は全て **sOf(H0C)=S₂ 側**に移った。

### ✅ landed 本 session (commits f31df00d, e3420cf4 — 全 axiom-clean)
- **`S13.coherent_SOf_HC`** (S13): `Nonempty (IsCoherent tau (SOf HC) A0)`。S(HC) は S(M'') の
  kernel-拡大部分族 (M''≤HC=`secondDerived_le_HC` ⟹ S(HC)⊆S(M'') kernel-antitone) ゆえ S(M'') の
  coherent 拡張 (`secondDerived_coherent`) を **inline で restrict** (isometry/τ-agreement/ZIrr は
  span_mono/zSupportedSpan_mono_left で transport)。唯一の新規入力 = nonzero witness ζ̄−ζ:
  member ζ∈S(HC) 存在は `inducedKernelFamily_nonempty_of_commutator_ne_top` を proper trace
  HC⊊M' (`HC_lt_derived`) 経由の `commutator_quotient_ne_top` で、conjDiff は A₀-supported
  (`mderivSharp_subset_A0`)・nonzero (odd order 実指標なし)。
- **`S13.HC_lt_derived`** (S13): HC⊊M' を `HC_le_secondDerived` から top-level 抽出 (前 session の
  未 commit refactor を確定)。U≤HC=H·C を normal H-factor 分解 → a∈H∩U=⊥ → u∈C で C⊊U 矛盾。
- **`S13.SOf_HC_subset_SHCSet`** (S13): S(HC) ⊆ SHCSet。S(HC)⊆S(M'') + `SOf_secondDerived_eq`
  (S(M'')=SHCSet=degree-w₁ 既約族)。S₁=S(HC) を uniform-degree-q 部分族として同定 → capstone が
  SHCSet の直交/generation infra を S(HC) 上で再利用する橋渡し。

### ★ 次 step の精密 map (endpoint は既に sorry-free と判明)
- **判明: `coherent_S_of_coherent_SH0C` (S13:1357) は既に sorry-free** (coherent(SOf(H0C)) →
  coherent(Sset) を (6.3) `six_three_of_six_two_oracle` で assemble 済)。∴ missing link は
  **coherent(SOf(H0C)) を作る capstone のみ**。
- **capstone `coherent_SOf_H0C_of_column_identities` (未作成, S13)**: 汎用 engine
  `S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` (S07:4811) を
  X=SOf(HC), Y=sOf(H0C) で instantiate → `SOf_H0C_eq_SOf_HC_union_sOf` (landed) で
  SOf(H0C)=SOf(HC)∪sOf(H0C) に rewrite → coherent(SOf(H0C))。engine 入力の gate 内訳:
  - `hX` = coherent(SOf(HC)) — ✅ **landed** (本 session)
  - `hsrc_ortho` (SOf(HC) ⊥ sOf(H0C)) — ✅ **landed** (update⁴², commit 645622e4)。当初「sOf(H0C)⊆Sset∖SHCSet に還元」と
    書いたのは誤: update⁴⁰ 通り SHCSet=SOf(M'') は H を kill しない deg-w₁ 既約を含むため
    sOf(H0C)⊆Sset∖SHCSet は不明/偽の恐れ → SHCSet route 不可。**正しい ungated route = source-level
    H-kernel distinctness**: SOf(HC) 成員 x=induce_K θ は hInHu(=H-trace in K=HU) ≤ ker θ (H≤HC≤ker),
    sOf(H0C) 成員 y=induceHU χ'=induce_K χ'' は ¬(hInHu⊆ker χ'') (`xiSet` 定義条件)。x=y なら
    `induce_eq_induce_iff_conj` で θ~χ'' → `hInHu_normal` ゆえ ker 共役不変で hInHu≤ker χ'' → 矛盾
    → x≠y → `inducedKernelFamily_pairwise_orthogonal`。span 化は `span_inner_SHCSet_diff_eq_zero` と
    同じ double `span_induction`。carrier bridge は `sOf_subset_SOf` (huSub=K, `induceHU_eq_induce`)
    踏襲。**gate でなく形式化労力のみ** — 次 iteration の第一候補。
  - `hY` = coherent(sOf(H0C), A0) — §14-gated + **packaging mismatch**: `S11.coherent_H0C_commutator`
    (S11:8298) は coherent(`chars.S`, `H0CprimeSupport`) を与え (sOf(H0C), A0) でない。
    bridging (chars.S↔sOf(H0C), H0CprimeSupport↔A0) 要。sibleyTarget_H0C 経由 = likely-UNSOUND(7001)。
  - `ν`+`hagreeX`/`hagreeY` (glue map) — §14 (旧 route `exists_glue_nu`=9016 の world-bridge 版)
  - `hmixed` (6.7 image-side 直交) — §14/BG§15
  - `hDτ` (5.8 column identity) — §14
  - `hgen` — §9 generation (旧 route `hgen_of_S2_uniform_degree` landed の world-bridge 版)
- **⟹ 残 work の分類**: (0) **ungated・要 build = `hsrc_ortho` (SOf(HC)⊥sOf(H0C), source-level
  H-kernel distinctness, 上記)** ← 次 iteration 第一候補; (a) §14 coherent(sOf(H0C),A0) honest 化
  ((9.11) Ptype_core_coherence, sibleyTarget bypass); (b) §14 glue (ν/hmixed/hDτ)。
  S₁ 側の coherence/構造同定は本 session で打ち止め (これ以上の ungated S₁ work 無し)、
  残る ungated は hsrc_ortho のみで、それ以外は §14/§9 深部。

## 🔬 update⁴² (2026-07-07 lane-a /loop) — ★ hsrc_ortho landed: capstone の ungated 入力が完備

update⁴¹ で ungated と判明した `hsrc_ortho` (SOf(HC) ⊥ sOf(H0C)) を **sorry-free landing**
(commit 645622e4, axiom-clean)。これで world-bridge union-glue engine
`S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` (S07:4811) の
**ungated 入力は全て完備** (hX=coherent(S(HC))=landed, hsrc_ortho=landed)。

### ✅ landed 本 iteration (S13, axiom-clean)
- **`SOf_HC_inner_sOf_H0C_eq_zero`** (pairwise): S(HC) 成員 ⊥ 𝒮(H0C) 成員。両者は pairwise 直交な
  §10 族 `inducedKernelFamily HU` の Ind_HU 成員 (`sOf_subset_SOf` で sOf⊆SOf) で **相異**:
  S(HC)-source θ は H を kill (H≤HC≤ker θ, `hInHu ⊆ ker θ`)、sOf-source χ' は 𝒳 (¬hInHu⊆ker χ',
  `xiSet` 定義)。Ind θ=Ind χ' なら `induce_eq_induce_iff_conj` で θ,χ' が M-共役 → H⊴M 共役不変
  (`subsetCharacterKernel_conjBy_of_invariant` + `hSubgroupOfM_normal`, hInHu invariance は
  `hInHuConj` の toFun パターン) で hInHu⊆ker χ' を強制 → χ'∈𝒳 矛盾 →
  `inducedKernelFamily_pairwise_orthogonal`。
- **`span_inner_SOf_HC_sOf_H0C_eq_zero`** (span): ℤ[S(HC)]⊥ℤ[𝒮(H0C)] = engine の hsrc_ortho 引数の
  正確な形。pairwise の double `span_induction` bilinear 拡張 (`span_inner_SHCSet_diff_eq_zero` mirror)。

### 残 capstone gate = 全て §14/§9-deep (ungated S₁-side work は完全に打ち止め)
capstone `coherent_SOf_H0C_of_column_identities` (未作成) の engine 入力で残るのは:
- `hY` = coherent(sOf(H0C), A0) — §14-gated + packaging mismatch (`coherent_H0C_commutator` は
  coherent(chars.S, H0CprimeSupport)、bridging 要、sibleyTarget_H0C=likely-UNSOUND/7001)
- `ν`+`hagreeX`/`hagreeY` (glue map) — §14 (exists_glue_nu の world-bridge 版)
- `hmixed` (6.7 image-side 直交) — §14/BG§15
- `hDτ` (5.8 column identity) — §14
- `hgen` — §9 generation (hgen_of_S2_uniform_degree の world-bridge 版)
⟹ **本 session (3 commit) で S₁-side = coherence + S₁-同定 + 直交 を完全 landing**。
capstone は上記 §14/§9 gated 入力を仮説パラメータ化した skeleton で前倒し可能 (次 iteration 候補) —
ただし ungated な genuine 数学は S₁-side で尽きたので、それ以降は §14 (lane b/c 領域) / §9 深部との
協調が必要。

## 🔬 update⁴³ (2026-07-07 lane-a /loop) — ★ capstone skeleton landed: world-bridge route 全配線

`coherent_SOf_H0C_of_glued` (S13, axiom-clean, commit 1b7f282d) を landing。汎用 engine
`S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` を (S(HC), 𝒮(H0C)) で
instantiate + `SOf_H0C_eq_SOf_HC_union_sOf` (landed) rewrite → coherent(SOf(H0C))。
**world-bridge route が end-to-end で配線完了**:
`coh[landed] + hY[gate] + glue[gate] → coherent(SOf(H0C)) → coherent_S_of_coherent_SH0C[既 sorry-free]
→ coherent(Sset) → (11.3) 矛盾`。

### ✅ 本 session 総括 (6 landing, 全 axiom-clean, full build green)
S₁-side + route の ungated 部分を**完全 landing**:
- `coherent_SOf_HC` — coherent(S(HC)) [f31df00d]
- `HC_lt_derived` — HC⊊M' 抽出 [f31df00d]
- `SOf_HC_subset_SHCSet` — S₁-同定 (S(HC)⊆SHCSet) [e3420cf4]
- `SOf_HC_inner_sOf_H0C_eq_zero` + `span_inner_SOf_HC_sOf_H0C_eq_zero` — hsrc_ortho [645622e4]
- `coherent_SOf_H0C_of_glued` — capstone skeleton [1b7f282d]

### 残 gate (⚠ 訂正: hgen も cleanly ungated でない — 全て §9/§14 gated)
capstone `coherent_SOf_H0C_of_glued` の仮説パラメータ (供給すれば coherent(SOf(H0C)) が閉じる):
- **`hgen`** — ⚠ **cleanly ungated でない (当初 update 訂正)**。world-bridge 版は S₂=sOf(H0C) の
  uniform-degree qu を要するが、**`forall_mem_sOf_H0C_apply_one_eq_qu` (S11:8211) は
  `caseB : CliffordCaseBData` を要求 = case-B 限定**。**case A は qa 既約 (deg qa≠qu) を含み uniform
  でない** (update⁴⁰ の §9 obligation; qa が C を kill するか未確定)。∴ hgen は **case-A/B dichotomy +
  case-A の §9 uniform 構造**に依存 → §9-gated。case-B side のみ ungated (部分的)。
- **`coh`** = coherent(S(HC)) [landed, caller が `coherent_SOf_HC` で供給]。
- **`hY`** = coherent(𝒮(H0C), A0) — §14-gated ((9.11) Ptype_core_coherence; sibleyTarget bypass 要;
  packaging bridge chars.S↔sOf, H0CprimeSupport↔A0 も要)。deep §9/§14。
- **`ν`+hagreeX/hagreeY** (glue map τ₃) — §14 (`exists_glue_nu`=9016 の world-bridge 版)。
- **`hmixed`** (6.7 image-side 直交) — §14/BG§15。
- **`hDτ`** (5.8 column identity) — §14。

⟹ **S₁-side の ungated work は本 session で完全に尽きた**。残 gate は**全て §9/§14 深部**:
hgen (case-A §9 uniform 構造 = qa/C-kernel 未確定) / hY (§14 (9.11) core-coherence) /
ν・hmixed・hDτ (§14/BG§15 glue)。これらは lane b/c 領域 or §9 深部との協調が必要 (単独 ungated build 不可)。
次 iteration は §9 case-A 構造 (qa が C を kill するか) か §14 gate 協調に降りる — いずれも deep frontier。

## 🔬 update⁴⁴ (2026-07-07 lane-a /loop) — ★ hY gate の honest route 確定 + hgen-uniform の非健全性を Coq で決着

残 gate のうち **hY (coherent(sOf(H0C))) の honest route を Coq PFsection9/11 精読で確定**。加えて hgen の
uniform-degree route が case-A で非健全であることを Coq S2 構造で裏取り。両者は同一の Coq 権威に帰着:
**Peterfalvi は S₂=S(H₀C) 側 coherence を uniform-degree で作らず、(9.11) core-coherence の 8-step
induction で作る**。

### ① hY = coherent(sOf(H0C)) の honest route = **(9.11) 8-step induction** (≠ sibleyTarget shortcut)
- **Coq `cohS2` (PFsection11.v:660-664)**: `S2 = seqIndD HU M H H0C` (= sOf(H0C)) の coherence は
  `subset_coherent (Ptype_core_coherence)` = **(9.11) core-coherence** 経由。uniform-degree は使わない
  (uniform は cohS1 = S(HC) 専用、`uniform_degree_coherence`, PFsection11.v:607-611)。
- **`Ptype_core_coherence` (Pf (9.11), PFsection9.v:1484-1571)** = coherent(S_ H0C')。証明は **(6.8) 抜きの
  8-step induction**: Galois → `uniform_degree_coherence` (S(H₀C') uniform-qu); 非Galois → degree-`qa`
  subfamily を filter → `uniform_degree_coherence` (qa uniform) → conjugate-pair を 1 組ずつ帰納 extend し
  maximality 矛盾。
- ∴ Lean `S11.coherent_H0C_commutator` の現 `cohereOfSibleyTarget (sibleyTarget_H0C)` wiring は **honest でない**
  (下記②)。**honest hY = この 8-step induction を Lean に port** (次 iteration の本体作業)。

### ② ★ `sibleyTarget_H0C` は UNSOUND — 7001 mandated 監査 COMPLETE (verdict UNSOUND, frobI-parallel)
7001 裁定②の必須 soundness 監査を実施 → **偽 field 要求で unprovable** と airtight 確定 (詳細 = issue 7001
「2032 型 soundness 監査 COMPLETE」節):
- `SibleyDadeHypothesis` (S08:3234) の `H_sharp_ti` (S08:3248) + `dade_H_eq_bot` (S08:3258) は **無条件 field**
  = (c1)/(c2) 両枝で `H^#` TI in `G` 必須。S(H₀C') の Sibley kernel `HC ⊆ F(M)` (nilpotent Hall) は非TI ⟹
  両 field 偽 ⟹ unprovable (frobI/2032 と同一)。
- **∴ `sibleyTarget_H0C` の sorry は fill しない**。in-code に⚠注記済 (本 commit、S11 docstring 2 箇所)。

### ③ hgen-uniform も case-A で非健全 (①と同根)
- capstone `coherent_SOf_H0C_of_glued` の `hgen` を旧 `hgen_of_S2_uniform_degree` (S₂ uniform-qu) で供給する
  route は **case-A で偽**: Coq S2 の**既約**成員が uniform-qu である保証は無い (Coq は `memS2red`
  PFsection11.v:684 で S2 の**可約**成員のみ `mu_j` deg qu と同定; 既約は (9.11) induction で扱う)。
  非Galois で degree-qa 既約が存在し得る (9.8.d)。
- ∴ hgen も uniform-degree でなく **①の core-coherence route と整合する generation** で供給すべき
  (D-set で mixed 項を honest に吸収、uniform 非依存)。case-B 限定なら uniform (5.11:8211) で供給可 (部分的)。

### ⟹ 次 lane-a iteration = **(9.11) 8-step induction の Lean port** (honest hY の本体)
- port の第一 ingredient (Coq PFsection9.v:1549-1551 mirror): S(H₀C') の uniform subfamily
  (Galois 全体 / 非Galois は degree-qa filter) の coherence を Lean `uniform_degree_coherence` engine
  (在庫確認要) で構成。次に coherence-extension induction。
- deep だが **lane-a 所有 (S11) の ungated genuine math** (§14/lane-b gate でない = 7001 裁定①)。
- capstone の hY 引数は、この honest `coherent_H0C_commutator` から (packaging bridge chars.S↔sOf,
  H0CprimeSupport↔A0 を付けて) 供給する。

## 🔬 update⁴⁵ (2026-07-07 lane-a /loop) — ★ (9.11) engine 在庫確認 = 全 sorry-free + 正しい port target を確定

subagent で S07 coherence infra を精査 → **(9.11) induction の engine 群は既に全部 landed (sorry-free)**。
同時に `coherent_H0C_commutator` の現 signature が **誤り (dead statement)** と判明。port は「deep multi-session
build」でなく **既存 engine の assembly** に縮小、ただし target を訂正する必要あり。

### ① ★ (9.11) engine 在庫 (全 sorry-free、S07/S08) — port は assembly
| engine | 場所 | 役割 |
|---|---|---|
| `coherent_of_constant_degree` | S07_CoherenceConstantDegree:551 | uniform-degree → coherent (Coq `uniform_degree_coherence`) |
| `coherent_subset_of_constant_degree` | S07_Subcoherent:246 | restrict + uniform coherence = **base case (Galois 全体 / 非Galois qa-subfamily)** |
| `irrSubcoherent` | S07_Subcoherent:148 | subcoherent `Hypothesis` 組立 (Coq `irr_subcoherent`) |
| `Snorm`/`sumnS` + `two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS` | S07_Subcoherent:383/390/445 | (9.11) norm-chain + extend 発火前提 (`lb0<sumnS ⟹ 2a<∑deg²/mc`) |
| squeeze lemmas `lb0_le_lb1`/`two_mul_le_of_dvd_of_odd`/`relIndex_le_relIndex_of_le` | S07_Subcoherent:468/509/542 | (9.11.2-9.11.4) 中間 squeeze |
| `retarget_isCoherent_of_decompositions_and_memberFamily` | S07_Coherence:4209 | per-step 1 conjugate-pair adjoin ((5.6.3)) |
| `xAdjoinStepW` | S08_CoherenceWeighted:287 | (5.6) extend_coherent (norm-weighted) |
| `coherentPairChain` | S07_Coherence:5033 | induction fold (9.11.1/7/8) |

残 = **assembly のみ** (~200-300 行): irrSubcoherent で Hypothesis 組立 → base = constant-degree →
coherentPairChain で norm-chain-gated adjoin を fold。§9 family-specific arithmetic (各 squeeze の
group-theoretic 具体化) が genuine work。

### ② ★ port target 訂正 — `coherent_H0C_commutator` は dead statement (使わない)
- `chars.S = sSet data` = **full family** {Ind χ | χ∈𝒳, H⊄ker} (S11:1601)。`coherent_H0C_commutator`
  (S11:8317) は `IsCoherent tau chars.S chars.H0CprimeSupport` を主張するが: (a) full family の coherence は
  **偽** (= Coq `FTtype345_noncoherence`: `S_ 1` 非coherent)、(b) `mkSection11CharacterData` が
  `H0CprimeSupport := ∅` を pin → `IsCoherent … ∅` は `zSupportedSpan S ∅={0}` で **unconstructible**
  (S12:4051-4054 が明記)。∴ **`coherent_H0C_commutator` は port target でない** (sibleyTarget unsound に加え
  signature も dead)。
- **正しい hY target (S13 capstone `coherent_SOf_H0C_of_glued` が消費)** = `IsCoherent hyp.base.tau
  (S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0` = **subfamily sOf(H0C) の coherence on 実 support A0**。

### ③ ★ honest route (確定) = (9.11) port → subset-restrict
1. **(9.11) induction port**: `coherent(sOf(H0C'), A0)` を上記 engine assembly で構成 (Coq
   `Ptype_core_coherence` PFsection9.v:1484-1571 の mirror; §9 sOf world = Coq `S_ H0C'` と同 induce-from-HU)。
2. **subset-restrict**: `C' ≤ C ⟹ H0C' ≤ H0C ⟹ sOf(H0C) ⊆ sOf(H0C')` (`sOf_antitone`) →
   `coherent(sOf(H0C), A0)` を subset-restriction (`isCoherent_of_subset` + nonzero witness) で。
   ⟹ capstone hY 完成。
- 両 step とも **lane-a §9 ungated** (§14/lane-b gate でない)。step 1 が本体 (assembly)、step 2 は小。
- (別 world の S12 `coherent_Sset_diff_SHCSet` (S12:4059、§10 inducedFamily world、正 signature の honest
  sorry) は世界橋 obstruction #3 経由の代替 target; S13 sOf-route が本線。)

### ⟹ 次 iteration = **step 1 の assembly を CODE 開始** (irrSubcoherent で sOf(H0C') の Hypothesis 組立
→ base-case constant-degree coherence)。調査は打ち止め、engine 在庫確定ゆえ Lean を書く段階。

## 🔬 update⁴⁶ (2026-07-07 lane-a /loop) — ★ hY-route subset step LANDED + hyp.C vs cSub 同定 gap を特定

**landed (S13, axiom-clean, build green)** — hY route の subset-restrict 部分を配線:
- `S13.isCoherent_of_subset` (前 commit, general L): `IsCoherent τ S A + S'⊆S + (S' nonzero witness) →
  IsCoherent τ S' A` (coherent_SOf_HC の inline restriction を抽出、同 refactor で validation)。
- `S13.Hypothesis.H0Cprime` = `chief.H0 ⊔ derivedInG C` (C'=[C,C]、Coq `S_ H0C'` trigger)。
- `S13.Hypothesis.sOf_H0C_subset_sOf_H0Cprime`: `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone` + C'≤C)。
- `S13.coherent_sOf_H0C_of_coherent_sOf_H0Cprime`: **capstone の hY 型** (`IsCoherent tau (sOf H0C) A0`)
  を `coherent(sOf(H0Cprime)) + 𝒮(H₀C) witness` から供給 (isCoherent_of_subset 適用)。
  ⟹ **hY ⟸ (9.11 coherence of 𝒮(H₀C')) + (𝒮(H₀C) nonemptiness)** に還元完了。

### ⚠ 特定した同定 gap (次の焦点) — `hyp.C` (S13) = `cSub` (S11) か?
- **`hyp.C = C_U(H)`** (S13 `C_eq_centralizer`: `U ⊓ centralizer(H)`) だが **`chars.C = cSub = C_U(H̄)`**
  (S11:1660, chief factor `H̄=H/H₀` 上の U-action kernel)。`C_U(H) ≤ C_U(H̄)` (一般) ゆえ **未同定なら
  capstone の family `sOf(chief.H0 ⊔ hyp.C)` は (9.11) の `sOf(chief.H0 ⊔ cSub)` と別物**。
- 予想: **Peterfalvi (11.6) `C = U'`** (`derivedU_le_C` S13:313 = U'≤C の逆) で `hyp.C = U'`、かつ
  `cSub = U'` も設定内で成立 ⟹ `hyp.C = cSub = U'` で同定成立。だが **repo に `hyp.C = cSub` 補題は無い**
  (grep 済) → **次 iteration の焦点 = この同定を (11.6) 経由で確立** (これが (9.11)→capstone 接続の要)。
  同定後、`coherent_sOf_H0C_of_coherent_sOf_H0Cprime` の hcoh は (9.11) port、hwit は
  `caseA_exists_irreducible_sOf_H0C` (chars.C = hyp.C 同定後に適用可) で埋まる。

⟹ **残 2 obligation**: (a) 同定 `hyp.C = cSub` ((11.6) C=U' 経由)、(b) (9.11) induction port (engine assembly)。
両方 lane-a §11 ungated。(a) が (b) の前提 (family 一致) ゆえ次は (a)。

## 🔬 update⁴⁷ (2026-07-07 lane-a /loop) — ★ 同定 `hyp.C = cSub` の正確な route = (11.7) H0=1 (update⁴⁶ の (11.6) 予想を訂正)

Coq PFsection11.v 精読で同定 route を確定。**update⁴⁶ の「(11.6) C=U' 経由」は不正確**、正しくは
**(11.7) H0=1 経由** (Coq `Ptype_Fcompl_kernel_cent`)。

- **Coq §11 C = `'C_U(H)`** (PFsection11.v:82) = **Lean `hyp.C` と一致** (S13 `C_eq_centralizer`)。設計は正しい。
- **同定 `cSub = hyp.C` = Coq `Ptype_Fcompl_kernel_cent`** (PFsection11.v:543):
  `Ptype_Fcompl_kernel MtypeP :=: C`。`Ptype_Fcompl_kernel` = U-action on H̄ の kernel = **cSub** (Lean)。
  証明は **`H0_1` (H0=1) を使う** (:545 `group_inj H0_1`)。H0=1 ⟹ H̄=H ⟹ cSub = C_U(H̄) = C_U(H) = hyp.C。
- **H0=1 は Coq §11 の section 事実** (PFsection11.v:541 `Let H0_1 : H0 :=: 1%g` via
  `FTtype34_Fcore_kernel_trivial`) = **Peterfalvi (11.7)** (:396 `p.-abelem H ∧ |H|=p^q ∧ H0=1`)。
  (11.7) は (10.8) gated。Lean 側 = `S13.core_structure` (11.7、S13:332、**sorried** = 既知 deep gate)。

### ⟹ hY route の依存鎖 (完全確定)
`hY = coherent(sOf(H0C))`
  ⟸ `coherent(sOf(H0Cprime))` [(9.11) port, ungated] + `𝒮(H₀C) witness` [nonemptiness]  ← **landed bridge**
  ⟸ 同定 `hyp.C = cSub` [(11.7) H0=1 経由、`Ptype_Fcompl_kernel_cent` port] ← **(11.7) sorried gate cite 可**
  ⟸ (11.7) H0=1 [core_structure, sorried] ⟸ (10.8) [deep]。

∴ hY の **ungated genuine math = (9.11) induction port** (engine assembly、cSub-based family)。
同定は (11.7) を cite して port (proof は `ker(uActionHom)=C_U(H)` の unfold、H0=1 で H̄=H、~30-50 行)。
capstone は加えて §14 glue (ν/hmixed/hDτ) も要 (lane b/c/§14 Dade) ゆえ lane-a 単独では閉じない
(既知)。**次 iteration = (9.11) port の genuine assembly に着手** (subcoherent(sOf(H0C')) 組立 →
base-case constant-degree → coherentPairChain extension)。同定は (11.7) cite で並行 or 後続。

## 🔬 update⁴⁸ (2026-07-07 lane-a /loop) — ★ 同定 `hyp.C = cSub` の proof path 完全確定 + step 1 landed

同定に要る全 lemma を code-level 確定。**(11.7) H0=1 は既に landed/citable** (S13_CoreStructure):
- `chief_H0_eq_bot` (S13_CoreStructure:1144): `chief.H0 = ⊥` = (11.7) crux (case-B/A dichotomy assembly、
  sorried の可能性あるが signature 正)。`H_elementaryAbelian` (:1210) が corollary。
- **★ landed 本 iteration**: `chief_N_eq_bot` (S13_CoreStructure): `chief.N = ⊥` (H0=⊥ + H0_eq +
  map_eq_bot_iff)。H_elementaryAbelian の inline を抽出 + refactor (de-dup)。= 同定の step 1。

### 同定 `Hypothesis.C_eq_cSub : hyp.C = S11.cSub hyp.s11Setup hyp.chief` の proof path (4 step)
1. **`chief.N = ⊥`** — `chief_N_eq_bot` (landed)。
2. **`cSub = (U.subgroupOf L ⊓ ker(quotientMulAutHom)).map L.subtype`** — S11 `cSub_normalized_by_uW1`
   proof 内の `hcSub` (S11:1741、要抽出 or 再証明)。L = U⊔W1。
3. **`ker(quotientMulAutHom chief.N_aInvariant) = ker(typeP_conjAction)` (N=⊥ 時)** — `quotientMulAutHom_apply`
   (Isaacs Ch04:2360, `qMAH a (g:H⧸N) = (φ a g : H⧸N)`) + N=⊥ ⟹ `(x:H⧸⊥)=(y:H⧸⊥) ↔ x=y`
   (QuotientGroup.mk mod ⊥) ⟹ `qMAH a = 1 ↔ φ a = 1`。φ = `typeP_conjAction`。
4. **`ker(typeP_conjAction) realized in U = C_U(H) = hyp.C`** — `typeP_conjAction_apply` (S11:209,
   = conjugation `(a:G)*x*(a:G)⁻¹`) ⟹ `φ a = 1 ↔ a ∈ centralizer(H)`; `C_eq_centralizer`
   (`hyp.C = U ⊓ centralizer(H)`) で結合。

⟹ 見積 40-80 行 (step 3-4 が crux)。**次 iteration = C_eq_cSub を書く** (step 1 landed、path 明確)。
これで capstone hY family (sOf(H0 ⊔ hyp.C)) = (9.11) family (sOf(H0 ⊔ cSub)、H0=⊥ で cprimeSub=
derivedInG cSub=derivedInG hyp.C=H0Cprime) が一致 → (9.11) port が hcoh を直接供給。

## 🔬 update⁴⁹ (2026-07-07 lane-a /loop) — ★ C_eq_cSub LANDED (同定完了) — capstone family = (9.11) family

同定 `S13_CoreStructure.C_eq_cSub : hyp.C = S11.cSub hyp.s11Setup hyp.chief` を **sorry-free landing**
(full build green, axiom-clean)。update⁴⁸ の 4-step path を実装:
- **forward** (`C_U(H) ≤ cSub`): `S11.mem_cSub_of_mem_U_of_centralizes` (既存、centralize H ⟹ H̄ trivial)。
- **reverse** (`cSub ≤ C_U(H)`, N=⊥ 使用): x∈cSub の ker(uActionHom) 成員 a を unfold →
  `quotientMulAutHom_apply_mk'` で coset action → `chief_N_eq_bot` (N=⊥) で `mk' N` injective
  (`ker_eq_bot_iff` + `ker_mk'`) → `typeP_conjAction l ⟨g,·⟩ = ⟨g,·⟩` → `typeP_conjAction_apply`
  (conjugation) で `x*g*x⁻¹=g` → `mul_inv_eq_iff_eq_mul` で `g*x=x*g`。s11Setup↔base は
  `setup_typeP_eq` で bridge。

### ⟹ hY route の同定 gate CLOSED。残 = (9.11) port のみ (ungated genuine math)
同定完了で **capstone hY family `sOf(hyp.H0C)` と (9.11) family が cSub 経由で一致**。残る hY
obligation は:
- **hcoh = coherent(sOf(hyp.H0Cprime))** = (9.11) `Ptype_core_coherence` port (engine assembly、
  update⁴⁵ 在庫の irrSubcoherent → coherent_subset_of_constant_degree → coherentPairChain)。
  H0Cprime = chief.H0 ⊔ derivedInG hyp.C、C_eq_cSub で = chief.H0 ⊔ cprimeSub (S11) と一致可。
- **hwit = 𝒮(H₀C) nonemptiness** = `caseA_exists_irreducible_sOf_H0C` (case split)。
両方 lane-a §9-11 ungated。**次 iteration = (9.11) port assembly か hwit** に着手。
(capstone は加えて §14 glue も要、lane-a 単独では非閉 — 既知。)

## 🔬 update⁵⁰ (2026-07-07 lane-a /loop) — ★ (9.11) port target を訂正: SOf(H0Cprime) = inducedKernelFamily (Coq S_ H0C')

Coq family variant を精査 → **(9.11) port target は `SOf(H0Cprime)` (= §10 inducedKernelFamily =
Coq `S_ H0C' = seqIndD HU M HU H0C'`)** であり、`sOf(H0Cprime)` (H-version) でない、と確定。
これで port が S08 subcoherent/witness 機構 (coherent_SOf_HC が使う inducedKernelFamily 系) を
再利用可 = **port の de-risk**。

- Coq (11.3) `cohS2 = coherent(S2=sOf(H0C))` は `subset_coherent(Ptype_core_coherence)` で、
  Ptype_core_coherence = coherent(`S_ H0C'` = seqIndD HU M **HU** H0C')。sOf(H0C) ⊆ S_ H0C' を
  seqIndS で直接 restrict (H-version sOf(H0Cprime) を経由しない)。
- Lean 対応: `SOf(Y) = inducedKernelFamily((derivedInG M).subgroupOf M)(Y.subgroupOf M) = S_ Y`
  (HU=M'=derivedInG M)。∴ (9.11) port = coherent(`hyp.SOf hyp.H0Cprime`)。

### ✅ landed 本 iteration: `coherent_sOf_H0C_of_coherent_SOf_H0Cprime` (S13, 正しい bridge)
`coherent(SOf(H0Cprime)) + 𝒮(H₀C) witness → hY`。subset `𝒮(H₀C) ⊆ SOf(H0Cprime)` =
`sOf_subset_SOf` (sOf⊆SOf) + `inducedKernelFamily_antitone` (H0Cprime≤H0C) → isCoherent_of_subset。
旧 `coherent_sOf_H0C_of_coherent_sOf_H0Cprime` (sOf(H0Cprime) 経由) は superseded (残置、無害)。

### ⟹ 残 hY obligation (訂正後)
- **hcoh = coherent(`hyp.SOf hyp.H0Cprime`)** = (9.11) port。target = inducedKernelFamily(H0Cprime)
  ⟹ subcoherent 組立は S08 inducedKernelFamily 機構 (pairwise_orthogonal/hasNoRealCharacters/
  closedUnderConjugate) を直接使える (coherent_SOf_HC の witness pattern と同型)。
- **hwit = 𝒮(H₀C) nonzero witness** = 別途 (reducible_mem_sOf_H0C で member、sOf conjugate-closure +
  conjDiff support + no-real で ζ.conj-ζ)。sOf-world witness 機構要 (~50 行)。
次 = (9.11) port (SOf(H0Cprime) の subcoherent → constant-degree base → pair-chain) か hwit。

## 🔬 update⁵¹ (2026-07-07 lane-a /loop) — ★ sOf_closedUnderConjugate landed (hwit step 1)

`S13.sOf_closedUnderConjugate` (`ClosedUnderConjugate (sOf data Y)`) を sorry-free landing
(inducedKernelFamily_closedUnderConjugate S08 を mirror)。φ=induceHU χ ∈ sOf(Y) → φ.conj =
induceHU(χ.conj) ∈ sOf(Y): `characterKernel_conj` で xiSet (H⊄ker) + Y-kernel 条件 保存、
`induceHU_eq_induce` + `ClassFunction.induce_conj` で induce∘conj 交換。= hwit の conjugate-closure。

### hwit (𝒮(H₀C) nonzero witness) の残ピース
- ✅ conjugate-closure: `sOf_closedUnderConjugate` (本 iteration)。
- ⏳ member ζ ∈ sOf(H0C): `reducible_mem_sOf_H0C` (reducible member、reducible_count_sOf_H0=p-1>0)。
  **要 `Section11CharacterData` の hyp からの構成** (hyp に chars field あるか要確認、無ければ構成)。
- ⏳ ζ.conj-ζ A0-support + ≠0: `inducedKernelFamily_conjDiff_support` / `_hasNoRealCharacters`
  (ζ∈SOf(H0C)=inducedKernelFamily via `sOf_subset_SOf`)。
- ⏳ C_eq_cSub bridge: sOf(hyp.H0C) = sOf(chief.H0 ⊔ chars.C) (hyp.C=cSub=chars.C)。
⟹ 次 = hwit assembly (chars 構成 + 上記結合) or (9.11) port。

## 🔬 update⁵² (2026-07-07 lane-a /loop) — ★ capstone gate の正確な picture + §14 label 訂正 (ユーザー質問契機)

ユーザー「§14 glue は誰の担当?」→ 精査で **glue は全部 lane a 自身 (S12) の担当**と判明。過去 update の
「§14/lane b/c gated」は**私 (lane a) の誤り** (prior session の不正確な hedge label を過度一般化)。

### ✅ capstone `coherent_Sset_of_column_identities` (S12:4291) の実際の gate (全 lane a)
proof (4306-4358) を精読 → 残 sorry は**厳密に 2 つ** + unsound hgen cite:
- **`hmixed`** (S12:4322 sorry): `⟨coh.extension x, hY.extension y⟩ = 0` = (6.7) image-side 直交
  ("b≡0 congruence")。両 coherent extension の像の直交 = "beyond bare IsCoherent" の Dade content。
- **`hDτ`** (S12:4330 sorry): `hY.extension(∑μ) = ∑ω^σ` = (5.8) column identity。hY.ext が μ-column を
  σ-grid ω^σ に送る specific 性質 = Dade content。
- **hgen**: `hgen_of_S2_uniform_degree` (algebra は landed sorry-free) だが `Sset_diff_SHCSet_apply_one_eq_qu`
  (= 非Galois で偽 uniform-degree) を cite → **unsound route** (world-bridge が置換)。
- **hY**: `coherent_Sset_diff_SHCSet` (S12:4059 sorry) = §10 world の (9.11) difference coherence。
- **ν**: `exists_glue_nu` (S12:4113) = **landed sorry-free**。

docstring (S12:4370): hmixed/hDτ = 「**the sole remaining genuine §11 character content**」。

### ⚠ 2-world 状況 (重要) — active path は §10、私の S13 work は redesign
- **active bare-sorry path** = `exists_zeta_residual_not_orthogonal` (S12:4460) → **S12 §10-world capstone**
  `coherent_Sset_of_column_identities` → hY = `coherent_Sset_diff_SHCSet` (§10 inducedFamily world) +
  unsound hgen。
- **私の S13 §9-world work** (C_eq_cSub / SOf-bridge / sOf_closedUnderConjugate) = **world-bridge redesign**
  で、S12 の unsound uniform-degree を sound な (9.11) route に置換するもの。だが**まだ bare sorry に
  wire されていない** — S13 capstone `coherent_SOf_H0C_of_glued` を bare sorry に再配線する必要。

### ⟹ 正確な残 work (全 lane a、§14 でない)
1. **hmixed** (6.7 image 直交、b≡0) — 両 extension の像直交。Dade content、deep。
2. **hDτ** (5.8 column identity) — hY.ext(∑μ)=∑ω^σ。Dade/σ-grid content、deep。
3. **hY** (9.11 coherence) — §9 world (私が構築中) or §10 world (`coherent_Sset_diff_SHCSet`)。
4. **hgen sound 化** — world-bridge で uniform-degree を置換 (進行中)。
5. **re-wiring** — bare sorry を S13 world-bridge capstone に接続。

hmixed/hDτ (1,2) は hY.extension の specific 性質ゆえ hY 構築後。∴ **hY が依然 upstream**。ただし
generic (9.11) coherence が hDτ の σ-grid 性質を与えるかは要検討 (与えないなら Dade 構築が別途要)。

## 🔬 update⁵³ (2026-07-07 lane-a /loop) — ★ inducedFamily_degreeSubfamily_isCoherent landed = (9.11) 定次数 base-case engine

(9.11) port の subcoherent base を精査 → **SHC_isCoherent が使う `inducedFamily_isCoherent_of_equalDegreeFamily`
(S12:1044) は R-datum-free** (Dade constant-degree engine `coherentEqualDegree_fromDade`)。∴ **定次数
subfamily の coherence は R-datum 無しで作れる** (full mixed-degree の induction とは別)。

### ✅ landed (S12, axiom-clean, full build green)
`S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent (d : ℕ) (hex : ∃ ζ∈inducedFamily, irr ∧ deg d)`:
degree-`d` の irreducible subfamily `{φ∈inducedFamily | irr ∧ φ1=d}` の coherence。SHC_isCoherent
(d=w₁ 固定) を任意 `d` に一般化 (enumerate via equivFin + conjugate-pair で ≥2 + equalDegree engine)。
= **(9.11) induction の constant-degree base case** (Coq `filter [deg==qa] S_ H0C'` → `uniform_degree_coherence`
に対応)。

### ⟹ (9.11) port の構造 (再確認)
- **base**: `inducedFamily_degreeSubfamily_isCoherent` (landed) で定次数 subfamily (Galois 全体 qu /
  非Galois qa-subfamily) の coherence。R-datum-free。
- **extension**: qa-base から full `S_ H0C'` へ `coherentPairChain` + `xAdjoinStepW` で 1 pair ずつ拡張。
  **reducible 成員 (mu_j) を含むため、この extension は full R-datum (Dade image) を要する = deep**。
- ⟹ base は landed、extension (reducible 込 + σ-grid) が残 deep content。

### ⚠ 実務ノート (この iteration の教訓)
IsCoherent を返す S12 lemma は **`open scoped FiniteInduce in`** が必須 (Fintype/Invertible の
scoped instance 供給; 無いと signature で `Fintype ↥M` synth 失敗)。

## 🔬 update⁵⁴ (2026-07-07 lane-a /loop) — ★ inducedFamily_irreducible_Rdatum landed = subcoherent R-datum の irreducible 半分

`S12.Hypothesis.inducedFamily_irreducible_Rdatum (χ : IrreducibleCharacter) (hχ : χ∈inducedFamily) :
CharacterDifferenceImage hyp.tau χ` を sorry-free landing。`dadeCharacterDifferenceImageOfDiff`
(S07:5729, Dade R-datum producer) に hyp.tau (= dadeIntegralCharacterMap hyp.dadeData.dade …,
S12_Core:404) + hreal (inducedFamily_hasNoRealCharacters) + hdiffsupp (inducedFamily_sub_support、
degree eq は irreducibleCharacter_apply_one_eq_pos_natCast + star_natCast) を供給。

= **subcoherent(S_ H0C') R-datum の irreducible 半分** ((9.11) induction の extension が要する)。
残 = **reducible (mu_j) の R-datum** (tau_muGrid_row_diff 経由、deep) + subcoherent 組立 (irrSubcoherent)
+ induction (coherentPairChain) + hmixed/hDτ (σ-grid)。

⟹ 直近 2 iteration で (9.11) port の base engine (update⁵³) + irreducible R-datum (本) を landing。
circling から concrete landing に復帰。次 = reducible R-datum か subcoherent 組立。

## 🔬 update⁵⁵ (2026-07-07 lane-a /loop) — ★★ 重大: (9.11) は lane-b (S15) が並行構築済 + mixed-degree extension は S07 Hypothesis の isometry で構造的にブロック

### ① lane-b (S15) が (9.11) base + Galois を並行構築済 (coordination miss)
`S15.Hypothesis.sSetIrrDeg_subcoherent` (S15:~1393、lane b) が **degree-d irreducible subfamily の
subcoherent** を irrSubcoherent + per-member R-datum (`sSet_member_differenceImage`) で構築済。
docstring: 「ready for `coherent_subset_of_constant_degree` (the (9.11) base + Galois)」。
- ⟹ **私の S12 `inducedFamily_degreeSubfamily_isCoherent` + `inducedFamily_irreducible_Rdatum` は
  §11.8 family (`inducedFamily M`) 向けの並行構築** — S15 を先に確認すべきだった (claim-before-build 違反)。
  ただし family は異なる (§11.8 の inducedFamily vs S15 §13 の hyp.S) ので literal 重複でなく、
  §11.8 lane-a work として genuine (保全)。理想は family-parameterized 一般化 + lane-b と coordinate。

### ② ★ mixed-degree extension の構造的ブロッカー (両レーン共通)
- **S07.Hypothesis (subcoherent) の `tau_isometry_diff` (S07:1777) は全 member 差分の isometry を要求**
  (`∀ a b c d ∈ S, ⟨τ(a-b),τ(c-d)⟩=⟨a-b,c-d⟩`)。docstring (S07:1774): FT Dade map は global isometry
  でなく **A-supported 差分でのみ成立** = **equal-degree family 限定**。
- ∴ `sSetIrrDeg_subcoherent` (degree-d = equal-degree) は OK だが、**full mixed `S_ H0C'` (qa+qu+reducible)
  は S07.Hypothesis を組めない** (mixed 差分は non-supported、isometry 偽)。
- Coq (9.11) の subcoherent は **degree-0 (L^#-supported) isometry** (5.2) で mixed でも成立。
  Lean S07.Hypothesis は all-differences に **over-specified** ⟹ mixed 不可。
- ⟹ **(9.11) non-Galois mixed extension は Lean に無い degree-0-isometry subcoherent 構造を要する** =
  構造的 deep work (S07 = lane b の isometry field 弱化 or 新構造)。base+Galois は両レーンで済むが、
  non-Galois mixed が両レーンで未達 (= isometry 構造ブロック)。

### ⟹ 帰結 (honest)
- (9.11) hY route の deep 核 = **mixed-degree subcoherent 構造** (degree-0 isometry) = 未構築、S07 (lane b) 絡み。
- 私の S12 base+R-datum は §11.8 向けに genuine だが lane-b と並行 (要 coordinate/一般化)。
- **これは incremental lane-a landing でなく、cross-lane 構造判断** (S07 isometry の弱化 or 新 mixed subcoherent)。
  hub/lane-b coordination 案件。次: reducible R-datum は mixed subcoherent が要るので、それ以前に構造を要解決。

## 🧭 HUB RULING (2026-07-07, update⁵⁵ への回答): S07 isometry 弱化 = Option A 確定 → issue 0099

update⁵⁵ の両論点を hub が調査・裁定した (workflow wf_4f8e7eca、Coq trace + Lean census):

1. **② 構造ブロッカー → 裁定 issue 0099**: claim は**正しい** (Coq subcoherent の isometry は
   `'Z[S, L^#]` のみ、PFsection5.v:488)。`tau_isometry_diff` (S07_Coherence.lean:1777 — 位置は
   S07_Subcoherent でなくこちら) を **zSupportedSpan 形へ in-place 弱化** (equal-degree 差分形では
   不足 — weighted combo 要)。**owner = b** (6 file 中 5 が b 所有)、blast radius ~15-20 宣言・機械的。
   弱 field は全 instantiation site が既存 brick で無条件 discharge 可 (mixed 含む)。landing 後、
   (9.11) mixed route は S07.Hypothesis を mixed family で組める。
2. **① a/b 並行構築 → 両方 keep**: S12 `inducedFamily_degreeSubfamily_isCoherent` (a) と S15
   `sSetIrrDeg_subcoherent` (b) は family が異なり両方 genuine (成果保全)。family-parameterized
   一般化は optional follow-up。

## 🔬 update⁵⁶ (2026-07-07 lane-a 再開) — ★ 0099 検証完了: 第二 field 障害の特定 + (9.11) Lean-native route 確定 (全 pieces = lane a 圏)

0099 最終 checkbox「mixed family で S07.Hypothesis を組めるか」を検証 → **完了** (詳細 = 0099
「検証記録」節)。要点:

### ① 検証結果: literal mixed 組立は依然 NO — `difference_image` が第二の field 障害
- `CharacterDifferenceImage` (S07_Coherence:395) = `τ(χ−χ̄) = ε(μ−ν)` の **2-element 固定**
  (‖image‖²=2)。reducible μ_j (‖μ_j‖²≥2) では 0099 弱形 isometry から ‖τ(μ_j−μ̄_j)‖² = 2‖μ_j‖² ≥ 4
  → **norm 矛盾で unconstructible** (2032/frobI 型偽 field)。family は genuinely mixed
  (μ_j ∈ S_H0C ⊆ S_H0C′、Coq 9.5/9.8) ゆえ S07.Hypothesis の mixed 組立は不可のまま。
- Coq subcoherent (d) の R ξ は**可変長** orthonormal seq — 2-element は既約特殊化。
  (5.4)/(5.6)/(5.7) は可変長を本質使用。**(9.11) induction は extend_coherent (5.6) 一本で
  chi の既約性を使わず reducible μ_j も adjoin** (PFsection9.v:1658-1667 を精読確認)。

### ② しかし (9.11) port は mixed S07.Hypothesis を必要としない — Lean-native route
Lean の extension 機構は S07.Hypothesis 非依存 (S04 Dade 直接) で、可変長 R-datum の対応物
**`CharacterPsiDecomposition.imageFamily`** (ofProjection producer) が既存。`xAdjoinStepW`
(S08_CoherenceWeighted:287) は S₁-side member の reducible (mc>1、Dmem で R-datum 受領) を
設計済み — 未対応は **adjoin 対象 χ の既約性固定のみ**。

### ③ (9.11) port の missing pieces (全て lane a 圏、Coq 文書順)
1. **base case**: SOf(H0Cprime) の deg-d irreducible subfamily coherence — update⁵³ S12 engine の
   SOf 版 (irrSubcoherent [S07_Subcoherent = **a 所有**] + 0099 弱形 isometry)。
2. **(9.11.1) wlog + norm-chain**: S1=qa-subfamily counting (typeP_nonGalois_characters (d) 系)
   + squeeze 在庫 (S07_Subcoherent:445-542、sorry-free)。
3. **extension loop**: irreducible adjoin = xAdjoinStepW 現形 / **reducible μ_j adjoin =
   xAdjoinStepW の χ-既約性 (hχχ : ‖χ‖²=1) を norm-mc 化した一般化** (S08_CoherenceWeighted =
   **a 所有** — b の coherence 例外 glob は S07_Coherence*+S08_PGroupReduction のみ)。
4. **μ_j R-datum**: CharacterPsiDecomposition via ofProjection + σ-image family (S12 muGrid = a)。
S07_Coherence (b 所有) は既存 def の cite のみで**構造変更不要** → cross-lane 裁定不要。
S07.Hypothesis 可変長化 (Coq-faithful) は不要につき起こさない。

### ⟹ 次 iteration = step 1 (base case) の CODE: SOf(H0Cprime) 版 degree-subfamily coherence
S13 に `SOf_degreeSubfamily_isCoherent` (SOf(Y) の deg-d irr subfamily coherence) を build
(update⁵³ の S12 版 mirror; witness 機構は coherent_SOf_HC の inducedKernelFamily パターン踏襲)。

## 🔬 update⁵⁷ (2026-07-07 lane-a) — ★ base case LANDED + adjoin engine 在庫の再発見 (update⁵⁶ の missing 評価を訂正)

### ✅ landed: `S13.SOf_degreeSubfamily_isCoherent` (sorry-free, axiom-clean, commit 97766644)
(9.11) base case の SOf-world 版: SOf(Y) の deg-d 既約 subfamily coherence。SOf(Y) ⊆ inducedFamily
(kernel-antitone + bot 同定) で S12 engine を ambient 発火 → isCoherent_of_subset で restrict。
witness = ζ̄−ζ (conj 保存 + conjDiff support + no-real)。∃-witness は Prop-confined
(Type-valued goal での obtain 不可 — S12:1112 と同じ罠を踏んで修正)。

### ★ 在庫再発見 — update⁵⁶ の「missing piece (i)(ii)」は既に landed 済みだった
- **(i) reducible adjoin engine = `xAdjoinStepW_k`** (S08_CoherenceWeighted:459、commit 577a0d69、
  (6.8.3) reducible-break 用に構築済): break pair {χ,χ̄} が reducible column μ_j でよい (5.6)
  weighted adjoin。break decomposition `Da : CharacterPsiDecomposition` をパラメータで受ける。
- **(ii) μ_j R-datum producer = `certainTypeDecompositionDa`** (S06_CertainTypeCoherence:723) +
  S12 bridge `toHypothesis46` (S12_Core:1088) + Ind-form recast `columnConstituentDecomposition`
  (S08_CaseBCoherence2:1691)。
- **chain fold**: `coherentOfPairChainCover` (S07) / `xChainCoherentW` (S08_CoherenceWeighted:786、
  irreducible-pair 版 bundle — mixed chain は coherentOfPairChainCover 直使いで step ごとに
  xAdjoinStepW / xAdjoinStepW_k を発火すれば新 engine 不要)。
- **§9 counting 在庫 (S12_Section9Counts)**: `forall_sOf_H0Cprime_degree_qu_caseB` (caseB で
  SOf(H0⊔C′) 全 member deg qu) / `muGrid_column_sum_mem_sOf_H0_and_reducible` /
  `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (reducible member = μ-column sum) /
  `mkSection11CharacterData` (§10→§9 bridge)。

### ⟹ (9.11) の残 = assembly そのもの (部品はほぼ完備)
- **(A) caseB assembly** (Galois 対応枝、部品完備で着手可能): family 全 member deg qu →
  irr-cut base (landed) + μ-column pairs を xAdjoinStepW_k で 1 対ずつ adjoin + chain fold。
  必要入力: hex (deg-qu irr ∈ SOf(H0Cprime) の存在 witness、caseB (9.9) 系)、per-pair の
  hDeg (2·qu·anchor < Σ deg²/mc、uniform-qu family で計算可)、hgen (span generation)、
  Da instantiation (toHypothesis46 経由)。
- **(B) caseA assembly** (non-Galois、(9.11.1)-(9.11.8)): deg-qa counting ((9.8)(d) lb_Sqa の
  Lean 対応要確認) + norm-chain squeeze (S07_Subcoherent 在庫) + S3 enumeration。
次 iteration = **(A) caseB assembly に着手** (hex witness 供給 → family 分解 → 1-pair adjoin
instantiation の順)。

## 🔬 update⁵⁸ (2026-07-07 lane-a /loop) — ★★ (9.11) target 訂正: sOf (𝒳-系) が正、SOf でない (update⁵⁰ 撤回) + sOf 版 base landed

### ① ★ target 訂正 (Coq 精読)
- **Coq §9 の `S_ Y := seqIndD M^`(1) M M`_\F Y`** (PFsection9.v:209) — **第 3 引数 = M`_\F = H**:
  source は「H ⊄ Ker θ」(𝒳-条件、`X_ Y = Iirr_kerD M' H Y` :208) を課される。∴ **(9.11)
  `Ptype_core_coherence` の family = 𝒳-系 = Lean `sOf`**。
- update⁵⁰ の「target = SOf(H0Cprime) = inducedKernelFamily」は **§11 の notation
  (`S_ := seqIndD HU M HU`, PFsection11.v:90 — nontrivial のみ) との混同で誤り**。撤回。
- 整合確認: `forall_sOf_H0Cprime_degree_qu_caseB` (S12_Section9Counts:77) の family = chars.SOf =
  𝒳-系。SOf (kernel-filter) だと deg-q member (S(HC) 系、H-killing) が混ざり「全 member deg qu」
  は偽 — 𝒳-系だから成立。教科書側の一貫性 ✓。
- **bridges への影響**: `coherent_sOf_H0C_of_coherent_sOf_H0Cprime` (update⁴⁶、sOf 版) が**本線に
  復帰**。SOf 版 bridge (update⁵⁰) は不使用 (無害残置; SOf coherence はより強い主張で (9.11) は
  それを与えない)。SOf 版 base (update⁵⁷ landed) は S(HC)/SOf 系の中間量として有用残置。

### ✅ landed: `S13.sOf_degreeSubfamily_isCoherent` (sorry-free, axiom-clean, commit 7d0ab806)
(9.11) が実際に消費する base: 𝒮(Y) の deg-d 既約 subfamily coherence。sOf-cut ⊆ SOf-cut
(sOf_subset_SOf) で update⁵⁷ の SOf 版から restrict。witness = ζ̄−ζ (sOf_closedUnderConjugate)。

### ② ★ all-reducible ケースの発見 — irr-witness は常には立たない
Coq (9.9)(c): `all redM (S_ H0C') → C=1 ∧ u=(p^q−1)/(p−1) ∧ Frobenius(HU/H0)` — **S_ H0C' が
全 member reducible の退化ケースが排除されていない** (その場合の特殊構造を export するのみ)。
Coq (9.11) は subcoherent (可変長 R-datum) ゆえ irreducibility 不要で場合分けなし。Lean-native
route (irr-cut base) は all-reducible で base が立たない ⟹ **μ-pair base (reducible conj-pair
{μ, μ̄} の 2-element coherence) が caseB assembly の必要部品**:
- 供給源: R(μ) = `certainTypeR` (σ-image family、S06) → extension ν(μ) = R の half-sum
  (‖ν(μ)‖² = ‖μ‖² が orthonormal half-sum で合う)。`coherentPair` (S07) の norm-mc 一般化
  or `certainTypeDecompositionDa` からの直接組立。
- caseB assembly 全体 = seed (irr-pair [coherentPair_fromDade] or μ-pair [新規]) + 残り pairs を
  xAdjoinStepW / xAdjoinStepW_k で adjoin + coherentOfPairChainCover fold。
次 = **μ-pair base の設計調査** (coherentPair の一般化可能性、certainTypeR half-sum 構造)。

## 🔬 update⁵⁹ (2026-07-07 lane-a /loop) — ★ coherentPair_k landed: μ-pair seed の generic 部品

### ✅ landed: `S07.coherentPair_k` (S07_RetargetScaled 末尾, sorry-free, commit 5f68e0a8)
reducible 共役対 {χ,χ̄} の単独 coherence seed — coherentPair の ‖χ‖²≠1 一般化 (S₁=∅、anchor
不要)。Gram-matched X,X̄ を受けて ν := retargetS で構成。調査確定事項:
- `retarget_isCoherent_S`/`retarget_isCoherent_of_extensionImage_k` は **anchor χ₁∈S₁ 必須**で
  seed 不可 → 本 lemma が gap を埋めた。
- **`retargetTargetPair_gen`** (S07_RetargetScaled、既存): ψ=0 `CharacterPsiDecomposition` から
  Gram-matched pair (‖X‖²=‖χ‖² 等) を**計算で**出す producer — coherentPair_k の入力供給源。
- S07_RetargetScaled / S08_RetargetReducible / S08_CoherenceWeighted は **lane a 所有** (b glob は
  S07_Coherence* + S08_PGroupReduction のみ) — この線の build は全て自所有内。

### μ-pair seed の残り (次 iteration)
1. **ψ=0 certain-type decomposition**: `CharacterPsiDecomposition τ_enl μ 0` の producer
   (`certainTypeDecompositionDa` は ψ=a•η₁ 形で ψ=0 にすると support 前提が偽 → 別途組む)。
   部品は S06 に完備: `certainTypeExtension_columnSum` (tau1(μ) = δΣω^σ = X、Y=0)、
   `certainTypeRImage`/`certainTypeR` (imageFamily)、`certainTypeOmegaSigma_inner` (isometry)。
2. **τ seam**: certainTypeR 系は enlarged Dade (h46.dade0) 上 — hyp.tau への retarget は
   S08_CaseBCoherence2 の (6.8.2.3) seam パターン踏襲。
3. seed 組立: retargetTargetPair_gen + coherentPair_k + μ−μ̄ support/nonzero (muGrid API)。

## 🔬 update⁶⁰ (2026-07-07 lane-a /loop) — ★ seedDecomposition landed + all-reducible corner は既存 3 部品で閉じる構図が確定

### ✅ landed: `S06.certainTypeSeedDecomposition` (sorry-free, commit 41a72280)
ψ=0 の `CharacterPsiDecomposition τ' (columnSum χ₂) 0`、coherent-set anchor 不要。
τ₁ = `certainTypeExtension` (σ-extension) 自身: ℤ[𝒯] isometry (`certainTypeExtension_inner_eq`、
基準列 k=χ₂ に μ, μ̄=μ_{χ₂⁻¹} 両方入る)、μ−μ̄ 上 Dade 一致 (columnDiff_eq_dade)、τ' seam は
hagree 引数。imageFamily = certainTypeR transport (image_eq 差し替え)。

### ★ 発見: all-reducible corner は seed 経由より直接的な既存 route がある
- **`S06.certainType_isCoherent`** ((4.9)(b)): `IsCoherent (dadeICM h.dade0 h.tau)
  (certainTypeSet h k) (supportInSubgroup A L)` — **𝒯 全体 (equal-deg μ-columns) の coherence が
  sorry-free で既存**。
- **`S07.IsCoherent.congrMap`** (S08_CaseBCoherence2:1469): zSupportedSpan 上一致する τ' への
  IsCoherent transport — τ seam 部品も既存。
- ⟹ **all-reducible corner = certainType_isCoherent → congrMap (τ' = hyp.tau) →
  isCoherent_of_subset (family = sOf(H0Cprime) ⊆ 𝒯 同定)** の 3 段。coherentPair_k /
  seedDecomposition 経由の pair-chain は不要 (両部品は保全: coherentPair_k は generic (5.6.3)
  seed、seedDecomposition は mixed-corner の Dmem/break 供給部品として (9.11) chain で使う)。

### caseB assembly の確定 map (全部品在庫確認済み)
- **mixed corner** (irr あり): irr-cut base (`sOf_degreeSubfamily_isCoherent` landed) +
  μ-pairs を `xAdjoinStepW_k` で adjoin (anchor = irr norm-1 ✓、break Da =
  `certainTypeDecompositionDa`、S₁-side μ の Dmem = `certainTypeMemberDecomposition`)。
- **all-reducible corner**: 上記 3 段 restrict。
- **残る instantiation work (genuine)**: ①§9 family ↔ certainTypeSet 同定 (S12 muGrid columnSum
  ↔ S06 columnSum、`toHypothesis46` 経由 — S08_CaseBCoherence2 の (6.8) case-B が同じ bridge を
  張った前例あり)、② A0 ↔ supportInSubgroup 同定 + congrMap の一致証明、③ per-pair hDeg
  (2·qu·anchor < Σdeg²/mc) の counting、④ hgen (span generation)。
次 iteration = ① の在庫確認 (toHypothesis46 の中身、CaseBCoherence2 の bridge 実装) →
mixed-corner 1-pair adjoin instantiation。

## 🔬 update⁶¹ (2026-07-07 lane-a /loop) — ★ instantiation work ② COMPLETE: μ-column coherence が hyp.tau/A₀(M) interface で landed

### ✅ landed 本 iteration (S13, 全 sorry-free / axiom-clean)
- **`isCoherent_of_supportedSpan_le`** (commit b8584ac5): support 変更版 restriction
  (ℤ[S,A₂] ⊆ ℤ[S,A₁] なら同一 extension で transport)。
- **`certainTypeSet_isCoherent_A0`** (commit 5d2c6b22): `IsCoherent hyp.tau
  (certainTypeSet (hyp.toHypothesis46 hG hodd) k) hyp.A0` — **update⁶⁰ の instantiation work ②
  が完了**。2 つの seam が予想以上に軽かった:
  - **τ seam = defeq 消滅**: `toHypothesis46` の `dade0 := hyp.dadeData.dade` /
    `tau := ….fullDadeIsometryData hyp.hconj` は `S12.Hypothesis.tau` (S12_Core:404) の構成要素
    そのもの → `certainType_isCoherent` が `IsCoherent hyp.tau …` として**直接型付け成功**
    (congrMap 不要; SibleyDade 側の hmapagree パターンより単純)。
  - **support seam A(M)→A₀(M)**: μ_j は A(M)∪{1} 外で消える (columnSum_support_subset →
    supportedSubmodule 論法で ℤ[𝒯] へ) + 1∉A₀ (one_notMem_A0) ⟹ ℤ[𝒯,A₀] ⊆ ℤ[𝒯,A(M)]。
    witness = certainType_nonzero の μ_{k⁻¹}−μ_k (A⊆A₀ mono)。

### ⟹ 残 instantiation work = ① family 同定が両 corner の共通 prerequisite
- **① certainTypeSet ↔ §9 sOf(H0Cprime) の μ-part**: sOf(H0Cprime) の reducible member =
  μ-column sum (S12_Section9Counts `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` が
  muGrid 形で保持) — **S12.muGrid columnSum ↔ S06.columnSum (toHypothesis46) の同定**が核。
  muGrid の定義が toHypothesis46 の columnFamily 経由なら defeq 級 (要確認)。
- all-reducible corner: 同定① → `isCoherent_of_subset` で closed (3 段完成)。
- mixed corner: irr-cut base + xAdjoinStepW_k adjoin (③ hDeg counting / ④ hgen が per-pair 入力)。
次 iteration = ① muGrid ↔ S06 columnSum の定義 trace → 同定 lemma。

## 🔬 update⁶² (2026-07-07 lane-a 再開) — ★ instantiation work ① 核 LANDED: muGrid 列和 = S06 columnSum (world-join)

### ✅ landed (S12_Section9Counts + S13, 全 sorry-free / axiom-clean, commits 2aff3dc5 / 0c6b15e7)
- **`toHypothesis46_toHypothesis`**: (toHypothesis46).toHypothesis = (toCertainTypeHypothesis).toHypothesis
  (projection rfl term)。
- **`Hypothesis.muColumnChar`**: μ-grid 列 j の W₂-dual character 抽出 (muGrid 定義内の
  `finCardEquivCharacterGroup (finCongr …) j` を statement 可能な def に)。
- **`Hypothesis.muGrid_columnSum_eq_columnSum`**: `Σᵢ muGrid i j = S06.columnSum (toHypothesis46 …)
  (muColumnChar j)` — **§10 ↔ §6 world-join の核**。これで `certainTypeSet_isCoherent_A0` が
  `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` の μ-列和に接続。
- S13 `certainTypeSet_isCoherent_A0` の data instance を statement から除去 (scoped 統一 refactor)。

### ⚠ Lean 罠 (メモリ lean-instance-defeq-traps §5 に恒久記録)
statement 明示の [Fintype ↥(W1⊔W2)] 等 data instance は**全称自由変数**となり証明内 scoped
FiniteInduce instance と unify 不能 (data ゆえ irrelevance 無し) — `with_unfolding_all rfl` の
@-explicit エラー表示で初めて可視化。fix = data instance を落とし scoped 統一 (NeZero は Prop で残害無)。
tactic-def 同士の同定は「同一 let/have 列を set で再構築 → show → unfold; rfl」(rw[set-def] は
h-依存 haveI で motive 破綻)。

### 残 (all-reducible corner 3 段の最終 piece)
sOf(H0Cprime) reducible member → certainTypeSet membership の合成で残るのは:
1. **`muColumnChar j ≠ 1 ⟺ j ≠ 0`** (finCardEquivCharacterGroup_zero + Equiv injectivity、小)。
2. **deg 条件** (基準列 k との一致): (10.3) cross-column constancy = `muGrid_apply_one_eq` (hw2
   prime 要)。
3. 合成 lemma: reducible φ ∈ SOf/sOf(H0Cprime) → φ ∈ certainTypeSet h46 k (1+2+S12_Section9Counts:572
   +update⁶² world-join)。
その後 mixed corner (③ hDeg / ④ hgen)。次 iteration = 残 1→2→3。

## 🔬 update⁶³ (2026-07-07 lane-a /loop) — ★ all-reducible corner の membership pieces 完備 (残 1→2→3 全 landed)

### ✅ landed (S12_Section9Counts, sorry-free ×3, commit 83092b0c ほか)
- **`muColumnChar_ne_one`**: j ≠ 0 → μ-列の W₂-dual ≠ 1 (fCECG_zero + Equiv injectivity)。
  ⚠ `rw [← fCECG_zero] at heq` は instance 表記差で pattern 不一致 → goal 方向 rw + exact に変更。
- **`muColumnChar_columnSum_apply_one_eq`**: (10.3) cross-column deg 一致を §6 columnFamily
  interface で (world-join を 1 で評価、map_sum AddMonoidHom.mk' + muGrid_apply_one_eq entrywise)。
- **`reducible_mem_inducedKernelFamily_mem_certainTypeSet`**: 任意 kernel filter S(B) の reducible
  member ψ → ψ ∈ certainTypeSet (toHypothesis46) (muColumnChar kref) (kref ≠ 0 任意、hw2 prime)。

### ⟹ all-reducible corner の残り = S13 family-level assembly のみ (~40 行)
「sOf(H0Cprime) が all-reducible ⟹ coherent(sOf(H0Cprime), A0)」: sOf ⊆ SOf = inducedKernelFamily
(sOf_subset_SOf + SOf_eq) → per-member 上記合成で ⊆ certainTypeSet → `certainTypeSet_isCoherent_A0`
+ `isCoherent_of_subset` (witness = sOf の μ̄−μ、conjDiff 系 landed パターン)。
mixed corner (③ hDeg counting / ④ hgen) は別途。次 iteration = S13 assembly。

## 🔬 update⁶⁴ (2026-07-07 lane-a /loop) — ★★ (9.11) all-reducible corner CLOSED (end-to-end sorry-free)

### ✅ landed: `S13.coherent_sOf_H0Cprime_of_allReducible` (commit 2343f0f7, axiom-clean)
(9.9)(c) corner: `𝒮(H₀C′)` 全 member reducible ⟹ `IsCoherent hyp.base.tau (sOf … H0Cprime) A₀`。
一発 green。組立 = certainTypeSet_isCoherent_A0 (基準列 muColumnChar kref、ne_one) → per-member
membership (sOf→SOf→inducedKernelFamily→reducible 合成、chief = exists_chiefFactorData.choose、
hw2 = params.w2_prime) → isCoherent_of_subset (witness ζ̄−ζ)。

### (9.11) base 側の到達状況 (両 corner 完備)
- **irr seed あり**: `sOf_degreeSubfamily_isCoherent` (update⁵⁸) — deg-d 既約 cut coherence。
- **all-reducible**: 本 lemma。
- **残る (9.11) 本体 = mixed corner の induction**: irr-cut base に μ-column pairs を
  `xAdjoinStepW_k` で adjoin する chain — per-pair 入力 (③ hDeg = 2·deg·anchor < Σdeg²/mc の
  counting、④ hgen = span generation、Da = certainTypeDecompositionDa/seedDecomposition、
  hortho_mem = certainTypeR 直交系) の instantiation + fold (coherentOfPairChainCover)。
  ここが Coq (9.11.1)-(9.11.8) の本体 (norm-chain wlog 込み) で、caseB (uniform-qu) を先に
  (全 member 同 deg で hDeg 計算が単純)、非 Galois caseA (qa/qu mixed) を後に。
次 iteration = mixed corner の 1-pair adjoin instantiation (caseB 形から)。

## 🔬 update⁶⁵ (2026-07-07 lane-a /loop) — mixed corner 1-pair adjoin の入力→supply 完全 map (handoff、composite は次 iteration で build)

xAdjoinStepW_k (S08_CoherenceWeighted:459-599) を精読し全入力の supply 元を確定。composite
`adjoin_muColumnPair_of_irrCut` (S13、~200 行) の設計:

### 設計判断: adjoin pair は S06 columnSum 表記で組む
χ = `columnSum h46 χ₂` (χ₂ = muColumnChar k / 一般 W₂-dual、χ₂ ≠ 1)、χ̄ = `columnSum h46 χ₂⁻¹`
(columnSum_conj_eq)。§12 muGrid 表記への変換は family 分解側で world-join を使う (adjoin engine
自体は S06 表記が最短)。τ = hyp.tau は dadeICM hyp.dadeData.dade (fullDadeIsometryData hyp.hconj)
と defeq (S04.Hypothesis 引数 = hyp.dadeData.dade、hconj = hyp.hconj、A = typePA0 →
suppIn = hyp.A0 ✓ certainTypeSet_isCoherent_A0 で実証済)。

### 入力 → supply 元 (17 項目)
| 入力 | supply | 状態 |
|---|---|---|
| hS₁ | `sOf_degreeSubfamily_isCoherent` (irr-cut, d=qu) | ✅ landed |
| hdiffsuppχ | `columnDiff_support_subset` (S06:302) + columnSum_conj_eq + A(M)→A₀ mono | ✅ 組める |
| hχχne | columnSum_def + `columnFamily_mu_sum_inner` 対角 = w1 ≠ 0 | ✅ 組める |
| hχbarχbarne | conj 側同様 (χ₂⁻¹ 対角) | ✅ |
| hχχbar/hχbarχ | mu_sum_inner off-diag + `column_inv_ne_self` | ✅ |
| hχ_S1/hχbar_S1 | μ ∈ inducedFamily (`muGrid_column_sum_mem_inducedFamily`+world-join or 直) ⊥ irr-cut member (distinct: reducible vs irr) via `inducedKernelFamily_pairwise_orthogonal` | ✅ 組める |
| s/χmem/deg/i₁ | irr-cut の Finset enumeration (equivFin パターン、deg ≡ 1) + anchor 選択 | 機械的 |
| hmemdegdiffsupp | equal-deg (qu) 差の support = `inducedKernelFamily_scaledDiff_support` 系 | ✅ |
| hmemS1/hmemortho/hanchorNorm | irr-cut 定義 + `irreducibleCharacter_inner_eq_ite` (mc ≡ 1) | ✅ |
| **a** | = 1 (caseB: μ(1) = w1·u = qu = anchor(1) — uniform-qu で係数 1) | ✅ |
| Dmem | `memberExtensionDecomposition` (irr member 用 ψ=0、S07/S08 — 所在確認) | 要確認 |
| Da | `certainTypeDecompositionDa` (ψ=a·η₁=χ₁; hμη₁supp = equal-deg diff support ✓、htau1_mema = Dade ZIrr ✓、hχψ/hχbarψ = μ⊥χ₁ ✓) | ✅ 組める |
| hDatau1 | rfl (ofProjection の tau1 = dadeICM) | ✅ |
| hortho_mem | `certainTypeR_imageSet_orthogonal_dadeOfDiff` (S06、column ⊥ irr-break の向き確認) | 要確認 |
| htau1Dmem | memberExtensionDecomposition 設計で rfl | 要確認 |
| htau1_memaχ | `dadeIntegralCharacterMap_mem_ZIrr_of_supported` (μ−χ₁ supported + ZIrr) | ✅ |
| ha1 | rfl (deg ≡ 1) | ✅ |
| **hDeg** | 2·1 < Σ 1²/1 = \|irr-cut\| ⟹ **\|irr-cut\| ≥ 3 の counting** | **named hypothesis** |
| hSgen | equal-deg family: x = (x−χ₁)+χ₁、x−χ₁ supported | ✅ (`zSupportedSpan_range_subset_span_sub_zero` 系) |
| hgen | uniform-deg collapse (S₁∪pair 全員 deg qu) | ✅ 組める (~30 行) |

### ⟹ 残る genuine gap = hDeg counting (\|irr-cut\| ≥ 3) のみ、他は組立
counting は §9 の X_H0C' サイズ下界 ((9.9)(a) Galois / (9.8)(d) 非Galois lb_Sqa) — named
hypothesis で前倒しし、§9 counting は別 piece。次 iteration = composite を上記 map 通りに build
(Dmem/hortho_mem の 2 「要確認」を先に grep)。

### 「要確認」2 点の確認結果 (2026-07-07 次 iteration 冒頭)
- **`memberExtensionDecomposition`** (S08_CoherenceCorePart1:1554) ✅ そのまま使える: 入力 =
  hS₁ + χ irr ∈ S₁ + χ̄ ∈ S₁ + non-real + diffsupp + hνZ (hS₁.extension_mem_ZIrr で discharge 可)
  + hχχbar。tau1 = hS₁.extension (htau1Dmem は rfl 系)、imageFamily = dadeOrthonormalCharacterImageFamilyOfDiff。
- **`certainTypeR_imageSet_orthogonal_dadeOfDiff`** (S08_CaseBHortho:44) ⚠ **Sibley world 前提**
  (hyp : SibleyDadeHypothesis G L H、A = sharpImage H、hHK : h46.K = H) — §12 world (A = typePA0)
  では直接使えない。証明核 (ticVdiff key brick、⟨ω^σ, ·⟩ = 0 の disjointness) は W-world の話で
  A への依存は τ の家経由。**対応 = composite では hortho_mem を named hypothesis 化**し、§12 版
  supply (S08_CaseBHortho の typePA0 一般化 or §12 instantiation、a 所有ゆえ可) を別 piece に。
- **追加発見**: `muGrid_inner_irr_member_eq_zero` (S12_Section9Counts:802、既存) — hχ_S1 の
  supply がほぼ直接ある (μ-grid ⊥ irr member)。
⟹ composite の named hypotheses = **hDeg counting + hortho_mem** の 2 つ、他 15 項目は実 supply。

## 🔬 update⁶⁶ (2026-07-07 lane-a /loop) — ★ mixed corner 1-pair adjoin composite LANDED

### ✅ landed: `S13.adjoin_muColumnPair_of_irrFamily` (commit 0cc0a2e5, sorry-free, axiom-clean)
xAdjoinStepW_k の §12 instantiation (τ = hyp.tau defeq、A₀(M)、a = 1): coherent 既約等次数族
s (Finset 直接、anchor χ₁ ∈ s) + certain-type column pair {columnSum χ₂, columnSum χ₂⁻¹} →
IsCoherent hyp.tau (↑s ∪ {μ, μ̄}) A₀。実 supply 済 = χ-side Gram/support、member scaled-diff
support、member 直交、τ(μ−χ₁) ∈ ZIrr、hSgen。**named 残 (次 pieces)**:
1. **Dmem** — `memberExtensionDecomposition` の per-member instantiation (conj-closure ほか)
2. **Da** — `certainTypeDecompositionDa` (ψ = 1•χ₁; hμη₁supp/htau1_mema/hχψ 系の supply)
3. **hortho_mem** — R(irr) ⊥ R(μ) の §12 版 (S08_CaseBHortho の Sibley→typePA0 一般化)
4. **hμ_S1/hμbar_S1** — muGrid_inner_irr_member_eq_zero からの変換
5. **hDeg** (2 < |s|、§9 counting) / **hgen** (span 分解 ~30 行) / hdiffasuppχ / hμZ (μ ∈ ZIrr)

### Lean 教訓 (traps §5 続き、メモリ反映予定)
- set 変数 (μ/h46) は structure 型引数・Eq RHS の unify を阻む → **生式統一が根治**
  (supply have も呼び出しも同一の unfolded 式で)。
- 引数に取る decomposition (Da/Dmem) の型は **engine-native (dadeICM) 形で statement に書く**
  — hyp.tau 形だと projection 親項の τ 差で application mismatch。
次 iteration = named 残の supply pieces (上流順: 4 → 2 → 1 → 5-hgen; 3 は §12 化の独立 work、
5-hDeg は §9 counting)。

## 🔬 update⁶⁷ (2026-07-07 lane-a /loop) — ★ piece 4 (hμ_S1) LANDED

### ✅ landed (S12_Section9Counts, sorry-free ×2, commit 57300af6)
- **`exists_muColumnChar_eq`**: muColumnChar は非自明 W₂-dual への全射 (fCECG 逆像 + k≠0)。
- **`columnSum_inner_irr_member_eq_zero`**: ⟨columnSum χ₂, x⟩ = 0 (χ₂≠1、irr x ∈ S(X)) —
  composite の hμ_S1 直接 supply (hμbar_S1 は conj_eq + inv_ne_one 経由)。
- traps §5 追補: 証明内 instance/card 同定は **statement 引数の型表記 (toHypothesis46) に統一**
  しないと fCECG の Equiv unify が metavariable のまま全滅。tactic-def unfold の rfl は
  with_unfolding_all で。

### 残 pieces (adjoin composite の named 入力)
2. **Da** = certainTypeDecompositionDa instantiation (ψ=1•χ₁; hμη₁supp の suppIn(A∪V^L) 形 ↔
   typePA0 同定、htau1_mema、hχψ = piece 4 の系)
1. **Dmem** = memberExtensionDecomposition per-member (conj-closure/no-real/pairwise を
   irr-cut 特殊化で discharge)
5. **hgen** (span 分解 ~30 行) / **hDeg** (|s| ≥ 3、§9 counting)
3. **hortho_mem** (R⊥R の §12 化、S08_CaseBHortho 一般化 — 独立 work)
次 iteration = piece 2 (Da)。

## 🔬 update⁶⁸ (2026-07-07 lane-a /loop) — ★ piece 2 (Da) LANDED

### ✅ landed: `S12.Hypothesis.columnBreakDa` (commit 9d0421ba, sorry-free, axiom-clean)
certainTypeDecompositionDa の §12 instantiation (ψ = 1•χ₁)。**support seam は全 defeq で消滅**:
h46.tic.V = typePV M (toHypothesis46 の tic literal projection) ⟹ suppIn (A(M) ∪ tic.V^M) M =
suppIn typePA0 M = hyp.A0 — `exact` 素通り。anchor 直交は piece 4 で discharge。

### 残 pieces
1. **Dmem** = memberExtensionDecomposition per-member (次 iteration): conj-closure hconjS +
   no-real (inducedFamily_hasNoRealCharacters) + pairwise (⟨x,x̄⟩=0) + diffsupp
   (conjDiff_support) + hνZ (extension_mem_ZIrr) を irr-family 仮定から discharge する
   per-member supply lemma。
5. **hgen** (span 分解 ~30 行、equal-deg collapse の 3-generator 版) / **hDeg** (|s| ≥ 3 counting、§9)
3. **hortho_mem** (R⊥R §12 化、S08_CaseBHortho 一般化 — 独立 work、最重)

## 🔬 update⁶⁹ (2026-07-07 lane-a /loop) — ★ piece 1 (Dmem) LANDED + piece 5-hgen/piece 3 の既存 producer 発見

### ✅ landed: `S13.irrFamilyMemberDecomposition` (commit 0865d818, sorry-free, axiom-clean)
Dmem supply: conj-closed irr subfamily ⊆ inducedFamily の per-member ψ=0 decomposition
(memberExtensionDecomposition instantiation; tau1 = hS₁.extension literal → htau1Dmem = rfl)。

### ★ 在庫再発見 (S08_CaseBEnumeration:1020-1075 = xAdjoinStepW_k 系の完全使用 template)
- **`S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration`** (S07_Coherence:208):
  **hgen の generic producer が既存** — 入力 = hSgen (composite 内 supply 済) + 次数算術
  (hχ1: μ(1)=a·χ₁(1)、hbar1: μ̄(1)=μ(1)、hchi1_ne、h1A = one_notMem_A0)。
  ⟹ **piece 5-hgen は「composite の hgen 引数を hdeganchor (μ(1)=χ₁(1)) に置換して in-proof
  supply」の改良 1 手** (~15 行)。hbar1 は columnSum_conj 1-値 (columnSum_inv_apply_one 系)。
- **`caseB_member_orthoDatum_columnBreak`** (S08_CaseBEnumeration): Dmem+hortho_mem+htau1 の
  **bundled datum producer (Sibley world)** — piece 3 (hortho_mem §12 化) の完全 template。
  `columnDecompositionTau` (Da の hyp.tau 版) も同居。§12 版は sharpImage H → typePA0 の
  読み替え (certainTypeSet_isCoherent_A0/columnBreakDa と同じ defeq seam の見込み)。

### 残 (composite の named → 実 supply 化)
- hgen: 上記改良 (次 iteration、~15 行)
- hortho_mem: caseB_member_orthoDatum_columnBreak の §12 mirror (中規模)
- hDeg: |s| ≥ 3 counting (§9、genuine)
- 特殊化: s = irr-cut (sOf_degreeSubfamily_isCoherent) + hμ_S1 (piece 4) + Da (piece 2) +
  Dmem (piece 1) を束ねた caseB 1-pair adjoin の end-to-end instantiation

## 🔬 update⁷⁰ (2026-07-07 lane-a /loop) — ★ piece 5-hgen 内蔵化 LANDED (composite の構造 named は hDeg + hortho_mem のみに)

### ✅ landed: hgen 内蔵 (commit 0a550775, sorry-free)
adjoin_muColumnPair_of_irrFamily の hgen 引数 → hdeganchor (μ(1)=χ₁(1)) に置換、
`zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration` (S07:208) で in-proof supply。

### composite 入力の現況 (named 残の全リスト)
- **hDeg** (2 < |s|): §9 counting — genuine 残
- **Dmem/htau1Dmem**: `irrFamilyMemberDecomposition` (piece 1 landed) で supply 可 (htau1Dmem = rfl)
- **Da/hDatau1**: `columnBreakDa` (piece 2 landed) で supply 可 (hDatau1 = rfl 系)
- **hortho_mem**: §12 化未 (caseB_member_orthoDatum_columnBreak の mirror) — genuine 残
- **hμ_S1/hμbar_S1**: `columnSum_inner_irr_member_eq_zero` (piece 4 landed) で supply 可
- hdeganchor/hdiffasuppχ/hμZ: caseB uniform-qu 特殊化時に §9 facts から
次 = **end-to-end caseB 特殊化 skeleton** (s = irr-cut、pieces を束ね、named = hDeg + hortho_mem
の 2 つだけの assembly) or hortho_mem §12 化。

## 🔬 update⁷¹ (2026-07-08 lane-a /loop) — 節目 full build green + caseB 特殊化の設計 map (handoff)

### ✅ full build 検証 (commit 群 0865d818〜0a550775 の節目)
lake build OddOrder green、2m07s、sorry warnings 84 (regression なし; 直近の (9.11) 追加は全て
sorry-free)。

### caseB end-to-end 特殊化 `caseB_adjoinOneColumnPair` の設計 map (次 iteration で build)
target: s = irr-cut (`{φ ∈ sOf(H0Cprime) | irr ∧ deg d}`) + 1 column pair の adjoin を
`adjoin_muColumnPair_of_irrFamily` の特殊化として。
- **Finset 化**: irr-cut は finite (⊆ inducedFamily finite via sOf_subset_SOf + subset_bot +
  inducedKernelFamily_finite) → `hfin.toFinset`、coercion は `Set.Finite.coe_toFinset`。
- **hS₁**: `sOf_degreeSubfamily_isCoherent` (landed) — Finset coercion 越しに family 一致。
- **hsub**: irr-cut ⊆ sOf ⊆ SOf = IKF ⊆ IKF ⊥ = inducedFamily (landed 鎖)。
- **hconjS**: sOf_closedUnderConjugate + irr.conj + deg conj (star_natCast) — ~10 行。
- **hdegmem**: 全 member deg d (cut 定義) + anchor も deg d → x 1 = χ₁ 1。
- **hμ_S1/hμbar_S1**: `columnSum_inner_irr_member_eq_zero` (piece 4) — x ∈ cut → IKF member
  (sOf_subset_SOf + SOf_eq) + irr。params/hmu は S13.Hypothesis の params/params_mu_eq。
- **Dmem** = `irrFamilyMemberDecomposition` (piece 1)、htau1Dmem = rfl。
- **Da** = `columnBreakDa` (piece 2; anchor χ₁ ∈ IKF は同鎖)、hDatau1 = rfl。
- **残 named (真の外部入力)**: ①hDeg (2 < |irr-cut|、§9 counting)、②hortho_mem (§12 化未、
  caseB_member_orthoDatum_columnBreak mirror)、③hdegcol (columnSum χ₂ 1 = (d:ℂ)、caseB
  uniform-qu の §9 fact)、④hμZ (columnSum ∈ ZIrr — Σ irr で組立可、小)、⑤hdiffasuppχ
  ((μ−χ₁).support ⊆ A0 — μ ∈ inducedFamily [muGrid_column_sum_mem_inducedFamily + world-join、
  hdk1 = nontrivial column deg ≠ 1 前提] + scaledDiff、caseB では ③ から)。
④⑤は特殊化内で supply 可能見込み (⑤は μ ∈ IKF ⊥ 経由の scaledDiff_support、③から deg 一致)。
∴ 特殊化後の真の残 = ①hDeg counting + ②hortho_mem + ③hdegcol (全て §9/caseB facts)。

## 🔬 update⁷² (2026-07-08 lane-a /loop) — caseB 特殊化 supply ×3 landed + bundled-datum 設計確定

### ✅ landed (commit 7648bbe3, sorry-free ×3, axiom-clean)
- `columnSum_mem_ZIrr` (S12_Section9Counts) — composite hμZ 供給
- `irrCut_finite` / `irrCut_conjClosed` (S13) — Finset 化 + hconjS 供給

### ★ 設計確定: hortho_mem は bundled-datum 方式で
hortho_mem の型は内部構築 Dmem (証明項依存の imageFamily) に依存 → 直接 named 化不可。
**S08_CaseBEnumeration の `caseB_member_orthoDatum_columnBreak` パターン** (Sibley world) の
§12 mirror = 「per-member subtype datum: { D : CharacterPsiDecomposition τ x 0 //
(D.imageFamily ⊥ certainTypeR …) ∧ D.tau1 x = hS₁.extension x }」を作るのが正解。
その §12 版の中身は irrFamilyMemberDecomposition (piece 1) + **R(irr) ⊥ R(μ) の直交本体**
(certainTypeR_imageSet_orthogonal_dadeOfDiff の Sibley 前提 [sharpImage H] を typePA0 に
読み替え) — 直交本体の §12 化が真の残 work (V-vanishing 機構の A 依存度を精査)。
### 残 (caseB end-to-end)
① bundled-datum §12 版 (直交本体の §12 化込み、中規模) ② hDeg counting (§9) ③ hdegcol
(caseB uniform-qu) ④ 特殊化 assembly (①-③ 後は機械的)。

## 🔬 update⁷³ (2026-07-08 lane-a /loop) — hortho §12 化の理路確定 (V-vanishing anchor の §12 版)

### 依存点の切り分け (S08_CaseBHortho:44 の証明精読)
`certainTypeR_imageSet_orthogonal_dadeOfDiff` の Sibley 依存は **`tau_apply_eq_zero_of_mem_ticVdiffV`
1 点のみ** (S08_CaseBCoherence2:1046)。他は全て h46 + generic Dade で完結 (`key` =
inner_smul_chiFam_eq_zero_of_diff_vanishOnV、CharacterDifferenceImage 分解、ticVdiff 機構)。

### Sibley 版 vs §12 版の理路の違い
- Sibley 版: `dade_H_eq_bot` (local triviality) → 「image は conjugatesOfSet(H^#) 外で 0」+
  「V ∉ conjugates(K^G)」。**§12 では V^M ⊆ A₀ ゆえこの route は不成立** (v ∈ conjugates(A₀))。
- **§12 理路 (新)**: v ∈ V ⊆ A₀ ⊆ dadeSupport → `dadeMap_apply`/`dadeValue_eq` で
  τ(α)(v) = α(a) (a = v の Dade base point) → **a は A₀ = typePA ⊔ V^M の V^M-part に落ちる**
  (typePA ↔ typePV の G-共役分離、W₁-part order 論法) → α(a) = 0 (α は typePA-supported)。

### 必要な新補題 (§12 anchor の部品)
1. **typePA/typePV 共役分離**: x ∈ typePA = (M')^#、y ∈ conjClassSetIn M (typePV) → ¬IsConj x y
   (or: v ∈ V^M ∩ dadeSupport の base point は typePA に入らない)。§8 A₀ 設計
   (`dadeSupportHypothesisData_typePA0_of_isTypeP1`) に既存の可能性 — 先に grep。
2. dadeValue の base-point 特定 API (`mem_dadeSupport_iff` の witness + `dadeValue_eq`)。
3. §12 anchor: `tau_apply_eq_zero_of_mem_ticVdiffV_typeP` — α typePA-supported →
   τ(α) が (ticVdiff h46).V 上 0。**⚠ α の support 前提は typePA (A(M)) — composite の
   χ−χ̄ diff は columnDiff_support_subset で typePA-supported ✓ 整合**。
4. その上で `certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` (Sibley 版の証明 mirror、
   anchor 差し替えのみ) → bundled datum §12 版 → 特殊化 assembly。

### 代替 (先行可能): bundled datum を named のまま特殊化 assembly を先に組む
hortho §12 化と独立に、caseB 特殊化 (irr-cut Finset 化 + pieces 束ね) は Dmem/Da/hortho を
引数のまま組める — どちらを先にするかは次 iteration の自律判断 (上流優先なら anchor から)。

## 🔬 update⁷⁴ (2026-07-08 lane-a /loop) — ★ §12 V-vanishing anchor LANDED (hortho 化の核心突破)

### ✅ landed: `S13.tau_apply_eq_zero_of_mem_typePV` (commit 8467027c, sorry-free, 一発 green)
A(M)-supported α の §12 Dade image が ticVdiff.V 上 0。**Sibley と別理路で分離補題不要**:
- ticVdiff.V = typePV M は defeq (tic literal projection、`hvPV := hv` 直通)
- v ∈ V^M ⊆ A₀ = Dade base point → `dadeValue_eq` (witness 供給形: a=v、h=1∈H_a、conj=1) で
  α^τ(v) = α(v) → v ∉ M′ (`typePData_typePV_not_mem_derived`) + α は (M′)^#-supported → 0。

### 残 (hortho §12 化の続き、機械化された)
1. **`certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP`**: S08_CaseBHortho:44 の証明 mirror —
   唯一の Sibley 依存 (`tau_apply_eq_zero_of_mem_ticVdiffV`) を本 anchor に差し替え。
   `key` (inner_smul_chiFam_eq_zero_of_diff_vanishOnV)/CharacterDifferenceImage 分解/hmin
   (three_le_card) は全て h46-generic で流用可。χ−χ̄ の A(M)-supported は
   `inducedKernelFamily_conjDiff_support` の A(M) 版 (typePA ⊆ typePA0 の逆は不要 — S08 の
   `mderivSharp` 系が (M′)^# 直で出す — conjDiff の supp ⊆ (M′)^# ∪ … 要確認、hdiffsuppχ の
   supported 前提を A(M) 形で受ければよい)。
2. bundled datum §12 版 (irrFamilyMemberDecomposition + 1) → 3. 特殊化 assembly。

## 🔬 update⁷⁵ (2026-07-08 lane-a /loop) — ★★ hortho §12 化の本体 LANDED (R(μ_j) ⊥ R(χ))

### ✅ landed: `S13.certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` (commit 90176fb9, sorry-free, 一発 green)
S08_CaseBHortho:44 の完全 mirror — 唯一の Sibley 依存を §12 anchor (update⁷⁴) に差し替え、
disjointness machine / R(χ) 抽象化 / 4-case は h46-generic 流用。conj-diff は A(M) + A₀ の
2-supported 引数。

### (9.11) mixed corner の残り (全部品が見えた)
1. **bundled datum §12 版**: irrFamilyMemberDecomposition (piece 1) + 本 R⊥R を束ね、
   「{ D // (D.imageFamily ⊥ certainTypeR …) ∧ D.tau1 x = ext x }」per-member subtype を返す
   (S08_CaseBEnumeration の caseB_member_orthoDatum_columnBreak mirror)。Dmem の imageFamily =
   dadeOrthonormalCharacterImageFamilyOfDiff (memberExtensionDecomposition 経由) — その imageSet
   と本 R⊥R の β-side family の一致 (同じ dadeOfDiff、A₀ 形) の確認が接続点。向き注意:
   composite の hortho_mem は (Dmem).Orthogonal (Da) — Da.imageFamily = certainTypeR (columnBreakDa
   経由、transport 済) — 向きの swap は conj 対称 (Orthogonal の def と inner_conj_symm)。
2. **特殊化 assembly** (irr-cut Finset 化 + 全 pieces 束ね、named 残 = hDeg + hdegcol)。
3. hDeg counting (§9、genuine)。

## 🔬 update⁷⁶ (2026-07-08 lane-a /loop) — ★ bundled datum LANDED: composite の構造 supply 完備

### ✅ landed: `S13.irrFamilyMemberOrthoDatum` (commit 066929f0, sorry-free, 一発 green)
Dmem+hortho_mem+htau1Dmem の per-member subtype package。memberExtensionDecomposition 直接
構成 (R⊥R の証明項/family 完全一致)、conj-symm swap で向き解決、A₀/A(M) 両 support は
conjDiff_support の hKsupp 差し替えで。

### (9.11) mixed corner の総括 — 残る真の外部入力は §9 facts のみ
adjoin composite (`adjoin_muColumnPair_of_irrFamily`) の全入力の供給状況:
| 入力 | 供給 | |
|---|---|---|
| hS₁/hsub/hirr/hconjS | sOf_degreeSubfamily_isCoherent + irrCut_finite/conjClosed | ✅ |
| Dmem/htau1Dmem/hortho_mem | irrFamilyMemberOrthoDatum | ✅ |
| Da/hDatau1 | columnBreakDa | ✅ |
| hμ_S1/hμbar_S1 | columnSum_inner_irr_member_eq_zero (+conj) | ✅ |
| hμZ | columnSum_mem_ZIrr | ✅ |
| hgen | 内蔵 (anchorGeneration producer) | ✅ |
| hdegmem | cut 定義 | ✅ |
| **hDeg** (2 < \|irr-cut\|) | **§9 counting — genuine 残** | ⏳ |
| **hdegcol** (columnSum χ₂ 1 = d) | **caseB uniform-qu (§9 fact) — genuine 残** | ⏳ |
| **hdiffasuppχ** ((μ−χ₁).support ⊆ A₀) | μ ∈ inducedFamily + scaledDiff (hdegcol から) — 組立可 | ⏳ |
次 = 特殊化 assembly (`caseB_adjoinOneColumnPair`、上表の ✅ を束ね named = hDeg/hdegcol の
2 つ + hdiffasuppχ in-proof) → その後 chain 化 (§9 counting と合流)。

## 🔬 update⁷⁷ (2026-07-08 lane-a /loop) — ★★ caseB 1-pair adjoin END-TO-END LANDED

### ✅ landed: `S13.caseB_adjoinOneColumnPair` (commit 4d2647ec, sorry-free)
(9.11) mixed corner の 1-pair step が閉じた: deg-d irr-cut + column pair {μ, μ̄} → coherent
(A₀)。全構造入力は landed 鎖から discharge。**残る genuine 入力 = hDeg (2 < |cut|) +
hdegcol (μ deg = d) + hdiffasuppχ の §9/caseB facts のみ**。
- Lean 教訓 (traps §5 追補、メモリ反映済): Type-valued data は have で束縛すると opaque
  (with_unfolding_all も不達) — **let 必須**。

### (9.11) caseB 全体の残り
1. **chain 化**: 1-pair step を全 column pairs (k = 1..(w2−1)/2 の代表) に fold
   (coherentOfPairChainCover) → family 全体 = cut ∪ all-μ-pairs = sOf(H0Cprime) (caseB) の
   coherence。pair enumeration (inverse-pair 代表系) + step ごとの hDeg 単調性 (cut は step で
   増えない — S₁ は成長するが cut-card ベースの bound は同じ… ⚠ chain の各 step の S₁ は
   前 step の union — xAdjoinStepW_k の hDeg は「S₁ 内の等次数既約 s 部分」で測る — 各 step で
   同じ irr-cut を s に使えるか [S₁ ⊇ cut は維持、hmemS1 ✓ — irr-cut を s に固定し S₁ だけ
   成長させる形で composite は既に対応済 (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)] — **⚠ composite の
   現 signature は hS₁ : IsCoherent ↑s — s = S₁ 全体を要求! chain では S₁ ⊋ s になる —
   composite の hS₁/s を分離する軽微な一般化が要る** (S₁ : Set 引数 + s : Finset ⊆ S₁)。
2. **hDeg/hdegcol の §9 supply** (caseB counting/uniform-qu)。
3. caseA (non-Galois) は (9.11.1)-(9.11.8) norm-chain — 別フェーズ。

## 🔬 update⁷⁸ (2026-07-08 lane-a /loop) — s/S₁ 分離一般化 landed (chain 化 ready)

### ✅ landed (commit ebb22747, sorry-free ×3 維持)
adjoin composite / bundled datum / caseB caller を (S₁ : Set) + (s : Finset ⊆ S₁) に分離。
S₁ は step ごとに成長、s = irr-cut (anchor family) 固定 — chain fold の各 step で同じ s を
使い回せる形。hdegS₁diff (S₁ 全体の anchor-diff support) が新 named (caseB では全 member
deg d で scaledDiff から供給、初段 caller で実証済)。

### 次: chain fold (`caseB_coherent_sOf_H0Cprime_of_mixed`)
- pair enumeration: 非自明 column の inverse-pair 代表系 (Fin ((w2−1)/2) or
  {χ₂ // χ₂ ≠ 1} / inverse 同一視) — columnSum 全列の被覆と sOf(H0Cprime) = cut ∪ ⋃ pairs
  (caseB) の family 同定 (all-reducible corner の membership 合成の mixed 版)。
- fold: coherentOfPairChainCover (S07) — pairUnion 形に合わせる。
- 各 step の hdegS₁diff: S₁ = cut ∪ 既 pairs — μ 系の deg = d (hdegcol) で保存 ✓。
- 各 step の hμ_S1 (S₁ 全体): cut 部 = columnSum_inner_irr…、μ 部 = 列違い直交
  (columnFamily_mu_sum_inner off-diag) ✓ 部品あり。
- 残る genuine: hDeg (counting) / hdegcol (uniform-qu) / family 同定 (caseB の
  sOf = cut ⊔ μ-pairs 分割)。

## 🔬 update⁷⁹ (2026-07-08 lane-a /loop) — chain fold 部品: member dichotomy landed

### ✅ landed: `S13.caseB_sOf_member_dichotomy` (commit fa01da1c, sorry-free)
hcover の核: hunif (caseB uniform-deg、§9 fact named) の下で 𝒮(H₀C′) member は irr-cut ∨
∃ k ≠ 0, = columnSum (muColumnChar k)。irr 側 = cut 定義、red 側 =
reducible_mem_…_eq_muGrid_columnSum + world-join。

### chain fold の残り設計 (次 iteration)
- **pair enumeration**: pair : ℕ → CF × CF で pair j = (columnSum (muColumnChar kⱼ),
  columnSum (muColumnChar kⱼ)⁻¹-対応)。**inverse-pair 被覆の注意**: dichotomy は「ある k ≠ 0 の
  columnSum」を返すが pair は代表 k と逆 k⁻ の両方をカバーする必要 —
  (columnSum χ₂).conj = columnSum χ₂⁻¹ ゆえ pairSet j = {μⱼ, μ̄ⱼ} = {columnSum(χ₂ⱼ),
  columnSum(χ₂ⱼ⁻¹)}。代表系: Fin w2 の nonzero index を全部 pair に使い (代表系にせず
  重複 adjoin も chain 上は無害 — pairSet ⊆ X と hcover が満たせれば良い、既 coherent への
  再 adjoin は…xAdjoinStepW_k は χ ∉ S₁ を要求しない? hχ_S1 : ∀ x ∈ S₁, ⟨μ,x⟩ = 0 —
  μ ∈ S₁ (既 adjoin 済) だと ⟨μ,μ⟩ = w1 ≠ 0 で hμ_S1 が偽 → **重複 adjoin 不可、真の代表系
  (k と inv(k) から 1 つ) が必要**)。inv-index: muColumnChar k の逆 = muColumnChar (invk k)
  の対応 (fCECG と inv の compat) — enumeration 補題群 (~50 行)。
- **hstep**: caseB_adjoinOneColumnPair の chain 版 (S₁ = pairUnion S₀ pair i、per-step
  hdegS₁diff/hμ_S1 の帰納的維持 — S₁ の全 member deg d [hunif] + pairwise column 直交)。
- 残 genuine: hDeg / hdegcol / hunif (全て caseB §9 facts)。

## 🔬 update⁸⁰ (2026-07-08 lane-a /loop) — chain 部品 ×2 landed + 代表系不要の設計確定

### ✅ landed (commit bfc32a52, sorry-free ×2)
- `columnSum_inner_columnSum_eq_zero` (χ₂ ≠ χ₂' → μ ⊥ μ')
- `columnSum_muColumnChar_mem_inducedFamily` (k≠0 + hdne1 [d≠1、caseB = u>1] → μ ∈ S)

### ★ chain 設計の簡略化確定 (代表系不要)
全 nonzero index k = 1..w2−1 を pair 列挙し、hstep 内 by_cases:
- pairSet i ⊆ pairUnion i → identity step (union_eq_self cast)
- else → 実 adjoin: 両成分 ∉ (pairUnion は per-pair conj-閉) → χ₂_new ∉ {χ₂_old 系} →
  相異直交で hμ_S1 の μ-part、cut-part は piece 4。

### chain fold 本体の残入力 (次 iteration で assembly)
- hdegS₁diff の帰納維持: S₁ = cut ∪ pairs — cut 部 = scaledDiff (landed 路)、μ 部 =
  columnSum_muColumnChar_mem_inducedFamily + scaledDiff (hunif で deg d)。
- hμ_S1 の帰納維持: cut 部 (piece 4) + μ 部 (相異直交、本 update)。
- named 残 (§9/caseB facts): **hunif** (uniform-deg d) / **hDeg** (2 < |cut|) / **hdne1**
  (d ≠ 1) / **hdegcol 系** (columnSum deg = d — hunif+membership or 直接)。
- fold = coherentOfPairChainCover (pair j := (columnSum (muColumnChar (j+1 as Fin)), .conj)、
  N := w2 − 1、hcover = dichotomy [update⁷⁹] + pairSet 第 1/2 成分)。

## 🔬 update⁸¹ (2026-07-08 lane-a /loop) — chain 部品完備 (fold 本体のみ残)

### ✅ landed (commit 1ba4ddde ほか, sorry-free)
- `columnSum_injective` (S12_Section9Counts): columnSum の dual-単射 — set 相異 → dual 相異。
- `sOf_anchor_diff_support` (S13): X-統一 hdegS₁diff — hunif 下で全 member の anchor-diff が
  A₀-supported (S₁ ⊆ X ゆえ全 step 共通供給)。
- `mem_pairUnion` は S07:4998 に既存確認。

### fold 本体 `caseB_coherent_sOf_H0Cprime_of_mixed` の設計 (次 iteration、一点集中)
named (§9/caseB facts): hunif (∀ deg d) / hDeg (2 < |cut|) / hdne1 (d ≠ 1) / anchor
(hχ₁mem/irr/deg)。構成:
- pair j := (columnSum (muColumnChar kⱼ), conj) where kⱼ = Fin-cast (j+1)、N := w2 − 1
- hcover: dichotomy → k ≠ 0 → j := k−1 < N、φ = pair.1; conj は sOf closure で X ⊆
- hpairs: columnSum ∈ sOf? — **⚠ 要確認: μ = columnSum (muColumnChar k) ∈ sOf(H0Cprime) が
  hpairs (pairSet ⊆ X) に必要** — all-reducible corner では membership は逆向き (member →
  certainTypeSet) だった。caseB での「columnSum ∈ sOf(H0Cprime)」= μ-column が family に属す
  (Coq (9.5)/(9.8): μ_j ∈ S_H0C ⊆ S_H0C′) — **S12_Section9Counts の
  muGrid_column_sum_mem_sOf_H0_and_reducible (:256) が sOf(H0) 版!** sOf(H0) ⊆ sOf(H0Cprime)?
  向き注意: H0 ≤ H0Cprime → kernel 条件は antitone (sOf_antitone: 大きい Y ⊆ 小さい Y…
  sOf(H0Cprime) ⊇ sOf(H0C) [update⁴⁶ hyp.sOf_H0C_subset_sOf_H0Cprime] — H0 ≤ H0C′ →
  sOf(H0Cprime) ⊆ sOf(H0)! 逆向き!) — **μ ∈ sOf(H0Cprime) は sOf(H0) membership からは出ない**
  (H0Cprime-kernel はより強い条件)。μ の source の kernel が H0C′ ⊇ H0 を含むか = μ の source
  θ_k は H0C′ を kill するか — Coq: μ_j ∈ S_ H0C (H0C-kernel) ⊆ S_ H0C′ ✓ (H0C′ ≤ H0C、
  antitone で S_H0C ⊆ S_H0C′) — Lean: sOf(H0C) ⊆ sOf(H0Cprime) (sOf_H0C_subset_sOf_H0Cprime
  landed ✓) — ∴ **μ ∈ sOf(H0C) を確立** → ⊆ で H0Cprime へ。μ ∈ sOf(H0C):
  muGrid_column_sum_mem_sOf_H0_and_reducible は sOf(H0) — H0C 版が必要 (source kernel が
  C も kill: μ の source は HC-linear の induce ゆえ C ⊆ ker ✓ 数学的には真、Lean 補題要 —
  or named hμmem : ∀ k ≠ 0, columnSum (muColumnChar k) ∈ sOf(H0Cprime) として §9 fact 化)。
- hstep: by_cases skip / adjoin (supply = update⁸⁰-⁸¹ 部品)。
まず hμmem を named にして fold を先に閉じ、hμmem の実証明 (source kernel 計算) は後続。

## 🔬 update⁸² (2026-07-08 lane-a /loop) — ★ chain step LANDED (fold 本体は薄い帰納のみに)

### ✅ landed: `S13.caseB_chainStep` (commit 947e432e, sorry-free, 一発 green)
S₁ (cut ∪ 既 pairs) + fresh column pair の adjoin。dual 相異は set-freshness から直接
(heq ▸ hx、injective 不要)。named = hunif/hDeg/anchor + freshness (hnotin/hnotin') +
hS₁mu (accumulator の μ-part 特徴付け)。

### fold 本体の残り (最終 assembly、~80 行)
coherentOfPairChainCover instantiation:
- pair j := dite (j+1 < w2) ((columnSum (muColumnChar ⟨j+1,_⟩), conj)) (0,0)、N = w2−1
- hcover = dichotomy (update⁷⁹) → pairSet 第 1 成分 (j := k−1、Fin cast)
- hpairs = hμmem (named) + sOf_closedUnderConjugate
- h0 = sOf_degreeSubfamily_isCoherent (coe_toFinset ▸)
- hstep = by_cases skip (pairSet ⊆ pairUnion → union_eq cast) / caseB_chainStep
  (帰納維持: hS₁sub/hS₁cut/hS₁mu は mem_pairUnion 分解、freshness = ¬skip + pair conj-閉、
  pairUnion_succ_eq_union_pair で結論形合わせ)
named 集約: hunif/hDeg/hdne1(不要化済)/hμmem/anchor。

## 🔬 update⁸³ (2026-07-08 lane-a /loop) — ★★ (9.11) caseB chain fold LANDED: mixed corner が named §9 facts に帰着

### ✅ landed: `S13.caseB_coherent_sOf_H0Cprime_of_mixed` (commit 31224b47, sorry-free, axiom-clean)
coherentOfPairChainCover instantiation が閉じ、**caseB mixed corner の coherence
`coherent(𝒮(H₀C′), A₀)` が end-to-end で導出可能に** (named §9 facts を除く)。
- `caseBPair` (+ `_of_lt`/`PairSet_of_lt`): 全 nonzero column 列挙 (dite、代表系不要)。
- hcover = dichotomy (update⁷⁹)、j := k−1 の Fin cast は `Fin.ext` + `change` defeq 展開
  (omega は Fin.val ⟨…⟩ を還元しない — 教訓)。
- hstep = by_cases skip (`Set.union_eq_left`) / `caseB_chainStep`。freshness 両成分は
  accumulator conj-閉性 (cut conj-closed + pair conj-pair) から。**∃-witness は Prop-confined
  have に閉じ込め** (Type-valued goal への ∃-elim は不可 — 一度 build error で確認)。

### caseB (9.11) の残 = named §9/caseB facts のみ (全て Prop、fold は組立済)
| named | 内容 | supply 見込み |
|---|---|---|
| **hμmem** | ∀ k ≠ 0, columnSum (muColumnChar k) ∈ 𝒮(H₀C′) | ★次 iteration: μ ∈ sOf(H0C) (source = HC-linear induce、C ⊆ ker) → `sOf_H0C_subset_sOf_H0Cprime`。S12_Section9Counts `muGrid_column_sum_mem_sOf_H0_and_reducible` (:256) の H0C 版 |
| **hunif** | ∀ φ ∈ 𝒮(H₀C′), φ 1 = d | caseB uniform-qu: `forall_mem_sOf_H0C_apply_one_eq_qu` (S11:8211, caseB) の H0Cprime 版 |
| **hDeg** | 2 < \|irr-cut\| | §9 counting ((9.8) count ≥ (p−1)u/… 系) — genuine |
| anchor χ₁ | deg-d irr member | hDeg ⟹ cut nonempty から (or §9 (c) 直接) |

## 📢 HUB 裁定通知 (2026-07-08, issue 0101): (9.11) caseA は b へ — a は caseB 完結 + 9000 pivot

b が 9016 hY-producer 裁定の実施として `S11_NineElevenCoherence.lean` (b 所有 carve-out) で
(9.11) caseA maximality 帰納 ((9.11.1)-(9.11.8)) の port に着工した。**分担境界 (issues/0101)**:
caseA = b / caseB 一様 route = a (landed 済) / full assembly = a (S12/S13 から b leaf を import 可)。
⟹ **a は caseA を自前組立しない** (queue から除去)。1019 の残 = caseB named §9 facts
(hμmem/hunif/hDeg/anchor) + full assembly 配線のみ。完了次第 **ft_endgame_plan_2026_07_07.md の R1**
(9000 typeP_Galois instance tail pivot、W9 は c へ) に移行する。

## 🔬 update⁸⁴ (2026-07-08 lane-a /loop) — ★★★ caseB (9.11) 端点 assembly LANDED: 残 = hDeg 1 本

fold (update⁸³) の named 入力を同 session で 3/4 discharge し、caseB branch の端点まで組み上げ:

### ✅ landed (3 commits: 4046ec99, 2615824c, e51eb7cf)
1. **hμmem** = `S13.columnSum_muColumnChar_mem_sOf_H0Cprime` (S13_CoreStructure):
   (11.8.1) muGrid 数え上げ [sorry-free] → 𝒮(⊥) 緩和 → **`S11.TypesIIIIIIVSetup.eq_of_typeP_eq`
   (新規 sorry-free: typeP 同一 → setup 同一、他 field 全部 Prop)** で s11Setup world へ →
   H₀=⊥ (`chief_H0_eq_bot`) → (9.9.b) `reducible_mem_sOf_H0C` [sorry-free] → `C_eq_cSub` で
   𝒮(H₀C) → antitone。⚠ 配置は S13_CoreStructure (chief_H0_eq_bot/C_eq_cSub が
   S13_MaximalIII_IV の下流のため)。
2. **hunif** = `S13.caseB_forall_mem_sOf_H0Cprime_apply_one_eq_qu`: `caseB_degree_qu` (S11
   (9.9.a)、sorry-free) の instantiate。cprimeSub = derivedInG cSub = [C,C] 同定。d = q·u。
3. **assembly** = `S13.caseB_coherent_sOf_H0Cprime` (Nonempty 包み): ∃-irr で by_cases —
   ∃ → anchor 導出 (deg は hunif が pin) + fold / ¬∃ → all-reducible corner (landed) +
   μ₁ 証人。**anchor が named から消滅** ((9.9.c) 構造: irr 無し corner は C=⊥ 経路でなく
   all-reducible corner が直接処理)。

### 残 (caseB (9.11) を閉じるのに必要なもの)
- **hDeg 1 本のみ**: ∃-irr 時に `2 < |irrCut(𝒮(H₀C′), qu)|` (Coq PFsection9 (9.9)(c) の
  irr count)。純 §9 counting — 次 iteration の一点集中対象。
- transitive sorryAx は既知 §13 core gate (`chief_H0_eq_bot`/`C_eq_cSub` = (11.7)) のみ。
  §9/counting/fold 側は全て sorry-free。
- その先 (hub 0101 裁定に従い訂正): **caseA は b 所有** (`S11_NineElevenCoherence`) — a は
  自前組立しない。a の残 = hDeg → **(9.11) full assembly 配線** (clifford_dichotomy で
  caseA[b leaf を cite]/caseB[本 assembly] を束ね) → hY packaging → capstone → R1 pivot。

## 🔬 update⁸⁵ (2026-07-08 lane-a /loop) — ★★ ROUTE 訂正: hDeg は route 人工物 → norm-general (5.7) port へ (claim 9075)

### 発見 (Coq 権威、code-level)
- **Coq (9.11) の Galois(=caseB) 枝 = `uniform_degree_coherence scohS0` 一発**
  (PFsection9.v:1510-1513): 家族 𝒮(H₀C′) **全体** (可約 μ 込み、全 deg qu) に適用。
  count 不要・pair-chain 不要・anchor 不要。非Galois 枝のみ S1 (deg-qa cut) + (9.11.1-8)
  帰納 (= b の caseA 担当分)。
- **Coq `uniform_degree_coherence` は norm N 一般** (PFsection5.v:1256-1264: N=⟨χ₁,χ₁⟩、
  R-datum 2N)。**Lean 港 `coherent_of_constant_degree` は norm-1 限定** (`hirr : ⟨ζ,ζ⟩=1`)
  — μ (norm q) を受けられない。これが fold route (irr-cut anchor + μ-pair adjoin) と
  hDeg (2 < |irr-cut|) が生えた根因。
- **hDeg は §9 事実でない**: (9.9) `typeP_Galois_characters` に irr-count conjunct は無く、
  |irr-cut| = 2 の corner で偽の恐れ (weighted adjoin でも初段 2(qu)² < 2(qu)² で strict
  失敗、irr→μ-族 adjoin も 2q < p−1 必要で type III の q > p と矛盾 — 全 incremental 路が
  |cut|=2 で死ぬ)。**hDeg の §9 count 証明は中止** (偽 hoist リスク)。

### 正 route = norm-general (5.7) port (shared S07 infra、claim = issues/9075)
1. `pivotCoherence` (Coq pivot_coherence :588): **明示式** `ν φ := s(φ)•ζ₁ + τ(φ − s(φ)•η₁)`、
   s(φ) = 直交係数和 (pairwise 直交ゆえ freeness/basis 不要で構成可能と設計確認済)。
   extends は φ(1)=0 → s=0 で即。
2. (5.7) 一般版: ζ₁ = R(χ₁) 半分和の構成 ((5.4) subcoherent_split/norm minimality、
   Coq :1265-1330)。
3. caseB 適用: 全族 pairwise-orthogonal/conj-closed/no-real/hunif[landed] →
   `caseB_coherent_sOf_H0Cprime` rewire (hDeg 撤去)。fold (update⁸²) と部品は landed のまま
   残置 (caseA-style 局面の再利用資産; assembly からの消費は差し替え)。

### status
- 9075 claim 済。次 iteration = pivotCoherence の CODE (S07_Subcoherent 追記 or 新 leaf)。

## 🔬 update⁸⁶ (2026-07-08 lane-a /loop) — ★ pivotCoherence engine LANDED (9075 part 1, sorry-free)

`S07_PivotCoherence.lean` 新 leaf (commit b648b01c, 322 行, axiom-clean)。norm-general
uniform-degree coherence の核 = Coq `pivot_coherence` の等次数特化を**明示式**で port:
`ν φ := s(φ)•ζ₁ + τ(φ − s(φ)•η₁)`、s = 直交係数和 functional。基底 freeness 不要
(pairwise 直交で係数 = inner product)。IsCoherent 全 5 field 構成済。

- Lean 教訓: ① `zsmul_eq_mul` は ClassFunction (ring) の `c • x` に先に食い付く —
  scalar 側の書き換えは isolated `have` で。② `ClassFunction.smul_apply` は `c * φ g` 形
  (smul でなく mul) — `smul_eq_mul` 不要。③ span_induction の 4 case とも δφ-rearrangement
  (`hδadd`/`hδsmul`) を先に抽出すると全補題が `rw` 一列で閉じる。

### 次 (9075 part 2) — ζ₁ の供給
caseB 適用には pivot 条件 `⟨τ(η−η₁), ζ₁⟩ = −N` ∀η の ζ₁ が要る。route 候補:
(a) **(5.4) 一般 port** (Coq subcoherent_split :863 / subcoherent_norm :881 → haveX
    :1265-1330): S07.Hypothesis の R-datum から X = R(χ₁) 半分和を構成。汎用・本命。
(b) **caseB 特化**: η₁ := μ₁ (常在, p−1≥2)、R(μ₁) = S06.certainTypeR (landed) の
    X-側半分和 — §6 の既存 Dade 展開 (dadeICM_columnDiff_eq_sum 系) から直接計算できる
    可能性 (irr member への cross 内積は §12/§13 の columnBreak/orthoDatum 資産)。
まず (b) の在庫確認 (certainTypeR の X-半分と ⟨τ(χ−μ₁), X⟩ 計算素材) → 足りなければ (a)。

## 🔬 update⁸⁷ (2026-07-08 lane-a /loop) — ★ 9075 CLOSED (norm-general (5.7) engine + caseB rewire 全 landed)

9075 完遂: `uniform_degree_coherence_of_families` (S07_PivotCoherence) +
`caseB_coherent_sOf_H0Cprime` を **hDeg 無しの全族一発適用に置換** (S13)。新 6 部品
axiom-clean、full build green 3937 jobs。**11.8.6 coherence 依存 (9075) は解消**。

### 次 lane-a frontier 決定 (2026-07-08、上流優先+文書順+FT経路+cross-lane 除外)
- **(9.11) capstone `coherent_H0Cprime_S` / sibleyTarget_H0C (S11:8314) 置換 = lane b の (13.3) 仕事**
  (S11_NineElevenCoherence:42 「Consumers: lane b's (13.3)」)。私の caseB は landed 共有 infra として供給済。
- **S10:384/507/3329 = BG §16 consequence の cross-lane cite** (「BG Section 16 consequence, not a local
  Peterfalvi argument」) — lane-a head-on 対象外。
- **S07_Subcoherent = 実 sorry ゼロ** (全 docstring)。
- ⟹ **genuine lane-a frontier = §11.8 orthogonality 計算** (S13_CoreStructure):
  - `orthogonality_setup` (:1359、11.8.1–11.8.4) = `OrthogonalityData` の構成。現状 scaffold:
    frobenius_setup / omega_support_reduction / average_formula / coefficient_formula が
    **opaque Prop field**、coefficient_zero が proof field に hard content を hoist ([[scaffold-sorry-free-not-done]])。
    honest 化 = Prop field de-opacify + Frobenius reciprocity 係数計算で **coefficientA a = 0** 実証明。
  - `not_orthogonal_mu0_sub_zeta` (:1378、11.8 結論) = orthogonality_setup を消費。
  → 次 iteration: mmd/Coq (PFsection11 の 11.8.1–11.8.5) 精読 → OrthogonalityData de-opacify + 係数計算 port。

## 進捗 (lane-a /loop, 2026-07-08) — SCOPING: forward (6.3) port gap 確定

(10.8) 側は完了 (h78 = (7.8.b) 実証明済、estimate `hA` proven、commit a559bd0a)。∴ (11.8.6) redesign が
lane-a 次 frontier。redesign の upstream ブロック = **forward `bounded_seqIndD_coherence` (Pf (6.3)) の port**。

### repo 状態 (grep 確定)
- **在る (analytic/contrapositive 側)**: `S08_Theorem63.lean` (`sSubFiltration_sum_le_two_psi_caseB` 等 =
  coherence-break degree bound `∑ ≤ 2ψ`)、`S08_SixTwoGeneral.lean` の `inducedKernelFamily` 一式 +
  `inducedKernelFamily_degreeSqNormReBound_of_break_k` (:468、= `coherent_seqIndD_bound` の解析核 `∑χ(1)²/‖·‖²`)。
- **無い (forward 側、port 要)**:
  1. **`extend_coherent` (Pf (6.2) forward)** = coherent 族を break pair で拡張する primitive。repo に decl 無
     (S08_Theorem63:102 は comment 言及のみ)。⚠ これが core。`IsCoherent.extension` (S07、coherent 拡張 MAP) とは別物
     (こちらは coherent SET を新 pair で拡張する定理)。
  2. **forward `bounded_seqIndD_coherence` (Pf (6.3))** = `[M,H,H1 <| L] + M⊆H1⊆H⊆K + nilpotent(H/M) +
     coherent(S H1) + |H:H1|>4|L:K|²+1 → coherent(S M)`。Coq PFsection6.v:114-167 = maxnormal 帰納
     (A=H1 を M へ縮小、各 step で A/B ⊆ Z(H/B) via nilpotency + 解析 bound `(x−x⁻¹)²≤(2|L:K|)²`)。
     deps: `extend_coherent`(上)、`coherent_seqIndD_bound`(:158、= 解析核 wrapper)、`sum_seqIndD_square`、
     `irr1_bound_quo`。

### 次 iteration の建設順 (upstream-first)
1. `extend_coherent` (Pf 6.2 forward) を port (S07/S08 coherence 機構の上に)。← 最大 piece、要 deep scope
   (Coq PFsection5/6 の `extend_coherent` 定義精読)。
2. `coherent_seqIndD_bound` wrapper を `inducedKernelFamily_degreeSqNormReBound_of_break_k` から組む。
3. forward `bounded_seqIndD_coherence` = maxnormal 帰納で assemble。
4. 然る後 capstone redesign (やること §2-3): `coherent_Sset_diff_SHCSet` を S_H0C に narrow + capstone を
   bounded-coherence route に。⟹ (11.8.6) sorry-free、(10.8) `S_not_coherent` へ接続。

⚠ shared-infra 判定: `extend_coherent`/`bounded_seqIndD_coherence` は §6 coherence 汎用 → 他レーン consumer
可能性あり。着手前に open 9000 scan (現状 9000/9014/9076 は σ-theory/prime-TI で別物、重複無し) + 必要なら 9000 claim。

## ⚠ 訂正 (lane-a /loop, 2026-07-08) — forward (6.3) は既に PORTED。真の gap は G2 (S12 capstone re-route)

**前 iteration の「forward (6.3) 未 port」= 誤り** ([[verify-port-state-by-number-not-coq-name]] の実例)。
`S08_Theorem62_63_Standalone.lean` を grep 対象から漏らしていた。実状 (Explore map + 検証):

- **forward `bounded_seqIndD_coherence` = `six_three_of_six_two_oracle`** (`S08_Theorem62_63_Standalone.lean:382`、
  sorry-free、`AxiomsCheck:2296` axiom-clean)。maxnormal 帰納 + nilpotency 中心化 + 解析 `(x−x⁻¹)²` bound +
  θ-degree √-geom + `sum_seqIndD_square` は**全て landed**。`extend_coherent` 相当は `xAdjoinStepW`
  (`S08_CoherenceWeighted:287`、reducible-tolerant) で、`exists_source_index_le_two_psi_of_break`
  (`S08_SixTwoGeneral:986`) に組み上げ済み。**Xset adjoin-steps 版は irr 限定で別物、port 不要。**
- **§13 consumer 済**: `coherent_S_of_coherent_SH0C` (`S13_MaximalIII_IV:1415`、**sorry-free**) =
  `coherent(S_H0C) → coherent(inducedFamily M)`、(K,H,M,H₁)=(M',HC,⊥,H₀C) で oracle を instantiate。
  `S_H0C_not_coherent` (`S13:1523`) → (10.8) 矛盾も配線済 (S13 全体 sorry-free)。
- **h56 grid datum** (`sixTwoDecompositionData`, issue 2022, owner=lane b) は §13 use では既に discharge 済
  (S13 sorry-free)。新 9000 claim 不要 (2022 で被覆)。

### 真の残 = G2 (lane-a-local): S12 capstone の false-sorry route を (6.3) route に置換
- `Hypothesis.coherent_Sset_of_column_identities` (`S12:4857`) は **deprecated uniform-degree route**、
  false sorry `Sset_diff_SHCSet_apply_one_eq_qu` (`S12:4480`, irr-side sorry `:4492`、非Galois III/IV で偽) を carry。
- **live 確証**: `coherent_Sset_of_column_identities` → `exists_zeta_residual_not_orthogonal` (`S12:5011`) →
  `w2_lt_w1_of_hypothesis` (`S12:5018`) → `card_kappaHall_lt_of_isTypeIIIorIV` (`FeitThompson:615`) → feitThompson。
  `#print axioms w2_lt_w1_of_hypothesis` = `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx 混入確認)。
  ∴ この false sorry は feitThompson spine 上に live。
- **entanglement**: S12 は S13 の `coherent_S_of_coherent_SH0C` を cite 不可 (S13 は S12 の下流)。
  ∴ S12 capstone は **S08 `six_three_of_six_two_oracle` を直 cite** (map 曰く import 制約はこれで解消) して
  自前で (K,H,M,H₁)=(M',HC,⊥,H₀C) + h56 + `coherent(S_H0C)` を組む必要。
- **次 iteration の要調査点**: (a) column-identity 入力 (11.8.5) から `coherent(S_H0C = SOf H0C)` が S12 レベルで
  導けるか (H0C/HC/SOf は S13-Hypothesis field、S12-Hypothesis に無い可能性)。(b) 無ければ
  `exists_zeta_residual_not_orthogonal`/`w2_lt_w1` の **S13 relocation** (issue の endgame relocation 案)。
  (c) いずれにせよ false uniform-degree sorry (`:4492`) を除去し、honest な (6.3) route に。

## ⚠⚠ 再訂正 (lane-a /loop, 2026-07-08) — ground-truth axiom-trace で verify (前訂正の sorry-free 判定は誤り)

**前訂正 (update「forward (6.3) 既 PORTED」) の「`coherent_S_of_coherent_SH0C` sorry-free」= 誤り。**
docstring の "sorry-free" を信用したのが原因 ([[verify-port-state-by-number-not-coq-name]] — docstring でなく
`#print axioms` が ground-truth)。直接 verify:
- **`coherent_S_of_coherent_SH0C` (S13:1415)** = `[propext, sorryAx, Classical.choice, Quot.sound]` (**sorryAx あり**)。
  ∴ (6.3) の §13 consumer は **not sorry-free** (oracle `six_three_of_six_two_oracle` 自体は clean だが consumer は gated)。
- **`H0C_relIndex_HC` (S13:853) は sorry-free** (完全証明 :853-883、`Nat.eq_of_mul_eq_mul_left`)。
  ⟹ G2 subagent の「sorryAx は H0C_relIndex_HC 経由」は**誤り** (attribution ミス、subagent 診断は部分的に不正確)。
- **`S_not_coherent` (10.8, S12) も sorryAx** (自身の hB TI-counting gate、10.7 cite 経由)。

### G2 (11.8.6 capstone re-route) は S12-local 不可能 — cross-lane 多部品 gate 確定 (verify 済結論)
honest な (6.3) route は `coherent(S_H0C)` を要すが、それは union-glue `S(HC) [uniform-deg] ∪ 𝒮(H0C) [(9.11)
core-coherence, non-uniform]` で作る。crux = **coherent(𝒮(H0C)) が repo のどこでも sorry-free 未証明**:
- `coherent_SOf_H0C_of_glued` (S13:2181) = glue capstone、axiom-clean **だが caller 無** (gate 未供給)。
- `caseB_coherent_sOf_H0Cprime` (S13_CoreStructure:1469) = **sorryAx**。
- `caseA_coherent_sOf_H0Cprime_of_refuter` (S11_NineElevenCaseA:65) = refuter 条件付き未供給 (caseA=lane b, 0101)。
- τ₃ glue `hmixed`(6.7)/`hDτ`(5.8) = §14/BG§15-gated; shortcut `sibleyTarget_H0C` は UNSOUND (issue 7001)。
- import: S13 は S12 を import ⟹ S12 は S13 の honest 機構を cite 不可 (循環)。H0C/HC/SOf は S13-field。

**⟹ honest fix = issue 1019 の multi-part cross-lane 継続作業** (relocate exists_zeta_residual/w2_lt_w1 を S13 へ +
coherent(𝒮(H0C)) via (9.11) [caseA=b/caseB sorryAx 掃除] + τ₃ glue §14/BG§15)。**lane-a-local な quick fix は無い。**
false `:4492` sorry は既存 ⚠ 付きで**現状維持が正しい** (今 replace すると true-but-unproven な hY/glue/(10.8) sorry へ
shuffle するだけ = 禁止)。∴ lane-a の §10-§11.8 cluster ungated work は hA/h78 完了で**枯渇**、残りは cross-lane gate。

## 2026-07-08 update⁹ (lane-a /loop) — ★ honest route FULLY MAPPED + caseB `hY` LANDED (`caseB_coherent_sOf_H0C`)

独立再検証 (textbook Pf (11.8.6) 原文 `04.13` L61-71 精読 + code trace) で honest 経路の**完全 piece graph**
を確定。last iteration の「cross-lane multi-part gated」診断は**構造的に正しい**が、以下 2 点を訂正/前進:

### ① honest (11.8.6) 完全 piece graph (全 signature 確認済、S13 に全在)
`exists_zeta_residual_not_orthogonal` を S13 に relocate し、**narrow-`𝒮₂` route** で組む
(現 S12 `coherent_Sset_of_column_identities` の wide `Sset\SHCSet` uniform-degree = **偽**を排除):
- `coh` = `coherent_SOf_HC` (S13:1847, landed)
- `hY` = **`caseB_coherent_sOf_H0C`** (本 update で LANDED) = caseB `𝒮(H₀C)` coherence
  = `caseB_coherent_sOf_H0Cprime` (9075) →[`coherent_sOf_H0C_of_coherent_sOf_H0Cprime` (11.7 C′→C)]→ `𝒮(H₀C)`。
  **caseA 版** = `caseA_coherent_sOf_H0Cprime_of_refuter` (S11_NineElevenCaseA:65) + 同 transfer = **lane-b refuter gated** (sorried-cite)。
- union-glue `coherent_SOf_H0C_of_glued` (S13:2181, axiom-clean skeleton): ν/hgen/hmixed/hDτ。
  **hgen** = narrow uniform-degree (caseB TRUE, `forall_mem_sOf_H0C_apply_one_eq_qu`) で genuine 化可。
  **hmixed/hDτ** = §14 Sibley (6.7)/(5.8) = lane-c gated (sorried-cite)。
- (6.3) lift `coherent_S_of_coherent_SH0C` (S13:1415) or 直接 `S_H0C_not_coherent` (S13:1523) と矛盾 = (10.8) gated。
⟹ honest fix は caseA(lane-b refuter) + hmixed/hDτ(§14 lane-c) + (10.8) の 3 cross-lane sorried-cite で組める
(false lemma を除去、hgen は genuine)。**前倒し gated-endpoint skeleton として build 可能** ([[feedback-gated-endpoint-skeleton-pattern]])。

### ② ★ LANDED (本 update、full build green 3941 jobs): `caseB_coherent_sOf_H0C` (S13_CoreStructure)
- **`columnSum_muColumnChar_mem_sOf_H0C`**: `columnSum_muColumnChar_mem_sOf_H0Cprime` を `𝒮(H₀C)` 中間で
  factor (H0Cprime 版 = subset で導出、下流不変)。
- **`caseB_coherent_sOf_H0C`**: 9075 の caseB `𝒮(H₀C′)` coherence を **(11.7) transfer で `𝒮(H₀C)` に前進**
  (witness = reducible μ-column の conj-diff, `A₀`-supported + nonzero)。= honest (11.8.6) の **caseB `hY` 入力**。
  → **これまで consumer 0 だった 9075 を load-bearing 化**。

### ③ ★ ground-truth 訂正 (`#print axioms`): 9075 は axiom-clean で**ない**
`caseB_coherent_sOf_H0Cprime` (9075) = `[propext, sorryAx, Classical.choice, Quot.sound]` — **sorryAx あり**。
notes/update⁸⁷ の「9075 axiom-clean」= 誤り (docstring 過信、[[verify-port-state-by-number-not-coq-name]])。
sorryAx 源 = §9 count chain (`muGrid_column_sum_mem_sOf_H0_and_reducible` → `reducible_count_sOf_H0`/`muGrid`、
S12_Section9Counts は直接 sorry-free ゆえ**推移的**、TRUE な §9 count) 経由 (`caseB_coherent_sOf_H0Cprime` の
μ-column pivot が引き込む)。→ caseB 分岐の真の残 gate = この §9 count chain の sorry leaf (次 iteration で pinpoint)。

### 次 iteration (上流優先)
1. §9 count chain の sorry leaf を pinpoint (`reducible_count_sOf_H0`/`muGrid`/Dade 系のどれか) → lane-a ownable か判定。
2. honest (11.8.6) caller を build: `coherent_SOf_H0C_of_glued` を `caseB_coherent_sOf_H0C` (caseB hY) で instantiate
   + ν 構成 + hgen (narrow uniform-deg) + hmixed/hDτ/caseA/(10.8) sorried-cite → false `Sset_diff_SHCSet_apply_one_eq_qu` 除去。

### ④ ★ caseB chain の sorry-leaf trace (本 update、`#print axioms` scratch で確定)
`caseB_coherent_sOf_H0C`/`caseB_coherent_sOf_H0Cprime`(9075) の sorryAx は **§9 count でなく (11.5)-(11.7)
structural chain** 経由と判明 (μ-column pivot が `columnSum_..._mem_sOf_H0C` → `chief_H0_eq_bot` を引く):
- **CLEAN (axiom-clean 確認済)**: `reducible_count_sOf_H0`, `muGrid`, `muGrid_column_sum_mem_sOf_H0_and_reducible`,
  `reducible_mem_sOf_H0C`, `sOf_H0C_subset_sOf_H0Cprime`, **`caseA_commutator_chain`** (11.7 case-a 非Galois
  D-antisymmetry, docstring の "remaining sorry" は stale — 実は clean), `chiefKernel_caseB_false` (case-b parity),
  `caseA_fixes_of_action_chain`, `caseA_fixed_contradiction`, `chiefFactor_clifford_U_dichotomy`,
  `secondDerived_coherent` (5.7) — **(11.7) の genuine 群論は完成**。
- **SORRYAX**: `chief_H0_eq_bot`/`chief_N_eq_bot`/`C_eq_cSub` (11.7) ← `H0_eq_Hprime`(11.6)/`H_isPGroup` ←
  **`HC_le_secondDerived`(11.5)** ← **`coherent_quotient_bound`(11.4)** ← (6.2)/(10.8)。`S_not_coherent`(10.8) = SORRYAX。
⟹ caseB (9.11) chain は **(11.4)/(11.5) char-gate 経由で (6.2)/(10.8) 底**。**shallow な ungated lane-a 勝ち筋は無い**
(case-helper は既に clean、gate は §6/§10 coherence)。

### 次 iteration の要検証 (ungated 勝ち筋の唯一候補)
**`coherent_quotient_bound` (11.4) の gate が (6.2) か (10.8) か**を pinpoint。Peterfalvi (11.5) 原文 (mmd `04.13`
L23-31) は **(11.4)+(5.7) で M''=HC を導き (10.8) を使わない** (repo docstring の「(11.3)/(11.4) 経由 (10.8)」は
repo 実装の routing、Pf 原証明でない可能性)。(11.4) が (6.2)-only gate (= §6 coherence quotient bound、
port 可能性) なら **(11.5)→(11.6)→(11.7)→caseB chain を (10.8) 非依存で un-gate** できる → caseB (9.11) を
honest 化する唯一の ungated 経路。(11.4) が (10.8) 底なら caseB chain は deep char-gate 確定 (再攻略せず sorried-cite)。

### ④′ 訂正 (同 iteration、(11.4) 直読で確定): caseB chain は **(10.8)-deep-gated、ungated 勝ち筋なし**
`coherent_quotient_bound` (11.4, S13_MaximalIII_IV:1534) の proof は `hBncoh` (:1562-1569) で
**`S_H0C_not_coherent` (11.3→10.8) を直接使用** — Pf (11.4)=(6.2) dichotomy が "S(H₀C) not coherent"
を break 入力に要するため (原文どおり)。∴ (11.5) を (10.8) 非依存で再導出する路は**無い** (Pf の (11.4)
自体が非coherence を使う)。⟹ **caseB (9.11) chain (my `caseB_coherent_sOf_H0C` 含む) は (10.8) deep-gate 確定**
(§9 columnSum が (11.7) H₀=1 = chief_H0_eq_bot で type III/IV 特化 → (11.5)→(11.4)→(10.8))。
repo artifact 注記: repo の caseB (9.11) 証明は (11.7) H₀=1 で特化 (§9 を §11 結果で証明する logical inversion)
ゆえ (10.8) を引く。H₀ 一般のまま (9.11) を証明すれば (10.8) 非依存化しうるが = §9 一般機構の re-architecture
(lane-b (9.11) territory、shallow でない)。⟹ **lane-a char cluster は (10.8)+§14+lane-b caseA で comprehensively
gated が再確認**。my `caseB_coherent_sOf_H0C` は principle-1 な gated-endpoint building block として landed 済
(9075 を honest (11.8.6) hY に前進、新 sorry 無し)。

## 2026-07-08 update¹⁰ (lane-a /loop) — ★ unconditional `𝒮(H₀C)` coherence LANDED (honest (11.8.6) `hY`)

新 leaf **`OddOrder/Peterfalvi/S13_Orthogonality.lean`** を作成 (caseA=`S11_NineElevenCaseA` と
caseB=`S13_CoreStructure` は sibling leaf ゆえ dispatch は両者 downstream の共通 file が必要; これが
honest (11.8.6) endpoint の自然な home、将来 FeitThompson が import)。

**`coherent_sOf_H0C`** (`Nonempty (IsCoherent τ (sOf hyp.s11Setup hyp.H0C) A0)`): (9.11) の
`clifford_dichotomy` で dispatch —
- **caseB** = 私の `caseB_coherent_sOf_H0C` (9075→11.7 transfer、landed、新 sorry 無し)、
- **caseA** = `caseA_coherent_sOf_H0Cprime_of_refuter` + 同 transfer + μ-column witness、
  **refuter のみ sorried** (= (9.11.2) pair-adjoining non-coherence、lane-b の `S11_NineElevenCoherence`
  active work、principle-1 sorried-cite)。

これで honest (11.8.6) の **unconditional `hY` (𝒮(H₀C)-coherence) 入力が揃った**
(`#print axioms` = 1 sorryAx = caseA refuter + caseB chain の (10.8) gate)。full build に組込済
(OddOrder.lean import 追加)。

### 次 iteration (honest (11.8.6) caller、同 file S13_Orthogonality)
`coherent_SOf_H0C_of_glued` を `coherent_sOf_H0C` (hY) で instantiate:
- coh = `coherent_SOf_HC` (landed)、ν = glue map 構成、hgen = narrow uniform-degree (caseB TRUE)、
  hmixed/hDτ = §14 Sibley sorried-cite。
→ `𝒮(H₀C)` coherent (union-glue) → **`S_H0C_not_coherent` (11.3/10.8) と矛盾で honest (11.8)**。
→ `exists_zeta_residual_not_orthogonal`/`w2_lt_w1` を本 file に relocate + FeitThompson rewire →
  **false `Sset_diff_SHCSet_apply_one_eq_qu` を spine から除去**。

## 2026-07-08 update¹¹ (lane-a /loop) — ★★ honest narrow (11.8) route LANDED + WIRED INTO SPINE (false lemma OFF-SPINE)

honest (11.8.6) narrow-`𝒮(H₀C)` caller を `S13_Orthogonality.lean` に完成し、**feitThompson spine を
それに rewire**。full build green 3943 jobs、AxiomsCheck OK。

### landed (S13_Orthogonality、S12 wide template を narrow に mirror)
- **`exists_glue_nu_H0C`** (sorry-free): SOf(HC)/sOf(H0C) glue-map constructor
  (`exists_integralCharacterMap_glue_of_orthogonal` + inducedKernelFamily 直交/norm + `SOf_HC_inner_sOf_H0C_eq_zero`)。
- **`coherent_SOf_H0C_of_column_identities`** (3 sorry のみ): narrow capstone。`coherent_sOf_H0C` (hY) を消費、
  `coherent_SOf_H0C_of_glued` を feed。3 sorry = **hmixed** (6.7、§14、S12:4888 と同型) / **hDτ** (5.8、§14、
  S12:4896 と同型) / **hgen** (6.8.1 生成、**§9 narrow uniform-degree で TRUE** ← S12 の FALSE
  `Sset_diff_SHCSet_apply_one_eq_qu` を置換)。
- **`exists_zeta_residual_not_orthogonal_H0C`** (sorry-free、S12 版と同一 statement): `intro h_orth` →
  S12 residual machinery で ν/hcol 構成 → narrow capstone → **`S_H0C_not_coherent` (11.3) と矛盾**。
  soundness = h_orth-gated (S12 と同型、unconditional False 無し、`#print axioms` = sorryAx のみ・新 axiom 無)。
- **`w2_lt_w1_of_hypothesis_H0C`**: narrow caller + `w2_lt_w1_of_residual_not_orthogonal` → w₂<w₁。

### spine rewire (FeitThompson)
`card_kappaHall_lt_of_isTypeIIIorIV` (:649) を `S12.w2_lt_w1_of_hypothesis` → **`S13.w2_lt_w1_of_hypothesis_H0C`**
に変更 (+ S13_Orthogonality import)。⟹ **feitThompson は FALSE `Sset_diff_SHCSet_apply_one_eq_qu` を
経由しなくなった**。spine 残 sorry は全て TRUE: hmixed/hDτ (§14 Sibley、lane-c)、hgen (§9 narrow、TRUE、
genuine 化 deferred)、caseA refuter (lane-b (9.11.2))、(10.8) `S_not_coherent`。
[[scaffold-sorry-free-not-done]]: FALSE-lemma-route → all-TRUE-sorry-route = genuine soundness 前進。

### 残 (deletable follow-up、churn 回避で defer)
wide chain (`Sset_diff_SHCSet_apply_one_eq_qu`/`coherent_Sset_of_column_identities`/`hgen_of_S2_uniform_degree`/
S12 `exists_zeta_residual_not_orthogonal`/`w2_lt_w1_of_hypothesis`) は今 **off-spine で unused** (docstring 参照のみ、
AxiomsCheck #assert 無)。削除で landmine 完全除去可 (共有 helper 有無を要確認ゆえ fresh context 推奨)。

## 2026-07-08 update¹² (lane-a /loop) — ⚠ 自己訂正: narrow hgen の caseA 健全性は UNCERTAIN (over-claim 修正)

update¹¹ の「spine 残 sorry は全て TRUE」は **over-confident**。narrow capstone
`coherent_SOf_H0C_of_column_identities` の **hgen** (D = {qu-column diagonal `∑μ_ij − dζ`}) は
**caseB では TRUE** (uniform degree qu、`forall_mem_sOf_H0C_apply_one_eq_qu`) だが、**caseA では健全性 UNCERTAIN**:
- **Clifford caseA で `sOf(H0C)` は非uniform** — `caseA_exists_irreducible_sOf_H0C` (S11:13170) /
  `caseA_exists_irreducible_source_degree_qa` (S11:6455) が degree-`qa` (a>1, ≠qu) 既約を与える。
- (6.8.1) 生成の decompose `φ = (φ_X + k·d·ζ) + (φ_Y − k·ψ₀) + k·(ψ₀−dζ)` は `k = −s_X/d ∈ ℤ` を要す。
  caseB は uniform relation `s_X = −s_Y·d` で `d|s_X` 自動成立。caseA は `s_X = −(d·n_qu + a·n_qa)` ゆえ
  `d|s_X ⟺ d|a·n_qa` で一般に不成立 → 単一 qu-diagonal D では **caseA の qa-mixed supported 元を生成できない疑い**
  (反例候補 `a·ζ − χ_qa` が A₀-supported なら hgen は caseA で FALSE)。⚠ A₀-support 制約が救う可能性は未確認。

### ⟹ milestone の honest 再評価
- **成立**: spine を Peterfalvi の**正しい族** 𝒮₂ = 𝒮(C) (= sOf H0C) + clean architecture に移行し、
  **wrong-family な wide false lemma `Sset_diff_SHCSet_apply_one_eq_qu` を repo から除去**。これは genuine な構造改善。
- **未成立 (over-claim)**: 「all-TRUE sorries」ではない。**hgen sorry は caseA で不十分/FALSE の疑い**があり、
  fix = **D を qa-diagonal で enrich** (qa-column witness + その (5.8) hDτ 恒等式) — Peterfalvi (11.8.6) caseA の
  qa-column identity を要す (intricate、caseB uniform より深い)。wide の fundamental falseness より修正可能だが未完。

### 次 iteration (fresh context 推奨)
1. **caseA hgen 健全性を確定**: `a·ζ − χ_qa` 型の A₀-supported 反例が存在するか (存在 ⟹ 現 D で hgen FALSE-caseA)。
2. FALSE なら D を qa-diagonal enrich (capstone を caseA/caseB split、caseA は qa-column witness
   `caseA_exists_irreducible_sOf_H0C` + qa-column (5.8) identity)。caseB hgen は uniform-degree で genuine 化。
3. Coq PFsection11 (11.8.6) の caseA generation 精読 (単一 diagonal か mixed か)。

## 2026-07-08 update¹³ (lane-a /loop, subagent 精査) — ★ VERDICT: narrow hgen は caseA で FALSE (wrong engine)、fix = bridge_coherent

update¹² の caseA 懸念を Coq PFsection11/9 精読 + Lean 不変量で**確定** (high confidence):

### narrow hgen は **caseA で FALSE** (単一 qu-diagonal では不十分) — 但し soundness 違反ではない
- **caseA で `sOf(H0C)` は mixed-degree {qu, qa}**: Coq `Ptype_core_coherence` (`PFsection9.v:1484`) 非Galois
  branch (`:1537`) が **degree-`qa` subfamily を明示 filter** (`a_gt1`/`a_dv_u` で `1<a<u`)。Lean `caseB_degree_qu`
  (S11:8106) / `forall_mem_sOf_H0C_apply_one_eq_qu` (S11:8223) は**両方 `CliffordCaseBData` 引数必須** = uniform-qu は caseB 限定。
- **反例 `χ_qa − a·ζ`**: A₀-supported (`inducedKernelFamily_scaledDiff_support` S08:251、`qa = a·q` ゆえ) だが
  **RHS span に無い**: 不変量 `π(∑cᵢξᵢ + ∑dⱼχⱼ) = ∑dⱼ·(χⱼ(1)/q)` は全 RHS generator で `≡0 (mod u)`
  (D の各 `μ_j − u·ζ` は `π=u`) だが `π(χ_qa − a·ζ) = a`、`0<a<u` ゆえ `a ∉ u·ℤ`。∴ hgen FALSE-caseA。
- **capstone statement 自体は TRUE** (Coq が同じ coherence を証明) ゆえ `False` は導出不可 = soundness 違反でない。
  問題は「caseA で閉じられない proof route」= 現状 spine の caseA route は broken (前 wide route と同様に false-in-caseA)。

### ⟹ milestone の再々評価 (honest)
update¹¹ の「false lemma を spine から除去」は不正確。実態: **正しい族 𝒮(C) + 正しい capstone statement に移行**
したが、**generation-based S07 engine (`coherentUnion_of_glued_...`, S07:4830) が mixed-degree family に不適**で
hgen が caseA で FALSE。wide の「wrong statement (false lemma)」より good (correct statement + 明確な fix) だが
「soundness 改善」ではない (caseA falseness は engine 差の placeholder として残存)。

### 正しい fix = Coq-faithful **`bridge_coherent`** S07 engine (generation 不要)
Coq (11.8) は `bridge_coherent` (`PFsection11.v:954`, stmt in PFsection5) で glue: **generation 仮説なし**、
両族 coherent + disjoint + **単一 bridge `χ−φ`** (A₀-supported) + その τ-identity のみ。mixed qa は `hY` 内に吸収、
`Zisometry_of_cfnorm` の norm-based 拡張が `ν` を `χ_qa−a·ζ` 上で `u·(χ_qa−a·ζ) = (u·χ_qa − a·μ_j) + a·(μ_j−u·ζ)`
(1/u 演算、ℤ-generation には不可視) 経由で決定。fix options:
- **(B) bridge_coherent S07 engine を port** (lane-a S07 territory、substantial だが self-contained、honest route)。★推奨
- (A) D を qa-diagonal enrich: qa-witness in smallest `sOf H0C` (現状 `sOf H0U'`/`H0C'` witness のみ) +
  qa-column (5.8) τ-identity (未形式化、lane-b `S11_NineElevenCaseA` と overlap) で **blocked**。
- (C) capstone を caseA/caseB split: caseB は uniform-qu で hgen genuine (narrow uniform-qu machinery 要、lane-a-tractable)、
  caseA は (A)/(B) gated。中間策。

docstring (S13:157-161) は caseB-only + FALSE-caseA + bridge_coherent fix に訂正済 (本 commit)。

## 2026-07-08 update¹⁴ (lane-a /loop, subagent) — ★ bridge_coherent engine LANDED (sorry-free, axiom-clean) — caseA fix の土台

update¹³ の verdict に基づく honest fix = Coq `bridge_coherent` (generation 不要) を port。
**`OddOrder/Peterfalvi/S07_BridgeCoherent.lean`** 新設 (additive、234 行):
- **`coherentUnion_of_glued_of_bridge`** (`Nonempty` でなく `IsCoherent` data を返す): 両族 coherent +
  span-orthogonality (`hsrc_ortho`) + image-orthogonality (`hmixed`) + 整数 degree + degree0→supported
  dictionary + **単一 bridge `χ−φ` (A₀-supported) の τ-identity** から `IsCoherent τ (X∪Y) A`。
  **generation 仮説なし** ⟹ caseA の qa-mixed でも成立。
- **sorry-free、axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)、full build green 3944 jobs。
- ★ key finding: norm-based `Zisometry_of_cfnorm` primitive は**不要**だった — isometry は bilinearity +
  orthogonality から従い、唯一の新規内容 `extends_on_supported` は Coq descaling identity
  (PFsection5.v:1044-1051、χ(1) 倍して anchor-bracket 分解して χ(1) で割る、elementary ℤ-lattice)。
- Coq 忠実 (hypotheses 弱化なし)。

### 次: capstone を bridge engine に rewire (caseA-false hgen を除去)
`coherent_SOf_H0C_of_column_identities` の `coherent_SOf_H0C_of_glued … hgen` を
`coherentUnion_of_glued_of_bridge` に置換 (X=sOf H0C, Y=SOf HC orientation)。hgen (caseA-false) 消滅、
hDτ は単一 bridge `hbridge_τ = hcol` に collapse、hmixed (§14) のみ genuine sorry として残る。structural
hyps (hsrc_ortho=span_inner_SOf_HC_sOf_H0C、hdeg/hsupp/h1A/hbridge_supp=setup) を discharge。

## 2026-07-08 update¹⁵ (lane-a /loop, subagent) — ★★ caseA-FALSE hgen を bridge engine で ELIMINATE (spine 上から除去)

update¹⁴ の `coherentUnion_of_glued_of_bridge` を capstone `coherent_SOf_H0C_of_column_identities`
に wire (S13_Orthogonality)。**caseA-FALSE generation hgen は完全消滅** (capstone は hgen/
`coherent_SOf_H0C_of_glued` を参照しない)。full build green 3944 jobs、AxiomsCheck OK、新 axiom 無。

### 新 helper (全 sorry-free、`inducedKernelFamily` 汎用)
- `inducedKernelFamily_mem_intDegree` (整数 degree)、`inducedKernelFamily_mem_apply_one_ne_zero`
  (nonzero degree)、`inducedKernelFamily_zSpan_support_of_apply_one_eq_zero` (degree0→A₀-supported、
  mixed {qu,qa} degree で uniform — `SHC_zSpan_vanish_support` の fixed-degree 制約を回避)。
- bridge の structural hyps 8 本 (hsrc_ortho/h1A/hdeg/hsupp/hχX/hdegχ 等) は全 sorry-free discharge。

### 残 sorry: 4 本 (全 TRUE、除去された false hgen とは別物)
- `hmixed` (§14 (6.7) image-orthogonality、genuine、旧と同一)
- `hbridge_τ` (μ-column τ-identity `hsofC.extension(∑μ_i1)=∑ω^σ_i1`、旧 hDτ の honest heir、§14/§9)
- `hφY` (`dζ ∈ ℤ[S(HC)]`) / `hbridge_supp` (`∑μ_i1−dζ` A₀-supported) — **TRUE だが capstone signature が
  `ζ ∈ S(HC)` + degree-match を carry しないため sorried** (caller は provide 可)。

### 次: ζ data を caller から thread して hφY/hbridge_supp を close → clean end state (hmixed + hbridge_τ のみ)
capstone に `(hζHC : ζ ∈ hyp.SOf hyp.HC)` + degree-match hyp を追加 (内部 signature のみ、spine-facing の
`exists_zeta_residual_not_orthogonal_H0C`/`w2_lt_w1_of_hypothesis_H0C` は不変)、caller が discharge
(ζ=params.zeta は deg-w₁ 既約 ∈ S(HC): `secondDerived_eq_HC`+`SOf_secondDerived_eq`、degree-match:
`degree_independent`)。⟹ (11.8) route は 2 genuine §14 sorry (hmixed/hbridge_τ) のみ、caseA-false 完全排除。

## 2026-07-08 update¹⁶ (lane-a /loop, subagent) — ★ clean end state: (11.8) capstone は genuine §14 sorry 2 本のみ

update¹⁵ の 2 threadable sorry (hφY/hbridge_supp) を caller から ζ data thread で close。
capstone signature に `hζHC : ζ ∈ SOf HC` + `hζdeg` (degree-match) 追加 (内部のみ、spine-facing 不変)、
caller `exists_zeta_residual_not_orthogonal_H0C` が discharge (hζHC = `secondDerived_eq_HC` +
`SOf_secondDerived_eq` + char params で clean、hζdeg = `degree_independent`)。full build green 3944 jobs。

### ★ (11.8) route の clean end state 到達
`coherent_SOf_H0C_of_column_identities` の残 sorry = **`hmixed` (6.7 image-orthogonality、§14 Sibley) +
`hbridge_τ` (5.8 μ-column τ-identity、§14/§9、旧 hDτ heir) の 2 本のみ、全て genuine**。
`exists_zeta_residual_not_orthogonal_H0C` / `w2_lt_w1_of_hypothesis_H0C` (spine-facing) は sorry-free。

### ⟹ lane-a の (11.8) ungated work は COMPLETE
(11.8) route は caseA-false obstruction 完全排除 + honest。残 spine sorry は全て genuine cross-lane/deep gate:
- `hmixed` / `hbridge_τ` (§14 Sibley coherence、lane-c territory)
- caseA refuter (S13_Orthogonality:101、lane-b (9.11.2) active)
- `S_not_coherent` (10.8、deep TI-counting gate)
lane-a-ownable な ungated (11.8) piece は尽きた (bridge engine + threading で honest 化完遂)。

## 2026-07-08 update¹⁷ (lane-a /loop) — broader Section16Inputs menu take-stock: lane-a producer 完遂、残は cross-lane

`feitThompson` → `sectionSixteenHypothesis_of_isMinimalSimpleOdd` (`Section16Inputs` menu、3 producer 分割)
の take-stock:
- **lane-a producer = (11.8) char route** (`card_kappaHall_lt_of_isTypeIIIorIV`/`w2_lt_w1_of_hypothesis_H0C`) —
  **honest 化完遂** (bridge engine で caseA-false hgen 排除、残 §14 sorry 2 本 hmixed/hbridge_τ は cross-lane)。
- 他 producer = **BG §14 type-P duality (FeitThompson:936、旧 "lane-f") + BG §16 maximal-pair (:708、旧 "lane-g")**
  = BG §14/§16 territory (現 lane-b/c、2026-07-06 reshape で b=BG§15/§16 追認)。type-P 構造 engine (:757/843/863)
  は sorry-free skeleton。
⟹ **lane-a の ungated FT-spine producer work は完遂**。残 spine work は cross-lane (lane-b/c BG §14/§16 +
(11.8) route の §14/lane-b/(10.8) gate)。

### lane-a descent 候補 (次 iteration、cluster-exhaustion 手順: hub defer + 次 ungated 上流に着手)
最有力 = **narrow 𝒮(H₀C) coherence の μ-column pin** (hbridge_τ = `hsofC.extension(∑μ_i1)=∑ω^σ_i1`)。
現 `coherent_sOf_H0C` は arbitrary coherent extension ゆえ pin 無 (`muColumn_tau1_pin` は Sset-coherence
`CoherentHypothesis` 限定)。narrow 版 pin 構築 = §9/§14 genuine work、lane-a-ownable の可能性 (§9 は lane-a)。
要調査: coherent_sOf_H0C を pin 付きで再構成できるか (caseB は forall_mem uniform、caseA は refuter 経由)。
次点: hmixed (§14 Sibley、lane-c) / (10.8) (deep) は cross-lane、claim-before-build 要。
