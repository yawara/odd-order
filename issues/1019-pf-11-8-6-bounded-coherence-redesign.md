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
