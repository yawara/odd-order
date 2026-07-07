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
