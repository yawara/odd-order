---
id: 8020
slug: signalizer-functor-port
title: "BG §14 signalizer functor (FT_signalizer_context) port — Theorem D(3)/(4) 基盤"
created: 2026-06-28
---

# BG §14 signalizer functor (FT_signalizer_context) port — Theorem D(3)/(4) 基盤

## 背景 / 位置づけ (lane-f W1 次フロンティア)

2026-06-28 lane-f が BG Theorem D(2) (`M_σ∩M^g` cyclic、issue 8019 cont.³) を完成した後の
frontier 全 survey で、**lane-f BG §14-16 の tractable ungated 群論は枯渇**と確定 (D(2) が最後の
クリーンな win)。残る FT-path sorry は全て signalizer-gated / char-gated / deep / faithfulness-blocked /
非消費。残る genuine FT-path 進捗 = **BG §14 signalizer functor 機構の genuine 構成**。

**FT 経路上の位置**:
```
FT_signalizer_context (BG §14, Coq BGsection14:866)
  → Theorem D(3)/(4) (RData = R(x) normal complement + sharply transitive、S16:904/933)
    → Theorem E cardinality (14.5c, thickenedA1_card)
      → bgTheoremE_cover_data (Pf 8.17) → card_LF_coprime_pq (S15_SAndT:463)
        → (13.17.b) → S16_NonExistenceG → POLE-2 → nonexistence_of_G → AppC → feitThompson
```

## ✅ 重要発見: abstract signalizer functor theorem **ではない** (concrete FT 構成)

当初「mathlib に signalizer functor 無し → 抽象定理ポートが要る大型」と評価したが**誤り**。Coq の
`FT_signalizer` は **具体的に定義**された FT 固有構成 (BGsection14:81-92):
```coq
Definition sigma_decomposition x := [set x.`_\sigma(M) | M : {group gT} in 'M]^#.
Definition sigma_length x := #|sigma_decomposition x|.
Definition sigma_mmax_of X := [set M in 'M | X \subset M`_\sigma].   (* 'M_σ[x] *)
Definition FT_signalizer_base x := if #|'M_σ[<[x]>]| > 1 then (the unique M of 'M('C[x])) else 1.
Definition FT_signalizer x := 'C_((FT_signalizer_base x)`_\sigma)[x].   (* R(x) *)
```
⟹ 抽象 signalizer functor theorem (Glauberman/Goldschmidt) は **不要**。FT_signalizer は
「C[x] の一意極大 N の N_σ における C[x]-centralizer」という具体構成。

**基盤は ported (D(2) で実証済み)**: `FT_signalizer_context` の証明核心 =
- **C[x] の一意極大** = Cor 12.14 `maximalContaining_centralizer_and_someSylow_eq_singleton`
  (S12_Corollary1214、sorry-free + axiom-clean、D(2) で確認)。
- **σ-fusion 推移性** (`sigma_group_trans`/`transCX`) = `fusion_control_of_mem_sigma`
  (S10_HallStructureCore:906、ported、D(2) core で使用)。
- **σ-uniqueness** = `norm_noncyclic_sigma` (Cor 12.4、ported)。
⟹ ポートは feasible。残るは概念の組立 (多セッション)。

## Lean 現状: scaffold (free field / dummy) — genuine 構成が未着手

- `SigmaDecompositionData` (S14_TypePCounting:1197) = **free `length` field の scaffold**
  (docstring「`def sigmaLength := 0` while still letting §§15-16 state their dependencies」)。
- `dummySigmaDecomposition` (S14:7896) = length=0 の dummy。
- `sigmaSharp M` (S14:1145) / `sigmaConjugacySaturation M` (S14:1149) / `Mtilde` (S14:4410) = 定義済。
- `RData` (S16:114) / `maximalConjugatesContaining` (S16:108) = D(3)/(4) target 定義済 (sorry hD3/hD4)。
⟹ genuine 構成 (`sigma_decomposition`/`sigma_length`/`sigma_mmax_of`/`FT_signalizer`) で free field を
置換する = [[scaffold-sorry-free-not-done]] の解消。**scaffold consumer (S15/S16 dep) の refactor を伴う**。

## 決定したチャンク分解 (multi-session、上流順)

**Chunk 1 (foundation — element σ-part + σ-decomposition)**:
- element の π-part 機構を確認/構成 (mathlib `... ` or 自作: cyclic ⟨x⟩ の π-Hall projection `x_π`)。
- `sigmaDecomposition x = {x_{σ(M)} : M maximal}#` / `sigmaLength x = card` を genuine def 化。
- 基本補題: `sigmaLength x = 0 ↔ x = 1` (Coq `ell_sigma0P`)、conj-不変 (`ell_sigmaJ`/`sigma_mmaxJ`)。
- `sigmaMmaxOf X = {M ∈ ℳ : X ≤ M_σ}` def + `sigma_mmax_exists` (Coq BGsection14:210)。

**Chunk 2 (FT_signalizer 構成 + 基本性質、ℓ_σ(x)=1)**:
- `FT_signalizer x` (= R(x)) def: |'M_σ[x]|>1 のとき C[x] の一意極大 (Cor 12.14) の σ-core ∩ C[x]。
- `FT_signalizer_context` 第1連言 (transitive R on 'M_σ[x] / |R|=|'M_σ[x]| / R◁C[x] / Hall) を証明。
  核心 = σ-fusion 推移性 (`fusion_control_of_mem_sigma`) + Cor 12.14 一意性。

**Chunk 3 (RData 供給 = D(3)/(4))**:
- `FT_signalizer_context` の |'M_σ[x]|>1 枝 (一意 N、R≠1、τ2/β/σ 型構造) を証明。
- `hD3` (`∀ x∈sigmaSharp M, ∃ R, RData M x R`) / `hD4` を `FT_signalizer x` で供給。
- `theoremD_msigma_conjugacy_and_centralizers` の残 2 sorry (D3/D4) を解消。

**Chunk 4 (Theorem E cardinality)**:
- Lemma 14.5(c) (`thickenedA1_card`、R(x) counting) → `theoremE_sigma_partition_and_counting`
  cardinality 連言 / Cor 14.9 covering / Cor 14.10 σ-length≤2。
- Pf-side `bgTheoremE_cover_data` 全 field 供給 → consumer `card_LF_coprime_pq` unblock。

## 完了条件

`theoremD_msigma_conjugacy_and_centralizers` の D(3)/(4) sorry 解消 (Chunk 3) を中間 milestone、
最終は `bgTheoremE_cover_data` sorry-free 化 + `card_LF_coprime_pq` unblock (Chunk 4)。各 chunk の
genuine def/補題が個別 landing し、scaffold free-field/dummy を順次置換。

## 参照

- Coq `FT_signalizer_context` (BGsection14:866)、defs (BGsection14:81-92)、`ell_sigma0P` (:222)。
- ported 基盤: Cor 12.14 `maximalContaining_centralizer_and_someSylow_eq_singleton` (S12_Corollary1214)、
  `fusion_control_of_mem_sigma` (S10_HallStructureCore:906)、`norm_noncyclic_sigma` (S12_ExceptionalBridge)。
- Lean scaffold: `SigmaDecompositionData` (S14:1197)、`RData` (S16:114)、`sigmaSharp` (S14:1145)。
- 上流 issue 8019 (Theorem E)。consumer chain = card_LF_coprime_pq → POLE-2。
- [[scaffold-sorry-free-not-done]] [[verify-port-state-by-number-not-coq-name]]

## 進捗ログ (lane d)

**2026-06-28 (lane d 立ち上げ初回): Chunk 1 の核心 genuine 構成 landed** — commits `bd4607b1` +
`f143b370` (全 axiom-clean、AxiomsCheck 登録、full build green)。

- **重要発見**: element π-part 分解は `OddOrder.GroupTheory.PiElementDecomposition` に既存
  (`exists_isPiElement_mul` 存在 + `isPiElement_mul_unique` 一意性)。これを土台に Chunk 1 を構成。
- **commit 1 (`bd4607b1`)**: `piPart π g` (element の π-part を**関数化** = unique 分解の
  `Classical.choose`)、`piPart_conj` (conj-equivariance via uniqueness)、`sigmaPart M x` (Coq
  `x.`_σ(M)`)、`sigmaDecomposition x` / `sigmaLength x` (genuine `Set G` / `ℕ` defs)、
  **`sigmaLength_eq_zero_iff`** (Coq `ell_sigma0P`: ℓ_σ(x)=0 ↔ x=1、forward は
  `exists_mem_sigma_of_prime_dvd_card`)、**`sigmaLength_conj`** (Coq `ell_sigmaJ`)。
- **commit 2 (`f143b370`)**: `piPart_self_of_isPiElement` / `piPart_eq_one_of_isPiElement_compl`、
  `isPiElement_sigma_of_mem_Msigma` (x∈M_σ ⟹ σ(M)-element)、
  `sigmaPart_eq_self_or_one_of_isPiElement_sigma` (σ(M)-element の σ(L)-part は x か 1: conj なら
  σ(L)=σ(M)、非 conj なら `sigma_disjoint_of_nonconjugate` で disjoint)、**`Msigma_ell1`**
  (x∈M_σ^# ⟹ ℓ_σ(x)=1、scaffold `length_one_of_isPiElement_sigma` の posit を genuine 証明化)。

**残 Chunk 1**: `sigma_decomposition_subG` (x∈H ⟹ decomp⊆H) **✅ landed**、`prod_sigma_decomposition`
(∏ σ-parts = x、深め、未着手 = 当面不要)。
**訂正**: 前ノートの「genuine sigmaLength は length_one_iff を満たさない」は**誤り**だった。Coq
`ell_sigma1P` (`ℓ_σ=1 ↔ x≠1 ∧ 𝓜_σ(x)≠∅`) が **まさに** scaffold の `length_one_iff`。`sigmaLength_eq_one_iff`
で証明し **`genuineSigmaDecomposition : SigmaDecompositionData G` を構成 (commit `c2e82ea9`、axiom-clean)**
= scaffold carrier の genuine 実現。`dummySigmaDecomposition` は consumer で genuine に差し替え可。

## 進捗ログ (lane d, 2 回目 — /loop)

**2026-06-28 cont. (/loop): Chunk 1 完全完了 — genuine SigmaDecompositionData carrier 実現** (commits
`bf63b78b`(subG/mem_zpowers) + `c2e82ea9`(ell_sigma1P + carrier)、全 axiom-clean、full build green)。
- `prime_dvd_orderOf_piPart` / `exists_mem_Msigma_of_isPiElement_sigma` (存在半を `length_one_of_isPiElement_sigma`
  から抽出、後者は委譲に refactor) / `sigmaLength_eq_one_iff` (ell_sigma1P) / **`genuineSigmaDecomposition`**。
- **上流判定 (重要)**: Cor 14.9 `nonidentity_covered_by_sigma_pieces` (S14、"faithfulness で証明禁止"、M̃ 要) も
  Cor 14.10 `exists_sigmaDecomposition_length_le_two` (σ-length≤2) も **signalizer functor R(x)/M̃ の下流**
  (covering→ℓ_σ≤2 が R(x) 依存)。∴ §14-16 の残 sorry の genuine 上流は **signalizer functor (Chunk 2)** に集約。
**次 = Chunk 2 (FT_signalizer R(x) 構成)**: Coq `FT_signalizer_context` (BGsection14:866) を精読済。構造 =
ℓ_σ(x)=1 で [第1連言: R 推移的 on M_σ[x] / |R|=|M_σ[x]| / R◁C[x] / Hall] ∧ [|M_σ[x]|>1 ⟹ N=一意極大 etc.]。
`FT_signalizer_base x` (=N[x]) / `FT_signalizer x` (=R[x]=C_{N_σ}[x]) def → 第1連言の trivial case
(|M_σ[x]|≤1 で R=1) から着手、hard case は sigma_group_trans (`fusion_control_of_mem_sigma`) + Cor 12.14。
[[scaffold-sorry-free-not-done]]

## 進捗ログ (lane d, 3 回目 — /loop Chunk 2)

**2026-06-28 cont.² (/loop): FT_signalizer R(x) 構成 + 第1連言の 2/4 sub-conjunct** (commits
`f95a0d11`(objects+nsRCx) / `5e5e12bf`(trivial branch) / `184fad9a`(hallR+reusable)、全 axiom-clean、
full build green、新 sorry なし)。S16_MainResults に実装。
- **objects**: `FT_signalizerBase x` (=N[x]、Coq の concrete `if |M_σ[x]|>1 then pick ℳ(C[x]) else ⊥`)
  / `FT_signalizer x` (=R(x)=(N[x])_σ ⊓ C[x])。
- **第1連言 (ℓ_σ(x)=1 で成立)**: ✅ `FT_signalizer_normal_in_centralizer` (R◁C[x]=Coq nsRCx、
  `le_normalizer_inf` + C[x]≤N[x]≤N(Msigma)) / ✅ `FT_signalizer_isHall` (R は σ(N[x])-Hall in C[x]=
  Coq hallR) / ✅ trivial branch (`FT_signalizer_eq_bot_of_not_branch`: |M_σ[x]|≤1⟹R=⊥)。
  **残 2/4 = transitive R on M_σ[x] + |R|=|M_σ[x]|** (R の conjugation action + orbit-stabilizer +
  Coq `sigma_group_trans`/transCX。最難、action infra 要)。
- **reusable**: **`isHallSubgroup_subgroupOf_inf_of_normal_isHall`** (Coq `setI_normal_Hall`: 正規
  π-Hall A◁N と H≤N で A⊓H が H の π-Hall。2nd-iso `relIndex_sup_right` 経由)。
**次 = 第1連言の transitivity/cardinality**: R (or C(X)) の {maximals} への conjugation action 設定 →
sigma_group_trans (Lean 存在未確認、要構築の可能性) → orbit-stabilizer。その後 第2連言 (|M_σ[x]|>1 枝:
一意 N / x∈τ2(N) / N type-F or P2 / complement 構造) → RData 供給 → hD3/hD4。

## 進捗ログ (lane d, 4 回目 — /loop Chunk 2: 重大発見)

**2026-06-28 cont.³ (/loop): `sigmaLength_one_centralizer_structure` が FT_signalizer_context の核を既に持つ。**
transitivity/cardinality を orbit-stabilizer でゼロ構築する必要なし — **既存 proven theorem に接続する**のが正道。

**発見**: `sigmaLength_one_centralizer_structure` (S14_TypePCounting、**sorry-free・AxiomsCheck 登録済**) は
`(D : SigmaDecompositionData G)` + `D.length x = 1` で、|M_σ[x]|>1 のとき次を供給:
**∃! N** (N maximal ∧ C[x]≤N ∧ N_σ∩C[x]≠⊥ ∧ **R=N_σ∩C[x] が σ(N)-Hall in C[x]** ∧ x primes∈τ2(N) ∧
(TypeF∨TypeP2 N) ∧ ∀M'∈M_σ[x]: [τ2∩π⊆σM'] [σ∩π⊆β] [IsComplement'((Msigma N)|N)((M'⊓N)|N)]
**[sharp transitivity: ∃!r∈R, M'^r=L]**)。docstring 自身が「R◁C[x] と sharp transitivity の headline は §16
(RData/ConjSharplyTransitiveOn=Theorem D) に preserve」と明記 → **§16 が cite すべき相手はこの S14 structure**。
`genuineSigmaDecomposition` (Chunk 1 capstone) を D に与え、`Msigma_ell1` で ℓ_σ(x)=1 を出せば、
x∈sigmaSharp M で structure が直接適用可能。

**精密 gap 分析 (structure に対する hD3/hD4 の残)**:
- **hD3 = RData M x R** (R:=Msigma N⊓C[x] を witness に): (1) **C_M(x)=M⊓C[x] が σ(M)-Hall in C[x]** [structure 外、別途] /
  (2) R◁C[x] ✅ [既証 `FT_signalizer_normal_in_centralizer` の議論を N で直接: C[x]≤N + Msigma N◁N] /
  (3) **R が C_M(x) を C[x] で complement** [Coq part(b)、structure 外] / (4) sharp transitivity on
  **`maximalConjugatesContaining M x`** [structure は **M_σ[x]** 上。両 set の関係 (x∈conj∧conj は M_σ[x] か) を要橋渡し]。
- **hD4 = RData + ∃!N**: ∃!N の core (maximal/C[x]≤N/Hall/complement[IsComplement' は `isComplement'_comm` で対称]/type/sharp trans) は structure 直供給。残 gap = **MF N=Msigma N** / **x∈ASet N ⊤ \ Msigma N** / **TypeP2 N→M の Frobenius 帰結** (structure 外の N 構造)。
- **共通の linchpin**: `FT_signalizerBase x = (structure の ∃!N)` には **`maximalSubgroupsContaining(C[x])={N}`** (全 maximal over C[x] が N=singleton、Coq 第2連言 part a) が要る。但し hD3/hD4 は N を structure から直接取れば **FT_signalizerBase 経由不要**。

**次 = bridge 構築 (上流順)**: (A) `signalizer_structure_of_mem_sigmaSharp` (structure を sigmaSharp 元へ再露出、
genuineSigmaDecomposition+Msigma_ell1 経由) → (B) hD3 の RData: R◁C[x] (既証移植) + C_M(x) Hall + complement(b) +
set 関係 (maximalConjugatesContaining↔M_σ[x]) → (C) hD4 の MF/ASet/P2 gap。my `FT_signalizer_isHall`/`_normal`
は structure と整合 (重複でなく N 接続待ち)。

## 進捗ログ (lane d, 7-9 回目 — /loop Chunk 2: RData 機構 + assembly skeleton)

**2026-06-29 cont.⁴ (/loop iter 5-8): RData assembly skeleton 完成 — conjuncts 2,4 を機構で discharge。**
commits: 一般 normality (`bd27057d`) / set-relation `maximalConjugatesContaining_eq_maximalSigma`
(`a188294d`) / sharp-transitivity core `conjSharplyTransitiveOn_of_pointed` (`6566921c`) /
**`RData_of_inputs`** assembly (`da6ed003`)。全 axiom-clean、full build green。

**Theorem D(3) RData の現状 (S16_MainResults)**:
- **conjunct 2 (R◁C[x])** ✅ = `centralizer_le_normalizer_Msigma_inf_centralizer` (任意 C[x]≤N)。
- **conjunct 4 (sharp transitivity on `maximalConjugatesContaining M x`)** ✅ =
  `maximalConjugatesContaining_eq_maximalSigma` (=M_σ[x]) + `conjSharplyTransitiveOn_of_pointed`
  (structure の from-M transitivity から full、r=b·a⁻¹)。
- **`RData_of_inputs`**: structure の (N, C[x]≤N, hsharp) + 深い M-side inputs (conjunct 1,3) から
  RData 全 4 連言を組立 (sorry-free skeleton)。**hD3 の >1 枝を conjunct 1,3 に結晶化**。

**⚠ 残 conjunct 1 (C_M(x) σ(M)-Hall in C[x]) の正確な性質 (高 context での誤判定回避メモ)**:
`mf_centralizer_hall_decomp` (S15) は C_M(⟨x⟩)=(C[x]⊓M_σ)⊔X (X cyclic, primes⊆τ2(M))。
**τ2(M)⊆σ(M)ᶜ** (`tau2_subset_sigma_compl`、def `tau2={p∉σ ∧ pRank=2}`) ゆえ X は σ 外。
**だが x∈M_σ^# では X=1**: τ2-element は M_σ-element を中心化しない (Thm 12.5
`Msigma_nilpotent_of_tau2`: p∈τ2 で C_{M_σ}(rank-2 elem-ab)=1)。⟹ C_M(x)=C[x]⊓M_σ で σ(M)-group。
∴ conjunct 1 ⟺ (a) M⊓C[x]=M_σ⊓C[x] [no-τ2-centralizer、Thm 12.5] + (b) M_σ⊓C[x] σ(M)-Hall in C[x]。
**conjunct 1 は偽ではない** — careful な τ2-centralizer 解析が要るだけ。

**⚠ 残 conjunct 3 (R⋊C_M(x)=C[x]、Coq part b)** = Frobenius complement の regular-action 構造。深い。

**次の上流順 work (fresh context 推奨)**: (1) `M⊓C[x]=M_σ⊓C[x]` for x∈M_σ^# (Thm 12.5 経由) →
conjunct 1 の (a) / (2) `M_σ⊓C[x] σ(M)-Hall in C[x]` = conjunct 1 (b) / (3) conjunct 3 (part b) /
(4) structure 適用 wiring (signalizer_structure_of_mem_sigmaSharp で N/hsharp 取得) + |M_σ[x]|=1 枝
(C[x]≤M, R=⊥) → hD3 完成 / (5) hD4 の MF=Msigma / x∈ASet / TypeP2→Frobenius gaps。
assembly skeleton `RData_of_inputs` は ready、残は M-side 構造の本体証明。

## 進捗ログ (lane d, 10-12 回目 — /loop: 深い endgame 到達 + blocker 明示)

**2026-06-29 cont.⁵ (/loop iter 9-11): case-split easy 方向 landed + 残 conjunct の本質 blocker 確認。**
commit `ba739946`: `maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le`
(C[x]≤M ⟹ 𝓜_σ(x)={M}、`exists_conj_centralizer` + N(M)=M、Theorem D(3) trivial-branch)。axiom-clean。

**⚠ 残 hD3/hD4 conjunct は一様に深く ready leverage なし (本質的 blocker、context でなく未ポート infra)**:
- **conjunct 1 (C_M(x) σ(M)-Hall in C[x] ⟺ C_M(x)≤M_σ)**: `mf_centralizer_hall_decomp` は ⟨x⟩ が
  M_σ-Hall を要し x に不適用。「σ-element の M-centralizer は σ-group」= 未ポートの §12-14 centralizer
  theory が必要。**path 未確定** (真偽含め要検証)。
- **conjunct 3 (R⋊C_M(x)=C[x], Coq part b)**: Frobenius/regular-action complement。modular-law descent
  は A≤H 不成立で不可。深い。
- **hard case-split 方向 (¬(C[x]≤M)⟹|M_σ[x]|>1)**: easy 方向の逆、深い (Coq not_sCX_M の逆向き)。
- **hD4 `MF N=Msigma N`**: **type-P2 では FittingIsTI 成立** (Thm 15.7a `fittingIsTI_of_isTypeP2`) ゆえ
  `mf_eq_msigma_of_not_fittingIsTI` 不適用 → type-依存、clean でない。x∈ASet / TypeP2→Frobenius も深い。

**結論**: signalizer functor Theorem D(3)/(4) の **assembly skeleton (RData_of_inputs) + 機構 (conjuncts
2,4 + bridge + case-split easy) は完成**。残は BG 最深 M-side 構造 (conjunct 1,3 + hard case-split + hD4
type gaps) で、各々 §12-14 の未ポート centralizer/Frobenius/type-classification infra を要する multi-session
porting。これは「上流 infra 不足」が真の blocker (難所回避でなく、上流が未整備)。**次の正しい上流 work** =
「σ-element の M-centralizer 構造」(conjunct 1 の前提) の §12-14 からのポート、または fresh-context での
careful な Coq-port。assembly skeleton は ready、cite 待ち。

## 🛑 重大発見 (lane d, iter 12): RData conjunct 1 は mis-encoded — hD3/hD4 が偽の target

**2026-06-29: RData (S16:114) conjunct 1 `Ch03.IsHallSubgroup (σ M) ((M⊓C[x]).subgroupOf C[x])`
(= C_M(x) が σ(M)-Hall in C[x]) は type-P M で偽。**
- **論拠**: `kappa_subset_sigmaCompl` (κ(M)⊆σ(M)ᶜ) + Kstar=M_σ∩C(K)。x∈Kstar^#⊆M_σ^#=sigmaSharp M で
  x は K を中心化 ⟹ K≤C(x), K≤M ⟹ **K≤C_M(x)**。K は κ-Hall (σ 外の素数)。∴ |C_M(x)| は σ(M)' 素数を
  含み **C_M(x) は σ(M)-group でない** ⟹ `IsHallSubgroup (σ M)` の第1連言 (|H| 素数⊆σM) が偽。
  type-P M (K≠⊥) かつ Kstar≠⊥ で x∈Kstar^# が実在 ⟹ hD3 `∀x∈sigmaSharp M` は偽。
- **Coq 正解 (Theorem 14.4(b)/(e))**: `R ><| 'C_(M:&:N)[x] = 'C[x]` (part b) + `\sigma(N)^'.-Hall(N)
  (M:&:N)` (part e)。∴ C_M(x)=C_{M∩N}(x) は R(σ(N)-Hall)の complement = **σ(N)'-Hall in C[x]** (N 参照)。
  Lean の `σ M` は **`σ N` (signalizer の極大) の '-Hall であるべき**で、σ(M)-Hall は誤エンコード。
- **影響**: conjunct 1 が偽 ⟹ hD3/hD4 は現エンコードのまま honest に閉じられない。私の機構 (conjunct 2,4 +
  bridge + set-relation + assembly skeleton + case-split) は**全て valid・再利用可** (conjunct 1 のエンコード
  だけが問題)。**RData は shared contract (theoremD は FT spine が cite) ゆえ無断改変不可** → hub/ユーザー判断要。
- **要決定**: RData conjunct 1 を σ(N)'-Hall (N=signalizer の極大) に修正するか。修正には N の存在 (|M_σ[x]|>1
  枝) を def に織り込む必要があり、trivial 枝 (R=⊥, C[x]≤M) では C_M(x)=C[x] が σ(M)... これも要再検討
  (trivial 枝でも κ が C[x] に入りうる)。**RData def の再設計が必要**。

## ✅ HUB 裁定 (2026-06-29)

lane-d の発見 (conjunct 1 = `IsHallSubgroup (σ M) (C_M(x) in C[x])` が type-P M で偽) を hub が実コードで検証:
- **数学的に妥当**: x∈Kstar^#⊆M_σ^# で K(κ-Hall, κ⊆σ(M)ᶜ)≤C_M(x) ⟹ C_M(x) は σ(M)' 素数を含む ⟹ σ(M)-Hall でない。Coq Thm 14.4(b)/(e) の `σ(N)'-Hall(N)(M∩N)` とも整合。**conjunct 1 は σ(N)'-Hall (N=signalizer の極大) であるべき = mis-encoding 確定。**
- **⚠ ただし「RData は FT spine が cite する shared contract」は事実誤認**: 実コード検証で
  **`RData`/`theoremD_*`/`theoremE_*` は FeitThompson.lean からも Peterfalvi/* からも一切 cite されていない**
  (grep 0 件)。consumer は S16_MainResults 内の theoremE のみ、theoremE も spine 非 cite。
  ⟹ **RData/theoremD/E は完全に δ-internal (lane-d 所有の S16_MainResults 内) かつ honest FT spine の外**。

**裁定**: RData は cross-lane 契約ではなく **δ-internal** ゆえ、STOP 条件 (d)「契約の無断改変」は**適用されない**。
**lane-d は RData conjunct 1 を Coq 正解 (σ(N)'-Hall(N=signalizer 極大)、N 存在を def に織り込む) へ自身で再設計してよい** (hub/他レーン承認不要、自クラスタ内編集)。trivial 枝 (C[x]≤M, R=⊥) の C_M(x) 性質も併せて再検討。
既存機構 (conjunct 2,4 + bridge + set-relation + assembly skeleton `RData_of_inputs` + case-split) は全て valid・再利用可。

**教訓**: 「shared contract だから無断改変不可」と escalate する前に、その def が**実際に cross-lane / on-spine で cite されているか**を grep 検証する。δ-internal な def は owner が再設計してよい (no-gating 原則; cf. `feedback-cite-sorried-lemmas-if-signature-correct`)。

**次手 (lane-d)**: (1) RData conjunct 1 を σ(N)'-Hall へ再設計 (N 存在込み) → (2) conjunct 1 (a) `M⊓C[x]=M_σ⊓C[x]` for x∈M_σ^# (Thm 12.5) / (b) σ(N)'-Hall 本体 → (3) conjunct 3 (Coq part b) → (4) hD3/hD4 完成。issue 継続。

## ✅ RESOLVED (lane d, 2026-06-29): RData mis-encoding 修正 + hD3 を conjunct 3 のみに結晶化

HUB 裁定 (δ-internal、再設計可) を受け修正完了 (commits `dcd1ace9` + `a33444c0`、axiom-clean、full build green):
- **RData conjunct 1 修正**: `IsHallSubgroup (σ M)` (type-P で偽) → **intrinsic Hall = `Nat.Coprime (card C_M(x)) (C_M(x).index)`** (σ-agnostic、docstring「C_M(x) is a Hall subgroup of C_G(x)」通り、Coq の σ(N)'-Hall と同値)。波及は RData_of_inputs のみ (theoremD/E は RData を抽象参照)。
- **RData_of_inputs 改良**: conjunct 1 (coprime) は深い入力でなく、structure 供給の **R σ(N)-Hall (hRhall) + conjunct 3 (complement)** から導出 (`IsComplement'.index_eq_card` + `IsHallSubgroup.coprime_index`)。
- ∴ **hD3 の |M_σ[x]|>1 枝 = `RData_of_inputs` の入力のうち hRhall/hsharp/hCN は全て structure (`signalizer_structure_of_mem_sigmaSharp`) 供給、唯一の真の deep 入力は conjunct 3 (Coq part b complement)**。

**教訓 (hub 記録済)**: 「shared contract で無断改変不可」と escalate する前に、def が実際に cross-lane / on-spine で cite されているか grep 検証する。δ-internal な def は owner が再設計してよい。

**残 work (上流順)**: (1) **conjunct 3 (Coq part b: R ⋊ C_M(x) = C[x])** = 唯一の deep input、Frobenius/regular-action complement / (2) structure 適用 wiring (signalizer_structure で N/hRhall/hsharp/hCN 取得) + |M_σ[x]|=1 枝 (case-split lemma 済) → hD3 完成 / (3) hD4 の MF/ASet/P2 gaps。

## ✅ 進捗 (lane d, 2026-06-29 cont.⁶ — /loop): conjunct 3 (centralizer complement) 完全 proven + hD3 の >1 枝 完成

**前ノートが「唯一の deep input・Frobenius/regular-action・modular-law descent 不可」とした conjunct 3
(`R ⋊ C_M(x) = C[x]`, Coq Thm 14.4(b)) は実は deep でなかった。** Coq 原文 (BGsection14:944 `defCx`) は
`subcent_sdprod defN` の 1 行で、**centralizer が complement を通って降下する** (factorization uniqueness)
だけ。前評価は誤った証明戦略 (modular law 直接適用) に対するもので、正しい engine は `subcent_sdprod`。

**landed (全 axiom-clean、full build green)**:
1. **`Subgroup.IsComplement'.inf_centralizer_of_normalizer`** (`OddOrder/Mathlib/SchurZassenhausConj.lean`)
   = 汎用 `subcent_sdprod`: `K`,`H` が `N` 内で complement (`K ◁ N`)、`a` が両者を normalize、`C_G(a) ≤ N`
   ⟹ `C_G(a)` 内で `K ⊓ C_G(a)` と `H ⊓ C_G(a)` が complement。証明核 = `g ∈ C(a)` を `g=k·h` 分解 →
   `a` で共役すると `g=(aka⁻¹)(aha⁻¹)` が第2の `K·H` 分解 → uniqueness (`K⊓H=⊥`) で `aka⁻¹=k`/`aha⁻¹=h`
   ⟹ `k,h ∈ C(a)`。汎用・再利用可 (signalizer theory 全般、`IsComplement'.subgroupOf_of_le` の隣)。
2. **`signalizer_centralizer_isComplement`** (S16) = conjunct 3 本体: structure の `N`-complement
   `(N)_σ ⋊ (M∩N) = N` に engine を適用 (K=(N)_σ normal, H=M∩N, a=x; x∈N は `C_G(x)≤N`、x∈M∩N)。
3. **`RData_of_gt_one`** (S16) = **hD3 の `|𝓜_σ(x)|>1` 枝 完全 assembled** (sorry-free): structure +
   `RData_of_inputs` + conjunct 3 で `∃R, RData M x R`。

**∴ conjunct 3 (前ノートの「唯一の deep input」) は解決済。残 hD3 = `|𝓜_σ(x)| ≤ 1` 枝のみ** =
`C_G(x) ≤ M` (dichotomy `not_sCX_M` の逆向き = `maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le`
の逆、Coq の transitive `C(X)`-action + orbit-count、deep)。これが closed すれば hD3 完全。
**教訓**: 「deep」評価は証明戦略依存 — 正しい engine (`subcent_sdprod`) を Coq で確認すれば tractable だった
([[scaffold-sorry-free-not-done]] と同系、原文の証明本体を読め)。次 = (1) ≤1 枝 (hard direction) or (2) hD4 gaps。

## ✅ 進捗 (lane d, 2026-06-29 cont.⁷ — /loop): full hD3 完成 — theoremD の hD3 conjunct を discharge

**前ノートが「deep (Coq `not_sCX_M` 逆向き、C(X)-transitive-action port 要)」とした dichotomy
`|𝓜_σ(x)| ≤ 1 ⟹ C_G(x) ≤ M` も実は浅かった** (conjunct 3 に続く 2 度目の過大評価)。直接論法:
`c ∈ C[x]\M` なら `Mᶜ ∈ 𝓜_σ(x)` (`x∈Mᶜ` ∵ `c⁻¹xc=x∈M`、`maximalConjugatesContaining_eq_maximalSigma`)
かつ `Mᶜ≠M` (∵ `c∉N(M)=M`) ⟹ `|𝓜_σ(x)|≥2`。**C(X)-orbit count 不要、`N(M)=M` (maximal
self-normalizing) のみ**。

**landed (axiom-clean、full build green)**:
- `centralizer_le_of_maximalSigma_le_one` (S16): dichotomy (`≤1 ⟹ C[x]≤M`、`N(M)=M` inline)。
- `exists_RData_of_mem_sigmaSharp` (S16): **full hD3** = `>1` 枝 (`RData_of_gt_one`) + `≤1` 枝
  (`C[x]≤M ⟹ R=⊥`: `C_M(x)=C[x]` で conjunct 1 trivial / conjunct 3 = `⊤⋊⊥` / `𝓜_σ(x)={M}` で
  sharp trans vacuous)。
- **`theoremD_msigma_conjugacy_and_centralizers` の hD3 conjunct を discharge** (S16, `· sorry` →
  `· exact exists_RData_of_mem_sigmaSharp hG hM`)。

**∴ Theorem D(3) (hD3) 完全 proven。残 theoremD = hD4 のみ** (`∃!N` with `MF=Msigma`/`ASet`/`P2→Frobenius`
gaps; ただし dichotomy が `¬(C[x]≤M)⟹>1` も供給ゆえ structure 適用は可能、残は `∃!N` の N-構造 gaps)。
**教訓 (再): 「deep」は証明戦略依存** — 2 度連続で BG §16 の「deep」評価が誤りだった (conjunct 3 / dichotomy)。
原文の証明本体を読み、正しい補題 (`subcent_sdprod` / 直接 2-element argument) を確認すれば浅い。

## ✅ 進捗 (lane d, 2026-06-29 cont.⁸ — /loop): `|R(x)|=|𝓜_σ(x)|` (Coq oR) + FT-path 解剖

**`card_signalizer_eq_card_maximalSigma`** (S16、axiom-clean): RData の sharp transitivity
(`ConjSharplyTransitiveOn`) を `R ≤ C_G(x)` の closure と合わせ bijection `R ≃ 𝓜_σ(x)` を構成 →
`|R|=|𝓜_σ(x)|` (Coq `oR`)。⟹ **FT_signalizer_context 第1連言ブロック完成** (transitive ✓ / `|R|=|𝓜_σ(x)|`
✓ / `R◁C[x]` ✓ / Hall ✓)。BG Theorem E の `|M̃|=(|M_σ|−1)·[G:M]` (Lemma 14.5c) の count 基盤。

**🔑 FT-path 解剖 (重要・次セッション handoff)**: spine consumer = `card_LF_coprime_pq`
(`Peterfalvi/S15_SAndT:463`, lane c, sorry)。依存鎖:
```
card_LF_coprime_pq (spine, lane c)  ←  bgTheoremE_cover_data (Pf 8.17, Peterfalvi/S10:570, sorry, owner=δ)
  ←  BG Theorem E (theoremE_sigma_partition_and_counting, S16:1598, sorry, lane d)
    ←  RData / hD3 ✅ (本セッション完成)
```
- **`card_LF_coprime_pq` が実際に使うのは `BGTheoremECoverData.primeFactors_disjoint` のみ** (S15_SAndT:455
  derivation note)。partition core は **既に proven** (`sigma_reps_pairwise_disjoint` /
  `sigma_reps_prime_cover` / `exists_reps_sigma_partition`、S16)。
- **だが `bgTheoremE_cover_data` (S10:570) は full struct を要求**: `primeFactors_disjoint` (partition ✅) +
  **`thickenedA1_card` (14.5c R(x) cardinality、deep)** + G# cover (`BGTheoremETypeICovering` 等)。
  しかも struct fields は Peterfalvi `mainSubgroup`/`π` 表現 (BG `σ(Mᵢ)`/`Msigma` でなく) ⟹ 翻訳要
  (`(Mᵢ)_s=M_F` for type I)。
- **⟹ 次の FT-path 選択肢**: (A) **14.5c (thickenedA1_card) を port** = `|R|=|𝓜_σ(x)|` (本セッション) を土台に
  `|M̃|=(|M_σ|−1)·[G:M]` の coset count (deep、BG Lemma 14.5c) → theoremE → bgTheoremE_cover_data 完成 →
  spine unblock。 (B) **cross-lane: `card_LF_coprime_pq` を partition-only lemma に refactor** (lane c 協調要、
  bgTheoremE_cover_data の deep cardinality を bypass、最短 spine unblock だが lane 境界越え)。 (C) hD4
  (theoremD 完成だが δ-internal、spine 非直結)。**推奨 = (A)** (genuine 上流・lane-d 単独・hD3 の自然な続き)。
**教訓: spine consumer が full struct を cite していても、実使用 field を grep 確認** (card_LF は disjoint のみ)。

## ✅ 進捗 (lane d, 2026-06-29 cont.⁹ — /loop): `piPart_mul_of_commute` (Coq consttM) — 14.5c cluster の基礎工具

14.5c (cardinality) cluster の依存を Coq で精査:
```
14.5c card_class_support_sigma (|M̃^G|=(|M_σ|−1)·[G:M])
  ← 14.5a sigma_cover_disjoint (x·R[x] ∩ y·R[y]=∅)  ← FT_signalizer uniqueness (∃!N) + sdprod tiRyNx + σ-cover-decomp
  + cover identity (M̃^G = ⋃ x·R[x]) + exchange_big double-count + orbit-stabilizer ([G:M])
  ← sigma_cover_decomposition (σ-decomp(x·x')={x,x'}, Coq Remark @BGsection14:1055)  ← **consttM (π-part of commuting product)**
```
**`piPart_mul_of_commute`** (S14、axiom-clean、AxiomsCheck 登録): `Commute x y ⟹ piPart π (x*y)=piPart π x · piPart π y`。
証明 = 両 π-part/π′-part は x,y の冪ゆえ pairwise commute (`hcomm.zpow_zpow`) → `x*y=(xπ yπ)(xπ′ yπ′)` を rearrange →
`isPiElement_mul_unique` で π-part 同定。汎用・再利用可 (Coq consttM)。

**残 14.5c cluster (上流順、全 deep multi-session)**:
1. **`sigma_cover_decomposition`** (σ-decomp(x·x')={x}∪{x'}^# for ℓ_σ(x)=1, x'∈R[x]): `piPart_mul_of_commute`
   (本セッション) で `sigmaPart L (x·x') = sigmaPart L x · sigmaPart L x'` 化 + structure の σ(M)/σ(N)/τ2 関係
   (x は τ2(N)-elt, x' は σ(N)-elt) で {x,x'} に collapse。**structure type info 要**。
2. **14.5a `sigma_cover_disjoint`**: 上記 + FT_signalizer uniqueness (∃!N, structure 供給) + sdprod 自明交差
   (`signalizer_centralizer_isComplement` の IsComplement' = disjoint)。
3. **14.5c**: cover identity (set 操作) + double-count (`|R|=|𝓜_σ(x)|` ✅ 本セッション + 14.5a disjoint で trivIset) +
   orbit-stabilizer for [G:M] (`ncard_conjugates_eq_index_of_normalizer_eq_self` S14:4749 在庫)。
**次 = sigma_cover_decomposition** (piPart_mul_of_commute の自然な consumer)。

## ✅ 進捗 (lane d, 2026-06-29 cont.¹⁰ — /loop): `sigma_cover_decomposition` (Coq BGsection14:1055)

**`sigma_cover_decomposition`** (S14、axiom-clean): `M,N` non-conj・`x∈M_σ^#`・`x'∈N_σ`・`Commute x x'`
⟹ `sigma_decomposition (x*x') = {x} ∪ {x'}^#`。**Coq の `constt'` route を回避し直接証明**:
`sigmaPart L (x*x') = sigmaPart L x · sigmaPart L x'` (piPart_mul_of_commute) で各 σ(L)-part を分解、
`L∼M`/`L∼N`/どちらでもない の by_cases (M,N non-conj で「両方」を排除) → part は `x`/`x'`/`1`。
- 補助 (directed `sigmaPart`): `sigmaPart_eq_self_of_conj` (L∼M ⟹ sigmaPart L x=x) /
  `sigmaPart_eq_one_of_not_conj` (L≁M ⟹ sigmaPart L x=1、σ-disjoint 経由)。再利用可。

**残 14.5c cluster (上流順)**: 1. **14.5a `sigma_cover_disjoint`** (`x·R[x] ∩ y·R[y]=∅`): sigma_cover_decomposition
(本) で共通元の σ-decomp を {x}∪{x'} と {y}∪{y'} に同定 → x=y or 矛盾 (FT_signalizer uniqueness ∃!N
[structure] + sdprod 自明交差 [`signalizer_centralizer_isComplement`])。 2. 14.5c (cover identity + double-count
[`card_signalizer_eq_card_maximalSigma` ✅] + orbit [S14:4749])。3. theoremE assemble → bgTheoremE_cover_data。
**次 = 14.5a sigma_cover_disjoint**。但し cover 文脈では M,N non-conj を structure t2Nx (x τ2(N)-elt vs σ(M)-elt) で要供給。

## ✅ 進捗 (lane d, 2026-06-29 cont.¹¹ — /loop): cover-decomp の structure 配線 (14.5a 直前)

- **`not_conj_of_mem_Msigma_of_tau2`** (S14、axiom-clean、reusable): x∈M_σ^# が τ2(N)-elt ⟹ M,N non-conj
  (M∼N なら σM=σN ∋ q|x, だが q∈τ2(N)⊆σ(N)ᶜ 矛盾)。**14.5a も使う M,N 非共役の核**。
- **`sigma_cover_decomposition_signalizer`** (S14): 上記 + `sigma_cover_decomposition` の合成 = structure
  context での cover decomp (x∈M_σ^#・τ2(N)・x'∈N_σ・commute ⟹ σ-decomp(x*x')={x}∪{x'}^#)。
**14.5c cluster 進捗**: consttM ✅ → sigma_cover_decomposition ✅ → cover-decomp 配線 ✅ → **[残] 14.5a
sigma_cover_disjoint** (signalizer for 2 elements x,y + sdprod 自明交差) → 14.5c (cover+count+orbit) → theoremE。
次 = 14.5a。

**cont.¹² 追記**: cover-decomp の corollary 2 本 (axiom-clean): `mem_sigma_cover_decomposition_signalizer`
(x∈σ-decomp(x*x')、14.5a 部品) + **`sigmaLength_cover_le_two_signalizer` = BG Cor 14.10** (ℓ_σ(x*x')≤2、
σ-decomp={x}∪{x'}^# が ≤2 元)。**14.5a の core (2-element signalizer + sdprod、~100 行 intricate) は次セッション**:
g∈x·R(x)∩y·R(y) ⟹ y=x' (cover-decomp) ⟹ x∈R(y)∩(N[x]⊓C[y]) = ⊥ (signalizer_centralizer_isComplement
を M'=N[x]/y に適用) ⟹ x=1 矛盾。structure を x,y 両方に適用 (signalizer_structure_of_mem_sigmaSharp、
general ℓ_σ=1 は 𝓜_σ(x)≠∅ から M 抽出)。

**🔑 cont.¹³ scoping (14.5a 実装 key insight, 次セッションの土台)**:
- **structure の R (`Msigma N_x ⊓ C[x]`, N_x = ∃!N を `choose`) を使う; canonical `FT_signalizer` を使わない**
  ⟹ `FT_signalizerBase x = N_x` の uniqueness bridge (`𝓜('C[x])={N}`, hD4 linchpin, deep) を**回避**。
  theoremE は R を parameter で取る (`hR : RData M x (R M x)`) ので canonical 不要、structure の R で OK。
- 精密 step (全 piece 在庫): (1) x,y に `signalizer_structure_of_mem_sigmaSharp` 適用 (N_x,N_y, choose) →
  R_x=Msigma N_x⊓C[x], R_y=Msigma N_y⊓C[y]。 (2) g=x·r=y·s (r∈R_x,s∈R_y)。`sigma_cover_decomposition_signalizer`
  (x の M_x,N_x,τ2) で σ-decomp(g)={x}∪{r}^#; 同 y で ={y}∪{s}^#。`mem_sigma_cover_decomposition_signalizer`
  で y∈σ-decomp(g)。y≠x ⟹ **y=r∈R_x⊆Msigma N_x** ⟹ N_x∈𝓜_σ(y)。 (3) x=s'... 正確には x=y' from
  x·r=y·s,r=y ⟹ s=x (commute) ⟹ **x∈R_y**。 (4) structure(y) の ∀M' clause を M'=N_x∈𝓜_σ(y) に適用 →
  `IsComplement'((Msigma N_y).subgroupOf N_y)((N_x⊓N_y).subgroupOf N_y)` → `signalizer_centralizer_isComplement`
  (a=y, M=N_x, N=N_y; y∈N_x ∵ y∈Msigma N_x) → `IsComplement'((N_x⊓C[y])..)((Msigma N_y⊓C[y])..)`。
  x∈両factor (x∈N_x⊓C[y] [x∈N_x via C[x]≤N_x; x∈C[y] via commute] かつ x∈R_y=Msigma N_y⊓C[y]) →
  `.disjoint` で x=1 矛盾。 (5) ⚠ branch: |𝓜_σ(x)|=1 (R_x=⊥) では x·R_x={x}; この場合の disjoint も要処理。
- ⚠ **長い grind 継続中** (14.5a→14.5c→theoremE→bgTheoremE→spine)。高速代替 = cross-lane refactor
  (card_LF を partition-only 化、lane c 協調) を hub/user 判断で検討推奨。

## ✅ 進捗 (lane d, 2026-06-29 cont.¹⁴ — /loop): **BG Lemma 14.5(a) core 完成** (sigma_cover_disjoint_of_inputs)

**`sigma_cover_disjoint_of_inputs`** (S16、axiom-clean、cluster 最難ピース): 異なる ℓ_σ=1 元 x,y の
cover coset `x·R(x)`, `y·R(y)` (R=Msigma N⊓C) は disjoint。証明 = 共通元 g=x·r=y·s ⟹
σ-decomp で `{x}∪{r}^#={y}∪{s}^#` ⟹ y=r, s=x ⟹ x が y-centralizer complement (M'=N_x) の自明交差に
落ちる (`signalizer_centralizer_isComplement`) ⟹ x=1 矛盾。`_of_inputs` 形 (structure data を hyp、choose 回避)。
plan 通り完遂 (1 build fix: `Set.mem_diff.mp`→`.1`)。

**残 14.5c**: (1) wrapper (structure 抽出で cover の canonical R に接続) (2) **14.5c cardinality**: cover
identity (M̃^G=⋃x·R(x)) + trivIset (14.5a ✅) + double-count (|R|=|𝓜_σ| ✅ `card_signalizer`) +
orbit-stabilizer ([G:M] `ncard_conjugates_eq_index_of_normalizer_eq_self` S14:4749) (3) theoremE assemble。
**14.5c cluster の数学核 (consttM/cover-decomp/14.5a) 完了; 残は assembly 寄り**。次 = 14.5c cardinality 組立。

## ⚠ 設計 finding (lane d, 2026-06-29 cont.¹⁵): theoremE cardinality は RData でなく structure を要する

14.5c cardinality 組立を scoping して判明: **`theoremE_sigma_partition_and_counting` は `hR : ∀x, RData M x (R M x)` を hyp に取るが、cardinality conjunct (14.5c) の trivIset (= 14.5a `sigma_cover_disjoint_of_inputs`) は signalizer structure (N_x, τ2(N_x), y-complement) を要し、RData だけでは出ない**。RData は conjunct1-4 (coprime/normal/complement/sharp-trans) のみで N/τ2 を carry しない。
- ⟹ **theoremE の cardinality を証明するには R が structure-derived (signalizer_structure_of_mem_sigmaSharp の N から) である必要**があり、hR:RData だけの現 hyp では 14.5a を呼べない。
- **選択肢**: (a) theoremE の hyp を強化 (structure data を渡す/内部で obtain) (b) theoremE 内で各 x の structure を再 obtain して 14.5a_of_inputs 適用 (c) 14.5c を別 lemma に切り出し structure を直接使う。
- これは formulation 設計判断 + 大型 assembly (~150-200行: cover identity M̃^G=⋃x·R(x) + trivIset[14.5a] + double-count[exchange_big] + orbit[|M^G|=[G:M]])。

**📍 lane d 現在地 (checkpoint, 2026-06-29 /loop ~13 turns, 9 commits)**: hD3 完全 + 14.5c cluster 数学核完成
(consttM/sigma_cover_decomposition/14.5a/Cor 14.10/|R|=|𝓜_σ|)。**残 = (A) 14.5c/theoremE assembly (上記設計
+大型、genuine BG Theorem E content) → bgTheoremE_cover_data → spine[card_LF] / (B) 高速代替 = cross-lane
refactor (card_LF を partition-only 化、lane c 協調; card_LF は primeFactors_disjoint のみ使用、partition core
は既 proven)**。hub/user 判断推奨: (A) 長い genuine 上流 vs (B) 最短 spine unblock。CLAUDE.md は genuine 上流
非 deprioritize を説くので (A) が default だが、(B) は lane c 協調で大幅短縮可。

## ✅ HUB 裁定 (2026-06-29, ユーザー判断): (A) genuine 上流を完遂

(A)/(B) の判断を hub からユーザーへ上げ、**(A) = BG Theorem E cardinality assembly を lane d 単独で完遂**に決定。
理由: CLAUDE.md の「genuine 上流を deprioritize しない / 最短 spine unblock を進捗指標にしない」方針通り。
本物の BG Theorem E content (cover identity M̃^G=⋃x·R(x) + trivIset[14.5a] + double-count[exchange_big] +
orbit[|M^G|=[G:M]]) を `bgTheoremE_cover_data` まで積み上げる。formulation は選択肢 (a)/(b)/(c) のうち lane d
裁量 (R を structure-derived にする: theoremE hyp 強化 or 内部 obtain or 14.5c 切り出し)。**(B) の cross-lane
refactor (card_LF partition-only 化) は採らない** — spine unblock の最短化は目的でない。lane d は (A) を淡々と
上流から埋める。

## ✅✅ 重大発見 (lane d, 2026-06-29 /loop¹⁶): **14.5(c) cardinality は既に DONE** — frontier は bgTheoremE_cover_data

前 checkpoint (cont.¹⁵ + HUB 裁定) は「残 = (A) 14.5c/theoremE assembly」と書いたが **stale**。frontier 全 survey で判明:

**14.5(c) cardinality は完成済み** = `sigmaConjugacySaturation_Mtilde_ncard` (S14:5342、commit `b9a7031b`
"14.5(c) COMPLETE"、**sorry-free + axiom-clean + AxiomsCheck 登録**):
`(conjClassSet (Mtilde hG D M)).ncard = (Nat.card ↥(Msigma M) - 1) * M.index`。
HUB 要請の「cover identity + trivIset[14.5a] + double-count[exchange_big] + orbit[|M^G|=[G:M]]」は **全部 S14 に landed**:
- `conjClassSet_Mtilde_eq_biUnion` (5308): cover identity 𝒞_G(M̃)=⋃ₓ x·R(x)、`Rsub_conj` 同変性経由。
- `sigmaSaturation_Rsub_count` (5153): double-count ∑|R(x)|=|M_σ#|·[G:M] (exchange_big + |R(x)|=|𝓜_σ(x)|)。
- `Mtilde_disjoint`/`xRsub_disjoint` (14.5a) + `Rsub_ncard_eq` + `normalizer_eq_self_of_mem_maximalSubgroups` (orbit)。

⟹ **HUB が (A) で要請した genuine 上流 (14.5c content) は既に完遂**。`theoremE_sigma_partition_and_counting`
(S16:1707, sorry) は **consumer 0** (grep 確認) — abstract R/RData 形で design finding の通り cardinality が
出ない intermediate。CLAUDE.md ラッパー方針より **深追い不要**。

### 真の FT-path frontier = `bgTheoremE_cover_data` (Pf 8.17, S10_MinimalSimpleStructure:570, sorry)

consumer = card_LF_coprime_pq (S15:453, primeFactors_disjoint) + S14_MaximalI:1368/2003 (primeFactors_cover
/reps/tau/typed + covering)。`BGTheoremECoverData` struct 全 field + covering 析取を構成する必要。残作業:

1. **(8.10)/(8.11) bridge `mainSubgroup M τ = Msigma M`** (linchpin): Pf 04.10:123 が明記 —
   「M_s は [BG] の M_σ」(BG Prop 16.1)。`mainSubgroup` (= M_F[I/II/V] / M'[III/IV]、(8.10)) = M_σ。
   per-type 証明: type-P2 は既存 (`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2` S15:9301,
   `msigma_isNilpotent_of_isTypeP2`)、type I (M_F=M_σ ⟺ M_σ nilpotent, `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`
   S15:231 — 残 `isTypeI → IsNilpotent M_σ`)、III/IV (M'=M_σ)。**5-type assembly、S15/S16 横断**。
2. **`primeFactors_Msigma_eq_sigma`**: π(M_σ)=σ(M) (M_σ は σ-Hall = `Msigma_isHall`)。prime fields の土台
   (`sigma_reps_prime_cover` の σ を mainSubgroup の primeFactors へ橋渡し)。← 本 /loop で着手。
3. **thickenedA1 ↔ conjClassSet Mtilde**: `supportKernel L M X` (Pf 8.14 R(x)) ↔ `Rsub` (§14 FT_signalizer)
   の identification。thickenedA1_card field 用。
4. **Cor 14.9 covering** (G# = ⋃ thickenedA1 ∪ [type-P で zTilde]): (8.8) dichotomy。covering 析取。
5. struct 組立 (reps→indexed via `exists_maximal_conjugacy_reps`、tau via `proposition_type_classification`)。

⟹ multi-session。14.5c (最深 math) DONE ゆえ残は genuine bridge 群 + 組立。次 = (8.10) bridge を上流から。

## ✅ 進捗 (lane d, 2026-06-29 /loop¹⁷): **(8.10) bridge `mainSubgroup M τ = Msigma M` 完成** (全 5 type)

bgTheoremE_cover_data の linchpin bridge を landed (S16_MainResults、axiom-clean、AxiomsCheck 登録;
S10_BGInterface は orphaned ゆえ consumer S10_MinimalSimpleStructure が import 済の S16 に配置):

- **`mainSubgroup_eq_Msigma`** (全 type): M の分類 type τ で `mainSubgroup M τ` (= M_F[I/II/V] / M'[III/IV])
  = `Msigma M`。Prop 16.1 (`proposition_type_classification`) から組立: I/II/V = clause (f)
  (M_F=M_σ ⟺ τ∈{I,II,V})、III/IV = clause (c) (τ∈{III,IV} ⟹ P1) + `isTypeP1_derivedInG_eq_Msigma`
  (P1 ⟹ M'=M_σ)。既存 `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II` (I/II のみ) を全 type に一般化。
- **`A1_eq_sigmaSharp`** (全 type): `A1 M τ` (= M_s#) = `sigmaSharp M` (= M_σ#)。mainSubgroup_eq_Msigma の系。
  既存 `A1_eq_sigmaSharp_of_typeI_or_II` を全 type に一般化。covering/thickenedA1 field 用。

⟹ Prop 16.1 が sorry-free + axiom-clean (issue 8015) ゆえ両 bridge も axiom-clean。
**bgTheoremE_cover_data の prime/cardinality field の主要 bridge が揃った**:
`primeFactors_Msigma_eq_sigma` (π(M_σ)=σ、/loop¹⁶) + `mainSubgroup_eq_Msigma` (M_s=M_σ) で
`sigma_reps_prime_cover` (σ-記述) → `BGTheoremECoverData.primeFactors_cover/disjoint` (π(mainSubgroup)) が組める。

**残**: (3) thickenedA1 ↔ conjClassSet Mtilde (`supportKernel` ↔ `Rsub`、cardinality field 用)、
(4) Cor 14.9 covering ((8.8) dichotomy)、(5) struct 組立 (reps indexed + tau 分類 + 全 field)。次 = struct 組立に
着手 (prime fields は bridge 揃い済、cardinality/covering は (3)/(4) 待ち)。

## ✅ 進捗 (lane d, 2026-06-29 /loop¹⁸): `exists_peterfalviType` (type 網羅性) landed

`exists_peterfalviType` (S16、axiom-clean、AxiomsCheck 登録): 任意の極大 M は HasPeterfalviType τ M を
持つ τ∈{I,…,V} が存在。Prop 16.1 を BG 三分 F/P₁/P₂ (網羅) 上で読む: F=I (a)、P₂=II (b)、P₁ は MF=Mσ で
V (d) else III/IV (c)。`BGTheoremECoverData.tau`/`typed` field 用。

⟹ struct の prime-side bridge + tau 網羅性が全て揃った。残 deep gate = (4) thickenedA1↔Mtilde
(`supportKernel`[Pf 8.14 R(x)=C_{M_F}(x)] ↔ `Rsub`[BG §14 (N[x])_σ⊓C(x)] の identification、深い)、
(5) Cor 14.9 covering。次 = struct 組立 (bridgeable field 実証 + (4)(5) を named sorry で isolate)。

## ✅✅ 進捗 (lane d, 2026-06-29 /loop¹⁹): **bgTheoremE_cover_data 本体組立** — 9/11 field 実証

`bgTheoremE_cover_data` (Pf 8.17、S10_MinimalSimpleStructure) を **sorry 1 個 → 実構成 (9 field 実証 +
deep gate 2 個)** に。full build 3886 green、consumer (S14_MaximalI `.{_,0}`) 不変。

**実証した 9 field** (前 /loop の bridge を配線):
- `ι`/`reps`/`tau`/`finite_index`/`maximal`/`typed`/`representatives`/`nonconjugate`: plumbing
  (`exists_maximal_conjugacy_reps` + `exists_peterfalviType`)。
- **`primeFactors_cover`/`primeFactors_disjoint`** (genuine 核心、card_LF が使う): `sigma_reps_prime_cover`
  /`sigma_reps_pairwise_disjoint` (σ-記述) を `mainSubgroup_eq_Msigma` (M_s=M_σ) + `primeFactors_Msigma_eq_sigma`
  (π(M_σ)=σ) で `π(mainSubgroup)` 形へ橋渡し。

**universe 解決**: 消費側が `.{_,0}` で ι 普遍量化 ⟹ `ι := ULift (Fin (card reps))` (Fintype.equivFin で
index) で ι を任意 universe に。`↥reps` (G の universe) 直接は型不一致。

**残 deep gate 2 個** (precise sorry):
1. `thickenedA1_card` (S10:640): `thickenedA1 M M τ` (Pf 8.14 `supportKernel` R(x)=C_{M_F}(x)) =
   `conjClassSet (Mtilde D M)` (BG §14 `Rsub` R(x)=(N[x])_σ⊓C_G(x)) の identification 待ち。これさえ出れば
   `sigmaConjugacySaturation_Mtilde_ncard` (14.5c DONE) + `mainSubgroup_eq_Msigma` で閉じる。
2. covering 析取 (S10:643): (8.8) dichotomy (BG Cor 14.9) で Type-I vs non-Type-I。

⟹ **prime partition (FT consumer card_LF が依存) は genuine 実証済**。残は signalizer R(x) の Pf↔BG
identification + covering。次 = `supportKernel ↔ Rsub` (gate 1) に着手。

## ⚠ 進捗 (lane d, 2026-06-29 /loop²⁰): gate 1 (thickenedA1_card) は **encoding faithfulness 問題** — issue 8021 起票

deep gate 1 (`thickenedA1_card`) を closing しようと Coq Pf (8.14) を精読 → **Lean の thickenedA1/supportKernel
が不忠実**と判明 (詳細 = 新 issue 8021):
- Coq `FTsignalizer M x = C_{(N[x])_F}[x]` (per-x signalizer 極大 N[x] の Fitting) vs Lean
  `supportKernel L M X x = L_F ⊓ C_G(x)` を struct field が **L=M** で使用 (= M_F)。escape する x で
  M_F⊓C[x]⊆M ≠ (N[x])_σ⊓C[x]⊆N[x] (別極大) ⟹ thickenedA1 (reps i)(reps i) は BG faithful cover でなく、
  `thickenedA1_card = (|M_σ|−1)·[G:M]` は現定義で likely false。
- ⟹ gate 1 は「supportKernel↔Rsub の identification」でなく **def/field の faithfulness 修正** (shared
  GroupTheory + S14_MaximalI consumer に跨る design 決定 = issue 8021)。sorry comment (S10:635) を更新済。

**landed ingredient**: `maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2` (S16、axiom-clean、
AxiomsCheck 登録): signalizer N[x] は type F/P₂ ゆえ `(N[x])_F = (N[x])_σ`。∴ faithful な Pf R(x) =
(N[x])_F⊓C[x] = (N[x])_σ⊓C[x] = BG Rsub(x)。修正後の gate 1 closing の鍵 (Pf R(x)=Rsub を与える)。

**残**: gate 1 = issue 8021 (encoding 修正、design 要)、gate 2 = covering 析取 (Cor 14.9)。prime partition
(9/11 field) は実証済。次 = issue 8021 の design 検討 or gate 2 (Cor 14.9) 調査。

## ✅✅ 進捗 (lane d, 2026-06-29 /loop²¹): **gate 1 (thickenedA1_card cardinality) 解消** — faithful cover wiring (hub/user 承認 Option B)

issue 8021 の design を hub/ユーザーへ上げ **Option 1 (lane d が δ struct + lane-b consumer を 1 commit で実施)** 承認 →
faithful cover への wiring 完遂 (S10 + S14_MaximalI、full build **3889 green / 63s**、所有例外 = hub 承認)。詳細 = issue 8021 RESOLVED。

- **Option A (共有 `supportKernel`→`Rsub` 再定義) は import 不可で却下**: `Rsub` (BG/Ch4/S14) ← 共有 `GroupTheory/MaximalSubgroupType` (`supportKernel`) を import ⟹ 逆向き循環。
- **採用 Option B**: `BGTheoremECoverData` に抽象 `cover : ι → Set G` field 追加、`thickenedA1_card`→**`cover_card`** に置換。witness で `cover i := conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) (reps i))` (BG faithful cover)、`cover_card` を **`sigmaConjugacySaturation_Mtilde_ncard` (14.5c DONE) + `mainSubgroup_eq_Msigma` + `Nat.card_coe_set_eq`** で**実証 sorry-free**。
- covering struct は `data.cover` に追従 + 新 field **`cover_subset_kernels`** (type-I の Frobenius kernel 包含、gate 2 sorry に bundle)。consumer `exists_typeICovering` (FT spine) の `two_le`/`covers` を追従。

**∴ 14.5c の数学 (DONE) を `bgTheoremE_cover_data` まで配線完了 — cardinality field は honest 実証**。
**残 frontier = gate 2 (covering disjunction `BGTheoremETypeICovering ∨ NonTypeICovering`, S10:664, sorry)** =
BG Cor 14.9 / (8.8.a) dichotomy。`cover_nonidentity` (G# = ⋃ 𝒞_G(M̃_i)) + `cover_subset_kernels` (type-I で
R(x)=1 ⟹ M̃=(M_i)_F#) + 各 disjointness。次の lane-d 上流 work。

## ✅ 進捗 (lane d, 2026-06-29 /loop²²): gate 2 着手 — faithful cover identity の easy half + gated skeleton

gate 2 (`cover_nonidentity` = BG Cor 14.9 cover identity) を上流から engage (S14、full build 3889 green):
- **`sigmaSharp_subset_Mtilde`** (sorry-free): `M_σ# ⊆ M̃`。ℓ_σ=1 元 x は `x = x·1` (1∈R(x)) で M̃ に入る
  cover の easy half。
- **`exists_mem_conjClassSet_Mtilde_of_ne_one`** (gated skeleton): `∀ g≠1, ∃ M maximal, g ∈ 𝒞_G(M̃ M)`。
  ℓ_σ(g)=1 を easy half で**実証**、ℓ_σ(g)≥2 を **BG Lemma 14.6 (signalizer capture: g=x·x', x'∈R(x))**
  として named sorry に isolate。canonical `genuineSigmaDecomposition` 使用ゆえ `bgTheoremE_cover_data` の
  `cover` field (= `conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) (reps i))`) に直結。
  既存の偽 surface `nonidentity_covered_by_sigma_pieces` (S14:9230、`𝒞_G(M_σ#)` で cover = BG に対し偽、
  「prove as-is するな」) の faithful 代替。

**残 = (i) Lemma 14.6 (ℓ_σ=2 capture、deep): `exists_length_one_factor` の σ(M)'-cofactor が signalizer
R(x)=(N[x])_σ∩C[x] に入ることを示す (σ-decomp が signalizer decomp と整合)。(ii) cover_nonidentity 組立
(reps への conj 還元 + sharpSubgroup ⊤ = ⋃ 𝒞_G(M̃_i))。(iii) cover_subset_kernels (type-I R(x)=1)。次 = (i)。**

## ⚠→✅ 進捗 (lane d, 2026-06-29 /loop²³): cover の deep core = `sigma_decomposition_dichotomy` 特定 + faithfulness 修正

Coq `sigma_decomposition_dichotomy` (BGsection14:1189) を精査 — cover identity の真の core:
**XOR**[ signalizer branch `∃x ℓ_σ(x)=1, x⁻¹g∈R(x)` ] ⊕ [ κ branch `∃y ℓ_σ(y)=1, ∃M∈M_σ[y], y⁻¹g∈C_M[y]# ∧ κ(M)-elt` ]。
~80 行 intricate、deps = `FT_signalizer_context`(✅=`sigmaLength_one_centralizer_structure`)・`consttM`(✅=
`piPart_mul_of_commute`)・`sigma_cover_decomposition`(✅)・**`pi_of_cent_sigma`(❌未ポート、centralizer の
π 分類)**・κ/τ₂ 機構。⟹ cover の deep core = この dichotomy port (multi-session、`pi_of_cent_sigma` が次の上流)。

**⚠ faithfulness 修正 (commit 次)**: /loop²² の `exists_mem_conjClassSet_Mtilde_of_ne_one` は **一般には偽**
だった (issue 8021 と同種): dichotomy は XOR ゆえ κ-branch 元 (type-P) は signalizer branch に入らず、どの
`𝒞_G(M̃)` にも属さない (zTilde piece へ)。⟹ `hall : ∀M, IsTypeF M` (全 type-F = κ-branch 空) を追加して**真に
修正**。ℓ_σ=1 は無条件で実証、ℓ_σ≥2 を dichotomy signalizer branch (κ 空 ⟹ 成立) として isolate。
genuine bridge **`mem_Mtilde_of_mem_coset`** (x∈M_σ#・x⁻¹g∈R(x) ⟹ g∈M̃) も追加 (dichotomy→cover の coset step)。

**教訓**: cover を述べる前に Coq dichotomy の XOR 構造を読め (signalizer branch ≠ κ branch)。
**次 = `pi_of_cent_sigma` の Lean port** (dichotomy の未ポート dep)。Coq BGsection12/14 で statement 精査要。

## ✅ 進捗 (lane d, 2026-06-30 /loop²⁴): gate 2 は **feasible** と確定 — pi_of_cent_sigma の deps は全てポート済 (stale-pointer 罠回避)

`pi_of_cent_sigma` (Coq Corollary BGsection14:797-856、~70 行) を精読。当初「deps 未ポート」と評価しかけたが、
**memory `verify-port-state-by-number-not-coq-name` に従い概念/番号で grep し直すと deps は全て descriptive 名でポート済**:
- **τ2-case uniqueness `'M('C[y])={M}`** = `maximalContaining_centralizer_eq_singleton_of_tau2_element` (S14:3032、Coq Cor 14.3 br.2、sorry-free)。
- τ2 元の elementary abelian = `exists_elemAb_rank_two_le_E_mem_of_tau2` (S14:664)。
- τ/σ partition = `mem_tau1_iff`/`mem_tau2_iff`/`mem_tau3_iff`/`mem_sigma_iff` (S12_ECore/S10_HallStructureCore)。
- Ptype 構造 = `typeP_structure` (S14:2198) / `Ptype_structure` 相当。
- σ-decomposition membership = ほぼ定義的 (`sigmaDecomposition x = {sigmaPart M x}\{1}`、4439/4514 で inline 使用)。

⟹ **gate 2 (cover) は blocked でなく feasible な substantial port**: `pi_of_cent_sigma` (~70 行、deps 揃い) →
`sigma_decomposition_dichotomy` (~80 行) → cover 組立。pi_of_cent_sigma の構造 = case split on τ2(M)-elt x':
[τ2: 𝓜(C[x'])={M} (上記 ported) + ℓ_σ(x')=1 (σ_H-decomp 論法 Coq:818-821) + τ2-elt] / [非τ2: κ-elt x' + C[x]⊆M (Ptype_structure 経由 Coq:822-856)]。

**訂正の教訓**: Coq 名 grep で「deps 未ポート→gate 2 too deep/blocked」と即断しかけた = まさに stale-pointer 罠
([[verify-port-state-by-number-not-coq-name]])。概念 grep で feasible と判明。gate 2 を「深すぎ」と deprioritize
しなくてよい (genuine 上流、deps 揃い)。**次 = pi_of_cent_sigma の port 実行** (τ2-case から: uniqueness は
ported lemma 直結、ℓ_σ(x')=1 と κ-case を埋める)。

## ✅ 進捗 (lane d, 2026-06-30 /loop²⁵): **pi_of_cent_sigma 完成確認 + BG Lemma 14.6 核心 (Coq `s'g`) 着地**

**(1) `pi_of_cent_sigma` (= `sigma_diagnostic`, S14:3335) は COMPLETE** — /loop²⁴ の「次=pi_of_cent_sigma の
port 実行」は直近 2 commit (`fa20fcc7` τ2-case uniqueness `𝓜(C[x'])={M}` + `810d1fad` τ2-case `ℓ_σ(x')=1`
`tau2_element_sigmaLength_one`) で完遂済。本 /loop で sorry-free 確認 (両 branch κ/τ2 とも proven、L3335-3660 に sorry 無し)。
⟹ gate 2 (cover) の真の上流 dep が解禁。

**(2) BG Lemma 14.6 (`sigma_decomposition_dichotomy`, Coq BGsection14:1189) の核心を port** (S14、axiom-clean、
AxiomsCheck 登録、full build 3888 green):
- **`centralizer_le_of_maximalSigma_ncard_eq_one`** (Coq `cent1_sub_uniq_sigma_mmax`, BGsection14:1008):
  `|𝓜_σ(x)|=1 ⟹ C_G(x)≤M` (unique element)。証明 = y∈C[x] が 𝓜_σ(x) を conj で permute → singleton 固定 →
  `Mʸ=M` → y∈N(M)=M (`normalizer_eq_self_of_mem_maximalSubgroups` + `mem_normalizer_of_map_conj_eq`)。**MSx'_gt1
  step の linchpin**。
- **`signalizer_coset_or_kappa_of_sigmaSharp`** (Coq `s'g`, Lemma 14.6 の心臓部): x∈M_σ^#・x' は M の σ(M)'-elt
  (≠1, x を中心化) ⟹ g=x·x' は **signalizer branch (∃y, ℓ_σ(y)=1 ∧ y⁻¹g∈R(y)、witness y=x') XOR κ branch
  (ℓ_σ(x)=1 ∧ M∈𝓜_σ(x) ∧ x'∈(C_M[x])^# ∧ x' は κ(M)-elt)** の disjunction に落ちる。**`sigma_diagnostic` の直接
  consumer**: τ2 branch → signalizer disjunct (cent1_sub_uniq で |𝓜_σ(x')|>1 を強制 + `exists_neighbor_eq_Rsub`
  で neighbour N=M 同定 → x∈Rsub D x')、κ branch → κ disjunct verbatim。

**▶▶ 残り Lemma 14.6 / cover (gate 2)**:
1. **full dichotomy assembly** `g≠1 ⟹ signalizerBranch ∨ κBranch` (Coq 第2半 BGsection14:1231-1287)。
   `s'g`-content (本 commit) を二度使う + `exists_length_one_factor` (σ-decomp 入力, S14:4617 在) + FT_signalizer_context
   (`sigmaLength_one_centralizer_structure`) + Hall conjugacy (Coq `Hall_subJ`) で `g∉M`-case を assemble。~60 行。
   ⚠ 配置注意: cover identity (S14:4965) は s'g-content (S14:5140) の**上流**ゆえ、cover の sorry を閉じるには
   cover identity を dichotomy より**下流に移動**する要 (consumer 0 = 移動安全)。
2. **cover identity** `exists_mem_conjClassSet_Mtilde_of_ne_one` (S14:4965) の `hall:∀M,IsTypeF M` 下の sorry を、
   dichotomy + 「type-F ⟹ κ(M)=∅ ⟹ κBranch 空 (x'≠1 の κ-elt が存在せず矛盾)」で閉じる。

**🔧 メモ**: `tau2_element_sigmaLength_one` / `maximalContaining_centralizer_eq_singleton_of_tau2_element`
(直近 2 commit) は AxiomsCheck 未登録のまま (lane が登録省略)。本 commit で sigma_diagnostic 系の登録 gap として
follow-up 候補 (issue or 次 /loop で登録)。次 = full dichotomy assembly。

## ✅ 進捗 (lane d, 2026-06-30 /loop²⁶): BG Lemma 14.6 — `g∈M` dichotomy corollary + σ-elt M_σ membership

dichotomy assembly に向けた 2 building block を landed (S14、axiom-clean、AxiomsCheck 登録、full build 3888 green):
- **`mem_Msigma_of_isPiElement_sigma_of_mem`** (Coq `mem_Hall_pcore (Msigma_Hall maxM)`): σ(M)-element x∈M
  ⟹ x∈M_σ (`isPiElement_sigma_of_mem_Msigma` の逆)。証明 = x の像 (M/M_σ 内) は σ(M)-elt かつ M_σ が σ(M)-Hall
  ゆえ M/M_σ は σ(M)'-group → 像 trivial → x∈M_σ。quotient orderOf 論法 (`orderOf_map_dvd` + `index_no_pi`)。
  **既存は conjugate 版 `exists_mem_Msigma_of_isPiElement_sigma` のみ; same-M 版は s'g に必須だった**。
- **`branchA_or_branchB_of_mem_maximal`** (Coq `s'g` の g∈M corollary = dichotomy disjunction for g∈M):
  g∈M maximal・σ(M)-part(g)≠1 ⟹ **signalizerBranch(g) ∨ κBranch(g)**。x=piPart(σM)g, x'=x⁻¹g で
  `mem_Msigma_…` (x∈M_σ^#) + `signalizer_coset_or_kappa_of_sigmaSharp` (s'g core) を合成。b=1 (g=x) は
  signalizer branch (x⁻¹g=1∈R(x)) で直接処理。**dichotomy の disjunction を g∈M ケースで実現**。

**▶▶ 残り Lemma 14.6 (full dichotomy `g≠1 ⟹ branchA ∨ branchB`)**: 残る gap = **g∉M ケース** (Coq 第2半
BGsection14:1264-1287)。σ_decomp(g)≠∅ で x=σ-part≠1 の M₀ を取るが g∉M₀ 一般 ⟹ branchA_or_branchB は不適用。
Coq は ¬A∧¬B 下で FT_signalizer N[x] + Hall conjugacy (`Hall_subJ`) で ⟨g⟩ を M₀∩N に conjugate → σ-part=1 矛盾。
deps: `exists_length_one_factor` (S14:4617 ✓ σ-decomp 入力)・`sigmaLength_one_centralizer_structure` (FT_signalizer ✓)・
`centralizer_le_of_maximalSigma_ncard_eq_one` (本 commit ✓)・Hall conjugacy (Lean 名 未確認、要調査)。
⟹ 次 /loop = full dichotomy の g∉M assembly。その後 cover identity (type-F で κBranch 排除) で gate 2 close。

## ✅ 進捗 (lane d, 2026-06-30 /loop²⁷): 一般 π Hall conjugacy (Coq `Hall_subJ`) — dichotomy g∉M ケースの鍵

**`exists_conj_smul_le_of_isHall`** (S14、axiom-clean、AxiomsCheck 登録、full build 3888 green): 極大 M 内で
π-subgroup X≤M は M の元で共役して任意の π-Hall K≤M に入る。**`exists_conj_smul_le_isHall_kappa` (S15、κ 特化) の
一般 π 版** (証明は同一: `aInvariant_piSubgroup_le_aInvariant_hall` で π-Hall に埋込 + `exists_conj_eq_of_isHall_subgroupOf`
で 2 つの Hall を共役)。S15 κ 版は upstream の本一般版を cite するよう将来 refactor 可 (現状 minor 重複)。

**▶▶ full dichotomy `g≠1 ⟹ branchA ∨ branchB` assembly (次 /loop、Coq 第2半 BGsection14:1264-1287)** — 全 piece
の所在確定:
1. **`by_contra` → ¬A∧¬B**。**s'g**: `∀M maximal, g∈M ⟹ sigmaPart M g=1` = `branchA_or_branchB_of_mem_maximal`
   (本セッション ✓) の対偶 (sigmaPart≠1⟹A∨B、¬A∧¬B で矛盾)。
2. **σ-decomp 抽出**: `exists_length_one_factor` (✓) で x=σ(M₀)-part≠1, ℓ_σ(x)=1, IsPiElement(σ M₀) x。
3. **WLOG x∈M_σ**: `sigma_subgroup_conj_into_Msigma_general` (S12_Cor1216:745) で M:=conj•M₀ を構成 (σ(M)=σ(M₀)
   via `sigma_conj` S10Core:619 ⟹ x=sigmaPart M g 保存)。
4. **notMg** (g∈M⟹s'g⟹sigmaPart=1=x≠1 矛盾)、**cxg** (x∈zpowers g)、**MSx_gt1** (≤1⟹`centralizer_le_of_maximalSigma_ncard_eq_one`✓⟹C[x]≤M⟹g∈M 矛盾)。
5. **FT_signalizer**: `sigmaLength_one_centralizer_structure` (✓) で N=N[x], C[x]≤N, `IsComplement'((Msigma N)|N)((M⊓N)|N)`。
6. **M∩N は σ(N)'-Hall in N**: co-Hall 補題 = `isHallSubgroup_subgroupOf_of_complement_pi_pi'` (S01:1131、**private**、
   ⟹ public 化 or S14 複製要、~8 行)。
7. **Hall conj**: `exists_conj_smul_le_of_isHall` (本セッション ✓) で ⟨g⟩ (σ(N)'-elt = `sN'g`=s'g N) を M∩N に共役 → g^z∈M。
8. **最終矛盾**: `sigmaPart M (g^z) = (sigmaPart M g)^z = x^z` (piPart_conj) = 1 (s'g M, g^z∈M) ⟹ x=1 矛盾。
⟹ 次 /loop = この assembly (~70 行 + co-Hall public 化)。その後 cover identity (type-F で κBranch 排除) で gate 2 close。

## ✅✅✅ 進捗 (lane d, 2026-06-30 /loop²⁸): **BG Lemma 14.6 (sigma_decomposition_dichotomy) 完成 + Cor 14.9 type-F cover sorry CLOSED**

§14 cover の deep core を完遂 (S14、全 axiom-clean、AxiomsCheck 登録、full build 3888 green / 1:56):
- **`sigma_conjSmul_eq`** (Coq `sigmaJ`): σ(c•M)=σ(M) as sets (per-prime `sigma_conj` 双方向 + σ⊆primes)。WLOG/最終段の鍵。
- **`sigma_decomposition_dichotomy`** (BG Lemma 14.6、Coq BGsection14:1189): **g≠1 ⟹ signalizerBranch ∨ κBranch**。
  Coq 第2半を full assembly: `by_contra` → `branchA_or_branchB_of_mem_maximal` で s'g (g∈M⟹σ-part=1) →
  σ-decomp 抽出 (`exists_length_one_factor` 不使用、`sigmaDecomposition` 直接) → WLOG x∈M_σ
  (`sigma_subgroup_conj_into_Msigma_general` で M=conj•M₀、σ(M)=σ(M₀) で x=sigmaPart M g 保存) → notMg/MSx_gt1
  (`centralizer_le_of_maximalSigma_ncard_eq_one`) → FT_signalizer N (`exists_neighbor_eq_Rsub`) → M∩N が σ(N)'-Hall
  (complement の index/card を inline 計算、private co-Hall 補題回避) → ⟨g⟩ を M∩N に Hall 共役
  (`exists_conj_smul_le_of_isHall`) → g∈Mʷ⁻¹ で s'g ⟹ x=1 矛盾。**~90 行、3 build-fix で着地** (主 fix=s'g は固定 g
  ゆえ共役は M 側を動かす [conj w⁻¹•M] のが正)。
- **`exists_mem_conjClassSet_Mtilde_of_ne_one`** (BG Cor 14.9 type-F cover): **sorry CLOSED** (旧 ℓ_σ≥2 の named
  sorry を dichotomy で discharge)。signalizer branch → `mem_Mtilde_of_mem_coset`、κ branch → IsTypeF N=κ(N)=∅ で
  即矛盾。定義位置を dichotomy 下流へ移動 (consumer 0 ゆえ安全)。

**∴ §14 cover の数学核 (BG Lemma 14.6) 完成。type-F cover identity sorry-free。**

**▶▶ 残り (gate 2 完全 close → bgTheoremE_cover_data)**: `exists_mem_conjClassSet_Mtilde_of_ne_one` は all-type-F
限定 (BG Cor 14.9 の type-I half)。**full covering disjunction `BGTheoremETypeICovering ∨ NonTypeICovering`
(S10:664)** には (a) type-P (非 type-I) branch (zTilde piece、`typeP_zTilde_*` 在) + (b) cover identity を
`bgTheoremE_cover_data.cover_nonidentity` field へ wiring が要る。次 = この wiring + type-P branch。

## ✅ 進捗 (lane d, 2026-06-30 /loop²⁹): BG Cor 14.9 covering equality (cover_nonidentity) under all-type-F

**`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`** (S14、axiom-clean、AxiomsCheck 登録、full build
3888 green): all-type-F で **G# = ⋃_M 𝒞_G(M̃)**。⊆ = Lemma 14.6 discharge した cover identity
(`exists_mem_conjClassSet_Mtilde_of_ne_one`)、⊇ = `one_not_mem_Mtilde` (1∉M̃ ⟹ 1∉𝒞_G(M̃))。
**= `BGTheoremETypeICovering.cover_nonidentity` field** (reps↔all-maximals は `Mtilde_conj_smul` で吸収)。
Lemma 14.6 の自然な帰結 = BG Cor 14.9 covering の核。

**gate 2 (bgTheoremE_cover_data S10:664 disjunction) の残 deep parts を確定**:
- **TypeICovering branch** (all-type-F): `cover_nonidentity` ✅ (本セッション)、`pairwise_disjoint_thickened` =
  `conjClassSet_Mtilde_disjoint` (S14:7913 在) + nonconjugate reps で**即可**、**`cover_subset_kernels` = deep**
  (cover i ⊆ 𝒞_G((M_i)_F#) には all-type-F で **R(x)=1** [(8.8.a) signalizer-trivial 構造、repo 未証明] が要る)。
- **NonTypeICovering branch** (else): deep (zTilde exceptional cover、`BGTheoremENonTypeICovering` の W 構成)。
⟹ gate 2 を閉じるには (a) **R(x)=1 under all-type-F** (cover_subset_kernels) と (b) **NonTypeICovering の zTilde
構成** の 2 deep piece が要る。cover_nonidentity/pairwise は揃った。次 = (a) R(x)=1-under-typeF (signalizer
trivial) の調査/構成、または gate 2 を by_cases all-type-F で restructure し TypeICovering を組んで NonTypeICovering
を named sorry に isolate。

## 🔎 進捗 (lane d, 2026-06-30 /loop³⁰): gate-2 frontier 確定調査 — cover_subset_kernels の真の依存を特定

新規 Lean なし。**gate-2 (bgTheoremE_cover_data の covering disjunction) の残依存を BG 原文 + Coq + ported 14.7
全 survey で確定** (cover_nonidentity ✅/pairwise ready の次に何が要るか):

**BG 原文 (mmd L4069 Cor 14.9, L3910 M̃ 定義)**: Cor 14.9(1) [𝓜_𝒫=∅] は **G# = ⊔ 𝒞_G(M̃_i)** (M̃ = thickened
`{xx':x∈M_σ#,x'∈R(x)}`、ℓ_σ≤2)。**M̃=M_σ# とは言っていない**。Coq `mFT_partition` Part 1 も partition のみ証明。
⟹ Lean struct の **`cover_subset_kernels` (cover_i ⊆ 𝒞_G((M_i)_F#)=𝒞_G(M_σ#)) は Cor 14.9 に無い追加 field**。

**cover_subset_kernels の真の内容 = R(x)=1 under all-type-F (M̃=M_σ#)**: これは **TRUE** (𝓜_𝒫=∅ ⟹ |M_σ[x]|=1
⟹ Rsub=⊥) **だが Theorem 14.7 の「|M_σ[x]|>1 ⟹ type-P」方向が要る**。FT_signalizer_context (Thm 14.4) は
neighbour N = type-F **or** P2 までしか言わず (S14:3797)、all-type-F でも N=type-F の |M_σ[x]|>1 を排除しない。
排除には **signalizer→type-P 構築 (Coq `Ptype_structure` の逆向き、未ポート)** が必要。

**ported 14.7 は全て `IsTypeP M` を仮説に取る** (`exists_partner`/`typeP_partner_structure`/`typeP_partner_existsUnique`、
S14:8555/9025/9363) — **逆向き (signalizer→type-P) は無い** (grep 0)。⟹ **cover_subset_kernels = 未ポートの deep
piece「|M_σ[x]|>1 ⟹ ∃ type-P maximal」** (Coq Ptype_structure 構築の逆、multi-session)。

**gate-2 両 branch とも Theorem 14.7 深部依存**:
- **TypeICovering**: cover_nonidentity ✅ (/loop²⁹) + pairwise (`conjClassSet_Mtilde_disjoint` ready) + **cover_subset_kernels**
  (= signalizer→type-P 逆、未ポート deep)。
- **NonTypeICovering**: Theorem 14.7(e) の Ẑ (zTilde) exceptional cover (deep)。

⟹ **§14 cover の数学核 (Lemma 14.6 + Cor 14.9 cover identity + covering equality) は完成**。gate-2 完全 close
は signalizer→type-P 逆向き (新 deep port) が gating。**overstatement 懸念は解消** (cover_subset_kernels は真、
ただし deep)。次 = (a)「|M_σ[x]|>1 ⟹ type-P」port (Coq Ptype_structure 逆、~multi-session) or (b) lane 再配分検討。

## 🔎 進捗 (lane d, 2026-06-30 /loop³¹): gate-2 cover_subset_kernels の tractable path 特定 — FittingIsTI-for-typeF に還元

新規 Lean なし (path 精緻化)。/loop³⁰ の「cover_subset_kernels = R(x)=1-under-typeF は 14.7 reverse (vague deep)」を
**具体的で tractable な sub-path に還元**:

**還元チェーン**: cover_subset_kernels ⟺ R(x)=1 under all-type-F ⟺ |M_σ[x]|=1 for x∈M_σ# (∀ type-F M)
 ⟸ **M_σ TI for type-F** (M_σ∩(M_σ)^g=1 for g∉M)。
- 論拠: N∈M_σ[x] (x∈N_σ∩M_σ) で N≠M なら Thm 13.9 (`sigma_disjoint_of_nonconjugate`) で M,N 共役 N=M^g、
  x∈M_σ∩(M_σ)^g。M_σ TI ⟹ =1 ⟹ x=1 矛盾。∴ |M_σ[x]|=1、Rsub=⊥。

**M_σ TI for type-F = `FittingIsTI M` for type-F** (M_F=M_σ via `maxNilpotentNormalHall_eq_Msigma_of_isTypeF`、
F(M)/M_F/M_σ の一致要確認)。repo 状況:
- ✅ `fittingIsTI_of_isTypeP2` (S15:8960) — type-P2 のみ。
- ❌ `fittingIsTI_of_isTypeF` **未ポート** = 真の missing piece (= Frobenius-kernel-TI for type-F、
  type-F M は M_σ⋊E Frobenius ゆえ kernel M_σ は TI; Isaacs Ch06 Frobenius TI infra が使える可能性)。
- `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI` (S16:1890): FittingIsTI ⟹ (M_F)# TI-subset。

**🔑 二重 unblock**: `fittingIsTI_of_isTypeF` は (1) consumer `exists_typeICovering` の **`isTI` field**
(= (M_F)# TI、`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI` 経由) と (2) **`covers` field**
(= cover_subset_kernels、R(x)=1 経由) の**両 residual sorry を同時に解禁**。

**▶▶ 次 = `fittingIsTI_of_isTypeF` の port** (type-F M の Frobenius kernel M_σ が TI)。Isaacs Ch06 Frobenius-kernel-TI
+ type-F の Frobenius 構造 (M_σ⋊E、`isFrobeniusGroup_E_of_caseTau1` 系) を接続。これが gate-2 TypeICovering branch の
唯一の deep input (cover_nonidentity ✅ + pairwise ✅ は済)。NonTypeICovering branch (Ẑ) は別 deep。

## ✅ 進捗 (lane d, 2026-06-30 /loop³²): BG Cor 14.8 part 2 (two classes) 証明 + 型-P data constructor

cover frontier (cover_subset_kernels = FittingIsTI-for-typeF、deep) を一旦保留し、completed Theorem 14.7 を使う
**Cor 14.8 (`typeP1_conjugate_and_typeP_twoClasses`) の part 2 を genuine 証明** (S14、full build green):
- **`exists_typeP_data`** (新 helper、sorry-free + axiom-clean + AxiomsCheck 登録): 任意極大 M に Theorem 14.7
  data (κ(M)-Hall K≤M / swap K*=M_σ⊓C(K) / (κ∪σ)ᶜ-Hall U) を `hall_E_exists` (solvable ↥M) で構成。
  **family-level corollary を bare `M∈maximalTypePFamily` から `exists_partner`/`typeP_covering` へ繋ぐ
  missing constructor**。
- **Cor 14.8 part 2** (𝓜_P = two conjugacy classes): `exists_typeP_data` + `exists_partner` (partner M*) +
  `typeP_family_member_data` (M* maximal+typeP) + `typeP_family_pairwise_nonconjugate` (¬conj) +
  `typeP_covering` (∀H~M∨~M*) で genuine 証明。
- **Cor 14.8 part 1** (𝓜_{P₁} single class) = isolated sorry: 「partner pair が両方 P1 でない (一方 P2)」
  = κ/κ* の type 解析が要り、clean な standalone lemma 未在 (deep 証明内に embed)。次の sub-target。

**残 §14 (δ-lane frontier)**: (a) gate-2 cover_subset_kernels = FittingIsTI-for-typeF (deep TI port) /
(b) Cor 14.8 part 1 = partner-pair-not-both-P1 (κ type 解析) / (c) Cor 14.10 (ℓ_σ≤2 general、cover-gated) /
(d) NonTypeICovering Ẑ (deep)。いずれも substantial。§14 cover の rapid-win phase は完了 (Lemma 14.6 + Cor 14.9
+ covering equality + Cor 14.8 part 2)。

## ✅ 進捗 (lane d, 2026-06-30 /loop³³): **BG Cor 14.8 完全証明** (part 1 + part 2、sorry CLOSED)

`typeP1_conjugate_and_typeP_twoClasses` を **両 part 完全証明** (S14、axiom-clean、AxiomsCheck 登録、full build
3888 green) — §14 の 1 sorry CLOSED:
- **part 1** (𝓜_{P₁} single class): M,N type-P1 で `exists_typeP_data`+`exists_partner` の partner M* が
  `isTypeP2_or_isTypeP2_partner` (M P1 ⟹ ¬P2 M ⟹ P2 M*) で type-P2 ⟹ `typeP_covering` の N~M∨N~M* で
  N~M* は (`isTypeP1_conj_smul` で M* P1、P2 と矛盾) 排除 ⟹ N~M ⟹ M~N。
- **part 2** (前 /loop³² 既証): two conjugacy classes。
- **配置修正**: `kappa_conj_smul`/`sigmaComplementPrimes_conj_smul`/`isTypeP_conj_smul`/`isTypeP1_conj_smul`
  (旧 10643~、Cor 14.8 の後) を Cor 14.8 前へ移動 (forward-ref 解消、deps は sigma_conj_smul_eq[3279 private]
  等で全て前)。

**🔧 cleanup note**: `sigma_conjSmul_eq` (5099、public、/loop²⁸ で私が追加) は既存 private `sigma_conj_smul_eq`
(3279) の重複 (当時 private を grep 見落とし)。consolidate 候補 (3279 を public 化 + 5099 削除 + dichotomy/AxiomsCheck
更新)。minor、別途。

**§14 δ-lane 残 sorry** (substantial): cover_subset_kernels (FittingIsTI-for-typeF) / Cor 14.10 (cover-gated) /
NonTypeICovering Ẑ / sigmaLength_one_frobenius_type。Cor 14.8 完了で family corollary 群は片付いた。

## 🧹 進捗 (lane d, 2026-06-30 /loop³⁴): duplicate consolidation + faithfulness findings (orphaned §14 pieces)

cover frontier (deep) を保留し、hygiene + faithfulness を整理 (S14、full build 3888 green):
- **duplicate 解消**: `sigma_conjSmul_eq` (/loop²⁸ で私が追加、public) を削除し既存 `sigma_conj_smul_eq`
  (3279、当時 private を grep 見落とし) を public 化 + 2 usages 更新 + AxiomsCheck rename。CLAUDE.md no-duplicate 準拠。
- **⚠ Lemma 14.13 (`sigmaLength_one_frobenius_type`) MIS-ENCODED 発見**: Lean 仮説 `M,N∈𝓜_σ(x)` で
  `¬IsConjugateSubgroup M N` は **inconsistent** (Thm 13.9 で σ(M)∩σ(N)=∅、だが x∈M_σ∩N_σ・x≠1 で共通素数 →
  矛盾 ⟹ 前提 vacuous)。Coq `non_disjoint_signalizer_Frobenius` (BGsection14:2412) は `1<|𝓜_σ(x)|` +
  「M は σ(N[x])'-group でない」(N[x]=signalizer neighbour) が正。docstring に ⚠ 警告追加 (vacuous 証明禁止)。
  orphaned (consumer 0)、FT 経路外。faithful 再述は `{N,hN,hMN,hinter}` → `1<ncard` + σ(N[x])'-group 条件。
- **Cor 14.10 (`exists_sigmaDecomposition_length_le_two`) は dummy-satisfiable**: `∃ D, ∀g, D.length g≤2` は
  `dummySigmaDecomposition` (length=0) で trivially 真 ⟹ genuine 証明には `genuineSigmaDecomposition` 固定 +
  cover-gated ℓ_σ≤2 が要 (scaffold statement)。orphaned。

**🛑 §14 δ-lane frontier 確定 (honest)**: rapid-win phase 完了 (Lemma 14.6 + Cor 14.9 type-F cover + covering
equality + Cor 14.8 全)。**残 on-path = deep multi-session のみ**: (1) cover_subset_kernels = FittingIsTI-for-typeF
(Frobenius-kernel-TI、消費される on-path) / (2) NonTypeICovering = Theorem 14.7(e) Ẑ (deep)。orphaned/scaffold な
14.10/14.13 は低価値。次の genuine on-path work は (1) の deep TI port。

## 🔎 進捗 (lane d, 2026-06-30 /loop³⁵): gate-2 残依存 survey — FittingIsTI-for-typeF は genuine gap, NonTypeICovering が次の tractable 候補

新規 Lean なし (frontier 精緻化)。gate-2 両 branch の deep 依存を確定:
- **cover_subset_kernels (= M_σ TI for type-F = FittingIsTI-for-typeF)**: `theoremA8_structure` (S16:4482、
  Theorem A(8)) は **M_F≠M_σ ケースのみ** (U=1, F(M) TI, |K| prime)。type-F は M_F=M_σ ゆえ **未カバー = genuine gap**。
  `fittingIsTI_of_isTypeP2` (type-P2) はあるが `_of_isTypeF` 無し。さらに Theorem D(2)
  (`Msigma_inf_conj_isCyclic`) は M_σ∩M^g **cyclic** までで TI (=1) でない ⟹ FittingIsTI-for-typeF は genuine に
  強く、Theorem A(8) の M_F=M_σ ケース (未証明) を要する deep piece。
- **NonTypeICovering (Ẑ branch)**: `cover_subset_kernels` field を**持たない** (W=Ẑ, cover_nonidentity, pairwise,
  exceptional_disjoint のみ)。cover_nonidentity (G#=⋃𝒞_G(M̃)∪𝒞_G(Ẑ#)) は **proven dichotomy
  (`sigma_decomposition_dichotomy`) から導出可** (signalizer branch→M̃ [`mem_Mtilde_of_mem_coset` 在]、κ branch→Ẑ
  [要 zTilde identification、Coq mFT_partition part 2])。⟹ **cover_subset_kernels (type-F TI gap) より tractable**。

**▶▶ 次の concrete target**: (a) **NonTypeICovering Ẑ assembly** (κ branch→𝒞_G(Ẑ#) identification + disjointness、
~50-80 行、dichotomy 利用、deep だが gap 無し) — gate-2 の 𝓜_𝒫≠∅ 枝。あるいは (b) gate-2 restructure
(by_cases all-type-F で TypeICovering の cover_nonidentity[在]+pairwise[在] を wire、cover_subset_kernels を
named sorry に isolate)。(a) が genuine math、(b) が配線。cover_subset_kernels (type-F TI) は Theorem A(8)
M_F=M_σ ケースの別 deep port。

## 進捗 (lane d, 2026-06-30 /loop³⁶): one_not_mem_zTilde prerequisite + κ→Ẑ port 精査 (deep monolith 確定)

- **`one_not_mem_zTilde`** (S14、新): `1∉Ẑ` (1∈K⊆K⊔K*、K∪K* に入る)。⟹ `sharpSubgroup Ẑ = Ẑ`、`𝒞_G(Ẑ#)⊆G#`。
  NonTypeICovering ⊇ direction の prerequisite。full build 3888 green。
- **κ→Ẑ cover identification (Coq mFT_partition part 2、L2028-2070+) を精査**: NonTypeICovering の
  cover_nonidentity ⊆ の κ branch は **deep monolith** = 2 重 WLOG (`wlog defH: H:=M` で H を M に正規化 +
  `wlog Ky': y'∈K` で κ-element を κ-Hall K に Hall_subJ 共役) + `Ptype_embedding` (cycZ/defZ で Z=K⊔K* dprod) +
  x=z·z' (z∈K*, z'∈K) 分解 → x∈Ẑ。**~50-70 行 Lean、deep Ptype/dprod machinery**。signalizer branch→M̃ は
  `mem_Mtilde_of_mem_coset` (在) で軽い。

**🛑 honest frontier (再確認)**: gate-2 両 branch とも deep multi-session port:
- TypeICovering: cover_subset_kernels = **FittingIsTI-for-typeF** (Theorem A(8) M_F=M_σ ケース未証明 gap、または
  Pf (8.13.c1) escaping-centralizer 経由、いずれも deep)。
- NonTypeICovering: κ→Ẑ cover identification (上記 ~50-70 行 monolith) + exceptional_disjoint (trivIset)。
§14 cover rapid-win phase 完了 (Lemma 14.6/Cor 14.9/covering eq/Cor 14.8)。残は sustained deep porting。
**次 = NonTypeICovering κ→Ẑ monolith を head-on で着手** (上記 2-WLOG 構造に従い multi-iteration grind)。

## ✅✅ 進捗 (lane d, 2026-06-30 /loop³⁷-⁴⁰): **κ→Ẑ identification 完成 + 一般 G# cover ⊆ 完成**

deep monolith だった **NonTypeICovering の κ→Ẑ identification (Coq mFT_partition part 2) を clean sorry-free
lemma 群に分解して完遂** (S14、全 axiom-clean、AxiomsCheck 登録、full build 3888 green)。~5 iteration で head-on grind:
- `one_not_mem_zTilde` (1∉Ẑ) / `mem_zTilde_of_mul` (y∈K*#·y'∈K#·K⊓K*=⊥ ⟹ y·y'∈Ẑ、algebraic core)
- `mem_centralizer_of_mem_sup_isCyclic` (y∈Z cyclic ⟹ y∈C(K)) / `typeP_sigmaElement_mem_Kstar`
  (y∈M_σ·centralizes y'∈K# ⟹ y∈K*、conjunct(d) `typeP_centralizer_kappaElement_eq` + Z cyclic 経由)
- `kappa_branch_mem_zTilde` (core, y'∈K) / `kappa_branch_mem_conjClassSet_zTilde` (general、⟨y'⟩を K に共役)
- `kappa_branch_dichotomy_mem_conjClassSet_zTilde` (dichotomy κ-branch → ∃K K*, g∈𝒞_G(Ẑ)、N の typeP data 構成)
- **`exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one`**: **一般 G# cover ⊆ (両 branch、all-type-F 不要)** =
  ∀g≠1, g∈𝒞_G(M̃) ∨ g∈𝒞_G(Ẑ)。signalizer→M̃ (`mem_Mtilde_of_mem_coset`) + κ→Ẑ。**BG Cor 14.9 partition の ⊆**。

**▶▶ 残り NonTypeICovering struct**: (1) Ẑ を fixed W に固定 (全 type-P Ẑ 共役 = Cor 14.8 two classes + Ẑ 対称性) /
(2) cover_nonidentity 完成 (⊇ = pieces⊆G# は `one_not_mem_Mtilde`/`one_not_mem_zTilde`+sharpSubgroup で軽い) /
(3) pairwise (`conjClassSet_Mtilde_disjoint` 在) / (4) exceptional_disjoint (Ẑ∩M̃=∅、Coq trivIset) / struct 組立。
**κ→Ẑ の deep heart は完了**; 残は struct plumbing + Ẑ-fixing。TypeICovering branch は別途 cover_subset_kernels
(FittingIsTI-for-typeF gap) 待ち。

## 🔍 調査 (lane d, 2026-06-30 /loop⁴¹): **NonTypeICovering disjointness は density_pieces で既済** — path 明確化

NonTypeICovering の hard と思っていた disjointness 群が **`density_pieces_ncard_le` (S14:8252) で既に組まれている**ことを発見 (重複構築を回避):
- `conjClassSet_T_Mtilde_disjoint` (S14:7995, **BG Lemma 14.6 = exceptional_disjoint**): `Disjoint (𝒞_G(Tset)) (𝒞_G(M̃ᵢ))` ✅
  - `Tset = (K⊔Kstar)\(⋃ N∈ZFamilyFinset, (K⊔Kstar)⊓N_σ)` = **exceptional Ẑ** (refined)。
- `conjClassSet_Mtilde_disjoint` 経由 `hpair` (pairwise M̃) ✅ / `one_not_mem_conjClassSet`+`one_not_mem_Mtilde` で
  `h1A,h1U` (1∉pieces) ✅ / `hsub`: **A∪U ⊆ G# (partition の ⊇)** ✅。
- つまり NonTypeICovering の **disjointness + ⊇ + avoid-1 は全部済**。残るは **cover ⊆ (= 私の `exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one`) を fixed-family の A=𝒞_G(Tset) に接続**。

**▶ 次の clean build = `Tset = zTilde` connector**: 2-member family `{M,Mstar}` (`exists_partner` の `hpart`) で
`⋃ = (Z⊓M_σ)∪(Z⊓Mstar_σ) = Kstar∪K` ⟹ `Tset = Z\(K∪Kstar) = zTilde K Kstar`。要 intersection facts
`(K⊔Kstar)⊓M_σ=Kstar`・`(K⊔Kstar)⊓Mstar_σ=K` (σ/κ Hall 分解、未 port、fiddly だが tractable)。これで density_pieces の A を
私の cover ⊆ に橋渡し → cover_nonidentity (G#=A∪U) → struct 組立。
**注意: gate-2 disjunction は依然 TypeICovering の `cover_subset_kernels` (FittingIsTI-for-typeF, A(8) M_F=M_σ deep gap) で block**。
NonTypeICovering 完成は ¬all-type-F branch を埋めるが gate-2 全閉には cover_subset_kernels が必須。

## 🎯 調査完了 (lane d, 2026-06-30 /loop⁴²-⁴³): **gate-2 frontier 精密マッピング** — cover_subset_kernels は単一 deep lemma に帰着

gate-2 disjunction (`bgTheoremE_cover_data`, S10:581) の **TypeICovering branch (`cover_subset_kernels`)** を精密に分解。
**周辺機械は全部済**で、残る deep gap は **ただ 1 つの clean statement** に帰着することを確認:

**cover_subset_kernels** = `𝒞_G(M̃_i) ⊆ 𝒞_G((M_i)_F#)` (docstring: type-I で R(x)=1 ⟹ M̃=M_σ#=M_F#)。要件分解:
- ✅ **R(x) card = |𝓜_σ(x)|** (`Rsub_ncard_eq`, S16:452) → R(x)=1 ⟺ |𝓜_σ(x)|≤1。
- ✅ **|𝓜_σ(x)|≤1 ⟹ C_G(x)≤M** (`centralizer_le_of_maximalSigma_le_one`, S16:1456)。
- ✅ **M_F=M_σ for type-F** (`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`, S16:5324;
  `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`, S16:3053)。
- ✅ **Frobenius kernel TI** (`IsFrobeniusGroup.trivialIntersection`, Isaacs Ch06 FrobeniusGroup:357)。
- ❌ **残 gap = `|𝓜_σ(x)| ≤ 1` for type-F M** (= M_σ が G-level TI)。route: type-F ⟹ M Frobenius
  (`typeI_frobenius`/12.7) ⟹ kernel M_σ=M_F ⟹ **G-level kernel TI** (M_σ∩M_σ^g=1 for g∉M=N_G(M_σ))。
  G-level TI を Isaacs の Frobenius-internal `trivialIntersection` から導けるか (or 別 BG 構造要) が次の核心。

**∴ gate-2 全閉の残り = 2 件のみ**:
- **(A) deep**: `|𝓜_σ(x)|≤1` for type-F (上記、単一 lemma だが genuine BG structure)。← 真の blocker、次の優先。
- **(B) plumbing**: NonTypeICovering struct 組立 (struct を sharpSubgroup W→Ẑ-set に redesign + `Tset=zTilde`
  connector + cover_nonidentity)。disjointness は density_pieces で既済。gate-2 を直接は閉じない (TypeICovering が
  block) が ¬all-type-F branch を埋める。
- 注: §14 cover MATH (κ→Ẑ + 一般 cover ⊆) は完了済。残りは (A) 1 lemma + (B) plumbing で、sprawling gap ではない。

## 🎯🎯 scoping 確定 (lane d, 2026-06-30 /loop⁴⁴-⁴⁵): **gate-2 真の blocker = Theorem D(4)** (issue 8019 と接続)

§16 を精査し gate-2 全閉の deep blocker を **Theorem D(4)** (`S16:1585` sorry) に確定。issue 8019 (BG Theorem E
cover/partition) と接続:
- ✅ **Theorem D(1)** (`msigma_fusion_control`) / **D(2)** (`Msigma_inf_conj_isCyclic`) — issue 8019 で既済。
- ✅ **Theorem D(3)** (`exists_RData_of_mem_sigmaSharp`, S16:1510) — **sorry-free**。|𝓜_σ(x)|>1 は
  `RData_of_gt_one` (S16:428)、≤1 は R=⊥ (`centralizer_le_of_maximalSigma_le_one` + singleton)。
- ❌ **Theorem D(4)** (S16:1561-1585 sorry): `¬C(x)≤M ⟹ ∃R, RData ∧ ∃! N (escaping maximal)` +
  型構造 (`IsTypeP2 N → IsTypeP M ∧ ¬FittingIsTI M`)。escaping-centralizer signalizer tail、deep。
- **cover_subset_kernels** (= gate-2 TypeICovering branch、type-F⟹R(x)=1⟹M̃=M_F#) は
  **type-F ⟹ |𝓜_σ(x)|≤1** に帰着。これは D(4) の `IsTypeP2 N→IsTypeP M` の contrapositive 近傍
  (type-F M で escaping neighbor が type-P2 なら矛盾) だが D(4) full proof 待ち。Theorem A(8) は M_F≠M_σ
  しか cover せず type-F (M_F=M_σ) を与えない。

**∴ D-lane gate-2 残 = (A) Theorem D(4) [S16:1585、escaping signalizer tail、deep multi-session] +
(B) NonTypeICovering plumbing [gate-2 を単独では unblock せず]**。§14 cover math (κ→Ẑ + 一般 cover ⊆) は完了。

**進捗 (B 着手)**: `typeP_Z_inf_Msigma_eq_Kstar` (S14、sorry-free): `Z⊓M_σ=K*` (base member)。
`typeP_neighbor_Kstar_eq_Z_inf_Msigma` を N=M に特殊化。`Tset=zTilde` connector の base case
(残: partner の `Z⊓Mstar_σ=K` + family={M,Mstar} で `Tset=Z∖(K∪K*)=zTilde`)。

**⚠ frontier flag**: 真の gate-2 blocker (Theorem D(4)) は BG signalizer functor 最深部・multi-session 大型。
§14 cover math 完了後、tractable な単一 win は connector/plumbing (gate-2 を単独 unblock せず) のみ。
