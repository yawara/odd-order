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
