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
