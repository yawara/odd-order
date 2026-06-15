---
id: 2007
slug: s14-prop142-g-blocked
title: "Prop 14.2 case-τ₁ (g): needs BG Thm 3.10(a) + Lem 12.17 TI"
created: 2026-06-15
---

# Prop 14.2 case-τ₁ (g): needs BG Thm 3.10(a) + Lem 12.17 TI

## 背景

`typeP_structure` (BG Prop 14.2) は 2026-06-15 に case-τ₃ 全 5 + case-τ₁ の
WLOG/(a)/(K\*≠1)/(b1)/(d) まで完成 (commit `7e289354` 等)。**残 sorry は case-τ₁ (g) 1 本のみ**
(`OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean`)。

(g): `IsTypeP2 M → σ(M)=β(M) ∧ ∃q prime, |K|=q ∧ M_σ が TI`。
case-τ₃ では M=P₁ ゆえ vacuous だが case-τ₁ では M が P₂ 可能ゆえ実内容が要る。

BG 原文 (mmd L3850) の chain:
1. U=E₂E₃≠1 ⟹ E は kernel U の Frobenius 群。
2. **Lem 14.1** ⟹ C_{M_σ}(U)=1, M_σ nilpotent。
   - repo 14.1 (`msigma_structure_of_notMem_sigma_kappa`) は単一 Sylow の Ω₁ 形。
   - C_{M_σ}(U)=1 は π(U) の 1 素数 p を選び A_p=Ω₁(Syl_p)≤U で橋渡し可 (=この issue の小部分、可)。
3. **Thm 3.10(a)**: K prime on M_σ ⟹ |K| 素数。**🛑 repo 未形式化**
   = 「solvable Frobenius 群 G=KR が nilpotent 群に coprime 作用、C_M(K)=1、C_M(x)=C_M(R)
   ⟹ R cyclic of prime order」(BG mmd L1267)。§3 rep-theory (Lane A 領域、3.4/3.5/3.6 のみ済)。
4. U=[U,K]=E' → **Lem 12.19** (✅ `derivedE_centralizes_betaComplement`) → β=σ。
5. **Lem 12.17 TI 形**: M_σ∩M_σ^g が β'-group (∀g∈G−M) ⟹ =1 (TI)。**🛑 repo 未形式化**
   - repo 12.17 (`Msigma_E_relations`) は `C(E)⊓M_σ≤M_σ'` ∧ `[M_σ,E]=M_σ` のみ
     (docstring「原典の M_σ∩M^g cyclic 評価は後続」)。TI 部分は別命題。

## やること

- [x] **Prop 3.9 ✅** (`S03g_Thm310.isCyclic_of_isPGroup_of_isFrobeniusAction`, commit `25de8490`):
      odd p-group の Frobenius 作用 ⟹ cyclic。Gorenstein G 5.3.14 の Isaacs Ch06 等価で攻略。
- [ ] **BG Thm 3.10(a)** (`|R|` 素数) を `S03g_Thm310.lean` に形式化 — **次の大物 rep-theory**:
  - statement framing 決定 (abstract `MulDistribMulAction (U⋊K) M_σ` vs concrete 共役 in G;
    Thm 3.7 `isNilpotent_of_normalizing_primeOrder_fixedPointFree`=S03c の concrete 形が precedent。
    (g) の適用は共役ゆえ concrete 形が橋渡し楽かも)。
  - **Case 1** (M に proper G-invariant 正規 M₀): |G|+|M| 帰納、M₀ maximal G-inv + quotient 作用
    (Prop 1.5(d))。
  - **Case 2** (M minimal normal = elem ab r-group): **Clifford (G 3.4.1) + G 3.4.3 + Wedderburn 成分
    分解 V=⊕Wx の dim 数え `dim C_V(P)=|R:P|·dim W`, prime action `dim C_V(P)=dim C_V(R)` ⟹
    `|R:P|=1` ⟹ |R|=p**。infra = `GroupTheory.RepresentationTheory.CliffordConjugateChar`
    (S03d/S03e で使用、~2835 行)。**§3B Thm 3.4/3.5 規模の effort**。
  - (g) は (a) のみ要 ((b)|M|=|C_M(R)|^p / (c) は不要)。R=K=E₁ は cyclic (12.1d) ゆえ Prop 3.9
    step は (g) では skip 可 (cyclic 前提の specialization でもよい)。
- [ ] Lem 12.17 の TI 形 (M_σ∩M_σ^g β'-group) を §12 (`S12_E` 付近) に追加。
- [ ] C_{M_σ}(U)=1 の Lem 14.1 橋渡し helper を S14 に追加 (π(U) 1 素数 → A_p≤U)。
- [ ] 上が揃ったら case-τ₁ (g) を埋める (typeP_structure sorry-free 化)。

## 🔑 アーキテクチャ確定 (2026-06-15, lane-h) — 簡素化された証明経路

実装調査の結果、**当初プランより大幅に簡素化**できることが判明 (Case 1 帰納が不要、Clifford 全体も不要):

### 核心の数え上げ = **trace でなく honest dim count** (重要な訂正)
trace formula `dim V^H = ⅟|H|·Σ tr ρ(h)` は **char r で lossy** (`(finrank V : k)` が 0 になり得る、
合同のみで等式不可) ⟹ **使えない**。代わりに **honest integer 次元等式**:
> **keystone**: `H` が weight-space ブロック `{Wᵢ}` を**自由に**置換するなら `finrank V = |H|·finrank V^H`。

証明 = H-軌道分解 (各軌道 = |H| 個の同次元ブロック、軌道和写像 `w ↦ Σ_h ρ(h)w` が `W_{i₀} ≅ V_o^H`)。
**= 汎用線形代数、`OddOrder/GroupTheory/RepresentationTheory/FreeBlockPermutation.lean` に実装中**
(`finrank_eq_card_mul_finrank_invariants_of_freeBlock`, interface 確定・proof は subagent 進行中)。

### `|R|=p` の導出 (keystone を 2 回適用)
weight 分解 (K abelian, alg-closed F̄, char∤|K|) に keystone を `H=R` と `H=⟨x⟩=P` (x∈R# 素数位数) で適用:
`finrank V = |R|·finrank V^R` ∧ `finrank V = p·finrank V^P`。cond(3) `C_V(x)=C_V(R)` ⟹ `finrank V^P=finrank V^R`
(≥1) ⟹ **|R|=p**。**irreducibility も transitivity も不要** (自由置換 + cond3 のみ)。

### freeness (L4) = abelian Frobenius
g∈R# は K に FPF (Frobenius) ⟹ K̂ (指標) に FPF ⟹ 非自明指標を固定しない。自明指標の weightSpace
= `C_V(K)` = 0 (C_M(K)=1 + base change)。⟹ ρ(g) が weightSpace を fixed-block なしで置換。

### 層構造 (3 層、当初の「§3B 規模」より小)
1. **keystone** (汎用): `FreeBlockPermutation.lean` ✅interface / proof 進行中。
2. **module core**: ρ irreducible faithful, G=KR Frobenius, K **elem abelian** (q-group), coprime,
   C_V(K)=0, cond(3) ⟹ |R|=p。= base change F̄ + L3 (weightSpace IsInternal) + L4 (freeness) + keystone×2。
   **K abelian への還元** = `K₀ minimal normal ≤K` で C_V(K₀)∈{0,V} 二分律 → |G| 帰納 (BG Case 2 前半。
   `thm34_aux`/`thm35_aux` の帰納形を踏襲)。
3. **outer**: M nilpotent → **minimal G-normal M₀ (elem abelian, irreducible) を取るだけ** (Case 1 帰納不要!
   hyps は M₀ に制限可)。abstract `MulDistribMulAction G M` + 具体 conjugation wrapper
   (`isNilpotent_of_normalizing_primeOrder_fixedPointFree` (S03c) パターン)。

### 確定した再利用インフラ
- weightSpace API (S03e: `weightSpace`/`map_weightSpace`/`iSupIndep_weightSpace`/`conjChar`)。
- base change (`BaseChange.lean`: `baseChangeRepresentation`/`finrank_invariants_baseChangeRepresentation`
  = 次元 base-change 不変/faithful 保存)。
- 単純対角化 `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo` (Pi.lean) = L3 span。
- elem-ab→ZMod module (`OperatorMaschke.lean`)、minimal normal→elem ab (`ChiefFactor.lean`/Isaacs Ch03)。

### 残タスク (この issue)
- [ ] keystone proof (FreeBlockPermutation, subagent 進行中)
- [ ] L3: weightSpace の IsInternal (support 制限 + alg-closed span via Pi.lean)
- [ ] L4 + module core terminal (|R|=p assembly)
- [ ] K-abelian reduction 帰納
- [ ] outer (minimal normal + MulDistribMulAction + 具体 wrapper)
- [ ] Lem 14.1 Frobenius 形 (C_{M_σ}(U)=1) / Lem 12.17 TI 形 / σ=β (Lem 12.19) bridge → (g) 配線

## 完了条件

`typeP_structure` が sorry-free + axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。

## 参照

- `notes/bg/s14_typeP_counting.md`「✅✅ case-τ₁ (b1) COMPLETE」(2026-06-15)
- commit `7e289354` (case-τ₁ b1)
- BG mmd: Prop 14.2 = L3821, Thm 3.10 = L1267, Lem 12.17 = L3448, Lem 14.1 = L3811
- repo: Thm 3.10 未形式化 (§3 = `S03*`, 3.4/3.5/3.6 のみ) / Lem 12.17 = `Msigma_E_relations` (S12_E:72)
