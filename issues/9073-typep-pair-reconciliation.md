---
id: 9073
slug: typep-pair-reconciliation
title: "shared-infra claim (lane c): typeP_pair reconciliation port (Coq PFsection8) — W₂ κ-Hall of T + W₁ = M_σ(T)⊓C(W₂)"
created: 2026-07-07
---

# shared-infra claim (lane c): typeP_pair reconciliation port (Coq PFsection8) — W₂ κ-Hall of T + W₁ = M_σ(T)⊓C(W₂)

## 背景

issue 0098 REACTIVATE パッケージ item 1。lane-c 所有 carve-out `reconciled_typePData_T`
(`OddOrder/Peterfalvi/S15_SAndT_Setup.lean:4476`) の 2 sorry を discharge するための shared-infra port。

- **`W2_le`** (:4520): goal `hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T`。
- **`centralizer_W1`** (:4590): goal `∀ x ∈ hyp.W2#, derivedInG hyp.T ⊓ C({x}) = hyp.W1`。

**claim-before-build**: 着手時に本 issue で claim。既存 grep = 0 (`typeP_pair`/`typeP_cent_compl`/
`of_typeP_pair` は repo 不在)。open 9000 issues scan 済 — 9000/9013 は本 port を「c の仕事」と
*参照* するのみで build を claim していない (非衝突)。

## 数学的還元 (2026-07-07 lane c の解析、Coq PFsection8 精読で確定)

Coq `of_typeP` clause (d): M の型-P 構造 (W = W₁ × W₂) は `{in W1^#, C_{M'}[x] = W2}` を持つ。
partner T は **役割 swap した** `of_typeP T V xdefW` (`xdefW : W₂ × W₁ = W`) を持ち、その clause (d) が
`∀ x ∈ W₂#, C_{T'}[x] = W₁` = まさに我々の `centralizer_W1` 目標。

**Lean 側は既に一般機構を持つ** (S16_MainResults.lean):
- `typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP hKM hK hKstar` (:3090):
  `∀ x ∈ K#, M' ⊓ C(x) = K*` — `M := T, K := W₂, K* := W₁` で `centralizer_W1` そのもの。
- `typeP_kstar_in_mf hG hM hP hKM hK hKstar`: `K* ≤ M_F`, `K* ≤ M''` — `W₁ ≤ Q ⊓ T''` = `W2_le`。

両者の前提:
- `hP : IsTypeP T` — `T_nonI` から (`typePData_of_isTypeNonI` / `IsTypeP = Nonempty (TypePData T)`)。✓
- `hKM : W₂ ≤ T` — `W₂ ≤ W ≤ T`。✓
- **Fact A** `hK : IsHallSubgroup (kappa T) (W₂.subgroupOf T)` — W₂ は T の κ-Hall。
  `W2_isComplement_T_deriv : T = T' ⋊ W₂` から。κ-Hall = M' の complement (order |T:T'|)。
- **Fact B (crux)** `hKstar : W₁ = M_σ(T) ⊓ C(W₂)` — 等価に `C_{T'}(W₂) = W₁`。
  = (8.4.d)-dual 中心化子律。**これに全体が還元される**。

⟹ **2 sorry は Fact A + Fact B に還元**。Fact B が本 port の本体。

### Fact B の位置づけ (local か global か — 要調査)

- `W₁ ≤ C(W₂)` は `W1_commutes_W2` から即 (W₁ ≤ C_G(W₂))。
- 残: `W₁ ≤ T'` (= W2_le の半分そのもの) + `|C_{T'}(W₂)| = q = |W₁|`。
- Coq の非循環な確立は **global `FTtypeP_pair_cases` (BGsummaryI 全 maximal 場合分け)** 経由 =
  port が重い。abstract `Hypothesis` から **local に** Fact B が出るか (S-side `Sdata` の対称性・
  `M_σ(T) ⊓ C(W₂)` の order 論法) が port scope の分岐点。→ 次段の alignment 機構調査で判定。

### 設計: shared leaf の generic 部品 (module-level, side 非依存 — interface guard)

1. `TypePData.centralizer_kappaFactor_eq` : `C_{M'}(d.W1) = d.W2` (Lean 版 `typeP_cent_compl`)。
   任意 `d : TypePData M` から provable (centralizer_W1 field + W1 cyclic)。**即着手可**。
2. Hall-conjugacy alignment: `d : TypePData M` を M' の任意 complement K に conjugate して
   `d'.W1 = K` にする (`TypePData.conj` + M' complement の T-conjugacy)。⟹ `d'.W2 = C_{M'}(K)`。
3. carve-out で: `d'` (W1=W₂ に align) → `d'.W2 = C_{T'}(W₂)` → Fact B で `= W₁`。

## 進捗 (2026-07-07 lane c loop¹ — verified landings)

**landed (build green、新 axiom無し)**:
1. `TypePData.derivedInG_inf_centralizer_W1_eq` (`OddOrder/GroupTheory/MaximalSubgroupType.lean`) =
   **Lean 版 Coq `typeP_cent_compl`**: 任意 `d : TypePData M` で `M' ⊓ C(d.W1) = d.W2`。generator 不要
   (⊆ は 1 個の `g∈W₁#` + centralizer_W1 field、⊇ は W cyclic ⟹ W₁,W₂ commute + W₂≤H≤M')。
   partner T の swap 版 `C_{T'}(W₂)=W₁` (= Fact B) を pin する再利用部品。
2. `subgroup_le_of_normal_coprime_index_prime` (S15_SAndT_Setup.lean) — `pgroup_le_of_normal_coprime_index`
   を **`Coprime p [S:P]` を直接取る**形に一般化 (既存 lemma は本 variant + `p∣|P|` で導出、refactor 済)。
3. `Hypothesis.W1_le_derivedInG_T` (S15_SAndT_Setup.lean) — **`W₁ ≤ T'`** (pairing-free local):
   `[T:T']=|W₂|=p`, `q≠p` ⟹ q-group W₁ が p-coprime-index normal T' に landing。

**精密還元の確定 (Coq 精読 + Lean 機構 audit)**: `reconciled_typePData_T` の 2 sorry は既存機構
(`typeP_derivedInG_inf_centralizer_kappaElement_eq` / `typeP_kstar_in_mf`) を M:=T, K:=W₂,
K*:=M_σ(T)⊓C(W₂) で instantiate すれば discharge、**前提は Fact A + Fact B のみ**:
- **Fact A** `IsHallSubgroup (kappa T) (W₂.subgroupOf T)` — これが alignment の coprimality
  (`coprime_card_derived_kappaHall_of_isComplement'` は Fact A を入力に要求) と typeP_duality を unlock。
  ⚠ **converse (complement⟹κ-Hall) は repo 不在** (`typeP_derivedInG_isComplement_kappaHall` は forward のみ)。
- **Fact B** `M_σ(T) ⊓ C(W₂) = W₁` (≡ `C_{T'}(W₂) = W₁`) — (8.4.d)-dual。W₁ ≤ Fact-B-LHS は local
  (W1_le_derivedInG_T + W1_commutes_W2)、逆包含 `C_{T'}(W₂) ≤ W₁` (≡ `C_{T'}(W₂) ≤ W`) が pairing crux。
  Coq の非循環源は global `FTtypeP_pair_cases` (BGsummaryI)。

## やること (残り)

- [x] 9000-range claim 起票 + alignment 機構調査 + generic 部品 build (loop¹)
- [ ] **Fact A** (W₂ κ-Hall of T) を確立 — これで alignment coprimality + typeP_duality が開く
- [ ] Fact A 後: alignment (datum conj で d'.W1=W₂) → `typeP_kstar_in_mf` で **W2_le 実証明**
- [ ] **Fact B** (`C_{T'}(W₂) = W₁`) — Fact A + pairing で `centralizer_W1` 実証明
- [ ] `reconciled_typePData_T` の 2 sorry discharge

## 完了条件

`reconciled_typePData_T` の `W2_le`/`centralizer_W1` sorry 解消、`lake build` 緑、AxiomsCheck OK、新 axiom なし。

## 参照

- issue 0098 (REACTIVATE パッケージ)、item 1
- Coq `coq/theories/PFsection8.v:229-746` (typeP_cent_compl / typeP_pair / FTtypeP_pair_witness / of_typeP_pair)
- Lean 既存機構: `S16_MainResults.lean:3090` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`)、
  `typeP_kstar_in_mf`、`typeP_centralizer_kappaElement_eq` (`S14_TypePCounting.lean:10847`)
- carve-out: `S15_SAndT_Setup.lean:4476` (`reconciled_typePData_T`)
