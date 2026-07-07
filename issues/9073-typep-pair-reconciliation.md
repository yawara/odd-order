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

## 進捗 (2026-07-07 lane c loop² — route 精密化: typeP_duality 経由と確定)

**local coprimality route は gated と実証確認**: `W2_card_coprime_Q_card` (S16_NonExistenceGCore:2122)
= `Coprime |W₂| |Q|` は `FieldNormalizerData` (→ `Q_elementaryAbelian`, `|Q|=q^k`) を要求。⟹
alignment coprimality `p∤|T'|` は abstract Hypothesis から local に出ず、深い §13 (FieldNormalizerData/
IsTypeII T) gated。**docstring の gating 記述は正しい**。

**⟹ honest route = 既存 `typeP_duality` の partner** (global port 不要、type-P only, issue 0098 と整合):
`typeP_duality` (S14_TypePCounting:9928) を **S に適用** (κ-Hall K=W₁, Kstar:=M_σ(S)⊓C(W₁)=W₂) すると、
unique partner `Mstar` が **Fact A (W₂ κ-Hall of Mstar) + Fact B (W₁ = M_σ(Mstar)⊓C(W₂))** を both 満たす
(∃! の conjunct そのもの)。さらに ∃! の最終 conjunct = covering `∀H type-P, conj H S ∨ conj H Mstar`。
- **step 1 (次)**: S-side κ-Hall setup — `IsHallSubgroup (kappa S) (W₁.subgroupOf S)` + `W₂ = M_σ(S)⊓C(W₁)`
  を S_typeP2/Sdata から確立 (Sdata.W1=W₁ が κ-Hall である identification; `card_P_eq` が内部で
  `typePData_of_kappaHall_hallComplement_W2` 経由で使う κ-Hall を expose する必要)。
- **step 2**: `typeP_duality S` → Mstar + Facts A/B(Mstar) + covering。
- **step 3**: covering + `¬conj(S,T)` → `T ~ Mstar`。
- **step 4 (alignment)**: `T = Mstar^g`、g が W₂ を固定 (W₂ κ-Hall 一意性) → Facts A/B が W₂,W₁ 保ったまま
  T へ transfer。= Coq `FTtypeP_pair_witness` の alignment 構造の Lean 版 (既存 typeP_duality 上に build)。
- **step 5**: Facts A/B(T) → `typeP_derivedInG_inf_centralizer_kappaElement_eq` / `typeP_kstar_in_mf` で
  `centralizer_W1` / `W2_le` を discharge。

⟹ item 1 は **global port でなく typeP_duality + alignment** (multi-session, type-P only)。頭から engage。

## やること (残り)

- [x] 9000-range claim + generic 部品 build (loop¹) + route 精密化 typeP_duality 経由確定 (loop²)
- [ ] **step 1**: S-side κ-Hall setup (`IsHallSubgroup (kappa S) (W₁.subgroupOf S)`, `W₂=M_σ(S)⊓C(W₁)`)
- [ ] **step 2–4**: `typeP_duality S` → Mstar + covering + alignment (T=Mstar^g fixing W₂)
- [ ] **step 5**: Facts A/B(T) で `reconciled_typePData_T` の 2 sorry discharge
- 補助: `¬ IsConjugateSubgroup S T` (covering→T~Mstar 用)、`W ⊓ T' = W₁` (local)

## 完了条件

`reconciled_typePData_T` の `W2_le`/`centralizer_W1` sorry 解消、`lake build` 緑、AxiomsCheck OK、新 axiom なし。

## 参照

- issue 0098 (REACTIVATE パッケージ)、item 1
- Coq `coq/theories/PFsection8.v:229-746` (typeP_cent_compl / typeP_pair / FTtypeP_pair_witness / of_typeP_pair)
- Lean 既存機構: `S16_MainResults.lean:3090` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`)、
  `typeP_kstar_in_mf`、`typeP_centralizer_kappaElement_eq` (`S14_TypePCounting.lean:10847`)
- carve-out: `S15_SAndT_Setup.lean:4476` (`reconciled_typePData_T`)

## 🧭 HUB 注記 (2026-07-07 tick): S15_SAndT_Setup carve-out 範囲の明確化

c の kickoff commit `7b12a4f6` は b 所有 S15_SAndT_Setup.lean に additive helper
(`subgroup_le_of_normal_coprime_index_prime` 一般化版 + `Hypothesis.W1_le_derivedInG_T`) を追加した。
0098 の carve-out 文言は reconciled_typePData_T decl 領域 (:4520/:4590) 限定だったが、**hub 裁定 = 受理 +
範囲明確化**: carve-out は「reconciled_typePData_T の discharge に必要な supporting helper の *additive* 追加」
を含む (既存宣言の signature 改変は不可 — `pgroup_le_of_normal_coprime_index` は無傷と検証済み)。
b の active frontier (9013 案A §13 estimate) と非衝突。
