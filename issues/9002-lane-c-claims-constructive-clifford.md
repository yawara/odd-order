---
id: 9002
slug: lane-c-claims-constructive-clifford
title: "lane c claims 構成的 Clifford (issue 0026 subsume): typeI_induced_char_constituents 一般ケース"
created: 2026-07-02
---

# lane c claims 構成的 Clifford (issue 0026 subsume): typeI_induced_char_constituents 一般ケース

> **CLAIM (lane c=γ, hub 再裁定 issue 9001 2026-07-02)**: 構成的 Clifford correspondence
> (Ind_H^L θ の構成要素分解 = Isaacs 6.2/6.11 + Pf 1.7) を lane c が build。**coherence 非依存の
> generic char 補題**。consumer = lane b (12.14 M-side) + lane c (deep char) の両方 = shared infra。
> **他レーンは着手前に本 issue を scan、cite (再構築しない)**。issue 0026 を subsume。

## 現状 (2026-07-02 精査、issue 0026 は 2026-05-30 更新で stale)

**⚠ 重要: 一般 module-core (BLOCKER B) は既に landing 済**。issue 0026 が「残る唯一の hard blocker =
module-theoretic Clifford core (orbit transitivity)、3-5 セッション」としたものは**その後 sorry-free 化**:
- `CliffordSingleOrbit.lean:122` `restrictionConstituentsSingleOrbit_of_isIrreducible` — Clifford
  (Isaacs 6.5) 第1節「Res^G_H χ の既約構成要素は単一 G-orbit」= **sorry-free landed**。
- 同 `:175` `apply_one_eq_restrictionMultiplicity_mul_index_inertia` — degree formula
  `χ(1)=⟨Res χ,θ₀⟩·[G:I]·θ₀(1)` = landed。
- `InducedIrreducible.lean`: `card_mul_inner_self_induce_eq_card_inertia` (⟨Ind θ,Ind θ⟩=[I:H])、
  `card_conjByOrbit_eq_index_inertia`、`induce_eq_induce_iff_conj`、`inner_induce_eq_zero_of_not_conj`
  = induction-side Clifford (Frobenius 相互律 + inertia orbit) landed。
- `CliffordMultiplicityOne.lean`: `restriction_isSimpleModule` (BG 2.2(a) mult-one) + conj semilinear
  端末 landed。**全 Clifford*.lean = 0 sorry**。

**∴ hub の「構成的 producer なし」前提は stale。** 一般 Clifford 核は在庫。残 gap は **assembly**。

## 残 gap = `typeI_induced_char_constituents` (S14_MaximalI.lean:389, sorry S14:398) 一般ケース

- **Frobenius ケースは proven**: `frobenius_typeI_induced_char_constituents` (S14:465, sorry-free) —
  L が Frobenius (kernel H) なら Ind_H^L θ は既約 → singleton {χ}。docstring 明記「(12.16) witness-side
  R(χ)/(12.3)/(12.4) が実消費するのは Frobenius ケース」。witness L は Frobenius ゆえこちらで足りる。
- **一般ケース (sorried)**: 一般 type-I maximal L で χ=Ind_H^L θ (θ∈Irr H∖{1}) が **等次数・非実・
  A(L)∪{1} 台の既約構成要素の mult-one 和**。body = §8 type-F Clifford:
  - Pf (1.7) **cyclic inertia quotient I_L(θ)/H → mult-one 等次数 Ind 分解** (核心、要精査で
    landed 有無確認)。
  - (8.2.c) `I(θ)∩U⊆U₁` inertia bound (§8 specific)。
  - (1.5.a) `(Res_H φ,1_H)=0` + (1.2) → 台 A(L)∪{1}。
  - 非実 = 奇数位数 (`not_isReal_of_ne_trivial_of_odd_card'` 既存)。

## 精査確定 (2026-07-02): landed vs missing の正確な境界

**landed (在庫、cite 可)**:
- `CliffordSingleOrbit.restrictionConstituentsSingleOrbit_of_isIrreducible` (Res χ 構成要素=単一 orbit)。
- `InducedIrreducible.isIrreducibleCharacter_induce_of_inertia_eq` ([Is] 6.34: I(θ)=H → Ind θ 既約)。
- `InducedIrreducible.card_mul_inner_self_induce_eq_card_inertia` (⟨Ind θ,Ind θ⟩=[I:H])。
- `InducedIrreducible.{sum_div_normSq_induce_image_eq, apply_one_eq_sum_restrictionMultiplicity_mul,
  card_filter_induce_eq_index_inertia}` (Pf (6.2) orbit-count/degree apparatus)。
- `S14.typeF_inertia_inf_le_U1` (8.2.c: I(θ)∩U⊆U₁, proven)。`frobenius_induce_char_singleton` (Frobenius 既約)。

**missing (generic char、要 build — Isaacs §6/§11、repo 未収録)**:
- **(G1) 指標拡張**: θ∈Irr H を I=I_L(θ) に拡張 (I/H cyclic ⟹ 拡張存在、[Is] 6.28/11.22 coprime 版)。
- **(G2) Gallagher** ([Is] 6.17): θ が I 上拡張 θ̃ を持てば Irr(I|θ)={θ̃·β: β∈Irr(I/H)}、⟨Res_H(θ̃β),θ⟩=β(1)。
- **(G3) mult-free 判定**: I/H **abelian** ⟹ Ind_H^L θ は multiplicity-free、構成要素は [I:H] 個・全て
  等次数 [L:I]·θ(1) (Clifford correspondence [Is] 6.11 で Irr(I|θ)↔Irr(L|θ) + G2 で β(1)=1)。

## 進捗 (2026-07-02)

- [x] **慣性商 abelian 前提の中核**: `S14.typeF_inertia_inf_U_isMulCommutative` (generic, sorry-free,
      commit `e6f0dbd9`) — (8.2.c) + `U₁` abelian ⟹ `I(θ)∩U` abelian。残 = Dedekind `I(θ)=H·(I(θ)∩U)`
      で `I(θ)/H` abelian を完成 (要 Γ=HU / H≤I(θ)≤HU)。
- 一時中断 (2026-07-02, lane D 退役で区切り)。次セッション再開点 = 下記 (G1) 拡張から。

## Coq-confirmed 経路 + missing pieces の精密化 (2026-07-02, cont.²)

Coq PFsection1 (1.7) の経路を確認 (`constt_Inertia_bijection` + `cfIndInd`)。一般ケースの proof は:
1. **induction-in-stages** `Ind_H^L θ = Ind_I^L (Ind_H^I θ)` (Coq `cfIndInd`)。**Lean 未実装**:
   `ClassFunction.induce (H : Subgroup G)` は **ambient G へのみ**誘導 (中間 I への stage なし)。
   → `induce I (induce (H.subgroupOf I) θ') = induce H θ` を build (coset 二重和の再添字、要 subgroupOf iso)。
2. **Clifford correspondence 全単射** `Ind_I^L : Irr(I|θ) ≃ Irr(L|θ)` (Isaacs 6.11)。**Lean は degree 形のみ landed**
   (`CliffordSingleOrbit.lean:222-360`)、全単射本体は未。
3. **local mult-free at I**: I 上で θ-invariant のとき `Ind_H^I θ` の mult-free ⟹ Gallagher (Isaacs 6.17)
   + 拡張 (Isaacs 6.28/11.22)。**両方 Lean 未実装**。

**✅ 設計点 解決 (Coq PFsection1.v:437-523 精読、2026-07-02)**: **abelian で十分、cyclic 不要**。
Coq (1.7)(b) `cfInd_central_Inertia` の hypothesis は `abelian (T/H)` (T=I(θ))。結論:
- ∃ e∈ℕ (e≠0)、`∀t∈calA, e_t = e` (全構成要素が**一様 multiplicity e**)。
- `Ind_G θ = e · ∑_{j∈calB} χ_j` (distinct 構成要素の e 倍和)。
- `|calB| = [T:H]/e²`、**`∀i∈calB, χ_i(1) = [G:T]·e·θ(1)`** (全**等次数**)。
- 機構: T/H abelian → `Irr(T/H)` は linear chars → `LtoT j = (χ_j %% H)·psi1` が calA を parametrize
  (Gallagher 型)、`Res_H psi1 = e·θ` (Clifford)。

**∴ 私の `typeF_inertia_inf_U_isMulCommutative` (I(θ)/H abelian) が (1.7)(b) hypothesis そのもの、正しく on-route。**
**mult-one (e=1)** は θ が T へ**拡張**するとき: type-I では `H=L_F` が Hall で `[T:H]` coprime `|H|`
⟹ coprime 拡張 (Isaacs 6.28/8.16) で θ 拡張 → e=1。equal-degree/non-real/台と合わせ typeI_induced_char_constituents。

## やること (bottom-up、generic は shared leaf)

- [ ] **Pf (1.7)/(8.2.c) 原文精読** — mult-one/equal-degree の正確な機構 (cyclic 要否) を確定。
- [ ] **induction-in-stages** `induce I (induce (H.subgroupOf I) θ) = induce H θ` を build (foundational)。
- [ ] **慣性商 abelian 完成**: Dedekind `I(θ)=H·(I(θ)∩U)` + `I(θ)/H ≃ I(θ)∩U` abelian (`sup_inf_assoc_of_le`)。
- [ ] **(G1) 拡張 lemma** を build (`OddOrder/GroupTheory/RepresentationTheory/` 新/既存 leaf)。coprime
      Hall (H=L_F normal Hall, U abelian complement) の下で I/H cyclic → θ 拡張。
- [ ] **(G2) Gallagher** + **(G3) mult-free-from-abelian-inertia** を build (同 leaf)。core generic 補題。
- [ ] **type-F 適用**: (8.2.c) I(θ)∩U⊆U₁⊆U(abelian) ⟹ I(θ)/H abelian → (G3) 適用。
- [ ] **(1.5.a)/(1.2) 台**: 各構成要素 φ の台 ⊆ A(L)∪{1}。非実 = 奇数位数 (`not_isReal_of_ne_trivial_of_odd_card'`)。
- [ ] `typeI_induced_char_constituents` (S14:398) を上記 cite で sorry-free 化。lane b (12.14) は cite。

**性質**: genuine multi-session char build (G1-G3 は Isaacs §6/§11 の generic char theory で repo 未収録)。
Frobenius sub-case は proven ゆえ witness (12.16) 経路は現状も通る; 本 issue は一般 (12.14) 用の shared infra。

## 完了条件

`typeI_induced_char_constituents` (S14:398) sorry-free、`lake build` 緑。generic Clifford 部が shared leaf
で lane b から cite 可能な signature。

## 参照

- 親 issue: 0026 (peterfalvi-clifford-core、subsume)、0023 (clifford-decomposition)
- hub 再裁定: issue 9001「HUB 再裁定 (2026-07-02) — σ-theory-dual 撤回 + lane c に構成的 Clifford 再配分」
- landed 核: `CliffordSingleOrbit.lean` / `InducedIrreducible.lean` / `CliffordMultiplicityOne.lean` /
  `Clifford.lean` / `Inertia.lean`
- consumer: `S14_MaximalI.lean:389` (lane c) / Pf (12.14) M-side (lane b)
- Pf 原文: 03 §3 (1.5)/(1.7)、04.8 §8 (8.2.c)
