---
id: 9108
slug: augmentation-ideal-group-ring
title: "shared: Algebra/AugmentationIdeal.lean — Z[G] augmentation ideal API (lane c claim, Isaacs 10.19-10.23)"
created: 2026-07-17
---

# shared: OddOrder/Algebra/AugmentationIdeal.lean (lane c claim)

Isaacs §10C (10.18–10.28, principal ideal theorem / Alperin-Kuo) の基盤。
mathlib 未収載を確認済 (2026-07-17: `Mathlib/Algebra/MonoidAlgebra/*` に
augmentation 無し; `RingTheory/Ideal/IsAugmentation.lean` は無関係な一般概念)。
将来 mathlib upstream 候補 HIGH (ch10 note §5.4)。

## 設計 (2026-07-17)

- 群環 = `MonoidAlgebra ℤ G`。
- **δ (augmentation)**: `MonoidAlgebra.lift ℤ G ℤ` を trivial `G →* ℤ` に適用した
  `→ₐ[ℤ]` (または直接 `Finsupp.sum` の RingHom)。
- **Δ(G)**: δ の kernel を **`Submodule ℤ (MonoidAlgebra ℤ G)`** として持つ
  (Isaacs の議論は加法群+積閉包なので Ideal でなく Submodule ℤ が正解;
  非可換群環でも `Submodule.mul` (`Algebra/Algebra/Operations`) が
  `Δ(K)·Δ(G)`, `Δ(G)²` を与える)。
- **10.19**: `{g - 1 | 1 ≠ g}` が Δ(G) の ℤ-basis —
  `Finsupp.basisSingleOne` からの座標変換で `Basis ℤ`。
- **10.20**: `G ⧸ G' ≃+ Δ(G)/Δ(G)²` — 順方向 φ(g) = (g-1) + Δ²、
  逆方向は basis の universal property (`Basis.constr`) で θ(g-1) = G'g。
- **10.21-10.23**: t-成分分解 (`Finsupp` の fiber 分解 or transversal 和)、
  `Δ(K)² = Δ(K)Δ(G) ∩ ℤ[K]`、`Δ(K)/Δ(K)Δ(G) ≅ K/K'`。
- 消費者: Ch10 §10C leaf (`PrincipalIdeal.lean` 予定; 10.18/10.24/10.25 +
  10.26 可換環補題 + 10.27/10.28 Alperin-Kuo)。

## 進捗 (2026-07-17 lane c)

- ✅ δ (`augmentation`) + Δ (`augmentationIdeal`, ℤ-Submodule) + simp 補題
- ✅ **Lemma 10.19 完成**: `augmentationIdeal_eq_span` (spanning) +
  `linearIndependent_of_sub_one` + `augmentationIdealBasis` (ℤ-basis) +
  `augmentationIdealBasis_apply`
- ✅ **Thm 10.20 完成** (`abelianizationEquivAugmentationQuotient :
  Abelianization G ≃* Multiplicative (AugmentationQuotient G)`)。
  実装どおり: 商 = `↥Δ ⧸ augmentationIdealSq` (comap Δ.subtype)、
  順方向 `toAugmentationQuotient`、逆方向 `augmentationRetraction`
  (`Basis.constr`)、`θ(Δ²)=0` は制限 mulLeft/mulRight + `Basis.ext` +
  `Submodule.mul_induction_on'`。simp 補題で e (of g) = (g−1)+Δ² を pin。
  root `OddOrder.lean` に wire 済 (leaf は consumer 0 で full build 外だった)。
- ✅ **10.21 完成**: `augmentationIdealOf K` (Δ(K) ⊆ ℤ[G], span 定義) +
  `transversalComponent` (f_t, classical ite) / `transversalComponentSum`
  (f = ∑f_t) を `Basis.constr` + mathlib `Subgroup.IsComplement.equiv`
  (equiv_mul_left_of_mem / equiv_fst_eq_self / equiv_one) で構成。
  `transversalComponent_mem` (α_t ∈ Δ(K)) + `transversalComponentSum_mem_sq`
  (f(α) ∈ Δ(K)²)。生成元計算は Isaacs の 2 case が単一 ite 恒等式に統合。
- ✅ **10.22 完成**: `groupRingOf K` (ℤ[K] ⊆ ℤ[G]) +
  `augmentationIdealOf_sq_eq_inf_groupRingOf` / `_sq_eq_inf` (両形式)。
  f = id on ℤ[K] は ker(f − id) への span_le で無帰納。transversal は
  `Subgroup.exists_isComplement_right K 1`。
- ✅ **10.23 完成** (`abelianizationEquivAugmentationQuotientOf :
  Abelianization K ≃* Multiplicative (AugmentationQuotientOf G K)`)。
  mapDomain 橋は不採用 — Δ(K)bar = Δ(K)/(Δ(K)Δ(G) ∩ Δ(K)) (第二同型定理
  読み) とし、10.20 の議論を span 版 basis (`augmentationIdealOfBasis`)
  で replay。kernel 同定に 10.22 (`_sq_eq_inf`)。独立性は
  `LinearIndependent.comp` が coe-of-mk 爆発 (traps §7) するため
  coord functional 証明を複製。
- ✅ **Thm 10.24 完成** (2026-07-17, `PrincipalIdealTheorem.lean` sorry-free):
  核心恒等式 `transferXi_mk_sub_one` (Ξ((g-1)‾) = ι(θ(v g))) +
  range 同型 `transferRangeEquivXiRange` (v(G) ≅ Ξ(Δ(G)‾))。
  設計の鍵: σ = 左 transversal S の**逆元和** (`transversalInvSum`) に取る
  と Isaacs の右 transversal 因子 k_q = (S q)⁻¹·g·S(g⁻¹•q) が mathlib
  `Subgroup.leftTransversals.diff` の因子と一致し左右規約の橋渡し不要。
  Fintype (G⧸K) は mathlib diff と同じ `fintypeQuotientOfFiniteIndex` を
  letI で pin (statement には出さず def 内に封じる)。[Finite G] でなく
  [K.FiniteIndex] に一般化。Ξ(range) = {Ξ((g-1)‾)} は
  `exists_of_mem_transferXi_range` (span_induction; add/smul case は
  ψ∘v の hom 性で閉じる)。
- ✅ **Thm 10.26 完成** (`FiniteIndexAnnihilator.lean`, mathlib のみ import,
  sorry-free): 可換環 R・ideal U・加法 f.g. の A, U・[A:UA]=m 有限 →
  ∃r, rA=0 ∧ r≡m·1 mod U (adjugate det trick;
  `exists_smul_eq_zero_and_sub_card_mem`)。A/UA の巡回分解は
  `equiv_directSum_zmod_of_finite'`。
- ✅ **10.25 基盤: Δ(G)‾ の ℤ[G/K]-module 構造 + index 計算** (2026-07-17,
  `PrincipalIdealTheorem.lean`, sorry-free):
  - `augmentationCoquotientAlgHom : ℤ[G/K] →ₐ End_ℤ(Δ(G)‾)` (作用)
  - `augmentationCoquotientAlgHomG` (ℤ[G] 版) + `_apply` (= mulLeft) +
    `augmentationCoquotientAlgHom_mapDomain` (π:ℤ[G]→ℤ[G/K] 経由で Kg が g
    と同一作用) + `augmentation_mapDomain` (π は augmentation 保存)
  - `augmentationCoquotientModule` (compHom, letI 用; diamond 回避)
  - `augmentationCoquotientSqImage` = Δ(G)²‾ + `augmentationCorel_le_sq`
    (Δ(K)Δ(G) ⊆ Δ(G)²) + 第三同型 `augmentationCoquotientSqQuotientEquiv`
    (Δ(G)‾/Δ(G)²‾ ≃ Δ(G)/Δ(G)²) →
    `nat_card_quotient_augmentationCoquotientSqImage`: |Δ(G)‾:Δ(G)²‾| =
    |G:G'| (10.20 接続)。
- ⏭ 次 (10.25 詰め): (a) UA = Δ(G)²‾ の同定 (U=Δ(G/K) の像作用 = Δ(G)
  左乗法 → Δ(G)A = Δ(G)²‾)。これで [A:UA]=|G:G'| が確定し 10.26 適用可。
  (b) Lemma 10.27 (ε∈ℤ[G], εΔ(G)‾=0, δ(ε)=m ⇒ |G:K| | m ∧
  (m/|G:K|)Ξ=0; transversal 係数の e_t 一致論法)。(c) 10.25 本体
  (γ∈ℤ[G/K] を 10.26 で得 → ε=mapDomain 逆像で δ(ε)=|G:G'| → 10.27 →
  |K:G'|Ξ=0 → 10.24 で v(g)^{|K:G'|}=1)。その後 10.27/10.28 Alperin-Kuo。
  PrincipalIdealTheorem.lean は現 ~740 行 (2000 上限まで余裕)。
  **10.24 設計メモ (2026-07-17 調査)**: transfer は mathlib
  `MonoidHom.transfer` (repo Ch05_Transfer が既用; v : G →* K/K' は
  ϕ = Abelianization.of : K →* Abelianization K で transfer)。
  K ⊴ G で Δ(K)Δ(G) は left ideal (g·Δ(K) = Δ(K)·g) → Δ(G)bar =
  Δ(G)/Δ(K)Δ(G) に G-作用 (K は自明に作用) → Ξ = (∑_{t∈T} t)·-。
  **10.24**: v(G) ≅ Ξ(Δ(G)bar)、鍵は Ξ(g−1 bar) = V(g)−1 bar
  (∑t(g−1) = ∑(k_t−1)(t·g) ≡ ∑(k_t−1) mod Δ(K)Δ(G))。
  **10.26**: 可換環 R、ideal U、A f.g. R-module、[A : UA] = m →
  ∃r ≡ m·1 mod U, rA = 0 — `Matrix.adjugate_mul` (det trick) で自前証明
  (mathlib Nakayama 変種 `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`
  は m=1 特殊形のみ)。
  **10.25**: G' ≤ K ≤ G ⇒ v(g)^{|K:G'|} = 1 — R = ℤ[G/K] (可換!)、
  A = Δ(G)bar、U = Δ(G/K) の像で 10.26 を適用。
- Lean 注意 (10.19): `rw [MonoidAlgebra.smul_single']` は smul instance
  不一致で失敗 → exact defeq 経由; MonoidAlgebra ≠ Finsupp 型分離
  (Finsupp.* API 不可、`MonoidAlgebra.induction_linear` /
  `MonoidAlgebra.basis` を使う)。
- Lean 注意 (10.20): ① `Submodule.span_mul_span` は Algebra-section 宣言で
  `Algebra.toModule` 固定の rigid instance を持ち、Module-section の
  `Submodule.mul` instance と keyed matching 不成立 (rw/exact とも失敗) →
  span·span 展開を回避し `mul_induction_on'` (Module-section、instance が
  全部 binder) + 制限 mulLeft/mulRight + `Basis.ext` で任意元積を処理。
  ② `toAdd_zpow` の zsmul と商加群 smul (`Submodule.Quotient.instSMul'`) の
  不一致は `Int.cast_smul_eq_zsmul` でも埋まらず → `with_unfolding_all rfl`。
- Lean 注意 (10.22): subtype-indexed span の membership 補題は
  `{x : G} (hx : x ∈ K)` 形式必須 — `(k : ↥K)` 形式を匿名 mk に適用すると
  1 use site ~950k heartbeats (memory lean-instance-defeq-traps §7)。

## 完了条件

- AugmentationIdeal.lean: δ/Δ def + 10.19 + 10.20 sorry-free (10.21-10.23 も同 leaf か
  分量次第で sibling)。
