---
id: 1044
slug: pf-8-18-type-uniform
title: "(8.18) を型仮定なしの非共役 maximal ペアへ一般化"
created: 2026-07-20
---

# (8.18) を型仮定なしの非共役 maximal ペアへ一般化

issue 9163 §3 項目 2 の実体 (同 issue の 2026-07-20 追記で「cross_zero の導出化」部分は
既に済んでいると実測確定したので、残るのは本件のみ)。

## 書籍 (PDF p.49 で確定)

**(8.18)** S, T を**二つの非共役 maximal subgroup** とする (型仮定なし)。
- (a) T supports S ⟺ A₁(S) ∩ A(T) ≠ ∅。かつ x ∈ A₁(S) ∩ A(T) なら C_G(x) ⊄ S かつ C_G(x) ⊂ T。
- (b) T のある共役が S を support する ⟺ Ã₁(S) ∩ Ã(T) ≠ ∅。
- (c) Ã₁(S) ∩ Ã(T) = ∅ または Ã₁(T) ∩ Ã(S) = ∅。

(a) の証明: (8.13.b,c3) で ⟸。⟹ は x ∈ A₁(S) ∩ A(T) を取り、(8.17.a) で
「x の位数は |T_s| と互いに素、かつ x ∉ A₁(T)」。**A(T) − A₁(T) ≠ ∅ ゆえ T は Type I か II**。
位数が |T_s| と素なので (8.12.b) より T は C_G(x) を含む唯一の maximal。

## repo の現状 (2026-07-20 実測)

`OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` に 3 本、いずれも **TypeIData S/T 固定**:
- `escaping_supported_of_A1_conj_mem_typeIA` (:404) — (8.18.a) の conjugation-free core
- `exists_A1_conj_mem_typeIA_of_not_disjoint` (:481) — (8.18.b)
- `ftThickenedSupport_mixed_disjoint_of_nonconjugate` (:575) — (8.18.c)

## ✅ 済 (2026-07-20, commit da2a4ec25)

- **型一様な A(M)**: `OddOrder.GroupTheory.typeA M tau`
  (= `centralizerSupport (sharpSubgroup (mainSubgroup M tau)) (supportHost M tau)`、
  `supportHost` = M (Type I) / derivedInG M (それ以外))。
  橋渡し `typeA_eq_typeIA` / `S10.typeA_eq_typePACore` / `A1_subset_typeA`。
- **(8.18.a) の型判定ステップ**: `S10.isTypeI_or_isTypeII_of_mem_typeA_not_mem_A1`
  (x ∈ A(M), x ∉ A₁(M) ⟹ IsTypeI M ∨ IsTypeII M)。
  経路 = `typeA_eq_A1_of_isTypeP1` ((8.10) 末尾) → 対偶 → `proposition_type_classification`。

## ⛏ 残り: (8.12.b) の type-II 化がボトルネック

`escaping_supported_of_A1_conj_mem_typeIA` の型-I 依存を洗った結果、**本質的に効いているのは
1 箇所だけ**:

- `A1 S .I` → `x ∈ Msigma S` の変換 (`maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`) は
  **型一様版で置換可能** (`mainSubgroup_eq_Msigma` は全 5 型で成立)。
- σ-order bookkeeping (`sigma_disjoint_of_nonconjugate` + `primeFactors_Msigma_eq_sigma`) は
  もともと型仮定なし。
- **残る唯一の型-I 依存 = `typeI_centralizer_le_and_unique` (:183)**。この補題は
  `hκ : kappa T = ∅` (= Type I) を使って「位数が |T_F| と素」から
  「x は (κ∪σ)′-元」を導き、Isaacs Hall D/C で type-F 補元 U へ共役させている。
  **type II では kappa T ≠ ∅ なのでこの一歩が落ちる**。

書籍 (8.12) 自身は Type I **または II** で述べられており、
「Type I なら M = H ⋊ U、Type II なら [M,M] = H ⋊ U」と場合分けしたうえで X ⊆ U^# を要求する。
⟹ type-II 版は **`derivedInG T` の中で** 同じ Hall D/C 論法を回す
(x ∈ A(T) ⊆ T′ = H ⋊ U、位数が |H| = |T_σ| と素 ⟹ U へ共役) のが正しい経路。

### 使える型一様素材 (実測済)
- `BG.Ch4.S16.uniqueMaximal_of_kappaSigmaCompl_element`
  (S16_MainResults/TheoremsAE.lean:216) — 型仮定ゼロ。ただし入力が
  `IsPiElement (kappa M ∪ sigma M)ᶜ y` なので、上記の「(κ∪σ)′-元への格上げ」が要る。
- `BG.Ch4.S14.typeP_hall_small_subgroup_cyclic_tau2`
  (S14_TypePCounting/LocalStructure.lean:486) — 部分群版、型仮定ゼロ、
  `U` が `(κ∪σ)ᶜ`-Hall であることを仮定として取る。type-II の U はこれで供給できる可能性。
- `BG.Ch4.S15.typeP_hall_derived_eq_and_abelian` — type 𝒫 で `M' = U₀ ⊔ M_σ`。
- `S15.typeP2_exists_matched_kappa_hall_pair` — matched κ-Hall / (κ∪σ)′-Hall ペアの存在。

## 着手順

1. `typeII_centralizer_le_and_unique` (または型一様な `centralizer_le_and_unique`) を
   `derivedInG T` 内の Hall D/C で証明。
2. `escaping_supported_of_A1_conj_mem_typeIA` を `typeA` + `tau` パラメータ化して
   `escaping_supported_of_A1_conj_mem_typeA` に一般化 (旧名は消して consumer を貼り替え)。
3. (8.18.b) `exists_A1_conj_mem_typeIA_of_not_disjoint` を同様に一般化。
   `escaping_typeIA_mem_A1` (escaping ⟹ A₁) の型一様版が要る。
4. (8.18.c) `ftThickenedSupport_mixed_disjoint_of_nonconjugate` を一般化。
5. 一般化後、`S12.Hypothesis.cross_dade_inner_eq_zero_at_pair` (canonical pair 固定の
   (8.18.b) 適用) を一般版で置換できるか検討。

## 参照

- issue 9163 (hub 裁定 Option B′ + 2026-07-20 追記の実測記録)
- 書籍 PDF `references/peterfalvi/pdf/04.10_pp_44_49_*.pdf` p.5-6 (= 書籍 p.48-49)
- `notes/peterfalvi/frontier_measured_2026_07_19.md` §8
