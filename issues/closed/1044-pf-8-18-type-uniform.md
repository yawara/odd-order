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

### 実測した最短経路 (2026-07-20): Hall 共役なしで (κ∪σ)′-元が出る

`uniqueMaximal_of_kappaSigmaCompl_element` の実際の入力は
`(hUM : U ≤ M) (hU : IsHallSubgroup (κ ∪ σ)ᶜ (U.subgroupOf M)) (hyM : y ∈ M) (hy1 : y ≠ 1)`
`(hyπ : IsPiElement (κ(M) ∪ σ(M))ᶜ y) (hyC : M_σ ⊓ C_G(y) ≠ ⊥)` で、
結論は `maximalSubgroupsContaining (C_G(y)) = {M}` (TheoremsAE.lean:216)。

type-I 版が Hall D/C を回しているのは「位数が |T_F| と素」から `hyπ` を作るためだが、
**type 𝒫 では x ∈ A(T) ⊆ T′ という所属だけで κ-側が落ちる**:

- p | orderOf x かつ x ∈ T′ ⟹ p | |T′|。
- (8.4.a) の Hall 互素性 `Nat.Coprime |T′| |W₁|` (= `typePData_W1_hall_coprime`、axiom-clean)
  より p ∤ |W₁|。W₁ は κ(T)-Hall なので p ∉ κ(T)。
- p ∉ σ(T) は「位数が |T_σ| と素」+ `primeFactors_Msigma_eq_sigma` から (型-I 版と同じ)。

⟹ **Hall D/C の再演は不要**。type-I 版が Hall を要したのは x ∈ T しか無いためで、
type 𝒫 では A(T) ⊆ T′ という (8.10) の host がそのまま効く。

## 着手順

### ✅ 1-2 完了 (2026-07-20)

1. **(8.12.b) の type-𝒫 半分** = `S10.typeP_centralizer_unique_of_mem_typePACore`
   (commit 4a7c0c6ce)。上記「Hall 共役不要」経路がそのまま通った。
1'. **(8.12.b) 型一様形** = `S10.centralizer_unique_of_mem_typeA` (commit b0b809817)。
   Type I → `typeI_centralizer_le_and_unique`、Type II--V → type-𝒫 半分 へ dispatch。
   κ-Hall 仮説は `tauT ≠ .I → ∀ data : TypePData T, ...` (Type I 分岐では未使用)。
2. **(8.18.a) core の型一様化** = `S10.escaping_supported_of_A1_conj_mem_typeA`
   (commit 2bc126ded)。旧 `..._typeIA` は一般版からの 6 行の導出に置換
   (signature 不変 ⟹ (8.18.c) 側の consumer 無変更)。

### ✅ 3-4 完了 (2026-07-20)

3. **(8.18.b)** = `exists_A1_conj_mem_typeA_of_not_disjoint` (commit 62f72468f)。
   併せて (8.17.c) `ftThickenedSupport_A1_disjoint_of_nonconjugate` と
   `ftThickenedSupport_A1_subset_conjClassSet_Mtilde` の Type I/II 制限も撤去
   (制限の由来は `A1_eq_sigmaSharp_of_typeI_or_II` 1 箇所だけで、全型版
   `A1_eq_sigmaSharp` を入れれば外れる)。型一様 (8.13.b) `escaping_typeA_mem_A1` と
   型一様 (8.13.c2) `coprime_FT_signalizer_centralizerIn_typeA` も新設。
4. **(8.18.c)** = `ftThickenedSupport_mixed_disjoint_of_nonconjugate_typeA`。
   経路上の型仮定も順に撤去:
   - `escaping_sigmaSharp_disjoint_centralizer` を **witness 形**
     (`..._of_witness`: `w ∈ S` + 「w が M_σ の非単位元と可換」) に一般化。
     旧形はその 2 行の系。これで type-I/type-𝒫 双方の Frobenius 吸収が 1 本に集約。
   - `escaping_sigma_disjoint_centralizer_typeA` / `supported_sigma_coprime_typeA` を新設。
   旧 Type-I 版はすべて一般版からの数行の導出に置換 (signature 不変)。

### ✅ 5 完了 (2026-07-20) — ただし「一般版で置換」ではなかった

**所有の確認**: `OddOrder/Peterfalvi/S*.lean` は **lane a territory** (2026-07-19 裁定 9154 で
c から移管、正本 = `lane_reallocation_2026_07_16.md` の表)。「lane b 寄り」という旧注記は誤り。

**実測した結論: `cross_dade_inner_eq_zero_at_pair` を型一様 (8.18.c) で置換するのは不可**。
(8.18.c) が与えるのは **選言** `Ã₁(S) ∩ Ã(T) = ∅ ∨ Ã₁(T) ∩ Ã(S) = ∅` だが、§12 が要るのは
**特定の向き** (`Ã₁(M) ∩ Ã(S) = ∅`、M = type P₁ / S = type II)。どちらの選言肢かを決めるのは
(8.18.c) の外の情報なので、§12 の証明は (8.18.c) より真に強いことを示している。
⟹ `Section16MaximalPairCore` 添字は**特殊化債務ではなく application の形**。

**代わりに実施した de-specialization** (これは本物の債務だった):

| 旧 | 新 | 落とした死荷重 |
|---|---|---|
| `typeP_pair_core_order_coprime` | **`typeP_core_order_coprime`** | `mp`/`data`/`hSW1`/`hSW2`/`hKstar`/`ha0` — **本体で 1 つも使われていなかった**。要るのは「S が M と非共役な maximal」だけ |
| `typeP_pair_escaping_centralizer_not_le_conj_partner` | **`typeP_escaping_centralizer_not_le_typeII`** | 同上。要るのは「S が type II」だけ |

canonical pair 側の呼び出しは各 1〜5 行の適用に縮んだ。⚠ 残る `mp` 添字の宣言
(`typeP_pair_base_bare_not_isConj` ほか 10 本、計 ~900 行) は `mp.S_typeP2` /
`mp.S_T_not_conj` / `mp.K`/`mp.Kstar` の整合を**実際に**使っているので、同様の棚卸しは
効果が小さい (次に触るときに再測すること)。

⟹ **issue 1044 は完了**。

## 参照

- issue 9163 (hub 裁定 Option B′ + 2026-07-20 追記の実測記録)
- 書籍 PDF `references/peterfalvi/pdf/04.10_pp_44_49_*.pdf` p.5-6 (= 書籍 p.48-49)
- `notes/peterfalvi/frontier_measured_2026_07_19.md` §8
