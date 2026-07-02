---
id: 26
slug: peterfalvi-clifford-core
title: "Peterfalvi Part I: Clifford decomposition の proof core を証明する"
created: 2026-05-26
---

# Peterfalvi Part I: Clifford decomposition の proof core を証明する

## 背景

`issues/0023-peterfalvi-clifford-decomposition.md` から分割した proof core。
`clifford_decomposition` の statement は Peterfalvi §3 (1.5)/(1.7) と BG §2 で
共有できる形に確認済みだが、証明本体は character-level induction/restriction
API がまだ不足している。

必要な層:

- `ClassFunction.restrict` と irreducible character inner product による constituent
  multiplicity API。
- `InducedCharacter` の numerical Frobenius reciprocity。
- `Res_H^G χ` の irreducible constituents が単一 `G`-orbit になる Clifford core。
- inertia subgroup `I_G(θ)` からの induction bijection ([Is] Thm 6.11)。
- cyclic inertia quotient の multiplicity-one specialization (Peterfalvi §3 (1.7))。

## やること

- [x] restriction inner product で constituent/multiplicity predicate を定義する。
- [x] `χ` irreducible なら restriction constituents are one `G`-orbit を statement 化する
      (`RestrictionConstituentsSingleOrbit` predicate)。
- [x] common multiplicity `e` を (single-orbit hypothesis から) 証明する
      (`hasCommonRestrictionMultiplicity_of_singleOrbit`, 2026-05-30)。
- [x] multiplicity `e = ⟨Res χ, θ⟩` の **整数性** (gap #5 の整数半分) を証明する
      (`restrictionMultiplicity_int`, 2026-05-30)。
- [x] multiplicity `e ≥ 0` (gap #5 の非負半分) を証明する
      (`restrictionMultiplicity_nonneg`, 2026-05-30)。BLOCKER B を経由せず, mathlib の
      Hom-次元公式 `card_inv_mul_sum_char_mul_char_eq_finrank` で
      `⟨Res^G_H χ, θ⟩ = dim_ℂ Hom_{ℂ[H]}(σ, ρ|_H) ≥ 0` を直接得た (isotype 分解不要)。
- [ ] orbit-sum decomposition (`Res χ = e · ∑ orbit`) を証明する — module 層待ち。
- [ ] `RestrictionConstituentsSingleOrbit` の hypothesis を外す (orbit transitivity 本体) — module 層待ち。

## 2026-05-26 update — sub-agent 調査結果 (6 件の API ギャップ)

1. **`IsIrreducibleCharacter` の module-theoretic provenance**: `ZIrr.lean` で
   `IsIrreducibleCharacter χ` は finite-dim irreducible `Representation ℂ G V` の存在を
   主張するのみで, 後で `V` / `Module (MonoidAlgebra ℂ G) V` / `Res^G_H V` の module
   分解で使う API が無い.
2. **`G`-action on `ℂ[H]`-summands of `Res V`** (semisimplicity bridge): mathlib
   `Maschke` はあるが「`Res V` の simple `ℂ[H]`-submodule は `G` で transitive に
   permute される」の statement / proof が無い. `Inertia.lean` は `ClassFunction ↥H ℂ`
   レベルにとどまり, 実 representation には届かない.
3. **`Irr H` の linear independence**: `θ_1, …, θ_t` distinct ⇒ `∑ c_i θ_i = 0 ⇒ c_i = 0`.
   mathlib `FDRep.char_orthonormal` 経由で出るが `ClassFunction`-level lemma が無い.
4. **numerical Frobenius reciprocity**: `InducedCharacter.lean` の `induce`/`induceSum`
   は定義済みだが `⟨induce H θ, χ⟩ = ⟨θ, restrict H χ⟩` の statement が無い.
5. **multiplicity ∈ ℤ⁺**: `restrictionMultiplicity` は `ℂ` 値. Clifford は `e : ℕ ∧ 0 < e`
   が必要. 「irreducible 同士の inner product は非負整数」の lemma が無い.
6. **signature に `[Finite G]` が無い**: `H` finite だけでは `[G : I_G(θ_0)]` 有限性が
   出ない. 実は `χ` irreducible で `Res V` 有限次元 ⇒ `H`-isotype は有限個, から `t : ℕ`
   抽出は可能だが finiteness 引数を明示する必要.

**結論**: sub-agent 判断は「multi-stage formalization task, not a single proof attempt」.
順番案: (1) `RepresentationOfIsIrreducibleCharacter` glue → (2) Maschke + isotype API →
(3) `G`-action on simple submodules → (4) orbit-stabilizer → (5) character計算 + 線形独立.
- [ ] inertia induction bijectionの statement を切る。
- [ ] `clifford_decomposition` に proof core を戻して `sorry` を消す。

## 2026-05-26 update

- `ClassFunction.restrictionMultiplicity H χ θ` を追加した。
- `ClassFunction.IsRestrictionConstituent H χ θ` を追加した。
- `IrreducibleCharacter.LiesOver H χ θ` を追加し、raw class-function
  constituent predicate への bridge を証明した。
- `IrreducibleCharacter.RestrictionConstituentsSingleOrbit` と
  `IrreducibleCharacter.HasCommonRestrictionMultiplicity` を predicate として追加した。
- `ClassFunction.inertiaQuotient θ = I_G(θ)/H` と
  `IrreducibleCharacter.HasCyclicInertiaQuotient` を追加し、§3 (1.7) の
  cyclic inertia quotient hypothesis を名前にした。
- `liesOver_iff_restrictionConstituent`,
  `RestrictionConstituentsSingleOrbit.exists_conj`, and
  `HasCommonRestrictionMultiplicity.eq_of_liesOver` を追加し、Clifford core
  の predicate 結論を unfold せずに使えるようにした。
- `ClassFunction.conjByEquiv`, `conjBy_restrict`, `innerSum_conjBy_conjBy`,
  and `inner_conjBy_conjBy` を追加し、normal subgroup 上の ambient conjugation を
  finite sum / inner product の permutation として扱えるようにした。
- `restrictionMultiplicity` の add/sub/neg/smul API と
  `restrictionMultiplicity_conjBy_right` を追加し、restriction constituent の
  nonzero multiplicity が ambient conjugation で保たれることを直接使えるようにした。
- `IsRestrictionConstituent.conjBy` を追加し、conjugate 側の irreducibility が
  supply されれば restriction constituent を transport できるようにした。
- `ClassFunction.conjByMulEquiv` を追加し、ambient conjugation を `H ≃* H`
  として使えるようにした。
- `Representation.IsIrreducible.comp_mulEquiv` と
  `ClassFunction.IsIrreducibleCharacter.conjBy` を追加し、`conjBy` が
  irreducible character を保つことを証明した。
- `IsRestrictionConstituent.conjBy` から conjugate 側 irreducibility 引数を消し、
  restriction constituent の orbit transport をそのまま使える形にした。
- `ClassFunction.conjBy_inv_conjBy` / `conjBy_conjBy_inv` と
  `IrreducibleCharacter.conjBy` を追加し、`Irr(H)` 上で ambient conjugation を
  直接使えるようにした。
- `liesOver_conjBy` / `liesOver_conjBy_iff` を追加し、`LiesOver` が
  `G`-conjugation orbit に沿って不変であることを theorem 化した。
- `IrreducibleCharacter.inertia`, `subgroup_le_inertia`, `inertiaQuotient`, and
  `conjBy_eq_conjBy_iff_mul_inv_mem_inertia` を追加し、`Irr(H)` 上の orbit
  representative equality を `g*h⁻¹ ∈ I_G(θ)` で扱えるようにした。
- `IrreducibleCharacter.conjByOrbit`,
  `conjByOrbitEquivRightCosets`, and `conjByOrbitEquivLeftCosets` を追加し、
  `θ` の `G`-orbit を `I_G(θ)` の coset quotient で parametrized できるようにした。
  次はこの同値から finite transversal / orbit sum の API を切る。
- 次の小単位は、restriction constituents が単一 orbit になる Clifford core
  theorem の statement/proof 入力、または inertia induction bijection の API 化。

## 2026-05-30 update — Frobenius 相互律 + common-multiplicity step を sorry-free 着地

### 着地した theorem (3 件, sorry/axiom 無し)

1. **`ClassFunction.inner_induce_eq_inner_restrict`** (`InducedCharacter.lean`):
   `⟨Ind_H^G θ, χ⟩_G = ⟨θ, Res_H^G χ⟩_H` ([Is] Lemma 5.2)。任意の部分群 `H` で成立
   (正規性不要)。補助: `sum_induceTerm_mul_star_eq` (x-slice の x 非依存性, χ class
   function による共役不変), `sum_induceTerm_one_mul_star_eq` (1-slice を `H` 上和へ収集),
   `sum_induceSum_mul_star_eq` (非正規化版 `∑ = |G| · ∑_{h∈H}`)。
2. **`ClassFunction.induce_conjBy_eq`** (+ `induceSum_conjBy_eq`) (`Clifford.lean`):
   Peterfalvi (1.5)(a) — `Ind_H^G (θ^g) = Ind_H^G θ` (`H ⊴ G`)。再添字 `x ↦ x·g` +
   normality の conj_mem。
3. **`IrreducibleCharacter.hasCommonRestrictionMultiplicity_of_singleOrbit`**
   (`Clifford.lean`): single-orbit ⇒ common multiplicity (Clifford 第 2 clause)。
   `restrictionMultiplicity_conjBy_right` で conjugate が multiplicity を保つことから。
   **注**: これは conditional scaffold ではなく Clifford の独立した clause の証明である
   (hypothesis `RestrictionConstituentsSingleOrbit` は結論 `HasCommonRestrictionMultiplicity`
   とは別の命題で, 含意自体に内容がある)。

### prior plan の誤りの訂正 (重要)

prior read-only plan は「character completeness (`span Irr H = CF(H)`) は未証明」を
blocker 4/5 として挙げていたが, **これは既に証明済み**である:
`CharacterCompleteness.lean` に
- `classFunction_eq_zero_of_orthogonal` (orthogonal ⇒ 0),
- `span_irreducibleCharacter_eq_top` (Irr が CF を張る),
- `card_irreducibleCharacter_eq` (`|Irr G| = |ConjClasses G|`),
さらに `ZIrrFourier.lean` に Fourier 係数 API (`mem_ZIrr_repr`, `inner_eq_coeff_of_repr`,
Parseval) が完備。したがって完成度の障壁は completeness ではなく **module 層** のみ。

### 残る唯一の hard blocker = module-theoretic Clifford core

orbit-sum decomposition と orbit transitivity (single-orbit hypothesis の除去) の双方が,
次の 1 つの module 層に帰着する:

> `IsIrreducibleCharacter χ` の証人 `ρ : Representation ℂ G V` (irreducible, f.d.) を取り,
> `Res^G_H ρ = ρ.comp H.subtype` を `H`-module として見たとき,
> (a) その指標が `restrict H χ` に一致し,
> (b) `Res ρ` は既約 `H`-部分加群の直和に分解し各 isotype が `G` で transitive に
>     permute される (Clifford の module 本体)。

(a) からは `restrictionMultiplicity H χ θ` が genuine character の係数 = **非負整数**で
あることが出る (現状 `ℂ` 値のまま; 整数性 lemma は未着地)。(b) からは single-orbit が出る。
mathlib は `Maschke`/`IsSemisimpleModule`/`sSup_simples_eq_top` を持つので (a) の指標一致と
isotype 抽出は手が届くが, **`G`-action による isotype の transitive permutation** は新規
module 開発が必要 (mathlib 未収録)。これは複数セッション規模で, 本セッションでは着手しない
(sorry や fake-scaffold を避け clean を優先)。

### 次の具体 step (順序案)

1. `Res^G_H ρ` の指標 = `restrict H (repCharacterClassFunction ρ)` の bridge lemma
   (`ρ.comp H.subtype` の character = `g ↦ ρ.character (g:G)`)。`Type 0` 制約は
   `CharacterCompleteness.transportRep` パターンで回避。
2. `restrict H χ ∈ ZIrr H` (genuine character) ⇒ `restrictionMultiplicity ∈ ℤ≥0`
   (Maschke 分解の係数; `Fourier` API で係数抽出後 module 側で非負整数性)。
3. `G`-action on simple `ℂ[H]`-submodules of `Res ρ.asModule` + orbit-stabilizer ⇒
   `RestrictionConstituentsSingleOrbit`。ここが新規 module 開発の本体。
4. 2+3 + completeness の Fourier 展開 ⇒ orbit-sum decomposition ⇒
   `clifford_decomposition` の tautological scaffold を実証明へ置換。

## 2026-05-30 update (2) — multiplicity 整数性を sorry-free 着地 + prior plan の重複指摘

### 着地した theorem (2 件, sorry/axiom 無し, `Clifford.lean`)

1. **`ClassFunction.restrictionMultiplicity_int`**:
   `χ ∈ ZIrr G → θ ∈ ZIrr H → ∃ m : ℤ, restrictionMultiplicity H χ θ = (m:ℂ)`。
   gap #5 (「multiplicity ∈ ℤ⁺」) の **整数半分**を解決。証明は既存 2 theorem の合成のみ:
   `restrict_mem_ZIrr` (`Res^G_H : ℤ[Irr G] → ℤ[Irr H]`, Peterfalvi (2.6.b)) で
   `restrict H χ ∈ ZIrr H` を得て, `inner_mem_ZIrr_int` (virtual character 同士の inner
   product は整数) を適用。仮説 (ZIrr 所属) と結論 (整数性) は別命題で含意自体に内容がある
   (tautology ではない)。
2. **`IrreducibleCharacter.restrictionMultiplicity_int`**: 上の既約指標版
   (`χ : IrreducibleCharacter G`, `θ : IrreducibleCharacter H`)。`.mem_ZIrr` 経由の特殊化。

両者とも `[Finite G]` を要する (`restrict_mem_ZIrr` の要件)。

### prior read-only plan の重複指摘 (重要)

prior plan は「Step 1 = `repCharacterClassFunction_comp_subtype`
(`repCharacterClassFunction (ρ.comp H.subtype) = restrict H (repCharacterClassFunction ρ)`)
を最初に着地せよ」と提案したが, **これは `InducedCharacter.lean` に既に
`restrict_repCharacterClassFunction` として存在する** (左右逆向きの等式だが内容同一)。
新規に書くと wrapper 規約違反。同様に prior plan の Step 2-4 (Maschke semisimple +
`restrict H χ ∈ ZIrr H` + 整数性) も `restrict_mem_ZIrr` / `inner_mem_ZIrr_int` で
**既に達成済み or 上記 1-2 で着地**。よって Phase 1 の残りは「**非負性のみ**」。

### 残る hard blocker = module-theoretic Clifford core (変わらず未着手)

`clifford_decomposition` の tautological scaffold (lines ~612-625) は **意図的に未置換**
(sorry-free だが偽の進捗; 結論 = 仮説の連言)。実証明への置換には次の 2 つが必須で,
いずれも mathlib 未収録の新規 module 開発 (見積り 3-5 セッション):

- **BLOCKER A (G-action on `ℂ[H]`-simples)** — ✅ **2026-05-30 着地** (下記 update 参照)。
  `H ⊴ G` のとき `N ↦ N.map (ρ g)` が `Res^G_H ρ.asModule` の simple `ℂ[H]`-submodule を
  simple `ℂ[H]`-submodule に送る。`N.map (ρ g)` 上の `ℂ[H]`-module 構造を normality
  (`h • (ρ g v) = ρ g (ρ (g⁻¹hg) v)`, `g⁻¹hg ∈ H`) で明示的に与える必要。
  `asModule` 型シノニムの instance 管理 (`set_option backward.isDefEq.respectTransparency
  false` 必須; issues/closed/0048 の gotcha 参照) が delicate。~50-80 行。
- **BLOCKER B (orbit transitivity)**: `ρ` が `G`-既約なら, simple `ℂ[H]`-submodule の
  `G`-orbit-sum は `ℂ[G]`-submodule ⇒ 既約性で `= ⊤`。`Submodule.linearEquiv_of_le_sSup`
  (Isotypic.lean) で任意の simple constituent が orbit 内の 1 つと `ℂ[H]`-linear 同型
  ⇒ single-orbit。submodule lattice 推論の glue が重い。~80 行。

**非負性 (gap #5 残り)** も BLOCKER B と同じ module 分解 (genuine character の Fourier
係数 = isotype 重複度 ≥ 0) に帰着するため, A/B 解決まで保留。

mathlib 確認済み相当 API: `IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top`,
`IsIsotypicOfType` / `isotypicComponent` (`RingTheory/SimpleModule/Isotypic.lean`),
`IsSimpleModule.congr`, `Submodule.equivMapOfInjective`,
`ofSubmodulePrime_isIrreducible` (本 repo `CharacterCompleteness.lean`)。
**欠落**: 「`H ⊴ G` で `ρ g` が simple `ℂ[H]`-submodule を simple `ℂ[H]`-submodule に
送る」(= BLOCKER A) — これだけは自前で書くしかない。

## 2026-05-30 update (3) — BLOCKER A (G-action on `ℂ[H]`-simples) を sorry-free 着地

`Clifford.lean` (namespace `OddOrder.RepresentationTheory.Representation`) に
module 層の片割れ **BLOCKER A** を実証明で着地 (sorry/axiom 無し, allowlist 3 axioms):

- **`isSimpleModule_map_conjBySimpleSemilinear`** (主定理): `ρ : Representation ℂ G V`,
  `H ⊴ G`, simple `ℂ[H]`-submodule `N` of `(restrictRep ρ H).asModule`, `g : G` のとき
  `N.map (conjBySimpleSemilinear ρ g)` は再び simple `ℂ[H]`-submodule。**ρ の既約性は不要**
  (より一般; 既約性は BLOCKER B の orbit transitivity でのみ必要)。
- 補助 (同ファイル):
  - `restrictRep ρ H : Representation ℂ ↥H V` = `ρ.comp H.subtype` の reducible abbrev
    (`.asModule`/`.asModuleEquiv` の dot 記法 + `Module ℂ[H]` instance 解決のため)。
  - `conjBySimpleRingHom g : ℂ[H] →+* ℂ[H]` = 共役 `h ↦ ghg⁻¹` 由来の環自己同型
    (`MonoidAlgebra.mapDomainRingHom` + `conjByMulEquiv`)。`RingHomSurjective` instance 付き。
  - `conjBySimpleSemilinear g : asModule →ₛₗ[conjBySimpleRingHom g] asModule` = `ρ g` を
    共役 twist に関する **semilinear** 写像として packaging。normality
    `ρ(h)(ρ g v)=ρ g(ρ(g⁻¹hg)v)` が semilinearity (`map_smul'`) の中身。
  - `conjBySimpleSemilinear_bijective` (= `ρ.apply_bijective g`),
    `mem_map_conjBySimpleSemilinear` (像は集合として `ρ g '' N`, 標準作用)。

証明の鍵: 「`IsSimpleModule R m ↔ IsAtom m` (`isSimpleModule_iff_isAtom`)」+ semilinear
全単射が誘導する **submodule lattice の order-iso** (`Submodule.orderIsoMapComapOfBijective`)
+ `OrderIso.isAtom_iff` で atom 性を transport。`IsSimpleModule.congr` は同環の linear equiv
専用で共役 twist (semilinear) には使えないため, atom 経由が正攻法。`asModule` 型シノニムの
instance/defeq 摩擦は `set_option backward.isDefEq.respectTransparency false` で解消。

**残るのは BLOCKER B (orbit transitivity, 既約性使用) のみ。** A は B の前提として再利用可能。
`AxiomsCheck.lean` に主定理を登録済 (all in allowlist)。

## 2026-05-30 update (4) — gap #5 非負半分を sorry-free 着地 (BLOCKER B 回避)

`Clifford.lean` (namespace `OddOrder.RepresentationTheory.ClassFunction`) に gap #5 の
**非負半分**を実証明で着地 (sorry/axiom 無し, allowlist 3 axioms)。**planner の sketch は
BLOCKER B (orbit transitivity) + Maschke isotype 分解経由を想定していたが, それは不要**だった:

- **`restrictionMultiplicity_eq_finrank_intertwiningMap`** (値の公式, 主補題):
  `χ = χ_ρ` (`ρ : Representation ℂ G V`, f.d.), `θ = χ_σ` (`σ : Representation ℂ ↥H W`, f.d.)
  のとき `⟨Res^G_H χ, θ⟩ = dim_ℂ Hom_{ℂ[H]}(σ, ρ|_H)` (= `finrank ℂ (IntertwiningMap σ (ρ.comp H.subtype))`)。
  これは multiplicity の module 論的同定そのもの (簡約 `σ` が genuine `H`-module `ρ|_H` に
  `Hom`-次元で何個入るか) であり, **gap #1 (multiplicity-as-inner-product) の核**でもある。
- **`restrictionMultiplicity_nonneg`** (非負性): 既約指標 `χ`, `θ` で `0 ≤ ⟨Res^G_H χ, θ⟩`。
  上の公式 + `Nat.cast_nonneg` (次元は cast された自然数) で即座。既約性は不要 (genuine
  character の証人だけ使う); irreducible 版を statement にしている。

**鍵**: mathlib `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`
(`Mathlib/RepresentationTheory/Character.lean`) が
`(Nat.card G)⁻¹ * ∑_g σ.char g * ρ.char g⁻¹ = finrank (IntertwiningMap ρ σ)` を与える。
これは `Representation` レベル (FDRep 不要 ⇒ universe 制約なし) かつ **既約性不要**で,
Schur ではなく `invariants` ↔ `IntertwiningMap` 同型 + 平均射影の trace で従う。
repo `inner` の `star(θ(h))` は `character_inv` (`CharacterConjugate.lean`,
`χ(g⁻¹) = star χ(g)`) で `σ.char h⁻¹` に直し, 上の公式に帰着。証明の骨格は G-side の
`RowOrthogonality.characterTableRowOrthogonality` と同型 (ただし `char_orthonormal` の
代わりに `card_inv_mul_sum_char_mul_char_eq_finrank` を使い, 0/1 でなく finrank ≥ 0)。

**残る module 層 = BLOCKER B (orbit transitivity, single-orbit hypothesis 除去) のみ。**
orbit-sum decomposition と `RestrictionConstituentsSingleOrbit` の hypothesis 除去は
依然 BLOCKER B 待ち (既約性使用, isotype の `G`-transitive permutation, mathlib 未収録)。
非負性は BLOCKER B に依存しないことが判明したので, これで gap #5 は完全に解決 (整数 + 非負)。

## 2026-05-30 update (5) — multiplicity ∈ ℕ (gap #5 を単一 theorem に統合)

整数半分 (`restrictionMultiplicity_int`) と非負半分 (`restrictionMultiplicity_nonneg`) を
**1 つの命題**に合成し, Clifford ([Is] Thm 6.5) が実際に消費する形
`⟨Res^G_H χ, θ⟩ = (k : ℂ)` (`k : ℕ`) を着地 (sorry/axiom 無し, allowlist 3 axioms)。これまで
gap #5 は「整数」と「非負」が**別仮説の 2 定理**(整数性は ZIrr 所属, 非負性は既約性)に
分かれており, 単一の自然数値ステートメントが欠けていた。既約指標は両方を供給する
(`.mem_ZIrr` で整数, 既約性で非負)ので合成可能。

- **`ClassFunction.restrictionMultiplicity_natCast`** (`Clifford.lean`):
  `[Finite G]`, `IsIrreducibleCharacter χ`, `IsIrreducibleCharacter θ` →
  `∃ k : ℕ, restrictionMultiplicity H χ θ = (k : ℂ)`。証明は `restrictionMultiplicity_int`
  + `restrictionMultiplicity_nonneg` の合成 (`0 ≤ (m:ℂ)` ⇒ `0 ≤ m` ⇒ `k = m.toNat`)。
- **`IrreducibleCharacter.restrictionMultiplicity_natCast`**: bundled 既約指標版。

これで gap #5 は文字通り完結 (ℕ 値として確定)。残る hard blocker は依然 BLOCKER B
(orbit transitivity) のみ。

## 完了条件

- `OddOrder.RepresentationTheory.clifford_decomposition` から `sorry` が消える、または
  上記の constituent/orbit/inertia-bijection lemmas が独立 theorem として statement 化される。
- `lake build OddOrder.GroupTheory.RepresentationTheory.Clifford` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0023-peterfalvi-clifford-decomposition.md`
- related: `issues/0021-peterfalvi-second-orthogonality.md`
- `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean`
- `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean`
- `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

issue 9002 (lane c claim, 2026-07-02) が本 issue を明示 subsume (9002 冒頭 L13)。旧 BLOCKER B (module core) は
`CliffordSingleOrbit.lean` で landed 済 — RepresentationTheory/Clifford*.lean 5 ファイルとも実 sorry 0 (検証 2026-07-02)。
残る一般ケースの追跡は 9002 側で行う。
