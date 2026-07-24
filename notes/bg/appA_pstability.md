# BG App.A: Prerequisites and p-Stability — mini-roadmap

**スコープ**: BG Appendix A (pp. 135-138, 約 4 ページ), mmd L4450-4516, **5 結果 (Thm A.1-A.5)**.
形式化先 (予定): `OddOrder/BG/AppA_PStability.lean` (~300-530 行想定).
ROADMAP 上の位置: **Phase 2a 第 2 波** (Phase 1 Isaacs Ch.7 完成必須, §6 と並行 or 直後).
役割: **Isaacs Ch.7 と BG §6-§16 の橋渡し**; **p-stability 概念の正式定義**; **Thm A.4(b) ≡ Isaacs Thm 7.6 の odd-order 再述**.

## ✅ 2026-05-28 (late PM, 実装完了) — A.1 / dim reduction / A.2 sorry-free

[`OddOrder/BG/AppA_PStability.lean`](../../OddOrder/BG/AppA_PStability.lean) (~545 行)
に **A.1**, **A.2 dim reduction lemma** (`quadratic_two_generated_irreducible_finrank_eq_two`),
**A.2** (`thmA2`) を実装、すべて sorry-free / axiom-clean、`lake build` green。
issue [#0041](../../issues/closed/0041-bg-appa-a2-dim-reduction.md) クローズ。

実装ハイライト:
- **A.1**: `odd_two_dim_sylow_abelian` (BG Thm 2.6 = repo S02) + `Subgroup.Normal.of_commutator_le`
  + `IsPGroup.invariants_ne_bot` (= `PGroupFixedVector`) で C_V(P) ≠ ⊥, G-不変、既約 ⇒ P 自明、
  忠実より P = ⊥, `Sylow.ne_bot_of_dvd_card` と矛盾。
- **dim reduction**: Gorenstein 8.1 mmd L2210-L2240 の 5 step 翻訳。
  Step 4 を ★ **「eigenvector 1 個」** (= `Module.End.exists_eigenvalue` on
  `T := (Ty * Tx).restrict : V₂ →ₗ V₂`) に精密化し、Jordan canonical form の
  自前実装 (~200 行) を回避。
- **A.2**: dim reduction + `sub_pow_char_of_commute` で `(ρ x)^p = 1` から
  `orderOf x = p` を得て `p ∣ |G|`、A.1 と矛盾。Dickson 不要。

A.3 / A.4(a/b/c) / A.5 は別 issue で継続(下記表「未実装」を更新予定)。

## 🚧 2026-05-29 — A.3 進捗 (Step 1-3 完了 + 助補題、Step 4-8 = 残 sorry)

[`OddOrder/BG/AppA_PStability.lean`](../../OddOrder/BG/AppA_PStability.lean)
末尾 (~ L546-768) に **`IsPStable` def + `thmA3` statement + Step 1-3 (witness
extraction + Baer-Suzuki + y = gxg⁻¹ ∈ K 性質伝播)** を実装。issue
[#0043](../../issues/0043-bg-appa-a3-pstability.md) 進行中。残 = **Step 4-8
(合成列 + coprime action + p-group irreducible + A.2 適用)** = `h_two_dvd : 2 ∣ |G|` 1 sorry。

### 実装済 (commits `b8ab8a9`, `33bb1df`, `7b6158f`, `1921dec`)

1. **`IsPStable` 定義** (`b8ab8a9`):
   ```lean
   def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
     ∀ ⦃F : Type*⦄ [Field F] [CharP F p] [IsAlgClosed F]
       ⦃V : Type*⦄ [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
       (ρ : Representation F G V), Function.Injective ρ →
       ∀ x : G, IsPGroup p (Subgroup.zpowers x) →
         ((ρ x : Module.End F V) - 1) ^ 2 = 0 → ρ x = 1
   ```
   `O_p(G) = 1` / `p odd` は使う側 (A.3/A.4) で hypothesis として渡す方針。

2. **`thmA3` statement + Step 1-2** (`33bb1df`): `¬ IsPStable` ⇒ 証人取り出し、
   Baer-Suzuki (= repo `Isaacs.Ch02.baerSuzuki_pCore`) で `O_p(G) = ⊥` + `x ≠ 1`
   から `∃ g, ⟨x, gxg⁻¹⟩` 非 p-群。

3. **共役元 helpers** (`7b6158f`, AppA_PStability.lean L562-636):
   - `representation_conj_sub_one`: `ρ(gxg⁻¹) - 1 = ρg (ρx - 1) ρg⁻¹`
   - `representation_conj_quadratic`: `(ρx - 1)² = 0 ⇒ (ρ(gxg⁻¹) - 1)² = 0`
   - `representation_conj_ne_one`: `ρx ≠ 1 ⇒ ρ(gxg⁻¹) ≠ 1`
   - `isPGroup_zpowers_conj`: `IsPGroup p ⟨x⟩ ⇒ IsPGroup p ⟨gxg⁻¹⟩`
     (`SemiconjBy.orderOf_eq` + `IsPGroup.iff_card`)

4. **Step 3 (y ∈ K) + H setup** (`1921dec`): `y := g x g⁻¹` で
   `hysq, hyne, hyp` を helpers から取得、`H := closure {x, y}` 非 p-群
   (`hH_not_pgroup`) + `hxH`, `hyH` ∈ H 准備。残 = `h_two_dvd : 2 ∣ |G|` のみ。

5. **Step 5 用 single-step coprime action** (`96b447e`, 2026-05-29):
   新ファイル [`OddOrder/GroupTheory/RepresentationTheory/CoprimeActionTrivial.lean`](../../OddOrder/GroupTheory/RepresentationTheory/CoprimeActionTrivial.lean)
   (147 行, sorry-free) に `coprime_action_trivial_step` を実装。`G` 有限,
   `[NeZero (Nat.card G : F)]`, `W ≤ V` 上 + `V/W` 上自明 ⇒ `V` 全体に自明。
   証明は Maschke 不要の直接展開: `T := ρ g - 1` で `T² = 0`, 二項展開で
   `(1 + T)^(orderOf g) = 1 + (orderOf g) • T`, `(ρ g)^(orderOf g) = 1` と
   `(orderOf g : F) ≠ 0` から `T = 0`。次は chain (合成列) 版 で下降帰納。

6. **Step 5 chain 版 + relative step** (`0b8ff45`, 2026-05-29 PM, sorry-free):
   同ファイルに +138 行追加 (合計 ~285 行):
   - `coprime_action_trivial_relative_step`: `W ≤ U ≤ V` で `G` が `W` 上自明 +
     `U` 上で `ρ g u - u ∈ W` (= `U/W` 上自明) ⇒ `G` は `U` 上自明.
     Pointwise binomial `(1+T)^n u = u + n • T u` when `T (T u) = 0` 経由。
   - `coprime_action_trivial_chain`: chain `s : Fin (n+1) → Submodule F V`,
     `s 0 = ⊥`, `s last = ⊤`, 各 quotient 上自明 ⇒ `V` 全体自明。
     上向き帰納で relative step を反復適用。
   - これで A.3 Step 5 の **chain 適用部分は完備**。残課題は次節参照。

### ✅ 2026-05-29 evening: Step 5 chain + Step 6 Case A 完了 (`22e281d`)

mathlib JordanHolderLattice diamond を `Subrepresentation ρ_H` lattice 上で直接
`exists_covBy_seq_of_wellFoundedLT_wellFoundedGT` を呼ぶことで回避:

- `WellFoundedLT/GT (Subrepresentation ρ_H)` を `StrictMono.wellFoundedLT/GT`
  + `Subrepresentation.toSubmodule_injective` で取得.
- 得られた `a : ℕ → Subrepresentation ρ_H` を `(a i).toSubmodule : Submodule F V`
  で取り出す.
- Step 6 Case A (`∀ i 自明 ⇒ 矛盾`) を `coprime_action_trivial_chain` で実装
  (素因数分解 + Cauchy + Q := zpowers q + 自明性持ち上げで faithful 矛盾).

Case B (`∃ i, N_i ⊊ ↥H ⇒ A.2 適用 ⇒ 2 ∣ |H| ∣ |G|`) は次セッション (≈ 150-200 行)
で issue [`#0043`](../../issues/0043-bg-appa-a3-pstability.md) 「残 Case B」節
roadmap に沿って実装.

### ⛔ 2026-05-29 PM hard block: F[H]-module 合成列構築 (初期試行記録、回避済)

Step 5 の残り = 「`V` を `F[↥H]`-module 視 + H-invariant composition series」を
mathlib の `exists_compositionSeries_of_isNoetherian_isArtinian` 経由で取得を
試みたが、**Lean 4 typeclass diamond で詰まる**:

- `@JordanHolderModule.instJordanHolderLattice (Submodule R M)`
  (`Mathlib.RingTheory.SimpleModule.Basic:552`): `[Ring R]` から
  `Ring.toSemiring` 経由の `Module R M` を要求。
- `Module (MonoidAlgebra F G) ρ.asModule`
  (`Mathlib.RepresentationTheory.Basic:162`): `MonoidAlgebra.semiring`
  (独立宣言 `MonoidAlgebra/Defs.lean:612`) 経由の Module 構造。
- 両者が `defeq` でないため `Module` instance が unify せず
  `JordanHolderLattice (Submodule (MonoidAlgebra F G) ρ.asModule)` を
  `inferInstance` 取得不可。`letI`, 明示 instance 指定でも diamond 解消できず。

mathlib 全体検索でも `CompositionSeries (Submodule (MonoidAlgebra ...) _)` 使用例
ゼロ、`Subrepresentation ρ` に `JordanHolderLattice` instance なし、`restrictScalars`
経由で合成列移送パターンもなし。

#### 次に試すべき選択肢 (issue #0043 に記録)

1. **`Subrepresentation ρ_H` に直接 `JordanHolderLattice` 実装** ~80-150 行
   - Order iso `subrepresentationSubmoduleOrderIso` 経由で transfer。
2. **finrank-induction で composition series 手構築** ~150-200 行
   - `H-invariant W ≠ ⊥` ⇒ ∃ 極大 proper H-invariant W' ⊊ W で再帰。
3. **合成列経由しない直接論法** ~100-150 行
   - 「H 全 simple F[H]-subquotient 自明 ⇒ V 上自明」finrank induction 直接。

合計 Step 5 残 + Step 6-8 = **400-650 行**、本セッション継続不可。詳細
[`issues/0043-bg-appa-a3-pstability.md`](../../issues/0043-bg-appa-a3-pstability.md)
「🚧 2026-05-29 PM」節。

### 残 (Step 4-8 = Gorenstein 8.3 mmd L2293-L2298)

| Step | 内容 | 鍵新規補題 |
|---|---|---|
| 4 | V を `F[H]`-module 視 + H-invariant 合成列 `V = V_1 ⊋ V_2 ⊋ … ⊋ V_{m+1} = 0` | `RingTheory.SimpleModule` / `Order.JordanHolder.CompositionSeries` の Submodule-restricted 版 |
| 5 | 全 i で `N_i := ker(H → End(V_i/V_{i+1})) = H` 仮定 ⇒ H の p'-subgroup Q が全 quotient 上自明 ⇒ V 上自明 (Maschke + Jordan-Hölder) ⇒ ρ faithful と矛盾、∴ ∃ i, N_i ⊊ H | **coprime action** = Gorenstein Thm 3.4 翻訳: 単段 `coprime_action_trivial_step` ✅ (`96b447e`, 147 行, sorry-free); chain 版 (下降帰納で composition series 上で適用) TODO |
| 6 | その i で H̄ := H/N_i, ρ̄ faithful irreducible on V_i/V_{i+1}, H̄ = ⟨x̄, ȳ⟩ | quotient representation `H/N_i → End_F (V_i/V_{i+1})` (新規定義 or `Representation.quotient`) |
| 7 | x̄, ȳ ≠ 1: x̄ = 1 ⇒ H̄ = ⟨ȳ⟩ p-group, alg-closed char p faithful irreducible 不可能 (= Gorenstein Thm 1.2) ⇒ H̄ = 1 矛盾 | **p-group irreducible faithful → trivial** = Gorenstein Thm 1.2 帰結: `IsPGroup.faithful_irreducible_in_charP_trivial` (repo `PGroupFixedVector.invariants_ne_bot` 系) |
| 8 | A.2 (`thmA2`) を H̄ ↷ V_i/V_{i+1} に適用 ⇒ ¬ Odd \|H̄\| ⇒ 2 ∣ \|H̄\| ∣ \|H\| ∣ \|G\| | 既存 `thmA2` を呼ぶだけ |

### 工数見積

- Step 4 (composition series): mathlib `CompositionSeries` を Submodule lattice 上で具体化、~50-80 行 (mathlib 既存 API 探索 + 適用)
- Step 5 (coprime action): **単段は完了** (`96b447e`, 147 行, Maschke 不要の直接展開). 残 chain 版 (composition series 上の下降帰納) ~50-80 行。
- Step 6 (quotient rep): ~30-50 行
- Step 7 (p-group irreducible): `PGroupFixedVector.invariants_ne_bot` 系 + irreducible 仮定で短い、~30 行
- Step 8 (A.2 適用 + Lagrange): ~30-50 行

**合計目安**: ~300-400 行 (中規模 1 sub-issue ~~2-3 セッション分)。

## ⚠️ 2026-05-28 訂正: A.4(b)/(c) は Isaacs import では出ない(7.3 reduction が要る)

下記 TL;DR / 形式化戦略 (L78-90「選択肢1 推奨: Isaacs 7.6 import for A.4(b)」) は**過度に楽観的**。
判明事項:
- **Isaacs FGT は Glauberman Z(J)-定理 (= BG Thm 6.2) と Gorenstein §6.5/§3.8 を持たない** (Isaacs p.217 明記)。repo `normal_J` は Isaacs 7.6(`P=C_G(Z(P))` 付き特殊形)で、6.2 一般形でも A.4(b)/(c) でもない。
- **A.4(b)(= Thm 6.1)も A.4(c) も Gorenstein §6.5 の special case**で、BG App.A は証明本体を書かず "G §6.5 を A.3 で置換し we obtain" とするのみ(A.2/A.3 も "G §3.8 を辿れ")。⇒ **Isaacs import では出ない**。
- ただし**最深部(SL(2,p) = Dickson/G 3.8.1)は repo に既証**: `Isaacs.Ch07.gl2_pSubgroup_centralizes_of_normalizes`(Lem 7.3)。A.4(b)/(c) は **7.3 を核とする新規 reduction**(bounded)。A.4(c) は **Isaacs 7.5 の系ではない**(兄弟定理、共通核が 7.3)。A.2/A.3/A.4(a) は直接構築すれば**迂回可**。
- 詳細・依存閉包(App.B 完備、ゲート = A.4(b)+A.4(c))・J→L 大域置換の検証は
  [`notes/meta/log/bg_s6_appAB_route_2026_05_28.md`](../meta/bg_s6_appAB_route_2026_05_28.md)。

## ★ 2026-05-28 (late PM) 追補: A.2 = Gorenstein 8.1 翻訳, **Jordan form 不要**

### 背景の変化

References repo に Gorenstein 1968 _Finite Groups_ が追加された(`references/gorenstein/finite-groups.{pdf,mmd}`)。これで BG App.A が "follow the proof of Theorem 3.8.1 of **G**" と書くだけで省略していた A.2 の証明本体(= Gorenstein Ch.3 §8 Thm 8.1 = mmd L2204+ statement / **L2210–L2240 proof**)が直接読めるようになり、issue [#0041](../../issues/0041-bg-appa-a2-dim-reduction.md) が「証明の再構成」から「Gorenstein 原文の Lean 翻訳」に簡素化された。

### Gorenstein 8.1 (V dim=2) の 5 ステップ(精読、mmd L2210–L2240)

1. **rank-nullity**: `xᵢ` が char `p` 上 `p`-element + 二次最小多項式 ⇒ `Wᵢ := V(xᵢ−1) ⊆ Vᵢ = C_V(xᵢ)`, `d ≤ 2dᵢ`。
2. **`V₁ ∩ V₂ = 0`**: `dᵢ > d/2` 仮定 ⇒ `W := V₁ ∩ V₂ ≠ 0`、両 `xᵢ` は `W` 上自明 ⇒ `G = ⟨x₁, x₂⟩` も自明 ⇒ 既約より `V = W` ⇒ 忠実かつ `xᵢ ≠ 1` と矛盾。∴ `d₁ = d₂ = m`, `V = V₁ ⊕ V₂`。
3. **ブロック行列**: `vᵢ` を `V₂` 基底、`v_{m+i} := vᵢ(x₁−1) ∈ V₁` で `V₁` 基底。この基底で `x₁ = (I 0 / I I)`, `x₂ = (I R / 0 I)`, `R` 非特異(`x₂−1: V₁ → V₂` 同型)。
4. **Jordan + 置換共役**: `R` を Jordan form `S = Q⁻¹RQ` (`F` alg-closed)、`D = diag(Q,Q)` で共役 → `B₁ = A₁`, `B₂ = (I S / 0 I)`。`P` = 行 2, m+1 swap で再共役 → top-left 2×2 が `C₁ = (1 0 / 1 1)`, `C₂ = (1 λ / 0 1)` (`λ = S` の (1,1) 成分)。
5. **U=V**: `U = span(u₁, u₂)` が `x₁, x₂` 不変 ⇒ `G`-不変 ⇒ 既約 + `u₁ ≠ 0` ⇒ `U = V` ⇒ **`dim V = 2`**。∎

(Gorenstein は更に Dickson で `G ⊇ SL(2,p)` を出すが、**BG A.2 weakening (`|G|` 偶) には dim=2 で十分**、Dickson 不要。)

### Step 4 の数学的精読 = ★ Jordan form 不要の発見

mmd L2230–L2236 で実際に proof が使う情報を抽出すると、**「`S` が Jordan canonical form である」 という構造全体は不要**で、**`S` の最初の列が `(λ, 0, …, 0)ᵀ`**(つまり `e₁` が `S` の eigenvector)だけで議論が回る。

理由: Step 4 の置換共役後、`x₂ u₂` の `U = span(u₁, u₂)` 外への成分は `S` の最初の列の (2 行目以降) で支配される。これがゼロ ⇔ `S e₁ = λ e₁` ⇔ `R` の対応する元が eigenvector。

⇒ **Jordan form 全体を構成せず、`R` の eigenvector 1 個で足りる**。

### Clean argument(Jordan form を使わない版)

```
T := (x₂ - 1) ∘ (x₁ - 1) : V₂ → V₂        -- composition of two isomorphisms
  (x₁ - 1)|_{V₂} : V₂ → V₁ iso, (x₂ - 1)|_{V₁} : V₁ → V₂ iso
T 非特異, V₂ 有限次元 nontrivial, F alg-closed
⇒ ∃ v ∈ V₂ \ {0}, ∃ λ ∈ F \ {0}, T(v) = λ v

u₁ := v ∈ V₂                              -- nonzero eigenvector
u₂ := (x₁ - 1)(v) ∈ V₁                    -- in V₁ via the iso (x₁-1)|_{V₂}

U := span(u₁, u₂)
  - u₁, u₂ は線形独立 (V₁ ∩ V₂ = 0, u₁ ∈ V₂\0, u₂ ∈ V₁\0)
  - x₁ u₁ = u₁ + (x₁-1)(u₁) = u₁ + u₂        ∈ U  ✓
  - x₁ u₂ = u₂                  (u₂ ∈ V₁)    ∈ U  ✓
  - x₂ u₁ = u₁                  (u₁ ∈ V₂)    ∈ U  ✓
  - x₂ u₂ = u₂ + (x₂-1)(u₂) = u₂ + T(v) = u₂ + λ u₁  ∈ U  ✓

⇒ U は x₁, x₂ 不変 ⇒ G = ⟨x₁,x₂⟩ 不変 ⇒ G-submodule.
既約 + u₁ ≠ 0 ⇒ U = V ⇒ dim V = 2. ∎
```

### mathlib 調査結果(packaged Jordan form の有無)

調査済。mathlib 4.30-rc2 にあるのは:
- ✅ `Module.End.exists_eigenvalue [IsAlgClosed F] [FiniteDimensional F V] [Nontrivial V]` (`LinearAlgebra/Eigenspace/Triangularizable.lean:63-66`)
- ✅ `Module.End.iSup_maxGenEigenspace_eq_top [IsAlgClosed]` (同 L75-137) — generalized eigenspace で全体 span
- ✅ Jordan-Chevalley 分解 (`Module.End.exists_isNilpotent_isSemisimple`, `LinearAlgebra/JordanChevalley.lean:76-101`) — 半単純 + 冪零、unique
- ✅ permutation matrix / block matrix / swap (`LinearAlgebra/Matrix/{Permutation,Block,Swap}.lean`)
- ❌ **Jordan block 行列の明示構成 / Jordan canonical form 定理は無い**

⇒ 上記 clean argument を採用すれば必要なのは `exists_eigenvalue` だけ。**Jordan form 自前実装 (~150-250 行) は完全に不要**。

### 実装 impact(issue #0041 への反映)

| 元の見積もり | 修正版 |
|---|---|
| Step 4 = Jordan form 自前実装 ~200 行 | Step 4 = `exists_eigenvalue` + `T := (x₂-1)∘(x₁-1)` の eigenvector で基底変換 ~30-50 行 |
| 全体 ~530 行 (App.A 全体) | A.2 縮約補題部分が大幅短縮 |
| 最大リスク = Jordan form の packaged 形が無い | リスクなし(`exists_eigenvalue` で直接) |

### 必要な mathlib API(縮約補題、最小限)

```lean
-- Step 1: rank-nullity
LinearMap.range_le_ker_iff
LinearMap.finrank_range
Module.finrank_add_finrank_quotient  -- or rank-nullity in some form
LinearMap.finrank_range_add_finrank_ker

-- Step 2: irreducibility-driven contradiction
IsSimpleModule.eq_top_of_isInvariant  -- or its equivalent
Submodule.eq_bot_or_eq_top  -- in IsSimpleModule context

-- Step 3: basis construction
Module.Basis.ofVectorSpace / Basis.extend / Basis.append
Submodule.isCompl_of_direct_sum  -- or DirectSum.Decomposition

-- Step 4: eigenvalue + eigenvector
Module.End.exists_eigenvalue   -- alg-closed + finite-dim + nontrivial
Module.End.HasEigenvector  -- eigenvector definition

-- Step 5: invariant subspace + simple module → top
Submodule.eq_top_of_isSimpleModule_of_ne_bot  -- or similar
```

詳細は issue [#0041](../../issues/0041-bg-appa-a2-dim-reduction.md)。

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/log/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/bg_phase2a_wave1_audit_2026_05_23.md).

- **L13-14 "下流被引用 BG Thm 6.1, 6.2"** → **方向逆**. App.A は §6 の **上流**. BG 序文 L4452 "Theorems 6.1 and 6.2 ... are obtained by use of p-stability ... we outline these shorter proofs". 実装順序: BG §1+§2 → **App.A → §6** (並行ではなく §6 直前).
- **L24 "Isaacs Thm 3.8.1 weakening" / L25 "Isaacs Thm 3.8.3"** → **Isaacs FGT にこれらの番号は存在しない** (Gorenstein 1968 §3.8 番号). Isaacs では Thm 7.3 (GL(2,p)) + Thm 7.5 (normal-P) path で再構築.
- **L29-61 "A.4(b) ≡ Isaacs 7.6 論理同値"** → **同値ではなく系**. 仮定: 7.6 は P=C_G(Z(P)) + O_{p'}(G)=1 等, A.4(b) は P Sylow のみ. 結論: 7.6 = J(P)⊴G (specific), A.4(b) = abelian normal of S ⊆ O_{p',p}(G) (collection bound). **7.6 ⇒ A.4(b) trivial, 逆方向は J(P) ⊴ G の追加要**.
- **L194-203 "mathlib ~10%, Ch.7 import ~50%"** → 過大評価. Ch.7 import で得るのは **A.4(b) のみ (~30%)**. A.1-A.3, A.4(c), A.5 は **BG §1 + §2** 経由.
- **L207-213 前提 "Phase 1 Ch.7 + Isaacs 6.20/6.24 のみ"** → **+ BG §1 Prop 1.8/1.15(b) + BG §2 Thm 2.6 必須** (A.1 proof L4464, A.5 proof L4503/L4507).
- **`O_p`, `O_{p'}`, `O_{p',p}` mathlib 完全に不在**. 新規 `OpResidual.lean` ~150-250 行が App.A 必須前提.
- 実装コスト: shared module 込み **11-15 日** (既存「9-11 日」は shared module + BG §1/§2 dep 見落とし).
- A.4(b) は §7 でも L2275, L2291 cite (既存ノート未捕捉).

## TL;DR — Isaacs Ch.7 の奇数位数特殊化 + p-stability 正式定義

**App.A の本質**: Isaacs Ch.7 全体 (Thm 7.1, 7.3, 7.5, 7.6, 7.8, Lem 7.2, 7.4, 7.7) を **「奇数位数群」仮定下で再構築** し、同時に **p-stability という概念名を正式に導入**. Isaacs では「p-solvable + abelian Sylow-2 + O_{p'}=1 + P=C_G(Z(P))」が定理仮定として分散しているのに対し、BG App.A は「これらの条件群を満たす G を p-stable と呼ぶ」と命名.

**下流被引用**:
- **BG Thm 6.1** (L1971-1973): A.4(b) として再述
- **BG Thm 6.2** (L1975-1977): 奇数位数下で完全等価 (Isaacs Thm 7.6)
- **BG §8-§9 Uniqueness**: Thm 6.2 (≡ A.4 系) を **7+ 箇所で直接引用**
- **BG App.B Puig L(S)**: App.A Thm A.5 を前提 (L4666, L4735)
- **BG App.C CN-theorem**: L5014, L5030 で App.A 結果を援用

## App.A 全 5 結果

| # | 種別 | mmd 行 | statement 概要 | Isaacs 対応 | 主要仮定 | 結論 | 下流被引用 |
|---|------|--------|---------------|-------------|----------|------|------------|
| A.1 | Thm | 4460-4464 | p odd, V 2-dim vec space /F (char p), G ≤ GL(V) faithful irreducible, \|G\| odd ⇒ p ∤ \|G\| | Dickson 系 (Isaacs 2.8.4) | V 2-dim, G 既約, 奇数 | p ∤ \|G\| | A.2 で直接, Thm 7.5 周辺 |
| A.2 | Thm | 4468-4472 | p odd, G acts faithfully irreducibly on V (alg closure F_p), G generated by 2 p-elements with quadratic min poly ⇒ \|G\| even | **Isaacs Thm 3.8.1** weakening | p odd, irreducible, 2 p-生成 | \|G\| even | A.3 へ |
| A.3 | Thm | 4476 | p odd, G has no nontrivial p-subgroups, G is not p-stable ⇒ \|G\| even | **Isaacs Thm 3.8.3** | p odd, O_p=1, ¬p-stable | \|G\| even | A.4(a) 動機付け |
| **A.4** | Thm (3 部) | 4480-4485 | (a) O_p(G)=1, G solvable odd ⇒ G p-stable; (b) P Syl_p ⇒ every normal abelian sub of P ⊆ O_{p',p}(G); (c) generalized J-localization | **Isaacs Thm 7.6** (+ 7.5 + 3.21) | solvable odd | (a) p-stability def; (b) Thm 6.1; (c) localized | **BG Thm 6.1-6.2, §8-§9 (7+ 箇所)** |
| A.5 | Thm (2 部) | 4488-4513 | (1) `XC_G(P)/C_G(P) ⊆ O_p(G/C_G(P))`, (2) O_{p'}(G)=1 + C_{O_p(G)}(P) ⊆ P ⇒ X ⊆ O_p(G) (X = ⟨abelian p-groups normalized by P⟩) | **Isaacs Thm 7.6 系** (generalization) | solvable odd, P normal | (1) 相対化, (2) 絶対化 | **App.B (L4666, L4735)** 中核 |

## Thm A.4(b) ↔ Isaacs Thm 7.6 精密対応

### Isaacs Thm 7.6 (L3832)

```
G p-solvable, p ≠ 2, Sylow-2 abelian, O_{p'}(G)=1, P=C_G(Z(P))
⇒ J(P) ⊴ G
```

### BG App.A Thm A.4(b) (L4483)

```
G solvable odd, p odd, P ∈ Syl_p(G)
⇒ O_{p',p}(G) contains every abelian normal subgroup of P
```

### 仮定の対応

| Isaacs 7.6 | BG A.4(b) | 差 |
|------------|-----------|-----|
| G p-solvable | G solvable odd | odd ⇒ p-solvable (∀ p), Sylow-2 automatically abelian (no Sylow-2!) |
| p ≠ 2 | p odd | 同一 |
| Sylow-2 abelian | 自動 (odd order) | odd ⇒ O_2(G) = 1 |
| O_{p'}(G) = 1 | (省略) | A.4(a) で O_p(G)=1 のみ要求 |
| P = C_G(Z(P)) | (省略) | P は任意 Sylow p-sub |

### 結論の対応

| Isaacs 7.6 | BG A.4(b) | 関係 |
|------------|-----------|------|
| J(P) ⊴ G | 全 normal abelian ⊆ O_{p',p}(G) | **論理同値** (odd-order solvable 下) |

J(P) は P 内 maximal elementary abelian の生成. odd-order solvable で J(P) ⊴ G ⇔ Z(J(P)) ⊴ G (Phase 1 Ch.7 経由) ⇔ O_{p'}(G)·Z(J(P)) ⊴ G (BG Thm 6.2) ⇔ A.4(b) characterization.

### Phase 2a 形式化戦略

**選択肢 1 (推奨): Isaacs import**:
```lean
theorem thmA4b {G : Type*} [Group G] [Fintype G] [Odd #G] [IsSolvable G] 
    {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) (P : Sylow p G) 
    (A : Subgroup P.subgroup) (hA_normal : A.Normal) (hA_ab : A.IsCommutative) :
    A ≤ Subgroup.O_pp' p G := by
  -- Phase 1: Isaacs.Ch07.theoremJ_norm を import, odd-order specialization
  sorry
```

**選択肢 2 (代替): BG App.A 経由再構築**: Isaacs を参考にしつつ A.4 内で再証明. Phase 2a self-contained.

**推奨**: **選択肢 1**. Phase 1 Ch.7 完成直後 1-2 日で可能.

## p-stability 定義の設計

### BG/Isaacs での "p-stability"

**BG App.A 流 "G is p-stable"** (Thm A.3, A.4(a) から逆算):

```
G is p-stable :=
  G is p-solvable
  ∧ p ≠ 2
  ∧ Sylow 2-subgroup abelian
  ∧ O_{p'}(G) = 1
  ∧ ∃ P ∈ Syl_p(G), P = C_G(Z(P))
```

**Glauberman 1968** ([11] _A characteristic subgroup of a p-stable group_, CJM 20, 1101-1135): Glauberman 原始定義は **p ≠ 2 時の Thompson factorization の特殊形**. BG は odd-order specialization で簡略化.

### Lean 設計 (3 層構造)

```lean
def IsPSolvable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ n, (O_{p'}^∘n (G)) = ⊥

def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsPSolvable p G ∧ p ≠ 2 ∧ (∀ S ∈ Sylow 2 G, IsAbelian S) 
  ∧ (O_{p'} G : Subgroup G) = ⊥
  ∧ (∃ P ∈ Sylow p G, P = C_G (Z P))

def IsPStableOddOrder (p : ℕ) (G : Type*) [Group G] (hOdd : Odd #G) : Prop :=
  IsSolvable G ∧ p ≠ 2
  -- Sylow-2 abelian, O_{p'}(G)=1 等は odd-order で自動 or 仮定簡略化
```

**実装推奨**:
1. Phase 1 Ch.7 で `IsPStable` (Isaacs 流) を `OddOrder/Isaacs/Ch07/*.lean`
2. Phase 2a App.A で `IsPStableOddOrder` を `OddOrder/BG/AppA/*.lean` (wrapper)
3. BG §6-§16 で `IsPStableOddOrder` 版を多用

## Thm A.1, A.2, A.3, A.5 の役割

### A.1: GL(2,p) の p-subgroup irreducibility

- **役割**: Dickson 定理 (Isaacs 2.8.3-2.8.4) の corollary. 「2 次元既約表現で p-subgroup は自明」
- **使用**: A.2 proof, Isaacs 7.5 step 引数

### A.2: 2 生成 p-element irreducible → even order

- **役割**: Isaacs 3.8.1 (線形群表現論: 2 生成 p-elements の minimal polynomial 分析) の weakening
- **論理**: A.2 statement → Dim analysis (Isaacs 3.8.1) → A.1 → \|G\| even
- **使用**: A.3 セットアップ

### A.3: No p-subgroup ∧ Not p-stable → Even order

- **役割**: **p-stability の negative characterization**. 「p-stability 不在 ⇒ even order」の対偶
- **論理**: O_p(G)=1 ∧ ¬p-stable → A.2 + Isaacs 3.8.3 合成 → \|G\| even
- **対偶**: \|G\| odd ⇒ O_p(G) ≠ 1 or p-stable

### A.4(a): O_p(G)=1 for odd order → G is p-stable (definitional)

- **役割**: **p-stability 概念の introduction**. A.3 の対偶から「O_p=1 ∧ odd ⇒ p-stable」と命名

### A.4(c): Generalized J-localization for centralizer quotients

- **役割**: N_G(P)/C_G(P) での p-structure characterization. A.4(b) を N_G(P) に相対化
- **使用**: BG §8 (Fitting of Max), §9 (Uniqueness) の局所分析で各 maximal M と Sylow p の centralizer quotient 制御

### A.5: Generalized normal abelian generation → p-group localization

- **役割**: A.4(c) の「X = ⟨abelian p-groups⟩」拡張
- **結論**: (1) XC_G(P)/C_G(P) ⊆ O_p(G/C_G(P)) — 相対化, (2) O_{p'}(G)=1 ∧ C_{O_p(G)}(P) ⊆ P ⇒ X ⊆ O_p(G) — 絶対化
- **使用**: **BG App.B (Puig L(S)) の中核前提**. Puig L(G) は abelian p-group の再帰的 "hull" で、A.5 の X = ⟨abelian⟩ 構成が直結

## BG 本文での被引用 (完全リスト)

| BG 箇所 | App.A 結果 | 文脈 |
|---------|-----------|------|
| L1971-1977 Thm 6.1-6.2 | A.4(b), A.4(a) | p-stability + normal abelian containment |
| L2456, L2482 §8 (Fitting of Max) | A.4(b) via Thm 6.2 | Z(J(P)) normality 制御 |
| L2511, L2515 §9 (Uniqueness) | A.4(b) via Thm 6.2 | N_G(P) ⊆ N_G(Z(J(P))) (7+ 箇所) |
| L4374 §16 (Main Results) | A.5 (implicit via A.4) | Type 分類で maximal M の構造 |
| **L4666 App.B proof** | **A.5(2)** | **L(S) generation + X ⊆ O_p(G)** |
| **L4735 App.B Lem B.4** | **A.5(1)-(2)** | **Z(L(S))·O_{p'}(G) ⊴ G** |
| L5014, L5030 App.C (CN-theorem) | A.5 + Thm 6.2 | Sibley 論証で J(P) substitute |

## App.B Puig L(S) との関係

**BG 構造の二者択一**:
```
Isaacs Thm 7.6 (J(P) ⊴ G)
        ↓
BG Thm 6.2 (Z(J(S))·O_{p'}(G) ⊴ G) — odd-order specialization
        ↓
[BG §6-§16 全面で引用]
        ↓
[分岐]
├─ [Path 1] App.A → J(S) path (形式化簡):
│    Phase 2a で App.A ✓ → App.B optional or 不要
└─ [Path 2] App.B Lem B.1-B.5 → L(S) path (より general):
     App.A 前提 → App.B Thm B.4 が Thm 6.2 substitute
```

**推奨 (minimum viable form)**:
1. **Phase 2a で App.A 完全実装** (Isaacs 7.6 + odd-order specialization)
2. **App.B は optional** (Phase 2a 完了後):
   - L(S) は J(S) の weak 代替 (Lem B.1-B.5 の一般性)
   - BG 本文は J(S) path で完結可
   - App.B は「より一般的な代替」の技術記事的扱い

**実装量**:
- App.A: Isaacs 7.x の odd-order 版 → ~300-530 行 (Isaacs Ch.7 既存から大半 import)
- App.B: L_n, L_∞, L(G), L_*(G) 再帰 + Lem B.1-B.5 → ~300-400 行 (独立実装)

## mathlib カバレッジ評価 (Phase 1 Ch.7 完成下)

| 結果 | mathlib | Phase 1 Ch.7 | App.A 新規 | コスト |
|------|---------|--------------|------------|-------|
| A.1 | 0% | Isaacs 2.6-3.1 (Dickson), Thm 7.3-7.5 補題 | 30% (odd-order spec) | 短 (~20 行) |
| A.2 | 10% | **Isaacs 3.8.1 + Thm 7.3-7.5** | 20% (embedding) | 中 (~50 行) |
| A.3 | 0% | Isaacs 3.8.3 + A.2 + A.1 | 40% (p-stability negation) | 短 (~30 行) |
| **A.4(a)** | 0% | Isaacs 7.6 contrapositive | 70% (**def 導入**) | 中 (~40 行 + def 5 行) |
| **A.4(b)** | 10% (O_{p',p} API) | **Isaacs 7.6 odd-order spec** | 50% (reformulation) | 中 (~80 行) |
| A.4(c) | 5% (quotient API) | Isaacs 7.6 Step 5-6 | 60% (localization) | 大 (~120 行) |
| A.5(1)-(2) | 5% (normal subgroup) | Isaacs 7.6 (transitivity) | 70% (proof structure) | 大 (~140 行) |

**全体**: mathlib ~10%, Phase 1 Ch.7 import ~50%, App.A 新規 ~40%.

## Phase 2a 形式化着手順

| 段階 | 結果 | 行数 | 時間 | 前提 |
|------|------|------|------|------|
| 第 1 | A.1-A.3 | ~100 | 2-3 日 | Isaacs Ch.7 §7A-§7B |
| 第 2 | p-stability def | ~10 | 0.5 日 | A.3 |
| 第 3 | A.4(a)-(b)-(c) | ~280 | 4-5 日 | Isaacs 7.6 完全実装 + odd-order coercion |
| 第 4 | A.5 | ~140 | 2-3 日 | A.4(c) + O_{p',p} 算法 |
| **合計** | **A.1-A.5** | **~530** | **~9-11 日** | Phase 1 Ch.7 完成 + Isaacs 6.20, 6.24 完成 |

## Phase 2a 全体における App.A の位置

```
Phase 1 Isaacs Ch.7 完成
          ↓
[第 1 波] §1, §4, §5, App.B 並行スタート
          ↓
[第 2 波] §3, §6 開始
          ↓
[**App.A ここで開始**] ← Isaacs Ch.7 奇数位数 rephrasing + p-stability def
          ↓
BG §6 Thm 6.1-6.2 証明完了 (= Isaacs 7.6 系 + A.4(b))
          ↓
[第 3 波] §7-§9 Uniqueness (A.4(b) を 7 ヶ所引用)
          ↓
[第 4-5 波] §10-§16 Maximal Subgroup, Main Results
          ↓
[Phase 2a 終盤] App.A 完全 → App.B (optional)
          ↓
[Phase 2b] Peterfalvi §1-§16 (BG §6-§16 を指標論翻訳, App.A は implicit)
```

## CLAUDE.md `feedback_no_mathlib_wrapper` 整合

- A.1-A.3: thin wrapper (Isaacs 2.6-3.1 + Dickson 系) — odd-order specialization の追加で **書く価値あり**
- A.4(a): **def 導入** + Isaacs 7.6 contrapositive の翻訳 — **書く価値あり**
- A.4(b): Isaacs 7.6 の reformulation — **書く価値あり** (引数順 + odd-order specialization)
- A.4(c), A.5: 新規 proof structure — **完全新規**
- 純粋リネーム禁止: A.4 全体は new framework として独立形式化, A.1-A.3 は Isaacs 結果 + odd-order の context wrapper

## 未解決 / TODO

1. **p-stability の「minimal axiomatization」**: BG では仮定 minimum, odd-order で何が自動化するか精密化. Lean では `IsPStable` vs `IsPStableOddOrder` の分離 level 決定.
2. **Glauberman 1968 paper [11] 直接参照**: BG App.A は Glauberman を言及しない (Isaacs 経由). Phase 2a では Isaacs 7.6 を source of truth とする方針か.
3. **App.B Puig L(S) path の実装順序**: App.A 直後 or BG §6-§16 完了後. 推奨は後者 (J(S) path で本体完結後).
4. **A.4(b)-(c) の quotient group arithmetic**: N_G(P)/C_G(P) の modular 性質 careful handling. `Subgroup.quotient_lattice_isoQuotientMap` 等 API 活用.
5. **O_{p',p}(G) notation 統一**: BG 本文 `O_{p',p}`, Isaacs Ch.2 で `O_{p^\prime,p}` 表記差あり要確認.

---

**作成**: 2026-05-22. **出典**: `references/bg/local-analysis.mmd` L4450-4516, `references/isaacs/finite-group-theory.mmd` Ch.7 full, `notes/bg/_overview.md`, `notes/isaacs/ch07_thompson.md`. Phase 1 Isaacs Ch.7 ノートのクロス参照確認済.
