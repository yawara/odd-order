# Peterfalvi §6: The Dade Isometry for a Certain Type of Subgroup — mini-roadmap

**スコープ**: Peterfalvi §6 (pp. 21-24), mmd `04.6_pp_21_24_*.mmd` (108 行), **10 結果 ((4.1)-(4.10))** ⚠️ audit 訂正 (旧 5 結果は (4.6) Hypothesis [実は中核], (4.7) Supp, (4.8), (4.9) τ-isometry, (4.10) 4-term identity 完全欠落).
形式化先 (予定): `OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean`.
ROADMAP 上の位置: **Phase 2b 第 2 波後半** (§4-§5 完成後).
役割: **§4 Dade isometry の Frobenius と特定 subgroup type への拡張**, §7 Coherence への中間ステップ.

---

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **L3 "5 結果 (4.1)-(4.5)"** → **重大誤認: 実際 10 結果 (4.1)-(4.10)**. 既存表で (4.6) Hypothesis (実は中核), (4.7) Supp 補題, (4.8), (4.9) τ-isometry Thm, (4.10) 4-term identity が完全欠落.
- **(4.1) orthogonality crit は下流 9 cite (技術 hub)**, (4.3) も 9 cite, **(4.7) Supp は 7 cite (§7 (5.3.b) proof で重要)**. 既存「(4.5) main thm」評価不十分.
- **L12 TL;DR "§4 の応用・拡張"** → 実は **§5 への依存が遥かに重い**: §5 (3.X) cite **8 件** (3.1×3, 3.2×5, 3.3×2, 3.4, 3.6, 3.8, 3.9×3) vs §4 (2.X) cite **3 件のみ**. §6 = "§5 σ を §6 (4.6) で embed + §4 Dade τ で L→G lift".
- **L14 "mathlib ~30%"** → "20%; Brauer permutation 最大 gap".
- **L60 (4.2.a) "W₁ は K の cyclic Hall subgroup"** → **正は "W₁ は L の cyclic Hall subgroup"** (L9 mmd: Hall of L). K (= L^p′) でない.
- **L181 (4.5.b) "Phase 1 Ch.指標論で fixed point theory 確認"** → **Brauer's permutation lemma ([Is] Thm 6.32) は mathlib v4.29.1 不在 (grep 0 hits); Phase 1 計画にも無し**. 新規 `OddOrder/RepresentationTheory/BrauerPermutation.lean` 要 — **§6 (4.5.b) の単一最大 blocker**.
- **L213 "§5 と独立"** → **誤り (8 §5 cites)**.
- L218-237 §7 bridge "(4.3.d), (4.5)/(4.4) → (5.6) norm bound" → 正は **(5.3.b) は (4.7)+(4.9) を経由** ((4.7) が API edge).
- §10 への §6 cite は **0** (note implied §10-§16 多出現は overstate). 最大消費は §12 (13 cites), §7 (11), §15 (11), §11 (7).
- 行数 "13-16h" → **18-22h realistic** ((4.5.b) Brauer 4-6h + 既存 (4.1)-(4.5) 想定の約 2 倍).

## TL;DR — §4 の応用・拡張, 新概念なし

**§6 の位置づけ**: §4 (2.1)-(2.6) で Dade isometry の一般理論を確立した後、**Hypothesis (4.2) という特定の algebraic structure** (L = K ⋊ W₁, cyclic Hall subgroup W₁, centralizer factorization) を持つ部分群族に対し、Dade isometry がどのように **具体的に構成・計算** されるかを詳細化. 新しい概念は不要で、§4 の結果を組み合わせる.

**mathlib カバレッジ**: ~30% (§4 同様の補助 lemma は部分カバー). 主定理 (4.3)-(4.5) は **§4 (2.6) の直接応用** で、新規設計判断は最小.

**§7 Coherence への役割**: (4.3)-(4.5) で構築した `μ_{ij}` 族と `χ_j` 族が、§7 で **coherent triple** を形成するための前提知識として機能. §7 (5.2)-(5.6) は本 §6 の character family を対象に Coherence を定義・検証する.

---

## Lean status (2026-05-26)

`OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean` は §4 interface を二段階で再利用する:

- `CertainTypeHypothesis.DadeApplication`: 係数 `k` に parametric な `S04.DadeIsometryData` を持ち、pointwise Dade-map equations と inner-product preservation を §6 carrier に載せる。
- `CertainTypeHypothesis.FullDadeApplication`: `k = ℂ` の `S04.FullDadeIsometryData` を持ち、virtual-character preservation も §6 側から `full_maps_virtualCharacter` で参照できる。
- `map_eq_of_mem_hCoset` / `full_map_eq_of_mem_hCoset`: §4 (2.5) の
  `aH(a)` 上の値指定を §6 carrier から直接使う。
- `map_eq_zero_of_not_mem_dadeSupport` /
  `full_map_eq_zero_of_not_mem_dadeSupport`: §4 Dade support の外で値が 0
  になることを §6 carrier から直接使う。

## §6 全 10 結果 (表) ⚠️ audit 訂正 (旧表「5 結果」は (4.6)-(4.10) 完全欠落)

| # | 行数 | 種別 | statement 概要 | 役割 | §7-§16 被引用 |
|---|-------|------|-----------------|------|-------------|
| **(4.1)** | 5-7 | **Lemma** | Orthogonality criterion: inner product + degree condition から character orthogonality | **技術 hub** | **9 cite** (§7×2, §12, §14, §15, §16) |
| **(4.2)** | 9-13 | **Hypothesis** | Hypothesis (4.2): L = K ⋊ W₁, W₁ cyclic Hall, C_K(x) = W₂ ∀x ∈ W₁^#, W₁ × W₂ odd | **核心 setup** (Frobenius 型) | §6 全結果の前提 |
| **(4.3)** | 15-23 | **Theorem** | 4 部: (a) W - W₂ は TI-subset, (b) character Ind_W^L(ω_ij - ω_{0j}) = δ_j(μ_ij - μ_{0j}), (c) μ_ij 値評価, (d) degree 合同 | **Dade 構成の詳細化**; (4.3.b) 論理中心 | **9 cite** (§7×2, §12×3, §15×2) |
| **(4.4)** | 35-37 | **Lemma** | μ_{i0} 族 (j=0 case): kernel が K を含む既約 character 類 | (4.3) 補遺 (kernel characterization) | 5 cite (§12×3) |
| **(4.5)** | 39-49 | **Theorem** | 2 部: (a) χ_j := Res_K^L μ_ij は i に無依存, Irr(K) 元, (b) Ind_K^L χ分解 | **Character factorization** | 5 cite (§7, §11×2) |
| **(4.6)** | (proof body) | **Hypothesis** | Dade 一般 setup (実は §9-§16 で **explicit に呼ばれる中核**) | **named hypothesis** for §9-§16 | 5 cite (§7×2, §8, §12) |
| **(4.7)** | (proof body) | **Supp lemma** | character support 制限の重要補題 | **§7 (5.3.b) proof の API edge** | **7 cite** (§7×3, §11×2, §8, §12) |
| **(4.8)** | (proof body) | helper | (4.7) 補助 | 内部 | 内部 |
| **(4.9)** | (proof body) | **τ-isometry Thm** | Dade isometry τ の formal Thm | 主結果 | 4 cite (§12, §13, §15) |
| **(4.10)** | (proof body) | 4-term identity | character identity for (4.9) | 計算補助 | 内部 |

---

## (4.1)-(4.5) 詳細解説

### (4.1) Lemma — Orthogonality criterion

**主張**: 有限群 X, α, β, γ, δ ∈ ±Irr(X), u, v ∈ ℝ^# に対し
- (α, β) = (γ, δ) = (α - β, uγ - vδ) = 0
- (α - β)(1) = (uγ - vδ)(1) = 0

⟹ **α, β, γ, δ が pairwise orthogonal**

**証明戦略**: 
- Suppose (α, γ) ≠ 0 ⇒ γ = εα (ε = ±1)
- 0 = (α - β, uγ - vδ) = u ε + v(β, δ) ⇒ (β, δ) ≠ 0
- Character degree condition (α - β)(1) = 0 から矛盾導出

**役割**: (4.3) 証明で μ_ij の pairwise distinctness を確認する際の技術補題.

**Lean 形式化**: 内積計算 + character degree algebra. ~20 行.

---

### (4.2) Hypothesis — Frobenius 型 subgroup family

**主張**: L = K ⋊ W₁ という **特定の structure** を仮定:

- **(a) W₁ は L の cyclic Hall subgroup** ⚠️ audit 訂正 (旧記載「K の Hall」は誤り; mmd L9: Hall of L) (cyclic かつ (|W₁|, |K|) = 1)
- **(b) ∃ cyclic W₂ ⊂ K: ∀ x ∈ W₁^#, C_K(x) = W₂** — **Key condition**: K の全ての non-identity W₁-elements が **同じ centralizer を持つ** (characteristic subgroup W₂)
- **(c) W := W₁ × W₂ は odd order**

**数学的意義**: 
- Frobenius group (complementary structure) の一般化 + **cyclic action による centralizer 硬直性**
- BG (局所部分群論) で現れる maximal subgroup Type II, III, IV の指標論的化身
- §4 の一般 Hypothesis (2.2) を **具体的・計算可能な形** に特殊化

**λ, q記号**: w₁ := |W₁|, w₂ := |W₂| (単位群要素数). mmd で これらが繰り返出現.

**Lean 形式化**: Structure で 3 条件 encode. ~30 行.

---

### (4.3) Theorem — TI-subset と Induced character の分解

**主張** (Hypothesis (4.2) 下):

#### (a) TI-property + Hypothesis (3.1) 継承

```
W - W₂ は TI-subset of L (正規化群 = W)
Hypothesis (3.1) が L に対して成立
```

**証明**: xy ∈ W - W₂ (x ∈ W₁^#, y ∈ W₂) の共役が再び W - W₂ に入るなら、x の共役は W₁ に入る. L/K commutative ⇒ x^g = x ⇒ g ∈ C_L(x) = W.

#### (b) Character induction 分解

```
∃ μ_ij ∈ Irr(L) (0 ≤ i < w₁, 0 ≤ j < w₂), δ_j = ±1 such that:
  Ind_W^L (ω_ij - ω_{0j}) = δ_j (μ_ij - μ_{0j})
  
(ω_ij := restriction of standard character を W で定義)
```

**Key observation**: 
- (ω_ij - ω_{0j})_{i>0,j≥0} が CF(W, W - W₂) の **basis** を成す (|(W - W₂)| = (w₁ - 1)w₂ 個)
- Ind_W^L が CF(W, W - W₂) 上 **isometry** (§3 Preliminary)
- (1.4) より character decomposition が可能

#### (c) Character value 評価

```
∀ 0 ≤ i < w₁, 0 ≤ j < w₂, x ∈ W - W₂:
  μ_ij(x) = δ_j ω_ij(x)
  
(Other char ∉ {μ_ij} は W - W₂ で vanish)
```

#### (d) Degree 合同

```
μ_ij(1) ≡ δ_j (mod w₁)
```

**証明**: μ_ij の W₁-restriction を分析. regular character ρ_{W₁} との合同.

**Lean 形式化**: (a) は TI criterion, (b)-(d) は character calculation. **形式化難所は (b) の induction decomposition**: § 3 の isometry + (1.4) lemma + (4.1) orthogonality を組合せ, w₁ · w₂ 個の basis element に対する並列 character construction. ~80-100 行.

---

### (4.4) Lemma — Kernel characterization

**主張**: (4.3) 記号下で、j = 0 case:

```
μ_{i0} (0 ≤ i < w₁): kernel が K を含む Irr(L) の complete set

δ_0 = 1 かつ μ_00 = 1_L (自明指標)
```

**意義**: 
- W₂ が trivial (j=0) のとき、Dade 像が **K を quot した L/K の character に対応**
- §7 Coherence, §11-§13 では μ_{i0} (または その induced version) が coherence family の一部として出現

**証明**: 
- χ ∈ Irr(L), K ⊆ Ker χ ⇒ restriction to W は ω_{i0} 型 (§3 preliminary + (3.9))
- (3.9) apply ⇒ χ = δ_0 μ_{i0}. Character なので δ_0 = 1
- k = 0 ⇒ μ_00 = 1_L

**Lean 形式化**: Kernel inclusion + character restriction. ~25 行.

---

### (4.5) Theorem — Induced character と K-restriction

**主張** (Hypothesis (4.2) 下):

#### (a) χ_j := Res_K^L μ_ij の i-independence

```
∀ i, i': χ_j(= Res_K^L μ_ij) = Res_K^L μ_{i'j}

χ_j ∈ Irr(K)
Ind_K^L χ_j = μ_j := ∑_{0≤i<w_1} μ_ij
```

**証明思路**:
- (4.3.b) より μ_ij - μ_{0j} は (W - W₂)^L の外で消える
- K ∩ W = W₂ なので K で消える ⇒ χ_j := Res_K^L μ_ij は i-independent
- χ = irreducible component of χ_j ⇒ (Ind_K^L χ, μ_ij) ≠ 0 for all i
- Degree counting: w₁ χ(1) = (Ind_K^L χ)(1) ≥ ∑_i μ_ij(1) = w₁ χ_j(1) ≥ w₁ χ(1) ⇒ χ = χ_j

#### (b) χ ∉ {χ_j} な場合の Ind_K^L χ

```
χ ∈ Irr(K), H ⊄ Ker χ ⇒ Ind_K^L χ ∈ Irr(L)

Ind_K^L χ ∉ {μ_ij}

Irr(L) = {μ_ij | 0≤i<w₁, 0≤j<w₂} ∪ {Ind_K^L χ | χ ∈ Irr(K) \ {χ_j}}
```

**証明**: 
- g ∈ W₁^# ⇒ g acts on K の conjugacy classes. Fixed-point-free action ⇒ |⟨g⟩| divides |C|, 矛盾. ⇒ ∃ x ∈ ⟨g⟩^# で C ∩ C_K(x) ≠ ∅ 固定点存在
- K の conjugacy class count normalized by g は ≤ w₂
- [Is] Thm 6.32 (character fixed point) ⇒ Irr(K) で g-fixed は ≤ w₂ 個
- μ_{0j} ∈ Irr(L) ⇒ χ_j fixed by g ⇒ other χ ∉ {χ_j} は g-fixed でない
- ⇒ I_L(χ) = K (inertia group = K のみ)
- (1.5.b) ⇒ Ind_K^L χ irreducible
- (Ind_K^L χ, μ_ij) = (χ, χ_j) = 0

**Lean 形式化**: (a) は degree counting + (4.3) apply, (b) は fixed point count + inertia group analysis. **難所**: (b) の Isaacs [Is] Thm 6.32 (Brauer permutation lemma / character centralizer fixed point). ⚠️ audit 訂正 (旧記載「Phase 1 Ch.指標論で確認」は誤り): **Brauer permutation lemma は mathlib v4.29.1 不在 (grep 0) かつ Phase 1 計画にも無し**. **新規 `OddOrder/RepresentationTheory/BrauerPermutation.lean` (~80 LOC) 要 — §6 (4.5.b) の単一最大 blocker** (§3 (1.1) でも必要). ~60-80 行 + infra.

---

## §4 (基礎 Dade) との差 + §5 との関係

### §4 との比較

| 項目 | §4 (2.1)-(2.6) | §6 (4.1)-(4.5) |
|------|---|---|
| **Hypothesis** | (2.2) 一般化 (conjugacy equiv, centralizer factorization, coprime) | (4.2) 特殊化 (L = K ⋊ W₁, cyclic Hall, centralizer = W₂) |
| **TI-subset** | (2.2) で抽象定義 | (4.3.a) で W - W₂ が TI 証明 |
| **Dade map τ** | (2.5) generic 定義 | (4.3) で W, K, μ_ij 明示構成 |
| **Main theorem** | (2.6) isometry + virtual character preservation | (4.3)-(4.5) concrete decomposition |
| **新概念** | Dade isometry (mathlib 未収載) | なし (§4 の application) |

**使用パターン**: §6 は「§4 (2.2)-(2.6) が、Hypothesis (4.2) を満たすとき、concretely どう計算されるか」を示す tutorial 役.

### §5 との関係 ⚠️ audit 訂正 (旧記載「§5 と独立」は誤り)

§5 (3.1)-(3.9) は **cyclic normalizer** 特殊化:
- L = N_G(A)
- A ⊂ L, A^g ∩ A ≠ ∅ ⇒ g ∈ L (TI-definition)
- L has cyclic normalizer (e.g., Frobenius complement)

§6 (4.2)-(4.10) は **異なる setup**:
- L = K ⋊ W₁ (semi-direct product structure explicit)
- Hypothesis (4.2.b) では "centralizer = W₂" と **fixed**, 関係定義ではない
- W - W₂ が TI-subset (§5 の後続結果)

**§5 → §6 (audit 訂正): 実は §5 dep が遥かに重い**:
- §5 (3.X) cite **8 件** (3.1×3, 3.2×5, 3.3×2, 3.4, 3.6, 3.8, 3.9×3) vs §4 (2.X) cite **3 件のみ**
- §6 = 「§5 σ を §6 (4.6) で embed + §4 Dade τ で L→G lift」
- §5, §6 両者が §7 Coherence で統合される

---

## §7 Coherence への橋渡し

### Character family の準備

§6 (4.3)-(4.5) で構築された character families:
- **μ_ij** ∈ Irr(L): (w₁ × w₂) 個の既約 character マトリックス
- **χ_j** ∈ Irr(K): w₂ 個の K-既約 character
- **δ_j** ∈ {±1}: induction sign

### §7 (5.1)-(5.6) での活用

**Coherence Hypothesis (5.2)** で:
- S ⊂ Irr(L) として {μ_ij | 0 < i < w₁, 0 < j < w₂} または subset を選択
- (5.2.a) complex conjugation: χ̄ ∈ S, χ̄ ≠ χ ⇒ **§6 では δ_j ∈ {±1} による対称性**
- (5.2.b) τ isometry: §6 の Dade isometry τ from (4.6)
- (5.2.d) R(χ) decomposition: (4.3.c) の character value 評価から orthonormal decomposition 導出

**Theorem (5.6) Coherence composition** では:
- (4.5) で χ_j の degree 関係 `χ_j(1) | μ_j(1)` が条件 (5.6.b) に
- (4.3.d) degree 合同 `μ_ij(1) ≡ δ_j (mod w₁)` が (5.6) の norm bound に

---

## §10-§16 Type 分析での使用

### §11 (Maximal Subgroup Type II/III/IV)

**(9.2) Hypothesis**: M maximal of Type II/III/IV, H kernel, U ⋊ W₁ Frobenius.

**利用ポイント**:
- (9.3): H の位数 (Type II なら |H| = |W₂|^q, Type III/IV なら |H| = p^q |C_H(U)|)
- (9.5), (9.8): **τ (Dade isometry relative to A(M), M, G)** の notation 導入
- **§6 (4.3)-(4.5) の character family が§11 の σ, ω_ij, μ_ij, χ_j として再現**

### §15 (Subgroup S and T)

最大規模の型分析節. §6 の character family:
- **S, T の characterization** に character-theoretic constraint (μ_ij の degree, χ_j の kernel)
- (13.X) lemma series で S/T の normal structure を §6 の character factorization で制限

---

## mathlib カバレッジ

| 結果 | mathlib | Phase 1 | 新規 | 形式化コスト |
|------|---------|---------|------|-----------|
| (4.1) | mid (inner product, degree) | — | 30% | 短 (~20 行) |
| (4.2) | low (structure def) | Frobenius 周辺 | 60% | 中 (~30 行) |
| (4.3) | low (construction) | §3 preliminary, TI-subset | **85%** | **大 (~100 行)** |
| (4.4) | mid (kernel characterization) | §3, (1.5) | 40% | 短 (~25 行) |
| (4.5) | low (induction decomposition) | character fixed point (Thm 6.32) | **85%** | **大 (~80 行)** |

**全体カバレッジ**: ~30% (mathlib + Phase 1 周辺) + **70% 新規** (character construction + fixed point analysis).

**§4 との比較**: §4 は Dade 新概念導入で 20% カバー, §6 は application で 30% (§4 結果 reuse). 難度は §4 (2.10) inclusion-exclusion と同等程度.

---

## Phase 2b §6 形式化着手順

### Stage 1: Infrastructure (1.5-2h)
- Hypothesis (4.2) structure 定義 (L, K, W₁, W₂)
- odd order condition encoding
- Phase 1 Ch.6 (Frobenius) からの import

### Stage 2: (4.1) Lemma (1h)
- Orthogonality criterion
- Inner product + degree computation

### Stage 3: (4.3) TI-property (1.5h)
- (4.3.a) W - W₂ の TI-proof
- Hypothesis (3.1) 継承

### Stage 4: (4.3) Character construction (3-4h, **山場**)
- ω_ij 族の basis generation
- Ind_W^L isometry (§3/§4 lemma reuse)
- (4.1) を使った μ_ij のorthogonality
- δ_j sign assignment
- **(4.3.c)-(d)** character value + degree calculation

### Stage 5: (4.4) Lemma (1h)
- j = 0 case의 kernel characterization
- μ_00 = 1_L verification

### Stage 6: (4.5) Theorem (2-3h, 難)
- (4.5.a) χ_j の i-independence + (Irr K) 証明
- Degree counting argument
- **(4.5.b)** Fixed point theory + inertia group (Isaacs [Is] Thm 6.32)
- Character decomposition 분해 = Irr(L) 완전성

### Stage 7: Integration + Verification (1-1.5h)
- §4, §5 との crosse-reference 확인
- §7 preview: coherence family 構成可能성 檢証

**합計**: **13-16 시간**, 행数 ~280-350 행.

---

## 核心技術: Dade Hypothesis (4.6) との관계

§6 는 §4 Hypothesis (2.2) 를 구체화하지만, 더 실용적인 **Hypothesis (4.6)** (§4 pp. 21-24 의 "4.6") 를 맡음:

- (4.6.a) L satisfies (4.2)
- (4.6.b) G, W satisfy (3.1) [Preliminary hypothesis]
- (4.6.c) H normal in L, W₂ ⊆ H ⊆ K
- (4.6.d) A with **∪_{h∈H^#} C_K(h)^# ⊆ A ⊆ K^#**, Hypothesis (2.2) holds both for A and A₀ := A ∪ V^L
- (4.6.e) τ is Dade isometry relative to A₀

**§9-§16 の具体適用**: Hypothesis (4.6) が §9 (Non-existence), §11 (Type II/III/IV), §15 (S, T) で explicitに呼び出される. (4.6) は (4.2)+(4.3)-(4.5) from §6 を前提に成立.

**形式化の dependency chain**:
```
§4 (2.1)-(2.6) Dade general theory
       ↓
§6 (4.1)-(4.5) Dade for Hypothesis (4.2)
       ↓
§6 (4.6) Dade for specific subgroup + A
       ↓
§7 (5.1)-(5.6) Coherence on Hypothesis (4.6) character family
       ↓
§9-§16: 具体型分析
```

---

## 未解決 / TODO

1. **Phase 1 Ch. 指標論完成**: (4.1), (4.3.c)-(d), (4.5.b) は character value computation + fixed point theory に依存. Phase 1 Ch.指標論 (Isaacs 再掲 + mathlib orthogonality) の完成日程を確認必須.

2. **Hypothesis (4.6) の section structure**: (4.6) は主に §9-§16 で多用. §6 ではHypothesis statement のみで、実際の形式化は (4.3)-(4.5) から自動に従うか、それとも separate lemma化すべきか設計.

3. **Phase 2a (BG) との同期**: §11 (9.1)-(9.8) で BG の Frobenius action (Wielandt theorem, Maschke) が heavily cited. BG Phase 2a との timing alignment.

4. **§5 との relationship clarity**: §5, §6 の順序が論理的に reverse か (§5 → §6) forward か (§6 独立か) を mmd 跡付けで最終確認.

---

## 監査 + 修正 (2026-06-01): `CertainTypeHypothesis` の (4.2) faithfulness バグ

Peterfalvi (6.8)(c2) (= "Hyp (4.6) holds with H=K") の formalize 中に `CertainTypeHypothesis` を
監査し、**実バグを発見・修正** (commit e6090a0、build+AxiomsCheck green、sorry 不変):

- **バグ**: 旧 field `W_sup : W1 ⊔ W2 = ⊤` は**数学的に誤り**。(4.2)(c) の `W = W₁ × W₂` は `L` の
  **真部分群** (`W₂ ⊊ K` ゆえ `|W| = w₁w₂ < |K|w₁ = |L|`); `W₁⊔W₂=⊤` は `L = W₁×W₂` を主張し (4.2)(a)
  `L = K⋊W₁` (K 非自明 normal) と矛盾。`W_disjoint` と併せ K 自明でない限り **vacuous** だった。
- **load-bearing 0**: repo 内で `CertainTypeHypothesis` の construct ゼロ・`W_sup`/`W1` 参照ゼロ
  (`DadeApplication`/`FullDadeApplication` は `.dade` のみ、Pf (6.8)(c2) は `.dade/.K/.W2/.W1`) ⟹ 安全。
- **修正後 (真の (4.2))**: `W_sup` 削除 → `isComplement : IsComplement' K W1` ((4.2.a) L=K⋊W₁) /
  `W1_cyclic`/`W2_cyclic` / `W2_le_K` ((4.2.b)) / `centralizer_W2` ((4.2.b) `C_K(x)=W₂ ∀x∈W₁^#`) /
  `W_odd` ((4.2.c) `|W₁⊔W₂|` odd)。`W_disjoint` 保持 (真: W₁∩W₂⊆W₁∩K=⊥)。
- **full (4.6) への残り** (§6 を §9-§16 で使う際に要追加): (4.6.b) `(3.1)` for `(G,W)`、(4.6.c) `H` normal
  with `W₂⊂H⊂K`、(4.6.d) Dade `A` の bounds `∪_{h∈H^#}C_K(h)^#⊂A⊂K^#` + `A₀=A∪V^L`、(4.2.a) Hall 性。
  **ただし (6.8)(c2) は H=K ((4.6)H が K に collapse) ゆえ現 (4.2)-core + dade で十分。**
- 帰結: Pf (6.8)(c2) を `cert.K=H ∧ cert.W1=W1 ∧ cert.dade=dade ∧ w₂素 ∧ W₂⊆[H,H]` に強化
  (`cert.W1=W1` は W_sup 撤去で初めて無矛盾)。

5. **(4.3.c) character value evaluation の tactics**: ω_ij, δ_j の explicit formula を Lean で derive する際、induction lemma + restriction formula の apply 順序最適化.

---

## Appendix: Notation 定義

- **L**: K ⋊ W₁ (semi-direct product)
- **K**: normal subgroup of L
- **W₁**: cyclic Hall subgroup of L (complement to K), order w₁
- **W₂**: cyclic subgroup of K, C_K(x) = W₂ for all x ∈ W₁^#, order w₂
- **W**: W₁ × W₂, odd order
- **ω_ij**: character on W, indexed by (i ∈ ℤ/w₁, j ∈ ℤ/w₂)
- **μ_ij**: irreducible character of L, constructed from ω_ij via Ind_W^L
- **δ_j**: sign ±1, coefficient in Ind_W^L(ω_ij - ω_{0j}) = δ_j(μ_ij - μ_{0j})
- **χ_j**: irreducible character of K, χ_j = Res_K^L μ_ij (i-independent)
- **A**: subset of K^# relevant to Dade isometry (Hypothesis (4.6.d))

---

*作成: 2026-05-22. 出典: Peterfalvi `references/peterfalvi/04.6_pp_21_24_*.mmd` (108 行), `04.4_pp_10_14_*.mmd` (§4 参照), `04.5_pp_15_20_*.mmd` (§5 参照), `notes/peterfalvi/_overview.md`, `notes/peterfalvi/s04_dade_isometry.md`, `notes/peterfalvi/s07_coherence.md`.*

**次ステップ**: §4 の predicate-based Dade isometry 設計が (4.2)-(4.5) の character construction と compatible か Stage 4 (construction) で検証. §7 preview time の coherence setup sanity check.
