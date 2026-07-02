# Peterfalvi §6: The Dade Isometry for a Certain Type of Subgroup — mini-roadmap

> ⚠ 2026-07-02: **HISTORICAL** — lane 名は 2026-07-02 3 レーン再編前; 現行 = [`ft_lane_reallocation_2026_06_28.md`](../meta/ft_lane_reallocation_2026_06_28.md)。「次 = B レーン戦略判断」は解消済 — coherence 後継 = (6.5.c)/(5.7)-S07 refactor (lane b, issue 9001)。

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

---

## 2026-06-08 (session 9, b-peterfalvi): certain-type プロジェクト着手 — RECON + Brauer-done 訂正 + 真スコープ + 依存順 plan

ユーザが「§4 certain-type に着手」(strategic fork option A) を選択。CB4 = (6.8.2) math-B の真のゲート。
**着手前の dependency-audit で session-8 CB4 verdict の中核主張が誤りと判明** (verify, don't assume)。

### 🔢 numbering 確定 (再調査するな)
repo `S0N` ファイル = PDF chunk `04.N`、**Peterfalvi の result 番号 = N−2**。
- result **(1.x)** prelim = chunk 04.3 = repo `S03_PreliminaryCharacter`
- result **(2.x)** Dade = chunk 04.4 = repo `S04_DadeIsometry`
- result **(3.x)** TI-cyclic σ = chunk 04.5 = repo `S05_TICyclic`
- result **(4.x)** certain-type = chunk 04.6 = repo `S06_DadeIsometryCertain`  ← **本プロジェクト**
- result **(5.x)** Coherence = chunk 04.7 = repo `S07_Coherence`
- result **(6.8)** capstone = chunk 04.8 = repo `S08_CoherenceTheorems`
verdict が「§4」と呼んだのは result 番号が 4.x だから。section/file は **S06** (本体) + 依存先 **S05** (σ)。

### 🛑→✅ session-8 verdict 訂正: Brauer [Is] 6.32 は形式化済み (verdict は誤り)
verdict は「(4.5.b) は Brauer permutation lemma [Is] 6.32 にブロック、未形式化 → 新 `BrauerPermutation.lean` 要、~4-6h」と書いたが、**既に完全形式化・0-sorry**:
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean`: `brauer_permutation_lemma` (一般形 + 仮説), `brauer_permutation_lemma_general/'`
- `BrauerPermutationUnconditional.lean`: `brauer_permutation_lemma'` (unconditional, hypothesis-free, [Is] 6.32)
- `ConjugationBrauer.lean`: ambient-conjugation packaging — docstring に "needed by Peterfalvi (6.8)", `inertia_eq_of_freeAction` 等 (= (4.5.b) の fixed-point 部分の道具)
**⟹ (4.5.b) の単一最大 blocker は消滅。** verdict の ~18-22h 見積もりの Brauer 部分は free。

### 真のスコープ (verify 済): §5 (3.x) σ-isometry + §6 (4.x) certain-type の**定理本体**
S05 (180 行) / S06 (151 行) は **hypothesis bundle + Dade-application interface のみ**。定理本体 (3.1)-(3.9) / (4.1)-(4.10) は**未形式化**。case-A (c1, DONE) は S08 で ad-hoc 構成し (4.x)/(3.x) を bypass したため、math-B (CB4) は本体を新規に要す。

**利用可能な基盤** (再調査するな):
- (4.1) ✅ `pairwise_inner_eq_zero_of_orthogonal_signedDifference` (S08:204) — orthogonality criterion
- (1.x) building blocks: S03 に `inductionCoefficient`/`IsInductionExpansion`/`characterDegree`/induction-restriction 補題群 (= (1.2)-(1.5) の素材豊富)
- (2.x) 汎用 Dade τ: S04 `Hypothesis`/`dadeIntegralCharacterMap`/`FullDadeIsometryData`/`IsDadeIsometry` (4326 行, 完成)
- §7 R(χ) per-pair producer: `dadeOrthonormalCharacterImageFamily` / `…OfDiff` (S07:5387/5472) — **{χ,χ̄} conjPairFamily 単位**の R(χ) を Dade map から生成 (irreducible χ 限定)
- Brauer ✅ (上記)、`TICyclicHypothesis`→`toDadeHypothesis`→S04 (S05) の配線

**未形式化 (本プロジェクトで書く)**:
- §5: (3.2) σ-isometry, (3.3) ω_ij notation, (3.4) α_ij basis, **(3.5) χ_ij 直交族 [HARD core]**, (3.6)Hyp/(3.7)/(3.8) NC(ψ) 構造, (3.9) Galois ((1.9) 要)
- §6: **(4.3) μ_ij 構成 [HARD, 山場]**, (4.4) kernel, (4.5) χ_j factorization (Brauer 消費), (4.7) Supp, (4.8), **(4.9) τ-isometry [CB4 target]**, (4.10) 4-term

### 🔑 核心の設計判断 (再調査するな): §7 producer は (3.5) を subsume しない
`dadeOrthonormalCharacterImageFamily` は **{χ,χ̄} pair 単位**の 2-元 R(χ) (coherence reflection) を作る。
(3.2) σ は **CF(W) 全体 (w₁·w₂ 次元) 上の global isometry** で、χ_ij = ω_ij^σ が**全 index 横断の直交族**を成す ((3.5) の構成)。両者は別物 — per-pair producer から global σ は出ない。
- **ω_ij^σ の存在 = (3.5) が本質的に必要** (Ind_W^G α_ij = 1−χ_i0−χ_0j+χ_ij の clean 分解の存在が (3.5))。
- (3.9.a) は「χ∈±Irr(G), χ|_V=ω|_V ⟹ χ=ω^σ」で**一意性**を与えるが**存在は (3.5)**。
- ω_ij は linear (deg 1=irred) だが、Dade map は supported 関数 (ω_ij(1)=1≠0 ゆえ ω_ij 自体は non-supported) にしか効かない → supported **差** Ind_W^G α_ij 経由でしか σ-image は出ず、その分解の存在が (3.5)。

⟹ **verdict が見落とした真のボトルネック = §5 (3.5) σ-construction** (Brauer ではない)。hard core は **2 つ: (3.5) と (4.3)**。

### 依存グラフ (CB4 = (4.9) への最短連鎖)
```
(3.3)ω_ij ─→ (3.4)α_ij basis ─→ (3.5)χ_ij 直交族 [HARD] ─→ (3.2)σ assembly
                                       │                        │
                                       ├─→ (3.6/3.7/3.8) NC(ψ) ─┤
                                       └─→ (3.9) Galois ((1.9))  │
(4.1)✅ ─────────────────────────────────────────────────────────┤
                                                                  ▼
   (3.2)σ + (1.4) ─→ (4.3)μ_ij [HARD,山場] ─→ (4.4)kernel
                          │                       │
                          ├─→ (4.5)χ_j (Brauer✅) │
                          ├─→ (4.7)Supp ──────────┤
                          └─→ (4.8)(uses 3.8) ─→ (4.9)τ-isometry [CB4 target] ─→ (4.10)
```
その後: (4.9) を (6.8.2) `inr`/math-B に配線 (CB4) + CB5 (6.8.3) + CB6 wiring → capstone 完了。

### 依存順 leaf plan (build-green + axiom-clean を 1 leaf ずつ)
1. **(3.3) ω_ij family** ← 🟡 FOUNDATION ✅ DONE (session 9, commit `086dac8f`, full 3599 + AxiomsCheck 3557 green, axiom-clean)。S05 に: (3.1) field `W_cyclic : IsCyclic W` 追加 (構築箇所 0 ゆえ安全) + `isMulCommutative_W` (W abelian) + `omega χ := linearIrreducibleCharacter χ` + `omega_apply`/`omega_apply_one` (deg 1) + `omega_injective`/`omega_surjective` (後者は `exists_linearIrreducibleCharacter_eq_of_isMulCommutative`) → **`omegaEquiv : (W →* ℂˣ) ≃ Irr(W)`** (= 「(3.3): Irr(W)={ω_ij}」)。**残 (3.3) = ω_i0/ω_0j sub-family** (`W2.subgroupOf W ≤ χ.ker` / `W1.subgroupOf W ≤ χ.ker`) **+ 積分解 `ω_ij = ω_i0·ω_0j`** — 内部直積 `↥W ≅ ↥W₁ × ↥W₂` が core。**構成レシピ (session 9 で API scope 済、再調査不要)**: mathlib に「2 部分群内部直積→group MulEquiv」の既製品は**無い** (`Subgroup.prodEquiv` は外部積、`IsComplement'.QuotientMulEquiv` は商)。自前構成: `W1' := hyp.W1.subgroupOf hyp.W`, `W2' := hyp.W2.subgroupOf hyp.W` (↥W の subgroup; `W1'⊓W2'=⊥` は `W_disjoint`、`W1'⊔W2'=⊤` は `W_sup`)。写像 `f : ↥W1' × ↥W2' →* ↥W := MonoidHom.noncommCoprod W1'.subtype W2'.subtype (commute は `isMulCommutative_W` から; ⚠ `MonoidHom.coprod` は `[CommMonoid]` instance 要で ↥W は Group+mixin のみゆえ避ける)`。injective (kernel ⊆ W1'⊓W2'=⊥)・surjective (range = W1'⊔W2'=⊤) → `MulEquiv.ofBijective`。次いで `Hom(↥W,ℂˣ) ≃ Hom(↥W1',ℂˣ)×Hom(↥W2',ℂˣ)` を `f.symm` 経由 + `MonoidHom.prod`/`MonoidHom.fst,snd` で。ω_i0 = W2'-trivial の χ (= W1' 成分のみ)、ω_0j = W1'-trivial、ω_ij = ω_i0·ω_0j (`omega` の multiplicativity: `omega_apply`+`map_mul`+`Units.val_mul`)。Fin w₁×Fin w₂ indexing は W₁/W₂ cyclic ⟹ `Irr(W_k)≅ZMod w_k` で後付け。

**進捗 (session 9 loop)**: ✅ **`wProdEquiv : ↥W1' × ↥W2' ≃* ↥W` + `W1_subgroupOf_inf/sup_W2_subgroupOf_eq_bot/top` DONE** (commit `a6a1f61f`, full 3599 green, axiom-clean, AxiomsCheck 登録)。レシピ通り `MonoidHom.coprod`(`open scoped IsMulCommutative` で `CommMonoid ↥W`)+ bijectivity。✅ **積分解 DONE** (commit `b0ae2f1b`): Hom-積 equiv は mathlib 不在ゆえ、より直接的に射影 `wProj1/wProj2 : ↥W →* ↥W` (`subtype∘fst/snd∘wProdEquiv.symm`) + 再構成 `wProj1 w · wProj2 w = w` + **`char_eq_wProj_comp_mul`** (`χ = (χ∘wProj1)·(χ∘wProj2)` = ω = ω_i0·ω_0j at Hom level) で実装。✅ **ω_i0/ω_0j defining property DONE** (commit `5a4373f7`): `wProj1_eq_one_of_mem_W2`/`wProj2_eq_one_of_mem_W1` + `W2/W1_subgroupOf_le_ker_comp_wProj1/2` (ω_i0 factor は W₂ を kernel に、ω_0j は W₁ を)。

**⟹ (3.3) Notation 完成** (omega/omegaEquiv=Irr(W)=linear chars + wProdEquiv=W₁×W₂ + ω=ω_i0·ω_0j + ω_i0/ω_0j の kernel 特性; 全 axiom-clean・AxiomsCheck 登録)。**Fin w₁×Fin w₂ の明示 indexing は (3.4) で count が要るとき後付け**(W₁/W₂ cyclic ⟹ `Irr(W_k)≅ZMod w_k`)。

**次 leaf = (3.4)** `α_ij = (1−ω_i0)(1−ω_0j)` が `CF(W,V)` (V=W−(W₁∪W₂)) の basis、`dim = |V| = (w₁−1)(w₂−1)`。

### (3.4) feasibility assessment (session 9 loop、stop checkpoint で精査)
`CF(W,V)` = `S04.SupportedClassFunctions ℂ V W` = `↥(ClassFunction.supportedSubmodule (supportInSubgroup V W))` (S04:148)。
- **tractable な sub-piece**: (a) `alpha (χ₁:↥W1'→*ℂˣ)(χ₂:↥W2'→*ℂˣ) := (1 − ω(χ₁∘wFst))·(1 − ω(χ₂∘wSnd))` の定義 + **membership `alpha ∈ CF(W,V)`** — 今 session の `W2/W1_subgroupOf_le_ker_comp_wProj1/2` で直接出る(W₁ 上 ω_0j=1⟹(1−ω_0j)=0、W₂ 上同様)。(b) 線形独立 — Fourier infra あり: `sum_inner_irreducibleCharacter_smul` (CharacterCompleteness:600) + `irreducibleCharacter_inner` (直交性)。`a_ij = ⟨∑a_kl α_kl, ω_ij⟩`。
- **🔴 インフラ gap**: `dim CF(W,V) = |V| = (w₁−1)(w₂−1)`。repo/mathlib に `finrank SupportedClassFunctions`/`finrank supportedSubmodule` の直接 API **無し** (grep 0)。`supportedSubmodule (supportInSubgroup V W)` の次元 = (W abelian ⟹ class=点 ⟹) `|V|` を新規に建てる要 (`finrank ClassFunction = |ConjClasses|` は CharacterCompleteness:557 にあるが supported 版は要構築)。`|V| = |W|−w₁−w₂+1 = (w₁−1)(w₂−1)`。
- **🔴 設計判断**: α の indexing。character-group `↥W1'→*ℂˣ × ↥W2'→*ℂˣ` (自然、命名軽) vs `Fin w₁×Fin w₂` (Peterfalvi 準拠)。**(3.5) σ-construction は明示 index `i,j` の組合せ論 (A_ij 3-元集合, case I/II) を使う** ⟹ Fin-indexing が (3.5) で要る公算大 (W₁/W₂ cyclic ⟹ `Irr(W_k)≅ZMod w_k` で橋渡し)。この選択は (3.4)/(3.5) 全体の foundation を決める。

⟹ **stop checkpoint**: (3.3) 完成は綺麗な milestone。(3.4) は「設計判断 (indexing) + API gap (CF(W,V) 次元)」の領域で、直後が hard core (3.5)。loop を止めユーザに選択肢提示 (2026-06-08 session 9 末)。

### ✅ 設計決定 (2026-06-08 session 9、ユーザ承認済み)
1. **indexing = character-group**(再調査不要)。α を **非自明 `Irr(W₁') × Irr(W₂')`**(= `(↥W₁'→*ℂˣ) × (↥W₂'→*ℂˣ)`)で index。**Fin/ZMod は使わない**。根拠: (3.5) の組合せ論 ((3.5.4) の β_i1 case 分析・"w₁≥5"・"|A_12|≥1+(w₁−2)") は index 集合の**濃度** `|Irr(W_k)\{1}|=w_k−1` と**相異な元の存在**のみ使い、index の算術は使わない ⟹ character-group(濃度 `|Irr(W_k)|=w_k`+相異)で (3.4) も (3.5) も回る。必要事実 = 有限 abelian 双対 `|↥W_k'→*ℂˣ| = w_k`(mathlib Pontryagin)。
2. **CF(W,V) 次元 = インフラ構築**。`dim CF(W,V) = |V| = (w₁−1)(w₂−1)` を新規補題で(abelian W ⟹ `ClassFunction = 点上関数`, `supportedSubmodule (supportInSubgroup V W)` 次元 = |V|; `|V| = |W|−w₁−w₂+1`)。
3. **線形独立 = Fourier** (`sum_inner_irreducibleCharacter_smul` + `irreducibleCharacter_inner`)、basis = lin-indep + 次元一致。
- sub-leaf 順: α 定義 + CF(W,V) membership(今 session の kernel 補題で出る)→ CF 次元インフラ → lin-indep → basis 組立。**loop 再開 (min-interval); (3.5) hard core 到達で再停止。**

**⚠ V-handling 決定 (session 9 loop で発見)**: `TICyclicHypothesis.V` は §6/§8 再利用のため一般フィールドで、**(3.4) が要求する `V = ↑W∖(↑W₁∪↑W₂)` に固定されていない**(`dim CF(W,V)=|V|=(w₁−1)(w₂−1)` はこの特定 V 必須)。**解決 = (3.x) 定理は `hVeq : hyp.V = (↑W:Set G)∖(↑hyp.W₁∪↑hyp.W₂)` を仮説に取る**(構造体は一般のまま、(3.1) 忠実; (3.2) σ が hyp.V の Dade map から来るので hVeq で V=Vdiff を固定)。

**進捗 (session 9 loop)**: ✅ **factor 射影 `wFst`/`wSnd : ↥W →* ↥W₁'/↥W₂'` + kill facts `wFst/wSnd_eq_one_of_mem_W2/W1` DONE** (commit `b3b93c3a`, full 3599 green, AxiomsCheck 登録) — α の prerequisite。**次 = `alpha (χ₁:↥W₁'→*ℂˣ)(χ₂:↥W₂'→*ℂˣ) := (1 − (omega(χ₁.comp wFst):CF))·(1 − (omega(χ₂.comp wSnd):CF))` 定義 + membership `alpha ∈ CF(W, Vdiff)`**(`hVeq` 下; W₁ 上 ω_0j=1⟹因子0、W₂ 上 ω_i0=1⟹因子0、`wFst/wSnd_eq_one` + `omega_apply_one` で)→ CF 次元インフラ → lin-indep → basis。

**進捗 (session 10, b-peterfalvi)**: ✅ **`alpha` 定義 + `CF(W,V)` membership DONE** (commit `c0b93e3e`, full AxiomsCheck 3557 green, axiom-clean, 7 guard 登録)。`Vdiff = ↑W∖(↑W₁∪↑W₂)` + `mem_Vdiff`; `alphaCF χ₁ χ₂ := (1−χ₁∘wFst)·(1−χ₂∘wSnd)` を **直接 `ClassFunction ↥W ℂ` として構成** (W abelian ⟹ conj-invariance free; **`ClassFunction.lean` に pointwise-Mul instance を足さず**共有ファイル不変); `alphaCF_apply` + kill `alphaCF_eq_zero_of_mem_W1/W2_subgroupOf`; `alphaCF_mem_supportedSubmodule` (hVeq 下, 積形状で W₁∪W₂ 上消滅) + bundled `alpha : SupportedOnV ℂ hyp` + `alpha_coe`。**設計メモ (再調査不要)**: ClassFunction に乗法構造は無く、共有 RepresentationTheory ファイルは触らない方針ゆえ α は明示関数で構成 (omega 経由でなく)。**次 = CF 次元インフラ `dim CF(W,V)=|V|=(w₁−1)(w₂−1)`** (abelian W ⟹ ClassFunction=点上関数, supportedSubmodule 次元=|V|; repo/mathlib に supported 版 finrank 直接 API 無し=新規; `|V|=|W|−w₁−w₂+1`) → lin-indep (Fourier: `sum_inner_irreducibleCharacter_smul`+`irreducibleCharacter_inner`, `a_ij=⟨∑a_kl α_kl, ω_ij⟩`; ここで α=1−ω_i0−ω_0j+ω_ij 展開 = alphaCF↔omega 接続が要る) → basis 組立。

**進捗 (session 10 cont., b-peterfalvi)**: ✅ **`dim CF(W,V) = (w₁−1)(w₂−1)` DONE** (commits `c56bd677` + `402da910`, full AxiomsCheck 3557 green, axiom-clean, 7 guard)。(a) 🔴 infra gap 解決 = **`finrank_supportedSubmodule_eq_card`** (一般 finite commutative `H`, `A⊆H`: `finrank ℂ (supportedSubmodule A)=|A|`; restrict/extend-by-zero で `CF(H,A)≃ₗ(↥A→ℂ)`, `LinearEquiv.ofBijective`; **共有 ClassFunction.lean 不変**, S05 に一般補題として配置)。(b) count = `supportInVdiffEquiv` (`V≃(W₁\1)×(W₂\1)` via `wProdEquiv`) + `card_supportInSubgroup_Vdiff` (`|V|=(w₁−1)(w₂−1)`) + helpers (`wFst/wSnd_wProdEquiv`, `eq_wFst_mul_wSnd`, `mem_W1/W2_subgroupOf_iff_wSnd/wFst_eq_one` = kill facts の逆向き iff)。(c) 結合 = **`finrank_supportedOnV (hVeq)`** = `(w₁−1)(w₂−1)` (= `Nat.card hyp.W1/W2 − 1` の積)。**⟹ (3.4) の次元 input 完成**。**次 leaf = (3.4) 線形独立 → basis 組立**: (i) `alphaCF = omega 1 − omega(χ₁∘wFst) − omega(χ₂∘wSnd) + omega((χ₁∘wFst)*(χ₂∘wSnd))` 展開 (ClassFunction.ext + omega_apply, ω_ij=omega の積 hom 版); (ii) omega 直交性 (`irreducibleCharacter_inner` を omega に, distinct linear char ⟹ orthonormal); (iii) `⟨∑a_kl α_kl, ω_ij⟩=a_ij` (i,j≥1 で ⟨α_kl,ω_ij⟩=δ); (iv) index 集合 `{χ₁≠1}×{χ₂≠1}` の濃度 = (w₁−1)(w₂−1) (Pontryagin `|Ŵ_k'|=w_k`); (v) lin-indep 族 size=finrank ⟹ basis (`basisOfLinearIndependentOfCardEqFinrank` 等)。**その後 (3.5) HARD core で loop 再停止**。

**進捗 (session 10 cont.², b-peterfalvi)**: ✅ **lin-indep foundations (i)+(ii) DONE** (commit `d0537536`, AxiomsCheck 3557 green, 3 guard)。(i) **`alphaCF_eq_omega_combination`** = `omega 1 − omega(χ₁∘wFst) − omega(χ₂∘wSnd) + omega((χ₁∘wFst)*(χ₂∘wSnd))` (ClassFunction.ext + simp[alphaCF_apply, omega_apply, MonoidHom.{comp,one,mul}_apply, Units.val_*] + ring; ω_ij = omega(積 in Hom(W,ℂˣ)))。(ii) **`omega_inner_self`/`omega_inner_ne`** (`irreducibleCharacter_inner`+`omega_injective`; **`if χ=χ'` 形は hom の DecidableEq 不在ゆえ self/ne 2 補題に分割**; 両者 **`[Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]` binder 必須** ∵ `ClassFunction.inner` が statement で要求 — file 規約 `FullDadeApplication` と同形)。**残 = (iii)-(v)**: **(iii)** `⟨alpha q₁ q₂, omega(p₁∘wFst·p₂∘wSnd)⟩ = if (p₁,p₂)=(q₁,q₂) then 1 else 0` (alpha_coe→expansion→inner 線形性→omega_inner_self/ne)。**要 character-group separation facts** (再調査不要、session 10 で特定): (A) `p₁∘wFst·p₂∘wSnd ≠ 1` (p₁≠1∨p₂≠1); (B) `q₁∘wFst ≠ p₁∘wFst·p₂∘wSnd` (p₂≠1; LHS W₂-trivial vs RHS W₂-nontrivial); (C) dual (p₁≠1); (D) `q₁∘wFst·q₂∘wSnd = p₁∘wFst·p₂∘wSnd ↔ q₁=p₁∧q₂=p₂` (= 双対 wProdEquiv の単射性)。**鍵 = `χ∘wFst` の W₂-triviality と単射性**: `wFst (incl_W₁' w) = w`, `wSnd (incl_W₁' w) = 1` (∵ wProdEquiv.symm (incl w)=(w,1)) ⟹ `χ₁∘wFst` を W₁' に制限すると χ₁ 復元 ⟹ `(χ₁,χ₂)↦χ₁∘wFst·χ₂∘wSnd` 単射 (= 双対 `Ŵ₁'×Ŵ₂'≃Ŵ`)。**(iv)** index `{χ:Ŵ₁'//χ≠1}×{χ:Ŵ₂'//χ≠1}` 濃度 = (w₁−1)(w₂−1): Pontryagin `Nat.card (Ŵ_k')=Nat.card W_k'` (有限 abelian 自己双対; mathlib `MonoidHom … ℂˣ` の card か `Module.Dual`/`CharacterModule`? 要 leansearch) − 1 の積。**(v)** lin-indep (`LinearIndependent.of_pairwise_dual_eq_zero_one` パターン= `linearIndependent_irreducibleCharacter` (CharacterCount:91) と同型, dual family = `innerDual (omega(p₁∘wFst·p₂∘wSnd))`) → size=finrank=`finrank_supportedOnV` ⟹ `basisOfLinearIndependentOfCardEqFinrank`。**⚠ alpha は `SupportedOnV` 元なので inner は CF(W) の inner に降ろす要** (`alpha_coe` で alphaCF に, supported submodule の inner = ambient inner)。**その後 (3.5) HARD core で loop 再停止**。

**進捗 (session 10 cont.³, b-peterfalvi) — ✅✅ (3.4) COMPLETE**: (iii)-(v) 全着地 (commits `cd918c46` separation+Fourier, `973f4759` basis; full AxiomsCheck 3557 green, axiom-clean, 計 8 guard)。
- **(iii) Fourier 係数** = `alpha_inner_omega_self`(=1)/`alpha_inner_omega_ne`(=0) (`if` 形は pair の DecidableEq 不在ゆえ self/ne 分割)。separation infra: `wFst/wSnd_W1/W2_subtype` (incl 上の簡約; **@[simp] 外す** ∵ `wFst_apply` @[simp] と競合) + **`comp_mul_injective`** (双対 `(χ₁,χ₂)↦χ₁∘wFst·χ₂∘wSnd` 単射, subtype 合成で復元; `simp only` で `wFst_apply` 回避) + `omegaProdChar`(=ω_ij, **noncomputable**)+恒等式(one_left/right/one)+`omegaProdChar_inj`+非一致 helper 4 個。**⚠ inner 線形性補題は `ClassFunction.inner_{add,sub}_left` と修飾必須** (無修飾は mathlib 汎用 `Inner` 型クラス版を拾う)。
- **(iv) Pontryagin** = `card_charGroup_subgroupOf : Nat.card ((H.subgroupOf W)→*ℂˣ) = Nat.card H` (H≤W, H cyclic via `Subgroup.isCyclic`)。**鍵 = `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`** (Mathlib.GroupTheory.FiniteAbelian.Duality) + `IsCyclic.commGroup` (letI) + `IsSepClosed.hasEnoughRootsOfUnity` (ℂ alg-closed; `NeZero ((exponent:ℂ))` via `neZero_exponent_of_finite`+`Nat.cast_ne_zero`)。**instance mismatch 回避 = `have key := by letI CommGroup; exact ...`** (exact は defeq 許容)。`Finite (Ŵ')` は inferInstance 可。
- **(v) basis** = `alphaLinearIndependent` (`LinearIndependent.of_pairwise_dual_eq_zero_one`, dual = `(innerDual (omega (omegaProdChar p))).comp (Submodule.subtype _)`; p≠q→¬(値一致) bridge = `Prod.ext∘Subtype.ext`) + `nonempty_charNeOne` (Pontryagin card>1→`Nontrivial`→`exists_ne 1`) + **`alphaBasis`** (`basisOfLinearIndependentOfCardEqFinrank`; **`Basis`→`Module.Basis` リネーム注意**; `Fintype (Ŵ')` ambient instance も haveI 要)。imports 追加: Duality / AlgebraicallyClosed / FiniteDimensional.Lemmas (full build 不変)。
**⟹ §5 (3.4) 完全形式化。** **次 = (3.5) HARD core (loop 停止点; multi-session 級)**: (3.5.1)-(3.5.5)、Ind_W^G α_ij の β_ij 分解、w₁≥5、A_ij 3元集合 case I/II 排除。**(3.5) は Dade induction `Ind_W^G` + §3/§4 機械を要し本質的に hard — 別セッションで設計から。**
2. **(3.4) α_ij basis** of CF(W,V), V=W−(W₁∪W₂)。α_ij=(1−ω_i0)(1−ω_0j)、dim=(w₁−1)(w₂−1)。線形独立 + 次元一致。**✅✅ COMPLETE (session 10): `alphaBasis` (α定義/membership/dim/lin-indep/basis 全部)。**
3. **(3.5) χ_ij 直交族 [HARD]**。(3.5.1) inner-product relations → (3.5.2) |A₁₁∩A₁₂|=1 → (3.5.4) ∩A_i1 → (3.5.5) decomposition。w₁≥5 仮定、A_ij=3 元 ±Irr 集合の case I/II 排除。abstract combinatorial lemma に切り出すと再利用しやすい。
4. **(3.2) σ-isometry** assembly ((3.5)+(1.3)→(3.2.a-d))。
5. **(3.6)Hyp + (3.7)/(3.8) NC(ψ)**。(3.7) は supported α との内積で linear identity、(3.8) は NC<2w₁ の 3-case 排除 (counting)。
6. **(3.9) Galois** ((1.9) field-automorphism 要 — S03/mathlib `Qbar`/cyclotomic で要確認)。
7. **(4.3) μ_ij [HARD,山場]** → **(4.4)/(4.5)/(4.7)/(4.8)** → **(4.9) [CB4 target]** → **(4.10)**。
8. **CB4 wiring**: (4.9) を (6.8.2) に。**CB5/CB6** は session-8 plan のまま。

### 改訂見積もり
verdict の 18-22h は §5 (3.x) を見落とし過少。Brauer free を差し引いても **§5+§6 で ~30-40h** (hard core ×2)。FT critical path 外だが §12/§13/§15 も (4.x) 消費ゆえ full-Pf completion の真ゲート。**正本 = 本ノート (本セクション); s08 blocker note の session-8 verdict は本訂正で superseded (Brauer 部分)。**

### 第一 leaf (3.3) の前提 (session 9 末で de-risk 済、再調査不要)
- **配置 = `S05_TICyclic.lean`** (results (3.x) の home, `namespace OddOrder.Peterfalvi.S05`)。
- **🔴 構造体ギャップ**: `S05.TICyclicHypothesis` (S05:37) は (3.1) の「W cyclic of odd order」を**欠く** —
  `W_card_odd` はあるが `W`/`W1`/`W2` の cyclic/abelian 仮説なし。ω_ij は linear character (deg 1) ゆえ
  (3.3) には **W abelian (cyclic) 必須**。⟹ `W1_cyclic : IsCyclic ↥W1` / `W2_cyclic : IsCyclic ↥W2`
  (W=W₁×W₂ coprime ⟹ W cyclic 導出) を**追加する**。
- **✅ field 追加は安全**: `TICyclicHypothesis` は repo 内で**一度も構築されていない** (`.mk`/`{W:=}` 0 件;
  参照は S05 自身の API と S15 docstring のみ)。consumer は `hyp : TICyclicHypothesis G` を取るだけ ⟹
  field 追加で既存 theorem は壊れない (full build で確認)。
- **構造体の `W_sup : W1⊔W2=W` + `W_disjoint` + coprime** ⟹ W=W₁×W₂ 内部直積。`W1_cyclic`+`W2_cyclic`
  追加で W cyclic (∴ abelian)。
- **⚠ 次セッション最初に scope すべき infra Q**: repo の `IrreducibleCharacter`/`ClassFunction` 枠組みで
  abelian 群の既約指標 = linear character (`MonoidHom ↥W ℂˣ` 相当) をどう表すか、Irr(W₁×W₂) の積分解
  API があるか (mathlib `MonoidHom (G×H) →` や character group の積)。これが (3.3) の工数を決める。
  まず `grep`/leansearch で確認してから書く。

---

## 2026-06-09 (session 11, b-peterfalvi): (3.5.1) COMPLETE + (3.2.a) bridge — new leaf file `S05_SigmaIsometry.lean`

(3.5) hard core 着手。新ファイル **`OddOrder/Peterfalvi/S05_SigmaIsometry.lean`** (imports `S05_TICyclic`、namespace `S05.TICyclicHypothesis` を再 open; 凍結 (3.1)-(3.4) は S05_TICyclic に残し active frontier を leaf に分離)。OddOrder root + AxiomsCheck 配線済、full AxiomsCheck 3558 green、全 axiom-clean。3 commits。

### ✅✅ 着地したもの (session 11)
1. **(3.5.1) Gram matrix** (commit `2e1fe55f`): `α_ij` の内積 `⟨α_ij,α_kl⟩ = 1 + δ_ik + δ_jl + δ_(ij)(kl)` (= 4/2/1) + 等長 `⟨Ind α_ij, Ind α_kl⟩` 同値 (`tau_alpha_inner`, `full_inner_eq` 経由)。
2. **(3.2.a) bridge `tau_eq_induce`** (commit `d75a38e1`): **§4 抽象 Dade carrier `app.tau` = 具体的 `Ind_W^G` on CF(W,V)**。`IsDadeMap.unique` + `induce ∈ IsDadeMap` で。これが Frobenius を解禁する鍵。
3. **(3.5.1) COMPLETE: β_ij** (commit `073b645e`): Frobenius `⟨Ind α_ij,1_G⟩=1` (`tau_alpha_inner_trivial`) + **`β_ij := Ind_W^G α_ij − 1_G`** の `beta_mem_ZIrr` / `beta_inner` (`⟨β,β'⟩=δ_ik+δ_jl+δ`) / `beta_inner_self`(=3) / `beta_inner_trivial`(=0)。

### 🔑 再利用可能な技術事実 (再調査不要)
- **omegaProdChar-uniform Gram 技法**: `α_ij` の 4 ラベル (`1, χ₁∘wFst, χ₂∘wSnd, χ₁∘wFst·χ₂∘wSnd`) を**全て `omegaProdChar (·,·)` 形に書く** (`alphaCF_eq_omegaProdChar_combination`) ⟹ ラベル一致が全て `omegaProdChar_inj`(成分一致)に帰着 ⟹ cross-type separation 補題不要。Gram の simp パターン: `simp only [inner_{sub,add}_{left,right}, omega_omegaProdChar_inner]` → `simp only [hp₁,hp₂,hq₁.symm,hq₂.symm, false_and, and_false, if_false, if_true, true_and, and_true]` → `ring`。`omega_omegaProdChar_inner : ⟨ω_b,ω_a⟩ = if (b₁=a₁∧b₂=a₂) then 1 else 0` (`open Classical in`)。
- **`tau_eq_induce`**: `(τ : S04.DadeIsometryData hyp.toDadeHypothesis)` を取る (DadeApplication.tau / FullDadeApplication.tau.toDadeIsometryData 両用)。`isDadeMap_inducedDadeMap` (= `induce` が IsDadeMap を満たす) が中身。**value half** = `induce_apply_eq_self_of_mem_V` ((3.2.c) on V; `{x: x⁻¹ax∈V}=W` を W_normalizes_V (⊇) + V_ti (⊆) で、`Σ_x induceTerm = |W|·α(a)`)、**support half** = `induce_eq_zero_of_not_conjugatesIntoSet` (dadeSupport=conjugatesOfSet V 経由)。k-general (CommRing k)。
- **Frobenius**: `inner_induce_eq_inner_restrict` (InducedCharacter:531, `⟨Ind θ,χ⟩=⟨θ,Res χ⟩`)。`1_G = trivialClassFunction G` (= `(trivialIrreducibleCharacter G : CF G)`); `Res_W 1_G = ω_00 = omega(omegaProdChar 1 1)` (`restrict_trivialClassFunction_eq`)。`⟨1_G,1_G⟩=1` = `inner_trivialClassFunction_self` (`irreducibleCharacter_inner` 対角)。
- **`inner_conj_symm`** (ZIrrFourier:147, **要 import** `OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier`; namespace = `OddOrder.RepresentationTheory.inner_conj_symm`, NOT `ClassFunction.`): `⟨ψ,φ⟩ = star ⟨φ,ψ⟩`。β pairwise の `⟨1_G, Ind⟩` 項に使用。
- **`α_ij ∈ ZIrr W`** = `alpha_mem_ZIrr` (`omega χ : IrreducibleCharacter W` ⟹ `.mem_ZIrr`、ZIrr submodule の add/sub 閉)。
- **gotchas**: `open Classical in` は docstring の**前**に置く (後置は parse error)。`if x ∈ W` を含む statement は `open Classical in` 必須。`[Fintype hyp.W]` を type で使わない補題は lint (`unusedFintypeInType`) ⟹ binder 外して `haveI : Fintype ↥W := Fintype.ofFinite _`。`FullDadeApplication.tau.toDadeMap` は abbrev ゆえ `rw [tau_eq_induce ..toDadeIsometryData..]` 前に `change ..toDadeIsometryData.toDadeMap..` 要。`show`→`change` (goal 変える場合)。

### ▶▶ 次 leaf = β_ij の norm-3 分解 (3.5.1 末) → (3.5.2)-(3.5.6) 組合せ論 [真の hard core]
**(3.5.1) の最後**: `β_ij ∈ ZIrr G`, `‖β_ij‖²=3`, `⟨β_ij,1_G⟩=0` から **`β_ij = Σ_{χ∈A_ij} χ`** (A_ij = 3 個の pairwise-orthogonal `±(Irr(G)∖{1})`)。これは「**norm² 3 + integer coeffs ⟹ 相異 3 個の ±irreducible**」の一般補題 (3 = 1+1+1 が唯一の平方和分解; `mem_ZIrr` の Fourier 係数 + `Σ n²=3`)。repo に既存の norm-小分解補題があるか要確認 (ZIrrFourier に `norm=2` 版 `..._norm..eq_2..` あり=line 529 付近; norm-3 は新規か拡張)。**この A_ij 集合の抽出が (3.5.2)-(3.5.6) 組合せ論の入口** — 真の multi-session hard core (case I/II 排除、w₁≥5、∩A_i1 等)。

**leaf 計画 (依存順)**:
1. ✅ (3.5.1) Gram + β (DONE session 11)
2. **norm-3 分解補題** (`β ∈ ZIrr ∧ ‖β‖²=3 ∧ ⟨β,1⟩=0 ⟹ ∃ 3 個の ±Irr∖{1} pairwise-orth, 和=β`)。抽象に切り出す (G レベル、TICyclic 非依存)。← 次セッション第一 leaf
3. (3.5.2) `|A₁₁∩A₁₂|=1` (β の `2χ=Ind(α-α)` が 1 で消える矛盾) → L(ij,i'j') / O(ij,i'j') notation
4. (3.5.4) `|∩A_i1|=1` (w₁≥5、case I/II 排除 — 最重)、(3.5.5) decomposition → χ_ij 族
5. (3.5.3-3.5.5) で `χ_ij ∈ ZIrr`, `χ_00=1_G`, `Ind α_ij = 1−χ_i0−χ_0j+χ_ij` 確立 = **(3.5) 完成**
6. (3.2) σ assembly: `ω_ij^σ := χ_ij`, linearity 拡張, (3.2.a-d) ((3.2.c)/(d) は (1.3))
7. (3.6)Hyp/(3.7)/(3.8) NC(ψ) → (3.9) Galois ((1.9)) → §6 (4.x)

正本 = 本ノート (session 11 セクション)。S05_SigmaIsometry.lean が (3.5)/(3.2)/(3.6)-(3.9) の home。

## 2026-06-09 (session 12, b-peterfalvi): (3.5.2) L/O + (3.5.3) + 固定族インフラ — 4 commits

(3.5) hard core の**組合せ論ツール層が完成**。すべて `S05_SigmaIsometry.lean`、sorry-free・axiom-clean・full AxiomsCheck green。次セッションは (3.5.4) 本体（sunflower）に集中できる。

### ✅ 着地 (session 12, 4 commits)
1. **signed-irreducible API** (S05 namespace, TICyclic 非依存・抽象):
   - `IsSignedNontrivialIrr.{apply_one_ne_zero, ne_zero, ne_neg_self, inner_self}`,
     `irreducibleCharacter_coe_ne_neg`, 三分法 `isSignedNontrivialIrr_inner`
     (`⟨x,c⟩ = 1/-1/0` ⟺ `x=c` / `x=-c` / else)。
   - **`IsSignedTriple β A` 構造体** (`[Invertible (Nat.card G : ℂ)]` を構造体束縛で持つ; β = 3 個の
     pairwise-orth signed nontrivial irr の和)。helper: `neg_not_mem`, `inner_right_signed`
     (`⟨β,c⟩ = [c∈A]-[-c∈A]`), `inner_self` (= |A|), `exists_isSignedTriple_of_inner_self_three`。
2. **(3.5.2) L補題** (commit `53799f92`):
   - `IsSignedTriple.no_neg_of_inner_one` (抽象): `⟨β,β'⟩=1 ∧ β(1)=β'(1) ⟹ ∀c∈A, -c∉A'`。
     **証明の核** = `δ := (β-β') - 2c` の `⟨δ,δ⟩=0` (正定値 `eq_zero_of_inner_self_re_eq_zero`)
     ⟹ `β-β'=2c` ⟹ `(β-β')(1)=2c(1)≠0`、しかし `β(1)=β'(1)` で 0 ⟹ 矛盾。
     (= 論文の「`2χ₃ = Ind(α₁₁-α₁₂)` が 1∈G で消える」。Cauchy-Schwarz も対称差も不要。)
   - `IsSignedTriple.L_of_inner_one`: + `|A∩A'| = ⟨β',β⟩ = 1`。
   - 値-at-1 供給: **`beta_apply_one`** (`β_ij(1)=-1`; `induce_apply_one` + `α_ij(1)=0` via
     `alphaCF_eq_zero_of_mem_W1_subgroupOf` (1∈W1.subgroupOf W))。
   - concrete: `beta_inner_eq_one_of_one_shared` + `betaTriple_L`。
3. **(3.5.2) O補題** (commit `1b04d612`):
   - `IsSignedTriple.O_card_inter_eq` (抽象): `⟨β,β'⟩=0 ⟹ |A∩A'| = |{x∈A : -x∈A'}|`。
     (`⟨β',β⟩ = |A∩A'| - |{x∈A:-x∈A'}| = ⟨β,β'⟩* = 0`。) downstream 用法: A,A' の共通元 ⟹ negated 共通元も。
   - concrete: `beta_inner_eq_zero_of_both_diff` + `betaTriple_O`。
4. **(3.5.3)** (commit `a17ebbde`): `sup_card_ge_five : 5 ≤ |W₁| ∨ 5 ≤ |W₂|`。
   両 odd (`Odd.of_dvd_nat` + `Subgroup.card_dvd_of_le`)・>1・coprime ⟹ 両≤4 なら両=3 ⟹ `¬Coprime 3 3`。
5. **固定族 A_ij** (commit `b0c8dcfd`): 論文が (3.5.1) 直後に固定する `A_ij`。index = 非自明 χ₁,χ₂ の subtype pair。
   - `Afam p q := (exists_isSignedTriple_beta ..).choose` (Classical.choose で一意固定)。
   - `Afam_isSignedTriple`, `Afam_L` (shared one index), `Afam_O` (both differ)。
   - 抽象 `IsSignedTriple.{L_of_inner_one, O_card_inter_eq}` を固定族に instantiate。

### 🔑 再利用可能な技術事実 (再調査不要)
- **`IsSignedTriple` 構造体は `[Invertible (Nat.card G : ℂ)]` を構造体束縛で持つ** (field `pairwise_orthogonal`
  が `ClassFunction.inner` を使うため)。使用側の補題は全て同 instance を持つので透過。
- **三分法 `isSignedNontrivialIrr_inner`**: 4-way `rcases hxχ with rfl|rfl <;> rcases hcψ with rfl|rfl`、
  各 case で `irr_cf_inner` + `irreducibleCharacter_coe_ne_neg` (X≠-Y は 1∈G で +d vs -d') + neg 操作
  (`inner_neg_left/right`, `neg_inj`, `neg_eq_iff_eq_neg`)。
- **L補題の value-at-1 核**: bilinear 展開を `simp only [inner_sub_left, inner_sub_right,
  inner_smul_left, inner_smul_right, ...]` で潰し `⟨δ,δ⟩=0`、`sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero (by rw[hzero]; exact Complex.zero_re))` で `β-β'=2•c`。`star (2:ℂ) = 2` は `by norm_num`。
- **`Finset.sum_boole` + `Finset.filter_mem_eq_inter`** で `Σ_{x∈A}(if x∈A' then 1 else 0) = |A∩A'|`。
- **O の対称性**: `⟨β',β⟩ = star ⟨β,β'⟩` (`inner_conj_symm β β'`); `star 0 = 0` (`star_zero`), `star 1 = 1` (`star_one`)。
- **`omit [Fintype G] in` は docstring の前**に置く (後置は parse error)。`open Classical in` も同様。
- `∩`/`filter` を含む statement は `open Classical in` 必須 (`DecidableEq (CF G ℂ)`)。

### ▶▶ 次 leaf = (3.5.4) `|⋂_i A_i1| = 1` [真の hard core, 多セッション]
**正本テキスト** = `references/peterfalvi/04.5_..._Cyclic_Normalizers.mmd` L59-107。

**構造** (≥4 行 × ≥2 列の signed-triple grid; 道具は全て揃った: `Afam_isSignedTriple/_L/_O`, `sup_card_ge_five`):
- **`⋂ ≤ 1` は易** (2 行の L で共通元一意)。**`⋂ ≠ ∅` が hard** (Cases I/II)。
- 「false ⟺ `⋂_i A_i1 = ∅`」(⋂≤1 なので |⋂|≠1 ⟺ ⋂=∅)。
- ⋂=∅ ⟹ 3 行が **triangle**: `β_11=χ1+χ2+χ3, β_21=χ1+χ4+χ5, β_31=χ2+χ4+χ6` (pairwise ∩ = {χ1},{χ2},{χ4} 相異)。
- **Case I** (A_41 が triangle の ∩点を含む, WLOG χ1∈A_41 ⟹ `β_41=χ1+χ6+χ7`): 補題 (3.5.4.1)〔χ1∈A_i2 ⟹ β_i2 の形〕,
  (3.5.4.2) `β_32=χ2-χ3+χ8`, (3.5.4.3) `β_12=χ2-χ4+χ5`, (3.5.4.4) `β_22=χ5+χ8+χ9`, (3.5.4.5) Case I 矛盾。
- **Case II** (A_41 が ∩点を含まない, `β_41=χ3+χ5+χ6`): (3.5.4.6) で `χ1∈A_12,−χ4∈A_12 ⟹ χ6∈A_12` が O(12,41) と矛盾。
- 各補題は L/O の連鎖 + membership 簿記。**WLOG/対称性が形式化の壁** (「β_21 と β_41 の対称性で -χ4∈A_12 と仮定」等)
  → 両 branch を証明 or 明示対称化が必要。faithful 形式化は ~400-600 行・複数セッション。
- **w₁≥5 の WLOG**: (3.5.4) は「≥4 非自明 χ₁ がある側」で証明 → 最終 assembly で `sup_card_ge_five` の
  `5≤|W₁| ∨ 5≤|W₂|` に応じて W₁/W₂ を swap (現状 `Afam_L/_O` は W₁↔W₂ 対称なので両側適用可)。

**(3.5.4) 後**: (3.5.5) decomposition (`-χ_01 := ⋂A_i1 の元`, `-χ_i0 := A_i1∩A_i2 の元`, `β_i1=-χ_i0-χ_01+φ_i`),
最終 assembly (`w₂=3` で完了 or `w₂≥5` で対称適用) → χ_ij 族 → (3.2) σ。

正本 = 本ノート (session 12 セクション)。

## 2026-06-09 (session 12 cont., b-peterfalvi): (3.5.4) 着手 — grid + 還元 + named-triangle + Case II

(3.5.4) `|⋂_i A_i1|=1` の sunflower 論法に着手。基盤 + Case II 完成。全て `S05_SigmaIsometry.lean`、sorry-free・axiom-clean・full AxiomsCheck green。3 commits (`97fc1c90`/`4fb2798b`/`aca41a24`)。

### ✅ 着地
1. **抽象 grid `IsSignedTripleGrid A`** (`97fc1c90`): row/col index `ι, κ` 上の signed-triple 族 + L/O 関係 (fields `card_eq_three`/`signed`/`orthogonal`/`inter_L`/`noNeg_L`/`inter_O`; `i i' j j'` は明示引数)。`Afam_isSignedTripleGrid` で β-族を instance 化。
   - `common_unique` (⋂≤1, 易) + `exists_triangle_of_not_exists_common` (¬∃common ⟹ 3 行 no-common; 「全 triple が共通元 ⟹ e₁₂ 一意性で ⋂≠∅」の対偶) + `neg_not_mem_self`。
2. **named-triangle `exists_namedTriangle`** (`4fb2798b`): 3 行 no-common ⟹ vertices e₁₂,e₁₃,e₂₃ (相異) + thirds t₁,t₂,t₃ + 3 集合等式 (`A i₁ j₀={e₁₂,e₁₃,t₁}` 等)。汎用 Finset 補助 `exists_third_of_card_three`。
3. **Case II `caseII_false`** (`aca41a24`): K₄ config (4 行目 `A i₄ j₀={χ3,χ5,χ6}`=thirds) ⟹ False。**🔑 パリティ論法 (WLOG 不要)**: `B=A i₁ j₁`、`n_k=[χ_k∈B]`,`p_k=[-χ_k∈B]`。L(i₁,i₁)⟹`n₁+n₂+n₃=1,p₁=p₂=p₃=0`; O(i₁,i_p) p=2,3,4 ⟹ 3 式; **3 式を足すと `1+2(n₄+n₅+n₆)=2(p₄+p₅+p₆)` = 奇=偶**、`omega`。論文 (3.5.4.6) の場合分けを 1 つの parity で置換。
   - 翻訳補助 `card_inter_triple` (`|s∩{a,b,c}|`=指標和, distinct a,b,c) + `card_filter_neg_triple` (filter 版, `-x∈{a,b,c}↔x∈{-a,-b,-c}`) + `triple_distinct` (card 3 ⟹ pairwise 相異)。

### 🔑 再利用可能 (再調査不要)
- **Case II の omega 帰着**: card 関係を指標和に翻訳 (`card_inter_triple`/`card_filter_neg_triple`、要 per-triple distinctness、cross-distinctness 不要) → `set n_k,p_k` で if を atom 化 (omega が ite split しないため必須) → `p₁=p₂=p₃=0` を noNeg から → omega (parity)。
- mathlib v4.30 名: `Finset.card_insert_of_notMem` (notMem!), `Finset.notMem_singleton`, `Finset.card_sdiff_of_subset` (部分群版; `card_sdiff` は ∩ 版で引数取らない), `Finset.card_pair` は不可→`card_insert_of_notMem`+`card_singleton`。
- `{χ..}` Finset 表記を含む文/補題は `open scoped Classical in` 必須 (DecidableEq)。

### ▶▶ 残り (3.5.4) = Case I + assembly [次セッション, hard]
- **Case I** (4 行目が三角形の頂点を含む, 例 `A i₄ j₀={χ1,χ6,χ7}`, χ7 新): **単一集合 B₁ counting は FEASIBLE** (`B₁={χ1,-χ5,-χ7}` が L+O 全部満たす, parity 不成立) ⟹ **マルチセット要素追跡が本質**。論文 3.5.4.1-5 は B₁,B₂,B₃,B₄ (=A_{i_p j₁}) を使い χ8(∈B₃),χ9(∈B₂) を命名して追う + WLOG (3.5.4.2/3)。**counting/omega は列 j₁ 同士の `B_p∩B_q` が固定元上でない (B_q が未知 3-集合) ため直接効かない** ⟹ B の新元素を named で追う必要。WLOG=「どの頂点 χ1/χ2/χ4 が A_{i₄} に入るか」(i₁i₂i₃ 対称) + 3.5.4.2/3 の選択。**multi-session 級。**
- **assembly `exists_common`**: triangle + 4 行目で `by_cases` (A_{i₄} が頂点を含むか) → Case I / Case II 適用 → ⋂≠∅ ⟹ `∃! z,∀i z∈A i j₀` (+ common_unique)。Case I の「どの頂点」WLOG を assembly で処理 (3 頂点対称、caseI_false を相応の relabel で適用 or 対称版で陳述)。
- その後: (3.5.5) decomposition → 最終 (3.5) → (3.2)σ。
- **w₁≥5 WLOG**: (3.5.4) を `4≤Fintype.card ι` 仮説で証明済設計 (ι=非自明χ₁); `sup_card_ge_five` の disjunction で W₁/W₂ 側を選ぶ (assembly/§3.5 末)。

正本 = 本ノート (session 12 cont. セクション)。

## 2026-06-09 (session 13, b-peterfalvi): (3.5.4) COMPLETE — sunflower `|⋂_i A_{i1}|=1` 完成 [真のボトルネック解除]

**hard core (3.5.4) を 1 セッションで完全形式化。** メモリが「真のボトルネック・multi-session 級・~400-600 行」と記した部分。すべて `S05_SigmaIsometry.lean`、sorry-free・axiom-clean・full AxiomsCheck green (3558 jobs)。6 commits (`0d02c134`/`99c62c80`/`ee9dbe42`/`646b0627`/`b38adc35`/`88692770`)。

### ✅ 着地 (session 13)
1. **L/O membership-deduction ヘルパー層** (`0d02c134`): abstract grid の `inter_L`/`noNeg_L`/`inter_O` フィールドを membership 演繹に変換。
   - `ne_neg_of_Llinked` (L-linked 2 cell の元は互いに負でない) / `eq_of_mem_Llinked` (共有元一意)。
   - **`oStep`** (核エンジン): `{χ,u,v}` が `B∋χ` と O 関係 (`-χ∉B`) ⟹ `u,v∉B` かつ `-u,-v` の**ちょうど一方**が B (`-u∈B ↔ -v∉B`)。
   - `lStep` (L 版: u,v∉B + 負も∉)、`oStep_out` (全員 out ⟹ 負も out)、`oStep_force` (`-x∈B`⟹z∈B)、`oStep_both_out` (新元素の cell 単位 newness)、`lStep_third` (L で z∈B)、`not_two_shared`、`not_disjoint_Llinked` (disjoint triple ⊥ L)、`cell_eq_triple`、`ne_neg_of_mem_same`。
2. **(3.5.4.1) `pencilCell`** (`0d02c134`): `χ∈A ra j₁ ⟹ A ra j₁={χ,-fb,-fc}`。**🔑 論文より clean**: 横断線 (transversal) の O 関係が**両 meet-point の負を一度に殺す** (`oStep_out`) ので、論文の「-χ₄ 仮定→χ₆→O(12,41) 矛盾」の迂回が不要。
3. **(3.5.4.2) `transversalCell`** (`99c62c80`): 横断 cell が meet `ma` を共有 ⟹ `A rt j₁={ma,-fa,χ8}`、χ8 新 (χ,fb,fc,-fb,-fc,-mb,-mc と相異)。`-fa` (not `-χ`) は「`-χ∈B` だと両 free `fb,fc∈B` (各 oStep_force) だが空きは 1 枠 ⟹ fb=fc 矛盾」で確定。χ8-newness は `oStep_both_out` の 7 連発。
4. **(3.5.4.4)-(3.5.4.5) endgame `caseI_tail`** (`ee9dbe42`): 役割固定 (ra=special/rb=active/rc=passive)。`B₁={ma,-mb,fb}`+`B₃={ma,-fa,χ8}` ⟹ False。(3.5.4.4) で `fb,χ8∈B₂`; (3.5.4.5) で `χ8∈B₄`→`-mb∈B₄`→`O(B₄,A rb j₀)` が `mb∈B₄` 強制で矛盾。**🔑 論文に無い明示化**: `-χ∉B₄` は**同じ行の noNeg_L** (χ∈A rc j₀) から自明 — これが論文「O(42,11)⟹χ₂∧-χ₃」の根拠。距離 bookkeeping は局所 `hnn` (任意の col-j₀ 名前付き元は互いに非負) + `hcross` (異 pencil 行の非 apex 元は相異) で圧縮。
5. **(3.5.4.3)+glue `caseI_special`** (`646b0627`): transversalCell→caseI_tail を接続。B₁ 確定 (χ∉B₁ via pencilCell⊥B₃; fa∉B₁ via noNeg(B₃,B₁); ma∈B₁; O で `-mb`/`-mc` のちょうど一方) → active 行を `by_cases` で命名 → 各枝 `oStep_force` で `B₁={ma,-m_act,f_act}` → caseI_tail (b↔c 対称を 2 呼び出しで処理)。**⚠ 性能**: cell 並べ替えは `Finset.insert_comm`/`pair_comm` で (旧 `ext;simp;tauto` は passive 枝でヒープ超過)。
6. **(3.5.4) `caseI_false` + assembly `exists_common` + capstone `existsUnique_common`** (`b38adc35`): 横断 cell が ma/mb/mc のどれを共有か rcases→caseI_special (pencil 3 行対称); assembly は triangle 抽出→4 行目→頂点 3 ケース [Case I] + 頂点なし [Case II→caseII_false]→`∃! z,∀i z∈A i j₀`。

### 🔑 再利用可能な技術事実 (再調査不要)
- **abstract `IsSignedTripleGrid` で (3.5.4) を完全に閉じた** — TICyclic 非依存。`existsUnique_common (hι:4≤card ι)(hjne:j₀≠j₁) : ∃! z,∀i z∈A i j₀`。Afam への instantiate は `Afam_isSignedTripleGrid` + w₁≥5 WLOG で (次セッション)。
- **距離 bookkeeping 圧縮レシピ**: `hnn : ∀{r s x y}, x∈A r j₀→y∈A s j₀→x≠-y` (by_cases r=s で ne_neg_of_mem_same / ne_neg_of_Llinked) + `hcross : r≠s→χ∈A r→χ∈A s→x∈A r→y∈A s→x≠χ→x≠y` (eq_of_mem_Llinked)。± 符号組合せは: `+x≠+y`=hcross/triple, `+x≠-y`=hnn, `-x≠+y`=(hnn y x).symm, `-x≠-y`=neg_injective.ne。
- **`simp not_or` 由来の `h:¬(a=b)` は `Ne` ヘッドでなく `Not` ⟹ `h.symm` 不可** → `Ne.symm h` を使う (defeq だが dot-notation が Function.symm を探す)。
- **大証明のヒープ**: 巨大 theorem を多数 `exact` する証明 + `tauto` 並べ替えはヒープ超過し得る。Finset 並べ替えは `insert_comm`/`pair_comm` を使う。
- mmd の (3.5.4.1)-(3.5.4.6) は faithful に再現したが、(3.5.4.1) は transversal-O で、Case II は単一 parity で簡略化。

### ▶▶ 次 = (3.5.5) decomposition → Afam 接続 → (3.5) 完成 → (3.2) σ
- **(3.5.5)**: `-χ_01 := ⋂A_i1 の元` (existsUnique_common で取得)、`-χ_02 := ⋂A_i2 の元`、`-χ_i0 := A_i1∩A_i2 の元`、`β_i1=-χ_i0-χ_01+φ_i`/`β_i2=-χ_i0-χ_02+ψ_i`、(φ_i)(ψ_i) 正規直交族で φ⊥ψ (i≠i')。mmd L97-107。
- **Afam 接続 (w₁≥5 WLOG)**: abstract `existsUnique_common` を `Afam_isSignedTripleGrid` に instantiate。ι=非自明χ₁ (card=w₁-1)、κ=非自明χ₂ (card=w₂-1)。`4≤card ι` は w₁≥5、`∃j₁≠j₀` は w₂≥3 (常成立)。`sup_card_ge_five` で w₁≥5∨w₂≥5、≥5 側を rows に取る (Afam は W₁↔W₂ 対称)。
- **w₂=3 で (3.5) 完了、w₂≥5 で W₁↔W₂ 適用** (mmd 末)。→ χ_ij 族確立 → (3.2) σ-isometry → (3.6)-(3.9)。
- まだ hard core ×1 = (4.3) が残る (§6 定理本体)。FT 経路外。

正本 = 本ノート (session 13 セクション)。

## 2026-06-09 (session 13 cont., b-peterfalvi): (3.5.5) core + transpose + Afam 接続 — 抽象結果を実 β-族で活性化

(3.5.4) 完成後、3 commits 追加 (`989a27af`/`4f7bb2e5`/`ea4fc3e4`)。全 axiom-clean・AxiomsCheck 3558 green。

### ✅ 着地
1. **(3.5.5) core `common_not_mem_other_column`** (`989a27af`): 列 j₀ の共通元 z は他列に直交 (`z∉A r j₁ ∧ -z∉A r j₁`)。論文「χ₀₁ は A_{i2} に直交」。**証明 (w₁≥5 counting)**: `±z∈A r j₁` なら各 i≠r (≥3 行) に対し O(r j₁, i j₀) (両辺相等、±z が片側を打つ) が A r j₁ の z と相異な witness を強制 → 相異 (共有なら共通 z) → ≥4 行が 3-元 cell に単射 → 矛盾。内部 engine = 単射 ι→A r j₁ で card ≤3。
2. **`IsSignedTripleGrid.transpose`** (`4f7bb2e5`): grid の row↔col 転置も grid (L/O 条件は対称)。**W₁↔W₂ interchange (WLOG w₁≥5) を可能に**: w₂≥5 のみのとき転置 Afam grid に row-indexed 結果を適用。
3. **Afam 接続 `Afam_existsUnique_common`** (`ea4fc3e4`): **抽象 sunflower を実 β-族で活性化**。w₁≥5 orientation で `∃! z=-χ₀₁, ∀χ₁(≠1) z∈A_{χ₁ χ₂₀}`。`≥4 行` は `|Irr(W₁')∖{1}|=|W₁|-1` (`Fintype.card_subtype_compl`/`_eq` + Pontryagin `card_charGroup_subgroupOf`) + |W₁|≥5。

### 🔑 再利用 (再調査不要)
- **Afam 接続レシピ**: `haveI:Finite G:=Finite.of_fintype G; haveI:Fintype(charGroup):=Fintype.ofFinite _; Fintype.card{χ//≠1}=Nat.card W_k-1` via `[Fintype.card_subtype_compl, Fintype.card_subtype_eq, ←Nat.card_eq_fintype_card, card_charGroup_subgroupOf hyp.W_k_le_W]`; 適用は `(hyp.Afam_isSignedTripleGrid hVeq app).existsUnique_common hcard hne` (dot-notation)。
- `card_charGroup_subgroupOf hyp (hHW:H≤W) : Nat.card((H.subgroupOf W)→*ℂˣ)=Nat.card H` (S05_TICyclic:844, Pontryagin)。
- `common_not_mem_other_column` 内 engine の単射: `choose!` で total witness Y → `insert w (image Y (univ.erase r)) ⊆ A r j₁` + card 計算 (`card_insert_of_notMem`+`card_image_of_injOn`+`card_erase_of_mem`+`Nat.sub_add_cancel`) で card ι ≤ 3 矛盾。

### ▶▶ 次 = (3.5.5) full decomposition → (3.5) 最終 → (3.2) σ
- **(3.5.5) decomposition (残)**: 各行 i で `A_{i,j₀}={-χ₀₁, -χ_{i0}, φ_i}` (`-χ₀₁`=列共通, `-χ_{i0}`=A_{i,j₀}∩A_{i,j₁} 元 [同行 L], `φ_i`=第3元)。`-χ₀₁≠-χ_{i0}` は `common_not_mem` から (後者∈A_{i,j₁}, 前者∉)。φ_i 正規直交族 + φ_i⊥ψ_{i'} (L/O から)。抽象 grid で記述可。
- **Afam 用 common_not_mem 接続**: `common_not_mem_other_column` も Afam に instantiate (transpose 付き)。
- **(3.5) 最終 assembly**: w₂=3 完了 / w₂≥5 で transpose 適用 → χ_ij 族 → (3.2) σ-isometry → (3.6)-(3.9)。
- 残 hard core ×1=(4.3)§6本体 (FT経路外)。

正本 = 本ノート (session 13 / session 13 cont.)。**Don't re-grind (3.5.4)/(3.5.5)-core/transpose/Afam接続 — 完成・axiom-clean.**

## 2026-06-09 (session 14, b-peterfalvi): (3.5.5) 抽象直交性 両レジーム COMPLETE — abstract grid の χ_ij 族正規直交性

(3.5.5) の組合せ論的核心 = **「z_j (列共通)・row-anchor・φ_ij (第3元) から成る族が正規直交」** を抽象 `IsSignedTripleGrid` 上で完全形式化。w₂≥5 (対称) と w₂=3 (2列) の両レジーム。全 `S05_SigmaIsometry.lean`、sorry-free・axiom-clean・full build 3558 + AxiomsCheck green。2 commits (`869c2a87` w₂≥5 backbone, `42b844b4` w₂=3 + DRY refactor)。

### ✅ 着地 (session 14)
1. **構造プリミティブ** (`869c2a87`):
   - `cell_decomposition`: 2列 行分解 `A i j₀ = {z₀, m_i, φ_i}` (z₀=列共通 via existsUnique_common, m_i=同行 meet A i j₀∩A i j₁, φ_i=第3元); `z₀≠m_i` は `common_not_mem_other_column` から。
   - `common_ne_other_column_mem`: **列共通元は他列の任意の元と直交** (≠, ≠-neg) — χ_0j 直交性の workhorse。
   - `symm_cell_decomposition`: w₂≥5 対称分解 `A i j = {z j, w i, φ}` (列共通 z j + 行共通 w i 両方)。
   - `third_not_mem_far_cell`: O(ij,kl) — far な内部 third が相互直交 (`oStep_both_out` + `transpose` で行側)。
   - `common_ne_other_row_mem`: 列版の transpose ラッパー (行共通元の直交性)。
   - `orthonormal_of_injective_of_no_neg`: **signed 族が injective ∧ no-neg ⟹ 正規直交** (diagonal 1, off-diag 0; `if a=b` を避け `DecidableEq` instance 問題を回避)。
2. **DRY 汎用組立** (`42b844b4`):
   - `symmFamily` → **`gridFamily {γ}`** (row-anchor m, col-anchor z (一般 γ), 内部 φ; index `ι ⊕ γ ⊕ ι×γ`)。
   - **`gridFamily_orthonormal`**: 6 つの atomic 関係 (Rmm/Rzz/Rzm/Rzφ/Rmφ/Rφφ) + signedness から正規直交を組立。**w₂≥5 と w₂=3 で共有** (差は row-anchor 関係 Rmm/Rmφ の証明法のみ)。3×3 case 分析 (injective + no-neg) はここに集約。
   - **`symm_orthonormal_family`** (w₂≥5): row-anchor=行共通、`common_ne_other_row_mem`/`third_not_mem_far_cell` で関係を作り gridFamily_orthonormal へ。
   - **`two_col_orthonormal_family`** (w₂=3): γ=Bool、row-anchor=行 meet `m_i∈A i (j false)∩A i (j true)`; meet は2参照列のみに居るので関係は L (meet≠列共通) と O (`oStep_both_out`) から (行共通でない)。論文が (3.5.5) 後「proof complete」と呼ぶケース。

### 🔑 再利用可能 (再調査不要)
- **正規直交 = injective + no-neg** (signed 族): `orthonormal_of_injective_of_no_neg` で内積に変換。組立は `gridFamily_orthonormal` (6 関係を渡すだけ)。新しい grid 族の正規直交はこの2つで即座。
- **row-anchor の2流儀**: 行共通 (w₂≥5, `common_ne_other_row_mem`=transpose) vs 行meet (w₂=3, L+O 手動)。両方 `gridFamily_orthonormal` の Rmm/Rmφ に詰める。
- **`gridFamily` の `cond b ψt ψf`** (γ=Bool の φ): `cases b` で defeq 簡約 (simp 不要)。
- **`if a=b` 出力**: `gridFamily_orthonormal` は diag/off-diag 連言を返す→使用側で `split_ifs` で `if` 形に (DecidableEq instance mismatch 回避)。

### ✅ 着地 (session 14 cont.): 具体 foundations + commons 抽出
2 commits 追加 (`86a36fdd` foundations, `c376cf8e` commons)。
- **signed-irr foundations** (`86a36fdd`): `IsSignedNontrivialIrr.mem_ZIrr` (x=±χ∈ZIrr) + `.inner_trivial` (⟨x,1_G⟩=0)。`inner_trivialClassFunction_self`(既存) と併せ「χ族 + 1_G」正規直交の具体 prep 完成 (これ以上抽象 prep 不要)。
- **commons 抽出** (`c376cf8e`): `exists_colCommon` (w₁≥5: `∃ z:Ĉ₂ⁿᵉ→CF, ∀q p, z q∈Afam p q` via existsUnique_common) + `exists_rowCommon` (w₂≥5: `∃ w:Ĉ₁ⁿᵉ→CF, ∀p q, w p∈Afam p q` via **transpose** grid の existsUnique_common — W₁↔W₂ 橋渡し検証済)。card 補題: Nontrivial Ĉ_kⁿᵉ (card W_k≥3 from odd+>1)、4≤card Ĉ₂ⁿᵉ (w₂≥5)。symm/two_col の z/w 入力が揃った。

### ▶▶ 次 = χ-assembly (3.5) → orientation wrapper → (3.2) σ [次セッション]
**残りは具体 plumbing。入力 (commons + 抽象正規直交 symm/two_col) 全て準備済。**

**χ-assembly (w₁≥5 前提)**: χ : Ĉ₁×Ĉ₂ → CF を 4-case で:
- (1,1)↦1_G, (p,1)[p≠1]↦-(row-anchor⟨p⟩), (1,q)[q≠1]↦-(col-common⟨q⟩), (p,q)[both≠1]↦third⟨p⟩⟨q⟩。
- 出力 (3.5): χ(1,1)=1_G ∧ ∀pq χ pq∈ZIrr ∧ 正規直交 ∧ **Ind α_pq = 1_G - χ(p,1) - χ(1,q) + χ(p,q)** (= β_pq=Σ_{Afam p q}=col+row+third via IsSignedTriple.sum_eq + cell {z,m,φ})。
- 正規直交: 16-case (p,q,p',q' の trivial 判定) を `inner_trivial`/`inner_trivialClassFunction_self`/hortho (symm or two_col の `⟨gridFamily a,gridFamily b⟩=if a=b`) + 符号 (inner_neg) で。

**🛑 設計論点 (次セッション最初に解決)**: symm は gridFamily を **γ=κ (=Ĉ₂ⁿᵉ)** で、two_col は **γ=Bool** で出力 (列 index 型が違う)。χ-over-Ĉ₁×Ĉ₂ は列 index=Ĉ₂ⁿᵉ を要す。
- w₂≥5: symm の κ=Ĉ₂ⁿᵉ で直接 OK。
- w₂=3: two_col の j:Bool→κ は card κ=2 ゆえ全単射。χ の列 q∈Ĉ₂ⁿᵉ を `q=j(false) or j(true)` で case 分けして two_col の Bool-φ に橋渡し (j 全単射の bookkeeping)。または two_col を「card κ=2 のとき γ=κ で出力」する補題に reindex (gridFamily の Bool↔κ 移送、~20行)。**推奨 = χ-assembly 内で q→Bool case 分け (reindex 補題より局所的)。**

**orientation wrapper (w₁<5 ⟹ w₁=3∧w₂≥5)**: colCommon が w₁≥5 を要すので、w₁<5 では **transpose grid (W₂ を rows, w₂≥5⟹≥4 rows)** で χ-assembly を回し、結果を transpose back (α_ij は W₁↔W₂ 対称、ω_ij も swap+transpose で対応)。`sup_card_ge_five` で w₁≥5∨w₂≥5、後者は transpose。**TICyclicHypothesis.swap が無いので transpose 経由が現実的。**

**(3.2) σ**: {ω_ij}=Irr(W) 正規直交基底 → χ_ij 線形写像 = isometry。**要 scope: CF(W) inner product space instance + Irr(W) orthonormal basis + 「orthonormal family → linear isometry」(mathlib `Orthonormal`/`LinearIsometry` 周辺)**。ℤIrr→ℤIrr (χ∈ZIrr); (a) α_ij→Ind, (b) ω_00→1_G, (c)(d) from (1.3)。
- 残 hard core ×1=(4.3)§6本体 (FT経路外)。

正本 = 本ノート (session 14 + cont.)。**Don't re-grind 抽象 (3.5.5) 正規直交 (symm/two_col/gridFamily_orthonormal) / foundations (mem_ZIrr/inner_trivial) / commons (col/rowCommon) — 完成・axiom-clean.**

## 2026-06-09 (session 15, b-peterfalvi): ✅✅✅ (3.5) χ_ij family COMPLETE — 全 (w₁,w₂) orientations

session 14 cont. が残した「χ-assembly → orientation wrapper」を完全形式化。**Peterfalvi (3.5) は任意の admissible `W=W₁×W₂` に対し concrete に成立** (`exists_chiFamily`)。4 commits、全 `S05_SigmaIsometry.lean`、sorry-free・axiom-clean・full build 3558 + AxiomsCheck green。

### ✅ 着地 (session 15, 4 commits)
1. **共有 χ-assembly 抽出 `exists_chiFamily_of_decomposition`** (`cb771e28`, refactor): symm の ~100 行 assembly (正規直交 16-case + Ind 関係) を共有補題に。入力 = `(z,w,φ, hcells: ∀pq Afam=√{z q,w p,φ p q}, hdiag0, hoff0)`。出力 = (3.5) χ-family 4 性質。3 orientation 共通。**ite-instance 地雷回避**: 仮説を `if a=b` でなく ite-free な `hdiag0`/`hoff0` で取り、内部で `hortho` を split_ifs 再構成 (具体 ι の genuine DecidableEq と generic ι の Classical が衝突しないように)。symm は thin caller に。
2. **w₂=3 ケース `exists_chiFamily_two_col`** (`dcc74409`): `w₁≥5, w₂=3`。新 reusable 抽象 bridge `IsSignedTripleGrid.two_col_orthonormal_family_reindexed` — two_col の Bool 出力を card κ=2 の κ へ `Fintype.equivOfCardEq` で再添字 ⟹ **symm と完全同形の出力** `(w,φ, A i j={z j,w i,φ i j}, gridFamily ortho)`。正規直交は reindex equiv `E` で移送 (split_ifs + `E.injective`)。
3. **transpose ケース `exists_chiFamily_transpose`** (`b26a857c` 同梱): `w₁=3, w₂≥5`。**転置グリッド** `(Afam_isSignedTripleGrid).transpose` (rows=Ĉ₂≥4, cols=Ĉ₁ card 2) に `two_col_orthonormal_family_reindexed` を適用。T-列共通 = 元の行共通 = `exists_rowCommon`(w₂≥5)。転置 gridFamily (`Ĉ₂⊕Ĉ₁⊕Ĉ₂×Ĉ₁`) を標準 `Ĉ₁⊕Ĉ₂⊕Ĉ₁×Ĉ₂` へ relabel: 平凡関数 `toT` (anchor swap + 積転置), injective は left-inverse `fromT`, `gridFamily _ = gridFamily _ ∘ toT` は構成子毎 `rfl`。col-anchor=`wMeet`(T-row-meet), row-anchor=`wRow`(元 row-common)。
4. **全体 `exists_chiFamily`** (`b26a857c` 同梱, capstone): `sup_card_ge_five` + |W₁|,|W₂| 奇数>1 (∈{3}∪[5,∞)) で 3 orientation を場合分け束ね。**= 真の Peterfalvi (3.5)** (case-complete)。

### 🔑 再利用可能 (再調査不要)
- **設計の要 = `exists_chiFamily_of_decomposition`**: 任意 orientation は `(z:Ĉ₂→CF col-anchor, w:Ĉ₁→CF row-anchor, φ:Ĉ₁→Ĉ₂→CF interior, hcells, ortho)` を作れば χ-family が出る。3 ケースは「どう (z,w,φ) を作るか」だけが違う。
- **`two_col_orthonormal_family_reindexed`** (card κ=2): two_col(Bool) → symm 形(κ) の汎用変換。w₂=3 と transpose で再利用。
- **転置の使い方**: `(grid).transpose` で rows↔cols 入替 ⟹ row-result を col に適用。transpose grid の cell は `fun q p => Afam p q`、col-common は `exists_rowCommon`。標準レイアウトへの戻しは `toT` relabel (Equiv 不要、平凡関数+left-inverse で injective、rfl で gridFamily 等式)。
- **ite-instance 地雷**: 抽象族 (generic ι) の `if a=b` は Classical、具体 ι は genuine DecidableEq。境界を跨ぐ補題は仮説を `hdiag0`/`hoff0` (ite-free) で取り、内部で `if a=b` 再構成。

### ✅ 着地 (session 15 cont.): (3.2) foundation — Irr(G)=CF(G) ℂ-基底 (`3dd8fb41`)
**(3.2) σ の最初の前提を整備。** mathlib `Module.Basis.constr` で σ:CF(W)→CF(G) を ω↦χ で定義するには「Irr が CF を張る基底」が要る。
- `classFunction_span_irreducibleCharacter_eq_top` (一般有限群): Irr が CF を張る。`f=Σ_χ⟨f,χ⟩•χ`、差が⊥Irr→0 (`classFunction_eq_zero_of_orthogonal` ← `CharacterCompleteness`)。
- `irreducibleCharacterBasis`: `Module.Basis.mk linearIndependent_irreducibleCharacter spanning.ge` (両方 `CharacterCount` 由来)。`+ _apply` simp。
- **🔑 再利用 (再調査不要)**: `ClassFunction.inner` は **Inner typeclass でなく素の def** (InnerProductSpace instance 無し) → 左引数線形 (`inner_smul_left`/`inner_add_left`/`inner_sub_left`)、共役は右。基底は `Module.Basis.mk` で手組み。`Basis`=`Module.Basis` (mathlib リネーム、`Module.Basis`/`.mk`/`.mk_apply` と書く)。`Finite/Fintype (IrreducibleCharacter G)` は `finite_irreducibleCharacter`(theorem, instance でない)→`haveI`+`Fintype.ofFinite`。S05 に `import CharacterCompleteness + Mathlib.LinearAlgebra.Basis.Basic` 追加済。

### ▶▶ 次 = (3.2) σ の本体 [次セッション]
**foundation (基底) 済。次の前提 = prod-char 全単射。**
- **🛑 次の一手 = `Ĉ₁ × Ĉ₂ ≃ (W →* ℂˣ)` (omegaProdChar の全単射化)**: `omegaProdChar : Ĉ₁→Ĉ₂→(W→*ℂˣ)` は injective のみ (`omegaProdChar_inj`, S05_TICyclic:745)。σ には全 index 対応 `Ĉ₁×Ĉ₂ ≃ Hom(W,ℂˣ) ≃[omegaEquiv] Irr(W)` が要る。W=W₁×W₂ 内部直積 (S05_TICyclic にある乗法 iso `↥W₁×↥W₂≃↥W`) から `Hom(W,ℂˣ)≃Hom(W₁)×Hom(W₂)` を作る。注意: `Ĉ_k = W_k.subgroupOf W →* ℂˣ` (subgroupOf)。**`alphaBasis`(S05_TICyclic:896) は CF(W,V) を `Ĉ₁ⁿᵉ×Ĉ₂ⁿᵉ` で張る既存基底 — 参考になるが σ は CF(W) 全体 (trivial 込み Ĉ₁×Ĉ₂) なので別物。**
- **σ 定義**: `σ := (irreducibleCharacterBasis (G:=hyp.W)).constr ℂ (fun ω => χfam (prodCharEquiv.symm (omegaEquiv.symm ω)))` 形 (χfam = `exists_chiFamily` の選択した族)。`Module.Basis.constr` は `M→ₗ[ℂ]M'`、`constr b f (b i)=f i`。
- **isometry**: ⟨σa,σb⟩=⟨a,b⟩ を基底上で (χ族正規直交 ⟨χp,χp'⟩=δ + Irr(W)正規直交 ⟨ω,ω'⟩=δ + bridge 単射) → 双線形拡張。**`ClassFunction.inner` は素の def なので mathlib `LinearIsometry` でなく手で双線形拡張**。
- **(3.2) 性質**: (a) σ(α_ij)=Ind (← (3.5) の Ind 関係 + α_ij=ω-combination `alphaCF_eq_omega_combination`), (b) σ(1_W)=1_G (← χ(1,1)=1_G), (c)(d) from (1.3) [**(1.3) の形式化状況 未確認**]。
- 残 hard core ×1=(4.3)§6本体 (FT経路外)。

正本 = 本ノート (session 15 + cont.)。**Don't re-grind (3.5) χ-family (symm/two_col/transpose/full) / 共有 assembly / reindex wrapper / (3.2) Irr-基底 (span+`irreducibleCharacterBasis`) — 完成・axiom-clean.**

## 2026-06-09 (session 16, b-peterfalvi, /loop 自走): (3.2) σ 本体 CORE COMPLETE — 定義+等長+ (a)基底+(b)+virtual→virtual

`/loop` dynamic mode で 5 commits、全 `S05_SigmaIsometry.lean`、build-green + axiom-clean (full build 3558 + AxiomsCheck green、guard 登録)。**σ:CF(W)→CF(G) (= Peterfalvi (3.2)) の核を構成完了。**

### ✅ 着地 (session 16, leaf 1-5)
1. **index bridge `Ĉ₁×Ĉ₂≃Irr(W)`** (`f5b3e32f`): `omegaProdChar_surjective` (ξ=(ξ|W₁)·(ξ|W₂) via `wProj1_mul_wProj2`) + `omegaProdEquiv` (Equiv.ofBijective, inj=既存 omegaProdChar_inj) + `omegaIrrEquiv` (= omegaProdEquiv.trans omegaEquiv)。
2. **σ 定義** (`f832ed39`): `chiFam`/`chiFam_spec` (= `exists_chiFamily` の選択族 + 4 性質, `.choose`/`.choose_spec`) + **`sigma := (irreducibleCharacterBasis (G:=W)).constr ℂ (fun ω => chiFam (omegaIrrEquiv.symm ω))`** (Module.Basis.constr) + `sigma_irreducibleCharacter` (σ(↑ω)=chiFam(...) via constr_basis)。
3. **σ 等長性** (`adfdb08a`): `sigma_inner` (⟨σa,σb⟩=⟨a,b⟩) + `sigma_inner_irreducibleCharacter` (基底 Gram 一致=δ) + **再利用 `inner_sum_smul_sum`** (一般 ι,H: ⟨∑r•F,∑s•F⟩=∑∑ r·conj(s)·⟨F,F⟩, 双線形展開 workhorse)。基底 repr + map_sum で全体に拡張。
4. **(3.2)(a)基底 + (b)** (`8169cd0e`): `sigma_omega` (σ(↑ω(ξ))=chiFam(omegaProdEquiv.symm ξ)) + `omegaProdEquiv_symm_omegaProdChar` + **(b) `sigma_trivial`** (σ(1_W)=1_G) + **(a)基底 `sigma_alphaCF`** (σ(alphaCF p q)=app.tau.toDadeMap(alpha p q), p,q≠1; alphaCF_eq_omega_combination で ω 4-項展開→sigma_omega→chiFam→(3.5) Ind 関係)。
5. **σ virtual→virtual** (`40748166`): `sigma_mem_ZIrr` (σ(ZIrr W)⊆ZIrr G; ZIrr_eq_span + span 帰納、各基底→chiFam∈ZIrr, ℤ-submodule 閉性)。

### 🔑 再利用可能 (再調査不要)
- **`inner_sum_smul_sum`** (S05, 一般): 「基底上 Gram 一致 → 等長」の workhorse。`ClassFunction.inner` は素の def なので mathlib LinearIsometry 不可、これで手動双線形展開。
- **`sigma_omega`**: σ on linear char = chiFam at omegaProdEquiv.symm。任意の ω-項を chiFam に落とす。
- ZIrrFourier に `inner_sum_left`/`inner_sum_right`/`inner_smul_right` 既存 (S05 が import 済、namespace `OddOrder.RepresentationTheory`、`inner_smul_right` は `_root_` と曖昧→qualify 要)。

### ▶▶ 残り (3.2): (a)全体 + (c)(d) — 両者 infra leaf 要 [STOP point, 次セッション/再loop]
**σ CORE は完成。残り 2 piece は別インフラを要し、loop STOP。両者 route 確定:**
- **(a) 全体** `∀ α∈CF(W,V), σ(↑α)=app.tau.toDadeMap α` [scoped, 未着手]: **route** = `induceₗ : CF(W)→ₗ[ℂ]CF(G)` を `{toFun:=induce W, map_add':=induce_add, map_smul':=induce_smul}` で構成 (InducedCharacter:312/317) → `(σ.comp submodule.subtype)` と `(induceₗ.comp subtype)` を `Module.Basis.ext (alphaBasis hVeq)` で一致 (各基底: `alphaBasis pq = alpha hVeq pq.1.1 pq.2.1` via `coe_basisOfLinearIndependentOfCardEqFinrank`, `alpha_coe`, `sigma_alphaCF` [pq.1.2/pq.2.2 で ≠1], `tau_eq_induce` [app.tau.toDadeMap=induce, S05:293; **要確認: app.tau.toDadeMap = app.tau.toDadeIsometryData.toDadeMap が rfl か**])。SupportedOnV=↥(supportedSubmodule ...)。~40-60行。
- **(c)(d)** [**(1.3)(b) gating**]: S03 は仮説述語 `IsInductionExpansion` (Ind ψ=∑⟨ψ,χ_i⟩•μ_i, S03:512) のみで **(1.3)(b) の結論 (μ_i|A=χ_i|A; μ⊥all μ_i→μ|A=0) は未形式化**。route = (1.3)(b) を形式化 [直交補空間 `CF(H,A)^⊥=CF(H,H-A)` 論法、mmd 04.3 (1.3) proof; 実質 leaf ~80-120行] → H=W,A=V,ψ_j=α_ij,χ_i=ω,μ_i=ω^σ で適用 ((c)=μ_i|V=χ_i|V→線形拡張、(d)=⊥im→vanish)。
- **exists_sigma 組立**: (a)全体 完了後、isometry+virtual→virtual+(a)+(b) を `∃ σ, ...` に束ねられる ((c)(d) は (1.3)(b) 後)。
- 残 hard core ×1=(4.3)§6本体 (FT経路外)。

正本 = 本ノート (session 16)。**Don't re-grind (3.2) σ CORE (sigma/sigma_inner/sigma_alphaCF/sigma_trivial/sigma_mem_ZIrr/sigma_omega/index bridge/inner_sum_smul_sum) — 完成・axiom-clean.**

## 2026-06-10 (session 17, b-peterfalvi): ✅✅✅ Peterfalvi Theorem (3.2) COMPLETE — (a)full + (1.3)(a) + (c)(d) + capstone

session 16 が残した「(3.2)(a)全体 + (c)(d) [(1.3) gating]」を完全形式化。**Peterfalvi Theorem (3.2) (a)-(d) は任意の admissible TI-cyclic `W=W₁×W₂` に対し成立** (`exists_sigma`)。全 `S05_SigmaIsometry.lean`、sorry-free・axiom-clean・full build 3558 + AxiomsCheck green。3 commits (`0ca7df1c` (a)full, `d7c3bf2b` (1.3)(a)+(c)(d), `db9b5dcc` capstone)。

### ✅ 着地 (session 17)
1. **(3.2)(a) 全体 `sigma_eq_tau`** (`0ca7df1c`): `∀ α∈CF(W,V), σ(↑α)=τ(α)=Ind_W^G α`。`σ∘↪` と `Ind∘↪` (両 `CF(W,V)→ₗCF(G)`) を `Module.Basis.ext (alphaBasis)` で一致 — 各 α_{ij} で LHS=`sigma_alphaCF`、RHS=`tau_eq_induce`。新 helper: `alphaBasis_apply` (`coe_basisOfLinearIndependentOfCardEqFinrank`, `unfold`+`letI` で baked-in Fintype 一致), `induceLinear`(+`_apply`) (`Ind` を bundled `CF(W)→ₗCF(G)` に)。
2. **(1.3)(a) engine `eq_zero_of_mem_of_inner_supported_eq_zero`** (`d7c3bf2b`, S05 namespace, 一般): conj-closed `A` 上、`f ⊥ (∀ supported on A)` ⟹ `f|_A=0`。**論文の直交補空間 `CF(H,A)^⊥=CF(H,H∖A)` を masking で実装**: テスト関数 `f·1_A` (conj-closed ゆえ class function) で `⟨f·1_A,f⟩=⅟|H|∑_{a∈A}|f(a)|²=0` ⟹ 各 `f(a)=0` (`Complex.mul_conj`/`normSq`/`sum_eq_zero_iff_of_nonneg`)。**論文の (1.3)(a)(b) full iff を経由せず、1 個の masking テスト関数で直接 vanishing を出す** (より短い)。
3. **bridge `vanishOnV_of_inner_alphaCF`** (`d7c3bf2b`): `f⊥全α_{ij}` ⟹ `f|_V=0`。α_{ij}=CF(W,V)基底(3.4) ⟹ 線形汎関数 `innerLeftFunctional f` が basis で 0 ⟹ submodule 全体で 0 (`Module.Basis.ext`)。`V` は abelian `W` で conj-closed (`mul_comm'`)。新 general infra: `innerLeftFunctional`(+`_apply`)。
4. **(3.2)(c) `sigma_apply_of_mem_V`** (`d7c3bf2b`): `∀α∈CF(W),x∈V, σ(α)(x)=α(x)`。per-ω `sigma_apply_irreducibleCharacter_of_mem_V`: `f=Res_W(ω^σ)-ω ⊥ α_{ij}` ∵ `⟨α_{ij},Res_W ω^σ⟩=⟨Ind α_{ij},ω^σ⟩=⟨α_{ij}^σ,ω^σ⟩=⟨α_{ij},ω⟩` (Frobenius `inner_induce_eq_inner_restrict` + (a) + `sigma_inner` isometry); 一般は Irr(W) 基底で線形拡張 (`D α=σ(α)(v)-α(v)` を `Basis.ext` で 0)。
5. **(3.2)(d) `eq_zero_of_mem_V_of_inner_chiFam_eq_zero`** (`d7c3bf2b`): `χ⊥全χ_{ij}` ⟹ `χ|_V=0`。`σ(α_{ij})=1_G-χ_{i0}-χ_{0j}+χ_{ij}`(3.5)+`1_G=χ_{00}` ⟹ `χ⊥σ(α_{ij})` ⟹ `⟨α_{ij},Res_W χ⟩=⟨σ(α_{ij}),χ⟩=0` (Frobenius+(a)+`inner_conj_symm`)。
6. **capstone `exists_sigma`** (`db9b5dcc`): `∃σ:CF(W)→ₗCF(G), 等長 ∧ ZIrr→ZIrr ∧ (a) ∧ (b) ∧ (c) ∧ (d)`。(d) は `χ⊥σ(Irr W)` 形 (index bridge `χ_{ab}=(ω_{ab})^σ` via `sigma_irreducibleCharacter`+`omegaIrrEquiv`)。**= Peterfalvi Theorem (3.2) そのもの**。

### 🔑 再利用可能 (再調査不要)
- **(1.3)(a) masking engine** `eq_zero_of_mem_of_inner_supported_eq_zero` (一般 conj-closed A): `f⊥CF(H,A) ⟹ f|_A=0`。論文の直交補空間論法。テスト関数=`f·1_A`。
- **`innerLeftFunctional f`** (一般): `φ↦⟨φ,f⟩` を bundled `CF(H)→ₗℂ` に。「f⊥basis ⟹ f⊥submodule」を `Basis.ext` で。
- **per-ω (c)/(d) の共通核**: `induce(alphaCF p q)=σ(alphaCF p q)` (sigma_eq_tau+tau_eq_induce+alpha_coe) + Frobenius `inner_induce_eq_inner_restrict` + `sigma_inner`/`inner_conj_symm`。
- **`alphaBasis_apply`**: `alphaBasis(p,q)=α_{pq}`。tactic-定義 basis の coe は `unfold`+`letI`(baked-in Fintype.ofFinite と defeq) で `coe_basisOfLinearIndependentOfCardEqFinrank` 適用。
- **σ on Irr-basis 線形拡張パターン**: `D:CF→ₗℂ := {α↦P(σ α)-Q(α)}` を作り `Basis.ext (irreducibleCharacterBasis)` で 0 を示す (map_add'/map_smul' は `simp[map_add/map_smul,add_apply/smul_apply]; ring`)。

### ▶▶ 次 = (3.6)-(3.9) → §6 (4.x) certain-type 本体 [hard core ×1 残]
**(3.2) σ 完全終了。§5 残り = σ-依存の (3.6)Hyp/(3.7)/(3.8) NC(ψ) → (3.9) Galois ((1.9))。** その後 §6 (4.x) certain-type Dade isometry 定理本体 (chunk 04.6; result番号 = repo S06; (4.3) が hard core)。これが (6.8) coherence capstone (S08 sole sorry) の最終依存。FT 最短経路外だが CLAUDE.md 全形式化スコープの正規ターゲット。
- 残 hard core ×1 = (4.3) §6本体 (FT経路外)。

正本 = 本ノート (session 17)。**Don't re-grind Peterfalvi (3.2) — (a)-(d) 完全・axiom-clean・`exists_sigma` で bundle 済。**

## 2026-06-10 (session 18, b-peterfalvi, Ultracode): ✅ (3.6)+(3.7)+(3.8)-corollary — σ-coefficient grid `NC(ψ)` theory

After (3.2) complete (session 17), advanced the §5 frontier through the `NC(ψ)` coefficient theory. All `S05_SigmaIsometry.lean`, sorry-free・axiom-clean・full build 3558 + AxiomsCheck green. 3 commits (`a81f8127` (3.6)+(3.7), `6e6257a4` (3.8)-cor). Preceded by an **understand-workflow** (4 parallel readers, run `wf_cf660de5-cba`) mapping downstream consumers + Galois infra + σ-API + (3.6) design.

### ✅ 着地 (session 18)
1. **(3.6) defs** (`a81f8127`): `sigmaCoeff ψ (p,q) := ⟨ψ, chiFam (p,q)⟩` (= a_ij, the Fourier coeff along the orthonormal σ-image family {ω_ij^σ}={χ_ij}; β=ψ−∑a_ij ω_ij^σ auto ⊥ Im σ) + `sigmaNC ψ := {pq | sigmaCoeff ψ pq ≠ 0}.ncard`.
2. **(3.7) `sigmaCoeff_add_eq`**: ψ vanishing on V ⟹ `a_ij + a_i'j' = a_ij' + a_i'j`. Via `omegaCombo`=ω_ij+ω_i'j'−ω_ij'−ω_i'j ∈ CF(W,V) (support lemma `omegaCombo_mem_supportedSubmodule`: vanishes on W₁/W₂ as q/p-parts collapse) → `inner_sigma_eq_zero_of_vanishOnV` (⟨ψ,σ(α)⟩=0 since σ(α)=Ind α supported on V^G=conjugatesOfSet V, ψ vanishes there; disjoint-support) → σ(omegaCombo)=χ_ij+… (σ linear + `sigma_omega`) → read off coeffs (`inner_add/sub_right` + `linear_combination`).
3. **(3.8) corollary `sigmaCoeff_eq_zero_of_sigmaNC_lt`** (`6e6257a4`): ψ vanishing on V ∧ `NC(ψ) < min(w₁,w₂)` ⟹ ALL a_ij=0. **🔑 KEY INSIGHT: the (3.7) identity makes the grid ADDITIVELY SEPARABLE** (`a(i,j)=f(i)+g(j)`). Abstract `grid_eq_zero_of_ncard_support_lt` (general ℂ-grid ι×κ→ℂ, vanishing mixed differences, #support < min|ι||κ| ⟹ ≡0): rows differ by a col-independent constant ⟹ two distinct rows give a nonzero in EVERY column (≥|κ|) / else all rows equal so one nonzero fills a column (≥|ι|). Instantiated at sigmaCoeff via card_charGroup_subgroupOf (w_k=|Ĉ_k|). **This is the part of (3.8) (3.9.a) and most §6/§7 consumers use** (small-NC⟹⊥image). 

### 🔑 再利用可能 / 検証済インフラ (再調査不要)
- **separable-grid lemma** `grid_eq_zero_of_ncard_support_lt` (ncard/Nat.card interface, converts to Finset internally to avoid caller Fintype-instance friction).
- **Galois infra EXISTS** (再調査するな): `CyclotomicGaloisAction.lean` = Peterfalvi (1.9) 完全形式化 (`exists_complexRingEquiv_mapRingEquiv_eq_pow`:363 [σ(φ g)=φ(g^k) on ZIrr, ord g∣a; =φ g if coprime], `exists_complexRingEquiv_pow_and_fixed`:311); `GaloisCharacter.lean` = `ClassFunction.mapRingEquiv`(coeffwise ℂ≃+*ℂ action)/`IrreducibleCharacter.galoisMap`/`galoisPerm`/`mapRingEquiv_inner`/`mapRingEquiv_mem_ZIrr`. S07 precedent `IsCoherent.extension_mapRingEquiv_comm` (isometry commutes with cyclotomic σc). ω^k = MonoidHom power (W abelian, ω:W→*ℂˣ); ord ω = orderOf in (W→*ℂˣ).
- **ZIrr integrality/norm tools**: `inner_mem_ZIrr_int {φ ψ}(∈ZIrr)(∈ZIrr):∃m:ℤ,⟨φ,ψ⟩=m` (InducedCharacter:716, **imported by S05**), `mem_ZIrr_inner_self_eq_sum_sq`(ZIrrFourier:234), positive-def `eq_zero_of_inner_self_re_eq_zero`(ZIrrFourier:189), `exists_pair_of_sum_sq_eq_two`(ZIrrFourier, norm-2 combinatorics template). **Bessel `sum_sq_le_inner_self_re` は S08 にあり S05 からは import 不可** (S05 は upstream) — (3.9.a) は Bessel 不要の norm-1-classifier 経路を使う。

### ▶▶ 次 = (3.9)(a)(b)(c) + (3.8) full trichotomy [全ルート確定・実装待ち]
**(3.9)(a) `χ∈±Irr, χ|_V=ω|_V ⟹ χ=ω^σ`** [§6 keystone, ~200 行, multi-piece]:
- **norm-1 classifier** (新, S05 leaf, mirror `exists_pair_of_sum_sq_eq_two`): `exists_single_of_sum_sq_eq_one` (∑c²=1,c≠0⟹単一±1) → `exists_irr_eq_or_neg_of_inner_self_one` (φ∈ZIrr,⟨φ,φ⟩=1⟹φ=±μ via mem_ZIrr_inner_self_eq_sum_sq).
- **χ-support≤1** `card_inner_chiFam_ne_zero_le_one`: χ=±μ₀, chiFam pq=±ν (classifier, chiFam∈ZIrr norm1 from chiFam_spec.2.1/.2.2.1-diag) ⟹ ⟨χ,chiFam pq⟩≠0⟺chiFam pq=±μ₀; 2つ⟹⟨chiFam pq,chiFam pq'⟩=±1≠0 contra chiFam_spec.2.2.1 (`Set.ncard_le_one`).
- **NC(σ↑ω−χ)≤2**: support⊆{ω-idx}∪χ-support (⟨σ↑ω,chiFam pq⟩=δ_{pq,ω-idx} via sigma_irreducibleCharacter+orthonormal).
- **min(w₁,w₂)≥3**: W_k nontrivial(≠⊥, card≥2) + |W_k| odd (∣|W| odd via Lagrange) ⟹ odd>1⟹≥3. (helper `three_le_card_W1/W2`.)
- **assembly**: corollary ⟹ coeffs 0 ⟹ ⟨φ,chiFam(ω-idx)⟩=0 ⟹ ⟨χ,σ↑ω⟩=1 ⟹ χ=σ↑ω via `⟨χ−σ↑ω,χ−σ↑ω⟩=2−1−1=0`+positive-def. φ vanishes on V from (3.2c) sigma_apply_of_mem_V + hyp.
- **σ-Galois "in particular"** ω^{σu}=ω^{uσ}: `mapRingEquiv u` commutes with σ on basis (S07 pattern `extension_mapRingEquiv_comm`).
**(3.9)(b)(c)** [independent of (3.8)/(3.9a), ~150-300 行]: bridge `omega(χ^k)=mapRingEquiv σ_k (omega χ)` (σ_k=(·^k) on |W|-th roots, ω linear) + push through σ (S07 commutation) ⟹ (ω^k)^σ=ω^{uσ}=ω^{σu}; value-part = `mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr` b-branch; (c) rationality = fixed-field + algebraic-integer (ClassSumAlgebra integrality).
**(3.8) full trichotomy (b)/(c)** [§12+ only, defer]: separable structure — subcase f-const⟹case(b) (one column, |{j:nonzero}|<2⟹=1), symmetric⟹(c), both-non-const⟹NC≥2w₁ (textbook (3.8.1) counting, the hard sub-lemma).

正本 = 本ノート (session 18)。**Don't re-grind (3.6)/(3.7)/(3.8-cor)/separable-grid — 完成・axiom-clean.**

## 2026-06-10 (session 19, b-peterfalvi): ✅✅✅ (3.9) COMPLETE — (a) §6-keystone + (b) + (c)

(3.9) 全体 (a)(b)(c) を `S05_SigmaIsometry.lean` で完全形式化。sorry-free・axiom-clean・full build
3601 + AxiomsCheck green。2 commits: `7af66f4b` (3.9.a), `295d06d9` (3.9.b)+(3.9.c)。

### ✅ 着地 (session 19)

1. **(3.9)(a)** `eq_sigma_of_apply_eq_on_V` [§6 keystone]: χ ∈ ZIrr G, ‖χ‖²=1, χ|_V=ω|_V ⟹
   χ = ω^σ。部品: `three_le_card_W1/W2` (odd ∧ >1 ⟹ ≥3)、`ncard_inner_chiFam_ne_zero_le_one`
   (norm-1 ⟹ chiFam-support ≤ 1)、NC(ω^σ−χ) ≤ 2 < 3 ≤ min(w₁,w₂) → (3.8)-cor で全係数 0 →
   ⟨χ,ω^σ⟩=1 → ‖χ−ω^σ‖²=0 + positive-def。
   - **norm-1 classifier の新設は不要だった**: `exists_zsmul_irreducibleCharacter_of_inner_self_one`
     が `InducedIrreducible.lean` に既存 (session-18 plan の「classifier 新設」項は verify で消えた)。
     S05 に import 追加: `InducedIrreducible` + `GaloisCharacter`。
   - "in particular" = `sigma_mapRingEquiv_comm`: (ω^σ)^u = (ω^u)^σ, ∀u : ℂ ≃+* ℂ。
     **star-commutation 仮定不要** — `mapRingEquiv_inner` を避け、ω^σ = ε•μ の ±Irr 表現経由で
     norm 1 を運ぶ (mapRingEquiv は ±Irr → ±Irr)。
2. **(3.9)(b)** `exists_mapRingEquiv_sigma_omega_pow`: a = orderOf ξ, k coprime a ⟹
   ∃u, (ω(ξ^k))^σ = (ω(ξ))^{σu} ∧ 値一致 at g (orderOf g coprime a)。
   - **🔑 B := ∏(divisors |G| coprime to a) trick**: `exists_complexRingEquiv_pow_and_fixed` の
     第2モジュラスに divisor-積を使い「a-coprime part」の因数分解 plumbing を完全回避
     (orderOf g ∣ B は `Finset.dvd_prod_of_mem` 一発、coprime は `Nat.coprime_prod_right_iff`)。
   - helper `orderOf_char_ne_zero` (ξ^|W| = 1 pointwise)。
3. **(3.9)(c)** `exists_intCast_sigma_omega_apply`: (ω(ξ))^σ(g) ∈ ℤ for orderOf g coprime a。
   - 核: 値が**全ての** u : ℂ ≃+* ℂ で固定 — u は a-th roots 上 (·^i) i coprime a
     (`exists_pow_forall_rootsOfUnity`) → bridge (ω(ξ))^u = ω(ξ^i) → (3.9.a)-comm +
     (3.9.b)-値部で元の値に戻る → 有理 → 整数 (`isIntegral_rat_imp_int`)。
   - **新 G-free infra** (S05 leaf 内に保持、docstring で upstream 候補と明記):
     `isIntegral_apply_of_mem_ZIrr` [→ ClassSumAlgebra 候補]、`exists_pow_forall_rootsOfUnity` /
     `exists_ratCast_of_forall_complexRingEquiv_eq` [→ CyclotomicGaloisAction 候補]。後者 =
     「ℚ-整 + 全自己同型固定 ⟹ ℚ」: 分解体 K = ℚ(rootSet p ℂ) は normal
     (`IntermediateField.adjoin_rootSet_isSplittingField` + `Normal.of_isSplittingField`)、
     `IsConjRoot.exists_algEquiv` で任意の根へ動かす自己同型を K 内に取り
     `exists_complexRingEquiv_extends` で ℂ に拡張 → 分離多項式の根が 1 個 →
     `Polynomial.card_rootSet_eq_natDegree` + `minpoly.natDegree_eq_one_iff` で deg 1。
   - 新 import: `Mathlib.FieldTheory.Minpoly.IsConjRoot` + `CyclotomicGaloisAction` ((1.9) 供給)。
   - elaboration tips: `IsPrimitiveRoot.eq_pow_of_pow_eq_one` は `[NeZero a]` 要 (haveI ⟨ha⟩);
     `IntermediateField.minpoly_eq` の `.symm` 側は引数明示しないと unifier が ↑?x で詰まる。

### ▶▶ 次 = §6 (4.2)/(4.3) 本体 [残 hard core ×1] — RECON 済 (再調査するな)

- **(3.1) の V に fork 無し**: V = W−(W₁∪W₂) で固定 (原文 (3.1) 確認済)。(4.3.a) の
  「W−W₂ is TI in L」は **追加構造** (CF(W, W−W₂) の Ind_W^L isometry 用) で、(3.1)-for-L は
  そこから従う。§5 σ 機構 (hVeq 前提) はそのまま L をアンビエントに適用できる。
- **(4.3) 証明部品の所在**:
  - (a) = 群論 (xy ∈ W−W₂, (xy)^g ∈ W−W₂ ⟹ x^g ∈ Kx ∩ W₁ ⟹ x^g = x ⟹ g ∈ C_L(x) = W)。
  - (b) = CF(W, W−W₂) 基底 (ω_ij−ω_0j) [(3.4) 類似の counting |W−W₂| = (w₁−1)w₂] +
    Ind_W^L isometry on CF(W, W−W₂) [TI 古典; S05 `inducedDadeMap`/`isDadeMap_inducedDadeMap`
    が L-side `FullDadeApplication` 構成の素材] + **(1.4) = `IsometryDifferencePair.lean` 整備済** +
    **(4.1) = S08:72-195 形式化済 ⚠ S08 は S06 の下流** — (4.3) の置き場 (新 leaf
    `S06_CertainType.lean`?) と (4.1) の upstream 移動の import-DAG 設計が最初の決定事項 +
    **(3.9.a) = 本セッションで解除 ✅**。
  - (c) = (1.3) 値 + 消滅; (d) = Res_{W₁} + 正則指標で μ_ij(1) ≡ δ_j mod w₁。
  - ⚠ TICyclicHypothesis を **L に対して** 立てる constructor (CertainTypeHypothesis →
    TICyclicHypothesis L) が最初の Lean leaf。
- **(4.4)** は (3.9)+(4.3) 消費で小; **(4.5.b)** は [Is] 6.32 Brauer (形式化済) 消費。
- **(3.8) full trichotomy (b)/(c)** は §12+ 専用で defer 継続。(3.9.b)/(3.9.c) の下流消費は
  §12/§13/§15/§16 (grep 済: 04.12 L17/L67, 04.13 L85, 04.15 L136, 04.16 L103)。

正本 = 本ノート (session 19)。**Don't re-grind (3.9) — (a)(b)(c) 完成・axiom-clean。**

## 2026-06-10 (session 20, b-peterfalvi): ✅ (4.2) 構造 + (4.3.a) COMPLETE + (4.3.b) isometry 基盤

§6 本体に着手。4 commits、全 build-green + axiom-clean (full 3601 + AxiomsCheck)。

### ✅ 着地 (session 20)

1. **(4.1) upstream 移動** (`686ffa1c`): S08:72-239 の (4.1) cluster
   (`inner_eq_zero_of_orthogonal_signedDifference` + pairwise 版 + 2 helpers) を
   `InducedIrreducible.lean` へ verbatim 移動 (同 namespace
   `OddOrder.RepresentationTheory` ⟹ S08 呼び出し側・AxiomsCheck guard 無変更)。
   S06 leaf から (4.1) が import 可能に (S08 は S06 の下流ゆえ必須だった)。
2. **(4.2) 抽象化 + Hall** (`bf1fdd03`): `S06.Hypothesis (L : Type*)` — 抽象有限群上の
   忠実な (4.2)。**新 field `card_coprime : Coprime |K| |W₁|`** (= Hall 性; 旧構造に欠落、
   S08 (c2) が side condition で外付けしていたもの)。`W_disjoint` は field → 導出 lemma。
   `CertainTypeHypothesis A L` は `extends Hypothesis ↥L` + `dade` に refactor
   (構成箇所ゼロ・S08 の field access 全て温存、S08 無変更で compile)。
   基本 API: `commute_of_mem_of_isCyclic` (generic)、`commute_of_mem_W1_of_mem_W2`、
   `coprime_card_W1_card_W2`、`isMulCommutative_sup` (`sup_eq_closure` +
   `isMulCommutative_closure`)、subgroupOf inf/sup、`exists_mul_of_mem_sup` (w = x·y)、
   **`exists_zpow_proj`** (∃n:ℤ, (xy)^n = x — Bézout `Nat.gcdA/gcdB` 直接、Euler/CRT 不要、
   finiteness-free)。
3. **(4.3.a) COMPLETE** (`fcc927ec`): `centralizer_eq_sup` (C_L(x) = W, x∈W₁^#; ≤ は
   c = k·u 分解 + W₁ abelian ⟹ k ∈ C_K(x) = W₂)、`isTISubset_sup_sdiff` (**W−W₂ TI**;
   x = a^n ⟹ g·x·g⁻¹ = (g·a·g⁻¹)^n ∈ W₁、κ ∈ K ⊓ W₁ = ⊥)、`supMulEquiv` +
   `card_sup_eq_mul` (|W| = |W₁||W₂|)、`isCyclic_sup` (生成元積の order = |W|)、
   `toTICyclicHypothesis` (**(3.1)-for-L**)。
4. **(4.3.b) isometry 基盤** (`8d506b44`): `toTICyclicHypothesisOfV` (V-パラメトリック
   (3.1) builder; W abelian ⟹ 任意 V ⊆ W を正規化)、`sdiffTICyclicHypothesis`
   (V = W−W₂)、`sdiffDadeHypothesis` ((2.2) on (L, W−W₂, W) を syntactic W₁⊔W₂ 形で)、
   **`sdiffFullDadeIsometryData`** = 「Ind_W^L は CF(W, W−W₂) 上 isometry」(教科書の
   "We know" 一文)。

### 🔑 KEY 発見 (再調査するな)

- **`TICyclicHypothesis.V` は§6 再利用のための free field** (S05:38 の設計コメント通り)。
  `toTICyclicHypothesisOfV` で V = W−(W₁∪W₂) と V = W−W₂ の両方を一つの builder から。
- **§4 Theorem (2.6) は構成済み**: `S04.Hypothesis.fullDadeIsometryData (hconj)` が
  isometry + ZIrr 保存を**証明付きで**返す。TI 由来 (H(a) ≡ ⊥) なら
  `HConjInvariant.of_forall_H_eq_bot` で hconj 自動 (toDadeHypothesis_H は rfl 証明
  ⟹ `fun _ => rfl` で渡せる)。**TI 誘導等長性の手証明は不要**。
- **`tau_eq_induce`** (S05:297) が任意の DadeIsometryData の写像を Ind と同定
  (IsDadeMap.unique 経由) — sdiff 側にも適用可。
- sdiff 系と (3.1) 系は **同じ W/W₁/W₂** (defeq) ⟹ ω/omegaProdChar 機構は両者で共有。
- Lean 地雷 (今回踏んだ): (i) `IsComplement.existsUnique` の等式は projection 形 →
  `change kk * u = c at hku` で正規化 (defeq 保証)。(ii) `refine ⟨?_, hk⟩` を
  `∈ A ⊓ B` に使うと Submonoid-coe 形に unfold され `mem_centralizer_iff` の rw が
  死ぬ → `Subgroup.mem_inf.mpr` 経由。(iii) `subst hz` (hz : z = x) は **x を消去**
  (calc が x を書いていると Unknown identifier) → 後続が x を使うなら `rw [hz]`。
  (iv) def の射影 (`(def).W`) は TC 探索で unfold されない → instance を要する
  hypothesis は syntactic 形で別 def に restate (`sdiffDadeHypothesis` パターン)。

### ▶▶ 次 = (4.3.b) 本体 [新 leaf `S06_CertainTypeCharacters.lean` 推奨]

新 import: S05_SigmaIsometry + S06_DadeIsometryCertain + IsometryDifferencePair。手順:

1. **CF(W, W−W₂) の基底** {ω_ij − ω_0j : i ≠ 1, j}: (w₁−1)·w₂ 本 = |W−W₂|
   (`card_sup_eq_mul` から counting)。S05 `SupportedDimension` section (S05:189) が
   CF(H,A) の次元 = |A| (可換 H) を供給。lin indep は alphaLinearIndependent
   (S05:856) パターン + `basisOfLinearIndependentOfCardEqFinrank` (session-17
   `alphaBasis_apply` の `unfold`+`letI` tip 再利用)。ω_ij − ω_0j が W₂ 上消える:
   wFst kills W₂ (S05:439)。
2. **(1.4) 適用 per column j**: ✅ interface 精査済 (session 20 末) —
   **`isometry_difference_pair_structure`** (IsometryDifferencePair.lean:730,
   docstring に「§6 (4.5) consumer」明記の抽象 (1.4))。入力 (全て session-20
   成果物で賄える):
   - `n := w₁`, `2 ≤ n` (← w₁ ≥ 3, S05 `three_le_card_W1` 系), `[NeZero n]`;
   - `χ : Fin w₁ → Irr(W)` = `i ↦ ω_{e(i),j}` (e : Fin w₁ ≃ Ĉ₁, **e 0 = 1 に pin**
     [`Fintype.equivOfCardEq` + swap; card = `card_charGroup_subgroupOf`]),
     injective (omegaProdChar_inj + omega_injective), same degree (全 linear,
     `omega_apply_one`);
   - `τ := (induceLinear …).restrictScalars ℤ` (S05 session-17 の bundled Ind);
   - `h_image_virtual` = `induce_mem_ZIrr` (差 ∈ ZIrr W);
   - `h_image_degree_zero` = `induce_apply_one` (差の degree 0);
   - `h_isom` = **ω_ij − ω_0j ∈ CF(W, W−W₂)** (wSnd-kills W₂ 計算, 新補題要) →
     `SupportedClassFunctions` に包んで `sdiffFullDadeIsometryData.inner_eq` +
     `tau_eq_induce` (Dade map = Ind) で transfer。
   出力: `SignedIrreducibleDifferenceFamily L w₁` = (μ_i injective, 一様 sign
   δ_j = ±1, `Ind(ω_ij − ω_0j) = δ_j • (μ_ij − μ_0j)`) — **列内 distinct は
   `.injective` field で出る**。注意: `signedDifference` 形 (sign • (μ_i − μ_0))
   との等式が結論; (4.3.b) の文言へは `sign_eq` で ±1 場合分け。
3. **列間 distinct**: (4.1) `pairwise_inner_eq_zero_of_orthogonal_signedDifference`
   (InducedIrreducible に移動済 ✓ S05 経由で import される)。
4. **σ 同定**: (3.9.a) `eq_sigma_of_apply_eq_on_V` + `exists_sigma`
   (S05_SigmaIsometry) を `toTICyclicHypothesis` (hVeq = rfl) 上で ⟹
   σ(ω_ij) = δ_j μ_ij。
5. その後 (4.3.c) 値 + 消滅 ((1.3)(a) masking engine
   `eq_zero_of_mem_of_inner_supported_eq_zero` S05:2158 再利用) → (4.3.d) 次数合同
   (Res_{W₁} + 正則指標) → (4.4) (小) → (4.5) ([Is]6.32 = ConjugationBrauer 形式化済)。

正本 = 本ノート (session 20)。**Don't re-grind (4.2)/(4.3.a)/sdiff-isometry 基盤 —
完成・axiom-clean。(4.1) は InducedIrreducible に在る。**

## 2026-06-10 (session 21, b-peterfalvi): ✅ (4.3.b) step 1+2 — per-column signed family `exists_columnSignedFamily`

新 leaf **`OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean`** を作成 (OddOrder.lean 登録済)。
session 20 の「次の一手」step 2 = (1.4) per-column 適用を完成。build-green + axiom-clean
(`[propext, Classical.choice, Quot.sound]` のみ)。

### ✅ 着地 (session 21)

`S06.Hypothesis L` 上 (`[Fintype L]`, recipe section で `[Invertible (Nat.card L : ℂ)]` +
`[Fintype ↥(W₁⊔W₂)]` + `[Invertible (Nat.card ↥(W₁⊔W₂):ℂ)]` + `[NeZero (Nat.card W1)]`):

1. **support 補題 (一般 hyp)**: `omegaProdChar_apply_of_mem_W2` (列内 ω は W₂ 上 χ₂∘wSnd で
   χ₁ 非依存) + `omega_omegaProdChar_sub_eq_zero_of_mem_W2` (列差は W₂ で消える)。
2. **packaging**: `omegaColumnDiff χ₁ χ₁' χ₂ : SupportedOnV ℂ sdiffTICyclicHypothesis`
   (= ω_{ij}−ω_{kj} ∈ CF(W, W−W₂)) + `omegaColumnDiff_coe` (rfl simp)。
3. **再添字**: `neZero_card_W1` (≥3 から) + `w1BaseEquiv` (card_charGroup 経由 `Fin w₁ ≃ Ŵ₁`)
   + **`w1CharEquiv`** (swap で `0 ↦ 1` に pin; `w1CharEquiv_zero`/`_injective`)。
4. **列族**: `chiColumn χ₂ : Fin w₁ → Irr(W)`, `i ↦ ω(omegaProdChar (e i) χ₂)` +
   `chiColumn_zero`/`_injective`/`_apply_one` (全 linear, degree 1)。
5. **(1.4) 適用**: `induceZ` (= Ind_W^L の ℤ-linear化 `induceLinear.restrictScalars ℤ`) +
   `isometryDifferenceImage_induceZ` (rfl: image = Ind(diff)) +
   **`isometryDifferenceImage_eq_dade`** (image = sdiffDade(α), `tau_eq_induce` 経由) +
   **`exists_columnSignedFamily`** (capstone): 3 hypotheses
   [virtual=`induce_mem_ZIrr`, degree-0=`induce_apply_one`+chiColumn_apply_one,
   isometry=`isometryDifferenceImage_eq_dade`+`full_inner_eq`] → `isometry_difference_pair_structure`
   ⟹ `∃ data : SignedIrreducibleDifferenceFamily L w₁, ∀ i, Ind(ω_{ij}−ω_{0j}) = data.signedDifference i`
   (= δ_j•(μ_{ij}−μ_{0j}), δ_j=±1, μ injective)。**列内 distinct は `.injective` field**。

### 🔑 KEY (再調査するな)

- **σ と (1.4)-isometry は別 hyp**: σ=`toTICyclicHypothesis` (V=W−(W₁∪W₂)=Vdiff, `exists_sigma`
  が `hVeq` 要求)、(1.4) の等長は `sdiffTICyclicHypothesis` (V=W−W₂, より大きい TI)。ω は W のみ
  依存ゆえ両 hyp で共有 (defeq)。
- **bridge instance 必須**: `h.sdiffTICyclicHypothesis.W` は `h.W1⊔h.W2` と defeq だが instance 探索は
  構文的 → recipe section に `instFintypeSdiffW`/`instInvertibleCardSdiffW` (`‹_›` で W₁⊔W₂ 形から移送)。
- **NeZero は statement binder に**: `(0 : Fin w₁)` を含む statement は `[NeZero (Nat.card W1)]` を
  binder に持つ必要 (proof 内 haveI は手遅れ)。use site で `haveI := h.neZero_card_W1`。
- **omega は ℤ-induction 経路**: 3 hypotheses のうち virtual/degree は素の induce 補題 (Dade 不要)、
  isometry のみ Dade (induce は一般に非等長; TI-supported でのみ等長)。
- Lean 地雷: (i) `rw [def]` は def 展開不可 → `rfl`-have or `congrArg`; (ii) omega defeq を omega
  tactic は見ない → 明示型 `have h3 : 3 ≤ Nat.card h.W1 := …`; (iii) coercion 先型は omega 本来の
  出力型 `↥sdiffTICyclicHypothesis.W` に合わせる (構文的 instance 探索)。

### ✅ 着地 (session 21 cont.): step 3 = cross-column distinctness COMPLETE

`exists_columnSignedFamily` の上に列間 distinct を完成 (全 build-green + axiom-clean):

1. **`columnFamily`** (choice) + `columnFamily_spec` — per-column `SignedIrreducibleDifferenceFamily L w₁`。
2. **`omega_diff_cross_inner_eq_zero`** (一般 hyp): χ₂≠χ₂' で ω-差の CF(W) 直交 (4 項とも
   `omegaProdChar` 別 index ⟹ `omega_inner_ne` で 0)。`omegaProdChar_ne_of_ne_right` 補助。
3. **`ind_cross_inner_eq_zero`**: Dade 等長 (`sdiffFullDadeIsometryData.inner_eq`) で Ind 像の列間直交
   = ω-差直交 = 0。
4. **`columnFamily_difference_apply_one`** (μ-差は 1 で消える, sign 除去) +
   **`columnFamily_difference_cross_inner_eq_zero`** (μ-差の列間直交, 両 sign 除去;
   `Int.cast_smul_eq_zsmul`+`inner_smul_left/right`+`star_intCast`)。
5. **`columnFamily_cross_products_zero`** (核): (4.1) `pairwise_inner_eq_zero_of_orthogonal_signedDifference`
   適用 (u=v=1, witnesses k,k'≠0) → 4 cross products `(μ_{kj},μ_{k'j'})`/`(μ_{kj},μ_{0j'})`/
   `(μ_{0j},μ_{k'j'})`/`(μ_{0j},μ_{0j'})` 全 = 0。
6. **`columnFamily_mu_ne`** (capstone): χ₂≠χ₂' で μ_{ij}≠μ_{i'j'} (i,i'=0? の 4 ケース分析で
   cross_products の適切な射影を選択; nonzero witness=`⟨1,one_lt_card_W1⟩`) +
   **`columnFamily_mu_injective`** (global: (χ₂,i)↦μ injective; 列内=`.injective`, 列間=`columnFamily_mu_ne`)。

Lean 地雷追記: (iv) (4.1) の `u•γ` は `((1:ℝ):ℂ)•` ⟹ `Complex.ofReal_one`+`one_smul`;
(v) `inner_smul_right` は mathlib と RepresentationTheory で曖昧 → 後者を明示修飾;
(vi) `difference`/`classFunction` abbrev は exact では defeq だが simpa では要 `difference_apply`/`classFunction_apply`。

### ✅ 着地 (session 21 cont.²): step 4 foundation + CF(W,W−W₂) 基底 COMPLETE

`eq_sigma_of_apply_eq_on_V` (S05:3637) は `σ(ω_{ij})=δ_j μ_{ij}` を **hres (∀v∈V, (δ_j μ_{ij})(v)=ω_{ij}(v))
のみ**に還元 (i: ZIrr/ii: inner=1 は易; NC≤2 は内部)。**🔑 (1.3)(b) (mmd 04.3 L17) が hres を供給**:
orthonormal family μ で `Ind ψ_j=∑_i(ψ_j,χ_i)μ_i` なら **μ_i|_A=χ_i|_A** (個別値!) — 私の step-3
μ-orthonormality がちょうど前提。(1.3)(b) 証明 = (1.3)(a) [masking `CF(W,A)^⊥=CF(W,W−A)`
(`eq_zero_of_mem_of_inner_supported_eq_zero` S05:2158) + Frobenius `inner_induce_eq_inner_restrict`
(InducedCharacter:531)] + μ-orthonormality。**2 commits landed**:
- biorthogonality `omegaColumnDiff_inner_omega_self`/`_ne` + `omegaColumnDiff_linearIndependent`;
- **基底 `omegaColumnDiffBasis`** (`card_supportInSubgroup_sdiff`=|W−W₂|=(w₁−1)w₂ [complement of W₂
  in W] + `finrank_sdiffSupported` + `basisOfLinearIndependentOfCardEqFinrank`)。

### ✅ 着地 (session 21 cont.³): step 4 (1.4)-image bridge + g-setup COMPLETE (commit 8d5c193f)

- **`chiColumn_w1CharEquiv_symm`**: ω_{kl}=chiColumn l (e⁻¹k) (`rw [chiColumn, Equiv.apply_symm_apply]`)。
- **`induce_omegaColumnDiff_eq`**: `Ind_W^L(ω_{kl}−ω_{0l})=(columnFamily l).signedDifference (e⁻¹k)`
  (`← columnFamily_spec`+`isometryDifferenceImage_induceZ`; val-eq は `rw[chiColumn_..symm, chiColumn_zero]; exact omegaColumnDiff_coe` で X=X 罠回避)。
- **`certainTypeRestrictDiff`** (= g) def 済。

### ▶▶ 次 = step 4 残: g⊥基底 → masking → eq_sigma [recipe 確定・Lean 名前判明・再調査するな]

**🔑 Lean 名前/手法 (今回判明)**: Frobenius=`ClassFunction.inner_induce_eq_inner_restrict` (qualify必須);
omega/μ 両方 `irreducibleCharacter_inner` (=if χ=χ' then 1 else 0; `omega_inner` は存在せず self/ne のみ);
条件変換は **`if_congr <iff> rfl rfl`** で; **`omega_injective.eq_iff`** + **`omegaProdChar_inj`** (W側) /
**`columnFamily_mu_injective.eq_iff`** (L側, global μ injective を直接!); `e.symm` 変換は `Equiv.symm_apply_eq`;
sign²=1 は `rcases sign_eq <;> norm_num`。

1. **`certainTypeRestrictDiff_inner_basis`** (χ₂)(i)(l){k:≠1}: `inner(omegaColumnDiff k 1 l : CF)(g χ₂ i)=0`。
   `rw [certainTypeRestrictDiff, inner_sub_right, ← ClassFunction.inner_induce_eq_inner_restrict,
   induce_omegaColumnDiff_eq l k]` ⟹ goal `T1 − T2 = 0` (T1=L側 `inner(signedDiff_l(e⁻¹k))(δ_{χ₂}μ_{i,χ₂})`,
   T2=W側 `inner(omegaColumnDiff k 1 l)(chiColumn χ₂ i)`)。**T1=T2 を示す**:
   - **T2** (W側): `irreducibleCharacter_inner` ×2 → `(if ω_{kl}=ω_{e i,χ₂} then 1 else 0)−(if ω_{0l}=ω_{e i,χ₂}...)`;
     `if_congr` で条件 → `(e⁻¹k=i∧l=χ₂)` / `(0=i∧l=χ₂)` (omega_injective.eq_iff+omegaProdChar_inj+`k=e i↔e⁻¹k=i`)。
   - **T1** (L側): `signedDifference_apply`+`difference`+`← Int.cast_smul_eq_zsmul ℂ`×2+`inner_smul_left`+
     `RepresentationTheory.inner_smul_right`+`star_intCast`+`inner_sub_left`+`classFunction`×3+
     `irreducibleCharacter_inner`×2 → `sign_l·sign_χ₂·((if μ_{e⁻¹k,l}=μ_{i,χ₂}..)−(if μ_{0,l}=μ_{i,χ₂}..))`;
     条件 → `(l=χ₂∧e⁻¹k=i)` via `columnFamily_mu_injective.eq_iff` (Prod.ext)。
   - **by_cases l=χ₂**: l=χ₂ で sign²=1, 両条件 `[e⁻¹k=i]−[0=i]` 一致; l≠χ₂ で T1 の μ-if は `columnFamily_mu_ne` で 0,
     T2 の omega-if も l≠χ₂ で 0 ⟹ 両 0。**✅ 全 i 相殺検算済 (i=0 で ω_{ij} 項の −[0=i] が効く罠)**。
   ⚠ session 21 cont.³ で初回実装試行 → omega_inner 名 + inner_induce qualify + if 条件変換で未完;
   上記名前で再実装すれば通る (~50-70 行, 検算は完了)。
2. **masking**: g ⊥ 基底 ⟹ `(innerDual g).comp subtype = 0` on `SupportedOnV` (`omegaColumnDiffBasis.ext`)
   ⟹ ∀φ supported, inner φ g=0 ⟹ `eq_zero_of_mem_of_inner_supported_eq_zero` (↥W abelian ∴ A conj-closed)
   ⟹ g a=0 ∀a∈A ⟹ `(δ_{χ₂}•μ_{i,χ₂})(a:L)=ω_{ij}(a)` on W−W₂ ⊇ V。
3. **eq_sigma**: hres (V⊆W−W₂ 値一致) + ZIrr + inner=1 → `eq_sigma_of_apply_eq_on_V` (`toTICyclicHypothesis`,
   hVeq=rfl, app=⟨toTICyclic Dade⟩) ⟹ **σ(ω_{ij})=δ_j μ_{ij}** = (4.3.b) capstone。⚠ σ=`toTICyclicHypothesis`(V=Vdiff),
   (1.4)/基底=`sdiffTICyclicHypothesis`(V=W−W₂); ω 共有 (defeq)。

その後 (4.3.c)(d) → (4.4)(小) → (4.5) ([Is]6.32=ConjugationBrauer 済)。

正本 = 本ノート (session 21 + cont. + cont.²)。**Don't re-grind step 1-3 + step-4 基底 — 完成・axiom-clean。
残 = 上記 1-3 (g⊥基底計算が intricate だが検算済; ~80-100 行)。bridge instance + defeq-bridge `have hc` +
sign-removal パターン確立。**

## 2026-06-10 (session 22, b-peterfalvi): ✅✅✅ (4.3.b) COMPLETE — certain-type characters as σ-images

session 21 cont.³ が残した step-4 recipe (1-3) を完全形式化。**Peterfalvi (4.3.b) は任意の admissible
`S06.Hypothesis L` に対し成立**: σ(ω_{ij}) = δ_j·μ_{ij}。全 `S06_CertainTypeCharacters.lean`、
sorry-free・axiom-clean・leaf green (3452 jobs)。3 commits。S06_CertainTypeCharacters は importer 無の真 leaf。

### ✅ 着地 (session 22)
- **step 1 = `certainTypeRestrictDiff_inner_basis`** (commit 173d66d0): g = Res_W(δ_j·μ_{ij}) − ω_{ij}
  が基底 ω_{kl}−ω_{0l} と直交。recipe 通り一発で通過 (recon 検算が正確だった)。
  - spine: `certainTypeRestrictDiff` → `inner_sub_right` → `sub_eq_zero` → Frobenius
    `← ClassFunction.inner_induce_eq_inner_restrict` → (1.4)-image `induce_omegaColumnDiff_eq` →
    `signedDifference_apply` + `← Int.cast_smul_eq_zsmul ℂ`×2 + `inner_smul_left`/`inner_smul_right`/
    `star_intCast` + `difference_apply`/`classFunction_apply`×2 + `inner_sub_left` + `omegaColumnDiff_coe` +
    `chiColumn` + `inner_sub_left` + `irreducibleCharacter_inner`×4。
  - `by_cases hl : l=χ₂`: diagonal は `(columnFamily l).injective.eq_iff` + `omega_injective.eq_iff` +
    局所 `hcol` iff (omegaProdChar_inj 単方向→iff) + `← Equiv.symm_apply_eq` + `hs1 : e.symm 1 = 0` で
    両条件を `e.symm k = i`/`0 = i` に統一 → sign²=1 (`← mul_assoc, hsign2, one_mul`)。
    off-diagonal は `if_neg`×4 (`columnFamily_mu_ne hl`×2 + omega 不等 ×2) + `ring`。
- **step 2 = masking** (commit 97c8e2b8): `omegaColumnDiffBasis_apply` (coe lemma via
  `coe_basisOfLinearIndependentOfCardEqFinrank`, alphaBasis_apply ミラー) +
  `certainTypeRestrictDiff_apply_eq_zero_of_mem_V` (g は W−W₂ 上消失)。
  - `vanishOnV_of_inner_alphaCF` (S05:3263) の純粋ミラー: `innerLeftFunctional g` (ℂ-linear,
    inner 第1引数線形) を `Module.Basis.ext h.omegaColumnDiffBasis` で 0 (step1)→
    `eq_zero_of_mem_of_inner_supported_eq_zero` (W−W₂ は abelian W で conj-closed)。
- **step 3 = capstone** (commit e97dd094): `toTICyclicFullDadeApplication` (=(3.1)-for-L Dade,
  `HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)`、sdiffFullDadeIsometryData ミラー) +
  `sigma_chiColumn_eq_certainType`。
  - `eq_sigma_of_apply_eq_on_V rfl app (chiColumn χ₂ i) hZIrr hnorm1 hres`:
    hZIrr=`(ZIrr L).smul_mem _ (mu i).mem_ZIrr`; hnorm1=δ_j²=1 (`← Int.cast_smul_eq_zsmul`+
    `inner_smul_left/right`+`star_intCast`+`irreducibleCharacter_inner if_pos`+sign_eq);
    hres=値一致 (step2 を `toTICyclic.V ⊆ sdiff.V`=`⟨hv.1, fun h2 => hv.2 (Or.inr h2)⟩` で transport,
    `certainTypeRestrictDiff`+`sub_apply`+`sub_eq_zero`+`restrict_apply` で `exact hg`)。
  - **🔑 W 整合の罠**: `chiColumn χ₂ i : IrreducibleCharacter sdiff.W` を `ClassFunction toTICyclic.W ℂ`
    に**直接 coercion すると Type mismatch** (defeq だが coercion machinery 厳格、toTICyclicHypothesisOfV の
    非 reducible unfold が要る)。**回避: statement で `(... : ClassFunction sdiff.W ℂ)` と ascription** →
    sigma 適用時の LinearMap-application defeq check に委ねる (sdiff.W=toTICyclic.W=h.W1⊔h.W2 は unifier が unfold)。
    bridge instance `instFintypeToTICyclicW`/`instInvertibleCardToTICyclicW` 追加。

### ✅✅✅ Theorem (4.3) COMPLETE (a)(b)(c)(d) — session 22 cont.
- **(4.3.c)** ✅ **DONE 両 part**: part1 `certainType_apply_eq_of_mem_V` (μ_{ij}(x)=δ_j ω_{ij}(x),
  commit `acd39ea1`); part2 `certainType_vanishes_of_ne` (μ_{ij} 以外の Irr(L) は W−W₂ 上消失,
  commit `438fddef`)。**masking engine を `apply_eq_zero_of_mem_V_of_inner_omegaColumnDiff` に抽出**
  (f⊥ω-basis⟹f|_{W−W₂}=0, 両 vanishing で共有); part2 = Res_W μ ⊥ basis (Frobenius+(1.4)image,
  `inner_omegaColumnDiff_restrict_eq_zero`)。
- **(4.3.d)** ✅ **DONE** `certainType_degree_modEq` (∃a, μ_{ij}(1)=δ_j+a·w₁, commit `6421038f`)。
  **🔑 経路 (論文の regular-char を回避)**: ψ=Res_{W₁⊆W}(Res_W μ_{ij})−δ_j·Res_{W₁⊆W} ω_{ij} を
  **↥W 上で**構成 (L↔W reindexing 不要・両者 ↥W 由来) → ψ は W₁^# 上消失 (4.3.c) → 汎用
  `exists_apply_one_eq_card_mul_of_vanishing_off_one` (ZIrr 非単位元消失⟹ψ(1)=card·ℤ; masking sum
  `card·⟨ψ,1⟩=∑ψ` が単位元項に collapse, `card_mul_inner`+`inner_mem_ZIrr_int`) → ψ(1)=μ_{ij}(1)−δ_j。
  coercion: ↥(W₁.subgroupOf W) 二重 coe, `Subgroup.mem_subgroupOf`, `disjoint_iff.mp W_disjoint`,
  `Subtype.ext rfl` で値点一致, Invertible は `invertibleOfNonzero`+`Nat.card_pos.ne'`。

### ▶▶ 次 = (4.4) → (4.5) [§6 構造定理, K-kernel/Clifford 機構]
- **(4.4)** μ_{i0} (j=0 列) = K⊆ker の Irr(L); δ_0=1, μ_{00}=1_L。
  - ✅ **(0,0)-anchor DONE** (`certainType_zero_column_anchor`, commit `a3ce7133`): δ_0=1 ∧ μ_{00}=1_L。
    σ(ω_{00})=σ(1_W)=1_L (`chiColumn_one_zero_eq_trivial`+`sigma_trivial`) ⟹ δ_0•μ_{00}=1_L ⟹
    ⟨μ_{00},1_L⟩∈{0,1} で δ_0=1 (oneIrr:=⟨trivialClassFunction,_⟩ bundling)。
  - 🔲 **残 = kernel 特徴付け** (χ∈Irr(L), K⊆ker χ ⟺ χ=μ_{i0}): **L/K≅W₁ (isComplement) + inflation 機構が要**。
    forward: K⊆ker χ ⟹ χ は L/K≅W₁ (abelian cyclic) を経由 ⟹ **χ linear** (χ(1)=1) ⟹ Res^L_W χ=ω_{i0}
    (W₂≤K⊆ker で W₂ 上自明) ⟹ V 上 χ=ω_{i0} ⟹ `eq_sigma_of_apply_eq_on_V` で χ=σ(ω_{i0})=δ_0 μ_{i0}=μ_{i0}。
    converse: K⊆ker μ_{i0} (μ_{i0} は |Irr(L/K)|=w₁ 個の inflation)。**InflationCharacter 機構 (repo 済) の recon が最初の手。**
- **(4.5)** μ_j=∑_i μ_{ij}, χ_j=Res_K μ_{ij}∈Irr(K) (Clifford, K∩W=W₂ で μ-diff が K 上消失),
  Ind^L_K で Irr(L) を尽くす ([Is]6.32=ConjugationBrauer 済)。→ (4.6)-(4.9) → S08 capstone CertainType case-B。

正本 = 本ノート (session 22)。**Don't re-grind Theorem (4.3) (a)-(d) — 完成・axiom-clean。** capstone =
`sigma_chiColumn_eq_certainType` (σ(ω_{ij})=δ_j μ_{ij})。**W 整合は sdiff.W ascription で回避済 (再調査するな)。**
**masking engine = `apply_eq_zero_of_mem_V_of_inner_omegaColumnDiff` (再利用可)。汎用 degree-divisibility =
`exists_apply_one_eq_card_mul_of_vanishing_off_one` (upstream 候補)。**

## 2026-06-11 (session 23, b-peterfalvi): ✅✅✅ Peterfalvi (4.4) COMPLETE — kernel 特徴付け 両方向 + iff

session 22 が残した「(4.4) kernel 特徴付け」を完全形式化。**μ_{i0} (j=0 列) は ちょうど K⊆ker の Irr(L)**。
全 `S06_CertainTypeCharacters.lean`、sorry-free・axiom-clean・full build 3630 + AxiomsCheck green。
2 commits (`be084608` forward, 次=converse+iff)。**§6 frontier = (4.5) に前進。**

### ✅ 着地 (session 23)
- **forward** `exists_certainType_zero_column_eq_of_subset_characterKernel` (χ∈Irr L, K⊆ker χ ⟹ ∃i, μ_{i0}=χ):
  χ は L/K(abelian)経由で linear ⟹ Res χ=ω_{i0} on V ⟹ `eq_sigma_of_apply_eq_on_V` で χ=δ_0μ_{i0}=μ_{i0}。
  - helpers: `instKNormal` (K⊴L を instance 化 → `L ⧸ h.K` が elaborate), `isCyclic_quotient_K` /
    `isMulCommutative_quotient_K` (L/K≅W₁ via `IsComplement'.QuotientMulEquiv` → cyclic → commutative),
    `chiColumn_one_apply` (ω_{i0}(w)=(w1CharEquiv i)(wFst w) 値補題)。
  - linearize: `χ.2.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one h1` で χ̂:L→*ℂˣ。χ̂ は K 上自明
    (K⊆ker+χ(1)=1)。v=x·y∈V (x∈W₁,y∈W₂⊆K) で χ(v)=χ̂(x)=χ₁(wFst v)、χ₁=χ̂|_{W₁}, i=`w1CharEquiv.symm χ₁`。
- **converse** `subset_characterKernel_certainType_zero_column` (∀i, K⊆ker μ_{i0}): inflation 全単射で counting。
  - `card_irreducibleCharacter_quotient_K`: |Irr(L/K)|=w₁ (linearIrr 全単射 [abelian] +
    `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` [Pontryagin] + `QuotientMulEquiv` card)。
  - `card_kernelContaining_quotient_K`: {χ//K⊆ker}≃Irr(L/K) (inflate 全単射)。
  - forward で得る単射 Ψ:Irr(L/K)→Fin w₁ が等濃度ゆえ全射 (`Fintype.bijective_iff_injective_and_card`) ⟹
    μ_{i0}=inflate χ̄ ⟹ `subset_characterKernel_inflate`。
- **iff** `subset_characterKernel_iff_eq_certainType_zero_column` (capstone, 両方向 bundle)。

### 🔑 KEY / 再調査するな
- **inflation API は N を explicit auto-bound 第1引数に取る** (`inflate`/`inflate_injective`/
  `subset_characterKernel_inflate`/`exists_inflate_eq_of_subset_characterKernel`/`inflate_apply_one`) →
  **必ず `(N := h.K)` を付ける** (付けないと χbar が N スロットに入り型エラー)。
  `import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter` を S06_CertainTypeCharacters に追加済。
- **abelian→linear→multiplicative の repo infra は全て既存** (`LinearCharacter.lean`):
  `IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative` / `map_mul_of_apply_one_eq_one` /
  `exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one` / `linearIrreducibleCharacter(_apply/_injective)`。
- **W 整合 (chiColumn_one_apply の値一致)**: `(w1CharEquiv i)` の domain は `W₁.subgroupOf (W₁⊔W₂)`、
  `wFst` の出力は `W₁.subgroupOf sdiff.W` — defeq だが DFunLike の α が違うので rw の reducible-rfl で閉じない。
  **`exact congrArg _ hmatch` (default transparency) で閉じる**。`χ1` は sdiff.W 上の subgroupOf で定義し
  `w1CharEquiv.symm` には defeq cast で渡す。

### ▶▶ 次 = (4.5) [§6 構造定理, Clifford/Ind 機構] → (4.6)-(4.9) → S08 case-B
- **(4.5)** μ_j=∑_{i} μ_{ij}, χ_j=Res^L_K μ_{ij}∈Irr(K) (Clifford; (4.3.b) で μ_{ij}−μ_{0j} は W−W₂^L 外で消える
  ⟹ K∩W=W₂ で K 上消失 ⟹ χ_j は i 非依存), Ind^L_K χ_j=μ_j。(b) χ∉{χ_j}⟹Ind^L_K χ∈Irr(L) かつ Irr(L) を尽くす
  (g∈W₁^# の固定点計数 + [Is]6.32=`ConjugationBrauer` 済 + (1.5.b))。
  - **infra 確認済 (session 23 recon, 再 recon 不要)**: 既約↔誘導/制限 Clifford 機構は `Clifford.lean`
    (`restrictionMultiplicity`(+`_int`/`_conjBy_right`[Normal]/`_nonneg`), `IrreducibleCharacter.LiesOver`,
    restriction-constituent API)。誘導は `InducedCharacter.lean` (`induce`/`induceSum`,
    **support 補題 `support_induce_subset_conjugatesInto` / `support_induce_subset_of_normal`** =
    (4.5.a) の「K 上消失」の核)。(4.5) は (4.4) 同等規模の Clifford 本体作業 (単一 leaf でない)。
- これ以降 (4.6)+ は G-埋込 `CertainTypeHypothesis` + A-set + τ Dade が要 ((4.8) は (3.8) full trichotomy 待ち=§12 defer)。

正本 = 本ノート (session 23)。**Don't re-grind (4.4) — forward/converse/iff 完成・axiom-clean。**
**inflation API は `(N := h.K)` 必須 (再調査するな)。**

## 2026-06-11 (session 24, b-peterfalvi): ✅ (4.5)(a) 土台 — μ_{ij}−μ_{0j} は K 上消失 + χ_j は i 非依存

新 leaf **`S06_CertainTypeClifford.lean`** を起こした (新主結果番号ゆえ新 leaf, 粒度規約どおり;
`OddOrder.lean` 配線済み, `import OddOrder.Peterfalvi.S06_CertainTypeCharacters`)。commit `c1ee2178`,
axiom-clean (allowlist 3), **full build 3631 + AxiomsCheck OK**。

### ✅ 着地 (session 24) — 全 `Hypothesis` 名前空間 (`OddOrder.Peterfalvi.S06.Hypothesis.*`)
- **`mem_W2_of_mem_sup_of_mem_K`** (`a∈W₁⊔W₂ → a∈K → a∈W₂`; 原文 "K∩W=W₂"): `exists_mul_of_mem_sup`
  で a=x·y (x∈W₁,y∈W₂≤K) → x=a·y⁻¹∈K → x∈K⊓W₁=⊥ (`isComplement.disjoint`) → x=1 → a=y∈W₂。
- **`induce_chiColumnDiff_eq_zero_of_mem_K`** (Ind_W^L(ω_{ij}−ω_{0j}) は K 上消失):
  `ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet` を A:={w:↥W | (w:L)∉W₂} で。
  support⊆A = 列内 ω は W₂ 上一致 (`omega_omegaProdChar_sub_eq_zero_of_mem_W2`; **`.support` は
  `ClassFunction.mem_support` で開く — `Function.mem_support` でない**)。k∉conjugatesIntoSet =
  `K_normal.conj_mem k hk x⁻¹` (要 `simpa`, x⁻¹⁻¹=x) で x⁻¹kx∈K, `mem_W2_of_mem_sup_of_mem_K` で W₂ 落ち。
- **`columnFamily_difference_vanishes_on_K`** ((columnFamily χ₂).difference i は K 上 0):
  `← columnFamily_spec`+`isometryDifferenceImage_induceZ` で induce 形へ → 上補題 → `signedDifference_apply`
  +`zsmul_eq_mul` で δ_j·diff=0, δ_j=±1≠0 → diff=0。
- **`restrict_certainType_eq`** (Res^L_K μ_{ij} = Res^L_K μ_{0j}, (4.5.a) 前半): `ext k`+`restrict_apply`
  +`← sub_eq_zero`+`difference_apply`/`classFunction_apply` で上補題に帰着。

### ▶▶ 次 = (4.5)(a) 後半 [χ_j∈Irr(K) + Ind^L_K χ_j=μ_j] — Clifford degree-counting (~200 行, 別単位)

**全 API 特定済み・再 recon 不要。recipe (検算済み, 論文 mmd 04.6 L45-49):**
1. **χ_j 定義**: `ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0)`。IsCharacter は (mu 0).isIrreducible
   .isCharacter を restrict 越しに (要確認: restrict が IsCharacter 保存。`restrict_repCharacterClassFunction`
   InducedCharacter:625 経由 or `IsCharacter.restrict` を探す/自作)。
2. **index=w₁**: `K.index = Nat.card h.W1`。`Subgroup.index_eq_card` (K.index=Nat.card(L⧸K))+
   `Nat.card_congr h.isComplement.QuotientMulEquiv.toEquiv` (S06_CertainTypeCharacters:300-301 と同型)。
   `(Ind χ)(1) = (K.index:ℂ)·χ(1)` = `ClassFunction.induce_apply_one`。
3. **constituent χ**: `exists_liesOver (h.columnFamily χ₂).mu 0 : ∃ θ:Irr K, LiesOver K (mu 0) θ`
   (= θ は Res(mu 0)=χ_j の constituent; LiesOver=restrictionMultiplicity≠0)。Clifford.lean:626。
4. **μ_{ij} liesOver θ**: restrictionMultiplicity K (mu i) θ = restrictionMultiplicity K (mu 0) θ
   (restrict 一致 = `restrict_certainType_eq` ⟹ multiplicity の inner が一致) ⟹ LiesOver K (mu i) θ。
5. **μ_{ij} は Ind θ の constituent**: `inner_induce_ne_zero_iff_liesOver (mu i) θ` (Clifford:583)
   ⟹ ⟨Ind θ, mu i⟩≠0。
6. **degree bound (iv) [要自作 helper]**: 「相異なる constituent (∀θ∈S, ⟨χ,θ⟩≠0, distinct) の次数和
   ∑_{θ∈S}(θ1).re ≤ (χ1).re」。`IsCharacter.exists_natFinsupp_eq_sum` から
   `apply_one_re_le_of_inner_ne_zero` (Clifford:1065, **単一版は既存**) を Finset 化:
   χ(1).re=∑_{a∈m.support}m_a(a1).re (全項≥0, deg>0), S⊆m.support, m_θ≥1, `Finset.sum_le_sum_of_subset_of_nonneg`。
   S = (mu ·) の像 finset (w₁ 個, columnFamily.injective で distinct)。
7. **等次数⟹一致 (H2) [要自作 or sharper bound]**: χ_j(1).re=χ(1).re ∧ χ constituent ⟹ χ_j=χ。
   同 decomposition で support={χ}, m_χ=1 を絞る (positivity)。⟹ χ_j∈Irr(K)。
8. **chain** (.re で): w₁χ(1)=(Ind θ)(1) ≥ ∑_iμ_{ij}(1) = w₁χ_j(1) ≥ w₁χ(1)
   [μ_{ij}(1)=χ_j(1) via restrict@1; χ_j(1)≥χ(1) via `apply_one_re_le_of_inner_ne_zero`] ⟹ 全等。
9. **Ind χ_j=μ_j**: 等号成立で Ind θ の constituent は ちょうど {μ_{ij}} 各 mult 1 ⟹ Ind θ=∑_iμ_{ij}=μ_j。

### ▶▶ その後 = (4.5)(b) [Ind^L_K χ で Irr(L) を尽くす] → (4.6)-(4.9) → S08 case-B
- g∈W₁^# の K-共役類への作用: ⟨g⟩ FPF on class C ⟹ |⟨g⟩| ∣ |C| ∣ |K| ⟹ coprime(|K|,w₁) 矛盾
  (`h.card_coprime`) ⟹ ∃x∈⟨g⟩^#, C∩C_K(x)=C∩W₂≠∅ ⟹ g-不変な K-class は ≤ w₂ 個。
- **Brauer [Is]6.32**: g-不変 class 数 = g-固定 Irr(K) 数 ⟹ g 固定の Irr(K) は ≤ w₂ 個。
  **`ConjugationBrauer.lean` / `BrauerPermutationUnconditional.lean` で正確な補題名を grep (まだ未特定)**。
- χ_j (w₂ 個) は g 固定 (μ_{0j}∈Irr(L)) ⟹ χ∉{χ_j} は g 非固定 ⟹ I_L(χ)=K ⟹
  **`isIrreducibleCharacter_induce_of_inertia_eq θ (hinertia : inertia θ=K)`** (InducedIrreducible:424,
  =(1.5.b); S08 `inertia_eq_H_of_c2` が同型論法の先例) ⟹ Ind^L_K χ∈Irr(L)。exhaustion で締め。

正本 = 本ノート (session 24)。**Don't re-grind (4.5)(a) 土台 — 完成・axiom-clean (c1ee2178)。**
**degree-counting helper (iv)(H2) は exists_natFinsupp_eq_sum から自作 (単一版 apply_one_re_le は既存)。
他レーン (BG/RepresentationTheory) ファイルは触らず helper は leaf 内に置く (CLAUDE 規約)。**

## 2026-06-11 (session 25, b-peterfalvi): ✅✅ (4.5)(a) 完結 — χ_j∈Irr(K) + Ind^L_K χ_j = μ_j

session 24 が残した「(4.5)(a) 後半」を完全形式化。全 `S06_CertainTypeClifford.lean`、sorry-free・
axiom-clean (allowlist 3: propext/Classical.choice/Quot.sound)・**full build 3631 + AxiomsCheck OK**。
leaf 557 行 (1500 trigger 未満)。**§6 frontier = (4.5)(b) [Irr(L) exhaustion] に前進。**

### ✅ 着地 (session 25)
- **core `exists_irreducible_restrict_certainType`** (`OddOrder.Peterfalvi.S06.Hypothesis.*`):
  `∃ θ:Irr(↥K), Res^L_K μ_{0j} = ↑θ ∧ Ind^L_K ↑θ = ∑_i μ_{ij}` を一度に返す
  (packaging の defeq 罠を避けるため両結論を 1 証明に束ねた)。
  - θ = `exists_liesOver (cf.mu 0)` の constituent → 各 μ_{ij} liesOver θ (`restrict_certainType_eq`
    で制限一致) → μ_{ij} は Ind θ の constituent (`inner_induce_ne_zero_iff_liesOver`) →
    degree bound `w₁·μ_{0j}(1) = ∑_i μ_{ij}(1) ≤ (Ind θ)(1) = w₁·θ(1)` で `μ_{0j}(1) ≤ θ(1)` →
    `eq_of_apply_one_re_le_of_inner_ne_zero` (singleton tight-bound) で χ_j = ↑θ。
  - degree 等号成立 ⟹ `eq_sum_of_apply_one_re_le_of_inner_ne_zero` (Fin w₁ tight-bound) で
    Ind ↑θ = ∑_i classFunction = ∑_i ↑μ_{ij} (最後の classFunction→↑mu は rw が defeq で閉じる)。
- **派生 (thin, core 消費)**: `certainTypeRestrict_isIrreducible` (χ_j∈Irr(K)) +
  `induce_restrict_certainType_eq` (Ind^L_K χ_j = μ_j; χ_j=↑θ で書換)。
- **helper `index_K_eq`** (`[L:K] = w₁`): `Subgroup.index_eq_card` + `isComplement.symm.QuotientMulEquiv`
  (S06_CTC:300-301 と同パターン)。

### 🔑 degree-counting 汎用補題 (leaf 内, 全 `OddOrder.Peterfalvi.S06.*`, 汎用 G)
- **#1 `sum_apply_one_re_le_of_inner_ne_zero`**: IsCharacter χ + 単射既約 constituent 族 ⟹
  `∑_{i∈s}(f i 1).re ≤ (χ1).re` (`apply_one_re_le_of_inner_ne_zero` の Finset 版,
  `exists_natFinsupp_eq_sum` から `sum_le_sum`+`sum_le_sum_of_subset_of_nonneg`)。
- **#2 `eq_sum_of_apply_one_re_le_of_inner_ne_zero`**: さらに `(χ1).re ≤ ∑` ⟹ `χ = ∑_{i∈s} f i`
  (tight ⟹ support 完全同定: supp=image (sum_sdiff+正項), m_a=1 (`sum_eq_sum_iff_of_le`))。
- **#2' `eq_of_apply_one_re_le_of_inner_ne_zero`** (singleton, ι=Unit 経由): 既約 constituent θ で
  `(χ1).re ≤ (θ1).re` ⟹ χ = θ (等次数⟹一致)。

### ⚠ hub への hoist 候補 (再調査するな)
- **infra 4 補題を S08 から leaf に複製**: `isCharacter_restrict` / `inner_isCharacter_nonneg` /
  `induce_exists_natFinsupp_eq_sum` / `isCharacter_induce` (全て S08_CoherenceCore に既存だが S08 は
  S06 の**下流**ゆえ import 不可)。**これら + 上の #1/#2/#2' は本来 `Clifford.lean`/`InducedCharacter.lean`
  に属する汎用補題** → hub が Clifford へ hoist + S08 版と dedup するのが望ましい (CLAUDE ラッパー方針)。
  現状は CLAUDE「他レーン RepresentationTheory を触らない」に従い leaf 内複製。

### 🔑 KEY / 再調査するな (Lean 機構の罠)
- **`inner_induce_ne_zero_iff_liesOver` / `exists_liesOver` は `H : Subgroup G` が EXPLICIT 第1引数**
  (`variable (H : Subgroup G)` 由来) → `inner_induce_ne_zero_iff_liesOver h.K (mu i) θ` と H 明示必須
  (S03:699 が先例)。これらは `IrreducibleCharacter` namespace ゆえ `IrreducibleCharacter.` 修飾要。
- **`set` 禁止 (defeq 暴走)**: `set χj := restrict h.K (mu 0)` 等は χj を opaque fvar 化し
  `restrict h.K ((columnFamily χ₂).mu 0)` との defeq を切る → `:= hθ0` 等が落ちる。さらに
  `columnFamily := (...).choose` の unfold が絡むと `isDefEq`/`whnf` heartbeat timeout。
  **既存スタイル通り `h.columnFamily χ₂` を明示展開で書く**。packaged IrreducibleCharacter が要るときは
  core 定理が `exists_liesOver` の θ を返し下流は ↑θ で扱う (inline ⟨_,_⟩ の coe_mk 経由)。
- **`Finset.sum_image` は被加算関数 g が HO 単一化で決まらず term 適用が落ちる** → `rw [Finset.sum_image
  (fun x _ y _ h => hinj h)]` の **rw 形**にする (goal の具体形が f/g を決める; `(g := …)` 明示は g が
  image 関数側に化けて誤る)。
- **statement の `ClassFunction.induce h.K (...)` は `[Invertible (Nat.card ↥h.K : ℂ)]` を要求** (induce 定義が
  `(Nat.card H)⁻¹•` ゆえ) → **section variable / 定理 binder で渡す** (haveI は proof 内で遅すぎ statement に
  効かない)。`Fintype ↥h.K` は statement に出ない (inner/induce_char の proof のみ) ので **proof 内
  `haveI : Fintype ↥h.K := Fintype.ofFinite _`** に留める (binder にすると unusedFintypeInType 警告 +
  caller 負担)。caller は `haveI : Invertible (Nat.card ↥h.K:ℂ) := invertibleOfNonzero (…)` で供給。

### ▶▶ 次 = (4.5)(b) [Ind^L_K χ で Irr(L) を尽くす] → (4.6)-(4.9) → S08 case-B
- session 24 末尾の (4.5)(b) recon そのまま有効 (g∈W₁^# の K-class 作用 FPF + Brauer [Is]6.32=
  `ConjugationBrauer` 済 + (1.5.b) `isIrreducibleCharacter_induce_of_inertia_eq`)。χ_j (w₂ 個) は g 固定、
  χ∉{χ_j} は I_L(χ)=K で Ind∈Irr(L)、exhaustion で締め。
- 利用可能: `certainTypeRestrict_isIrreducible` / `induce_restrict_certainType_eq` / `index_K_eq` /
  上記 degree-counting #1/#2/#2'。

正本 = 本ノート (session 25)。**Don't re-grind (4.5)(a) — core+派生 完成・axiom-clean。**
**inner_induce/exists_liesOver は H explicit, set 禁止, sum_image は rw 形, induce statement は Invertible binder (再調査するな)。**

## 2026-06-11 (session 26, b-peterfalvi): ✅✅✅ Peterfalvi Theorem (4.5)(b) COMPLETE — Ind^L_K χ で Irr(L) を尽くす

(4.5)(b) を 3 文すべて完全形式化。全 `S06_CertainTypeClifford.lean` (975 行, 1500 trigger 未満)、
sorry-free・axiom-clean (allowlist 3)・**full build 3631 + AxiomsCheck OK**。**§6 frontier = (4.6)-(4.9) →
S08 case-B に前進。** 6 commits (301a6b79 / 3b112b93 / 93b44015 / 011645b0 / a1679621 + 着手時の build fix)。

### ✅ 着地 (session 26) — 全 `OddOrder.Peterfalvi.S06.Hypothesis.*`
- **counting 部品** (`card_fixed_irr_le_W2`, session 26 冒頭): g∈W₁^# 固定の Irr(K) は ≤ w₂ 個。
  `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm` ([Is]6.32 Brauer) で g-不変
  K-共役類数に等値 → `card_fixed_conjClasses_le_W2` (各 g-不変類が W₂ と交わる `conjClass_meets_W2` →
  W₂ 代表元単射)。
- **bridge** `mem_inertia_iff_isFixedPt_conjByPerm`: g∈inertia θ ↔ θ∈fixedPoints(conjByPerm g)。
  `IrreducibleCharacter.mem_inertia` + `conjByPerm_apply` の **defeq** (`exact Iff.rfl`)。
- **`chiRestrict χ₂` = χ_j を IrreducibleCharacter K に束ねる def** (+ `coe_chiRestrict` simp)。
  - `chiRestrict_isFixedPt`: ∀g∈L で fixed。`ClassFunction.conjBy_restrict` (L-指標の制限は L-共役不変)。
  - `chiRestrict_injective`: χ₂ で単射。Ind=μ_j (`induce_restrict_certainType_eq`) + `inner_sum_left` で
    ⟨μ_j,μ_{0j}⟩=1 (Finset.sum_ite_eq' + injective.eq_iff) vs ⟨μ_{j'},μ_{0j}⟩=0 (cross-column 直交
    `columnFamily_mu_ne`)。
  - `card_charGroup_W2`: |Ŵ₂|=w₂。`sdiffTICyclicHypothesis.card_charGroup_subgroupOf W2_le_W` 一発。
- **counting collapse** `exists_eq_chiRestrict_of_isFixedPt`: g∈W₁^# 固定の χ は χ_j のいずれか。
  w₂ 個 distinct χ_j (chiRestrict_injective + card_charGroup_W2) が card_fixed_irr_le_W2 の bound を
  埋める → `F : Ŵ₂ ↪ Fix(g)` を `Fintype.bijective_iff_injective_and_card` (injective + card 一致 ⟹
  surjective) で全単射 → preimage。card sandwich は `le_antisymm` + `Nat.card_le_card_of_injective`。
- **🔑 inertia 核心** `inertia_eq_K_of_forall_chiRestrict_ne`: χ が χ_j のいずれでもない ⟹ I_L(χ)=K。
  `Subgroup.IsComplement.existsUnique h.isComplement ℓ` で ℓ=k·w 分解 (k∈K,w∈W₁; `change kk*u=ℓ`),
  w=k⁻¹ℓ∈inertia; w≠1 なら counting collapse で χ=χ_j 矛盾ゆえ w=1, ℓ=k∈K。
- **capstone 3 文**:
  - `induce_isIrreducible_of_forall_chiRestrict_ne`: Ind^L_K χ∈Irr(L)。I_L(χ)=K + (1.5.b/[Is]6.34)
    `isIrreducibleCharacter_induce_of_inertia_eq` (inertia abbrev は ClassFunction.inertia と defeq)。
  - `induce_ne_certainType_of_forall_chiRestrict_ne`: Ind^L_K χ≠μ_{ij}。Frobenius
    `ClassFunction.inner_induce_eq_inner_restrict` で ⟨Ind χ,μ_{ij}⟩=⟨χ,Res μ_{ij}⟩=⟨χ,χ_j⟩=0
    (`restrict_certainType_eq` + χ≠χ_j) vs ⟨μ_{ij},μ_{ij}⟩=1。
  - `exists_eq_certainType_or_induce` (exhaustion): μ∈Irr(L) は μ_{ij} or Ind^L_K χ。
    `exists_liesOver` で Res μ の成分 θ → `inner_induce_ne_zero_iff_liesOver` で μ は Ind θ の成分。
    θ=χ_j なら Ind θ=∑_i μ_{ij} (`Finset.exists_ne_zero_of_sum_ne_zero`) ゆえ μ=μ_{ij};
    そうでなければ Ind θ∈Irr(L) ゆえ μ=Ind θ (`irreducibleCharacter_inner_eq_ite` + `coe_mk`)。

### 🔑 KEY / 再調査するな (Lean 機構の罠, session 26 新規)
- **`Subtype.ext_iff.mp hpq` の逆向き単一化トラップ**: `Subtype.ext (Subtype.ext_iff.mp hpq)` のように
  2 段ネストすると、外側 `Subtype.ext` の expected type `↑?a=↑?b` が内側 `?a ?b` を**誤った subtype 層**
  (K-val) に固定し、引数 hpq (W₂ 要素の等式) と型不一致になる。さらに `have hL : (wit p:L)=(wit q:L) :=
  Subtype.ext_iff.mp hpq` の**型注釈も** `(wit p:L)` を `↑(wit p)` と読んで K-subtype を選ばせ同じ失敗。
  **解 = 型注釈を外し `have hL := Subtype.ext_iff.mp hpq` で引数駆動にし、次段 `Subtype.ext hL` の
  defeq に委ねる** (congrArg Subtype.val も同じ逆向き単一化で落ちる)。
- **`congrArg (fun θ => ↑θ) heq` / `congrArg (fun φ => inner φ ψ) h` は beta-redex が残り後続 rw が
  パターン不一致**。**解 = lambda を使わず `congrArg IrreducibleCharacter.toClassFunction heq` (直接の
  coercion 関数)、inner は `have key : inner (∑…) ψ = inner (∑…) ψ := by rw [hind]` と明示 statement**。
- **`h.coe_chiRestrict χ₂` は h 明示必須** (Hypothesis namespace の `variable (h)` ゆえ第1引数=h)。
  bare `coe_chiRestrict χ₂` は χ₂ を h と誤解 (rw 内で implicit 化されるとき以外)。
- **`ClassFunction.inner_induce_eq_inner_restrict` は `ClassFunction.` 修飾要** (open しても
  bare `inner_induce_eq_inner_restrict` は unknown)。
- **`if` の Decidable は `classical` で統一** (sum_congr で irreducibleCharacter_inner_eq_ite を rw すると
  IrreducibleCharacter 等式の Decidable インスタンス不整合 → proof 冒頭 `classical`)。

### ▶▶ 次 = (4.6)-(4.9) → S08 case-B
- (4.5) cluster は (a)(b) 両方 COMPLETE。利用可能 (全 axiom-clean):
  `chiRestrict` / `chiRestrict_injective` / `card_charGroup_W2` / `inertia_eq_K_of_forall_chiRestrict_ne`
  / `induce_isIrreducible_of_forall_chiRestrict_ne` / `induce_ne_certainType_of_forall_chiRestrict_ne`
  / `exists_eq_certainType_or_induce` / (session 25) `certainTypeRestrict_isIrreducible` /
  `induce_restrict_certainType_eq` / `index_K_eq`。
- (4.6) Hypothesis (G⊃L が (4.2) + Dade τ rel A₀ 等) の構造体定義から。mmd 04.6 (4.6)-(4.9)。

正本 = 本ノート (session 26)。**Don't re-grind (4.5) — (a)(b) 完成・axiom-clean (full build 3631)。**
**Subtype.ext_iff 逆向き単一化トラップ + congrArg beta-redex + h.coe_chiRestrict 明示 (再調査するな)。**

### 🚨 RECON (session 26 末): (4.6)-(4.9) → S08 case-B は full (3.8) trichotomy がブロッカー

mmd 04.6 (4.6)-(4.9) を精読した結果、**S08 case-B (6.8) 閉鎖の critical path に未形式化の full (3.8)
trichotomy がある**ことが判明 (既存 repo 注記の訂正が必要)。

- **(4.6) Hypothesis** (新 leaf 要): G⊃L が (4.2)、G,W が (3.1)、H⊴L (W₂⊂H⊂K)、A は (2.2) を満たし
  ⋃_{h∈H^#}C_K(h)^#⊂A⊂K^#、A₀=A∪V^L も (2.2) を満たす、τ=Dade isometry rel A₀。**(2.2)/(3.1)/(3.6)
  の既存 Hypothesis 構造体 + Dade τ をバンドルする大きな structure。** σ,ω_ij,μ_ij,μ_j,χ_j,δ_j は
  (3.3),(3.2),(4.3),(4.5) と同じ。
- **(4.7)** [Supp χ⊂A∪{1} for H⊄Ker χ]: (4.6.d)+(1.2) で。**(3.8) 非依存**。χ_j (j≥1) も。
- **(4.8)** [μ_ij(1)=μ_ik(1) ⟹ Supp(μ_ij−μ_ik)⊂A₀, δ_j=δ_k, (μ_ij−μ_ik)^τ=δ_j(ω_ij^σ−ω_ik^σ)]:
  🚨 **full (3.8) trichotomy を使う**。NC(ψ)≤4 で「cases (b)/(c) は ≥3 同係数 ω 成分を要し不可能」と
  排除して case (a) に落とす。**corollary `grid_eq_zero_of_ncard_support_lt` (NC<min(w₁,w₂)⟹0) では
  不足**: w₁=3<w₂ のとき NC≤4 は min=3 未満でないので corollary 不適用、full trichotomy 必須
  ((3.8) 仮説は NC<2w₁=6)。(2.1),(4.3.c)(d),(3.2.c),(3.6) も使用。
- **(4.9)** [Z[𝒯] 上の等長 T が τ と一致]: (4.8)+(3.9)+(4.3)+(4.7) で。**(4.8) 経由で (3.8) に依存**。
- **S08 case-B**: (4.9)(b) の等長 (μ_j↦δ_k∑_i ω_ij^σ, Z[𝒯,A] で τ 一致) が certain-type の coherence
  ingredient。⟹ **case-B = (4.9) ← (4.8) ← full (3.8)**。

**⟹ repo `S05_SigmaIsometry.lean:1418` の「full trichotomy (3.8.b)/(3.8.c) は §12+ のみ」は (4.8) を
見落とした不正確な注記。(4.8) が w₁=3 で要求する。** ただし (4.8) は full (3.8) でなく「NC≤4 + 構造で
(b)/(c) を排除する標的補題」で済む可能性あり (full trichotomy の (b)/(c)-exclusion 部分のみ)。

**(3.8) full trichotomy の現状** (S05): (a) ψ=β / (b) NC=w₁ かつ ψ=a∑_i ω_ij^σ+β (full column) /
(c) NC=w₂ かつ ψ=a∑_j ω_ij^σ+β (full row)。証明 = 3.8.1/3.8.2/3.8.3 の grid 組合せ論
(既存の `S05_SignedTripleGrid` / `SigmaIsometry` infra 上)。corollary のみ済、本体 0。

**次セッションの選択肢** (どれも substantial、(3.8) は (3.5) 級の組合せ論):
1. **(4.6) Hypothesis + (4.7)** — unblocked・foundational ((4.x) すべての土台、(3.8) 非依存)。
2. **full (3.8) trichotomy** ((4.8)/(4.9)→case-B の真のブロッカー解除; 標的 (b)/(c)-exclusion で
   足りるか先に精査推奨)。
3. (4.5) で打ち止め (クリーンな milestone)。

## 2026-06-11 (session 26 cont., b-peterfalvi): ✅✅✅ Peterfalvi (3.8) FULL trichotomy COMPLETE

ユーザー選択 (選択肢2) に従い full (3.8) trichotomy を完全形式化。**(4.8)/(4.9)→S08 case-B の
ブロッカー解除済み。** 3 commits、全 axiom-clean (allowlist 3)、**full build 3764 + AxiomsCheck OK**。
(3.5) 級と覚悟したが textbook の index-relabelling を回避する clean な分解で 1 セッション内に完了。

### ✅ 着地 — 2 新 leaf
- **抽象 `grid_trichotomy`** (`S05_GridTrichotomy.lean`, 純 ℂ-grid, minimal import, commit 619ba765):
  separable grid `a:ι×κ→ℂ` (`a(i,j)+a(i',j')=a(i,j')+a(i',j)`), `|ι|+2≤|κ|`, `|support|<2|ι|` ⟹
  (a) 全0 / (b) 単一定数列 j₀ / (c) 単一定数行 i₀。
  - **🔑 核心トリック**: separable grid は `a(i,j)=f i+g j` に分解 (`exists_param`: f i=a(i,j₀),
    g j=a(i₀,j)-a(i₀,j₀), `linear_combination hadd`)。⟹ f/g の定数性で場合分け (textbook の
    a_{00}≠0 WLOG + index 並べ替えが**不要**になる)。
  - f 定数 ⟹ 列依存 b j=f i₀+g j、`card_support_const_snd` で `|support|=|ι|·#{b≠0}`<2|ι| ⟹
    #{b≠0}≤1 (`Nat.lt_of_mul_lt_mul_right`) ⟹ `eq_zero_or_single` で (a)/(b)。
  - g 定数 ⟹ 行依存、`card_support_const_fst` で `#{c≠0}·|κ|`<2|ι|、|κ|>|ι| (gcongr+omega) で
    #{c≠0}≤1 ⟹ (a)/(c)。
  - 両非定数 ⟹ **`card_support_ge_of_not_const`**: 行ごと二重数え上げ — 各行 ≥1 非零 (g 非定数)、
    異2行 i₁,i₂ (f i₁≠f i₂) は零集合 disjoint で nonzero 合計 ≥|κ|、`Finset.sum_sdiff` で
    `|support|=∑_i Srow ≥ |κ|+(|ι|-2)` ⟹ ≥2|ι| (|κ|≥|ι|+2) で hyp と矛盾。
  - helper: `exists_param`/`card_support_const_snd`/`_fst`/`eq_zero_or_single`/`card_support_ge_of_not_const`。
- **具体 `sigmaCoeff_trichotomy`** (`S05_SigmaTrichotomy.lean`, imports SigmaIsometry+GridTrichotomy,
  commit 4b6c79bf): 抽象版を σ-係数 grid `sigmaCoeff=⟨ψ,ω_{ij}^σ⟩` に適用。separability=
  `sigmaCoeff_add_eq`(3.7), 支持数=`sigmaNC`(3.6 def そのもの), |Ŵ_k|=w_k=`card_charGroup_subgroupOf`,
  Nonempty Ŵ_k=trivial char `⟨1⟩`。**(4.8) が直接消費する形** ((a)全係数0/(b)単一定数W₂列/(c)単一定数W₁行)。
  既存 corollary `sigmaCoeff_eq_zero_of_sigmaNC_lt` (NC<min のみ) を真に拡張。

### 🔑 KEY / 再調査するな (session 26 cont. 新規)
- **trichotomy 結論は DecidableEq-free 形にした** (commit 58454341, consumer hardening): `if j=j₀ then c
  else 0` 形だと `[DecidableEq κ]` を要求し、Ŵ_k=`(W_k.subgroupOf W)→*ℂˣ` は **DecidableEq 無**で
  consumer がブロックされる。⟹ 結論を `c≠0 ∧ (∀i, a(i,j₀)=c) ∧ ∀i j, j≠j₀→a(i,j)=0` 形へ。
  proof 内の Finset 操作 ({i₁,i₂}/sdiff) は `classical` で供給。**MonoidHom→ℂˣ に DecidableEq を期待しない。**
- **omega の atom 不一致 = beta-redex**: 目標 filter が `(fun j=>f i₀+g j) j` (un-beta)、hlt が
  `f i₀+g j` (beta'd) だと omega が別 atom 扱い → fail。**`have` の filter は beta'd で書き、
  `card_support_const_snd (fun j=>...)` は明示引数で渡す** (rw の HO 単一化が b を推論しないため)。
- **`Finset.card_sdiff` はこの mathlib で `(s\t).card=s.card-(s∩t).card` (subset 仮説なし版)** →
  subset 版は `Finset.card_sdiff_add_card_eq_card hsub : (t\s).card+s.card=t.card` を使う。
- **`Nat.mul_le_mul_right` の署名揺れ回避** = `gcongr` で `2*card κ ≤ X*card κ` を `2≤X` に落とす。

### ▶▶ 次 = (4.6) Hypothesis + (4.7) → (4.8)[sigmaCoeff_trichotomy 消費] → (4.9) → S08 case-B
- **(3.8) ブロッカーは解除済み。** (4.8) は `sigmaCoeff_trichotomy` を ψ=(μ_ij−μ_ik)^τ−δ_j(ω_ij^σ−ω_ik^σ)
  に適用し、NC(ψ)≤4 で cases (b)/(c) を「ψ は 2 列 j,k に異なる係数」で排除 → case (a)=全係数0 ⟹
  ψ⊥ω_ij^σ,ω_ik^σ ⟹ ψ=0。
- 残る最初の大物 = **(4.6) Hypothesis 構造体** (G⊃L が (4.2)+(3.1)+(3.6)+H[W₂⊂H⊂K]+A[(2.2)]+A₀+Dade τ
  をバンドル)。(2.2)/(3.6) の既存構造体 recon が要る。

正本 = 本ノート (session 26 cont.)。**(3.8) full trichotomy 完成・axiom-clean。Don't re-grind。**
**trichotomy 結論は DecidableEq-free, beta-redex で omega atom 注意, card_sdiff は add 版 (再調査するな)。**

### 🚨🚨 依存関係の訂正 (session 26 cont.², mmd 04.8 (6.8) 全証明精読): (4.7)-(4.9) は (6.8) case-B の経路上に「ない」

session 26 の RECON「case-B ← (4.9) ← (4.8) ← (3.8)」は**不正確だった**。mmd `04.8` の **(6.8) Theorem
全証明**を精読した結果:
- **(6.8)(c2) の証明 (mmd L160-)**: 「L と L/Z が (4.2) を満たし…**(1.6) と Theorem (4.5)** で S, S(Z) が
  各 w₂−1 個 reducible…」+ **(6.8.2) case-B (L176-)** は τ₁/τ₂ (Dade isometry rel A₁⊆A₀)・regular char・
  **(6.7)** を使う。**(4.7)/(4.8)/(4.9) は (6.8) 証明に一切登場しない。**
- ⟹ **(6.8) case-B (c2) が §6 から要するのは: Hypothesis (4.6) [構造、特に Dade τ rel A₀=A∪V^L] +
  Theorem (4.5)[✅完成] + (1.6)。** 加えて §8 engine (6.6)/(6.7) + s08_6_8_blocker_central_Z.md の
  Zc-central X-coherence + (6.8.1)/(6.8.2)/(6.8.3)。
- **(4.7)/(4.8)/(4.9) は §6 内部の結果** (Hypothesis (4.6) 下) で、(6.8) case-B の**critical path 外**。
  別 consumer (§9 Feit-Sibley か §11+ maximal subgroups) 用。**∴ (3.8)→(4.8) も §6 完成スコープで
  あって (6.8) closer ではない** (3.8 自体は full-Pf scope の正当な成果)。

**∴ (6.8) case-B closing の真の gateway = Hypothesis (4.6) 構造体** (S08 (c2) が carry する `cert` を
full (4.6) に拡張: 現 `CertainTypeHypothesis`=(4.2)+(2.2)-Dade-on-A のみで、**A₀=A∪V₀ の combined Dade
τ・(3.1) が欠落**; (6.8) の τ₁ は τ|_{A₁} で A₀ Dade が要る)。これを建てれば (6.8)(c2) の τ machinery が
供給され、残りは §8 program (Zc-central, (6.6)/(6.7)[要 status 確認], (1.6))。

**訂正後の選択肢:**
1. **(4.6) Hypothesis 構造体** (gateway; (6.8)(c2) の τ rel A₀ + §6 (4.7)-(4.9) 双方の土台)。
   combined Dade は **field として仮定** (構成は instantiator=S08 (6.8) application の責務)。
   設計難所 = L≤G coercion (W₁,W₂≤↥L vs W≤G via TICyclic) + 二 (2.2) instance (A, A₀)。
2. **§8 (6.8) program 直接** (s08_6_8_blocker_central_Z.md; Zc-central coherence; (1.6)/(6.7) status 確認要)。
3. **(4.7)-(4.9) §6 完成** ((3.8) を活かす; (6.8) 経路外だが full-Pf scope; (4.6) structure 要)。

### ✅ 着地 (session 26 cont.²): Pf (4.6) Hypothesis 構造体 (gateway scaffold, commit 2fa0830e)

`Hypothesis46 (A : Set G) (L : Subgroup G)` を新 leaf `S06_CertainHypothesis46.lean` に定義
(構造体のみ, warning-free, full build 3765 + AxiomsCheck OK)。**`extends CertainTypeHypothesis A L`**
(= (4.2) on ↥L + (2.2)-Dade on A) + 追加フィールド:
- (4.6.b) `tic : TICyclicHypothesis G` + `tic_W1/tic_W2 : tic.W_k = (W_k).map L.subtype` (L↪G 像で matching)
- (4.6.c) `subH : Subgroup ↥L` + `subH_normal` + `W2_le_subH` + `subH_le_K`
- (4.6.d) `A_covers : ∀hh∈subH^#, ∀x∈C_K(hh)^#, L.subtype x ∈ A` (covering ⋃C_K(h)^#⊆A) +
  `dade0 : S04.Hypothesis G (A ∪ {l·v·l⁻¹ | l∈L, v∈tic.V}) L` (A₀=A∪V^L の (2.2))
- (4.6.e) `tau : FullDadeIsometryData dade0` (τ rel A₀)
- **🔑 instance: `[Fintype ↥L] [Invertible (Nat.card G:ℂ)] [Invertible (Nat.card ↥L:ℂ)]` を構造体
  シグネチャに要求** (dade0/tau フィールドが要する; Fintype ↥L は [Fintype G] から自動でない)。
- **Dade data (dade/dade0/tau) は field として仮定** — 構成 (K-local + V-TI Dade の合成) は
  instantiator=§8 (6.8) application の責務。S08 の `CertainTypeHypothesis`(現 (c2) carry)を
  `Hypothesis46` に拡張すれば (6.8)(c2) の τ rel A₀ が供給される。

### ▶▶ 次 = (4.7) [Supp χ⊆A∪{1}] — ⚠ **(1.2) がブロッカー (未着手)**
- **(1.2)** (mmd 04.3): H⊴G, χ∈Irr(G), H⊄Ker χ, C_H(g)=1 ⟹ χ(g)=0。**repo 未着手**。
  証明 = 第二直交関係 `∑_χ|χ(g)|²=|C_G(g)|` + `C_H(g)=1⟹|C_G(g)|≤|C_{G/H}(ḡ)|` +
  inflation (Φ=H-trivial chars=Irr(G/H), `∑_{φ∈Φ}|φ(g)|²=|C_{G/H}(ḡ)|`) ⟹ χ∉Φ で χ(g)=0。
  clean self-contained (~100 行), 汎用 char theory (InflationCharacter + 第二直交)。
- (4.7) は (1.2) + (4.6.d) A_covers で `Supp χ⊆A∪{1}` (χ∈Irr(K), H⊄Ker χ); χ_j (j≥1) part も。
  Hypothesis46 のフィールドアクセス + (4.5) の χ_j (`certainTypeRestrict_isIrreducible` 等) を使う。

正本 = 本ノート (session 26 cont.²)。**(4.6) structure 完成 (gateway)。次 = (1.2) [未着手, 第二直交+inflation]
→ (4.7)。** **(4.7)-(4.9) は (6.8) case-B 経路外 (上記訂正); (6.8) closer は §8 Zc program。**

## 2026-06-11 (session 27, b-peterfalvi): ✅✅✅ Peterfalvi (1.2) + (4.7) core + (4.7) induced COMPLETE (3 commits)

(1.2) ブロッカー解除 + (4.7) の (1.2)-消費する core 2 半分を完全形式化。全 axiom-clean
(allowlist 3)・full build 3774 (1.2 commit 時) / leaf build 緑。**3 commits**:
`0f2bc684` (1.2) / `de5471ea` (4.7) core / `6f30fe6d` (4.7) induced。

### ✅ 着地 1 — Peterfalvi (1.2) [新 leaf `S03b_Vanishing.lean`, `OddOrder.Peterfalvi.S03.*`]
- **`irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`** ((1.2) 本体):
  H⊴G, χ∈Irr(G), H⊄Ker χ, C_H(g)=1 ⟹ χ(g)=0。証明 = 第二直交を G と G/H に適用
  (`column_orthogonality_diagonal`、**repo に既存**=`ColumnOrthogonality.lean`、ノートの「未着手」は
  定理本体のことでインフラは完備だった) + 値保存 inflation bijection (`inflate_apply` +
  `exists_inflate_eq_of_subset_characterKernel`、**InflationCharacter.lean に既存**) + centralizer
  埋め込み `|C_G(g)|≤|C_{G/H}(ḡ)|` ⟹ ∑_χ normSq(χ g) の squeeze で H⊄ker 項を 0 に。
- **`card_centralizer_le_card_centralizer_quotient`** (centralizer 不等式):
  C_H(g)=1 ⟹ `mk' H` は C_G(g) 上 injective (ker∩C=C_H(g)=⊥) かつ像が ḡ を centralize
  (`MonoidHom.ofInjective` で `C_G(g)≃*range` + `Nat.card_mono`)。
- `vanishesOnTrivialSubgroupCentralizers_of_not_subset_characterKernel`: S03 述語への packaging。
- **AxiomsCheck 登録済** ((1.2) 本体 + centralizer 不等式、§3 kernel block 内)。**(1.2) は汎用 char theory
  ゆえ repo 全体で再利用可。** 🔑 **InflationCharacter は S03_PreliminaryCharacter を import する**
  ので (1.2) は S03 本体に置けず別 leaf に分離 (循環回避; 「新 leaf default」とも合致)。

### ✅ 着地 2/3 — Peterfalvi (4.7) core + induced [新 leaf `S06_CertainTypeSupport.lean`, `…S06.*`]
χ_j 機構に**非依存**で Hypothesis46 のフィールド + (1.2) のみ消費 (∴ abstract-Hypothesis bridge 不要)。
- **`mem_A_of_apply_ne_zero_of_not_subset_characterKernel`** ((4.7) core, Supp χ⊆A∪{1}):
  (1.2) を群 K・正規部分群 `h.subH.subgroupOf h.K ⊴ ↥K` に適用。χ(g)≠0 ⟹ (1.2) 対偶で
  C_H(g)≠⊥ ⟹ ∃ c∈H^# が g を centralize ⟹ (4.6.d) `A_covers` で g の G-像 (=`L.subtype (K.subtype g)`)∈A。
- **`apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`** (support form, 対偶)。
- **`induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`** ((4.7) induced,
  Supp Ind_K^L χ⊆A∪{1}): `ClassFunction.support_induce_subset_conjugatesIntoSet` で非零点 z は
  Supp χ の w∈K に L-共役 → core で w の G-像∈A∪{1} → A は L-共役不変 (**S04.Hypothesis フィールド
  `L_normalizes_A`** = `h.dade.L_normalizes_A`) ＋ z,w L-共役ゆえ z の G-像∈A∪{1}。
  **`[Invertible (Nat.card ↥h.K : ℂ)]` を instance binder で要求** ((4.5) lemma 群と同様、statement
  に `induce` があるため elaboration 時必須; in-proof haveI では遅い ← 罠)。

### 🔑 KEY / 再調査するな (session 27)
- **第二直交は repo に完備** (`OddOrder.RepresentationTheory.column_orthogonality_diagonal`:
  `∑_χ χ(g)·star(χ(g))=|C_G(g)|`)。inflation も完備 (`inflate`/`inflate_apply`/`inflate_injective`/
  `exists_inflate_eq_of_subset_characterKernel`/`subset_characterKernel_inflate`、kernel 述語 =
  `(N:Set G)⊆OddOrder.Peterfalvi.S03.characterKernel χ`)。
- **`conjugatesIntoSet`/`support_induce_subset_conjugatesIntoSet`/`mem_conjugatesIntoSet` は
  `OddOrder.RepresentationTheory.ClassFunction` namespace** (要 `ClassFunction.` 修飾; `open …RepresentationTheory`
  だけでは出ない)。
- **`h.K`/`h.subH`/`h.dade` は projection 解決する** (Hypothesis46→CertainTypeHypothesis→Hypothesis ↥L
  の extends 連鎖; `h.toCertainTypeHypothesis.K` と書かなくてよい)。
- G-像は `L.subtype (h.K.subtype g)` で統一 (A_covers/L_normalizes_A と整合)。subtype injective は
  `h.K.subtype_injective`、≠1 は `map_one` 経由。

### ▶▶ 次 = (4.7) j≥1 part → (4.8)[sigmaCoeff_trichotomy 消費]/(4.9) [全て (6.8) 経路外・full-Pf scope]
- **(4.7) j≥1 part** (mmd 04.6 L69-73): χ_j (j≥1) について H⊄Ker χ_j を示し、core/induced を χ_j に
  適用して Supp χ_j, Supp μ_j ⊆ A∪{1}。**H⊄Ker χ_j の ω_{0j} 論法**が核 (背理法: H⊆Ker χ_j 仮定 →
  W₂⊂H ゆえ ω_{0j}(y)=ω_{0j}(xy)=δ_j μ_{0j}(xy)=δ_j μ_{0j}(x)=ω_{0j}(x)=1 [x∈W₁^#,y∈W₂, by (4.3)] →
  χ₂=1 → j=0 矛盾)。**要 API 層** (未 survey): χ_j bridge = `h.toCertainTypeHypothesis.toHypothesis.chiRestrict χ₂`
  ([NeZero (Nat.card h.W1)] 要、W1_nontrivial から)、ω_{0j} 積構造 (`omegaColumnDiff`/`columnFamily`/
  `chiColumn`/`omega_apply` @ S06_CertainTypeCharacters)、(4.3.c) value-match。**substantial (~100-200 行)、
  (4.3) API 精読が前提。** core/induced は既に χ_j に適用可 (χ_j : IrreducibleCharacter ↥h.K)。
- **(4.8)/(4.9)**: session 26 cont. の `sigmaCoeff_trichotomy` を消費 ((4.8) は NC≤4 で full (3.8) の
  case(b)/(c) 排除 → 全係数0)。(4.9) は (4.8)+(3.9)+(4.3)+(4.7)。

正本 = 本ノート (session 27)。**(1.2) 完成 (汎用・AxiomsCheck 登録) + (4.7) core/induced 完成
(χ_j 非依存)。Don't re-grind。** **(4.7)-(4.9) は (6.8) case-B 経路外 (full-Pf scope); (6.8) closer は
§8 Zc program (s08_6_8_blocker_central_Z.md)。** ← ⚠ この経路評価は **session 29 (s08) で撤回**
(R(reducible)=(5.3.b)=(4.9) 引用ゆえ (4.7)-(4.9) は on-path)。session 30 参照。

## 2026-06-12 (session 30, b-peterfalvi, Opus 4.8 1M): ✅ (4.7) j≥1 landed + (4.8)-(4.10) PDF proof 精読

### ✅ (4.7) j≥1 COMPLETE (commit 751943f1) + AxiomsCheck import 漏れ是正
前セッション未コミットの (4.7) j≥1 part を build-green + axiom-clean 検証してコミット (S06_CertainTypeSupport)。
`Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one` (ω_{0j} 背理法) + Hyp46 form
`not_subset_characterKernel_chiRestrict` + `chiRestrict_apply_eq_zero_of_not_mem_union` /
`induce_chiRestrict_apply_eq_zero_of_not_mem_union` (Supp χ_j, Supp μ_j ⊆ A∪{1})。基盤 =
`apply_mul_eq_of_mem_characterKernel` (InflationCharacter; kernel translation `g∈Ker χ⟹χ(x·g)=χ(x)`,
`rep_eq_id_of_character_eq_one` 経由)。**PDF (4.7) proof の ω_{0j} 論法と完全一致確認済み。**

- 🛑 **運用教訓 (再発防止)**: session 27 で S06_CertainTypeSupport を新 leaf 化したとき
  **AxiomsCheck に import し忘れ** + core/induced の guard 未登録だった。今回 j≥1 の assert を登録したら
  「constant not found」で full build 赤。**新 leaf は root(OddOrder.lean:123 在)+AxiomsCheck 両方に
  import + 全 top-level を guard 登録**が必須。S06_CertainTypeSupport の全7結果を登録済み
  (full build 3781 + AxiomsCheck 緑、全 allowlist 3)。

### 📖 (4.8)-(4.10) PDF 精読 (pdf/04.6 p.23-24; ⚠ mmd 04.6 は (4.8) 以降 Nougat 破損で信頼不可 — 再読不要)
**(4.8)** Hyp(4.6), 0≤i<w₁, 0<j,k<w₂, μ_{ij}(1)=μ_{ik}(1) ⟹ 3 結論:
`Supp(μ_ij−μ_ik) ⊂ A₀`、`δ_j=δ_k`、`(μ_ij−μ_ik)^τ = δ_j(ω_ij^σ−ω_ik^σ)`. **proof 8 step**:
(1) δ_j≡δ_k (mod w₁) by (4.3.d), w₁>2 ⟹ δ_j=δ_k. (2) μ_ij−μ_ik vanishes on W₁ by (4.3.c).
(3) z∈L−K ⟹ (2.1) で z は xW₂ (x∈W₁^#) に L-共役 ⟹ Supp 内なら z∈V^L; Supp∩K⊂A by (4.7) ⟹
Supp(μ_ij−μ_ik)⊂A₀. (4) ψ:=(μ_ij−μ_ik)^τ−δ_j(ω_ij^σ−ω_ik^σ) は V で消滅 ((3.2.c)(4.3.c)+τ def).
(5) τ isometry + (μ_ij−μ_ik)^τ は 1 で消滅 ⟹ ∃λ₁,λ₂∈Irr(G), ψ=λ₁−λ₂−δ_j(ω_ij^σ−ω_ik^σ).
(6) NC(ψ)≤4<2inf(w₁,w₂). (7) (3.8) cases(b)(c) 不可能 — これらは同係数 ω_rs^σ を**3 個以上**含むが
ψ は持たない (ψ の ω^σ 係数は j,k 2 列に ±δ_j のみ). (8) (3.8) ⟹ ψ⊥ω_ij^σ,ω_ik^σ ⟹ ψ=0.

**(4.9) Theorem** Hyp(4.6), 0<k<w₂, T={μ_j|0<j<w₂,μ_j(1)=μ_k(1)}:
(a) μ_j∈T ⟹ μ̄_j∈T ∧ μ̄_j≠μ_j; 0≠Z[T,L^#]=Z[T,A]. proof: ω̄_ij=ω_{i'j'}, j'≠j (j≠0,|W| odd, j' は i 非依存),
(3.9)+(4.3) で δ_j μ̄_ij=δ_{j'} μ_{i'j'} ⟹ μ̄_ij=μ_{i'j'} ⟹ μ̄_j=μ_{j'}≠μ_j; 0≠μ̄_k−μ_k∈Z[T,L^#],
(4.7) で Z[T,L^#]=Z[T,A]. (b) Z[T]→Z[Irr G], μ_j↦δ_k∑_{0≤i<w₁}ω_ij^σ は isometry で Z[T,A] 上 τ と一致.
proof: isometry 明らか; Z[T,A] は μ_j−μ_k で生成、(4.8) で (μ_j−μ_k)^τ=∑_i(μ_ij−μ_ik)^τ=δ_k∑_i(ω_ij^σ−ω_ik^σ).

**(4.10)** Hyp(4.6), 0≤i<w₁,0≤j<w₂: `(δ_j μ_ij−δ_j μ_0j−μ_i0+μ_00)^τ = ω_ij^σ−ω_0j^σ−ω_i0^σ+ω_00^σ`.
proof: α=ω_ij−ω_0j−ω_i0+ω_00, β=δ_j μ_ij−δ_j μ_0j−μ_i0+μ_00; (4.3.b)+(4.4) で β=Ind_W^L α;
(3.4) で Supp(α)⊂V ⟹ Supp(β)⊂V^L; x∈V で C_G(x)=W⊂L; τ def で β^τ(g)=α^σ(g) ∀g ((4.3.c)(3.2.c)).

### ▶▶ 次 = (4.8) 実装 (新 leaf S06_CertainTypeIsometry.lean 想定)
消費 API (要 survey で Lean 名確定): (4.3.c)(d) [certainType value / δ 合同 mod w₁], (3.2.c)
sigma_apply_of_mem_V, (3.8) sigmaCoeff_trichotomy [S05_SigmaTrichotomy, DecidableEq-free 形:
(a)全0/(b)定数W₂列/(c)定数W₁行], τ Dade isometry [sdiffFullDadeIsometryData /
toTICyclicFullDadeApplication], NC=sigmaNC, ω_ij^σ=sigma_chiColumn_eq_certainType。
**最難所 = step (7) cases(b)(c) 排除** (ψ の ω^σ 係数構造が「2 列 j,k に ±δ_j」⟹ 単一定数列/行と矛盾)。
### step(7) 先行調査結果 (session 30 cont. — ユーザー指示「最難所先行調査」)
- **`sigmaCoeff_trichotomy`** (S05_SigmaTrichotomy:41) signature 確定:
  `(hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (card W:ℂ)] [Invertible (card G:ℂ)]
   (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication hyp) {ψ : ClassFunction G ℂ}
   (hψ : ∀v∈hyp.V, ψ v=0) (hgap : card W1 + 2 ≤ card W2) (hNC : sigmaNC hVeq app ψ < 2*card W1)`
  → (a) `∀pq, sigmaCoeff..pq=0` / (b) `∃ j₀ c, c≠0 ∧ ∀p sigmaCoeff(p,j₀)=c ∧ ∀p q≠j₀→0` /
  (c) `∃ i₀ c, c≠0 ∧ ∀q sigmaCoeff(i₀,q)=c ∧ ∀p≠i₀ q→0`。p:Ŵ₁=(W1.subgroupOf W)→*ℂˣ, q:Ŵ₂。
- **`sigmaCoeff hVeq app ψ (p,q) = ⟨ψ, (omegaProdCharImage hVeq app p q)^σ⟩ = ⟨ψ, ω_{pq}^σ⟩`**
  (S05_SigmaIsometry:1377)。`sigmaNC` (1385) = 非零係数の個数、`sigmaCoeff_add_eq` (1395, 3.7 separability)。
- **🔑 cases(b)(c) 排除の設計** (PDF「3個以上同係数 ω^σ 成分」の Lean 化方針):
  ψ=λ₁−λ₂−δ_j(ω_ij^σ−ω_ik^σ) (step5) ⟹ `sigmaCoeff(ψ)(p,q)=⟨λ₁−λ₂,ω_pq^σ⟩−δ_j([pq=ij]−[pq=ik])`。
  非零は高々 4 個 (λ₁:+1 を≤1箇所, λ₂:−1 を≤1箇所, (i,j):−δ_j, (i,k):+δ_j)、**各値の出現は高々2回**。
  (b)(c) は単一列/行に w_k≥3 個の同値 c≠0 を要求 ⟹ 矛盾。**w₁=3 でも**: j₀ 列の行≠i 成分は
  λ₁−λ₂ のみ (≤2箇所, 値 +1/−1 で異符号) ⟹ 3 行が同値 c≠0 は不可能。counting argument で行ける。
- **残課題 (実装時に確定要)**: ① **FullDadeApplication の供給元**（S06 直接 grep ヒットせず → `h.dade`
  経由 or S05 構成、(4.3)/(4.5) certainType 構成で既出のはず — 実装最初に特定）② step(5) τ-image=λ₁−λ₂
  (norm²=2 virtual + 1 で消滅 ⟹ 2 既約差; `mem_ZIrr`+norm 系) ③ ω^σ 正規直交 ⟨ω_pq^σ,ω_rs^σ⟩=[pq=rs]
  (`sigma_inner` 系、S05:1310 付近) ④ τ↔σ 関係で ⟨(μ_ij−μ_ik)^τ, ω_pq^σ⟩ を λ₁,λ₂ で表す。
- ⚠ **環境注記**: 本 session で grep/Read の tool 出力に narration ノイズ + 偽行番号が断続混入。
  実データは S05_SigmaTrichotomy:41 直接 Read と明示行番号で確認済み（信頼可）。次セッションも要警戒。

正本 = 本 session 30。**(4.8)-(4.10) statement/proof は PDF 確定、mmd 再読不要。step(7) 設計も確定。**

### 🔑🔑 残課題確定 (session 30 cont.² — 再調査するな; Edit tool が効かず cat 追記)
(4.8) 核心 = σ 2層 + τ:
- `h.tic : TICyclicHypothesis G` (Hypothesis46 field 43, (4.6.b) (3.1)-for-G, tic.W1=W1.map L.subtype)
  = σ_G (W→G)。**(4.8) trichotomy はこの h.tic で回す** (ψ∈CF(G) で (μ−μ)^τ と型整合)。
- `h.toTICyclicHypothesis : TICyclicHypothesis L` = σ_L(chiColumn)=δ_j•μ_ij
  (sigma_chiColumn_eq_certainType @ S06_CertainTypeCharacters:852) — σ_G とは別物。
- `h.tau : S04.FullDadeIsometryData dade0` (field 65, dade0 field 62) = Dade τ (L→G)。
- `FullDadeApplication hyp = {tau : FullDadeIsometryData hyp.toDadeHypothesis}` (S05_TICyclic:133 wrapper;
  helper full_map_eq_of_mem_V[τ の V 値≈(3.2.c)]/full_inner_eq[isometry]/full_maps_virtualCharacter[ZIrr] @151-185)。
- (4.8) ω_ij^σ = h.tic.sigma rfl <app> (omegaProdCharImage) [tic.W ベース, NOT chiColumn]。
- step(1) δ_j=δ_k: certainType_degree_modEq(937: μ_ij(1)=δ_j+w₁a)×2列 + μ_ij(1)=μ_ik(1) ⟹
  |δ_j−δ_k|≤2<w₁(奇数>2) ⟹ δ_j=δ_k [独立小補題、最初に実装]。
- step(4) ψ|_V=0: v∈V で ψ(v)=(δ_j−δ_k)ω_ik(v)=0 [full_map_eq_of_mem_V+(3.2.c)+certainType_apply_eq_of_mem_V(878)]。
- step(3)Supp⊂A₀/step(5)λ₁−λ₂/step(7)(8)trichotomy+counting = step(7)セクション参照。
- ⚠⚠ (4.8) 複数セッション規模 (σ_G 群移行 L↔G + τ-σ_G V値 + λ₁−λ₂ + counting)。
  段階: step(1)→statement→(3)(4)→(5)→(7)(8)。新 leaf S06_CertainTypeIsometry.lean (root+AxiomsCheck import必須)。

## 2026-06-12 (session 31, b-peterfalvi, Opus 4.8 1M): ✅ (4.8) step(1)+step(2) landed + 🚨 (2.1) critical-path blocker 判明

新 leaf **`S06_CertainTypeIsometry.lean`** 作成 (root + AxiomsCheck 両 import + guard 登録済、full build 3782 緑、allowlist 3)。

### ✅ step(1) `certainType_sign_eq_of_degree_eq` (commit 268d0940)
同一行 i・2 列 χ₂,χ₂' で `μ_ij(1)=μ_ik(1) ⟹ δ_j=δ_k`。`certainType_degree_modEq` (μ(1)≡δ mod w₁) を
2 列に適用 → ℂ 等式を `exact_mod_cast` で ℤ 化 → δ_j−δ_k=w₁·(b−a) ⟹ `(w₁:ℤ)∣2` (sign∈{±1} で
場合分け) → `Int.le_of_dvd (by norm_num) hdvd : w₁≤2` と `three_le_card_W1` (w₁≥3) で矛盾。
off-diag 2 case の witness 符号差は `first | …⟨b-a, linear_combination hZ⟩ | …⟨a-b, linear_combination -hZ⟩`。

### ✅ step(2) `certainType_apply_eq_of_mem_W1` + helper `chiColumn_apply_of_mem_W1` (commit 26e92857)
μ_ij−μ_ik が **W₁ 上で消失**。helper: ω_{ij}=chiColumn χ₂ i は W₁ 上で**列 χ₂ 非依存**
(`wSnd_eq_one_of_mem_W1` で W₂-射影自明 ⟹ ω_{ij}(w)=(w1CharEquiv i)(wFst w))。本体: W₁^#⊆W−W₂=sdiff.V
上 (4.3.c) `certainType_apply_eq_of_mem_V` (μ=δ·chiColumn) + step(1) + helper、1 では equal-degree 仮定。
σ_G/τ/(2.1) 全て非依存。

### 🚨🚨 CRITICAL FINDING — session-30 plan を訂正: **(2.1) が critical path 上の未形式化 blocker**
session 30 cont.² の段階表「step(1)→statement→(3)(4)→…」は **2 点を見落としていた**:
1. **conclusion 3 (FT-critical な isometry 恒等式) は conclusion 1 に依存する**。理由: LHS `(μ_ij−μ_ik)^τ`
   の τ (=`h.tau : S04.FullDadeIsometryData dade0`) の domain は **A₀ 上 supported な CF(L)**
   (`full_map_eq_of_mem_V` の入力は `SupportedOnV`)。μ_ij−μ_ik を τ に渡すには **Supp⊆A₀ = conclusion 1**
   を先に確立せねばならない。よって statement 単独では書けず、conclusion 1 が前提。
2. **conclusion 1 (Supp(μ_ij−μ_ik)⊆A₀) は (2.1) [L−K conjugacy] を要し、これは未形式化**。
   - 内訳: step(2) [vanish on W₁] ✅ + **(2.1)** [z∈L−K ⟹ z は xW₂ (x∈W₁^#) に L-共役] + L↔G V-bridge
     (A₀=A∪V^L の **V^L は ambient `tic.V` (G-level)** = `{g:G|∃l∈L,∃v∈tic.V,g=lvl⁻¹}`、CertainHypothesis46:63)。
   - **(2.1) は S04/S05/S06 に無い** (grep 済、`V_subset_sharp` のみ存在)。Peterfalvi §2 の構造定理
     (L=K⋊W₁, C_K(x)=W₂ ⟹ L−K の元は xW₂ に共役)。
   ⟹ **(2.1) は conclusion 1・conclusion 3 双方の critical-path blocker** (Task #4)。

### ▶▶ 次セッション推奨 (この順)
1. **(2.1) derivability 調査**: 既存 API (`centralizer_eq_sup` C_L(x)=W [session 20]、`isComplement`、
   `|L−K|=|K|(w₁−1)` counting、`coprime_card_W1_card_W2`) から導けるか精査。導ければ conclusion 1 leaf 内補題、
   重ければ独自 leaf/issue (base 1000)。**ここが真の hard core** (σ_G/τ より前)。
2. **conclusion 1** `certainType_diff_supp_subset_A0` (新 leaf 継続): step(2) + (2.1) + (4.7)
   (`chiRestrict_apply_eq_zero_of_not_mem_union`/`induce_…`) + L↔G bridge。
3. **conclusion 3** statement (σ_G=`h.tic.sigma rfl app`, τ=`h.tau`) + step(4) [step(1) で
   `ψ(v)=(δ_j−δ_k)ω_ik(v)=0` と簡単化済] → (5) λ₁−λ₂ → (7)(8) `sigmaCoeff_trichotomy`+counting。

### API 確定 (再調査不要)
- σ_G: `h.tic.sigma rfl app : ClassFunction h.tic.W ℂ →ₗ[ℂ] ClassFunction G ℂ` (S05_SigmaIsometry:948);
  `sigma_apply_of_mem_V` (1203): `sigma … α v = α ⟨v,_⟩` for v∈V (=(3.2.c))。
- τ value-on-V: `full_map_eq_of_mem_V` (S05_TICyclic:151), `full_inner_eq` (171, isometry),
  `full_maps_virtualCharacter` (179, ZIrr)。`FullDadeApplication` (133) = {tau : FullDadeIsometryData …}。
- `certainType_apply_eq_of_mem_V` (878): `μ_ij(v)=δ_j·chiColumn χ₂ i ⟨v,_⟩` for v∈sdiff.V=W−W₂。
  `certainType_degree_modEq` (937), `three_le_card_W1` (w₁≥3), `wSnd_eq_one_of_mem_W1` (S05_TICyclic:449)。
- SignedIrreducibleDifferenceFamily (IsometryDifferencePair:312): `mu : Fin n→IrreducibleCharacter G`,
  `sign : ℤ`, `sign_eq : sign=1∨sign=-1`。

### Lean gotchas (本 session 確立、再調査不要)
- **新 S06-level lemma (h : Hypothesis46 を明示第一引数) は `h.foo` dot 不可** → `foo h …` で呼ぶ
  (foo は `namespace S06` 直下で Hypothesis46 namespace でないため)。既存 `Hypothesis L` members
  (`certainType_apply_eq_of_mem_V` 等) は `h.` dot OK (extends 連鎖 Hypothesis46→CTH→Hypothesis ↥L)。
- **χ₂ 系結果 (columnFamily/certainType_degree_modEq を呼ぶ) は `[NeZero (Nat.card h.W1)]
  [Fintype ↥(h.W1⊔h.W2)] [Invertible (Nat.card ↥(h.W1⊔h.W2):ℂ)]` を instance binder で明示**
  (CertainTypeSupport (4.7) と同; `[Fintype ↥L]` から部分群の Fintype は自動導出されない)。
  **chiColumn のみの結果は `[Fintype]` 不要** (columnFamily が要る; helper は NeZero のみ)。
- **W-consistency**: `χ₂(wSnd w)=1` は `rw [wSnd_eq_one_of_mem_W1 hw]; exact map_one χ₂` (defeq) で。
  `simp`/`rw [map_one]` は syntactic で defeq-`1` (sdiff form vs χ₂ domain form) に不発。
- chiColumn unfold は外側 namespace から `rw [Hypothesis.chiColumn]` (修飾要)。

正本 = 本 session 31。**step(1)(2) landed。(4.8) の真 blocker = (2.1) [未形式化、conclusion 1/3 双方の前提]。**

## 2026-06-12 (session 32, b-peterfalvi, Opus 4.8 1M): ✅✅ (2.1) + (4.8) conclusion (1) landed

### ✅ (2.1) coprime-coset structure lemma (commit 60bb0b8a, new leaf S06_CertainTypeStructure)
- 🔑 **CORRECTION to session 31**: Peterfalvi (2.1) は L−K-specific でなく **一般の coprime-coset 補題**:
  「g normalizes H, gcd(o(g),|H|)=1 ⟹ Hg の各元は C_H(g)·g の元に H-共役」. issue 1003 title は誤称.
- `coset_conj_into_centralizer_coset`: self-contained 証明 (SZ-conjugacy **不使用**). 一様 Bézout 指数 e
  (e≡1 mod o(g), e≡0 mod |H|; `Nat.chineseRemainder`) で collapse `(w·g)^e=g` (w∈C_H(g)) → 共役写像
  `(H⧸C_H(g))×C_H(g)→Hg` 単射 → |dom|=|H|=|Hg| (Lagrange) で全射 (`Set.eq_of_subset_of_ncard_le`).
- application `Hypothesis.mem_compl_conj_into_W`: z∈L−K ⟹ ∃c,x∈W₁^#,y∈W₂, c⁻¹zc=x·y (C_K(x)=W₂).
- 記録: SZ-conjugacy は in-repo `OddOrder/Mathlib/SchurZassenhausConj.lean` に sorry-free で在 (今回不使用).

### 🔑🔑 CRITICAL: V = W−W₂ (NOT W−(W₁∪W₂)) — session 31 の読み訂正
- Peterfalvi (4.3.a): 「W−W₂ is a TI-subset of L, Hypothesis (3.1) holds」⟹ (3.1) の V = **W−W₂**.
- (4.6.b) G-level (3.1) も同じ V=W−W₂. ⟹ A₀=A∪V^L の V も W−W₂.
- ⟹ (4.8) conclusion 1: z∈L−K → xW₂ に共役、xW₂⊆W−W₂=V (x≠1) ⟹ z∈V^L. **step(2) [W₁-vanish] 不要**
  (xW₂ 全体が V に入る; x∈W₁^# も V に入る). step(2) は conclusion 3 の ψ-vanishing 用に残る.

### ✅ (4.8) conclusion (1) `certainType_diff_supp_subset_A0` (commit 22223004, S06_CertainTypeIsometry)
- Supp(μ_ij−μ_ik)⊆A₀. cases: z=1 vacuous (equal degree); z∈K→A (μ|_K=χ via `restrict_certainType_eq`
  +`coe_chiRestrict`, (4.7) `chiRestrict_apply_eq_zero_of_not_mem_union` で A∪{1} 外消失); z∈L−K→V^L.
- **新 field `Hypothesis46.tic_V : tic.V = ↑tic.W \ ↑tic.W2`** 追加 (faithful to (4.3.a)/(4.6.b);
  Hypothesis46 は **producer 無し** [S08 で未使用] ゆえ field 追加は無害). tic.W=(W₁⊔W₂).map subtype は
  導出 (W_sup+tic_W1/W2+map_sup).
- 🔑 V-bridge (再調査不要): L.subtype(xy)∈tic.V via tic.W membership (xy∈W₁⊔W₂) + ∉tic.W2 (xy∉W₂ ⟸ x≠1).
- gotcha: chiRestrict/coe_chiRestrict/restrict_certainType_eq は inner `namespace Hypothesis` ⟹ h:Hypothesis46
  には **dot 経由** `h.coe_chiRestrict`/`h.restrict_certainType_eq` (extends 連鎖で coerce). bare 不可.
  対して `chiRestrict_apply_eq_zero_of_not_mem_union` 等は S06 直下 (h 明示) ⟹ `foo h …`.

### ▶▶ 残: (4.8) conclusion (3) [FT-critical isometry 恒等式] = steps (4)-(8)
- conclusion 2 (δ_j=δ_k) = step(1) `certainType_sign_eq_of_degree_eq` (session 31) で **DONE**.
  ⟹ **(4.8) は 2/3 完了** (conclusion 1 ✅ + conclusion 2 ✅; 残 conclusion 3).
- conclusion 3: `(μ_ij−μ_ik)^τ = δ_j(ω_ij^σ−ω_ik^σ)`. **conclusion 1 で Supp⊆A₀ ⟹ τ (h.tau) に渡せる**
  (`full_map_eq_of_mem_V` の `SupportedOnV` 入力が conclusion 1 で供給可能に).
  - step(4) ψ:=(μ_ij−μ_ik)^τ−δ_j(ω_ij^σ−ω_ik^σ) が V で消滅 (full_map_eq_of_mem_V+(3.2.c)+(4.3.c)+step(2)).
  - step(5) τ isometry + (μ_ij−μ_ik)^τ(1)=0 ⟹ ∃λ₁,λ₂∈Irr(G), ψ=λ₁−λ₂−δ_j(ω_ij^σ−ω_ik^σ).
  - step(6)-(8): NC(ψ)≤4<2inf(w₁,w₂), (3.8) cases(b)(c) 排除 (ψ の ω^σ 係数は 2列 j,k に ±δ_j のみ),
    (3.8)⟹ψ⊥ω_ij^σ,ω_ik^σ ⟹ ψ=0.
  - **要 full (3.8) trichotomy `sigmaCoeff_trichotomy` (S05_SigmaTrichotomy:41)** = LAUNCH flagged hard part
    (Fable 5 候補). step(7) counting 設計は session 30 cont. に確定済.
- → (4.9) → S08 case-B → (6.8). 正本=本 session 32. **issue 1003 は CLOSED (条件達成).**

## 2026-06-12 (session 33, b-peterfalvi, Opus 4.8 1M): ✅ (3.8) precheck=AVAILABLE + ticFullDadeApplication (σ_G 供給元) landed

### ✅✅ (3.8) PRECHECK 結論: full trichotomy は既に証明済 — **Fable 5 不要**
- `sigmaCoeff_trichotomy` (S05_SigmaTrichotomy:41) は **sorry-free + axiom-clean** (allowlist 3)。
  abstract `grid_trichotomy` (S05_GridTrichotomy, 0 sorry) への specialization。既 landed
  (commits 4b6c79bf/58454341/619ba765, sessions 18-19 era)。
- ⟹ LAUNCH/session-32 の「(3.8) 本体 = この lane の真 hard part、Fable 5 候補」は **OUTDATED**。
  本体は構築済。conclusion 3 は **Opus で `sigmaCoeff_trichotomy` を black-box 利用**で足りる。
- signature: hVeq, app:FullDadeApplication, hψ(∀v∈V,ψv=0), hgap(w₁+2≤w₂), hNC(sigmaNC<2w₁) →
  (a) ∀pq sigmaCoeff=0 / (b) ∃j₀ c≠0 列定数,他0 / (c) ∃i₀ c≠0 行定数,他0。

### ✅ ticFullDadeApplication (σ_G の app 供給元) = session-30 blocker #1 解決 (S06_CertainTypeIsometry)
- **h.tic も TICyclicHypothesis G ゆえ L-side `toTICyclicFullDadeApplication` と同 recipe で構成可**:
  `⟨h.tic.toDadeHypothesis.fullDadeIsometryData (S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩`。
  TI-cyclic ⟹ local H(a)=⊥ ⟹ HConjInvariant 無料。**build-green + axiom-clean**。
- instance binder 要: `[Fintype h.tic.W] [Invertible (Nat.card h.tic.W : ℂ)]` (subtype Fintype は
  DecidablePred 無で非自動合成)。**def は AxiomsCheck 非登録**(L-side app も非登録; theorem のみ登録)。

### 🔑 conclusion 3 の精密 plan (以下 ▶=design、未 Lean 検証; 実装時に確認)
σ_G = `h.tic.sigma rfl h.ticFullDadeApplication`、τ = `h.tau.toDadeMap`
(domain = `S04.SupportedClassFunctions ℂ A₀ L` = CF(L) supported on A₀; membership = conclusion 1)。
- **既存 certain-type 機構は全て sdiff-side** (`h.sdiffTICyclicHypothesis.W`=W1⊔W2 in L; chiColumn/columnFamily/
  w1CharEquiv 全部 sdiff)。tic-side(G) に omega/chiColumn 無 ⟹ **sdiff↔tic 文字 bridge を新規構築要**
  (= L↔G 群移行の hard part)。iso e:sdiff.W ≃* tic.W = `Subgroup.equivMapOfInjective (W1⊔W2) L.subtype …`。
  ω_ij^{σ_G} := h.tic.sigma rfl app (h.tic.omega ((omegaProdChar (w1CharEquiv i) χ₂).comp e.symm))。
- ▶ **step 4 (ψ|V=0) は full grid-index bridge 不要 — V 上の値だけで足りる(本 session の鍵 simplification)**:
  v∈tic.V (↔ w∈sdiff.V via subtype) で ω_ij^{σ_G}(v)=(omega ξ_tic)⟨v⟩=chiColumn(χ₂,i)(w) [sigma_apply_of_mem_V],
  (μ_ij−μ_ik)^τ(v)=(μ_ij−μ_ik)(w) [full_map_eq_of_mem_V]=δ_j·chiColumn(χ₂,i)(w)−δ_k·chiColumn(χ₂',i)(w) [(4.3.c)],
  δ_j=δ_k (step 1) ⟹ ψ(v)=0。grid-index identification (omegaProdEquiv.symm) は steps 6-8 のみ。
- ▶ **(b)(c) 排除 = |supp(L)|≤2 clean counting**(session-30 の row-counting より明快):
  step 5 で (μ_ij−μ_ik)^τ=λ₁−λ₂ (distinct Irr)。sigmaCoeff(ψ)(p,q)=⟨λ₁−λ₂,chiFam(p,q)⟩−δ_j(δ[pq=ij]−δ[pq=ik])。
  L(p,q):=⟨λ₁−λ₂,chiFam(p,q)⟩ は **非零 ≤2 個** (`ncard_inner_chiFam_ne_zero_le_one` ×2)。
  D=δ-part=2 点 (p_i,q_j)↦−δ_j,(p_i,q_k)↦+δ_j (異列 q_j≠q_k)。
  - (b) 列 q₀ 定数 c≠0 (w₁≥3): q_j≠q_k ⟹ ≥1 δ-点が q₀ 外 (a=0⟹L=−D≠0∈supp L); 列 q₀ の δ-点でない
    ≥w₁−1≥2 行は a=L=c≠0∈supp L。disjoint ⟹ |supp L|≥3>2 矛盾。
  - (c) 行 i₀ 定数 c≠0 (w₂≥5 by gap): i₀≠p_i⟹行 w₂≥5 全 pure-L; i₀=p_i⟹q∉{q_j,q_k} の w₂−2≥3 列 pure-L=c。
    両者 |supp L|>2 矛盾。
  - (a) ⟹ ⟨ψ,ω_ij^σ⟩=⟨ψ,ω_ik^σ⟩=0 + norm²((μ−μ)^τ)=2 ⟹ ⟨λ₁−λ₂,ω_ij^σ⟩=δ_j,⟨…,ω_ik^σ⟩=−δ_j ⟹ λ₁−λ₂=δ_j(ω_ij^σ−ω_ik^σ) ⟹ ψ=0。
- 段階: [bridge def + step4] → [step5 norm-2] → [steps6-8 grid+counting]。複数 commit 想定。同 leaf S06_CertainTypeIsometry。

正本 = 本 session 33。**(3.8) AVAILABLE・ticFullDadeApplication landed・次 = sdiff↔tic ω bridge + step 4。**

### 🔧 session 33 cont. — CORRECTION: σ_G は h.tic でなく **ticVdiff** (V=W−(W₁∪W₂))
- **🚨 上の "σ_G = h.tic.sigma rfl …" は誤り**。`sigma` は `hVeq : hyp.V = hyp.Vdiff` を要求し
  `Vdiff = W∖(W₁∪W₂)`。だが **tic.V = W∖W₂** (≠ Vdiff) ⟹ `h.tic.sigma` は型が付かない。
  L-side も同じ理由で σ_L は `toTICyclicHypothesis` (V=W∖(W₁∪W₂)) 上で回す (sdiffTICyclicHypothesis
  [V=W∖W₂] でなく)。
- **解決 = `ticVdiff : TICyclicHypothesis G`** (新規, S06_CertainTypeIsometry) — h.tic の W/W₁/W₂ を流用、
  V := ↑tic.W∖(↑tic.W₁∪↑tic.W₂)。鍵: **V_ti は再証明不要** = `h.tic.V_ti.subset` (Vdiff⊆tic.V、`IsTISubset`
  は集合に antitone)。W_normalizes_V は `open scoped IsMulCommutative` + 可換性。**`ticVdiff.V = ticVdiff.Vdiff`
  は rfl** ⟹ `(ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h)` が型付く。
- **⚠ session 33 の `ticFullDadeApplication` (h.tic 上, commit 7fe9d8bc) は mis-targeted で削除済** →
  `ticVdiffFullDadeApplication` (ticVdiff 上) に置換。bridge (ticWEquivSdiffW/omegaProdCharTic) は
  V 非依存ゆえ不変・流用 (omegaProdCharTic は tic.W=ticVdiff.W 上の char)。
- **landed (build-green, axiom-clean)**: `ticVdiff`, `ticVdiffFullDadeApplication`,
  `certainTypeOmegaSigma` (= ω_ij^σ ∈ CF(G)), `certainTypeOmegaSigma_apply_of_mem_V`
  (v∈ticVdiff.V で ω_ij^σ(v)=chiColumn χ₂ i (e⟨v⟩))。τ-side: `certainTypeDiffSupported`,
  `tau_toDadeMap_apply_of_mem` (τ(α)(a)=α(a) ∀a∈A₀, via a∈hCoset a, H 自明性不要)。
- **▶ 次 = step 4** (ψ:=(μ_ij−μ_ik)^τ − δ_j(ω_ij^σ−ω_ik^σ) が ticVdiff.V で消滅): v∈ticVdiff.V=W∖(W₁∪W₂)
  ⊆ sdiff.V=W∖W₂ ゆえ (4.3.c) 適用可。(A) τ値 = tau_toDadeMap_apply_of_mem (要 v∈A₀ = `Or.inr ⟨1,_,v,hv',by group⟩`
  + e⟨v⟩↔⟨v,mem_L⟩ 同一視 via coe_ticWEquivSdiffW+subtype_injective) → (4.3.c)×2; (B) ω値 =
  certainTypeOmegaSigma_apply_of_mem_V; 差 = (δ_j−δ_k)·chiColumn χ₂' i (e⟨v⟩) = 0 (step 1)。

### ✅ session 33 cont.² — step (4) landed + steps 5-8 endgame plan 確定 (φ(1)=0 回避)
- **✅ landed (build-green, axiom-clean)**: `certainType_diff_dade_apply_eq_of_mem_V` (step 4):
  v∈ticVdiff.V で `(μ_ij−μ_ik)^τ(v) = δ_j(ω_ij^σ(v)−ω_ik^σ(v))`。L↔G plumbing 全 discharge
  (v∈A₀ via l=1; (w:L)=⟨v,_⟩ via Subtype.ext+coe_ticWEquivSdiffW; (w:L)∈sdiff.V; (4.3.c)×2 + step1)。
  recipe = tau_toDadeMap_apply_of_mem → ClassFunction.sub_apply → ←hwL → certainType_apply_eq_of_mem_V×2
  → hwpt (Subtype.ext rfl) → certainTypeOmegaSigma_apply_of_mem_V×2 → certainType_sign_eq → ring。
- **▶▶ 残 = steps 5-8 (trichotomy endgame, 別 commit ~150-250 行)。設計確定 (再調査不要)**:
  φ := h.tau.toDadeMap (certainTypeDiffSupported …), ψ := φ − δ_j•(ω_ij^σ − ω_ik^σ) [= certainTypeOmegaSigma×2]。
  1. **ψ が V で消滅**: step4 (= equality) を `ψ v = 0` 形へ (φ(v) − δ_j(ω_ij^σ(v)−ω_ik^σ(v)) = 0)。
  2. **‖φ‖²=2**: `h.tau.toDadeIsometryData.isDadeIsometry.inner_eq` (or full_inner_eq pattern) ⟹
     ⟨φ,φ⟩=⟨μ_ij−μ_ik,μ_ij−μ_ik⟩=2。**要 μ_ij≠μ_ik** ⟹ **conclusion 3 に χ₂≠χ₂' 仮説追加**
     (textbook 0<j,k<w₂ で j=k なら自明 0=0; (4.1) 列間 distinct で μ_ij≠μ_ik)。φ∈ZIrr via maps_virtualCharacter。
  3. **f(p,q):=⟨φ,chiFam(p,q)⟩ は ℤ 値** (`inner_mem_ZIrr_int`, φ∈ZIrr ∧ chiFam∈ZIrr) ∧ **∑f²≤‖φ‖²=2**
     (Bessel, chiFam 正規直交) ⟹ **|supp f|≤2**。[Bessel/「norm² n ⟹ ≤n nonzero」補題 = 要発掘 or 自作;
     `ncard_inner_chiFam_ne_zero_le_one` [S05:1460, norm1→≤1] の norm2 一般化]。
  4. **sigmaCoeff(ψ)(p,q) = f(p,q) − δ_j([pq=P_ij]−[pq=P_ik])** (ω_ij^σ=chiFam(P_ij), via sigma_omega +
     omegaProdEquiv.symm 同定; P_ij=(w1char i 系の tic-index, χ₂); 異列 P_ij≠P_ik [col q_j≠q_k])。
     ⟹ **NC(ψ)=|supp(sigmaCoeff ψ)| ≤ |supp f|+2 ≤ 4 < 2w₁** (w₁≥3)。
  5. **trichotomy** `sigmaCoeff_trichotomy hVeq=rfl app=ticVdiffFullDadeApplication hψ hgap hNC`:
     hgap=w₁+2≤w₂ [要 (W odd ⟹ w₁<w₂) 補題; gap], hNC=NC<2w₁。→ (a)/(b)/(c)。
  6. **(a)** [∀pq sigmaCoeff=0] ⟹ ⟨ψ,chiFam(P_ij)⟩=⟨ψ,chiFam(P_ik)⟩=0 ⟹ ⟨φ,ω_ij^σ⟩=δ_j, ⟨φ,ω_ik^σ⟩=−δ_j
     ⟹ **‖ψ‖²= 2 − 2δ_j(δ_j−(−δ_j)) + δ_j²·2 = 2−4+2 = 0 ⟹ ψ=0** (norm 計算; chiFam 正規直交+δ²=1)。
     **🔑 `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` [S05:1234] は χ=0 でなく χ|V=0 しか出さない ⟹ case(a) には不可。norm 論法が要**。
  7. **(b)** [列 q₀ 定数 c≠0, w₁≥3 行] ⟹ p≠p_i の ≥w₁−1≥2 行で sigmaCoeff=f=c≠0 (2 個の f 非零) +
     δ-点の ≥1 個が q₀ 外 (sigmaCoeff=0 ⟹ f=±δ_j≠0, 3 個目) ⟹ |supp f|≥3 >2 矛盾。
  8. **(c)** [行 i₀ 定数 c≠0, w₂≥5 by gap] ⟹ q∉{q_j,q_k} の w₂−2≥3 列で sigmaCoeff=f=c≠0 ⟹ |supp f|≥3 矛盾。
- **🔑🔑 φ(1)=0 は不要** (session 30 plan の step5「1 で消滅⟹λ₁−λ₂」は norm 論法で代替; 1∈dadeSupport は
  H(a) 依存で abstract に否定不可 — 深入り回避)。**`exists_irr_sub_irr_of_inner_self_two` も不要**。
- **要発掘/自作 補題** (次 session 最初): (i) ‖φ‖²=2 の isometry 経路 (h.tau.…isDadeIsometry.inner_eq の正確名),
  (ii) |supp f|≤2 (Bessel or norm2→≤2), (iii) w₁<w₂ ⟹ w₁+2≤w₂ (odd gap), (iv) sigmaCoeff(ψ) の f+δ 展開
  (ω_ij^σ=chiFam(P_ij) 同定 = omegaProdCharTic→sigma_omega→omegaProdEquiv.symm)。
正本 = 本 session 33。**foundation+step4 DONE。endgame は上記 8 段で確定 (φ(1)=0/λ₁−λ₂ 回避済)。**

### ✅ session 33 cont.³ — endgame INPUT 補題 全 landed (残 = trichotomy assembly のみ)
**landed (build-green, axiom-clean, AxiomsCheck 登録済)**:
- `certainType_diff_dade_apply_eq_of_mem_V` (step 4): ψ が V で消滅 (equality 形)。
- `certainType_diff_dade_inner_self`: **‖φ‖²=2** (要 χ₂≠χ₂'; τ isometry `h.tau.inner_eq` + `columnFamily_mu_ne` (4.1))。
- `sigmaNC_dade_le_two`: **NC(φ)≤2** (norm-2⟹2 constituents via `mem_ZIrr_inner_self_eq_sum_sq`+
  `exists_pair_of_sum_sq_eq_two`、φ=ε_α α+ε_β β、各 `ncard_inner_chiFam_ne_zero_le_one`≤1、supp⊆S_α∪S_β)。
  **gotcha (再調査不要)**: 文字群 index の `Finite` synth が ticVdiff unfold で timeout → proof 冒頭で
  `haveI : Fintype (W1hat) := Fintype.ofFinite _` ×2 + `haveI : Fintype (prod) := inferInstance` +
  `haveI : Finite (prod) := Finite.of_fintype _`、union finite は `Set.finite_univ.subset (subset_univ _)`。
- `certainTypeOmegaSigma_eq_chiFam`: **ω_ij^σ = chiFam(P_ij)** where P_ij=`omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)`
  (= `sigma_omega` 一発)。⟹ δ-term 位置 P_ij,P_ik 確定。

### ▶▶ 残 = trichotomy assembly (1 セッション規模、設計確定)
φ:=h.tau.toDadeMap(certainTypeDiffSupported …)、ψ:=φ − δ_j•(certainTypeOmegaSigma χ₂ i − certainTypeOmegaSigma χ₂' i)。
1. **ψ vanish on V**: step4 (equality) を `ψ v=0` に (`ClassFunction.sub_apply`+`smul_apply`、自明)。
2. **NC(ψ)≤4**: sigmaCoeff(ψ)(pq)=⟨ψ,chiFam pq⟩ = ⟨φ,chiFam pq⟩ − δ_j([pq=P_ij]−[pq=P_ik])
   [certainTypeOmegaSigma_eq_chiFam + chiFam 正規直交 `chiFam_spec.2.2.1`]。
   ⟹ supp(sigmaCoeff ψ) ⊆ supp(sigmaCoeff φ) ∪ {P_ij,P_ik}、NC(ψ)≤NC(φ)+2≤4。
3. **🔑🔑 ORIENTATION 問題 (残 hard part の核)**: `sigmaCoeff_trichotomy` は **w₁+2≤w₂** (W₁=rows) を要求。
   だが certain-type に w₁<w₂ は無い (確認済: CertainTypeHypothesis に順序無)。**ただし `coprime_card_W1_card_W2`
   ⟹ w₁≠w₂、両 odd ⟹ |w₂−w₁|≥2**。⟹ **小さい方を rows に取れば gap 成立** (min+2≤max、max≥5)。
   - w₁<w₂: `sigmaCoeff_trichotomy` 直接 (rows=Ŵ₁、gap=w₁+2≤w₂、NC<2w₁≥6)。
   - w₂<w₁: **transposed** — `grid_trichotomy` を a'(q,p)=sigmaCoeff(p,q) に (ι=Ŵ₂,κ=Ŵ₁) で直接適用
     (separability/NC は転置不変、gap=w₂+2≤w₁)。(b')(c') は (c)(b) に対応。**両 case 要 = 残最大作業**。
   - 別解: min(w₁,w₂)≥5 なら corollary `sigmaCoeff_eq_zero_of_sigmaNC_lt` (NC<min) で case(a) 直接 ⟹
     trichotomy 不要。**min=3 の時だけ** trichotomy+orientation 要 (w_smaller=3 を rows)。
4. **(b)(c) 排除 = |supp f|≥3 矛盾** (f=sigmaCoeff φ、|supp f|≤2): 列定数 c≠0 (rows≥3 行) ⟹ p≠p_i の
   ≥rows−1≥2 行 pure-f=c + 異列 δ-点≥1 個 off-column (f=±δ_j) ⟹ |supp f|≥3>2。行定数も同様 (cols≥5、cols−2≥3)。
5. **(a) ⟹ ψ=0**: ⟨ψ,chiFam P_ij⟩=⟨ψ,chiFam P_ik⟩=0 ⟹ ⟨φ,ω_ij^σ⟩=δ_j,⟨φ,ω_ik^σ⟩=−δ_j ⟹
   ‖ψ‖²=2−2δ_j(δ_j−(−δ_j))+2=0 (chiFam 正規直交+δ²=1) ⟹ ψ=0 (`ClassFunction.inner_self_eq_zero`)。
6. **最終 statement**: `(μ_ij−μ_ik)^τ = δ_j(ω_ij^σ−ω_ik^σ)` (要 χ₂≠χ₂'; ψ=0 から移項) → (4.9) → case-B → (6.8)。

正本 = 本 session 33 cont.³。**input 補題 全 landed (9 commits)。残 = assembly (orientation 込み trichotomy)、1 セッション。**

### 🔧 session 33 cont.⁴ — 🚨 exclusion 精査: **|f|≤1 が必須** (|supp f|≤2 では不足)
**🚨 重要発見 (notes cont.³ の exclusion 設計を訂正)**: trichotomy (b)(c) 排除は |supp f|≤2 だけでは
**w₂=3 の row case を排除できない**。
- P_ij=(omegaProdEquiv.symm(omegaProdCharTic χ₂ i)), P_ik=(... χ₂' i)。**P_ij.1=P_ik.1 (同 row, 両方 i)、
  P_ij.2≠P_ik.2 (異 column, χ₂≠χ₂')**。
- row i₀=P_ij.1 定数 c≠0, w₂=3: 純f列 1個 + δ列で f(P_ij)=c+δ_j, f(P_ik)=c−δ_j。
  c=−δ_j なら f(P_ij)=0 だが **f(P_ik)=−2δ_j**。supp f={純f点, P_ik}=2 点 ⟹ |supp f|≤2 と無矛盾 = **排除できない**。
  ⟹ **|f(pq)|≤1 (f∈{0,±1}) が必要** (f(P_ik)=±2 を弾く)。
- ⟹ exclusion は **|supp f|≤2 (column case) + |f|≤1 (row w₂=3 case)** の両方を使う。
  あるいは uniform に **∑f²≤2** (Bessel) でも可 (∑≥3c²+2≥5>2)。**|f|≤1 が最小限**。

### ▶ 残 INPUT 補題 = **`sigmaCoeff_dade_eq_zero_or_one`** (f∈{0,±1})
証明ルート (cont.⁴ で draft 着手→revert; 設計確定):
φ=(cα:ℂ)•α+(cβ:ℂ)•β (mem_ZIrr_inner_self_eq_sum_sq+exists_pair_of_sum_sq_eq_two, cα,cβ∈{±1});
chiFam pq=(ε:ℤ)•ν (exists_zsmul_irreducibleCharacter_of_inner_self_one, ε∈{±1}, ν:IrreducibleCharacter);
f=⟨φ,chiFam pq⟩=cα·ε·⟨α,ν⟩+cβ·ε·⟨β,ν⟩=cα·ε·[⟨α,_⟩=ν]+cβ·ε·[⟨β,_⟩=ν]。
α=ν⟹cα·ε∈{±1}; β=ν⟹cβ·ε∈{±1}; else 0 (α≠β で同時不可)。
**🛑 draft で詰まった点 (次回修正)**:
  (1) 右 smul lemma 名 = **`OddOrder.RepresentationTheory.inner_smul_right`** (`ClassFunction.inner_smul_right` 不在)。
  (2) `irreducibleCharacter_inner_eq_ite ⟨α,hαm⟩ ν` の ite 条件は **IrreducibleCharacter 等式 `⟨α,hαm⟩=ν`** で
      α:CF とは coercion 差 ⟹ by_cases も IrreducibleCharacter 等式で。⟨α,(ν:CF)⟩ rw に coe 整合注意。
  (3) 最後の `(c:ℂ)=0∨=1∨=-1` 閉じは `rcases hcα<;>rcases hε<;>rw[…]<;>norm_num` で disjunct 自動選択不可 →
      明示 `left/right` か `decide`不可(ℂ)→ `first|(left;norm_num)|(right;left;norm_num)|(right;right;norm_num)`。

### ▶▶ 残 = assembly (cont.³ の 6 段 + |f|≤1; 1 セッション)
INPUT 全 (step4, ‖φ‖²=2, NC(φ)≤2, ω_ij^σ=chiFam(P_ij), **+f∈{0,±1}**) 揃えば:
ψ定義→V消失→NC(ψ)≤4→**orientation** (w₁<w₂直接/w₂<w₁ transposed grid_trichotomy)→
(b)(c)排除 (|supp f|≤2 + |f|≤1, P 同row異col)→(a)⟹‖ψ‖²=0⟹ψ=0→最終 statement (χ₂≠χ₂' 要)。
正本=本 session 33 cont.⁴。**10 commits landed; 残=f∈{0,±1}+assembly。**

### ✅ session 33 cont.⁵ — f∈{0,±1} landed (`sigmaCoeff_dade_eq_zero_or_one`) = **全 INPUT 完了**
- **landed (build-green, axiom-clean, AxiomsCheck 登録)**: `sigmaCoeff_dade_eq_zero_or_one`
  (⟨φ,chiFam pq⟩∈{0,±1})。draft snag 解決済: **inner は left 線形・right 共役線形**
  (`OddOrder.RepresentationTheory.inner_smul_right` が `star ↑ε` を出す → `star_intCast` 要)、
  ite の CF↔IrreducibleCharacter coe は **型注釈 `have hαν : ... := irreducibleCharacter_inner_eq_ite ⟨α,hαm⟩ ν`**
  で吸収、disjunct 閉じは `rcases<;>rw<;>norm_num`。
- **🎉 (4.8) conclusion 3 の INPUT 補題 全 landed** (step4 / ‖φ‖²=2 / NC(φ)≤2 / ω_ij^σ=chiFam(P_ij) / f∈{0,±1})。
  12 commits landed this session。
- **▶▶ 残 = assembly のみ** (1 theorem, ~180 行, helper 分割推奨):
  (1) `sigmaCoeff_psi_eq`: a(pq):=sigmaCoeff(ψ)(pq) = f(pq) − δ_j([pq=P_ij]−[pq=P_ik])
      [certainTypeOmegaSigma_eq_chiFam + chiFam 正規直交; ψ:=φ−δ_j(certainTypeOmegaSigma χ₂ i−…χ₂' i)]。
  (2) ψ vanish on V [step4 移項], a separable [sigmaCoeff_add_eq], NC(ψ)≤4 [supp a⊆supp f∪{P_ij,P_ik}, NC(φ)≤2]。
  (3) orientation: w₁≠w₂(coprime)・|Δ|≥2(odd) ⟹ 小さい方 rows。w₁<w₂=直接 grid_trichotomy(Ŵ₁,Ŵ₂)、
      w₂<w₁=transposed(Ŵ₂,Ŵ₁, a'(q,p)=a(p,q))。両者 (all-0)∨(row)∨(column) を出す。
  (4) exclusion: column(w₁≥3)=|supp f|≤2 矛盾; row(w₂≥5 or w₂=3)=|supp f|≤2 **+ f∈{0,±1}**
      (w₂=3,c=−δ_j で f(P_ik)=−2δ_j を弾く)。**P_ij.1=P_ik.1(同row,both i), P_ij.2≠P_ik.2(異col,χ₂≠χ₂')** 要証明。
  (5) (a)⟹ a(P_ij)=a(P_ik)=0 ⟹ f(P_ij)=δ_j,f(P_ik)=−δ_j ⟹ ‖ψ‖²=2−2δ_j·2δ_j+2=0 ⟹ ψ=0。
  (6) 最終 `certainType_diff_dade_eq` (χ₂≠χ₂' 仮説付): (μ_ij−μ_ik)^τ = δ_j(ω_ij^σ−ω_ik^σ)。→ (4.9)→case-B→(6.8)。
正本=本 session 33 cont.⁵。**全 INPUT landed (12 commits); 残=assembly 1 unit。**

### ✅ session 33 cont.⁶ (/loop) — `sigmaCoeff_psi_eq` landed; 残=orientation+exclusion+conclude
- **landed** (commit 68021c0a, full build 3787 + AxiomsCheck): `sigmaCoeff_psi_eq` (general φ):
  a(pq)=sigmaCoeff(ψ)(pq) = ⟨φ,chiFam pq⟩ − δ_j·([P_ij=pq]−[P_ik=pq]), P_ij=omegaProdEquiv.symm(omegaProdCharTic χ₂ i)。
  gotcha: `if`に `open scoped Classical in` (docstring の**前**)、columnFamily に `[Fintype ↥(W1⊔W2)]`+`[Invertible …]` 要。
- **▶ 残 = final theorem `certainType_diff_dade_eq`** (1 unit, 最難 = exclusion):
  - skeleton: set φ=h.tau.toDadeMap(certainTypeDiffSupported…), ψ=φ−δ_j•(certainTypeOmegaSigma χ₂ i−…χ₂' i);
    ψ vanish on V [step4 移項 + ClassFunction.zsmul_apply]; a:=sigmaCoeff(ψ) separable [sigmaCoeff_add_eq];
    a(pq)=sigmaCoeff_psi_eq。
  - **all a=0** (orientation): w₁≠w₂(coprime, card_charGroup_subgroupOf で Ŵ card=w)、|Δ|≥2(odd) ⟹
    w₁<w₂=`sigmaCoeff_trichotomy` 直接; w₂<w₁=`grid_trichotomy` transposed (ι=Ŵ₂,κ=Ŵ₁, a'(q,p)=a(p,q))。
    両者 (all-0)∨(column)∨(row)。
  - **exclusion** (要 component-structure 補題): **P_ij.1=P_ik.1 (同 Ŵ₁, both i), P_ij.2≠P_ik.2 (異 Ŵ₂, χ₂≠χ₂')**
    [omegaProdEquiv.symm∘omegaProdCharTic の (Ŵ₁,Ŵ₂) 分解 = (w1charEquiv i 対応, χ₂ 対応); tic omegaProdEquiv ↔
    transported char の compatibility 補題 ~40行 要]。
    column j₀ const c≠0: {δ-rows in col}={P_ij.1}(1個, 同row) ⟹ Ŵ₁∖{P_ij.1} の ≥w₁−1≥2 行で g=sigmaCoeff(φ)=c≠0
    + off-col δ(≥1, 異col) で g=±δ_j≠0 ⟹ |supp g|≥3 > 2 矛盾 [sigmaNC_dade_le_two]。
    row i₀ const: w₂≥5 なら w₂−2≥3 pure-g; w₂=3 (transposed orientation) は **f∈{0,±1}** で f(P_ik)=±2 弾く。
  - **conclude**: all a=0 ⟹ a(P_ij)=0 ⟹ sigmaCoeff(φ)(P_ij)=s, a(P_ik)=0 ⟹ sigmaCoeff(φ)(P_ik)=−s ⟹
    ⟨φ,ωij⟩=s,⟨φ,ωik⟩=−s ⟹ ‖ψ‖²=2−2s·2s+2·s²=0 ⟹ ψ=0 [`eq_zero_of_inner_self_re_eq_zero`, ZIrrFourier:189]。
  - 最終: (μ_ij−μ_ik)^τ = δ_j(ω_ij^σ−ω_ik^σ) (χ₂≠χ₂' 仮説)。→ (4.9)→case-B→(6.8)。
正本=本 cont.⁶。**残=final theorem (orientation+exclusion+conclude); component-structure 補題が最初の sub-step。**

### 🔧 session 33 cont.⁷ (/loop) — assembly ~90% : conclude + distinctness landed; 残 = exclusion
- **landed this loop** (4 commits): `sigmaCoeff_psi_eq` (a(pq)=g(pq)−s([P_ij=pq]−[P_ik=pq])),
  `omegaProdCharTic_ne`/`omegaProdEquiv_symm_omegaProdCharTic_ne` (P_ij≠P_ik),
  **`certainType_diff_dade_eq_of_all_sigmaCoeff_zero`** (case (a) ⟹ conclusion 3 = ψ=0 via ‖ψ‖²=0)。
  + helper `exists_two_ne_ne` (fintype card≥3, 2 distinct ≠ d) landed (uncommitted→commit予定)。
- **▶ 残 = exclusion `hnocol`/`hnorow` + orientation + final** (設計確定, ~150行):
  - **hnocol** (¬∃ 列 j₀ c≠0 定数): rintro ⟨j₀,c,hc,hcol,hoff⟩; g:=sigmaCoeff(φ); hexp=sigmaCoeff_psi_eq;
    hsupp2: {pq|g≠0}.ncard≤2 (=sigmaNC_dade_le_two, sigmaNC unfold); hg01 (sigmaCoeff_dade_eq_zero_or_one)。
    by_cases hboth: P_ij.2=j₀ ∧ P_ik.2=j₀:
    - **both**: hcol@P_ij.1, P_ik.1 → g(P_ij)=c+s, g(P_ik)=c−s; hsum:g(P_ij)+g(P_ik)=2c, hdiff:..=2s;
      `rcases hg01 P_ij<;>hg01 P_ik<;>sign_eq<;>rw<;>first|exact hc(by linear_combination (-1/2)*hsum)|norm_num at hdiff`
      (g diff=2s=±2 ⟹ {1,−1} ⟹ sum=0 ⟹ c=0 矛盾)。
    - **¬both**: by_cases P_ij.2=j₀, P_ik.2=j₀ (3 combo, (T,T)=absurd hboth):
      (T,F)P_off=P_ik,d=P_ij.1; (F,T)P_off=P_ij,d=P_ik.1; (F,F)P_off=P_ij,d=P_ij.1。
      exists_two_ne_ne (card Ŵ₁=w₁≥3 via card_charGroup_subgroupOf+three_le_card) d → r₁,r₂≠d distinct;
      witnesses {(r₁,j₀),(r₂,j₀),P_off} ⊆ {pq|g≠0} (g(r,j₀)=c≠0 [hcol+hexp+(r,j₀)∉{P_ij,P_ik}],
      g(P_off)=±s≠0 [hoff+hexp]); 3 distinct (r₁≠r₂, P_off.2≠j₀) → ncard≥3 (ncard_eq_three+ncard_le_ncard) 矛盾 hsupp2。
  - **hnorow** = hnocol の転置 (行 i₀, w₂≥3, P_ij.1/P_ik.1=i₀ で同 row 判定; 同構造)。
  - **all-zero + orientation**: card(tic.W1)≠card(tic.W2) (coprime+both≥3⟹≠), |Δ|≥2 (odd);
    w₁<w₂: `sigmaCoeff_trichotomy (ticVdiff h) rfl app hψV hgap hNC` → (a)∨(b)∨(c); kill b=hnocol,c=hnorow。
    w₂<w₁: `grid_trichotomy` on a'(q,p)=sigmaCoeff(ψ)(p,q) over (Ŵ₂,Ŵ₁), gap w₂+2≤w₁; (b')=row→hnorow,(c')=col→hnocol。
    hψV (step4 移項), hNC: sigmaNC(ψ)≤4 (supp⊆supp(φ)∪{P_ij,P_ik}) < 2·min(w)≥6。
  - **final `certainType_diff_dade_eq`** = `apply certainType_diff_dade_eq_of_all_sigmaCoeff_zero; [all-zero]`。
正本=本 cont.⁷。**conclude+distinctness landed; 残=hnocol/hnorow/orientation/final (設計完備)。**

## 2026-06-12 (session 33 cont.⁸, /loop): 🎉🎉🎉 (4.8) conclusion 3 COMPLETE — (4.8) 全結論 DONE
**`certainType_diff_dade_eq` landed (commit 07908c46, full build 3787 + AxiomsCheck, axiom-clean)**:
`(μ_ij−μ_ik)^τ = δ_j(ω_ij^σ − ω_ik^σ)` (要 χ₂≠χ₂'; FT-critical isometry 恒等式)。
- 組立: `apply certainType_diff_dade_eq_of_all_sigmaCoeff_zero` → ∀pq sigmaCoeff(ψ)=0 を:
  hψV (step4 移項) + hadd (sigmaCoeff_add_eq 3.7) + hNC4 (≤4, supp⊆supp G∪{P_ij,P_ik}) +
  orientation (w₁≠w₂ coprime+odd ⟹ w₁+2≤w₂ ∨ w₂+2≤w₁) で `grid_trichotomy` (direct on a / transposed on aᵀ) →
  (b)(c) を `grid_no_constant_column`/`grid_no_constant_row` で排除 → 全0。
- **abstract exclusion** (汎用 ι,κ): `grid_no_constant_column` (both-in-col⟹c=0 [g(P_ij)=c+s,g(P_ik)=c−s,
  diff=2s=±2⟹{1,−1}⟹c=0] / ¬both⟹≥3 supp g 矛盾) + `grid_no_constant_row` (swap corollary)。helper `exists_two_ne_ne`。
- gotchas (再調査不要): grid_trichotomy は `Nat.card` (not Fintype.card)・要 `import S05_GridTrichotomy`;
  inner は left-linear/right-conj (`inner_smul_right`=star ↑ε, `star_intCast`); `open scoped Classical in` は
  docstring の**前**; Prod.swap if 同定は `Prod.fst_swap/snd_swap+tauto`; defeq (ticVdiff.W1=tic.W1) は `exact` で。
- **🎉 §6 (4.8) 全結論 (1)(2)(3) 完成** (sessions 30-33)。conclusion 3 は本 session の /loop で foundation→
  step4→inputs(‖φ‖²=2,NC≤2,ω=chiFam,f∈{0,±1})→assembly を 13+ commits で完走。

### ▶▶ 次 = (4.9) (Theorem (4.9), notes 上記 session 30 の (4.9) 転記参照)
(4.9)(a): μ_j∈T⟹μ̄_j∈T∧μ̄_j≠μ_j; 0≠Z[T,L^#]=Z[T,A]。 (b): Z[T]→Z[Irr G], μ_j↦δ_k∑_iω_ij^σ は
isometry で Z[T,A] 上 τ と一致。**(4.9)(b) は (4.8) conclusion 3 を使う** ((μ_j−μ_k)^τ=∑_i(μ_ij−μ_ik)^τ=
δ_k∑_i(ω_ij^σ−ω_ik^σ))。⟹ (4.8) 完成で (4.9) unblocked。→ (4.9) → S08 case-B → (6.8)。
正本=本 cont.⁸。**(4.8) DONE; 次 = (4.9)。**

## 2026-06-12 (session 34, /loop): ✅ (4.9)(b) summed isometry landed (computational core)

**commit `8603fe8c`** (S06_CertainTypeIsometry, axiom-clean, AxiomsCheck 登録, full build 3771)。
(4.9)(b) の計算核 = 「列差 μ_j−μ_k を τ で送ると δ_j ∑_i(ω_ij^σ−ω_ik^σ)」を landed:

- **`tau_toDadeMap_sum`**: 「τ (= h.tau.toDadeMap) は有限和に対し加法的」 = τ(∑α_i)=∑ τ(α_i)。
  **🔑 手法**: 抽象 `FullDadeIsometryData` の map は `IsDadeMap.unique` で構成版 `h.dade0.dadeMap`
  と一致 (両者 IsDadeMap h.dade0; 後者 = `Hypothesis.isDadeMap_dadeMap`)、構成版は本物の ℂ-linear
  `dadeLinearMap` (`dadeLinearMap_apply` rfl) ⟹ `map_sum`。ClassFunction に `sum_apply` 不要で済む。
  → **(4.9)(b) full / (4.10) でも τ-linearity が要るとき再利用可**。
- **`certainType_diff_dade_sum_eq`**: `τ(∑_i certainTypeDiffSupported_i) = δ_j • ∑_i(ω_ij^σ−ω_ik^σ)`。
  proof = `rw [tau_toDadeMap_sum, Finset.smul_sum]` → `Finset.sum_congr rfl (conclusion 3)` の 2 行。
  per-row 仮説 `∀i, μ_ij(1)=μ_ik(1)` で stated (δ_j=δ_k は conclusion 2、列の全 μ_ij は同次数)。

### ▶▶ 次 = (4.9) 残り (session 34 cont. 以降)
1. ✅ **列次数恒常性 + 橋渡し DONE** (commit `3596eda3`): `columnFamily_mu_apply_one_eq`
   (μ_ij(1)=μ_0j(1), `columnFamily_difference_apply_one` から) + `forall_columnFamily_mu_apply_one_eq_of_sum_eq`
   (∑μ_ij(1)=∑μ_ik(1) ⟹ ∀i 同次数; w₁≠0 で cancel) + `certainType_diff_dade_sum_eq_of_degree`
   (summed isometry を μ_j(1)=μ_k(1) 仮説で再述)。**🔑 罠**: columnFamily は home-file の section
   variable で `[Fintype ↥(W1⊔W2)] [Invertible (card(W1⊔W2):ℂ)]` を要求 → isometry leaf で明示要
   (postpone は proof 経由 unify のときだけ効く; hypothesis 型は upfront synth)。S06-namespace 補題は
   dot 不可 (`columnFamily_mu_apply_one_eq h χ₂`, 位置引数; Hypothesis46-namespace の columnFamily 等は dot 可)。
2. **(4.9)(a)** 共役 μ̄_j=μ_{j'} (ω̄_ij=ω_{i'j'}, j'≠j; (3.9)+(4.3) で δ 引き出し) + Z[T,L^#]=Z[T,A]
   ((4.7) 経由)。**hard 寄り** (character conjugation + (3.9))。要調査: 指標複素共役 API + (3.9) map。
3. **(4.9)(b) full**: isometry Z[T]→Z[Irr G] の写像化 (ω_ij^σ 正規直交で「isometry 明らか」=
   `sigma_inner` 系 S05:1310 付近) + Z[T,A] 上 τ 一致 (= summed identity の線型拡張)。
→ (4.9) → S08 case-B (`sibleySetup_is_coherent` の CertainType branch) → (6.8) capstone。
**正本=本 session 34。(4.9)(b) 計算核+次数橋渡し landed; 次 = (4.9)(a) 共役 or (4.9)(b) isometry 性。**

## 2026-06-12 (session 35, /loop): ✅ (4.9)(b) isometry 性 COMPLETE + (4.9)(a)/IsCoherent 精密 scope

**commit `6c2d555b`** (S06_CertainTypeIsometry, axiom-clean, full build 3791, AxiomsCheck 5 件登録)。
(4.9)(b) の **isometry 性**(σ 像と μ 列和が同 Gram 行列 `w₁·δ_jk`)を完全形式化:

- **`omegaProdCharTic_eq_iff`**: grid-index 判定 `ω_ij^{tic}=ω_{i'j'}^{tic} ↔ χ₂=χ₂' ∧ i=i'`
  (`omegaProdChar_inj`+`w1CharEquiv` injective+`ticWEquivSdiffW` 全射で comp strip)。
  `omegaProdCharTic_ne` を i≠i' へ一般化。
- **`certainTypeOmegaSigma_inner`**: per-element σ 像直交 `⟨ω_ij^σ,ω_{i'j'}^σ⟩=δ`。
  **🔑 経路 = `sigma_inner`(σ 等長, S05:985)+`omega_inner_self`/`omega_inner_ne`** で chiFam 不要。
  `certainTypeOmegaSigma = σ(ω(omegaProdCharTic))` を `simp only [certainTypeOmegaSigma]` で開いて
  sigma_inner 適用 → ⟨ω(P),ω(P')⟩ → omegaProdCharTic_eq_iff。
- **`certainTypeOmegaSigma_sum_inner`** / **`columnFamily_mu_sum_inner`**: σ-side / μ-side(L 上)の
  列和直交 = `if χ₂=χ₂' then (w₁:ℂ) else 0`。bilinear 展開(`inner_sum_left`/`inner_sum_right`)+
  per-element + `Finset.sum_ite_eq`。μ-side は S06_CertainTypeClifford:813 テンプレ
  (`irreducibleCharacter_inner_eq_ite`+`columnFamily.injective`+`columnFamily_mu_ne`)。
- **`certainType_omega_sum_isometry`** (capstone): `⟨∑ω_ij^σ,∑ω_il^σ⟩=⟨∑μ_ij,∑μ_il⟩`
  (両辺 `if χ₂=χ₂' then w₁ else 0`)。δ_k=±1 で δ_k² 相殺ゆえ符号なしで写像の等長性そのもの。
- **罠**: statement の `if χ₂=χ₂'` は MonoidHom 等値非可決定 → `open scoped Classical in` を
  **docstring の前**に置く(後ろは parse error; 既存 561/693/764 と同形)。

**🔑 IsCoherent インターフェース確定** (`S07.IsCoherent τ S A`, S07_Coherence:1557; 下流 S08 case-B が
要求する型)。5 フィールド: `nonzero`(∃φ∈Z[S,A] φ≠0) / `extension`(IntegralCharacterMap) /
`extension_inner_eq`(Z[S]=zSpan 上等長) / `extends_on_supported`(Z[S,A]=zSupportedSpan 上 τ 一致) /
`extension_mem_ZIrr`(Z[S]→ZIrr)。⟹ **(4.9)(b) の私の identity は field 3(等長)/field 4(τ一致)の
「生成元上」版**; 残りは ① extension map を Z[𝒯] 上 packaging(`Basis.constr` 級)→ ② 生成元等式を
zSpan へ lift → ③ nonzero(=(4.9)(a))→ ④ ZIrr codomain。

### ▶▶ 次 = (4.9)(a) 共役 + IsCoherent packaging (session 36 以降; **scope 済**)

**(4.9)(a) の確定チェーン** (full scope 済, 新規基礎インフラ要):
1. **複素共役 RingEquiv** `ℂ ≃+* ℂ`: mathlib `Complex.conjAe.toRingEquiv`(要 build 確認; Pf 内に既存
   使用なし)。
2. **character 共役 = 逆指標** `galoisMap (conj) (omega ξ) = omega ξ⁻¹` (ext + omega_apply 値計算;
   `galoisMap_apply_apply` S05/GaloisCharacter:384)。⟹ ω̄_ij = ω(omegaProdChar χ₁⁻¹ χ₂⁻¹) = grid (i',j')。
3. **grid index 写像** (i,j)↦(i',j'): χ₁↦χ₁⁻¹(w1CharEquiv 経由 i'), χ₂↦χ₂⁻¹(列 j'); **j'≠j は |W| 奇**
   (χ₂≠χ₂⁻¹ ⟺ χ₂²≠1 ⟺ ord χ₂ 奇 ∧ χ₂≠1); j' は i 非依存。
4. **(3.9)+(4.3) bridge** μ̄_ij = μ_{i'j'}: `sigma_mapRingEquiv_comm`(S05:1589, σ が Galois 可換)を
   u=conj で適用 ⟹ `conj(ω_ij^σ)=ω̄_ij^σ=ω_{i'j'}^σ`; (4.3.b) σ(ω_ij)=δ_j μ_ij で δ_j μ̄_ij=δ_{j'}μ_{i'j'}
   ⟹ μ̄_ij=μ_{i'j'} (δ=±1)。
5. **μ̄_j=μ_{j'}≠μ_j** (i で和) ⟹ μ̄_k∈𝒯 ∧ μ̄_k≠μ_k ⟹ **nonzero**(μ̄_k−μ_k∈Z[𝒯,A] 非零)。
   **Z[𝒯,L^#]=Z[𝒯,A]** は (4.7)(Supp μ_j⊆A∪{1}) + 次数零(virtual char が 1 で消える)。

**判断**: (4.9)(a) は新規 API(conj RingEquiv, character 共役, grid index 写像)を要し 1 commit 超。
IsCoherent packaging(extension map on Z[𝒯])も同様。両者で **§6 残りの主作業**。Opus 継続可
(Galois は (3.9) で既 landed = 利用のみ; full (3.8) 級の新規 grid 組合せ論は不要)。
**第一 leaf 候補 = `S06_CertainTypeConjugation.lean`**(2 → 3 → 4 → 5 の順; nonzero まで)。
**正本=本 session 35。(4.9)(b) 完全 DONE; 次 = (4.9)(a) チェーン step 1-2 から。**

## 2026-06-12 (session 36, /loop): ✅ (4.9)(a) 共役インフラ — μ-bridge `δ_j μ̄_ij = δ_{j'} μ_{i'j'}` 到達

新 leaf **`S06_CertainTypeConjugation.lean`** (5 commits, 全 axiom-clean, full build 3792)。(4.9)(a)
の共役論法を σ-side + L-side 両方で構築し、**核心の μ-character bridge まで landed**:

- **commit `b14c19a5`** 共役 foundation: `galoisMap_conj_omega` (複素共役 = 逆指標 `galoisMap conj
  (ω χ) = ω χ⁻¹`; 値は 1 の冪根ゆえ `Complex.norm_eq_one_of_pow_eq_one`+`Complex.inv_eq_conj`;
  **conj RingEquiv = `Complex.conjAe.toRingEquiv`**) + `certainTypeOmegaSigma_conj` (G-side σ_G の
  共役 = σ_G(ω P⁻¹), via `sigma_mapRingEquiv_comm` (3.9))。**`galoisMap_conj_omega` は general
  (任意 TICyclicHypothesis) で σ_G/σ_L 両方に再利用**。
- **commit `902c2533`** grid-index 共役: `omegaProdChar_inv` (ω(χ₁,χ₂)⁻¹=ω(χ₁⁻¹,χ₂⁻¹), ℂˣ 可換) +
  `rowInv`/`w1CharEquiv_rowInv` (行反転 index, w1CharEquiv (rowInv i)=(w1CharEquiv i)⁻¹) +
  `omegaProdCharTic_inv` + `certainTypeOmegaSigma_conj_eq` (**(ω_ij^σ)̄ = ω_{i'j'}^σ**, σ-side 閉包)。
- **commit `02011962`** L-side 閉包: `chiColumn_conj` (χ_ij̄=χ_{i'j'}; chiColumn=ω(omegaProdChar)
  ゆえ general lemma 再利用) + `sigma_chiColumn_conj` (**σ_L(ω_ij)̄ = σ_L(ω_{i'j'})**)。
- **commit `7b7ea8ff`** ✅ **μ-bridge** `certainType_mu_conj_bridge`: **`δ_j • μ_ij̄ = δ_{j'} •
  μ_{i'j'}`** = (4.3.b) `sigma_chiColumn_eq_certainType` に `mapRingEquiv conj` 適用
  (左=`sigma_chiColumn_conj`+4.3.b再適用、右=`ClassFunction.mapRingEquiv_zsmul` [sign∈ℤ])。

**🔑 W-整合の罠 (session 36 で 3 回踏んだ; 再調査不要)**: `(ticVdiff h).W` vs `h.tic.W`、
`toTICyclicHypothesis.W` vs `sdiffTICyclicHypothesis.W` は defeq だが非 syntactic → `rw`/`simp only`
の pattern matching が黙って失敗 (「did not find pattern」/「unused simp arg」)。**回避 = term-mode
`congrArg`+`exact`(defeq) か、goal 側を `← lemma` で書き換えてから `exact`**(sigma_chiColumn_conj が
好例: goal は sdiff ascription で chiColumn_conj に一致 → `rw [← chiColumn_conj]` → `exact
sigma_mapRingEquiv_comm`)。**explicit `[Fintype toTICyclic.W]` 等の binder は canonical (W1⊔W2 由来)
と diamond → 宣言せず `[Fintype ↥(W1⊔W2)]` のみ供給**。hom 逆 `f⁻¹ a` は defeq `(f a)⁻¹` だが
`MonoidHom.inv_apply` simp が発火しないことあり → `congrArg`+引数等式で defeq 閉じ。

### ▶▶ 次 = (4.9)(a) 残り → nonzero → IsCoherent (session 37 以降; **Opus 継続**)
1. **`μ_ij̄ = μ_{i'j'}`** (bridge から): `δ_j • μ_ij̄ = δ_{j'} • μ_{i'j'}` の両辺を `1` で評価 →
   μ_ij̄(1)=μ_ij(1)>0、μ_{i'j'}(1)>0 ゆえ δ_j δ_{j'}=1 ⟹ **δ_j=δ_{j'}** ⟹ μ_ij̄=μ_{i'j'}
   (「指標は別の指標の −1 倍になれない」; 次数正値 or inner)。
2. **`μ̄_j = μ_{j'}`**: μ_j=∑_i μ_ij ([[certainTypeDiffSupported]] の和構造) ⟹ μ̄_j=∑_i μ_ij̄=
   ∑_i μ_{i'j'}=μ_{j'} (i↦rowInv i は行の全単射)。
3. **`μ_{j'} ≠ μ_j`**: j'=χ₂⁻¹≠χ₂ (|W| 奇 ⟹ χ₂²≠1 ∨ χ₂=1; χ₂≠1 前提) ⟹ `chiRestrict_injective`
   で μ_{χ₂⁻¹}≠μ_{χ₂}。
4. **nonzero**: μ̄_k−μ_k≠0 ∈ Z[𝒯,A]。**Z[𝒯,L^#]=Z[𝒯,A]** は (4.7)(Supp μ_j⊆A∪{1})+次数零。
5. **IsCoherent packaging** (`S07.IsCoherent τ 𝒯 A`, 5 fields; session 35 ノート参照): extension map
   on Z[𝒯] + 等長 (`certainType_omega_sum_isometry` lift) + τ一致 (`certainType_diff_dade_sum_eq_of_degree`
   lift) + nonzero (step 4) + ZIrr codomain。**重い** (IntegralCharacterMap/zSpan/zSupportedSpan 機構)。
→ (4.9) → S08 case-B → (6.8)。**正本=本 session 36。(4.9)(a) μ-bridge DONE; 次 = step 1 (μ_ij̄=μ_{i'j'})。**

## 2026-06-12 (session 36 cont., /goal "Bレーン完遂"): ✅ (4.9)(a) 共役チェーン完結 — `μ̄_k ≠ μ_k`

session 36 から継続 (`/goal` で完遂モード)。(4.9)(a) の共役論法を **nonvanishing 入力 `μ̄_k ≠ μ_k` まで完結** (S06_CertainTypeConjugation, 全 axiom-clean):

- **commit `aa61a690`** `certainType_mu_conj_eq`: **`μ_ij̄ = μ_{i'j'}`** (per-element)。bridge を μ_{i'j'}
  と内積 → δ_j⟨μ_ij̄,μ_{i'j'}⟩=δ_{j'}≠0 → 既約同士の内積 0/1 ゆえ 1 → 一致。**🔑 罠: `inner_smul_left`
  は無印だと mathlib InnerProductSpace 版 (共役付き) に解決 → `ClassFunction.inner_smul_left` 明示必須**。
  zsmul→ℂsmul 変換は `← Int.cast_smul_eq_zsmul ℂ <sign> <classfn>` と **3 引数明示** (無印は stacking 暴走)。
- **commit `70312fb0`** `certainType_columnSum_conj`: **`μ̄_j = μ_{j'}`** (列和)。`mapRingEquivLinear`+`map_sum`
  で和分配、各項 `certainType_mu_conj_eq`、行 reindex `rowInvEquiv` (= `rowInv` involution
  `rowInv_rowInv`)。
- **commit `fb5a98a6`** capstone `μ̄_k ≠ μ_k`:
  - `column_inv_ne_self`: **χ₂⁻¹≠χ₂** (χ₂≠1)。char group `(W₂.subgroupOf W)→*ℂˣ` 奇数位数
    (`card_charGroup_W2`=|W₂|, `W_odd.of_dvd_nat (Subgroup.card_dvd_of_le le_sup_right)`) ⟹ 対合なし
    (χ₂²=1→orderOf∣2 ∧ odd→1; `Nat.dvd_prime Nat.prime_two`+`absurd (_▸_) (by decide)`)。
  - `certainType_columnSum_conj_ne`: **`μ̄_k≠μ_k`**。μ̄_k=μ_{χ₂⁻¹} (columnSum_conj) ⊥ μ_χ₂
    (`columnFamily_mu_sum_inner` if_neg) ⟹ ⟨μ̄_k,μ_k⟩=0≠w₁。

### ▶▶ 次 = `Z[𝒯,L^#]=Z[𝒯,A]` + **IsCoherent packaging** (本命の残り; 重い)

`S07.IsCoherent τ 𝒯 A` の 5 field 構成が S08 case-B への橋。手持ち材料:
- **field 3 (等長 on zSpan 𝒯)** ← `certainType_omega_sum_isometry` (生成元 Gram 行列)を zSpan へ lift。
- **field 4 (τ一致 on zSupportedSpan 𝒯 A)** ← `certainType_diff_dade_sum_eq_of_degree` を lift。
- **field 1 (nonzero)** ← **`certainType_columnSum_conj_ne` (μ̄_k≠μ_k) = 本 session で完成**; μ̄_k−μ_k∈Z[𝒯,A]
  の supportedness は (4.7)(Supp μ_j⊆A∪{1}) + 次数零。
- **field 2 (extension : IntegralCharacterMap)** + **field 5 (ZIrr codomain)** = extension map 構成。
要調査: `zSpan`/`zSupportedSpan`/`IntegralCharacterMap` の API (S07_Coherence)、IsCoherent 構成 helper の
有無。**第一手 = S07 の zSpan/zSupportedSpan/IntegralCharacterMap を Read 通読**してから extension map を
`Basis.constr` 級で構成 (μ_j ↦ δ_k ∑_i ω_ij^σ) → 5 field を埋める。
**正本=本 session 36 cont.。(4.9)(a) 共役完結; 次 = IsCoherent packaging (S07 機構 Read から)。**

## 2026-06-12 (session 37, /loop): ✅ IsCoherent packaging — extension map ν + fields 2/3/5 (of 5)

新 leaf **`S06_CertainTypeCoherence.lean`** (3 commits, 全 axiom-clean, full build 3794)。Peterfalvi
(4.9)(b) の coherent extension `ν : CF(↥L) → CF(G)` を構成し、`S07.IsCoherent τ 𝒯 A` の 5 field の
うち **field 2 (extension)・field 3 (isometry)・field 5 (ZIrr)** を landed。

### 確定した型・構成 (再調査不要)

- **(4.9) の 𝒯 = 列和の集合** (per-element ではない): `𝒯 = {μ_j | 0<j<w₂, μ_j(1)=μ_k(1)}`。
  repo: `certainTypeSet h k := {f | ∃ χ₂≠1, columnSum h χ₂ (1) = columnSum h k (1) ∧ f = columnSum h χ₂}`。
  `columnSum h χ₂ := ∑ i, (h.columnFamily χ₂).mu i` (= μ_j)。
- **extension map** `certainTypeExtension h : S07.IntegralCharacterMap ↥L G` = `Irr(↥L)` 基底上
  `μ_ij ↦ δ_j ω_ij^σ` (他 irr ↦ 0)、`(S05.irreducibleCharacterBasis).constr ℂ ... |>.restrictScalars ℤ`。
  基底 rule の well-defined は **`columnFamily_mu_injective`** (大域 `(χ₂,i)↦μ_ij` 単射) が核。
  eval: `certainTypeExtension_mu` (`ν μ_ij = δ_j ω_ij^σ`)、`certainTypeExtension_columnSum`
  (`ν μ_j = δ_j ∑_i ω_ij^σ`)。**罠: `open scoped Classical in` は docstring の前**。
- **field 5 (ZIrr)**: `certainTypeOmegaSigma_mem_ZIrr` (= `sigma_mem_ZIrr` + omega の `.mem_ZIrr`) →
  `certainTypeExtension_mem_ZIrr` (span_induction、ZIrr は ℤ-submodule)。
- **field 3 (isometry)**: generator `certainTypeExtension_columnSum_inner` (`⟨ν μ_j,ν μ_l⟩=⟨μ_j,μ_l⟩`,
  **無条件** — 対角で δ_j²=1、非対角は Gram=0 が符号吸収; `certainType_omega_sum_isometry` +
  `columnFamily_mu_sum_inner` + zsmul→ℂsmul は `← Int.cast_smul_eq_zsmul ℂ sign cf`) → full
  `certainTypeExtension_inner_eq` (**`Submodule.span_induction₂`** 一発、8 case = mem_mem/zero_*/add_*/smul_*;
  双線型は `ClassFunction.inner_{add,smul}_{left,right}`、smul は ℂ-cast 変換)。

### 🔑 残り field 4 (agreement) + field 1 (nonzero) + capstone — τ 型が確定 (再調査不要)

**IsCoherent.τ = `S07.dadeIntegralCharacterMap h.dade0 h.tau : IntegralCharacterMap ↥L G`** (大域版)。
`h.tau.toDadeMap` は bundled `SupportedClassFunctions A₀ L → CF(G)` で **IntegralCharacterMap ではない**;
`dadeIntegralCharacterMap` が `LinearMap.exists_extend` で大域化したもの (S07:5233)。
- **`dadeIntegralCharacterMap_apply_of_support`** (S07:5243): `supp φ ⊆ supportInSubgroup A₀ L ⟹
  dadeICM φ = h.dade0.dadeMap ⟨φ, _⟩` ← これで `certainType_diff_dade_sum_eq` (toDadeMap 版) に接続。
- **A vs A₀ の罠**: `h.dade0 : S04.Hypothesis G A₀ L`, `A₀ = A ∪ V^L` (Hypothesis46.dade0; tic.V 由来)。
  (4.9) の `Z[𝒯,A]` は **certain subgroup A** だが A ⊆ A₀ ゆえ supp⊆A → supp⊆A₀ で Dade 適用可。
  IsCoherent.A は `supportInSubgroup A L` を採る見込み (S09 の pattern; 要最終確認)。

**field 4 plan** (`extends_on_supported : ∀ φ∈zSupportedSpan 𝒯 A, ν φ = τ φ`):
1. **「Z[𝒯,A] は μ_j−μ_k で生成」**: φ∈zSpan 𝒯 ∧ supp⊆A ⟹ φ∈span ℤ {μ_j−μ_k}。証明 = φ=∑c_μ μ
   (mem_span)、supp⊆A⟹φ(1)=0 (1∉A)、全 μ_j 同次数 d ⟹ d·∑c_μ=0 ⟹ ∑c_μ=0 ⟹ φ=∑c_μ(μ_j−μ_k)。
   [Finsupp/mem_span_finset 要; これが残 hard sub-lemma]
2. **generator 一致** `ν(μ_j−μ_k) = τ(μ_j−μ_k)`: τ側 = `certainType_diff_dade_sum_eq` (要 δ_j=δ_k =
   (4.8) sign-eq、μ_j,μ_k∈𝒯 で同次数ゆえ成立) で `δ_j ∑(ω_ij^σ−ω_ik^σ)`; ν側 = `ν μ_j − ν μ_k =
   δ_j ∑ω_ij^σ − δ_k ∑ω_ik^σ`; δ_j=δ_k で一致。**`certainTypeDiffSupported` の underlying = μ_ij−μ_ik**
   なので `∑_i certainTypeDiffSupported = μ_j − μ_k = columnSum χ₂ − columnSum χ₂'` の bundling 接続が要。
3. **span へ拡張**: `S07.eq_on_zSpan_of_eq_on` (ℤ-linear 2写像が生成集合一致→span一致)。

**field 1 (nonzero)**: witness `μ̄_k − μ_k = columnSum k⁻¹ − columnSum k`。≠0 = `certainType_columnSum_conj_ne`
(済)。∈ zSupportedSpan 𝒯 A: 両端 ∈ 𝒯 (μ̄_k=μ_{k'}, k'=k⁻¹≠k、`certainType_columnSum_conj`+`column_inv_ne_self`、
同次数 = 複素共役は次数保存) ∧ supp⊆A ((4.7) `induce_chiRestrict_apply_eq_zero_of_not_mem_union` で
supp μ_j⊆A∪{1}、差は1で消える)。

**capstone**: `certainType_isCoherent : S07.IsCoherent (dadeIntegralCharacterMap h.dade0 h.tau)
(certainTypeSet h k) (supportInSubgroup A L)` を 5 field 組立 (要 k≠1)。→ S08 case-B。
**正本=本 session 37。次 = field 4 の sub-lemma 1「Z[𝒯,A] 生成」から (S06_CertainTypeCoherence に追記)。**

## 2026-06-12 (session 37 cont., /loop): ✅ field 4 core — generator τ-agreement + infra

(S06_CertainTypeCoherence, +4 commits, axiom-clean, build 3601)。field 4 (extends_on_supported)
の数学的核心を landed:

- **certainTypeSet 次数条件を `∑_i μ_ij(1)` 形に変更** (degree bridge `forall_columnFamily_mu_apply_one_eq_of_sum_eq`
  の hyp 形に一致; fields 3/5 は次数 component を `_` で無視ゆえ無傷)。
- **columnSum_apply_one**: `μ_j(1) = ∑_i μ_ij(1)` (eval AddMonoidHom `AddMonoidHom.mk' (fun φ => φ 1) (fun _ _ => rfl)` + map_sum)。
- **certainType_columnSign_eq**: 列次数等 ⟹ `δ_j = δ_k` ((4.8) step1 列版、`certainType_sign_eq_of_degree_eq` を row 0 で)。
- **columnDiff_support_subset**: `Supp(μ_j−μ_k) ⊆ supportInSubgroup A L` (両 μ vanish off A∪{1}、差は1で消える)。
- **✅✅ certainTypeExtension_columnDiff_eq_dade** (field 4 核心): `ν(μ_j−μ_k) = τ(μ_j−μ_k)`、両辺 = `δ_j ∑(ω_ij^σ−ω_ik^σ)`。
  RHS = `dadeIntegralCharacterMap_apply_of_support` (supp⊆A⊆A₀、`supportInSubgroup_mono Set.subset_union_left`)
  → `S04.IsDadeMap.unique (k:=ℂ) h.dade0.isDadeMap_dadeMap h.tau.toDadeIsometryData.isDadeMap`
  (h.dade0.dadeMap = h.tau.toDadeMap) → `certainType_diff_dade_sum_eq h hχeq hχ₂ hχ₂' hdi`
  (bundled `⟨μ_j−μ_k,_⟩ = ∑ certainTypeDiffSupported` を `congr 1; Subtype.ext hval`、
  `hval`= `AddSubmonoidClass.coe_finset_sum` + columnSum_def + `rfl`)。χ₂=χ₂' は `sub_self;map_zero` で別処理。
  LHS = `map_sub` + certainTypeExtension_columnSum×2 + `← certainType_columnSign_eq` + `←smul_sub` + `←Finset.sum_sub_distrib`。

### ▶▶ 次 = field 4 仕上げ → field 1 → capstone (session 38; **Opus 継続**)

1. **「Z[𝒯,A] は μ_j−μ_k で生成」** (残 Finsupp lemma): `φ ∈ zSupportedSpan 𝒯 (supportInSubgroup A L) →
   φ ∈ span ℤ ((·−columnSum k)''𝒯)`。証明 = `mem_span_set` で `c : CF→₀ℤ` (supp⊆𝒯) →
   各 m∈𝒯 は m(1)=d (columnSum_apply_one + 𝒯 次数条件、d=μ_k(1)≠0) → **φ(1)=0** (supp⊆supportInSubgroup A L,
   **1∉A** = `h.dade0.ne_one` 経由 [a∈A₀→a≠1, A⊆A₀]) → ∑c(m)=0 → φ=∑c(m)(m−μ_k)∈span T。
   `Finsupp.sum` の (1) 評価が要 (`columnSum_apply_one` の eval-hom 流用)。
2. **field 4 = `certainTypeExtension_eq_dade_of_mem_zSupportedSpan`**: `S07.eq_on_zSpan_of_eq_on`
   (T=差集合; T 上一致 = generator agreement、span 帰属 = 1.の lemma)。
3. **field 1 (nonzero)**: witness `columnSum k⁻¹ − columnSum k`。∈ zSupportedSpan: 両端∈𝒯
   (μ̄_k=μ_{k⁻¹}=`certainType_columnSum_conj`、k⁻¹≠1[k≠1]、次数等 [複素共役は次数保存: μ_{k⁻¹}(1)=conj(μ_k(1))=μ_k(1) ∵ 指標次数は実]、
   supp⊆supportInSubgroup A L = `columnDiff_support_subset h (k⁻¹≠1) (k≠1) (deg)`)。≠0 = `certainType_columnSum_conj_ne`。
   ⚠ 次数等の「∑μ_{i,k⁻¹}(1) = ∑μ_{i,k}(1)」: 複素共役の次数保存を sum 形で要証明。
4. **capstone** `certainType_isCoherent : S07.IsCoherent (dadeIntegralCharacterMap h.dade0 h.tau)
   (certainTypeSet h k) (supportInSubgroup A L)` (要 k≠1)、5 field 組立。→ S08 case-B。
**正本=本 session 37 cont.。field 4 核心 DONE; 次 = generated-by-differences Finsupp lemma。**

## 2026-06-13 (session 37 cont.², /loop): 🎉🎉🎉 Peterfalvi (4.9)(b) COMPLETE — certain-type coherence

**`certainType_isCoherent`** (S06_CertainTypeCoherence, capstone `187b5517`, axiom-clean, full build
3794 + AxiomsCheck OK)。**Theorem (4.9)(b) 完全形式化** — Dade 写像 `τ = dadeIntegralCharacterMap
h.dade0 h.tau` は certain-type 集合 `𝒯` 上 coherent:
`S07.IsCoherent τ (certainTypeSet h k) (S04.supportInSubgroup A L)` (要 `k ≠ 1`)、5 field 全証明:

- **field 2 (extension)** = `certainTypeExtension h` (μ_ij ↦ δ_j ω_ij^σ)。
- **field 3 (isometry)** = `certainTypeExtension_inner_eq` (span_induction₂)。
- **field 4 (τ-agree)** = `certainTypeExtension_eq_dade_of_mem_zSupportedSpan`:
  generator `certainTypeExtension_columnDiff_eq_dade` (核心、`IsDadeMap.unique` + (4.8) summed) +
  生成 `mem_span_columnDiff_of_mem_zSupportedSpan` (sup-decomp `Z[𝒯] ≤ D ⊔ ℤ·μ_k`、1∉A=`h.dade0.ne_one`、
  μ_k(1)≠0=`irreducibleCharacter_apply_one_eq_pos_natCast`) + `eq_on_zSpan_of_eq_on`。
- **field 5 (ZIrr)** = `certainTypeExtension_mem_ZIrr` (span_induction + `sigma_mem_ZIrr`)。
- **field 1 (nonzero)** = `certainType_nonzero`: μ̄_k−μ_k (μ̄_k=μ_{k⁻¹}∈𝒯、`columnSum_inv_apply_one`
  [複素共役は実次数固定: `map_natCast`]、≠0=`certainType_columnSum_conj_ne`)。

session 37 全体 = **10 commits** (foundation→𝒯+ZIrr→isometry→support infra→field4 infra→generator
agreement→field4→nonzero+capstone + notes×2)。**§5 (3.x) + §6 (4.1)-(4.9) 全 COMPLETE。**

### ▶▶ 次 = case-B 配線 or (4.10) (session 38 で RECON 要)

**(4.9) は S08 case-B (`sibleySetup_is_coherent` の CertainType branch / S08 sole sorry) の入力。**
残る選択肢:
1. **S08 case-B 配線** (本命): certain-type `Hypothesis46` ↔ Sibley setup の接続を精査し、
   `certainType_isCoherent` を X-chain coherence に注入。**大 glue** (S08 X-nonempty sorry は
   Frobenius/CertainType case split + per-step data + 合成 ν の構築要; (4.9) は CertainType 側の
   coherence 供給のみ)。RECON 必須: S08_CoherenceTheorems:59 sorry の構造、何が Hypothesis46 を
   構成するか、certainType_isCoherent をどの interface に渡すか。
2. **(4.10)** (`(δ_j μ_ij−δ_j μ_0j−μ_i0+μ_00)^τ = ω_ij^σ−ω_0j^σ−ω_i0^σ+ω_00^σ`): (4.9) 非依存の
   補助恒等式。(4.8) generator + grid 拡張で書けそうだが case-B critical path 外の可能性。
**推奨第一手 = S08 case-B sorry (S08_CoherenceTheorems:46-59) を Read して配線可能性を RECON**。
**正本=本 session 37 cont.²。(4.9)(b) COMPLETE; 次 = case-B 配線 RECON。**

## 2026-06-13 (session 37 cont.³, /loop): S08 case-B 配線 RECON 結論 + 次 = (4.10)

**RECON 結論: S08 case-B 配線は単発 plug-in でなく §8 (6.8) 大 assembly** (正本=notes/peterfalvi/s08_6_8_assembly_plan.md, 96KB, T0-T11 DAG)。
- `sibleySetup_is_coherent` (S08_CoherenceTheorems:46) X-nonempty branch sorry (:59) = Frobenius/CertainType
  case split (`hyp.cases : IsFrobeniusGroup ∨ ∃ cert:CertainTypeHypothesis…`) で X=S−S(Z) coherence を
  Y=S(H') coherence と §7 engine `coherentUnion_of_glued` で gluing。
- **Sibley case-B (`cases.inr`) は `cert : S06.CertainTypeHypothesis (sharpImage H) L` + (w₂ prime/W₂⊆[H,H]/
  Coprime|H||W1|/cert.dade=dade/cert.K=H/cert.W1=W1) を供給 — `Hypothesis46` ではない。** ⟹ (4.9)
  `certainType_isCoherent` を使うには **Hypothesis46-from-Sibley bridge** (tic/dade0/tau/subH/A_covers の
  構成、(3.1)-for-W + (4.6.c/d) 確立) が要、substantial。
- Frobenius path は概ね構築済 (B engine surgery 完, `Xset_commutator_isCoherent…_of_frobenius` +
  `peterfalvi_66_coherence_of_X_from_dade`)。c2 path は open blocker 多数 (T6 inertia discharge / Y-family
  construction / c2 inertia / T10 case-B gluing)。**T7 c2 X-char は (4.5)✓ 使用。**
- ⟹ **case-B は §8 program の大仕事で Lane B 単独 cold engage は overlap/risk。(4.9) は necessary input
  (供給済) だが gluing machinery が bulk。** 戦略判断 (case-B 大 assembly に commit するか) はユーザー/合流調整向き。

**次 = (4.10)** (§6 最終結果、章完結): `(δ_j μ_ij−δ_j μ_0j−μ_i0+μ_00)^τ = ω_ij^σ−ω_0j^σ−ω_i0^σ+ω_00^σ`。
原文「(4.8) と同様」= 同じ V-vanishing+trichotomy 論法 (`sigmaCoeff_trichotomy` 消費)。(4.3.b)
`σ(ω_ij)=δ_j μ_ij` + (4.8) step-4 engine (`certainType_diff_dade_apply_eq_of_mem_V` 等) を 4-corner
combination に適用。(4.8) conclusion-3 (`certainType_diff_dade_eq`) の隣接 row+column 版。
in-lane・(4.8)/(4.9) infra 流用可・§6 完結。**正本=本 session 37 cont.³。次 = (4.10)。**

## 2026-06-13 (session 37 cont.⁴, /loop): (4.10) code-ready plan (ユーザー裁可: (4.10) で §6 完結)

ユーザーが「(4.10) で §6 完結」を選択。RECON 完了、code-ready 計画:

**(4.10) statement**: `(δ_j μ_ij − δ_j μ_0j − μ_i0 + μ_00)^τ = ω_ij^σ − ω_0j^σ − ω_i0^σ + ω_00^σ`
(0≤i<w₁, 0≤j<w₂; τ=h.tau.toDadeMap, σ=certainTypeOmegaSigma)。

**🔑 確定した reduction (再調査不要)**:
- **W-side 4-corner α = alphaCF**: `alphaCF_eq_omega_combination` (S05_TICyclic:659) =
  `(ticVdiff h).alphaCF χ₁ χ₂ = ω(1) − ω(χ₁∘wFst) − ω(χ₂∘wSnd) + ω((χ₁∘wFst)·(χ₂∘wSnd))`
  = 1_W − ω_i0 − ω_0j + ω_ij。**Supp α ⊂ V** = `alphaCF_mem_supportedSubmodule` (S05_TICyclic:511, (3.4))。
- **RHS = σ_G(α)**: `certainTypeOmegaSigma = (ticVdiff h).sigma rfl app (omega …)`、4-corner は
  σ の線形性 + `alphaCF_eq_omega_combination` で `(ticVdiff h).sigma rfl app (alphaCF)`。
- **🔑 `sigma_eq_tau` (S05_SigmaIsometry:1098)**: `hyp.sigma hVeq app (α:CF) = app.tau.toDadeMap α`
  for `α : SupportedOnV ℂ hyp` ⟹ **σ_G(alphaCF) = (ticVdiff h).tau.toDadeMap (alphaCF-on-V)**。
- **LHS = h.tau.toDadeMap (Ind_W^L alphaCF)**: β = δ_j μ_ij−δ_j μ_0j−μ_i0+μ_00 = Ind_W^L alphaCF。
  via (1.4) image `columnFamily_spec`/`isometryDifferenceImage_induceZ` (`Ind(ω_ij−ω_0j)=δ_j(μ_ij−μ_0j)`)
  + col-0 (χ₂=1, δ_0=1 by (4.4))。

**⟹ (4.10) = Dade-induction compatibility `h.tau.toDadeMap (Ind_W^L α) = (ticVdiff h).tau.toDadeMap α`**
(α ∈ CF(W,V))。両辺 class function on G、V-vanishing 論法で証明 ((4.8) step-4
`certainType_diff_dade_apply_eq_of_mem_V` の pattern):
- v∈V: 両辺 = value (h.tau: `tau_toDadeMap_apply_of_mem` on A₀⊇V^L; ticVdiff.tau: V-value)。
- g∉V^G: 両辺 vanish (h.tau: `map_eq_zero_of_not_mem_dadeSupport`, β supp⊂V^L⟹dade image supp⊂V^G;
  ticVdiff.tau(α): α supp⊂V⟹ image supp⊂V^G)。
- assembly: class-function invariance で V→V^G、それ以外 0。

**piece 順**: (a) `β = Ind_W^L alphaCF` (1.4 image, col-0 δ_0=1) → (b) Supp β⊂A₀ (supported β 構成) →
(c) value-on-V (mirror 4.8 step-4, `sigma_eq_tau` for RHS) → (d) off-V^G vanishing 両辺 → (e) assembly
(`ClassFunction.ext` + V^G class-fn 論法)。**~3-5 commits, §4 Dade-support 機構の deep dive だが trichotomy 不要**。
**正本=本 session 37 cont.⁴。次 = (4.10) piece (a) から coding。**

## 2026-06-13 (session 37 cont.⁵, /loop): (4.10) piece (a) landed; piece (b1) STOP — W-coord `1` 罠

✅ **piece (a) `fourcorner_signedDiff_eq_induce`** landed (`fa5a578e`, S06_CertainTypeFourCorner, axiom-clean,
full build 3795): `δ_j(μ_ij−μ_0j) − δ_0(μ_i0−μ_00) = Ind_W^L(sdiff 4-corner)` via columnFamily_spec +
`h.isometryDifferenceImage_induceZ` (← **Hypothesis method, dot 修飾必須**) + induceLinear/map_sub
(induce_sub 無)。

🛑 **piece (b1) `chiColumn 4-corner = alphaCF` STOP (~8 試行、真の W-coord 罠)**: 目標
`(chiColumn χ₂ i − chiColumn χ₂ 0 − (chiColumn 1 i − chiColumn 1 0)) = sdiff.alphaCF (w1CharEquiv i) χ₂`。
pointwise (alphaCF_apply+omega_apply+omegaProdChar+ring) も omega-combination (abel) も**同じ箇所で詰む**:
**`(1 : M →* ℂˣ)(x) = 1` の simp が発火しない** (`MonoidHom.one_apply` も `MonoidHom.one_comp` も unused、
full simp も不可)。**根本原因**: chiColumn の χ₂=1 列 / w1CharEquiv 0=1 行で出る `1` の domain は
`h.W2.subgroupOf (h.W1⊔h.W2)` 系だが、適用先 arg は `sdiff.W2sub` 系 — **defeq だが非 syntactic** ゆえ
one_apply/one_comp の単一化が失敗 (sdiff vs h の W-coord 罠、memory 既出)。goal は `↑(1(wSnd w))`/
`↑(1(wFst w))` が atom 残留で ring 不可 (これらが 1 になれば閉じる: 両辺 (1−a)(1−b))。

### ▶▶ 次 = (4.10) piece (b) 別ルート (session 38; W-coord 回避)
1. **`1`型整合の workaround**: (a) chiColumn 1-列の `1` を `change`/`convert` で sdiff 型に揃える、
   (b) `omegaProdChar_one_left/right/one` を CF レベルで先に適用し pointwise の `(1)(x)` を回避
   (omega(1) は line 666 (S05_TICyclic) パターンで one_apply 可)、(c) chiColumn の coe を ascription。
2. **alphaCF 経由を捨てる別 support 証明**: sdiff 4-corner が sdiff.V 上 support を直接
   (W₁∪W₂ で消失、`alphaCF_eq_zero_of_mem_W1/W2_subgroupOf` 流の omega 値計算)。
3. piece (b) 完了後: (c) value-on-V (4.8 step-4 ミラー) → (d) off-V^G vanishing → (e) assembly。
**正本=本 session 37 cont.⁵。(4.10) piece (a) DONE; piece (b1) は W-coord `1` 罠で STOP、別ルート要。**

## 2026-06-13 (session 37 cont.⁶, /loop): (4.10) — W-coord `1` 解決、chiColumn_apply_eq landed; alphaCF-match は coercion 残留 → route 2 へ

✅ **W-coord `1` 罠 解決済**: `MonoidHom.one_apply` が `(1: _→*ℂˣ)(x)` で発火しないのは sdiff/h の `1`-domain
非 syntactic ゆえ。**fix = `change` で omegaProdChar を defeq 展開 + explicit-domain `hone : (1:(h.W2.subgroupOf
(h.W1⊔h.W2))→*ℂˣ)(wSnd w)=1 := MonoidHom.one_apply _`**。
✅ **`chiColumn_apply_eq` landed** (`f83d9bc4`, build 3598, axiom-clean): `ω_ij(w)=↑((w1Eq i)(wFst w))·↑(χ₂(wSnd w))`
(chiColumn unfold + omega_apply + `change`(omegaProdChar 展開) + Units.val_mul)。**(4.10) support の value 道具**。

🛑 **`chiColumn_fourcorner_eq_alphaCF` (piece b1) は coercion 残留で STOP** (~14 試行): pointwise で
hone1/hone2+chiColumn_apply_eq 適用後、goal は **表示上 `1−X+XY−Y = 1−X+XY−Y` (完全一致表示) なのに
ring/rfl/push_cast/norm_cast/set 全滅**。原因 = LHS の atom (chiColumn_apply_eq 由来) と RHS の atom
(alphaCF_apply 由来) が **表示同一だが別 term** (coercion instance か elaboration 差)。**2 lemma の coercion 不整合**。

### ▶▶ 次 = (4.10) piece (b) **route 2 (alphaCF 回避)** (session 38)
alphaCF-match を捨て、**`Supp(sdiff 4-corner) ⊂ sdiff.V` を直接** (vanish on W₁∪W₂, **全て chiColumn_apply_eq
由来ゆえ coercion 不整合なし**):
- w∈W₂ (`wFst w = 1` by `wFst_eq_one_of_mem_W2`): 各 chiColumn = ↑(1)·↑(χ(wSnd w))=↑(χ(wSnd w))、4-corner=0。
- w∈W₁ (`wSnd w = 1` by `wSnd_eq_one_of_mem_W1`): 対称、4-corner=0。
- `(w1Eq i)(1)=1`/`χ₂(1)=1` は `map_one`。`supportedSubmodule` 帰属で Supp⊂sdiff.V。
- 必要なら fourcorner_signedDiff_eq_induce(piece a)で `signedDiff 4-corner = Ind(sdiff 4-corner)` →
  `Supp(Ind) ⊂ (sdiff.V)^L ⊂ A₀` (induce support + sdiff.V⊂tic.V)。
- **代替 (もし coercion を直したい)**: pp.all で LHS/RHS atom 差を特定 → chiColumn_apply_eq の coercion を
  alphaCF_apply と一致させる。だが route 2 が安全。
→ piece (c) value-on-V (4.8 step-4 ミラー) → (d) off-V^G vanishing → (e) assembly。
**正本=本 session 37 cont.⁶。chiColumn_apply_eq DONE; alphaCF-match は coercion で STOP、route 2 推奨。**

## 2026-06-13 (session 38, /loop「難所回避せず」): (4.10) piece (b) COMPLETE (route 2 + 強化 + carrier)

**3 commits landed (leaf build 3598 green, axiom-clean, pure leaf=誰も import せず・root 在)**:
1. `6e807abb` route 2 弱版: four-corner ∈ CF(W, **W−W₂**) via `omegaColumnDiff` 差 + `Submodule.sub_mem`
   (chiColumn=omega∘omegaProdChar ゆえ omegaColumnDiff_coe へ rfl; coercion 罠なし)。
2. `56f82435` **強化版** (弱版を置換): four-corner ∈ CF(W, **W−(W₁∪W₂)**) = `SupportedOnV ℂ toTICyclicHypothesis`。
   弱版 (W−W₂) では下流不足 (Ind_W^L β の Supp⊂V^L⊂A₀ は A₀ の V=tic.V=W−(W₁∪W₂) 小さい方を要求)。
   four-corner は W₁ でも消える (列差が打ち消す: chiColumn_apply_of_mem_W1 は両列同一 atom)。**新 helper
   `chiColumn_apply_of_mem_W2`** (W1 版の対) + `alphaCF_mem_supportedSubmodule` ミラー (W₁∧W₂ 両 vanish、
   各 branch は 4×chiColumn 値 rewrite 後 `ring`、全 atom 同 lemma family ゆえ coercion 衝突なし)。
3. `91c9b52e` **carrier `chiFourCornerOnV`** : four-corner を `SupportedOnV ℂ toTICyclicHypothesis` subtype
   element 化 (Ind_W^L が食う pre-induce handle) + `chiFourCornerOnV_coe` (coe=four-corner, rfl)。

### 🔑 defeq 教訓 (再調査不要)
- **`sdiffTICyclicHypothesis.W` と `toTICyclicHypothesis.W` は両方 `W₁⊔W₂` (toTICyclicHypothesisOfV の
  `.W:=h.W1⊔h.W2`、V のみ違う) — defeq だが非 syntactic**。chiColumn は sdiff.W 上だが carrier は toTIC.W 上。
- **SupportedOnV element の coe lemma は「自分の hypothesis の `.W`」へ ascribe せよ** (= toTIC.W、coe の自然
  出力)。sdiff.W↔toTIC.W defeq は **Eq の中で rfl が処理**、coercion-insertion では処理されない
  (single/cross ascription `(x:SupportedOnV toTIC):CF sdiff.W` は coe を起動できず失敗)。`omegaColumnDiff_coe`
  (S06_CertainTypeCharacters:207) が double-ascription 同 hypothesis の手本。
- chiColumn_apply_of_mem_W1/W2 と chiFourCornerOnV は **S06 namespace で h:Hypothesis46 を明示引数に取る**
  ⟹ dot 記法 `h.chiColumn_apply_of_mem_W1` 不可、`chiColumn_apply_of_mem_W1 h …` と書く (chiColumn /
  omegaColumnDiff は Hypothesis namespace ゆえ dot 可、と対照的)。

### ▶▶ 次 = (4.10) piece (c)(d)(e) = Dade-transitivity core (session 39)
**RECON 完了・全 construction map 判明**。(4.10) は **`h.tau.toDadeMap (Ind_W^L α) = certainTypeOmegaSigma 四隅`**
(α=four-corner)。(4.8) と違い **trichotomy 不要** — 単一 V-supported α の Dade 写像両立 (V-agreement+off-V vanishing)。
ただし **(4.8) の overall 構造 (σ-coeff trichotomy) のコピーでは無い**: sigma_eq_tau 経由の新 construction。

**LHS 配管 (piece の前提)**: β=`signedDiff χ₂ i − signedDiff 1 i` = `Ind_W^L(four-corner)` (piece a
`fourcorner_signedDiff_eq_induce` 既landed)。β∈CF(L,A₀) を要す (h.tau が食う型 `SupportedClassFunctions ℂ A₀ L`、
A₀=`A∪{l·v·l⁻¹:v∈tic.V}`)。
- β = toTIC Dade 写像(chiFourCornerOnV) [via `toTICyclicHypothesis.tau_eq_induce` + `toTICyclicFullDadeApplication`
  既存 S06_CertainTypeCharacters:837]。⟹ β は `conjugatesOfSet(toTIC.V)` off で消失
  [`TICyclicHypothesis.map_eq_zero_of_not_mem_conjugatesOfSet_V` S05:120]。
- **bridge `conjugatesOfSet(toTIC.V) ⊂ A₀`**: toTIC.V (⊂L, =W−(W₁∪W₂)) の L-共役は A₀ の `{l·v·l⁻¹:v∈tic.V}`
  へ。L→G で v↦(v:G)∈tic.V を要す。**(4.8) conclusion-1 `certainType_diff_supp_subset_A0` (S06_CertainTypeIsometry:264-330)
  の line 303-330 が同 bridge logic (W元→A₀、`hvV:L.subtype(x·y)∈tic.V` 構成) — 流用/ミラー**。
  defeq 注意: sdiff.W=toTIC.W で induce 形が一致するはず。

**piece (c) value-on-V**: v∈tic.V で両辺=four-corner(v)。LHS=`tau_toDadeMap_apply_of_mem h _ hvA0` (S06_CertainTypeIsometry:356)
で β(⟨v,_⟩)、(4.3.c) `certainType_apply_eq_of_mem_V` で μ=δ·ω、δ_j²=1 (sign_eq) で χ₂列係数消去・δ_0=1 (4.4
`certainType_zero_column_anchor`) で 1列。RHS=`certainTypeOmegaSigma_apply_of_mem_V` (S06_CertainTypeIsometry:152)
で ω^σ(v)=ω(v)。両辺=ω_ij(v)−ω_0j(v)−ω_i0(v)+ω_00(v)。**(4.8) step-4 `certainType_diff_dade_apply_eq_of_mem_V`
(:372-410) が手本**。

**piece (d) off-V^G vanishing**: LHS=h.tau β off `h.dade.dadeSupport` で消失 [`map_eq_zero_of_not_mem_dadeSupport`
S06_DadeIsometryCertain:503]。RHS=σ 四隅 = `(ticVdiff h).sigma(G側 four-corner)` [σ 線形]、off conjugatesOfSet(tic.V)
で消失 [S05:120 の ticVdiff 版]。**RHS の G側 four-corner support (piece b の tic 版) が要る** — omegaProdCharTic
(tic.W 上) の四隅 ∈ SupportedOnV ticVdiff。bridge ticWEquivSdiffW で sdiff 版から transport か、または tic 側で再証明。

**piece (e) assembly**: 両辺 class fn on G、V^G off で消失 (d)、V で一致 (c)。V^G の元は V の元の共役、class-fn 不変性
で V-値に帰着、それ以外 0 ⟹ 等しい。**ready-made assembly lemma 無し (4.8 は trichotomy 使用) — 新規構築要**
(or sigma_eq_tau で RHS=Ind_W^G(G側 four-corner) 化し、両 Ind の transitivity を別に立てる)。

**sigma_eq_tau (S05_SigmaIsometry:1098)**: `hyp.sigma α = app.tau.toDadeMap α = Ind_W^G α` (tau_eq_induce)。
RHS 簡約に使用。**hard core ではない (機械的だが zoo の defeq friction 多)、~2-4 commits 見込み、FT 経路外**。
**正本=本 session 38。piece (b) COMPLETE; 次=piece (c) value-on-V から (LHS β∈CF(L,A₀) 配管が前提)。**

## 2026-06-13 (session 38 cont., /loop): (4.10) 教科書証明を精読 — skeleton 確定 + strengthen 根拠訂正

**📖 book proof 読了** (`references/peterfalvi/04.6_...mmd:97`)。正確な論法:
- α = ω_ij−ω_0j−ω_i0+ω_00 (W側), β = δ_jμ_ij−δ_jμ_0j−μ_i0+μ_00 (L側)。
- (4.3.b)+(4.4): **β = Ind_W^L α** [= piece a ✓].
- **(3.4): Supp(α) ⊂ V, ゆえ Supp(β) ⊂ V^L。ここ V = W−(W₁∪W₂)** [(3.4)=alphaCF の V、SMALLER]。
- **「x∈V で C_G(x)=W⊂L。τ の定義より β^τ(g) = β(g) (g∈V) / 0 (g∉V^G)」**。
- (4.3.c)+(3.2.c) で β^τ(g)=α^σ(g) ∀g。

**🔧 訂正 (session 38 本文の note は根拠が誤り)**: piece (b) strong 化 (W−(W₁∪W₂)) は**正しい** — ただし
理由は「A₀ の V」ではない (A₀ の tic.V=**W−W₂**=larger、line 51 確認済ゆえ weak でも A₀ 帰属は足りた)。
**正しい根拠 = book の (3.4) V = W−(W₁∪W₂) (smaller)** で「C_G(x)=W」が要る。strong 版 = book と一致、必要。

### 🎯 clean Lean skeleton (確定、session 39 で実装)
**RHS 簡約**: ω^σ 四隅 = σ(ω_ij)−σ(ω_0j)−σ(ω_i0)+σ(ω_00) [σ 線形] = `ticVdiff.sigma(α_G)` [α_G=G側四隅
∈SupportedOnV ticVdiff] = **`Ind_W^G(α_G)`** [`sigma_eq_tau` S05:1098 + `tau_eq_induce` S05_SignedTripleGrid:288]。
ticVdiff.sigma は (ticVdiff.V)^G=V^G off で消失 [`full_map_eq_zero_of_not_mem_conjugatesOfSet_V` S05:161]、V で α一致 [sigma_apply_of_mem_V]。

**LHS = h.tau.toDadeMap(β)**, β∈CF(L,A₀) 要 (h.tau の型)。三段:
- **(c) value-on-V**: g∈V で β^τ(g)=β(⟨g,_⟩) [`tau_toDadeMap_apply_of_mem` S06_CertainTypeIsometry:356,
  V⊆tic.V⊆A₀]=α(g) [(4.3.c) `certainType_apply_eq_of_mem_V` で μ=δω、δ_j²=1 (sign_eq)、δ_0=1 (4.4)]。
  (4.8 step-4 :372-410 が手本)。
- **(d) off-V^G vanishing of β^τ** [🔑 crux]: book は「Supp β⊂V^L + τ 定義」。Lean: β^τ(g)=0 for g∉V^G。
  h.tau の `map_eq_zero_of_not_mem_dadeSupport` (dadeSupport⊇A-conj ⊉ V^G ゆえ直接不可) では足りぬ。
  β supported on V^L + hCoset(a)={a} (a∈V で H(a)=1) ⟹ h.tau(β) supported on V^L⊆V^G。要 hCoset/H=1 論法 (intricate)。
- **(e) assembly**: β^τ, α^σ 両 class fn。ext g; g∈V^G なら共役 v∈V へ class-fn 還元 → β(v)=α(v)=α^σ(v);
  g∉V^G なら両 0。ready-made uniqueness 無し (`eq_sigma_of_apply_eq_on_V` S05:1518 は norm-1 限定、四隅は非 norm-1)。

**前提 = LHS packaging β∈CF(L,A₀)**: β=`signedDiff χ₂ i − signedDiff 1 i`、Supp⊆A₀。
最短 = β=`sdiffFullDadeIsometryData.toDadeMap(omegaColumnDiff χ₂ − omegaColumnDiff 1)` [via
`isometryDifferenceImage_eq_dade` S06_CertainTypeCharacters:362 + Dade 線形] → off conj(sdiff.V=W−W₂) 消失
[`full_map_eq_zero...V` sdiff] → **bridge `conjugatesOfSet(W−W₂ in L) ⊆ A₀`** (v∈W−W₂→(v:G)∈tic.V、
(4.8 concl-1 :303-330 の logic 流用; tic_W2=W2.map subtype, L.subtype inj)。
[別 route: toTIC carrier 経由で W−(W₁∪W₂)、こちらは smaller ゆえ bridge 自明だが induce defeq sdiff.W=toTIC.W 要]。
**次 = bridge lemma (self-contained 群論) から。crux=(d) off-V^G。~2-3 commits、FT 経路外。**

## 2026-06-13 (session 38 cont.², /loop): (4.10) L-side packaging COMPLETE + (d) crux 機構特定

**landed (2 commits, leaf 3598 green)**:
- `d396656b` bridge `coe_mem_A0_of_mem_conjugatesOfSet_toTICV`: conj_L(toTIC.V) → A₀ (純群論)。
- `3f0cf45d` `signedDiff_fourcorner_eq_toTICDade` (β = toTIC Dade(carrier), via piece a +
  `tau_eq_induce` + FullDadeIsometryData.toDadeMap = .toDadeIsometryData.toDadeMap abbrev defeq) +
  **`fourCornerDiffSupported : SupportedClassFunctions ℂ A₀ L`** (β∈CF(L,A₀); Supp⊆conj(toTIC.V)→A₀
  via `full_map_eq_zero_of_not_mem_conjugatesOfSet_V`)。

⟹ **(4.10) の代数前提すべて完成** (β=Indα / α∈CF(W,V)+carrier / β∈CF(L,A₀) / bridge / β=toTIC Dade)。

### 🔴 残 = (c)(d)(e) final assembly。crux = (d) off-V^G vanishing of β^τ
`β^τ = h.tau.toDadeMap(fourCornerDiffSupported) = h.dade0.dadeMap β` [S06_CertainTypeIsometry:922]。
`dadeValue β g`: g∈dadeSupport で base point a∈A の β(a)、off で 0 [S04 dadeMapCF:3564, dadeValue_eq /
dadeValue_of_not_mem_dadeSupport]。
**(d) `β^τ(g)=0` for g∉V^G** の機構 (book「C_G(x)=W⊂L」の Lean 化):
- g∉dadeSupport → 0 [自明]。
- g∈dadeSupport → g conj a·h (a∈A, h∈H(a))、β^τ(g)=β(a)。β(a)≠0 → a∈Supp β⊆conj_L(toTIC.V)⊆V^L。
- **🔑 H(a)=⊥ for a∈V^L**: S04 Hypothesis の `centralizer_eq_sup` (C_G(a)=H(a)⊔C_L(a)) + `centralizer_disjoint`
  (H(a)⊓C_L(a)=⊥) ⟹ **C_G(a)⊆L ならば H(a)=⊥**。
- H(a)=⊥ → hCoset(a)={a} → g conj a → g∈a^G⊆(V^L)^G=V^G。g∉V^G と矛盾。⟹ β(a)=0。

**🟡 残ギャップ = 「C_G(a)⊆L for a∈conj_L(toTIC.V)」(G-side centralizer)**。book=C_G(v)=W for v∈V。
Lean `centralizer_eq_sup` (S06_DadeIsometryCertain:195) は **C_L(x)=W₁⊔W₂ (L-side のみ)**。**G-side C_G(v)⊆L for
v∈tic.V/ticVdiff.V が必要 — tic (TICyclicHypothesis G) の TI 構造から導出可か要確認** (V_ti+cyclic+self-cent?
or 新 field/補題)。これが (4.10) 完成の最後の hard core。

### ▶ 次 (session 39): 
1. **「C_G(v)⊆L for v∈tic.V」availability 確認** (tic の TI-cyclic 公理から; なければ Hypothesis46 が
   この compatibility を field で持つか、dade0 経由で出るか精査)。
2. 出れば (d) を上記機構で構築 → (c) value-on-V [mirror 4.8 step-4 `certainType_diff_dade_apply_eq_of_mem_V`、
   β(v)=α(v) は toTIC Dade value on V or (4.3.c)+δ²+δ_0=1] → (e) `ClassFunction.ext` g∈V^G/∉ case split。
3. RHS=ticVdiff.sigma(α_G)=`Ind_W^G(α_G)` [sigma_eq_tau]、off V^G 消失は `full_map_eq_zero...V` (ticVdiff) で clean。
**hard core ×1 = (d) の C_G(v)⊆L gap。FT 経路外。正本=本 session 38 cont.²。**

## 2026-06-13 (session 38 cont.³, /loop): 🎉🎉🎉 (4.10) COMPLETE — §6 four-corner Dade identity DONE

**`fourCorner_dade_eq` landed sorry-free + axiom-clean (leaf build 3598)**:
`(δ_j μ_{ij} − δ_j μ_{0j} − μ_{i0} + μ_{00})^τ = ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ + ω_{00}^σ`.

### 全 piece chain (commits 6e807abb → 785bd1d3, S06_CertainTypeFourCorner.lean):
- **piece (a)** `fourcorner_signedDiff_eq_induce`: β = Ind_W^L α (既存; (1.4) image + (4.4)).
- **piece (b)** `chiColumn_fourcorner_mem_supportedSubmodule`: α ∈ CF(W, W−(W₁∪W₂)) [pointwise vanish
  on W₁ (column-diff cancels via chiColumn_apply_of_mem_W1) and W₂ (新 `chiColumn_apply_of_mem_W2`)]
  + carrier `chiFourCornerOnV` (SupportedOnV toTIC) + `chiFourCornerOnV_coe`.
- **L-side packaging**: `coe_mem_A0_of_mem_conjugatesOfSet_toTICV` (bridge conj_L(V)⊆A₀) +
  `signedDiff_fourcorner_eq_toTICDade` (β = toTIC Dade(carrier) via tau_eq_induce) +
  `fourCornerDiffSupported` (β ∈ CF(L,A₀), h.tau の入力).
- **crux (d)** `fourCornerDade_eq_zero_of_not_mem_conjugatesV` (off-V^G vanishing, book の hand-wave 部):
  `centralizer_le_L_of_mem_ticVdiffV` (C_G(v)⊆L from IsTISubset V_ti — 鍵 unblock) +
  `H_eq_bot_of_centralizer_le` (S04 一般: C_G(a)⊆L ⟹ H(a)=⊥ via centralizer_eq_sup/disjoint) +
  `coe_mem_ticVdiffV_of_mem_toTICV` + `centralizer_le_L_of_mem_conj_toTICV` (共役閉包) →
  dadeValue base-point case analysis (β supp⊆V^L → H(a)=⊥ → h=1 → g conj a ∈ V^G).
- **G-side support** `omegaTic_fourcorner_mem_supportedSubmodule`: α_G ∈ SupportedOnV ticVdiff
  (piece b を bridge omegaProdCharTic_apply で transport).
- **crux (c)** `fourCornerDade_apply_eq_of_mem_V`: V 上一致 (両辺=sdiff-four-corner(bridge v); route B
  = β=σ_L(α) ゆえ δ²/δ₀ sign 不要; mirror 4.8 step-4).
- **capstone** `fourCorner_dade_eq`: ClassFunction.ext g; g∈V^G→conj_eq+( c); g∉V^G→(d)+RHS=σ(α_G)=τ(γ)
  vanish (map_sub + sigma_eq_tau + full_map_eq_zero).

### 🔑 再調査不要の知見:
- A₀ の V = tic.V = **W−W₂** (larger); book の (3.4)/value-vanishing の V = **W−(W₁∪W₂)** (smaller,
  ticVdiff.V/toTIC.V)。strong support (smaller) が正しい (C_G(v)=W⊂L が要)。
- **C_G(v)⊆L for v∈V は IsTISubset から直接** (c centralizes v → c·v·c⁻¹=v∈V → c∈W⊆L)。
- SupportedOnV coe lemma は自分の hypothesis の .W へ ascribe (defeq は Eq 内 rfl)。
- chiColumn_apply_of_mem_W1/W2, chiFourCornerOnV, centralizer_le_L_of_mem_* は S06 namespace で
  h 明示引数 → dot 記法不可。sigma は LinearMap (map_sub 可)。

### ▶▶ §6 (4.x) 全 COMPLETE。次 = B レーン戦略判断 (case-B §8 大 assembly は user/合流調整向き)
§6 character-theory ((3.x)σ + (4.1)-(4.10)) 完了。残る §6 統合 = **case-B → S08 (6.8)** = §8 large
assembly (s08_6_8_assembly_plan.md T0-T11 DAG; 単独 cold-engage は overlap/risk と既 RECON 済)。
**正本=本 session 38 cont.³。(4.10) DONE。**
