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
