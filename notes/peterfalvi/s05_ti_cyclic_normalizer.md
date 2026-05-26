# Peterfalvi §5: TI-Subsets with Cyclic Normalizers — mini-roadmap

**スコープ**: Peterfalvi §5 (pp.15-20), mmd `04.5_pp_15_20_TI-Subsets_with_Cyclic_Normalizers.mmd` (174 行), **9 結果 ((3.1)-(3.9))** ⚠️ audit 訂正 (旧 5 結果は (3.6)-(3.9) 欠落; **(3.8) NC trichotomy が forward 8 cite で外部最多 hub**).
形式化先 (予定): `OddOrder/Peterfalvi/S05_TICyclic.lean`.
ROADMAP 上の位置: **Phase 2b 第 2 波** (§4 Dade 完成必須).
役割: **§4 Dade isometry の cyclic normalizer specialization**, Frobenius complement との連結, 計算的取り扱いの簡素化.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **L3, L12 "5 結果 (3.1)-(3.5)"** → **重大誤認: 実際 9 結果 (3.1)-(3.9)**. 既存表で (3.6) Hypothesis, (3.7) index identity, **(3.8) NC trichotomy**, (3.9) Galois rationality package が完全欠落.
- **(3.8) NC trichotomy が下流 8 cite で最多 hub** (§6×多, §7, §12×2, §15×2). 既存「side material」評価は逆.
- (3.9.b) Galois は §6×2, §12, §13, §15 で利用; (3.7) は **§16 final-contradiction calc** で直接消費.
- **L18 (3.5) "§6-§8+§10-§16 全面"** → 実測 §6×9, §15×3, §12×2, §7×2, §13, §16; **§8/§9/§10/§11/§14 = 0 direct cite**.
- **L53 "Phase 1 §4 (Frobenius) TI-subset dep"** → §5 mmd で §4 (2.X) cite **0**. 実 dep は §3 (1.3) ×1 + §3 (1.9) ×2 + [Is] Ch.7 + [Is] Cor 2.23 + Thm 4.21.
- **L216-232 "Frobenius Complement との関係"** → 推測; §5 mmd で `Frobenius` keyword **0**.
- L292 forward "§11 (9.1), (9.2)" → 誤り; §11 = 0 direct (3.X) cite.
- **L294-319 mathlib eval**: "Induced character 既存 / CF 既存 / ZIrr 既存" → **全て誤り**. mathlib `Induced.lean` は categorical `IndV` (coinvariants) のみ, classical induced character formula 不在. `ClassFunction` 型不在. `ZIrr` 不在.
- **`MulAction.IsBlock` ≠ TI-subset** (混同に注意); TI-subset は新規 `OddOrder/GroupTheory/TISubset.lean` 要.
- "[BG] §3 dep" → **0**. §5 は **BG 完全独立**.
- 行数 "350-400 LOC" → **700-850 LOC** (500-650 (3.1-3.5) + 150-200 (3.6-3.9)).
- **Two-hub** structure: (3.5) Case I/II 内部 hub + (3.8) NC 外部 forward hub. 既存「(3.5) only hub」誤認.

## TL;DR

§5 は §4 Dade isometry を **最重要特殊化** する. 仮説: `G` 有限群, `W = W₁ × W₂` が cyclic (odd order), `V = W - (W₁ ∪ W₂)` が TI-subset で `N_G(V) = W` となる case. **目標**: W が cyclic ⇒ `CF(W, V)` の basis `(α_{ij})` を explicit に構成し、induced characters `Ind_W^G α_{ij}` が orthonormal family `(χ_{ij})` を張る. **結果**: Dade map `τ` の image の orthogonality 構造が完全に決定される ⇒ §6-§8 で coherence 条件を精密に制御可能.

## Lean status (2026-05-26)

`OddOrder/Peterfalvi/S05_TICyclic.lean` は §5 の TI-cyclic setup を §4 Dade interface に接続している:

- `TICyclicHypothesis.toDadeHypothesis`: `H(a)=1` specialization として `S04.Hypothesis` を作る。
- `TICyclicHypothesis.SupportedOnV`: Peterfalvi `CF(W,V)` の Lean 名。
- `TICyclicHypothesis.DadeApplication`: 係数 `k` に parametric な `S04.DadeIsometryData` を §5 carrier に載せる。
- `TICyclicHypothesis.FullDadeApplication`: `k = ℂ` の `S04.FullDadeIsometryData` を載せ、`full_inner_eq` と `full_maps_virtualCharacter` で (2.6.a)/(2.6.b) を §5 側から使えるようにする。
- `map_eq_of_mem_V` / `full_map_eq_of_mem_V`: `H(a)=1` の §4 Dade-map equation を §5 側に直接 expose し、`v ∈ V` 上では `τ α v = α v` と使える。
- `map_eq_zero_of_not_mem_conjugatesOfSet_V` /
  `full_map_eq_zero_of_not_mem_conjugatesOfSet_V`: `V` の共役飽和の外で Dade map が 0 になることを §5 carrier から直接使える。

| # | mmd 行 | 種別 | statement 概要 | 役割 | mathlib | phase2b 被引用 |
|---|--------|------|-----------------|------|---------|---------------|
| **(3.1)** | 3-5 | **Hypothesis** | G 有限群, W = W₁×W₂ cyclic odd, w₁,w₂ > 1, V = W-(W₁∪W₂) は TI-subset で norm=W | **Setup** | low | 全結果の前提 |
| **(3.2)** | 9-19 | **Main Theorem** | σ: CF(W)→CF(G) linear isometry で (a) CF(W,V) は induced, (b) 1_W↦1_G, (c) σ on V は identity, (d) irreducible outside image vanishes on V | **Dade specialization の主結果** | low | (3.3)-(3.5) + §6 |
| **(3.3)** | 21-23 | **Notation** | Irr(W) = {ω_{ij} : 0≤i<w₁, 0≤j<w₂}, ω_{ij}=ω_{i0}ω_{0j} (因数分解) | **Basis 構築の準備** | mid | (3.4)-(3.5) 中核 |
| **(3.4)** | 25-31 | **Lemma** | α_{ij} = (1_W-ω_{i0})(1_W-ω_{0j}) (1≤i<w₁, 1≤j<w₂) が CF(W,V) の ℂ-basis | **Basis 構成** | low | (3.5) + §6 |
| **(3.5)** | 33-115 | **Main Decomposition** | ∃ orthonormal (χ_{ij})_{0≤i<w₁, 0≤j<w₂} ⊂ Z Irr(G) s.t. Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij} | **Cyclic W による orthogonality**; **(3.5) Case I/II 内部 hub** + **(3.8) NC 外部 forward hub** の two-hub 構造 | low | ⚠️ audit 訂正: §6×9, §15×3, §12×2, §7×2, §13, §16 のみ; §8/§9/§10/§11/§14 = **0 direct cite** |
| **(3.6)** | (proof body) | Hypothesis | (3.5) Case II 用 setup | (3.5) 内部 | low | 内部 |
| **(3.7)** | (proof body) | index identity | 単純 index 等式 | 計算補助 | low | **§16 final-contradiction で直接消費** |
| **(3.8)** | (proof body) | **NC trichotomy** | normalizer-centralizer 3 場合分け combinatorial hub | **forward 外部最多 hub** | low | **8 cite** (§6×多, §7, §12×2, §15×2) |
| **(3.9)** | (proof body) | Galois rationality | (a) Galois 作用 (b) σ-rationality | character Galois 整数性 | low | 4 cite (§6×2, §12, §13, §15) |

---

## (3.1) Hypothesis — cyclic normalizer setup

**主張**: 仮定設定
- G: 有限群
- W = W₁ × W₂ ⊂ G: cyclic, odd order
- w₁ := |W₁| ≠ 1, w₂ := |W₂| ≠ 1
- w₁, w₂ coprime (cyclic direct product より)
- V := W - (W₁ ∪ W₂): TI-subset (Trivial Intersection)
- N_G(V) = W: V の正規化群は W

**重要性**: 
- W cyclic ⇒ Ind_W^G が linear isometry on CF(W, V) (Isaacs Ch.7 定理)
- V は W 内で "trivial に交わる" ⇒ V 外の元は V と disjoint conjugate

**Peterfalvi の動機**: §4 の一般仮説 (2.2) で H(a)=1 case に専門化. 計算的に tractable.

**Lean 表現**:
```lean
structure TICyclicNormalizer (G : Type*) [Group G] where
  W : Subgroup G
  W₁ W₂ : Subgroup W
  hW_cyclic : IsCyclic W
  hW_odd : Odd W.card
  hW_decomp : W = Subgroup.prod W₁ W₂
  hw₁ : W₁.card ≠ 1
  hw₂ : W₂.card ≠ 1
  V : Set G
  hV_ti : TrivialIntersection V
  hV_norm : Subgroup.normalizer V = W
```

**Phase 1 との依存** ⚠️ audit 訂正 (旧記載「Phase 1 Ch.6 (Frobenius) の TI-subset dep」は誤り): §5 mmd で **§4 (2.X) cite = 0**. 実 dep は §3 (1.3) ×1 + §3 (1.9) ×2 + [Is] Ch.7 + [Is] Cor 2.23 + Thm 4.21 のみ. Ch.6 Frobenius 不要; Wave 1a 新規 `TISubset.lean` で十分.

---

## (3.2) Main Theorem σ — isometry from W to G

**主張**: isometry σ : CF(W) → CF(G) が存在して以下を満たす:

**(a)** CF(W, V) 上で σ は ind だ:
```
α ∈ CF(W,V) ⟹ α^σ = Ind_W^G α
```

**(b)** trivial 指標は trivial に送られる:
```
1_W^σ = 1_G
```

**(c)** V 上で σ は identity:
```
α ∈ CF(W), x ∈ V ⟹ α^σ(x) = α(x)
```

**(d)** irreducible の "外部" 指標は V で消える:
```
χ ∈ Irr(G) \\ Image(σ) ⟹ χ|_V = 0
```

**意義**: 
- (a): V は W の `trivial intersection` ⇒ induced は "clean"
- (b): σ は normalized mapping (1 保存)
- (c): σ は V 上では "local" (外への extension)
- (d): G の irreducible は σ-image か V-vanishing で split

**Lean 形式化戦略**:
```lean
theorem tiCyclicIsometryExists (hyp : TICyclicNormalizer G) :
    ∃ σ : CF W →ₗᵢ[ℂ] (G → ℂ), 
      (∀ α ∈ CF_support W hyp.V, σ α = Ind_W^G α) ∧
      (σ 1_W = 1_G) ∧
      (∀ α x, x ∈ hyp.V → σ α x = α x) ∧
      (∀ χ ∈ Irr G, χ ∉ Set.range σ → ∀ x ∈ hyp.V, χ x = 0) := by
  sorry
```

---

## (3.3) Notation — irreducible factorization of W

**主張**: W = W₁ × W₂ cyclic より:
- ω_{i0} (0 ≤ i < w₁): kernel が W₂ の irreducible (i.e., W₁ から来る)
- ω_{0j} (0 ≤ j < w₂): kernel が W₁ の irreducible (W₂ から来る)
- ω_{00} := 1_W
- **ω_{ij} := ω_{i0} · ω_{0j}** (factorization)

**重要性**: cyclic だから direct product ⇒ Irr(W) は因数分解される.

**References**: Isaacs Ch.2 Thm 4.21 (cyclic product の irreducible), Cor 2.23 (number of irreducibles).

**Lean**:
```lean
def tiCyclicIrr (hyp : TICyclicNormalizer G) :
    Finset (W → ℂ) :=
  let irr_W₁ := Irr W₁
  let irr_W₂ := Irr W₂
  irr_W₁ ×ˢ irr_W₂ |>.image (fun (ω₁, ω₂) => ω₁.restrict · ω₂.restrict)
```

---

## (3.4) Lemma — basis construction in CF(W, V)

**主張**: CF(W, V) (= W 上の class function で V で支持されたもの) の ℂ-basis は:

```
{α_{ij} := (1_W - ω_{i0})(1_W - ω_{0j}) : 1 ≤ i < w₁, 1 ≤ j < w₂}
```

計 (w₁-1)(w₂-1) 個.

**証明スケッチ**:
1. α_{ij} ∈ CF(W, V): product form (1_W - ω_{i0}) vanishes on W₁ (kernel が W₂より), (1_W - ω_{0j}) vanishes on W₂. 交差で V = W - (W₁∪W₂) に support.
2. Linear independence: ⟨α_{ij}, ω_{ij}⟩ = 1 (orthogonality of Irr)で diagonal.
3. Dimension: |V| = |W| - |W₁| - |W₂| + 1 = (w₁-1)(w₂-1).

**Lean 形式化**:
```lean
lemma tiCyclicBasis (hyp : TICyclicNormalizer G) :
    let α := fun i j => (1 - ω_{i0}) * (1 - ω_{0j})
    Basis.mk_eq_range (Finset.range (w₁-1) ×ˢ Finset.range (w₂-1)) 
      (fun ⟨i, j⟩ => α (i+1) (j+1)) = CF W hyp.V := by
  sorry
```

**物理的意味**: W = W₁ × W₂ の product 構造が basis にそのまま現れる (tensor product 的).

---

## (3.5) Main Decomposition — orthonormal (χ_{ij})

**主張**: orthonormal family が存在:
```
(χ_{ij})_{0≤i<w₁, 0≤j<w₂} ⊂ ZIrr(G)
s.t. χ₀₀ = 1_G
and  (i,j)≠(0,0) ⟹ Ind_W^G α_{ij} = 1_G - χ_{i0} - χ_{0j} + χ_{ij}
```

**§5 の山場**: この分解により (3.2) の σ が完全に決定される.

### (3.5.0) Basic inner products

**補助結果 (3.5.1)**: β_{ij} := Ind_W^G α_{ij} - 1_G とすると:
- ⟨β_{ij}, 1_G⟩ = 0
- ‖β_{ij}‖² = 3
- β_{ij}, β_{ij'} が orthogonal if i≠i', j≠j'

**証明**: Ind_W^G が isometry (Isaacs Ch.7), α_{ij} が orthonormal basis.

### (3.5.2) Single-intersection lemma

**補助結果 (3.5.2)**: β_{ij} ∈ ZIrr(G) ⇒ β_{ij} = Σ_{χ∈A_{ij}} χ (sum of 3 irreducibles).

|A₁₁ ∩ A₁₂| = 1 (single element in common).

**証明**: norm 3 + orthogonality ⇒ exactly 3 irreducibles. Intersection size by characteristic polynomial argument.

**重要性**: (3.5.2) の "single intersection" が inductive step (3.5.4)-(3.5.5) を駆動.

### (3.5.3)-(3.5.5) Inductive lattice construction

**大戦略**: w₁ ≥ 5 (WLOG) を仮定. (3.5.2) を索引 (i,j) の全格子で系統的に適用.

**Case I vs. Case II** (行 60-108): 
- **Case I**: 3 つ以上の A_{i1} が共通元を持つ ⇒ **矛盾** (3.5.4.5 で導出)
- **Case II**: pairwise disjoint ⇒ **矛盾** (3.5.4.6 で導出)

**結論 (3.5.4)**: ∩_{1≤i<w₁} A_{i1} = {-χ₀₁} (単一元).

**拡張 (3.5.5)**: 全 (i,j) に対して
```
β_{i1} = -χ_{i0} - χ₀₁ + χ_{i1}
β_{i2} = -χ_{i0} - χ₀₂ + χ_{i2}
```
を得る. w₂ ≥ 5 の場合は同じロジックで全 (i,j) に拡張.

**Lean 形式化**:

Case I/II の詳細は mmd L60-108 (52 行). **Peterfalvi の最大の計算量の節**.

推奨: **Finset induction** + **orthogonality tactic** で自動化. 手書きは避ける.

```lean
lemma tiCyclicIntersectionLattice (hyp : TICyclicNormalizer G) (hw₁ : 5 ≤ w₁) :
    ∃ χ₀₁ χ₀₂ : Irr G,
      (∀ i, ∃ χ_{i0} χ_{i1} χ_{i2}, 
        β_{i1} = -χ_{i0} - χ₀₁ + χ_{i1} ∧
        β_{i2} = -χ_{i0} - χ₀₂ + χ_{i2}) := by
  -- 矛盾を逐次排除
  sorry
```

---

## Frobenius Complement との関係 (Isaacs Ch.6)

**Context**: Frobenius group G = H ⋊ K (K が fixed point free action)
- Frobenius kernel H: normal, nilpotent
- Frobenius complement K: cyclic or trivial
- Character theory: 1_H から来る irreducible が非常に rigid

**Peterfalvi §5 との連結**:
- W = Frobenius complement に specialization 可能 (cyclic normalizer ⇒ Frobenius complement)
- V = Frobenius kernel の部分集合 (TI-subset)
- Dade isometry τ: K-character を G-character に lift

**Phase 1 Ch.6 との dependency**:
- TI-subset: Ch.6 §1-§2
- Frobenius kernel nilpotent: Ch.6 §3
- Transfer + central extension: Ch.6 §4-§5

---

## §4 Dade isometry の §5 specialization

**§4 Hypothesis (2.2)** (一般):
- (a) conjugacy equivalence
- (b) centralizer factorization C_G(a) = H(a) ⋊ C_L(a)
- (c) coprime |H(a)| ⊥ |C_L(b)|

**§5 Hypothesis (3.1)** (specialization):
- L = W = cyclic, N_G(V) = W
- H(a) = 1 for all a ∈ V (Classical TI-subset)
- W cyclic ⇒ coprime w₁ ⊥ w₂ automatic

**効果**:
- H(a) = 1 ⇒ (2.4.b) の factorization C_G(a) = C_W(a) に simplify
- cyclic ⇒ induced character は explicit に計算可能
- **結果**: (3.2)-(3.5) で Dade map σ の image を完全に刻印可能

---

## §6 (Dade for certain type) への橋渡し

**§6 の role**: (3.1)-(3.5) を特定の **部分群 type に対して一般化**.

```
§5 (3.1)-(3.5): W = N_G(V), V が TI-subset, W cyclic
         ↓
§6 (4.1)-(4.5): より広い subgroup family (不必ずしも N_G(V))
```

**§6 の新仮説**: "Certain type subgroup" (Peterfalvi に特有な術語) は
- maximal abelian subgroup or
- Frobenius complement or
- より一般的に, 特定の cohomology 条件を満たす

**Phase 2b 着手時の整理**: §6 を読む前に §5 を完全にmaster. §5 の basis `α_{ij}` と decomposition `(χ_{ij})` が §6 の前提.

---

## §10-§16 Type 分析での使用

### (3.1)-(3.5) が活躍する場所

| 節 | Type | 用途 | reference |
|---|------|------|-----------|
| **§11** | II, III, IV | Maximal subgroup N/L が cyclic complement で W = normalizer → (3.2)-(3.5) apply | (9.1), (9.2) |
| **§12** | III, IV, V | [S,S] が Frobenius group → §5 の Dade specialization | (10.7) |
| **§14** | I | Maximal subgroup が特定 structure → (3.2) の σ を使う | (12.1)-(12.13) |
| **§15** | S, T | 最終仕込み: S と T の位数・指標 → (3.5) の χ_{ij} 族で表現 | (13.1)-(13.17) |

### 具体例: §15 の使用パターン

§15 で「virtual character ψ に対して」
```
ψ = Σ a_{ij} ω_{ij}^σ + β
```
という decomposition が現れたら、(3.2)-(3.5) の σ がそれを裏付けしている.

---

## mathlib カバレッジ ⚠️ audit 訂正 (旧表の「Induced/CF/ZIrr 既存」は **全て誤り**)

| 概念 | mathlib 状況 | Phase 1 依存 | 新規実装 | 形式化コスト |
|------|---------|---------|----------|----------|
| Cyclic group | 既存 | — | ~0% | — |
| Direct product W₁×W₂ | 既存 | — | ~0% | — |
| TI-subset | **不在** (`IsTrivialBlock` ≠ TI) | — | **100%** (新規 `TISubset.lean`) | 中 (~80 LOC) |
| Induced character | **不在** (`IndV` coinvariants のみ; classical formula なし) | — | **100%** (新規 `InducedCharacter.lean`) | 大 (~200 LOC) |
| Class function CF | **不在** (only `character : G → k`) | — | **100%** (新規 `ClassFunction.lean`) | 中 (~150 LOC) |
| Virtual character ZIrr | **不在** | — | **100%** (新規 `ZIrr.lean`) | 中 (~80 LOC) |
| **Basis in CF(W,V)** | — | — | **100%** | **中 (8h)** |
| **Orthonormal (χ_{ij})** | — | — | **100%** | **大 (16h)** |

**全体**: ~0% mathlib (前提 infra 全部新規), ~0% Phase 1 dep, **100% 新規**. **行数**: **~700-850 LOC** (audit 訂正; 旧記載「350-400 LOC」の約 2 倍, (3.6)-(3.9) 追加分含む).

### "Basis in CF(W,V)" の実装

Product structure (W₁ × W₂) を利用:

```lean
def tiCyclicBasisFamily (hyp : TICyclicNormalizer G) :
    Finset (W → ℂ) :=
  let irr₁ := Irr W₁ \ {1_W₁}
  let irr₂ := Irr W₂ \ {1_W₂}
  Finset.biUnion irr₁ (fun ω₁ =>
    Finset.map (fun ω₂ => (1 - ω₁.restrict) * (1 - ω₂.restrict)) irr₂)
```

### "Orthonormal (χ_{ij})" の Lean 表現

**戦略**: existence + uniqueness の分離.

```lean
structure TICyclicOrthonormal (hyp : TICyclicNormalizer G) where
  χ : Fin w₁ × Fin w₂ → Irr G
  h_χ₀₀ : χ (0, 0) = 1_G
  h_χ_ortho : ∀ ij ij', ij ≠ ij' → ⟨χ ij, χ ij'⟩ = 0
  h_χ_decomp : ∀ i j, i ≠ 0 ∨ j ≠ 0 →
    Ind_W^G (α ij) = 1_G - χ (i, 0) - χ (0, j) + χ (i, j)
```

---

## Phase 2b 形式化着手順

### Stage 1: Hypothesis Setup (2-3h)
- (3.1) TICyclicNormalizer structure
- Phase 1 Ch.6 からの import (TI-subset, cyclic group)

### Stage 2: Basis Construction (6-8h, 中盤の山場)
- (3.3) Notation (irreducible factorization)
- (3.4) Basis α_{ij} 構成 + linear independence
- helper lemmas (dimension calc)

### Stage 3: Orthonormal Decomposition (12-16h, **最大山場**)
- (3.5.1) β_{ij} の norm・直交関係
- (3.5.2) A_{ij} 族の intersection analysis
- **(3.5.4)-(3.5.6) Case analysis** (Case I/II 矛盾排除) — **最大計算量**
- (3.5) 最終分解

### Stage 4: Main Theorem (3-4h)
- (3.2) σ の existence + properties
- (3.1)-(3.5) との consistency 確認

**合計**: **23-31 時間** (標準 Lean 形式化者).

### 実装タイムライン (Phase 2b 第 2 波)

```
Week N (§4 Dade 完成直後)
  ├─ Day 1-2: (3.1) Hypothesis setup + import review
  ├─ Day 3-4: (3.3)-(3.4) Basis 構成
  └─ EOW: basic infra PR (50 lines, non-blocking)

Week N+1 (Case analysis 開始)
  ├─ Day 1-3: (3.5.1)-(3.5.2) basic norm/orthogonality
  ├─ Day 4-5: (3.5.4) Case I decomposition (矛盾排除)
  └─ EOW: partial results PR (100 lines)

Week N+2 (Case II 完成)
  ├─ Day 1-2: (3.5.6) Case II (矛盾排除)
  ├─ Day 3: (3.5.5) 最終分解
  └─ Day 4-5: (3.2) σ and (3.1)-(3.5) 統合 PR (main, 150 lines)
```

---

## 未解決 / TODO

1. **mathlib CH.6 (Frobenius) 完成日程**: §5 形式化が Phase 1 Ch.6 の TI-subset/normalizer result に依存. Ch.6 の形式化スケジュール確認要.

2. **(3.5.4)-(3.5.6) 矛盾排除の formalization 戦略**:
   - **手書き**: 52 行 (mmd L60-108) の detail を tactic で埋める → 200+ lines, 時間大
   - **macro**: custom `orthogonal_tactic` で A_{ij} 族の intersection 自動分析 → 開発時間 vs. 使用時間 trade-off
   - **推奨**: **3 つの Case (Case I subcase, Case II subcase, Case III degenerate)** を分離して `by sorry` で 1-2 week 様子見後に決定

3. **σ の computability**: (3.2) では σ が "存在する" のみ. 実装では explicit map か existence か? — §6-§8 で σ を具体的に使うなら explicit 必須. preview §6 して判断.

4. **Frobenius group specialization**: Peterfalvi は text で明言していないが、W = Frobenius complement case への apply が自然. Phase 1 Ch.6 Frobenius kernel の API readiness に依存.

5. **§5 と §6 の interface**: §6 は (3.1)-(3.5) を一般化するが、どこまで? — §6 mmd preview して scope 確定要.

---

**作成**: 2026-05-22.
**出典**: `references/peterfalvi/04.5_pp_15_20_TI-Subsets_with_Cyclic_Normalizers.mmd` (174 行), §4 ノート, overview.
**次ステップ**: 
- Stage 1 (Hypothesis setup) を試行実装 → PR with docstring
- (3.5.4)-(3.5.6) の矛盾排除 tactic macro 検討
- §6 preview (relationship to "Certain type" subgroup)
