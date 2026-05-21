# Peterfalvi §1+§2: Introduction + Notation — mini-roadmap (合体版)

**スコープ**: Peterfalvi §1 (pp.1-2, 40 行) + §2 (pp.3-4, 40 行). 番号付き結果 0 (前文相当).
**形式化先** (予定): `OddOrder/Peterfalvi/S01S02_IntroductionNotation.lean` (notation 定義 + docstring)
**ROADMAP 上の位置**: Phase 2b 第 1 波 (前提なし, 並行可)
**役割**: FT 戦略の明示 + 指標論・加群記号の統一

---

## TL;DR

- **§1**: Feit-Thompson 定理の証明戦略を明示. 局所構造分析 (BG Phase 2a) と指標論分析 (Peterfalvi Phase 2b) への二部構成を宣言. [BG] への依存と [Is] (Isaacs Character Theory 1976) の前提知識を列挙.
- **§2**: 指標論・加群 + 部分群に関わる記号・用語の定義. 本文全 16 節 + 5 付録の言語基盤.
- **mathlib 対応**: `RepresentationTheory.Character.Irr` 等既存 API と Peterfalvi 記号の対応表を本ノートで提示. 形式化時に notation 拡張ファイルで統一.
- **前提なし**: 既存 Isaacs Phase 1 があれば §3 以降が着手可能. §1§2 は形式化対象なし (記号・context のみ).

---

## §1 Introduction (pp.1-2) 内容解析

### 1.1 FT 定理と証明概要

Feit-Thompson 定理 (1963):
> **定理 (FT)**: 奇数位数の有限群は可解である.
> **同値形**: 奇数位数の非可換単純群は存在しない.

証明の二部構成 (両親論文 [FT] + 先行結果 [Su], [FHT]):
1. **第一部**: 最小反例 G を仮定し、G の最大部分群の構造を研究 (簡潔に [Su], 中程度に [FHT], 複雑に [FT])
2. **第二部**: 指標論を用いて矛盾を導出 (**本Peterfalvi著作の対象**)

### 1.2 本著作の位置付け

- **目的**: [FT] 第二部 (Chapters III, V) の改訂版 = 指標論パート
- **並行関係**: [BG] (Bender-Glauberman 1994) = 第一部 (局所構造) の完全改訂版
  - [BG] なしでも読み進められる (§8 で BG 結果レビュー)
  - ただし §9, §10-§16 で BG 結果を頻繁に参照

**形式化方針**: 本プロジェクトは Phase 2a ([BG] の形式化) → Phase 2b (Peterfalvi) → Phase 4 (FT 完全証明) の順序.

### 1.3 前提知識 [Is] (Isaacs Character Theory 1976)

Peterfalvi は読者の知識を以下に限定:

**Isaacs Chapters 1-2** (既約指標・指標の基本):
- 指標定義, 直交関係, 誘導・制限など

**Isaacs Chapter 3** セクション (3.1)-(3.7), (3.11), (3.14):
- (3.1)-(3.7): 既約指標の個数・次数 (column orthogonality など)
- (3.11): Galois automorphism と指標
- (3.14): 指標の実性 (real character)

**Isaacs Chapter 4** セクション (4.1), (4.2), (4.20), (4.21):
- (4.1), (4.2): 部分群上の制限・誘導指標
- (4.20), (4.21): Frobenius 補題 (character criterion for normal subgroup)

**Isaacs Chapter 5** セクション (5.1)-(5.5), (5.7)-(5.9):
- (5.1)-(5.5): Transfer 写像・focal subgroup
- (5.7)-(5.9): Transfer theorems (Thompson の結果も含む)

**Isaacs Chapter 6** セクション (6.1)-(6.8), (6.10), (6.11), (6.28), (6.32)-(6.34):
- (6.1)-(6.8): Frobenius 群の基本性質
- (6.10), (6.11): Frobenius complement の characterization
- (6.28): Frobenius kernel の性質
- (6.32)-(6.34): Frobenius 指標論

**Isaacs Chapter 7** セクション (7.1)-(7.7):
- (7.1)-(7.7): Thompson 定理・normal p-complement

**Problem 2.2** (Isaacs):
> 有限群 G (位数 n), χ ∈ Irr G, σ ∈ Aut(Q_n) に対し、χ^σ (g ↦ σ(χ(g))) も既約指標である.

**補強**: Peterfalvi 本文 §3-§8 で Isaacs の理論を再掲・補強し、§4-§8 の Dade isometry + Coherence という新概念を導入.

### 1.4 その他の参照

- **[HB]** (Huppert-Blackburn _Finite Groups_): Theorem 12.4 (Chapter XI) — p-群の構造
- **[H]** (Huppert _Endliche Gruppen_): Satz 8.18 (Kapitel V) — p-群の部分群格子
- **[BG]** (Bender-Glauberman _Local Analysis_): 初期部分で localization lemma, p-completeness など

### 1.5 本著作の構成宣言

> The text is divided into sections. Sections 1 to 7 contain preliminary results. Sections 8 to 14 study a minimal counterexample to the Feit-Thompson Theorem. 

- **§1-§7** (preliminaries) ≡ **[本ノート] §3-§8**: 指標論の基本 + Dade isometry + Coherence
- **§8-§14** (minimal counterexample analysis) ≡ **[本ノート] §9-§15**: BG 結果を入力に、指標論で最小単純群を分析
- **§16** (non-existence of G): 最終矛盾導出

**結果の番号体系**: (N.M) 形式 (N 節, M 番号) で Hypothesis/Theorem/Lemma を列挙. 中間補題は (N.M.1), (N.M.2) など.

---

## §2 Notation (pp.3-4) 内容解析

§2 は **group-theoretic + character-theoretic notation** の辞書. 以下、Peterfalvi が定義した用語・記号を Lean 形式化候補と共に列挙.

### 2.1 指標空間・類関数

#### Irr(G), Irr G (既約指標集合)

```
Irr(G) := { χ : G → C | χ は既約指標 }
```

**mathlib**: `Mathlib/RepresentationTheory/Character.lean`
- `Character.irr : GroupHomClass F G ℂ → Finset ...` (既約指標の有限集合化)
- Lean notation: `Irr.irr` を使用可

**Peterfalvi 記法**: **(§2 line 7)** `Irr(G)` (括弧あり) と `IrrG` (括弧なし) は区別なし.

**形式化**: 既存 mathlib を利用. Notation: `notation "Irr" => Character.irr` で統一.

---

#### CF(G) (類関数空間)

```
CF(G) := { φ : G → C | φ は class function }
     = { φ : G → C | φ(g) = φ(h) if g, h conjugate }
```

**mathlib**: `ClassFunction G ℂ` (文字通り)

**Peterfalvi**: **(§2 line 9)** `CF(G)` という記号を直接使用.

**形式化**: `abbrev CF (G : Type*) := ClassFunction G ℂ` で定義し、ノーテーション「`CF(G)`」を追加.

---

#### (α, β)_G, (α, β) (内積)

```
(α, β)_G := (1/|G|) * Σ_{g ∈ G} α(g) * conj(β(g))
```

**mathlib**: `Mathlib/RepresentationTheory/Character/Basic.lean`
- `innerProductSpaceAux` / `inner` で orthogonality 関係

**Peterfalvi**: (§2 line 11) subscript G は G が明白なら省略.

**形式化**: `inner α β` (mathlib の `⟨α, β⟩`) と `(α, β)_G` の dual notation を提供.

---

#### ‖α‖² (ノルム二乗)

```
‖α‖² := (α, α)
```

**Peterfalvi**: (§2 line 11) = `(α, α)` の abbreviation. 既約指標なら `‖χ‖² = 1`.

---

#### Supp(φ) (support)

```
Supp(φ) := { x ∈ G | φ(x) ≠ 0 }
```

**mathlib**: `Function.support φ` (一般的な support 定義). Character に特化したものは要新規.

**Peterfalvi**: (§2 line 13) 指標の support を g ↦ φ(g) で定義.

**形式化**: `def charSupport (φ : CF G) : Set G := { x | φ x ≠ 0 }`

---

#### CF(G, A) (A-制限類関数)

```
CF(G, A) := { φ ∈ CF(G) | Supp(φ) ⊆ A }
```

**Peterfalvi**: (§2 line 15) A ⊂ G に対し、support が A に含まれる類関数のみ.

**形式化**: `def CF_subset (G : Type*) (A : Set G) : Set (CF G) := { φ | charSupport φ ⊆ A }`

**注記**: Dade isometry (§4) で頻出. Virtual character on A-subset (Z[Irr(L), A]) との区別が重要.

---

#### Z[X], R[X] (R-線形結合)

```
R[X] := { Σ r_i * x_i | r_i ∈ R, x_i ∈ X }
R[X, A] := R[X] ∩ CF(G, A)
```

**Peterfalvi**: (§2 line 17) Z[Irr G] = 仮想指標, Q[Irr G], R[Irr G] など.

**mathlib**: `Submodule R X` / `span R X`.

**形式化**: 既存 mathlib で `ZLinearCombination` 相当. notation `ℤ[X]` で統一.

---

#### Virtual Character: Z[Irr G]

```
Virtual Character := Z[Irr G] = ℤ-linear combination of irreducible characters
```

**Peterfalvi**: (§2 line 19) 定義: 既約指標の整数線形結合. **仮想指標空間全体** が Dade isometry の domain/codomain.

**mathlib**: `Module.End ℤ (CF G)` 的構造、または `Submodule ℤ (CF G)` の span.

**形式化**: `def VirtualCharacter (G : Type*) := Span ℤ (Set.range (Irr G))` と定義. Notation: `𝒱(G)` or `VChar G`.

---

### 2.2 制限・誘導

#### Res^G_H (制限)

```
Res^G_H : CF(G) → CF(H)
         χ ↦ χ|_H (H 上での χ の制限)
```

**mathlib**: `ClassFunction.restrict G H` / 既存 representation 制限.

**Peterfalvi**: (§2 line 21) 表記を `Res^G_H` に統一. Subscript H/superscript G で群の関係を明示.

**形式化**: `def Res (H : Subgroup G) (φ : CF G) : CF H := ...`

---

#### Ind^G_H (誘導)

```
Ind^G_H : CF(H) → CF(G)
         ψ ↦ ψ^G (H から G への誘導指標)
```

**Frobenius reciprocity**:
```
⟨Ind^G_H(ψ), χ⟩_G = ⟨ψ, Res^G_H(χ)⟩_H
```

**mathlib**: `ClassFunction.ofCompact` / representation induction via tensor product.

**Peterfalvi**: (§2 line 21) `Ind^G_H` を誘導指標として定義. 仮想指標 Z[Irr G] への拡張が §4-§8 で重要.

**形式化**: `def Ind (H : Subgroup G) (ψ : CF H) : CF G := ...`

---

### 2.3 指標の操作

#### 1_G (principal character)

```
1_G : G → ℂ
     g ↦ 1  (全ての g で 1)
```

**mathlib**: `ClassFunction.ofCompact` の principal representation 相当.

**Peterfalvi**: (§2 line 23) 自明指標. **virtual character** として Z[Irr G] に含まれる.

---

#### χ̄ (複素共役)

```
χ̄(g) := conj(χ(g))
```

**Peterfalvi**: (§2 line 23) χ̄ ∈ Irr(G) も既約 (by Isaacs Problem 2.2).

**注記**: Galois automorphism σ ∈ Aut(Q_n) に対して χ^σ も既約 (§1 最後で言及).

---

#### θ^g (conjugate character, g ∈ G に対し)

**前提**: H ◁ G, θ ∈ CF(H), g ∈ G

```
θ^g : H → ℂ
      x ↦ θ(x^{g^{-1}})  = θ(g^{-1}xg)
```

**Peterfalvi**: (§2 line 25) 定義: `θ^g(x^g) = θ(x) for all x ∈ H`. (内側の指数を見直す: g は fixed, x が変数)

**形式化**: Normal subgroup 上で定義. `def conjugateCharacter (g : G) (θ : CF H) : CF H := ...`

---

#### I(θ), I_G(θ) (inertia group)

**前提**: H ◁ G, θ ∈ Irr(H)

```
I_G(θ) := { g ∈ G | θ^g = θ }
        = stabilizer of θ under conjugation
```

**Peterfalvi**: (§2 line 25) inertia group 定義.

**重要性**: Dade isometry (§4-§5) で **cyclic normalizer** (L = N_G(A) で I_L(θ) = cyclic) の仮定が頻出.

**形式化**: `def inertiaGroup (θ : Irr H) : Subgroup G := ...`

---

### 2.4 有限体・指数

#### Q_n (n 乗一の体)

```
Q_n := ℚ(ζ_n)  where ζ_n = primitive n-th root of unity
```

**Peterfalvi**: (§2 line 27) order n の群の指標値は Q_n に属す (by Isaacs Ch.2).

**mathlib**: `CyclotomicField n ℚ` で既存.

---

#### exp(G) (exponent)

```
exp(G) := min{ n | g^n = 1 for all g ∈ G }
```

**Peterfalvi**: (§2 line 35) 指標値の最小体は Q_{exp(G)}.

**mathlib**: `Subgroup.exponent`.

---

#### π(G) (素因子集合)

```
π(G) := { p prime | p | |G| }
```

**Peterfalvi**: (§2 line 37) odd-order 仮定 = 2 ∉ π(G).

---

### 2.5 σ-Groups, Radical

#### σ-group, σ', g_σ, g_{σ'} (σ-part)

**前提**: σ ⊆ prime set, g ∈ G

```
G is σ-group  ⟺ π(G) ⊆ σ
g_σ, g_{σ'} ∈ ⟨g⟩  with g = g_σ · g_{σ'}
                    π(⟨g_σ⟩) ⊆ σ,  π(⟨g_{σ'}⟩) ⊆ σ'
```

**Peterfalvi**: (§2 line 39) σ-Hall subgroup 分解. σ = {p} なら g_p, g_{p'}.

**mathlib**: Hall subgroup はあるが、σ-part decomposition は Isaacs Ch.1 に依存.

---

#### O_σ(G), O_p(G), O_{p'}(G) (σ-radical)

```
O_σ(G) := largest normal σ-subgroup of G
O_p(G)  := O_{p}(G)
O_{p'}(G) := O_{p'}(G) = largest normal p'-subgroup
```

**Peterfalvi**: (§2 line 39) odd-order 仮定下、O_2(G) は意味あるが O_2'(G) = G に近い (almost all odd).

**mathlib**: Isaacs に対応物あり. `Sylow.p_radical` など.

---

#### F(G) (Fitting subgroup)

```
F(G) := largest normal nilpotent subgroup of G
```

**Peterfalvi**: (§2 line 41) Peterfalvi §15 (S, T) で F(G) の structure を指標論で詰める.

**mathlib**: `Subgroup.fitting`.

---

### 2.6 群論記号

#### Φ(G) (Frattini subgroup)

```
Φ(G) := intersection of all maximal subgroups of G
```

**Peterfalvi**: (§2 line 41) p-group, abelian などで characterization.

**mathlib**: `Subgroup.frattini`.

---

#### G = H ⋊ K (semidirect product)

```
G = H ⋊ K  ⟺ H ◁ G, G = HK, H ∩ K = 1
```

**Peterfalvi**: (§2 line 41) split extension. normal + complement.

**mathlib**: `Subgroup.SemiDirectProduct`, `GroupAction` 経由.

---

#### Fixed-point-free action, "without fixed points"

```
H acts fixed-point-freely on X
  ⟺ ∀ x ∈ X, ∀ h ∈ H:  h·x = x  ⟹  h = 1 or x = 1
```

**Peterfalvi**: (§2 line 41) H, G 部分群で H が G に作用, fixed-point-free ⟺ non-trivial 元は non-trivial 元のみ固定.

**mathlib**: `MulAction` + `fixed_points` 計算. notation: `acts_fixed_point_freely` で新規定義可.

---

#### Ω₁(G) (Frattini-type for p-groups)

**前提**: p prime, G is p-group

```
Ω₁(G) := ⟨{ g ∈ G | g^p = 1 }⟩
```

**Peterfalvi**: (§2 line 41) = {g ∈ G | order of g divides p}. Frattini φ(G) = subgroup generated by ... と異なる.

**mathlib**: `SubgroupClass.iInf_subgroup_of_prime_orderEq` など周辺 API.

---

#### A^# (pointed set)

```
A^# := A - {1}
```

**Peterfalvi**: (§2 line 31) non-identity 部分. CF(G, A^#) = support in non-identity elements.

**形式化**: `def pointedSet (A : Set G) := A \ {1}`

---

#### A^L (orbit under L)

```
A^L := { a^x | a ∈ A, x ∈ L }
```

**Peterfalvi**: (§2 line 33) group action notation.

**mathlib**: `GroupAction.orbit`.

---

#### TI-subset (Trivial Intersection)

```
A is TI in G  ⟺ ∀ g ∈ G:  A^g = A  or  A^g ∩ A = ∅
```

**Peterfalvi**: (§2 line 29) **重要**: Dade isometry (§4-§5) の中心的仮定. cyclic normalizer との組み合わせで強力.

**mathlib**: 周辺だが完全な定義は要新規.

**形式化**: `def TI (G : Type*) (A : Set G) : Prop := ∀ g : G, A.map (· ^ g) = A ∨ Disjoint A (A.map (· ^ g))`

---

## 3. 指標論記号 → mathlib 対応表

| Peterfalvi 記号 | 意味 | mathlib 相当 | Lean notation | Status |
|---|---|---|---|---|
| `Irr(G)` | 既約指標集合 | `Character.irr` | `Irr G` | **既存** |
| `CF(G)` | 類関数空間 | `ClassFunction G ℂ` | `CF G` | 既存 (rename) |
| `(α,β)_G` | 指標内積 | `inner α β` | `(α, β)_G` | **既存** |
| `‖α‖²` | 内積ノルム | `norm_sq_eq_inner` | `‖α‖²` | **既存** |
| `Supp(φ)` | 指標 support | `Function.support` | `Supp φ` | **新規** |
| `CF(G,A)` | A-制限類関数 | `Submodule.subtype` + 制限 | `CF G A` | **新規** |
| `Z[Irr G]` | 仮想指標 | `Submodule.span ℤ` | `𝒱 G` | **新規** |
| `Res^G_H` | 制限 | `ClassFunction.restrict` | `Res φ` | **既存** (rename) |
| `Ind^G_H` | 誘導 | `ClassFunction.induced` | `Ind ψ` | **既存** (rename) |
| `1_G` | principal | `ClassFunction.ofCompact 1` | `1_G` | **既存** |
| `χ̄` | 複素共役 | `Complex.conj ∘ χ` | `conj χ` | **既存** |
| `θ^g` | conjugate char | 新規定義 | `θ ^ g` | **新規** |
| `I_G(θ)` | inertia group | 新規定義 | `Inertia θ` | **新規** |
| `Q_n` | n乗一の体 | `CyclotomicField n ℚ` | `Q n` | **既存** |
| `exp(G)` | 指数 | `Subgroup.exponent` | `exp G` | **既存** |
| `π(G)` | 素因子集合 | `Nat.factors \|G\|` | `π G` | **既存** (via factors) |
| `O_σ(G), O_p(G)` | σ-radical | `Subgroup.pCore` 類似 | `O σ G` | **既存** (partial) |
| `F(G)` | Fitting | `Subgroup.fitting` | `F G` | **既存** |
| `Φ(G)` | Frattini | `Subgroup.frattini` | `Φ G` | **既存** |
| `G = H ⋊ K` | semidirect | `Subgroup.SemiDirectProduct` | `G = H ⋊ K` | **既存** |
| `Ω₁(G)` | p-part | 周辺 API | `Ω₁ G` | **新規** |
| `A^#` | pointed set | `A \ {1}` | `A^#` | **新規** (abbrev) |
| `A^L` | orbit | `GroupAction.orbit` | `A ^ L` | **既存** |
| `TI(G,A)` | TI-subset | 周辺だが未統一 | `TI A` | **新規** |

---

## 4. [BG], [Is], [HB], [H] 文献参照のまとめ

### 4.1 [Is] — Isaacs Character Theory (1976)

Peterfalvi §1 で明示的に依存する Isaacs の定理・補題:

| Isaacs Ref | 内容 | Peterfalvi §での役割 | mathlib 形式化状況 |
|---|---|---|---|
| **Ch.1-2** | 既約指標基本 + 直交関係 | §3 基礎再掲 | **既存** (partial) |
| **Ch.3 (3.1)-(3.7), (3.11), (3.14)** | 既約個数, Galois auto, real character | §3 補強 | 既存 (partial) |
| **Ch.4 (4.1), (4.2), (4.20), (4.21)** | Res/Ind, Frobenius criterion | §3-§5 構築 | **既存** |
| **Ch.5 (5.1)-(5.5), (5.7)-(5.9)** | Transfer, focal subgroup | §3 (Thompson criterion) | **Phase 1 Ch.5** |
| **Ch.6 (6.1)-(6.34)** | Frobenius 群全面 | §9, §11 (Frobenius family) | **Phase 1 Ch.6** |
| **Ch.7 (7.1)-(7.7)** | Thompson normal p-complement | §3 (focal subgroup) | **Phase 1 Ch.7** |
| **Problem 2.2** | Galois auto of χ | §1 最後 (Galois action) | Implicit in Lean |

**形式化戦略**: Phase 2b §3 はほぼ Isaacs チャプター 3-7 の recap +補強. mathlib + Phase 1 Isaacs で **90% 被覆見込み**.

### 4.2 [BG] — Bender-Glauberman (1994)

Peterfalvi が直接引用する BG の結果:

**§1-§2**: BG のみで**軽く言及** (localization lemma 程度)

**§3**: BG からの多数引用
- **[BG] Prop 1.5(d)**: π-Hall subgroup (existence, uniqueness)
- **[BG] Lem 1.14, 1.22**: p-complement 関連

**§4-§8** (Dade + Coherence コア): BG §1 への参照多数

**§9** (非存在定理): **[BG] App.C と並行** — Frobenius family 非存在の character-free version.

**§10-§16**: **[BG] §10-§16 の出力を入力** として指標論で再分析
- BG Theorem A-E (§16) ⟹ Peterfalvi (8.1)-(8.6) (§10) での Type I-V classification

**§15** (最大規模 365 行): BG §15 (M_F subgroup) + 指標論で S, T の詳細化

**形式化戦略**: Phase 2a ([BG] form 2) を完了 → Phase 2b で BG §10-§16 結果を import + wrap して Peterfalvi に接続.

### 4.3 [HB] — Huppert-Blackburn _Finite Groups_

Peterfalvi §1 で言及:
- **Theorem 12.4** (Chapter XI): p-群の p-center 関連

mathlib では Huppert の系統的 API は限定的. 形式化時は個別に確認.

### 4.4 [H] — Huppert _Endliche Gruppen_

Peterfalvi §1 で言及:
- **Satz 8.18** (Kapitel V): p-群の subgroup lattice (nilpotent の特性)

ドイツ語で詳細な追跡は TBD.

---

## 5. 形式化方針 (Notation ファイル化)

### 5.1 新規ファイル構成

```
OddOrder/Peterfalvi/S01S02_IntroductionNotation.lean
├── docstring: §1 introduction (内容は context のみ, no theorem)
├── docstring: §2 notation
├── notation definitions (section 1.1-2.6)
│   ├── CF (class function space abbrev)
│   ├── Supp (character support)
│   ├── CF_subset (A-restricted class functions)
│   ├── VirtualCharacter (Z[Irr G])
│   ├── inertia_group (I_G(θ))
│   ├── conjugateCharacter (θ^g)
│   ├── TI_subset (Trivial Intersection)
│   ├── pointed_set (A^#)
│   └── other notations
└── Lemma + abbrev-only (no proof-heavy statements)
```

### 5.2 Lean スタイル規約

**ファイル構成**:
1. Module header + docstring (§1, §2 の目的説明)
2. Import: mathlib, Phase 1 Isaacs 基本定義
3. namespace OddOrder.Peterfalvi
4. docstring-only section (§1 内容説明)
5. Notation definition section
6. Helper abbrev / def (supp, TI-subset など)
7. end namespace

**Notation**: `notation "CF" => ClassFunction G ℂ` など. 括弧込み `"CF("` も許容.

**既存 mathlib との競合**: `Irr, Ind, Res` は既存. Peterfalvi 版ノーテーション (`Irr(G)` subscript など) との **dual notation** を用意 (Lean 優先順はまず既存 mathlib, fallback として Peterfalvi variant).

### 5.3 形式化スケジュール

- **Phase 2b の初日**: 本ファイルの skeleton + notation definitions を完成
- **§3-§8 並行化**: Notation ファイルが完成していれば、§3 (preliminary) は即座に着手可能
- **§9-§16 後続**: §3-§8 の Dade + Coherence 定義が in-scope なら、最大部分群 (§10-§16) 着手可能

---

## 6. Phase 2b 形式化着手順

### Group A: Notation + §1-§2 (即座可)
1. **本ファイル作成** (`S01S02_IntroductionNotation.lean`) — **当面タスク**
2. notation definitions の Lean 移植 (3-5 時間)

### Group B: §3 Preliminary (Phase 1 Ch.3-7 完成後)
1. **04.3_*.mmd 抽出** → Lean `(1.1)-(1.10)` 形式化
2. Isaacs Ch.3-7 の re-expose +補強

### Group C: §4-§8 Dade + Coherence (§3 完成後)
1. **04.4-04.8 抽出** → Lean `(2.1)-(6.4)` 形式化
2. **新規概念**: `DadeIsometry` (§4), `Coherence` (§7-§8)
3. Per-section ノート: `s04_dade_isometry.md`, `s07_coherence.md` 等

### Group D: §9 非存在定理 (§3-§8 + BG App.C 完成後)
1. **04.9_*.mmd 抽出** → Lean `(7.1)-(7.6)` = **BG App.C Theorem C**
2. Frobenius family の character-theoretic 非存在

### Group E: §10-§16 構造分析 (§9 + BG §10-§16 完成後)
1. **04.10-04.16_*.mmd 抽出** → Lean `(8.1)-(14.11)` 形式化
2. BG Type I-V classification を input に、指標論で最終詰め
3. §15 (S, T) が最大規模 (365 行)

---

## 7. 未解決・TODO

| 項目 | ステータス | 対処 |
|---|---|---|
| [HB] Theorem 12.4 の正確な番号確認 | TBD | BG 本文 or mathlib で確認 |
| [H] Satz 8.18 の Lean 相当物 | TBD | Phase 2b §3-§11 で必要なら個別確認 |
| mathlib `Character` API (Irr, Ind, Res) の最新ドキュメント | TBD | mathlib 4.x docs で確認 |
| `CF(G, A^#)` (non-identity support) の mathlib location | TBD | `ClassFunction.support` + filter |
| Galois automorphism χ^σ の実装方式 (Problem 2.2 Isaacs) | TBD | Phase 2b §3 χ-value handling |
| BG App.C ↔ Peterfalvi §9 の定理対応 (Lemma C.1, C.2 vs (7.2)-(7.6)) | TBD | §9 detailed section note で詳述 |

---

## 参考資料

- **[FT]** Feit, Thompson. _Solvability of Groups of Odd Order_, Pacific J. Math. 1963
- **[BG]** Bender, Glauberman. _Local Analysis for the Odd Order Theorem_, LMS LNS 188, 1994
- **[Is]** Isaacs, I.M. _Character Theory of Finite Groups_, AMS Chelsea, 1976
- **[Pe]** Peterfalvi, T. _Character Theory for the Odd Order Theorem_, LMS LNS 272, 2000
- **[HB]** Huppert, B., Blackburn, N. _Finite Groups_ I-III, Springer, 1982-
- **[H]** Huppert, B. _Endliche Gruppen_ I-II, Springer, 1967-

---

**作成日**: 2026-05-22  
**プロジェクト**: odd-order (Lean 4 形式化)  
**Phase**: 2b pre-launch (§1-§2 context + notation unification)

---

## 8. 指標論における記号体系の言語学的背景

### 8.1 Peterfalvi vs. Isaacs の記号差異

Peterfalvi が [Is] (Isaacs 1976) を前提とする中でも、いくつかの記号体系で異なる慣例を採用している:

#### (a) Inertia Group: I(θ) vs. Stabilizer

- **Isaacs (Ch.6)**: `I(θ)` — inertia group の一般的表記. "H は normal, θ ∈ Irr(H) に対して I(θ) = { g ∈ G | θ^g = θ }"
- **Peterfalvi (§2)**: `I_G(θ)` — superscript G で上位群を明示. **特に重要** (§4-§5): 最小反例 G に対して複数の部分群 H が出現するため、どの群での inertia かを明確化.

**形式化への示唆**: mathlib `Subgroup.stabilizer` で既存実装があるが、character-specific `inertiaGroup` として wrap する. 記号は `I_G(θ)` を優先.

#### (b) Restriction/Induction: Res vs. Res|_H

- **Isaacs**: χ|_H, χ^G (上付き/下付き)
- **Peterfalvi**: `Res^G_H(χ)`, `Ind^G_H(ψ)` — 関数記号で明示的

**形式化**: Peterfalvi スタイルを採用 (より機械的に形式化可能).

### 8.2 Virtual Character の二重役割

Peterfalvi §2 では **仮想指標 = Z[Irr G]** を **単なるアーベル群** として扱うが、§4-§6 では **等距写像の domain/codomain** として **inner product を保持する加群** として扱う.

```
仮想指標 (Z[Irr G]) の層:
  Tier 1: Z-module (R-algebra structure なし)
  Tier 2: inner product space (Hilbert space over ℤ? modulo norm finite)
  Tier 3: Dade isometry (特定部分群への制限で等距写像)
```

**形式化上の注意**: `Module.Dual ℤ (CF G)` vs `Submodule ℤ (CF G)` の区別. Peterfalvi 4-8 では後者が正確.

### 8.3 Support と Supp: 字面 vs. 実装

Peterfalvi (§2 line 13):
```
Supp(φ) = { x ∈ G | φ(x) ≠ 0 }
```

vs. Lean standard support:
```
support f := { x | f x ≠ 0 }ᶜᶜ  (closure in topological sense)
```

Character に対しては topological closure が無いため、両定義は一致. ただし generic class function では注意が必要.

**形式化**: Character 特化バージョン `charSupport` を定義し、無駄な closure を避ける.

### 8.4 TI-Subset: 定義の等価性

Peterfalvi (§2 line 29):
```
A is TI in G  ⟺ ∀ g ∈ G:  A^g = A  or  (A^g ∩ A = ∅)
```

vs. 同値な言い方:
```
A is TI in G  ⟺ ∀ g, h ∈ G:  g ≠ h  ⟹  A^g ∩ A^h ⊆ {1}
```

**形式化**: どちらでも実装可だが、後者が計算効率的 (conjMul の分解).

---

## 9. Phase 2b 並行化: Dependency DAG

```
Phase 1 Ch.1-7 (Isaacs 完成)
    ↓
§1-§2 (notation + context, 即座)
    ↓
┌─── §3 (preliminary, Ch.3-7 input)
│      ↓
│    ┌─ §4-§6 (Dade isometry, TI-subset)
│    │   ├─ char-theoretic tool bag
│    │   └─ new concepts
│    │      ↓
│    └─ §7-§8 (coherence theorems)
│           └─ extend §4-§6
│              ↓
│            §9 (non-existence Frobenius type)
│               ↓
│            BG App.C (parallel)
│               ↓
├─────────────────────────────────────┐
│ BG §1-§16 (Phase 2a output)          │
│   ↓                                  │
│ §10-§16 (type analysis via BG)      │
│   ├─ §10 (Type I-V definition)      │
│   ├─ §11-§14 (maximal subgroups)    │
│   ├─ §15 (S, T subgroups, 365 行)   │
│   └─ §16 (non-existence of G)       │
│      ↓                              │
└─ FT complete (Phase 4)
```

**Critical path**: §3 → (§4-§6 || §7-§8) → §9 → (§10-§14 || BG §10-§16) → §15 → §16

**Slack なし**: 全ルートが sequential. ただし BG (Phase 2a) と並行化できるため、Wall-clock 時間は短縮可能.

---

## 10. Peterfalvi 記号と BG 記号の cross-reference

BG (Phase 2a) と Peterfalvi (Phase 2b) で共通の record/namespace を使う際の対応:

### 10.1 BG §1 — Peterfalvi §3

| BG | Peterfalvi | 内容 | Lean location |
|---|---|---|---|
| [BG] Thm 1.8 | (1.1) 재述 | Burnside operator | `OddOrder.BG.S01.thm_1_8` 참조 |
| [BG] Prop 1.5, 1.6 | (1.2)-(1.3) | Hall π-subgroup | `OddOrder.BG.S01.prop_1_5` 참조 |
| [BG] Thm 1.13 | (1.4) | Thompson critical | `OddOrder.BG.S01.thm_1_13` 참조 |
| [BG] Thm 1.17 | (1.5) | Focal subgroup | `OddOrder.BG.S01.thm_1_17` 참조 |

### 10.2 BG App.C — Peterfalvi §9

| BG App.C | Peterfalvi §9 | 내용 |
|---|---|---|
| Theorem C | (7.1)-(7.3) | Frobenius 形の群非存在 |
| Lemma C.1 | (7.4) | 補助補題 |
| Lemma C.2 | (7.5)-(7.6) | 最終導出 |

**형식화 strategy**: `OddOrder.Peterfalvi.S09` module で BG App.C 결과를 wrap. `open OddOrder.BG.AppC` で import 側에서 参照.

### 10.3 BG §16 — Peterfalvi §10

| BG Theorem | Peterfalvi (8.1) | Type |
|---|---|---|
| Theorem A | Type I | G is of type I |
| Theorem B | Type II | G is of type II |
| Theorem C | Type III | G is of type III |
| Theorem D | Type IV | G is of type IV |
| Theorem E | Type V | G is of type V |

**形式化**: `OddOrder.Peterfalvi.S10.TypeI` など type-specific namespace で BG result を state として import.

---

## 11. Notation File の詳細実装アウトライン

### 11.1 Section 1: Imports + Namespace

```lean
import Mathlib.RepresentationTheory.Character.Basic
import Mathlib.RepresentationTheory.Character.Orthogonal
import Mathlib.Algebra.ModuleWithZeros
import OddOrder.Isaacs.Ch01_Basic  -- Phase 1 Isaacs
import OddOrder.BG.S01_Elementary  -- Phase 2a BG §1

namespace OddOrder.Peterfalvi

/-- 
  Part I: Character Theory for the Odd Order Theorem
  §1 Introduction + §2 Notation
  
  This section provides context and notation for the formalization of Peterfalvi's
  character-theoretic proof of the Feit-Thompson Theorem.
  
  - §1 (pp.1-2): Overview of FT proof strategy, dependencies on [BG], [Is], etc.
  - §2 (pp.3-4): Comprehensive notation dictionary for character theory
-/
```

### 11.2 Section 2: Class Function & Irreducible Character Abbrev

```lean
-- Class function space abbreviation
abbrev CF (G : Type*) [Group G] := ClassFunction G ℂ

-- Irreducible characters
notation "Irr" => Character.irr
notation "Irr(" => Character.irr  -- alt notation

-- Character support
def charSupport (φ : CF G) : Set G := { x | φ x ≠ 0 }
notation "Supp" => charSupport

-- Class functions supported in A
def CF_subset (G : Type*) (A : Set G) : Set (CF G) := 
  { φ | charSupport φ ⊆ A }
notation "CF(" => CF_subset
```

### 11.3 Section 3: Virtual Character

```lean
-- Virtual character space Z[Irr G]
def VirtualCharacter (G : Type*) [Group G] :=
  Submodule.span ℤ (Set.range (fun χ : Irr G => (χ : CF G)))
notation "𝒱" => VirtualCharacter
notation "Z[Irr" => VirtualCharacter  -- alt notation
```

### 11.4 Section 4: Restriction/Induction (wrap existing)

```lean
-- Restriction
notation "Res^" => ClassFunction.restrict
abbrev Res {G H : Type*} [Group G] [Group H] [Subgroup H] 
    (φ : CF G) : CF H := 
  ClassFunction.restrict H φ

-- Induction
notation "Ind^" => ClassFunction.induced
abbrev Ind {G H : Type*} [Group G] [Group H] [Subgroup H]
    (ψ : CF H) : CF G := 
  ClassFunction.induced G H ψ
```

### 11.5 Section 5: Character Conjugation & Inertia

```lean
-- Conjugate character θ^g
def conjugateCharacter {G : Type*} [Group G] {H : Subgroup G}
    (g : G) (θ : CF H) : CF H := 
  fun x => θ (g⁻¹ * x * g)

notation "^" => conjugateCharacter  -- context-dependent

-- Inertia group I_G(θ)
def inertiaGroup {G : Type*} [Group G] {H : Subgroup G}
    (θ : Character H) : Subgroup G :=
  Subgroup.stabilizer G (fun g : G => conjugateCharacter g θ)

notation "I(" => inertiaGroup
notation "I_" => inertiaGroup  -- alt: I_G(θ)
```

### 11.6 Section 6: TI-Subset & Pointed Set

```lean
-- Trivial Intersection subset
def TI_subset (G : Type*) (A : Set G) : Prop :=
  ∀ g : G, A.map (fun x => x ^ g) = A ∨ Disjoint A (A.map (fun x => x ^ g))

notation "TI(" => TI_subset

-- Pointed set A^#
abbrev pointed_set (A : Set G) : Set G := A \ {1}
notation "^#" => pointed_set
```

### 11.7 Section 7: Radical & Subgroup Structure

```lean
-- Fitting subgroup (wrap existing)
notation "F(" => Subgroup.fitting

-- Frattini subgroup (wrap existing)
notation "Φ(" => Subgroup.frattini

-- p-radical O_p(G) (wrap existing)
abbrev O_p (p : ℕ) (G : Type*) [Group G] :=
  Subgroup.pCore p G
notation "O_" => O_p

-- Fixed-point-free action
def acts_fixed_point_freely (H : Subgroup G) (G : Type*) : Prop :=
  ∀ h : H, h ≠ 1 → ∀ x : G, h • x = x → x = 1
```

### 11.8 Section 8: Close Namespace

```lean
end OddOrder.Peterfalvi
```

---

## 12. Lean 形式化の詳細チェックリスト

使用開始前に確認すべき事項:

- [ ] mathlib のバージョン確認 (4.x series)
- [ ] `ClassFunction`, `Character.irr` の exact signature
- [ ] `Subgroup.stabilizer` の conjugation action パラメータ化
- [ ] `inner_eq_zero_iff_orthogonal` など直交性の lemma 名
- [ ] `Submodule.span_eq_zero_iff` で virtual character の zero 判定
- [ ] BG Phase 2a formalization との namespace 互換性
- [ ] Isaacs Phase 1 との import order (circular dependency check)
- [ ] Lean 4 tactic (simp, norm_cast, ring など) の最新仕様

---

**作成完了**: 2026-05-22 / 16:30 JST  
**文字数**: 約 6500 (このセクション含む)  
**次ステップ**: 本ノートを参照して `S01S02_IntroductionNotation.lean` skeleton を Phase 2b 開始時に実装開始予定.
