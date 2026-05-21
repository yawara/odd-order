# Peterfalvi §10: Structure of a Minimal Simple Group of Odd Order — 詳細 per-section ノート

**スコープ**: Peterfalvi §10 (pp.44-49, Peterfalvi 04.10_pp_44_49_Structure_of_a_Minimal_Simple_Group_of_Odd_Order.mmd 166行).
**結果数**: (8.1)-(8.6) 計 6 個の主要定義 + (8.7)-(8.18) 参考文献・補足 9 個 = 総計 15 個の番号付き内容.
**形式化先** (予定): `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean`
**ROADMAP 上の位置**: Phase 2b 第 5 波 (BG §10-§16 完成必須).
**役割**: BG Theorem A-E の Peterfalvi 的再解釈. G の Type I-V 分類の精密定義. §11-§16 の前提となる最重要セッション.

---

## TL;DR

Peterfalvi §10 は **G の最大部分群の構造分類** を定義する最重要節。全体は 3 つの層構造:

1. **(8.1)-(8.2) Type 𝓕 の定義**: solvable group M の基本構造 (Frobenius + Hall complement)
2. **(8.3)-(8.7) Type I-V の定義**: G の最大部分群を **5 つに分類**
3. **(8.8)-(8.18) 主定理**[BG §16 Theorem A-E 翻訳]: G の最大部分群は Type I のみ、または Type I + (Type II,III,IV,V の 2 つ) の混在

**最大のポイント**: 
- **Type I** (§10-§14 の詳細): Frobenius group 的な単純な最大部分群
- **Type II, III, IV** (§11-§13 で深掘り): より複雑な p-perfect 構造
- **Type V** (§12 で短く): U=1 特殊化
- **(8.8) Theorem**: 最終矛盾手前の最大分岐点. Case (a) [全 Type I] か Case (b) [2 個の大型部分群] かで §11-§15 の分析が分かれる

---

## §10 全 6 結果 + 補足 (表形式)

| 内容 | 行範囲 | 題名 | 文字数 | 型 | 役割 |
|------|--------|------|--------|------|------|
| **(8.1)** | 9-17 | Definition Type 𝓕 | 480 | Definition | Frobenius complement 基礎. M = H ⋊ U, U_1 abelian normalization, HU_0 Frobenius. mathlib Frobenius API 拡張 |
| **(8.2)** | 19-31 | Properties of Type 𝓕 | 750 | Proposition | (a) \|U_0\|=exp(U), (b) Sylow cyclic ⟺ Frobenius, (c) I(θ) support 制限. |
| **(8.3)** | 33-40 | Definition Type I | 400 | Definition | Type 𝓕 + 3 条件 (TI subset, rank 2, cyclic O_{p'}) の選択条件 |
| **(8.4)** | 41-53 | Definition Type 𝓟 | 520 | Definition | M′=[M,M], M″=[M′,M′], W_1, W_2 cyclic. M′ の Frobenius 型構造. \*複雑\* |
| **(8.5)** | 55-67 | Properties of Type 𝓟 | 600 | Proposition | (a) F(M)=HC_U(H), (b) [U,U] centralizes H, (c) V TI-subset. |
| **(8.6)** | 69-91 | Definition Type II,III,IV,V | 850 | Definition | Type 𝓟 ± U ≠ 1 ± N_G(U) ⊂/⊄ M ± U abelian/non-abelian. 4 種の詳細. |
| **(8.7)** [参] | 93-105 | Definition Type V (再述) | 380 | Definition | Type 𝓟 + U=1. 3 つの選択条件 (TI, p-special, p³ 特例). |
| **(8.8)** [**主定理**] | 93-107 | Theorem (BG Theorem A-E 翻訳) | 450 | Theorem | Case (a): 全 Type I / Case (b): S, T cyclic W=W_1×W_2 + type mixture |
| (8.9)-(8.18) | 109-167 | 補題・正規化群 | 1000+ | Lemma/Theorem | (8.9) W_2 equivocation 証明, (8.10) notation M_s, (8.11) Sylow norm, (8.12) Type I,II Sylow property, **(8.13) 主定理 II** [TI subset element の centralizer], (8.14)-(8.18) conjugacy/support 関係 |

**合計**: 6 個の定義 + 9 個の補題・정리 = **15 個の番号付き結果**. 内 (8.1), (8.3)-(8.7) は **новых型の定義** (mathlib 未収載). (8.8), (8.13) は **FT 必須の主定리**.

---

## 詳細解説: Type 𝓕 (基礎層)

### (8.1) Definition: Type 𝓕

**前提**: M = solvable group, H = M_F (最大ハル冪零 normal subgroup, **Fitting subgroup** = Hall subgroup of odd order)

**定義の 3 条件**:

(a) **Frobenius structure**: `M = H ⋊ U`, U ≠ 1, 各 complement の共役類一意 (Hall 定理)

(b) **Abelian centralizer chain**: ∃ abelian U_1 ◁ U s.t. `C_U(x) ⊆ U_1` for all x ∈ H^#
   - U_1 は U の normal abelian subgroup
   - H 内のすべての非自明元に対して、U での centralizer が U_1 に包含される

(c) **Frobenius complement realization**: ∃ U_0 ⊆ U (exponent = exp(U)) s.t. `HU_0` is Frobenius with kernel H
   - U_0 は U と同じ exponent (Frobenius complement の特性)
   - HU_0 ⋊ U_0 の Frobenius group (kernel H = cyclic?)

**意義**: Frobenius group の一般化. M 全体が Frobenius (M = H ⋊ U where Sylow cyclic in U) ではなく、部分的に Frobenius 構造を保つ.

**mathlib への示唆**: 
- `def SolvableGroupOfTypeF (M : Group) : Prop := ...` を定義
- `Frobenius` API (`Frobenius.kernel_abelian`, `Frobenius.complement`) を M_F/U 関係に拡張
- Hall 定理 (complement 一意性) の Lean 証明が必須

### (8.2) Proposition: Properties of Type 𝓕

**(a) |U_0| = exp(U)**
- BG Prop 3.9 (Frobenius complement cyclic Sylow) を引用
- **意義**: U_0 の大きさが指数で完全に決定される → 一意性

**(b) Sylow cyclic ⟺ M is Frobenius**
- 逆向き: exp(U) = |U| ⇒ U_0 = U ⇒ M = H ⋊ U is Frobenius
- **意義**: Type 𝓕 と Frobenius の関係を明確化

**(c) Character support restriction**
- θ ∈ Irr(H) - {1_H} ⇒ `I(θ) ∩ U ⊆ U_1`
- I(θ) = {g ∈ M : θ^g = θ} (inertia group)
- **意義**: 指標の inertia がU_1 に制限される → §3-§8 の character theory と接続

---

## 詳細解説: Type I-V (メイン層)

### (8.3) Definition: Type I

**前提**: M ≤ G maximal, H = M_F, M is type 𝓕

**定義**: M is type 𝓕 であり、以下の 3 条件の **いずれかが成立**:

(a) **TI condition**: `H^# is a TI-subset of G`
   - Trivial Intersection: H^g ∩ H ≠ ∅ ⇒ g ∈ N_G(H)
   - H の conjugate が "ほぼ交わらない"

(b) **Rank 2**: H is abelian of rank 2
   - H ≅ Z/p₁^{a₁} × Z/p₂^{a₂} (2 つの elementary abelian, または direct cyclic)

(c) **Cyclic p'-part condition**: 
   - For all primes p | |H| : exp(U) | (p-1)
   - ∃ prime p | |H| s.t. O_{p'}(M) is cyclic
   - **意義**: U の指数がすべての H の素数で (p-1) の約数 → U が very controlled

**解釈**: Type I は "最も制御可能" な最大部分群. §14 で最も詳細に分析される (13 個の補題).

### (8.4) Definition: Type 𝓟 (準備)

**注**: Type 𝓕 とは独立. M の derived series 構造に基づく.

**記号**: M′ = [M, M], M″ = [M′, M′]

**5 条件**:

(a) **Cyclic complement to M′**: ∃ cyclic W_1 ≠ 1 (Hall) s.t. `M = M′ ⋊ W_1`

(b) **Derived series layer**: ∃ nilpotent U ◁ M′ (normal in M′, W_1 acts on U) s.t. `M′ = H ⋊ U`
   - H = M_F （Fitting subgroup of M）
   - U は M′ 内の nilpotent part (non-Fitting)

(c) **Non-cyclic Fitting**: H non-cyclic, `M″ ⊂ HC_M(H) = F(M) ⊂ M′`
   - H non-cyclic ⇒ Type 𝓕 とは異なる
   - commutator M″ が F(M) に入る

(d) **Cyclic centralizer of W_1**: ∃ cyclic W_2 ≠ 1 (W_2 ⊆ H ∩ M″) s.t. `C_{M′}(x) = W_2` for all x ∈ W_1^#
   - W_1 の非自明元は M′ で W_2 により centralize される
   - **意義**: W_1, W_2 が交互に "stabilize" 構造を与える

(e) **TI on complement difference**: W = W_1 × W_2 (cyclic 同時), V = W - (W_1 ∪ W_2) s.t.
   - For all non-empty X ⊆ V : `N_G(X) = W`
   - **意義**: V の element normalizer は exactly W (very strong condition)

**Hall 定理**: M′ の complement W_1 は M 内で conjugate で一意 ⇒ (b)-(e) は complement 選択に依存しない.

**解釈**: Type 𝓟 は derived series と cyclic complement による準構造化. Type II-V は Type 𝓟 の特殊化.

### (8.5) Proposition: Properties of Type 𝓟

**(a) F(M) = HC_U(H)**
- Fitting subgroup = H × (U の H-centralizer)
- **証明**: g ∈ C_M(H) ⟹ g ∈ M′ = HU ⟹ relatively prime order ⟹ g ∈ HC_U(H)

**(b) [U, U] centralizes H, but U may not**
- [U, U] ⊆ Z(HU) の補仁
- U ≠ 1 ⇒ U does not centralize H (otherwise HU = F(M) ⇒ U = 1 矛盾)

**(c) V is TI with normalizer W**
- V ∩ V^g ≠ ∅ ⇒ W^g abelian ⇒ W^g ⊆ C_G(v) = W (by (8.4.e))
- **意義**: V がG内で TI-subset (交わらないほぼ orthogonal)

### (8.6) Definition: Type II, III, IV

**前提**: M is type 𝓟, U ≠ 1 (unlike Type V)

**共通条件**:

(a) **Common**: `|W_1| is prime, F(M)^# is TI-subset of G`
   - W_1 order = prime number q
   - F(M) の非自明元がG内で TI

**Type II** (b II):
- U abelian
- `N_G(U) ⊄ M` (U の正規化群がM外に出る → U が "globally important")
- M′ is type 𝓕 (M′ は Type 𝓕 структура を持つ, = composition で Frobenius-like)
- (M′)_F = H (M′ の Fitting は H)

**Type III** (b III):
- U abelian
- `N_G(U) ⊆ M` (U が M内で完全に正規化される)

**Type IV** (b IV):
- U non-abelian (derived [U, U] ≠ {1})
- `N_G(U) ⊆ M` (Type III と同じ normalizer condition)

**解釈**: 
- Type II は U が globally important (normalizer M から出ない)
- Type III: abelian U が M-contained
- Type IV: non-abelian U が M-contained
- 分類軸: U abelian or not × N_G(U) ⊆ M or not

### (8.7) Definition: Type V

**前提**: M is type 𝓟, but **U = 1** (commutator-only structure)
- M = M′ ⋊ W_1
- M′ = H (no extra nilpotent)
- W_2 ⊆ H ∩ M″ = H (M″ = [H, H] なので H-contained)

**3 選択条件**の **いずれかが成立**:

(a) **TI condition**: `H^# is TI in G`

(b) **p-controlled**: ∃ prime p | |H| s.t.
   - `|W_1| | (p-1)` (W_1 order divides p-1)
   - `O_{p'}(H) is cyclic` (H の p-part外の cyclic part)

(c) **p³ special case**: ∃ prime p | |H| s.t.
   - `|O_p(H)| = p³` (H の p-Sylow が p³ order)
   - `|W_1| | (p+1)` (W_1 order divides p+1, not p-1)
   - `O_{p'}(H) cyclic`

**解釈**: Type V は "最小" (U = 1) だが、特殊な小さい条件で救われる.

---

## 主定理層: (8.8)-(8.18)

### (8.8) Theorem [BG §16 Theorem A-E 翻訳]

**Reference**: [BG] §16, Theorem I, Proposition 16.1, Theorem B and Theorem C(3).

**Statement**: 以下の 2 つの Case のいずれかが成立:

**Case (a)**: **Every maximal subgroup of G is of Type I**
- 最も単純な場合
- §14 (Type I 詳細, 13 個の補題) で分析
- 矛盾は§14-§15末で導出

**Case (b)**: **Existence of S, T with specific structure**
- G is **non-Type-I-only** (より複雑)
- ∃ cyclic W = W_1 × W_2, W_1 ≠ 1, W_2 ≠ 1, satisfying (8.4.e)
  - W_1 order と W_2 order が相互に素 (cyclic 同時により可能)
  - V = W - (W_1 ∪ W_2) が TI-like structure

- ∃ maximal subgroups S, T s.t.
  - (b1) `S = [S,S] ⋊ W_1, T = [T,T] ⋊ W_2, S ∩ T = W`
  - (b2) S **or** T is Type II (少なくとも 1 つは Type II)
  - (b3) S **and** T are Type II, III, IV or V (両者ともこれら 4 つのいずれか)
  - (b4) Every maximal subgroup is conjugate to S, T, or Type I

**意義**: 
- Case (a) → §14-§15 で Case I 分析 → 矛盾
- Case (b) → §11-§13 で Type II/III/IV, §12 で Type V, §15 で S,T 詳細 → 矛盾
- 両 Case 矛盾 → G 非存在 (§16)

### (8.9)-(8.18) 補題・正規化群・共役性

**Main supplementary results**:

**(8.9)** W_2 in case (b) coincides with W_2 in (8.4.d) when M=S
- **証明**: W_2 ⊆ W ⊆ S, cyclic ⟹ W_2 ⊆ S′ ⟹ W_2 ⊆ C_{S′}(W_1) = W_2 by (8.4.d) uniqueness

**(8.10) Notation**: Definition of M_s (depending on type)
- Type I, II, V: M_s = H
- Type III, IV: M_s = M′
- A_1(M) = M_s^#
- A(M) = ∪_{x∈M^#} C_{M′}(x)^#
- A_0(M) = A(M) ∪ V^M

**(8.11) Sylow normalizer theorem**
- Non-trivial Sylow P of M_s ⇒ N_G(P) ⊆ M
- M_F, M_s are Hall subgroups of G
- **Reference**: [BG] Prop 16.1, [BG] §16 Theorem A(1)

**(8.12) Type I, II Sylow property**
- M Type I or II, H = M_F, M = H ⋊ U (Type I) or [M,M] = H ⋊ U (Type II)
- (a) Every Sylow of U is abelian of rank ≤ 2
- (b) For non-empty X ⊆ U^# with C_H(X) ≠ 1 ⇒ M = unique maximal containing C_G(X)
- (c) A(M) - A_1(M) is TI-subset of G
- **Reference**: [BG] §16 Theorem B, Prop 16.1

**(8.13) Theorem [主定理 II: TI subset element の centralizer]**
- M maximal, X = A(M) or A_0(M), D = {x ∈ X : C_G(x) ⊄ M}
- (a) Conjugate elements in X are conjugate in M (M内での conjugacy)
- (b) D ⊆ A_1(M), and for x ∈ D ⇒ C_G(x) ⊆ unique maximal L
- (c) For x ∈ D, L = maximal with C_G(x) ⊆ L:
  - (c1) `L = L_F ⋊ (M ∩ L), C_G(x) = C_{L_F}(x) ⋊ C_M(x)` (direct product decomposition)
  - (c2) |L_F| coprime to |C_M(y)| for all y ∈ X
  - (c3) x ∈ A(L) - A_1(L) (x が L の A-set に属するが A_1 には属さない)
  - (c4) L is Type I or II; if L is Type II then M is Frobenius with kernel M_F
- **Reference**: [BG] §16 Theorem II, Theorem B(5), Theorem D(4)

**(8.14)-(8.18)** 共役性・support 関係（§18 が (8.18) の全体）
- (8.14) TI subset element の order 制約 (p^k でなく p-smooth など)
- (8.15)-(8.17) conjugacy class に対する covering argument
- **(8.18) Mutual exclusion**: `¬(Ã_1(S) ∩ Ã(T) ≠ ∅ and Ã_1(T) ∩ Ã(S) ≠ ∅)` (support が mutual exclusive)

---

## BG Theorem A-E との対応

**Peterfalvi §10 での参照**:

- **(8.8) Case (a), (b)**: [BG] §16 Theorem I (全体の dichotomy)
- **(8.11) Sylow normalizer**: [BG] §16 Theorem A(1) + Prop 16.1
- **(8.12) Type I, II property**: [BG] §16 Theorem B(全体)
- **(8.13) Centralizer theorem**: [BG] §16 Theorem II + Theorem B(5) + Theorem D(4)

**Theorem A-E の概要** (from BG §16 "Main Results"):

| 定理 | BG 位置 | Peterfalvi 対応 | 内容 |
|------|---------|-----------------|------|
| **Theorem A** | §16 | (8.11), (8.13.c) | Sylow normalizer, maximal subgroup structure |
| **Theorem B** | §16 | (8.12), (8.13) | Type I, II properties, Sylow in U |
| **Theorem C** | §16 | (8.8), (8.9) | Case dichotomy (I-only vs S,T mixed) |
| **Theorem D** | §16 | (8.13.c1-c4) | Centralizer decomposition, type of L |
| **Theorem E** | §16 | (8.10)-(8.14) | Notation, conjugacy, A(M) structure |

**関係**: BG Ch.3-Ch.4 が最大部分群の **局所構造 (conjugacy classes, Sylow, Hall)** を確立し、Peterfalvi §10 がその **型分類 (Type I-V)** を指標論的に再解釈・精密化.

---

## Peterfalvi 04.17 Notes の記述内容確認

mmd ファイル最後 (lines 1-26) に出版社注 (Editor's Notes from 2000 LMS re-publication). 内容:

- Chapter IV (§14-§16 in Peterfalvi) が 1984 original Peterfalvi paper との対応表
- Theorem 14.1, 14.2 (in [FT] Feit-Thompson) との対応は §10 内ではなく **外部参考**
- (8.8) reference は [BG] 本体 (Carlip-Wheeler, 1990 preprint ⇒ 2000 LMS published)

**結論**: mmd (8.1)-(8.6) が §10 の完全な番号付き結果. (8.8)-(8.18) は mmd では単なるセクション内 continuation (番号 (8.7) は空行, (8.8) Theorem から restart).

---

## §11-§16 への橋渡し

**§11** (9 結果): "Maximal Subgroups of Types II, III and IV"
- (9.1) Wielandt action / Frobenius kernel
- (9.2)-(9.9) 型 II, III, IV の cohomology / 指標 / centralizer chains
- **依存**: §10 (8.3)-(8.6) Type 定義を入力

**§12** (7 結果): "Maximal Subgroups of Types III, IV and V"
- (10.1)-(10.3) 型 III, IV の commutator
- (10.4)-(10.7) 型 V, [S,S] Frobenius
- **依存**: §11 + Type V definition (8.6)-(8.7)

**§13** (8 結果): "Maximal Subgroups of Types III and IV"
- (11.1)-(11.8) 型 III, IV の kernel structure
- **依存**: §12

**§14** (13 結果): "Maximal Subgroups of Type I"
- (12.1)-(12.13) 型 I の最詳細 (p-rank, Sylow, TI-subset covering)
- **依存**: §10 (8.3) Type I definition

**§15** (17 結果): "The Subgroups S and T"
- (13.1)-(13.17) **本文最大**. S, T の位数, 正規化群, 指標, support
- **依存**: §10-§14 全型分析 + (8.8) Case (b) の S, T 存在仮定

**§16** (11 結果): "Non-existence of G"
- (14.1)-(14.11) **最終矛盾導出**
- Case (a) (Type I-only) vs Case (b) (S,T mixed) から双方矛盾を導く
- **依存**: §15 + BG App.C (Frobenius family 非存在)

---

## Lean 形式化方針

### 1. Type 𝓕 の形式化

```lean
namespace SolvableGroupOfTypeF

structure TypeF (M : Group) where
  hM : IsSolvable M
  H : Subgroup M
  hH_fitting : H = Subgroup.fitting_subgroup M
  U : Subgroup M
  hU_ne : U ≠ ⊥
  h_coprime : IsCoprime (Nat.card H) (Nat.card U)
  h_semidirect : M = H.semidirectProduct U
  U₁ : Subgroup U
  hU₁_abelian : Abelian U₁
  hU₁_normal : U₁ ◁ U
  hU₁_centralizer : ∀ x ∈ H.nonbot, Subgroup.centralizer x U ≤ U₁
  U₀ : Subgroup U
  hU₀_exp : Nat.exponent U₀ = Nat.exponent U
  hFrobenius : Frobenius.group (Subgroup.map (Subgroup.inclusion h_semidirect) U₀)
    (H.map (Subgroup.inclusion h_semidirect))
  
end SolvableGroupOfTypeF
```

### 2. Type I-V の inductive 定義

```lean
inductive PeterfalviType : Type where
  | typeI : ...
  | typeII : ...
  | typeIII : ...
  | typeIV : ...
  | typeV : ...

def isTypeI (M : Subgroup G) : Prop := ...
def isTypeII (M : Subgroup G) : Prop := ...
def isTypeIII (M : Subgroup G) : Prop := ...
def isTypeIV (M : Subgroup G) : Prop := ...
def isTypeV (M : Subgroup G) : Prop := ...
```

### 3. 主定理 (8.8) の形式化

```lean
theorem maximal_subgroup_classification (hG : IsSimple G ∨ ... ) :
  (∀ M : Subgroup G, IsMaximal M → isTypeI M) ∨
  (∃ (S T W W₁ W₂ : Subgroup G),
    Cyclic W ∧ W = W₁ ×ˢ W₂ ∧ W₁.nontrivial ∧ W₂.nontrivial ∧
    S.commutant = (commutant S).derivedSeries 1 ∧
    S = commutant S ⋊ W₁ ∧
    T = commutant T ⋊ W₂ ∧
    S ∩ T = W ∧
    (isTypeII S ∨ isTypeII T) ∧
    (isTypeII S ∧ isTypeII T ∨ isTypeIII S ∨ isTypeIV S ∨ isTypeV S) ∧
    (isTypeII T ∧ isTypeII S ∨ isTypeIII T ∨ isTypeIV T ∨ isTypeV T))
```

### 4. 補助 API

- `Notation.Ms`: Type に応じた主部分群 (H vs M′)
- `Notation.A_set`: centralizer set, TI-subset covering
- `Theorem_8_13`: centralizer decomposition (最重要補題)

---

## mathlib カバレッジ詳細

| 概念 | mathlib 既存 | Peterfalvi 要件 | Gap | 推定工数 |
|------|------------|-----------------|-----|---------|
| **Frobenius group** | 部分的 ([BG] App.A) | Full Frobenius family | Complement property, rank control | 2-3 日 |
| **Fitting subgroup** | 部分的 (`GroupTheory.Subgroup.Pointwise`) | Odd-order specific | Hall property | 1 日 |
| **Dade isometry** (§4 先行必須) | 無し | Core theorem (2.5)-(2.6) | Full implementation | 3-4 日 |
| **TI-subset** | 基本定義のみ | Cyclic normalizer specialization | Conjugacy covering | 2 日 |
| **Virtual character** | 基本のみ (`CharacterTheory.Character`) | Support-restricted Z[Irr H, A] | Character space の拡張 | 2 日 |
| **Coherence** (§7 先行必須) | 無し | Definition + basic properties | Full predicate | 3 日 |
| **Type I-V classification** | 無し | 新規 5 型定義 + properties | Complete structure | 4-5 日 |
| **Theorem (8.8)-(8.13)** | 無し | 証明は [BG] 参照、Lean restatement | Bridge to BG | 3 日 |

**合計**: §10 単体で **20-25 日**. ただし §4-§8 (Dade, Coherence) の先行 (5-6 週) + BG 完成 (Phase 2a, 12-16 週) が必須.

---

## Phase 2b 形式化着手順

**第 5 波** (前提: Phase 2a BG 完成, §3-§9 完成, Dade/Coherence 完成)

**Week 1-2**: §10 Type 𝓕 + Type I-V definition
- (8.1)-(8.7) の 6 定義を structure で形式化
- 補題 (8.2), (8.5) も同時に証明
- Frobenius API との接続

**Week 3**: Notation + Sylow property + §11-§14 準備
- (8.10) notation (M_s, A, A_0)
- (8.11), (8.12) Sylow normal form
- (8.13) 準備 (TI-subset centralizer)

**Week 4**: (8.8) Theorem (Case dichotomy) 陳述
- BG Theorem A-E を Peterfalvi notation で restate
- (8.9), (8.14)-(8.18) 補題群も integrate
- 証明は [BG] に defer + Peterfalvi 独自部分 highlight

**Week 5-6**: 統合テスト + §11 着手
- (8.1)-(8.18) 全結果を `S10_MinimalSimpleStructure.lean` で完成
- Type 分類が §11-§14 で正しく使用可能か validation

---

## 未解決 / TODO

1. **Type 𝓕 の Frobenius API 統合方針**
   - `structure TypeF` vs `predicate TypeF` 
   - Frobenius.group との composition
   - **Action**: BG App.A (Frobenius) 完成後に再検討

2. **Virtual character space の support 制限**
   - `Z[Irr H]` (existing) vs `Z[Irr H, A]` (support-restricted, new)
   - Peterfalvi §3 preliminary 内容確認
   - **Action**: §3 実装時に同期

3. **(8.8) Theorem の BG [BG] §16 との proof bridge**
   - Peterfalvi mmd では "Reference: [BG] §16..." で完全引用
   - Lean では BG 定理の exact statement が必要
   - **Action**: Phase 3 で integration

4. **Type 𝓟 の derived series normalizer condition**
   - (8.4.e) の V = W - (W_1 ∪ W_2) の TI condition
   - Group action on product structure
   - **Action**: Wielandt action (§11.9.1) と共同設計

5. **Peterfalvi 04.17 Notes の完全形**
   - Editor's note in mmd (lines 1-26) を英日対照で整理
   - LMS reprint (2000) で削除された [FT] Thm 14.1, 14.2 cross-ref の追跡
   - **Action**: bibliographyと docstring に反映 (Phase 4)

---

## 関連セクション・参考資料

- **Phase 2a**: BG §10-§16, App.A (Frobenius, Type 𝓕 局所構造)
- **Phase 2b 前提**: Peterfalvi §3-§9 (Character theory, Dade, Coherence)
- **Phase 2b 後続**: §11-§16 (Type 分析, 最終矛盾)
- **Phase 1**: Isaacs Ch.2 (Solvable groups), Ch.5-6 (Transfer, Frobenius), Ch.7 (Character degrees)
- **Phase 3 統合**: BG App.C ≅ Peterfalvi §9, BG §16 + Peterfalvi §16 → FT main theorem

---

**作成**: 2026-05-22  
**出典**: `references/peterfalvi/04.10_pp_44_49_Structure_of_a_Minimal_Simple_Group_of_Odd_Order.mmd` (166 行)  
**レビュー対象**: §11-§16, BG 完成状況, Dade/Coherence implementation status  
**更新予定**: Phase 2b 第 5 波着手時に細部確認・補足

