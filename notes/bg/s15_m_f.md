# BG §15: The Subgroup M_F — mini-roadmap

> ## ⚠ 現状 (2026-06-20、以下の「予定」記述に優先)
> 本ノートは **着工前の調査・計画段階** (「形式化先(予定)」) の記述で、実装は大きく先行している。
> `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean` は **~6000 行・実在** (lane-f 所有)。
> **Theorem 15.2 (M_F 構造) は step-1〜step (c)/(d)/3 まで sorry-free 構築済**
> (`isTypeP1_of_mf_ne_msigma` / chief-factor engine / prime-manner / `hsecFit` C-interface /
> `card_centralizer_quotient_eq_of_kstar` / M_σ/Q nilpotent / Q=O_q(M) Sylow / K-invariant complement D)。
> **更新 (2026-07-02)**: **Theorem 15.2 は完全証明済** (wrapper gate `Q0⊴M` も解消)。S15_MF の残
> sorry = **15.8 `tau2_transfer_constraint` / 15.9 `centralizer_escape_final_local` の 2 点のみ**
> (off-spine deep char = memory [[ft-settled-findings]])。⚠ 以下の pointer は dead:
> memory [[ft-endgame-two-poles]] は現存せず、issue 8012 は closed、issue 7007 も本日
> (2026-07-02) close。
> (旧記述 2026-06-20: 「残 = wrapper gate `Q0⊴M` 1 点。live 状況は issue 8012 が正本、
> 全体地図は [`../meta/ft_master_roadmap_2026_05_29.md`](../meta/ft_master_roadmap_2026_05_29.md) 冒頭 2026-06-20 ヘッダ」)
> 巨大化 (>1500 行) につき split issue [0071](../../issues/0071-s15-mf-split.md) が capstone 後分割を追跡。
> 以下は当初計画 (歴史的参考) ↓

**スコープ**: BG §15 (pp.117-122), mmd L4086-4255, 9 結果.
形式化先 (予定): `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean`
ROADMAP 上の位置: **Phase 2a 第 5 波** (§14 完成必須, §16 直前)
役割: **M_F (Fitting-related maximal subgroup)**、§16 Main Results への橋渡し、Peterfalvi §15 (S, T) との対応

---

## TL;DR

§15 は Fitting subgroup F(M) とその関連部分群 M_F (maximal normal nilpotent Hall subgroup) の構造を分析する短章。§14 の "type 𝒫" に基づき、**M_F ≠ M_σ のとき何が成立するか**を詳細に解析。§16 の Main Theorem への橋渡しで、特に Theorem 15.2 が中核（type 𝒫₁ への特徴付けと Fitting subgroup の分解）。

**形式化難度**: 中程度（§14 を使用するが、§12-§13 の複雑な構造論は直接不要）
**mathlib カバレッジ**: low（Fitting subgroup 基本は既存だが、局所解析的な characterization は新規）

---

## §15 全 9 結果（一覧表）

| # | 結果名 | 型 | 主要命題 | 証明手段 | FT 経路 |
|---|--------|-----|---------|---------|--------|
| 15.1 | Lemma 15.1 | Lemma | 5 部分: UM_σ ⊴ M, K cyclic, M_σ ⊆ M', M'/M_σ abelian など | §14.7, §12, §10.2 参照 + Thm 12.12 再利用 | ◯ |
| 15.2 | Theorem 15.2 | Thm | M_F ≠ M_σ ⟹ type 𝒫₁, F(M) 分解, Q ⊴ M | Prime action, Thm 3.7, 3.8, Prop 1.5, 14.2 | ☆ |
| 15.3 | Corollary 15.3 | Cor | Hall subgroup のentralizer + 共役性 | §14.2, 14.4, Frattini |  ◯ |
| 15.4 | Corollary 15.4 | Cor | Nilpotent Hall subgroup の埋め込み | 15.3(a) から直接 | △ |
| 15.5 | Corollary 15.5 | Cor | F(M) = C_M(H)H = F(M_σ) × Y | Y = cyclic τ₂(M)-subgroup | ◯ |
| 15.6 | Corollary 15.6 | Cor | M ∈ ℳ_𝒫 ⟹ K* nonidentity cyclic, M_F not cyclic | Lemma 15.1(b), Thm 14.7(h), Lem 6.3 | ◯ |
| 15.7 | Theorem 15.7 | Thm | F(M) not TI ⟹ 3 subcase: M ∈ ℳ_𝓕 or ℳ_𝒫₁, E structure | §12-13 subgroups E, 条件分岐 | ☆ |
| 15.8 | Theorem 15.8 (FT 1991) | Thm | τ₂(H) ≠ ∅ ⟹ τ₂(M) = ∅, τ₂(N) = {q} | App.C（最終矛盾）への鍵 | ☆ |
| 15.9 | Corollary 15.9 | Cor | x ∈ M_σ#, N ∈ ℳ(C_G(x)), N ∉ ℳ_𝓕 ⟹ 3 部分 | 15.8 + 14.12 活用 | ☆ |

**合計**: 9 結果（Lemma 1 + Theorem 2 + Corollary 6）

---

## M_F の定義と性質

### 形式的定義（§15 序文）

M を G の maximal subgroup とするとき、
- **M_F** := M の最大 normal nilpotent Hall subgroup
- **言い換え**: M_σ（normal Sylow subgroup の積）のうち、nilpotent な最大部分群（F(M) の central extension 部分）

**重要**: M_F は次のいずれかの場合に分かれる：
1. **M_F = M_σ**: M_σ自体が nilpotent（この場合、M は "type ℱ"、cf. §14）
2. **M_F ⊂ M_σ**: M_σ が non-nilpotent（この場合、M は必ず "type 𝒫₁"）

### Lemma 15.1: UM_σ ⊴ M の構造

**主張** (5 部分)：

(a) **UM_σ ⊴ M**, K cyclic, **M_σ ⊆ M'**, **(M'/M_σ) abelian**
   - 証明: §14.7(d), (h) + §12.10(b) + §10.2(c) 組み合わせ
   - **意味**: K（κ(M)-Hall subgroup）がないなら M は Frobenius group 的；あっても M' 構造は predictable

(b) **K ≠ 1 ⟹ M' = UM_σ, U abelian**
   - **意味**: complementary structure 確立

(c) **X ⊆ U nonidentity, C_{M_σ}(X) ≠ 1 ⟹ ℳ(C_G(X)) = {M}, X は cyclic τ₂(M)-subgroup**
   - **Application**: §15.7 で X = F(M) ∩ F(M)^g のときに再利用

(d) **⟨C_U(x) | x ∈ M_σ#⟩ abelian**
   - **技巧**: U の centralizer sublattice が可換

(e) **U ≠ 1 ⟹ ∃ U_0 (= exp(U)) s.t. U_0M_σ は Frobenius group, kernel M_σ**

---

## Theorem 15.2: M_F ≠ M_σ のときの characterization

### 主張（最重要）

**M_F ≠ M_σ** と仮定すると、自動的に **M は type 𝒫₁**（K ≠ 1, U = 1）となり、以下が成立：

(a) **M = KM_σ** (type 𝒫₁ の特徴付け)

(b) **p = |K|, q = |K*| はともに素数、q ∈ π(M_F) ∩ β(M)**
   - K* := C_{M_σ}(K)（K の centralizer in M_σ）
   - β(M) = {primes q : |O_q(M)| > 1 ∧ O_q(M) not cyclic}（"bad" prime）

(c) **Q := O_q(M) ⊴ M** (normal Sylow q-subgroup)

(d) **D (complement of Q in M_σ = M') は nilpotent**

(e) **Q_0 := C_Q(D) ⊴ M** (normal subgroup of M)

(f) **Q̄ = Q/Q_0 は minimal normal in M/Q_0, elementary abelian of order q^p**

(g) **M'' = (M_σ)' ⊆ F(M) = QC_M(Q) = C_M(Q̄) = C_{M_σ}(K̄*)** かつ **M_σ = M'**

### 証明構造（概要）

1. **Lemma 14.1** により M_σ が non-nilpotent であることを確認 ⟹ type ℱ でない
2. **Prop 14.2(a)** で K が M_σ に prime に作用することを使用
3. **Lem 6.3(a)** で [M_σ, K] = M_σ を導出
4. **Thm 3.8** で K* ∩ F(M) ≠ 1 ⟹ K* ⊆ O_q(M)
5. **Prop 1.5(d)** で K が M_σ/Q に regular に作用 ⟹ **Thm 3.7** で M_σ/Q は nilpotent
6. **後半**: Q_0, Q_1 の nested normalizer argument で Q̄ の minimal normality を確立
7. **Thm 3.10** (Frobenius group action) で |K| = p（素数）, |Q̄| = q^p の出現

**鍵となる補題**:
- **Thm 3.7** (p-soluble group, cyclic action on nilpotent): 作用が regular ⟹ 核が nilpotent
- **Thm 3.8** ([X, Y] ⊄ F(X) ⟹ X* ∩ F(G) ≠ 1): FT 局所論の基本
- **Prop 1.5** (A-invariant Hall system): 構造を保つ complement の存在

---

## §14 (Type 𝒫) との関係

§14 (Maximal Subgroups of Type 𝒫 and Counting) では、maximal subgroup M を **3 つに分類**：
- **Type ℱ** (ℳ_𝓕): M_σ が nilpotent
- **Type 𝒫₁** (ℳ_{𝒫₁}): K ≠ 1, U = 1（つまり M = KM_σ）
- **Type 𝒫₂** (ℳ_{𝒫₂}): K ≠ 1, U ≠ 1

**§15 Theorem 15.2** は次を述べる：
- **M_F = M_σ** ⟺ M_σ nilpotent ⟺ M ∈ ℳ_𝓕
- **M_F ⊂ M_σ** ⟹ M ∈ ℳ_{𝒫₁}（type 𝒫₂ は起こらない！）

**Corollary 15.6** (M ∈ ℳ_𝒫 のとき):
- K* = C_{M_σ}(K) は nonidentity cyclic
- K* ⊆ M_F ∩ M'' (Fitting subgroup と derived series の交点)
- M_F は not cyclic

これは **§14 の type 𝒫 counting** に精密な情報を提供。

---

## §16 (Main Results) への橋渡し

### Theorem 15.7: F(M) が TI でない場合

**最大級に重要な定理**（FT critical path の山場の一つ）。

**仮定**: F(M) is not a TI-subgroup of G
- つまり、∃g ∈ G - M s.t. X := F(M) ∩ F(M)^g is nontrivial

**結論**:

(a) **M ∈ ℳ_𝓕 ∪ ℳ_{𝒫₁}** and **H = M_F = M_σ**
   - つまり F(M) の「交差」を持つ場合、M は type 𝒫₂ ではあり得ない

(b) **X ⊆ H, X cyclic**

(c) **M' = F(M) = M_σ × O_{σ(M)'}(F(M))**
   - M' と F(M) が等しい、かつ direct product 分解

(d) **E_3 = 1, E_2 ⊴ E, E/E_2 ≅ E_1 cyclic**
   - E_1, E_2, E_3 は §12-13 で定義された E の derived series

(e) **3 つの部分ケース**のいずれか：
   - **(1) M ∈ ℳ_𝓕, H abelian of rank 2**
   - **(2) p = |X| ∈ σ(M) - β(M), O_p(H) non-abelian, O_{p'}(H) cyclic, exp(M/H) | q-1**
   - **(3) p = |X| ∈ σ(M) - β(M), O_{p'}(H) cyclic, O_p(H) non-abelian of order p^3, M ∈ ℳ_{𝒫₁}, |M/H| | p+1**

**証明方針**:
- K_1 ∈ E_p^1(X) の normalizer argument
- Thm 12.13（p-群が 𝓤-member ⟺ 特定構造）の応用
- Case split on whether H = M_σ is abelian

**§16 への直結**: Main Theorem (Theorem 16 唯一の結果) で「F(M) が TI でない」という局所分析の最終部を統合。§15.7 の 3 subcase が App.C の矛盾導出へ leading cases を提供。

### Theorem 15.8 (Feit-Thompson 1991): τ₂ との関係

**重要性**: FT path での **critical result**（App.C 最終矛盾の直接的手がかり）。

**仮定** (Corollary 14.12 の状況): M*, H 等が特定条件を満たし、τ₂(H) ≠ ∅（primes p s.t. ∃ abelian of rank ≥ 2 in O_p(G)）

**結論**:
- **q = |K| は唯一の τ₂(H) の素数**
- **τ₂(M) = ∅**（つまり M には large abelian p-group がない）

**証明メカニズム**:
- A ∈ ℰ^2(D)（rank 2 elementary subgroup）をとり、A ⊆ C_G(K) で specialization
- Uniqueness Theorem (Thm 9.6) と Corollary 9.2（A ∉ 𝓤 ⟹ Q ∉ 𝓤 contradiction）の combination
- τ₂ の一意性 extraction

**§16 との関係**: Main Theorem を述べるとき、「いくつかの M では τ₂(M) が制限されている」という形で現れる可能性。

### Corollary 15.9 (Sibley, Feit-Thompson): 最終着陸点

**状況**: x ∈ M_σ#, N ∈ ℳ(C_G(x)), C_G(x) ⊄ M, N ∉ ℳ_𝓕

**結論** (3 部分):
(a) **(Sibley)** M ∈ ℳ_𝓕, N ∈ ℳ_{𝒫₂}
(b) **(FT)** E (complement to M_σ in M) は cyclic, M は Frobenius group
(c) r ∈ τ₂(N), N_E(⟨x_r⟩) ⊆ E ∩ N, |E ∩ N| = |N/N'|

**証明**: Thm 14.4 (两つの maximal が含む element x への action) + Thm 15.8 + Thm 15.7 の結果の packaging

**App.C への意味**: Peterfalvi §9 と統合され、最終的に「すべての場合を exhaustively cover して矛盾に到達」するルート上の重要な binding point。

---

## Peterfalvi §15 (S, T) との対応

BG と Peterfalvi (1984 paper) には**表記と視点の違い**がある：

| 側面 | BG | Peterfalvi |
|------|-----|-----------|
| **主役 subgroup** | M_F (Fitting-related maximal) | S, T (更に精密な subgroup 対) |
| **焦点** | Fitting subgroup F(M) の structure | G 全体の character sum argument に繋ぐ |
| **扱う定理** | 15.2 (type 𝒫₁ characterization) | 15-equivalent conditions for final config. |
| **§15 の役割** | FT local decomposition のまとめ | Central extension of character theory |

**mathlib 観点**:
- BG §15 を実装して、M_F の性質をしっかり axiomatize
- Peterfalvi 統合時は、上記の性質を parameter として passing（重複実装を避ける）
- App.C 完成時に「BG §15 + Peterfalvi §9」が fully interlocked

---

## mathlib カバレッジ

### 既存 API（利用可能）
- `Fintype.Subgroup`, `IsSolvable`, `IsCyclic`, `Commutative`
- Hall system: Schur-Zassenhaus for solvable groups
- Fitting subgroup: `FittingSubgroup` (mathlib で defined 済み)
- Normal subgroups, derived series, center

### 新規実装（Phase 2a で必要）

1. **M_F (Fitting-related nilpotent Hall subgroup) の形式化**
   - `def fittin_related_maximal_nilpotent_hall` or similar
   - 性質: M_σ の部分群, nilpotent, Hall system property

2. **Type 𝒫₁ / Type ℱ の formalization**
   - §14 より imported: `Type𝒫₁`, `Typeℱ` type class or predicate
   - **Thm 15.2** で "M_F ≠ M_σ ⟹ Type 𝒫₁" を axiom/lemma に

3. **Theorem 15.2 の statement と証明**
   - Non-trivial: prime action (Prop 14.2), Thm 3.7, 3.8 を chain
   - 「p, q 両者が prime」「Q ⊴ M」など、derived property extraction

4. **Corollary 15.3-15.6**: 比較的小さい; Hall subgroup + centralizer の direct application

5. **Theorem 15.7, 15.8, 15.9**: 
   - **最高難度**: §12-13 の E subgroup structure と integration
   - τ₂ notation の formalization（§5 narrow p-group と連携）
   - 3-way case split の careful encoding

### 推定行数（Lean 4 全体）
- **§15 全体**: 800-1200 行（Lean 4, rfl + library + 証明）
- うち **Thm 15.2**: 200-300 行（prime action lemma chain）
- うち **Thm 15.7**: 300-400 行（3-way case, E structure integration）

---

## Phase 2a 形式化着手順

### 着手前提
- **§1-§6 完成**: Solvable, Hall, Frobenius action, narrow p-group
- **§10-§14 完成**: M_α, M_σ, type 𝒫 classification
- **§12-§13 checked**: E subgroup notation, prime action base structure

### ステップ 1: §15.1 (Lemma 15.1)
- **難度**: 低（mostly reference to §14.7, §12, §10.2）
- **行数**: 100-150 行
- **進め方**: UM_σ ⊴ M from §14; K cyclic from 14.7(d); M_σ ⊆ M' from 10.2(c)
- **依存**: §14 の K, U definition, §12.10 Corollary

### ステップ 2: Corollary 15.3, 15.4, 15.5, 15.6
- **難度**: 低～中（Thm 15.2 の帰結をまつ）
- **行数**: 150-200 行（4 corollaries combined）
- **進め方**: 15.3 は Prop 14.2, Thm 14.4 の direct application
  - 15.6 は K* の cyclic property を extract

### ステップ 3: Theorem 15.2（最重要）
- **難度**: 中～高
- **行数**: 250-350 行
- **進め方**:
  1. M_σ non-nilpotent ⟹ type 𝒫₁ (Lemma 14.1, Thm 14.7(f))
  2. Prime action (Prop 14.2(a)) + [M_σ, K] = M_σ (Lem 6.3)
  3. K* ∩ F(M) ≠ 1 (Thm 3.8) ⟹ K* ⊆ Q
  4. Regular action on M_σ/Q (Prop 1.5(d)) ⟹ M_σ/Q nilpotent (Thm 3.7)
  5. Minimal normality of Q̄ by nested normalizer argument
  6. Thm 3.10 (Frobenius action on minimal abelian) で p, q extract

### ステップ 4: Theorem 15.7 (F(M) not TI case)
- **難度**: 高
- **行数**: 300-400 行
- **進め方**:
  1. X = F(M) ∩ F(M)^g cyclic (Lemma 15.1(c) + Thm 10.1(a))
  2. E structure (§12-13 から imported): E_1, E_2, E_3
  3. Case split on whether H = M_σ is abelian
  4. Subcase (1): M ∈ ℳ_𝓕, rank(H) = 2
  5. Subcase (2), (3): M ∈ ℳ_{𝒫₁}, p ∈ σ(M) - β(M), detailed p-group rank argument

### ステップ 5: Theorem 15.8, Corollary 15.9
- **難度**: 中（15.8）～高（15.9 の final integration）
- **行数**: 150-250 行
- **進め方**:
  1. τ₂ notation, Uniqueness Thm (9.6) チェイン
  2. 15.8: Corollary 9.2 の application （A ∈ ℰ^2(D) ⟹ q は unique in τ₂(H)）
  3. 15.9: Sibley's result (15.3(a)) + FT 1991 factorization の packaging

### 並列化可能部分
- **ステップ 1, 2** は parallel に進める可能
- **ステップ 3** は ステップ 1 完了後
- **ステップ 4** は ステップ 3 完了 + §12 triple E structure proof 完成後
- **ステップ 5** は ステップ 4 完了後（Thm 15.8 は 14.12 も参照）

---

## 未解決 / TODO

### Formalization 時に必要な検討

1. **M_F の定義の formalization**
   - ⊆ M_σ, normal in M, nilpotent, Hall system?
   - **maximal** normal nilpotent Hall をどう encode するか（recursive definition vs. existential）
   - **参考**: mathlib の `FittingSubgroup` は `sSupIInf` で defined; M_F も similar approach

2. **β(M) ("bad primes") の formalization**
   - β(M) := {q prime : |O_q(M)| > 1 ∧ O_q(M) not cyclic}
   - §5 narrow p-group で既出だが, **§15.2 で初めて使用**
   - **要注意**: Decidability? Finite? 

3. **τ₂(G) (large abelian primes) の formalization**
   - τ₂(G) := {p prime : ∃ rank ≥ 2 abelian subgroup in O_p(G)}
   - **Thm 15.8** で crucial; **App.C** でも使用
   - Fintype に基づく definition likely necessary

4. **Theorem 15.7 の 3-way case split**
   - Conditions (1), (2), (3) が mutually exclusive で exhaustive か formal proof 必要
   - E, E_1, E_2, E_3 structure の dependency を確認

5. **Integration with Peterfalvi§15**
   - App.C で BG §15 result を import し、Peterfalvi framework に adapt する方法
   - **Current plan**: separate `OddOrder/Peterfalvi/S15_ST.lean` として parallel maintain

### Cross-references で要確認

| Reference | Location | Status |
|-----------|----------|--------|
| §14.1, §14.2 | Type 𝒫, K, U structure | ✓ Phase 2a Wave 4 |
| §12.10, §12.13 | E rank, 𝓤-membership | ✓ Phase 2a Wave 3 |
| Thm 3.7, 3.8 | p-soluble action, prime action consequence | ✓ Phase 1 Ch.1 |
| Prop 1.5 | A-invariant Hall system | ✓ Phase 2a Wave 1 |
| Lem 6.3 | Commutator subgroup estimate | ✓ Phase 2a Wave 2 |
| Thm 10.1, 10.2 | M_α, M_σ basics | ✓ Phase 2a Wave 3 |

---

## コメント欄

### 設計上の注記

- **§15.2 の命題(b) で「q ∈ π(M_F) ∩ β(M)」**: FT の巧妙な数え上げの入口。§16 Main Theorem では「β(M) が空でない」という局所的情報を global argument と結合する。

- **Theorem 15.7 の existence of X**（"F(M) not TI"）: App.C での最終矛盾導出に直結。BG p.119-120 の 3 subcase analysis は **purely local** で global property と統合しない; Peterfalvi §9 がそれを担当する。

- **Theorem 15.8 の「τ₂(M) = ∅」**: 非常に strong な condition。これが成立しないと Peterfalvi character theory に leading cases が生じてしまう（= FT 証明のキモ）。

- **Corollary 15.9** は「D. Sibley の結果」と「Feit-Thompson 1991」の**asymptotic combination**。Peterfalvi 論文出版後の refinement であり, BG の追記（1994 edition）。

### 時間見積もり（Full formalization）

- **ステップ 1-2**: 1-2 週間（独立に進行可）
- **ステップ 3 (Thm 15.2)**: 1-2 週間（chain of prime action lemmas）
- **ステップ 4 (Thm 15.7)**: 2-3 週間（E-structure の詳細, 3-way case split, reference 整理）
- **ステップ 5 (Thm 15.8, 15.9)**: 1-2 週間（mostly packaging existing 15.2-15.7）
- **Integration test**: 1 週間

**総計**: 6-12 週間（Phase 2a Wave 4 完成後）

---

## BG Thm 15.7(e) type-F trichotomy (hFI bridge, `isTypeI_of_isTypeF`) — 2026-06-23 cont.¹³

`TypeIData.alternative` (Pf (8.3) 3-way) の ¬TI 枝 = BG Thm 15.7(e) (Coq `nonTI_Fitting_structure`,
BGsection15.v:939-1240)。`by_cases IsMulCommutative M_F`:
- **abelian 枝 = disjunct (b) `rank M_F=2`**: ✅ 締結 (commit `dfdec279`)。witness infra 3 本
  (`exists_inf_conj_fitting_orderP_witness` / `not_isCyclic_opiCore_mf_of_orderP_le_conj` /
  `two_le_pRank_of_comm_isPGroup_not_isCyclic`、全 sorry-free + axiom-clean)。
- **非 abelian 枝 = disjunct (c)**: 残務 (S16:1391 sorry)。**完全攻略計画 = issue 7007 cont.¹³**
  (① conjunct B cyclic O_{p'} = E1X_facts→not_cPP→cycHp'、uniqueness API in-stock ② conjunct A exponent =
  Frobenius semiregular、`TypeFData.frobenius_HU0` 利用、`regular_norm_dvd_pred` 相当は要 ChatGPT de-risk)。
  **type-F 簡略化**: (e3) p³ case 排除・defX 不要。

---

**最終更新**: 2026-06-23 (cont.¹³)
**Next Wave**: hFI 非 abelian 枝 (c) — 正本 issue 7007 cont.¹³ → ✅ 完了 (2026-07-02:
`isTypeI_of_isTypeF` / `isTypeF_of_isTypeI` proven、S16_MainResults sorry-free 側に着地)
