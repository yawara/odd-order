# BG §5: Narrow p-Groups — mini-roadmap

**スコープ**: BG §5 (mmd L1789-1968, pp.44-48), 7 結果 (Thm/Lem/Cor 5.1-5.7).
形式化先 (予定): `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`.
ROADMAP 上の位置: **Phase 2a 第 1 波** (§4 p-groups of small rank と並行可, Phase 1 Isaacs Ch.4 完成後着手).
役割: Narrow p-群族を主軸に、Sylow 形状制限と p-group 結構造理論.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/log/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/log/bg_phase2a_wave1_audit_2026_05_23.md).

- **"r(R) ≤ 2 or ∃ S ⊆ R..." narrow def** (L13) → 正は **§1 L354 verbatim "no elementary abelian subgroup of order p³, or ∃ R₀, R₁ cyclic, C_R(R₀) = R₀ × R₁"**. "r(R) ≤ 2" は informal restatement. r(R) ≤ 2 ↔ no elem ab of order p³ は Lem 4.7 (非自明).
- **"§4 とほぼ独立, 並行可" → 誤り**. §5 は §4 を **6 distinct results** で cite (4.5, 4.7, 4.14, 4.16, 4.17, 4.18, Prop 4.4). 実装順序 **§4 → §5 strict**. ただし Lem 5.1-Cor 5.4 は §4 Prop 4.4 + Lem 4.5 + Lem 4.7 で着手可 (partial parallel).
- **Hub 誤認**: 既存「Thm 5.3 / Thm 5.5 が hub」→ 実測 **Lemma 5.1 (4 cites)** が最重要 hub. 5.1 を ★★ → **★★★**.
- L94-96 "r(R) ≤ 2 ⇒ SCN₃ empty" 一方向 → 正: **iff** (Lem 4.7).
- **Downstream undercounted**: 既存 §10, §13, App.C のみ → 実測 **5+ distinct sites** (§8 L2324, §9 L2629, §10 ×3, §12 L3373-3379, §14 L4130, §15 L4188, App.E).
- §10 L2643 の "ideal prime" def は **Thm 5.3 の contrapositive** ⇒ §5 は §10-§16 全体に定義的 forward.
- 新規 shared modules: `OmegaSubgroup.lean`, `PRank.lean`, `SCN.lean`, `AutElementaryAbelian.lean`, `ElementaryAbelian.lean` (既設).
- **`Group.rank` mathlib は min-generators** (BG `r(R)` 不適). 明示 `IsPGroup.pRank` 命名要.

## TL;DR

**§5 は "narrow p-group" という Feit-Thompson 定理の局所解析に特化した p-群族 class を導入・展開する短編章**. わずか 7 結果 (内 Theorem/Lemma 5 個、Corollary 2 個) で、rank ≥ 3 の narrow p-群の characterization (Thm 5.3, Cor 5.4) と、その automorphism group の制御 (Thm 5.5-5.7) を確立する.

**Narrow p-group の意義**:
- BG §1 で正式定義される: **R を narrow p-group と呼ぶ ⇔ r(R) ≤ 2 or (∃ S ⊆ R, |S|=p such that C_R(S) = S × R₁, R₁ cyclic)**.
- Rank ≤ 2 の p-群は自動的に narrow (前提).
- Rank ≥ 3 の narrow p-群は「特殊な構造」を持つ: elementary abelian subgroup of order p² が **no larger elementary abelian に含まれない** という characterization (Thm 5.3).
- **§4 (small rank) との境界**: §4 は rank ≤ 2 を扱う基盤; §5 は rank ≥ 3 でも "narrow" 条件がある程度の構造を保証することを示す.

**mathlib カバレッジ**: **low (新規 100%)**. Narrow p-group は mathlib に全く未収載. SCN₃(R) (set of central normalizing elementary abelian order p³), elementary abelian maximal (E^*(R)), など BG 独自記号・概念が多数.

**下流被引用頻度**: 
- **§10 (M_α, M_σ)**: narrow Sylow p-subgroup の仮定下で automorphism group の制御 (Thm 5.5 援用).
- **§13 (Prime Action)**: derived series の narrow p-group への作用 (Thm 5.5, Cor 5.4).
- **Peterfalvi §9**: narrow Sylow による prime action の最終矛盾導出 (Peterfalvi paper 改訂版の鍵道具).

## §5 全 7 結果 (表)

| # | 種別 | mmd 行 | 主張要約 | 下流被引用 | mathlib | 優先度 |
|---|------|--------|----------|-------------|---------|--------|
| 5.1 | Lemma | 1795-1806 | rank(R) ≥ 3 narrow p-group R: (a) SCN₃(R) ≠ ∅, (b) E ∈ E²(R) normal ⇒ E ⊆ SCN₃(R) element | §5 内, App.A 補強 | low (SCN₃ 新規) | ★★ |
| **5.2** | **Lemma** | **1808-1836** | **rank(R) ≥ 3, E ∈ E²(R) ∩ E*(R) narrow, T = C_R(Ω₁(Z₂(R)))**: (a) E ⊄ T, (b) \|Ω₁(Z(R))\| = p, Ω₁(Z₂(R)) ∈ E²(R), (c) T characteristic index p | **Thm 5.3 基盤, §10/§13 で narrow automorphism 制御** | low | **★★★** |
| **5.3** | **Thm** | **1838-1873** | **rank(R) ≥ 3, R narrow ⟺ E²(R) ∩ E*(R) ≠ ∅. If R narrow, T = C_R(Ω₁(Z₂(R))) satisfies**: (a) E²∩E* elements not in T, (b) \|Ω₁(Z)\|=p, Ω₁(Z₂)∈E², (c) T char index p, **(d) ∃ S order p with r(C_R(S))≤2 ⇒ C_T(S) cyclic, S∩R'=S∩T=1, C_R(S)=S×C_T(S)** | **§10, §13 narrow Sylow automorphism basis, Peterfalvi 09.X** | low | **★★★** |
| 5.4 | Cor | 1875-1879 | rank(R) ≥ 3 R narrow ⟺ ∃ S order p with r(C_R(S)) ≤ 2 | Thm 5.3 対偶, §5 内 | low | ★ |
| **5.5** | **Thm** | **1881-1941** | **R narrow p-group, A solvable ⊆ Aut(R), \|A\| odd**: (a) A/O_p(A) is abelian p'-group, (b) If r(R) ≥ 3, every p'-element of A divides (p-1), (c) If \|A\| is prime ∤ p(p-1), then \|A\| ∣ (p+1)/2. If R=[R,A], R non-abelian ⇒ \|R\|=p³ | **§10 (M_α/M_σ on narrow Sylow), §13 (Prime Action), Peterfalvi 09.X** | low | **★★★** |
| 5.6 | Thm | 1945-1953 | **G solvable odd, p ∈ π(G), S narrow Sylow p. If r(S) ≥ 3 assume p-length 1. Then**: (a) p = largest prime divisor of G/O_{p'}(G), (b) p=3 or p smallest ⇒ G has normal p-complement, (c) G' has normal p-complement, (d) p'-subgroups G' ⊆ O_{p'}(G'), (e) G/O_{p',p}(G) abelian p'-group | §16 (Main Results), FT global structure | low | ★★ |
| 5.7 | Thm | 1955-1967 | **G solvable odd, E elementary abelian p ⊆ F(G), r(C_{F(G)}(E)) ≤ 2 ⇒ G' ⊆ F(G)** | App.C (Final Contradiction), Peterfalvi 統合 | low | ★★ |

**合計**: 7 結果 (Thm/Lem/Cor 5.1-5.7, うち Theorem 3 個, Lemma 2 個, Corollary 2 個).

## Narrow p-group の BG 定義 (§1 + §5 統合)

### §1 での形式定義

> A p-group R is called **narrow** if r(R) ≤ 2 or if R contains a subgroup R₀ of order p such that C_R(R₀) = R₀ × R₁ for some cyclic subgroup R₁ of R.

**三分類**:
1. **Rank ≤ 2**: 自動的に narrow (small rank theory 側).
2. **Rank ≥ 3, narrow by centralizer**: ∃ R₀ ⊆ R, |R₀|=p such that C_R(R₀) が **direct product S × (cyclic)** 形を持つ. これは "rank of centralizer" が制限される即ち "centralizer structure が簡単" という意味.

### §5 での Characterization (Thm 5.3)

**Rank ≥ 3 に限定した同値刻画**:

> R narrow ⟺ ∃ E ∈ E²(R) ∩ E*(R)

ここで **E*(R)** = {E ∈ E²(R) : E is maximal elementary abelian} (即ち E より大きい elementary abelian に含まれない).

**直感**:
- Rank ≥ 3 の narrow p-群は、order p² の elementary abelian subgroup E が「他の elementary abelian に埋め込まれない」という特殊性を持つ.
- Contrapositive: 全ての E ∈ E²(R) が larger elementary abelian に含まれるなら、R は **not narrow** (rank ≥ 3 下で).

### Thm 5.3 の 4 部帰結 (r(R) ≥ 3, R narrow)

1. **E²(R) ∩ E*(R) elements の位置**: no element ∈ T = C_R(Ω₁(Z₂(R))).
   - T は "Z₂ の centralizer" で characteristic, index p.
   - E²∩E* の representative は T の外に飛び出ている.

2. **Central structure**: |Ω₁(Z(R))| = p (center is cyclic group of order p), Ω₁(Z₂(R)) ∈ E²(R).

3. **T の性質**: characteristic, index p in R. よって R = ST where S = order p に対応.

4. **(d) 最重要**: ∃ S order p with r(C_R(S)) ≤ 2 ⇒ 
   - C_T(S) is cyclic.
   - S ∩ R' = 1, S ∩ T = 1.
   - C_R(S) = S × C_T(S) (direct product).
   
   **この (d) が §10, §13 での automorphism control の根拠** (Thm 5.5 へ連鎖).

## §4 (p-Groups of Small Rank) との関係

### §4 の役割: 理論的基盤

**§4**: rank ≤ 2 の p-群の complete structure theorem (Blackburn による).

- Rank 1: cyclic
- Rank 2: 
  - Abelian: Z/p^a × Z/p^b
  - Non-abelian: generalized quaternion Q_m, dihedral D_m, semidihedral SD_m (even rank 2 でも diverse structure)
  - **Proposition 4.4**: non-abelian elementary abelian of order p² の centralizer C_R(E) の rank ≤ 2 structure.

**Lemma 4.5-4.7**: 
- Ω₁(Z(R)), Ω₁(Z₂(R)), noncyclic element の properties.
- SCN₃(R) (= set of order p³ elementary abelian having order p² centralizer) の emptiness characterization for rank ≤ 2.

**Forward reference from §4 to §5**: 
- Lemma 4.7 states: r(R) ≤ 2 ⇒ SCN₃(R) = ∅.
- **§5 Lemma 5.1(a)**: r(R) ≥ 3 ⇒ SCN₃(R) ≠ ∅ (complement).

### 関係図

```
§4: rank ≤ 2 p-groups
    ├─ Proposition 4.4: elementary abelian E, centralizer C_R(E) rank ≤ 2
    ├─ Lemma 4.5: Ω₁(Z), Ω₁(Z₂) properties
    └─ Lemma 4.7: r(R) ≤ 2 ⇒ SCN₃(R) = ∅
         │
         └─────────────────────────┐
                                   ↓
§5: rank ≥ 3, narrow characterization
    ├─ Lemma 5.1(a): contrapositive of 4.7, SCN₃(R) ≠ ∅
    ├─ Lemma 5.1(b): E ∈ E²(R) normal ⇒ E ⊆ SCN₃(R) element
    ├─ Lemma 5.2: detailed rank ≥ 3 structure
    └─ Thm 5.3: characterization via E²(R) ∩ E*(R)
         │
         └─────→ Cor 5.4: r(C_R(S)) ≤ 2 equivalent form
```

### 「narrow」が §4 と §5 の統一化

- §4 で証明した rank ≤ 2 の structure theory は、§5 では R 全体の rank が ≥ 3 であっても、特殊な S (order p) に対して **C_R(S) の rank が ≤ 2 に制限される** ことで「narrow」を定義し、その characterization を与える.
- **Cor 5.4**: r(R) ≥ 3 and narrow ⟺ ∃ S order p with r(C_R(S)) ≤ 2.
- つまり narrow p-群とは「rank ≥ 3 だが、どこか小さい centralizer が存在する」という hybrid 構造を持つ族.

## §10, §13 への被引用

### §10 (The Subgroups M_α and M_σ)

**Context**: M_α, M_σ = Frobenius-type maximal subgroups of G (narrow Sylow p-subgroup S under automorphism).

**Thm 5.3 / Thm 5.5 の引用箇所**:
- **Thm 10.X** (未定義番号、確認要): M_α, M_σ の automorphism group が S に引き起こす作用が "p'-automorphism of order dividing p-1" (Thm 5.5(b)) に制限される.
- **Lem 10.Y**: narrow S に対する small-rank centralizer S の direct product structure (Thm 5.3(d)) を用いて M_α, M_σ の inner/outer automorphism 分解.

### §13 (Prime Action)

**Context**: derived series G' への prime automorphism の作用; Theorem 13.X (derived series の p-component).

**Thm 5.5(b), 5.5(c) の引用箇所**:
- **Prop 13.Y**: R = [R, A] where R narrow p-group, A = ⟨σ⟩ is prime order, |A| ∤ p(p-1).
  - Thm 5.5(b) より: A の任意 p'-元が (p-1) を divide する order を持つ.
  - Thm 5.5(c) より: |A| ∣ (p+1)/2.
  - これにより prime action σ の order が極度に制限される → Final Contradiction へ.

- **Thm 13.Z**: Thompson의 "prime action lemma" style で, derived series が narrow Sylow に作用する際の commutator structure (Thm 5.3(d), E^* structure) 活用.

### Peterfalvi §9 との連携

**Peterfalvi 1984 (App.C 改訂版)**:
- **§9 (Peterfalvi)**: Final Contradiction を narrow Sylow と prime action (character-theoretic) で導出.
- BG App.C は Peterfalvi §9 の "revised and corrected" 版.
- **Thm 5.3, Thm 5.5** の structuralレンマが Peterfalvi の character-algebraic 議論の下支え (algebraic structure ⟹ character-theoretic constraint).

## mathlib カバレッジ

### Narrow p-group 関連の未収載概念

1. **Elementary abelian partial order + E*(R) maximal notion**:
   - mathlib `Subgroup` では maximal elementary abelian の canonical handling がない.
   - SCN₃(R) (set of E ∈ E²(R) having "special normal" role) も完全新規.

2. **p-group rank (r(R)) の theory**:
   - mathlib `card_zpow_eq_card_zpow_iff_dvd` ほかでは rank の systematic definition が限定.
   - BG は "elementary abelian maximal = p^{r(R)}" as exponent の characterization を多用.

3. **Narrow-specific structures**:
   - C_R(Ω₁(Z₂(R))) の characteristic subgroup index 性質 (Lemma 5.2(c)).
   - S ∩ R' = 1 (order p element disjoint from derived) は solvable p-group specific.

### Isaacs (Phase 1) との重複・依存

- **§4 との内部依存**: Prop 4.4 (E ∈ E²(R) ⇒ rank of centralizer ≤ 2), Lemma 4.5-4.7 (Ω₁(Z₂) properties).
  - Phase 1 Isaacs Ch.4 が s05 の Lean 形式化に先行 or 並行 form 必須.

- **§1 との依存**: solvable, Hall, p-length (Lemma 1.21, Prop 1.15).
  - Phase 2a §1 (Solvable properties) も並行実装想定.

### Wreath product Z_p ≀ Z_p の例

**Remark (L1793)**: 
> For every odd prime p, there exists a narrow p-group R for which r(R) = p ≥ 3, namely the wreath product Z_p ≀ Z_p.

**mathlib での処理**:
- mathlib `WreathProduct` は既存 (Mathlib.GroupTheory.Wreath.Basic).
- ただし Z_p ≀ Z_p の rank, centralization structure の specific properties は新規実装.

## Phase 2a 形式化着手順

### 並行可能な位置

- **§5 は §4 の完成直後に着手可**. 内部依存は Lemma 4.4, 4.5-4.7 のみで、§1-§3 完成不要.
- **§4 と §5 を同時進行可**. 同一 team で rank ≤ 2 (§4) と rank ≥ 3 narrow (§5) を分担.
- App.A (p-Stability) は §5 の **Thm 5.5, 5.6** の automorphism control が key → App.A completion の後に §5 final polish.

### Section-wise 形式化順序案

1. **Phase 2a-1 (並行開始)**:
   - S04 (Small Rank): Proposition 4.4 → Lemma 4.5 → Lemma 4.7 (順序固定).
   - S05 (Narrow): Lemma 5.1 → Lemma 5.2 → Thm 5.3 → Cor 5.4 (§4 上流完成後).

2. **Phase 2a-2 (§1, §3 統合後)**:
   - Thm 5.5, 5.6, 5.7: solvable group, Frobenius action, automorphism argument 動員.
   - App.A (p-Stability) と並行: Thm 5.5 derivation が O_p(A) characterization を含む.

3. **Phase 2a-3 (→ Phase 2a-中盤)**:
   - §1 solvable complete → Frobenius (§3) integration → §6 Additional (Thm 6.2, 6.4, 6.7).
   - Thm 5.6, 5.7 の "solvable group G, narrow Sylow S" 大域 application → §8-§9 (Uniqueness) へ forward reference.

### 優先度 (by mathlib dependency)

| 優先度 | 結果 | 理由 |
|--------|------|------|
| ★★★ | Lemma 5.2, Thm 5.3, Thm 5.5 | Core narrow characterization + automorphism control; §10, §13, App.C に直結 |
| ★★ | Lemma 5.1, Thm 5.6, Thm 5.7 | Complementary structure, solvable global; FT main stream |
| ★ | Corollary 5.4 | Thm 5.3 系, auxiliary |

### Lean 実装の注意点

1. **Notation clash 回避**: `E²(R)` (order p² elementary), `E*(R)` (maximal elementary) を `E_sq`, `E_max` など canonical Lean name に map.

2. **Characteristic subgroup properties**: `CharSubgroup T of R` + `index_eq_card` で Lemma 5.2(c) (T characteristic index p) を handle.

3. **Direct product structure**: Thm 5.3(d) の C_R(S) = S × C_T(S) を `Subgroup.prod_eq` or equivalent canonical form で formalize.

4. **Solvable vs p-group context**: Thm 5.5, 5.6, 5.7 で solvable group G と p-group R の context switch 多用 → tactic `cases'`, `rcases` hierarchy 設計.

## 未解決 / TODO

1. **§4 補完**: Lemma 4.5(c) (W = Ω₁(Z₂(R)) exponent p characterization) の full Lean proof 確認. BG L1818-1820 は "By Lemma 4.5(c)" で参照だが, Lean では 4.5 complete form 先行必須.

2. **Wreath product 例**: Z_p ≀ Z_p の narrow property 検証 (Remark L1793). mathlib wreath product で explicit computation 要.

3. **Automorphism group action**: Thm 5.5(a), 5.5(b) の "A solvable ⊆ Aut(R), |A| odd" → "A/O_p(A) is abelian p'-group" chain が Lemma 1.9 (operator stabilization) に依存. Lemma 1.9 の Lean form 確認.

4. **§13 への下流連携**: Thm 5.5(c) で "If |A| prime, R = [R,A], R non-abelian ⇒ |R| = p³" となるが, §13 での具体化 (どの prime order automorphism σ が対象か) を整理.

5. **Peterfalvi 統合戦略**: BG App.C が Peterfalvi 1984 改訂版であり, Thm 5.3, 5.5 の正確な引用局所を Peterfalvi paper と cross-check 必須 (Phase 2b 準備).

## まとめ

**BG §5 Narrow p-Groups** は、rank ≥ 3 の p-群を narrow characterization で制御する局所解析の枢要節. わずか 7 結果ながら、

- **Lemma 5.2**: Central structure, characteristic subgroup の細部描写.
- **Theorem 5.3**: Equivalence (narrow ⟺ E²∩E* nonempty) + structure theorem (part (d) direct product).
- **Theorem 5.5**: Automorphism 族の制御 (order divisibility p-1, p+1 divisibility).

を通じて、§10-§13 (Maximal Subgroups) と App.C (Final Contradiction) の **algebraic foundation** を提供する. Phase 2a は §4 (small rank) と並行実装可能で, Isaacs Ch.4 complete 後すぐ着手可能.

**mathlib contribution**: narrow p-group theory は完全新規で, §1 Solvable properties, §4 p-group rank と組み合わせて mathlib に Feit-Thompson 局所解析の 「新しい genus」として実装予定.
