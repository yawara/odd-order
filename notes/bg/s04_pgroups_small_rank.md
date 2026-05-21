# BG §4: p-Groups of Small Rank — mini-roadmap

**スコープ**: BG §4 (pp.33-43), mmd L1359-1788, **10 主要結果**.

形式化先 (予定): `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean`.

**ROADMAP 上の位置**: **Phase 2a 第 1 波** (独立節, Phase 1 Ch.4 (Commutators) 軽前提).

**役割**: Rank ≤ 2 p-群構造定理 (Blackburn Thm 4.16), §10 (α(M) 定義) で直接利用, §7-§16 全体で Sylow p-subgroup 構造の基盤.

---

## TL;DR

§4 は **rank-based p-group 構造の完全分類**: 
- **Thm 4.16 (Blackburn)** = 中核. r(R) ≤ 2, odd automorphism group → metacyclic or extraspecial 分類.
- **m_p(G), r_p(G) rank 概念** = 精密定義. generator 最小数 (m), sectional rank (r) の理論化.
- **Prop 4.3, Lem 4.5-4.15** = rank ≤ 2 p-群の characterization 道具袋.
- **Thm 4.18, 4.20** = 下流結果. rank ≤ 2 条件下での solvable 群全体の構造定理.
- **mathlib**: p-group basic, rank 概念は新規実装; Blackburn 分類は独立定理.

---

## §4 全 10 主要結果一覧

| # | 種別 | mmd 行 | statement 要約 (1-2 行) | Isaacs 対応 | 後続被引用 |
|---|------|--------|--------------------------|-------------|------------|
| **4.1** | Lem | 1385-1387 | G/Z(G) cyclic ⇒ G abelian | **Thm 1.3.4** | §4 Lem 4.15 proof (implicit); FT "cyclic quotient" standard result |
| **4.2** | Lem | 1389-1396 | [x,y] ∈ Z(G) ⇒ [x^n,y]=[x,y]^n, (xy)^n binomial formula | **Lem 2.2.2** | §4 Prop 4.3 proof; commutator calculation fundamental |
| **4.3** | Prop | 1398-1472 | p odd, cl(R) ≤ 2 (or p>3, cl ≤ 3) ⇒ (a) Ω₁(R) exp 1 or p, (b) R'⊆Ω₁(R) ⇒ x↦x^p homomorphism | Hall regular p-group theory + manual | **Prop 4.8(b); Thm 4.11, 4.12 核心**; **§10 Sylow p-group analysis** |
| **4.4** | Prop | 1474-1479 | SCN(R) = maximal abelian normal ⊴R, if R Syl_p then C_G(A)=A×H for A∈SCN, H p'-group | **Thm 5.3.12, 7.6.5** | **Thm 4.16 proof (core)**; §10 α(M) definition (SCN_{≥3}(R) condition) |
| **4.5** | Lem | 1481-1499 | p odd, R noncyclic p-group ⇒ (a) ∃ normal E_p² ⊴R, (b) cyclic index p ⇒ Ω₁(R) elementary ≅ E_p², (c) Ω₁(Z₂(R)) noncyclic exp p | **Thm 5.4.10, 5.4.4, 5.4.3** | **Lem 4.6, 4.10; Thm 4.11; Prop 4.8**; **Thm 4.16 proof** |
| **4.6** | Prop | 1501-1503 | p odd, S normal noncyclic ⊴R ⇒ S contains normal E_p² ⊴R | manual (Lem 4.5 + Lemma 1.22) | **Lem 4.7 proof; Remark 4.9 (rank ≤ 2 ↔ no E_p³ normal)** |
| **4.7** | Lem | 1505-1507 | p odd, R p-group ⇒ SCN₃(R)=∅ ⟺ r(R) ≤ 2 | **Thm 5.4.15** (core equivalence) | **Lem 4.13, 4.14; Thm 4.16 setup; §10 α(M)={p : r_p(M) ≥ 3}** |
| **4.8** | Prop | 1511-1520 | R p-group, r(R) ≤ 2 ⇒ (a) exp p ⇒ \|R\| ≤ p³, (b) p>3 ⇒ Ω₁(R) exp 1 or p | manual (Lem 4.5, Prop 4.3, induction) | **Prop 4.11, Thm 4.12, Thm 4.16**; **size bound for p-group rank ≤ 2** |
| **4.9** | Lem | 1522-1544 | p>3, \|Ω₁(R)\| ≤ p² ⇒ \|Ω₁(R/T)\| ≤ p² for all T⊴R (rank ≤ 2 preserved under quotient) | manual (induction on \|R\|, quotient tower) | **Prop 4.11 (Huppert metacyclic), Thm 4.16**; quotient preservation |
| **4.10** | Lem | 1546-1552 | p odd, R metacyclic noncyclic ⇒ Ω₁(R) elementary ≅ E_p² | **Lem 4.5(b)** direct | **Thm 4.12 core**; metacyclic structure |
| **4.11** | Prop | 1554-1586 | **(Huppert)** p odd >3, \|Ω₁(R)\| ≤ p² ⇒ R metacyclic | **Satz III.11.6 [Huppert 1967]** | **Thm 4.12, Thm 4.16 prerequisite**; foundational Huppert theorem |
| **4.12** | Thm | 1588-1622 | **(Huppert)** R metacyclic p-group, p odd, A p'-group operators, [R,A]=R ⇒ (a) R abelian, (b) [R,A]∩C_R(A)=1, (c) \|\Ω₁(R)\|=\|\Omega₁([R,A])\|·\|\Omega₁(C_R(A))\|=p² | manual (induction, Lem 4.5, 4.10, Maschke) | **Thm 4.16 core**; metacyclic modular action |
| **4.13** | Lem | 1623-1626 | p odd, SCN₃(R)=∅, q\|Aut R, q≠p ⇒ q\|(p²-1), q<p | **Thm 5.4.15** + arithmetic | **Lem 4.14, Thm 4.16 constraint**; divisibility on rank ≤ 2 |
| **4.14** | Lem | 1628-1630 | (Lem 4.13 cont.) q odd ⇒ q\|\frac{1}{2}(p±1) | arithmetic (p²-1=4·\frac{1}{2}(p-1)·\frac{1}{2}(p+1)) | **Thm 4.16 odd automorphism constraint**; prime divisor refinement |
| **4.15** | Lem | 1632-1634 | S extraspecial p-subgroup, [S,R]⊆S' ⇒ R=SC_R(S) | **Lem 5.4.6** | **Thm 4.16 proof (critical step in non-abelian case)**; extraspecial action |
| **4.16** | **Thm** | **1636-1704** | **(Blackburn) — CORE RESULT** p odd, R p-group, A p'-automorphisms, r(R)≤2, [R,A]=R, \|A\| odd ⇒ p>3 and R ∈ {(1) cyclic or E_p, (2) M(p,r) = c.p. of extraspecial of exp p and cyclic} | **[Blackburn 1958] original** | **Thm 4.17, 4.18, 4.20 setup; §10, §12-§16 Sylow p-subgroup classification**; **FT backbone** |
| **4.17** | Lem | 1706-1732 | p odd, R p-group, A solvable p'-group automorphisms, r(R)≤2, \|A\| odd ⇒ A'=p-group | manual (Thm 1.13, 1.8; case m(V)=2 → GL(2,p), Thm 2.6) | **Thm 4.18 proof**; A' constraint for subsequent deriv series |
| **4.18** | **Thm** | **1734-1748** | **(solvable, odd order, rank ≤ 2)** G solvable odd, p∈π(G), r_p(G)≤2 ⇒ (a) p largest in \|G/O_{p'}(G)\|, (b) p=3 or p smallest ⇒ ∃ normal p-complement, (c) G'∩O_p'(G)=G'∩O_p' ⊴ G', (d) all p'-subgroups of G' ⊆ O_{p'}(G'), (e) G/O_{p',p}(G) abelian p'-group | manual (Lem 4.17, Lem 4.7; Thm 4.16 + derived series analysis) | **Thm 4.20 core; §10 (M_α definition, Sylow structure); §12-§16 FT**; **solvable rank ≤ 2 standard form** |
| **4.19** | Cor | 1750-1762 | G solvable odd, G^*⊴G, r_p(G^*)≤2 ⇒ G' centralizes every p-chief factor U/V⊆G^* | manual (Thm 4.18, Lem 4.17; chief series theory) | **Thm 4.20(a) proof**; chief factor centralization |
| **4.20** | **Thm** | **1764-1787** | **(solvable, odd order, overall rank ≤ 2)** G solvable odd, r(G)≤2 or r(F(G))≤2 ⇒ (a) G' nilpotent, (b) S Syl with T⊴S, T⊆S' ⇒ T⊴G, (c) ∃ characteristic series G=G₀⊃···⊃G_n=1, G_{i-1}/G_i ≅ Syl_{p_i}(G) | manual (Cor 4.19, Prop 1.2, Thm 4.18 + Sylow induction) | **§7-§16 framework: Fitting subgroup structure, derived series, Sylow sequence**; **FT minimal counterexample setup** |

**計 20 結果** (Thm 4.1-4.20, Lem, Prop, Cor 混在).

**太字**: Blackburn Thm 4.16 (中核), Thm 4.18, 4.20 (下流定理).

---

## Blackburn Thm 4.16 の詳細

### Statement (mmd L1636-1637)

```
p: odd prime
R: non-identity p-group
A: p'-group of automorphisms of R
─────────────────────────────────────────────
Conditions: r(R) ≤ 2, [R,A]=R, |A| odd
────────────────────────────────────────────
Conclusion: p > 3 and R ∈ {
  (1) R abelian (cyclic or E_p),
  (2) R = M(p,r) = central product of extraspecial of exp p and cyclic group
}
```

### 核心概念

**Extraspecial p-group**: p-group E with E'=Z(E) cyclic of order p.
- **M(p,r)** (Blackburn notation): central product (circ) of r extraspecial p-groups and cyclic group.
- **Condition r(R) ≤ 2**: rank restricted to max 2 generators for all abelian subgroups.
- **[R,A]=R** (R acting transitively): A acts on R with no proper normal A-invariant subgroup.
- **|A| odd**: A has no element of order 2.

### 証明構造 (L1638-L1704, 約 67 行)

**ステップ 1**: SCN₃(R)=∅ (Lem 4.7) → p>3 (Lem 4.13 by odd |A|).

**ステップ 2**: Case |Ω₁(R)| ≤ p²:
- Prop 4.11 (Huppert) → R metacyclic.
- Thm 4.12 (Huppert operators) → R abelian.
- **結論**: (1) holds.

**ステップ 3**: Case |Ω₁(R)| > p² (remaining):
- Prop 4.8(b) → Ω₁(R) exp p, order p³.
- S=Ω₁(R) extraspecial (not abelian by r(R)=2, rank argument).
- C=C_R(S) cyclic (Lem 4.5).

**ステップ 4**: Subcase "R centralizes S/S'":
- Lem 4.15 → R=SC_R(S).
- **結論**: (2) holds (extraspecial + cyclic central product).

**ステップ 5**: Subcase "R does NOT centralize S/S'" (adversarial, led to contradiction):
- T=[R,S], |T|=p² (analysis of action on S/S').
- Aut T ≅ GL(2,p), |R/C_R(T)|=p.
- Derive system of congruences mod p for exponents i,j,k (L1697-L1702).
- **j² ≢ 1 (mod p)** (by α² acts on S/T nontrivially) ∧ **jk≡i, ij≡k, ij²≡i, j²≡1 (mod p)** → **contradiction** (j² ≢ 1 ∧ j²≡1).
- **結論**: This case impossible.

### Phase 2a 形式化方針

**難度**: **高** (20-30 日).

**理由**:
1. **Huppert Prop 4.11** (metacyclic characterization, L1554-L1586) は長い induction; Lem 4.9 (quotient preservation) で基礎.
2. **Thm 4.12** (metacyclic operator action) の Maschke 適用 + 詳細計算.
3. **Thm 4.16 本体**: Step 5 の congruence argument は純粋代数計算だが、GL(2,p) embedding と乗数定理の精密化必須.
4. **lem 4.15** (extraspecial + centroid): Isaacs Lem 5.4.6 existing but Lean での適用に工夫.

**前提**:
- Phase 1 Ch.4 (Commutators): Lem 4.2 型, basic bracket algebra.
- Phase 1 Ch.5 (p-groups): Ω₁, Z_k, SCN, Frattini 等基本. Prop 4.3 の regular p-group 理論は新規 (Hall 再証明 or Isaacs Thm 5.4 chain).

**推奨実装順序**:
1. **Lem 4.1-4.2** (cyclic quotient, bracket identities): 短 (1 日).
2. **Prop 4.3** (regular p-group, exponent formula): 長い帰納 (3-4 日, Hall 理論整理).
3. **Prop 4.4** (SCN characterization): thin wrapper (Isaacs Thm 5.3.12 etc.) (1 日).
4. **Lem 4.5-4.10** (p-group characterization): sequential, Lem 4.5 → Lem 4.6, Lem 4.10 (4-5 日).
5. **Prop 4.11** (Huppert metacyclic): induction + Lem 4.9 (5-6 日, **critical**).
6. **Thm 4.12** (metacyclic operators): Maschke + calculation (3-4 日).
7. **Lem 4.13-4.15** (divisibility + extraspecial): 短 (2 日).
8. **Thm 4.16** (Blackburn): congruence + contradiction (7-10 日, **main**).
9. **Lem 4.17** (A' characterization): logic + GL(2,p) (2 日).
10. **Thm 4.18, 4.19, 4.20** (solvable derived theorems): induction + Lem 4.17, Thm 4.16 (3-5 日).

**並列可能**: Lem 4.1-4.2 と Prop 4.4 (独立) → 他は sequential.

**総計**: **25-35 日** (Prop 4.3 Hall 理論の lean化 次第).

---

## m_p(G), r_p(G) rank 概念の精密化

### 定義 (BG L1363-1369)

**m(A)** (minimal number of generators): abelian p-group A に対し,
```
m(A) = minimal n such that A can be generated by n elements.
```

**同値**: |Ω₁(A)| = p^{m(A)} (p-groups の exponent p 層).

**r_q(G)** (q-rank of G):
```
r_q(G) = max{ m(A) | A abelian q-subgroup of G }
```

**r(G)** (rank of G):
```
r(G) = max{ r_q(G) | q prime divisor of |G| }
```

### BG での用語

- **q-depth** (Gorenstein): r_q(G) の別名.
- **depth**: r(G) の別名.
- **sectional rank**: 部分商に対する rank (Zassenhaus, BG §1 footnote).

### Phase 2a 形式化上の注意

1. **Lean 型**: `r_q G = ⨆ (A : Subgroup G) [AbelianSubgroup ↑A] (Fact (∀ a ∈ A, a^q = 1)), card (Ω₁ A)` (index-theoretic definition).

2. **m(A) vs. rank A**: mathlib `rank` は ℤ-module rank. p-group A に対し m(A) = rank_p A (additive).

3. **r_p(M) 計算**, §10 では:
   ```
   α(M) = { p ∈ π(M) : r_p(M) ≥ 3 }  — "bad primes"
   ```
   Thm 4.7 (rank ≤ 2 ↔ SCN₃=∅) が direct characterization.

### 被引用箇所

| セクション | mmd 行 | 文脈 |
|-----------|--------|------|
| **§4 自体** | L1505-L1507 (Lem 4.7) | "SCN₃(R) = ∅ ⟺ r(R) ≤ 2" (中核同値) |
| **§10** | L2795-L2820 | "M_α = { S ⊆ G : r_p(S) ≥ 3 } に対応" (α(M) = π(M_α)) |
| **§12-§16** | 多数 | Sylow p-subgroup の rank 制約による case split |

---

## §10 (M_α/M_σ 定義) との連携

### Thm 4.16 → §10 の下流

**Thm 4.16 結論**: r(R) ≤ 2 (rank ≤ 2 p-group) → R is metacyclic or M(p,r) extraspecial central product.

**§10 での定義** (Thm 10.1, mmd L2795+):
```
α(M) = { p ∈ π(M) : r_p(M) ≥ 3 }    (bad primes, 順位付けキャラ)
M_α = ∩_{p ∈ α(M)} O_p(M)           (bad p-layers)
M_σ = O_{α(M)'}(M)                  (good p'-layers)
```

### 論理的依存鎖

```
Thm 4.16 (r(R)≤2 classification)
  ↓
Thm 4.18, 4.20 (solvable rank ≤ 2 structure)
  ↓
Lem 4.7 (equivalence r(R)≤2 ⟺ SCN₃(R)=∅)  [core lemma]
  ↓
α(M) = { p : SCN₃(M_p) ≠ ∅ }  [negative characterization]
  ↓
§10 Thm 10.1-10.4: M_α, M_σ detailed structure
```

### Phase 2a → Phase 2b への準備

**Thm 4.16 完成 = §10 開始の必須条件**.

---

## §12-§16 での被引用

| セクション | 題名 | mmd 行 | 引用 |
|-----------|------|--------|------|
| **§7** | The Uniqueness Theorem | L2261+ | Thm 4.16 implicit (Sylow p-subgroup classification) |
| **§8** | Fitting Subgroups | L2456+ | Thm 4.18 (rank ≤ 2 solvable standard form) |
| **§10** | M_α Structure | L2795-2820 | **Thm 4.16, Lem 4.7 direct** (bad prime definition) |
| **§12-§16** | FT (main) | — | Thm 4.16 Blackburn (Sylow classification throughout) |

**計**: 計 4-5 セクション直接引用, plus implicit rank-based case analysis (§7-§16 全体).

---

## mathlib カバレッジ評価

| 結果 | mathlib 対応 | 新規実装 | 難度 |
|------|---------|----------|------|
| **Lem 4.1** (cyclic quotient → abelian) | **high** (`Group.comm_of_cyclic_quotient` exists or similar) | thin wrapper | 短 |
| **Lem 4.2** (bracket identities) | **high** (commutator lemmas, exponent binomial: existing) | thin wrapper | 短 |
| **Prop 4.3** (regular p-group exponent) | **low** (Hall regular p-group: not in mathlib Lean 4; Isaacs 5.4 chain) | **新規: Hall 理論** (3-4 日) | **大** |
| **Prop 4.4** (SCN characterization) | **mid** (`Subgroup.commutantOpposite`; maximal abelian normal: concept existing) | wrapper (Isaacs Thm 5.3.12) | 中 |
| **Lem 4.5-4.10** (p-group characterization) | **mid** (Ω₁, Z_k, noncyclic; Frattini: existing) | inductive suite | 中 |
| **Prop 4.11** (Huppert metacyclic) | **low** (metacyclic definition: simpler; Huppert classification: new) | **新規: induction + Lem 4.9** | **大** |
| **Thm 4.12** (metacyclic operators) | **low** (operator action, Maschke: basic; metacyclic action structure: new) | **新規: Maschke + calculation** | **中-大** |
| **Lem 4.13-4.15** (divisibility + extraspecial) | **mid** (divisibility: existing; extraspecial action: concept new) | wrapper + extraspecial theory | 中 |
| **Thm 4.16** (Blackburn) | **low** (congruence argument, GL(2,p): not in mathlib; classification structure: new) | **新規: main theorem** | **大** |
| **Lem 4.17-Thm 4.20** (solvable derived theorems) | **mid** (solvable, derived series, normal subgroup: existing; rank constraint: new) | **新規: rank ≤ 2 specialization** | **大** |

**総合**: **mathlib カバレッジ ~30-40%, 新規実装 ~60-70%** (Prop 4.3 Hall 理論が largest contributor).

**関鍵**: Phase 1 Ch.5 (p-groups basic, SCN 等) の完成が **§4 形式化開始の必須**.

---

## Phase 2a 形式化着手順

### 推奨形式化順序 (§4 内)

1. **Lem 4.1** (cyclic quotient): 短 (0.5 日).
2. **Lem 4.2** (bracket identities): 短 (0.5 日).
3. **Prop 4.3** (regular p-group): **longest** — Hall 理論整備 (3-4 日).
4. **Prop 4.4** (SCN): medium (1 日).
5. **Lem 4.5-4.6** (elementary abelian in p-group): sequential (2 日).
6. **Lem 4.7** (rank ≤ 2 ↔ SCN₃=∅): **critical** — establishes α(M) definition (1 日).
7. **Lem 4.9** (quotient preservation): (1.5 日).
8. **Prop 4.11** (Huppert metacyclic): **induction landmark** (5-6 日).
9. **Lem 4.10** (metacyclic Ω₁): (0.5 日).
10. **Thm 4.12** (metacyclic operators, Maschke): (3-4 日).
11. **Lem 4.13-4.15** (divisibility + extraspecial): (1.5 日).
12. **Thm 4.16** (Blackburn, **main**): (8-10 日).
13. **Lem 4.17** (A' characterization): (1.5 日).
14. **Thm 4.18-4.20** (solvable derived suite): (3-4 日).

### 並列可能グループ

- **Group A**: Lem 4.1-4.2, Prop 4.4 (independent, short) = **1 日**
- **Group B**: Lem 4.5-4.7, 4.9 (sequential, rank theory) = **4-5 日**
- **Group C**: Prop 4.11, Lem 4.10, Thm 4.12 (sequential, metacyclic) = **6-7 日**
- **Group D**: Lem 4.13-4.15 (sequential, short) = **1.5 日**
- **Group E**: **Thm 4.16 (Blackburn, **main**, critical path)** = **8-10 日** (depends on C, D)
- **Group F**: Lem 4.17, Thm 4.18-4.20 (depends on E) = **4-5 日**

### 日程パス

```
Week 1: Group A (1) + Group B (2-3) → Group C (2-3) parallel start
Week 2: Group B complete + Group C continue
Week 3: Group D (1-2) + Group C complete (metacyclic done)
Week 4-5: Group E (Thm 4.16, Blackburn, **main effort**)
Week 6: Group F (solvable theorems)
────────────────────────────────────────
Total: 25-35 working days (Prop 4.3 Hall integration cost)
```

### Gate Condition

**Phase 1 Ch.5 (p-groups: Ω₁, Z_k, SCN, noncyclic characterization, Frattini) 完成が必須**.

---

## Isaacs Correspondence

| BG Thm/Lem | Isaacs 引用 | 対応性 |
|------------|-----------|-------|
| Lem 4.1 | Thm 1.3.4 (cyclic center → abelian) | 完全一致 |
| Lem 4.2 | Lem 2.2.2 (bracket identities) | 完全一致 |
| Prop 4.3 | Hall regular p-group theory (pp. 183-187) + [19] (not in Isaacs), manual proof in BG | 新規; Isaacs 미포함 |
| Prop 4.4 | Thm 5.3.12, 7.6.5 (maximal abelian, SCN) | 완전일치 |
| Lem 4.5-4.10 | Thm 5.4.3, 5.4.4, 5.4.10 (noncyclic, Frattini, metacyclic) | 완全일치 |
| Prop 4.11 | [Blackburn-Huppert Satz III.11.6, p. 338] (not in Isaacs) | 新規; 독립 |
| Thm 4.12 | Isaacs Thm 5.7 (metacyclic + operator action), Maschke Thm | 준등가 (induction 재구성) |
| Lem 4.13-4.15 | Thm 5.4.15, Lem 5.4.6 (divisibility, extraspecial) | 完全일치 |
| **Thm 4.16** | **[Blackburn 1958]** (original, not in Isaacs) | **新規; FT independent theorem** |
| Lem 4.17 | Thm 1.13, Thm 2.6 (characteristic subgroup, GL(2,p)) | 準등가 |
| Thm 4.18-4.20 | Thm 6.3.2 (Fitting structure), derived series analysis | 准등价 |

**결론**: **Thm 4.16 (Blackburn), Prop 4.3, Prop 4.11 은 Isaacs 미포함 원본 문헌 필수**.

---

## Relation to Peterfalvi

**Peterfalvi 08-09.mmd** (attached theorems) 검색:

| Peterfalvi Section | Reference | BG §4 connection |
|--------------------|-----------|------------------|
| **Peterfalvi §1** (group setup) | "rank of a p-Sylow" | r_p(S) definition (Thm 4.16 context) |
| **Peterfalvi §4** (p-group structure) | minimal counterexample Sylow analysis | Thm 4.16 classification (metacyclic / extraspecial) |
| **Peterfalvi §10** (uniqueness) | Thm 10.1: M_α := { p : bad } | **Lem 4.7 (rank ≤ 2 ↔ SCN₃=∅) 핵심** |

**결론**: **Peterfalvi 본문 Phase 2b (§10+) 시작 전, BG §4 (특히 Thm 4.16, Lem 4.7) 완성 필수**.

---

## Unresolved / TODO

| Item | Status | Priority |
|------|--------|----------|
| **Prop 4.3 Hall regular p-group proof formalization** | TBD | **HIGH** — longest single proof; Hall [19] 원문 접근 |
| **Thm 4.16 GL(2,p) embedding in Lean** | TBD | **HIGH** — congruence argument 정밀화 |
| **m(A), r_p(G) formalization in mathlib** | TBD | **MED** — type-theoretic encoding (finrank vs. explicit generator count) |
| **extraspecial p-group M(p,r) notation in Lean** | TBD | **MED** — central product implementation, Thm 4.16 (2) statement |
| **Lem 4.17 "A' is p-group" — derived series constraint** | TBD | **MED** — GL(2,p) case analysis, Thm 2.6 (solvable group invariant) |
| **Phase 1 Ch.5 p-group basics completion date** | TBD | **GATE** — §4 착수 전제조건 |
| **α(M) definition in §10 — linking back to Lem 4.7** | TBD | **MED** (Phase 2b §10) — negative characterization proof |

---

## Summary: Phase 2a § 4 Roadmap

**독립적 절 (Phase 1 Ch.4 기초 가정 + Ch.5 p-group basics 前提)**.

**중심 결과**: **Blackburn Thm 4.16** (odd-order solvable 최소반례의 Sylow p-subgroup 분류).

**파급 효과**: 
- §10 (M_α definition) 기초.
- §7-§16 (FT) Sylow structure 전체 제약.
- Peterfalvi §10+ 논의 의존.

**형식화 규모**: **25-35 일** (parallel possible, Prop 4.3 + Thm 4.16 main bottleneck).

**mathlib 신규**: Hall regular p-group 이론, Blackburn 분류, rank-based solvable structure.

---

**작성**: 2026-05-22

**출처**:
- `references/bg/local-analysis.mmd` lines 1359-1788 (§4 완문)
- `references/bg/bg.pdf` pp.33-43 (本文検証)
- `references/isaacs/finite-group-theory.mmd` (Isaacs 대응)
- `notes/bg/s06_additional.md` (조직 패턴 참고)

**다음 단계**:
- Phase 1 Ch.4-5 완료 date 확인 (gate condition).
- Prop 4.3 Hall 이론 Lean 번역 전략 (external [19] 원문 분석).
- Thm 4.16 congruence argument proof sketch (GL(2,p) embedding).
- §10 per-section ノート 작성 (α(M) definition link).

