# Peterfalvi App.B + C + D + E: 小規模付録 — mini-roadmap (合体)

**スコープ**: Peterfalvi の 4 つの小規模付録 (合計 9 結果, 428 行)
**形式化先** (予定): OddOrder/Peterfalvi/Appendices/{Huppert,NearFields,Suzuki2Groups,FeitSibley}.lean
**ROADMAP 上の位置**: Phase 2b 第 7 波 (本体完了後の発展材料)
**役割**: FT 本筋外 (△), Peterfalvi 完成度のため記念的再録

---

## TL;DR

Peterfalvi 第 I 巻末の 4 つの付録は、FT 本体証明の外側に位置しながら、各種対称群・特殊群論の重要な部分定理を収集・再証明したもの。

- **App.B (Huppert 特例)**: 奇数位数の二重推移群の構造定理 (Huppert 1957 の特例版)
- **App.C (Near-Fields)**: 有限 near-field の分類 (Zassenhaus 定理の素説)
- **App.D (Suzuki 2-群)**: Higman による Suzuki 2-群の分類と quadratic form の幾何学
- **App.E (Feit-Sibley 定理)**: 奇数位数の D に対する character coherence の主定理

合計 8 定理・命題と 4 本の補題で構成。mathlib への寄与はほぼ 0（Huppert, Higman 参考文献に依存）だが、形式化の完全性のため Phase 2b 後に optional で再録の価値あり。

---

## 4 付録の概要 (表)

| 付録 | 名称 | 行数 | 結果数 | 主定理 | mathlib 新規度 | 本体での用途 |
|------|------|------|--------|--------|-------|---------|
| **B** | Huppert 特例 | 26 | 1 | Prop.1 (Huppert group 構造) | 高 | なし (△) |
| **C** | Near-Fields | 44 | 2 | Prop.1, 2 (near-field 分類) | 高 | なし (△) |
| **D** | Suzuki 2-群 | 130 | 4 | Theorem (Higman 分類) | 高 | なし (△) |
| **E** | Feit-Sibley | 228 | 2 | Theorem (odd ord. coherence) | 中 | あり (character) |

**合計**: 428 行, 9 結果, **全 △ (FT 経路外)**

---

## App.B: Huppert 特例 (06.0, pp.135–136)

### 1 結果

**Proposition 1** (Huppert 1957): 
_奇数位数の群 D が初等アーベル q-群 E に忠実に、E^# 上推移的に作用するとき、F(D) は巡回で E に不動点なく作用し、D/F(D) はアーベル。_

### 意義

- Huppert の二重推移群定理の古典的特例
- FT 本体では使われない（△）が、本体経路上の特殊ケースの完全性のため記載
- Higman 分類前の「初等的」再証明パターン

### 証明の構造

**Lemma**: p ≠ 2, P が q-群 E に忠実に作用し、|P_a| が a ∈ E^# で独立 ⟹ P は巡回。

**証明手順**:
1. E = E₁ ⊕ ⋯ ⊕ E_r (r ≥ 2) と分解 ⟹ P_a は各 E_i を中心化 ⟹ 矛盾
2. P が E に既約に作用すると仮定
3. P の非可換な (p,p)-正規部分群 R を取得（[H], Cap.III, Hilfsatz 7.5）
4. Schur 補題で Z(P) は有限体の乗法群の部分群 ⟹ 巡回
5. P による推移作用を利用して矛盾導出

### 計算例

主定理の応用: D が奇数位数で E に推移的に忠実に作用すれば、Fitting subgroup F(D) の structure が完全に決定される。これにより、E ⋊ D の二重推移性が保証される。

**mathlib への寄与**: ほぼなし（Group theory の基本参照）

**形式化優先度**: **低** (optional, Phase 2b 後)

---

## App.C: Near-Fields (07.0, pp.137–138)

### 2 結果

**Proposition 1** (Near-field from FT context):
_G が (A1), (A2) を満たし 2-rank = 1 ⟹ near-field F, automorphism 群 Σ があり、G ≅ ℒ(F) ⋊ Σ = (F ⋊ F^*) ⋊ Σ。Q は F^*, D は Σ に対応。_

**Proposition 2** (near-field 分類):
_有限 near-field で乗法群が index 2 の巡回部分群を持つ ⟹ F は体か F = F_{r²,2} (Wedderburn 非可換 near-field)。後者では |Z(F^*)|  = r-1。_

### Near-field 基礎定義

- (F, +, ·) で F は加群, F^* = F - {0} は乗法群
- 右分配法則のみ: (a+b)c = ac + bc (左分配律は不要)
- ℒ(F) = F ⋊ F^* (affine group)

### F_{r²,2} 構成

r = 奇素数の冪, K = **F**_{r²} に対し、
```
x ∘ y = { xy       if y ∈ (K^*)²
        { x^r y    otherwise
```

これは near-field を成す（Frobenius 自己同型 σ(x) = x^r で説明可能）。

### Peterfalvi 本体での使用

- 2-rank 1 の特殊ケースの character 論的刻画に used
- near-field 構造 = character table 解析への橋渡し
- Zassenhaus (1957) 有限 near-field 完全分類に依存

**mathlib への寄与**: **中～高** (near-field は標準的でなし)

**形式化優先度**: **中** (本体の 2-rank ケース分けに関連)

---

## App.D: Suzuki 2-Groups (08.0, pp.139–143)

### 4 結果

**Lemma 1** (2-群の quadratic form):
- (a) P が 2-群, W = Z(P), V = P/W が初等アーベル ⟹ x ↦ x² は quadratic mapping V → W
- (b) 逆に任意 quadratic q: V → W に対し、拡大 W ↪ P ↠ V が存在
- (c) 同型条件: quadratic form が可換
- (d) 中心拡大の自己同型: Hom(V, W) の加法群に同型

**Lemma 2** (**F**₂ 上の quadratic form の次元):
F = **F**_{2^n} に対し、
- (a) F の **F**₂-線型自己準同型: Aut(F) を基とする n 次元
- (b) Bilinear F × F → F: n² 次元
- (c) Quadratic F → F: 1 + (n choose 2) = n(n+1)/2 次元

**Definition 1** (Suzuki 2-群):
_非可換な 2-群 P で少なくとも 2 つの involution を持ち、巡回群 K が P に忠実に作用し involution の集合に正則に作用するもの。_

**Definition 2, 3** (Type A, B):
- **Type A**: A(n, φ) = quadratic form x ↦ xφ(x) from F = **F**_{2^n} to F
- **Type B**: B(n, φ, ε) = quadratic form (a,b) ↦ aφ(a) + εaφ(b) + bφ(b) from F × F to F

**Theorem** (Higman の分類, [Hi], [HB] Ch.VIII, Thm.7.9):
_Suzuki 2-群 P で Z = Z(P), q = |Z|, F = **F**_q, K を as in Def.1 とするとき:_
- (a) Involution の集合は Z^#, Z は初等アーベル
- (b) P/Z は order q または q² の初等アーベル ⟹ |P| = q² または q³, exponent = 4
- (c) |P| = q² ⟹ Type A, K ≅ F^* 作用: a^ε = xa, b^ε = xφ(x)b
- (d) |P| = q³ ⟹ P/Z = 2 つの同型 **F**₂[K]-加群の直和
- (e) Type B iff P/Z = 同型加群の直和

**Proposition 1** (B(n,1) の幾何学):
_E = **F**_{2^{2n}} に q(x) = x̄x (Galois involution) として quadratic form 構造を持つ。_

**Proposition 2** (Aut(B(n,1)) の構造):
_Aut(B(n,1)) → {x ↦ λσ(x) : λ ∈ E^*, σ ∈ Aut(E)} は全射, kernel は初等アーベル 2-群。_

### 数学的背景

Suzuki 2-群は FT の「特殊 involution」の幾何学的モデル。
- Higman (1966) の分類は完全で、Type C, D の明示的定義は不要
- 2-adic quadratic form の観点から、characteristic 2 の field extension の automorphism を制御
- Prop.2 の automorphism group 計算: Aut(B(n,1)) は B(n,1) 自身の拡大で生成

**mathlib への寄与**: **極高** (quadratic form, Galois theory, 2-adic geometry)

**形式化優先度**: **高** (Phase 2b 後の Suzuki 2-群の完全モデル化に不可欠)

---

## App.E: Feit-Sibley 定理 (09.0, pp.144–150)

### 2 結果 + 主定理

**Lemma 1** (Character coherence の十分条件):
- (a) (𝒮₀, τ) が coherent, ψ で χ₀(1) | ψ(1) かつ 2χ₀(1)ψ(1) < Σ χ∈𝒮₀ χ(1)² ⟹ (𝒮₀ ∪ {ψ}, τ) coherent
- (b) |𝒮| ≥ 2 で全 χ ∈ 𝒮 が同じ次数 ⟹ coherent

**Lemma 2** (Induction isometry):
- (a) 𝒮 = 文字 Ind_Q^H φ (φ ∈ Irr(Q), Q₁ ⊄ ker φ)
- (b) ψ ↦ Ind_H^G ψ は isometry **Z**[𝒮]^∘ → **Z**[Irr(G)]^∘
- (c) d odd, χ ∈ 𝒮 ⟹ χ̄ ≠ χ

**主定理** (Feit-Sibley, odd order case):
_G finite, H = Q ⋊ D with (|D|, |Q|) = 1, Q ∩ Q^x = 1 (x ∈ G - H), Q = S × Q₁ (coprime, D fixed-point-free on Q₁), 𝒮 = {χ ∈ Irr(H) : Q₁ ⊄ ker χ}。このとき **d odd ⟹ 𝒮 coherent w.r.t. Ind isometry**。_

### 証明の肝

**(1)** |Q₁| が 2 つ以上の素数で割り切られる場合: 𝒮(S') coherent
- Nilpotent S の chief factor 分析で、character 次数の divisibility 制約を使う

**(2)** 𝒮(S') coherent ⟹ 𝒮 coherent
- Non-abelian Q₁ への帰納的削減

**(3)** Z = [Q₁, Q₁] ∩ Z(Q₁) ≠ 1 に対し、𝒳 = 𝒮 - 𝒮(Z) coherent
- Character 次数の divisibility chain で recursion

**(4)–(8)** 最終段階: 
- 𝒴 = 𝒮(Q') (別の coherent set) との **orthogonality** 証明 (step 5)
- Ind_H^G による character lifting の compatibility (step 6)
- Central element 上の congruence argument (step 7)

**Remark**: d even の場合も論じられるが、Q₁ abelian, |Q₁| > d+1 or S ≠ 1 条件の下で同様に成立。

### FT での役割

- Character table の global な consistency をチェック
- Brauer-Suzuki theorem + Feit-Thompson (odd order solvable) からの deduction
- Near-field, Suzuki 2-群パターンの各ケース分析に適用される

**mathlib への寄与**: **中** (character coherence は specialized, 一般的な理論体系では稀)

**形式化優先度**: **中** (Phase 2b 第 7 波でカバー予定, full character coherence は複雑)

---

## 共通: mathlib カバレッジ (完全新規)

### 現状

- **Group theory**: p-groups, nilpotent groups, Hall subgroups は OK
- **Character theory**: 基本定義と induction あり
- **Missing**:
  - Quadratic forms over **F**₂ (App.D)
  - Near-field 構造と Zassenhaus 分類 (App.C)
  - Coherent character family の full framework (App.E)
  - Huppert 二重推移群定理の形式化 (App.B)

### 推奨順序

1. **App.D (Suzuki 2-群)**: quadratic form library 構築が最優先
2. **App.C (Near-fields)**: field extension, Galois theory とのリンク
3. **App.E (Feit-Sibley)**: coherence predicate, character space の abstract algebra
4. **App.B (Huppert)**: 基本定理だが、他と独立可能

---

## Phase 2b 形式化着手順 (本体完了後, optional)

### Timeline

**2026年後半 (Phase 2a 完了後)**:
1. App.D (Suzuki 2-群) quadratic form infrastructure
2. App.C (near-field) 並列着手
3. App.E (Feit-Sibley) character coherence framework 構築
4. App.B (Huppert) 最後に補足

### 各付録の形式化チェックリスト

#### App.B (Huppert)
- [ ] Huppert.SpecialCase.Prop1: Faithful, transitive odd-order group structure
- [ ] Lemma: odd-order p-group with uniform stabilizer sizes → cyclic

#### App.C (Near-Fields)
- [ ] NearField: Definition and construction
- [ ] NearFieldEquiv: G ≅ L(F) ⋊ Σ for 2-rank 1 case
- [ ] NearFieldDivisor: F_{r²,2} type classification

#### App.D (Suzuki 2-Groups)
- [ ] QuadraticForm: Bilinear-to-quadratic isomorphism
- [ ] Suzuki2Group: Definition, involution set = Z^#
- [ ] Suzuki2GroupTypeA, TypeB: Explicit constructions via A(n,φ), B(n,φ,ε)
- [ ] Higman.Classification: Theorem (a)–(e) with involution orbits
- [ ] Aut(B(n,1)): Surjection to semilinear automorphisms

#### App.E (Feit-Sibley)
- [ ] CoherentCharacterFamily: ⟨S, τ⟩ definition
- [ ] CharacterIsometry: Ind_H^G as Z[Irr] isometry
- [ ] FeitSibley.Main: Coherence under (|D|, |Q|) = 1, fixed-point-free, odd d
- [ ] Lemma 1(a), 1(b): Coherence sufficient conditions
- [ ] Step (1)–(8): Inductive proof with divisibility and orthogonality

---

## 未解決 / TODO

### 短期 (論文調査)

- [ ] App.B: Huppert 原論文 (1957) の exact statement との照合
- [ ] App.C: Zassenhaus (1958) near-field 分類の完全リスト確認
- [ ] App.D: Higman (1966) [Hi] 原論文での Type C, D の定義確認
- [ ] App.E: Sibley (1970s) の coherence theorem 全般確認

### 中期 (形式化設計)

- [ ] Quadratic form library の「最小」スコープ定義（2026Q3）
- [ ] Character coherence の abstract predicate 設計（2026Q3）
- [ ] Odd-order group の FT 経由での可解性との connection check

### 長期 (形式化実装)

- [ ] App.D quadratic form の concrete computation（2026Q4）
- [ ] App.E の character table global consistency checker（2027Q1 可能性）
- [ ] All 4 appendices の cross-reference validation suite

---

## 参考文献

- [H] Huppert, *Endliche Gruppen I* (1967)
- [HB] Huppert-Black, *Finite Groups II, III* (1982, 1982)
- [Is] Isaacs, *Character Theory of Finite Groups* (1976)
- [F] Feit, *Characters of Finite Groups* (1967) + coherence theorem
- [Si] Sibley (1970s), coherence generalization
- [Z] Zassenhaus, *Finite near-fields* classification
- [Hi] Higman, *Suzuki 2-groups classification* (1966)
- [S2] Suzuki, *Group Theory I* (1982)

---

**Created**: 2026-05-22
**Project**: OddOrder Lean 4
**Phase**: 2b (Post-Main Body, Optional)
**Status**: ✓ Survey complete, await Phase 2a completion for formalization start
