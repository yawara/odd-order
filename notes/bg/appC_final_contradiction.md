# BG App.C: The Final Contradiction — mini-roadmap

**スコープ**: BG Appendix C (pp. 145–152), mmd L4759–5005 (246 行), 3 結果 (Theorem C, Lemma C.1, C.2) + (I)–(XI) preliminary remarks. 形式化先 (予定): `OddOrder/BG/AppC_FinalContradiction.lean` (Phase 2b §9 統合、section docstring 中心). ROADMAP 上の位置: **Phase 2a 第 5–6 波** (Phase 2b §9 と並行 or §9 完成後). 役割: **FT 最終矛盾の generator-relation argument 版**. Peterfalvi §9 と統合実装.

---

## TL;DR — Peterfalvi 1984 paper の編集再録、Phase 2b §9 と統合

**BG App.C の位置づけ**:
- Feit-Thompson 1963 原論文の最終章 (Ch.VI, 17 ページ generator-relation argument) を **Peterfalvi 1984 paper [22]** が大幅簡略化した成果.
- BG が採録したのは、Peterfalvi 論文を **Walter Carlip & Wayne W. Wheeler** が University of Chicago Junior Group Theory Seminar 向けに再編した解説版 [2].

**本プロジェクトでの扱い**:
- **Peterfalvi §9** (pp. 38–43 本体、162 行) と **BG App.C** (pp. 145–152、246 行) は **論理的に同一内容**.
- Peterfalvi は **指標論的** アプローチ (Dade isometry + Coherence)
- BG は **有限体代数的** アプローチ (Frobenius 群、norm 計算、Galois theory)
- **形式化方針**: Peterfalvi §9 を一次、BG App.C を二次 (整合性確認 + section docstring 中心).

**FT 最終矛盾の役割**: 
- Phase 2a §1–§16 の局所解析結果 + Phase 2b §3–§8 の指標論結果 → **最小反例 G の不存在を導く**
- **Theorem C**: primes p, q が条件 (A) と仮説 (B) を満たす場合 **p ≤ q** (矛盾: 最小反例なら p > q だから)

---

## App.C 全 3 結果 + (I)–(XI) preliminary remarks（完全一覧）

| # | 種別 | mmd 行 | ステートメント要約 | 役割 |
|---|------|--------|-------------------|------|
| **Theorem C** | **Main** | L4765–4773 | primes p, q が (A) `gcd((p^q-1)/(p-1), p-1)=1` + 仮説 (B) (埋め込み σ: H→G, Q abelian p'-group, y∈Q, normalization conditions) ⇒ **p ≤ q** | **FT final contradiction** の statement |
| **Lemma C.1** | **Key lemma** | L4815–4826 | E=E^{-1} ∧ \|E\|≥2 ⇒ p ≤ q | Lemma C.2, C.3 から導く |
| **Lemma C.2** | **Lemma** | L4827–4872 | \|E\|≥2 (q≥5 と q=3 の分岐) | Theorem C 前置き |
| **Lemma C.3** | **Long lemma** | L4875–5002 | E=E^{-1} (Step 1–4: generator-relation argument の核) | Theorem C の最大難所 |
| **(I)** | **Remark** | L4777–4781 | Condition (A) ≡ q ∤ (p-1) (gcd 条件と割切性の equivalence) | 条件の簡潔化 |
| **(II)** | **Remark** | L4783–4786 | Peterfalvi 例: p=2, G=SL(2,2^q) で仮説 (B) 充足 | 仮説の非自明性確認 |
| **(III)** | **Remark** | L4787–4788 | 最小反例 G ⟹ p>q (FT Thm 27.1, Lem 38.1 から導出) | Theorem C 矛盾の出所 |
| **(IV)** | **Remark** | L4789–4790 | 拡張: p≤3 (Norton-Glauberman [12] から) | Phase 3 精密化 |
| **(V)** | **Remark** | L4791–4792 | p, q 奇素数 と仮定可 | Proof の簡略化 |
| **(VI)** | **Remark** | L4793–4794 | H を G に埋め込み済みとし、P の演算を乗法化 | notation change |
| **(VII)** | **Remark** | L4795–4798 | Galois theory (Frob automorphism α: x↦x^p, U cyclic by Satz 90) | norm 計算の基礎 |
| **(VIII)** | **Remark** | L4799–4800 | F_{p^q}^* = F_p^* × U (by condition A) | Frobenius 群の TI-subset 条件 |
| **(IX)** | **Remark** | L4801–4802 | H は Frobenius 群 (kernel P, complement U) | Coherence 適用正当化 |
| **(X)** | **Remark** | L4803–4804 | Q = C_Q(P_0) ⊕ [Q, P_0] (p-group 分解) | y の置き方の自由度 |
| **(XI)** | **Remark** | L4805–4806 | y ∈ [Q, P_0] と仮定可 | Step 1 の前置き |

**付加**: **Notation**: norm N(a), set E = {a ∈ F_{p^q} : N(a)=N(2-a)=1} (L4807–4809).

---

## Theorem C のステートメント（精密解析）

### 前置き: Frobenius 群 H = P ⋊ U の構成

**Set-up** (BG L4765–4809):
- **F_{p^q}**: 有限体, order p^q
- **P = F_{p^q}^+**: 加法群 (abelian, order p^q)
- **P_0 ⊆ P**: F_p の像 (additive subgroup, order p)
- **U ⊆ (F_{p^q})^*** : norm-1 部分群 (Satz 90: cyclic of order (p^q-1)/(p-1))
- **H = P ⋊ U**: semidirect product (U acts on P by multiplication)

**Condition (A)** (L4765–4767):
$$\gcd\left(\frac{p^q-1}{p-1}, p-1\right) = 1$$
Remark (I): 同値 — **q ∤ (p-1)**.

### Hypothesis (B) (L4769–4771)

G を群として:
1. **Monomorphism σ: H → G**
2. **Q ⊆ G**: finite abelian p'-subgroup (p' = complement of {p})
3. **y ∈ Q**: element
4. **σ(P_0)** normalizes **Q**
5. **σ(P_0)^y** normalizes **U** (U is image σ(U) in G)

### Main Statement (L4773)

$$\boxed{p \leq q}$$

---

## (I)–(XI) Preliminary Remarks の役割と Peterfalvi 対応

### 役割の体系

| Remark | 内容 | 機能 | Peterfalvi 対応 |
|--------|------|------|-----------------|
| (I)–(II) | Condition (A) 同値化, 例示 | **仮説の簡潔化 + 非自明性** | (7.4)–(7.5) 仮説設定 |
| (III)–(V) | 最小反例/奇素数 | **矛盾の出所 + proof 簡略化** | (7.10)–(7.11) 構造定理背景 |
| (VI)–(VIII) | notation, Galois theory, TI-subset | **代数的基盤 (Satz 90, F_p^* × U)** | (2.5)–(2.6) Dade 計算基礎 |
| (IX)–(XI) | Frobenius, Q 分解, y 選択 | **Generator-relation 準備** | (7.6)–(7.8) Coherence application |

### Galois Theory の role: (VII)

BG Remark (VII) (L4795–4798):
$$\text{Gal}(F_{p^q}/F_p) = \langle \alpha \rangle, \quad x^\alpha = x^p$$
$$U = \left\{\frac{x}{x^\alpha} : x \in F_{p^q}^*\right\} \text{ (cyclic of order } \frac{p^q-1}{p-1}\text{)}$$

**Hilbert Satz 90** による U の cyclic 性 → norm map N: F_{p^q}^* → F_p^* の kernel.

**Peterfalvi §9 対応**: (7.1)–(7.3) の ρ (Dade isometry) の下で、norm 計算は (2.5)–(2.6) 指標論計算と dual.

---

## mmd L4763 Nougat 抽出ミスの確認と実際の App.C 範囲

### 問題の詳細

| 詳細 | 記載 |
|------|------|
| **mmd L4763** | `## Appendix D The Main Theorem` (見出し) |
| **実際の内容** | L4765–4809 は **Theorem C の statement + Remarks (I)–(XI)** = **App.C 本体の続き** |
| **誤りの原因** | Nougat PDF 抽出時に、**App.D (CN-Groups) の見出し** (mmd L5006 実体) と **App.C の定理 statement** が誤って "Appendix D The Main Theorem" で統合 |
| **実体的構成** | 「Appendix D」という見出しが L4763 に誤配置。実際は L4759–5005 全体が App.C, L5006 以降が App.D |

### PDF 確認結果

- **BG PDF p. 145**: "## Appendix C: The Final Contradiction" (correct)
- **BG PDF p. 145–152**: App.C 本体 (Theorem C + Remarks + Lemmas)
- **BG PDF p. 152–end**: App.D (CN-Groups)

**結論**: mmd L4759–5005 **全体が App.C**. L4763 の `## Appendix D` は **Nougat 誤認**, 形式化時には無視して L4759 から L5005 までを連続して扱う.

---

## Lemma C.1, C.2, C.3 の役割と証明スケッチ

### Lemma C.2: |E| ≥ 2 (L4827–4872)

**Statement**: 
$$E = \{a \in F_{p^q} : N(a)=N(2-a)=1\} \text{ has } |E| \geq 2.$$

**証明スケッチ** (BG L4827–4872):
- **q ≥ 5 の場合**: Frobenius 群 H の共役類和 argument (group algebra, Theorem 4.2.12). norm 計算で |E| = character 係数 → p^{q-2} - p^{q/2} > 1.
- **q = 3 の場合**: polynomial f_c(x) = x(x-2)(x-c)+(x-1) ∈ F_p[x] の根の存在性を Galois 理論で検討. ∃c s.t. f_c は F_p に根なくても F_{p^3} に根 a 持つ → N(a)=N(2-a)=1 から 1, a ∈ E → |E|≥2.

**役割**: Theorem C の前置き. Lemma C.1 が |E|≥2 と E=E^{-1} を合わせて p≤q を導くため.

### Lemma C.1: E=E^{-1} ∧ |E|≥2 ⇒ p ≤ q (L4815–4826)

**Statement**:
$$E=E^{-1} \text{ and } |E| \geq 2 \Rightarrow p \leq q$$

**証明スケッチ** (BG L4815–4826):
- ∀a ∈ E^#: N(1-a) ≠ 0 (a ≠ 1)
- τ(a) := 1/(2-a) ∈ E (if E=E^{-1})
- **Induction**: τ^k(a) = [k-(k-1)a] / [(k+1)-ka] ∈ E
- **Norm計算**: N((1-a)x+1) = N(1-a)x^q + ... + Tr(1-a)x (polynomial in x)
- 全 k ∈ F_p で N((1-a)k+1)=1 成立 → 次数 q の多項式が p 個の根 → **q ≥ p**.

**Peterfalvi 対応**: (7.10) Theorem の構造定理 (複数 Frobenius 族の数値下界) の BG 有限体版 = norm 計算による直接証明.

### Lemma C.3: E=E^{-1} (L4875–5002)

**Statement**: 
$$E = E^{-1}$$

**Proof構造** (4 Steps):

**Step 1** (L4881–4883): ∀x ∈ PU ⟹ ∃u,v ∈ U, s_1 ∈ P_0 s.t. x=us_1v (Frattini分解).

**Step 2** (L4885–4890): s_1us_2 ∈ U ⇒ (s_1=s_2=1) ∨ (u=1, s_1s_2=1) (generator-relation의 핵심: U과 P_0의 교차불가능성).

**Step 3** (L4892–4896): t_1 ∈ P_1^# ⇒ (PU) ∩ (PU)^{t_1} = U (P_1 = P_0^y 경유의 교집합).

**Step 4** (L4898–5002): 関係式 (C.2)–(C.10) から
- s_1t_1^{-1}t^{-1} = t^{-1}t_3^{-1}s_3
- y の固定点への制約 (kernel argument)
- y ∈ [Q, P_0] 下での Frobenius 작用 反복 (t^{3n})
- a^{-1} ∈ E を귀납적に導出

**著者による注**: L4876–4878 で「p=3 の場合は簡単」と述べ、一般의 p (especially p>3) では Step 4가 複잡.

**Peterfalvi対応**: (7.6)–(7.9)–(7.10) の Coherence + 複数族 non-orthogonality (반쌍곡성) と dual: BG는 관계식으로직접証명, Peterfalvi는지표論으로증명.

---

## Peterfalvi §9 (7.6) との完全対応マップ

### 병렬 결과 比較

| Peterfalvi (§9) | BG App.C | 형식화時の処理 |
|-----------------|----------|-------------|
| **(7.1) Dade isometry ρ 정의** | **(VI)–(VII) Frobenius H notation** | 기호변환: ρ ↔ σ (작용의幾何화) |
| **(7.2) ρ-τ 성질 (\|\|χ^ρ\|\| ≤ \|\|χ\|\|)** | **(VIII)–(IX) F_p^* × U, H Frobenius** | 正規化構造로치환 |
| **(7.3) 적분부등식** | **(VII) Satz 90 (U cyclic)** | norm완전성로대체 |
| **(7.4)–(7.5) 複数 TI-subset 족** | **(X)–(XI) Q 분해, y선택** | 설정の단순화 (1족→1원소y) |
| **(7.6)–(7.8) Coherence + 계산** | **Lemma C.2, C.3 (norm계산)** | 指標論→대수적계산で증명 |
| **(7.9) 2족 non-orthogonality** | **Lemma C.3 Step 2–3 (s_1, u交차불가)** | 관계식의核心 (반쌍곡성) |
| **(7.10) k≥2族 구조정리** | **Lemma C.1 (다항식≥p근)** | 수치下界의具体화 |
| **THEOREM (7.11)**: $G_0=\{1\}$ 불가능 | **Theorem C**: 仮説(A)–(B) ⇒ p≤q | **동일한비존재** (지표論vs유한체) |

---

## 형式化方針 (Peterfalvi §9 一次、BG App.C 二次)

### 통합전략：案 A (推奨、最小二重化)

**实装位置**: `OddOrder/Peterfalvi/S09_NonExistenceCertainGroup.lean` (주요 실装)

**BG App.C의역할**:
- Section docstring에서 "Carlip-Wheeler edit [2] 경유의概要"명記
- Theorem C 형식化시 norm计算참조
- Lemma C.1/C.2/C.3는 (7.6)–(7.10)–(7.11)의보조보기로统合

### 파일구成

```
OddOrder/Peterfalvi/S09_NonExistenceCertainGroup.lean
  ├── /-- § App.C (BG) との対応: Carlip-Wheeler 編集版 [2]
  │      指標論的(Dade) vs 有限体代数的(norm) 의證明方針 --/
  │
  ├── def FrobeniusGroup.H (p q : ℕ) : Group
  │   /-- = P ⋊ U, P = F_{p^q}^+, U = norm-1 subgroup --/
  │
  ├── lemma condition_A_equiv (p q : ℕ) : 
  │     gcd((p^q-1)/(p-1), p-1) = 1 ↔ ¬(q ∣ (p-1))
  │   /-- Remark (I) --/
  │
  ├── structure Hypothesis_B (G : Type*) [Group G] (p q : ℕ) : Prop
  │   /-- σ: H ↪→ G, Q abelian p'-group, normalization conditions --/
  │
  ├── lemma lemmaC2_card_E_ge_two : |E| ≥ 2
  │   /-- (L4827–4872): Frobenius character sum + q=3 polynomial --/
  │
  ├── lemma lemmaC3_E_inv_closed : E = E⁻¹
  │   /-- (L4875–5002): Step 1–4, generator-relation by y ∈ [Q,P_0] --/
  │
  ├── lemma lemmaC1_main : E=E⁻¹ ∧ |E|≥2 → p ≤ q
  │   /-- (L4815–4826): polynomial root count argument --/
  │
  ├── theorem TheoremC (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
  │     (hA : condition_A p q) (G : Type*) [Group G] (hB : Hypothesis_B G p q) :
  │     p ≤ q
  │   /-- Main: Lemma C.1/C.2/C.3 を統合 --/
  │
  └── theorem NonExistence_Structure : 
        仮説(7.10) ∧ G_0={1} → false
      /-- (7.11) Theorem: FT 矛盾完成 --/

OddOrder/FiniteField/Norm.lean (새로운, 공용)
  ├── def norm : F_{p^q} → F_p
  ├── lemma norm_multiplicative
  ├── lemma norm_surjective : N: (F_{p^q})^* → F_p^* surjective
  └── /-- Satz 90 응용: U = ker(N) cyclic --/
```

---

## Phase 3 での結合: equivalence lemma

**當面の形式化**: Phase 2b §9 で Peterfalvi §9 (= Theorem (7.11)) 형式化.

**Phase 3 時점**:
- §10–§15 (BG のみ): maximal subgroup family, counting, Type-𝒫 analysis
- **§16 + App.C**: 최小반례 G의구조 → 仮説 (7.10) instantiation

**最終統合**:
```lean
-- Phase 3: BG §16 + Peterfalvi §9 の統合
theorem FeitThompsonContradiction (G : Type*) [Group G] [Fintype G] 
    (hOdd : Odd G.card) (hMinimal : IsMinimalCounterexample G) :
    false := by
  -- §16 (BG): minimal counterexample G の structure
  have h_structure : SatisfiesHypothesis_710 G := sorry
  
  -- §9 (Peterfalvi): Hypothesis (7.10) + G_0={1} ⇒ false
  have h_contradiction := NonExistence_Structure h_structure
  
  exact h_contradiction
```

---

## mathlib カバレッジ

| 領域 | カバレッジ | 説明 |
|------|-----------|------|
| **Finite Field API** | **HIGH** | `FiniteField p q`, Frobenius automorphism, field extension |
| **Algebra.Norm** | **HIGH** | Field extension norm function (F_pq → F_p) |
| **Hilbert Satz 90** | **MID** | norm-1 subgroup の cyclicity (mathlib にあるか確認要) |
| **Semidirect Product** | **HIGH** | `SemidirectProduct`, `IsFrobeniusGroup` |
| **Thompson J-subgroup** | **LOW** | Phase 1 Ch.7 で新規実装予定 |
| **Dade Isometry** | **LOW** | Phase 2b §4 で新規実装予定 |
| **Coherence** | **LOW** | Phase 2b §7–§8 で新規実装予定 |

---

## 未解決 / TODO

### 優先度 HIGH

1. **mmd L4763 Nougat 誤認の扱い**: 形式化時に section 開始を L4759 にすること、見出し `## Appendix D The Main Theorem` は無視.

2. **Norm function の mathlib 連携**: `Algebra.Norm` が F_pq → F_p に直結するか。Field extension algebra 設定の重さを確認.

3. **Satz 90 実装**: U = ker(N) が cyclic of order (p^q-1)/(p-1) であることの Lean 証明.

4. **Lemma C.3 Step 1–4 の Lean 翻訳**: (C.2)–(C.10) の長い関係式。自動化困難、phase 3 で deferred 検討.

### 優先度 MID

5. **Peterfalvi §9 (7.6)–(7.8) Coherence との完全対応確認**: 形式化時に指標論と有限体代数の dual がどのレベルで exact correspondence か確認.

6. **BG App.C 参照の文献化**: Carlip-Wheeler [2], Peterfalvi [22] の正確な citation style.

7. **Condition (A) 数値計算**: gcd((p^q-1)/(p-1), p-1) = 1 を Lean `Nat.gcd` tactic で処理可能か.

### 優先度 LOW

8. **App.C vs App.D 標題の混同防止**: ドキュメント / section docstring で明確化.

9. **Problem 1 (L5004–5005)**: "p=3 可能か" という open problem。Phase 3 で検討対象.

---

## 参考：BG App.C の詳細構成

```
L4759–4761  : 序論 (Peterfalvi 1984 論文の再編)
L4762–4764  : 見出し (Nougat 誤認: `## Appendix D The Main Theorem`)
L4765–4773  : **Theorem C** statement
L4774–4809  : **Preliminary Remarks (I)–(XI)** + Notation (norm, E)
L4811–4815  : Proof 開始
L4815–4826  : **Lemma C.1**
L4827–4872  : **Lemma C.2** (q≥5 と q=3 分岐)
L4875–5002  : **Lemma C.3** (Step 1–4)
L5004–5005  : Problem 1
```

**計**: 1 Theorem (メイン) + 3 Lemmas + 11 Remarks = **15 結果項目**.

---

## Phase 2b §9 との統合時程表

| 波 | 内容 | 期間 (見積) | 依存 |
|----|------|-----------|------|
| Phase 2b Week 6 | §8 (Coherence) 完成 | 1 週 | §7 完成 |
| **Phase 2b Week 7** | **§9 (Theorem (7.11) + App.C norm version)** | **3–4 日** | §8 終 |
| Phase 2b Week 8–12 | §10–§15 (BG maximal family) | 5 週 | BG Ch.3 終 |
| Phase 2b Week 13 | §16 (BG Main Results) | 1 週 | §15 終 |
| **Phase 3** | **統合: §16 + §9 + App.C ⇒ FT 矛盾** | **2–3 週** | 本体完成 |

---

## 结论

**BG App.C は Peterfalvi 1984 paper の Carlip-Wheeler 編集版であり、指標論的証明（Peterfalvi §9）と有限体代数的証明（App.C）が完全に dual である。形式化は Peterfalvi §9 を主軸とし、App.C は norm 計算と有限体代数の補助資料として機能させる方針が最適。**

FT 最終矛盾達成の鍵は Lemma C.3 の generator-relation argument (Step 1–4) であり、これを Lean で形式化することが Phase 3 の最大課題となる。

---

*作成: 2026-05-22. 出典: `references/bg/local-analysis.mmd` (L4759–5005), PDF pp. 145–152. 参考: `notes/peterfalvi/s09_nonexistence_certain.md`, `notes/bg/_overview.md`, `notes/bg/s06_additional.md`. Phase 2b 第 4 波 (§9) + Phase 3 統合の roadmap に組み込み。*
