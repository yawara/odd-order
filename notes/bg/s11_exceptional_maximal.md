# BG §11: Exceptional Maximal Subgroups — mini-roadmap

**スコープ**: BG §11 (pp.80-82 in BG PDF), mmd L2913-3022, **4 結果**.  
**形式化先 (予定)**: `OddOrder/BG/Ch3_MaximalSubgroups/S11_ExceptionalMaximal.lean`  
**ROADMAP 上の位置**: Phase 2a 第 4 波（§10 完成必須）  
**役割**: 例外的 maximal subgroup M の精密構造定理. σ(M)' における素数 p に対する M_σ の性質を確立. §12 "部分群 E" の理論的基盤.

---

## TL;DR: Hypothesis 11.1 下での maximal subgroup の病理学

§11 は短編(4 結果, 110 行)ながら **highly technical** な局所化セクション. 最小反例 G が「expected」と異なる構造を持つ maximal subgroup M を分析する必須ステップ.

**中核概念**: M が「**exceptional**」 ⟺ p ∈ σ(M)' (σ に属さない) でありながら，Hypothesis 11.1 の条件 (N_G(A₀) ⊆ M for A₀ ∈ ℰ_p¹(M)) を満たす場合.

**3 つの主要性質** (Thm 11.3, 11.5, 11.7):
1. **M_σ is nilpotent** (Thm 11.3)
2. **Sylow p-subgroups of M are abelian** (Thm 11.5)
3. **M_σA ⊲ M** where A ∈ ℰ_p²(M) (Thm 11.7)

これら 3 つは **Hypothesis 11.1 の entire content を determinate** し，§12 の τ₂(M) ≠ ∅ case に直結.

---

## §11 全 4 結果（表）

| # | 名前 | mmd 行 | 型 | 要旨 | 依存先 |
|---|------|--------|-----|------|--------|
| 1 | **Lemma 11.1** | 2938–2944 | Lemma(a-b) | Conjugate Sylow q-subgroups は disjoint; X ∈ ℰ¹(A) なら C_{Q_1}(X)=1 or C_{Q_2}(X)=1 | Thm 7.6 (Thompson Transitivity), Prop 7.5, Lem 7.1 |
| 2 | **Corollary 11.2** | 2946–2953 | Corollary(a-b) | M_σ ∩ M^g = 1; M_σ ∩ C_G(A_0^g) = 1 | Lem 11.1, Prop 1.5 (Sylow conjugacy) |
| 3 | **Theorem 11.3** | 2955–2957 | Theorem | M_σ is nilpotent | Cor 11.2(b), Thm 3.7 (fixed-point-free action) |
| 4 | **Corollary 11.4** | 2959–2961 | Corollary | H ∈ ℳ(A), M_σ ∩ H_σ ≠ 1 ⟹ M = H | Lem 10.12(b) (M_σ nilpotent ⟹ H conjugate to M) |
| 5 | **Theorem 11.5** | 2963–2975 | Theorem | Sylow p-subgroups of M are abelian | Lem 11.1(b), Prop 1.16 (elementary abelian generation), Lem 10.13(c) (Ω₁ structure) |
| 6 | **Corollary 11.6** | 2977–2993 | Corollary(a-c) | A = Ω₁(P); C_{M_σ}(A)=1; C_{M_σ}(A_1)=C_{M_σ}(A_2)=1 | Cor 11.2(b), rank argument in N_G(P) |
| 7 | **Theorem 11.7** | 2997–3021 | Theorem | M_σA ⊲ M | Lem 11.1 / Lem 10.11(d) (commutator control via Prop 1.6), Prop 10.11(d) |

**統計**: 2 Theorem + 3 Corollary + 2 Lemma = **7 結果** (mmd では引用関係を "主 4 + 補助 3" と分類すると，Thm 11.5 直前の段落説明で主 3 個と明記).

---

## Hypothesis 11.1: 病理的 maximal の定義

### 文脈と意図 (L2915–2931)

```
M ∈ ℳ,  p ∈ σ(M)',  A_0 ∈ ℰ_p¹(M),  N_G(A_0) ⊆ M
```

**意図**: 通常 N_G(A_0) ⊆ M (for A_0 ∈ ℰ_p¹(G)) かつ p ∉ σ(M) なら，**G は p-rank 1 構造が「健全」と期待** される. しかし最小反例では，このような M が存在し得る. 

### 仮説の 3 推論 (L2917–2929)

**By Lemma 10.5**, r_p(M) = 2 かつ A_0 ⊆ A for some A ∈ ℰ_p²(M).

**Key fact**: p ∉ σ(M) なので，N_G(P) ⊄ M (P = Sylow p of M). しかし:

```
C_G(A) ⊆ C_G(A_0) ⊆ M
    ↓
A ∈ ℰ_p*(G)  [exceptional at p for G]
```

**定義**: M is **exceptional maximal subgroup** ⟺ 上記条件下にあり，§11-§12 で 3 つの性質が成立する M.

### 理由と先読み (L2931–2935)

**Proposition 12.4** (§12 L3095–3126) では，**すべての maximal H with r(H/H_σ) = 2 are exceptional** と言い切る. §11 はその「core case」を isolated で研究.

**後続での活用**: §12 で M* ∈ ℳ(N_G(X)) for X ∈ ℰ_p¹(M) を検討するときに，M* が exceptional になる可能性が生じ，その場合 §11 の 3 性質が apply される.

---

## Lemma 11.1: Thompson 推移性の相対化

### 主張 (L2938–2942)

```
g ∈ G - M,  A ⊆ M^g,  q ∈ σ(M),
Q_1, Q_2: A-invariant Sylow q-subgroups of M_σ, M_σ^g
```

**(a)** Q_1 ∩ Q_2 = 1

**(b)** X ∈ ℰ¹(A) ⟹ C_{Q_1}(X) = 1 or C_{Q_2}(X) = 1

### 証明梗概 (L2943–2944)

**Step 1**: A ∈ ℰ_p*(G) ⟹ A satisfies Hypothesis 7.1 (by Prop 7.5, §7).

**Step 2**: Suppose (a) or (b) false. By Lemma 7.1 (Thompson Transitivity, Thm 7.6 の相対版), Q_2 = Q_1^k for some k ∈ C_G(A).

**Step 3**: C_G(A) ⊆ M ⟹ Q_2 ⊆ M. But then by Thm 10.1(d), g ∈ M. Contradiction.

### 役割

**Lemma 11.1** は §11 の「foundation lemma」. Thm 7.6 (Thompson Transitivity) を maximal subgroup の σ-側に制限し，conjugate Sylow q-subgroups の分離を確立. 後続の Corollary 11.2 と Thm 11.3 (nilpotency) に直結.

---

## Corollary 11.2: 共役性と non-intersection

### 主張 (L2946–2949)

```
g ∈ G - M,  A ⊆ M^g
```

**(a)** M_σ ∩ M^g = 1

**(b)** M_σ ∩ C_G(A_0^g) = 1

### 証明梗概 (L2950–2953)

**(a) 証明**: 反証法. q ∈ π(M_σ ∩ M^g) なら q ∈ σ(M). By Prop 1.5, A normalizes Sylow q-subgroups Q_0 ⊆ Q_1 ∩ Q_2 of M_σ ∩ M^g, M_σ, M_σ^g.

By Lemma 11.1(a), Q_1 ∩ Q_2 = 1 ⟹ Q_0 = 1. Contradiction.

**(b) 証明**: C_G(A_0^g) ⊆ M^g ⟹ from (a).

### 역할

**Corollary 11.2** は M_σ の「isolation」を確立. これは Thm 11.3 (nilpotency) で fixed-point-free action を set up する際の critical step.

---

## Theorem 11.3: M_σ の nilpotency

### 主장 (L2955)

```
M_σ is nilpotent.
```

### 증명 梗概 (L2956–2957)

**Step 1**: Take g ∈ N_G(P) - N_M(P) (possible since p ∉ σ(M) ⟹ N_G(P) ⊄ M).

**Step 2**: A_0^g ⊆ P ⊆ M, and A_0^g acts fixed-point-free on M_σ by Corollary 11.2(b).

**Step 3**: By Theorem 3.7 (fixed-point-free action ⟹ nilpotency), M_σ is nilpotent.

### 역할

**Theorem 11.3** は **§11 の最初の substantive result**. M_σ が nilpotent という事実は:
- Corollary 11.4 (maximal 一意性)
- Theorem 11.5 (abelian Sylow p)
- Theorem 11.7 (normality M_σA ⊲ M)

の 3 つすべてを可能にする foundation. さらに §12 Lemma 12.1 でも E' nilpotent として echo される.

---

## Corollary 11.4: Maximal 一意性

### 主장 (L2959)

```
H ∈ ℳ(A),  M_σ ∩ H_σ ≠ 1  ⟹  M = H
```

### 증명 梗概 (L2960–2961)

**Step 1**: M_σ nilpotent ⟹ by Lemma 10.12(b), H is conjugate to M, say H = M^g.

**Step 2**: M_σ ∩ H_σ ≠ 1 ⟹ M_σ ∩ M_σ^g ≠ 1.

**Step 3**: By Corollary 11.2(a), g ∈ M.

**Step 4**: Thus H = M^g = M.

### 역할

**Corollary 11.4** は M_σ の global properties から M の local uniqueness (at A) を推論. これは Lemma 10.12 との synergy を示す.

---

## Theorem 11.5: Sylow p-subgroups の abelianity

### 主장 (L2963)

```
The Sylow p-subgroups of M are abelian.
```

### 증명 梗概 (L2965–2975)

**Suppose P nonabelian** (goal: contradiction).

**Step 1**: Take g ∈ N_G(P) - N_M(P), q ∈ σ(M), Q_1 = A-invariant Sylow q-subgroup of M_σ.

**Step 2**: By Proposition 1.16,
```
Q_1 = ⟨C_{Q_1}(X) | X ∈ ℰ¹(A)⟩
Q_2 = Q_1^g = ⟨C_{Q_2}(X) | X ∈ ℰ¹(A)⟩
```

So ∃X_1, X_2 ∈ ℰ¹(A): C_{Q_1}(X_1) ≠ 1, C_{Q_2}(X_2) ≠ 1.

**Step 3**: By Lemma 11.1(b), ∀X ∈ ℰ¹(A), C_{Q_1}(X) = 1 or C_{Q_2}(X) = 1.

**Step 4**: So C_{Q_1}(X_2) = 1, hence X_2 ≁_P X_1 (not conjugate in P).

**Step 5**: By Lemma 10.13(c), all subgroups in ℰ¹(A) - {Ω₁(Z(P))} are conjugate in P.

**Step 6**: So {X_1, X_2} ∩ {Ω₁(Z(P))} has size ≥ 1. But X = Ω₁(Z(P)) ⟹ X = X^g ⟹ C_{Q_1}(X) = C_{Q_2}(X)^g ⟹ C_{Q_1}(X) = C_{Q_2}(X).

Combined with Lemma 11.1(b), C_{Q_1}(X) = C_{Q_2}(X) = 1. Contradiction.

### 역할

**Theorem 11.5** は Hypothesis 11.1 の second major consequence. Abelian Sylow p-subgroups は Thm 11.7 (normality of M_σA) の crucial step と，§12 での E structure (Lemma 12.1) で abelian case assumption を make possible にする.

---

## Corollary 11.6: Ω₁(P), C_{M_σ}(A), A₁ × A₂ 分解

### 주장 (L2977–2983)

P = abelian Sylow p-subgroup of M에 대해:

**(a)** A = Ω₁(P)

**(b)** C_{M_σ}(A) = 1

**(c)** C_{M_σ}(A_1) = C_{M_σ}(A_2) = 1

여기서 A_1 = A_0^{g_1}, A_2 = A_0^{g_2} (g_1, g_2 ∈ N_G(P) - N_M(P) 적절히 선택).

### 증명 梗概 (L2985–2993)

**Step 1**: P abelian, A ∈ ℰ²(P) ⟹ A = Ω₁(P) ⊲ N_G(P).

**Step 2**: N_G(P) ⊄ M (since p ∉ σ(M)) ⟹ |N_G(P) : N_M(P)| ≥ 3 (G has odd order).

**Step 3**: ∃g_1, g_2 ∈ N_G(P) - N_M(P) with g_1g_2^{-1} ∉ M ⟹ g_1g_2^{-1} ∉ N_G(A_0) ⟹ A_0^{g_1} ≠ A_0^{g_2}.

**Step 4**: A_0 ⊆ A ⊲ N_G(P) ⟹ A_1, A_2 ∈ A, distinct.

**Step 5**: By Cor 11.2(b), C_{M_σ}(A_1) = C_{M_σ}(A_2) = 1, hence C_{M_σ}(A) = 1.

### 역할

**Corollary 11.6** は Thm 11.7 의 proof 중 **최대 난제** (L3006–3020) 인 commutator control argument の foundation を set up. 특히 A_1 × A_2 분해와 [A_1, Q_0], [A_2, Q_0]의 각각이 normal in M이라는 argument에서 **essential data**.

---

## Theorem 11.7: M_σA ⊲ M (main result)

### 주장 (L2997)

```
M_σ A ⊲ M
```

여기서 A ∈ ℰ_p²(M), A ⊆ P (Sylow p of M), C_G(A) ⊆ M (from Hypothesis 11.1 setup).

### 증명梗概 (L2999–3021)

**Assume false** (goal: contradiction from Frattini-style argument).

**Step 1**: Let E = complement to M_σ in M containing A. Then r(E) = 2 (by Thm 10.2).

**Step 2**: τ = {q ∈ π(E) | q > p}, K = O_τ(E) (Hall τ-subgroup by Thm 4.20).

**Step 3**: By Cor 11.6(a), A = Ω₁(P). If A centralized K, then KA = K × A (coprime), A = Ω₁(O_p(KP)) ⊲ E, and M_σA ⊲ M (contradiction).

**Step 4**: So A does not centralize K. Take q | |K : C_K(A)|, Q = A-invariant Sylow q of K. Then [A, Q] ≠ 1.

**Step 5**: Suppose C_Q(A) ≠ 1. Then Q nonabelian, so r(Q) = 2. Let B ∈ ℰ²(Q). By Lemma 10.4(c), A, B ∈ ℰ_p*(G), B ∈ ℰ_q*(G).

Moreover, q ∈ π(C_Q(A)) ⊆ π(C_G(A)). Let Q ⊆ Q* ∈ H_G*(A;q) (Hall q-subgroup containing Q).

By Proposition 10.10(c), [A, Q*] = 1, contradicting [A, Q] ≠ 1.

**Step 6**: Therefore C_Q(A) = 1.

**Step 7**: By Prop 1.6(d), Z(Q) = [A, Z(Q)].

**Step 8**: With A_1, A_2 from Cor 11.6(c), A = A_1 × A_2 ⟹
```
Z(Q) = [A_1, Z(Q)][A_2, Z(Q)]
```

**Step 9**: By **Proposition 10.11(d)**, for each A_i, [A_i, Z(Q)] ⊲ M.

**Step 10**: So Z(Q) ⊲ M, hence N_G(Q) ⊆ N_G(Z(Q)) = M.

But Q is Sylow q of M and q ∉ σ(M) ⟹ contradiction (N_G(Q) ⊄ M expected).

---

### 증명의 핵심 논리

**Proposition 10.11(d)** 를 적용하려면:
```
M ∈ ℳ, K = σ(M)'-subgroup of M, P = A_i (abelian), 
[P, Z(K)] centralizes M_σ and is cyclic normal in M.
```

이 단계에서:
- K = Z(Q) (σ(M)'-subgroup)
- P = A_i (abelian p-subgroup)
- [P, Z(K)] = [A_i, Z(Q)] ⊲ M (Prop 10.11(d) 의 결론)

### 역할

**Theorem 11.7** 은 **§11 의 climax**, Hypothesis 11.1 아래에서 M_σ의 "globality"를 확립. 이는:
- §12 Lemma 12.1(e) (E_2 E_3 ⊲ E) 의 대응 version
- §12 Corollary 12.6 (C_G(A) ⊆ N_M(A) = E for A ∈ ℰ_p²(E)) 의 추진력

---

## §10 로부터의 継承

### Lemma 10.5 (補助)

Hypothesis 11.1 첫 문장에서:

```
N_G(A_0) ⊆ M, A_0 ∈ ℰ_p¹(M)
```

**By Lemma 10.5**, r_p(M) = 2 and A_0 ⊆ A for some A ∈ ℰ_p²(M).

**역할**: Hypothesis 11.1 の syntactic sugar를 unwrap.

### Theorem 10.1 사용

**Thm 10.1(d)**: p ∈ σ(M), X^g ⊆ M, X Sylow ⟹ g ∈ M.

**Lemma 11.1 증명** (L2944): C_G(A) ⊆ M에서 Q_2 ⊆ M이면 g ∈ M을 import.

### Theorem 10.2 상속

**Thm 10.2(c)**: M_σ ⊆ M'.

**Thm 11.7 증명**: M'/M_σ가 abelian rank ≤ 2 (complement E의 rank).

### Corollary 10.7 병렬화

**Cor 10.7(a)**: P = [P, V] ⊆ N_G(P)'.

**Thm 11.5 증명**: Abelian Sylow p의 guarantee와 Q_1 = ⟨C_{Q_1}(X)⟩ (Prop 1.16) 의 parallel structure.

### Lemma 10.12 (補助)

**Lem 10.12(b)**: M_σ nilpotent ⟹ any H ∈ ℳ(A) containing M_σ is conjugate to M.

**Cor 11.4** (L2961): "then H = M^g for g ∈ G, and ... g ∈ M".

### Lemma 10.13 (補助)

**Lem 10.13(c)**: r(P) = 2 (abelian) ⟹ all subgroups in ℰ¹(A) - {Ω₁(Z(P))} are conjugate in P.

**Thm 11.5 증명** (L2973): "all of the subgroups in ℰ¹(A)-{X}, where X=Ω₁(Z(P)), are conjugate in P".

### Lemma 10.4 (補助, 未标註)

**Location**: Thm 10.6 증명에서 인용.

**Content**: r_p(M) = 2, narrow P ⟹ ∃x ∈ Q (Sylow q of M'), C_{M_α}(x) is Z-group.

**Thm 11.7 증명** (L3008): "By Lemma 10.4(c), A and B lie in ℰ_p*(G) and ℰ_q*(G), respectively".

### Proposition 10.10(c) (補助)

**Location**: L2844–2854.

**Content**: A ∈ ℰ_p² ∩ ℰ_p*, Q ∈ H_G*(A;q), q ∈ π(C_G(A)) ⟹ [A, Q*] = 1 (under certain cyclic / narrow condition).

**Thm 11.7 증명** (L3009): "By Proposition 10.10(c), [A,Q*]=1, contrary to the fact that [A,Q]≠1".

### Proposition 10.11(d) (補助)

**Location**: L2856–2883.

**Content**: K = σ(M)'-subgroup of M, P = abelian, then [P, Z(K)] ⊲ M and is normal.

**Thm 11.7 증명** (L3020): "By Proposition 10.11(d), with K=Q_0 and P being A_1 and then A_2, both subgroups [A_1,Q_0] and [A_2,Q_0] are normal in M".

---

## §12-§13 への橋渡し

### Proposition 12.4: Exceptional maximal の一般化 (§12, L3095–3126)

**Main statement**: A ∈ ℰ_p²(M) ⟹ C_G(A) ⊆ M.

**Key paragraph** (L3101–3110): 
- "In the exceptional case when X ⊄ M_σ^*, we will have the situation described above (with M* and X in place of M and A_0)."
- つまり，§11 Hypothesis 11.1 は M* にも apply される.

**形式化予想**: Thm 11.3, 11.5, 11.7 の 3 つは Prop 12.4 の **setup と證明中に直接引用**.

### Theorem 12.5: τ₂(M) ≠ ∅ case (§12, L3129–3148)

**Main results**: M_σ nilpotent (Thm 11.3), Sylow p abelian (Thm 11.5), M_σA ⊲ M (Thm 11.7).

**引用**: "We will show that M_σ is nilpotent, M has abelian Sylow p-subgroups, and AM_σ ⊲ M (Theorems 11.3, 11.5, and 11.7)" (L2933).

### Section 13: Prime Action (未作成)

**予想構造**: τ₁, τ₂, τ₃ 側の M_σ 作用. Thm 11.7 (M_σA ⊲ M) から E/E' の structure が制御される.

---

## mathlib カバレッジ

| 概念 | mathlib 存在 | 新規実装要 | 注記 |
|------|-------------|----------|------|
| Hypothesis/仮設定 | mid | Partial | Hypothesis 11.1 自体は BG 独自. 前提 (r_p(M)=2, A_0 ∈ ℰ_p¹(M), N_G(A_0) ⊆ M) の unbundling が必要. |
| ℰ_p¹, ℰ_p² (elementary abelian) | high | No | mathlib has basic definitions. σ-exceptional の parametrization は §10 の σ(M) definition と同期. |
| Nilpotent group / fixed-point-free | high | No | mathlib has Nilpotent class. Thm 3.7 (fixed-point-free → nilpotent) は Phase 1 で実装. |
| σ(M) & σ(M)' partition | low | Yes | σ(M) definition is §10. σ(M)' = π(M) \ σ(M) は syntactic complement. |
| Sylow p-subgroup structure | high | No | Prop 1.16 (elementary abelian generation via centralizers) は §1 で. |
| Thompson Transitivity (Thm 7.6) | low | Yes | Phase 1 Ch.7. Lemma 11.1 は相対化版. |
| Proposition 10.11(d) (commutator control) | low | Yes | §10 補助. Thm 11.7 の **key tool**. Phase 2a 初期に form check. |

---

## Phase 2a 形式化着手順

### 準備

1. **§10 完成確認**: Thm 10.1–10.2, Lem 10.4, 10.5, 10.12, 10.13, Prop 10.10(c), 10.11(d).
2. **§1, §3, §4, §6, §7 の support lemmas**:
   - Prop 1.5 (Sylow conjugacy)
   - Prop 1.6(d) (commutator formula)
   - Prop 1.16 (elementary abelian generation)
   - Thm 3.7 (fixed-point-free → nilpotent)
   - Thm 4.20 (Hall subgroup via O_π)

### Phase 2a 第 4 波（§10 完成直後）

1. **Lemma 11.1** (40 行):
   - Hyp 7.1 verification (A ∈ ℰ_p*(G))
   - Lemma 7.1 + Thm 10.1(d) の gluing

2. **Corollary 11.2** (25 行):
   - Lemma 11.1 + Prop 1.5 の elementary algebra

3. **Theorem 11.3** (10 行):
   - Cor 11.2(b) + Thm 3.7 の direct application

4. **Corollary 11.4** (15 行):
   - Thm 11.3 + Lem 10.12(b) + Lem 11.1

5. **Theorem 11.5** (50 行):
   - **Technical peak**: Prop 1.16, Lem 11.1(b), Lem 10.13(c) の integration
   - Proof strategy:反証法で nonabelian P を仮定, Q_1, Q_2 の generation を Prop 1.16 で explicate, Lem 11.1(b) で contradiction drive.

6. **Corollary 11.6** (30 行):
   - Abelian P, abelian rank 2 structure
   - Cor 11.2(b) を 2 elements g_1, g_2 で apply

7. **Theorem 11.7** (80 行, **最難**):
   - **Proof strategy**:
     1. Assume M_σA ⊲ M is false (proof by contradiction)
     2. E complement ⟹ r(E) = 2 (by Thm 10.2(d))
     3. τ partition & Hall subgroup K (Thm 4.20)
     4. A = Ω₁(P) (Cor 11.6(a)) ⟹ if A cent. K, done (簡単)
     5. [A, Q] ≠ 1 ⟹ C_Q(A) ≠ 1 ⟹ nonabelian Q ⟹ r(Q) = 2
     6. Lemma 10.4(c) で A, B ∈ ℰ_p*, ℰ_q*
     7. Q ⊆ Q* ∈ H_G*(A;q) で Prop 10.10(c) apply ⟹ [A, Q*] = 1 (矛盾)
     8. C_Q(A) = 1 ⟹ Z(Q) = [A, Z(Q)] (Prop 1.6(d))
     9. A = A_1 × A_2 (Cor 11.6(c)) ⟹ Z(Q) = [A_1, Z(Q)][A_2, Z(Q)]
     10. **Prop 10.11(d)** で [A_i, Z(Q)] ⊲ M
     11. Z(Q) ⊲ M ⟹ N_G(Q) ⊆ M ⟹ final contradiction

---

## 未解決 / TODO

### Lemma 10.4 の正確な statement

**Location**: Thm 11.7 (L3008) で "By Lemma 10.4(c), ..." と引用.

**Expected content**: ℰ²(Q) ∩ ℰ*(Q) nonvoid or Q cyclic ⟹ ... (exact formulation is missing from detailed notes).

**Action**: §10 PDF p.87 (missing in mmd) を直接参照. または既存 BG PDF から Lem 10.4 を extract.

### Proposition 10.11(d) の統合

**Location**: Thm 11.7 (L3020).

**Challenge**: Proposition 10.11 is auxiliary in §10, defined as σ(M)'-subgroup conditions. Thm 11.7 では K = Z(Q), P = A_i で instantiate する際に **exact alignment** を verify.

**Action**: Prop 10.11 全 4 部を detail で list, Thm 11.7 context での適用を **per-lemma proof sketch** で refine.

### Lemma 10.13 の abelian structure

**Location**: Thm 11.5 (L2973) で "By Lemma 10.13(c), ...".

**Challenge**: Lem 10.13(c) は "all subgroups in ℰ¹(A) - {X} conjugate in P" と簡潔だが，**formal definition** は rank 2 abelian p-group P の構造定理に基づく.

**Action**: Lem 10.13 の full statement (a-c) を §10 ノートから transport and refine.

### Thompson Transitivity の相対化 (Lemma 7.1)

**Location**: Lemma 11.1 (L2944).

**Challenge**: "By Lemma 7.1 shows that Q_2 = Q_1^k ..." の Lemma 7.1 の reference が Thm 7.6 (Thompson Transitivity) の相対化. exact statement of Lemma 7.1 の確認.

**Action**: §7 ノート (s07_transitivity.md) から Lemma 7.1 のformal statement を verify.

---

## 参考文献（本セクション内）

**§11 内部**:
- **Lemma 11.1**: Thompson Transitivity (Thm 7.6), Prop 7.5, Lemma 7.1
- **Corollary 11.2**: Lemma 11.1, Prop 1.5
- **Theorem 11.3**: Cor 11.2, Thm 3.7
- **Corollary 11.4**: Thm 11.3, Lem 10.12(b)
- **Theorem 11.5**: Lem 11.1, Prop 1.16, Lem 10.13(c)
- **Corollary 11.6**: Thm 11.5, Cor 11.2
- **Theorem 11.7**: All above, Prop 1.6, Lem 10.4, Prop 10.10(c), Prop 10.11(d), Thm 4.20

**§10 依存**:
- **Lemma 10.5** (r_p(M) = 2 characterization)
- **Theorem 10.1** (Conjugacy control)
- **Theorem 10.2** (M' ⊇ M_σ, r(M/M_α) ≤ 2)
- **Lemma 10.4, 10.12, 10.13** (補助)
- **Proposition 10.10(c), 10.11(d)** (補助)

**§1, §3, §4, §6, §7 支援**:
- **Prop 1.5, 1.6(d), 1.16**
- **Thm 3.7** (fixed-point-free)
- **Thm 4.20** (Hall via O_π)
- **Thm 7.6, Lemma 7.1** (Thompson)

**§12 継承先**:
- **Prop 12.4** (Exceptional maximal existence)
- **Thm 12.5** (τ₂ case)
- **Lemma 12.1** (E structure, echo of Thm 11.3-11.7)

---

## Peterfalvi との対比（コンテキスト）

Peterfalvi チャプターでは minimal non-abelian simple group S の **exceptional structure** を separate に分析. BG §11 の maximal subgroup analysis と conceptually parallel だが，G (solvable) vs. S (non-abelian simple) の distinction で。

---

## 完成予想時期

- **形式化開始**: Phase 2a 第 4 波（§10 完了から 1 週間後）
- **完成目安**: 5–7 日（Thm 11.7 の detailed proof development が最大ボトルネック）
- **検収**: Prop 12.4 への §11 依存を明示的に track

---

*作成: 2026-05-22. 出典: `references/bg/local-analysis.mmd` L2913-3022 (7 結果を含む).*  
*§10 "M_α, M_σ" 完成直後の第 4 波着手ノード. Hypothesis 11.1 의 symptomatology から 3 つの main results (Thm 11.3, 11.5, 11.7) への logical flow を emphasize.*  
*§12 Lemma 12.1 との echo と Prop 12.4 への bridge 下での integration point を highlight.*  
*形式化詳細は per-lemma proof sketch として Phase 2a 波着手時に refine.*
