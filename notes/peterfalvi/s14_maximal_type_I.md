# Peterfalvi §14: Maximal Subgroups of Type I — 詳細 per-section ノート

**スコープ**: Peterfalvi §14 (pp.69-74, mmd `04.14_pp_69_74_Maximal_Subgroups_of_Type_I.mmd` 110 行)  
**結果数**: 13 結果 ((12.1)-(12.13)) + 補足 ((12.14)-(12.17)) = **計 17 個**  
**形式化先** (予定): `OddOrder/Peterfalvi/S14_MaximalI.lean`  
**ROADMAP 上の位置**: **Phase 2b 第 6 波** (§13 完成必須, §15 入力)  
**役割**: **Type I 最大部分群** (最複雑型) の精密構造. Frobenius 的性質、TI-subset / rank 2 / cyclic 3 サブ条件の論理関係、Dade isometry による指標論的制約を確立. §15 (S, T) と §16 (G 非存在) への direct input.

---

## TL;DR — Type I は最複雑な 3 サブケースを持つ最大部分群

Peterfalvi §14 は **Type I 最大部分群 M (13 個の補題 + 4 個の追加結果)** を分析する最重要節. §10 で定義された Type I (Definition (8.3): TI-subset OR rank 2 OR cyclic p'-part の 3 条件のいずれか) の **細部構造化**を行う.

**Main Theorem (12.7)**: すべての Type I 最大部分群は Frobenius group (kernel = M_F) である.

**構成**: (12.1)-(12.2) [Dade isometry + 指標分解] → (12.3) [multiple Type I 部分群の直交性] → (12.4)-(12.5) [制限写像 ρ による constant character] → (12.6) [coherence] → **(12.7) MAIN: Frobenius 定理** → (12.8)-(12.13) [反例存在仮定による矛盾導出]

**最大のポイント**:
- Type I の 3 条件 (TI / rank 2 / cyclic) は実は 1 つに統一される **可能性** を示唆
- (12.8)-(12.13): 「rank 2 Sylow が cyclic でない」と仮定すると矛盾 → 全員 cyclic forced
- **c = 1** (centralizer trivial, §15 で再登場) の準備

---

## §14 全 13 結果 + 補足 (表形式)

| # | 結果 | 型 | 頁 | 主張 | 文字数 | 難度 | 依存 |
|---|------|------|------|------|--------|------|------|
| **(12.1)** | Hypothesis | 仮説設定 | 69 | L maximal Type I, H=L_F, 𝒮={Ind_H^L θ}, τ Dade isometry | 150 | ◯ | (8.3) |
| **(12.2)** | Prop (a)-(b) | 指標分解 + Dade 定義領域 | 69 | (a) χ∈𝒮 ⇒ χ = Σ_φ∈S(χ) φ, degree constant; τ on Z[⋃S(χ), L^#]. (b) Hyp(5.2) holds, (φ-φ̄)^τ = Σ α ∈ R₁(φ), \|R₁(φ)\| = 2 | 480 | ◎ | (8.2.c), (1.7.c), (1.5.a), (1.2) |
| **(12.3)** | Prop | 複数型 I の直交性 | 69-70 | L₁, L₂ non-conjugate Type I ⇒ R(χ₁) ⊥ R(χ₂) | 320 | ◎ | (12.2), (5.9), (8.18.c) |
| **(12.4)** | Prop | character on TI coset | 70 | ψ ⊥ R(χ) all χ∈𝒮, x∈L-H ⇒ ψ constant on xH | 420 | ◎◎ | (8.12.c), (1.4), (1.5), (12.2), [Is] Lem 7.7 |
| **(12.5)** | Prop | ρ-reduction on H-H' | 70-71 | ψ⊥R(χ) ⇒ ψ^ρ constant on H-H' | 380 | ◎◎ | (12.4), (5.5), (5.7), (1.7.b) |
| **(12.6)** | Prop | Type I Frobenius ⇒ coherence | 71 | L Frobenius with kernel H ⇒ 𝒮⊂Irr L, 𝒮 coherent | 180 | ◯ | (8.3), (6.8), (5.7), (6.5), (8.2.a), [Is] Thm 6.34 |
| **(12.7)** | **Theorem** | **MAIN THEOREM** | 71 | **Every maximal M of Type I is Frobenius** | 50 | ◎◎◎ | (12.8)-(12.16) 参照 |
| **(12.8)** | Hypothesis | 反例仮定 | 71-72 | π ≠ ∅, p ∈ π s.t. M of Type I has non-cyclic Sylow_p/M_F. M, K=M_F, P₀ Sylow_p | 200 | ◯ | (8.8) case (b) |
| **(12.9)** | Prop | rank 2 Sylow | 72 | P₀ abelian rank 2. ∃L maximal P₀⊂L_s. ∃x∈Ω₁(P₀)^# s.t. C_K(x)⊄K', N_G((x))⊂M, C_G(x)⊄L | 240 | ◎◎ | (8.12.a), (8.17.a), (8.11), [BG] Prop 1.16, Lem 1.14, (8.12.b) |
| **(12.10)** | Prop | L is Type I Frobenius | 72 | H=L_F, L is Frobenius with kernel H (by exhaustion: not II, then III⇒cyclic⇒φ_contradiction, not Type I TI⇒φ_contradiction) | 600 | ◎◎◎ | (12.9), (10.10), (11.9.c), (9.7.b), (11.6), (8.6.a), (8.3), (8.1.c), (8.2.b) |
| **(12.11)** | Prop | M∩L 構造 | 72-73 | M∩L complement K, M∩L⊂H | 280 | ◎◎ | (12.9), (8.13.c1), (12.10), (9.1), (8.1.b) |
| **(12.12)** | Prop | complement cyclic | 73 | E complement H in L, e=\|E\|. E cyclic, e\|(p-1) or e\|(p+1) | 720 | ◎◎◎ | (8.1.c), (12.10), [BG] Thm 2.6(a), (12.11), (9.7.b), (12.9) |
| **(12.13)** | Notation | Dade extension 記号 | 73-74 | 𝒮, τ, τ₁, χ(1)=e, ψ=χ^{τ₁}, ρ | 150 | ◯ | (12.1), (12.6), (7.1) |
| **(12.14)** | Prop | ψ on xK 定数 | 74 | x as (12.9), g∈K ⇒ ψ(xg)=ψ^ρ(x)=χ(x) | 880 | ◎◎◎ | (12.3), (12.4), (5.5), (8.14), (7.8.a), (12.6), (7.8.a) |
| **(12.15)** | Prop | ρ_M上でψ整数 | 74-75 | g∈K^# ⇒ ψ^{ρ_M}(g)=ψ(g), ψ constant on K-K', ψ(g)∈Z | 420 | ◎◎ | (12.3), (12.4), (5.5), (1.10) |
| **(12.16)** | **Proof of (12.7)** | **Frobenius 定理の証明** | 75 | 反例π非空仮定下で矛盾導出: ψ(g) norm lower bound ⇒ (e-1)²よりlower ⇒ |K/K'| < 4 矛盾 | 1100 | ◎◎◎ | (12.8)-(12.15), (7.3), (7.8.b), (8.17), (8.13.c1) |
| **(12.17)** | Prop | **Case (b) of (8.8) 成立** | 75 | Case (a) [全 Type I] 仮定で矛盾 ⇒ Case (b) holds | 420 | ◎◎ | (12.7), (2.3), (8.13.c1), (8.17.a), (8.17.c), (7.11) |

**合計**: (12.1)-(12.13) 計 13 個の主要結果 + (12.14)-(12.17) 補足 4 個 = **17 個番号付き内容**.

---

## 構造と論理展開

### Phase A: 基本設定と Dade 等距写像 ((12.1)-(12.6))

**(12.1) 仮説 (Hypothesis)**:
- L: maximal subgroup of G, Type I
- H = L_F (Fitting subgroup = maximal odd-order normal)
- H' = [H, H]
- 𝒮 = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H} (induced characters from H)
- τ: Dade isometry relative to (A(L), L, G) [§4 の等距写像]

**意義**: Type I の最小設定. Frobenius structure (kernel H) の予期を含む.

**(12.2) 指標分解と Dade 定義領域**:

**定理**: (a) χ ∈ 𝒮 ⇒ χ = Σ_{φ ∈ S(χ)} φ (irreducible components of identical degree).
- S(χ) ⊆ Irr L: χ の既約分解
- **degree constant**: すべての φ ∈ S(χ) が同じ degree を持つ
- τ は Z[⋃_{χ∈𝒮} S(χ), L^#] 上で定義可能

**証明スケッチ**:
1. (8.2.c) より, Ind_H^L θ の既約分解
2. (1.5.a): (Res_H^L φ, 1_H) = 0 ⇒ H ⊄ Ker φ
3. (1.2): Supp(φ) ⊆ A(L) ∪ {1} (support が A(L) に包含)
4. τ はA(L) 上で定義 ⇒ φ について定義可能

**定理 (b)**: Hyp (5.2) [generic Dade hypothesis] 成立. τ restricted to Z[𝒮, L^#] が正規等距写像.
- (φ - φ̄)^τ = Σ_{α ∈ R₁(φ)} α (orthonormal set of size 2)
- R(χ) = ⋃_{φ ∈ S(χ)} R₁(φ) (coherent pairing)

**mathlib への示唆**: Character induced from normal subgroup の degree constant property, Dade isometry の algebraic closure.

**(12.3) 複数の Type I 最大部分群の直交性**:

**定理**: L₁, L₂ non-conjugate maximal subgroups of Type I. χᵢ ∈ 𝒮ᵢ ⇒ R(χ₁) ⊥ R(χ₂) (orthogonal in Z[Irr G]).

**証明**: TI-subset support の mutual exclusion (8.18.c) と Dade image の locality.

**意義**: §14 で複数の Type I を扱う際の独立性保証.

**(12.4) TI 余集合上の character 定数性**:

**定理**: ψ ∈ CF(G) s.t. ψ ⊥ R(χ) for all χ ∈ 𝒮. Then x ∈ L - H ⇒ ψ constant on xH.

**証明** (要点):
1. θ₁, θ₂ ∈ Irr H, θᵢ ≠ 1_H, χᵢ = Ind_H^L θᵢ ∈ 𝒮
2. φ₁, φ₂ ∈ S(χ) ⇒ (Res_H^L φᵢ, θ) = 1 (already in χ)
3. Supp(φ₁ - φ₂) ⊆ A(L) - H^# (difference vanishes on H)
4. A(L) - H^# is TI-subset by (8.12.c)
5. (φ₁ - φ₂)^τ ∈ Z[R(χ)] ⇒ (Res_H^G ψ, φ₁ - φ₂) = 0
6. ⇒ Res_L^G ψ = β + γ, β ∈ C[𝒮], γ has kernel ⊇ H
7. ⇒ ψ(xh) = γ(xh) = γ(x) for h ∈ H

**意義**: §15 の ψ^ρ 計算の準備. TI-subset 上での constant property.

**(12.5) ρ-reduction による H-H' 上の定数性**:

**定理**: 𝒮 と θ₁, θ₂ ∈ Irr H は same degree ⇒ (Res_H^L(ψ^ρ), θ₁ - θ₂) = 0 ⇒ ψ^ρ は H-H' 上で定数.

**証明**: (12.4) + (5.7) [Coherence hypot] による nested reduction.

**意義**: §15 での S ∩ T = W (cyclic) の詳細分析への道.

**(12.6) Type I Frobenius ⇒ Coherence**:

**定理**: L Frobenius with kernel H ⇒ 𝒮 ⊆ Irr L かつ 𝒮 coherent.

**証明** (3 分岐):
- (a) TI condition: H^# is TI ⇒ 𝒮 coherent by (6.8)
- (b) Rank 2 condition: all elements of 𝒮 have same degree ⇒ 𝒮 coherent by (5.7)
- (c) Cyclic condition: O_{p'}(M) cyclic ⇒ exponent control ⇒ 𝒮 coherent by (6.5.c)

**意義**: Type I の 3 条件がすべて coherence を保証.

---

### Phase B: MAIN THEOREM (12.7) と反例排除 ((12.7)-(12.13))

**(12.7) MAIN THEOREM: Every maximal Type I is Frobenius**

**Statement**: Let M be a maximal subgroup of G of Type I. Then M is a Frobenius group with kernel M_F.

**重要性**: Type I の定義 (3 条件のいずれか) から Frobenius group (Sylow cyclic in complement) への upgrade.

**Proof Strategy** ((12.8)-(12.16)):

反否法: If ∃M Type I with non-cyclic Sylow_p/M_F, derive contradiction.

---

### Phase C: 反例排除の詳細 ((12.8)-(12.16))

**(12.8) 反例仮定 (Hypothesis)**:

π = {p : ∃M maximal Type I s.t. Sylow_p(M/M_F) is non-cyclic} ≠ ∅.

p = min π, M Type I with non-cyclic Sylow_p(M/M_F).

K = M_F, K' = [K, K], P₀ Sylow_p subgroup of M.

**意義**: Frobenius の cyclic complement 条件を violate する最小素数 p を選択.

**(12.9) P₀ abelian rank 2 と x の特殊性**:

**定理**: 
- (a) P₀ abelian of rank ≥ 2
- (b) ∃L maximal s.t. P₀ ⊆ L_s (L_s = 𝒪_p(L_F) Sylow)
- (c) ∃x ∈ Ω₁(P₀)^# s.t. C_K(x) ⊄ K', N_G((x)) ⊆ M, C_G(x) ⊄ L

**証明**:
1. (8.12.a) non-cyclic Sylow ⇒ rank ≥ 2 (Sylow of abelian non-cyclic group)
2. (8.17.a): p | |L_s| for some maximal L
3. [BG] Prop 1.16: non-cyclic abelian P ⇒ ∃x with C_K(x) ⊄ K'
4. [BG] Lemma 1.14: C_K(x) characterization
5. (8.12.b): localizer condition ⇒ N_G((x)) ⊆ M uniquely

**意義**: Generic な rank 2 element x が outer centralizer を持つ (C_G(x) ⊄ L) → contradiction source.

**(12.10) L は Type I Frobenius**:

**定理**: H = L_F. Then L is Frobenius with kernel H.

**証明** (exhaustion on L's type):
1. **Not Type II**: (8.16) ⇒ C_G(y) ⊆ L for all y ∈ A(L) ⇒ C_G(x) ⊆ L, contradicting (12.9)
2. **Not Type III**: (10.10) + (11.9.c) ⇒ L is Type III ⇒ case (b) of (9.7) for L ⇒ [L,L] has cyclic complement U ⇒ P₀ abelian rank 2 ⊆ [L,L]' ⇒ but (11.6) + (8.1.b) ⇒ C_U(H) = 1 ⇒ U cyclic by (9.7.b) ⇒ P₀ ⊆ H (since non-cyclic) ⇒ (8.6.a) ⇒ C_G(y) ⊆ L for y ∈ H^#, contradicting (12.9)
3. **Must be Type I**: Case (a) (TI) ⇒ (8.6.a) ⇒ contradiction. Case (b) (rank 2) ⇒ P₀ ⊆ H (non-cyclic) ⇒ (8.6.a) ⇒ contradiction. **Case (c) (cyclic)**: By minimality of p on (8.2.b), all Sylow of L/H are cyclic ⇒ L Frobenius.

**意義**: 反例の外部相手 L が強制的に Type I + Frobenius.

**(12.11) M ∩ L の構造**:

**定理**: M ∩ L is complement of K in M, and M ∩ L ⊆ H.

**証明**:
1. (8.13.c1) ⇒ M ∩ L complements K
2. A ⊆ M ∩ L of order coprime |H| ⇒ A normalizes P₀ = O_p(H) ∩ M
3. (8.1.c) ⇒ P₀ does not centralize K
4. If A ≠ 1, P₀A Frobenius by (12.10) ⇒ (9.1) ⇒ ∃C_K(A) ≠ 1
5. (12.9) ⇒ ∃x ∈ C_G(A) ∩ C_K(x) ⇒ A ⊆ centralizer of x
6. (8.1.b) ⇒ A = 1. Thus M ∩ L ⊆ H.

**意義**: M と L の intersection が H に包含 → complement 一意化.

**(12.12) Complement cyclic + order 制約**:

**定理**: E complement of H in L, e = |E|. Then E is cyclic and **e | (p-1) or e | (p+1)**.

**証明** (3 段):

**段 1** (TI case): H^# TI-subset ⇒ E cyclic, e | (p-1) by (8.1.b) + (8.2.b).

**段 2** (Rank 2 case):
1. Z(P) ⊆ C_P(x) ⊆ P₀ (from (12.9), x ∈ Ω₁(P₀))
2. T = Ω₁Z(P) ≅ (Z/p)^a, a ≤ 2
3. E acts fixed-point-freely on T by (12.10) Frobenius
4. If E normalizes a subgroup T₀ ⊆ T of order p ⇒ E ⊆ Aut(Z/p) ⇒ E cyclic, e | (p-1)
5. Otherwise, |T| = p², E acts irreducibly
6. By [BG] Thm 2.6(a) + Schur ⇒ E cyclic, e | (p²-1)
7. A ⊆ E of order | (p-1) ⇒ A ⊆ F_p^* ⇒ A normalizes all ord-p subgroups of T
8. Since T = Ω₁(P₀) and x ∈ T, A normalizes (x)
9. A ⊆ M by (12.9) + N_G((x)) ⊆ M ⇒ (12.11) ⇒ A = 1
10. Thus e | (p+1).

**意義**: Frobenius complement E の order は p-1 または p+1 の約数.

**(12.13) Dade extension notation**:

𝒮, τ, τ₁ (extension to Z[𝒮]), χ with χ(1) = e, ψ = χ^{τ₁}, ρ mapping の正式化.

---

### Phase D: 矛盾導出 ((12.14)-(12.16))

**(12.14) ψ on xK 定数かつ値指定**:

**定理**: x as (12.9), g ∈ K ⇒ ψ(xg) = ψ^ρ(x) = χ(x).

**証明** (技巧的):

1. **ψ が R(χ) orthogonal** (by (12.3)-(12.5) ⇒ ψ ∈ Z[R(χ)] by (5.5))
2. **ψ is constant on xK** (by (12.4) generalized to minimal Type I vs Type III L)
3. **L と M non-conjugate** (since p | |L_s| but p ∤ |M_s| by (12.8) minimality)
4. **ψ^ρ(x) = ψ(x)** (by definition of ρ = "locally supported averaging")
5. **Character evaluation χ(x)**: α = Ind_H^L 1_H - χ, and decomposition via (7.8.a)
   - ⇒ (α^τ, ψ) = (-ψ + a Σ d_i χ_i^{τ₁} + Γ, ψ) with a = 0 (from norm inequality)
   - ⇒ ψ = χ^{τ₁} for specific χ with χ(1) = e
6. **Value**: ψ(xg) = χ(x) (by (7.7.a) orthogonality picking)

**意義**: ψ の値が χ(x) に固定 → norm bound に転化.

**(12.15) ψ^{ρ_M} 上で Z-valued**:

**定理**: ρ_M mapping (Hyp (7.1) with M, A₁(M)). Then:
- (a) g ∈ K^# ⇒ ψ^{ρ_M}(g) = ψ(g)
- (b) ψ constant on K - K'
- (c) ψ(g) ∈ Z for g ∈ K - K'

**証明**:
1. **ψ^{ρ_M}(g) = ψ(g)** (by similar TI-subset disjointness (12.3)-(12.4) applied to all Type I)
2. **ψ constant on K - K'** (by (12.5) ρ-reduction + (12.3) multiple Type I direct orthogonality)
3. **ψ(g) ∈ Z** (from Σ_{k∈K} ψ(k) = |K'| · (Res ψ, 1) + |K - K'| · ψ(g) ⇒ rationality + algebraic integer ⇒ Z)

**意義**: ψ の specific form と整性が §16 での final bound に活躍.

**(12.16) PROOF OF MAIN THEOREM (12.7)**:

**矛盾導出**:

1. **ψ(g) の mod p 制約**:
   - x ∈ C_K(x) with x ∉ K', g such element
   - ψ(xg) ≡ ψ(g) (mod 1-ζ) by (1.10.a) (ζ primitive p-th root)
   - χ(x) ≡ χ(1) = e (mod 1-ζ)
   - ⇒ ψ(g) ≡ e (mod 1-ζ) by (12.14)
   - ⇒ ψ(g) ≡ e (mod p) by (1.10.b) + (12.15)

2. **ψ(g) の norm lower bound**:
   - 2e ≤ p+1 by (12.12) ⇒ e - p ≤ 1 - e ⇒ |ψ(g)| ≥ e - 1
   - ‖ψ^{ρ_M}‖² ≥ (|K - K'|/|M|)(e-1)² by Cauchy-Schwarz on K-K'

3. **ψ^ρ の norm control**:
   - ‖ψ^ρ‖² ≥ 1 - e/|H| by (7.8.b)

4. **Global norm bound**:
   - 1 = ‖ψ‖² ≥ (ψ(1)²/|G|) + (...) > ‖ψ^{ρ_M}‖² + ‖ψ^ρ‖² by (7.3) (A₁(M) ∩ A₁(L) disjoint)
   - ⇒ (|K - K'|/|M|)(e-1)² + 1 - e/|H| < 1
   - ⇒ (|K - K'|/|K|)(e-1)² < e (by |M| ≤ |K||H|)
   - ⇒ (1 - |K'|/|K|) < e/(e-1)² = (1/e)(1 + 1/(e-1))² ≤ (1/3)(1.5)² = 3/4

5. **矛盾**:
   - ⇒ |K/K'| < 4
   - But (8.1.c) ⇒ ∃ element of order p acting fixed-point-freely on K/K'
   - ⇒ |K/K'| ≥ p ≥ 5 (since p ≥ 3 odd prime)
   - **CONTRADICTION**

**結論**: π = ∅ ⇒ すべての Type I M は Frobenius. ∎

**(12.17) Case (b) of (8.8) 成立**:

**定理**: Suppose every maximal M of G is Type I. Then contradiction ⇒ Case (b) of (8.8) holds (S, T 存在).

**証明**:
1. Type I-only 仮定 + (12.7) ⇒ すべての maximal M は Frobenius with kernel M_F
2. (2.3) + (8.13.c1) ⇒ ∀i, H_i^# is TI-subset
3. (8.17.a) ⇒ (7.10.c) holds
4. (8.17.c) ⇒ G^# = ⋃_i (H_i^#)^G
5. But (7.11) ⇒ contradicts G simple

**結論**: Case (a) [全 Type I] は矛盾 ⇒ Case (b) [S, T 存在] forced. ∎

---

## Type I の 3 サブ条件と論理関係

### §10 Definition (8.3) 再掲

M is Type I iff M is type 𝓕 and **at least one of** (a), (b), (c):

**(a) TI condition**: H^# is TI-subset of G
**(b) Rank 2**: H abelian of rank 2
**(c) Cyclic p'-part**: ∃p | |H| s.t. O_{p'}(M) is cyclic and ord(Sylow_p in M/H) | (p-1)

### §14 での統一への道

- **(12.6)**: All 3 conditions ⇒ 𝒮 coherent
- **(12.7) Main**: Every Type I ⇒ **Frobenius** (=All Sylow cyclic)
- **Implication**: Frobenius ⇒ "All three conditions coincide in structure"

**未解決の問題**: 
- 実際に、3 つ条件が logical に equivalent か?
- Or 別々に sufficient (but not necessary)?
- §15 の S, T 分析で clarify される見込み.

---

## BG §12 (E, Fitting subgroup) との関係

**BG Reference**: [BG] App.A (Frobenius family), [BG] §10-§16 (maximal subgroup structure).

**Peterfalvi §14 での参照**:

| BG 内容 | Peterfalvi 用途 | 場所 |
|--------|-----------------|------|
| **BG Prop 3.9** (Frobenius cyclic Sylow) | (12.12) complement order | (12.12) Proof |
| **[BG] Thm 2.6(a)** (Aut(F_p²) structure) | (12.12) rank-2 Sylow | (12.12)段 2-6 |
| **[BG] Prop 1.16** (non-cyclic abelian) | (12.9) generic element | (12.9) Proof |
| **[BG] Lemma 1.14** (centralizer in quotient) | (12.9) C_K(x) ⊄ K' | (12.9) Proof |
| **BG Theorem A-E** (full classification) | (12.7) Frobenius conclusion | (12.7)-(12.16) |

**Integration Point**: BG の Fitting subgroup (M_F = 最大ハル odd-order normal) と Peterfalvi §14 の H = M_F の relationship.

---

## §15 (S, T) への橋渡し

### §14 → §15 の継承構造

**§14 確立**:
- (12.7) Main: すべての Type I は Frobenius
- (12.12): complement e | (p-1) or e | (p+1)
- (12.6): coherence
- (12.13): Dade notation (ψ, τ₁, etc.)

**§15 で使用**:
- (13.1) Hypothesis: S, T = "non-Type-I" maximal pairs
- (13.2.a) "S Type II or III" (not Type I by (12.7))
- (13.17) "L Type I ⇒ Frobenius" (§14 Thm reuse)
- (13.16), (13.19.c) : Type I + (S,T) の orthogonality

### Critical Path

```
§14 (12.7): Type I ⇒ Frobenius
          ↓
§14 (12.17): Case (a) impossible ⇒ Case (b) [S, T exists]
          ↓
§15 (13.1)-(13.19): S, T 詳細分析
          ↓
§16 (14.1)-(14.11): Final contradiction
```

---

## §16 (G 非存在) での Type I 矛盾

**§16 で使用される §14 結果**:

| §16 結果 | 依存 §14 | 用途 |
|---------|---------|------|
| (14.3) L exists | (12.7)-(12.10) | Type I Frobenius structure |
| (14.5.a) L Frobenius | (12.7) Main | Complement structure |
| (14.12)-(14.16) | (12.14)-(12.15) | ψ値と norm control |

**最終矛盾の源**:
1. §14 (12.7): すべての Type I は Frobenius
2. §15 (13.17): S Type II の場合, N_G(U) ⊆ L maximal Type I Frobenius
3. §16 (14.3)-(14.11): そのような L が存在 ⇒ global norm bound violation

---

## mathlib カバレッジ詳細

### 新規必須 (Peterfalvi 固有)

| 概念 | mathlib status | Peterfalvi 要件 | Gap | 推定工数 |
|------|----------------|-----------------|-----|---------|
| **Type I definition (8.3)** | 無し | Fitting + 3 条件の union | Full structure | 2 日 |
| **Dade isometry τ** (§4) | 無し | Core §4 theorem | Character norm operator | 3-4 日 |
| **TI-subset coherence** (§7) | 基本のみ | Full (6.5)-(6.8) | Predicate + cases | 2 日 |
| **Character on TI coset** (12.4) | 無し | CF(G) locally constant | inner product on support | 1 日 |
| **ρ-reduction** (7.1 hyp) | 無し | local averaging on A | integral Cauchy | 1.5 日 |
| **Frobenius cyclic Sylow** (12.12) | 部分的 | Complete proof by cases | rank-2 abelian → Aut(F_p²) | 2 日 |

### 部分既存 (拡張必要)

| 概念 | mathlib既存 | 拡張内容 | Gap |
|------|----------|---------|-----|
| **Character induced** | ✓ degree control | character分解 χ = Σ φ (same deg) | constant degree lemma |
| **Frobenius group** | ✓ basic def | kernel H, complement structure | theorem 12.7 restatement |
| **Sylow subgroup** | ✓ existence | P₀ rank control | (8.12.a) abelian rank |
| **Fixed-point action** | ✓ basic | fixed-point-free Frobenius | (8.1.c) application |

### 直接参照 (§3-§8 依存)

- (1.2), (1.4), (1.5), (1.6), (1.7): Character theory (Isaacs Ch.5-6)
- (3.2.c), (3.4), (3.9.b): Virtual character support
- (4.3), (4.4), (4.5), (4.8), (4.9): Dade isometry (§4)
- (5.3.b), (5.5), (5.7), (5.8): Coherence definition
- (6.5), (6.8), (7.7.a), (7.8), (7.8.b): Coherence properties
- (8.1.b), (8.1.c), (8.2.b): Type 𝓕 property
- (8.3), (8.6.a), (8.8), (8.12.a), (8.12.b), (8.12.c): Type definition

---

## Phase 2b 形式化着手順

**前提**: Phase 2a (BG 完成), §3-§13 完成

**Timeline** (§14 単体):

### Week 1-2: (12.1)-(12.6) Setup + Coherence
- (12.1) 仮説 structure
- (12.2) Dade 定義領域 lemma
- (12.3) 直交性 (relatively simple)
- (12.4)-(12.5) ρ-reduction (complex character manipulation)
- (12.6) Coherence (3 case split)
- **Expected**: 250-350 行

### Week 3: (12.7)-(12.13) MAIN Theorem setup
- (12.7) Statement (陳述のみ)
- (12.8)-(12.13) Notation + helper lemmas
- **Expected**: 150-200 行

### Week 4-5: (12.8)-(12.16) Proof of (12.7)
- (12.9) rank 2 + x 特殊性 (technical)
- (12.10) L Type I (exhaustion case split, longest)
- (12.11) M ∩ L (module theory)
- (12.12) complement cyclic (3 分岐, numeric)
- (12.14)-(12.15) norm bound preparation
- (12.16) 矛盾導出 (Cauchy-Schwarz, norm)
- **Expected**: 600-800 行

### Week 5: (12.17) Case (b) conclusion
- (12.17) TI-subset covering
- **Expected**: 100-150 行

**総工数**: **4-5 週** (§3-§13 完成後)
**総 Lean 行数**: **1000-1500 行** (comments 除く)

---

## 未解決 / TODO

### Theory-Level

1. **Type I の 3 条件の equivalence**: (8.3)-(8.7) で 3 つ OR 構造. (12.7) で全員 Frobenius に統一されるが、actually equivalent な理由は unclear. §15 の S, T 分析で clarify されるはず.

2. **complement order (12.12) の p+1 ケース**: E cyclic, e | (p+1) の存在condition. K ⊆ F_{p²}* の action が本質. [BG] Thm 2.6(a) reference correct?

3. **ψ(g) ∈ Z in (12.15)**: algebraic integer from character, rational from norm → Z. Lean での rationality argument の詳細?

### Formalization-Level

1. **Character on TI coset (12.4)**: ψ constant on xH の proof. TI-subset support (8.12.c) の formalization + Dade image の locality が key. (φ₁ - φ₂)^τ ∈ Z[R(χ)] の type system design?

2. **(12.9) の [BG] Prop 1.16 引用**: Lean では BG が imported された形で、exact statement を引き継ぐ? Or redo in Peterfalvi setting?

3. **ρ-reduction (7.1 hypothesis)**: Notation ρ: ρ(ψ) is "restriction to A" mapped via character orthogonality. Lean functional type?

4. **(12.16) 矛盾導出の numeric bound**: (e-1)²·(|K-K'|/|K|) < e の Lean proof. Norm inequality from (7.3), then omega or norm_num?

### Integration-Level

1. **§14 vs §15 の normalizer structure**: (12.7) Main で L Frobenius ⇒ (13.17) で "L = H⋊W₁" 형태を再確認. Complement の uniqueness (Hall property)?

2. **Case (a) → (b) transition (12.17)**: (12.7) + (2.3) logic の formalization. (8.13.c1) + TI-subset covering の formal argument.

---

## Summary: 13 結果の意義と階層

### Stratum 1: Dade + Character Theory (12.1)-(12.6)
- Dade isometry τ の domain 確立
- Coherence の 3 condition 検証
- **核**: 𝒮 coherent ⇒ Dade well-defined

### Stratum 2: Type I Main Theorem (12.7)
- **最重要**: すべての Type I は Frobenius
- 反例排除により証明

### Stratum 3: Contradiction Derivation (12.8)-(12.16)
- 反例P₀非-cyclic仮定
- L Type I (exhaustion)
- ψ norm bound計算
- |K/K'| < 4 矛盾

### Stratum 4: Case Completion (12.17)
- Case (a) [全 Type I] impossible
- Case (b) [S, T exists] forced
- §15 入力

---

## 関連セクション・参考資料

- **Phase 2a 完成**: BG §10-§16, App.A-C
- **§3-§13 前提**: Character theory, Dade isometry, Coherence
- **§10-§11 復習**: Type 𝓕, Type I-V definition
- **§15 直接続編**: (13.1)-(13.19) S, T subgroups
- **§16 最終**: (14.1)-(14.11) G non-existence

---

**作成**: 2026-05-22  
**出典**: `references/peterfalvi/04.14_pp_69_74_Maximal_Subgroups_of_Type_I.mmd` (110 行)  
**レビュー**: §10 (Type I definition), §13 (Type II/III), §15 (S, T), §16 (Non-existence)  
**更新予定**: Phase 2b 第 6 波着手時 (§13 完成後)
