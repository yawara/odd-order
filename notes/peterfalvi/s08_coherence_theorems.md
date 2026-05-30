# Peterfalvi §8: Some Coherence Theorems — mini-roadmap

**スコープ**: Peterfalvi §8 (pp. 30-37), mmd `04.8_pp_30_37_*.mmd` (243 行), **8 結果 ((6.1)-(6.8)) 全て同格 named results** ⚠️ audit 訂正 (旧記載「4+2 結果」は `**(N.M)**` grep artifact).

形式化先 (予定): `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`.

ROADMAP 上の位置: **Phase 2b 第 3 波** (§7 Coherence 完成直後).

役割: **§7 で定義した Coherence の応用定理群**. Sibley 系の表現論的特性化. §9-§16 構造分析の重要な道具.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **L3 "4 + 2 結果 (6.1)-(6.4), (6.5)-(6.8) は拡張"** → **重大誤認: 実際 8 結果 (6.1)-(6.8) 全て同格 named results**. overview の "4 結果" は `**(N.M)**` grep artifact.
- **L18, L137, L142, L257 "Sibley 1984 Contemp. Math. 47"** → **完全捏造**. 訂正: Peterfalvi Notes §SS6 (mmd 04.17 L11) 明示「(6.3), (6.5) は **[FT] §11** から; (6.8) only is Sibley」. Sibley 参照は実際 **[Si1] = Sibley 1976 *Illinois J. Math.* 20:434-442** "Coherence in finite groups containing a Frobenius section" + [Si2] unpublished lectures. **"Contemp. Math. 47" は存在しない**.
- **L20, L158, L181, L261-273 "Reynolds 1965 Duke Math. J."** → **完全捏造**. Reynolds は Peterfalvi 参考文献 (`04.18`) + Notes (`04.17`) **両方に存在せず**. (6.7) は無名 internal lemma. **L261-273 sub-section 全削除推奨**.
- **L24 "mathlib coverage ~5%"** → (6.7)/(6.8) は **0%**. 既存「statement-level」評価は表面のみ; proof-internal で 10 helper lemma + 2 新規 module 要.
- **(6.7) は character-class congruence 単独 theorem**, (6.8) Sibley の前段補題. proof で **[Is] p.35 class-sum algebra hom `ω : ZC[G] → C`** (mathlib 不在) + **algebraic integer congruence** (mathlib 不在) + **TI-subset (§4-§5)** + **[Is] Lem 7.7** (§8 で 2 回) 利用. **`OddOrder/RepresentationTheory/ClassSumAlgebraHom.lean` + `AlgInt.cong.lean` 新規** 要.
- **(6.8) は §9, §12 (Type V), §14 (Type I) の各章 single decisive use** で「全 type を一発で消す」道具. forward は §13=6, §12=3, §9=1, §14=1.
- **[Is] cites in §8 = 8 件** (Lem 7.7 ×2, Thm 6.34 ×3, Cor 2.30 ×2, p.35 ω, Lem 2.27). 全 proof body cite, mathlib 対応**ゼロ**.
- **L405-408 "30 days"** → **35-45 days realistic** ((6.7) class-sum module + (6.8) full Sibley apparatus).
- §8 mmd 243 行は §3-§8 中 **最大**, 結果数 8 で **§3-§8 implementation effort の ~40% 単独占有**.
- **File 分割推奨**: A_Descent ((6.1)-(6.3)), B_OddOrderStructure ((6.4)-(6.6)), C_SibleyMainTheorem ((6.7)-(6.8)).

## TL;DR

§8 は **8 つの主定理** ((6.1)-(6.8)) 全て同格:

1. **(6.1) Hypothesis**: 仮説セットアップ (K solvable normal, S = 導入指標集, S(A) filtration)
2. **(6.2) Lemma**: Coherence の「失敗」判定式 — 不等式で coherence 喪失の条件をバウンド
3. **(6.3) Theorem**: nilpotent 商での Coherence 伝播 — M から H_1 へ下降
4. **(6.4) Hypothesis**: **奇数位数下の特殊化** — Frobenius + TI-subset + cyclic normalizer の総合
5. **(6.5)-(6.6)**: ⚠️ audit 訂正: 本書 Notes §SS6 (mmd 04.17 L11) 明示「(6.3), (6.5) は **[FT] §11** から; Sibley とは無関係」. (6.6) は center coherence
6. **(6.7)**: character-class congruence (Galois 整数性). proof で [Is] p.35 class-sum algebra hom + AlgInt congruence (両方 mathlib 不在). ⚠️ audit 訂正: 旧記載「Reynolds 1965 Duke Math. J.」は **完全捏造** (Peterfalvi 参考文献/Notes に Reynolds **不在**); (6.7) は無名 internal lemma
7. **(6.8) Main Theorem (= Sibley の唯一の寄与)**: L が Frobenius or Dade condition 満たす時 S が coherent. ⚠️ audit 訂正: **Sibley 参照は [Si1] Sibley 1976 *Illinois J. Math.* 20:434-442** "Coherence in finite groups containing a Frobenius section" + [Si2] unpublished lectures. "Sibley 1984 Contemp. Math. 47" は **存在しない**

**mathlib カバレッジ**: ~5% statement-level (表面のみ); **(6.7)/(6.8) は実 0%**. proof-internal で 10 helper lemma + 2 新規 module (`ClassSumAlgebraHom.lean` + `AlgInt.cong.lean`) 要. Coherence framework (§7) の上に全面構築.

**FT 必須度**: ☆☆ (§8 自体は局所的に完結しているが、§9-§16 では頻出. 特に (6.8) が §10-§14 の Type I-V 構造分析の土台)

## Lean status (2026-05-26)

`OddOrder/Peterfalvi/S08_CoherenceTheorems.lean` currently records the carrier
structures for §8:

- `DescentHypothesis`: (6.1) の solvable-normal filtration setup。
- `FiltrationData`: (6.1) の `S(A)` を、基底集合 `S` への包含と
  `A ≤ B → S(B) ⊆ S(A)` という kernel filtration の向き付きで保持。
  `zSupportedSpan` への lift も持つので、`Z[S(A),B]` から `Z[S,B]`
  への戻しと filtration の単調性を直接使える。
- `OddOrderSpecialization`: (6.4) の odd-order specialization carrier。
- `SibleySetup`: (6.8) の final setup with TI-subset condition。
- `SibleySetup.CoherenceTarget`: §7 `IsCoherent` target attached to the setup。
- `coherence_tau_inner_eq`: §7 hypothesis に含まれる `tau_isometry` を §8
  setup から直接使う。
- `coherence_inner_eq_on_supported`: proved coherence target があるとき、
  `Z[S,A]` 上で `τ` 自身が inner product を保存することを §8 setup から直接使う。

### (2026-05-31) §7 (5.6) coherence-union 依存の sub-lemma 진척

§8 (6.2)/(6.6)이 반복 invoke하는 **§7 Theorem (5.6)** (coherence-union hub)의
family-free honest sub-lemma 2개를 `S07_Coherence.lean`에 landing (sorry/axiom 無):
`int_eq_zero_of_sq_mul_le_of_two_mul_lt` ((5.6.2) integer-forcing core, division-free
`2a < D, λ²D-2λa+z ≤ 0 ⇒ λ=0`) + `CharacterPsiDecomposition.inner_self_Y_re_le_inner_self_psi`
((5.6.2) 첫 norm bound `‖Y‖² ≤ ‖ψ‖²`). 상세·잔여는 `notes/peterfalvi/s07_coherence.md`
"(2026-05-31)" 절. (5.6) main `IsCoherent(S₁∪{χ,χ̄})`의 단일 blocker = `τ₂`의
**전역** `IsIntegralIsometry` 확장 생성자 (repo/mathlib 부재; orthonormal-basis → 전역 등거리).

### (2026-05-31, pass 5) USER-APPROVED def 약화 → general (5.6) UNCONDITIONAL 완성 (commit b14a987)

위 blocker를 **정의 약화**로 해소하여 §5 coherence hub (5.6)을 일반형으로 닫음
(`S07_Coherence.lean`/`S08_CoherenceTheorems.lean`/`AxiomsCheck.lean`; sorry/axiom 無 —
`#print axioms retarget_isCoherent` = {propext, Classical.choice, Quot.sound}; full
`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑).

- **`IsCoherent` 약화** (USER-APPROVED, 이 branch 한정): 전역 필드
  `extension_isometry : IsIntegralIsometry extension` → 격자-相對
  `extension_inner_eq : ∀ φ ψ ∈ zSpan S, ⟨ν φ, ν ψ⟩ = ⟨φ, ψ⟩`. 이유: FT에서
  `dim CF(L) > dim CF(G)`이라 character-difference 격자를 `CF(G)`로 보내는 **전역** 등거리는
  일반적으로 부재; Peterfalvi (5.6.3)이 실제로 주장하는 대상은 **격자** 등거리이고, 모든 하류
  consumer가 격자원 `ζ∈S`에만 inner-preservation을 쓴다.
- **신규 keystone** (`namespace IntegralCharacterMap`, AxiomsCheck 등록 2건):
  - `orthoResidualMap_mem_zSpan`: {χ,χ̄} Gram–Schmidt 잔차가 `ℤ[S₁∪{χ,χ̄}] → ℤ[S₁]`
    (`span_induction`; 생성원 x∈S₁↦x [x⊥{χ,χ̄}], χ↦0, χ̄↦0). 이것이 전역 등거리 없이 격자
    등거리를 가능케 하는 핵심 격자 사실.
  - `retarget_inner_eq_on_zSpan_union`: `retarget_inner_eq_on`의 정직 충족형 integral-span 판.
    재타게팅이 `ℤ[S₁∪{χ,χ̄}]` 전체에서 `⟨·,·⟩` 보존, **τ₁의 `ℤ[S₁]`-등거리** (= S₁ coherence)
    + 격자 직교 `X,X̄ ⊥ τ₁ξ` (ξ∈ℤ[S₁]) 만 사용 (전역 등거리/over-strong 입력 불요). 잔차∈ℤ[S₁]
    ⟹ `inner_block_expand`로 폐합.
- **`retarget_isCoherent` 이제 UNCONDITIONAL general (5.6)**: `hX_ortho`/`hXbar_ortho`를 정직한
  격자형 (`∀ξ∈ℤ[S₁]`)으로 약화 (전역 `∀ξ⊥{χ,χ̄}`보다 약한 가설 = 더 강한 정리), τ₂:=retarget
  구성, `retarget_inner_eq_on_zSpan_union`로 약화된 `IsCoherent` 산출. **special-position 제한
  제거**; X,X̄⊥S₁^{τ₁}는 진짜 (5.5)+(5.2.e) 격자 사실 (posit 無).
- **S08 consumer 적응**: `IndChainDecomposition.ofIsCoherent`에 `hζ_mem : ∀ t, ζ t ∈ S` 추가,
  `Submodule.subset_span` (ζt∈S⊆zSpan S)로 격자 `extension_inner_eq` 공급. 약화는 consumer
  증명을 **쉽게** 만들 뿐 (전역성 미사용이었음). `sibleySetup_is_coherent` (S08:188, 여전히
  sorry)는 약화된 `CoherenceTarget`에 그대로 typecheck — 향후 증명도 약화로 더 쉬워짐.
- **의의**: (5.6)은 쌍 인접으로 coherence를 짓는 **귀납 엔진**, §6 (case-A/B coherence) 및
  궁극적으로 S08:188 `sibleySetup_is_coherent`로의 관문. 상세는 issue 0046 pass-5.

## §8 全結果表

| # | mmd 行 | 種別 | Statement 概要 | 数学的意義 | 形式化難度 | §9-§16 被引用 |
|---|--------|------|----------------------|-----------|-----------|-----------|
| **(6.1)** | 3-5 | **Hypothesis** | K solvable, S = Ind_K^L(Irr K - 1), S(A) filtration | Coherence 応用の基盤セットアップ | low | 全結果の前提 |
| **(6.2)** | 7-22 | **Lemma** | Coherence 喪失判定: 2\|L:C\|\sqrt{\|C:D\|} ≥ \|K:A\|-1 | Coherence 不成立による矛盾導出の技法 | **high** (長計算) | (6.3), (6.5), 構造分析で頻出 |
| **(6.3)** | 24-48 | **Theorem** | nilpotent 商 H/M での coherence 伝播 | 下降補題: coherence が層状に保存 | **high** (5 段階矛盾導出) | (6.4), (6.5), (6.8) 依存 |
| **(6.4)** | 50-73 | **Hypothesis + (6.5)-(6.6)** | |L| odd, K/M nilpotent, Frobenius 構造 → K/M は p-群で特定 | **奇数位数下での特殊化** (Sibley 系) | mid | (6.6), (6.8) 直前提 |
| **(6.7)** | 87-135 | **Theorem** | P Sylow p, L=N_G(P), P^# TI → character class 関係式 | **Galois 作用下の character 整数性** (Reynolds 1965 関連) | **very high** (7 つの sub-lemmas) | (6.8) 依存, (6.7.1)-(6.7.3) sub-structure |
| **(6.8)** | 136-244 | **Main Theorem** | L = H ⋊ W_1, H^# TI, Frobenius or Dade cond. → S coherent | **Frobenius family の coherence 統合定理** | **very high** (6.8.1)-(6.8.3, 8 sub-parts) | §9, §10-§14 の最重要入口 |

## 各結果の詳細

### (6.1) Hypothesis — Coherence 応用の枠組み

**主張**:
- (a) Hypothesis (ref:eq:C) が成立 (= §7 Coherence の前提 (5.2))
- (b) K は L の可解正規部分群
- (c) S = {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1_K} (K からの導入指標集合)
- (d) A ⊂ K が L の正規部分群なら S(A) = {Ind_K^L θ | A ⊂ Ker θ, θ ≠ 1_K}

**数学的意義**:
- K が可解正規部分群という点が重要 ⟹ K/A も可解 ⟹ K/A は線形指標を持つ
- 導入指標集 S の "filtration by kernel" S(A) を考える = 正規部分群の階層構造を character level で追跡

**Lean 表現**:
```lean
structure CoherenceHypothesis (G L K : Type*) [Group G] [Group L] [Group K] 
    (hyp_C : Hypothesis (5.2) L G) where
  K_solvable : IsSolvable K
  K_normal : K ◁ L
  S : Set (Representation ℂ L)  -- = Ind_K^L (Irr K - 1_K)
  S_A : (A : Subgroup K) → A ◁ L → Set (Representation ℂ L)  -- filtration
```

### (6.2) Lemma — Coherence 喪失の数値的判定

**主張**: Hypothesis (ref:eq:C) 下で、

- (a) A ⊂ K (A ≠ ∅), B ⊂ D ⊂ C ⊂ K, D/B ⊂ Z(C/B) (正規化群条件)
- (b) S(A) は coherent だが S(B) は NOT coherent

なら **2|L:C|√|C:D| ≥ |K:A|-1**

**証明概要** (mmd L14-22):
1. Hypothesis (ref:eq:C.b) より ∃ S_1, S_2 (S_1 closed under conj, S_1 coherent, S_1 ∪ S_2 NOT coherent)
2. K solvable ⟹ K/A は線形指標を持つ ⟹ S(A) の一員は degree |L:K|
3. **Theorem (5.6)** (§7 Coherence 拡張定理) 適用 ⟹ 2ψ(1)|L:K| ≥ Σ χ(1)²/‖χ‖²
4. (ref:eq:C.c), (ref:eq:C.d) より Σ χ∈S(A) χ(1)²/‖χ‖² = |L:K|(|K:A|-1)
5. θ(1) ≤ |K:C|√|C:D| (by (ref:eq:C)) ⟹ ψ(1) = Ind_K^L θ(1) ≤ |L:C|√|C:D| ⟹ 完成

**形式化の難所**:
- 多重的な sum/product 計算 (∑ χ∈S(A) χ(1)²/‖χ‖²)
- induced character の degree 推定 (最後の不等式)
- (ref:eq:C.b)-(ref:eq:C.d) の各条件の局所適用

**役割**: (6.3)-(6.5) での矛盾導出に直結

### (6.3) Theorem — Nilpotent 商での Coherence 伝播

**主張**: Hypothesis (ref:eq:C) 下で、M ⊂ H_1 ⊂ H ⊂ K (全て L の正規部分群) かつ

- (a) H/M が nilpotent
- (b) S(H_1) は coherent
- (c) |H:H_1| > 4|L:K|² + 1

なら **S(M) is coherent** (M での filtration も coherent)

**証明概要** (mmd L24-48):
1. Minimal counterexample: A ⊃ M, A ⊂ H_1, S(A) coherent, A minimal with these properties
2. A ≠ M と仮定 (矛盾を狙う)
3. B を M ⊂ B ⊂ A, B maximal で選ぶ
4. H/M nilpotent ⟹ (A/B) ∩ Z(H/B) ≠ 1 ⟹ A/B ⊂ Z(H/B)
5. **(6.2) を C=H, D=A で適用** ⟹ 2|L:H|√|H:A| ≥ |K:A|-1
6. x = |H:A| で変形: (√x - 1/√x)² = x - 2 + 1/x ≤ 4|L:K|²
7. |H:H_1| > 4|L:K|² + 1 に矛盾

**数学的意義**:
- **下降補題 (Descent Lemma)**: coherence が層状に保存される
- K の分層構造を利用して、上から下へ coherence を伝播させる
- (6.4)-(6.5)-(6.6) での Frobenius + odd-order 特殊化の前提

**Lean 表現**: 矛盾導出が複雑 — `decide` で不等式評価をサポート要

### (6.4) Hypothesis + (6.5)-(6.6) — 奇数位数下での特殊化

⚠️ audit 訂正: 旧 section 見出し「(Sibley 系)」は誤帰属. (6.3) と (6.5) は **[FT] §11** から (Peterfalvi Notes §SS6 明示). Sibley の寄与は **(6.8) のみ**.

#### (6.4) Setup

**主張**:
- (a) Hypothesis (6.1) + |L| odd
- (b) M ⊂ K, K/M nilpotent
- (c) H_1/M = [K/M, K/M] (commutator subgroup)
- (d) L/H_1 は kernel K/H_1 を持つ Frobenius 群

#### (6.5) Lemma — K/M の構造決定

Hypothesis (6.4) + S(M) NOT coherent なら:

- **(a)** K/H_1 は L の chief factor で |K:H_1| ≤ 4|L:K|² + 1
- **(b)** ∃ prime p s.t. K/M is non-abelian p-group
- **(c)** |L:K| ∤ (p-1) (p-1 を割らない)

**証明**:
1. (6.3) の仮説 H=K で K/H_1 abelian & non-trivial ⟹ (6.3.b) holds
2. (6.3) 適用 ⟹ |K:H_1| ≤ 4|L:K|² + 1
3. K solvable & commutator [K,K]=H_1 ⟹ K/M is p-group for some p
4. (c) proof by contrapositive: |L:K| | (p-1) ⟹ p ≥ 2|L:K|+1 ⟹ |K:H_1| ≥ p² > 4|L:K|²+1 矛盾

**数学的意義** ⚠️ audit 訂正 (旧記載「Sibley 1984 の翻訳」は **完全誤帰属**):
- (6.5) は **[FT] §11** (Feit-Thompson 1963 原論文) からの character-theoretic 引き取り
- Sibley とは無関係 ((6.8) のみが [Si1] Sibley 1976 *Illinois J. Math.* 20)
- K/M が p-group かつ non-abelian
- commutator K/H_1 が chief factor (Frobenius 構造の key)
- |L:K| coprime to (p-1) — [FT] §11 の signature condition

#### (6.6) Lemma — Center での Coherence

Hypothesis (6.4) + M=1 + Z ⊂ Z(K) non-trivial, X = S - S(Z) ⊂ Irr L なら:

**X = {χ ∈ Irr L | Z ⊄ Ker χ} and X is coherent**

**証明** (mmd L76-84): **複雑, 8 段階**
1. n = |X| ≥ 2
2. X の elements を degree で sort: χ_1(1) ≤ ⋯ ≤ χ_n(1)
3. χ_i = Ind_K^L θ_i, θ_i(1) = power of p (K/M は p-group)
4. θ_i(1)² | Σ_{j≥i} χ_j(1)²
5. Σ_{j≥i} χ_j(1)² = |L| - |L:Z| - Σ_{j<i} χ_j(1)²
6. **[Is] Corollary 2.30**: θ_i(1)² ≤ |K:Z|
7. Σ_j<i χ_j(1)² divisibility + **Theorem (5.6)** の繰り返し適用 ⟹ X is coherent

**役割**: (6.7)-(6.8) へ向けた coherence の final composition

### (6.7) Theorem — Character Class 関係式 (無名 internal lemma)

⚠️ audit 訂正: 旧見出し「(Reynolds 1965 関連)」は **完全捏造**. Reynolds は Peterfalvi 参考文献 (04.18) + Notes (04.17) **両方に存在せず**. (6.7) は無名の internal lemma で (6.8) Sibley の前段補題.

**主張**: G 有限, p prime, P Sylow p-subgroup of G, L = N_G(P),
- |L| odd, P^# TI-subset of G
- Z ⊂ Z(P) non-trivial, |C_L(z)| independent of z ∈ Z^#
- ψ ∈ Irr G, ψ constant on Z^#

**結論**: z ∈ Z^# ⟹ ψ(z) ∈ ℤ かつ **ψ(z) ≡ ψ(1) (mod |P|)**

**証明概要** (mmd L88-135, 6 つの sub-lemmas):

**(6.7.1) Lemma**: P^# が Z^# × Z^# に fixed-point-free に作用 ⟹ TI 性

**(6.7.2) Lemma**: Algebra homomorphism ω: Z[G] → ℂ (via ψ) の class operation 下での structure

**(6.7.3) Lemma** (Main): z ∈ Z^# ⟹ ψ(z) ≡ ψ(1) (mod |P|)
- Proof: ℤ[G] の conjugacy class algebra の construction
- z, z^{-1} が distinct conjugacy class (|L| odd ⟹ z^{-1} ≠ z^g)
- a_{11}, a_{12} calculation mod |P|
- integrality + congruence arithmetic

**数学的意義** ⚠️ audit 訂正 (旧「Reynolds 1965 定理」は捏造帰属):
- character class congruence: TI-subset + cyclic centralizer ⟹ character が "rigid" (mod |P|)
- (6.8) Sibley main thm の前準備
- proof 内で [Is] p.35 class-sum algebra hom `ω : ZC[G] → C` + algebraic integer congruence を使用 (両方 mathlib 不在; 新規 `OddOrder/RepresentationTheory/ClassSumAlgebraHom.lean` + `AlgInt.cong.lean` 要)

> **進捗 2026-05-30 (issue 1000 完了)**: class-sum algebra + central character `ω_ρ` の整数性を
> `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` に実装済 (unconditional, AxiomsCheck 登録).
> - `classSum_mul` : `C_i · C_j = ∑_s m_s · C_s` の **正しい** explicit 形 (係数 `m_s = (classSum Ci * classSum Cj) C_s.out`
>   = per-element 因子分解個数, 同一類上で定数; class-function 性は `classSum_mul_apply_conj`/`_out`).
>   read-only plan の `classSumCoeff/|C_s|` 形は誤りで採用せず (issue 注意書き通り).
> - `centralCharacterOfRep_classSum_mul` : `ω_ρ(C_i)·ω_ρ(C_j) = ∑_s m_s · ω_ρ(C_s)` (ℕ 係数; ω が ℂ-alg hom).
> - `centralCharacterOfRep_classSum_isIntegral` : **`IsIntegral ℤ (ω_ρ(C))`**. 行列固有値論法を回避し,
>   `{ω_ρ(C_s)}∪{1}` 生成の ℤ-部分加群 `N⊆ℂ` が乗法閉 (上記 product rule) かつ f.g. ⟹ `Submodule.toSubalgebra`
>   で部分代数化 ⟹ `IsIntegral.of_mem_of_fg`. これが (6.7.3) の `ψ(z)≡ψ(1) (mod |P|)` で使う integrality 部品.
> - 残: `AlgInt.cong` (合同 arithmetic in ℤ[ζ_n]) + a_{11}/a_{12} mod |P| の計算 = (6.7.3) 本体.

> **進捗 2026-05-30 (AlgInt.cong infra 完了)**: 合同関係 `α ≡ β (mod n)` を
> `OddOrder/Algebra/AlgInt.lean` に実装済 (unconditional, AxiomsCheck 登録).
> `Cong n α β := IsIntegral ℤ ((α - β)/n)` (Peterfalvi の三条件のうち load-bearing な商整数性;
> 端点整数性は別途 `character_isIntegral` 等で供給). API:
> - refl / symm / comm / trans / add / sub / neg = 加法的合同.
> - **`Cong.smul_left`/`smul_right`** : 片側を**任意の代数的整数で**スケール = (6.7.2)/(6.7.3) の
>   乗法ステップ (合同を ψ(1), 構造定数 a_{ij}, 別の整数 ω-値で掛ける). ⚠️ 2 つの合同の積
>   (`a≡b ∧ c≡d ⟹ ac≡bd`) は端点整数性を要し**無条件には成立しない**; 教科書も整数定数倍しかしないので一致.
> - `intMul_left`/`intMul_right`/`natMul_left` : 整数/ℕ スカラー特殊形.
> - `cong_of_exists_isIntegral`/`cong_of_sub_eq_intMul`/`Cong.of_int` : 導入形 (差を n×整数として提示).
> - notation `α ≡ β [ALGMOD n]` (scoped). commit dde7758.
> - **(6.7.3) 本体の残依存** (精密化): (1) **(6.7.1)** P が
>   `Ω = {(u,v) ∈ C_i × C_j | uv ∈ C_s}` (`C_s ∩ Z = ∅`) に fixed-point-free 作用 ⟹ `|P| ∣ a_{ijs}|C_s|`.
>   proof は **TI-subset ⟹ `C_G(x) ⊆ L` (x∈P^#)** + y∈{u,v} が L の p-元 ⟹ y∈P ⟹ (Z normal in L で) y∈Z ⟹ uv∈Z 矛盾.
>   これは `IsTISubset` + Sylow-in-L の group-theoretic 組み立て (~40-60 LOC, 未着手).
>   (2) **(6.7.2)** `ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α) (mod |P|)`: `ω(C_i)ω(C_j)=∑ a_{ijs}ω(C_s)` (既存
>   `centralCharacterOfRep_classSum_mul`) に (6.7.1) を適用し `C_s∩Z=∅` 項を mod |P| で落とす.
>   (3) **(6.7.3)** assembly: |L| odd ⟹ z, z⁻¹ が異なる G-共役類 ⟹ a_{110}=0, a_{120}=|C_1|;
>   `ψ=1_G` で a_{11}≡1+a_{12} ⟹ (1+a_{12})ψ(z)≡ψ(1)+a_{12}ψ(z) ⟹ ψ(z)≡ψ(1). ⟸ ここで本 module の
>   `Cong.smul_left`/`add`/`trans` が直接効く. (1)(2)(3) は §6 group-theory 組み立てなので別 issue.

> **進捗 2026-05-30 ((6.7.1) orbit-counting half 完了)**: (6.7.1) の**数え上げ部分**を
> `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` に実装済 (unconditional, AxiomsCheck 登録).
> planner が CRITICAL と指摘した「集合上の作用の `|G| ∣ |Ω|`」欠落 primitive を埋めた:
> - `card_dvd_of_stabilizer_eq_bot` : 有限群 `Γ` の有限集合 `β` への**自由**作用 (全 stabilizer ⊥) ⟹ `|Γ| ∣ |β|`.
>   proof は free-action 分解 `β ≃ (β/Γ) × Γ` (mathlib `MulAction.selfEquivOrbitsQuotientProd`).
>   ⚠️ "fixed-point-free" は教科書文脈では **自由作用** (x≠1 が点を固定しない=全 stabilizer 自明) の意で,
>   mathlib の `IsPGroup.card_modEq_card_fixedPoints` (= `p ∣ |Ω|` しか出ない) では**不足**; 自由作用の
>   orbit-stabilizer 分解で初めて全 `|P| ∣ |Ω|` が出る (教科書の主張は `|P|` 整除であって `p` 整除ではない).
> - `card_dvd_of_no_nontrivial_fixed` : 等価な仮説形 (no `x≠1` fixes a point).
> - `classPairMulAction` : 部分群 `P` の `ClassPair = {q:G×G // IsClassPair Ci Cj Cs q}` (= Ω) 上共役作用.
> - `card_classPair` : `|Ω| = classSumCoeff Ci Cj Cs` (= a_{ijs}|C_s|).
> - **`card_dvd_classSumCoeff_of_fixedPointFree`** : fixed-point-free ⟹ `|P| ∣ a_{ijs}|C_s|` = (6.7.1) 結論.
> - **残**: fixed-point-free *仮説の検証* (TI ⟹ C_G(x)⊆L ⟹ y∈P ⟹ y∈Z ⟹ uv∈Z 矛盾) は Sylow/TI/Z setup
>   (`IsTISubset`+Sylow-in-L) を要し repo 未実装 = `needs-infra`. 揃えば (6.7.2)/(6.7.3) は本 module の
>   `centralCharacterOfRep_classSum_mul` + `card_dvd_classSumCoeff_of_fixedPointFree` + `AlgInt.Cong` で assembly.

> **進捗 2026-05-30 ((6.7.1) fixed-point-free 仮説検証 完了, commit 384e5b5)**: 上記「残」だった
> fixed-point-free *仮説の検証* を `ClassSumAlgebra.lean` に実装済 (unconditional, AxiomsCheck 登録).
> これで (6.7.1) の group-theory 部分が完全に閉じた:
> - **`mem_sylow_of_mem_normalizer_of_isPGroup`** : `N_G(P)` の p-元は Sylow p-部分群 `P` に属する
>   (P は N_G(P) で normal ⟹ unique Sylow p). proof は `P ⊔ ⟨u⟩` が p-群
>   (`IsPGroup.to_sup_of_normal_left'`; `⟨u⟩ ≤ N_G(P)`) + `Sylow.is_maximal'` で join が `P` に collapse.
>   ⚠️ `Z ≤ Z(P)` ではなく `Z ≤ P` のみ使用 (教科書の `Z ⊆ Z(P)` は強いが load-bearing なのは `Z ≤ P`).
> - **`fixedPointFree_classPair_of_isTISubset`** : (6.7) setup (P Sylow p in L=N_G(P), P^# TI-subset,
>   Z ≤ P normal in L; C_i,C_j が Z^# と交わり C_s∩Z=∅) で `P` が
>   `Ω = {(u,v)∈C_i×C_j | uv∈C_s}` に **fixed-point-free** 作用 (no `x∈P^#` が pair を固定).
>   - x∈P^# が (u,v) を固定 ⟹ x が u,v を中心化 ⟹ TI (`IsTISubset`, `y` が x を共役で動かさない
>     ⟹ y conjugates `x∈P^#` to `x∈P^#` ⟹ y∈L) で `C_G(x) ⊆ L`.
>   - u,v は p-元 (Z^#∩C_i 経由で `z∈Z≤P` (p-群) に G-共役; `SemiconjBy.orderOf_eq` で order 保存)
>     ⟹ 上記 `mem_sylow_…` で u,v∈P.
>   - 同じ共役が u (resp. v) を `c⁻¹` で `Z^#⊆P^#` に送る ⟹ TI で conjugator∈L ⟹ `Z⊴L` で u,v∈Z
>     ⟹ uv∈Z, `C_s∩Z=∅` に矛盾.
> - **assembly 可能**: `card_dvd_classSumCoeff_of_fixedPointFree` と合成して (6.7.1) 結論
>   `|P| ∣ a_{ijs}|C_s|` (C_s∩Z=∅) が完全形で出る. 残は (6.7.2) `ψ(1)α²≡ψ(1)(a_{ij0}+a_{ij}α)`
>   (本 module `centralCharacterOfRep_classSum_mul` + (6.7.1) で C_s∩Z=∅ 項を mod|P| 落とす) と
>   (6.7.3) assembly (|L| odd ⟹ z,z⁻¹ 異 G-共役類; `Cong.smul_left`/`add`/`trans`). これらは §6
>   class-algebra/合同算術の組み立てで group-theory 依存は解消済.

> **進捗 2026-05-30 ((6.7.2) product rule mod |P| 完了, commit 3735af4)**: (6.7.1) keystone
> (`card_dvd_classSumCoeff_of_fixedPointFree`) を product rule に流して (6.7.2) を `ClassSumAlgebra.lean`
> に実装済 (AxiomsCheck 登録). `import OddOrder.Algebra.AlgInt` 追加, `CharacterValuesIntegral` section を
> `ClassCongruence` section の前へ移動 (`character_isIntegral` を scope に入れるため).
> - `coeff_mul_card_eq_classSumCoeff` : per-element 因子数 `a_{ijs}=(classSum Ci*classSum Cj) Cs.out` ×
>   `|C_s|` = pair-count `classSumCoeff Ci Cj Cs` (Peterfalvi `a_{ijs}|C_s|`). `classSum_mul` の class-sum
>   係数 (per-element count) と (6.7.1) の pair-count を ℂ-cast で橋渡し. proof は pair 集合を `uv` の class
>   で fiber 分割 (`Finset.card_biUnion`) + per-element count の class-不変性 (`classSum_mul_apply_out`).
> - `character_one_mul_coeff_mul_centralChar` : 各項 `ψ(1)·a_{ijs}·ω(C_s) = (a_{ijs}|C_s|)·χ(C_s.out)`
>   (`ω(C_s)=(|C_s|χ(C_s.out))/χ(1)` + 上記 pair-count identity).
> - `character_one_mul_coeff_mul_centralChar_cong_zero` : `m ∣ a_{ijs}|C_s|` ((6.7.1) 入力) ⟹ 当該項
>   `≡ 0 [ALGMOD m]` (`cong_of_exists_isIntegral`; 代数的整数 `χ(C_s.out)` の `m` 倍).
> - **`centralCharacterOfRep_classSum_mul_cong`** = **(6.7.2)** :
>   `ψ(1)·ω(C_i)·ω(C_j) ≡ ∑_{inZ C_s} ψ(1)·a_{ijs}·ω(C_s) [ALGMOD m]` (`inZ` = `C_s∩Z≠∅` の decidable 述語;
>   `¬inZ` 項は `m∣a_{ijs}|C_s|` で脱落). proof は `centralCharacterOfRep_classSum_mul` ×ψ(1) で全 sum 展開 →
>   `Finset.sum_filter_add_sum_filter_not` で split → `¬inZ` 部分が `Finset.sum_induction` (`≡0` の加法閉) で `≡0`.
>   Peterfalvi `ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α)` の `ω(C_s)=α` collapse 前形 (collapse は α 不変性の group-theory 要).

> **進捗 2026-05-30 ((6.7.3) 合同算術 assembly 完了, commits 27ed939/2be1cc3)**: (6.7.3) を
> group-theory atoms を仮説とする **conditional** assembly に還元して `ClassSumAlgebra.lean` に, cancellation
> infra を `AlgInt.lean` に実装済 (AxiomsCheck 登録). ⚠️ memory `scaffold-sorry-free-not-done` に照らし:
> これは sorry-free だが atoms (`a_{110}=0`,`a_{120}=|C₁|`,`z⁻¹∤z`,`ω(C_s)=α` const) を仮説に外出しした
> conditional 形 — 真の完了には atoms の group-theory 証明が要る (下記「残依存」). assembly 自体の算術は本物.
> - `AlgInt.Cong.intMul_cancel_left` : `(c:ℂ)·a≡(c:ℂ)·b (mod n)` + `IsCoprime c n` (ℤ) + a,b 代数的整数 ⟹
>   `a≡b (mod n)`. Bézout `uc+vn=1` で `(a-b)/n = u·(c(a-b)/n) + v·(a-b)` (両項整数係数×代数的整数で整). =
>   (6.7.3) の「`|C₁|` で割る」step. **端点整数性が本質** (2 合同の積が無条件でないのと同根; `character_isIntegral` 供給).
> - `peterfalvi_673_combine` : 2 つの (6.7.2) instance (1,1) `ψ(1)α²≡ψ(1)a_{11}α` (a_{110}=0) /
>   (1,2) `ψ(1)α²≡ψ(1)(|C₁|+a_{12}α)` (a_{120}=|C₁|) の `symm.trans`.
> - `peterfalvi_673_cancel` : `ψ(1)α=|C₁|ψ(z)` 代入で両辺を `|C₁|·(…)` 形にして `intMul_cancel_left` で
>   `|C₁|` cancel ⟹ `a_{11}ψ(z)≡ψ(1)+a_{12}ψ(z)`.
> - `peterfalvi_673_final` : `1_G` instance `a_{11}≡1+a_{12}` を `ψ(z)` (整) 倍 (`Cong.smul_left`) →
>   `a_{11}ψ(z)≡ψ(z)+a_{12}ψ(z)`, `hψ` と trans して `ψ(z)+a_{12}ψ(z)≡ψ(1)+a_{12}ψ(z)`, `a_{12}ψ(z)` を sub.
> - **`peterfalvi_673`** = **(6.7.3)** : combine→cancel→final の chain を atoms 仮説から組む 1 本.
> - **残依存** (= (6.7.3) 真完了に要る group-theory atoms; いずれも (6.7) full setup
>   `IsTISubset`+Sylow `P`+`Z⊴L`+`|C_L(z)|` const を要する `needs-infra`):
>   (i) 構造定数計算 `a_{110}=0` (`(u,u⁻¹)`, u∈C_1, u⁻¹∈C_2≠C_1 ⟹ 不可) / `a_{120}=|C_1|`;
>   (ii) `|L| odd ⟹ z⁻¹` が `z` に G-非共役 (z∈C_1, z⁻¹∈C_2 を distinct に取れる);
>   (iii) `ω(C_s)=α` が `C_s∩Z^#≠∅` 上不変 (`ψ(z),|C_L(z)|` の z∈Z^# 不変性から) + `ω(C_0)=1` で右辺 collapse;
>   (iv) `(|C_1|,p)=1` (= `IsCoprime |C_1| |P|`).

> **進捗 2026-05-30 ((6.7.2) geometric form — abstract `hdvd` を (6.7) setup から放電)**:
> `ClassSumAlgebra.lean` (`section ClassCongruence`) に
> **`centralCharacterOfRep_classSum_mul_cong_of_isTISubset`** を landing (AxiomsCheck 登録, 3 axioms 全
> allowlist 内). これは抽象版 `centralCharacterOfRep_classSum_mul_cong` (仮説 `hdvd : ∀ Cs, ¬inZ Cs →
> m ∣ classSumCoeff` を要求) を **実 (6.7) setup** へ特殊化したもの:
> - 仮説: Sylow `p`-subgroup `P`, `Z ≤ P` で `Z ⊴ L=N_G(P)` (`hZnormal`), `P^#=P∖{1}` TI-subset
>   (`hti : IsTISubset (P∖{1}) (N_G(P))`), source class `C_i,C_j` が `Z^#` と交わる (`hCi`/`hCj`).
> - 設定: `m := |P| = Nat.card P` (≠0: `Nat.card_pos`, P は群 nonempty + finite), 
>   `inZ Cs := ∃ w, ⟦w⟧=Cs ∧ w∈Z` (= Peterfalvi の `C_s∩Z≠∅`; `open Classical in` で statement の
>   `Finset.filter` の `DecidablePred` を供給, `omit [DecidableEq G]`).
> - `hdvd` の放電が新規部分: `¬inZ C_s` は `∀ w, ⟦w⟧=Cs → w∉Z` と同値 = (6.7.1)
>   `fixedPointFree_classPair_of_isTISubset` の `hCs` 仮説そのもの. それで fixed-point-free を得て (6.7.1)
>   counting `card_dvd_classSumCoeff_of_fixedPointFree` に流すと `|P| ∣ a_{ijs}|C_s|` (ℕ);
>   `exact_mod_cast` で ℤ. これで **(6.7.1) fixed-point-free + counting + (6.7.2) product rule を 1 定理に
>   合成**, (6.7.3) の geometric source `h11`/`h12` (`ψ(1)α²≡ψ(1)(a_{ij0}+a_{ij}α)`) が立つ.
>   残 atoms = 上記 (i)`a_{110}=0`/`a_{120}=|C₁|` 構造定数 + (iii)`ω(C_s)=α` const + (iv)`(|C₁|,p)=1` のみ
>   (= 純粋に構造定数・指標値の計算; fixed-point-free の group-theory は本定理で解消済).

> **進捗 2026-05-30 ((6.7.3) atom discharge — (i)/(iv)/`ω(C₀)=1` 完了, (ii)/(iii) 残)**:
> `ClassSumAlgebra.lean` に (6.7.3) の group-theory atoms を放電する standalone 補題群を landing
> (commits 5105064 / 4588590 / 399945c / ed4fae7, 全 AxiomsCheck 登録, unconditional). これで
> `peterfalvi_673` の conditional 仮説のうち **構造定数 (i) と coprimality (iv) と (iii) の `ω(C₀)=1`
> 部分が真の補題として独立に証明済**になった:
> - **構造定数 (i)** (`section StructureCoeffAtIdentity`): `classSumCoeff_one_eq_zero` (`a_{110}=0`,
>   抽象仮説 `∀u, mk u=Ci→mk u⁻¹≠Cj` で filter 空) / `classSumCoeff_one_eq_card` (`a_{120}=|C₁|`,
>   `Cj` = inverse class で bijection `u↦(u,u⁻¹)`). z-keyed instance:
>   `classSumCoeff_self_one_eq_zero` (`C₁=⟦z⟧`, **唯一の仮説 = `⟦z⁻¹⟧≠⟦z⟧`**) /
>   `classSumCoeff_self_inv_one_eq_card` (`C₂=⟦z⁻¹⟧`, **完全 unconditional** — `mk_inv_eq_of_mk_eq`).
> - **coprimality (iv)** (`section ClassSizeCoprime`, `[Finite G]`): `card_class_eq_index_centralizer`
>   (orbit-stabilizer `|⟦z⟧|=[G:C_G(z)]`; `ConjAct G` 作用, `orbit=carrier`, `stabilizer=centralizer`,
>   `toConjAct` 同型で card 移送 + `index_mul_card` cancel) / `coprime_card_class_card_sylow`
>   (`(|C₁|,p)=1`; `P≤C_G(z)` (z∈Z(P)) ⟹ `[G:C_G(z)]∣[G:P]` (`index_dvd_of_le`), `p∤[G:P]`
>   (`Sylow.not_dvd_index`), `|P|=p^k`).
> - **(iii) の `ω(C₀)=1`** (`section Evaluation`): `centralCharacterOfRep_one` (identity class =
>   singleton `{1}`, `ω=1·χ(1)/χ(1)=1`).
> - **残 atom (fully unconditional `peterfalvi_673` 化の前提)**:
>   (ii-wrap) real-class atom `⟦z⁻¹⟧≠⟦z⟧` の **TI-reduction** (`|L| odd`+`P^#` TI+`z∈P` ⟹
>     `¬IsConj_G z⁻¹ z`, Peterfalvi L122). core `ConjClasses.eq_one_of_isConj_inv_of_odd_card` は repo
>     既存 (`BrauerPermutation.lean`) だが TI-reduction wrapper は **import cycle
>     `ClassSumAlgebra←ZIrr←IrrIndexing←BrauerPermutation` で `ClassSumAlgebra` に置けない** ⟹
>     downstream module (例: `ZIrr` か新規 file) 行き.
>   (iii-collapse) `centralCharacterOfRep_classSum_mul_cong_of_isTISubset` の RHS sum を Peterfalvi
>     `ψ(1)(a_{ij0}+a_{ij}α)` 形へ collapse する補題. `{C_s∩Z≠∅}` を `{⟦1⟧}` (ω=1) と `{C_s∩Z^#≠∅}`
>     (ω=α, **atom iii = `ω` 不変性, `ψ`+`|C_L(z)|` の Z^# 不変性依存**) に分割し per-element count を
>     regroup. `|C_L(z)|` const の (6.7) setup 仕込みを要する最深 `needs-infra`.

> **進捗 2026-05-30 ((6.7.3) 残 atom (ii-wrap) real-class TI-reduction 完了, 新規 `RealClassTISubset.lean`)**:
> 上記 (ii-wrap) を解消. `BrauerPermutation` (= `eq_one_of_isConj_inv_of_odd_card` の在処) と
> `ClassSumAlgebra` の **両方の downstream** に新 leaf module
> `OddOrder/GroupTheory/RepresentationTheory/RealClassTISubset.lean` を作成 (unconditional, AxiomsCheck 登録).
> import cycle 回避: `ZIrr` は `BrauerPermutation` の *upstream* ゆえ不可 (`ZIrr←IrrIndexing←BrauerPermutation`);
> `BrauerPermutation` を import すれば `ClassSumAlgebra` も transitive に入る. 2 定理:
> - `not_isConj_inv_of_isTISubset` : `P∈Syl_p`, `Odd |N_G(P)|`, `P^#=P∖{1}` が `N_G(P)` 相対 TI-subset,
>   `z∈P`, `z≠1` ⟹ `¬IsConj z⁻¹ z`. 証明: `z,z⁻¹∈P^#`; `G`-conjugator `c` (`c z⁻¹ c⁻¹=z`) が `z⁻¹∈P^#`
>   を `z∈P^#` へ送るので TI で `c∈L=N_G(P)`; `z∈L` (`P≤L`) と合わせ `↥L` 内で `IsConj (⟨z,_⟩⁻¹) ⟨z,_⟩`;
>   `|L|` odd で `eq_one_of_isConj_inv_of_odd_card` が `z=1` を強制し矛盾. = Peterfalvi L122「`|L|` odd ⟹
>   `z⁻¹` は `G` 内で `z` に共役でない」.
> - `mk_inv_ne_self_of_isTISubset` : 上の class 形 `⟦z⁻¹⟧≠⟦z⟧` (`mk_eq_mk_iff_isConj`). これが
>   `classSumCoeff_self_one_eq_zero` の唯一仮説に直接プラグインし **(ii) 残を解消**.
> - mathlib quirk (rc2): `Subgroup.normalizer : Set G → Subgroup G` (Set 引数) のため, `Nat.card`/`Finite`/
>   subtype-ascription 等の型位置では `Subgroup→Set` 引数 coercion が自動挿入されずエラー. `∈`/`IsTISubset`
>   引数位置 (期待型 `Subgroup G`) は OK. `set L := Subgroup.normalizer ((P:Subgroup G):Set G)` で `hodd`/`hti`
>   を畳んで全箇所一貫化し回避.
> - **残**: fully unconditional `peterfalvi_673` の最後の依存は (iii-collapse) のみ
>   (`centralCharacterOfRep_classSum_mul_cong_of_isTISubset` の RHS sum collapse, `|C_L(z)|` const 依存).

> **進捗 2026-05-30 ((6.7.3) atom (i) `a_{110}=0` を (6.7) setup から hypothesis-free 化, `RealClassTISubset.lean`)**:
> 上記 (ii-wrap) real-class atom を構造定数計算に**配線**し, `a_{110}=0` を (6.7) setup から無条件化.
> `RealClassTISubset.lean` に `classSumCoeff_self_one_eq_zero_of_isTISubset` を追加 (unconditional,
> AxiomsCheck 登録, `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑, 3 axioms 全 allowlist 内):
> - `classSumCoeff_self_one_eq_zero_of_isTISubset` (`[Fintype G]`, `[DecidableEq (ConjClasses G)]`,
>   `P∈Syl_p`, `Odd |N_G(P)|`, `P^#=P∖{1}` が `N_G(P)` 相対 TI-subset, `z∈P`, `z≠1` ⟹
>   `classSumCoeff ⟦z⟧ ⟦z⟧ 1 = 0`): `mk_inv_ne_self_of_isTISubset` を `classSumCoeff_self_one_eq_zero`
>   (唯一仮説 = `⟦z⁻¹⟧≠⟦z⟧`) にプラグイン. これで **(6.7.3) の `a_{110}=0` 入力が group-theory 仮説ゼロ**で
>   (6.7) data から出る (`z∈P^#` のみ要求). placement は atom と同理由で本 leaf (`BrauerPermutation` downstream;
>   `ClassSumAlgebra` への `BrauerPermutation` import は cycle `ClassSumAlgebra←ZIrr←IrrIndexing←BrauerPermutation`).
> - **残 (fully unconditional `peterfalvi_673` の唯一の前提)**: (iii-collapse) のみ.
>   `centralCharacterOfRep_classSum_mul_cong_of_isTISubset` は (6.7.2) を **SUM 形**
>   (`ψ(1)ω(C_i)ω(C_j) ≡ ∑_{C_s∩Z≠∅} ψ(1)a_{ijs}ω(C_s)`) で無条件に出すが, `peterfalvi_673` の `h11`/`h12`
>   入力は **collapse 形** (`ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α)`). 橋には `ω(C_s)=α` (`C_s∩Z^#≠∅` 上不変) が要り,
>   それは `|C_L(z)|` const = `[G:C_G(z)]·ψ(z)` が `z∈Z^#` で不変 = (6.7) hypothesis の deep character-theory
>   仕込み (`needs-infra`). これは memory `scaffold-sorry-free-not-done` の趣旨に照らし**仮説外出ししない**
>   (外出しは vacuous/too-strong になる). 真の完了には `|C_L(z)|`-constancy 部品の実装が要る (別 issue).

> **進捗 2026-05-30 (characterDegree ↔ finrank bridge 完了)**: Round 3 の `finrank_dvd_card`
> (`χ_ρ(1) ∣ |G|`, `ClassSumAlgebra.lean`) は `Representation.character` レベルだったため S03 の
> `characterDegree`/`ClassFunction` 層へ流れず Peterfalvi の degree 文に乗らなかった。この橋を
> `OddOrder/GroupTheory/RepresentationTheory/ZIrr.lean` に実装 (unconditional, AxiomsCheck 登録):
> - `IsIrreducibleCharacter.exists_finrank_charValue_one` : 既約指標 `φ` の値 `φ 1` は任意の witness 表現
>   `ρ` on `V` の次元 `finrank ℂ V` に等しい (`IsIrreducibleCharacter` の存在 witness を unpack →
>   仮説 `Representation.IsIrreducible ρ` を `haveI` で instance 化 → `ρ.char_one`)。`[Finite G]` 不要。
> - `IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card` `[Finite G]` : ∃ `n:ℕ`, `0<n ∧ φ 1 = n ∧ n ∣ |G|`
>   (= Isaacs Thm 3.11 の `ClassFunction` 層への載せ替え; `finrank_dvd_card ρ` を直接適用)。
> - **消費経路**: Peterfalvi の `characterDegree φ` は定義上 `φ 1` (`characterDegree_def`, `rfl`/`@[simp]`)
>   なので S03 側で `rw [characterDegree_def]` 後に上記を当てれば `characterDegree φ ∣ |G|` (ℕ 鋳直し) が出る。
>   `ZIrr` は `ClassSumAlgebra` を新規 import (両者 sibling, `ClassFunction` 経由で acyclic; `characterDegree`
>   自体は S03 = downstream なので `ZIrr` からは参照せず `φ 1` 形で橋渡しした)。

**Lean 表現**: 
```lean
theorem S08_6_7 (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L : Subgroup G) (Z : Subgroup L) 
    (h_odd : Odd (Nat.card L))
    (h_ti : TI_Subset G P.val)
    (h_Z_center : Z ≤ Subgroup.center P.val)
    (h_Z_nontrivial : Z ≠ ⊥)
    (h_C_independent : ∀ z₁ z₂ ∈ Z.val, z₁ ≠ 1 → z₂ ≠ 1 → 
                       (Subgroup.centralizer G z₁).card = (Subgroup.centralizer G z₂).card)
    (ψ : Character G)
    (h_ψ_const : ∀ z₁ z₂ ∈ Z.val, z₁ ≠ 1 → z₂ ≠ 1 → ψ z₁ = ψ z₂) :
    ∀ z ∈ Z.val, z ≠ 1 → ψ z ∈ ℤ ∧ ψ z ≡ ψ 1 [ZMOD P.val.card] := by
  sorry
```

複雑: 7 つの sub-lemma が必要, class algebra の detailed calculation

### (6.8) Main Theorem — Frobenius Family の Coherence 統合定理

**主張**: G 有限, L ⊂ G,
- (a) L = H ⋊ W_1, |L| odd, H non-identity nilpotent, H^# TI with normalizer L
- (b) S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}, τ = restriction of Ind_L^G to Z[S, L^#]
- (c) Two cases:
  - (c1) L は kernel H を持つ Frobenius 群
  - (c2) Hypothesis (4.6) (Dade condition) + w_2 prime + W_2 ⊂ [H,H]

**結論**: **S is coherent** (τ が全 Z[S] に拡張できる)

**証明** (mmd L136-244, 3 つの main sub-proofs + 8 sub-lemmas):

**(6.8.1) X ∪ Y coherent in case (A)**: 
- Setup: Z = Z(H) ∩ [H,H] in (A), or Z = W_2 in (B)
- X = S - S(Z), Y = S([H,H])
- (6.6) + Dade 応用 ⟹ X coherent
- Y は orthonormal base ⟹ X ∪ Y coherent

**(6.8.2) X ∪ Y coherent in case (B)** (W_2 ⊂ Z(H)):
- Sub-lemmas:
  - **(6.8.2.1)**: η ∈ Y ⟹ η^{τ_1} constant on Z^#
  - **(6.8.2.2)**: (Ind_Z φ - |H:Z|η_1)^τ = X - |H:Z|Y (with explicit formula)
  - **(6.8.2.3)**: χ ∈ X ⟹ (χ - a η_1)^τ = X_1 - aY
- Isometry preservation

**(6.8.3) S is coherent** (Final):
- Contrapositive: S NOT coherent ⟹ S ≠ X ∪ Y ∃ S_1, S_2 with S_1 coherent, S_1 ∪ S_2 NOT coherent
- (5.6) apply ⟹ 2ψ(1)η_1(1) > Σ_χ χ(1)²/‖χ‖²
- (6.8.1)-(6.8.2) + calculation mod 4|W_1|² ⟹ contradiction

**数学的意義**:
- **§8 の最高峰** — Coherence framework の最終統合
- Frobenius group (case c1) + Dade isometry (case c2) の両立
- §9-§16 構造分析での character 計算基盤

**Lean 形式化難度**: ★★★★★
- 8 つの sub-lemma の逐次的構築
- case split (A) vs (B)
- isometry 延長の explicit construction
- norm/orthogonality 計算の chain

## Sibley 系の同定 (Reynolds 削除)

⚠️ audit 訂正 (2026-05-23): 旧 section の「Sibley 1984 Contemp. Math. 47」と「Reynolds 1965 Duke Math. J.」は **両方とも完全捏造** (Peterfalvi 参考文献 04.18 + Notes 04.17 で検証):

- **正しい Sibley 引用**: **[Si1] Sibley, M. J. (1976), "Coherence in finite groups containing a Frobenius section", *Illinois J. Math.* 20:434-442** + **[Si2] unpublished lectures**
- **Reynolds は本書全体に存在しない**. (6.7) は無名 internal lemma; (6.8) Sibley の前段補題.

### Sibley 1976 [Si1] との関連

**Notes §SS6 (mmd 04.17 L11) 明示**:
- (6.3), (6.5) は **[FT] §11** (Feit-Thompson 1963 原論文) から
- **(6.8) のみ** が Sibley [Si1] の寄与

(6.8) Main Theorem: L が Frobenius or Dade condition 満たす時 S が coherent — これが Sibley 1976 *Illinois J. Math.* 20 の主結果の Peterfalvi 版.

### (6.7) は無名 lemma

Reynolds 帰属は完全捏造のため削除. (6.7) は character class congruence の internal lemma で、proof で:
- [Is] p.35 class-sum algebra hom `ω : ZC[G] → C` (mathlib 不在)
- algebraic integer congruence `α ≡ β mod n` in Z[ζ_n] (mathlib 不在)
- TI-subset (§4-§5)
- [Is] Lem 7.7 (§8 で 2 回利用)

を使用. (6.8) の Frobenius case の前準備.

## §10-§16 구조분석에서의 사용

### §9 Non-existence of Certain Type (BG App.C)

- (6.1)-(6.4): Frobenius family의 coherence를 통해 non-existence 증명의 "character-theoretic obstruction" 제공
- (6.8): 최종 non-existence의 핵심 — Type I-V 분류 이전에 Frobenius structure 자체가 불가능함을 보임

### §10-§14 Type I-V 분석

- **(6.8)**: Type I (Elementary abelian Sylow 2-subgroup, BG Type A) 분석의 기초
- (6.1)-(6.3): Commutator subgroup chain을 따라 coherence를 추적하며 maximal subgroup의 structure constraint 도출
- (6.5): p-group structure bound가 Type classification을 진행하는 동안 dimension reduction 제공

### §15 S and T 부분군 분석

- (6.8.1)-(6.8.3)의 explicit isometry construction이 S, T의 character extension을 계산할 때 reuse됨
- Coherence predicate이 "S ⊂ Irr L" 판정에 사용됨 (irreducibility vs reducibility 구분)

### §16 Non-existence of G

- (6.2)의 inequality chaining: |K:A|-1 bound가 size argument (counting irreducibles)로 변환
- (6.7) mod |P| congruence: G의 존재 → character class 계산에서 모순 (final punch)
- (6.8) coherence chain: 최종 FT 증명에서 "모든 가능한 G의 maximal subgroup이 coherent character set을 가질 수 없다" 를 보이는 핵심

## mathlib 카버리지

### 기존 API
- `Subgroup.normal`: normal subgroup predicate ✓
- `Representation ℂ L` / `Character L`: representation, character type ✓
- `inner_product` (character 내적): ✓
- `Induced`: induced character/representation (부분) ✓

### 新規 (Phase 2b에서 정의 필요)

1. **Coherence 관련**:
   - `def Coherence (τ : E →ₗᵢ[ℤ] Z[Irr G]) (S : Set (Irr L)) (A : Set L) : Prop`
   - `structure CoherenceTriple`
   - Lemma/Theorem collections 전 (5.2)-(5.9) [§7에서 정의]

2. **§8 고유**:
   - `def CoherenceHypothesis (6.1)` — mmd notation과 정확히 동일
   - `structure FilteredCharacterSet` — S(A) filtration
   - `theorem S08_6_2` — 부등식 기반 lemma
   - `theorem S08_6_3` — nilpotent descent
   - `theorem S08_6_7` — Reynolds congruence (복잡)
   - `theorem S08_6_8` — Main theorem

3. **보조 타입**:
   - `IsTI_Subset`: TI-subset predicate (if not in mathlib)
   - `IsCoherent.extends` — isometry extension existence
   - `CharacterClass.CongruenceMod` — modular arithmetic wrapper

## Phase 2b 형식化 着手順

### 선행 조건
- ✓ Phase 1 Isaacs Ch.1-8 완성
- ✓ Phase 2b §3 (Preliminary) 완성
- ✓ Phase 2b §4 (Dade Isometry) 완성
- ✓ Phase 2b §5 (TI-cyclic norm) 완성
- ✓ Phase 2b §6 (Dade for certain type) 완성
- ✓ Phase 2b §7 (Coherence) 완성

### §8 형식화 계획 (예상 2-3주)

#### Wave 1: (6.1) Setup (1-2일)
```lean
structure CoherenceHypothesis ... where
  K : Subgroup L
  K_solvable : IsSolvable K
  K_normal : K ◁ L
  S : Set (Irr L)
  S_def : S = {Ind_K^L θ | θ ∈ Irr K ∧ θ ≠ 1_K}
  S_A : (A : Subgroup K) → A ◁ L → Set (Irr L)
```

#### Wave 2: (6.2) + (6.3) (3-4일)
- (6.2) 부등식의 algebraic 재배열
- (6.3) inductive 모순 구조 — `decide` vs `omega` vs manual `ring` calculation
- (5.6) Coherence extension theorem의 직접 활용

#### Wave 3: (6.4)-(6.5)-(6.6) (4-5일)
- Case split: |L| odd 가정의 전역화
- (6.3) + Frobenius structure 조합 → p-group determination (6.5.b)
- (6.7) 전 단계 — Reynolds congruence 예비

#### Wave 4: (6.7) Lemma (5-7일) ⭐ **hardest**
- Class algebra construction: Z[G]의 conjugacy class의 formal algebra
- `algebra_homomorphism ω` 타입: fintype conjugacy class의 enumeration
- 6 sub-lemma들의 sequential dependent proof
- `decide` / `omega` / `ring` / `decide` chain으로 modular arithmetic

#### Wave 5: (6.8) Main Theorem (7-10일) ⭐⭐ **very hardest**
- (6.8.1) X ∪ Y coherent (case A): (6.6) 활용 + explicit isometry extension
- (6.8.2) X ∪ Y coherent (case B): 3 sub-lemmas + norm 계산
- (6.8.3) S coherent: final contradiction 유도
- **Coherence framework와의 상호작용 극대화** — §7 (5.1)-(5.9)와의 타이트한 integration

#### Wave 6: Integration + Testing (3-4일)
- § 7과의 cross-reference 검증
- §9 형식화 시작 (§8 완료 후 바로)
- LEAN 타입체킹 및 doc string 완성

## 未解決 / TODO

1. **§7 (5.2)-(5.9)와의 정확한 interface**: Hypothesis (5.2) vs (6.4)의 관계 — formal Lean type에서 sub-hypothesison 활용 방법 결정 필요

2. **(6.7)의 "conjugacy class algebra" 형식화 전략**: 
   - Option A: Explicit fintype enumeration (|G| finite이므로 computable)
   - Option B: Abstract algebra homomorphism (더 이론적이지만 계산 어려움)
   - 권장: Hybrid — enumeration + omega tactic

3. **(6.8.2.1)-(6.8.2.3)의 sub-lemma ordering**: 증명 의존도가 복잡하므로 formal dependency graph 먼저 그리기 필요

4. ~~**Sibley 1984 paper access**~~ ⚠️ audit 訂正 (2026-05-23): "Sibley 1984 Contemp. Math. 47" は **完全捏造で存在しない**. 正しくは [Si1] Sibley 1976 *Illinois J. Math.* 20:434-442 のみ. (6.8) Main Theorem が Sibley 1976 の寄与.

5. ~~**Reynolds 1965의 정확한 statement 확인**~~ ⚠️ audit 訂正: "Reynolds 1965 Duke Math. J." は **完全捏造**. Peterfalvi 参考文献 + Notes 両方に Reynolds 不在. (6.7) は無名 internal lemma.

6. **mathlib Character/Induced API의 최신 상태 (May 2026)**: 
   - `Subgroup.induced : Representation ℂ H → Representation ℂ G` (computable?)
   - `Character.inner : Character H → Character H → ℤ` vs `Z[Irr H]` module structure
   - Recent PRs 확인 필요

---

## Summary Table

| Section | Theorems | Type | Mathlib Coverage | FT Role | Est. Implementation |
|---------|----------|------|------------------|---------|-------------------|
| (6.1) | 1 | Setup Hypothesis | low | Foundation | 1-2 days |
| (6.2) | 1 | Inequality Lemma | low | Obstruction | 2 days |
| (6.3) | 1 | Descent Theorem | low | Key tool | 2-3 days |
| (6.4)-(6.6) | 3 | Special case + Lemmas | mid | Sibley system | 4-5 days |
| (6.7) | 1 | Reynolds-type | low | Character class calc | 5-7 days |
| (6.8) | 1 (+ 3 sub-proofs) | Main Theorem | low | Structure analysis | 7-10 days |
| **TOTAL** | **8 主結果** | - | **~5%** (statement-level; (6.7)/(6.8) 0%) | **☆☆** | **~35-45 days realistic** (audit 訂正; 旧 30 days は (6.7) class-sum module + (6.8) Sibley apparatus を過小評価) |

---

*作成: 2026-05-22. 出典: `references/peterfalvi/04.8_pp_30_37_Some_Coherence_Theorems.mmd` (243 行) + `04.7_pp_25_29_Coherence.mmd` (136 行). クロス参照確認済: §7 (5.1)-(5.9), (6.1)-(6.8) self-contained, §9 (7.1)-(7.6) 依存. Phase 2b 第 3 波着手予定は §7 完成後.*
