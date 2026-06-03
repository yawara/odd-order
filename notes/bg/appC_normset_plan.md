# BG App C 有限体 norm-set 論法 — 実装計画 (2026-06-04)

**スコープ**: BG Appendix C (mmd L4855-5005) の Theorem C + Lemmas C.1-C.3。FT 最終矛盾の
generator-relation 版 (`p ≤ q` を強制)。下流監査 (`s16_appc_downstream_audit_2026_06_04.md`) で
**唯一の実質的下流ターゲット**と特定。issue 3000。

実装先: **`OddOrder/BG/AppC_NormSet.lean`** (mathlib-only leaf, namespace `OddOrder.BG.AppC.NormSet`)。
既存 `AppC_FinalContradiction.lean` の scaffold (theoremC/NormSetData/HypothesisB, opaque) とは分離し、
**実 `GaloisField p q` 上の finite-field 補題**として構築。完成後に scaffold theoremC へ配線。

## 数学 (BG L4855-5005)

**設定**: `p, q` 素数, 条件 (A) `gcd((p^q-1)/(p-1), p-1)=1`。`F = F_{p^q}`, `P=F^+`,
`U = {x∈F^* | N(x)=1}` (norm-1, Hilbert 90 で cyclic of order (p^q-1)/(p-1)), `H = P⋊U` Frobenius。
**仮説 (B)**: 群 `G`, monomorphism `σ:H→G`, finite abelian p'-subgroup `Q`, `y∈Q`,
`σ(P_0)` normalizes `Q`, `σ(P_0)^y` normalizes `U`。**結論 `p ≤ q`**。

**Notation**: `N(a)` = norm of `a∈F` over `F_p`。`E = {a∈F | N(a)=N(2-a)=1}`。

### Remark (I) — 条件 (A) ⟺ q ∤ (p-1) 【純数論・最易】
`(p^q-1)/(p-1) = ∑_{i<q} p^i ≡ q (mod p-1)` (∵ p≡1 mod p-1)。
⟹ `gcd((p^q-1)/(p-1), p-1) = gcd(q, p-1)`。q 素数ゆえ `= 1 ⟺ ¬ q∣(p-1)`。

### Lemma C.1 — `E=E⁻¹ ∧ |E|≥2 ⟹ p≤q` 【純有限体・多項式】
`a∈E^#` に対し `τ(a)=1/(2-a)∈E` (∵ E=E⁻¹)。帰納で `τ^k(a)∈E` かつ
`∏_{j=1}^k τ^j(a) = 1/((k+1)-ka)` (telescoping; `τ^j` の num=`j-(j-1)a`, den=`(j+1)-ja`, den_j=num_{j+1})。
各 `τ^j(a)∈E` ゆえ `N(∏)=1` ⟹ `N((k+1)-ka)=N((1-a)k+1)=1` ∀k∈F_p。
**核**: 多項式 `g(X) = ∏_{i<q}((1-a)^{p^i} X + 1) - 1 ∈ F[X]`。
- `g` の値: k∈F_p で `g(k) = N((1-a)k+1) - 1 = 0` (∵ k^{p^i}=k, Frobenius)。
- `deg g = q` (leading coeff = ∏(1-a)^{p^i} = N(1-a) ≠ 0, ∵ a≠1)。
- F_p の p 個の元すべて root ⟹ `p ≤ #roots ≤ deg g = q`。
**必須 mathlib**: `GaloisField p q`, `FiniteField.pow_card` (x^{p^q}=x ⟹ k∈F_p で k^{p^i}=k),
`Polynomial.card_roots'` (#roots ≤ natDegree), `Nat.card_range_of_injective` (|F_p|=p)。
**norm の積形**: 自前定義 `normN x := ∏_{i<q} x^{p^i}` (= 実 field norm; Algebra.norm 接続は C.2 用に後回し)。

### Lemma C.2 — `|E|≥2` 【q=3 純有限体 / q≥5 Frobenius 指標論】
- **q=3**: 多項式 `f_c(x)=x(x-2)(x-c)+(x-1)`。ある c∈F_p で F_p に根なし ⟹ その根 a∈F_{p^3} が
  `N(a)=N(2-a)=1` ⟹ a∈E; さらに 1∈E ⟹ |E|≥2。純有限体。
- **q≥5**: Frobenius 群 H の指標論。`e = |E|` = 構造定数 (Ŝ_1·Ŝ_1 の K̂_2 係数) = `card{(u,v)∈U²|us+vs=2s}`。
  直交関係で `e ≥ p^{q-2} - p^{q/2} > 1`。**concrete Frobenius 群の指標論が要 (重)**。

### Lemma C.3 — `E=E⁻¹` 【群論的 generator-relation・最難・仮説(B)必須】
Step1: `∀x∈PU, ∃u,v∈U, s₁∈P_0, x=us₁v` (∵ F^*=F_p^*×U)。
Step2: `s₁us₂∈U ⟹ (s₁=s₂=1) ∨ (u=1∧s₁s₂=1)`。
Step3: `t₁∈P₁^# ⟹ (PU)∩(PU)^{t₁}=U` (U が P に既約作用 + P_0=P_1 矛盾)。
Step4: `a∈E^#`, `b=2-a∈E` から `s^a s^b=s^2` ⟹ (C.2) 関係式 → `a^p∈E` を経由して E=E⁻¹。
**群 G・σ・Q (commutative)・y を本質的に使用** ⟹ FieldNormalizerData materialize 必須 (半上流)。

### Theorem C — assembly
C.1 ∧ C.2 ∧ C.3 ⟹ p≤q。既存 scaffold `AppC.theoremC` がこの statement。配線は materialize 後。

## 実装順序 (issue 3000)
1. **基盤 + Remark (I)** (本セッション): normN/E 定義, Remark (I) 証明, C.1/C.2/C.3 faithful statement (sorry)。
2. **Lemma C.1** (次): 多項式核。最も self-contained。
3. **Lemma C.2 q=3** (次): f_c 多項式。
4. **Lemma C.2 q≥5**: concrete Frobenius 指標論 (別 infra)。
5. **Lemma C.3 + Theorem C**: FieldNormalizerData materialize → 群論 generator-relation。**最難・複数セッション**。

## 注意
- norm: 自前 `normN x := ∏_{i<q} x^{p^i}` で C.1/C.2(q=3) は完結。C.2(q≥5)/U 構造は `Algebra.norm` 接続が要。
- `E⁻¹`: `Set.inv` (Pointwise), `a∈E⁻¹ ↔ a⁻¹∈E`。
- C.3/ThmC は仮説 (B) (群 G 埋め込み) 必須 ⟹ 純下流でない (FieldNormalizerData の field_model materialize と共有)。
