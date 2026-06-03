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

#### ✅✅ C.1 完成 (2026-06-04, commits 398e5f2/32ae2f4, sorry-free・axiom-clean・AxiomsCheck 登録)
`lemmaC1` 完全証明。`dSeq`+`tauIter`+`tauIter_eq_dSeq_div`(閉形式)+`normN_dSeq_eq_one`(telescoping で N(dₖ)=1)
+ `natCast_pow_pPow`(F_p Frobenius 不変) + 多項式 `∏(C((1-a)^{p^i})X+C 1)-C 1` の degree-q 根数
(`natDegree_prod`/`natDegree_linear`/`add_pow_char_pow`/`CharP.natCast_injOn_Iio`/`card_roots'`)。
**罠**: `eval_C`(not eval_one); image は `Nat.cast` 統一(InjOn); `CharP.natCast_injOn_Iio (F) p` 明示引数; `classical` 要。
**残 (次セッション)**: C.2(q=3/q≥5) → C.3 → Thm C 配線。以下は C.1 着手前の旧計画メモ (参考):

#### C.1 実装詳細 (2026-06-04 精緻化, 旧メモ)
**✅ 済 (commit aab7be8/次)**: `normN_one`/`normN_mul`/`normN_ne_zero`/`mem_normSetE_iff`/
`two_sub_mem_normSetE` (a∈E ⟹ 2-a∈E)/`one_mem_normSetE` (1∈E)。

**残コア = 2 ブロック**:

**(B1) `∀ k:ℕ, N(d_k) = 1`** where `d_k := (k+1 : F) - (k : F) * a` (= `(1-a)•k + 1`)。
反復列 `a₀=a, a_{k+1} = (2 - a_k)⁻¹` を定義 (`Nat.rec`)。
- `aₖ ∈ E` ∀k: 帰納。base a∈E; step `two_sub_mem_normSetE` + `hEinv` (E=E⁻¹) で `(2-aₖ)⁻¹∈E`
  (`a∈E⁻¹ ↔ a⁻¹∈E`, `Set.mem_inv`)。⟹ `N(aₖ)=1`, `aₖ≠0`, `2-aₖ≠0` (norm 1 ⟹ ≠0; `ne_zero` 補題要追加: `normN x=1 ⟹ x≠0`, q>0 で `normN 0=0`)。
- **closed form `aₖ = d_{k-1}/d_k` (k≥1) + `d_k≠0`**: 帰納。**鍵代数等式 `2·d_k - d_{k-1} = d_{k+1}`**
  (`2((k+1)-ka) - (k-(k-1)a) = (k+2)-(k+1)a`, `ring`/`push_cast`+`ring` で k:ℕ→F cast 注意)。
  step: `2 - aₖ = 2 - d_{k-1}/d_k = (2d_k - d_{k-1})/d_k = d_{k+1}/d_k` ≠0 (∵ 2-aₖ≠0) ⟹ d_{k+1}≠0,
  `a_{k+1}=(2-aₖ)⁻¹ = d_k/d_{k+1}`。
- `N(d_k)=1`: `aₖ=d_{k-1}/d_k∈E` ⟹ `N(d_{k-1}/d_k)=1` ⟹ `N(d_{k-1})=N(d_k)` (normN_mul + inv);
  `N(d_0)=N(1)=1` から帰納。**別法 (簡)**: `∏_{j=1}^k aⱼ = d_0/d_k = 1/d_k` (telescoping) ⟹ `N(1/d_k)=1`。

**(B2) 多項式根数 ⟹ p≤q**:
- `frobPoly := ∏ i∈range q, (C ((1-a)^(p^i)) * X + 1) : F[X]`。`g := frobPoly - C 1`。
- **`g.natDegree = q`**: 各因子 degree 1 (leading `(1-a)^{p^i}≠0` ∵ a≠1 ⟹ `normN_ne_zero`); `Polynomial.natDegree_prod`
  (domain, 全因子≠0) ⟹ deg = ∑1 = q; `-C 1` は deg q≥1 不変 (`natDegree_sub_C`?)。
- **eval at k∈F_p**: `g.eval (↑m) = N((1-a)•↑m + 1) - 1 = N(d_m)-1 = 0` (B1)。
  ∵ `((1-a)↑m+1)^{p^i} = (1-a)^{p^i}·↑m + 1` (Frobenius: `frobenius`/`add_pow_char`+`(↑m)^{p^i}=↑m` で
  `m∈F_p`; `FiniteField.pow_card`/prime subfield)。`frobPoly.eval ↑m = ∏((1-a)^{p^i}↑m+1) = N((1-a)↑m+1)`。
- **p 個の root**: `Finset.image (algebraMap (ZMod p) F) univ` (card p, `Nat.card_range_of_injective`/`Finset.card_image_of_injective`)
  ⊆ `g.roots.toFinset`。`g≠0` (deg q≥1)。`Polynomial.card_roots'` / `Finset.card_le_card` ⟹ `p ≤ #roots ≤ deg g = q`。

**罠**: k:ℕ→F cast は `Nat.cast`; `d_k` の `(k:F)` と多項式の root `(↑m : F)` (m:ZMod p) の対応 =
`m=0..p-1` の ℕcast が F_p の全元 (char p, ℕ→F が 0..p-1 で単射)。`push_cast`+`ring` 多用。
`Set.ncard ≥ 2 ⟹ ∃ a∈E, a≠1`: `Set.one_lt_ncard_iff` 等で 2 元抽出, 1∈E と異なる方を採用。

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
