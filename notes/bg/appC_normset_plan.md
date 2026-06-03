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

#### ✅ Remark (VII) / `U` 位数 bridge 完成 (2026-06-04)
`normN_eq_algebraMap_norm` で自前の積表示 `normN` と mathlib の `Algebra.norm` を接続し、
`normOneUnits : Subgroup (GaloisField p q)ˣ` を `ker (Units.map (Algebra.norm ...))` として materialize。
`FiniteField.unitsMap_norm_surjective` + `Subgroup.index_ker` から
`normOneUnits_card : |U| = (p^q - 1)/(p - 1)` を sorry-free 証明し、AxiomsCheck に登録。
これは C.2(q≥5) の Frobenius 群 `H=P⋊U` で使う `|U|` の基礎補題。

#### ✅ Remark (VII) / `𝔽_{p^q}ˣ = 𝔽_pˣ · U` 分解完成 (2026-06-04)
`primeFieldUnits` を `Units.map (algebraMap 𝔽_p 𝔽_{p^q})` の range として定義。
条件(A)から `q∤(p-1)` を経由し、cyclic group API
`IsCyclic.index_powMonoidHom_range` で `(ZMod p)ˣ` 上の `q` 乗写像が全射
(`zmodUnits_pow_surjective_of_conditionA`) と証明。さらに
`unitsMap_norm_primeFieldUnit` (`N(b)=b^q`) を使って、任意の `x∈𝔽_{p^q}ˣ` を
`x = b * u` (`b∈𝔽_pˣ`, `u∈U`) と分解する
`exists_primeFieldUnit_mul_normOne` を追加し、AxiomsCheck に登録。
これは BG C.3 Step1 の `F^* = F_p^* × U` 使用箇所へ向けた前処理。
さらに `primeFieldUnits_inf_normOneUnits_eq_bot` で `𝔽_pˣ ∩ U = 1` を証明。
`q` 乗写像の全射性から有限性で injectivity を得て、`b^q=1` なら `b=1` とする。
これで Remark (VII) の「積で全体を覆う」だけでなく「交わり自明」も Lean 側に揃った。
さらに `primeFieldUnits_mul_normOneUnits_eq_univ` で carrier-set product
`(𝔽_pˣ : Set 𝔽_{p^q}ˣ) * (U : Set 𝔽_{p^q}ˣ) = Set.univ` を明示 theorem 化し、
下流の class-sum/作用計算から `Set.mem_mul` で直接使える形にした。AxiomsCheck 登録済み。

#### ✅ C.2 structure-constant bridge 完成 (2026-06-04)
`normOnePairSet : Set (U × U)` を `{(u,v) | u+v=2}` として定義し、
`normOnePairSet_ncard_eq_normSetE_ncard` で `|E|` とこの pair set の個数を同一視。
写像 `(u,v) ↦ u` と逆写像 `a ↦ (a, 2-a)` を `normN`/`U` membership bridge で Lean 化した。
これにより q≥5 branch で残る作業は、この pair count を Frobenius 群 `H=P⋊U` の class-sum
構造定数へ持ち上げ、指標直交関係から下界 `p^{q-2}-p^{q/2}>1` を出す部分に絞られた。

#### ✅ BG 本文の `us+vs=2s` 形式まで接続 (2026-06-04)
`normOnePairSetAt s := {(u,v)∈U×U | u*s+v*s=2*s}` を定義し、`s≠0` なら
`normOnePairSetAt s = normOnePairSet` を証明。従って
`normOnePairSetAt_ncard_eq_normSetE_ncard : |{(u,v) | u*s+v*s=2*s}| = |E|`。
これは BG C.2 の class-sum 構造定数 `card{(u,v)∈U² | us+vs=2s}` を Lean 側の norm set に
直接接続する補題。

#### ✅ q≥5 用 Frobenius 半直積 `H=P⋊U` の concrete setup (2026-06-04)
`P` を `additiveFieldGroup := Multiplicative 𝔽_{p^q}` として置き、
`normOneMulAction : U →* MulAut P` を `AddAut.mulLeft` から構成。
`normOneFrobeniusGroup := P ⋊ U` を定義し、
`normOneFrobenius_conj_inl` で `H` 内の共役公式 `u s u⁻¹ = u*s` を Lean 化した。
また `mem_normOnePairSetAt_iff_inl_mul_inl` で `us+vs=2s` を additive kernel `P≤H` 内の
積方程式 `inl(us) * inl(vs) = inl(2s)` と同値化。これで次の残作業は、U 軌道を
`ConjClasses H` に同定して `classSumCoeff` / `classSum_mul_apply` に接続する層。
AxiomsCheck 登録済み。

#### ✅ class-sum `IsClassPair` への片方向 bridge (2026-06-04)
`AppC_FrobeniusClassSum.lean` を追加し、class-sum 依存を finite-field leaf から分離。
`normOneClassAt s := ConjClasses.mk (inl s)` を定義し、
`normOneClassAt_mul_eq` で任意の `u∈U` について `inl(u*s)` が `inl s` の共役類にあることを証明。
さらに `normOnePairSetAt_isClassPair` で、`normOnePairSetAt s` が数える `(u,v)` から
`classSumCoeff (C_s) (C_s) (C_{2s})` の underlying pair predicate `IsClassPair` への map を構成。
AxiomsCheck 登録済み。

#### ✅ class-sum bridge: 共役類 = `U`-orbit の逆向き (2026-06-04)
`normOneFrobenius_conj_inl_any` で、任意の `x∈H=P⋊U` による `inl s` の共役は
`x.right * s` だけで決まることを証明。`P` 成分が消えるのは additive kernel が可換だから。
これを使い `exists_normOne_mul_of_mem_normOneClass` で、`normOneClassAt s` の任意の元が
`inl(u*s)` と書けることを固定した。AxiomsCheck 登録済み。

#### ✅ class-sum bridge: fixed-product fiber (2026-06-04)
`IsFixedProductClassPair` を導入し、通常の `IsClassPair` の product-class 条件を
product が代表元 `inl(2*s)` に等しい fiber 条件へ切り出した。
`normOnePairSetAt_isFixedProductClassPair` と
`exists_normOnePairSetAt_of_isFixedProductClassPair` で、`normOnePairSetAt s` がこの fiber を
正確に parametrise することを証明。さらに `fixedProductClassPairSet` と
`normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard` で、`s≠0` のとき pair count が
fixed-product fiber の `ncard` と等しいことを証明した。残る cardinal bridge は、full class pair を
product class の fiber 和として分解し、class-size factor を整理する部分。AxiomsCheck 登録済み。

#### ✅ class-sum bridge: additive-kernel class size (2026-06-04)
`normOneClassAt_carrier_ncard_eq_normOneUnits_card` で `s≠0` のとき
`C_s = {inl(u*s) | u∈U}` の cardinality が `Nat.card U` と一致することを証明。
あわせて `normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card` で `2≠0` の product class
`C_{2s}` も同じサイズを持つ形にした。次の target は full class-pair count を
`|C_{2s}|` 個の fixed-product fiber に分解する補題。AxiomsCheck 登録済み。

#### ✅ class-sum bridge: full class-pair fiber decomposition (2026-06-04)
`classPairSet` を導入し、`classPairSet_eq_iUnion_fixedProductClassPairSet` で full `IsClassPair`
を product class `C_s` 上の exact-product fiber の和として展開。
`classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard` と
`classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard` で、既存 `classSumCoeff` が fixed fiber
cardinality の有限和であることを証明した。次は AppC の `H=P⋊U` で各 fiber の cardinality を
代表元 fiber と同一視する conjugation-bijection。AxiomsCheck 登録済み。

#### ✅ class-sum bridge: equal fibers and class-size factor (2026-06-04)
`fixedProductClassPairSet_ncard_eq_of_isConj` で exact-product fibers が product の共役で
同じ cardinality を持つことを証明。これを有限和に適用して
`finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul` と
`classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard` を追加し、
`classSumCoeff(C_i,C_j,C_z) = |C_z| * |fixedFiber(z)|` の形まで整理した。AxiomsCheck 登録済み。

#### ✅ class-sum bridge: norm pair coefficient specialization (2026-06-04)
`classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard` で
`C_s*C_s` の `C_{2s}` 係数を `|U| * |normOnePairSetAt s|` に特殊化。さらに
`normOnePairSetAt_ncard_eq_normSetE_ncard` を合成して `|U| * |E|` 版も登録した。
AxiomsCheck 登録済み。

#### ✅ class-sum bridge: coefficient lower bound reducer (2026-06-04)
`normSetE_ncard_ge_two_of_normOneCoeff_gt_normOneUnits_card` で、将来の指標論から
`classSumCoeff(C_s,C_s,C_{2s}) > |U|` が得られれば `|E| ≥ 2` へ直ちに落とせる形にした。
q≥5 分岐の残りを concrete Frobenius group の coefficient lower bound に分離。AxiomsCheck 登録済み。

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

---

## App C 完成への残作業 — 精密 breakdown + 進捗 (2026-06-04, `/goal` "appC完成" 自走中)

### ✅ 完成済 (build-green, sorry-free, axiom-clean)
- **Remark (I)** `conditionA_iff_not_dvd`、**Lemma C.1** `lemmaC1` (E=E⁻¹∧|E|≥2⟹p≤q)。
- **C.2 (q=3) 前半**: `exists_rootFree_cubic` (pigeonhole: ∃c, f_c が F_p に無根) +
  `fCubic`/`fCubic_eval`/`fCubic_natDegree`(=3, compute_degree!)/`fCubic_irreducible`
  (root-free ⟹ Irreducible, `irreducible_of_degree_le_three_of_not_isRoot`)。

### 🔜 残 3 ブロック (いずれも multi-session の深い formalization)

**(A) C.2 (q=3) 持ち上げ** (~200行, 有限体論): irreducible `fCubic c` から
`a ∈ GaloisField p 3` で `normN a=1 ∧ normN(2-a)=1 ∧ a≠1` を得て `|normSetE p 3|≥2`。
- **root 取得**: `AdjoinRoot (fCubic c)` (field, irreducible) の `powerBasis` で finrank=3
  ⟹ card=p³ ⟹ `algEquivGaloisField` で `≃ₐ[ZMod p] GaloisField p 3`、root を transport。
  (別経路: `fCubic|X^{p³}-X` (forward divisibility, mathlib に無し→要証明) + `Splits.of_dvd` + `exists_root_of_splits`。)
- **Frobenius 軌道因数分解**: `f(a^p)=f(a)^p=0` (F_p 係数 + char p; eval=∑cᵢaⁱ, cᵢ^p=cᵢ),
  `a,a^p,a^{p²}` 相異 (a∉F_p ∵ deg minpoly=3), monic deg-3 ⟹ `fCubic=∏(X-a^{p^i})`。
- **norm 接続**: `fCubic(0)=∏(0-a^{p^i})=-normN a` ⟹ `normN a=-fCubic.eval 0=-(-1)=1`;
  `fCubic(2)=∏(2-a^{p^i})=∏(2-a)^{p^i}=normN(2-a)=1` (∵2∈F_p, (2-a)^{p^i}=2-a^{p^i})。
  (別経路: `Algebra.norm`+`PowerBasis.norm_gen_eq_coeff_zero_minpoly`+`minpoly`=fCubic、ただし
  `normN=algebraMap∘Algebra.norm` bridge (~100行, `norm_eq_prod_automorphisms`+Gal=Frobenius冪
  `Extension.exists_frob_pow_eq`/`exists_forall_apply_eq_pow`) が要。)

**(B) C.2 (q≥5)** (**最重・新 infra**): Frobenius 群 `H=P⋊U` (P=(F_{p^q},+), U=norm-1) の指標論。
`e=|E|`=構造定数 (K̂₁·K̂₁ の K̂₂ 係数) = `|{(u,v)∈U²|us+vs=2s}|`、既約指標 (|U| linear + (p-1) of
degree |U| induced from P) + 直交関係で `|E|≥p^{q-2}-p^{q/2}>1`。**concrete Frobenius 群の指標構成 +
class sum 構造定数 = repo の指標 infra から大規模に組む必要 (multi-session)**。

**(C) Lemma C.3 + Theorem C** (**最難・半上流**): `E=E⁻¹` の generators-and-relations (BG Step1-4,
mmd L4975-5005)。**仮説(B)=群G埋め込み σ:H→G, abelian p'-subgroup Q, y∈Q** が本質的に必要 ⟹
`FieldNormalizerData.field_model` の materialize (現 opaque) = 設計判断 + 上流 interface 改変と共有。
Theorem C = C.1∧C.2∧C.3 の assembly (容易) + 既存 scaffold `AppC.theoremC` への配線。

### 正直な現状評価
App C 完成は **3 つの深い研究レベル formalization (A 有限体持ち上げ / B Frobenius 群指標論 / C
generators-relations+仮説B)** を要し、**単一 /goal 自走では完了不能** (各々 multi-session)。anti-scaffold
原則ゆえ偽完成は不可。C.1 (最難 analytic core) + C.2(q=3) 前半は genuine に完成・commit 済。

### C.2 (q=3) 持ち上げ後半 — 実装 recipe 精緻化 (2026-06-04, aeval_pow_p まで済)
✅ 済: `exists_root_fCubic` (root a∈F_{p³}), `aeval_pow_p` (f(a)ᵖ=f(aᵖ))。
残 (次セッション、~100行):
- **a∉素体** `root_not_mem_range`: a=algebraMap b ⟹ `aeval (algebraMap b) fCubic = algebraMap (eval b fCubic)`
  (`Polynomial.aeval_algebraMap_apply`/`map_aeval`)=0 ⟹ eval b fCubic=0 (algebraMap 単射) ⟹ root-free 矛盾。
- **a,aᵖ,aᵖ² 相異**: `aeval_pow_p` で aᵖ,aᵖ² も根。`aᵖ³=a` (`FiniteField.pow_card`, card=p³)。
  aᵖ=a ⟹ `minpoly (ZMod p) a | X^p-X` (∵ aeval a (X^p-X)=aᵖ-a=0, `minpoly.dvd`)。
  `X^p-X=∏_{c}(X-C c)` over ZMod p (`roots_X_pow_card_sub_X`+`prod_multiset_X_sub_C_of_monic_of_roots_card_eq`)。
  minpoly irreducible (`minpoly.irreducible`) | ∏ ⟹ | (X-C c) ⟹ deg minpoly=1 ⟹ a=algebraMap c ⟹ a∈素体, 矛盾。
  aᵖ²≠a, aᵖ≠aᵖ² は aᵖ³=a で aᵖ=a に帰着。
- **因数分解 fCubic.map=∏(X-a^{p^i})**: 3 相異根 ⟹ `{a,aᵖ,aᵖ²}.val ≤ roots`, `card_roots'`≤3 ⟹ card roots=3,
  `splits_iff_card_roots` で Splits; `PerfectField.ofFinite`⟹`Irreducible.separable`⟹`nodup_roots` で
  roots=`{a,aᵖ,aᵖ²}` (multiset)。
- **norm 読み取り**: `Splits.eval_eq_prod_roots_of_monic` で `(fCubic.map).eval x = ∏_{r∈roots}(x-r)`。
  `(fCubic.map).eval 0 = ∏(0-a^{p^i}) = -normN a`, かつ `(fCubic.map).eval 0 = algebraMap(fCubic.eval 0)=algebraMap(-1)=-1`
  (`eval_map`+`hom_eval₂`) ⟹ normN a=1。eval 2: `(2-a)^{p^i}=2-a^{p^i}` (∵2∈F_p, `aeval_pow_p` 類似) ⟹
  normN(2-a)=∏(2-a^{p^i})=(fCubic.map).eval 2=algebraMap(fCubic.eval 2)=1。
- **a≠1**: a∉素体, 1∈素体 (=algebraMap 1)。
- ⟹ `a∈normSetE p 3 ∧ a≠1` ⟹ `2≤(normSetE p 3).ncard` (lemmaC2 q=3 分岐, `Set.one_lt_ncard`/2 元 {a,1})。
