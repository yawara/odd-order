---
id: 3000
slug: bg-appc-normset
title: "BG Appendix C: finite-field norm-set argument (Lemmas C.1-C.3, Theorem C)"
created: 2026-06-04
---

# BG Appendix C: finite-field norm-set argument (Lemmas C.1-C.3, Theorem C)

## 背景

下流監査 (`notes/meta/s16_appc_downstream_audit_2026_06_04.md`) で、`feitThompson` 最終矛盾 (`nonexistence_of_G`)
が消費する 2 gap のうち **`AppC.theoremC : FieldNormalizerData → p ≤ q`** が唯一の実質的下流ターゲットと特定。
これは BG Appendix C (mmd L4855-5005) の有限体 norm-set 論法 (Lemmas C.1-C.3)。BG §7-16 / Pf §10-16 と非交差で
進められる。実装計画 = `notes/bg/appC_normset_plan.md`。

## やること

実装先 `OddOrder/BG/AppC_NormSet.lean` (namespace `OddOrder.BG.AppC.NormSet`, mathlib-only leaf)。
実 `GaloisField p q = 𝔽_{p^q}` 上で norm `N(x)=∏_{i<q}x^{p^i}` と `E={a|N(a)=N(2-a)=1}` を materialize。

- [x] 基盤: `normN` / `normSetE` 定義 + **Remark (I)** `conditionA_iff_not_dvd` (条件A ⟺ q∤(p-1), axiom-clean, AxiomsCheck 登録) — 2026-06-04 commit
- [x] **Lemma C.1** `lemmaC1` (E=E⁻¹ ∧ |E|≥2 ⟹ p≤q) — **完成・sorry-free・axiom-clean・AxiomsCheck 登録** (2026-06-04 commit 32ae2f4)。τ-反復 `tauIter`/`dSeq`/`normN_dSeq_eq_one` (telescoping) + `natCast_pow_pPow` + degree-q Frobenius 多項式根数 (`natDegree_prod`/`card_roots'`/`CharP.natCast_injOn_Iio`)。
- [x] **Lemma C.2 (q=3)** — **完成** (2026-06-04 commit 5268ce0, sorry-free, axiom-clean, AxiomsCheck 登録):
  `exists_mem_normSetE_three` (∃a∈𝔽_{p³}, N(a)=N(2-a)=1 ∧ a≠1) + lemmaC2 q=3 分岐配線。
  pigeonhole → 既約 → root∈𝔽_{p³} (AdjoinRoot iso) → Frobenius 軌道 {a,aᵖ,aᵖ²} 相異 (root∉𝔽_p +
  Frobenius 固定点=𝔽_p) → fCubic.map=∏(X-a^{p^i}) (roots multiset 同定) → eval 0/2 で normN 読み取り。
  helpers: `aeval_pow_p`/`exists_root_fCubic`/`root_not_mem_range`/`mem_range_of_pow_p_eq_self`/`fCubic_monic`/`normN_three`。
- [x] **Remark (VII)** norm-one subgroup `U`: `normN` と `Algebra.norm` の bridge
  `normN_eq_algebraMap_norm`、`normOneUnits`、`mem_normOneUnits_iff_normN`、
  `normOneUnits_card : |U| = (p^q - 1)/(p - 1)` を追加し、AxiomsCheck 登録。
- [x] **Remark (VII)** prime-field/norm-one decomposition:
  `primeFieldUnits`、`unitsMap_norm_primeFieldUnit`、条件(A)下の `q` 乗全射
  `zmodUnits_pow_surjective_of_conditionA`、および
  `exists_primeFieldUnit_mul_normOne : 𝔽_{p^q}ˣ = 𝔽_pˣ · U` 型の分解補題を追加。
- [x] **Remark (VII)** direct-product intersection:
  `primeFieldUnits_inf_normOneUnits_eq_bot` を追加。条件(A)下で `𝔽_pˣ ∩ U = 1`、
  したがって前項の積分解が直積分解として使える。
- [x] **Remark (VII)** product decomposition carrier form:
  `primeFieldUnits_mul_normOneUnits_eq_univ` を追加。条件(A)下で carrier-set product
  `𝔽_pˣ · U` が `𝔽_{p^q}ˣ` 全体になることを、下流の class-sum/作用計算から直接使える形で固定。
- [x] **C.2 structure-constant bridge**: `normOnePairSet` と
  `normOnePairSet_ncard_eq_normSetE_ncard` を追加。`|E|` を `u+v=2` を満たす
  norm-one unit pairs の個数として同一視し、q≥5 の Frobenius 群 class-sum 計算への入口を materialize。
- [x] **C.2 class-sum pair form**: `normOnePairSetAt` と
  `normOnePairSetAt_ncard_eq_normSetE_ncard` を追加。BG 本文の `us+vs=2s` 形式
  (非零 `s`) の pair count を `|E|` に接続。
- [x] **C.2 q≥5 Frobenius semidirect setup**:
  `additiveFieldGroup`、`normOneMulAction`、`normOneFrobeniusGroup` を追加し、
  `normOneFrobenius_conj_inl` で `H=P⋊U` 内の共役作用 `u s u⁻¹ = u*s` を固定。
  さらに `mem_normOnePairSetAt_iff_inl_mul_inl` で `us+vs=2s` を `P≤H` 内の積方程式に変換。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 concrete Frobenius subgroup-pair**:
  `AppC_FrobeniusClassSum.lean` で `normOneFrobeniusKernel = inl(P).range`、
  `normOneFrobeniusComplement = inr(U).range` を定義し、normal/complement/nontrivial と
  `normOneFrobenius_isFrobeniusGroup : IsFrobeniusGroup H P U` (`1<q`) を証明。
  既存の induced-character Frobenius API に接続可能な subgroup-pair 形式。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 class-pair bridge**:
  `AppC_FrobeniusClassSum.lean` を追加。`normOneClassAt`、`normOneClassAt_mul_eq`、
  `normOnePairSetAt_isClassPair` で、`normOnePairSetAt` の pair を `H=P⋊U` の class-sum
  structure constant が数える `IsClassPair` に送る片方向 bridge を固定。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 conjugacy-class orbit bridge**:
  `normOneFrobenius_conj_inl_any` と `exists_normOne_mul_of_mem_normOneClass` を追加。
  任意の `H=P⋊U` 共役で additive-kernel 元の移動は `U` 成分だけで決まり、
  `inl s` の共役類が `U`-orbit と一致する逆向き bridge を固定。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 fixed-product fiber bridge**:
  `IsFixedProductClassPair`、`normOnePairSetAt_isFixedProductClassPair`、
  `exists_normOnePairSetAt_of_isFixedProductClassPair` を追加。`normOnePairSetAt s` が
  class-pair 全体ではなく product が代表元 `inl(2*s)` に等しい fiber を正確に数えることを固定。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 fixed-product fiber cardinality**:
  `fixedProductClassPairSet` と
  `normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard` を追加。`s≠0` で
  `normOnePairSetAt s` の pair count が fixed-product fiber の `ncard` と等しいことを証明。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 additive-kernel class size**:
  `normOneClassAt_carrier_ncard_eq_normOneUnits_card` を追加し、`s≠0` で `|C_s| = |U|` を証明。
  `2≠0` の下で product class `C_{2s}` も同じ cardinality になる特殊形を登録。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 full class-pair fiber decomposition**:
  `classPairSet` を exact-product fibers の disjoint union として分解し、`classSumCoeff` が
  product class 上の fixed-product fiber cardinalities の有限和になることを証明。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 class-size factor**:
  共役で fixed-product fiber cardinality が不変なことを証明し、
  `classSumCoeff(C_i,C_j,C_z) = |C_z| * |fixedFiber(z)|` まで整理。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 coefficient specialization**:
  `C_s*C_s` の `C_{2s}` class-sum coefficient を `|U| * |normOnePairSetAt s|`、さらに
  `|U| * |E|` に同一視。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 coefficient lower-bound reducer**:
  将来の指標論から `classSumCoeff(C_s,C_s,C_{2s}) > |U|` が得られれば `|E|≥2`。
  `s=1` 版で `2≠0`/`q≠0` side condition も解消。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 centralizer size input**:
  `C_H(inl s)=P` for `s≠0` と `|C_H(inl s)|=p^q` を証明。BG の直交関係評価
  `∑|χ(s^j)|²=|C_H(s^j)|=|P|` の concrete group-theory side を固定。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 semidirect-product group order**:
  `|H| = p^q * |U|` を `normOneFrobeniusGroup_card_eq` として証明。class-sum character formula の
  denominator を整理するための concrete size input。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 column orthogonality specialization**:
  `∑_{χ∈Irr(H)} χ(inl s) * star(χ(inl s)) = p^q` (`s≠0`) と `2*s` 版を証明。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 induced-character specialization**:
  `P≤H` の index が `|U|` であることを固定し、非自明 `θ∈Irr(P)` の誘導が `Irr(H)` になる
  `normOneFrobeniusKernel_induce_isIrreducible` と degree formula
  `normOneFrobeniusKernel_induce_apply_one` を追加。BG の induced degree-`|U|` character family へ接続。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 induced-character degree-one specialization**:
  `P` が abelian であることを `normOneFrobeniusKernel_mul_comm` として明示し、任意の
  `θ∈Irr(P)` について `θ(1)=1`、従って `Ind_P^H θ` の degree が `|U|` であることを証明。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 induced-character support specialization**:
  `Ind_P^H θ` の support が `P` に含まれること、および非自明 complement 元 `inr u` 上では
  0 になることを concrete theorem 化。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 linear-character kernel specialization**:
  `1<q` なら任意の `inl(s)∈P` が `H=P⋊U` の commutator であることを証明し、
  degree-one irreducible character / subtype 版が additive kernel 上で値 `1` になることを concrete theorem 化。
  q≥5 の class-sum character formula で linear characters の寄与を固定する入力。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 character expansion infra**:
  subtype 版 `χ(g⁻¹)=star(χ(g))` と class-function Fourier 展開
  `sum_inner_irreducibleCharacter_smul` を追加。class-sum coefficient character formula の反転入力。
  AxiomsCheck 登録済み。
- [x] **C.2 q≥5 kernel-character main contribution split**:
  `P⊆ker χ` で filter した既約指標の degree-square sum を `|H/P|=|U|` に固定し、
  kernel 元 `inl(s)` 上での column contribution も `|U|` になる concrete theorem を追加。
  total column norm `p^q` との差として、非 kernel 側の寄与が `p^q-|U|` になる split も theorem 化。
  q≥5 coefficient lower bound を主項と non-kernel error に分ける数値入力。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 non-kernel error bound, degree-free form**:
  非 kernel 既約指標が additive kernel から誘導され degree `|U|` を持つことを使い、既存の
  `hdeg` 仮定付き評価を `normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt` に閉じた。
  これで残る q≥5 branch の Lean core は class-sum 公式から coefficient 下界を抜く実数/自然数評価。
- [x] **C.2 q≥5 coefficient bridge, numeric separation form**:
  class-sum 公式 `coeff * p^q = |U|^3 + error` と degree-free error bound から、
  任意の `c≤|U|` が main term から error bound より遠いという純数値仮定を渡せば
  `|U| < coeff` を返す `normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card_of_error_separation` を追加。
- [x] **C.2 q≥5 norm-one subgroup lower bound**:
  `|U|=(p^q-1)/(p-1)=1+p+...+p^(q-1)` の最大項から
  `pow_sub_one_le_normOneUnits_card : p^(q-1) ≤ |U|` を追加。q≥5 の純数値評価の入力。
- [x] **C.2 q≥5 numeric separation**:
  幾何和の最後の二項から `p^q*(1+p^(q-2)) ≤ |U|^2` を証明し、
  `normOneFrobenius_error_separation_of_five_le` で任意の `c≤|U|` に対する
  non-kernel error separation を閉じた。AxiomsCheck 登録済み。
- [x] **C.2 q≥5 class-sum coefficient lower bound**:
  `normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card` と
  `normSetE_ncard_ge_two_of_five_le` を追加し、class-sum 側では q≥5 分岐が
  `2 ≤ |E|` まで到達。`AppC_NormSet.lemmaC2` 本体への直配線は import cycle 回避のため
  後続の placement 整理で扱う。AxiomsCheck 登録済み。
- [x] **Lemma C.2 packaging (q≥5)**: q=3 helper を `AppC_NormSet` に残し、
  full `lemmaC2` を class-sum 下流の `AppC_LemmaC2` へ移して
  `normSetE_ncard_ge_two_of_five_le` を配線。循環 import なしで `sorry` を除去。
- [x] **Lemma C.3 p=3 branch**: BG C.3 note を `normSetE_eq_inv_of_p_eq_three` として純有限体で証明。characteristic 3 では `2*a-1=2-a` なので generator-relation argument なしで `E=E⁻¹`。AxiomsCheck 登録済み。
- [x] **AppC-facing Lemma C.3 interface**: `S16.FieldNormalizerData` の C.3 obligation を最終結論 `E=E⁻¹` から generator-relation 出力 `appCNormSetGeneratorRelation` (`∀a∈E, N(2*a-1)=1`) に細分化し、`AppC_FinalContradiction.lemmaC3_inverse_closed` は純有限体補題経由で `sorry` なしに維持 (2026-06-04, branch `codex/ft-appc-downstream`)。
- [x] **Lemma C.3 Step 1 finite-field/semidirect core**: condition(A) 下の直積分解
  `𝔽_{p^q}ˣ = 𝔽_pˣ · U` から、任意の非零 prime-field line `𝔽_p s` に対して全 field 点が
  `U`-orbit に入る `exists_normOne_mul_primeLine_eq` を証明。さらに concrete `P⋊U` 内の任意の元を
  `u s₁ v` (`u,v∈U`, `s₁∈𝔽_p s`) と書く
  `normOneFrobenius_exists_inr_primeLine_inr` まで materialize。AxiomsCheck 登録済み。
- [x] **Lemma C.3 Step 2 finite-field/semidirect core**: `U ∩ 𝔽_pˣ = 1` から
  `normOneUnits_eq_one_of_mem_primeFieldUnits` を公開し、prime-field line 上の relation
  `c*s + u*(d*s)=0` が BG Step 2 の二択 `(c=d=0) ∨ (u=1 ∧ c+d=0)` を強制する
  `generatorRelation_step2_primeLine` まで証明。さらに concrete `P⋊U` 内で `s₁ u s₂∈U` から同じ二択を返す
  `normOneFrobenius_generatorRelation_step2_primeLine` を追加。AxiomsCheck 登録済み。
- [x] **Lemma C.3 Step 3 finite-field irreducibility input**: condition(A) 下で
  norm-one subgroup `U` が加法群 `𝔽_{p^q}` を `𝔽_p`-既約に作用することを
  `normOneUnits_invariant_submodule_eq_top_of_ne_bot` として証明。さらに非零 `U`-不変
  subspace が `U` とともに concrete `P⋊U` 全体を生成することを
  `normOneFrobeniusSubspaceGroup_eq_top_of_ne_bot` として固定。続いて任意の subgroup
  `X≤P⋊U` について、`U≤X` かつ `X∩P` が非自明なら `X=⊤` とする
  `normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_exists_inl` を materialize。さらに
  semidirect product の分解から `U≤X` かつ `X≠U` なら `X=⊤` とする
  `normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range` まで固定。
  AxiomsCheck 登録済み。
- [x] **Lemma C.3 Step 4 finite-field Frobenius core**: `normN_pow_p` と
  `normSetE_pow_p` により `p`-power Frobenius が `E` を保つことを証明し、
  `normSetE_frobenius_pair` で `a,b∈E` かつ `a+b=2` なら `a^p,b^p∈E` かつ
  `a^p+b^p=2` を固定。さらに condition(A) から `u∈U` かつ `u^(p-1)=1` なら
  `u=1` を返す `normOneUnits_eq_one_of_pow_sub_one_eq_one` を追加。BG Step 4 の
  Frobenius propagation / “by (A)” 入力。AxiomsCheck 登録済み。
- [x] **Lemma C.3 Step 4 twisted-inverse induction tail**: BG 最後の
  `(a⁻¹)^{t^3}` を p 回反復する議論を `inv_mem_of_twistedInv_step` として一般化し、
  field/full-unit one-step output から inverse-closure/generator relation へ落とす adapter 群を追加。
  さらに actual `t`-action に合わせた norm-one group 版
  `normSetETwistedNormOneStep`, `normSetE_eq_inv_of_twisted_normOne_step`,
  `forall_normN_two_mul_sub_one_of_twisted_normOne_step` を追加し、S16 producer obligation も
  `appCNormSetTwistedNormOneStep` に狭めた。AxiomsCheck 登録済み。
- [x] **Theorem C scaffold assembly**: 既存 `AppC_FinalContradiction.theoremC` から直接 `sorry` を除去し、実 finite-field `lemmaC1`/`lemmaC2` + C.3 interface field に配線 (2026-06-04, branch `codex/ft-appc-downstream`)。
- [x] **AppC-facing Lemma C.2 bridge**: `conditionA` だけから `normSetCardGeTwo` を返す
  `lemmaC2_card_ge_two_of_conditionA` を分離し、`FieldNormalizerData` 依存の wrapper はこの adapter を呼ぶ形に整理。
- [x] **S16/AppC Hypothesis (B) concrete carrier**: `S16.FieldNormalizerData` と
  `AppC_FinalContradiction.HypothesisB` の opaque model/formula fields を、concrete `H=P⋊U`、
  monomorphism `σ:H→G`、`P`/`P0`/`U` image identification、normalizer 条件に置換。
- [x] **C.3 Step 4 prime-line generator extraction**: concrete `H=P⋊U` の
  `P0` 内の非自明元 `fieldNormalizerPrimeLineGenerator` を定義し、
  `FieldNormalizerData.s` として `G` へ transport。`s ∈ W₂`、`s ≠ 1`、
  `s ∈ N_G(Q)` を derived theorem 化。
- [x] **C.3 Step 4 conjugate line seed**: `FieldNormalizerData.P1` と
  `FieldNormalizerData.t` を materialize。`t ∈ P1`、`t ≠ 1`、
  `P1 ≤ N_G(U)`、`t ∈ N_G(U)`、`t ∈ N_G(Q)`、`s⁻¹t ∈ Q` を theorem 化し、
  BG Step3/Step4 の conjugate-line / Q-commutation 計算の入口を固定。
- [x] **C.3 Step 4 Q-power commutator seed**: `inv_pow_mul_pow_mem_of_inv_mul_mem` で
  `s⁻¹t ∈ Q` から `(s⁻¹)^n t^n ∈ Q` を、逆向きにも `t⁻¹s ∈ Q` から
  `(t⁻¹)^n s^n ∈ Q` を theorem 化。BG Step4 の
  `s^{-i}t^i ∈ Q` 型の冪計算を group-theoretic side に固定。
- [x] **C.3 Step 4 norm-one transport**: concrete `normOneUnits` を
  `σ` で Peterfalvi の `U` へ運ぶ `normOneUnitsEquivU` を作成し、
  `t ∈ N_G(U)` から `tConjUAut` / `tConjNormOneUnitsAut` を theorem 化。
  `σ(inr u)` に対する ambient conjugation 公式も rewrite 可能にした。
- [x] **C.3 Step 4 twisted t-action bridge**: `normOneUnitsEquivU_twistedInv_tConjNormOneUnitsAut_apply_coe` と
  `appC_twisted_normOne_step_of_tConjNormOneUnitsAut` を公開し、残りの producer を
  concrete `t` 共役が `E` を保つことに縮約。AxiomsCheck 登録済み。
- [x] **C.3 Step 4 p-power action seed**: `fieldNormalizerPrimeLineGenerator_pow_p`、
  `s_pow_p_eq_one`、`t_pow_p_eq_one`、`tConjUAut_pow_p_eq_one`、
  `tConjNormOneUnitsAut_pow_p_eq_one` を追加し、BG Step4 の `t`-conjugation action が
  p 乗で恒等になることを concrete complement 側にも transport した。
- [x] **C.3 Step 4 E-to-pair API**: `a∈E` を norm-one unit に持ち上げる
  `normOneUnitOfMemNormSetE` と、BG の pair `(a,2-a)` を `normOnePairSet` / `normOnePairSetAt`
  に入れる `normOnePairOfMemNormSetE_mem_*` を公開。C.3 group proof で Step4 の
  `a+b=2` を concrete `U`-pair として再利用する入口を固定。AxiomsCheck 登録済み。
- [x] **C.3 Step 4 Q-commutativity bridge**: `Q_elementaryAbelian` から
  `FieldNormalizerData.Q_mul_comm` を公開し、`s^{-n}t^n` / `t^{-n}s^n` 型の
  Q 内 commutator factors が互いに可換であることを theorem 化。BG の
  “Since Q is commutative, (C.3) becomes (C.4)” を使う入口を固定。AxiomsCheck 登録済み。
- [x] **C.3 Step 1 decomposition bridge**: `fieldNormalizerPrimeLineElement`、
  `exists_normOne_primeLine_normOne`、`exists_sigma_normOne_primeLine_normOne_of_mem_PU` を公開し、
  concrete `P⋊U` と transported `PU` の任意元を `u s₁ v` に分解できる入口を固定。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 2 generator-relation bridge**: `generatorRelation_step2_primeLine` と
  `generatorRelation_step2_primeLine_of_sigma_mem_U` を公開し、`s₁ u s₂∈U` から
  BG Step2 の二択を concrete `P⋊U` と transported `G` の両方で読めるようにした。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 3 P₀ non-normalization bridge**:
  `fieldNormalizerNormOneUnits_card_gt_one` / `exists_fieldNormalizerNormOneUnit_ne_one` と
  `s_not_normalizes_U` / `W2_not_le_normalizer_U` を公開し、非自明 norm-one unit と
  Step2 generator relation から `P₀` (`W₂`) が `U` を正規化できないことを transport。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 3 `P₁=P₀` contradiction endpoint**:
  `P1_ne_W2` / `W2_ne_P1` を公開し、`P₁≤N_G(U)` と `W₂⊄N_G(U)` から
  BG Step3 の `P₁=P₀` 矛盾を直接消費できる形に固定。AxiomsCheck 登録済み。
- [x] **C.3 Step 3 irreducibility bridge**:
  `subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U` を公開し、`U≤X≤PU` かつ
  `X≠U` なら `X=PU` となる BG Step3 の irreducibility 入力を `σ` 経由で transport。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 3 intersection dichotomy bridge**:
  `P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U` と
  `P_sup_U_inf_conj_t_pow_eq_U_or_eq_P_sup_U` を公開し、`g∈N_G(U)` から
  `(PU)∩(PU)^g = U ∨ (PU)∩(PU)^g = PU` を読めるようにした。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 4 sigma normal-form bridge**: `sigma_eq_left_eq`、
  `sigma_eq_right_eq`、`sigma_eq_iff_left_right_eq` を公開し、`σ : P⋊U → G` の
  等式から concrete 半直積の `left/right` 成分を読む API を固定。BG Step4 の
  “mod P” で `U` 成分だけを取り出す入力。AxiomsCheck 登録済み。
- [x] **C.3 Step 4 `(C.5)` decomposition bridge**:
  `s_mem_P` / `s_zpow_mem_P_sup_U`、`t_zpow_conj_sigma_inr_mem_U`、および
  `exists_step4_decomposition_of_zpow_tConj_normOne` を公開し、`s^m (u)^{t^n} s^r`
  型の項が `PU` に入り Step1 の `u₁s₁v₁` normal form を持つことを固定。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 4 natural-power `t`-action bridge**:
  `normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe` と
  `t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` を公開し、
  `(u)^{t^n}` を concrete norm-one unit の `tConjNormOneUnitsAut^n` として
  読めるようにした。AxiomsCheck 登録済み。
- [x] **C.3 Step 4 natural-power `(C.5)` normal-form bridge**:
  `s_zpow_mul_t_pow_conj_sigma_inr_mul_s_zpow_eq_sigma_inr_tConjNormOneUnitsAut_pow`、
  `s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U`、
  `exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow` を公開し、
  `(C.5)` の各中間項を concrete `tConjNormOneUnitsAut^n` で Step1 normal form に渡せるようにした。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 4 `mod P` right-component bridge**:
  `right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition` を公開し、
  natural-power `(C.5)` normal form から `tConjNormOneUnitsAut^n u = u₁*v₁` を
  SemidirectProduct の right projection で読めるようにした。AxiomsCheck 登録済み。
- [x] **C.3 Step 4 `k=3` first `(C.5)` bridge**:
  `exists_step4_first_k_three_decomposition` と
  `right_component_of_step4_first_k_three_decomposition` を公開し、BG final paragraph の
  `s(a^{-1})^{t^3}s^{-2}=u₁s₁v₁` と “mod P” 読み
  `(a^{-1})^{t^3}=u₁*v₁` を concrete `tConjNormOneUnitsAut` で消費できる形にした。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 4 `k=3` generator-relation coordinate bridge**:
  `normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition` と
  `normN_two_mul_sub_one_of_step4_first_k_three_decomposition` を公開し、
  `s φ(u⁻¹) s⁻² = u₁ s⁻¹ v₁` の additive coordinate から
  `N(2*φ(u⁻¹)-1)=1` を concrete `P⋊U` と S16 field normalizer data の両方で読める形にした。
  AxiomsCheck 登録済み。残る hard input は、前段 C.4-C.10/Step4 から middle prime-line factor が
  実際に `s⁻¹` になることを materialize し、`appC_twisted_normOne_step` へ接続する部分。
- [x] **C.3 Step 4 arbitrary middle-coordinate adapter**:
  `normN_two_mul_sub_one_of_sigma_first_k_three_decomposition` と
  `appC_normSet_generator_relation_of_first_k_three_coordinate` を公開し、任意の
  norm-one middle complement `w` について first `k=3` normal form の middle factor が `s⁻¹` なら
  `N(2*w-1)=1` を読めるようにした。さらに、これを `∀w∈E` で供給すれば
  `appCNormSetGeneratorRelation` が直ちに出る。AxiomsCheck 登録済み。
  次の hard target は BG C.4-C.10 の消去から、この universal middle-coordinate step を materialize すること。
- [x] **C.3 Step 4 P-U intersection bridge**: `fieldNormalizerKernel_inf_complement_eq_bot` と
  `P_inf_U_eq_bot` を公開し、concrete `P⋊U` と Peterfalvi 側 `G` の両方で
  `P∩U=1` を使えるようにした。BG Step4 の “mod P, since U∩P=1” 入力。
  AxiomsCheck 登録済み。
- [x] **C.3 Step 4 P0-Q intersection bridge**: `W2_pow_p_eq_one`、
  `Q_pow_q_eq_one`、`W2_inf_Q_eq_bot` を公開し、`W₂=σ(P₀)` と `Q` の交わりが
  自明であることを concrete data から導出。BG Step4 の “mod Q, since P₀∩Q=1”
  を使う入力。AxiomsCheck 登録済み。
- [ ] **C.3 genuine proof/materialization**: `appCNormSetTwistedNormOneStep` を FieldNormalizerData/Hypothesis(B) の具体 embedding data から証明する。これは `tConjNormOneUnitsAut` による `u ↦ t(u⁻¹)t⁻¹` が `E` を保つという BG C.3 Step3/Step4 本体。`appCNormSetGeneratorRelation` (`∀a∈E, N(2*a-1)=1`) は derived theorem で供給済み。

## 完了条件

`AppC.theoremC` が sorry-free (Lemmas C.1-C.3 + 配線完成)。`nonexistence_of_G` の BG 側 gap が閉じる。
2026-06-04 時点で `AppC_FinalContradiction` は direct sorry-free; `theoremC` は AxiomsCheck 登録済み。
残る数学的 C.3 generator-relation は `S16.FieldNormalizerData.appC_twisted_normOne_step` の upstream materialization として追跡する。`appC_normSet_generator_relation` は derived theorem になった。AppC 側では `N(2*a-1)=1` から `E=E⁻¹` への有限体代数部分を証明済み。
段階的に C.1 → C.2(q=3) → C.2(q≥5) → assembly → C.3 materialization。

## 参照

- 計画: `notes/bg/appC_normset_plan.md`
- 監査: `notes/meta/s16_appc_downstream_audit_2026_06_04.md`
- 原典: BG mmd `references/bg/local-analysis.mmd` L4855-5005
- 既存 scaffold: `OddOrder/BG/AppC_FinalContradiction.lean` (theoremC/NormSetData/HypothesisB, opaque)

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

AppC C.1–C.3 完了・field-free: `S16_NonExistenceGCore.lean` は comment-strip で実 sorry 0 (検証 2026-07-02)。
残 = FieldNormalizerData producer (lane c、issue 4001)。
