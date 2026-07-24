---
id: 148
slug: app3-honest-closeout
title: "Appendix III honest close-out: Lemma 1(a)/Lemma 2/Prop 1/Prop 2 の実形式化"
created: 2026-07-24
---

# Appendix III honest close-out: Lemma 1(a)/Lemma 2/Prop 1/Prop 2 の実形式化

## 背景

`OddOrder/Peterfalvi/Appendices/Suzuki2Groups.lean` に居座っていた opaque-Prop
scaffold 4 本 (`square_map_quadratic` / `higman_classification` /
`typeB_field_model` / `typeB_automorphism_structure`) + 空 structure 3 本
(`QuadraticMapData` / `FiniteFieldTwoMapBasis` / `SuzukiTypeData`) は
**論理的空虚** (`⟨True, trivial⟩` で閉じるトートロジー、issue 0127 ② の audit)
のため 2026-07-24 に削除した (削除トリガー = 2048/9160 closed + Higman 完成、成立済)。

`higman_classification` は **置換不要の純削除** — 実体は
`OddOrder.Higman.Suzuki2Groups.higmanClassification` /
`higmanClassification_of_isSuzuki2Group` として完成済みで、0127 ③ の
ユーザー裁定「分類定理の薄い Peterfalvi wrapper は作らない」により
Pf 側の再掲は書かない。

残り 3 本の scaffold が指していた **App III の番号付き結果は未形式化のまま**
なので、本 issue で honest 形式化を追跡する (sorry マーカーは無いが genuine
残作業; sorry 数で進捗を測らない原則)。

## やること (文書順)

- [x] **Lemma 1(a)** ✅ 2026-07-24 (hub): `QuadraticExtensions.lean` (1(b) と同居) に一般形で
      実装 — `centralSquare` (squaring の descend) / `centralCommPairing` (**polarization として
      定義**することで well-definedness 証明を丸ごと回避する設計) / `centralCommPairing_mk`
      (polar form = commutator pairing `⁅y,x⁆`) / `centralCommPairing_mul_left/right`
      (biadditivity — 今日 dedup したばかりの `commutatorElement_mul_*_of_class_le_two` を cite) /
      **`centralSquareQuadraticMap`** (bundled `QuadraticMap (ZMod 2)`、AxiomsCheck 登録済)。
      書籍の「P 2-group」仮定は不要 (使うのは W ≤ Z(P) + 両 exponent 2 のみ) なので一般化。
      ⚠ 実装知見: `IsMulCommutative.instCommGroup` は **scoped instance** — `open scoped
      IsMulCommutative` が無いと letI 連鎖が組めず zmodModule の型と不一致になる。
- [ ] **Lemma 2**: `F_{2^n}` 上の linear / bilinear / quadratic map の基底表示。
      **(a) ✅ 2026-07-24 (hub)**: `SemilinearFieldAut.lean` に一般標数で実装 —
      `linearIndependent_algAut_toLinearMap` (Dedekind `linearIndependent_monoidHom` を
      `LinearIndependent.comp` + `.of_comp coeFnLinear` で 𝔽_p-線形写像空間へ転送) /
      `finrank_linearMap_self_eq_finrank` (`Module.finBasis` + `Basis.constr F` の equiv で
      dim_F Hom = [F:𝔽_p]) / **`algAutLinearBasis : Module.Basis (F ≃ₐ[ZMod p] F) F
      (F →ₗ[ZMod p] F)`** (`basisOfLinearIndependentOfCardEqFinrank` +
      `IsGalois.card_aut_eq_finrank`、AxiomsCheck 登録)。
      **(b) ✅ 2026-07-24 (hub、theorem-packaging)**: `algAutMulBilin` (σ(x)τ(y) の bilinear 化、
      `LinearMap.mul.compl₁₂`) / `linearIndependent_algAutMulBilin` (⭐ 独立性は **F × F の積
      monoid 上の Dedekind** に帰着 — 対 (σ,τ) を `algAutPairChar : (F × F) →* F` とみなすと
      (a) と同一パターンで sum 操作不要) / `finrank_bilinMap_self_eq` (dim = n²) /
      `card_autProd_eq_finrank_bilinMap`。AxiomsCheck 2 assert。
      ⚠ **bundled `Module.Basis` は繰延**: 二重入れ子 `F →ₗ[ZMod p] F →ₗ[ZMod p] F` 上の
      `basisOfLinearIndependentOfCardEqFinrank` が whnf/isDefEq 発散 (maxHeartbeats 3.2M でも
      不足、diagnostics で `Add.add` 23,535 回 unfold を確認; card 補題の top-level 抽出・
      Nonempty/Fintype letI 明示・Nat.card 経路化はいずれも効かず)。独立性 + card=dim の
      theorem 2 本が数学的内容としては完結 (有限次元で basis と同値)。bundle 再挑戦の候補 =
      `@Basis.mk` 全 instance 明示 / instance 径路の pin / mathlib 側の module-instance 整理待ち。
      (追記: spanning を `span_eq_top_of_card_eq_finrank` の theorem 形で出す試みも同じ
      isDefEq 発散 — bundle/spanning とも同根で pending。)
      **(c) ✅ 2026-07-24 (hub、独立性側)**: `autMulQuadraticMap σ τ` (QuadraticMap (ZMod 2)、
      companion = `algAutMulBilin στ + τσ`) / **`autMulQuadratic_coeff_symm`** (消える結合の
      係数は対称 — polar 化で対角が char 2 消滅し、swap 再指数 + 積 monoid 指標の Dedekind
      独立で閉じる) / **`autMulQuadratic_diag_eq_zero`** (対角係数消滅 — swap involution で
      off-diag が打ち消し、`frobeniusEquiv` 全射で (a) に帰着)。ordered-pair 供述にしたので
      Sym2/順序 index が不要になった (2 定理が合わせて「サイズ 1–2 部分集合族の独立性」)。
      AxiomsCheck 2 assert。spanning 側は (b) と同じ packaging 繰延。
      ⚠ 実装知見: 入れ子 `F →ₗ F →ₗ F` の module instance は `LinearMap.ext`/評価/`map'`/
      `ker_eq_bot` どれも isDefEq 爆発 — **常に関数空間 (Pi) + MonoidHom 指標側で作業**し、
      入れ子空間には (b) の of_comp 一撃でしか触れないこと。
- [x] **Proposition 1** ✅ 2026-07-24 (hub): `B(n,1,ε)` が field model `q(x) = x·x̄` を許容する。
      **前半**: 新 leaf `Suzuki2Groups/FieldModel.lean` (hub 配線済) —
      `fieldModelPoly = X² + εX + 1` (monicity!/compute_degree!) /
      **`fieldModelPoly_irreducible`** (anisotropy → 根なし → deg-2 既約、
      `irreducible_of_degree_le_three_of_not_isRoot`) / `epsilon_ne_zero_of_anisotropic` /
      `FieldModel ε := AdjoinRoot` + `alpha` + `add_self` (2•x=0 経由で **CharP instance 不要**の
      char-2 補題) + `alpha_sq` (α²=εα+1) + `aeval_conj_root` (ε+α も根)。
      **後半**: ① conj 自己同型 = **`AdjoinRoot.liftAlgHom` を ε+α へ** (現 mathlib は
      `liftHom` でなく `liftAlgHom (i : R →ₐ[S] T)`; i = `Algebra.ofId`、根条件は
      `simpa [aeval_def]`)。bijective 化は **`AlgEquiv.ofAlgHom` + 自己合成 = id**
      (`algHom_ext` で root 値のみ、有限次元論法・field instance とも不要) → `conj` /
      `conj_conj` (involution) / `conj_ne_refl` (ε≠0、`AdjoinRoot.coe_injective` +
      `linear_combination`) ② `equivProd : (F×F) ≃ₗ[F] FieldModel ε` =
      `powerBasis'.basis.reindex (finCongr natDegree=2)` の equivFun.symm ∘
      `finTwoArrow.symm`; apply は `Basis.equivFun_symm_apply` + `Fin.sum_univ_two` +
      `norm_num [LinearEquiv.finTwoArrow]` ③ **norm 恒等式 `mul_conj`** =
      `linear_combination B²·alpha_sq + add_self (ABα + B²Eα)` (char-2 の 2t=0 を
      linear_combination 項として渡すのが鍵) ④ `isField` (Fact 化で field instance)。
      AxiomsCheck 5 assert (irreducible/isField/conj_conj/conj_ne_refl/mul_conj) 全て
      axiom-clean。原文 = PDF p. 142。
- [ ] **Proposition 2**: `B(n,1)` の automorphism map が surjective で
      kernel が elementary abelian 2-group。原文 = PDF pp. 142-143 (α ↦ f_α は
      Aut(B(n,1)) から「x ↦ λσ(x) (λ ∈ E*, σ ∈ Aut(E)) の群」への全射 hom、
      kernel は Lemma 1(d) 経由で elementary abelian)。**6 段分解 (2026-07-24 設計)**:
  - [x] **(i) Lemma 1(c)** ✅ 2026-07-24 (hub): 新 leaf
        `GroupTheory/CentralExtensionAutomorphisms.lean` (配線済) —
        `GroupExtension.twistCoords` (端群の reindex; 中央群不変) /
        `comp_squareMap_eq_of_mulEquiv` (necessity — square 座標の直計算) /
        `exists_mulEquiv_of_comp_squareMap_eq` (sufficiency — **T を (f,g) で
        twist して同一 square map の 2 拡大に還元 → 既存
        `equivOfCommonSquareMap`**。書籍の基底持ち上げ論法は再実装不要)。
        AxiomsCheck 2 assert。
  - [x] **(ii) Lemma 1(d)** ✅ 2026-07-24 (hub): 同 leaf —
        `GroupExtension.inducingIdAuts` (Subgroup (MulAut E)) /
        `inducesIdHom` (deviation Φe·e⁻¹ の W 座標が V →+ W;
        well-definedness は inl 固定のみ、加法性に centrality) /
        `autOfHom`+`autOfHomHom` (逆向き hom) / injective + range 一致 →
        **`inducingIdAutsEquivHom : Multiplicative (V →+ W) ≃* inducingIdAuts`** /
        **`isElementaryAbelian_inducingIdAuts`** (ZMod 2 加群で)。
        AxiomsCheck 2 assert。実装知見: kernelCoordinate は
        `MonoidHom.ofInjective .symm` で取ると `simp [定義]` 一発で
        inl_kernelCoordinate が閉じる。
  - [x] **(iii) 誘導写像機構** ✅ 2026-07-24 (hub): 新 leaf
        `Suzuki2Groups/AutomorphismInducedMaps.lean` (hub 経由配線済) —
        `center_eq_range_inl` (hrad = polarization 非退化) /
        `map_mem_range_inl_iff` (center characteristic;
        `characteristic_iff_comap_eq.mp inferInstance` 形) /
        `autQuotientFun`・`autKernelFun` / `map_inl`・`map_quotient` /
        加法性 2 本 / `autQuotientAddEquiv` /
        **`autQuotientHom : MulAut X →* Multiplicative (AddAut V)`** /
        `autKernel_squareMap` (compat g∘q=q∘f) /
        `inducesId_of_autQuotient_id` (hspan) / `ker_autQuotientHom` =
        inducingIdAuts / `isElementaryAbelian_ker_autQuotientHom`。
        AxiomsCheck 3 assert (autQuotientHom / ker / isElementaryAbelian)。
        診断済み修正 ①〜④ (map_inl の ofAdd 形 statement / squareMap は
        exact 任せ / additive case 名 mem-zero-add-neg / show→change) は
        全て有効だった。⚠ 追加で必要だった 2 点: (α) 現 mathlib に
        `Mathlib.Algebra.Group.Aut` は無い — MulAut/AddAut は
        `Mathlib.Algebra.Group.End` (β) **AddAut は 2026-05-26 に加法群化**
        (mul_def→add_def 等 deprecated alias 化) — `MulAut X →* AddAut V` は
        型エラーで、codomain を `Multiplicative (AddAut V)` に包む
        (Lemma 1(d) の `Multiplicative (V →+ W)` と同じ流儀; map_mul' は
        AddEquiv ext + `congrArg Multiplicative.ofAdd`、apply 補題は
        `.toAdd v` 形)。`Characteristic.fixed` も直接射影不可 →
        `characteristic_iff_comap_eq.mp inferInstance` (repo 慣用形)。
  - [x] **(iv) norm 全射性** ✅ 2026-07-24 (hub): `FieldModel.lean` 末尾に追加。
        **units/cyclic 勘定は不要だった** — char 2 では conj がスカラー固定 +
        Frobenius 全射 (`frobeniusEquiv F 2`, 要 `[Finite F]`) により、
        `a² = c` なるスカラー a の norm `a·ā = a²` だけで F を尽くす。
        `exists_mul_conj_eq` (norm 全射) / `typeBQuadraticMap_surjective`
        (`q(a,0) = a²` で第 1 軸のみで全射) /
        `closure_range_typeBQuadraticMap` ((iii) の hspan 供給)。
        anisotropy 仮定も不要。AxiomsCheck 2 assert。
  - [x] **(v) semilinear 分類 (核心)** — **f-側 collapse ✅ 2026-07-24 (hub)**:
        `SemilinearFieldAut.lean` に抽象形で追加 —
        **`exists_smul_algAut_of_norm_intertwiner`**: κ 非自明 involutive
        (`κ*κ = 1`)、f ≠ 0 𝔽₂-linear、`Σ_ρ μ_ρ ρ(x·κx) = f(x)·κ(f(x))`
        ⟹ `∃ λ ≠ 0, σ, κσκ = σ ∧ f = λ·σ`。証明 = Lemma 2(a) で展開 →
        pair 族の vanishing 結合 c(α,β) = λ_α κ(λ_{κβ}) + δ_{β,ακ} μ_α を
        組み → diag/symm (Lemma 2(c)) が書籍の (3)(4) → 一点集中。
        AxiomsCheck 1 assert。実装知見: ⚠ **κσκ = σ (可換性) は証明から
        無料で出る** (Gal abelian を前提部品にする必要なし — α ≠ κακ なら
        λ_α = 0 になるため)。μ-δ 項は (4) 適用箇所 (β ≠ ακ) で両側とも
        消えるので対角 δ 対称性も不要。`push_neg` は deprecated → `push Not`;
        `self_eq_mul_right` → 現 mathlib 名 `left_eq_mul`。
        **g-側 μ collapse は Prop 2 の statement に不要と判明** (kernel も
        全射性も f-側のみで述べられる; 逆向きは g を直接構成) — 実施せず。
  - [x] **(vi) Prop 2 組み上げ** ✅ 2026-07-24 (hub): 新 leaf
        `Suzuki2Groups/AutomorphismClassification.lean` (hub 配線済) —
        **`exists_semilinear_of_aut`** (順: f_Φ を equivProd で E に移送 →
        autKernel_squareMap を mul_conj + 展開 lift で norm-intertwiner 化 →
        (v) collapse) / **`exists_aut_of_semilinear`** (逆: 任意の λσ に対し
        g := N(λ)·σ|_F を restrictNormal で構成、σκ = κσ は
        `IsCyclic Gal` instance (mathlib FieldTheory.Finite.Basic) の生成元
        zpow 表示で、Lemma 1(c) sufficiency で lift; basis は Fin n 限定 =
        1(c) の要求) / **`isElementaryAbelian_ker_autQuotientHom_typeB`**
        (kernel; hspan = (iv) の closure_range)。AxiomsCheck 3 assert。
        ⚠ 実装知見: FieldModel (= AdjoinRoot) に `ZMod.algebra` の local
        instance を足すと `AdjoinRoot.instSMulAdjoinRoot` と defeq-非構文的
        SMul diamond — **Algebra (ZMod 2) F だけ宣言し AdjoinRoot の generic
        Algebra/IsScalarTower instance に任せる**のが正解。
- [ ] Theorem (e) ⟹ 方向は既存 [issue 2052](2052-pf-appendix3-e-forward.md) —
      本 issue とは独立に追跡継続。

## 完了条件

上記 4 項が sorry-free で landing し AxiomsCheck 登録、
`Suzuki2Groups.lean` hub docstring の「Still to be formalized」段落を更新。

## 参照

- issue 0127 ②③ (audit と削除裁定・wrapper 不要裁定)
- `OddOrder/Higman/Suzuki2Groups/` (Higman 定理本体・完成済)
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/` (concrete leaves)
