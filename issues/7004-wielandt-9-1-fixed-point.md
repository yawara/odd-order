---
id: 7004
slug: wielandt-9-1-fixed-point
title: "Pf (9.1) Wielandt fixed-point formula — CoprimeAction.lean 3 sorries"
created: 2026-06-16
owner: lane-f
---

# Pf (9.1) Wielandt fixed-point formula — CoprimeAction.lean 3 sorries

## 背景

2026-06-16 (夜³): F は §16 / POLE-2 / Pf がすべて 2 long pole（H `typeP_duality`,
B `(6.8)`）に gated で STANDBY だった。hub の実コード再検証で両 trigger 未達を確認した一方、
**唯一の非衝突 ungated・FT-closure タスク = Wielandt (9.1)** が `CoprimeAction.lean` に
3 本の実 sorry として残存していると判明（141 のうち 3 本）。ユーザー裁可で F を reactivate。

- 依存的に ungated: 入力 = `IsFrobeniusGroup`（Isaacs Ch06 済）+ coprime/card のみ。
- 非衝突: 消費側は Pf §11（`S11_MaximalII_III_IV`）の docstring 参照のみ（term 未配線）。
- FT-path 必然: Pf §11 (9.2)-(9.9) の全 character count が (9.1) ベース。

## 進捗 (2026-06-17)

- [x] `CoprimeFrobeniusAction` faithful 再設計（実 action `φ:L→MulAut H`, fixedByUE/E/U
      = `fixedSubgroup`; 旧構造は作用無しで証明不能だった）— `c55f6db2`（main 合流済）
- [x] 系(i)(ii) を本体から証明（`wielandt_fixedPoint_trivial_E_fixed`/`_U_fixed`）
- [x] **3 sorry → 1**（残=本体 `wielandt_fixedPoint_frobenius`）
- [ ] 本体 `wielandt_fixedPoint_frobenius` = `|C_H(UE)|^|E|·|H| = |C_H(E)|^|E|·|C_H(U)|`

## 方針: NO axiom, ボトムアップ完全形式化 (ユーザー裁可 2026-06-17)

本体の **勘定核心 (†)** `Wᵁ=0 ⇒ dim W=|E|·dim Wᴱ` は「E が非自明 `𝔽_p[U]`-既約**加群**に
自由作用」＝ **modular Brauer permutation lemma (𝔽̄_p 上, p′-群)** を要する。repo の Brauer は
**ℂ-指標版のみ**で `𝔽_p`-加群へ橋渡し不可。⟹ **欠落インフラを新規構築（axiom 無し）**。

- **FT 接続確認済**: (9.1) → Pf `S11`→`S12`/`S13`→`S14`→`S15`→`S16` → S16.Hypothesis → `feitThompson`
- **レーン干渉なし**: F は `GroupTheory/CoprimeAction` + 新規 `GroupTheory/RepresentationTheory/*`
  のみ編集; lane-b/g/h はこれら・`RepresentationTheory/` を一切 commit せず（検証済）

### 新規インフラ sub-pieces（正本 = notes/peterfalvi/s11_wielandt_91_design.md）

- [x] coprime 分解 `V=V^G⊕[V,G]`（dim 形 + `[V,G]^G=0` + `IsCompl`）— `WielandtCounting.lean` `a1bddfaa`
- [x] **step 2: el-ab 恒等式 (⋆) COMPLETE (modulo (†))** — `finrank_elab_identity` `95757a9f`。toolkit: `Vᵁᴱ=Vᵁ⊓Vᴱ`(`80a4d926`) + compatible-decomposition(`fadb55d6`) + averageMap 明示形(`87816c20`) + `[V,U]` L-不変性 via `MulAut.conjNormal`(`6e2df864`)
- [x] **(I-3) regular-orbit fixed-space count COMPLETE** — `finrank_eq_card_mul_finrank_invariants` (`dim V = |G|·dim V^G`) + reverse-half `finrank_invariants_le_finrank_A1`, `b95fcc6b`（dimension/easy halves は `8c1f0f43`/`c140816c`）
- [ ] 系(i) を BG 3.3 + chief-series で **unconditional 化** — **2026-06-17: 部品調査完了**。keystone
      `Isaacs.Ch04.coprime_fixedPoints_quotient`（Cor 3.28, `φ:A→MulAut G` 形式）+ BG 3.3
      `S03b.kernel_acts_trivially_of_centralizer_eq_bot` + el-ab bridge
      `ElementaryAbelianRepresentation` + φ-descent `IsAInvariant.quotientMulAutHom`(Ch04 Main:2248)
      は**全て既存**。**stability helper COMPLETE**（新 leaf `CoprimeFrobeniusKernel.lean`
      `mulAut_iterate_apply`/`_pow_eq_one_of_exponent`/`_eq_one_of_exponent_of_coprime`, `c467872a`）。
      残 = induction assembly（el-ab φ(L)-不変 normal 存在 [derived 末項の p-torsion で characteristic]
      + 表現 setup + BG 3.3 適用 + keystone で `C_{H/N}(E)=1` + φ̄ 強帰納 `Nat.card H`）。
      ⚠ **cor (i) は side-quest**（I-5 keystone が既存判明ゆえ新規共有インフラ無し・sorry 数不変）。
- [ ] (I-2) isotypic 分解（mathlib `IsSemisimpleModule`+`Maschke`）
- [ ] (I-1) **Brauer permutation 補題 — ⚡ Teichmüller-free に再設計 (2026-06-17, user 裁可)**:
      `#(⟨e⟩-orbits on classes) = #(⟨e⟩-orbits on simples)` を `Z(𝔽̄_p[U])` の 2 基底（class-sum /
      冪等元 `Z≅𝔽̄_p^N`）+ `dim ker(σ_e−1)=#orbits`（任意体）で導出 → coprime-FPF free-on-classes +
      counting で free-on-simples。**Teichmüller integer-lift 不要**（旧「char-0 wall」を回避）。
      build order: (1) ✅ **cornerstone `finrank_invariants_eq_card_orbits` COMPLETE**
      (`PermutationInvariants.lean` `d4b0d4b5`, 任意体, orbit パラメトリゼーション `orbitToVec`,
      lint-clean) → (2) ✅ **COMPLETE** `Z(k[G])` class-sum 基底 + σ 置換
      (`CenterClassSumBasis.lean`: `centerBasis : Basis (ConjClasses G) k ↥center` `bbc3519c` +
      `domCongr_classSum` σ-置換 `c4f52a6c`, 任意体, sorry-free, axiom-clean)
      → (3) split-ss `Z≅𝔽̄_p^N` 冪等元基底
      （mathlib `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`）→ (4) cornerstone を 2 基底
      に適用し #orbits 一致 + Glauberman free-on-classes + counting。
      **(3) σ-置換の核心 ✅ COMPLETE** (`PiAlgebraAut.lean` `afa21d09`): `algEquiv_permutes_single` =
      「`(ι→k)` の代数自己同型は標準冪等元 `Pi.single i 1` を置換」(自己完結・upstream 可)。⚠ char p の
      罠（列和=1 では p+1 個も和=1）を **orthogonality（各座標高々1個）** で回避、support disjoint+cover
      の Finset 数え上げ。**(3) Wedderburn center transport ✅ COMPLETE** (`CenterSplitting.lean`
      `edba3d51`/`2688af89`/`0606a2f2`/`3584c746`): `exists_center_algEquiv_pi : ∃ N, Nonempty
      (Z(k[U]) ≃ₐ[k] (Fin N → k))` を 3 リンク (`AlgEquiv.centerCongr` Z(A)≅Z(B) / `centerPiEquiv`
      Z(∏C)≅∏Z(C) / `matrixCenterEquiv` Z(Mat n k)≅k) + Wedderburn で組立。**残 (3) = 冪等元基底 +
      cornerstone (simples 側)**。**step 3b 大半 ✅ (loop, `afa21d09`→`f1527db4`)**: 群作用整合の
      subtle 部分を `algAutPerm : Aut(∏k) →* Perm`（正準 MonoidHom）で解決（⟨e⟩ 限定でなく MulAut G 全体が
      genuine MulAction）+ `centerCongrHom : Aut k[G] →* Aut Z` + **`simplesAction φ : MulAut G →* Perm(Fin N)`**
      + cornerstone hρ `centerRep_apply_symm_single` 完成（`CenterSimplesOrbit.lean`）。
      **✅✅✅ steps 1-4 COMPLETE (2026-06-17 resume⁴, `f26fd70c`, sorry-free + axiom-clean)**:
      `idemBasis φ` (冪等元基底 = `Pi.basisFun.map φ.symm`, CenterCarrier 経由) + `centerRep'_apply_idemBasis`
      (simples 側 hρ) + `finrank_centerRep_invariants_eq_card_orbits_simples` (cornerstone 適用、
      任意の `[MulAction (MulAut G) (Fin N)]` + `hact = simplesAction φ` 一致仮説で `dim Z = #orbits-on-Fin-N`)
      + **`card_orbits_classes_eq_card_orbits_simples` = Brauer orbit 等式
      `#(orbits on ConjClasses) = #(orbits on Fin N)`** (両者 = `dim Z^{MulAut G}`、char-0/Teichmüller 不要)。
      詳細 = design notes「2026-06-17 (resume⁴)」。
      **(4) class-sum 側 ✅✅ FULLY COMPLETE** (`CenterOrbitCount.lean` `cab132a7`+`faeb1bc8`):
      `MulAction (MulAut G) (ConjClasses G)` (`ConjClasses.map`) + `centerRep : Representation k
      (MulAut G) ↥center` (`domCongr α` を中心へ制限) + compatibility `centerRep_apply_centerBasis`
      = cornerstone の `hρ` + **capstone `finrank_centerRep_invariants_eq_card_orbits`:
      `finrank ↥(invariants centerRep') = #(MulAut G-orbits on classes)`**。⚠ isDefEq/whnf 爆発
      (`↥(Subalgebra.center k …)` の Module instance diamond) は **carrier type synonym `CenterCarrier`
      + inferInstanceAs で正準化して解消** ([[lean-type-synonym-fixes-instance-diamond]])。
      ⚠ repo `ClassSumAlgebra.lean` は **ℂ 専用**だったので (2) は新規に k-一般化済。
      **残 = step 3d counting bridge**: (3d.1) ✅ **DONE (`78f8c86f`)** Brauer 等式を一般作用群へ一般化
      （`centerRepComp ψ`, `card_orbits_classes_eq_card_orbits_simples_comp`）→ (3d.2) ✅ **DONE
      (`dccd7dd3`)** coprime-FPF auto は自明 class のみ固定（`CenterOrbitFree.map_eq_self_imp_eq_trivial_of_fpf`,
      `glauberman_fixed_point_exists` を `Ω={y//mk y=C}` に適用、sorry-free・axiom-clean）→ (3d.3a) ✅
      **DONE (`9ec8db73`)** free-action orbit 算術 `FreeActionOrbitCount.orbit_trivial_or_free_of_card_orbits`
      （`#orbits=1+(n−1)/d ⟹ 各軌道 size 1 or d + 固定点≤1`; ∑(d−sᵢ)=d−1 & 真の約数≤d/2 で defect 1 個に
      強制、素数性不要、sorry-free・axiom-clean）→ **(3d.3) 残**: (3d.3b) trivial simple は MulAut-fixed
      （対称化冪等元 `(1/|U|)∑g` 経由）+ forward-count（classes 側 free+1fixed ⟹ #orbits=1+(Ncl−1)/|E|）
      + (3d.3c) 合流 ⟹ E free on 非自明 simples → (†) [I-2 isotypic + I-4 base change + per-orbit I-3]。
      正本 = design notes「2026-06-17 (resume⁴)」(詳細・約数論法込み)。
- [ ] (†) kernel-FPF count + (I-4) base change `𝔽_p→𝔽̄_p`
- [ ] (I-5) chief-series coprime — **keystone `coprime_fixedPoints_quotient` は既存**（Isaacs Cor 3.28）。
      残 = 乗法性 `|C_H(X)|=∏|C_{V_i}(X)|`（main formula 用、keystone + chief series から組立）
- [ ] assembly → `wielandt_fixedPoint_frobenius`

**見積 ~6-9 session**（I-1 が `p`-adic lifting まで要れば再 flag）。**真の critical path = I-1 wall**
（cor (i)/I-5-keystone は achievable/既存）。

## 完了条件

`CoprimeAction.lean` の本体 sorry が消え、`lake build OddOrder OddOrder.AxiomsCheck` green +
**新規 axiom 無し** + 実 sorry が（最終的に）3 本減（hub merge tick で検証）。

## 参照

- 正本: `references/peterfalvi/04.11_pp_50_57_On_the_Maximal_Subgroups_of_G_of_Types_II_III_and_IV.mmd` (9.1)
- 古典出典: Wielandt の定理 = [HB] Ch.XI Thm 12.4
- 解析メモ: `notes/peterfalvi/s11_maximal_II_III_IV.md:47`（§(9.1)）
- F の LAUNCH.md（2026-06-16 夜³ 指令）
