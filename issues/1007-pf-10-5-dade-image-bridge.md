---
id: 1007
slug: pf-10-5-dade-image-bridge
title: "Pf (10.5) Dade-image: §10 σ↔τ bridge + §6↔§5 ω reconcile linchpin"
created: 2026-06-21
---

# Pf (10.5) Dade-image: §10 σ↔τ bridge + §6↔§5 ω reconcile linchpin

## 背景

Peterfalvi (10.5) の Dade-image 半分 `α_ij^τ = δ(ω_ij^σ − ω_i0^σ) − n·ζ^{τ₁}`
(`S12_MaximalIII_IV_V.lean` の `alpha_tau_image`, sorry)。support 半分は完了
(`muGrid_alpha_support`, commit a52abf68)。Dade-image 半分の foundation を 2 件 landing 済
(`CoherentHypothesis` de-opaque + `Hypothesis.tau_apply_of_mem_typePV` cornerstone)。
正本設計 = [`notes/peterfalvi/s12_s10_character_bridge.md`](../notes/peterfalvi/s12_s10_character_bridge.md)
「更新⁴」。原文 = `references/peterfalvi/04.12_*.mmd` (10.5)。

`alpha_tau_image` は現状 statement では**証明不能** (arbitrary `params`/`coh`、`omegaSigma`/`mu` free)。
閉じるには下記 carrier 材料化 + 解析が必須 ([[scaffold-sorry-free-not-done]])。

## ⚠⚠⚠ 最重要 finding (2026-06-21 transport build 中に発覚) — grid index 不整合

**`muGrid` と `omegaSigmaGrid` は独立な index→ω map を使う ⟹ 同一 (i,j) で μ_ij と ω_ij^σ が無関係な
character になり、per-(i,j) の (10.5) identity `alpha_tau_image` は現 grid 定義では SEMANTICALLY FALSE**
(transport だけでは閉じない; これが真の core issue):
- `muGrid i j` (S12:750) = chiColumn 経由、W₁-dual = **`w1CharEquiv i`** (§6, S06:196)、W₂-dual =
  **`finCardEquivCharacterGroup j`** (§10, S12:721)。台 = ↥M。
- `omegaSigmaGrid i j` (S12:782) = §5 tic 経由、両 dual = **`charEquiv i`/`charEquiv j`** (§5, S05:54)。台 = G。
- `w1CharEquiv`/`finCardEquivCharacterGroup`/`charEquiv` は全て「Fin card ≃ duals, 0↦1」だが **独立な
  base equiv** ゆえ対応しない。producer (`exists_charParameters` S12:1659-1660) は両 grid を**独立に**
  `mu := muGrid` / `omegaSigma := omegaSigmaGrid` で詰める ⟹ misaligned。
- **(10.3) (degree/δ 独立性) は index-invariant ゆえ dormant だった**; (10.5) が初めて per-(i,j) 対応を要求し露見。

**∴ 正しい fix = `omegaSigma` を muGrid 自身の ω の §5 σ-image (↥M→G transport) として ALIGN 定義する**
(transport を畳み込み + 整合を構成的に保証)。cross-level transport は不可避だが、それを「与えられた 2 grid の
reconcile」でなく「omegaSigma を muGrid に揃えて定義」する形で使う。⚠ **cross-file 影響**: `omegaSigmaGrid` は
S15.Hypothesis.eta も pin (docstring) ⟹ omegaSigmaGrid 自体を再定義すると S15 に波及。低影響版 = producer 内で
`omegaSigma` だけ aligned grid に差し替え (omegaSigmaGrid は S15 用に温存、docstring の「同一」主張は要更新)。
**要ユーザー判断** (architectural, cross-file)。

## ✅✅ 進捗 (2026-06-21) — cross-level transport + reconciliation DONE

misalignment fix (producer-local) を実装し、**deep gate だった cross-level reconciliation を close**:
- ✅ `Hypothesis.alignedOmegaSigmaGrid` (`3b28cb54`): muGrid 自身の ω (`chiColumn`) を §6 `↥M` から §10 `G` へ
  `e : ↥tic.W ≃* ↥(h.W1⊔h.W2)` (`subgroupOfEquivOfLe.symm` ∘ `subgroupCongr`) で transport し σ_∫。
  infra: `typePData_W2_le_self`/`typePData_W_le_self`/`typePData_sup_subgroupOf_eq` + `ClassFunction.compHom`。
- ✅ `Hypothesis.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` (`dda1134c`): **V 上で
  `μ_ij(v) = δ_j · alignedOmegaSigma_ij(v)`**。M-side (4.3.c) + σ-side (`sigmaIntegral_apply_of_mem_V`+`compHom_apply`)
  + `e` が v を保つ (`he_coe`: `subgroupCongr_apply` rfl + `subgroupOfEquivOfLe.symm` 定義的) → 両 chiColumn 引数一致。
- ⟹ aligned design 検証完了。per-(i,j) (10.5) identity が provable に (raw omegaSigmaGrid では不可能だった)。

## ✅✅✅ 進捗 (2026-06-21 cont.) — value-on-V leg DONE (2 analytic leg のうち 1 本)

下記「残り 2」の **value-on-V leg を grid-level で完全形式化** (`0601b2bb`, build-green 3818 jobs)。
原文「By (3.2.c), (4.3.c) and the definition of τ, α_ij^τ − δ(ω_ij^σ − ω_i0^σ) vanishes on V」を honest 実装:

- ✅ `Hypothesis.tau_muGridAlpha_apply_eq_on_typePV` (leg 本体): **V 上で
  `hyp.tau (μ_ij − δ·μ_i0 − n·ζ) v = δ·(ω_ij^σ − ω_i0^σ)(v)`** (ω^σ = alignedOmegaSigmaGrid)。
  cornerstone `tau_apply_of_mem_typePV` (α は A₀ supported ∵ `muGrid_alpha_support` → τ が V で α 復元)
  + reconciliation `muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` (j と 0 の両方)
  + `muColumnSign_zero` (δ_0=1) + ζ-vanishing (induced from normal M', v∉M')。
- ✅ `typePData_typePV_not_mem_derived` (**完全 axiom-clean** `[propext,Classical.choice,Quot.sound]`):
  v∈V ⟹ v∉M'。↥W (abelian) で v=x·y 分解 (`Subgroup.mem_sup`) → W₂≤M' ∧ W₁⊓M'=⊥ (`M_complement`)
  ⟹ x=1 ⟹ v=y∈W₂ 矛盾。ζ-vanishing on V の構造的核心。
- ✅ `Hypothesis.muColumnSign_zero` (δ_0=1): column-0 dual = trivial (`finCardEquivCharacterGroup_zero`)
  + trivial column sign=1 (`certainType_zero_column_anchor.1`)。
- axiom footprint: leg/muColumnSign_zero = `[propext, sorryAx, Classical.choice, Quot.sound]`
  (sorryAx = §10 muGrid 系と同じ上流 bridge gate Prop16.1/theoremA、**自前 sorry 無**)。

**▶ 残り (full `alpha_tau_image` を閉じるための 2 gate)**:
1. **carrier pinning** (⚠ 要ユーザー判断・cross-file): producer `exists_charParameters` の
   `omegaSigma := hyp.omegaSigmaGrid` を `alignedOmegaSigmaGrid` に差し替え + `CharacterParameters` に
   identity field (`mu_def`/`omegaSigma_def`)。ただし `CharacterParameters` は `hG`/`hodd` を carry せず
   (S13 cascade 回避のため structure param 化は危険、note cont. 参照) ⟹ identity field でなく
   **`alpha_tau_image` を grid-level の `Hypothesis.tau_muGridAlpha_eq` 定理に再構成**し params 版を
   薄い corollary (`hmu`/`hos`/`hzeta` hypothesis で grid に紐付け) にするのが本筋。
2. **a=0 norm 論証** (deep, multi-session): `(α^τ, ζ^{τ₁})=a−n` 定義 → `(α^τ,(ζ−ζ̄)^τ)=−n` (τ isometry)
   → `(α^τ, μ_k^{τ₁})=da` (k≠j,0) → Cauchy-Schwarz `d²a² ≤ ‖α^τ‖²‖μ_k^{τ₁}‖²=(2+n²)w₁` → n<2 矛盾
   ((10.3) n even>0) → `α^τ = X − nζ^{τ₁}`, `‖X‖²=2`, X⊥ζ^{τ₁} → ζ^{τ₁} vanishes on V (5.3.b/5.5/3.2.d)
   → ψ=X−δ(ω^σ diff) vanishes on V (**= leg ✅ + 上記**) → NC(ψ)≤4<2inf(w₁,w₂) → (3.8) → ψ=0。
   要 §3 NC machinery (3.6/3.8) + §5 (5.3.b)/(5.5) + τ-inner-product isometry + μ-grid orthonormality。

## ✅✅✅✅ 進捗 (2026-06-21 cont.²) — a=0 の μ-side inner-product inventory 完成 (CRUX 含む)

a=0 norm 論証の **M-side inner products を全て形式化** (build-green 3818 jobs、全 axiom-clean = 上流 gate のみ)。
**最重要発見: μ⊥ζ (Explore が「200-500行 Clifford/Mackey」と見積もった crux) は Clifford 不要 — degree distinctness のみ**:

- ✅ **`muGrid_inner_eq_zero_of_apply_one_ne` (CRUX, `78d7c066`)**: `(μ_ij, χ)=0` for irreducible χ with
  `μ_ij(1) ≠ χ(1)`。**μ_ij も ζ も既約** ⟹ `irr_cf_inner` で inner = if eq then 1 else 0、degree mismatch で
  ≠。∴ `(μ_ij,ζ)=0`/`(μ_ij,ζ̄)=0` は degree (`μ_i0(1)=1≠w₁`, `μ_ij(1)=d≠w₁` ∵ n·w₁=d−δ/d>1/w₁>1) のみ。
  **当初の RES_K μ_ij Clifford 分析は不要だった** (∵ ζ 既約ゆえ直交は単なる distinctness)。
- ✅ `muGrid_inner_self` (`24bcfd02`): `(μ_ij,μ_ij)=1`。
- ✅ `muGrid_inner_cross_column` (`24bcfd02`): `(μ_ij,μ_i'j')=0` for j≠j' (cross-column, (4.1))。
- ✅ `muGrid_inner_within_column` (`36609290`): `(μ_ij,μ_i'j)=0` for i≠i' (within-column) → full grid orthonormality。
- ✅ `muGrid_column_sum_inner_self` (`36609290`): `‖∑_i μ_ik‖²=w₁` (Cauchy-Schwarz の `‖μ_k^{τ₁}‖²` factor)。
- ⚠ instance 罠 (記録): inner は `@inner ↥M _ (FiniteInduce.finiteSubFintype M) ...` で **Fintype を term-relevant
  instance に持つ**。muGrid unfold;rfl 系は explicit `[Fintype ↥M]` 不可 (choose が instance-dependent) →
  `classical`/`open scoped FiniteInduce` で finiteSubFintype を synthesize。sum 系は `open scoped FiniteInduce in`。

**✅ (i) `‖α_ij‖²=2+n²` assembly DONE** (`bda228a8`): `Hypothesis.muGridAlpha_inner_self` — grid-level
(pinning 回避)、degree mismatch を hypothesis 化 (`hdζ`/`h0ζ`)。{μ_ij,μ_i0,ζ} orthonormal + δ²=1。
sesquilinear `inner_sub/smul` 展開 + 逆順は `inner_conj_symm` + `rcases hδpm <;> ring`。一発 build。

**▶ 残り (a=0 の上で積む、grid-level で pinning 回避)**:
- (ii) **τ/τ₁ isometry transfer** (次の sub-area、§7 Dade machinery): `(α^τ,(ζ−ζ̄)^τ)=(α,ζ−ζ̄)`。
  鍵 = ζ−ζ̄ ∈ ℤ[S,A_0] (supported on A_0: ζ−ζ̄ は K=M' 上 support、K^#⊆A(M)⊆A_0、(ζ−ζ̄)(1)=0) +
  Dade isometry `(τα,τβ)=(α,β)` (`S07.dadeIntegralCharacterMap` isometry) + τ₁ extends τ on supported
  (`coherent.extends_on_supported` で (ζ−ζ̄)^τ=(ζ−ζ̄)^{τ₁})。
- (iii) `(α,ζ−ζ̄)=−n` / `(α,μ_k−dζ̄)=0` (M-side、μ-inventory ✅ で組める)。
- (iv) Cauchy-Schwarz `d²a²≤‖α^τ‖²·‖μ_k^{τ₁}‖²=(2+n²)w₁` (✅ ‖α‖²=2+n² + ✅ ‖μ_k‖²=w₁ + τ-isometry) + n<2 矛盾 + a=0。
- (v) ζ^{τ₁} vanishes on V (§5 5.3.b/5.5/3.2.d) → ψ=X−δ(ω^σ diff) vanishes on V (**= value-on-V leg ✅**)。
- (vi) NC(ψ)≤4 + (3.8) → ψ=0 → `alpha_tau_image`。
gate 1 (carrier pinning) は params 接続で必要だが grid-level statement で回避継続。

## ✅✅✅✅✅ 進捗 (2026-06-21 cont.³) — (ii) τ-isometry + (iii) M-side + (iv) τ-side leg 完成 (6 補題)

a=0 論証の **τ-isometry primitive + M-side inner products + τ-side transfer** を全形式化 (build-green
3818 jobs、全 axiom footprint = `[propext,(sorryAx),Classical.choice,Quot.sound]`、sorryAx は muGrid 系
上流 gate のみ・自前 sorry 0)。commit `de5b502d`/`dbd34818`/`c3506741`:

- ✅✅ **`Hypothesis.tau_inner_eq_of_supported`** (`de5b502d`, **完全 axiom-clean** = sorryAx 無):
  A₀-supported φ,ψ で `(hyp.tau φ, hyp.tau ψ) = (φ, ψ)`。§7 `dadeIntegralCharacterMap_inner_eq_on_supported_span`
  を `hyp.dadeData.dade`/`hyp.hconj` + 2 元集合 `{φ,ψ}` で instantiate。**再利用可能 primitive** (a=0 の
  全 `(α^τ,…)` で使う)。⚠ `open scoped FiniteInduce in` 必須 (hyp.tau と同じ `Fintype.ofFinite` instance;
  明示 `[Fintype G]` は defeq mismatch)。
- ✅ **`Hypothesis.muGridAlpha_tau_inner_self`** (`de5b502d`): `‖α_ij^τ‖² = 2+n²` (Cauchy-Schwarz 第1因子)。
  `muGridAlpha_inner_self` を primitive で transfer (α A₀-supported by `muGrid_alpha_support`)。
- ✅ **`Hypothesis.muGridAlpha_inner_zeta_sub_conj`** (`dbd34818`): M-side `(α_ij, ζ−ζ̄) = −n`。
  μ_ij/μ_i0 が ζ,ζ̄ (共 degree w₁) と次数相異 + `(ζ,ζ̄)=0` (ζ≠ζ̄=no-real, caller-supplied) + `(ζ,ζ)=1`。
  `ζ̄(1)=ζ(1)` は `exists_natDegree_charValue_one_dvd_card` (degree 実数)。
- ✅ **`Hypothesis.muGridAlpha_inner_muColumn_sub_conj`** (`dbd34818`): M-side `(α_ij, μ_k−dζ̄) = 0`
  (k≠j,k≠0, μ_k=∑_i' μ_{i'k})。cross-column 直交 (`muGrid_inner_cross_column`) + `(ζ,μ_{i'k})=0` (次数) で
  `(α,μ_k)=0`; `(α,ζ̄)=0` で `(α,dζ̄)=0`。
- ✅ **`Hypothesis.zeta_sub_conj_support`** (`c3506741`, **完全 axiom-clean**): `(ζ−ζ̄).support ⊆ A₀`。
  ζ,ζ̄ は normal M' 誘導ゆえ M' 外で消滅 + `(ζ−ζ̄)(1)=0` → M'^#、各 M'^# 元は自己中心化で A(M)⊆A₀
  (`muGrid_alpha_support` 左 disjunct パターン、(2.1) 共役不要で簡潔)。
- ✅ **`Hypothesis.muGridAlpha_tau_inner_zeta_sub_conj`** (`c3506741`): **`(α_ij^τ, (ζ−ζ̄)^τ) = −n`**。
  α と ζ−ζ̄ 共に A₀-supported → primitive で M-side 値 (=−n) に transfer。

**▶ 残り = τ₁-side (distinct deep sub-area、要 coherence object `coh` + Dade-coherence adjunction)**:
1. **τ/τ₁ 互換 on supported** (中): `hyp.tau (ζ−ζ̄) = coh.tau1 ζ − coh.tau1 ζ.conj`。
   要 `ζ−ζ̄ ∈ zSpan(S)` (← `ClosedUnderConjugate(inducedFamily)`、未確立; ζ̄=ζ.conj∈S は induce-conj-commute で
   要証明) + `coh.coherent.extends_on_supported` (ζ−ζ̄ A₀-supported by `zeta_sub_conj_support` ✅) + 線形性。
   ⟹ `(α^τ, ζ̄^{τ₁}) = a` (a := `(α^{τ₁},ζ^{τ₁})+n` 定義 + 上の `(α^τ,(ζ−ζ̄)^τ)=−n` ✅ + 線形)。
2. **🔑 Dade-coherence adjunction (最難・crux)**: `(α^τ, β^{τ₁}) = (α, β)` for **α A₀-supported, β ∈ ℤ[S]**
   (β=μ_k−dζ̄ は A₀-supported でない=μ_k 全指標ゆえ `extends_on_supported` 不可)。原文 line 29 の
   `(α,μ_k−dζ̄)=(α^τ,μ_k^{τ₁}−dζ̄^{τ₁})` の核心。§4 `adjoint_formula` (2.7) を χ=β^{τ₁} で使うには
   `adjointAverageFun(β^{τ₁})=β` on A₀ が要 = coherence extension の Dade-averaging 互換性 (非自明・未形式化)。
   ⚠ **domain 機微**: 原文 `α^{τ₁}` は α∉ℤ[S] ゆえ厳密には α^τ (supported 拡張) を指す; τ₁ の domain と
   α/μ_ij の lattice 帰属を精密化要。**この adjunction が τ₁-side 全体の gate**。
3. (iv) 続き: adjunction で `(α^τ, μ_k^{τ₁})=da` → Cauchy-Schwarz (✅ ‖α^τ‖²=2+n² + 要 ‖μ_k^{τ₁}‖²=w₁
   [`muGrid_column_sum_inner_self` ✅ を τ₁ で transfer]) → n<2 矛盾 → a=0。
4. (v) ζ^{τ₁} vanishes on V (§5) → ψ vanishes on V (value-on-V leg ✅)。(vi) NC≤4+(3.8)→ψ=0。

**次セッション着手先 = 上記 1 (τ/τ₁ 互換) + ClosedUnderConjugate(inducedFamily)** が tractable warm-up、
本丸は 2 (adjunction)。adjunction が解ければ μ_k step → Cauchy-Schwarz → a=0 が一気に通る。

## ✅✅✅✅✅✅ 進捗 (2026-06-21 cont.⁴) — 🔑 adjunction 不要が判明 + τ₁-side 基盤 5 補題

**🔑 最重要発見: 一般 Dade-coherence adjunction は完全に不要**。cont.³ で「μ_k step の crux = adjunction」と
診断したが**誤り**: 原文 line 29 の `μ_k − dζ̄` は **combination が A₀-supported** (μ_k は M' から誘導され消滅、
ζ̄ も M' 誘導、degree が dw₁ で相殺 → (μ_k−dζ̄)(1)=0)。∴ ζ−ζ̄ と全く同様に既存 `tau_inner_eq_of_supported`
primitive で transfer でき、adjunction は要らない。これで τ₁-side が大幅に de-risk。commit `af1eb2b5`/`cf45120c`/`32f87323`:

- ✅ **`inducedFamily_closedUnderConjugate`** (`af1eb2b5`, **完全 axiom-clean**): S=inducedFamily が共役閉
  (`(Ind θ).conj=Ind θ̄` via `ClassFunction.induce_conj`、θ̄≠1 は inline `conj_conj`+`trivialClassFunction_isReal`;
  S08 `irreducibleCharacter_conj_ne_trivial` は S12 import 外)。⟹ ζ̄∈ℤ[S]。
- ✅ **`muGrid_column_sum_vanishes_off_derived`** (`cf45120c`): `∑_i μ_{ik}` が M' 外で消滅。列和=誘導指標
  `Ind_{M'}^M(Res_{M'} μ_{0k})` (§6 `induce_restrict_certainType_eq`、§10→§6 host 再構成 + `finCongr` reindex)
  → normal M' 外で `induce_eq_zero_of_not_mem_normal`。**μ_k=∑μ_ik が誘導**という構造事実が adjunction 回避の鍵。
- ✅ **`muColumn_sub_conj_support`** (`cf45120c`): `(μ_k−dζ̄).support ⊆ A₀`。`zeta_sub_conj_support` の companion
  (μ_k vanishing + degree 相殺 + M'^#→A(M))。⚠ クラス関数有限和の点評価は `Finset.induction` helper (直接 sum_apply 無)。
- ✅ **`muGridAlpha_tau_inner_muColumn_sub_conj`** (`cf45120c`): **`(α_ij^τ, (μ_k−dζ̄)^τ) = 0`**
  (primitive + M-side E)。μ_k,ζ̄∈ℤ[S] ゆえ `(μ_k−dζ̄)^τ=μ_k^{τ₁}−dζ̄^{τ₁}` → `(α^τ,μ_k^{τ₁})=da` step。
- ✅ **`tau_zeta_sub_conj_eq_tau1`** (`32f87323`, **完全 axiom-clean**): `hyp.tau(ζ−ζ̄)=coh.tau1 ζ−coh.tau1 ζ.conj`。
  `coh.coherent.extends_on_supported` (ζ−ζ̄∈zSupportedSpan) + `map_sub`。**CoherentHypothesis explicit-Fintype
  regime と hyp.tau の FiniteInduce regime は extends_on_supported が hyp.tau を直接参照ゆえ衝突せず**。

**▶ 残り (a=0 完遂への明確な arc、adjunction 不要が確定したので全て primitive ベース)**:
1. **μ_k τ/τ₁ 互換** `hyp.tau((∑μ)−dζ̄)=coh.tau1(∑μ)−d•coh.tau1 ζ.conj` (`tau_zeta_sub_conj_eq_tau1` の類比)。
   要 `∑_i μ_ik ∈ ℤ[S]` (= μ_k∈inducedFamily、列和=`induce(θ)` θ既約非自明; §6 `exists_irreducible_restrict_certainType`)。
2. **a-derivation**: `a := (α^τ,coh.tau1 ζ)+n` 定義 → `(α^τ,ζ̄^{τ₁})=a` (τ/τ₁ ζ−ζ̄ ✅ + def) →
   `(α^τ,μ_k^{τ₁})=da` (μ_k τ/τ₁ + 上記)。
3. **Cauchy-Schwarz + a=0**: `(da)²≤‖α^τ‖²·‖μ_k^{τ₁}‖²=(2+n²)·w₁` (✅ `muGridAlpha_tau_inner_self` +
   要 `‖μ_k^{τ₁}‖²=w₁` = coherence isometry で `muGrid_column_sum_inner_self` ✅ を transfer) + a∈ℤ (α^τ,μ_k^{τ₁}∈ZIrr) +
   a≠0→|a|≥1→`d²≤(2+n²)w₁`→n<2 矛盾 ((10.3) n even>0)。
4. **(v)(vi)**: a=0 → `α^τ=X−nζ^{τ₁}`, X⊥ζ^{τ₁}, ‖X‖²=2 → ζ^{τ₁} vanishes on V (§5 5.3.b/5.5/3.2.d) →
   ψ=X−δ(ω^σ diff) vanishes on V (value-on-V leg ✅) → NC(ψ)≤4 + (3.8) → ψ=0 → `alpha_tau_image`。
全 piece は `coh`+ζ irreducibility 経由、新 adjunction 数学なし。Cauchy-Schwarz が次の山。

## ✅✅✅✅✅✅✅ 進捗 (2026-06-21 cont.⁵) — τ₁-side inner-product 計算 完成 (5 補題)、残 = Cauchy-Schwarz+数論

a=0 論証の **τ₁-side inner-product 計算を完全に積み上げ**、Cauchy-Schwarz の全入力を materialize。
commit `e6eb42b6`/`15bcd901`/`364b3690`/`d5014be8`:

- ✅ **`muGrid_column_sum_mem_inducedFamily`** (`e6eb42b6`): `∑_i μ_{ik} ∈ S` (k で μ_{0k}(1)≠1)。列和=
  `Ind_{M'}^M θ` (θ既約 via §6 `exists_irreducible_restrict_certainType`)、θ≠1 from θ(1)=μ_{0k}(1)≠1。
  ⟹ μ_k∈ℤ[S] (τ₁ の定義域)。⚠ host 再構成 + finCongr reindex + θ(1)=μ_0(1) (restrict_apply, forward-rw)。
- ✅ **`tau_muColumn_sub_conj_eq_tau1`** (`15bcd901`): `(μ_k−dζ̄)^τ=μ_k^{τ₁}−dζ̄^{τ₁}`。tau_zeta 版の類比、
  μ_k∈S + ζ̄∈S。⚠ `(d:ℂ)•` (ℂ-smul) を `Nat.cast_smul_eq_nsmul`+`map_nsmul` で ℤ-linear τ₁ に通す。
- ✅✅ **`muGridAlpha_tau1_inner_muColumn`** (`364b3690`): **`(α_ij^τ, μ_k^{τ₁}) = d·((α_ij^τ,ζ^{τ₁})+n)` = da**
  (a:=(α^τ,ζ^{τ₁})+n)。両 τ/τ₁ bridge + 純-τ identity (=−n,=0) を `inner_sub/smul_right`+`linear_combination`。
  ⚠⚠ **instance regime 衝突 (FiniteInduce vs explicit Fintype) が inner で顕在** → この lemma を `[Finite G]`+
  FiniteInduce 一本に統一 (CoherentHypothesis の explicit binder も FiniteInduce が供給) で解消。**以後 coh を
  使う inner 計算 lemma は全て FiniteInduce regime で書くこと** (explicit Fintype を混ぜると `inner` の Invertible が
  defeq mismatch)。
- ✅ **`muColumn_tau1_inner_self`** (`d5014be8`): `‖μ_k^{τ₁}‖²=w₁` (`coherent.extension_inner_eq` +
  `muGrid_column_sum_inner_self`)。⚠ `coh.tau1=extension` は `show` で defeq 変換してから rw。

**⟹ Cauchy-Schwarz `(da)² ≤ ‖α^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)·w₁` の全因子が揃った**:
✅ `(α^τ,μ_k^{τ₁})=da` + ✅ `‖α^τ‖²=2+n²` (`muGridAlpha_tau_inner_self`) + ✅ `‖μ_k^{τ₁}‖²=w₁`。

**▶ 残り (final assembly = a=0 の山 + (v)(vi))**:
1. **a∈ℤ**: `(α^τ,ζ^{τ₁})∈ℤ` ← `inner_mem_ZIrr_int` (InducedCharacter:716、利用可) + α^τ,ζ^{τ₁}∈ZIrr(G)
   (Dade `dadeIntegralCharacterMap_mem_ZIrr_of_supported` + coherence `extension_mem_ZIrr`)。
2. **Cauchy-Schwarz**: `(da)²≤(2+n²)·w₁`。⚠ ClassFunction.inner の**一般** Cauchy-Schwarz が必要 (既存は
   coefficient-vector `ZIrrFourier:306` / norm-1 `S08_CaseBCoherence2:613` の特殊形のみ; α^τ,μ_k^{τ₁} を Irr(G)
   正規直交基底で展開して coefficient 版に帰着、or 一般形を新規証明)。
3. **数論**: d=nw₁+δ (hnf), δ=±1, w₁>1, n even>0。a≠0→|a|≥1→`d²≤(2+n²)w₁`→`(nw₁+δ)²≤(2+n²)w₁`→n<2 矛盾→a=0。
4. **(v)(vi)**: a=0→`α^τ=X−nζ^{τ₁}`,X⊥ζ^{τ₁},‖X‖²=2→ζ^{τ₁} vanish on V (§5)→ψ vanish on V (leg ✅)→
   NC(ψ)≤4+(3.8)→ψ=0→`alpha_tau_image`。
次の山 = (2) 一般 Cauchy-Schwarz (or 基底展開) + (3) 数論。(1) は cite で軽い。

## 🎉🎉🎉 進捗 (2026-06-21 cont.⁶) — **a=0 PROVEN** (Cauchy-Schwarz 解析的核心 完成)

**(10.5) の解析的核心 `a=0` を完全形式化** = `(α_ij^τ, ζ^{τ₁}) = −n`。Cauchy-Schwarz 議論の全 step
を組み上げた。commit `cb6111df`/`39f85329`/`553b004e`:

- ✅ **`classFunction_inner_re_sq_le`** (`cb6111df`, private, 一般 H): `⟨φ,ψ⟩.re² ≤ ⟨φ,φ⟩.re·⟨ψ,ψ⟩.re`。
  **判別式法** — `‖φ−tψ‖²≥0 ∀t` (`inner_self_re_nonneg`) → `discrim_le_zero`。**Parseval/基底展開 不要**
  (cont.⁵ の「基底展開 or 新規証明」見積もりより遥かに簡潔)。⚠ `.re` 展開は `pow_two`+`Complex.mul_im`+
  `Complex.star_def` で `(↑t)²` の im と `(star z).re` を処理。
- ✅ **`muGrid_isIrreducible`** + **`muGridAlpha_tau_mem_ZIrr`** (`39f85329`): μ_ij 既約 (host emj) → α∈ℤ[Irr M]
  (sub/zsmul/nsmul_mem + `Int/Nat.cast_smul_eq_zsmul/nsmul`) → α^τ∈ℤ[Irr G] (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`)。
- ✅ **`cauchySchwarz_numeric`** (`553b004e`, private, 純算術): `(d·a)²≤(2+n²)w₁`, d=nw₁+δ, δ=±1, **w₁≥3 (奇数)**,
  **n≥2 (偶数)** → a=0。a≠0→a²≥1→d²≤(2+n²)w₁ だが `(nw₁+δ)²>(2+n²)w₁` (nlinarith)。原文「n<2 矛盾」を
  忠実実装。**鍵 = w₁ は奇数 >1 ゆえ ≥3** (これが無いと w₁=2 で bound 違反せず)。
- ✅✅✅ **`muGridAlpha_tau1_zeta_eq_neg_n`** (`553b004e`): **`(α_ij^τ, ζ^{τ₁}) = −n` (a=0)**。
  m=(α^τ,ζ^τ₁)∈ℤ (`ClassFunction.inner_mem_ZIrr_int`) + da identity + C-S helper + 3 inner 値 (da, 2+n², w₁) +
  cauchySchwarz_numeric。`.re` 計算 + `convert`/`push_cast` で numeric に橋渡し。

**✅ X-decomposition DONE** (`541122df`): `Hypothesis.zeta_tau1_inner_self` (‖ζ^τ₁‖²=1) +
`muGridAlpha_tau_X_inner` (X:=α^τ+nζ^τ₁ で **‖X‖²=2 ∧ X⊥ζ^τ₁**)。a=0 + ‖α^τ‖²=2+n² + ‖ζ^τ₁‖²=1 の
sesquilinear 展開。⟹ `α^τ = X − nζ^τ₁` (X virtual char, ‖X‖²=2, X⊥ζ^τ₁) 確立。

**▶ 残り = (10.5) Dade-image を閉じる最終 (v)(vi) のみ** (別 large sub-area、§5/§3 wiring + pinning):
1. **ζ^{τ₁} vanishes on V** (§5 (5.3.b)/(5.5)/(3.2.d))。coh.tau1 ζ が V で消える — §5 coherence/σ 機構の §10 wiring。
2. **ψ vanishes on V**: ψ:=X−δ(ω^σ diff)。on V: ψ = (α^τ−δ(ω^σ diff)) + nζ^τ₁ = 0 + n·0 = 0
   (value-on-V leg `tau_muGridAlpha_apply_eq_on_typePV` ✅ で α^τ=δ(ω^σ diff) on V、+ 上記 1)。**= 1 が gate**。
3. **NC(ψ)≤4 + (3.8)**: `sigmaCoeff_trichotomy` (S05_SigmaTrichotomy:41) は `TICyclicHypothesis G`
   (`typePData_toTICyclicHypothesis` ✅) + **`FullDadeApplication` (要構成)** + ψ vanish on V + gap `w₁+2≤w₂` +
   `sigmaNC ψ < 2w₁` を取り σ-coeff trichotomy を返す。ψ の σ-coeff 計算 + NC≤4 (w₁≥3 で 2w₁≥6>4) →
   trichotomy → ψ⊥ω^σ → ψ=0 → X=δ(ω^σ diff) → `α^τ=δ(ω^σ diff)−nζ^τ₁`。
4. **pinning**: grid-level (10.5) → `alpha_tau_image` (params.alpha/omegaSigma/zeta を grid に pin)。
**要 §5 (5.3.b)/(5.5) ζ^τ₁-vanish + FullDadeApplication 構成 + (3.8) σ-coeff wiring** — 新 large sub-area
(別セッション規模)。**a=0 + X-decomposition で (10.5) の解析の山は完全に越えた**; 残りは構造論的 endgame。

## やること (旧)

- [ ] **carrier pinning**: `CharacterParameters.omegaSigma`/`mu` を `Hypothesis.omegaSigmaGrid`/`muGrid`
      に identity field (`omegaSigma_def`/`mu_def`) で pin。producer `exists_charParameters` は既に
      `:= …Grid` ゆえ `rfl` discharge。S13 projection 非破壊の additive 変更 (要 build 確認)。
- [ ] **§10 σ↔τ bridge on V** (本体): `α_ij^τ − δ(ω_ij^σ − ω_i0^σ)` が V=typePV で消える。
  - (a) M-side `muGrid(v) = δ·ω_ij(v)` on V ← (4.3.c) `certainType_apply_eq_of_mem_V`
        (`S06_CertainTypeCharacters:878`、§6 `Hypothesis L`、V=W∖W₂⊇typePV)。
  - (b) σ-side `omegaSigmaGrid(v) = ω_ij(v)` on V ← (3.2.c) `sigma_apply_of_mem_V` (`S05_SigmaIsometry:1203`)。
  - (c) τ-side ← `Hypothesis.tau_apply_of_mem_typePV` (✅ landed, axiom-clean)。
  - **⚠ linchpin (2026-06-21 精査で characterize)**: §6 `chiColumn` ω (4.3.c の RHS) ↔ §5 `omegaGrid` ω
    (omegaSigmaGrid の素材) を reconcile。**両者とも `omega ∘ omegaProdChar` で構成同型だが別 level の
    `TICyclicHypothesis` 上**:
      - §6 = `((hyp.toCertainTypeHypothesis).toHypothesis).sdiffTICyclicHypothesis` = **`TICyclicHypothesis ↥M`**
        (W1/W2 = `subgroupOf M`)、`chiColumn χ₂ i = sdiff.omega (sdiff.omegaProdChar (w1CharEquiv i) χ₂)`
        (`S06_CertainTypeCharacters:222`)。
      - §5 = `typePData_toTICyclicHypothesis hyp.typeP hodd` = **`TICyclicHypothesis G`** (W1/W2 = G の subgroup)、
        `omegaGrid i j = omega (omegaProdChar (charEquiv W1_le_W i) (charEquiv W2_le_W j))` (`S05_OmegaGrid:65`)。
    ⟹ reconcile = **↥M-level ω ↔ G-level ω の cross-level value-transport** (W ≤ M ≤ G, `subtype`/`subgroupOf`)。
    precedent: §5 `mapOfInjective` (`S05_TICyclic:97`) + §6 内部 `omegaProdCharTic`
    (`S06_CertainTypeIsometry:122-142`, ↥L-side chiColumn を G-side に転送し bridge 点で値一致; §6 は自前 ticVdiff
    (W∖W₂) で実装済)。これが **deep gate の核心** (multi-step cross-level transport)。
  - **σ-side note**: `sigmaIntegral_apply_of_mem_V` (3.2.c) の clean 適用だが、`omegaSigmaGrid` の def が
    tactic-mode + 内部 `haveI : NeZero (Nat.card tic.W1)` ゆえ **standalone lemma 化は instance synth が awkward**
    (RHS の `tic.omegaGrid` が NeZero 要求; 2026-06-21 試行→revert)。**→ bridge 本体内で inline 証明**が clean。
  - **(3.8) trichotomy は §5 level** (`sigmaCoeff_trichotomy`/`sigmaNC`) ⟹ omegaSigma の正しい target は §5
    `omegaSigmaGrid` (現状 def) で正解 (§6 `certainTypeOmegaSigma` でなく)。
  - **⚠ 別 obstruction = Dade support gap**: §6 (4.8) `certainType_diff_dade_eq` の `h.tau` は **W∖W₂-based**
    (ticVdiff)、§10 `hyp.tau` は **typePV-based** (typePA0)。W₁# 扱いが違い直 cite 不可 ((10.5) は −nζ で W₁# を消し
    typePV に落とす)。∴ §10 は §6 (4.8) を template に parallel re-derive (部品 4.3.c/3.2.c/3.8/NC 共有)。
  - **▶ build entry-point (2026-06-21 atomize)**: reconcile は **value-level の character transport を一から build**
    する。`omega`/`omegaProdChar`/`charEquiv` は **W のみ依存** (V/Dade 非依存) ゆえ:
    - atom (1) `omega_apply` (`S05_TICyclic:330`): `omega χ w = χ w`。
    - atom (2) `omegaProdChar χ₁ χ₂ (w) = χ₁ (wFst w) · χ₂ (wSnd w)` (`wFst`/`wSnd` = W₁/W₂ 成分射影,
      `S05_TICyclic:488-501`)。
    - ⟹ `chiColumn_6@↥M(v)` と `omegaGrid_5@G(v)` を両方 dual 値に分解し、`wFst`/`wSnd` の M.subtype 転送 +
      **index 対応** (§6 χ₂ = `finCardEquivCharacterGroup j` ⟦muGrid def⟧ vs §5 `charEquiv W2_le_W j`) を示す。
    - ⚠ `mapOfInjective` (`S05_TICyclic:97`, ↥L→G 転送、docstring が「§6 toTICyclicHypothesis を G に lift」と明記)
      は **定義済だが全くの未使用** (omega/charEquiv transport lemma ゼロ)。∴ transport API は新規 build。
      §5 tic は mapOfInjective 経由でなく G に直接構成ゆえ、tic = `mapOfInjective sdiff M.subtype` の証明も要
      (W は一致するが V が異なる ⟹ 構造 eq でなく omega-grid value 一致を狙う)。
    - 他の bridge 部品: ζ-vanishing on V = `induce_eq_zero_of_not_mem_normal` (ζ∈inducedFamily, v∈V⟹v∉M' ∵
      W₁-成分非自明 + W₁∩M'=1; `muGrid_alpha_support` 内に pattern 既在)。M-side = (4.3.c)。σ-side = inline。
- [ ] **norm/numeric `a=0`**: τ isometry (`IsCoherent.inner_eq_on_supported` / `extension_inner_eq`) +
      τ₁ 拡張で `(α_ij^τ, ζ^τ₁) = −n`、Cauchy-Schwarz + 不等式 + (n even,>0 ⟹ n≥2 で n<2 と矛盾)。
      要 μ-grid orthonormality (genuine μ 構造)。
- [ ] **(3.8) trichotomy 配線**: 機構は §5 W-level に既在 (`sigmaCoeff_trichotomy` `S05_SigmaTrichotomy:41`,
      `grid_no_constant_column`/`sigmaNC`)。§10 carrier の σ-coefficient grid に接続。
- [ ] `alpha_tau_image` を close (build-green + axiom 確認)。可能なら (10.6) `tau1_values_and_norm_bound` も。

## 完了条件

`alpha_tau_image` (S12) が sorry-free。axiom footprint は §10 muGrid 系と同じ上流 gate のみ
(自前 sorry 無)。full build + AxiomsCheck green。

## 参照

- 正本設計: `notes/peterfalvi/s12_s10_character_bridge.md` 「更新⁴」「更新³」「6. (10.2)–(10.5) 原文照合」
- §6 (4.8) template (support 違いで直 cite 不可だが部品共有): `S06_CertainTypeIsometry.lean`
  `certainType_diff_dade_eq` (`:794`)・`certainType_diff_dade_apply_eq_of_mem_V` (`:372`)・
  `sigmaNC_dade_le_two` (`:442`)。
- landed foundation: `CoherentHypothesis` (S12, IsCoherent extension)・`Hypothesis.tau_apply_of_mem_typePV`。
- 上位: [[ft-endgame-two-poles]] [[peterfalvi-s10-13-gated-on-bg-spine]]、issue 1004 (section16CharacterData は §10-13 待ち)。

## ✅ 進捗 (2026-06-22, lane-b) — (vi) precursor「ψ vanishes on V」landed + endgame 精密スコープ

(10.5) 原典証明 (04.12:43) を精読し endgame を完全 map:
`a=0 ✅` → `α^τ = X − nζ^τ₁ (‖X‖²=2, X⊥ζ^τ₁) ✅` (`muGridAlpha_tau_X_inner`) →
**ζ^τ₁ vanishes on V** ((5.3.b)/(5.5)/(3.2.d)) → α^τ − δ(ω^σ diff) vanishes on V (**= value-on-V leg ✅**)
→ **ψ = X − δ(ω^σ diff) vanishes on V** → NC(ψ)≤4 + (3.8) → ψ⊥ω^σ → ψ=0 → `alpha_tau_image`。

- ✅ **`Hypothesis.muGridPsi_vanishes_on_typePV`** (`0b587456`, sorry-free, build-green 3843):
  ψ = α^τ + n·ζ^τ₁ − δ(ω^σ diff) が V で消える。value-on-V leg + ζ^τ₁-vanish (named hypothesis
  `hζvanish`) の assembly。gate 1/2 と同じ honest-reduction パターン (proven piece を組み、genuine
  upstream fact = ζ^τ₁-vanish を named input に隔離)。`ClassFunction.{sub,add,smul}_apply` + leg + `simp`。

**▶ `alpha_tau_image` を閉じる残り = 3 piece** (いずれも別 sub-task):
1. **ζ^τ₁ vanishes on V** (§5/§7、真の bottleneck): 原典「By (5.3.b), (5.5) and (3.2.d), ζ^τ₁ vanishes
   on V」。coh.tau1 ζ (§7 coherence extension) を §5 V-構造に wiring。§5 lemma = `vanishOnV_of_inner_alphaCF`
   (S05_SigmaIsometry:1144) / `sigma_apply_of_mem_V` (:1203)。multi-lemma §5/§3 chain。
2. **(3.8) trichotomy** = `S05.sigmaCoeff_trichotomy` (S05_SigmaTrichotomy:41): 要 `FullDadeApplication
   (G:=G) tic` (tic = `typePData_toTICyclicHypothesis`) **の構成** (issue「要構成」、§4/§5 V-supported Dade
   isometry; hyp.dadeData は A_0(M)-support ゆえ別物) + ψ vanish on V (✅) + gap `w₁+2≤w₂` + `sigmaNC ψ < 2w₁`
   (NC≤4 計算)。trichotomy → ψ⊥ω^σ → ψ=0。
3. **carrier pinning**: grid-level (ψ-vanish 等) → params.alpha/omegaSigma/zeta version。`alpha_tau_image`
   は params-level。grid-level `Hypothesis.tau_muGridPsi_eq` 定理 + 薄い params corollary が本筋 (issue 旧記載)。

最難 = (2) FullDadeApplication 構成 (横断: (10.6)/(10.8) も σ-coeff machinery を要求)。
