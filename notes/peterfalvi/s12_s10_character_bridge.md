# Pf §10–§13 character bridge — Lane B 再開 roadmap (gate #3 proper)

> 2026-06-20 Lane B 再開時の現地調査結果 (正本)。ユーザーが「§11-13 spine 着手」を選択
> ((6.8) capstone 締結後)。本 note = §11-13 character theory を honest に閉じるための設計・API 在庫・攻略順。
> 上位文脈 = 記憶 [[ft-endgame-two-poles]] [[peterfalvi-s10-13-gated-on-bg-spine]]、
> Lane H 視点の正本 = [`s10_13_maximal_structure.md`](s10_13_maximal_structure.md)。

## ✅✅ 2026-06-22 更新⁹ — (5.8) endgame 仮説 2/4 着地 + §5-gate 回避経路を確立 (issue 1009)

lane-b 再開セッション。(10.6.a) を **§5-gated `ζ̄^τ₁⊥Imσ` を通さず**閉じる column-(5.5) 経路を確定し、
(5.8) σ-endgame (`eq_smul_chiFam_column_of_vanishOnV`) の 4 仮説のうち 2 つを materialize:

- **🔑 設計上の決定的発見**: `OrthonormalCharacterImageFamily` (S07_Coherence:766) は **2 元限定でなく汎用**
  (`imageSet : Finset (CF G ℂ)` + `image_eq : τ(χ−χ̄) = ∑_{α∈R} α` のみ要求)。∴ column μ_k に直接適用でき、
  R(μ_k) = signed σ-image 族 `{δ·ω_ik^σ}∪{−δ·ω_ik'^σ}` (2w₁ 元) で `CharacterPsiDecomposition` を組めば
  (5.5) `eq_sum_of_psi_eq_zero` が μ_k^τ₁ = ∑_{E⊆R(μ_k)} α を直接出す。= note 旧「column-(5.5) を別途立てる」
  (route ii) の具体化。**更新⁸ の `CharacterDifferenceImage` 一般化は不要** (汎用 `OrthonormalCharacterImageFamily`
  を使えばよい)。
- **column-difference DONE** (`tau_muGrid_column_diff` + `tau_muGrid_columnSum_diff`, commit `bd4c8340`):
  `τ(μ_ij−μ_ik) = δ(ω_ij^σ−ω_ik^σ)` (+ summed)。`alpha_tau_image` の系 (α の `−δμ_i0−nζ` tail 相殺)。
  = column image family の `image_eq` 材料 (= (4.9) summed Dade identity の §10 版)。
- **μ_k^τ₁ vanishes on V DONE** (`Hypothesis.muColumn_tau1_vanishes_on_typePV`, commit `02ec7e03`):
  (5.8) 原文の χ=ζ̄ ルート。(4.7) `muColumn_sub_conj_support` (μ_k−dζ̄ が A_0-supported) +
  `tau_apply_of_mem_typePV` (τ が V で値復元) + 誘導指標 V-vanishing + `tau_muColumn_sub_conj_eq_tau1` +
  完成済 `tau1_zeta_vanishes_on_typePV`(ζ̄)。両 commit axiom-clean (§10 muGrid 系と同じ upstream
  Prop16.1/theoremA gate のみ、自前 sorry 0)。
- **🔑 §5-gate 回避が確定**: `tau1_zeta_vanishes_on_typePV` が honest 完成 (norm-1 の NC≤2 トリックで §5 (3.8)
  経由、sorry-free) ゆえ、column 経路は更新⁸ が懸念した §5-gated `ζ̄^τ₁⊥Imσ` を**通らない**。直接 (10.6.a)
  reduction (`(δ(ω_ij^σ−ω_i0^σ), μ_j^τ₁))=1` 経由) は ζ̄^τ₁⊥Imσ を要したが、(5.5)-for-column 経路は
  μ_k^τ₁ を直接分解し、その V-vanishing は単一指標 ζ̄^τ₁-vanishing + (4.7) のみで出る。
- **残 = (5.8) 仮説 4/4 のうち最後 = sigmaCoeff 2-column structure**: column `OrthonormalCharacterImageFamily`
  本体構築 (要 **conjugate-column** `conj(μ_k)=μ_{k'}` の §10 同定 + 2w₁ 個の signed σ-image の orthonormality)
  → `CharacterPsiDecomposition.ofProjection` (ψ=0, tau1=coh.tau1; htau1_inner_eq=`coherent.extension_inner_eq`,
  htau1_agrees=column-difference, htau1_mem=μ_k^τ₁∈ZIrr) → (5.5) → μ_k^τ₁=∑_E α → sigmaCoeff 翻訳
  (R(μ_k) の元 ↔ chiFam 元、`exists_alignedOmegaSigmaGrid_chiFam_family` 経由) → σ-endgame 適用。
  ‖μ_k^τ₁‖²=w₁ は既存 (`muColumn_tau1_inner_self`)。**次セッション = conjugate-column + image family**。

## ✅✅ 2026-06-22 更新⁸ — (5.8) σ-level full-column endgame 完成 (issue 1009) + (5.5) gate 精密 map

(10.6.a) summed isometry の linchpin = (5.8) σ-wrapper のうち **(a) Parseval + (d) sigmaCoeff↔core
配線を完成** (commit `bcec3f86`, `S05_SigmaTrichotomy.lean`, 両 axiom-clean, full build 3881 green):

- **`eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq`** (Fourier 復元): Parseval *等式*
  `⟨X,X⟩ = ∑ sigmaCoeff·conj(sigmaCoeff)` (= X が Im σ ⊥ 成分無し、β=0) ⟹ `X = ∑ sigmaCoeff • χ_pq`。
  chiFam 直交性のみ依存。`span(chiFam)` を定義せず Parseval-等式を仮説化 (norm-2 endgame は ‖·‖²=0 で
  coeff を消すが (5.8) は復元が必要)。⚠ char-group 積型に global Fintype 無 → 文の `∑ pq` が Fintype を
  metavar 化 → 両 W1/W2 char-group `[Fintype]` を **instance 引数**化 (codebase は局所 `Fintype.ofFinite`)。
- **`eq_smul_chiFam_column_of_vanishOnV`** ((5.8) σ-coeff full-column endgame): X が V で消え、sigmaCoeff
  2-column {jcol,kcol} support + {0,δ}/{0,−δ} entries + ‖X‖²=w₁ + Parseval 等式 ⟹
  `X = δ•∑_p χ_{(p,kcol)}` ∨ `X = −δ•∑_p χ_{(p,jcol)}`。abstract core `grid_eq_const_column_of_two_col`
  + Fourier 復元 を合成。= norm-w₁ 版 `eq_smul_chiFam_diff_of_vanishOnV`。

⟹ **(10.6.a) を (5.5) の出力に honest 還元完了**。残 linchpin = wrapper 仮説を実 `μ_k^τ₁` で establish。

### 残 gate = (5.5)-for-columns / §6↔§5(§10) reconcile (deep, multi-session) — 精密 map (2026-06-22 調査)

- **§6 `certainTypeExtension` (ν) が結論形を既に持つ**: `certainTypeExtension_columnSum` (S06_CertainTypeCoherence:112)
  = `ν(μ_j) = δ_j ∑_i ω_{ij}^σ`。∴ (10.6.a) の真の中身 = **`coh.tau1` が certain-type column 上で ν に一致**
  することを (5.8) で**強制**する (ν と tau1 は定義上は別、(5.8) が一致を出す)。
- **(5.5) 機構は在庫だが単一既約用**: `eq_sum_of_psi_eq_zero` (S07_Coherence:1522, (5.5)) +
  `norm_eq_and_X_eq_sum_of_norm_Y_ge` (S07:1469, (5.4.b)) は `CharacterPsiDecomposition` (S07:1130 付近) 上で
  `χ^τ₁ = ∑_{α∈E⊆R(χ)} α` (E card=‖χ‖²) を出す。**だが `CharacterDifferenceImage.imageSet` は 2 元集合**
  ({muClassFunction, nuClassFunction}=単一既約 χ の χ−χ̄ 像)。certain-type column μ_j は w₁ 既約の和で
  R(μ_j)=2-**column** 構造 (2·w₁ σ-像) ⟹ **直接当てはまらない**。これが reconcile の crux。
- **`IsCoherent` は abstract isometry で (5.5) を carry しない** (2026-06-22 確認、S07:1557)。§10 `coh.tau1` は
  `IsCoherent` projection。∴ (5.5) を column に適用するには (i) `Hypothesis46` 経由で §6 certain-type host に
  繋ぐ (旧 note cont.² の A₀/V support mismatch 問題=要原文精読) か (ii) coherence isometry 用に column-(5.5) を
  別途立てる。**いずれも multi-session**。
- ⚠ Explore 監査 (2026-06-22) は「400-500 行・no blocker」と評価したが、item B (μ_k 2-column 分解) を
  「implicit」と自認 = これが linchpin。reconcile 複雑度を過小評価 ([[scaffold-sorry-free-not-done]] audit 版)。
- **次セッション entry 候補**: (1) `Hypothesis46` bridge を原文 (8.15)/(4.6) 精読で詰める (§6 全 apparatus を
  L=M 発火、(10.2)/(10.3) も unlock)、(2) column-用 `CharacterDifferenceImage` 一般化 (imageSet を 2-column に)。
  正本 = issue 1009「残 linchpin」節。

## ✅✅✅ 2026-06-22 完了 — (10.5) Dade-image identity 締結 (issue 1007 CLOSED)

mirror assembly + pinning 完成。(10.5) を grid + params 両 sorry-free に締結 (full build 3881 green、
FT-path scaffold sorry 131→130)。正本 = `issues/closed/1007-pf-10-5-dade-image-bridge.md`「完了」節。

- **S05_SigmaTrichotomy** 一般トリコトミー toolkit 3 本 (axiom-clean, §6 `certainType_diff_dade_eq` 抽象):
  `sigmaCoeff_sub_smul_chiFam_diff` / `eq_smul_chiFam_diff_of_all_sigmaCoeff_zero` /
  `eq_smul_chiFam_diff_of_vanishOnV` (norm-2 X + ψ vanish on V ⟹ X=s·(χ_P₁−χ_P₂))。commit `8c5c90a1`。
- **`Hypothesis.tau_muGridAlpha_eq`** (grid-level (10.5)): X=α^τ+n·ζ^τ₁ → 一般トリコトミーで締結。
  footprint=上流 gate (sorryAx Prop16.1/theoremA) のみ。
- producer omegaSigma→**alignedOmegaSigmaGrid** + **`alpha_tau_image`** faithful corollary (sorry-free)。
  commit `5f03d3d1`。
- **残る honest gate = `hn2`(=(10.3) n 偶数, → issue 1008)**: §10 (10.5) chain 全体が担う genuine 算術入力
  (cauchy-schwarz n<2 矛盾に必須)。`hzconj`(ζ̄≠ζ) は (1.1) で導出可だが chain 慣例で仮説化。

## ★★★★★ 2026-06-21 更新⁷ — a=0 の τ-isometry primitive + M-side + τ-side leg 完成 (6 補題)

(10.5) a=0 論証の **(ii) τ-isometry transfer + (iii) M-side inner products + (iv) τ-side** を全形式化
(build-green 3818 jobs、全 axiom-clean=muGrid 上流 gate のみ)。commit `de5b502d`/`dbd34818`/`c3506741`、
詳細 = issue 1007「進捗 cont.³」。主要 = **`tau_inner_eq_of_supported`** (完全 axiom-clean な再利用 primitive:
A₀-supported で `(hyp.tau φ,hyp.tau ψ)=(φ,ψ)`、§7 `dadeIntegralCharacterMap_inner_eq_on_supported_span` を
`{φ,ψ}` で instantiate) + `muGridAlpha_tau_inner_self` (‖α^τ‖²=2+n²) + `muGridAlpha_inner_zeta_sub_conj`
((α,ζ−ζ̄)=−n) + `muGridAlpha_inner_muColumn_sub_conj` ((α,μ_k−dζ̄)=0) + `zeta_sub_conj_support`
((ζ−ζ̄).support⊆A₀, 完全 axiom-clean) + `muGridAlpha_tau_inner_zeta_sub_conj` ((α^τ,(ζ−ζ̄)^τ)=−n)。

**▶ 残り = τ₁-side**。**🔑 2026-06-21 cont.⁴: 一般 Dade-coherence adjunction は不要と判明** — 原文 line 29 の
`μ_k−dζ̄` は **combination が A₀-supported** (μ_k=∑μ_ik は M' 誘導で消滅 by `induce_restrict_certainType_eq`、
degree dw₁ 相殺) ゆえ既存 `tau_inner_eq_of_supported` で transfer 可。cont.⁴ で τ₁-side 基盤 5 補題 landing
(`inducedFamily_closedUnderConjugate`/`muGrid_column_sum_vanishes_off_derived`/`muColumn_sub_conj_support`/
`muGridAlpha_tau_inner_muColumn_sub_conj`/`tau_zeta_sub_conj_eq_tau1`、詳細 issue 1007 cont.⁴)。
**cont.⁵ (2026-06-21) で τ₁-side inner-product 計算 完成** (5 補題、issue 1007 cont.⁵): `muGrid_column_sum_mem_inducedFamily`
(μ_k∈ℤ[S]) + `tau_muColumn_sub_conj_eq_tau1` (μ_k τ/τ₁) + **`muGridAlpha_tau1_inner_muColumn`** (`(α^τ,μ_k^{τ₁})=da`) +
`muColumn_tau1_inner_self` (`‖μ_k^{τ₁}‖²=w₁`)。⟹ **Cauchy-Schwarz `(da)²≤(2+n²)w₁` の全因子 materialize**
(`(α^τ,μ_k^{τ₁})=da` + `‖α^τ‖²=2+n²` + `‖μ_k^{τ₁}‖²=w₁`)。⚠ **coh を使う inner 計算 lemma は `[Finite G]`+FiniteInduce
regime 一本で書く** (explicit Fintype 混入で inner の Invertible が defeq mismatch、cont.⁵ で実害)。
**残 = final assembly の山**: (1)a∈ℤ (`inner_mem_ZIrr_int` cite, 軽い)、(2)**一般 Cauchy-Schwarz** (ClassFunction.inner、
既存は coefficient/norm-1 特殊形のみ→基底展開 or 新規証明; 次の山)、(3)数論 (nw₁+δ)²≤(2+n²)w₁→n<2 矛盾→a=0、
(4)(v)ζ^{τ₁} vanish on V + (vi)NC≤4+(3.8)→ψ=0。⟹ issue 1007 cont.⁵ 参照。

## ★★★★ 2026-06-21 更新⁶ — a=0 の μ-side inner-product inventory 完成 (CRUX μ⊥ζ 含む)

a=0 norm 論証の M-side inner products を全形式化 (build-green、axiom-clean=上流 gate のみ)。詳細・commit =
issue 1007「進捗 cont.²」。**最重要: μ⊥ζ (crux) は Clifford 不要 — μ_ij も ζ も既約ゆえ degree distinctness のみ**:
- `muGrid_inner_eq_zero_of_apply_one_ne` (CRUX `78d7c066`): `(μ_ij,χ)=0` for irr χ with `μ_ij(1)≠χ(1)`
  (`irr_cf_inner`+degree)。`(μ_ij,ζ)=0`/`(μ_ij,ζ̄)=0` = `μ_i0(1)=1≠w₁`/`μ_ij(1)=d≠w₁` (n·w₁=d−δ,d>1,w₁>1)。
  ⚠ Explore の「200-500行 Clifford/Mackey」見積もりは誤り (Res_K μ_ij 分析不要)。
- `muGrid_inner_self`/`_cross_column`/`_within_column` (`24bcfd02`/`36609290`): full grid orthonormality。
- `muGrid_column_sum_inner_self` (`36609290`): `‖∑_i μ_ik‖²=w₁`。
- ⚠ instance: inner は Fintype を term-relevant に持つ → unfold;rfl 系は explicit Fintype 不可、classical/
  `open scoped FiniteInduce` で finiteSubFintype synthesize。

**⟹ ‖α‖²=2+n² 組める**。残 = (i)norm assembly(grid-level で pinning 回避)(ii)τ/τ₁ isometry transfer
(§7→hyp.tau/coh.tau1)(iii)(α,ζ−ζ̄)=−n 等(iv)Cauchy-Schwarz+a=0(v)ζ^{τ₁} vanish on V(vi)NC+(3.8)→ψ=0。

## ★★★ 2026-06-21 更新⁵ — (10.5) Dade-image の **value-on-V leg** 完成 (2 leg のうち 1)

**(10.5) Dade-image の 2 analytic leg のうち value-on-V leg を完全形式化** (`0601b2bb`, build-green
3818 jobs)。原文「By (3.2.c), (4.3.c) and the definition of τ, α_ij^τ − δ(ω_ij^σ − ω_i0^σ) vanishes on V」。
3 補題 (S12、詳細・recipe = issue 1007「進捗 2026-06-21 cont.」):
- `Hypothesis.tau_muGridAlpha_apply_eq_on_typePV` (leg 本体): V 上で
  `hyp.tau (μ_ij − δ·μ_i0 − n·ζ) v = δ·(ω_ij^σ − ω_i0^σ)(v)` (ω^σ=alignedOmegaSigmaGrid)。
  = cornerstone (τ が V で α 復元) + reconciliation (μ=δ_j·ω^σ, j&0) + δ_0=1 + ζ-vanishing (v∉M')。
- `typePData_typePV_not_mem_derived` (**完全 axiom-clean**): v∈V ⟹ v∉M'。
- `Hypothesis.muColumnSign_zero`: δ_0=1。

**▶ 残り 2 gate (full `alpha_tau_image`)**:
1. **carrier pinning** (低リスク確認済: **S13 は params.omegaSigma/alpha_tau_image を未使用、S15.eta は独立**):
   producer omegaSigma→alignedOmegaSigmaGrid + `alpha_tau_image` を grid-level 定理に再構成 (params 版は薄い
   corollary)。ただし pinning だけでは sorry 不消 (a=0 が残る) = faithfulness plumbing。
2. **a=0 norm 論証** (deep, multi-session): Cauchy-Schwarz + ‖α‖²=2+n² + (10.3 n even>0) → n<2 矛盾 →
   ψ=X−δ(ω^σ diff) vanishes on V (**= leg ✅ で半分**) → NC(ψ)≤4 + (3.8) → ψ=0。
   **未整備の前提** (次の real-math 着手先): (a) **cross-column μ 直交** `(μ_ij, μ_i0)=0` (§6 は within-column
   `d.mu m ⊥ d.mu n` のみ S06:519/523) + **μ⊥ζ** → ‖α‖²=2+n²。(b) τ/τ₁ inner-product manipulation
   (`coherent.extension_inner_eq`/`extends_on_supported` S07、(α^τ,(ζ−ζ̄)^τ)=(α,ζ−ζ̄)=−n)。
   (c) ζ^{τ₁} vanishes on V (§5 (5.3.b)/(5.5)/(3.2.d))。(d) **§10↔§5 NC wiring** (§5 `sigmaCoeff_trichotomy`
   S05_SigmaTrichotomy:41 / `sigmaCoeff_eq_zero_of_sigmaNC_lt` を §10 alignedOmegaSigmaGrid に接続)。
   インフラ (§5 trichotomy / §7 isometry) は実在するが §10 carrier wiring が deep。

## ★★★ 2026-06-21 更新⁴ — (10.5) Dade-image foundation (carrier de-opaque + τ-value cornerstone)

**「(10.5) Dade-image」着手。最重要 finding: `alpha_tau_image` は現状の statement では数学的に証明不能 (scaffold sorry)** —
`{params : CharacterParameters}`・`{coh : CoherentHypothesis}` を**任意**に取り、`params.omegaSigma`/`params.mu` は
free field・旧 `coh.tau1` も free + `tau1_extends_tau_on_S` は opaque `Prop` ゆえ、結論
`τ(α_ij) = δ(ω_ij^σ−ω_i0^σ) − n·τ₁ζ` は arbitrary な omegaSigma/τ₁ に対し成立しない。**閉じるには carrier 材料化が必須**
(headline sorry を opaque field に hoist して消すのは禁止 [[scaffold-sorry-free-not-done]])。今回はその honest foundation を 2 つ landing:

- **① `CoherentHypothesis` de-opaque (10.4.b)**: 旧 `coherent_S : Nonempty(IsCoherent…)` (Prop、extension 取り出し不能)
  ＋ free `tau1` ＋ opaque `tau1_extends_tau_on_S` を **genuine `coherent : S07.IsCoherent hyp.tau hyp.Sset hyp.A0`**
  1 field に置換。`CoherentHypothesis.tau1 := coh.coherent.extension` (def) で Peterfalvi の τ₁ を materialize ⟹
  τ₁ が **本物の lattice isometry** (`coherent.extension_inner_eq`) ＋ **τ の supported-lattice 拡張**
  (`coherent.extends_on_supported`/`extension_agrees`) を carry。producer 無し (純 hypothesis = 「(10.4) を仮定」) ゆえ安全。
  consumer (`alpha_tau_image`/`tau1_values_and_norm_bound`/`typeII_derived_frobenius`) は `coh.tau1` のまま透過。
- **② `Hypothesis.tau_apply_of_mem_typePV` (τ-value cornerstone, axiom-clean)**: φ supported on A₀(M) なら
  `v∈V=typePV` で `(φ^τ)(v) = φ(v)`。`typePV ⊆ conjClassSet(typePV) ⊆ typePA0` (`subset_conjClassSet`) ＋
  `S07.dadeIntegralCharacterMap_apply_mem` の直適用。**`#print axioms` = [propext, Classical.choice, Quot.sound]
  (sorryAx 無・Prop16.1 gate 無 — 周辺 muGrid 系より clean)**。これは原文「by definition of τ, X vanishes on V」の
  **再利用 step** で (10.5) Dade-image・(10.6.b)・(10.9) が共有。⚠ 要 `open scoped FiniteInduce in` (hyp.tau と同じ
  scoped Fintype/Invertible instance を使う; 明示 `[Fintype G]` を足すと instance defeq mismatch する罠)。

**▶ (10.5) Dade-image を閉じるための残 gate (real 進捗順、この foundation の上に積む)**:
1. **carrier pinning**: `CharacterParameters.omegaSigma`/`mu` を `omegaSigmaGrid`/`muGrid` に identity field で pin
   (producer は既に `:= …Grid` ゆえ `rfl` discharge、S13 projection 非破壊の additive 変更)。⟹ statement を faithful 化。
2. **bridge 本体 = §10 σ↔τ on V**: `α_ij^τ − δ(ω_ij^σ − ω_i0^σ)` が V で消える。3 部品:
   (a) **M-side** `muGrid(v) = δ·ω_ij(v)` on V = (4.3.c) `certainType_apply_eq_of_mem_V` (§6 `Hypothesis L`、V=W∖W₂⊇typePV)。
   (b) **σ-side** `omegaSigmaGrid(v) = ω_ij(v)` on V = (3.2.c) `sigma_apply_of_mem_V` (§5)。
   (c) **τ-side** = cornerstone ② (✅landed)。
   ⚠⚠ **真の linchpin = §6 chiColumn ω (in 4.3.c) ↔ §5 omegaGrid ω (in omegaSigmaGrid) の reconcile**: 両者は
   `TypePData` から**別 bridge** (`toCertainTypeHypothesis` vs `typePData_toTICyclicHypothesis`) で構成され、
   現状 citeable な等式が無い = **deep gate** (multi-session)。
3. **norm/numeric `a=0`**: τ isometry (`coherent.extension_inner_eq` ＋ `inner_eq_on_supported`) ＋ τ₁ 拡張で
   `(α_ij^τ, ζ^τ₁)=−n` ＋ Cauchy-Schwarz ＋ (n even,>0,<2 矛盾)。要 μ-grid orthonormality (genuine μ 構造)。
4. **(3.8) trichotomy at §10**: 機構は §5 W-level に既在 (`sigmaCoeff_trichotomy`/`grid_no_constant_column`/`sigmaNC`)、
   §10 carrier への配線要。
- **§6 は (4.8) の完全 template を持つ** (`certainType_diff_dade_eq` = `(μ_ij−μ_ik)^τ=δ(ω_ij^σ−ω_ik^σ)`, sorry-free)
  が **support が W∖W₂** ゆえ §10 (typePV) には**直 cite 不可** (W₁# の扱いが違う; (10.5) は −nζ で W₁# を消して typePV に落とす)。
  → §10 は parallel な re-derivation。但し部品 (4.3.c/3.2.c/3.8/NC) は §5/§6 と共有。
- **issue = [1007](../../issues/1007-pf-10-5-dade-image-bridge.md)** (σ↔τ bridge + reconcile linchpin)。

## ★★★ 2026-06-21 更新³ — (10.5) support half 完成 (dade0-free, 自前 sorry 0)

**Peterfalvi (10.5) の support 半分 `Supp(α_{ij}) ⊆ A_0(M)` を dade0-free で完全形式化** (S12, build-green
3870 jobs + AxiomsCheck OK)。直前 commit (`f1467765` で抽出した (4.7) structural core) を使う計画通り、
**enlarged-support Dade (`Hypothesis46.dade0`) を一切構成せず**に原文 (10.5) の short argument を忠実に再現:

- **`Hypothesis.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1`** (linchpin): `x ∈ W₁^#` で
  `μ_{ij}(x) = δ_j · μ_{i0}(x)` ((4.3.c) `certainType_apply_eq_of_mem_V` on `V=W∖W₂ ⊇ W₁^#` + chiColumn の
  `W₁`-coll collapse (`wSnd=1` で χ₂ 因子消滅, inline `chiColumn_apply_eq` 相当) + δ_0=1 anchor)。muGrid/muColumnSign
  reconstruction は `unfold; rfl` idiom (instance は **明示供給せず synthesis** に任せる ← `Fintype` は data ゆえ
  明示 haveI は def の synthesized と不一致になり rfl 破綻、これが最大の罠だった)。
- **`Hypothesis.muGrid_zero_column_apply_one`**: `μ_{i0}(1)=1` ((4.4) anchor `μ_{00}=1_L` + within-column 定数性)。
- **`Hypothesis.muGrid_alpha_support`** (本体): α(1)=0 (n·w₁=d−δ) + ζ は M' 誘導ゆえ M' 外で消滅
  (`support_induce_subset_of_normal`/`induce_eq_zero_of_not_mem_normal`) + z∈M' は自己中心化で `(M')^#⊆typePA` +
  z∉M' は (2.1) `mem_compl_conj_into_W` で `x·y` (x∈W₁^#,y∈W₂) に共役、y=1 なら W₁^# vanishing で矛盾、y≠1 なら
  `x·y∈typePV`⟹`z∈conjClassSet typePV`。`α.conj_eq` で class-function 不変性、`typePData_disjoint_W1_W2` で W₁⊓W₂=⊥。
- **carrier 配線**: `CharacterParameters` に **`alpha_support : ∀ i j, j≠0 → (alpha i j).support ⊆ A0`** field を追加
  (placeholder でなく genuine 述語)。producer `exists_charParameters` で `muGrid_alpha_support` から discharge。
  そのため `exists_charParamArith` を **δ_j-independence (`∀ j≠0, muColumnSign j = delta`) も返す**よう拡張
  (`muColumnSign_eq_of_ne` + `unfold muColumnSign; rfl`)。`alpha_support_and_image` (旧 1 sorry, support+image 束ね) を
  **`alpha_support` (= `params.alpha_support`, 完全 axiom-clean `[propext,Classical.choice,Quot.sound]`) + `alpha_tau_image`
  (Dade-image 半分, sorry 残置)** に分割。
- **axiom footprint**: `muGrid_alpha_support`/W₁-lemma = `[propext, sorryAx, Classical.choice, Quot.sound]`、sorryAx は
  **すべて上流 bridge gate (Prop 16.1 / `theoremA_maximal_structure`, lane-f 所有) 由来で自前 sorry 0** (§10 muGrid 全結果と同じ)。
  `alpha_support` (projection) は sorryAx すら無し。

**▶ 次の lane-b frontier** (real 進捗順): **(10.5) Dade-image 半分 `alpha_tau_image`** (`S12:~1690`, sorry) =
`α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`。原文は `hyp.tau` (既存 §10 Dade) + `omegaSigmaGrid` (§5) + (4.3.c) +
(3.2.c)/(3.6)/(3.8) NC machinery + (5.3.b)/(5.5) を使う **重い analytic** (cont.² で dade0-free と確認済だが §3 NC が要)。
その後 (10.6) `tau1_values_and_norm_bound`。(10.7)/(10.8) は (8.8)=lane-f gate。S12 は **1700+ 行で hub 分割対象** (⚠ flag)。

## ★★ 2026-06-21 更新² — 循環解消 + (10.2)/(10.3) producer 完全 materialize

下の「更新」の結論「producer は (8.8) gate 待ちで打ち止め (循環)」は **SUPERSEDED**。循環は構造変更で断ち、
producer は実証明で組み上がった (実 sorry S12: 9→7)。方針 = [[feedback-cite-sorried-lemmas-if-signature-correct]]
(signature 正しければ gated lemma を cite して下流を実証明)。

- **① 循環解消 (`0c4f250a`)**: 旧 `w2_prime` は generic case-B datum 経由で `no_typeV_maximal` → producer に
  循環した。Peterfalvi (10.3) 原文証明 (`04.12:17` verbatim「By Theorem (8.8), there is a maximal subgroup
  S of G of **Type II** such that |S:[S,S]|=w₂, **and so w₂ is prime**」) が正路。新 obligation
  `Hypothesis.exists_typeII_maximal_with_w2` (∃ type-II maximal S, |S:S'|=w₂; faithful sorry, lane-f
  `theorem88_caseB_holds` gate) から `w2_prime` を**非循環**に実証明 (type-II → W₁ prime (8.6.a), no_typeV 不要)。
  旧 `exists_caseBData_with_w2` 削除。⟹ `w2_prime` を producer 上流に配置可能に。
  ⚠ **(8.8) case (b3) 原文確認**: S,T は「Type II/III/IV **or V**」 ⟹ datum を non-type-V に強化するのは
  unfaithful。type-V を許す generic datum では prime W₁ が出ず no_typeV 必須 = 循環は本物だった。type-II 特化が解。
- **② producer materialize (`10e97492`)**: 実 sorry 2 本 (`exists_zeta_degree_w1` (10.2) +
  `w2_prime_and_parameter_independence` (10.3)) → 実証明。
  - **`Hypothesis.exists_charParamArith`** (sorry-free body): (10.3) 算術 d/δ/n を §6 から materialize。
    j₀ nontrivial column (w₂ prime⇒≥2)、`d = μ_{0j₀}(1)∈ℕ` (`exists_natDegree_characterDegree_dvd_card`)、
    **d>1 = (4.4)** (非自明 column は linear でない: linear⇒K-trivial⇒column-0、`columnFamily_mu_ne` 矛盾;
    `exists_zeta` crux の inline。§6 Recipe 補題は concrete `↥M` instance 要ゆえ generic-L Lemma は不可、inline が解)、
    **δ=column sign, n·w₁=d−δ = (4.3.d)** (`certainType_degree_modEq` の `μ(1)=δ+w₁·a`、n:=a.toNat、a≥0 ∵ d−δ>0)、
    degree independence = `muGrid_apply_one_eq`。muGrid↔columnFamily 接続 = `unfold Hypothesis.muGrid; rfl`
    (host/instance を muGrid と同一に再構成)。
  - **`Hypothesis.exists_charParameters`**: ζ(10.2)+μ/ω^σ-grid+w2_prime+算術 を実 `CharacterParameters` に package。
    残 opaque field (delta_independent / τ₁-formulas) は True で埋め (→ (10.5)/(10.6) Dade calc 待ち)。両 producer が cite。
  - axiom footprint = [propext, sorryAx, Classical.choice, Quot.sound] (sorryAx = (8.8)+Prop16.1 gate のみ、body は sorry 無)。

- **③ (10.3) δ_j-independence 完成 (`fa71df35`)**: producer 最後の vacuous clause (`delta_independent := True`) を実証明化。
  新 §6 sign-constancy `columnFamily_mu_zero_sign_pow` + prime form `columnFamily_mu_zero_sign_eq_of_ne_one`
  (**axiom-clean**; degree lemma と同じ (3.9.b)+(4.3.b) `hZ : δ'·d'=δ·d`、d'=d>0 で δ'=δ をキャンセル) +
  §10 `Hypothesis.muColumnSign` (per-column 符号、muGrid 同型再構成) + `muColumnSign_eq_of_ne` (δ_j=δ_j')。
  `CharacterParameters` の opaque `delta_independent`/`_holds` フィールド削除 → (10.3) 結論が実
  `∀ j j'≠0, muColumnSign j = muColumnSign j'` を主張・`muColumnSign_eq_of_ne` で証明。
  **⟹ (10.3) `w2_prime_and_parameter_independence` 全 5 clause 実証明** (w₂ prime / d>1 / degree-indep /
  δ-indep / n-formula)。sign lemma 単体は axiom-clean、§10 muColumnSign_eq_of_ne は bridge Prop16.1 gate のみ。

**▶ 次の lane-b frontier**: S12 残 7 sorry = `exists_typeII_maximal_with_w2` ((8.8) gate=lane-f) +
(10.5) `alpha_support_and_image` + (10.6) `tau1_values_and_norm_bound` (= Dade calc、`CoherentHypothesis`
仮定下、要 τ₁) + (10.7)/(10.8)(=(8.8) gate+counting) + (10.9)/(10.10.x)。
**⚠ (10.5)+ は重い**: (10.5) Dade image は (3.6)/(3.8)/(3.2.c/d)/(5.3.b)/(5.5) の重 §3/§5 machinery を要し、かつ
`params.mu`/`omegaSigma` は free field ゆえ arbitrary params では未証明。(10.7)/(10.8) は (8.8)=lane-f gate。

### ★ 2026-06-21 cont. 調査結果 (次セッション用 de-risk)

- **faithfulness pinning `[Finite G]`-on-structure 経路は不可** (試行→revert): CharacterParameters に `[Finite G]`
  追加すると S13.Hypothesis(`params : CharacterParameters base`)が要 `[Finite G]` 化 → S13 の auto-generated
  field projection (`Hypothesis.q`/`.p` 等)の dot-notation が壊れる cascade。**∀-hG pin を使うなら `@Hypothesis.muGrid G _ hyp.finiteG …` explicit-finiteG 形式** (structure に `[Finite G]` 足さない) か、muGrid の sig から `[Finite G]` を外し
  hyp.finiteG 内部供給に変える(muGrid は既に body で `haveI := hyp.finiteG` 済→sig の `[Finite G]` は冗長の可能性)。
- **`Hypothesis46` 全構築は dade0 が deep**: `Hypothesis46.tic_V = W\W₂` 固定 (4.3.a 大 TI)、`dade0` は
  `A ∪ (W\W₂)^L` 上 = `typePA0 ∪ (W₁#)^M`。§10 `typePA0 = typePA ∪ (typePV)^G` (typePV=W\(W1∪W2)、**W₁# 除外**)
  ゆえ §10 dadeData(typePA0 上)では **(W₁#)^M 分** 足りない → enlarged-support Dade を新規構成要 (§4、deep)。
- **🟢 但し (10.5) SUPPORT 半分は dade0 不要で feasible**: (4.7) core
  `mem_A_of_apply_ne_zero_of_not_subset_characterKernel` (S06_CertainTypeSupport:47) は **構造フィールドのみ使用**
  (`subH`/`subH_normal`/`K`/`A_covers`、**`dade0`/`tau` 不使用**)。∴ §10 structural (4.6.a-d) データで (4.7) を発火可
  (Hypothesis46 全体=dade0 不要)。**次セッション (10.5) support 攻略**: (4.7) core を structural-param 化
  (または §10 で再証明) + (4.3.c) μ-W₁-vanishing (`induce_omegaColumnDiff_mu_diff` の Hyp-L 版要確認) + (4.4)
  `certainType_zero_column_anchor` + (2.1) `mem_compl_conj_into_W` で canonical α の support ⊆ A_0 を構成。
  (10.5) を `alpha_support` / `alpha_tau_image` に分割し前者を close。後者 (Dade image) は dade0 待ち。
- **∴ §10 spine: support 系は dade0-free で進める / Dade-image 系は enlarged dade0 (deep §4) + (8.8) (lane-f) 待ち**。

### ★★★ 2026-06-21 cont.² 決定的発見 — (10.5)/(10.6) は deep dade0 を必要としない (Explore 検証)

⚠ 上記「Dade-image 系は enlarged dade0 待ち」は **訂正**。Peterfalvi (10.5)/(10.6) 原文 + Lean §6 精査で確定:
**(10.5)/(10.6) は §10 既存 `hyp.tau` (= Dade rel (A_0(M),M,G)、typePV-based) + 既存 `omegaSigmaGrid` (§5 σ) +
構造的 §6 facts のみ使用、新規 W\W₂ Dade (`Hypothesis46.dade0`) 不要。** 各 cited fact の Lean level:
- **(4.3.c)** = `certainType_apply_eq_of_mem_V` (S06_CertainTypeCharacters:878、**Hypothesis L**、dade0 不使用) ✅在庫
- **(4.4)** = `certainType_zero_column_anchor` (S06、**Hypothesis L**) ✅在庫
- **(4.7)** = `mem_A_of_apply_ne_zero_of_not_subset_characterKernel` (S06_CertainTypeSupport:47、Hypothesis46 だが
  **proof は subH/subH_normal/subH_le_K/A_covers/K のみ使用、dade0/tau 不使用**)。consumer = 同一ファイル 3 箇所
  (:100/:136) + AxiomsCheck:752 のみ。
- **τ** = `hyp.tau` (既存 §10 Dade)、**ω^σ** = `omegaSigmaGrid` (既存 §5 bridge、typePV) ✅在庫
- **(3.2.c)/(3.8)/(3.6)** = §3 Dade NC machinery (要確認だが §3 既存と推定)。

**⟹ §10 Hypothesis46 全構築 (dade0/tau) は UNNECESSARY。** `Hypothesis46.tic_V=W\W₂` は §6 (6.8) 専用特殊化で
§10 (typePV) には元々不適合 (cont.² で既出)。

**▶ dade0-free 実装計画**:
1. **(4.7) を structural-param 化** (decouple from `Hypothesis46`): `mem_A_of_apply_ne_zero...` を
   (K, subH, subH_normal, A_covers) 引数版にし、既存 Hypothesis46 consumer は h.subH 等で呼ぶ (DRY)。
2. **§10 structural (4.6.c-d) data**: subH = M_F (=maxNilpotentNormalHall M, subgroupOf M; W2≤M_F≤M'),
   subH_normal (M_F◁M), A_covers = **typePA 定義そのもの** (C_{M'}(h)#⊆typePA ∀h∈M#)。tractable。
3. **(10.5) `alpha_support`** (分割前半、dade0-free): structural (4.7) + (4.3.c) + (4.4) + (2.1)
   `mem_compl_conj_into_W` で canonical α support ⊆ A_0。
4. **(10.5) `alpha_tau_image`** (分割後半): `hyp.tau` + `omegaSigmaGrid` + (4.3.c) + (3.2.c)/(3.8)/(3.6) +
   (5.3.b)/(5.5)。§3 NC machinery 使用、harder だが dade0-free。
5. **(10.6)** 同様。
→ (10.7)/(10.8) のみ (8.8)=lane-f gate 残。**§10 spine の大半は lane-b 単独で dade0-free に開通可能**。

## ★ 2026-06-21 更新 — (10.3) degree theory 完全 materialize (axiom-clean) + column-0 faithfulness 修正

§6 attack-order の (b)(c) ((10.3) degree 独立性) を**両半分とも axiom-clean で形式化完了**。frontier 前進:

- **(b) within-column (i-independence) ✅** `Hypothesis.muGrid_apply_one_within_column` (S12, `69dc59fb`):
  muGrid レベル、`columnFamily_difference_apply_one` 経由。muGrid unfold 技法確立 = `unfold Hypothesis.muGrid; simp only [key]`。
- **(c) cross-column (j-independence) Galois ✅ axiom-clean** `columnFamily_mu_zero_apply_one_pow` (S12, `eec2a065`):
  原文 (10.3) の核心。χ₂ → χ₂^k で degree 不変。(3.9.b) `exists_mapRingEquiv_sigma_omega_pow` + (4.3.b)
  `sigma_chiColumn_eq_certainType` + 1 で評価 (u は ℤ 固定 `map_intCast`, degree>0/sign=±1 `Int.natAbs`)。
  sdiff/toTIC σ は W 共有で omega/omegaProdChar defeq (`chiColumn_zero` bridge)。
- **(c') prime-order form ✅ axiom-clean** `columnFamily_mu_zero_apply_one_eq_of_ne_one` (S12, `c122d857`):
  |D| prime (=w₂) なら全非自明 column が共通 degree。prime card ⟹ `Finite D` (`Nat.card_pos_iff`)、非自明元が
  生成 ⟹ χ₂'=χ₂^k、k coprime w₂、coprimality を source order に転送 (`orderOf(ω(1,χ₂)) ∣ orderOf χ₂`)。
  helper `omegaProdChar_one_pow` ((ω(1,χ₂))^k=ω(1,χ₂^k)) 抽出。
- **column-0 faithfulness 修正 ✅** `finCardEquivCharacterGroup` を 0↦trivial に pin (`3d170683`、`finCardEquivCharacterGroup_zero`)。
  旧版は任意全単射で muGrid column-0 が trivial dual に固定されず → degree_independent (j≠0=非自明前提) が
  unfaithful になりえた。Peterfalvi (4.4) 規約 (column 0 = trivial) に整合。

**✅ muGrid-level cross-column wiring DONE (2026-06-21 後続セッション)**: `Hypothesis.muGrid_apply_one_cross_column`
(S12) — `muGrid 0 j 1 = muGrid 0 j' 1` (j,j'≠0)。実装:
- (i) §6 corollary `columnFamily_mu_zero_apply_one_eq_of_ne_one` を within-column と同じ `key` 技法
  (`unfold Hypothesis.muGrid; simp only [key]` で row index を 0 に剥がす) で muGrid に配線、最後に corollary を `exact`。
- (ii) Pontryagin card: `h.card_charGroup_W2 : Nat.card (Ŵ₂) = Nat.card h.W2`、これを `subgroupOfEquivOfLe` で
  `Nat.card (W2.subgroupOf (W1⊔W2)) = hcardW2sub` 経由 `hyp.w2` に繋ぐ。
- (iii) **w₂ prime は仮説 `hw2 : (hyp.w2).Prime` として取る** (`Hypothesis.w2_prime` を cite **しない**)。
  ⚠ **理由 = 循環依存回避**: `Hypothesis.w2_prime` → `theorem88_caseB_prime_orders` → `caseB_typeP_prime_W1`
  (type-V branch) → **`no_typeV_maximal`** → `w2_prime_and_parameter_independence` (= **producer 自身**) →
  (もし cross-column を cite すれば) → w2_prime。`TypeVData` は `TypePNontrivialCore` (prime W1) フィールドを
  持たない (typeP/U_eq_bot/alternative のみ) ゆえ type-V を no_typeV で除外するしかなく循環は本物
  (Peterfalvi が §10 で no-type-V と w₂-prime を相互証明する構造を反映)。∴ cross-column は hw2 を仮説化して自己完結。
- nontriviality: `finCardEquivCharacterGroup` injective + `finCardEquivCharacterGroup_zero` (0↦trivial) + finCongr val。

**✅ combined degree independence DONE**: `Hypothesis.muGrid_apply_one_eq`
(`(hw2 : w2.Prime) → muGrid i j 1 = muGrid i' j' 1` for j,j'≠0) = within (i→0) ×2 + cross (j→j')。
これが `CharacterParameters.degree_independent` の materialized 本体 (producer で d を命名して使う)。
両者とも axiom footprint = muGrid と同一 (= upstream Prop 16.1 gate のみ、自前 sorry 0; within-column と同じ)。

**▶ 残 = producer (`w2_prime_and_parameter_independence`/`exists_zeta_degree_w1`) = (8.8) gate 待ち (循環)**:
producer は `CharacterParameters.w2_prime : hyp.w2.Prime` field を要求するが、これは上記循環で lane-b 単独では
閉じない。`Hypothesis.w2_prime` (S12:1174) の sorry 源 = `exists_caseBData_with_w2` (faithful (8.8)↔M 義務) +
`no_typeV_maximal` 経由の producer 循環。**∴ §10 keystone ((10.8)) + producer + (10.3) w₂ prime は lane-f (8.8)
着地待ち**。(10.3) degree theory の lane-b 単独 honest 反映は cross-column 完成で**打ち止め (完了)**。

## 0. 現在地 (2026-06-20)

- **(6.8) `sibleySetup_is_coherent` DONE** (§8 唯一 sorry 消滅、実 sorry 138)。
- §10-13 の lane 分担: **§10 (S10) = Lane H** (BG §16 cite/wiring) / **§11-13 (S11/S12/S13) = Lane B 領域**。
- §11-13 (~25 sorry) は **G2 = Pf §3-8 char API** に gate。その 2 半分:
  - ① (6.8) coherence producer = ✅ DONE。
  - ② **gate #3 = ω/η/μ/ν/σ index 族 + σ/τ₁ の §5/§6 materialization**。
    S05 ω-grid (`omegaGrid`/`omegaSigmaGrid`/`sigmaIntegral`) は ✅ 全 sorry-free。
    **欠けているのは「§10 carrier (`Hypothesis M`) を §5/§6 の ω/μ machinery に接続するブリッジ」** = gate #3 proper。
- ⚠ **「S11-13 の sorry 除去 ≠ 進捗」** ([[scaffold-sorry-free-not-done]])。carrier の opaque Prop を vacuous に
  埋めるのは scaffold。doneness = carrier 材料化 (real 恒等式 + 実構成)。

## 1. §10 の数学 (Pf §12 = pp.58-63、原文 `references/peterfalvi/04.12_*.mmd`)

`M` = type III/IV/V maximal、`M' = [M,M]`、`W = W₁ × W₂` cyclic、`τ` = Dade isometry rel `(A₀(M),M,G)`。

| Pf | 内容 | S12 行 |
|---|---|---|
| (10.1) | Hypothesis (setup) | 86 (`Hypothesis M`, ✅materialized) |
| (10.2) | ∃ ζ ∈ S∩Irr M, ζ(1)=w₁ | 286 (sorry) |
| (10.3) | w₂ prime; d=μ_ij(1) 独立, δ=δ_j 独立, d>1, n=(d-δ)/w₁∈ℕ | 295 (sorry) |
| (10.4) | Hypothesis (a): ζ,d,δ,n + τ₁ 拡張 | 271 (`CoherentHypothesis`) |
| (10.5) | α_ij=μ_ij-δμ_i0-nζ, Supp(α_ij)⊆A₀(M), α_ij^τ formula | 307 (sorry) |
| (10.6) | τ₁ images, ζ^τ₁ norm bound | 318 (sorry) |
| (10.7) | type II ⟹ [S,S] Frobenius kernel S_F | 339 (sorry) |
| (10.8)★ | **S not coherent** (keystone) | 348 (sorry) |
| (10.9) | w₁<w₂ ⟹ (μ₀-ζ)^τ=Σω_i0^σ-χ, χ⊥(IrrW)^σ, ‖χ‖²=1 | 358 (sorry) |
| (10.10) | no type V maximal (via (10.8): type V ⟹ S coherent、(6.8)/(6.4)/(6.5) 使用) | 368/378 (✅body sorry-free, 依存 sorry) |
| (10.11) | case(b) ⟹ \|W₁\|,\|W₂\| prime; type II ⟹ H elem ab p^q | 425 (✅body sorry-free, 依存 sorry) |

**依存連鎖** (lane-f POLE-1 への接続): `theorem88_caseB_prime_orders` (✅body) → `no_typeV_maximal` (✅body)
→ (10.8) `S_not_coherent` + (10.10.x) `typeV_forces_coherence` (両 sorry) → ⟹ **(10.8)/(10.10.x) を閉じれば
lane-f の POLE-1 `section16TypePStructure` の primes 残 sorry も honest 化**。

## 2. carrier de-opaque plan (`CharacterParameters`, S12:241)

現状 = **scaffold**: real field (`zeta`/`d`/`delta`/`n`/`w2_prime`/grid `mu`/`omegaSigma`/`alpha`) と
**11 opaque Prop** (`zeta_irreducible`/`degree_independent`/`delta_independent`/`n_formula`/`alpha_formula`/
`alpha_tau_formula`/`mu_tau1_formula`/`zeta_tau1_norm_bound`/`orthogonality_w1_lt_w2`/
`typeV_parameter_formula`/`typeV_coherence_formula`) が混在。**producer 未存在** (全定理 `∃ params, sorry`)。

**模範 = `S15.Hypothesis`** (S15_SAndT:73-170、commit c724456 で de-opaque 済): real grid
`omega`/`eta`/`mu`/`nu` + honest 恒等式 field `eta_eq_tau_omega`/`mu_definition`/`nu_definition`。
→ `CharacterParameters` も同様に opaque Prop を実恒等式に置換: 例
`alpha_formula : Prop` → `alpha_def : ∀ i j, alpha i j = mu i j - delta • mu i 0 - n • zeta`、
`zeta_irreducible : Prop` → 実 `IsIrreducibleCharacter zeta` 等。

## 3. gate #3 ブリッジ: §10 `Hypothesis M` → §5 `TICyclicHypothesis G`

§10 の μ/ω 解析は §5/§6 の ω-grid を要する。§6 の ω/μ API は全て **`Hypothesis46 A L`/`TICyclicHypothesis`**
ベース ⟹ ブリッジが gate #3 proper の核心。

### 3a. `TICyclicHypothesis G` のフィールド (S05_TICyclic:41) と TypePData (MaximalSubgroupType:126) からの導出

| field | 導出 | 状態 |
|---|---|---|
| W/W1/W2, W1≤W, W2≤W, nontrivial, W1⊔W2=W, W_cyclic | TypePData 直対応 (`W_eq`/`W_cyclic`/`W*_nontrivial`) | 易 |
| `W_disjoint` | `M_complement` (W1∩M'=⊥) + W2≤H≤M' | ✅ **DONE** = `typePData_disjoint_W1_W2` (S12) |
| `W_card_coprime` | disjoint + cyclic ⟹ coprime | ✅ **DONE** = `typePData_coprime_card_W1_W2` (S12) |
| `W_card_odd` | `Odd |G| ⟹ |W| ∣ |G| ⟹ Odd |W|` | ✅ **DONE** = `typePData_W_card_odd` |
| `V := typePV M = W\(W1∪W2)` | TICyclicHypothesis.V と一致 | ✅ |
| `V_subset_sharp` | 1∈W1 ⟹ 1∉V ⟹ V⊆univ\{1} | ✅ |
| `V_subset_W` | set diff ⊆ W | ✅ |
| `W_normalizes_V` | W abelian (cyclic) ⟹ w∈W で wvw⁻¹=v∈V | ✅ (`commute_of_mem_of_isCyclic`) |
| `V_ti : IsTISubset V W` | ✅ **DONE** = `typePData_V_ti` (§3b, cyclic-characteristic) | ✅ **issue 1005 CLOSED** |

**⟹ ブリッジ `typePData_toTICyclicHypothesis` (S12) 完成・axiom-clean・unconditional (2026-06-20)。**
`hVti` param は廃止、`typePData_V_ti data` で内部 discharge。

### 3b. V_ti ✅ RESOLVED (2026-06-20, issue 1005 CLOSED)

**当初「genuine gap」と診断したが誤り**。`normalizer_V` + **cyclic 因子構造**で完全に閉じる。
キーは「**cyclic W では W₁, W₂ が位数で一意 ⟹ characteristic**」(当初の §3b 分析はこれを見落とし)。

- `typePData_V_ti (data : TypePData M) : IsTISubset (typePV M data) data.W` (S12, axiom-clean)。
- 証明: g, a∈V, b=gag⁻¹∈V を取る。
  - `normalizer_V {a}` で `N_G({a}) = W`、同 `N_G({b}) = W` (singleton normalizer = 点 stabilizer)。
  - `g` は W を正規化: `h∈W ↔ ghg⁻¹∈W` は両辺とも `hah⁻¹=a` に帰着 (b=gag⁻¹ の展開を `group`)。
  - **characteristic**: A≤W cyclic で `A.map (conj g) = A` を `cyclic_subgroup_eq_of_card_eq`
    (`BG.Ch3.S10`, ↥W で位数一致 ⟹ 部分群一致) で。⟹ g は W₁, W₂ も正規化。
  - ⟹ g は V を正規化 ⟹ `g ∈ N_G(V) = W` (`normalizer_V` X=V, nonempty=`typePData_typePV_nonempty`)。
- ⚠ 当初「IsTISubset は normalizer_V より strict に強い」「§6 でも入力」は **cyclicity 抜きの話**で、
  type-P の cyclic W では成立しない。`normalizer_eq_sup_of_isTISubset_of_isCyclic` (逆方向) は不要だった。

### 3c. coprime ✅ DONE

`typePData_coprime_card_W1_W2` (S12, axiom-clean)。Klein-four 反例ゆえ **cyclic が本質** (disjoint 単独では
不可)。S15 `coprime_card_U_card_P_of_disjoint` (S15_SAndT:888) は Hall 経由で別機構ゆえ非流用。
**実装** = 乗法写像 `(Subgroup.inclusion hW1le).coprod (Subgroup.inclusion hW2le) : ↥W₁ × ↥W₂ →* ↥W`
が disjoint から injective → `isCyclic_of_injective` (cyclic への埋め込みは cyclic) →
`coprime_card_of_isCyclic_prod` (mathlib `SpecificGroups/Cyclic`: 有限 cyclic product ⟹ 因子 coprime)。

### 3d. μ-level (ブリッジの次)

TICyclicHypothesis は **W-level ω/σ** のみ (ω on W, ω^σ on G)。μ_ij (on M, = Ind_{M'}^M …) は別途
**§6 `Hypothesis46`/`CertainTypeHypothesis` for M'** が要 (certain-type μ family + Dade)。これが de-opaque の
`mu`/`alpha` grid の供給源。§10 `Hypothesis M` から M' の certain-type 構造を構築 = 重い (full 4.6 apparatus)。

## 4. API 在庫 (sorry-free、消費可)

- **S05 ω-grid**: `TICyclicHypothesis.omegaGrid` (S05_OmegaGrid:65, `Fin|W1|→Fin|W2|→CF ↥W ℂ`),
  `omegaSigmaGrid` (S05_OmegaSigmaGrid:50, `→CF G ℂ`, = σ(ω)), `sigmaIntegral` (S05_IntegralSigma:48,
  `IntegralCharacterMap ↥W G`), `sigmaIntegral_apply_of_mem_V` (V 上恒等), β family + Gram (S05_SigmaIsometry:155).
- **§6 certain-type**: `Hypothesis46` (S06_CertainHypothesis46:39, extends `CertainTypeHypothesis`),
  `toTICyclicHypothesis` (S06_DadeIsometryCertain:414), μ/ω column API (`induce_omegaColumnDiff_*`,
  `columnFamily_mu_*`, `induce_isIrreducible_of_forall_chiRestrict_ne` Clifford, S06_CertainTypeCharacters/Clifford)。
- **TypePData** (MaximalSubgroupType:126): H/U/W1/W2/W + `M_complement`/`derived_complement`/`centralizer_W1`/
  `normalizer_V` + `card_W1_eq_derived_index`/`derivedInG_eq_fitting_sup_U`。`typePV`/`typePA0` (290/294)。
- **coherence**: `sibleySetup_is_coherent` (S08_CoherenceTheorems, ✅(6.8)), `IsCoherent` (S07:1557),
  `IntegralCharacterMap` (S07:301), `CharacterDifferenceImage` (S07:395)。
- **§4 Dade**: `S04_DadeIsometry` (main, sorry-free)。

## 5. 攻略順 (推奨)

1. ✅ `typePData_disjoint_W1_W2` (DONE, S12)。
2. ✅ `typePData_coprime_card_W1_W2` (DONE, S12)。
3. ✅ `typePData_W_card_odd` (DONE, S12; `Odd |G| → |W| ∣ |G| → Odd |W|`)。
4. ✅✅ **ブリッジ `typePData_toTICyclicHypothesis` 完成** (DONE 2026-06-20, S12, axiom-clean)。
   17 フィールド中 16 を `TypePData` から実証明で供給、`V_ti` のみ ambient TI = Peterfalvi (4.6.b) を
   **明示パラメータ `hVti`** で取る (§5 `mapOfInjective` / §6 `toTICyclicHypothesisOfV` と同設計;
   §3b の調査 (i)/(ii) で Dade data も normalizer_V も V_ti を供給しないと確定 → (iii) パラメータ化)。
   ⟹ ω-grid (`omegaGrid`/`omegaSigmaGrid`/`sigmaIntegral`) が §10 で利用可能に。
   **残 obligation = `hVti` の discharge = [issue 1005](../../issues/1005-typep-ambient-v-ti.md)**
   (4.6.b ambient-TI; 上流 BG σ-理論に gate されるか要判定)。
5. ▶ **次**: `CharacterParameters` de-opaque (§2、S15 模範) — opaque Prop を実恒等式に。
6. μ-level: M' の certain-type 構造 (§3d) ⟹ `mu`/`alpha` grid 供給。
7. (10.2)/(10.3) producer 構成 → (10.5)/(10.6) Dade calc → (10.8) keystone → (10.9)/(10.10.x)。
8. ⟹ §11/S13 (9.x/11.x riders) も同 machinery で。

**STOP 規律**: 1 leaf が ~4-5 実質試行で進まなければ STOP + 本 note に障害記録。難所回避禁止 ([[feedback-no-avoiding-hard-parts]])。

## 6. (10.2)–(10.5) 原文照合 + (10.2) 攻略 diagnosis (2026-06-20 bridge 後の調査)

原文 = `references/peterfalvi/04.12_pp_58_63_Maximal_Subgroups_of_Types_III_IV_and_V.mmd` L1-42 を verbatim 照合。
**確定した式 (de-opaque で baking する正値)**:

- **(10.1)**: `S = {Ind_{M'}^M θ | θ∈Irr M', θ≠1}`。「By (8.15), Hyp (4.6) と (5.2) が L=M, H=K=M' で成立。
  w₁,w₂,σ,ω_ij,μ_ij,μ_j,δ_j は **Hyp (4.6) with L=M** と同義」⟹ **μ/ω/δ は §6 (4.6)-with-L=M 由来**
  (∴ μ-level の真の供給源 = §10 Hyp → §6 `Hypothesis46 M M'` bridge、§3d)。
- **(10.3)**: `0≤i<w₁, 0<j<w₂` で `d=μ_ij(1)` は i,j 独立、`δ=δ_j` は j 独立、`d>1`、`n=(d-δ)/w₁∈ℕ`。
  (w₂ prime は **Thm (8.8)** 経由 type-II maximal S with |S:[S,S]|=w₂。)
- **(10.5)**: `α_ij = μ_ij − δ·μ_i0 − n·ζ` (`0≤i<w₁, 0<j<w₂`)、`Supp(α_ij)⊆A₀(M)`、
  `α_ij^τ = δ(ω_ij^σ − ω_i0^σ) − n·ζ^τ₁`。

### CharacterParameters de-opaque field specs (S15.Hypothesis 模範 = data+real恒等式, opaque Prop 廃止)

| 現 opaque Prop | 実恒等式 (self-contained = tau/tau₁ 不要) | 備考 |
|---|---|---|
| `zeta_irreducible` | `IsIrreducibleCharacter zeta` | producer 結論も書換要 (∧ の項) |
| `n_formula` | `(n:ℤ)*(hyp.w1:ℤ) = (d:ℤ) - delta` | clean |
| `alpha_formula` | `∀ i j, alpha i j = mu i j - (delta:ℂ)•mu i 0 - (n:ℂ)•zeta` | clean |
| `degree_independent` | `∀ i (j:Fin w2), j≠0 → (mu i j) 1 = (d:ℂ)` | index 0<j 要 |
| `delta_independent` | δ_j family field 追加要 (現状 `delta:ℤ` は共通値のみ) | 要新 field |
| `alpha_tau_formula`/`mu_tau1_formula`/`zeta_tau1_norm_bound`/`orthogonality_w1_lt_w2`/`typeV_*` | **tau (hyp.tau) / tau₁ (CoherentHypothesis) 要** | CoherentHypothesis 文脈で de-opaque |

⚠ S15.Hypothesis は `omega`/`eta`/`tau3` を **data field** + 恒等式 `eta_eq_tau_omega : eta i j = tau3 (omega i j)`
(S15_SAndT:131-147) で carry。CharacterParameters.omegaSigma も同様に bridge の `omegaSigmaGrid` に pin できる
(`omegaSigmaGrid` docstring が「`S12.CharacterParameters.omegaSigma` がこれに pin される」と明記)。

### ★ (10.2)/(10.3)/μ-grid 攻略 = §10→§6 (4.2)+Dade bridge (apparatus は §6 に既在!)

⚠⚠ **重要訂正** (2026-06-20 深掘り): 当初「(10.2) は quotient-Frobenius + Brauer を一から build」と
診断したが **誤り**。(10.1) 原文「Hyp (4.6) が L=M, H=K=M' で成立」が正路を指す: **§6 certain-type
apparatus が (10.2)/(10.3)/μ-grid をすべて供給**、新規 apparatus build は不要。Brauer/inertia は §6 に既在:
- `S06_CertainTypeClifford.lean:538` `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`
  (**Brauer permutation lemma**)、`:756` inertia `I_L(χ)=K`「W₁# で不動な char 無し」(= FPF-on-chars)。
- `IsFrobeniusGroup.of_centralizer_kernel_le` (`Ch06_FrobeniusActions/FrobeniusGroup.lean:324`) =
  `centralizer_W1` 条件から Frobenius 構成。
- `isIrreducibleCharacter_induce_of_inertia_eq` (`InducedIrreducible.lean:424`)。

**∴ 真の次ステップ = §10→§6 bridge = `Hypothesis M → S06.CertainTypeHypothesis (typePA0 M typeP) M`**
(`CertainTypeHypothesis A L extends S06.Hypothesis ↥L` + `dade : S04.Hypothesis G A L`):
- **Dade 部 `dade` は §10 Hyp に既在**: `Hypothesis.dadeData.dade : S04.Hypothesis G (typePA0 M typeP) M`。
- **構造部 `S06.Hypothesis ↥M`** (S06_DadeIsometryCertain:67, **11 field**) を `TypePData M` から構成
  (L=↥M, K=M'.subgroupOf M, W1/W2.subgroupOf M)。field 対応:

  | S06.Hypothesis ↥M field | TypePData M source | 備考 |
  |---|---|---|
  | `K = M'.subgroupOf M` / `K_normal` | derivedInG M 正規 (commutator) | 易 (subtype transport) |
  | `isComplement : IsComplement' K W1` | `M_complement` | **直対応** |
  | `W1_nontrivial`/`W1_cyclic` | `W1_nontrivial`/`W1_cyclic` | subgroupOf transport |
  | `W2_nontrivial`/`W2_cyclic`/`W2_le_K` | `W2_*`/(W2≤H≤M') | subgroupOf transport |
  | `centralizer_W2 : ∀x∈W1#, C_K(x)=W2` | `centralizer_W1` (C_{M'}(x)=W2) | G↔↥M transport (fiddly) |
  | `card_coprime : Coprime |K| |W1|` | **param `hHall`** (W₁ Hall, 非導出) | ⏸ **issue 1006** |
  | `W_odd` | `typePData_W_card_odd` 系 | ✅ 易 |

  **`card_coprime` (W₁ が M の Hall complement = gcd(|M'|,|W₁|)=1) は param `hHall` 化**: complement だけ
  では従わない (確認済: C₂×C₂ 反例)、κ-Hall 経由でのみ導出可ゆえ obligation = [issue 1006](../../issues/1006-typep-w1-hall.md)。
  他 10 field は subtype (subgroupOf) transport の機械作業で discharge (centralizer は `S03h.centralizer_subgroupOf`)。

**✅✅ bridge DONE (2026-06-20)**: `typePData_toS06Hypothesis` (構造部, 11 field) +
`Hypothesis.toCertainTypeHypothesis` (CertainTypeHypothesis 組立, dade=既在) 完成・axiom-clean
(`39f1ead4` 系の続き)。⟹ §6 の `toTICyclicHypothesis`・μ/ω column API・Clifford inertia が L=M で発火可。

### ▶ 次の着手順 (real 進捗順)

1. ✅ **§10→§6 bridge DONE**。残 = `hHall` discharge ([issue 1006](../../issues/1006-typep-w1-hall.md), κ-Hall 経由)。
2. **▶ (10.2) を §6 Clifford 機構で形式化** (RECON 済 2026-06-20、正確な execution path):
   - **核心定理 = `induce_isIrreducible_of_forall_chiRestrict_ne`** (`S06_CertainTypeClifford:902`):
     `h : Hypothesis L` (or CertainTypeHypothesis), `χ : IrreducibleCharacter ↥h.K`,
     `hχ : ∀ χ₂, h.chiRestrict χ₂ ≠ χ` ⟹ `IsIrreducibleCharacter (induce h.K χ)`。
     engine = `inertia_eq_K_of_forall_chiRestrict_ne` (`:878`, I_L(χ)=K) + Isaacs 6.34。
   - **(10.2) ζ**: θ = 非自明 linear (degree-1) irreducible char of M'=K を取る。
     `induce_isIrreducible_of_forall_chiRestrict_ne` 適用 → Ind_{M'}^M θ irreducible、
     degree = [M:M']·1 = w₁、∈ inducedFamily M (= Sset)。
   - **crux = `∀ χ₂, chiRestrict χ₂ ≠ θ`**: `chiRestrict χ₂ = Res_K μ_0j` (column leader 制限,
     `:772`)。degree 論で discharge — j>0 で μ_0j(1)=d>1 ((10.3)) ゆえ degree-1 の θ と不一致;
     j=0 (trivial χ₂) の chiRestrict のみ degree 1 なので θ がそれと異なる事を別途確認 (μ_00 の特定要)。
   - **prereq**: 非自明 linear char of M' の存在 (M'/M''≠1、M' solvable≠1 ゆえ); μ_0j degrees の特定。
   - これで `CharacterParameters.zeta` が §6 由来の実データに。
   - **(10.3)**: w₂ prime = `theorem88_caseB_prime_orders` (`S12:622`, mp→Theorem88CaseBData);
     d/δ independence = columnFamily の degree-const (`columnFamily_difference_apply_one :468`) + (4.5.a)。
   - μ-grid (de-opaque `mu`/`alpha` 供給源) = `columnFamily` (`S06_CertainTypeCharacters:432`,
     `SignedIrreducibleDifferenceFamily L |W1|`) + `induce_omegaColumnDiff_mu_diff` (`S06_MuColumnBridge:44`)。
3. CharacterParameters de-opaque (self-contained field: zeta_irreducible/n_formula/alpha_formula) を
   producer signature 書換と一括で。
4. issue 1005 (hVti) / 1006 (hHall) discharge。

### ✅✅✅ (10.2) DONE (2026-06-20 cont.⁴): `exists_zeta_in_inducedFamily_degree_w1`

**Peterfalvi (10.2) を構成的に形式化完了** (`S12_MaximalIII_IV_V.lean`, axiom-clean, sorry-free, full
build 3870 green)。下の BREAKTHROUGH 通り、全 `Hypothesis L` (§6 bridge) で完結:
- helper `exists_nontrivial_linearIrreducibleCharacter` (非 perfect 群 → 非自明 linear char,
  Pontryagin `exists_apply_ne_one_of_hasEnoughRootsOfUnity` + abelianization, axiom-clean)。
- M' 非 perfect = M''<M' (TypePData `secondDerived_le_fitting`+`fitting_eq`+`fitting_lt_derived`)
  → `Group.IsPerfect.ofSurjective` で ↥h.K≅↥M' 転送。
- crux = (4.4) `certainType_zero_column_anchor` (μ_00=1_L) + `exists_certainType_zero_column_eq_of_
  subset_characterKernel` + `apply_eq_one_of_mem_commutator_of_apply_one_eq_one` + `columnFamily_mu_ne`。
- assembly = `induce_isIrreducible_of_forall_chiRestrict_ne` + `induce_apply_one` + `card_W1_eq_derived_index`。

⚠ **デバッグ知見**: `IsPerfect` は `namespace Group` 内 = `Group.IsPerfect` (import
`Mathlib.GroupTheory.IsPerfect`)。instance synth は `let h` の `↥h.K` を見抜けない → 明示
`↥((derivedInG M).subgroupOf M)` で `haveI` 登録要。`induce` の Invertible instance は
inducedFamily と同じ ambient (FiniteInduce) を使う (自前 haveI を作ると membership rfl 破綻)。
`commutator_def` は 2 名義あり曖昧 → `Group.IsPerfect.ofSurjective` 経由が clean。

**▶ 次の frontier 整理 (2026-06-20 cont.⁵)**:
- ✅ **`CharacterParameters.zeta_irreducible` de-opaque 済** (`250096bc`): opaque Prop → `IsIrreducibleCharacter zeta`
  (S15.Hypothesis 模範)。`exists_zeta_degree_w1` conclusion も実述語化。
- ⚠ **§10 producer chain は (8.8) に gate**: `CharacterParameters` は `w2_prime : hyp.w2.Prime` を
  **real field** として要求 ⟹ どの producer も w₂ prime なしに CharacterParameters を構成不可。
  w₂ prime = Peterfalvi (8.8) (type-II partner S with |S:[S,S]|=w₂)、`Theorem88CaseBData` は
  **case-B pair (S,T)** ゆえ単一 `Hypothesis M` から得られない (深い BG §16 構造)。
  ∴ exists_zeta_degree_w1 / w2_prime_and_parameter_independence は (8.8) 待ち。
  **私の standalone (10.2) `exists_zeta_in_inducedFamily_degree_w1` はこの gate を回避** (CharacterParameters 非経由)。
- **次の non-gated 候補**: (a) (10.3) within-column degree-const `μ_ij(1)=μ_0j(1)` を Hypothesis L で
  (columnFamily_difference_apply_one、小)。(b) μ-grid materialize (CharacterParameters.mu ← §6 columnFamily,
  W₂-dual ↔ Fin w₂ equiv 要、中)。(c) omegaSigma ← §5 bridge omegaSigmaGrid。
  **gated 本筋**: (8.8) w₂ prime → (10.3)-(10.6) → (10.8) keystone。(8.8) は BG §16 partner existence。

### ★ (8.8) gate 攻略 map (2026-06-20 cont.⁶, ユーザー選択「(8.8) 攻略」)

依存構造を精査 (S12 keystone chain + S14 (12.17)):
- **(8.8) case-(b) 存在 = `theorem88_caseB_holds` (Pf (12.17), `S14_MaximalI:308`, SORRY)** =「全 type-I は不可能」。
  Pf §12 ゆえ §10 結果に依存 (独立 counting path は無い)。
- **prime-orders chain** `theorem88_caseB_prime_orders` (S12:720) → `no_typeV_maximal` (S12:675) →
  **3 sorry に依存**: `w2_prime_and_parameter_independence` (10.3, S12:587) + `typeV_forces_coherence`
  (10.10.x, S12:659) + **`S_not_coherent` (10.8, S12:640)**。
- ⚠⚠ **訂正 (2026-06-20 原文 04.12 L77-90 精読)**: cont.⁶ の「(10.8) は standalone 証明可」は **誤り**。
  signature が `(hyp : Hypothesis M)` のみ ≠ proof が standalone。原文 (10.8) の証明本体が
  **Theorem (8.8) を直接 cite**:「By Theorem (8.8), there is a maximal subgroup S of Type II such that
  S∩M=W, S=[S,S]⋊W₂, C_{[S,S]}(W₂)=W₁」+ (7.5)/(7.8.b) counting + (8.11) Hall + (8.6.a) TI + (10.7)。
  ∴ **(10.8) は (8.8)=`theorem88_caseB_holds` (S14:308 SORRY, lane-f/BG §14) に gate**。(10.2) と違い回避不可。

**(10.8) S_not_coherent の証明** (Pf 原文 04.12 L77-): S coherent 仮定 → (8.8) で Type-II partner S 取得
→ G を G₀ (order prime to w₁, ∉Ã(M)) / G₁ に分割 → (7.5)+(7.8.b) counting + (10.6.b) `|ζ^τ₁(g)|≥1`
→ `w₁/|M'| ≥ 1 − |G₁|/|G| − 1/w₁` の不等式 → G₁⊆(H#)^G∪V^G (8.11/8.6.a/10.7) で |G₁|/|G| 評価 → 矛盾。
(⚠ 旧記載の「n²−n−1<0 が (10.8)」は誤り — それは (10.5) 内の補助矛盾。)

**真の §10 spine gating 構造** (3 gate、すべて lane-f BG §14 or §6 deep):
- (10.3) w₂ prime / (10.7)/(10.8) = **(8.8) Type-II partner** に gate (lane-f `theorem88_caseB_holds`)。
- (10.3) cross-column degree (μ_0j(1) indep of j, δ_j indep) = §5 σ-Galois ((3.9.b)) — §5 bridge は ✅ unconditional
  になった (issue 1005 closed) ので**発火可**。within-column (μ_ij(1) indep of i) = `columnFamily_difference_apply_one`
  (bare Hypothesis L) も発火可。
- μ-grid materialize = §6 bridge `typePData_toS06Hypothesis` 経由だが `hHall` (issue 1006) 待ち。
  **issue 1006 は lane-f κ-Hall cyclicity (`theoremA` SORRY / `typeP_duality`) に gate** と判明 (2026-06-20 調査)。

**∴ lane-b 単独で今 honest に積めるのは**: (a) §5 bridge unconditional 化 ✅ DONE (issue 1005)、
(b) (10.3) within-column degree (Hypothesis L, 小)、(c) (10.3) cross-column degree (§5 σ-Galois、要調査)。
**(10.8) 本体 + μ-grid + (10.3) w₂ prime は lane-f BG §14 ((8.8)/κ-Hall) 待ち** (cross-lane gate)。

---
### ★★★ BREAKTHROUGH (2026-06-20 cont.³, 原文 (8.15)+(4.4) 精読): **(10.2) は Hypothesis L で可、Hypothesis46 不要**

⚠⚠⚠ **下の cont.² の「Hypothesis46 が次の build target」は SUPERSEDED**。原文 (8.15) (Nougat 欠落 page を
PDF 復元) + (4.4) で判明:

- **(8.15) 原文**: 「M type-P, M'=[M,M] ⟹ Hyp (4.6) holds for **L=M, K=M', A=A(M), A_0=A_0(M)**, H=M_F or M_s」。
  ∴ §10 の (4.6) は **V=typePV, A_0=typePA0** (W\W2 ではない!)。§10 dadeData の support と一致 ⟹
  **A_0 不一致は誤診だった** (cont.² の dade0 transport 問題は消滅)。Lean `Hypothesis46.tic_V=W\W2` は
  §6/(6.8) 専用の特殊化で §10 には合わない ⟹ **§10 で Hypothesis46 は使わない**。
- **(4.4) 原文** (`04.6:35`, Lean `certainType_zero_column_anchor` `S06_CertainTypeCharacters:1013` +
  `exists_certainType_zero_column_eq_of_subset_characterKernel` `:1060`、**両方 Hypothesis L 上**):
  「μ_i0 (column 0) = K-trivial irreducibles、**δ_0=1, μ_00=1_L**」。K-trivial ⟺ column-0 ⟺ linear。

**⟹ (10.2) crux `∀χ₂, chiRestrict χ₂ ≠ θ` (θ=非自明 linear char of K) は Hypothesis L で完結**:
- χ₂=1: `chiRestrict 1 = Res_K μ_00 = Res_K 1_L = 1_K` ⟹ θ≠1_K (非自明) で回避。
- χ₂≠1: μ_0j は column-0 でない ⟹ (4.4) で K-trivial でない ⟹ linear でない (linear ⟹ K=[L,L]⊆ker ⟹
  K-trivial) ⟹ `chiRestrict χ₂ = Res_K μ_0j` degree = μ_0j(1) = d > 1 ≠ 1 = θ(1) で回避。
- degree 定数性 `columnFamily_difference_apply_one` も **Hypothesis L** (`S06_CertainTypeCharacters:468`)。

**⟹ (10.2) は §6 bridge (`typePData_toS06Hypothesis : S06.Hypothesis ↥M`) で形式化可。Hypothesis46 不要。**
残ステップ (全 Hypothesis L): (1) 非自明 linear char of K 存在 (K^ab=M'/M''≠1; `LinearCharacter.lean` API),
(2) crux 上記, (3) `induce_isIrreducible_of_forall_chiRestrict_ne` (S06_Clifford:902), (4) degree=w₁ + ∈Sset。
要 instance = `[NeZero (Nat.card W1)]`(`one_lt_card_W1`)/`[Fintype ↥M]`/`[Invertible (Nat.card ↥M:ℂ)]`/
`[Invertible (Nat.card ↥K:ℂ)]` (FiniteInduce)。**これが次の build。中規模 (~150 行) だが全 Hypothesis L で gate-free。**

---
### ★★ (旧 SUPERSEDED) (10.2) cont.²: Hypothesis46 が次の build target

§6 Clifford 機構の host を精査して判明 (`S06_CertainTypeClifford:365` `variable (h : Hypothesis L)`):
- **core Clifford (`columnFamily`/`chiRestrict`/`inertia_eq_K_of_forall_chiRestrict_ne`/
  `induce_isIrreducible_of_forall_chiRestrict_ne` `:902`) は bare `Hypothesis L` 上** ⟹ §6 bridge
  (`typePData_toS06Hypothesis : S06.Hypothesis ↥M`) で irreducibility step は発火可。要 instance =
  `[NeZero (Nat.card h.W1)]`(=`one_lt_card_W1`)/`[Fintype ↥M]`/`[Invertible (Nat.card ↥M:ℂ)]`/
  `[Invertible (Nat.card ↥K:ℂ)]` (FiniteInduce 供給)。
- **だが (10.2) crux `∀χ₂, chiRestrict χ₂ ≠ θ` は degree fact を要す**: counting 論 = K の非自明 linear char
  ≥2 個 (|M'/M''|≥3 odd) vs degree-1 chiRestrict ≤1 個 (χ₂=1 列のみ degree 1; χ₂≠1 は μ_0j(1)=d>1)。
  この「χ₂≠1 ⟹ μ_0j(1)>1」= `columnFamily_mu_apply_one_eq` (`S06_CertainTypeIsometry:961`, **Hypothesis46 上**)
  + (4.4) d>1。∴ **crux は Hypothesis46-level degree theory に gate**。

**⟹ 次 build target = `Hypothesis.toHypothesis46 : S06.Hypothesis46 (typePA0 M typeP) M`** (両 bridge 統合):
`Hypothesis46 extends CertainTypeHypothesis A L` + 追加 field (`S06_CertainHypothesis46:39`):
- `tic` = **§5 bridge の VARIANT (要新規)**: ⚠ `tic_V : tic.V = ↑W\↑W2` (= (4.3.a) 大 TI set),
  既存 `typePData_toTICyclicHypothesis` の `V := typePV = ↑W\(↑W1∪↑W2)` とは **不一致**
  (W1∩W2=⊥ ゆえ W1# 分だけ違う)。⟹ V=↑W\↑W2 版の §5 bridge を別途構成要 (V_ti = (4.3.a) ambient TI;
  §6 `isTISubset_sup_sdiff` の ambient 版)。既存 bridge (V=typePV) は A_0/Dade-support 用で流用不可。
- `tic_W1/tic_W2` = `(data.W1.subgroupOf M).map M.subtype = data.W1` (`map_subgroupOf_eq_of_le`, W1≤M)。
- `subH := K` (H=K=M' from (10.1)); `subH_normal`/`W2_le_subH`/`subH_le_K` = K facts (易)。
- `A_covers`: ∀h∈K#, x∈C_K(h)#, ↑x∈typePA0 — `typePA = centralizerSupport (sharpSubgroup M) (derivedInG M)`
  定義から (h∈M'#⊆M#, x∈C_{M'}(h) ⟹ x∈typePA)。要 centralizerSupport 定義確認。
- `dade0 : S04.Hypothesis G (A∪tic.V^L) M`: ⚠⚠ **tic.V=W\W2 ゆえ A∪tic.V^L = typePA0 ∪ (W\W2)^M ⊋ typePA0**
  (W\W2 ⊇ W1#、W1∩M'=⊥ ゆえ W1#-conj ∉ typePA0)。∴ **§10 dadeData.dade (typePA0 上) では不足** —
  §6 (4.6) の A₀ (W\W2-based) は §10 A_0(M) (typePV-based) と **別 support**。Peterfalvi (8.15)/(4.6) の
  A の取り方を精読して reconcile 要 (typePA0 と (4.6) A の関係)。**= 深い Dade bookkeeping、naive transport 不可**。
- `tau : FullDadeIsometryData dade0`: dade0 解決後。

**主リスク (改訂)** = **dade0 の support 不一致** (§10 typePV-A_0 vs §6 W\W2-A₀ の Peterfalvi 整合) が最重。
+ §5 bridge variant (V=W\W2) + A_covers。⟹ Hypothesis46 は「両 bridge の clean 統合」**ではなく**、
(4.6) の A/A₀ 定義を Peterfalvi 原文 (§8.15) で精読して §10 と橋渡しする deep construction。**要原文精読**。
完成すれば §6 全 apparatus (degree theory) が L=M 発火 ⟹ (10.2) crux counting + (10.3) が落ちる。

**代替 route (10.2 のみ)** = 商 M/M'' の Frobenius (`IsFrobeniusGroup.of_centralizer_kernel_le` で
centralizer_W1 から構成) + `isIrreducibleCharacter_induce_of_frobeniusGroup` + inflation 引き戻し。
Hypothesis46 を経ず (10.2) 単独可だが inflation/商 API 要。**Hypothesis46 が (10.3)/μ-grid も一括 unlock
ゆえ優先推奨**。
