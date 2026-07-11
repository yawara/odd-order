---
id: 1021
slug: typev-forces-coherence
title: "typeV_forces_coherence 実装 — (10.10.1)-(10.10.4) の §6-route (v2 方式で S12_Noncoherence に)"
created: 2026-07-11
---

# typeV_forces_coherence 実装 ((10.10) の残 genuine math)

**背景**: (10.10) 無条件版 (`no_typeV_maximal_unconditional`、S12_Noncoherence) の唯一の
sorryAx 残渣 = `typeV_forces_coherence` (S12_MaximalIII_IV_V:~1650、bare sorry)。
book (10.10) の「type V なら 𝒮 coherent」((10.8) との矛盾用)。

## 設計 findings (2026-07-11 tick¹⁵ survey)

- **(8.7)-trichotomy は TypeVData.alternative field に忠実に在る**
  (MaximalSubgroupType:287-296): (a) H# TI / (b) ∃p: w₁|p−1 + O_{p'}(H) cyclic /
  (c) |O_p(H)| = p³ + w₁|p+1 + O_{p'}(H) cyclic。
- **H は data-独立** (H_eq = maxNilpotentNormalHall) なので dV↔hyp.typeP の
  trichotomy 転送は card/H-invariance で clean。type V は U = ⊥ → M' = H。
- **book の場合分け**: (a) → (6.8) で coherent / (b) → (6.5.c) で coherent /
  (c) → (10.10.1)-(10.10.4) + (10.9) で **False** (exfalso → coherent)。
- ⚠ **S14-(12.6) template は Frobenius-特化** (`nonempty_coherent_SOf_bot_of_index_dvd`
  は hF : IsFrobeniusGroup ↥L H C を要求) — type V の M = H⋊W₁ は Frobenius で
  ない (C_H(w) = W₂ ≠ 1)。book は **Hypothesis (6.4)** route ((8.15): (6.4) holds for
  (L,K,M) := (M, M', 1))。⟹ S08 の (6.4)-side engine ((6.5.b)/(6.5.c) の
  Hypothesis-(6.4) 版) を survey して使う (次 tick)。
- **配置 = S12_Noncoherence** (v2 方式): 原 sorry の home (S12_MaximalIII_IV_V) は
  (11.x)/(6.x) 消費機構の上流 (S13_Lemmas113To115 は下流) — 同じ mis-layering。
  原 sorry には superseded 警告を付け、v2 が消費する。
- (c)-refutation は (10.9) (`S12_Prop109` 系?) + μ-算術 — 最深部、別 sub-issue 可。

## 手順
1. S08 の (6.4)-Hypothesis side engines survey ((6.5.b)/(6.5.c)/(6.8) interfaces)。
2. S12_Noncoherence に typeV branch (a)/(b) 実装。
3. (c)-refutation ((10.10.1)-(10.10.4)、(10.9) 消費)。
4. no_typeV_maximal_unconditional を新版に配線 → sorryAx-free 化。

## 2026-07-11 tick¹⁶ — 部品 survey 完了 + transfer lemma landed

- `TypeVData.alternative_transfer` landed (MaximalBasic、axiom-clean 見込み) —
  (8.7)-trichotomy を hyp.typeP へ転送。
- **case-(a) 設計確定**: SibleyDadeHypothesis は **H#-TI が field** → (a) 専用。
  組立部品: split = M_complement (U=⊥ で M' = H)、dade = S04.Hypothesis.of_isTISubset
  (S09_FrobeniusSibley の sibleyDadeHypothesis_of_frobenius が producer template、
  ただし cases-branch は Frobenius でなく **h46-certain-type** 側 —
  certainTypeHypothesis_of_typeP_kappaHall (FTS:1160) で構成)。
  出力の transport: 家族差分は (M')# = H#-supported (type V) なので
  `isCoherent_of_supportedSpan_le` (S13_Lemmas113To115:318) で A₀ 版へ。
  tau-agreement は S04.restrict 系。
- **case (b)**: (6.4)-general の (6.5.c) — SibleyDade (TI) 外。候補 =
  (11.4)/(11.5) filtration route (S13_Lemmas113To115、type II/III/IV 向けに proven —
  type V 適用可否の確認が次) or S08_SixTwoGeneral の非-TI 形。
- **case (c)**: (10.10.1)-(10.10.4) + (10.9) refutation — 最深、最後。

## 2026-07-11 tick¹⁷ — case-(a) 供給連鎖の完全 map (残る設計点 1 つ)

- **h46 producer 発見**: `Hypothesis.toHypothesis46` (S12_Core:1057、hyp 自身の完全 (4.6)!)。
  type V では typePA = ⋃_{x∈H#}C_{M'}(x)# = **H#** (M' = H) なので A-param も一致。
  side conditions: W₂ prime = w2_prime ✓ / W₂ ≤ [H,H] = W2_le (≤ secondDerived) ✓ /
  coprime = hall ✓。K = H ✓ (M' = H)。
- **SibleyDade 組立部品**: split = M_complement (U=⊥) / dade = S04.of_isTISubset
  ((a)-TI から、H a = ⊥ ✓ dade_H_eq_bot) / S_eq = inducedFamily 同定 /
  cases = Or.inr ⟨toHypothesis46, …⟩。
- **⚠ 残る設計点**: `h46.dade = dade` field — toHypothesis46.dade は A₀-Dade の
  restrict (H(a) = 継承 signalizer、⊥ とは限らない) vs TI-構成 dade (H ≡ ⊥)。
  同定には dadeHypothesis_eq_of_forall_H_eq_bot (9079 part 1、両側 H≡⊥ 要) —
  つまり **hyp.dadeData の H(a) が type-V-case-(a) で ⊥ かは data 依存**。
  解決候補: (i) hyp.dadeData 構築 (exists_hypothesis_of_typeIIIorIVorV、axiom-clean!)
  の H(a)-fields を実測 — (8.15)-構成が type V/case-(a) で ⊥ を選んでいれば同定可;
  (ii) さもなくば Sibley 側を h46.dade ベースで組む (dade_H_eq_bot を h46 側から) —
  case-(a) の TI が R(a) = 1 を強制する事実 ((2.3)-route) を経由。
- 出力 transport: isCoherent_of_supportedSpan_le + S_eq→inducedFamily ✓ (前 tick 済)。

## tick¹⁸ 測定 pointer
dadeData 供給 = `S10.dadeSupportHypothesisData_typePA0_of_isTypeP1` (Nonempty-producer)。
h46.dade 同定の実測 = この producer の H(a)-choice を読む (S10 側 (8.15)-構成)。
type-P₂ branch は sorried と注記あり — type-V (P₁) 側は生きている。次 tick はここから。

## 2026-07-11 tick¹⁹ — ★設計点解消 (data-independent)、(2.3) 逆方向 landed

- **producer 実測** (参考): engine = `dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`
  (S10:1608)、H := `ftSupportKernel M X` = escaping なら `FT_signalizer a`、
  non-escaping なら ⊥。つまり「H(a)=⊥ ⟺ C_G(a) ≤ M」。
- **しかし実測は不要になった**: `S04.Hypothesis.H_eq_bot_of_centralizer_le` /
  `H_eq_bot_of_isTISubset` landed (S04_DadeIsometryBasic、commit 5c946ed5)。
  centralizer_eq_sup + centralizer_disjoint だけから **任意の** (2.2) datum で
  C_G(a) ≤ L → H(a) = ⊥。⟹ case-(a) TI から h46.dade の H ≡ ⊥ が opaque な
  hyp.dadeData のまま出る。**SibleyDadeHypothesis の dade field に h46.dade
  自身を渡す**: `dade_H_eq_bot` = 新 lemma、`cases` の `h46.dade = dade` = **rfl**。
  TI-側 S04.of_isTISubset 構成も dadeHypothesis_eq_of_forall_H_eq_bot も不要。
- **⚠ TI の相対先**: TypeVData.alternative (a) =
  `IsTISubset (sharpSubgroup typeP.H) (normalizer (typeP.H :Set G))` — **N_G(H) 相対**。
  M-相対へは `IsTISubset.mono` でなく N_G(H) = M の同定 (H = M' ≠ 1 normal、M maximal、
  M ≤ N_G(H) ≠ G) → 既存 lemma を探す (S09 系に必ずある)。+ A-param 座標合わせ
  (sharpSubgroup typeP.H : Set G / sharpImage (H:Subgroup ↥M) / typePA)。
- **book (10.10) 場合分けの訂正** (本 issue 冒頭記載を修正; mmd 04.12 L113):
  case (c) は False でなく **(10.10.1)–(10.10.4) が honest に coherent を結論**。
  not-(a) は trichotomy の (b)/(c) 直行でなく: (8.4.d)+(8.15) → **Hyp (6.4) for
  (L,K,M):=(M,H,1)** → **(6.5.b)** で「H non-abelian p-group (p=w₂) でなければ
  coherent」→ **(6.5.c)** が case (b) を排除 → case (c) のみ残り |H|=p³。
  ⟹ 実装も (b) を個別に扱わず (6.4)-engine 側で潰すのが book-faithful。
- **(6.8) capstone 確認**: `sibleySetup_is_coherent` (S08_CoherenceTheorems:52) は
  **完成済 (sorry 無)** : hyp.CoherenceTarget。case-(a) は
  ① SibleyDadeHypothesis 構成 (座標合わせ + h46 = toHypothesis46) →
  ② capstone → ③ transport (tau-agreement (S04.restrict 系) +
  isCoherent_of_supportedSpan_le + Sset=inducedFamily 同定) の 3 段。
- 次 tick: `toHypothesis46` (S12_Core:1057) の実 signature 読解 → ① の座標合わせ
  (L=M、H : Subgroup ↥M、A-param) を開始。

## 2026-07-11 tick²⁰ — 座標層 landed (S12_TypeVSibley 新 leaf、commit 955b03a8)

- `toHypothesis46` 実読 (S12_Core/Hypothesis.lean:1312): 出力 =
  `S06.Hypothesis46 (typePA M hyp.typeP) M`、dade = `hyp.dadeData.dade.restrict`
  (A₀→A)、dade0 = dadeData.dade そのもの、tau = fullDadeIsometryData。
- **新 leaf S12_TypeVSibley** (S10_MinimalSimpleBasic + S08_YsetInner import):
  `TypeVData.derivedInG_eq_H` (M'=M_F=data.H、任意 witness) /
  `sharpImage_subgroupOf_derivedInG` / `normalizer_sharpSubgroup` (N(H^#)=N(H)) /
  `normalizer_sharpSubgroup_derivedInG_eq` (N((M')^#)=M) /
  `typePA_isTISubset_of_typeV_TI` (M-相対 TI)。全部 sorry-free。
- **次 tick (assembly ①)**: SibleyDadeHypothesis G M ((derivedInG M).subgroupOf M) の
  構成。残 field 素材: W1 = typeP.W1.subgroupOf M / split = M_complement /
  H_normal = commutator normal (toS06 の K_normal 流用) / H_ne_bot = W2 経由 /
  H_nilpotent = M_F nilpotent (maxNilpotentNormalHall) を subgroupOfEquivOfLe で
  ↥H_M に transport / H_sharp_ti = tick²⁰ lemma + sharpImage 座標 rw /
  dade = **A-param transport が必要**: toHypothesis46 は typePA-座標 →
  sharpImage-座標へ。方針 = S04.Hypothesis.restrict を equality-subset で使う
  (restrict hAB.le: Hypothesis G A M → Hypothesis G B M、H-field は値レベル
  reindex、Eq.rec 無し)。Hypothesis46 全体の congr helper も同様に
  restrict + A-indep fields 再梱包で作る (data field は dade/toHypothesis.dade
  のみ、A_covers は Prop なので ▸ 可)。cases の h46.dade = dade は
  「Sibley.dade := (congr した h46).dade」にすれば rfl。
- dade_H_eq_bot = S04.Hypothesis.H_eq_bot_of_isTISubset (tick¹⁹) ✓ /
  hconj = HConjInvariant.of_forall_H_eq_bot ✓ / w₂ prime = hyp.w2_prime ✓ /
  W2 ≤ ⁅H_M,H_M⁆ = W2_le→secondDerived を subgroupOf へ ✓ /
  coprime = typePData_W1_hall_coprime ✓。

## 2026-07-11 tick²¹ — ★assembly ① 完成: typeVSibleyDadeHypothesis (sorry-free)

- **`typeVSibleyDadeHypothesis` landed** (S12_TypeVSibley、commit 4c8af378):
  型 V + (8.7)(a) TI → `SibleyDadeHypothesis G M ((M').subgroupOf M)` 全 field
  実構成。dade = castSet(toHypothesis46).dade で **cases の h46.dade = dade は
  rfl** (tick¹⁹ 設計実証)。**S := inducedFamily M (= hyp.Sset 定義一致)** —
  case-(a) 出力の family 同定 (transport ③ の一部) が不要になった。
- **⚠ instance 教訓**: consumer は [Finite G] のみ + `open scoped FiniteInduce in`
  (S12_Core/Hypothesis.lean:25-41 の 4 scoped instances)。[Fintype G] や
  [Invertible …] を binder に取ると toHypothesis46 の出力型と diamond →
  "synthesized instance not defeq"。Isometry105 の signature が正パターン。
- **⚠ 衝突事故と修正** (commit 67784bdd): tick¹⁹ の S04 追加が
  S06_CertainTypeFourCorner:241 の同名 `_root_` 宣言 (同一 statement) と衝突
  — leaf build では不可視の latent full-build 破壊だった。S06 側を削除して
  S04 (topic home) に一本化。**教訓: namespace 追加宣言の前に repo-wide grep
  必須** (claim-before-build の局所版)。
- **残り (case (a) 完結まで)**:
  1. `sibleySetup_is_coherent (typeVSibleyDadeHypothesis …)` を適用 →
     `IsCoherent (Sibley.tau) (inducedFamily M) (supportInSubgroup (sharpImage H_M) M)`。
  2. **tau-agreement**: Sibley.tau = dadeIntegralCharacterMap (casted h46.dade)
     vs hyp.tau = dadeIntegralCharacterMap hyp.dadeData.dade (A₀-full)。
     A-supported 元上の一致 = (2.11) restriction 系 (S04.restrict + IsDadeMap
     uniqueness、dadeMap_unique_of_forall_H_eq_bot も使える — 両者 H≡⊥!)。
  3. **support 拡大**: supportInSubgroup (sharpImage) → hyp.A0 =
     supportInSubgroup (typePA0)。A ⊆ A₀ (union-left)。
     `isCoherent_of_supportedSpan_le` (S13_Lemmas113To115:318) — **DAG 注意**:
     S13 は S12 下流。v2 の配線先 S12_Noncoherence の import に S13 が既に
     あるか要確認 (無ければ transport は S13 側 or 新 mid-leaf)。
  4. その後: not-(a) route ((6.4)+(6.5.b)/(6.5.c) engine survey) → case (c)
     ((10.10.1)-(10.10.4) grid、最深)。

## 2026-07-11 tick²² — transport 設計確定 (cast-elim 不要、uniqueness hammer 経由)

既存 API 調査の結果、case-(a) transport は全部品既存で組める:

- **congrMap**: `S07.IsCoherent.congrMap` (S08_CaseBCoherence2:1084) —
  τ₁-coherence + lattice 上の τ₁=τ₂ → τ₂-coherence。
- **(2.11) restrict 一致**: `dadeIntegralCharacterMap_restrict_eq_of_support`
  (同:1138) — dadeICM(restrict) φ = dadeICM(full) φ (A₁-supported φ)。
  A := typePA0、A₁ := sharpImage H_M で hyp.tau 側に直接適用可。
- **tau-agreement の cast seam 解消**: sib.tau (castSet 経由の dade) vs
  restrict-直の dade — **cast-elim lemma 不要**。両者とも
  (sharpImage H_M, M) 上の Hypothesis で **H ≡ ⊥** (H_eq_bot_of_isTISubset、
  data-independent) ⟹ `dadeMap_unique_of_forall_H_eq_bot` (S12_TICyclicSigmaBridge:70、
  (2.5)-uniqueness、**異なる hyp 梱包でも同 (A,L) なら DadeMap 等しい**) で
  同一視。手順: dadeICM_apply_of_support で両辺を .toDadeMap 値に落とす →
  hammer で map 等式 → congrArg。
- **support 拡大 A→A₀**: `isCoherent_of_supportedSpan_le` (S13_Lemmas113To115:318)。
  hle (ℤ[S,A₀] ⊆ ℤ[S,A_sharp]) は「Ind_{M'}^M θ は M'-set 外で 0」+
  「1 ∉ A₀ (hyp.one_notMem_A0)」— S13:367-387 の columnSum 版 proof を
  inducedFamily 版 (induce の off-M' 消滅 lemma) で mirror。witness = 任意
  ζ ∈ S の ζ̄ − ζ (S13:436-453 の inducedKernelFamily 版 mirror;
  mderivSharp_subset_A0 ✓ 既存)。
- **§10 interface 実例**: `certainTypeSet_isCoherent_A0` (S13:349) が 𝒯-版の
  完全 template (そこは dade0-経由で seam 無し; S-版の私の経路は seam 有りで
  上記 hammer を挟む点だけ違う)。
- **確定 signature** (次 tick 即用):
  `SibleyDadeHypothesis.tau` = abbrev、`dadeICM hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)`
  (S08_YsetConjugation:37) / `CoherenceTarget` = abbrev `IsCoherent hyp.tau hyp.S
  (supportInSubgroup (sharpImage H) L)` (同:45) / S12 `Hypothesis.tau` =
  `dadeICM hyp.dadeData.dade (….fullDadeIsometryData hyp.hconj)` (S12_Core/Hypothesis:375) —
  **両 tau は同形 (dade だけ違う)** / `dadeIntegralCharacterMap` +
  `dadeIntegralCharacterMap_apply_of_support` = S07_Coherence/FamilyBundleDade:320/330。
## 2026-07-11 tick²⁴ — ★★ case-(a) 完全証明: typeV_caseA_coherence (commit 6e4800d5)

- `typeV_caseA_coherence` (S13_Lemmas113To115 末尾、sorry-free):
  型 V + (8.7)(a) TI → `IsCoherent hyp.tau hyp.Sset hyp.A0`。
  組立 = capstone → congrMap (tau_agree) → supportedSpan_le (witness ζ̄−ζ)。
  inducedKernelFamily の ⊥-kernel membership + one_mem_characterKernel で
  witness 部品を全流用 (S13:436-453 mirror)。
- **(10.10) case-(a) はこれで book-faithful に閉じた**。tick¹⁵ 起点の設計
  (v2 方式・S12_Noncoherence 配線) の case-(a) 供給が完成。
- 残り: **not-(a) 縮約** ((8.4.d)+(8.15) → Hyp (6.4) for (M,H,1) → (6.5.b) で
  「H non-abelian p-group (p=w₂) でなければ coherent」→ (6.5.c) が case (b)
  排除) と **case (c)** ((10.10.1)-(10.10.4)、typeV_param_arithmetic ✓済 +
  grid 組立)。次 tick: S08 の (6.4)/(6.5.b)/(6.5.c) engine の Lean 所在 survey
  (six_five_* 断片は S08_CoherenceCorePart1/PGroupReduction に確認済み — 
  Hypothesis (6.4) carrier の有無と (6.5.b)/(6.5.c) の statement 形を特定)。
- v2 配線 (typeV_forces_coherence_v2 @ S12_Noncoherence) は 3 分岐が揃って
  から: case-(a) は本 lemma + dV.alternative_transfer の Or.inl で接続。

## 2026-07-11 tick²³ — tau-agreement landed (commit 6880c3e6)

- `dadeIntegralCharacterMap_eq_of_forall_H_eq_bot` ((2.5) integral-map 版、
  梱包差全吸収) + `typeVSibleyDadeHypothesis_tau_agree` (Sibley τ = hyp.tau
  on (M')^#-supported) — 両方 sorry-free、S12_TypeVSibley (今 ~370 行)。
- import 追加: S12_TICyclicSigmaBridge (uniqueness hammer) +
  S08_CaseBCoherence2 (congrMap + restrict_eq_of_support)。
- **case-(a) 残り = 最終組立のみ**: c0 := sibleySetup_is_coherent
  (typeVSibleyDadeHypothesis …) : IsCoherent sib.tau (inducedFamily M) A_sharp
  → .congrMap (tau_agree、zSupportedSpan 元は mem_supportedSubmodule 経由で
  support ⊆ 条件へ) → IsCoherent hyp.tau (inducedFamily M) A_sharp
  → isCoherent_of_supportedSpan_le (hle = 「Ind は M'-set 外 0」+ one_notMem_A0、
  witness = ζ̄−ζ) → IsCoherent hyp.tau hyp.Sset hyp.A0 (Sset=inducedFamily rfl、
  A0 = supportInSubgroup typePA0 rfl)。配置は S13_Lemmas113To115 (S12_TypeVSibley
  を import 追加、supportedSpan_le がそこ在住) → v2 は S12_Noncoherence が S13 を
  import できるか次第。
- 部品検索残: 「Ind_{H}^{M} θ の support ⊆ H-set」lemma (induce の外部消滅) と
  Sset 非空 (exists_zeta_in_inducedFamily_degree_w1 S12_Core:1376 ✓) +
  ζ̄−ζ ≠ 0 (odd order no real char) + conj-closure (inducedFamily_closedUnderConjugate
  S12_Core:61 ✓) + conjDiff support (inducedKernelFamily_conjDiff_support 系 or
  mderivSharp_subset_A0 経由)。

- **DAG**: S12_Noncoherence は S12_TypeIICrossIsometryPair + S14 を import —
  S13_Lemmas113To115 は import して**いない**。transport ③ を書く場所:
  S13_Lemmas113To115 は S12_TypeVSibley を import できるか? (S13 ← S12_Core
  経由で S12_TypeVSibley と独立 → S13 に置くのは可だが、v2 の配線先
  S12_Noncoherence が S13 を import する必要が生じる)。**代替: transport を
  S12_TypeVSibley に置き、isCoherent_of_supportedSpan_le だけ S13 から
  S12_TypeVSibley へは import 不可 (S13 が下流) → supportedSpan_le の一般
  lemma は S13:318 のものを S07-side へ hoist するか、S12_TypeVSibley で
  同型を再宣言せず S13 に最終組立 lemma を置く**。→ 次 tick: S13 の import
  チェーン確認後、最終組立 (typeV_caseA_coherence) は S13_Lemmas113To115 か
  新 leaf (S13 直下) に配置、v2 (S12_Noncoherence) の import に追加。
