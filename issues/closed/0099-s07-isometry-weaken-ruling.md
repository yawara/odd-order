---
id: 99
slug: s07-isometry-weaken-ruling
title: "HUB 裁定: S07 tau_isometry_diff を zSupportedSpan 形へ in-place 弱化 (Option A、owner=b、mixed-degree ブロッカー解消)"
created: 2026-07-07
---

# HUB 裁定: S07 `tau_isometry_diff` を zSupportedSpan 形へ in-place 弱化

## 背景

lane-a flag (issue 1019 update⁵⁵、2026-07-07): `S07.Hypothesis` の `tau_isometry_diff`
(**S07_Coherence.lean:1777**、S07_Subcoherent でなく — 調査で位置訂正) が**全 member 差分**の isometry を要求
→ mixed-degree family では honest Dade map に対し**偽** (deg a ≠ deg b の a−b は A-supported でない) →
S07.Hypothesis が mixed family で **uninstantiable** → **(9.11) non-Galois mixed extension が構造的にブロック**
(a の Pf 11.8 hY route = FT critical path、b の §13 mixed consumer にも波及)。

hub 調査 = workflow wf_4f8e7eca (2 agent: Coq interface trace / Lean consumer census)。

## 調査確定事実

- **Coq interface**: `subcoherent` clause (b) = `{in 'Z[S, L^#], isometry tau}` (PFsection5.v:488) —
  isometry は **degree-0 / L^#-supported sublattice のみ**。全差分 isometry は Coq 開発全体に**存在しない**。
  Dade 側の供給は A-supportedness 経由 (`prDade_subcoherent` の defSA step、PFsection5.v:701-710)。
- **全 extension 機構が L^#-restricted form のみ消費**: (5.4) subcoherent_norm / (5.6) extend_coherent
  (divisibility で χ − a·ξ₁ を degree-0 化) / (5.6.3) / (5.7) uniform_degree_coherence (等次数仮定が
  生差分を degree-0 にする**まさにその箇所**) / (5.9a)。**Coq (9.11)** `Ptype_core_coherence`
  (PFsection9.v:1484) は q·a 次数 S1 に q·u≠q·a 次数 S3 を接ぐ**真の mixed 拡張**をこの interface だけで実行。
- **Lean census**: instantiation 4 site (S14:4032 / S14:4131 / S15_SAndT_Setup:1393 / S16:1048 T_typeIII_hyp07)
  は**全て equal-degree** で、弱 field を既存 brick `dadeIntegralCharacterMap_inner_eq_on_supported_span`
  (S07_Coherence.lean:5533) で**無条件に** discharge 可能 (mixed family 含む)。consumer 4 箇所
  (S07_CoherenceConstantDegree:210/460/613 + S07_Subcoherent:168 irrSubcoherent) は**全て A-supported 差分のみ**使用。
- **強 field ⇏ 弱 field**: member 差分 isometry は non-difference degree-0 combo (q·a − q'·b, χ − a·χ₁) を
  制御しない。∴ Option B (並行弱構造) は forgetful map 無し → **A の全 consumer 作業 + 構造重複**に退化。
- mixed 接続 engine (`retarget_isCoherent_of_decompositions` S07_Coherence:4141 / `coherentPairChain` :5033)
  は既に Hypothesis-free で、scaled degree-0 combo を扱う = **弱化後の形が (9.11) non-Galois route の
  native な要求**。

## 裁定 (Option A)

**`tau_isometry_diff` を in-place で Coq-faithful に弱化**:

```
tau_isometry_diff : ∀ φ ψ, φ ∈ zSupportedSpan S A → ψ ∈ zSupportedSpan S A →
    ClassFunction.inner (tau φ) (tau ψ) = ClassFunction.inner φ ψ
```

(zSupportedSpan 形 = `{f ∈ zSpan S | support ⊆ A}`、S07_Coherence.lean:44-46。
**equal-degree 差分形への弱化では不足** — (5.6)/(5.9a) 型 consumer は weighted combo を要する。)

- **owner = lane b** (対象 6 file 中 5 が b 所有: S07_Coherence / S07_CoherenceConstantDegree /
  S07_Subcoherent / S14_MaximalI / S15_SAndT_Setup)。**9013 案A より優先 insert 推奨** — 機械的 ~1 session で
  a の critical path (11.8 hY) と b 自身の §13 mixed consumer を同時 unblock する最上流工事。
- **c の分担**: S16_NonExistenceG:1048 (T_typeIII_hyp07) の instantiation-lambda swap 1 箇所 (b landing 後に cite 修正)。
- 実装 sketch (census 詳細は wf_4f8e7eca): field 差し替え (~3 行+docstring) → S07_CoherenceConstantDegree の
  ~11 lemma chain に `hsuppdiff` threading (`coherent_of_constant_degree` の外部 signature **不変** —
  hsuppdiff は既に引数) → irrSubcoherent に hconjsupp 引数 1 本 → 4 instantiation の lambda swap。
  既存 per-site witness lemma (Sset_tau_isometry_diff 等) は standalone fact として温存。
- **併せて裁定 (a/b 並行構築 dup)**: a の S12 `inducedFamily_degreeSubfamily_isCoherent` と b の S15
  `sSetIrrDeg_subcoherent` は**両方 keep** (family が異なり両方 genuine — 成果保全原則)。family-parameterized
  一般化は optional follow-up (どちらかが (9.11) 本体で必要になった時点で)。a の claim-before-build miss は
  自己申告済み、是正不要。

## 完了条件

- [x] b が S07_Coherence.lean:1777 の field を zSupportedSpan 形に弱化 + consumer threading (build green)
- [x] 4 instantiation site の discharge を弱 field 経由に swap (S14×2/S15 = b、S16 = c)
- [x] a の (9.11) mixed route が S07.Hypothesis を mixed family で組めることを確認 (1019 側で検証)
      → **検証完了 (2026-07-07 lane a、下記「検証記録」)**

## 検証記録 (lane a、2026-07-07)

**問い**: S07.Hypothesis を mixed family (`SOf(H0Cprime)` ∋ reducible μ_j) で組めるか。

**答え: literal には NO (第二の field 障害)、しかし (9.11) port には literal mixed 組立は不要 —
route は前進可能で、0099 弱化はそのために必要十分だった。**

1. **第二の field 障害 (norm 論法)**: `CharacterDifferenceImage` (S07_Coherence:395) は
   `τ(χ−χ̄) = ε(μ−ν)` (μ,ν 既約ちょうど 2 個、‖image‖²=2) を固定。reducible μ_j
   (‖μ_j‖² ≥ 2) では isometry (0099 弱形が適用可: μ_j−μ̄_j は degree-0 で A0-supported) から
   ‖τ(μ_j−μ̄_j)‖² = 2‖μ_j‖² ≥ 4 ≠ 2 → `difference_image` field が **unconstructible**
   (2032/frobI 型の偽 field)。μ_j ∈ S_H0C ⊆ S_H0C' は non-Galois で実在 (Coq 9.5/9.8) ゆえ
   family は genuinely mixed。∴ S07.Hypothesis の literal mixed 組立は 0099 後も不可。
2. **Coq 対比**: Coq subcoherent clause (d) (PFsection5.v:486-494) の R ξ は**可変長** orthonormal
   seq (`tau (xi − xi^*) = Σ_{α∈R ξ} α`) で 2-element は既約特殊化。(5.4)/(5.6)/(5.7) は可変長を
   本質使用 (R-span 直交分解・zchar_expansion・subseq 選択)。(9.11) の induction step は
   `extend_coherent` (5.6) 一本で **chi の既約性を使わない** (reducible μ_j も同機構で adjoin、
   PFsection9.v:1658-1667 の `apply: (extend_coherent scohS0 ...)`)。
3. **Lean の可変長対応物は既存**: `CharacterPsiDecomposition.imageFamily` (S07_Coherence) が
   Coq R ξ 相当 (orthonormal family、`ofProjection` producer)。`xAdjoinStepW`
   (S08_CoherenceWeighted:287) は S₁-side member に reducible (mc i = ‖·‖² > 1) を許し
   `Dmem : CharacterPsiDecomposition` で R-datum を受ける設計済み — docstring 明記
   「a non-anchor member may be a reducible certain-type column μⱼ」。
4. **∴ (9.11) Lean-native 組立** (S07.Hypothesis の mixed 組立を経由しない):
   base = deg-qa irreducible subfamily の coherence (S07.Hypothesis は irreducible family で組める、
   0099 弱形 isometry で discharge) → extension = Hypothesis-free adjoin
   (irreducible: xAdjoinStepW 現形 / **reducible μ_j: xAdjoinStepW の χ-既約性を外した一般化が
   missing piece** — S08_CoherenceWeighted = **lane a 所有** [b の coherence 例外 glob は
   `S07_Coherence*`+`S08_PGroupReduction` のみ、merge_monitor 🔒] ゆえ a が直接 build) + μ_j の
   CharacterPsiDecomposition 供給 (σ-image family、S12 muGrid infra = a)。
   **全 missing pieces が lane a 圏** (S07_Coherence [b] は既存 def の cite のみ、構造変更不要)。
5. **S07.Hypothesis の可変長 R-datum 化 (Coq-faithful subcoherent) は (9.11) に不要**ゆえ本 issue
   では起こさない (将来 (5.4)/(5.6) の direct port が要る場面が来たら別 issue で設計)。

⟹ 本 issue の完了条件は全て充足 → **closed 移行可** (hub 合流 tick にて)。

## 実施記録 (lane b、2026-07-07)

- **field 弱化 + 供給 brick**: `tau_isometry_diff` を zSupportedSpan 形へ in-place 弱化
  (S07_Coherence)。派生補題 `Hypothesis.tau_isometry_memberDiff` (旧 member-差分形、support
  引数 2 本付き) と **pair-form brick `dadeIntegralCharacterMap_inner_eq_of_supported`**
  (支持条件 2 本だけで無条件供給 — mixed family 含む) を追加。
- **(5.7) chain threading**: S07_CoherenceConstantDegree の 11 declarations
  (pairDecomp / pairDecomp' / pairDecomp'_image / commonImage / pairDecomp'_two_sided /
  commonImage_self / _inner_ref / _inner_conj / _inner_refconj / _inner_other / _inner) に
  `hsuppdiff` を threading。`coherent_of_constant_degree` の外部 signature は**不変** (裁定通り)。
- **irrSubcoherent**: hiso を弱形へ + `hconjsupp` 引数 1 本 (共役差分の A-支持)。
  `Hypothesis.restrict` は `zSupportedSpan_mono_left` 経由に。
- **4 instantiation site swap 完了**: S14:2 site + S15 sSetIrrDeg_subcoherent + **S16
  T_typeIII_hyp07 (c 分担分)**。⚠ S16 分は裁定で c 割当だが、field 変更と原子的でないと
  build が壊れるため **b が同 commit で機械的 lambda swap のみ実施** (3 行、設計内容ゼロ、
  `hdiff_supp`+pair brick 経由)。c は次回 sync 時に review し、必要なら自所有の形に調整可。
  witness lemma (Sset_tau_isometry_diff / SsubFiltration_commutator_tau_isometry_diff /
  tSideDadeMap_isometry_diff) は裁定通り standalone fact として温存。
- 検証: full build green (3934 jobs、clean rebuild 5m03s)、sorry 数 78 = 78 (regression なし)、
  AxiomsCheck 全 OK。mixed-degree family での S07.Hypothesis 組立てが構造的に可能になった
  (a の 1019 検証待ち → 最後の checkbox)。

## 参照

- 調査 = workflow wf_4f8e7eca-b3b (coq:subcoherent-interface / lean:s07-consumer-census)、2026-07-07
- issues/1019 update⁵⁵ (a の flag)、issues/0098 (レーン再点検)、coq/theories/PFsection5.v:486-494・PFsection9.v:1484

## HUB 追認 (2026-07-07 合流 tick)

b による S16_NonExistenceG:T_typeIII_hyp07 の instantiation-lambda swap (裁定では c 分担) を
**非逸脱として追認**: (i) 0099 裁定の実質範囲内 (work item 自体は裁定済、executor のみ変更)、
(ii) field 弱化と atomic でないと build が壊れる必要性が genuine、(iii) 機械的 3 行 swap のみで
新宣言・設計内容ゼロ、(iv) issue で self-flag 済み。c は次回 sync 時に review し自所有の形に調整可
(調整不要ならそのまま)。merge = 57887d84。
