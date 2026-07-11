---
id: 9083
slug: lane-a-1007-decomp-moot-revised-frontier
title: "HUB: (10.7) 3 分解は pair で完了済と判明 (9082 承認 plan の moot 化) — 改訂 frontier 提案"
created: 2026-07-11
---

# HUB: (10.7) 3 分解は pair で完了済と判明 (9082 承認 plan の moot 化) — 改訂 frontier 提案

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 経緯

9082 の hub 承認 (③→①→②) の**直後の precision survey で前提が覆った**:
`exists_typeIICrossIsometryData_at_pair` (S12_TypeIICrossIsometryPair:1345) が
③①② を**全て sorry-free で実装済み**。critical path
(S_not_coherent_unconditional → typeII_HU_frobenius_of_coherent' → at_pair) は
これを消費 (S_not_coherent_unconditional の axiom-clean assert 通過と整合)。
base 非交差は (8.13.c4) not-Frobenius でなく **σ-route**
(typeP_pair_core_order_coprime → sigma_disjoint_of_nonconjugate)。

⟹ **9082 承認 plan は対象消滅 (moot)**。S10 additive 条件・9079/② 注意は
該当作業ごと不要に。

## hub への cleanup 裁定依頼 (急がない)

superseded sorry 3 兄弟の keep/delete/退役方式:
- S12_TypeIIFrobenius:1221 `exists_typeIICrossIsometryData` (dead consumer:
  typeII_derived_frobenius 経由 docstring 参照のみ)。退役案 =
  TypeIICrossIsometryData の MulAut.conj 移送 lemma (near-definitional) で
  pair 版から導出、or 宣言ごと削除。
- S12_MaximalBasic:1257 (「DO NOT fill」注記済) / S12_MaximalIII_IV_V:1659
  (typeV 原本、superseded 注記済)。

## 改訂 frontier (lane a、着手宣言)

**`coherent_Sset_diff_SHCSet`** (S12_MaximalIII_IV_V:1548-1559) の honest 化:
(9.11) の SOf-difference 形再 port + (11.7) collapse。文書順で現 open 作業の
最上流 ((9.11) < (10.x) < (11.x))。docstring の「§14/lane-b 協調」注記は
S11/SOf 世界橋の設計点を指す — lane b の 2022 (S07/S08 coherence infra) とも
c の S16 とも対象非重複の見込み。**本 issue をもって claim** (重複あれば hub 指示を)。
次 iteration: 対象の依存 survey (mkSection11CharacterData の ∅-support 問題 /
SOf-difference の正しい statement / (11.7) collapse の所在) から。

---

# 🧭 HUB RULING (2026-07-11 tick): moot 化追認 + 改訂 frontier 承認 + cleanup 裁定

## moot 化の追認 (hub 検証済)

`exists_typeIICrossIsometryData_at_pair` (S12_TypeIICrossIsometryPair:1345) を hub が実測:
file 実 sorry 0 / critical path が :1446 で消費 / `S_not_coherent_unconditional` の AxiomsCheck
assert (7357) が全 build で通過。⟹ **9082 承認 plan の対象は消滅、同 ruling の実施条件
(S10 additive 制約・9079 ② 調整) は該当作業ごと void** (9079 claim 自体は a 保持のまま —
将来 (8.8) transpose が別経路で必要になれば再活用可)。

## cleanup 裁定 (superseded sorry 3 兄弟)

- **S12_TypeIIFrobenius:1221 `exists_typeIICrossIsometryData` = 削除** (dead sorried decl の
  不要化削除 — sanctioned、先例 = witness_psi_degree 49607ba9)。「pair 版から transport lemma で
  導出して残す」案は**不採用** — consumer 0 の薄 wrapper は書かない方針 (CLAUDE.md ラッパー方針)
  に反する。削除時に typeII_derived_frobenius の docstring 参照も修正。
- **S12_MaximalBasic:1257 / S12_MaximalIII_IV_V:1659**: consumer を grep で確認し、**0 なら同様に
  削除可・参照が残るなら annotated-keep** (a 裁量、削除が default)。「DO NOT fill」注記の温存は
  削除しない場合のみ意味を持つ。
- 実施は a の任意 tick で (急がない、通常 continuation)。

## 改訂 frontier の承認 + claim 有効化

**`coherent_Sset_diff_SHCSet` honest 化 ((9.11) SOf-difference 再 port + (11.7) collapse) を承認**。
文書順 (9.11) < (10.x) < (11.x) で現 open 最上流 ✓ / 所有 = S11・S12 (a regex 内) ✓ /
b の 2022 (S07/S08 coherence infra)・c の S16 と対象非重複 ✓。**§14 協調点の条件**: S14_MaximalI
(b 所有) の signature が必要になったら **sorried-cite + 要変更は issue 経由** (S14 直接編集は逸脱)。
本 issue の claim をもって着手可。9083 は本 ruling で **close**。

---

## lane a 追記 (close 後着信、hub が統合 2026-07-11)


## 再訂正 (同日 survey #2): coherent_Sset_diff_SHCSet も DEAD — claim 差し替え

precision survey の断定:
- **coherent_Sset_diff_SHCSet は dead** — call site 0 (def + docstring 2 件のみ)、
  consumer 連鎖は「coherent_Sset_of_glued (未適用)」→「coherent_Sset_of_column_identities
  (未定義の幻)」、AxiomsCheck 不在、**issue 1019 で deprecated** (wide route は
  non-Galois type III/IV で false → narrow 𝒮(H₀C) route に置換済)。port 不実施。
- (9.11) の book 原文 = full family 𝒮(H₀C′) coherent; 「difference」は (11.8.6) での
  isCoherent_of_subset + (11.7) H₀=1 collapse という応用に過ぎない。

## 改訂² frontier claim (lane a): honest (9.11) Ptype_core_coherence induction

- **対象**: `sibleyTarget_H0C` (S11_MaximalII_III_IV/Coherence911.lean:48) の置換 —
  **7001 監査で UNSOUND と開示済みの「do NOT fill」sorry** ((6.8) SibleyTarget の
  TI 仮説が nilpotent-Hall kernel HC で false)。live 参照あり
  (coherent_H0C_commutator :63 → S15 HypothesisBasics:422/435)。
- **本物の新規 math** = Coq PFsection9.v:1484-1571 の (9.11.1)–(9.11.8)
  maximal-subfamily refutation を、landed 済の S07 skeleton
  (exists_maximal_coherent_between :648 / coherent_of_maximal_coherent_pair_refuted)
  + S13 base cases (sOf_degreeSubfamily_isCoherent :588 /
  coherent_sOf_H0Cprime_of_allReducible :409) の上に組む。
- **境界注意**: S07 skeleton は b の carve-out 産 (family-agnostic infra、追加変更
  なしで消費のみ) — §9/§11 family での assembly は S13-側 consumer work = a 領域。
- **hub へ 2 点**: (i) この claim の重複チェック (S11/Coherence911 の所有)。
  (ii) liveness trace 依頼: coherent_H0C track (S15 tau1S_ofHonest 系) が S16
  非存在証明に現に配線されているか (survey は未確認と報告 — S16 は
  S07.irrSubcoherent + Rdatum 経由の別 route を使用中の模様)。配線されていなくても
  UNSOUND stand-in の置換は正当 (unsound scaffold は STOP-級の問題対象) だが、
  wiring の実態は §15/§16 側 (b/c) の設計に影響する。

## (9.11) port 設計確定 (survey #3、5-phase plan)

**honest route は ~80% landed 済**: 算術/refutation spine (nineElevenOne〜Five、
S11_SingleFactorCentralizer/NineElevenCoherence)・S07 skeleton・caseB 完了
(caseB_coherent_sOf_H0Cprime S13_CoreStructure:1482)・caseA reduction
(caseA_coherent_sOf_H0Cprime_of_refuter S11_NineElevenCaseA:65) 全て sorry-free。
**唯一の open gap = hrefute (S13_Orthogonality:130 の live sorry)** — これが
9083 改訂² の対象そのもの (sibleyTarget_H0C は並行 dead-end; 置換は本 route)。

Phase plan (詳細は survey 出力; 各 phase = 1 iteration 級):
- **A (S, ungated)**: squeeze wiring + dichotomy dispatch — hrefute を equality
  configuration + χ∈𝒮₃ 抽出まで落とし、coherent_sOf_H0Cprime 無条件版を組む。
  部品: clifford_dichotomy / caseB / nineElevenOne_configuration /
  coherentDegreeSqNormBound_of_not_coherentW / sumnS 系。全部品 proven。
- **B (M)**: (9.11.2) two-summand inertia index (K₁/K₂ relIndex = a、C = K₁⊓K₂)。
- **C (M, ungated)**: (9.11.3) W₁-orbit count split (hn : n = q|𝒮₄| + (p−1))。
- **D (L, ⚠gated)**: (9.11.4) Mackey norm + HU₁ ⊆ {1}∪A(M) (Coq gap-patch:
  Philip Hall/(2.1); §4 A(M)-support infra 要確認)。
- **E (L, ungated)**: (9.11.6-8) α^τ⊥𝒮₃ → β^τ 分解 → b=0 → pair 構成
  (isCoherent_pair_of_differenceImage) → refuter close。
配線仕上げ: mkSection11CharacterData の H0CprimeSupport := ∅ → hyp.base.A0 pin
+ sSet→sOf 家族修正 (S12:1548-1554 の 3 blocker)。

---

# 🧭 HUB 回答 (2026-07-11 tick、a の依頼 2 点 + 追記への応答)

## (i) claim 重複チェック → **重複なし、a 単独で進行可**

9000 番台 open を全 grep: S11/Coherence911 を対象とする claim は無し (9005 は S08→GroupTheory
prefix-split の claim で、Coherence911 は consumer 言及のみ)。S11_* は a regex 内・coherence 例外
glob (`S07_Coherence*`/`S08_PGroupReduction`) 非該当 ⟹ a 所有で確定。

## (ii) liveness trace → **coherent_H0C track は S16 に未配線 (survey どおり)**

hub grep: `tau1S_ofHonest` / `coherent_H0C` は `S16_NonExistenceG/**` に 0 hit。S16 の実 route は
`S07.irrSubcoherent` + `Rdatum` (TSideTypeP / TTypeII)。⟹ 置換は S16 を壊さない。
**重要な符合**: `sibleyTarget_H0C` の現 consumer は b 側 (S07_Subcoherent:306-330 /
S15 SubcoherenceInputs:840,881) で、**b 自身が「likely-UNSOUND (PU ≠ C')」と文書化済み**、
S07_Subcoherent:330 に「完全置換への残 steps」明記あり — a の 5-phase plan はまさにこれを供給する
(cross-lane 整合 ✓、b は本 issue + 自 file の注記で認知済み)。unsound stand-in の置換は正当
(hub 追認)。

## 運用注記 (frontier pivot の HUB issue について)

survey レベルの within-cluster pivot ((10.7)→diff-port→honest induction、全て a 領域内) は
**lane 自律で確定してよく、per-pivot の HUB 承認 issue は不要** (ft_path_policy §0 policy 5-6)。
HUB issue が適切なのは今回の (i)(ii) のような **cross-territory claim 照会・他レーン影響の trace 依頼**
のみ。9083 はこの回答をもって最終 close (5-phase plan A→E の実行は a 自律)。

---

# Phase A 完了 (2026-07-11, lane a)

squeeze wiring + dichotomy dispatch を landed (sorry 0・新 axiom 0・append-only):

- **`S11_NineElevenCaseA.lean`** (+222 行):
  - `NineElevenPairBound` (Prop shape) — (5.6) pair-bound bundle。pair-refuted な χ∈𝒮₃ に
    source degree `d ≤ u` (`χ(1) = q·d`) と `∀ F ⊆ 𝒮₂ finite, sumnS F ≤ 2q²a·d` を供給する形。
    **Phase E (5.6)-engine 側 discharge 対象** (per-member Dade data を
    `coherentDegreeSqNormBound_of_not_coherentW` に通し `sumnS_image_eq_anchorSq_mul` で rescale)。
  - `NineElevenEqualityRefutation` (Prop shape) — equality configuration
    (`2a = p−1`・`C = U′`・∀χ∈𝒮₃ deg = qu・count equality `n₁a² = (p−1)[U:U′]`・
    saturated bound `∀F⊆𝒮₂, sumnS F ≤ 2q²au`) + full situation → False。
    **Phase B/C/D/E の合流 discharge 対象** (`nineElevenCaseA_equality_refutation` が算術 spine;
    B = (9.11.2) K₁/K₂ inertia、C = (9.11.3) hclass+hn、D = (9.11.4) hnorm、
    E = (9.11.5-8) hle + pair 構成 + 𝒮₂=𝒮₁ 抽出 — 抽出は saturated bound から
    Snorm>0 で回収可能)。
  - `caseA_refuter_of_equality_refutation` — 上 2 つから S07 refuter clause を discharge。
    (9.11.1) squeeze を **𝒮₃ の各 member ごとに**回す (book の "we may assume" wlog 不要化):
    lower bound = `sumnS_irreducible_constant_degree` (𝒮₁′ = 𝒮(H₀U′) の degree-qa irr cut、
    `sOf_antitone` で 𝒮₂ 内へ)、upper bound = bundle の F-instantiation、
    `nineElevenOne_configuration` で closed circle。**axiom-clean 実測**
    (propext/Classical.choice/Quot.sound のみ)。
- **`S13_Orthogonality.lean`** (+39 行): `coherent_sOf_H0Cprime_of_equality_refutation` —
  `clifford_dichotomy` dispatch、caseB → `caseB_coherent_sOf_H0Cprime` (9075)、
  caseA → `caseA_coherent_sOf_H0Cprime_of_refuter` + Phase-A refuter。結論
  `Nonempty (IsCoherent hyp.base.tau (sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0)`、
  仮説は `∀ caseA, NineElevenPairBound/NineElevenEqualityRefutation` の 2 本のみ。
  sorryAx は caseB 側 upstream 由来 (既存・9075 transitive) で本 commit の追加分は clean。

残 phase の直接ターゲット = `NineElevenPairBound` と `NineElevenEqualityRefutation` の 2 定理
(両方 landed 時に `coherent_sOf_H0Cprime_of_equality_refutation` が無条件化 →
S13_Orthogonality:130 の live sorry を置換)。

---

# Phase E-PairBound 完了 (2026-07-11, lane a)

**`NineElevenPairBound` を discharge** — `nineElevenPairBound` (S11_NineElevenCaseA.lean、
append-only +347 行、自前 sorry 0・新 axiom 0):

- **`caseA_sOf_source_degree_ratio`** — (9.8.a) member-degree dictionary (Coq `a_dv_XH0`
  member 形): `𝒮(H₀ ⊔ Y)` の各 member は degree `q·a·e` (`caseA_source_degree_dvd_a` 経由)。
  Coq が `extend_coherent` の側条件 `xi1 1 %| chi 1` に食わせるのと同一の divisibility。
- **`nineElevenPairBound`** — (5.6) pair-bound bundle 本体。break dictionary
  (`χ = Ind ζ`, `χ(1) = q·d`) + `d ≤ u` (`xiOf_H0Cprime_source_apply_one_le_u`、
  `H₀C′ = H₀ ⊔ C′` の同定は `C_eq_cSub`) + `a ∣ d`。bound は
  `coherentDegreeSqNormBound_of_not_coherentW_k` (norm-weighted (5.6) 逆読み) を
  degree-`qa` anchor ((9.8.d) count の正値性、Phase A base case と同一抽出) で発火:
  per-member Dade data = **`S12.sixTwoDecompositionData`** ((5.2.d)/(5.2.e) grid 供給、
  issue 2022 産・sorry-free)、Gram/support/ZIrr/generation = S08_SixTwoGeneral 層
  (`inducedKernelFamily_degreeSqNormReBound_of_break_k` の assembly を anchor 度数 `qa`・
  ratio `d/a` に組み替え)。rescale `sumnS F ≤ sumnS 𝒮₂ = (qa)²·Σ deg²/mc ≤ (qa)²·2(d/a)
  = 2q²a·d`。
- **axiom 実測**: `nineElevenPairBound` = propext/**sorryAx**/Classical.choice/Quot.sound。
  sorryAx は**本 commit の追加分ではなく** `C_eq_cSub` (S13_CoreStructure) →
  `H0_eq_Hprime`/(11.5) chain の既存 upstream 由来 — **caseB 分岐
  (`caseB_coherent_sOf_H0Cprime`, 9075) が既に負っている同一 debt** (sorried-cite 規約適合)。
  helper `caseA_sOf_source_degree_ratio` は axiom-clean。
- 消費側: `caseA_refuter_of_equality_refutation` の `hbound` 仮説が直接充足可能に。
  **残 = `NineElevenEqualityRefutation` のみ** (Phase B (9.11.2) / C (9.11.3) / D (9.11.4) /
  E-remainder (9.11.5-8))。

---

# Phase B 完了 (2026-07-11, lane a)

**(9.11.2) two-summand inertia inputs を landed** — 新 leaf `S11_NineElevenTwoSummand.lean`
(865 行、自前 sorry 0・新 axiom 0) + `S11_NineElevenCaseA.lean` 追記 (+59 行、append-only):

- **構成 (book (9.11.2) / Coq PFsection9.v:1681-1790 `tiU1` の port)**:
  two-summand character θ (`exists_caseA_two_summand_char`、H_i/H_j 上非自明・他 summand 上自明)
  を inertia 部分群 `H·K` (K = `cuSubOf i ⊓ cuSubOf j` realized = `cuInHuPair`) 上の**線形**指標
  `nineElevenTwoPsi` に拡張 (`SemidirectProduct.lift`、complement =
  `hInHu_isComplement'_cuInHuPair` ← `H ⊓ K = ⊥`; lift 両立条件 = θ₀ の K-不変性 ←
  landed `cuInHuPair_le_inertia`)。inertia(ψ) = H·K (landed `caseA_inertia_eq_hcuInHuPair`) ⟹
  `ζ = Ind_{HK}^{HU} ψ` **irreducible** (`isIrreducibleCharacter_induce_of_inertia_eq`) of degree
  `[HU:HK] = [U:K]` (landed index 連鎖) — book の "(1.6)/(1.7.c) applied to (HU)/(H₀C)" は
  「線形 source を full inertia group から誘導」の形で実現 (商群経由不要、e=1 が構成から出る)。
  ζ ∈ 𝒳(H₀C) (kernel: seed が H₀ を、complement 自明性が C ≤ K を kill; H ⊄ Ker: θ ≠ 1)、
  member `Ind_{HU}^M ζ ∈ 𝒮(H₀C)` of degree `q·[U:K]`。
- **dichotomy 解決 (`nineElevenTwo_two_summand_inertia`)**: hdeg (𝒮(H₀C)-member degree ∈
  {qu, qa}) から `[U:K_{ij}] ∈ {u, a}` (q cancel)。**pair-uniform trick で book の W₁-orbit
  propagation を置換**: (i) ある pair で = u ⟹ C ≤ K_{ij} + 等 relIndex ⟹ C = K_{ij}
  (`relIndex_lt_relIndex_of_le_of_ne`); (ii) 全 pair で = a ⟹ 各 pair で K_{ij} = K_i = K_j ⟹
  全 `cuSubOf` 一致 ⟹ C = ⋂_k C_U(H_k) = 共通値 (新補題 `mem_cSub_of_forall_mem_cuSubOf` +
  `uActionHom_eq_one_of_forall_summand`、`Hpart_iSup` span 論法) ⟹ K₁ = K₂ = 共通値で
  `C = K₁ ⊓ K₂` 成立。**book の「u ≠ a で矛盾」は不要** — 消費側 `nineElevenTwo_u_le_a_sq` は
  ∃-form の K₁/K₂ で足り、u = a なら u ≤ a² が自明に真 (吸収)。
- **S13 corollary `caseA_two_summand_inertia_inputs`** (S11_NineElevenCaseA.lean): equality
  configuration の hS3deg (landed、𝒮₃ = degree qu) + **Phase-E remainder `hS2deg`**
  (𝒮₂-member degree qa = 「𝒮₂=𝒮₁」抽出、名前付き仮説) から
  `∃ K₁ K₂, relIndex = a ∧ relIndex = a ∧ chars.C = K₁ ⊓ K₂` —
  `nineElevenCaseA_equality_refutation` の hK₁/hK₂/hCinf と**同形**。
- **axiom 実測**: S11 層は全部 axiom-clean (`nineElevenTwo_two_summand_inertia` /
  `nineElevenTwo_relIndex_dichotomy` / `nineElevenTwoZeta_mem_xiOf` /
  `mem_cSub_of_forall_mem_cuSubOf` = propext/Classical.choice/Quot.sound のみ)。
  S13 corollary のみ sorryAx — **既存 upstream `C_eq_cSub` 由来** (caseB/E-PairBound と同一 debt、
  本 commit の追加分ではない)。
- **残 = Phases C/D/E のみ**: C = (9.11.3) hclass (`sum_xiOf_H0C_degreeSq` landed、残 = |Ū| 項の
  組立) + hn (W₁-orbit split)、D = (9.11.4) hnorm (Mackey)、E = (9.11.5-8) hle + `𝒮₂=𝒮₁` 抽出
  (hS2deg 供給、saturated bound + Snorm>0) + pair 構成。B の出力は
  `nineElevenCaseA_equality_refutation` に直結済み。

---

# Phase C 完了 (2026-07-11, lane a)

**(9.11.3) W₁-orbit count split を landed** — `S11_NineElevenCoherence.lean` 追記 (+485 行、
append-only) + `S11_NineElevenCaseA.lean` 追記 (+234 行、append-only)。自前 sorry 0・新 axiom 0。

- **構成 (book (9.11.3) / Coq PFsection9.v `card_S4` の port)**: `hclass` を
  **`n = |𝒮₄|·q + (p−1)` で直接証明**する設計 — `hn` は definitional (`rfl`) になり、
  book の「n を先に数えて後から割る」を逆転 (ℕ-division 不要)。エンジンは `𝒳(H₀C)` の
  `Ind_{HU}^M` fibration:
  - **fibre = full M-conjugation orbit** (`card_filter_induce_eq_index_inertia`、
    `𝒳(H₀C)` filter の conjugation-closedness は新補題
    `subsetCharacterKernel_conjBy_iff_of_invariant` + `realized_conjByMulEquiv_mem`
    — `H₀C`-realized/`H`-realized の M-正規性から);
  - **orbit size dichotomy** (`[M:HU] = q` prime): 新補題
    `inertia_index_eq_q_of_induce_irreducible` (‖Ind χ‖² = 1 ⟹ |I| = |HU| ⟹ index q —
    (9.11.3) の「q conjugates under W₁」) /
    `inertia_index_eq_one_of_induce_reducible` (index ∣ q prime、index = q なら
    `isIrreducibleCharacter_induce_of_inertia_eq` で irreducible になり矛盾 — reducible
    member は W₁-invariant single source);
  - **3 分割**: reducible part (count p−1 = `reducible_count_sOf_H0C`、source degree u =
    (9.8.b) `caseA_reducible_induceHU_apply_one_eq_qu`) / irr-in-𝒮₂ part (degree a、
    `|𝒮₁′|·a² = (p−1)·[U:U′] = (p−1)·u` — hcount + `C = U′` + `relIndex_cSub_U_eq_u`) /
    irr-outside-𝒮₂ part (= 𝒮₄、degree u);
  - **台帳閉じ**: `sum_xiOf_H0C_degreeSq` (∑χ(1)² = p^q·u − u) に 3 部分の
    card×degree² を代入、`linear_combination` で ℂ→`Nat.cast_inj`→ℕ。
- **S11 主定理 `nineElevenThree_orbit_split`**: 仮説 = hS₁'sub (degree-qa 𝒮(H₀U′) ⊆ S₂)、
  hS3deg' (𝒮(H₀C)∖S₂ degree qu)、hS2deg (S₂ degree qa)、hCU (`cSub = uprimeSub`)、hcount。
  結論 = `u + (|𝒮₄|·q + (p−1))·u² + q(p−1)u = p^q·u` (hclass @ n := |𝒮₄|·q + (p−1))。
- **S13 層** (`S11_NineElevenCaseA.lean`):
  - `nineElevenSFour hyp S₂` — 𝒮₄ の正準 spelling ({φ ∈ 𝒮(H₀C) | irr ∧ φ ∉ S₂})。
    **Phase E の `hle : |𝒮₄| ≤ N` はこの ncard を bound する契約**。
  - `caseA_nineElevenThree_count_inputs` — equality-configuration budget から hclass を供給
    (H₀C′ ≤ H₀U′ / H₀C′ ≤ H₀C の antitone 移送は Phase A/B と同型)。
  - **Prop 形 `NineElevenSTwoExtraction`** ((9.11.1) 𝒮₂=𝒮₁ 抽出、Phase E) /
    **`NineElevenNormBound`** ((9.11.4) hnorm + (9.11.5-8) |𝒮₄| ≤ ‖α‖²、Phase D+E) —
    equality-configuration 全 11 antecedent で ∀-quantify した book-cited 名前付き仮説。
  - **assembler `nineElevenEqualityRefutation_of_sTwoExtraction_normBound`**: 上記 2 Prop
    ⟹ `NineElevenEqualityRefutation` (B+C 出力 + q≥3 (odd prime) + u≥1 (`u_odd`) +
    p=2a+1 を内部供給、hn = `rfl`)。**残距離 = この 2 Prop の discharge のみ (= Phases D/E)**。
- **axiom 実測**: S11 層は全部 axiom-clean (`nineElevenThree_orbit_split` /
  `subsetCharacterKernel_conjBy_iff_of_invariant` / `realized_conjByMulEquiv_mem` /
  `inertia_index_eq_q_of_induce_irreducible` / `inertia_index_eq_one_of_induce_reducible`
  = propext/Classical.choice/Quot.sound のみ)。S13 層 (`caseA_nineElevenThree_count_inputs` /
  assembler) のみ sorryAx — **既存 upstream `C_eq_cSub` 由来** (H₀C′ ≤ H₀C 移送と Phase-B
  corollary 経由; caseB/E-PairBound/B と同一 debt、本 commit の追加分ではない)。
- ⚠ **hub への分割 flag**: `S11_NineElevenCoherence.lean` が 1511 行 (>1500 trigger)。
  凍結境界での prefix-split (または dir 化) を hub に委任 (本 commit は append-only を維持)。

---

# Phase D 完了 (2026-07-11, lane a)

**(9.11.4) Mackey norm + support を landed** — 新 leaf `S11_NineElevenMackeyNorm.lean`
(877 行、自前 sorry 0・新 axiom 0) + `S11_NineElevenCaseA.lean` 追記 (+170 行、append-only)。
**全成果 axiom-clean 実測** (propext/Classical.choice/Quot.sound のみ — S13 bundle 含め
sorryAx ゼロ; C_eq_cSub debt も不使用: C = U′ 同定は hCUprime を chars-level defeq で消費)。

- **gating 判定 (指示の 30min check)**: **UNGATED**。(a) Pf (2.1) は S04_InduceConjFinset に
  複数 landed (不使用で済んだ); (b) A(M)-support bridge: 本形式化では **A(M) = (M′)^# が定理**
  (`typePA_eq_sharpSubgroup_derivedInG`) + `mderivSharp_subset_A0` で `(M′)^# ⊆ A₀(M)` ⟹
  **Coq gap-patch (PFsection9.v:1476-1483 の Philip Hall/solvability/(2.1)) は本設計では不要**
  (HU₁ ≤ M′ から自明); (c) Hall/solvability 不要。
- **構成 (book (9.11.4) / Coq PFsection9.v:1863-1952 の port)**:
  - **averaging-projector vanishing** (`sum_apply_mul_eq_zero_of_not_subset_characterKernel`):
    N ◁ Γ, χ irr, N ⊄ Ker χ ⟹ Σ_{n∈N} χ(ny) = 0 — rep-level (T = Σρ(n) の range は
    subrep; ⊤ なら N ⊆ Ker、⊥ なら T = 0)。Coq の `sub_cfker_constt_Ind_irr`
    constituent-kernel 機構の代替。⟨γ, ψ₁⟩ = 0 は **source ζ の H ⊄ Ker (xiSet 所属そのもの)**
    まで Frobenius reciprocity + 誘導公式で降ろして発火 (`inner_induce_trivial_induce_eq_zero`)
    — M-level の kernel-avoidance 論法 (character bound) 不要。
  - **Mackey count**: `‖Ind_K^M 1‖²·|K|² = Σ_{x∈M} |K ∩ ˣK|`
    (`inner_induce_trivial_self_mul_card_sq`) + `(H·U)·W₁`-fibred 評価
    `Σ = |H|²·|U|·(|U₁| + (q−1)|C|)` (`sum_card_inf_conjSMul_eq`; Dedekind 恒等式
    `(H⊔U₁)⊓(H⊔V) = H⊔(U₁⊓V)` + U₁ ◁ U (U′ ≤ U₁ ← equality config C = U′) +
    W₁ ≤ N(U))。book の λ(x)-count を **商群指標転送なしの部分群算術**で実現
    (Coq の cfIndMod/cfIndIsom/cfIndInd 層を回避)。
  - **γ-context 層** (`nineElevenGamma_*`): supp γ ⊆ HU / γ(1) = qa ([M:HU₁] 鎖) /
    ⟨γ, Ind_{HU} ζ⟩ = 0 (∀ζ ∈ 𝒳) / **‖γ‖²·u = a·u + (q−1)·a²** (cleared form)。
  - **S13 bundle `caseA_nineElevenFour_norm_inputs`**: equality config (hCUprime + hcount)
    + TI-witness ⟹ `∃ N, N·u = (a+1)·u + (q−1)·a² ∧ ∃ α ∈ ℤ[Irr M], supp α ⊆ A₀ ∧ ‖α‖² = N`
    — ψ₁ は hcount 正値性から 𝒮₁-family で選択、α = γ − ψ₁、‖α‖² = ‖γ‖²+1
    (`cfnorm_sub_irreducible_orthogonal`)、整数性は ZIrr Fourier
    (`mem_ZIrr_inner_self_eq_sum_sq`)、support は HU = M′ + 次数相殺 α(1) = qa−qa = 0 +
    `mderivSharp_subset_A0`。**NineElevenNormBound の hnorm 半分がこれで供給**;
    残 = `|𝒮₄| ≤ N = ‖α‖²` ((9.11.5-8)、Phase E が同じ α を τ 経由で消費)。
- **残された ONE 名前付き Prop = `NineElevenTwoTIWitness`** (book (9.11.2) の表示文
  そのもの: "if w ∈ W₁^# then U₁ ∩ U₁^w = C" + witness U₁ = C_U(H₁) の standing facts
  C ≤ U₁ ≤ U, [U:U₁] = a — 全て landed lemma で book-true)。discharge には Phase-B pair
  dichotomy (`nineElevenTwo_relIndex_dichotomy`) + **W₁ ↔ Clifford summand 共役辞書
  `C_U(H₁)^w = C_U(H₁^w)`** (`Hpart_orbit` の実現、Phase E)。all-pairs-a 分岐では
  U₁ = C で witness は自明に立つ (u = a 吸収と同型)。
- **AxiomsCheck**: 主要 7 定理の `#assert_only_allowed_axioms` を追加。
- 消費側: Phase E は `NineElevenNormBound` を「本 bundle (hnorm+α) + |𝒮₄| ≤ ‖α‖²
  (α^τ 直交性、pair-refutation ← (9.11.6-8))」で discharge、
  `NineElevenSTwoExtraction` と併せて `nineElevenEqualityRefutation_of_sTwoExtraction_normBound`
  が閉じ、S13_Orthogonality:130 の live sorry が置換される。
