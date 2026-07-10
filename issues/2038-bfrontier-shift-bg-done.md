---
id: 2038
slug: bfrontier-shift-bg-done
title: "b-frontier shift: BG §15/§16 done, reachable clean b-sorry 枯渇 → reallocation 要検討 (hub)"
created: 2026-07-08
---

# b-frontier shift: assigned BG §15/§16 done、reachable clean b-sorry 枯渇 (hub 裁定要)

## 契機 (lane-b /loop、2026-07-08)

lane-b /loop で assigned frontier (memory [[ft-four-fronts-w1-w4]] の「真の bottleneck = BG §15/§16
node、4 bare sorry」) を進めようとしたが、**comment-strip 実測で BG §15/§16 は実質 done** と判明
([[grep-sorry-docstring-contamination]] の実害 — 旧 scan は docstring 汚染で ~40 sorry 誤認)。

## 検証結果 (comment-strip、code-level)

- **BG §15/§16 = done**: `S15_MF.lean` 実 sorry **0**、`S16_MainResults.lean` 実 sorry **1**
  (`theoremA_maximal_structure` = faithful 版 `theoremA_maximal_structure_faithful` が proven ゆえ意図的
  scaffold、gap でない)。memory の「BG §15/§16 bottleneck」は完全 stale (memory 訂正済)。
- **真の b-owned 実 sorry** (comment-strip): S14_MaximalI **11** / S15_SAndT_Setup **11** / S15_SAndT **9**
  (S07/S08/S09 = 0)。
- **だが全て gated/off-path/lane-c-coupled** (docstring code-level 確認):
  - **S14 (11)**: 全て「BG §16 residual / hub 9003 に gated、not in reach of S14」明記 —
    `escapingCentralizers_control` (S10:497、(2.3) escaping-centralizer、sorried ungated-most upstream) /
    (8.8.a) dichotomy / (8.3)/(12.8) minimality (=9003)。
  - **S15 char (20)**: W-side (gammaGrid 等) = lane-c-active / S-side cascade
    (`sibleyTarget_S`/`character_degree_analysis`/(13.10) analytic) = **off-path vestigial** (hub 2026-07-02
    ruling: spine は W-side eta grid 経由、tauS=0 placeholder、do-not-complete)。残 (caseB_order_u 等) は
    abstract Prop param (`caseB_for_S : Prop` 中身なし) or coherence 依存で gated。

## lane-b の genuine landed (2026-07-08、参考)

§13 prime-TI residue bridge (`residueS`/`mu2_ne`、S13_PrimeTIResidueBridge.lean) +
`honestTypeP2ASet_subset_typePA` + (13.18) support-set 解決 (9008: typePA0=over-claim、honestTypeP2A0Set
正しい、certainTypeDiffSupported が A parametric ゆえ route clean) + Hypothesis46-for-S feasibility 確定
(subH=M_σ で A_covers 成立)。→ (13.18) pins 2/3 の残 assembly = Hypothesis46-for-S (lane-c file、dadeHypS0 消費、
subH 設計は lane-c 構造知識)。

## hub 裁定要 (reallocation)

assigned b-frontier (BG §15/§16) が done ゆえ **lane-b の次 focus が underdetermined**。選択肢:
1. **char W-side / Hypothesis46-for-S を lane-c と coordinate** (lane-c が active に (13.18) betaGrid_A0_support
   endgame を finishing 中、Hypothesis46-for-S が gate、lane-b の residueS が upstream で citable)。
2. **deep cross-cutting residual を lane-b が engage** (`escapingCentralizers_control` (2.3) 等) — ただし
   BG §16/Ch2 uniqueness 領域で ownership 要確認 (claim-before-build)、hub 9003 と重複可能性。
3. **lane-b reallocation** (frontier 供給に合わせ、過去 4→3 レーン縮約の前例)。

lane-b は本 issue 記録後、/loop 判断で最も policy-compliant な継続 (ungated upstream engage or lane-c 支援)
を選ぶが、reallocation は hub 裁定事項ゆえ surface。

## ✅ HUB RULING (2026-07-08 合流 tick、自律裁定 🧭) — reallocation せず、b は (13.18) upstream 継続

**事実検証 (hub、comment-strip 実測)**: b の主張は全て正確 — BG §15/§16 done (`S15_MF`=0、
`S16_MainResults`=1 は faithful 版 proven ゆえ意図 scaffold、BG Ch1-4 計 3)。b 所有実 sorry =
`S14_MaximalI` 11 / `S15_SAndT_Setup` 11 / `S15_SAndT` 9 (計 31、大半 gated)。全体 87 (on-path 64 /
off-path 凍結 23)。memory [[ft-four-fronts-w1-w4]] は既に 2026-07-08 訂正済 (stale でない)。

**裁定: 選択肢 3 (reallocation) 却下。b は継続 (選択肢 1 = (13.18) upstream + lane-c 支援)。**

根拠:
1. **policy**: CLAUDE.md「進捗の測り方」— gated / quick-win 不在 / deep-char 多反復 は**着手/継続/
   reallocation の判断基準でない**。gated frontier のレーンは**さらに上流の ungated genuine math に降りて
   実証明する** (ft_path_policy §0 policy 5-6)。「reachable clean sorry 枯渇」は reallocation 根拠にならない。
2. **b は churn でなく genuine output を生産中**: 本 session の residueS/mu2_ne/honestTypeP2ASet_subset_typePA/
   (13.18) support-set 解決 = 実 on-path 進捗。lane-d 退役基準 (genuine ungated on-path work ゼロ + dup churn
   drift) に**該当しない** (lane-d とは質的に別)。
3. **(13.18) char endgame は active**: c が `betaGrid_A0_support` finishing 中、b の residue 上流が feed。

**b の継続 priority (上流優先 + 文書順)**:
- **主 = (13.18) endgame の upstream**: pins 2/3 の residue facts (S06 `Hypothesis46` certain-type API =
  `certainTypeDiffSupported` (support) / `certainType_diff_dade_eq` (V-value) の S-side wiring) を **b 所有の
  `S13_PrimeTIResidueBridge` (carve-out) or 共有 S06 API** に citable infra として build。**分担境界**:
  b = residue 上流 (residueS/mu2/prTIirr-value) 供給 / c = `Hypothesis46-for-S` 組立 (`S15_HonestTypeP2A0`、
  dadeHypS0 消費、subH 構造知識)。**b は Hypothesis46-for-S 本体 (c file) を build しない** (upstream 供給に徹する)。
- **副 (主が枯渇時) = 次の ungated upstream に降りる**: `escapingCentralizers_control` ((2.3)) の source は
  **S10 (a 所有)** ゆえ b は無断編集不可 — 降りたい場合は **hub carve-out 申請** (9003 との重複を hub が判定) or
  共有 group-theory infra へ。**reallocation でなく descent**。
- **やらないこと**: off-path S-side cascade (sibleyTarget_S/(13.10) analytic、2026-07-02 ruling で do-not-complete)
  の完成、a active S10/S13/S12 の無断編集。

**再評価トリガー**: b が複数 tick 連続で ungated on-path work ゼロ + dup relocation churn に drift した場合のみ
reallocation を再検討 (lane-d 基準)。現時点は非該当。本 issue は ruling 記録後 closed 相当 (b は継続)。

## ✅ 訂正 (2026-07-08 続): signalizer uniqueness は PROVEN、(8.13) は assemble 可能 (deep-port 悲観は stale comment 由来)

前記「残 = BG Theorem D signalizer uniqueness の major port」は **誤り** ([[verify-port-state-by-number-not-coq-name]]
の再実例)。code-level 精査で判明:
- `signalizer_structure_of_mem_sigmaSharp` (S16_MainResults:271) は **PROVEN (sorry-free)** —
  `S14.sigmaLength_one_centralizer_structure` (proven) 経由で σ-sharp element の **unique maximal ∃! N[x]**
  over C_G(x) + Hall(R) + sharp transitivity + type-F/P2 dichotomy + complement を供給。
- S16_MainResults:156 の「FT_signalizer_context uniqueness is remaining content」comment は **STALE**。
- BG Cor 12.14 (`maximalContaining_centralizer_and_someSylow_eq_singleton`, S12_Corollary1214) も proven。

**⟹ (8.13) `escapingCentralizers_control` (S10、lane-a) は今 assemble 可能** = genuine buildable b-work:
escaping x (∈A0(M), C_G(x)⊄M) → x∈M_σ^# σ-sharp ∧ >1 σ-maximal → `signalizer_structure_of_mem_sigmaSharp`
で ∃! N + (typeF∨typeP2 N) → typeI/II 変換 (`isTypeI_of_isTypeF`/`isTypeII_of_isTypeP2`)。→ S14 all-type-I
分岐 (`allTypeI_fittingIsTI`/`not_nonTypeICovering`) を unblock。配置: assembly を BG §16 (b-owned) に置き
S14/S10 が cite (S10 は territorial ゆえ新 lemma を S14/§16 側に)。**次 iteration で build**。

⟹ **reallocation は不要かも** (lane-b に genuine buildable on-path work = (8.13) assembly + S14 branch が残存)。
hub は本 finding を勘案。lane-b は build 継続。

## ✅ (2026-07-08 続²、lane-b /loop) — (8.13) per-element ∃! **landed**、allTypeI_fittingIsTI 到達性を精査

**landed (commit 3e88b161)**: `existsUnique_maximal_centralizer_le_typeI_or_typeII` (S16_MainResults、b-owned)
= (8.13) の per-element `∃!` 結論 (existence 半分 `exists_maximal_centralizer_le_typeI_or_typeII` +
Theorem-D singleton uniqueness `maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape` を
合成)。escapingCentralizers_control (S10、lane-a) 第2連言の literal shape そのもの (`theoremII_tame_embedding`
の BG-set-bound per-x clause の Peterfalvi-set 版 clean core)。full build 3943 green・AxiomsCheck OK。

**allTypeI_fittingIsTI (S14:7089、次 consumer) 到達性 — 精査結果 (docstring は STALE でなく正確)**:
- consumer chain は明瞭: `exists_typeICovering` (S14:7168) は `allTypeI_fittingIsTI` → 既存
  `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI` (S16) のみ。∴ `allTypeI_fittingIsTI` が唯一 gate。
- clean route (contrapositive): type-I M は type-F (`isTypeF_of_isTypeI`)。¬FittingIsTI と仮定 → 矛盾を出す。
  だが `exists_RData_escape_structure` (S16:6095) は escaping σ# x に対し neighbour N (typeF∨typeP2) を出すのみで、
  **all-type-I では N は maximal ⟹ type I ⟹ type F** ゆえ disjunction が typeF に落ち、`IsTypeP2 N → ¬FittingIsTI`
  は空虚 → 矛盾出ず。
- **真の crux (未組立)**: 「type-F M で escaping σ# ⟹ neighbour N が type-P₂」= **Cor 15.9 の逆**。
  Lean の `centralizer_escape_final_local` (S16:5916) は `¬IsTypeF N` を**仮説**に要求 (all-type-I では偽) ゆえ
  そのままでは使えない。∴ docstring の「escapingCentralizers_control (S10, lane-a) に gated」は**正確**
  (私の (8.13) ∃! はまさに escapingCentralizers_control の upstream ingredient — lane-a が S10 で cite → 下って
  allTypeI_fittingIsTI へ)。
- 「¬FittingIsTI ⟹ ∃ escaping σ#-element」の confident reverse 還元 (pieces:
  `exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` + `mem_sigma_of_prime_dvd_card_inf_conj_fitting` +
  `mem_Msigma_of_isPiElement_sigma_of_mem` + `maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le`) も
  **Fitting conj-equivariance (`conj g • fittingInAmbient M = fittingInAmbient (conj g • M)`) が現状 absent** ゆえ
  infra 追加要 (step: z ∈ F(M)^g ⟹ z ∈ M_σ(M^g))。かつ consumer は P₂-crux で依然 blocked。

**次 b 選択肢** (どれも genuine on-path): (i) Fitting-conj-equivariance infra + reverse-escape lemma を confident
partial として build (allTypeI の半分)、(ii) lane-a と escapingCentralizers_control で coordinate (b の (8.13) ∃!
が now citable upstream)、(iii) 別 b-frontier piece。lane-b は /loop 継続。

## ✅ (2026-07-08 続³、lane-b /loop) — reverse-escape lemma **landed** (option i)、P₂-crux が唯一残 gate

**landed (commit aac73cfb)**: `exists_sigmaSharp_escape_of_not_fittingIsTI` (S16_MainResults、b-owned) =
`not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le` の honest な逆 (**¬FittingIsTI M ⟹ ∃ z ∈ M_σ#,
C_G(z) ⊄ M**)。**Fitting-conj-equivariance 不要**と判明: `mem_sigma_of_prime_dvd_card_inf_conj_fitting` が
「F(M) ⊓ F(M)^g の card を割る素数は全て σ(M)」を与えるゆえ、交わりの任意の非単位元 z は自動 σ-element →
z ∈ M_σ(M^g) は z ∈ conj g • F(M) ≤ conj g • M = M^g + σ-conj-invariance で直接 (F(M^g) 経由不要)。full build
3943 green・AxiomsCheck OK。

**allTypeI_fittingIsTI の残 gate = P₂-crux のみ** (確定): reverse-escape で ∃ escaping z を得ても、
`exists_RData_escape_structure` の neighbour N は all-type-I で type-F に落ちる (前記) → 矛盾出ず。
**「type-F M で escaping σ# ⟹ N type-P₂」が genuinely 未組立**: Lean `centralizer_escape_final_local` も Coq
`nonFtype_signalizer_base` (BGsection15:1399) も **¬IsTypeF N (= "nonFtype") を仮説要求** (証明せず)。∴ この
crux は深い BG Cor 15.9 の逆で、S16 (b-owned) に置ける可能性はあるが Cor-15.9-machinery
(`typeP2_neighbor_is_typeF_of_mem`/`norm_noncyclic_sigma`/`tau2_transfer_constraint`) の逆向き組立要 →
Coq/教科書精読 ([[feedback-ask-chatgpt-for-elided-gaps]]) 候補。**次 iteration**: (a) P₂-crux を Coq-assisted で
attempt、or (b) upstream-priority 再考 (§13 (13.18) residue supply 等)。b の (8.13) ∃! + reverse-escape は
escapingCentralizers_control (lane-a) の citable upstream として残る。

## 🧭 (2026-07-08 続⁴、lane-b /loop) — b の (8.13)/escaping クラスタ寄与は **完了**、残は lane-a-coupled 深部 (hub 裁定要)

3 iteration の frontier 精査の**確定診断** (hub 向け):
- **b の clean 寄与は landed で完了**: `existsUnique_maximal_centralizer_le_typeI_or_typeII` (∃!) +
  `exists_sigmaSharp_escape_of_not_fittingIsTI` (reverse-escape)。両者 sigmaSharp-based で **b/lane-a 境界の正しい
  b 側**。escaping-set 形 (A1 M tau → sigmaSharp bridge) は Peterfalvi `A1` (S10、lane-a) を要すゆえ lane-a 側。
- **P₂-crux = BG §14 type-duality の逆**: repo は `typeP2_neighbor_is_typeF`/`_of_mem` (S14:11396/12030 = Cor 14.12
  = Coq `P2type_signalizer`) で **M-type-P₂ ⟹ neighbour-type-F** を持つが、逆の **M-type-F + escaping ⟹
  neighbour-type-P₂** は未組立 (Cor 14.12 machinery の逆向き; Cor 15.9 も Coq もこれを仮説に取る)。深い multi-lemma port。
- **b の S14 残 sorry (11) は一律 gated**: allTypeI/(8.8.a)/(12.11 = 8.13.c1+8.1.b/c+9.1+12.10)/hub 9003 = 全て §8/§16
  escaping-centralizer 深部 = escapingCentralizers_control (lane-a S10) 系。b-owned で clean ungated な残は無し。
- **∴ hub 裁定事項**: (1) lane-a が b の ∃!+reverse-escape を input に escapingCentralizers_control を組む、
  (2) P₂-crux (type-duality 逆) を b or shared に deep-port 割当 (Coq-assisted, multi-session)、
  (3) b を別クラスタへ reallocate。lane-b は再評価トリガー (ungated on-path work ゼロ) に**近い**が、本 session で
  genuine 2 lemma landed ゆえ churn drift ではない。次 /loop iteration は (2) を Coq-assisted で begin する
  (deep frontier を engage; policy「難所を回避しない」)、hub が別途 (1)/(3) を裁定可。

## ✅ (2026-07-08 続⁵、lane-b /loop) — 訂正: b frontier は**枯渇していない** — intersection_le_kernel が assemblable

前 (続⁴) の「b clean frontier 枯渇 → hub reallocate 検討」は**部分的に誤り** (再: [[verify-port-state-by-number-not-coq-name]])。
comprehensive survey で **`intersection_le_kernel` (S14:5245、Pf 12.11 第2主張、b-owned、on-path 12.11→12.17) が
genuinely ASSEMBLABLE** と判明 — docstring「Genuinely still-missing」は **STALE**。全 prereq 実在:
- (12.10) `witness_L_frobenius` = **PROVEN** (docstring は「pinned」と誤記)
- (8.1.b) = `TypeFData.{centralizer_le_U1, U1_commutative, U1_normal}` (field!)
- (8.1.c) = `TypeFData.{exponent_eq, frobenius_HU0}` (field)
- (9.1) Wielandt = `GroupTheory/CoprimeFixedPoints`+`WielandtFixedPoint` (実在)
- (12.9) = `RankTwoWitnessData.CKx_not_le_Kprime`

深い multi-step proof (A≤M∩L の p'-part 自明性: P₀=O_p(H)∩M / P₀A Frobenius / Wielandt C_K(A)≠1 /
(8.1.b) abelian ⟹ A centralizes x ⟹ A=1) だが gated でない。**次 /loop iteration で build** (issue 4/task)。
∴ **hub は b を reallocate しない** — b に genuine ungated on-path deep work あり。同種の rank-two witness cluster
(S14: sharpImage/centralizer_le/witness_psi_degree/witness_value_norm_package 等) も stale-docstring 疑い、要精査。

## ⚠ (2026-07-08 続⁶、lane-b /loop) — 続⁵「assemblable」を**訂正**: intersection_le_kernel は multi-lemma deep

続⁵ の「intersection_le_kernel assemblable」は **over-optimistic** ([[verify-port-state-by-number-not-coq-name]]
の自戒: TypeFData field は確認したが (9.1)/Frobenius machinery を未確認で「assemblable」と label した)。
検証で判明:
- **(9.1) = Wielandt order formula** (Pf mmd 04.11: U⋊E Frobenius coprime action on solvable H)。`CoprimeFrobeniusAction`
  + `wielandt_formula_of_perfactor` (WielandtAssembly) の machinery は在るが、**C_K(A)≠1 を出すには `CoprimeFrobeniusAction`
  instance (P₀⋊A ↷ K) の構築が要** — これに Frobenius sub-structure が要る。
- **Frobenius sub-structure (P₀⋊A Frobenius, kernel P₀)**: L=H⋊U Frobenius・P₀≤H・A≤L (A∩H=1) から。
  `IsFrobeniusGroup` = {isNormal, isComplement, ne_bot×2, conj_frobenius (FPF)}。conj_frobenius は
  「a∈A\{1} ⟹ C_{P₀}(a)=1」= 「a∉kernel H ⟹ FPF on H」を要すが、これは complement-conjugacy 経由
  (conj_frobenius は特定 complement U のみ) + subgroup-of setup。**clean な既存 lemma 無し** (prime-complement 版
  `isFrobeniusGroup_of_prime_complement_fixedFree` のみ)。

**⟹ intersection_le_kernel = genuine multi-lemma deep proof** (gated でないが deep)。**decomposition** (次 build 順):
1. **Frobenius sub-structure lemma** (Isaacs Ch06 infra、reusable): Frobenius L=N⋊U で a∉N ⟹ C_N(a)=1
   (element-outside-kernel FPF)、hence P₀ A-invariant ⟹ P₀⋊A Frobenius kernel P₀。
2. **CoprimeFrobeniusAction 構築** + Wielandt formula → C_K(A)≠1。
3. **(8.1.b) abelian argument** (TypeFData.centralizer_le_U1) → A centralizes x → A=1 → M∩L⊆H。

これは deep char/group-theory work (multi-iteration)。b は継続 engage (policy「難所回避しない」)。downstream (12.11 combiner)
は intersection_complements_K (8.13.c1、lane-a) に依然 gated だが、doneness policy 上 intersection_le_kernel 自体が
genuine assertion ゆえ build 価値あり。**5 iteration の char-endgame 精査で判明した構造的事実**: b の char frontier は
一律 deep multi-lemma (survey では「stale/assemblable」に見えても body は深い) — 今後は body 検証を先に。

## ✅ (2026-07-09, lane-b) — (12.11) 第2主張 `intersection_le_kernel` 攻略開始、steps 3-5 + step4 + step10-core landed

続⁶ の「intersection_le_kernel = multi-lemma deep proof」を実際に engage。原文を **10-step 分解**し
(正本 notes/peterfalvi/s14_maximalI.md)、**5 lemma を green で landing** (full build 3944 jobs, AxiomsCheck OK):

**commit 57c4394a (steps 3-5, reusable Frobenius+Wielandt infra)**:
- `IsFrobeniusGroup.frobeniusGroup_sup_of_invariant_le_kernel` (CoprimeAction): Frobenius L kernel N で
  P≤N・Q⊓N=⊥ が P を normalize ⟹ P⊔Q Frobenius kernel P (internal 形)。
- `..._ambient`: ambient-G 形 (engine が subgroupOf transfer 無しで consume)。
- `exists_ne_one_centralized_by_complement_of_kernel_not_centralizes` (WielandtFixedPoint): steps 3-5 統合、
  「P が K 非中心化 ⟹ C_K(A)≠1」(既存 `frobenius_kernel_centralizes_of_complement_fpf` の対偶)。

**commit 96a3f820 (step 4)**:
- `P0_not_le_centralizer_K` (S14): P₀ は K=M_F を非中心化。BG Prop 10.11(b) rank≤1 vs P₀ rank2 の矛盾
  (当初想定の self-centralizing は不要)。helper `MF_eq_Msigma`/`p_not_mem_sigma` (additive)。

**step10-core (Mathlib/Subgroup.lean, uncommitted→commit予定)**:
- `le_of_coprime_card_index_of_normal`: H⊴G + gcd(|S|,[G:H])=1 ⟹ S≤H (normal Hall reduction、general reusable)。

**残 (次 iteration)**: step7 (8.1.b + A,x を complement へ Hall conjugate — 最も subtle、textbook elision)、
step6/8/9 wiring、coprimality (first assertion `intersection_complements_K` sorried-cite + M_F Hall)、
最終 assembly。infra は全て揃った (per-A の C_K(A)≠1 は consumer-ready)。lane-b は継続。

## ✅✅ COMPLETE (2026-07-09, lane-b) — `intersection_le_kernel` (Pf 12.11 第2主張) 完全 proven

続⁶ で「multi-lemma deep proof」と診断した `intersection_le_kernel` (M∩L⊆L_F、S14) を **完全に実証明**
(own proof sorry-free、full build 3945 jobs green、AxiomsCheck OK)。本 session で 10-step 全 assembly を landing:

**commit 履歴** (b): 57c4394a (steps3-5 Frobenius+Wielandt engine) → 96a3f820 (step4 P₀非中心化K) →
5bd0e4e0 (step10 Hall reduction) → f5642384 (step7 keystone 共通 abelian W) → 2a9d2546 (assembly-prep:
P₀⊆L_F, nilpotent p-core) → **0f61c1ea (per-A core + reduction = intersection_le_kernel 完成)**。

**transitive に残る sorried-cite のみ**: 第1主張 `intersection_complements_K` (8.13.c1 = BG §16 Theorem II、
**lane-a gated**、signature 正で cite) + (12.10) `witness_L_sylow_cyclic_of_dvd_complement` (minimality obligation)。

**次の b-frontier**: (12.11) 全体を閉じるには第1主張 `intersection_complements_K` が要 (lane-a の 8.13.c1)。
それが埋まれば下流 (12.12 complement E cyclic → 12.14 → 12.16 Dade → 12.17 矛盾) へ。lane-b は本 issue の
reallocation 議論に該当せず — genuine on-path major result を landing 済。継続。

## ✅✅ (2026-07-09 続、lane-b) — (12.10) minimality core + (8.16) pin + (12.11) 第1主張、3 連 landed

前回の「(12.11) 全体を閉じるには第1主張 (lane-a gated) が要る」を**再診断で覆して完遂**。
S14 実 sorry 10 → 7 (comment-strip)。3 commits (b47a1c66 / 51a7cbba / 59780cc9):

1. **`witness_L_sylow_cyclic_of_dvd_complement` ((12.10) minimality core) 完全 proven**:
   (8.3) 3-case → q < p (case a = TI 排除 typeI 形 / case b = Ω₁ FPF counting q|p²−1 /
   case c = exp(U)|p−1) + (12.8) minimal_p 対偶。reusable infra:
   `IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient` (CoprimeAction) /
   `mem_normalizer_omega1OfAbelian` (OmegaSubgroup) /
   `TypeFData.prime_dvd_sq_sub_one_of_abelian_kernel` / `prime_lt_of_odd_dvd_sq_sub_one` (S14)。
2. **`typeII_centralizer_le_of_mem_mainSubgroup` ((8.16) pin) 完全 proven**: Pf p.48 が
   Nougat MISSING と判明 → PDF 画像読みで復元 — (8.16) 証明 = 「A₁ 上 (8.6.a) で R(a)=1」。
   (8.6.a) = TypePNontrivialCore の TI field (既 encode 済) + N_G(L_F)=L で直接。共通 core
   `typeP_core_centralizer_le_of_mem_fitting` 新設。typeIIIorIV pin は
   `typeIIIorIV_noncyclic_le_fitting` (P₀⊆L_F reduction、(11.9.c)/(9.7.b) = S13 char gated) に narrow 化。
3. **`intersection_complements_K` ((12.11) 第1主張 8.13.c1) 完全 proven**: 「lane-a gated」は
   stale — D(4) tail「N = N_F ⋊ (M∩N)」は proven `signalizer_structure_of_mem_sigmaSharp` の
   IsComplement' conjunct に既在。singleton 𝓜(C_G(x)) で N=M を pin、M':=L で instantiate。
   **⟹ (12.11) 全体が own-proof sorry-free**。

**残 S14 sorry 7**: sibleyTarget_frobI (12.3 case a) / typeIIIorIV_noncyclic_le_fitting
(S13 char gated) / exists_center_omega1_elemAbelian_fpf_of_witness (12.12 — 今回の Ω₁ infra
で attack 可能見込み) / witness_psi_degree + witness_value_norm_package (12.13-15 char) /
allTypeI_fittingIsTI + not_nonTypeICovering (P₂-crux gated)。次 = 文書順で (12.12) T-package。

## ✅✅ (2026-07-09 続³、lane-b) — (12.12) p+1 refinement 完全 proven、S14 実 sorry 7 → 6

前回リストの文書順先頭「(12.12) 系」を完遂 (commits c4cf5a54 / ae0babd8):

1. **`witness_complement_dvd_p_sub_or_add_one` 完全 proven** ((12.12) の p+1 refinement、
   S14 最後の (12.12) sorry)。Singer-cyclic 識別の代わりに proven 済み
   `isCyclic_and_card_dvd_sub_or_add_one_of_fpf_conj_elemAbelian` の **nonscalar 仮説**へ還元し、
   Peterfalvi の A=1 議論を elementwise 実装: |T|=p² → T=Ω₁(P₀)∋x (card 挟み撃ち) /
   scalar e は ⟨x⟩ を normalize (zpowers card 論法 + conj_zpow) / (12.9) N_G(⟨x⟩)≤M +
   (12.11) intersection_le_kernel で e ∈ M⊓L ≤ H / Frobenius disjointness で e=1。
   ⟹ **(12.12) 全体 (complement_cyclic_order_dvd) が own-proof sorry-free**。
2. **`two_mul_card_complement_le`** (2e ≤ p+1、原文 (12.16) の numeric): odd divisor of
   even p∓1 divides half。witness_value_norm_package の h2e conjunct の ℕ-core。

**残 S14 実 sorry 6 の frontier map (精査済み)**:
- `witness_psi_degree` (12.13 ψ(1)=e) + `witness_value_norm_package` (12.14/12.15 束):
  **共通上流 = (12.14) evaluation 機械** (a=0 counting + (7.7.a))。部品状況:
  - ✅ `psi_constant_on_xK` **proven** ((12.14) constancy 半分、h_const 供給可能)
  - ✅ (12.3)/(12.4)/(12.5)/(5.5) = RhoConstancy.lean に sorry-free 済
  - ✅ `witness_L_hypothesis78` proven (witness の Hypothesis78、(7.8.a) agreement 込)
  - 残 = (7.8.a) 分解 α^τ = 1_G − ψ + aΣdᵢχᵢ^{τ₁} + Γ の a=0 counting +
    (7.7.a) evaluation ψ^ρ(x) = χ(x) (S09_Building78C の decomposition 消費)。
  - 注: 原文 (12.16) は ψ(1)=e を直接使わず ψ(x)=χ(x) + χ(x)≡χ(1)=e (L側 1.10.a) 経由。
    h_psix の供給再配線も選択肢 (どちらも (7.7.a) 機械が本丸)。
- `hidx` (4|K'|≤|K|、(8.1.c)): **組立可能と診断** — frobenius_HU0 (U₀ FPF on K) +
  p ∣ exp U₀ (Cauchy) + coprime descent to K/K' (coprime_fixedPoints_quotient) +
  IsPGroup.card_modEq_card_fixedPoints → |K/K'| ≡ 1 (mod p) ≥ p+1 ≥ 4。ambient 化要
  (~100-150 行)。**次 iteration 候補 (文書順では (12.14) 機械が先だが hidx は独立部品)**。
- `sibleyTarget_frobI` (12.3 case a TI): 実 consumer 無し (witness route は (b)/(c) dispatch、
  docstring 言及のみ) — off-path 保留妥当。
- `typeIIIorIV_noncyclic_le_fitting`: S13 char gated (変化なし)。
- `allTypeI_fittingIsTI` + `not_nonTypeICovering`: P₂-crux gated (変化なし)。

## ✅ (2026-07-09 続⁴、lane-b) — hidx (4|K'| ≤ |K|、8.1.c) 完全 proven

frontier map の「hidx 組立可能」を実施 (commit f349de80):
`four_mul_card_Kprime_le` + helper `p_not_dvd_card_K` (WitnessSylowCyclic)。
frobenius_HU0 ambient FPF → quotientMulAutHom descent → Isaacs Cor 3.28 固定点
lift → IsPGroup.card_modEq_card_fixedPoints で |K/K'| ≡ 1 (mod p) ≥ p+1 ≥ 4。

**witness_value_norm_package conjunct 供給状況**: h_const ✅ (psi_constant_on_xK proven 済) /
h2e ✅ (two_mul_card_complement_le) / hidx ✅ (本 commit) / 残 = h_psig_int ((12.15) ℤ-値) +
hA ((12.15) ρM relation) + hB ((7.8.b) — S09 zetaNuRhoNormSqGeOfDade 接続、witness_L_hypothesis78
proven 済ゆえ配線距離短い) + hC ((7.3)+(8.17)) + mval 束ね。
**次 iteration**: (a) hB 接続 (Hypothesis78 → zetaNuRhoNormSqGeOfDade → dade.psi 形へ) or
(b) (12.14) evaluation 機械 (a=0 counting + (7.7.a)、witness_psi_degree と h_psig_int の共通上流)。
文書順は (12.14) が先。

## ✅✅ (2026-07-09 続⁴、lane-b) — (12.14) の数学的 engine 完成 (a=0 + two-sided (7.7.a) + ρ-collapse)

(12.14) ψ(xg) = ψ^ρ(x) = χ(x) の 3 部品 + ρ-bridging を全て実証明
(commits 952f3f77 / 976fdd7c / 131c99a1、全 full build green + AxiomsCheck OK):

1. **a = 0 counting** (S09_CertificateDischarge):
   - `betaDecomp_a_eq_zero_of_p_bounds` (arithmetic core): ‖β‖²=e+1 + 直交展開
     (betaNormSq_eq_of_source_orthogonal) + ‖Γ‖²≥0 → ((h−1)/e)a²−2a ≤ e−1、
     p²≤h + 2e≤p+1 ((12.12)) + p≥3 → a=0 (nlinarith 2 case)。
   - `betaDecompOfDade_a_eq_zero`: hypothesis78OfDade/betaDecompOfDade 実現形への適用
     (SourceDiffNormEvaluation / univ.erase degree sum = family_degree_sum を discharge)。
2. **two-sided (7.7.a) evaluation** (S09_Building78C):
   - `zeta0_decomp_on_A`: ζ₀ 自身の A 上 (7.7.a) 分解 (eq_zero_on_A_of_inner_zero は
     対象非 supported でも supportedProj 経由で効く、という構造的発見)。
   - `chiRho_apply_eq_zeta0_of_inner_tau_uniform`: 係数 uniform c_i = −d_i なら
     χ^ρ(x) = ζ₀(x)。**a=0 が c_{ind1H} = a−1 = −1 = −d_{ind1H} を uniform 化**
     (ind1H の場合分けが消える)。
3. **ρ-collapse** (Hypothesis71): `chiRho_apply_eq_of_forall_coset` — χ constant on
   a·H(a) → χ^ρ(a) = χ(a)。

**残る (12.14) 完成 wire (次 iteration)**: witness 文脈 discharge —
(i) hc uniform: 既存 `cCoeff_nu_zeta_zero_eq_neg_d` (i≠ind1H) + a=0 + d_{ind1H}=1;
(ii) hspan: CF(L,A) spanning (S09_Building78C 74-160 の induced spanning から);
(iii) hconst: witness Dade datum の H(x) = R(x) ⊆ K 構造 + proven `psi_constant_on_xK`;
(iv) assembly → witness_psi_degree 代替の h_psix 再配線 or (12.14) full statement。
witness_L_zeta_bound (hB、既 proven) と同じ供給ライン。

## ⚖️ HUB carve-out (2026-07-09 監視 tick — merge 03fd8474): 2038 供給編集権

**b の a 所有 S09 機構ファイルへの additive 編集を retroactive carve-out で受理** (3002 供給編集権 = ユーザー裁定 2026-07-05 の先例と同型、hub 自律裁定):

- **対象実例**: `S09_Building78C.lean` (+82, `zeta0_decomp_on_A` / `chiRho_apply_eq_zeta0_of_inner_tau_uniform`)、`S09_NonexistenceCertain/Hypothesis71.lean` (+19, `chiRho_apply_eq_of_forall_coset`)。いずれも新 theorem のみ・既存宣言改変なし。
- **hub 検証**: (i) 純 additive、(ii) 全て proven (sorry/axiom 追加なし)、(iii) 用途 = 本 issue (12.14) の chiRho 供給 chain (χ^ρ 機構は S09 に在住、0089 裁定で cite 先)、(iv) a の並行編集ゼロ (`main..a` = 0)。
- **⟹ 恒久ルール (本 issue の (12.14) 供給完了まで)**: b は **2038 (12.14) 供給 chain に必要な a 所有 S09 chiRho 機構ファイルへの純 additive・proven な helper 追加**を行ってよい (条件は 3002 先例と同一: additive / proven / 用途明示 / self-flag)。既存宣言の statement・proof 改変は従来どおり逸脱。**(12.14) 供給完了で失効**。

## ⚠ WIP (2026-07-10 00:24、lane-b /loop 休止前 snapshot) — ofDade wrapper が whnf-wall、診断ログ

`chiRho_apply_eq_zeta0_induced` (Ind-family 完成形) は **landed** (afa72d2f)。残る最終 wire
`chiRho_nu_zeta0_apply_eq_zeta0_ofDade` (S09_CertificateDischarge、working tree に WIP) が
**whnf-wall**: 最終 `refine chiRho_apply_eq_zeta0_induced …` の unification が 3.2M heartbeats
でも爆発 ([[lean-giant-declaration-debugging]] 系)。

**診断確定事項** (bisect 済):
- 引数 elaboration + `set H78 := hypothesis78OfDade …` + ha0 (betaDecompOfDade_a_eq_zero 適用)
  + hdind + hc (uniform 係数、hβ の H78.beta defeq bridge 込み) までは **800k 内で green**
  (final application を sorry にすると通る)。
- 犯人 = **最終 refine/exact 単独** (hc hole を sorry にしても爆発 → hc unify でなく他引数
  or 結論 or context)。`clear_value H78; clear hH78 ha ha0` を直前に挿入しても爆発
  (let-body 除去では不十分)。
- 次の試行候補: (a) `set H78` を完全排除しフル適用形で書く (context から
  hypothesis78OfDade 項を消す)、(b) 最終 application を **別 theorem に分離**
  (hc/hζ0norm 等を引数に取る thin wrapper — 巨大 context と切り離して unify)、
  (c) chiRho_apply_eq_zeta0_induced 側の暗黙引数を明示指定 (unify の探索を殺す)。
  (b) が最有望: hc の型は H78 非依存 (明示形) なので、hc を持ち出せば ofDade context 不要。

working tree: S09_CertificateDischarge.lean に WIP (clear_value 版、build 赤)。
original snapshot = scratchpad/S09_CertificateDischarge.lean.bak。

## ✅✅ (2026-07-10、lane-b 再開) — whnf-wall 突破、`chiRho_nu_zeta0_apply_eq_zeta0_ofDade` 完全 proven

休止前 snapshot の whnf-wall を **root-cause 特定して解決** (S09_CertificateDischarge sorry 0 維持)。

**診断経過** (試行 (b)+(c) 複合で決着):
1. `@` 全明示適用 (instance synthesis / HO unification 排除) → **依然爆発** → 犯人は synthesis でない。
2. `set_option diagnostics true` → **`Subgroup.toSubmonoid ↦ 1,982,312 unfold** / SetLike.coe 116k /
   Cardinal.mk→Quotient.mk 9.7k` — defeq が `↥(H.subgroupOf L)` の membership/instance 実装比較に降下。
3. 最終 application を軽量 wrapper `chiRho_apply_eq_zeta0_sharp` (hc を仮説に取る、ofDade context 無し)
   に分離 → **wrapper 単体はデフォルト 200k で green** → K 具体項自体は無罪、重い context との相互作用。
4. wrapper 呼び出しでも χ 明示書き下しでは爆発 → **真犯人 = exact 内に新規書き下した χ 項
   `ν (induce …)` の再 elaboration が、statement elaboration と instance 実装レベルで異なる Expr を生成**
   し、goal との defeq が instance 項の中身比較 (Subgroup.toSubmonoid の海) へ降下。
5. **χ を `_` にして goal からの unification で同一 Expr を拾わせる → 即 green** (800k 内)。

**landed 形**: `chiRho_apply_eq_zeta0_sharp` (sharp-support 幾何 discharge 済の isolation wrapper、
reusable) + `chiRho_nu_zeta0_apply_eq_zeta0_ofDade` (a=0 counting → c 係数 uniform 化 → two-sided
(7.7.a) evaluation、ψ^ρ(x) = ζ₀(x) on A)。**(12.14) の evaluation 本体が ofDade 実現形で完結**。

**残 wire (次)**: (iii) hconst (witness Dade datum の H(x)=R(x)⊆K + proven `psi_constant_on_xK`) で
ρ-collapse `chiRho_apply_eq_of_forall_coset` → ψ(x) = ψ^ρ(x) = ζ₀(x)、(iv) S14 witness 文脈
(`witness_psi_degree` / `witness_value_norm_package` h_psix) への配線。

## ✅✅ (2026-07-10 続、lane-b) — **(12.14) witness full form 完成 + h_psix 配線 + witness_psi_degree 削除** (S14 実 sorry 6→5)

上記「残 wire」(iii)(iv) を完遂 (commits 9c80627f / 49607ba9、full build 4131 green・AxiomsCheck 2148 OK):

1. **ρ-collapse chain (9c80627f)**: `witness_x_mem_L`/`witness_x_mem_typeIA` (x∈P₀⊆L_F、x∈A(L)) /
   `witness_maximalContaining_centralizer_eq_singleton` (Theorem-D singleton 𝓜(C_G(x))={M}、x は
   L-σ-sharp escaping) / `witness_ftSupportKernel_le_K` (R(x)=(N[x])_σ⊓C_G(x)≤K、N[x]=M pin +
   MF_eq_Msigma) / `witness_chiRho_apply_eq_of_forall_K` (x·K constancy → χ^ρ(x)=χ(x))。
2. **witness full form (49607ba9)**: `witness_dade_psi_apply_x_eq_chi` — witness の (12.13) dade で
   **ψ(x) = χ(x)** (constancy [psi_constant_on_xK 初配線、hLM = 新 `witness_L_not_conj_M`:
   Msigma_conj_smul 輸送で p∣|L_σ| vs p∤|M_σ|] + collapse + evaluation の 3 部品合成)。
   供給部品: `counterexample_three_le_p` / `witness_p_sq_le_card_kernel` / `witness_two_mul_index_le_p_add_one`。
3. **h_psix route B**: `exists_counterexample_dade_data` の h_psix を「ψ(x)=χ(x) + χ(x)≡χ(1)=e
   (L側 1.10.a `exists_integral_apply_sub_of_commute`)」に再配線。原文どおり ψ(1)=e 不要 →
   **`witness_psi_degree` (sorry) を削除**。
4. **⚠ 循環バグ発見+解消**: `Hypothesis.typeIA_eq_sharp` は (12.7) `typeI_frobenius`=`pi_empty`=
   `counterexample_contradiction` 経由 — **(12.16) supply chain から使うと論理循環** (Lean の前方参照
   エラーとして顕在化; 既存 `witness_L_hypothesis78`/`witness_L_zeta_bound`/`witness_L_hzeta0nu` にも
   潜在していた = witness_value_norm_package が sorry のため未検出だった)。新 `witness_typeIA_eq_sharp`
   ((12.10) `witness_L_frobenius` 経由、(12.7)-free) に全張り替え。`witness_L_hzeta0nu` は hAH 仮説
   引数化 (S16 下流 2 呼び出し [lane-c files PairingCoherence/ComparingLM] は文脈既存供給で 1-line 追従
   — signature 変更に伴う build 修復の最小機械的追従、self-flag)。

**残 S14 on-path sorry = `witness_value_norm_package` 1 つ** (+P₂-crux gated 2)。conjunct 状況:
h_const ✅ (psi_constant_on_xK、配線実証済) / h2e ✅ / hidx ✅ / hB ✅ (witness_L_zeta_bound、H78→dade.psi
形変換要) / **残 = h_psig_int ((12.15) 前半 constancy on K−K′ + proven rhoM_integer_values) +
hA ((12.15) ρM norm relation) + hC ((7.3)+(8.17))**。次 = 文書順で (12.15)。

## HUB pointer (2026-07-10 監視 tick)

issues/3004 の HUB RULING に **b 宛 work item 2 件**: 裁定 2 = S15_SAndT `TypeIOrthogonalityGridData`
の (13.19) 忠実 restate (`betaL_eta_independent` は over-strong で除去要)、裁定 3 = V-side
`exists_M_structural`/`complement_inf_P_structure` の無条件 index=pq を (13.17.c)-dual 二分岐へ
weaken ((14.5) の除外論法は q<p 非対称で V-side に双対化できない)。詳細 = issues/3004 HUB RULING。

## ✅ (2026-07-10 続²、lane-b /loop) — (12.5) 完全 proven + (12.15) 攻略設計 (次セッション用)

**landed (commit b2df1a76)**: `chiRhoCF_restrict_constant_off_derived` (RhoConstancy) = **Peterfalvi
(12.5) 完成** — ψ ⊥ coherent images ⟹ Res_H(ψ^ρ) constant on H−H′。既存 proven 部品
(`chiRhoCF_restrict_inner_eq_of_equal_degree` + `commutator_induce_constituents_apply_one_eq` +
`inner_induce_constituent_eq_of_apply_one_eq` + `constant_off_normal_of_inner_block_const`) の合成のみ。
+ `ClassFunction.innerSum_star_comm`/`inner_star_comm` (shared infra)。

**(12.15) 攻略設計 (調査済、次セッションの実装キュー)** — 目標 = witness_value_norm_package の
h_psig_int (ψ(g)=mval) + hA (ρM norm):

1. **(12.5) M 版 (coh-free 化) が先決**: 現 `chiRhoCF_restrict_constant_off_derived` は
   coh : IsCoherent (家族全体) を要求 — witness L 用は OK だが **M (counterexample、非 Frobenius) には
   家族 coherence が無い**。原文 (12.5) は (12.2)+(5.7) の **pairwise coherence** ({χ₁,χ₂,χ̄₁,χ̄₂}) しか
   使わない。coh 使用箇所は `chiRhoCF_inner_eq_of_equal_degree` の
   `coh.extends_on_supported` 1 箇所のみ — 必要なのは **⟨τ(χ₁−χ₂), ψ⟩ = 0**、その supply は
   τ(χ₁−χ₂) ∈ ℤ[R(χ₁)∪R(χ₂)] ((5.5)) + horth (Rset 形、psi_constant_on_xK と同一供給)。
   **実装**: `exists_uniform_image_of_constituents` (RhoConstancy:789、単一 χ の conjugate-closed
   constituent set T の uniform coherent image、(12.4) pin (a) の機械) を **等次数 2-character 版**
   (T := constituents(χ₁) ∪ constituents(χ₂) ∪ conj、等次数なので同じ isometry_difference_pair_structure
   が効く) に拡張 → (χ₁−χ₂)^τ ∈ ℤ[R(χ₁)∪R(χ₂)] → M 版係数一致 (chiRho_adjoint reciprocity 経由、
   coh-free) → (12.5) M 版。
2. **第 1 主張 ψ^{ρM}(g) = ψ(g) on K^#**: chiRho_apply_eq_of_forall_coset + H(g) 場合分け —
   non-escaping: H(g)=⊥ trivial。escaping: H(g) = FT_signalizer g ≤ (N[g])_σ = (N[g])_F
   (N[g] type I、(8.13.c4))、ψ constant on g·N_F は **N 側 (12.4)**
   (orthogonal_character_constant_on_coset hypN) + cross-orth ψ ⊥ R_N。N ≁ L は「C_{N_F}(g) ≠ 1
   (8.13.c1) ⟹ N not Frobenius w/ kernel N_F」vs「L Frobenius (12.10)」+ **Frobenius 性の conj
   transport** (witness_L_not_conj_M の Msigma_conj_smul と同型の infra、要新設)。
3. **合成**: 1+2 → ψ constant on K−K′ (`mem_commutator_subgroupOf_iff` bridge、
   derivedInG K = ctr.Kprime は Kprime_eq: rfl)。
4. **h_psig_int**: 3 + `rhoM_integer_values` (proven、constancy 入力)。
5. **hA**: ‖ψ^{ρM}‖²_M ≥ (|K−K′|/|M|)·mval² — chiRho の norm 展開 + 3 の定数値 (K−K′ 上 |ψ^{ρM}| = |mval|)。

実装順: 1a (2-char uniform image) → 1b (M 係数一致) → 1c ((12.5) M 版) → 2 → 3 → 4 → 5。

## ✅✅ (2026-07-10 続³、lane-b /loop) — **(12.15) 実装キュー step 1 完遂: (12.5) M 版 coh-free 化** (commit f4255870)

新 leaf `S14_MaximalI/PairCoherence.lean` (706 行、全 sorry-free、標準 axioms のみ):

- **(1.5.c) Sset facts**: `Sset_pairwise_orthogonal` (`induce_eq_induce_iff_conj` +
  `inner_induce_eq_zero_of_not_conj` 既存 infra で直接) / `decomposition_{inner_self_card,
  inner_conj_eq_zero,ne_conj,apply_one_pos_natCast,mem_ZIrr}` / 制約 count 補題 2 本。
- **`RsetImageFamily`** ((12.2.b) bundled): R(χ) を `OrthonormalCharacterImageFamily` に束ね
  `(χ−χ̄)^τ = Σ_{R(χ)} α` (cross-block 直交 = `constituentDiff_tau_inner_eq_zero_of_ne_across`)。
- **`pair_tau_diff_mem_span`**: 等次数 χ₁,χ₂ ∈ S で `τ(χ₁−χ₂) ∈ ℤ[R(χ₁)∪R(χ₂)]`。
- **`chiRhoCF_restrict_constant_off_derived_ofData`** = **(12.5) M 版** (horth は Rset 形 =
  原文の仮説形)。

**⚠ 設計変更 (前セッション設計 1a からの deviation、重要)**: 設計was「`exists_uniform_image_of_constituents`
を等次数 2-character 版に拡張 (T := S(χ₁)∪S(χ₂)∪conj)」— これは**数学的ギャップあり**:
cross-family の constituent 次数 d₁=d₂ は自動でない ((1.7.c): d = |L:I_L(θ)|·θ(1)、inertia 指数は
θ ごとに異なりうる)。**採用 route = 原文/Coq 忠実の character-level quadruple coherence**:
{χ₁,χ₂,χ̄₁,χ̄₂} (等次数、reducible メンバー) に norm-general (5.7) engine
`uniform_degree_coherence_of_families` (S07_PivotCoherence 既存!) を適用 → norm-general (5.5)
(`ofProjection (ψ:=0)` + `eq_sum_of_psi_eq_zero`、これも既存) で各 `coh.extension χᵢ ∈ ℤ[R(χᵢ)]`
(`coherent_extension_mem_span_Rset_of_mem` 新設、再利用可能)。Coq `pair_degree_coherence` +
`mem_coherent_sum_subseq` (PFsection5) と同構造。

**次 = (12.15) step 2** (キュー継続): 第 1 主張 ψ^{ρM}(g) = ψ(g) on K^# —
`chiRho_apply_eq_of_forall_coset` + H(g) 場合分け (non-escaping trivial / escaping:
(8.13.c4) N type I + (8.13.c1) C_{N_F}(g)≠1 → N not-Frobenius-with-kernel-N_F → N ≁ L、
N 側 (12.4) `orthogonal_character_constant_on_coset` + cross-orth ψ ⊥ R_N)。
要新設 infra: Frobenius 性の conj transport (witness_L_not_conj_M の Msigma_conj_smul 同型)。
その後 step 3 (K−K′ constancy 合成、(12.5) M 版が今回できたので配線可能) → 4 (h_psig_int) → 5 (hA)。

## ✅ (2026-07-10 続⁴、lane-b /loop) — (12.15) step 2-3 の下部構造 3 commits (ebbca083 / 51fc5484)

1. **(12.5)-M chain の非 Frobenius 一般化** (ebbca083): hAH 等式 (A(L)=H^#、Frobenius 専用) を
   (hsub : H^# ⊆ A(M)) + (h1A : 1 ∉ A(M)) に置換 — 供給補題 `sharpSubgroup_H_subset_typeIA` /
   `one_notMem_typeIA` (MaximalSubgroupType def-site、additive)。
   **合成 lemma `psi_constant_on_kernel_sub_derived_ofData`** (PairCoherence 末尾、clean axioms):
   ψ constant on H−H′ ← (12.5)-M + claim-1 evaluation (仮説 `heval` にパラメータ化) +
   `mem_commutator_subgroupOf_iff` bridge。
2. **claim-1 前提 2 本** (51fc5484、MinimalCounterexample):
   `counterexample_not_frobenius_MF` ((8.13.c4) furthermore の反駁形 — escape 構造の IsTypeP2 枝を殺す) /
   `witness_L_not_conj_of_kernel_centralizer_ne_bot` ((12.15) N≁L step、element-level 転送)。

**残 = claim-1 組立** (`counterexample_chiRho_apply_eq_on_K_sharp`、次 iteration の主タスク)。設計確定済:
```
∀ g ∈ ctr.K, g ≠ 1 → hypM.toHypothesis71.chiRho ψ ⟨g, K≤M⟩ = ψ g
```
via `chiRho_apply_eq_of_forall_coset hypM.toHypothesis71 ψ hgA hcoset` (L-side
`witness_chiRho_apply_eq_of_forall_K` のパターン、DadeContradiction:381-396 mirror):
- hgA : g ∈ typeIA M = `sharpSubgroup_H_subset_typeIA` + hHK (hypM.H=K)。
- hcoset : ∀ y ∈ H(g)=ftSupportKernel、ψ(g·y)=ψ(g)。branch `hypM.dadeData.H_eq_ftSupportKernel`:
  - non-escaping: `ftSupportKernel_eq_bot_of_not_escaping` → y=1 trivial。
  - escaping: g ∈ sigmaSharp M (K=Msigma via MF_eq_Msigma + g≠1)、
    `exists_RData_escape_structure hG ctr.M_maximal hx hesc` → N conjuncts:
    (i) FT_signalizerBase g = N pin: `maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`
        → 𝓜(C_G(g))={N₀}、escape-N ∈ 𝓜 → N=N₀; base = choose ∈ {N₀}
        (witness_ftSupportKernel_le_K:363-367 パターン) → ftSupportKernel g = Msigma N ⊓ C_G(g) = R。
    (ii) N type F (P2 枝は counterexample_not_frobenius_MF で殺す — D(4) の furthermore package が
        M-Frobenius-over-Msigma を出すので直接矛盾)。
    (iii) hypN := exists_typeI_hypothesis hG hNmax (isTypeI_of_isTypeF ... — N typeF → IsTypeI N の
        変換 lemma 要確認、issue 2038 続³ で言及の `isTypeI_of_isTypeF`)。
    (iv) g ∈ N (C_G(g)∋g≤N)、g ∉ N_F: escape 構造の `x ∈ ASet N ⊤ \ Msigma N` conjunct +
        maxNilpotentNormalHall N = Msigma N (`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`)。
    (v) C_{N_F}(g) ≠ ⊥: R ≠ ⊥ conjunct (Msigma N ⊓ C ≠ ⊥) + 同上の =。
    (vi) N ≁ L: `witness_L_not_conj_of_kernel_centralizer_ne_bot` (iv)(v) を食わせる。
    (vii) N-side (12.4): `orthogonal_character_constant_on_coset hG hypN data_N horth_N hgN hgNF`
        (data_N = `character_decomposition_and_dade_domain`、horth_N =
        `coherent_extension_constituent_orthogonal_Rset_of_nonconjugate` w/ (vi)、
        psi_constant_on_xK:214-230 の M→N 置換 mirror) → ψ constant on g·N_F ⊇ g·R ✓。
- 注: chiRho vs chiRhoCF の apply bridge (`chiRhoCF` = CF-bundle) — witness 側の対応箇所を mirror。
最後に h_psig_int 配線: hconst := psi_constant_on_kernel_sub_derived_ofData (heval := claim-1) →
`rhoM_integer_values`。その後 hA/hC (norm 側、(7.3)+(8.17))。

## ✅✅ (2026-07-10 続⁵、lane-b /loop) — **(12.15) 全 3 主張 proven** (commit 1f2706aa)

新 leaf `S14_MaximalI/RhoMEvaluation.lean` — 実装キュー step 2-4 完遂 (own-proof 全て sorry-free):

1. **claim-1 `counterexample_chiRho_eval_of_mem_K_sharp`** (ψ^{ρM}(g)=ψ(g) on K^#):
   H(g) 場合分け。escaping 枝 = **BG Theorem D(4) `exists_RData_escape_structure` (それ自体
   fully sorry-free と判明!)** → N=N[g] pin (σ-sharp escape singleton + FT_signalizerBase choose) →
   P₂ 枝は `counterexample_not_frobenius_MF` で殺す ((8.13.c4) furthermore package が M-Frobenius を
   出すので直撃) → N type I (`isTypeI_of_isTypeF`、clean) + N_F=N_σ → g∈N∖N_F・C_{N_F}(g)≠1 →
   N≁L (`witness_L_not_conj_of_kernel_centralizer_ne_bot`) → N-side (12.4) で ψ constant on g·N_F。
2. **claim-2 `counterexample_psi_constant_on_K_sub_Kprime`**: (12.5)-M 合成 lemma + claim-1 (heval 供給)。
3. **claim-3 `counterexample_psi_int_on_K_sub_Kprime`**: claim-2 → proven `rhoM_integer_values`。

transitive sorry は既知 residual のみ (`exists_typeI_hypothesis` producer 系 / witness chain)。
D(4)/isTypeI_of_isTypeF/(12.2.a) producer は clean axioms。

**⟹ witness_value_norm_package の conjunct 状況更新**: h_const ✅ / h_psig_int ✅ (今回、
counterexample_psi_int_* を dade.psi = coh.extension chi0 で instantiate + mval obtain) /
h2e ✅ / hidx ✅ / **残 = hB 配線 (witness_L_zeta_bound → dade.psi 形) + hA ((12.15) norm 関係、
‖ψ^{ρM}‖² ≥ (|K−K′|/|M|)mval²、claim-1+2 と chiRho norm 展開) + hC ((7.3)+(8.17) 分離)**。
次 iteration = hA (claim-1/2 の直接続き、chiRhoCF ノルムを K−K′ 上で下から評価) → hB → hC。

## ✅ (2026-07-10 続⁶、lane-b /loop) — **hA landed: A₁(M)-based ρM + norm 下界** (commit 86255c2d)

キュー step 5 (hA)。RhoMEvaluation に追加:
- **`hypothesis71SharpKernel`** = (12.15) が定義するとおりの **A₁(M)=K^# ベース ρM**
  (S04/FullDadeIsometryData/HConjInvariant の `.restrict` 3 点、S12 type-P toHypothesis71 パターン、
  own axioms clean)。**⚠ 設計上の要点**: (12.16) の hC は (7.3) 上界が thickened Ã₁(M) 上を走り
  (8.17) で Ã₁(L) と disjoint であることを要するため、A(M) 全体ベースの hypM.toHypothesis71 では
  **不可** — A₁ 版が必須 (このため claim-1 を constancy core + wrapper に refactor し A₁ 版 eval
  `counterexample_chiRhoA1_eval_of_mem_K_sharp` を追加)。
- **`counterexample_chiRhoA1_normSq_ge` (hA)**: ‖ψ^{ρM}‖² ≥ (|K|−|K′|)/|M|·mval² —
  ノルム展開 |M|⁻¹Σ_m + K−K′ の |K|−|K′| 点 (claims 1-3 で値 mval) でサンプリング。

**残 (witness_value_norm_package 完成まで)**:
- **hB**: `witness_L_zeta_bound` (proven、H78 形) → dade.psi 形へ変換 (配線)。normRho の定義を
  L-side ‖ψ^ρ‖² に取り hB = 1 − e/|H| ≤ normRho。
- **hC**: normRhoM + normRho < 1。部品: (i) (7.3) `chiRho_integral_inequality` を両側に適用
  (L-side は hyp.toHypothesis71 [A(L)=A₁(L) Frobenius ✓]、M-side は hypothesis71SharpKernel)、
  (ii) **thickened dadeSupport disjointness**: Ã₁(M) ∩ Ã(L) = ∅ ((8.17)/(8.18.c) — Lean 側の
  dadeSupport-disjointness lemma を要調査/新設: `nonconjugate_diffImage_inner_zero` が使う
  (8.18.c) 幾何の supply を確認)、(iii) ‖ψ‖² = 1 (coh isometry: ⟨ext χ₀, ext χ₀⟩ = ⟨χ₀,χ₀⟩ = 1)、
  (iv) 厳密不等号: ψ(1) ≠ 0 (ψ ∈ ZIrr, ‖ψ‖=1 → ψ = ±irreducible → ψ(1) = ±deg ≠ 0;
  (5.5) E-subsum |E|=1 route)。両 (7.3) 和 + 1∉Ã 系 + ψ(1)² 項で < 1。
- 最後: witness_value_norm_package の sorry を conjunct 供給で置換 (mval := claim-3 の witness g、
  normRhoM := ‖chiRhoCF_{A₁}ψ‖².re、normRho := L-side)。

## 📋 (2026-07-10 続⁷、lane-b /loop) — hB/hC 完全配線プラン (調査完了、次 iteration 実装)

**hC の鍵発見**: 必要な対称 disjointness Ã₁(L)∩Ã₁(M)=∅ は、既存
`nonconjugate_thickened_mixed_disjoint_or_swap` (RhoConstancy:239、proven) の mixed 二択
(Disjoint Ã(L₁) Ã₁(L₂) ∨ swap) の**どちらの枝からも従う** (Ã₁ ⊆ Ã 単調性のみ) — 新幾何不要。
sets は `S10.ftThickenedSupport Lᵢ (typeIA/A1)` 形。

**hC 組立** (normRhoM + normRho < 1):
1. (7.3) `chiRho_integral_inequality` (Hypothesis71:439、proven) を両側に:
   L-side H71 = hyp.toHypothesis71 (A(L)=A₁(L) Frobenius)、M-side = `hypothesis71SharpKernel`。
   hiso 供給: L = `(hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry`、
   M = restricted 版 (S12 `toFamilyHypothesis71` の isDadeIsometry パターン)。
2. 上界和の統合: dadeSupport(L-datum) ∩ dadeSupport(M-A₁-datum) = ∅。bridge 要:
   S04.Hypothesis.dadeSupport (⋃ conjugatesOfSet (hCoset a)) ↔ S10.ftThickenedSupport (faithful
   datum で一致するはず — S10 に bridge lemma を grep/新設)。A₁ 側の集合同定:
   `A1 L .I = sharpSubgroup (mainSubgroup L .I)` と私の `sharpSubgroup hypM.typeI.typeF.H` の一致
   (mainSubgroup .I の def 確認 + H_eq)。
3. Σ_{Ã₁(M) ⊔ Ã(L)} ‖ψ‖² ≤ Σ_{G∖{1}} ‖ψ‖² = |G|(‖ψ‖²) − ‖ψ(1)‖²:
   1 ∉ 両 support = `S04.Hypothesis.one_notMem_dadeSupport` (proven、AxiomsCheck 済) ×2。
4. ‖ψ‖² = 1: `coh.extension_inner_eq` + χ₀ irreducible norm-1。
5. **厳密性 ψ(1) ≠ 0**: ψ ∈ ZIrr ∧ ⟨ψ,ψ⟩=1 → ψ = ±μ (単一 irreducible) → ψ(1) = ±deg ≠ 0。
   Parseval `inner_self_eq_sum_sq_of_repr` (ZIrrFourier:222) で Σn_i²=1 → 単一 ±1 (新 lemma ~40 行)。

**hB 配線**: `witness_L_zeta_bound` (DadeContradiction:1506、proven) は自前 (hyp, H78) を ∃-生成 —
package の (hyp, coh, dade) に**結合する版が必要**: (a) proof body を (hyp)(coh) 引数版に refactor
(witness_L_hypothesis_frobenius / coherence dispatch 部分だけが hyp/coh 生成箇所)、(b) H78 の
zetaDistinct を **dade.chi の family-index に placed** する必要 (現 `exists_witness_placed_family` は
θ0 = degree-e member を place — dade.chi も `exists_distinguished_char` の degree-e member なので
**同一 index 0 に押し込めるか、placed-family の θ0 を dade.chi そのものにする変種**を作る)。
その後 normRho := H78.zetaNuRhoNormSq = ‖hyp.toHypothesis71.chiRhoCF (ν ζ₀)‖².re が
‖chiRhoCF dade.psi‖².re に一致 (ν ζ₀ = coh.extension chi0 = dade.psi の同定、H78 構成時に ν :=
coh.extension 線形化 + ζ₀ := chi0 で組む)。
**最終**: witness_value_norm_package の sorry を全 conjunct 供給で置換
(mval/h_psig_int = counterexample_psi_int_*、normRhoM = A₁-chiRhoCF norm、normRho = 上記、
hA = counterexample_chiRhoA1_normSq_ge、hB/hC = 本プラン)。

## ✅✅✅ COMPLETE (2026-07-10 続⁸、lane-b 再開) — **witness_value_norm_package 完全 proven、(12.16) norm contract 完結** (S14 on-path ungated sorry = 0)

続⁷ の hB/hC 配線プランを完遂 (4 commits: d223ed1a split / bb86103c hB / c1bfe83f hC-prep / 3fb0aec7 hC+fill)。
full build **4140 jobs green + AxiomsCheck OK**。S14 実 sorry 6→**4** (残 = sibleyTarget_frobI off-path /
typeIIIorIV S13-gated / P₂-crux 2 のみ = **ungated on-path 0**)。

1. **分割 (d223ed1a)**: DadeContradiction 2075 行 → 3 leaf: `DadeContradiction` (1416、(12.13)-(12.15) 部品) /
   **`NormPackage`** (新、import RhoMEvaluation — CounterexampleDadeData/witness_value_norm_package/
   exists_counterexample_dade_data/counterexample_contradiction/pi_empty/typeI_frobenius/typeIA_eq_sharp) /
   **`TypeICovering`** (新、(12.17)+theorem88)。witness_value_norm_package が ρM 機構 (RhoMEvaluation) を
   cite できる位置に移動 — これが分割の必然理由 (import 方向)。
2. **hB (bb86103c)**: `witness_dade_psi_rho_norm_ge` — witness_L_zeta_bound の (hyp,coh,dade)-parametric 版。
   鍵 = placed family を **dade.chi に anchor** (exists_placed_induced_family χdist:=dade.chi) →
   ζ₀ = Ind(θ0) = dade.chi → zetaNuRhoNormSqGeOfDade の bound が ‖chiRhoCF dade.psi‖² に直接着地
   (kernelOrder/complementIndex は rfl、zetaNuRhoNormSq は show+rw[h0,←hψeq] 1 発 — whnf-wall 無し)。
3. **hC prep (c1bfe83f)**: `ftThickenedSupport_mono` / `dadeSupport_restrict_subset_ftThickenedSupport`
   (restrict datum の §4 support ⊆ Ã(A₁)) / `A1_eq_sharpSubgroup_H` / `hypothesis71SharpKernel_dadeSupport_subset`。
   hypothesis71SharpKernel の hsub/hnorm を top-level (`sharpSubgroup_H_conj_mem`) に抽出 (unification 用)。
   **ψ(1)≠0 は新規不要**: 既存 `one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one` (InducedIrreducible、
   (13.10) Parseval 用に既設) が丁度 — ZIrrFourier に書いた draft は重複で破棄 (claim-before-build の教訓)。
4. **hC + fill (3fb0aec7)**: `witness_dade_psi_rhoM_rho_normSq_lt_one` — (7.3) 両側 (L=toHypothesis71 /
   M=hypothesis71SharpKernel+restricted isometry) + **(8.18.c) mixed disjointness はどちらの枝でも十分**
   (witness は A(L)=A₁(L) ゆえ swap 枝も A1_eq+mono で落ちる、続⁷ の鍵発見どおり) + 1∉support ×2 +
   ‖ψ‖²=1 (coh isometry + Frobenius induced) + ‖ψ(1)‖²≥1 で strict。witness_value_norm_package は
   7 conjunct 全供給 (h_const=psi_constant_on_xK / mval=counterexample_psi_int_* / h2e / hidx /
   hA=counterexample_chiRhoA1_normSq_ge / hB / hC、chi0-bundle は witness_dade_psi_apply_x_eq_chi パターン)。

**⟹ (12.16) counterexample_contradiction / (12.7) pi_empty / typeI_frobenius が own-proof sorry-free 化**
(transitive residual は既知の witness-chain/D(4)/(12.2.a) producer 系のみ)。

**次の b-frontier (上流優先+文書順)** — ⚠ 当初「3004 裁定 2・3 へ」と書いたが**両方とも別 b セッションが
完了済み** (0757c158 restate + 5dc4e84a cleanup、issue 3004 実施報告参照; 二重作業を回避)。改めて残 b-owned
実 sorry を再スキャン (comment-strip): S15_SAndT_Setup 11 (QD_sharp_centralizer_le_T / tSide_theta_package /
basic_structure_gated / sibleyTarget_S / character_degree_analysis / exists_muT_index /
exists_etaT_alphaFun_one_int / numeric_bounds / pc_le_maxNilpotentNormalHall / caseA_parameters /
caseB_order_u) + S15_SAndT 7 (complement_inf_Q_structure / complement_inf_P_structure_dichotomy /
betaGrid_support / betaGrid_A0_support / gammaGrid_real / gammaGrid_Y_norm_bound /
typeIOrthogonalityGridData_of_typeISetup) + S15_Gate3 1。次候補 (要 3002/1017 末尾との整合確認):
(a) s15_s_and_t.md 2026-07-07 LIVE STATUS の (13.3) G1 assembly 続行、(b) (13.18) betaGrid_support /
(13.19) producer 実証明 ((13.17.c) E=W₁ 排除の上流)、(c) off-path vestigial (sibleyTarget_S 等) は
do-not-complete 維持。

**frontier 確定 (同日、調査済)**: 次 = **(b) の (13.18)/(13.19) cluster** (S15_SAndT、b 所有)。根拠:
(i) 0757c158 の忠実 restate により `typeIOrthogonalityGridData_of_typeISetup` が W-side η-grid spine の
honest な producer obligation になった — 「S-side cascade off-path」(2026-07-02 ruling) の対象
(sibleyTarget_S/character_degree_analysis/tauS placeholder) とは**別物** (こちらは η_ij grid = spine 側)。
(ii) c の (14.11) restructure (3004 裁定 1) は (13.19.c) を「明示 hypothesis パラメータ、**b landing 後に
差し替え**」で待っている = 本物の downstream 需要。(iii) 文書順: (13.18) betaGrid_support →
(13.18.c/d) gammaGrid_real / gammaGrid_Y_norm_bound → (13.19) producer → その下流で (13.17.c)
`complement_inf_Q_structure` の E=W₁ 排除 ((13.19.c1)+(14.5) 論法) が閉じる。原文 (13.18) proof
(mmd 04.15 p.83) の部品: (4.5.a) Res μ_0j / (13.3.a)(13.12) vanishing / (1.6.b) inflation 同定 /
(2.1) W-coset conjugacy / Frobenius counting — 各部品の Lean 所在 survey から次 iteration 開始。
3002 の b-side は全完了済 (2026-07-07)、s15_s_and_t.md の (13.3) G1 assembly は S-side
CharacterDegreeData 系で off-path ruling との整合要確認 — (13.18)/(13.19) を先行する。

## 📋 (2026-07-10 続⁹、lane-b /loop iter 1) — (13.18.a) betaGrid_support survey (Coq PVSbeta 精読)

**Coq PFsection13 `FTtypeP_bridge_facts` (:1792-1870) の PVSbeta 証明構造** (= 原文 (13.18.a)):
β_j = Ind_{P⋊W₁}^S 1 − μ_0j、主張 = β_j ∈ CF(S, P^# ∪ V_S) (V_S = (W−W₁∪W₂)^S)。
z ∉ P^#∪V_S で Ind(1)(z) = μ_0j(z) を場合分け:
1. **z ∈ PU (=S′)**: (i) z=1 → 両辺 u (γ(1)=u [index 計算]、μ_0j(1)=(1/q)μ_j(1)=u [cfRes_prTIirr])。
   (ii) z∉P → 両辺 0 (μ_j は Ind-from-Fitting ゆえ P 外 0 [seqInd_on+FTprTIred_Ind_Fitting]、
   Ind(1) は (PW₁)^S∩PU=P の外 0 [group_modl 計算])。
2. **z ∈ S−PU**: rcoset partition + `partition_cent_rcoset` + StypeP.prPUW1 で z ~ x·y (x∈W₁^#、y∈W₂)。
   y≠1 → z∈V_S 矛盾。y=1 → z~x∈W₁^#: Ind(1)(x) = γ(x̄) = 1 (**gammaW1**: S̄=S/P Frobenius +
   normedTI W₁bar → induction 値 1) / μ_0j(x) = 1 (prTIirr_id + linear 値)。
3. A0beta: P^#∪V_S ⊆ A₀(S) は別 step。

**Lean 側の対応課題**: 現 statement は grid form `supp(β_j) ⊆ ⋃_i supp(μ_ij)` (consumer 向け restate)。
Coq の P^#∪V_S 形との橋 (「μ_ij 族の support が P^#∪V_S を覆う/一致する」) の要否を含め、次 iteration で
(a) consumer ((13.19) producer / gammaGrid_real) が実際に必要とする形を確認、(b) 部品の Lean 所在
(S̄=S/P Frobenius = `typeP_uW1_frobenius` 済 [indPW1_inner_self_aux で使用中]、μ_0j Res 公式 =
mu2Grid/PrimeTIResidue 系、class_support W₁^# 分解 = (2.1) 対応物) を grep、(c) statement 忠実性の
判定 (grid form が over/under-strong でないか) — 不忠実なら restate (0757c158 と同型の faithfulness 修正)。

## 📋 (2026-07-10 続¹⁰、lane-b /loop iter 2) — (13.18) 依存構造確定: betaGrid_A0_support が単一 gate

- **gammaGrid_orthogonal_one (13.18.c 前半) は既に proven** (aux:1107-1181、9076 の
  sInstance_dade0_eq_induce bridge + Frobenius reciprocity + eta_orthonormal) — 消費する sorry は
  `betaGrid_A0_support` のみ。docstring 明記: 「This single 'A0-support obligation is what both
  gammaGrid_orthogonal_one and gammaGrid_Y_norm_bound reduce to」。
- **∴ 攻略順確定**: (1) `betaGrid_A0_support` (= Coq PVSbeta+A0beta、続⁹ の証明構造) →
  (2) `betaGrid_support` (grid form、PVSbeta の系 or 独立計算) → (3) `gammaGrid_real`
  (conj-commutation: cfAutInd/Dtau/prTIirr_aut/cfAut_cycTIiso の port) → (4) `gammaGrid_Y_norm_bound`
  ((13.18.d)、betaGrid_norm proven + on-support isometry + (a)(c))。
- `honestTypeP2A0Set M data = honestTypeP2ASet M ∪ conjClassSetIn M (typePV M data)` (S15_HonestTypeP2A0)
  — Coq の P^# ∪ V_S ⊆ A₀(S) (A0beta step) は typePV との同定で処理する見込み。
- 次 iter: typePV def / hyp.mu の supplied fields (S15_SAndTDefs) / prTIirr_id 対応
  (S13_PrimeTIResidueBridge の residueS/mu2_ne — b 自身が port 済) を精査して PVSbeta port の
  Lean 実装計画を固める → 実装。

## 📋 (2026-07-10 続¹¹、lane-b /loop iter 3) — betaGrid_A0_support port の部品階層 (実装計画確定)

**部品在庫確認済**: mu supplied fields (SubcoherenceInputs:156-210) = `mu_definition` ((13.1.e)
Ind_W^S(ω_ij−ω_0j) = δ_j(μ_ij−μ_0j)) / `mu_degree_modEq_delta` / `mu_colSum_eq_induce` ((4.5.a)
Σ_i μ_ij = Ind_{S'}ψ、ψ irred) / `mu_irreducible` / `mu_col_injective`。
`honestTypeP2ASet M = centralizerSupport (Msigma M)^# (derivedInG M)` (mem iff: y∈S′ ∧ y≠1 ∧
∃x∈Msigma^#, y∈C(x))。`typePV = W∖(W₁∪W₂)` (Coq cyclicTIset と一致)。
S15_HonestTypeP2A0 に mu_row0 engine (mu_row0_ne proven / tauS_mu_row0_{diff_support,vanish_on_V}
= (13.18) pins、「hyp.mu grounded to residueS.mu2 で discharge、ungated」注記 :658)。

**Coq PVSbeta → Lean 部品階層** (実装順 D→A→B→C→assembly):
- **D (浅い、次 iter 着手)**: `P^# ∪ (typePV)^S ⊆ honestTypeP2A0Set hyp.S hyp.Sdata`。
  P^# ⊆ honestTypeP2ASet: y∈P^# → y∈S′ (P≤S′=P⊔U) ∧ ∃x:=y∈Msigma^# (要 **P = Msigma S 同定**
  — S type-P₂ の MF=Msigma、S14 の MF_eq_Msigma 対応物を S15 で確認/新設) ∧ y∈C(y)。
  V_S 側は honestTypeP2A0Set def の右 union 成分 (ほぼ rfl) + hyp.W1/W2 ↔ Sdata.W1/W2 同定
  (hyp.Sdata_W1_eq 既存)。
- **A (Ind_{PW₁}^S 1 の値)**: (i) PU 上: (PW₁)^S ∩ PU = P (group calc、Coq group_modl 対応) で
  P 外 0; P 上は γ=Ind_{W̄₁}^{S̄}1 の mod-P inflation (indPW1_inner_self_aux:688-694 の
  induce_one_eq_compHom_induce_one_of_le + typeP_uW1_frobenius が既に同じ変換を実装済 — 流用)。
  (ii) W₁^# 上: **gammaW1** = S̄ Frobenius + normedTI W̄₁ → γ(x̄)=1。normedTI は
  `escaping_honestTypeP2ASet_eq_empty`/G2 系 (76d1b27b) で W₁-class 版があるか要 grep。
- **B (μ_0j の値)**: (i) S′∖P → 0: mu_definition で μ_ij−μ_0j が W^S-supported (Ind_W の support)
  → S′∖W^S 上で全行一致 → q·μ_0j = Σμ_ij = Ind_{S'}ψ、ψ の P-support (Coq FTprTIred_Ind_Fitting
  対応 — mu_colSum_eq_induce の ψ が P-supported かは field に無い、要追加調査/追加 pin) → 0。
  (ii) μ_0j(1) = u: colSum degree + 行一致から。(iii) W₁^# 上 = 1: prime-TI residue (9014、
  S13_PrimeTIResidueBridge residueS/mu2 grounding — S15_HonestTypeP2A0:658 の grounding 経路)。
- **C (S−S′ 分解)**: z∈S−S′ → z ~_S x·y (x∈W₁^#、y∈W₂)。Coq: rcosets partition +
  partition_cent_rcoset + StypeP.prPUW1 (Frobenius 性)。Lean: S = S′⋊W₁ (S_deriv_eq_PU +
  complement) + W₂ 側 …新規幾何、(2.1) 対応物の有無を要 grep (BG §14 に類似?)。
- **assembly**: cfun_onP 型の pointwise 論法 (z ∉ P^#∪V_S → β_j(z)=0) を Lean の
  Set/support ⊆ に書き換え。

**リスク注記**: B(i) の ψ P-support と C の (2.1) 対応物が repo 未在なら追加 pin/新規補題
(数十〜百行級)。D は self-contained で即着手可。

## ✅📋 (2026-07-10 続¹²、lane-b /loop iter 4-5) — 部品 D landed + 部品 A は既存 API で inflation 橋 1 本のみ

- **iter 4 (commit 7a7039cd)**: 部品 D `sharpP_union_V_subset_A0` **完全 proven** (P^#∪V_S ⊆ 'A0(S))。
  P=Msigma (S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II + isTypeII_of_isTypeP2、
  SubcoherenceInputs:1096 の hPeq パターン)、P≤S′、self-centralize。V^S 側は def の右成分。
- **iter 5 (調査、重複回避 3 回目)**: 部品 A の一般補題は **両方 Machinery135 に既存**:
  `induce_one_eq_zero_of_mem_normal_inf_bot` (kernel^# で 0) + `induce_one_eq_one_of_mem_complement`
  (complement^# で 1、Frobenius TI)。さらに **S̄=S/P への Frobenius 輸送 setup が
  indPW1_inner_self_aux:694-756 に完備** (typeP_uW1_frobenius → e : ↥(U⊔W₁)≃*S̄ →
  isFrobeniusGroup_map_equiv → hAmatch : W̄₁ = Ā = (PW₁)/P)。
- **∴ 部品 A の残実装 = inflation 橋 1 本**: `indPW1_apply_eq_one_of_mem_W1_sharp`
  (x∈W₁^# → indPW1 hyp x = 1)。手順: (1) `induce_one_eq_compHom_induce_one_of_le hNA` で
  indPW1 = (Ind_Ā^{S̄} 1)∘mk′ (aux:689-691 の rw)、(2) 値 = Ind_Ā 1 (x̄)、(3) x̄∈Ā ∧ x̄≠1
  (W₁⊓P=⊥ 系 disjointness で x∉P)、(4) `induce_one_eq_one_of_mem_complement hFrob`。
  setup は aux:694-756 複製 (aux は private ゆえ共通抽出 refactor は hub 委任候補、まず動くものを)。
  同型の `indPW1_apply_eq_zero` (PU∖P で 0、A(i)) も同 setup: (PW₁)^S∩PU=P group calc +
  induce_one_eq_zero (P̄=⊥ 側でなく S 内直接計算の方が素直か — Coq は PU-case を S 内で処理)。
  次 iter: この 2 本を実装。

## ✅ (2026-07-10 続¹³、lane-b /loop iter 6-7) — 部品 A 完了 (Ind 側の値 2 本 landed)

- **iter 6 (b03c7f62)**: `indPW1_apply_eq_one_of_mem_W1_sharp` (A(ii)、Coq gammaW1) —
  mod-P inflation (induce_one_eq_compHom_induce_one_of_le) + S̄=Ū⋊W̄₁ Frobenius 輸送
  (aux setup 複製) + induce_one_eq_one_of_mem_complement。一発 green。
- **iter 7 (本 commit)**: `indPW1_apply_eq_zero_of_mem_derived_not_mem_P` (A(i)、PU-case) —
  conjugator 空: 共役は normal S′ に留まり、(P⊔W₁)⊓S′ ∋ w は PW₁=P*W₁ 分解 + W₁⊓S′=⊥ で
  w∈P (elementwise Dedekind; ⚠ Subgroup lattice は non-modular ゆえ
  order.sup_inf_assoc_of_le は使えない — coe_mul 分解が正道)、z∈P^g=P 矛盾。
- **残 = 部品 B** (μ_0j の値 3 点: (i) S′∖P → 0 [mu_definition の W^S-support + colSum P-support、
  ψ P-support 未 field ゆえ要追加調査]、(ii) 1 → u、(iii) W₁^# → 1 [prime-TI residue 9014/
  S13_PrimeTIResidueBridge grounding]) + **部品 C** (z∈S−S′ → z ~ x·y、x∈W₁^#、y∈W₂ の分解) +
  assembly (pointwise → support ⊆)。B(iii)/C が深い — 次 iter は B の部品在庫精査から。

## 📋 (2026-07-10 続¹⁴、lane-b /loop iter 8) — 部品 B 診断: gate = mu-grounding (3002 残の b-side field)

**発見**: S15_HonestTypeP2A0 に (13.18) 用 engine が **proven で 2 本既存**:
- `Hypothesis.residueS_mu2_diff_support` (:758) — residue grid の equal-degree 列差 μ2_ij−μ2_ik が
  A₀(S)-supported (§6 certainType_diff_supp_subset_A0 @ hyp46S で実証明済)。
- V-value engine (:806+) — τ_S(μ2 差)(v) = δ(ω^σ差)(v) on V_S。
両 engine の注記が明言: **残 gap = grid grounding `hyp.mu = residueS.mu2` (b-side field、9076/3002 予告) のみ**。

**部品 B の診断**:
- B(iii) (W₁^# → μ_0j = 1): mu_definition から直接出そうとすると Ind_W^S の W₁^# 値計算 =
  prime-TI/N_S(W) 幾何に落ちる (9014 系) — **grounding 経由が正道** (residue 側は
  prTIirr 値 API を既に持つ)。
- B(i) (S′∖P → 0): mu_definition (行差 W^S-supported) + mu_colSum_eq_induce (Σ = Ind_{S′}ψ) +
  ψ の P-support (未 field) — こちらも grounding 経由なら residue API から一括の可能性。
- B(ii) (1 → u): colSum degree + 行一致 (grounding 不要で可能そうだが単独では使い道薄)。

**∴ 次の作業単位 = mu-grounding field の設計+追加** (SubcoherenceInputs.Hypothesis、b 所有):
S15.Hypothesis の producer は未構成 (grep で不在確認 — 仮説 carrier) ゆえ **field 追加の producer
追従は現状不要**、3002 の「7 grid property fields 追加」先例と同型の自律 carrier enrichment。
設計課題: residueS は hG-依存 (hyp.residueS hG) + index が Fin q vs Fin (Nat.card W1) で cast 要
(NeZero instances)。field は hG-quantified 形 (`∀ hG, mu i j = (residueS hG).mu2 (castIdx i) (castIdx j)`)
か、s06S の card 同定 (q_eq_card_W1 系) を介した enum-free 形か — 次 iter で residueS/mu2 の型を
精査して設計確定 → field 追加 → tauS_mu_row0 pins (S15_HonestTypeP2A0:877/891 sorry) の discharge →
B(i)/(iii) → PVSbeta assembly。

## 📋 (2026-07-10 続¹⁵、lane-b /loop iter 9) — grounding 設計確定: 「性質 field 化」(3002 同型、循環回避)

- **scan 訂正**: S15_HonestTypeP2A0 (b 系列 9076 file、git log 確認) に実 sorry **3 本**が残存
  (前回の b-owned scan の対象 glob 外だった): `mu_row0_ne` (:739 hoff 直交のみ sorry) /
  `tauS_mu_row0_diff_support` (:881) / `tauS_mu_row0_vanish_on_V` (:899)。3 本とも
  「grounding 後は proven engine (residueS_mu2_diff_support / V-value engine / mu2 直交) の
  rewriting」と docstring 明記。
- **grounding field の設計判断**: `mu = residueS.mu2` を S15.Hypothesis の field に直接書くのは
  **不可** — residueS は Hypothesis 自身を引数に取る def (S13_PrimeTIResidueBridge:75) ゆえ循環。
  正道 = **grounding の帰結を性質 field 化** (3002「7 grid property fields」と同型、構成可能性 =
  spine 構成時に mu := residueS.mu2 と置けば discharge 可能なので sound、hoisted-conclusion には
  非該当)。候補 field: `mu_orthonormal` (grid 全体 pairwise 直交 — mu_row0_ne の hoff を閉じる) +
  B(iii) 用の W₁-値 or (4.8) residue-値 field (residueS.mu2 の対応 API を S13 で確認してから確定)。
- 次 iter: S13_PrimeTIResidueBridge の mu2 API 精査 (orthonormality / W₁^# 値 / degree) →
  field リスト確定 → SubcoherenceInputs.Hypothesis へ追加 (producer 未構成ゆえ追従なし、
  ただし既存 mock/instance が repo に無いか grep してから) → mu_row0_ne 等 discharge。

## 📋 (2026-07-10 続¹⁶、lane-b /loop iter 10) — PrimeTIResidueData API 精査完了、field 設計最終形

**PrimeTIResidueData (9014) の在庫**: mu2 (IrreducibleCharacter grid) / **mu2_orthonormal** (4.3.b) /
**chi_eq_restrict** (chi j = Res_{PU}(mu2 0 j)、restriction の i-独立 = (4.5.a)) /
**induce_chi_eq_sum** (Ind_{PU}(chi j) = Σ_i mu2 i j) / chi_zero / cfker_prTIres (4.5.b) /
prTIres_irr_cases (残: 全て posited-field、constructor ofS06Hypothesis で discharge 済の設計)。

**B 部品との対応**:
- B(i) (S′∖P → μ_0j = 0): chi_eq_restrict + induce_chi_eq_sum + cfker 系で residue 側は完結可能
  (Coq と同じ Res/Ind 計算)。grounding 後に S15 側へ transport。
- B(ii) (1 → u): induce_chi_eq_sum の degree + chi_zero。
- **B(iii) (W₁^# → 1) の真の gap = prTIirr_id (Coq PFsection4) 相当の W₁^#-値が PrimeTIResidueData
  に未 port** — cyclicTIiso 由来の mathcomp theorem で、9014 の port は distinctness/支持/V-値まで。
  正道 = PrimeTIResidueData に W₁-値 field を追加 (他 fields と同じ posited パターン、constructor
  拡張は 9014 続き) — ただし構造は shared (b port、9014)、constructor ofS06Hypothesis の追従が要る
  (field 追加 = constructor red → discharge 実装まで 1 unit)。
- S15.Hypothesis 側の性質 field 化 (mu_orthonormal / mu_res_row_indep / mu_W1_value) は
  residue 側が揃ってから一括が効率的。

**工程再評価**: (13.18) full port = 9014 拡張 (W₁-値 field + constructor discharge) →
S15 grounding fields → pins/mu_row0_ne discharge → PVSbeta assembly の multi-session 級。
部品 D/A は landed 済、B/C は上記経路で継続。次 iter: 9014 の constructor
(ofS06Hypothesis) の W₁-値 discharge 可能性を精査 (S06 側に W₁-restriction 値があるか) —
可能なら field+constructor を 1 commit で。

## 📋 (2026-07-10 続¹⁷、lane-b /loop iter 11) — B(iii) への残 gap が 2 点に絞れた

**ofS06Hypothesis constructor 精読**: mu2 i j := (columnFamily (charGroupW2Equiv j)).mu i —
全 field が S06 定理で discharge 済 (mu2_orthonormal/chi_res/ind_chi/chi_zero/cfker/dichotomy)。
**同 file に mu2Grid (σ-grounding) が移設済**: `mu2Grid_eq_sign_smul_sigma_omega` = **μ = δ·σ(ω)**
(sign ±1 = mu2GridSign) + mu2Grid_orthonormal/injective。

**∴ B(iii) (μ_0j(x)=1 on W₁^#) への残 gap は 2 点**:
1. **σ(ω) の W₁^#-値 API**: TICyclicHypothesis の σ (cyclicTIiso (3.2)) が W 上で ω とどう関係するか
   (Coq prTIirr_id の中身 = cycTI の W-値 identity)。x∈W₁^# で σ(ω_0j)(x) = ω_0j(x) = 1
   (ω_0j の W₁-part = trivial)。TICyclicHypothesis の値 API の有無を次 iter で精査。
2. **columnFamily.mu ↔ mu2Grid の同定**: residueS の mu2 は columnFamily 経由、σ-値は mu2Grid 経由 —
   両 μ-grid の同定 (どちらも orthonormal + 同 column 構造だが identification が要る;
   「σ-grounding down-payment」の表現は full 接続が未了を示唆)。

どちらも 9014 の続き (cyclicTIiso port の残り)。gap 1 が閉じれば B(iii) は
mu2Grid_eq_sign_smul_sigma_omega + σ-値 + δ の (4.4)-normalization (delta_zero_eq_one 系) で組める。

## 📋 (2026-07-10 続¹⁸、lane-b /loop iter 12) — gap 1 の正体確定: σ(ω) の W₁^#-値 (Coq primeTIirr_spec 内蔵)

- repo σ-値 API は **V 上のみ** (`sigma_apply_of_mem_V` (3.5.a)、S05_SigmaIsometry:327)。W₁^# は V 外。
- Coq `prTIirr_id : {in W :\: W2, mu2_ i j =1 delta_ j *: w_ i j}` (PFsection4:403) の証明は
  `by case: primeTIirr_spec` — **W∖W₂-値 (W₁^# 込み) は primeTIirr_spec (:288-387、dirr_dIirr 構成)
  に内蔵**。repo の mu2Grid は同 spec の「σ(ω) = δ•μ 大域一致」半分を port 済
  (`sigma_omega_eq_mu2GridSign_smul_mu2Grid`) ゆえ、**B(iii) は完全に「σ(ω_0j)(x) = ω_0j(x) = 1
  for x ∈ W₁^#」= cycTI の W∖W₂-値拡張に帰着**。
- 理論構造メモ: `eq_sigma_of_apply_eq_on_V` (:814) の存在は V-値+直交で σ-image が pin される
  構造を示唆 — W₁^#-値の port は (a) primeTIirr_spec の W∖W₂ 拡張値を Coq :288-387 から直 port、
  (b) V-値 + ‖·‖ + 整数値 ((3.9.c)) から W₁^#-値を再導出、の 2 route。次 iter: Coq :288-387 の
  該当補題 (spec の W∖W₂ 成分がどの cycTI 原理から出るか) を精読して route 選択。

## 📋 (2026-07-10 続¹⁹、lane-b /loop iter 13) — primeTIirr_spec 精読完了: port 最深部 = equiv_restrict_compl_ortho

**Coq primeTIirr_spec (:288-387) の W∖W₂-値 (c) の導出構造**:
1. `isoV2 := normedTI_isometry normedTI_prTIset` — **W∖W₂ が S 内 normedTI** ⟹ Ind が
   Z[Sj, W∖W₂] 上 isometry。
2. `vchar_isometry_base` — isometry image の signed-irr 抽出 (repo mu2Grid が対応済の部分)。
3. **`equiv_restrict_compl_ortho`** (mathcomp、:361) — V2base (CF(W, W∖W₂) の ew-基底) との
   内積一致から **W∖W₂ 上の pointwise 値一致** を出す同値原理。muW = δ·μ grid が基底内積で
   ω と一致 → `{in W :\: W2, mu2 =1 δ·ω}` (= prTIirr_id)。
**⟹ B(iii) port の残 3 部品**: (i) normedTI (W∖W₂) S W 相当 (TICyclicHypothesis field
の有無要確認 — G2 で W₁-class normedTI は触った)、(ii) equiv_restrict_compl_ortho の
repo 対応 (grep 未ヒット → 新規 port、mathcomp character theory 一般原理、
Frobenius-reciprocity + 基底展開で self-contained に証明可能な見込み)、(iii) 両者の合成で
prTIirr_id 対応 (`mu2Grid_apply_eq_of_mem_W_sub_W2`) を mu2Grid API に追加。
これが (13.18)/(13.19) cluster の真の最上流 — 9014 continuation として次 session/iter で
equiv_restrict_compl_ortho port から着手。

## 📋 (2026-07-10 続²⁰、lane-b /loop iter 14) — 依存鎖の底 = Peterfalvi (1.3.a)/(1.3.b) 未 port 確定

- **equiv_restrict_compl(_ortho) = Peterfalvi (1.3.a)/(1.3.b)** (Coq PFsection1:87/123 — §1 の
  一般原理、mathcomp 本体でない)。repo S03_PreliminaryCharacter の (1.3) 部は
  `inductionCoefficient` API + `IsInductionExpansion` predicate のみで**本体定理は未 port**
  (docstring 自認: 「numerical Frobenius-reciprocity theorem remains routed to the
  InducedCharacter proof core」)。
- **(1.3.a) statement**: H ≤ G、A ⊴ H、Φ basis of CF(H,A)、μ ∈ CF(G):
  `{on A, μ = Σ d_i·χ_i} ↔ ∀j, Σ_i ⟨Φ_j,χ_i⟩·d_i^* = ⟨Ind Φ_j, μ⟩`。
  証明部品: D := Res μ − Σd_i χ_i の CF(H,H∖A)-membership ⟺ 内積条件
  (Frobenius reciprocity + **CF(H) = CF(H,A) ⊕ CF(H,H∖A) 直交補分解** [cfun_complement/
  cfdot_complement — repo 対応要確認] + 基底展開)。
- **(1.3.b)**: + mu_ orthonormal + `Ind Φ_j = Σ⟨Φ_j,χ_i⟩·mu_i` → ∀i {on A, mu_i = χ_i} ∧
  (⊥全mu → A 上 0)。(a) の 2 instantiation。
- **port 配置**: S03 系新 leaf (例 `S03_RestrictComplement.lean`、§1=S03 文書順で最上流) or
  RepresentationTheory shared leaf。mathlib Basis over supportedSubmodule + repo の
  inner_induce_eq_inner_restrict で self-contained。
- **依存鎖 (確定、深→浅)**: (1.3.b) port → normedTI(W∖W₂) 供給 → prTIirr_id 対応
  (mu2Grid W∖W₂-値) → residueS transport → S15 grounding fields → mu_row0_ne/pins →
  B(i)(iii) → PVSbeta assembly = betaGrid_A0_support → gammaGrid 系 → (13.19) producer。
  次 iter: (1.3) port 実装開始 (直交補分解の repo 在庫確認から)。

## ✅✅ (2026-07-11、lane-b /loop iter 15) — **Pf (1.3.a/b) core 完全 proven** (依存鎖の底 landed)

新 shared leaf `GroupTheory/RepresentationTheory/SupportedSpanOrthogonality.lean` (sorry-free 一発 green):
- `eq_zero_on_iff_forall_inner_eq_zero_of_span` ((1.3.a) core): conj-不変 A + A-supported spanning
  family Φ に対し「D は A 上 0 ↔ D ⊥ 全 Φ i」。非自明方向 = indicator split (conj-不変性で
  class function、S09 χ₁ パターン) + disjoint-support 直交 + span_induction + ⟨D_A,D_A⟩=0。
- `apply_eq_on_of_forall_inner_eq` ((1.3.b) 値同定半分): Φ-pairing が一致する 2 つの CF は A 上一致。
**次 (依存鎖を上へ)**: (i) normedTI(W∖W₂) 供給 — Φ := ew-基底 (CF(W, W∖W₂) の spanning family) の
構成と、その Ind-image が mu2Grid の δ·μ grid と pairing 一致することの確認 (Coq :361 の
instantiation)、(ii) mu2Grid の W∖W₂-値 identity (`prTIirr_id` 対応) を PrimeTIResidue に追加。
Φ-spanning は supportedSubmodule (W∖W₂-in-W) の基底 = ω-grid の差族 (V2base = ew_ ij) —
S05/S06 の ω-grid API から組む。

## ✅ (2026-07-11、lane-b /loop iter 16) — Fourier 展開補題 landed ((1.3.a) core の univ-instance)

`eq_sum_inner_smul_of_orthonormal_of_span_top` (SupportedSpanOrthogonality 追記、sorry-free
一発 green): orthonormal spanning family Φ で f = Σ⟨f,Φi⟩•Φi。証明 = (1.3.a) core @ A=univ +
orthonormal collapse + inner_conj_symm。
**次 (ω-差族 spanning への残 3 部品)**: (i) span top bridge (span_irreducibleCharacter_eq_top
[CharacterCompleteness:683] + omega_surjective [S05_TICyclic:343] → CF(↥W) = span(range ω))、
(ii) W₂-vanishing → 行和 0 (f = Σc_χ ω_χ、x∈W₂ で ω_χ(x) = χのW₂成分値 → W₂-char 独立性で
Σ_{W₁成分} c = 0 per W₂-char)、(iii) 差族 reassembly (行和 0 ⟹ f = Σ_j Σ_i c_ij(ω_ij−ω_0j))。
wFst/wSnd (W=W₁×W₂ 射影、S05) で char の積分解。

## ✅ (2026-07-11、lane-b /loop iter 17-18) — ω-差族 spanning 完成 (V2basis spanning 半分 landed)

- iter 17 (707c6e62): `S05_OmegaSpanning` 新 leaf — `span_omega_eq_top` (Irr W = ω-range +
  completeness) + `eq_sum_inner_smul_omega` (ω-Fourier 展開)。
- iter 18 (本 commit): `sndPart` (W₂-成分 lift、Coq w_ 0 j) + **`supported_le_span_omega_sub_sndPart`**
  (CF(W,W∖W₂) ⊆ span{ω_χ − ω_{sndPart χ}})。**W₂-char 独立性論法を完全回避**: Fourier split の
  残余 g は W₂ 上 0 かつ W₂-成分のみ依存 → 恒等 0。
**次 = cross-level (1.3.b) wrapper**: H ≤ G、A ⊆ H、Φ_j ∈ CF(H,A) spanning、mu_i ∈ CF(G)
orthonormal、`Ind Φ_j = Σ_i ⟨Φ_j,χ_i⟩•mu_i` → mu_i = χ_i on A。導出 = Res mu_i に (1.3.a) core:
⟨Φ_j, Res mu_i⟩ = ⟨Ind Φ_j, mu_i⟩ (inner_induce_eq_inner_restrict) = ⟨Φ_j,χ_i⟩ (orthonormal
collapse) → D := Res mu_i − χ_i ⊥ 全 Φ → D = 0 on A。SupportedSpanOrthogonality に追記 →
その後 mu2Grid instantiation (Φ := ω-差族 [今回 landed]、mu_ := δ·mu2Grid 族、hypothesis =
sigma_omega_eq_mu2GridSign_smul_mu2Grid 経由) で prTIirr_id 対応が閉じる。

## ✅ (2026-07-11、lane-b /loop iter 19) — cross-level (1.3.b) landed、(1.3) 三部作完成

`restrict_apply_eq_on_of_induce_eq_sum` (SupportedSpanOrthogonality、一発 green): H≤G、conj-不変
A⊆H、A-supported spanning Φ、CF(G) orthonormal mu 族、`Ind Φ_j = Σ_k ⟨Φ_j,χ_k⟩•mu_k` →
Res(mu i) = χ i on A。reciprocity + orthonormal collapse + 同一群版で 3 行帰着。
**(1.3) port 完了** (core / 同一群 / cross-level / Fourier / ω-差族 spanning の 5 点セット)。
**次 = mu2Grid instantiation (prTIirr_id)**: Φ := ω_χ−ω_{sndPart χ} 族 (supported ✓ spanning ✓)、
A := {w | w ∉ W₂-sub} (W abelian → conj-inv 自明)、mu := mu2Grid 族 (orthonormal ✓)、
**残る供給 = hInd**: Ind_W^S(ω-diff) = Σ⟨diff,·⟩•(δ·μ) — σ (3.2 cyclicTIiso) の
「A₁-supported diff で σ = Ind」性質 (TICyclicHypothesis の σ↔Ind agreement API、
sigma_apply 系 or dadeIntegralCharacterMap 系) を次 iter で精査 → instantiation。

## 📋 (2026-07-11、lane-b /loop iter 20) — prTIirr_id への最終帰着: σ↔Ind の W∖W₂-拡張一致 1 点

**構造発見 (instantiation の簡約)**: cross-level (1.3.b) の mu 族を **σ(ω_χ) 族** (= δ·mu2Grid、
`sigma_omega_eq_mu2GridSign_smul_mu2Grid`) に取ると:
- orthonormality: ⟨σω,σω'⟩ = δδ'⟨μ,μ'⟩ = Kronecker ✓ (σ isometry + sign²=1)
- ⟨Φ_j, ω_k⟩ = [k=χ]−[k=sndPart χ] (ω orthonormal) → hInd ⟺ **Ind(Φ_j) = σ(Φ_j)**
- 結論 = Res(σ(ω_χ)) = ω_χ on W∖W₂ = **prTIirr_id の σ-form** (mu2Grid 形へ sign 1 発)
**∴ 残 gap は 1 点**: 「Ind(ω_χ − ω_{sndPart χ}) = σ(ω_χ − ω_{sndPart χ})」(W∖W₂-supported diff
での σ↔Ind agreement — 既存 `sigma_eq_tau` (3.2.a) は V-supported 限定)。
**その証明に必要なもの**: ‖Ind diff‖² = ‖diff‖² (= 2) — **Ind の W∖W₂-isometry** =
Coq `normedTI_prTIset : normedTI (W∖W₂) S W` (prime-TI 文脈仮定、cycTI の V-TI より強い) 由来
(`normedTI_isometry`)。TICyclicHypothesis は V-conj 条件のみ field 化 — W∖W₂-TI は
(a) TICyclicHypothesis 新 field (carrier enrichment、既存 producer 追従要)、
(b) 定理の仮説パラメータ (prime-TI 消費側 [S = type-P₂ maximal] が (8.x)/(13.x) 幾何から供給)、
の選択。**(b) が軽い** — prTIirr_id 対応を「hTI : W∖W₂ TI-条件 (S-conj が W-normalizer 経由のみ)」
仮説付き lemma として PrimeTIResidue に置き、S-side 供給は別途。ただし ‖Ind diff‖² = 2 の導出
(TI → induction norm) 自体も port 要 (Coq normedTI_isometry / Isaacs 系 — repo の
`IsTISubset`/`normedTI` 対応 [G2 で触った isTISubset_honestTypeP2ASet 系] を次 iter で確認)。

**追記 (iter 20 末)**: TICyclicHypothesis fields 実確認 — TI は `V_ti : IsTISubset V W` のみ ✓。
`S04.Hypothesis.of_isTISubset` (S05_TICyclic:71) が「TI → Dade datum」の既存 bridge で、
W∖W₂-TI 仮説からの Ind-isometry はこれで組める。**同定 route の鍵候補 =
`eq_sigma_of_apply_eq_on_V` (S05_SigmaIsometry:814)**: Coq :361-387 後半の「Ind-based μ と
σ-based μ の同定」は V-値一致 + norm-1 ZIrr rigidity の形 — 次 iter は
eq_sigma_of_apply_eq_on_V の statement 精読から (これが刺されば normedTI-isometry port すら
不要で prTIirr_id が閉じる可能性)。

## 📋 (2026-07-11、lane-b /loop iter 21) — prTIirr_id の完全 route 確定 ((3.9.a) が同定 step に直刺し)

**`eq_sigma_of_apply_eq_on_V` (S05_SigmaIsometry:814) = Pf (3.9.a)、完全 proven**:
χ ∈ ZIrr ∧ ‖χ‖²=1 ∧ V 上 ω と一致 → **χ = σ(ω)** ((3.8) NC-rigidity で係数 pin)。

**∴ Coq :288-387 の Lean 化 route が完全確定** (全 4 step、うち 2 は landed/existing):
- **a. Ind-based signed family 抽出**: Ind(ω_χ − ω_{sndPart χ}) ∈ ZIrr、norm 2、pairwise 直交
  (W∖W₂-TI 仮説 → `S04.Hypothesis.of_isTISubset` + `tau_eq_induce` の Ind-isometry) →
  signed-irr 差 dmu_χ − dmu_{sndPart χ} 形に分解 (§3 (1.4) core `isometry_difference_pair_structure`
  [IsometryDifferencePair、landed 済] の再利用を次 iter で確認)。
- **b. equiv_restrict**: cross-level (1.3.b) `restrict_apply_eq_on_of_induce_eq_sum` (**landed**) を
  Φ := ω-差族 (spanning **landed**)、mu := dmu 族に適用 → dmu の W∖W₂-値 = ω-値。
- **c. (3.9.a) 同定**: dmu_k は ZIrr ∧ norm 1 ∧ V ⊆ W∖W₂ 上 ω_k と一致 (b の制限) →
  `eq_sigma_of_apply_eq_on_V` で **dmu_k = σ(ω_k)** (existing、port 不要!)。
- **d. 合成**: σ(ω_k) の W∖W₂-値 = ω_k 値 = **prTIirr_id (4.3.c)** ✓ → mu2Grid 形へは
  sigma_omega_eq_mu2GridSign_smul_mu2Grid で sign 変換。
残実装 = a の family 抽出 (isometry_difference_pair_structure 再利用性) + hTI (W∖W₂ IsTISubset)
仮説の設計 + b-d assembly。次 iter: isometry_difference_pair_structure の signature 精読。

## 📋 (2026-07-11、lane-b /loop iter 22) — step a の部品設計確定

- `isometry_difference_pair_structure` 結論 = `∃ data : SignedIrreducibleDifferenceFamily G n,
  ∀ i, τ(χ_i − χ_0) = data.signedDifference i` — **Coq dmu 抽出の Lean 版そのもの** ✓ 再利用。
  適用は **列ごと** (fixed W₂-char ψ、χ 族 := {ω(ω₁ⁱ·ψ)}ᵢ 0-anchored、全 degree 1 ✓ distinct ✓)。
  列間整合 (Coq inj_Imu) は直交性で別途 — Coq :296-330 の写し。
- **h_isom 入力 = TI→Ind-isometry、直接証明で新設** (`of_isTISubset` datum 経由より軽い):
  `inner_induce_eq_of_isTISubset : IsTISubset A H → f,g A-supported → ⟨Ind f, Ind g⟩_G = ⟨f,g⟩_H`。
  証明 = reciprocity + **Res Ind g = g on A** (TI-collapse: (Ind g)(a) の conjugator が
  g-support 制約 + TI で全部 H 内 → class-fn 値 g(a) に collapse — induce_apply_eq_sum_filter /
  induceTerm API [Machinery135 の induce_one_apply と同系])。~60 行 self-contained。
  次 iter: これを実装 (置き場 = SupportedSpanOrthogonality or InducedCharacter 追記)。

## ✅ (2026-07-11、lane-b /loop iter 23) — TI→Ind-isometry landed (step a の h_isom 入力完成)

iter 22 設計どおり実装 (commit d9625eed、InducedCharacter.lean 新 section TIInduction、
full build 4147 green・AxiomsCheck OK):

- **`induce_apply_coe_of_isTISubset`** (TI 値恒等式 = Isaacs CTFG Lemma 7.7 identity part / Coq
  `normedTI_Ind_id`): A TI (normalizer-bound H)、θ off-A 消滅 ⟹ `Ind_H^G θ (↑a) = θ a` on A。
  証明 = induction sum の直接計算: off-H conjugator の非零項は A の 2 共役 overlap を作り TI で
  conjugator ∈ H に矛盾 / in-H 項は conj_eq で各 θ a → ⅟|H|·|H|·θ a。
- **`inner_induce_eq_of_isTISubset`** (isometry part / Coq `normedTI_isometry`): θ,ψ off-A 消滅 ⟹
  `⟨Ind θ, Ind ψ⟩_G = ⟨θ,ψ⟩_H`。reciprocity + 値恒等式 + disjoint-support 直交の 3 行合成。
- 一般 CommRing k で成立 (StarRing は isometry のみ)。Coq の Dade-経由 (`normedTI_Dade`) を
  回避した self-contained 直接証明 ~100 行。新 import = GroupTheory.TISubset (mathlib-only leaf)。

**次 iter (step a 本体)**: 列ごと signed family 抽出 — fixed W₂-char ψ の族 {ω(ω₁ⁱ·ψ)}ᵢ
(0-anchored、degree 1、distinct) の差族に `isometry_difference_pair_structure` を適用。
h_isom 入力 = 本 commit の `inner_induce_eq_of_isTISubset` (hTI : IsTISubset (W∖W₂ G-level) W
仮説パラメータ; supported 側は ω-差族の W∖W₂-supported [landed 済])。突合せ点:
isometry_difference_pair_structure の τ-引数形 (linear map か pairwise inner 条件か) を精読し、
τ := Ind_W^S に instantiate できる形か確認 → 列間整合 (Coq inj_Imu、直交性) は次々 iter。

## ✅ (2026-07-11、lane-b /loop iter 24) — step a 完成: TI 誘導の signed family 抽出 (generic)

新 shared leaf `GroupTheory/RepresentationTheory/TIInducedFamily.lean` (commit d067219d、
一発 green、full build 4148・AxiomsCheck OK):

- **`induce_difference_pair_structure_of_isTISubset`**: A TI (bound H)、n≥2 個の等次数 distinct
  irreducible χᵢ が off-A 一致 ⟹ ∃ SignedIrreducibleDifferenceFamily (n 個の distinct μᵢ + 一様
  符号 ε) で `Ind_H^G(χᵢ−χ₀) = ε•(μᵢ−μ₀)`。iter 23 の TI-isometry + (1.4)
  isometry_difference_pair_structure の合成 (ZIrr = induce_mem_ZIrr / degree-0 = induce_apply_one /
  isometry = inner_induce_eq_of_isTISubset)。Ind の ℤ-linear bundle は inline 構成。root 登録済。

**次 iter (列間整合 = Coq inj_Imu :296-330 の Lean 版)**: 組合せ補題を IsometryDifferencePair.lean に
追加 — 2 つの SignedIrreducibleDifferenceFamily (n,m ≥ 2) が全 difference 直交
(`⟨data.difference i, data'.difference j⟩ = 0 ∀i,j`) ⟹ **μ-grid 全体 disjoint**
(`data.mu i ≠ data'.mu j ∀i,j`)。**導出精査済 (このセッション)**: a_ij := [μᵢ=μ'ⱼ] の Kronecker
展開 E(i,j): a_ij − a_i0 − a_0j + a_00 = 0 (irreducibleCharacter_inner_sub_sub_eq_ite 既存) から
(1) a_00=1 なら i,j≠0 で −a_ij=1 矛盾 → anchors distinct、(2) a_i0=1 (i≠0) なら a_ij=1+a_0j≥1 ∀j≠0
→ μ' 単射性矛盾 (m≥2 で足りる) → 縁 0、(3) a_ij = a_i0+a_0j = 0。sign は ⟨εd, ε'd'⟩=εε'⟨d,d'⟩ で
消える (per-column 符号差は (1.3.b) の orthonormality に影響しない — dmu_k := ε_col•μ_k は常に
orthonormal)。その後: prime-TI instantiation (列 = fixed W₂-char、ω-grid → hTI 仮説パラメータ) →
hInd (列抽出+pairing collapse) → (1.3.b) → (3.9.a) → prTIirr_id。

## ✅ (2026-07-11、lane-b /loop iter 25) — 列間整合 (inj_Imu) landed

IsometryDifferencePair.lean 末尾に SignedIrreducibleDifferenceFamily「Cross-family matching」
section 追加 (commit fd7b130d、一発 green、full build 4148・AxiomsCheck OK):

- **`mu_ne_of_forall_inner_difference_eq_zero`** (Coq inj_Imu :296-330): 2 family (n,m≥2) の
  difference 全直交 ⟹ μ-grid 全 disjoint。Kronecker 展開 E(i,j) → anchors distinct →
  縁 delta 0 (単射性) → 内部 delta 0。iter 24 末尾の導出精査どおり一発実装。
- **`inner_difference_eq_zero_of_signedDifference`**: signed 直交 → unsigned 直交 (符号は unit、
  sign_smul_signedDifference + Int.cast_smul + inner_smul_left/right)。

**⟹ generic 部品は完備**: (i) TI-isometry (iter 23) / (ii) 列抽出 (iter 24) / (iii) 列間 disjoint
(本 iter) / (iv) cross-level (1.3.b) + ω-差族 spanning (iter 15-19) / (v) (3.9.a) 同定 (existing)。

**次 iter (prime-TI instantiation 開始)**: S05 側の設計精査 —
(1) ω の型と grid 構造 (S05_TICyclic omega / S05_OmegaSpanning sndPart、Irr W ≃ Irr W₁ × Irr W₂
の積分解 equiv の有無、wFst/wSnd)、(2) 列の Fin-enumeration (列 = fixed W₂-char、0-anchor =
sndPart lift; 積 equiv があれば直接、なければ Finset.equivFin [[lean-coherence-subfamily-enumeration]])、
(3) hTI : IsTISubset (W∖W₂ G-level) W 仮説パラメータの設計 (iter 20 (b) 案)、
(4) 置き場 = PrimeTIResidue.lean vs 新 S05 leaf。精査後、列ごと instantiation
(induce_difference_pair_structure_of_isTISubset 適用可能形) を実装。

## ⚠✅ (2026-07-11、lane-b /loop iter 26) — **大訂正: prTIirr_id (4.3.c) は S06 に 2026-06-10 から完全 landed 済**

instantiation 精査で判明 ([[verify-port-state-by-number-not-coq-name]] の再発、同 memory に追記済):

- **`certainType_apply_eq_of_mem_V`** (S06_CertainTypeCharacters:958、sorry-free) = **prTIirr_id
  (4.3.c) first part そのもの**: `μ_{ij}(x) = δ_j·ω_{ij}(x)` for `x ∈ sdiffTICyclicHypothesis.V`
  (**= W∖W₂ 全体**、V ⊊ W∖W₂ ではない — sdiff hypothesis の V が W∖W₂)。commit acd39ea1
  (2026-06-10)「Pf (4.3.c) first part」。同 file に (4.3.c) second part
  (`certainType_vanishes_of_ne`) / (4.3.d) / **σ-grounding `sigma_chiColumn_eq_certainType`**
  (σ(ω_{ij}) = δ_j·μ_{ij}、iter 11 の「gap 2: columnFamily.mu ↔ mu2Grid 同定」も実質解消) まで完備。
- **S06 の内部 route**: columnFamily ((1.4) per-column、isometry は sdiffFullDadeIsometryData =
  Dade package 経由) → certainTypeRestrictDiff ⊥ omegaColumnDiffBasis (Step 4) →
  apply_eq_zero_of_mem_V_of_inner_omegaColumnDiff (masking) → 値恒等式。つまり iter 20-22 で設計した
  a-d route (TI-isometry → 列抽出 → (1.3.b) → (3.9.a)) の instantiation は**全て不要**。
- **iter 12-25 の評価**: 「W∖W₂-値は未 port」の診断 (iter 12) は Coq 名 grep
  (prTIirr_id/equiv_restrict_compl_ortho) による検索ミス — `git log -S "4.3"` で一発だった。
  iter 15-19 の (1.3) 三部作 + ω-差族 spanning、iter 23-25 の TI-isometry/generic 列抽出/列間
  disjoint は **generic shared infra として維持** (S06 版は CertainTypeHypothesis 固定・Dade 依存、
  generic 版は任意 TI 文脈で軽量) — ただし本 route の必要部品としては superseded。

**真の残 gap (修正後、iter 20 依存鎖の再評価)**: S06 (4.3.c) → residue chain の**配線のみ**:
1. **ofS06Hypothesis companion lemma** (PrimeTIResidue.lean): `(ofS06Hypothesis h H hW2H).mu2 i j`
   の W∖W₂-値 = `certainType_apply_eq_of_mem_V` の Fin-index 形 (mu2 = columnFamily.mu は rfl)。
2. **residueS 形** (S13_PrimeTIResidueBridge、b-owned): hyp.residueS の mu2 値恒等式。
3. **S15 grounding**: B(i) (S′∖P→0) / B(ii) (1→u) / B(iii) (W₁^#: 列和 Σ_i δω_{ij}(x)、
   ω₁-full-dual 和消滅) を primeTIred/beta 消費形で。
次 iter: 1+2 実装。

## ✅ (2026-07-11、lane-b /loop iter 27) — 配線 layer-1 landed: 値恒等式の residue-grid 形

- merge conflict (issues/9080 の hub RULING と b 認知の同位置追記) を両保持で解決 —
  **hub ruling: 9080 migration 承認、S14 側 owner = b、b の scheduling 裁量** (現 2038 配線
  ユニット完了後に engage、b 側記録と整合)。
- **`PrimeTIResidueData.ofS06Hypothesis_mu2_apply_of_mem_V`** (PrimeTIResidue.lean、commit
  0aa97038、full build 4149 green・AxiomsCheck OK): ofS06Hypothesis grid の
  `mu2 i j (x) = δ_j·ω_{ij}(x)` on W∖W₂ — S06 `certainType_apply_eq_of_mem_V` の
  charGroupW2Equiv 経由 Fin-index 形 (mu2 = columnFamily.mu は rfl ゆえ 1-term proof)。

**次 iter (配線続き、上流優先)**: S15 grounding 向け B-部品の消費形 —
(i) W₁^# ⊆ sdiffV membership bridge (x ∈ W₁∖{1} → x ∈ W∖W₂) の所在確認 or 追加、
(ii) B(iii) 形: 列和 `Σ_i mu2 i j (x)` for x ∈ W₁^# = δ_j·Σ_i ω_{ij}(x) = 0 (j≠0 列;
ω₁-full-dual 和消滅 Σ_i ω₁ⁱ(x) = 0 for x ≠ 1 — 既存 character-sum lemma を探索:
CharacterCompleteness/SecondOrthogonality 系 or 新規 ~30 行)、B(i) (S′∖P → 0) は
conjugatesIntoSet 支持 (support_induceSum 系) 経由。(iii) 消費側 (S15_HonestTypeP2A0 の
pins / mu_row0_ne) の requirement 形を先に確認してから供給形を決める (lane-c file のため
b は供給のみ、cite 形の合意は issue 経由)。9080 step 1 (TypeICovering migration) は
本配線ユニット完了後。

## ✅✅ (2026-07-11、lane-b /loop iter 28) — **mu_orthonormal grounding + (13.18) pin 1/3 (mu_row0_ne) 閉鎖**

消費側精査 → pins の gate は「hyp.mu の grid-property grounding」と確定 → 3002-pattern で実施
(commit 4e8c7880、full build 4149 green・AxiomsCheck OK):

1. **S15.Hypothesis に `mu_orthonormal` field** (SubcoherenceInputs、b-owned) — full-grid
   直交正規性 (4.3.b)。Section16Inputs + character-data 層 (FeitThompsonSetup) にも同 field。
2. **producer 側 discharge = `Section16CharacterData.muS_orthonormal` 実証明** (FeitThompson.lean、
   muS = columnFamily.mu の列内 injective + 列間 columnFamily_mu_ne、omegaS_inner と同型 ~20 行)。
   両 derivation site に threading。construction site 破れゼロ (S15.Hypothesis の構築は spine
   1 箇所のみ)。
3. **`mu_row0_ne` (S15_HonestTypeP2A0、c file) の sorry を実証明で閉鎖** — pin 自身の docstring が
   宣言していた interface (「b-side field 待ち」) の完遂、3 行 (mu_orthonormal + if_neg)。
   cross-lane 編集 self-flag。⚠ 学び: field の inner は **scoped FiniteInduce instance** で
   elaborate される — 消費側の local `haveI` (Fintype.ofFinite/invertibleOfNonzero) とは
   instance 項不一致で rw 不可 → lemma 全体を `open scoped FiniteInduce in` に統一
   ([[lean-instance-defeq-traps]] の新実例)。

**S15_HonestTypeP2A0 実 sorry 3 → 2** (残 = tauS_mu_row0_diff_support :878 /
tauS_mu_row0_vanish_on_V :896)。両 pin の engines (`residueS_mu2_diff_support` /
`residueS_mu2_diff_dade_apply_of_mem_V`) は **proven 済** (c、hyp46S 経由) — 残 gap は
(a) pin signature の j≠0 修正 (9076 over-claim fix、consumer `_hj` pass = b の S15_SAndT 側)、
(b) hyp.mu = residueS.mu2 の **等式 grounding** (mu_orthonormal より強い、mu field ↔ residue grid
同定; engines の結論を pin の hyp.mu 形へ transport するのに必要) + η/ω^σ-grid 同定 (V-value pin)。
次 iter: (a) の signature 修正 + (b) の設計 (等式 field か、pin ごと residueS 形へ restate か —
consumer tauS_mu_row0_cross の要求形を S15_SAndT:4020 で確認してから)。9080 step 1 はその後。

## 📋 (2026-07-11、lane-b /loop iter 29) — 残 2 pins の設計確定 (consumer 精査)

- **`tauS_mu_row0_cross` (S15_SAndT:1129、(13.18.c) cross-relation) は body 完全 proven** —
  消費 = mu_row0_ne (✅ iter 28) + `tauS_mu_row0_diff_support` + `tauS_mu_row0_vanish_on_V`
  (= S15_HonestTypeP2A0 の残 2 sorry) + eta_diff_rigidity (proven)。**pins 2/3 が閉じれば
  (13.18.c) → gammaGrid_defGamma チェーンが閉じる**。docstring の「prTIirr_id 未 port」は stale
  (iter 26 で否定済) — 実体は grounding 問題のみ。
- consumer の pin 呼び出しは `tauS_mu_row0_diff_support j` / `tauS_mu_row0_vanish_on_V hG j x hx`
  — j≠0 (`_hj`) は consumer 側に既在で signature 追加時に pass 可能 (9076 fix)。
- **設計決定 (B: field-statement 方式)**: pins 2/3 は抽象 Hypothesis から under-determined
  (mu が residue grid である linking が要る)。mu_orthonormal (iter 28) と同型に、pin 相当の
  **property fields を S15.Hypothesis + 2 上位層に追加**し、producer (FT.lean cd-construction、
  mu := muS = columnFamily.mu) で実証明 discharge → pin theorems は field 射影 + j≠0 修正。
  - field 案: `mu_row_diff_support` (∀ i j k, j≠0 → k≠0 → 等次数 → (mu i j − mu i k).support ⊆
    A₀-form) / `mu_diff_dade_vanish_on_V` (V-value 形は eta を含む — eta_definition (η=ω^τ) と
    τ₃ regular-set 恒等 (tau3_apply_of_regular field) + certainTypeOmegaSigma の同定が producer
    discharge の部品)。
  - ⚠ producer 層の engine は **mp.certainTypeS** (Section16MaximalPair 由来) — S15_HonestTypeP2A0
    の engines (residueS_mu2_diff_support 等) は **hyp.s06S/hyp46S** 由来で別 instance。producer
    discharge は certainTypeS-level の S06 engines (`certainType_diff_supp_subset_A0` /
    `certainType_diff_dade_apply_eq_of_mem_V`) を直接使う (support 側は producer の A₀-Dade と
    hyp46S-A₀ の同定が必要 — ここが次 iter の精査点)。
- 副 finding: lane-c 新 leaf `TGapPrimeTI.lean` (14.9 T-side) が S13_PrimeTIResidueBridge を
  消費開始 — b の bridge が cross-lane で cite され始めた (良い信号、干渉なし)。

次 iter: (1) producer 層の A₀-Dade/hyp46S 同定を精査 (FT.lean cd-construction の Dade 部品と
honestTypeP2A0Set の対応)、(2) support field から実装 (V-value field は η 同定込みで後続)。

## 📋 (2026-07-11、lane-b /loop iter 30) — producer 層 A₀-Dade 可用性 precheck 完了

**確定**: `Hypothesis.dadeHypS0` (S15_HonestTypeP2A0:581) は
`(dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.S_maximal hyp.S_typeP2 hyp.Sdata).some.dade`
— **hG + S_maximal + S_typeP2 + Sdata のみが入力** (hyp の他 fields 不要)。∴ producer (FT.lean
cd-construction) 層でも mp-level の同名 4 部品から**同じ A₀-Dade + mp-level Hypothesis46**
(hyp46S の構築 [S15_HonestTypeP2A0:660-699] の hyp.* → mp.* 置換コピー) を構築できる。

**support field 実装手順 (次 iter、確定形)**:
1. **field** (3 層: SubcoherenceInputs / FTSetup inputs / FTSetup cd): `mu_diff_support :
   ∀ (i : Fin q) {j k : Fin p}, (j:ℕ) ≠ 0 → (k:ℕ) ≠ 0 → mu i j 1 = mu i k 1 →
   (mu i j − mu i k).support ⊆ S04.supportInSubgroup (honestTypeP2A0Set S Sdata) S`
   (S/Sdata は各層の対応 field; cd 層は mp.S + cd の Sdata source — cd/inputs の Sdata field 名を
   実装時に確認)。
2. **producer discharge**: FT.lean に `Section16CharacterData.hyp46Smp` (mp-level Hypothesis46、
   hyp46S のコピー) + `muS_diff_support` (= S15_HonestTypeP2A0 の `residueS_mu2_diff_support` の
   証明を mp-level に写す: charGroupW2Equiv → chi2enum、residueS.mu2 → muS、
   certainType_diff_supp_subset_A0 (hyp46Smp) 適用)。
3. **pin 修正** (S15_HonestTypeP2A0:878、self-flag): `tauS_mu_row0_diff_support` に
   `(hj0 : (j:ℕ) ≠ 0)` 追加 (9076 fix) + body = field 射影 (`hyp.mu_diff_support 0 hj0 one_ne
   hdeg` — hdeg は row-0 の mu2 次数一致: `mu_degree_modEq_delta` からは出ない (mod q 合同のみ)。
   **⚠ hdeg 供給が非自明**: 原文 (4.8) は残基次数一致 (両列 residue が同次数) — Coq は consumer
   が具体次数で discharge。row-0 では μ_{0j}(1) = residue-degree、j,k≠0 で一致は §13 の具体
   次数事実 — S15.Hypothesis に既存 field があるか (mu_degree 系) 実装時に確認、なければ
   `forall_columnFamily_mu_apply_one_eq_of_sum_eq` (iter 28 記録の hdeg 供給候補) を producer
   で使い hdeg-free の row-0 特化 field にする)。
4. consumer (S15_SAndT:1152 `hsupp := hyp.tauS_mu_row0_diff_support j`) に `_hj` pass (1-line)。
V-value pin (pin 3) は support field 完了後に同型で (η 同定込み)。

## 📋 (2026-07-11、lane-b /loop iter 31) — hdeg 供給の正体確定、設計完結

- **S06 に次数機構は完備**: `columnFamily_mu_apply_one_eq` (列内次数一定、proven) +
  `forall_columnFamily_mu_apply_one_eq_of_sum_eq` (列和一致 → 行別一致、proven、
  S06_CertainTypeIsometry:824)。∴ hdeg (行別) ⟸ **列和次数一致 μ_j(1) = μ_k(1) (j,k≠0)**
  ⟺ residue 次数一致 χ_j(1) = χ_k(1) (μ_j = Ind_{S'}^S χ_j、mu_colSum_eq_induce)。
- **residue 次数一致は repo 不在の genuine §13 math** (grep 確認: S13/S15 に mu 次数 fact 無し、
  S06 は (4.3.d) mod-q のみ)。数学的内容 = Pf (13.3)-region「μ_j(1) = qu (j≠0)」: S' = PU が
  **Frobenius kernel P** (type-P₂ の (13.2)/(8.4) 構造) ⟹ 非線形 Irr(PU) は全て Ind_P^{PU}(線形)
  で次数 u ⟹ 全 j≠0 で χ_j(1) = u。P-nonlinear 性は cfker_prTIres field と接続。
- **∴ 最終実装順 (確定)**:
  1. **支持 field (hdeg-parametric、math-risk ゼロ)**: `mu_diff_support` を 3 層 +
     producer discharge (mp-level Hypothesis46 + certainType_diff_supp_subset_A0、hdeg は
     hypothesis で素通し) + pin へ hj0/hk0/hdeg 追加 + 射影。
  2. **genuine math unit: residue 次数一致** — PU Frobenius kernel P ⟹ 非自明 residue 次数 = u。
     置き場 = S06 側 (certainType 層、PU-Frobenius 仮定 parametric) or S13 bridge (S-instance)。
     Isaacs Ch.6 Frobenius character theory (Ind from kernel) の在庫確認から。
  3. consumer 配線: field `mu_row0_apply_one_eq`-形 or 直接 (2) を cite して
     tauS_mu_row0_diff_support / tauS_mu_row0_cross の hdeg discharge。
  4. V-value pin (pin 3) は 1-3 後に同型 (η/ω^σ 同定込み)。

## ⚠📋 (2026-07-11、lane-b /loop iter 32) — support field の前提 blocker: def 再配置が要る

producer 部品は全て確認済 (`tp.Sdata : TypePData mp.S` / `mp.S_maximal` / `mp.S_typeP2` 存在 →
hyp46Smp copy 可)。しかし **field 文の語彙が不足**:
- `honestTypeP2A0Set (M) (data)` の定義は **S15_HonestTypeP2A0.lean:47 (lane-c file)** —
  SubcoherenceInputs (S15.Hypothesis の家) から参照不可 (import 逆方向)。
- `honestTypeP2ASet (M)` は SubcoherenceInputs **:537 = structure (:74) より後方** — field から
  前方参照不可 (b-owned なので structure 前へ移動は可)。
- A₀ の V-part (`conjClassSetIn M (typePData_toTICyclicHypothesis data hodd).V`) は hodd 依存 —
  S15.Hypothesis が hodd/odd_card field を持つか要確認。

**解決案 (次 iter で選択・実施)**:
- **案 X (推奨)**: `honestTypeP2ASet` を SubcoherenceInputs の structure 前へ移動 (b-owned、
  同 file 内 reorder のみ) + `honestTypeP2A0Set` を **S15_HonestTypeP2A0 から SubcoherenceInputs
  (structure 前) へ移設** (c file からの移設 = hub/c 調整 or 9000 issue で claim; 定義は
  honestTypeP2ASet ∪ conjClass 形で軽量、下流 import 不変 [S15_HonestTypeP2A0 は Setup を import
  済ゆえ再 export で無破壊])。その後 field 追加 (iter 30-31 の設計どおり)。
- **案 Y**: field を諦め、pins 2/3 を **hG-引数付き theorem のまま S15_HonestTypeP2A0 内で
  discharge** — hyp.mu と residueS.mu2 を結ぶには grounding が要る点は不変だが、mu_orthonormal
  同様の「pin 専用の弱い field」(例: `mu_eq_certainType_grid : ∃ (同定 data), ...`) でなく、
  **mu_definition (13.1.e) から mu を residue grid と同定する一意性定理** (Ind-差 = δ(μ-差) が
  mu を列ごと anchor+順序まで pin する — mu_orthonormal + mu_definition + delta で mu = muS を
  導出できるか) を精査。可能なら **field 追加ゼロ**で pins が閉じる (最も honest)。
次 iter: 案 Y の一意性精査 (mu_definition の pin 力) を 30 分 → 不成立なら案 X 実施。

## 📋 (2026-07-11、lane-b /loop iter 33) — 案 Y 一意性検証: mu-given-omega は成立、omega-grounding に帰着

**案 Y の数学検証 (机上、成立)**: mu_definition (列差 Ind 恒等式) + mu_irreducible +
mu_col_injective だけで **grid は (omega, delta) から一意**:
2 解 mu, mu' は列差一致 → mu i j = mu' i j + c (c = anchor 差、i-独立)。c ≠ 0 なら ‖c‖² = 2、
norm 展開で i≠0 に ⟨mu' i j, mu 0 j⟩ = −1 を強制 — genuine irreducible 同士の inner は {0,1}
ゆえ矛盾 (q ≥ 2 で i≠0 存在) → c = 0 → mu = mu'。**この一意性補題は単体で landing 価値あり**
(グリッド grounding の全てをこれ 1 本で「omega/delta grounding」に帰着させる)。

**ただし pins 2/3 には不十分**: 一意性は hyp.mu を「hyp.omega が生成する grid」に pin するが、
support/V-value の certain-type 幾何は **hyp.omega = (transported chiColumn grid)** の grounding
を要する — omega の既存 property fields (mul/orthonormal/pow/row-col-zero、2033/3002) は
omega を relabeling まで pin するのみ (生成元べき enumeration の同定が別途要る)。
∴ **案 X (def 再配置 + field) が pins の実務 route で確定**。一意性補題は独立 unit として後続
(mu-grounding 系の整理に使う)。

**次 iter (案 X 実施、順序)**:
1. `honestTypeP2ASet` (:537) を SubcoherenceInputs 内で structure (:74) 前へ移動 (b-owned reorder、
   下流不変)。
2. `honestTypeP2A0Set` の移設 (S15_HonestTypeP2A0:47 → SubcoherenceInputs structure 前) —
   c-file からの移設は 9000-issue で claim + self-flag (定義 1 個 + hodd 依存の V-part;
   S15.Hypothesis の odd_card/hodd field 有無を確認し、無ければ A₀ 形を「A ∪ (hodd 引数付き
   V-conj 部)」でなく **field 側で hodd を仮定に取る**か検討)。
3. field 追加 (iter 30 設計) + producer discharge (hyp46Smp) + pin 修正。

## ✅ (2026-07-11、lane-b /loop iter 34) — 案 X step 1-2 完了: A/A₀-support def 移設

`honestTypeP2ASet` (同 file 内前方移動) + `honestTypeP2A0Set` (S15_HonestTypeP2A0 [c file、
self-flag content-preserving 移設] → SubcoherenceInputs structure 前) — 両 def が S15.Hypothesis
の field 語彙で使用可能に (commit 上記、full build 4150 green・AxiomsCheck OK)。typePV/
conjClassSetIn は GroupTheory 層で既に閉包内、hodd-free 確認済。

**次 iter (案 X step 3 = iter 30 設計の field 追加本体)**:
`mu_diff_support : ∀ (i : Fin q) {j k : Fin p}, (j:ℕ)≠0 → (k:ℕ)≠0 → mu i j 1 = mu i k 1 →
((mu i j − mu i k)).support ⊆ S04.supportInSubgroup (honestTypeP2A0Set S Sdata) S` を 3 層 +
producer discharge (hyp46Smp = hyp46S copy [dadeSupportHypothesisData_honestTypeP2A0Set hG
mp.S_maximal mp.S_typeP2 tp.Sdata + subH=M_σ 4 論証、S15_HonestTypeP2A0:660-699 参照] +
muS_diff_support = residueS_mu2_diff_support の mp-level 写し [chi2enum 版]) + pin 修正
(hj0/hk0/hdeg 化) + consumer `_hj` pass。

## ⚠📋 (2026-07-11、lane-b /loop iter 35) — 真の残 content 確定: 2 つの S06 instance の grid 同定

field 追加の producer discharge 精査で **make-or-break 事実**:
- **producer grid `muS` は `mp.certainTypeS` 上** = `certainTypeHypothesis_of_typeP_kappaHall`
  構築 (FTSetup:1142、kappaHall-based)。
- **engines (certainType_diff_supp_subset_A0 経由の hyp46S/hyp46Smp) は
  `typePData_toS06Hypothesis (Sdata)` 上** (hypothesis46OfTypePData が toHypothesis を hardcode)。
- 両者は **別 instance の S06.Hypothesis** (W₁/W₂ は Sdata_W1_eq 等で propositionally 一致するが
  columnFamily は各 instance の `.choose`) — ∴ **muS-grid と engine-grid の同定**が pins 2/3 の
  真の残 mathematical content (c が pins を「grounding 待ち」と sorried にした本当の理由)。

**同定 plan (iter 33 の一意性がまさに道具)**:
1. **一意性補題 landing** (次 iter、self-contained): 同一 (Ind, ω-族, δ) に対する (13.1.e) 恒等式の
   解 grid は一意 — iter 33 検証済の議論 (列差一致 + anchor 差 c の norm 矛盾、
   irreducible inner ∈ {0,1})。置き場 = IsometryDifferencePair or S06 層
   (`SignedIrreducibleDifferenceFamily.eq_of_signedDifference_eq`-形: 2 family が
   ∀ i, signedDifference 一致 + sign 一致 → mu 一致; あるいは Ind-恒等式形で)。
2. **ω-grid 同定**: certainTypeS.chiColumn ↔ (Sdata-instance).chiColumn — 両者は同じ W ≤ S の
   線形指標 grid (enumeration 差)。omegaProdChar の自然性 + W₁/W₂ set-equalities で。
3. mu-grid 同定 (1+2) → engines の結論を muS/hyp.mu 形へ transport → pins/field discharge。

**当面の実装順変更**: field 3 層追加は同定完了後に延期 (field 文自体は iter 34 で語彙 ready)。
次 iter = 一意性補題 (step 1) の Lean 化 — 数学は検証済ゆえ実装のみ。

## ✅ (2026-07-11、lane-b /loop iter 36) — grid 一意性 (anchored-difference rigidity) landed

**`irreducibleCharacterFamily_eq_of_difference_eq`** (IsometryDifferencePair.lean、commit 512b3c82、
一発 green、full build 4150・AxiomsCheck OK): 差族一致 (ν_i − ν_0 = ν'_i − ν'_0) + ν' 単射 +
n ≥ 2 ⟹ ν = ν'。iter 33 検証の anchor-shift norm 矛盾論法どおり。

**⟹ (13.1.e) 型 grid は (ω, δ, Ind) から一意** — certainTypeS ↔ Sdata-instance の mu-grid 同定は
「両 instance の **ω-grid + δ + Ind の同定**」に帰着 (iter 35 plan step 2)。

**次 iter (同定 step 2 = ω-grid 同定の精査)**: certainTypeS.chiColumn と
(typePData_toS06Hypothesis Sdata).chiColumn の関係 — 両者の W (W₁ ⊔ W₂) は同一部分群か
(certainTypeHypothesis_of_typeP_kappaHall の W₁/W₂ = mp.K/mp.Kstar vs Sdata の W1/W2 —
tp.Sdata_W1_eq : Sdata.W1 = tp.W1 と mp.K との関係、FTSetup の certainTypeS_W1_eq/W2_eq
[FT.lean iter 28 で見た] が既にこの同定の一部)。同一なら chiColumn は同じ型の grid で
enumeration (w1CharEquiv/両 instance の生成元べき) の突合せのみ。δ/Ind は W 同定に従属。
その後: 同定合成 → engines の muS-transport → pins 2/3 discharge → field 追加は不要になる
可能性 (同定が直接 pin を出すなら iter 30-34 の field 計画は簡約) — 同定完了時に再判断。
