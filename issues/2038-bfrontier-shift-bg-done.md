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
