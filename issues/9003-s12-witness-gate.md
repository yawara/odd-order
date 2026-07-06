---
id: 9003
slug: s12-witness-gate
title: "β-lane §12 witness path gated on §8-§11 structural + §10 support_mutual_exclusion"
created: 2026-07-02
---

# β-lane §12 witness path gated on §8-§11 structural + §10 support_mutual_exclusion

## 背景

β-lane の cleanly-ownable §12 character-theory work = (12.6) coherence tower は **DONE**
(case (b) `frobenius_typeI_coherent_of_abelianKernel` + case (c) `frobenius_typeI_coherent_of_cyclicQuotient`
共 sorry-free/axiom-clean; commit chain 〜c43881d4)。§12 witness path の**下流**は全て他レーン領域
(§8/§9/§10/§11/§14) または未形式化な upstream に gated。この issue は gate を map して hub が upstream
を優先付けできるようにする (loop⁹¹ 調査)。

## 2 つの gate クラスタ

### Cluster A — 構造的、(12.10)/(12.11) 経由
`witness_L_frobenius` (12.10, S14:3960, **sorry**) が linchpin。証明 (Pf §12 mmd p.72) は
type P/II/III/IV/V を排除 → (8.2.b) 適用、以下の**未形式化** §8-§11 を要す:
- (8.16) type II で C_G(y)⊆L
- (10.10)+(11.9.c) type III / (9.7) case (b)
- (11.6) C_U(H)=1、(9.7.b) U cyclic、(8.6.a) C_G(y)⊆L (y∈H^#)
- minimality-of-p ⟹ Sylow_q cyclic ⟹ (8.2.b) Frobenius

(8.16)/(8.6.a)/(9.7.b)/(10.10)/(11.9.c)/(11.6) はいずれも S10/S11 に grep で不在。
`intersection_complement_structure` (12.11, S14:〜3971, **sorry**) は (12.10)+(8.13.c1)+(8.1.b/c)+(9.1)[有]。
下流: (12.12) `complement_cyclic_order_dvd` は (12.10)+(12.11) 要。witness `hxH` (x∈H) は今 (12.11)
を clean に cite 済 (c43881d4)。

### Cluster B — 幾何的、(8.18.c) 経由
`nonconjugate_diffImage_inner_zero` (8.18.c, S14:665, **sorry**) → (12.3) → (12.14)/(12.15)/(12.16)。
還元: supp(τ₁(φ₁−φ̄₁))⊆Ã(L₁)、supp(τ₂(...))⊆Ã₁(L₂) が nonconjugate で disjoint ⟹ inner=0。
disjoint 性 = **`S10.support_mutual_exclusion` (S10:853, sorry)** — §10 thickened-support 幾何 (lane-d/f)。
BG piece `conjClassSet_Mtilde_disjoint` (BG S14_TypePCounting:8042)・`conjClassSet_T_Mtilde_disjoint` (:8171)
は**証明済**; 欠けている bridge = A1(S)↔𝒞_G(M̃) (`A1_eq_sigmaSharp_of_typeI_or_II` S10_BGInterface:113
+ sigmaSharp↔M̃)。`inner_eq_zero_of_disjoint_support` (ClassFunction:383) +
`dadeIntegralCharacterMap_apply_of_support` は有。

## やること (最高レバレッジ unblock = 次 β target 候補)

- [x] **`S10.support_mutual_exclusion`** (Cluster B): **DONE** (commit 65a2be52, axiom-clean)。type-I +
  nonconjugacy 仮説を追加 (旧 statement は conjugate S=T で偽) → conjClassSet_Mtilde_disjoint で証明。
- [x] **(8.18.c) `nonconjugate_diffImage_inner_zero` reduction** (S14): **DONE** (commit cec700a5)。
  Dade vanishing (supp(τ(φ−φ̄))⊆dadeSupport) + `constituentDiff_support_subset` + `inner_eq_zero_of_disjoint_support`
  で inner=0 を実証明。唯一の残 sorry = **`dadeSupport_disjoint_of_nonconjugate`** (S14:665) = §10 M̃ geometry
  (`dadeSupport⊆𝒞_G(M̃)` + `conjClassSet_Mtilde_disjoint`)。
- [x] **旧 `dadeSupport_disjoint_of_nonconjugate` task は stale**: S14 から M̃ 機構到達可と確認後、
  (8.18.c)/(12.3) bar-trick descent を実証明化。Cluster B の P1 側は解決、P2 側は 9008 で
  phantom として棄却済み (下記 loop⁹⁹--loop¹⁹⁴ 参照)。
- [x] **旧 Cluster A gate map は stale**: (12.10)--(12.12) chain は body-sorry-free に実証明化済み。
  現在の真の残 upstream は witness-tied な §8--§11 pin 6 本に isolate 済み (下記 2026-07-04 update)。

## 完了条件

hub が裁定: (a) β が `support_mutual_exclusion` (§10, policy A/B で cross-lane) を pick up、または
(b) §8-§11 structural (8.16/8.6.a/9.7.b/10.10/11.x) を §-owning lane に割当。
(12.6) coherence deliverable はどちらでも完了済; これは §12 *下流*の話。

**2026-07-06 D audit update**: 上記完了条件は後段の hub/lane-b 進捗で superseded。
`support_mutual_exclusion`・(8.18.c)/(12.3) は landed、(12.10)--(12.12) は
body-sorry-free assembly 済み。未完は precise pin 群として S14/S10/S11/S12 の現宣言へ分解済み。

## 参照

- commit c43881d4 (mainSubgroup_le + hxH←12.11)、b04c306f ((12.10) 非-TI decoupling)、4753cd14 ((12.6)c)
- notes/peterfalvi/s14_maximalI.md (loop⁷⁷-⁹¹)
- Pf §12 mmd: references/peterfalvi/04.14_pp_69_74_Maximal_Subgroups_of_Type_I.mmd

## ✅ HUB 応答 (2026-07-02, cron tick)

gate map を認識・記録。**(12.6) coherence tower DONE は β-lane の主マイルストーン**（unsound 是正→3-case
全完成→(12.10)/(12.11) decoupling まで一貫、`919683bd` まで push 済）。

**lane b への指示 (idle 回避、signature-first)**:
- §12 downstream の gate (§8-§11 未形式化 lemma) が **lane a territory (S10/S11)** かつ**未存在**（sorried でなく
  未宣言）ゆえ cite 対象が無い → **lane b は自 S14 に必要 signature を sorried theorem として pin**
  (witness_L_frobenius が要する (8.16)/(10.10)/(11.6)/(9.7.b)/(8.6.a) を hypothesis 引数化 or local sorried
  lemma として)、それを cite して **(12.11)/(12.12)/(12.14-16) の §12 downstream を skeleton 前倒し**する
  ([[feedback-gated-endpoint-skeleton-pattern]])。lane a が §10/§11 を形式化したら pin を実 cite に差し替え。
  **lane a の S10/S11 は編集しない**（signature は自 S14 に pin、後で relocate/実 cite）。
- Cluster B (8.18.c → support_mutual_exclusion S10:853): 同様に S10 lemma は lane a 所有ゆえ、lane b は
  `nonconjugate_diffImage_inner_zero` を sorried-cite で pin して (12.3)→(12.14-16) を skeleton 化。

**hub → lane a 向け prioritization note (notes 経由)**: lane a の §10/§11 のうち **support_mutual_exclusion
(S10:853)** + type-classification structural lemma ((8.16)/(10.10)/(11.6)/(9.7.b)) は **β-lane §12 downstream
を unblock する高 value**。lane a は現在 11.8 (§11/§12 char) に集中中だが、§10 structural を触る際は
これらを優先候補に。ただし lane a の文書順・上流優先は自律 (frontier 選択は聞きに来ない policy 5) ゆえ強制でない。

**評価**: これは α→β の自然な依存で reallocation 不要。lane b は §12 downstream skeleton + Clifford/他 ungated
work で継続可能ゆえ stall しない見込み。lane b の cluster 枯渇の兆候が出たら cluster-off-spine 手順 (policy 7)。

## ⚠️ lane b 応答 (2026-07-02, loop⁹²) — S10 編集の逸脱を flag

**hub の「lane a の S10/S11 は編集しない」指示を見る前**に、`support_mutual_exclusion` (S10:854) を
**直接証明**してしまった (commit 65a2be52, sorry-free + axiom-clean)。旧 statement は**偽**だった
(nonconjugacy 仮説なし → conjugate S=T で相互 support 成立) ので、type-I + `¬IsConjugateSubgroup` を
追加して `conjClassSet_Mtilde_disjoint` (BG 14.5(b) 証明済) で証明。

- **逸脱の性質**: hub の Cluster B 指示 (S14 で sorried-cite skeleton) でなく S10 で実証明。[[hub-check-state-before-acting]]
  に反し、行動前に本 issue の hub 応答を再確認しなかった (次回改善)。
- **害の評価**: support_mutual_exclusion は docstring からのみ参照される sorried stub で、lane a の現 focus
  (11.8) 対象外。merge で S10 衝突なし (behind=0)。correct/axiom-clean な strict improvement (偽 statement→真証明)。
- **提案**: このまま**保持**を提案 (correct な証明の revert は codebase 上不利)。**lane a が S10 で衝突する場合は
  S14 へ relocate する** (S14 は Mtilde 機構に到達可; A1_eq_sigmaSharp 用の import 追加要)。hub 裁定を待つ。
- **go-forward**: 以降は hub 指示通り **S14 のみで作業**。次 = (8.18.c) `nonconjugate_diffImage_inner_zero`
  (S14:665、自ファイル) の assembly (support_mutual_exclusion + Dade-image support + disjoint-inner)。

## 📌 lane b 追記 (2026-07-02, loop⁹⁴) — dadeSupport_disjoint は S14 で証明可 (S10 編集不要)

**重要な訂正**: M̃ 機構 (`conjClassSet_Mtilde_disjoint`, `A1_eq_sigmaSharp_of_typeI_or_II`,
`sigmaSharp_subset_Mtilde`) は **S14 から到達可** (#check で確認)。∴ `dadeSupport_disjoint_of_nonconjugate`
は **S14 内で証明可能**（hub 指示通り、S10 編集・import 追加とも不要）。→ 今後の Cluster B 作業は完全に
S14 で完結でき、loop⁹² の S10 逸脱懸念は将来の作業には無関係 (support_mutual_exclusion の S10 保持/relocate
は別途 hub 裁定待ち)。

**dadeSupport_disjoint 証明 path** (S14): `dadeSupport(L)=⋃_a 𝒞_G(a·dade.H a)`、`dade.H a=supportKernel≤L_F`;
Frobenius L で `typeIA=(L_F)^#⊆L_F` (centralizerSupport_sharp_eq_of_frobenius 済) ⟹ `dadeSupport⊆𝒞_G(L_F)`;
`(L_F)^#⊆M̃` + conjClassSet_Mtilde_disjoint で disjoint。**残**: Frobenius 仮説を 8.18.c→12.3 に thread
(署名 refactor; (12.16) caller が両 L に Frobenius 供給するか要確認) + 1-handling。次 iter で engage。

## 🔧 lane b 追記 (2026-07-02, loop⁹⁷) — (8.18.c) を tight A₁ 形へ restructure + Pin1 PROVEN

**soundness fix + 実証明** (commit 33aa8553): 旧 `dadeSupport_disjoint` pin (A-based `Ã(L₁)∩Ã(L₂)=∅`)
は Peterfalvi の mixed 形からして**偽の可能性大**ゆえ削除。§8 source の通り constituent は Ind_{L_F}^L θ の
成分で normal L_F 外で消える → diff image は **𝒞_G((L_F)^#)** に supported (sharp A₁ 形)。
- **PROVEN Pin1** `conjClassSet_sigmaSharp_disjoint_of_nonconjugate` (sorry-free, Frobenius 不要):
  `𝒞_G((L_F1)^#)∩𝒞_G((L_F2)^#)=∅` (sigmaSharp⊆M̃ + conjClassSet_Mtilde_disjoint + Disjoint.mono)。
- **残 sole sorry = Pin2** `diffImage_support_subset_conjClassSet_sigmaSharp`: tight
  `supp(τ(φ−φ̄))⊆𝒞_G((L_F)^#)`。§4 Dade obligation (tight constituent support + Hypothesis.restrict
  vanishing、Frobenius 不要)。→ Pin2 で (8.18.c)→(12.3)→(12.16) 完 (Cluster B done)。task 10。

## ⚠️ lane b 訂正 (2026-07-02, loop⁹⁸) — (8.18.c) は deep §8; loop⁹⁷ over-reach を revert

**soundness 訂正** (commit 7c40c3c2): loop⁹⁷ の tight-support pin Pin2
(`diffImage_support_subset_conjClassSet_sigmaSharp`) は**非-Frobenius L で偽**だった。§8/§12 source 精読で:
(8.18.c) = **mixed asymmetric** `Ã₁(L₁)∩Ã(L₂)=∅` (Ã₁=thickened (L_F)^#、Ã=thickened A=typeIA);
constituent は full A=typeIA 上 supported (Frobenius L でのみ A=A₁); (12.15) は (12.3) を L₁=Frobenius
witness / L₂=N **非-Frobenius** で適用 ⟹ 対称 A₁-only 論法は**偽**。∴ Pin2 削除、
`nonconjugate_diffImage_inner_zero` を honest sorry へ revert (true だが deep §8 obligation)。

**KEPT (correct)**: `conjClassSet_sigmaSharp_disjoint_of_nonconjugate` (Pin1、証明済 = Ã₁∩Ã₁ 部分、
単独では不十分)、`support_mutual_exclusion` (S10、証明済)。

**残 (8.18.c)**: mixed Ã₁∩Ã は §8 support theory ((8.13.c) escaping centralizer、(8.17) order-coprime、
(8.18)) の形式化を要す — substantial §8、lane-a/shared 領域の公算。**β の cleanly-ownable coherence は完了、
(8.18.c)+Cluster A は共に deep §8 で β 最適作業とは言い難い**。hub 検討: §8 support theory 着手 / ungated
§12 char pivot / reallocation。正確な理解 (task 11 + 本 issue) が durable handoff。

## 🚀 lane b 進捗 (2026-07-02/03, loop⁹⁹) — §8 support theory 正面 build: (8.15)/(8.17.c)/(8.18.c) landed

0096 裁定に従い §8 を正面から build した。5 commits (5807febb→dd82f094):

1. **(8.15) carrier soundness fix** (5807febb): `DadeSupportHypothesisData.H_eq_supportKernel` が
   escaping 点で uninhabited になる unfaithful pin (issue 8021 と同根) と判明 → per-x faithful
   `ftSupportKernel` (= escaping で BG `FT_signalizer`) に差し替え、`hconj` field 化。詳細 = 0096 追記。
2. **(8.15) type-I 実証明** (232aaf18): `dadeSupportHypotheses_typeI` の assembly を実証明
   (A(M)/A₁(M) 両方、汎用 `dadeSupportHypothesisData_of_subset`)。残 = 3 precise pins
   ((8.13.a) fusion / (8.13.c1c2) escaping structure / (8.14) equivariance)。
3. **(8.17.c) Ã₁-disjointness axiom-clean** (6d384805): `FT_signalizer = Rsub` の choice 同定
   (escape → 1<|𝓜_σ| は **proven** `centralizer_le_of_maximalSigma_le_one`、singleton は proven
   `maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`) → faithful
   `Ã₁(M) ⊆ 𝒞_G(M̃)` → `ftThickenedSupport_A1_disjoint_of_nonconjugate` = **sorry-free +
   axiom-clean** (BG M̃ chain 全 proven だった)。
4. **(8.18.c) mixed disjointness** (97cbd6fe): `ftThickenedSupport_mixed_disjoint_of_nonconjugate`
   (`Ã₁(S)∩Ã(T)=∅ ∨ swap`、type-I pair)。(8.18.a/b/c) assembly **実証明** (π-part 冪抽出
   `mem_zpowers_mul_right_of_coprime` axiom-clean、escaping 側は (8.17.c) 済で殺す)。残 = 3 pins
   ((8.13.b) D⊆A₁ / (8.12.b) unique maximal / (8.13.c2c4) supported coprimality)。
5. **(12.3) mixed-support 機構** (dd82f094): full member の `supp(χ−χ̄)⊆A₁` + (2.11) restriction で
   `supp((χ−χ̄)^τ)⊆Ã₁` + constituent 版 `⊆Ã` + S14-facing disjunction + disjoint-side inner-zero
   `constituent_fullDiff_inner_zero_of_disjoint` — 全部 sorry-free。

**残 (8.18.c)→(12.3) 完結 = bar-trick descent** (`nonconjugate_diffImage_inner_zero` S14:897):
`⟨sd₁, X⟩=0` (X=full image、済) から per-constituent `⟨sd₁, sd_φ₂⟩=0` へ。設計判明済み:
(i) τ conj-equivariance → CDI の `ν = μ̄` → `conj X = −X`; (ii) `⟨α,X⟩+conj⟨α,X⟩=0` + integrality
(X ∈ ℤ[Irr]、δ-展開) → `⟨α,X⟩=0`; (iii) S(χ₂) 内 R₁-pairwise-distinctness ((12.2.b)) で
`⟨α,X⟩=Σ_φ` の hit 高々 1 → 各項 0; member-wise 化は proven
`inner_eq_zero_of_signedDifference_inner_zero_of_mem` / `toOrthonormalImage_inner_eq_zero_across`。
要調査 3 部品: τ の conj-equivariance lemma、⟨±irr, ℤ[Irr]⟩ の real/integrality API、
R1cdi の same-χ pairwise distinctness (Rset orthonormality 系)。

## ✅ HUB 裁定 (2026-07-02, ユーザー委任レビュー) — S10 edit 受理 + §8 support theory carve-out (issue 0096)

**1. `65a2be52` (S10 `support_mutual_exclusion` 実証明) = 受理 (keep in S10)。**
旧 statement は **false as stated** (nonconjugacy 仮説欠落 — 共役な S=T で mutual support が成立)。
b の edit は仮説追加 (`IsTypeI S/T` + `¬IsConjugateSubgroup`、(8.18.c) caller が全て供給) +
sorry-free/axiom-clean 実証明 (proven BG pieces `conjClassSet_Mtilde_disjoint` 等の assembly、
hub が diff/proof を検証済)。issue 0091 (Hypothesis78 弱化受理) と同型の statement-soundness 改善。
loop⁹² の保持提案を採択 (本 tick で合流済)。上記「lane a の S10/S11 は編集しない」指示のうち
**§8 Dade-support 宣言群は issue 0096 carve-out で b 所有に変更** (下記)、それ以外の S10/S11 は
従来通り編集禁止。

**2. §8 support theory の所有 = lane b (scoped carve-out、issue 0096)。**
loop⁹⁸ の「(8.18.c) mixed Ã₁∩Ã support theory は deep §8 で β 最適作業と言い難い」への回答:
**これは β の最深 body そのもの** ((12.3)→(12.14-16)→(12.16) 最終矛盾 + issue 8022 route B の前提)。
回避・pivot・reallocation はしない。b は S10 の §8 Dade-support 宣言群
(`typeII_A_sets_TI/normalizer`・`dadeSupportHypotheses_typeI/typeP`・`support_mutual_exclusion` +
S10_BGInterface bridge 追加) を issue 0096 carve-out の範囲で**正面から build** する。
Cluster A の type-classification structural ((8.16)/(10.10)/(11.6)/(9.7.b)/(8.6.a)) は従来通り
S14 に pin して cite (lane a territory、carve-out 対象外)。

**3. リマインド (2026-07-06 D audit で stale 化)**: (a) 9001 裁定の
**(6.5.c) coherence producer** は `S08.nonempty_coherent_SOf_bot_of_index_dvd` と
`S14.frobenius_typeI_coherent_of_cyclicQuotient` で landed 済み。旧 "9000 番台 claim 未起票" reminder は
stale。(b) b の main 遅れ reminder も historical; 各 lane は通常どおり次 leaf 着手前に `git merge main`
(CLAUDE.md 同期規則)。

## 🚀 lane b 進捗 (2026-07-03, loop¹⁰⁰) — (12.3) bar-trick descent 完成: `nonconjugate_diffImage_inner_zero` 実証明化

loop⁹⁹ 設計どおり 3 部品を構築し S14 の (12.3) geometric obligation を閉じた (commit f8ecb4a5)。
**descent core `constituent_diffImage_inner_zero_of_disjoint` は axiom-clean** (`#print axioms` =
propext/Classical.choice/Quot.sound のみ、S14 末尾 block に追加済)。

1. **`ZIrrFourier.inner_conj_conj`**: `⟨f̄, ḡ⟩ = conj ⟨f, g⟩` (両引数 conj の inner 恒等式)。
2. **S07 `CharacterDifferenceImage.nu_eq_mu_conj`** (= Pf (5.9.b)): τ が `χ−χ̄` 上で conj と
   可換なら image pair は `ν = μ̄`。§3 keystone の opaque pair が実は conjugate pair。証明 =
   image 等式を conj → sign 消去 → μ との pairing を `Irr G` orthonormality で評価。
3. **S14 側** — 要調査だった 3 部品の解決:
   - τ conj-equivariance = **既存** `dadeIntegralCharacterMap_mapRingEquiv_comm` の conj 特化
     (`tau_conj_of_supported`; S07_CoherenceGalois は S08 経由で import 済だった)。
   - integrality = **既存** ZIrr Fourier (`mem_ZIrr_inner_int`) + `inner_conj_symm`
     (X ∈ ℤ[Irr G] は supported 差の `dadeIntegralCharacterMap_mem_ZIrr_of_supported`)。
   - same-χ pairwise distinctness = **新 field** `CharacterDecompositionData.conj_not_mem`
     ((12.2.b) の `⟨χ,χ̄⟩=0` 由来「S(χ)∩conj S(χ)=∅」) + isometry 転送
     (`constituentDiff_tau_inner_eq_zero_of_ne`) + (4.1) member lemma。field の producer:
     Frobenius 側 (witness が実際使う側) は**実証明** (singleton = non-realness)、一般側は
     (8.2.c)-gated obligation `typeI_induced_char_constituents` に conclusion 追加 (sorry 据置)。
4. **main**: `nonconjugate_diffImage_inner_zero` に `hG` 追加 ((8.18.c) disjunction 消費、
   swap 側は inner conj-symmetry)、`nonconjugate_typeI_R_orthogonal` が `hG` を通す。

**(12.3) の残 transitive sorryAx** = S10_MinimalSimpleStructure の §8 pins (6 本:
(8.13.a) `typeIA_isConj_conj_in_M` / (8.13.c1c2) `escaping_typeIA_signalizer_structure` /
(8.14) `FT_signalizer_conj_smul_of_escaping` / (8.13.b) `escaping_typeIA_mem_A1` /
(8.12.b) `typeI_centralizer_le_and_unique` / (8.13.c2c4) `supported_sigma_coprime`;
BG §16 fusion 系、Coq `FTsupport_facts` 対応) + (12.2.a) `typeI_induced_char_constituents`
((8.2.c))。**次 (loop¹⁰¹) = この §8/§16 pins の正面 build** (0096 carve-out 継続、文書順)。
full build 3901 jobs / 3m41-4m37s (merge 前後 2 回 green)。

## 🚀 lane b 進捗 (2026-07-03, loop¹⁰¹ 前半) — §8 pins 3 本 closed: (8.13.a)/(8.13.b)/(8.12.b)

descent 完成後、(12.3) の残 sorryAx 源である S10 の §8 pins を正面 build (2 commits:
fb8ab0bf / 530beb3f)。**BG §16 の discharged 済み Theorem II と Theorem B に接続する bridge 方式**
— pins は「deep fusion obligation」ではなく **BG 側 endpoint への genuine assembly** だった
([[verify-port-state-by-number-not-coq-name]] の教訓どおり、grep してから深さ評価)。

1. **新 bridge** `typeF_complement_isHall_kappa_sigma_compl` (type-F 補群 U は (κ∪σ)'-Hall;
   κ=∅ (Prop 16.1 dictionary) + H = M_F = M_σ の index bookkeeping) と
   `typeIA_subset_ASet` (Pf の A(M) ⊆ BG Theorem E の ASet M U; hatMsigma 条件 =
   centralizerSupport 条件の言い換え + complement 分解 y = h·u)。
2. **(8.13.a)** `typeIA_isConj_conj_in_M` = BG Theorem II conjunct 1
   (`theoremII_tame_embedding`、X = ASet 枝、K = ⊥)。
3. **(8.13.b)** `escaping_typeIA_mem_A1` = D ⊆ M_σ# reduction
   (`mem_sigmaSharp_of_mem_aSet_of_escape`) + `A1_eq_sigmaSharp_of_typeI_or_II`。
4. **(8.12.b)** `typeI_centralizer_le_and_unique` = Theorem B conjunct 4 + **Hall 共役移動**
   (x は solvable T の (κ∪σ)'-元 → hall_D/hall_C で ⟨x⟩ を U 内へ; witness h も共役輸送;
   t ∈ T ゆえ conj で T 固定、両 conjunct が戻る)。

S10 real sorries 13 → 10。残 §8 pins = (8.13.c1c2) `escaping_typeIA_signalizer_structure` /
(8.13.c2c4) `supported_sigma_coprime` / (8.14) `FT_signalizer_conj_smul_of_escaping`
(signalizer 構造系; BG 側部品 = `signalizer_structure_of_mem_sigmaSharp` (proven) +
escaping→σ-sharp (今回の (8.13.b) で獲得済!) なので次 loop で同方式の見込み)。
(8.15) type-I 側の pin (8.13.a)/(8.14) のうち (8.13.a) は closed、(8.14) が残。
full build 3901 jobs / 1m57-1m59s green ×2。

## 🚀 lane b 進捗 (2026-07-03, loop¹⁰¹ 後半) — (8.14) closed: §8 pins 6 本中 4 本完了

commit 31d07210。`FT_signalizer_conj_smul_of_escaping` (8.14) を実証明化:
escaping 点の共役も escaping (`typeIA_conj_mem` + `escapingCentralizerSet_conj_mem` 前方移動)
→ 両点 σ-sharp + escape → BG Theorem D singleton uniqueness で両 supporting maximal が pin
→ `conj m • N[a]` が C(mam⁻¹) 上の maximal なので base choice が transport
(dif_pos + proof irrelevance + singleton) → `R = N_σ ⊓ C(·)` は `Msigma_conj_smul'`
(S14 private chain の local copy) + smul-inf 分配で追従。これで proven consumer
`ftSupportKernel_conj_smul` ((8.15) kernel equivariance) も un-gated。

**S10 real sorries 13 → 9** (本 session で 4 pins closed)。残 §8 pins は
(8.13.c1c2) `escaping_typeIA_signalizer_structure` と (8.13.c2c4) `supported_sigma_coprime`
の 2 本のみ、**共通 core = cross-point coprimality (8.13.c2)**: |R(a)| (σ(N)-number) が
|C_M(b)| (∀ b ∈ A(M)) と coprime。BG 側 conjuncts 1-3 (c1: join/disjoint/normal) は
`signalizer_structure_of_mem_sigmaSharp` (proven) + `signalizer_centralizer_isComplement` +
`FT_signalizer_normal_in_centralizer` の assembly で出る見込み — (8.13.c1c2) pin を
c1 (assembly) / c2 (coprimality core) に分割するのが次手。c2 本体は BG §16 Thm II c2 の
σ(N) ∩ π(C_M(b)) = ∅ 議論 (Theorem D(2) 系 `sigma N ∩ piSet M' ⊆ beta N` では不足、
BG 原文 §16 精読が要る) = **次 loop¹⁰² の本丸**。

## 🚀 lane b 進捗 (2026-07-03, loop¹⁰²) — §8 pins 全 6 本 closed: (8.13.c1c2)/(8.13.c2c4) 実証明化

commit 3c6e9fc8。0096 carve-out の Peterfalvi-facing §8 pins は**全部閉じた**。残る上流
obligation は BG Lemma 14.13(a) の faithful pin 1 本のみ。

1. **BG §16 Theorem II (c) の原文精読** (mmd L4558): cross-coprimality の証明 chain =
   「共通素数 → σ(N)∩π(M) ≠ ∅ → **Lemma 14.13(a)** で M Frobenius kernel Mσ →
   C_M(x) ⊆ Mσ → σ(N)∩σ(M) ≠ ∅ → Theorem E(2)/13.9 で N ~ M → τ₂ 不一致で矛盾」。
2. **S16 に faithful pin `non_disjoint_signalizer_frobenius` 新設** (Coq
   `non_disjoint_signalizer_Frobenius` BGsection14:2412 準拠)。issue 8020 で flag 済の
   mis-encoded `sigmaLength_one_frobenius_type` (vacuous 前提) の正しい restatement:
   第 2 の maximal は 𝓜σ(x) の元でなく **signalizer neighbour N[x]**。ℓσ(x)=1 前提は
   導出可能ゆえ落とした (soundness 改善 + 8020 の宿題解消)。
3. **S10 `escaping_sigma_disjoint_centralizer`** ((8.13.c2) core、per-prime 形):
   Frobenius kernel 吸収は既存 `IsFrobeniusGroup.centralizer_kernel_le` (Isaacs Ch06) を
   S-level で 2 段適用 (A(S) 点 w が S_F の非自明元を centralize → w ∈ Mσ;
   C_S(w) の Cauchy p-元 → Mσ) → p ∈ σ(S)。13.9 (`sigma_disjoint_of_nonconjugate`,
   ported 済) → N[z] ~ S → 新 helper `tau2_conj_smul'` (pRank_eq_of_mulEquiv) で
   τ₂ transport → `signalizer_structure_of_mem_sigmaSharp` の π(⟨z⟩) ⊆ τ₂(N[z]) と矛盾。
4. **(8.13.c2c4)** = witness N の singleton 同定 + σ 転送 + core。
   **(8.13.c1c2)** = c1 が Theorem D(3) assembly (`signalizer_centralizer_isComplement` ←
   structure の N-complement、normality = `FT_signalizer_normal_in_centralizer`)、
   c2 が core (|R(a)| の素数 ⊆ σ(N[a]))。

**S10 real sorries 9 → 7 / S16 +1 (14.13(a) pin)**。§8 support theory の Peterfalvi 側は
これで (8.15)/(8.17)/(8.18) 系すべて BG-native obligations に集約。
**次 (loop¹⁰³) = 14.13(a) 本体の正面 build**: Coq 証明 ~90 行、必要部品 =
14.4(d) σ∩π ⊆ β / Cor 12.14 (`cent_der_sigma_uniq` 対応) / 12.1(g) (`tau2_not_beta`) /
Prop 14.2(g) / Thm 14.7(a)(b) / Cor 12.9・12.10(c) / r_p(N) ≤ 1 議論。まず repo 対応物の
棚卸しから (settled findings の教訓: grep してから深さ評価)。
full build 3904 jobs / 1m58s green。

### loop¹⁰³ 準備: 14.13(a) 部品の初期棚卸し (2026-07-03)

- **12.1(g)**: `tau2_prime_mem_sigma_diff_beta` (S12_Lemma1211:390) — τ₂→σ∖β、14.13(a) step
  「π(⟨x⟩) ⊆ τ₂(N) ⊆ σ(M)∖β(M)」の候補。statement 精査要。
- **Cor 12.14**: S12_Corollary1214 に faithful form ported ✓ (:110 と :415 の 2 形)。
- **14.4(d) σ∩π ⊆ β**: `signalizer_structure_of_mem_sigmaSharp` conclusion 内
  (`sigma N ∩ piSet M' ⊆ beta N`, S16:283) ✓ 既取得可。
- **Prop 14.2(g) / Thm 14.7(a)(b)**: theorem 形の直接 port 未発見 (docstring 言及のみ、
  S14_TypePCounting:1022/1882 周辺) — 実体特定が loop¹⁰³ の最初の仕事。
- **type F + τ₂=∅ → Frobenius 化** (pin 結論の ∃U 部): 独自導出要 (~40 行、κ=∅ +
  π-分割で complement の f.p.f. 性; Coq FtypeP 系対応物の grep も)。

## ✅ lane b 完了 (2026-07-03, loop¹⁰³) — BG 14.13(a) 全証明・axiom-clean

`non_disjoint_signalizer_frobenius` (BG Lemma 14.13(a)) を **sorry-free + axiom-clean** で完成
(commit chain 60da6782 → 65ac0c1a、新 leaf `S16_Lemma1413.lean`)。§8 type-I support pin の
最後の 1 本。`#print axioms` = propext/Classical.choice/Quot.sound のみ。

**構成 (4 部品、全 sorry-free)**:
1. **reduction** (60da6782): signalizer neighbour `N`, 素数 `q ∈ σ(N)∩π(M)` (⟹ β(N)) と
   `p = minFac(ord x) ∈ σ(M)∩τ₂(N)`; `N` 非共役 `M` (13.9 ⟹ q∉σ(M)); Q conj into N;
   Cor 12.14 で `ℳ(C(Q))={Nᵍ}`; `p∉β(M)` (12.1(g))。+ `typeF_frobenius_of_tau2_prime_free`
   (type-F + no-τ₂ ⟹ Frobenius over M_σ) + `beta_conj_smul_eq`/`pRank_conj_smul_eq`。
   + P₂ case (σ=β via typeP_structure(g) ⇔ p∈σ∖β 矛盾)。
2. **Part 2 no-τ₂** (6638beb4): `r_{p'}(N)≤1` (π(N)-partition + tau2_not_beta) → Cor 12.9
   (`commutator_decomp_of_tau1_action`) で非共役 rank-1 `[A,Q]`,`C_A(Q)` → cyclic Sylow で
   共役 → 矛盾。新 reusable `exists_conj_smul_eq_of_le_of_card_prime` (cyclic-Sylow で order-p
   部分群は共役)。
3. **Part 1 type-P₁** (65ac0c1a): dual partner `Mstar=Nᵍ` の `Kstar` が κ(Mstar)-Hall かつ
   **σ(M)-Hall** ⟹ `p∈σ(M)∩π(Mstar)` で `p∈κ(Mstar)` (rank≤1) vs `r_p(Mstar)=2` 矛盾。
   新 reusable `kstar_isHall_sigmaM_of_partner` (Coq `Ptype_embedding` の `sMhallKs`; 14.2(f)
   `typeP_sigma_subgroup_le_Msigma` + Hall superset + σ-disjoint `⁅Y,K⁆≤M_σ⊓Mstar_σ=1`)。

**§8 type-I support 系は全完了** ((8.13.a/b/c1c2/c2c4)/(8.14)/(8.15)/(8.17)/(8.18) + 14.13(a))。
`escaping_sigma_disjoint_centralizer` (8.13.c2 core) の 14.13(a) 由来 sorryAx は解消。
残る S10 real sorry 7 本は **type-II / type-P Dade-support obligation** (`typeII_A_sets_TI`
/`typeII_A_sets_normalizer` (8.15 type-II)、`dadeSupportHypotheses_typeP`、`bgTheoremE_cover_data`、
`hall_maxNilpotentNormalHall_and_mainSubgroup`、`typeI_or_typeII_centralizer_unique`、
`escapingCentralizers_control`) = 別クラスタ (0096 carve-out の type-II 側)。次 loop¹⁰⁴ 候補。
full build 3906 jobs green。

## 📋 lane b frontier map (2026-07-03, loop¹⁰³ 終) — §8 type-II 系は BG Theorem B に gated

14.13(a) 完了後の残 S10 type-II sorry 7 本の tractability を精査 (grep-before-depth)。
**3 obligation とも proven でない上流 BG §16 に gated** — 即座の bridge は無い:

- **(8.11) `hall_maxNilpotentNormalHall_and_mainSubgroup`**: M_s=M_σ は全 type で proven
  (`mainSubgroup_eq_Msigma` + `Msigma_isHall`)。M_F 側は **type I/II のみ proven**
  (`maxNilpotentNormalHall_isHall_of_typeI_or_II`, S10_BGInterface:96)。**type III/IV は
  M_F ⊊ M_σ の proper-Hall** で「still-sorry BG §14–§15 structure」に gated
  (S10_BGInterface:90-94 docstring)。→ tau∈{I,II,V} は建てられるが III/IV M_F が残る。
- **(8.12.b) `typeI_or_typeII_centralizer_unique`**: `theoremB_U_and_A_tame` conjunct 4
  (`∀ X≤U, M_σ⊓C(X)≠⊥ ⟹ ℳ(C(X))={M}`, S16_MainResults:690, **sorried** :692) に gated。
- **(8.16) `typeII_A_sets_TI` / `_normalizer`**: `theoremB_U_and_A_tame` conjunct 5
  (`IsTISubset (ASet M U ∖ M_σ) M`, S16:691, **sorried**) に gated。sister の Theorem C(9)
  (`theoremC_paired_structure` A_0∖A) は proven だが A∖M_σ は Theorem B 依存。

**共通の ungated 上流 = BG Theorem B `theoremB_U_and_A_tame`** (S16_MainResults:679, sorried :692)。
5 conjunct: (1) Sylow abelian rank≤2 (**proven** standalone `theoremB_U_sylow_abelian_rank_le_two`),
(2) centralizerGeneratedBySigma abelian, (3) U0 witness, (4) centralizer uniqueness [=8.12.b gate],
(5) ASet TI [=8.16 gate]。`theoremII_tame_embedding` も transitively sorryAx (Theorem B 消費)。
Theorem B(4)/(5) = BG §16 tame-embedding の核 — Theorem E (M̃ normedTI) / Theorem II を要す
deep port (type-I 版 `typeI_centralizer_le_and_unique` は proven なので B(4) は部分的に射程内か)。

**loop¹⁰⁴ = policy「gated なら ungated 上流 (Theorem B) に降りて実証明」に従い BG Theorem B
`theoremB_U_and_A_tame` conjunct 4/5 を正面 build** (conjunct 1 は proven、Theorem E の M̃
machinery `conjClassSet_Mtilde_disjoint` は proven ゆえ conjunct 5 の TI は射程内の可能性)。

## ✅ lane b 完了 (2026-07-03, loop¹⁰⁴) — BG Theorem B(4)(5) 全証明 + Theorem B 全 5 conjunct 完成・axiom-clean

commit 94a34018 (3 files, +332/-25)。§8 type-II support クラスタの共通上流 =
BG Theorem B(4)(5) を正面 build。**frontier map (loop¹⁰³) の「Theorem E/II deep port」推測は
grep-before-depth で覆り、実際は Lemma 15.1(c) からの genuine assembly だった**
([[verify-port-state-by-number-not-coq-name]] の教訓再確認)。

**新規 (S16_MainResults、全 axiom-clean [propext, Classical.choice, Quot.sound])**:
1. **`theoremB_A_minus_Msigma_isTISubset` (B(5)、mmd L4373)**: `IsTISubset (A(M)∖M_σ) M`。
   a∈A(M)∖M_σ の (κ∪σ)'-part w=piPart(κ∪σ)ᶜ a に `𝓜(C_G(w))={M}` (下記一般形) →
   piPart 共役同変 (`piPart_conj`) + `centralizer_pointwise_smul` + coatom 共役
   (`isCoatom_pointwise_smul`) + `mem_normalizer_of_conj_smul_eq_self` + N_G(M)=M で g∈M。
   w≠1 は `mem_U_sup_Msigma_iff_isPiElement_kappa_compl` (κ'-ness) + `mem_Msigma_iff_isPiElement_sigma`。
2. **`uniqueMaximal_of_kappaSigmaCompl_element` (Lemma 15.1(c) 一般形)**: (κ∪σ)'-元 y∈M で
   C_{M_σ}(y)≠1 → `𝓜(C_G(y))={M}`。`hall_D`/`hall_C` で ⟨y⟩ を U に共役 →
   `typeP_hall_small_subgroup_cyclic_tau2` (=B(4)、S14 に proven 済) → τ∈M で共役戻し。
   Pf 8.12.b (`typeI_centralizer_le_and_unique`) の type-independent core。

**`theoremB_U_and_A_tame` faithful 化 + 全 5 conjunct assembled で完全証明**:
- signature に hKM/hUM/hK 追加 (BG setup M=KUM_σ)、conjunct 1 を `p.Prime` 制限
  (旧 `∀ p:ℕ` 版は非可換 {q,r}-group で **偽**だった latent unsoundness を是正)。
- (1) `theoremB_U_sylow_abelian_rank_le_two` / (2) `typeP_centralizerGeneratedBySigma_isMulCommutative`
  (15.1d) / (3) `typeP_hall_frobenius_factor` (15.1e) + Frobenius fpf
  (`centralizer_inf_kernel_eq_bot_of_not_mem`) 変換 / (4) `typeP_hall_small_subgroup_cyclic_tau2`
  (15.1c) / (5) `theoremB_A_minus_Msigma_isTISubset`。

**消費者 un-gate (Theorem B sorry cite → sorry-free cite)**:
- S16 `theoremII_tame_embedding{,_of_inputs}` + `mem_sigmaSharp_of_mem_aSet_of_escape` (B5 ×3
  → `theoremB_A_minus_Msigma_isTISubset` 直接 cite)。
- S10 `typeI_centralizer_le_and_unique` (B4 → `typeP_hall_small_subgroup_cyclic_tau2` 直接 cite)。

toolkit: `isCoatom_pointwise_smul` (MaximalSubgroupTypeConj、downstream private の共通化)。
full build 3906 jobs green / 2m7s。

### 次 frontier (loop¹⁰⁵) — §8 type-II support pins が un-gate されて tractable に

`theoremII_tame_embedding` (Theorem II conjunct 1) と `uniqueMaximal_of_kappaSigmaCompl_element`
が axiom-clean になったので、S10 の残 type-II pin (bare sorry) が正面 build 可能に:
- **`typeI_or_typeII_centralizer_unique` (S10:398, 8.12.b I+II 形)**: X⊆U#, M_F⊓C(X)≠⊥ →
  C(X)≤M ∧ IsUniquelyMaximal(C(X))。type II で M_F=M_σ ゆえ `uniqueMaximal_of_kappaSigmaCompl_element`
  を set→element 還元で適用 (X の各元は (κ∪σ)'-元)。
- **`typeII_A_sets_TI` (S10:492, 8.16)** / **`typeII_A_sets_normalizer` (S10:502)**: A_II sets の TI 性、
  `theoremB_A_minus_Msigma_isTISubset` を type-II M に適用。

### loop¹⁰⁵ 精査 (2026-07-03) — (8.12.b) `typeI_or_typeII_centralizer_unique` は **false-as-stated** + exact fix 判明

Pf (8.12.b) 原文 (04.10:129): 「非空 X⊆**U#** (U は complement: type I で M=H⋊U、type II で
[M,M]=H⋊U) で C_H(X)≠1 → M は C_G(X) を含む唯一の maximal」。証明 = [BG] §16 Theorem B(4)。

**Lean `typeI_or_typeII_centralizer_unique` (S10:398) は false-as-stated**:
- 仮説が `hUle : U ≤ M` (任意) で、caller S14:4366 は **U=M, X={x}⊆M#** を渡す。
- 反例: escaping σ-元 x∈M_σ# は `M_σ⊓C(x)⊇⟨x⟩≠⊥` (仮説満たす) だが `C(x)⊄M` (escaping の定義)
  → 結論 `C(X)≤M` を破る。実 caller の x は complement 由来の (κ∪σ)'-元なので使用箇所は健全だが、
  ∀-statement が偽インスタンスを含む (theoremB conjunct 1 と同種の scaffold soundness issue)。

**exact fix (tractable、B(4) が今 available)**: `hUle : U ≤ M` を
`hU : Ch03.IsHallSubgroup ((κ∪σ)ᶜ) (U.subgroupOf M)` に faithful 化。証明 =
`⟨X⟩ ≤ U` (X⊆U# 非空 → ⟨X⟩≠⊥)、`C_G(X)=C_G(⟨X⟩)`、`C_{M_σ}(⟨X⟩)≠⊥` → **Theorem B(4)**
(`typeP_hall_small_subgroup_cyclic_tau2` / `theoremB_U_and_A_tame` conjunct 4) で 𝓜(C(⟨X⟩))={M}
→ `IsUniquelyMaximal(C(X))` + `C(X)≤M`。type I/II 共に B(4) は type-agnostic ゆえ両対応。

**cross-lane**: caller 更新が要る (S10 restate = 自、S14 caller = 自 `exists_sigmaKappaCompl_hall_ge_P0`
で Hall 供給、**S11 caller (lane a) = `isHall_kappaSigmaCompl_of_isTypeP2_complement`
(FeitThompson.lean、lane a) で data.U を (κ∪σ)'-Hall 化**)。enablers 両方存在
(`typeF_complement_isHall_kappa_sigma_compl` type I / 上記 type II)。

**(8.16) `typeII_A_sets_TI` (S10:492)**: `IsTISubset (typePA0/typePA/A1) M`。typePA↔BG ASet の
encoding bridge + `theoremB_A_minus_Msigma_isTISubset` (A(M)∖M_σ) / Theorem C(9) 適用。
Pf (8.12.c) = A(M)−A_1(M) TI = Theorem B(5) の Pf 名。次 loop で bridge を建てる。

## 🚀 lane b 進捗 (2026-07-03, loop¹⁰⁵) — (8.12.b) faithful 版 `_hall` を axiom-clean で landing (S14 un-gate)

loop¹⁰⁴ の Theorem B(4) を使い、(8.12.b) の faithful 版を実証明。上記 false-as-stated finding を
**新 theorem `typeI_or_typeII_centralizer_unique_hall`** (S10、axiom-clean) として landing:
- signature = `hUM : U ≤ M` + `hU : (κ∪σ)ᶜ-Hall (U.subgroupOf M)`。証明 = `⟨X⟩ ≤ U` に
  `typeP_hall_small_subgroup_cyclic_tau2` (B(4)) 直接適用、`centralizer_closure` + `M_F=M_σ` +
  `IsUniquelyMaximal.of_unique_maximal`。conjugation 不要 (X⊆U# ゆえ ⟨X⟩≤U)。
- **S14 caller `centralizer_control_of_CKx` を `_hall` に migrate**: `exists_sigmaKappaCompl_hall_ge_P0`
  で (κ∪σ)ᶜ-Hall complement U₀⊇P₀∋x を供給 (旧 U=M は非-Hall で偽インスタンスだった)。type-I support
  path が Theorem B の sorry gate から解放。
- 旧 `typeI_or_typeII_centralizer_unique` (false-as-stated, sorry) は S11 caller
  (`typeII_centralizer_U_eq_bot`) のため残置 + deprecated 注記。

**S11 migration の blocker (cross-lane infra、次 loop 候補)**: S11 caller は `data.U` (TypePData
complement) を (κ∪σ)ᶜ-Hall として供給する必要があるが、その witness
`isHall_kappaSigmaCompl_of_isTypeP2_complement` + 補助 `isHallSubgroup_of_card_eq` /
`card_mul_card_of_complement_normal` が **downstream の `FeitThompson.lean` (lane a) に誤配置**
(全て §11 上流の依存しか使わない generic 補題)。→ 3 補題を上流 (card 2 本 = GroupTheory base、
Hall 本体 = S10_BGInterface) へ relocate すれば S11 も `_hall` に migrate 可能。**hub 調整 issue 要**
(FeitThompson は lane a 所有、relocate は cross-lane)。sup/inf witness は既存
(`TypePData.derivedInG_eq_fitting_sup_U` + 要新 `fitting_inf_U_eq_bot`) + `isTypeII_iff_isTypeP2`。

## 📋 loop¹⁰⁶ (2026-07-03) — §8 type-II support cluster の consumer 監査 + vestigial 偽 pin 発見

loop¹⁰⁵ の (8.12.b) を受け、残 S10 §8 type-II pins の consumer 状況 + faithfulness を監査:

**vestigial (0 consumer) + overstated/false-as-stated** — proven せず ⚠ 注記のみ (commit 済):
- **`typeII_A_sets_TI` / `typeII_A_sets_normalizer` (8.16)**: full `A(M)=(M')#` / `A_1(M)=M_σ#` の
  TI を主張するが、Pf (8.10/8.12.c, mmd 04.10 L119/L131) は **`A(M)−A_1(M)` のみ TI** (=B(5)、proven)。
  M_σ は tamely imbedded (Theorem II)、M_σ∩M_σ^g cyclic (Theorem D(2)) ゆえ M_σ# は TI でない。
  → retire or restate to `A(M)−A_1(M)`。docstring に ⚠ 注記。
- **`escapingCentralizers_control` (8.13.b)**: 0 consumer だが overstatement ではない (tame-embedding
  の escaping control、Theorem II/D(4) 内容)。Theorem II で proven 可能な見込み — 注記せず残置。

**real (consumed) — 次 frontier 候補 (各々個別に deep)**:
- `hall_maxNilpotentNormalHall_and_mainSubgroup` (S14×4): type I/II proven、**type III/IV は
  M_F⊊M_σ proper-Hall で BG §14-15 に gated** (loop¹⁰³)。
- `dadeSupportHypotheses_typeP` (S12×3): Dade support hypotheses、type-P。
- `bgTheoremE_cover_data` (×9): Theorem E cover。

**教訓**: §8 type-II support scaffold は TI/uniqueness を過剰主張しがち (8.12.b・8.16 とも false-as-stated、
15.7(c) overstatement と同パターン [[ft-settled-findings]])。faithful 核 (A(M)−A_1(M) TI = B(5)、
tame embedding = Theorem II) は既に proven。consumed pin のみ実 frontier、うち III/IV は BG §14-15 gated。

## 📋 loop¹⁰⁷ (2026-07-03) — consumed §8 type-II pin の深さ評価: 残りは type-P Dade engine (deep 新機構)

`dadeSupportHypotheses_typeP` (S10:1542, S12×3 consumer) を精査。type-I 版
`dadeSupportHypotheses_typeI` は proven だが、engine `dadeSupportHypothesisData_of_subset`
(S10:1415) は **type-I 専用** (`data : TypeIData`、base = `typeIA`、依存 =
`escaping_typeIA_signalizer_structure` / `typeIA_isConj_conj_in_M` (8.13.a) /
`ftSupportKernel_conj_smul` — 全て私の loop⁹⁹ type-I (8.15) 機構)。

**type-P 版に要る新機構 (de-risked build plan、次 focused session)**:
- **`dadeSupportHypothesisData_of_subset_typeP`** (engine、gated-endpoint skeleton 可): assembly は
  type-I をミラー、base = `typePA M data = (M')#`。isolate すべき type-P pins:
  1. **`escaping_typePA_signalizer_structure`** — (M')# escaping 点の signalizer 構造 (type-P、
     K≠1 の σ-support geometry; type-I の類推だが K-structure で異なる)。
  2. **`typePA_isConj_conj_in_M`** — (8.13.a type-P): (M')# 点の G-共役は M-共役。
  3. **`ftSupportKernel_conj_smul`** (type-P equivariance)。
- conj-invariance (`typePA_conj_mem` / `typePA0_conj_mem` / `A1_typeII_conj_mem`) は tractable
  (M' ⊴ M / M_σ ⊴ M の M-共役不変性)。
- `dadeSupportHypotheses_typeP` = engine を typePA0 (⊇ V^M 部は conjClassSetIn M ゆえ M-不変) /
  typePA / A1(=M_σ#⊆(M')#) に適用。

**残 consumed pin の深さ**: `bgTheoremE_cover_data` (×9) = Theorem E cover (deep);
`hall_maxNilpotentNormalHall_and_mainSubgroup` III/IV = BG §14-15 gated (loop¹⁰³)。
→ §8 type-II の tractable TI 作業 (8.12.b faithful + vestigial 監査) は完了; 残りは type-P Dade
geometry (新機構) か BG §14-15 gate。次 session は type-P engine を focused に build するのが妥当。

## 📋 loop¹⁰⁸/¹⁰⁹ (2026-07-03) — type-P Dade engine 前提整備 + Pf/BG A(M) 不一致の発見

**loop¹⁰⁸ landing** (commit 8c85dcac): type-P Dade engine の conj-invariance 前提を build。
`sharpSubgroup_conj_mem` (general) + `A1_conj_mem` (全 tau、旧 `A1_typeI_conj_mem` を dedup 置換) +
`typePA_conj_mem`。full build green。

**loop¹⁰⁹ 発見 (検証済み、engine build 前に要 reconciliation)**: type-P の A(M) 定義が Pf と BG で**別物**:
- **Pf (8.10, mmd 04.10 L117)**: type-P `A(M) = ⋃_{x∈M#} C_{M'}(x)# = (M')#` (Lean `typePA`、
  `typePA_eq_sharpSubgroup_derivedInG` で確認; x=y で C_{M'}(y)∋y ゆえ全 M'# を被覆)。
- **BG (§16)**: `A(M) = ASet = hatMsigma ∩ (U⊔M_σ) = hatMsigma ∩ M'` (C_{M_σ}≠1 を要求)。
- **不一致**: type II で C_H(U)=1 (`typeII_centralizer_U_eq_bot`) ゆえ U-元 a∈U#⊆(M')# は
  C_{M_σ}(a)=1 → a∉hatMsigma → **a∈typePA だが a∉ASet**。よって typePA=(M')# ⊋ ASet。

**含意**: Pf (8.12.c) 「A(M)−A_1(M) TI」は Pf の A(M)=(M')# ゆえ **(M')#−M_σ# TI** を主張し、
私の B(5) (`theoremB_A_minus_Msigma_isTISubset` = BG ASet−M_σ TI) と**別主張**。Pf ref は [BG] Thm B
なので両者は整合するはずだが、その alignment (Pf A(M)−A_1(M) = BG ASet−M_σ、i.e. ∀y∈M'∖M_σ,
C_{M_σ}(y)≠1) は type-P structure の非自明な事実で、要 careful 証明。→ **type-P Dade engine は
Pf/BG A(M) 整合 + escaping_typePA_signalizer_structure を要する deep piece、fresh focused session 向け**。

**§8 type-II の tractable 作業は枯渇** (8.12.b faithful + vestigial 監査 + conj 前提)。残 pin は全て
deep (type-P Dade / §12 witness / §8 III/IV BG§14-15 gate)。次は別クラスタ (S07/S08/S09) の tractable
target を探すか、type-P engine を fresh session で。

## 📋 loop¹¹⁰ (2026-07-03) — レーン b tractable 作業の枯渇確認 (S07/S08 完成、S09 は 7.9 gated)

§8 type-II 枯渇後、レーン b 別クラスタを survey:
- **S07_Coherence* / S08_* (PGroupReduction + CaseB + Coherence 全 26 files): 全 sorry-free (完成)**。
- **S09_CertificateDischarge: sorry-free**。
- **S09_NonexistenceCertain: 残 1 sorry** = `card_G0_lower_bound` (Pf 7.10, issue 0044) の
  `CharacterEstimateData` assembly。**(7.9) two-family 非直交 (未証明 interface `Hypothesis79`、
  proof は follow-on、深い char theory ≈ 11.8 系) に gated** → 独立に tractable でない。

**結論**: レーン b の tractable な on-path 実装作業は枯渇。残る全 frontier は deep か gated:
- §8 type-II: type-P Dade engine (Pf/BG A(M) reconciliation + escaping structure、fresh session)、
  §12 witness pins (§8-§11 type-analysis)、III/IV (BG §14-15 gate)。
- S09 card_G0: (7.9)/(11.8) char theory (lane a 系) に gated。
→ 次は (a) 上記 deep pin を fresh focused session で正面 build、または (b) 他レーンの 11.8/7.9 進捗待ち。

## 🚀 lane b 進捗 (2026-07-04, loop¹¹¹) — Pf (12.4) `constituent_diff_support_subset_nonescaping` 実証明 + [Is] 6.2 Clifford 制限 mult-one 版を構築

loop¹¹⁰ の「tractable 枯渇」判定を再検証したところ、**S14_MaximalI (lane b 主所有、§12 Dade tower)
の 13 sorry が loop¹¹⁰ の survey (S07/S08/S09 のみ) で見落とされていた**。うち Pf (12.4) の §8 support
obligation を実証明化 (commit 6e5e3275、S14 13→12 sorry)。

**核 = 新 helper `restrict_eq_of_mem_constituents`** = Clifford's theorem [Is] 6.2 の
**multiplicity-one 版** (S01_Introduction が「Clifford [Is] 6.5 不在」と記録していた foundational
char theory の必要部分): χ = Ind_K^L θ (K=(L_F).subgroupOf L ⊴ L) の 2 constituent φ₁,φ₂ は
`Res_K φ₁ = Res_K φ₂`。full inertia 機構を回避し inner-product level で証明:
- ⟨Res_K φᵢ, ψ⟩ = ⟨φᵢ, Ind_K ψ⟩ (Frobenius); ψ~θ で 1 (mult-one decomp + `induce_conjBy_eq`)、
  ψ≁θ で 0 (既存 `restrictionConstituentsSingleOrbit_of_isIrreducible`); Fourier で確定。
- 既存 char infra が想定より充実 (`CliffordSingleOrbit.lean` 等) だったのが決め手。

**application (12.4)**: supp(φ₁−φ₂)⊆A(L)∪{1} (carrier) + degree-cancel → ⊆A(L); escaping 点は
A₁=H^# ((8.13.b) `escaping_typeIA_mem_A1`) で Res 一致し消える。(12.4) coset chain
(`constituent_diff_tau_eq_induce`/`Sset_coeff_equal`/`Sset_offKernel_vanishes_off_H`/
`orthogonal_character_constant_on_coset`) に hG thread (上位は既に _hG)。full build 3910 green。

**残 S14 frontier の深さ評価 (次 iter 向け)**:
- **(8.2.c) `typeI_induced_char_constituents`** (S14 最上流 sorry、general 版): 非-Frobenius N の
  (12.3)/(12.4) が要する (on-path)。だが mult-free 分解は type-F inertia (I_L(θ) 解析) を要し
  自明でない = deep (8.2.c)。Frobenius 版は proven。
- **(12.5) `rho_constant_on_H_minus_Hprime`**: **現状 consumer 0** + 生 psi の H−H' 上定数性は
  ρ-reduction 込みでないと偽の可能性 (Pf は ψ^ρ を主張) → faithful 化要検討、blind に埋めない。
- **(12.10)/(12.11)/(12.12)** = Cluster A (§8-§11 type-analysis) gated (既記載)。
- **(12.14)/(12.15)/(12.16)** = Dade 計算 + witness assembly (deep)。
- **helper `restrict_eq_of_mem_constituents` は reusable** — 将来 (8.2.c) や他の Res-of-Ind に流用可。

## loop¹⁹¹ (2026-07-04) — 🎉 (12.5) 完全証明で DpsiH クラスタ完済 → frontier = deep type-P engine / gated 群

**(12.5) `rho_constant_on_H_minus_Hprime` 完全証明** (sorry-free、標準3 axiom、full build green 3915 jobs)。
loop¹¹¹ が tractable と見出した (12.4)/(12.5) DpsiH クラスタは**完済**。generic 機構
(DpsiH core / block partition / 等次数・等mult / ψ存在) + S14 wiring を landing。

**frontier 再検証 (S10/S14/S09 横断)** — loop¹¹⁰ の「枯渇」判定は今度は正しい (tractable 例外 DpsiH を
完済したため):
- **S14**: (8.2.c) は既 proven。残 = `witness_L_isTypeI`/`witness_L_complement_isZGroup` (Cluster A、
  deep §8-§11 type-analysis、gated) / **`rhoM_integer_values` (12.15) は opaque `rhoMFormula` Prop
  free field ⟹ scaffold** (一般 dade で証明不能・honest でない、要 DadeNotation de-scaffold 設計判断) /
  (12.14/16)+counterexample assembly (deep Dade)。
- **S10**: `dadeSupportHypotheses_typeP` = **type-P Dade engine** (Pf (M')# vs BG ASet reconciliation、
  loop¹⁰⁷ de-risked plan + loop¹⁰⁹ reconciliation 論点済) = 最深 lane-b-owned on-path pin。
  他 (hall/centralizer_unique/escapingCentralizers/bgTheoremE_cover) は §8/§4 structure。
- **S09**: `card_G0_lower_bound` は (7.9)/(11.8) char theory (lane a 系) に gated。

**次 = type-P Dade engine `dadeSupportHypotheses_typeP` を正面 build** (feedback-no-avoiding-hard-parts:
deep でも engage)。loop¹⁰⁷ de-risked plan に従う。**設計判断 flag**: (12.15) の DadeNotation opaque
Prop (rhoFormula/rhoMFormula/e_eq_index) de-scaffold は §12 endgame の honest 化に要 — hub/ユーザー裁定歓迎
(type-P engine を優先し、(12.15) は後回し)。

## loop¹⁹² (2026-07-04) — type-P engine P1 完済確認 / P2 は deep BG§14-15 gated — 全 lane-b frontier 精査完了

`dadeSupportHypotheses_typeP` (S10:2466) 精査: **P1 case は完済** (A(M)=M_σ#=A_1、
`typePA_eq_sigmaSharp_of_isTypeP1` + `dadeSupportHypothesisData_typePA0_of_isTypeP1`)。
**残 = type-P2 の 2 sorry**:
- **typePA P2** (S10:2509): X=(M')# ⊋ M_σ# ゆえ `dadeSupportHypothesisData_of_subset_sigmaSharp`
  (X⊆M_σ# 要求) は使えない。type-P escaping engine + **`escaping_typePA_mem_A1`** (type-P 8.13.b) +
  **`escaping_typePA_signalizer_structure`** (type-P σ-geometry) が要る。loop¹⁰⁹ 反例 (M'∖M_σ の
  U-元は C_{M_σ}=1 で A_1 に落ちない) ゆえ type-I の clean analogue でない = deep BG§14-15 type-P2 geometry。
- **typePA0 P2** (S10:2500): V^M exceptional support geometry (type-P2)。

**全 lane-b frontier 精査完了 (S07/S08/S09/S10/S14、engine signature まで確認、loop¹¹⁰ の推測的枯渇宣言と違い
tractable 例外 DpsiH/(12.5) を完済済)**:
| pin | 状態 |
|---|---|
| §7/§8 coherence (S07/S08 26 files) | ✅ done |
| DpsiH/(12.4)/(12.5) (S14) | ✅ **done (今 session)** |
| (8.2.c) typeI_induced_char_constituents | ✅ done |
| type-P engine P1 | ✅ done |
| type-P engine **P2** | ⛔ deep BG§14-15 type-P2 geometry |
| (12.10) witness_L_isTypeI/isZGroup | ⛔ Cluster A §8-§11 type-analysis gated |
| (12.15) rhoM_integer_values | ⚠ scaffold (DadeNotation opaque Prop、de-scaffold 設計判断) |
| S09 card_G0 | ⛔ (7.9)/(11.8) char theory gated (lane a 系) |
| §8 III/IV, bgTheoremE_cover | ⛔ BG §14-15 gated |

**結論**: lane b の cleanly-tractable, ungated, honest な char/support work は (12.5) 完済で枯渇。
残る全 pin は (a) deep BG§14-15 type-P2/III-IV geometry (other-cluster)、(b) §8-§11 type-analysis gated、
(c) (7.9)/(11.8) char (lane a) gated、(d) DadeNotation de-scaffold 設計判断。
→ loop cadence を heartbeat (20min) に落とし、user 方向指示 / 他レーン (BG§14-15, 7.9/11.8) unblock を待つ。

## ✅ HUB/ユーザー裁定 (2026-07-04, loop¹⁹² frontier 枯渇への回答): b を BG§14-15 type-P2 geometry へ再配分

lane b の loop¹⁹² 精査「(12.5) 完済で ungated tractable work 枯渇、残 type-P engine P2 は deep BG§14-15
type-P2 geometry に gated」に対し、**ユーザー裁定 = b は自 engine P2 を gate している BG§14-15 type-P2
geometry を正面 build する** (heartbeat 待機でなく、深いゲートを foundation 構築で開ける)。

**具体 target** (b の loop¹⁹² 分析より):
- **`escaping_typePA_mem_A1`** (type-P 8.13.b) — type-P escaping 元が A_1 に属する。
- **`escaping_typePA_signalizer_structure`** (type-P σ-geometry) — type-P2 の signalizer 構造。
- これらが `dadeSupportHypotheses_typeP` の **typePA P2** (S10:2509) / **typePA0 P2** (S10:2500, V^M
  exceptional support) を un-gate する。

**運用**:
- BG§14-15 の type-P2 geometry lemma は **BG/** (shared foundation) に build 可** (Theorem B(4)(5) 完成の
  前例と同型: b が BG を extend、ユーザー承認済)。**BG は "完了・共有凍結" だが type-P2 geometry は未形式化ゆえ
  additive extension は許容** (既存 BG 宣言の statement 改変は要 flag)。原文は BG §14-15 + Gorenstein 行間
  (coq/theories/BGsection14.v/15.v コメント併読)。
- type-P2 の反例 (loop¹⁰⁹: M'∖M_σ の U-元は C_{M_σ}=1 で A_1 に落ちない) を踏まえ、type-I の clean analogue
  でない deep geometry を honest に build (feedback-no-avoiding-hard-parts)。
- 完成で type-P engine P2 → `dadeSupportHypotheses_typeP` 全 field discharge → §12 Dade tower endgame へ。
- **(12.15) DadeNotation de-scaffold は今回は保留** (type-P engine P2 を優先; 必要になれば別途裁定)。
- b は着手前に本裁定 + loop¹⁰⁷ de-risked plan + loop¹⁰⁹ reconciliation を再読。

**⚠ 下記 loop¹⁹³ で refine**: BG §14 σ-theory foundation は issue 9000 で **別レーンが claim 済・能動 build 中**
と b が判明 → b は σ-theory foundation を**重複 build しない** (claim-before-build)。本裁定の「BG§14-15 type-P2
geometry を build」は、**b 所有部分 = type-P2 の CLOSE (`escaping_typePA_mem_A1` + S10 engine mirror、b の
carve-out)** に読み替え、σ-foundation が merge-main で揃い次第 engage する (それまで heartbeat)。σ-foundation
自体は 9000 claim レーンが build。⟹ hub は BG §14 の σ-theory build が停滞していないか (9000 レーンの生存) を注視。

## loop¹⁹³ (2026-07-04, heartbeat) — type-P2 obstruction を精密特定: typePA の K-part は BG A0Set escape lemma 範囲外

heartbeat 起動、main に他レーン進捗無し (gate 未解除)。type-P2 の deep 度を精密検証:
- **BG escape lemma `mem_sigmaSharp_of_mem_aSet_of_escape` (S16) は type-general** (K=kappa-Hall 引数)、
  escaping 点 (of ASet or A0Set) → M_σ#。→ 機構は存在。
- **しかし `A0Set M K = hatMsigma M \ conjClassSet(sharpSubgroup K)` は K-part を除外**。
  一方 **`typePA = (M')# = sharpSubgroup(derivedInG M)` は K-part を含む** (K ⊆ M')。
  ⟹ typePA の K-元 (kappa#) は A0Set にも ASet にも入らず、escape lemma の射程外。
- **∴ type-P2 typePA case は BG §14-15 type-P2 の新 K-structure geometry (V^M / kappa-action /
  K# の signalizer) を要する** — type-I の clean mirror では**閉じない** (loop¹⁰⁹ の
  「別物」を set-level で確定: (M')# の K-part が A0Set 除外部)。

**結論 (loop¹⁰⁹ を精密化)**: type-P2 は BG §14-15「III/IV gate」領域の新 geometry を要し、lane-b 単独
build 圏外 (BG Ch4 cluster 領域、claim-before-build/coordination 要)。→ heartbeat 継続、BG§14-15 進捗 /
ユーザー方向指示待ち。lane-b の char/support tractable 作業は (12.5) 完済で確定的に枯渇。

**⟳ type-P2 gate は LIVE (別レーンが BG §14 σ-theory を能動 build 中)**: `git log -- BG/Ch4/S14/S15` に
非常に最近の `feat(BG §14)` 群 (`mem_U_sup_Msigma_iff_isPiElement_kappa_compl` /
`mem_Msigma_iff_isPiElement_sigma` / `index_U_sup_Msigma_primeFactors_subset_kappa` / Cor 14.10
σ-length ≤ 2 / fix-W type-P Ẑ ...) = type-P2 K-part geometry の前提。issue 9000
(sigma-theory-typep-galois-foundation) で claim 済。→ **type-P2 は idle-gate でなく別レーン能動作業に
gated**。claim-before-build ゆえ lane-b は BG §14 を重複 build しない。heartbeat が正: merge-main で
BG §14 進捗を拾い、σ-foundation 揃い次第 type-P2 close (escaping_typePA_mem_A1 + engine mirror) を engage。

## 🔎 HUB 明確化 (2026-07-04, loop¹⁹³ の待機前提を訂正): σ-foundation は in-main、b は今 engage せよ

hub 検証: b の loop¹⁹³「別レーンが BG §14 σ-theory を能動 build 中ゆえ heartbeat 待機」の前提は**不正確**。
- b が参照する σ-theory 補題 (`mem_U_sup_Msigma_iff_isPiElement_kappa_compl` / `mem_Msigma_iff_isPiElement_sigma` /
  `index_U_sup_Msigma_primeFactors_subset_kappa` 等) は**既に main の `BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean`
  に存在** (以前の σ-theory build で landing 済)。
- **現在 BG §14 σ-theory を能動 build しているレーンは無い** (全レーン `main..lane`=0; issue 9000 は lane a 承継だが
  a は §7 S09 に集中中)。⟹ b が「σ-foundation 揃うのを待つ」= 進行していない build を待つことになる。
- ⟹ **ユーザー裁定どおり b は今 engage せよ** (heartbeat 待機でなく): 既存 σ-foundation を cite しつつ、type-P2 の
  K-structure geometry (typePA K-part = A0Set 除外部の新 geometry: V^M / kappa-action / K# signalizer +
  `escaping_typePA_mem_A1` (8.13.b) + engine mirror) を **shared BG-foundation / S10 carve-out で正面 build**。
  追加で要る σ-lemma (Cor 14.10 σ-length≤2 等が未 landing なら) も同じく shared BG に additive build (Theorem B 前例)。
- b の loop¹⁹³ 技術分析 (typePA K-part が escape lemma 射程外 = 新 geometry 要) は**正しい**; 訂正点は「別レーンが
  それを build 中」の部分のみ (実際は誰も build しておらず b が担当)。

## ✅ lane b 解決 (2026-07-04, loop¹⁹⁴) — type-P2 は phantom だった: mmd OCR 誤りで typePA over-claim (→ issue 9008)

hub 明確化「b は今 type-P2 K-geometry を engage せよ」に従い正面から engage した結果、**追うべき deep
geometry は存在しなかった**ことが判明。原因は **Peterfalvi (8.10) の mmd 抽出 OCR 誤り**（詳細 = **issue 9008**）:

- **PDF 確認**: 本文は `A(M) = ⋃_{x∈M_s#} C_{M'}(x)#`（core `M_s#=M_σ#` 上の union）。`.mmd:117` が
  添字 `s` を落とし `⋃_{x∈M#}` に化け → Lean `typePA` が `(M')#` と定義されていた。
- **P1 では一致** (`M_σ=M'`) だが **P2 (type II, `M_σ=M_F⊊M'`) で乖離**: 正しい A(M) は Frobenius 補元
  `U#`（`C_{M_σ}=1`）を除外するが `(M')#` は含む。U# は escaping し得るゆえ `DadeSupportHypothesisData M
  (typePA=(M')#)` は P2 で **false-as-stated**（loop¹⁹³ の「typePA K-part が escape lemma 射程外」は
  「新 geometry 要」でなく「statement が偽」の徴候だった）。
- **consumer 0**: `dadeSupportHypotheses_typeP` は live caller 無し、唯一の intent consumer
  `S12.Hypothesis.dadeData` は III/IV/V=P1 限定、type-II Dade は `Section16CharacterData.A0S`（off-path
  vestigial）。∴ P2 typePA0/typePA Dade を要する on-path consumer は無い。

**landing (commit 本 tick)**: `dadeSupportHypotheses_typeP` に `hP1 : IsTypeP1 M` を追加し P2 sorry 2 本削除
（Option B、S10 のみ・cross-lane 破壊なし・full build 3916 green）。typePA docstring に P1/P2 caveat 明記。
**この issue の Cluster A/B gate map は P1 側は解決、P2 側は phantom として棄却**。type-P2 の「BG§14-15 新
geometry build」指示は不要（構築対象が偽だった）。→ **lane-b char/support frontier は確定的に枯渇**。次配分は
9008「hub への確認事項」参照。

## ✅ 2026-07-04 (lane b): Cluster A gate map が STALE と判明 → §12 (12.10)-(12.12) chain を実証明化
本 issue の Cluster A「§8-§11 は grep 不在ゆえ (12.10) witness path は gated」は **07-02 時点で stale**。
その後 §8-§11 の多くが形式化済 (`no_typeV_maximal` S12:3742・`typeI_or_typeII_centralizer_unique` S10:407・
`typeII_centralizer_U_eq_bot` S11:530 等)。cite-and-proceed (available cite + 欠け分を sound sorried pin) で
**§12 の (12.10)/(12.11)/(12.12)/(12.10.B) 全 4 obligation を body-sorry-free に実証明** (commits 3fe1980a
`witness_L_isTypeI` / 0282f2cb 残 3)。
- **isolate された §8-§11 pin (6 本、= 真の残 upstream obligation、Cluster A の実体)**:
  `typeII_centralizer_le_of_mem_mainSubgroup` (8.16)・`typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup`
  (11.9.c+11.6+9.7.b+8.6.a)・`witness_L_sylow_cyclic_of_dvd_complement` (8.3/12.8 minimality)・
  `intersection_complements_K` (12.11.1, 8.13.c1)・`intersection_le_kernel` (12.11.2, 8.1.b/c+9.1+12.10)・
  `exists_center_omega1_elemAbelian_fpf_of_witness` (12.12 T-package + 12.11 refinement)。全 witness-tied で
  sound-as-stated (§8-§11 が clean 形式化されたら discharge/relocate 可)。
- ⟹ **Cluster A は「§12 witness path 全体 gated」でなく「6 個の precise §8-§11 pin に isolate 済」に更新**。
  §12 の構造 logic は real。**教訓: gate map issue は日付を見て疑い、上流を今 grep + cite-sorried を適用**。
