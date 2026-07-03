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
- [ ] **`dadeSupport_disjoint_of_nonconjugate`** (§10、最後の Cluster B piece): M̃ 機構が S14 から到達不可
  (0 uses)。relocate to S10 (hub 要調整) か S14 import 追加 (巨大 rebuild) か lane a 所有化。→ (12.16) 閉じる。
- [ ] Cluster A ((12.10) type-analysis) は §8-§11 の大きな multi-theorem effort。§-owning lane に割当?

## 完了条件

hub が裁定: (a) β が `support_mutual_exclusion` (§10, policy A/B で cross-lane) を pick up、または
(b) §8-§11 structural (8.16/8.6.a/9.7.b/10.10/11.x) を §-owning lane に割当。
(12.6) coherence deliverable はどちらでも完了済; これは §12 *下流*の話。

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

**3. リマインド**: (a) 9001 裁定の **(6.5.c) coherence producer の 9000 番台 claim が未起票** —
build 着手前に必ず `bin/new-issue --base 9000` で起票 (policy 6)。(b) b は main に 17 commits
遅れ (最終 merge 44ccb169; 本 tick 合流でさらに進む) — **次 leaf 着手前に `git merge main`**
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
