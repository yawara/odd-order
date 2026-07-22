# lean-eval への proof 提出 — 単一正本

> **この note が lean-eval 関連の唯一の正本** (2026-07-22 統合)。観点は一貫して
> **「proof を submit する」**。従来分散していた 3 note を畳んで 1 本にした:
> - `lean_eval_baer_suzuki.md` (提出実務・self-contained 化) → 本 note §1–§2
> - `lean_eval_candidates_2026_07_19.md` (ready-now 全表・reject 記録・eval 側仕様) → 本 note §3・§6・§7
> - `lean_eval_forward_list_2026_07_22.md` (3 層・frontier 進捗) → 本 note §3–§5
>
> **tracker = [issue 0050](../../issues/0050-lean-eval-submission-candidates.md)** (actionable checklist のみ。
> 候補データは本 note を見る)。個別提出は per-problem sub-issue (0042 型) を切る。
>
> lean-eval: <https://github.com/leanprover/lean-eval> / 提出先
> <https://github.com/leanprover/lean-eval-submissions> / 公開面 <https://lean-lang.org/eval/>

---

## §0. 現況サマリ (2026-07-22)

| | 件数 | 内容 |
|---|---|---|
| **提出済・solved** | 2 | `feit_thompson` (2026-07-16, #828)、`baer_suzuki` (2026-05-29, #118) |
| **Tier A: 今すぐ submit 可** | 34 + 🆕6 | axiom-clean 証明済。ほぼ全て**提案** (新規 problem PR) |
| **Tier B: frontier 完成で submit 可** | 3 | `brauer_suzuki` (既存**未解決**を解答) / Feit–Sibley / Suzuki 分類 |
| **Tier C: 3 冊経路の外** | 3 | Z* / Gorenstein–Walter / brauer_splitting_field |

**「3 冊が順調に完成すると自然に submit できる」経路**: (i) Tier A の提案群 (今〜)、
(ii) `brauer_suzuki` の**解答** (issue 9318 完成時)、(iii) Feit–Sibley・Suzuki 分類の提案
(issue 1054/2053 完成時)。Tier C は 3 冊の外側で、別途 modular 表現論等を立てない限り来ない。

⚠ lean-eval 作業は 3 冊 frontier に対し**オプショナル・トラック** (0042 scope 注記)。

---

## §1. proof を submit する手順 (playbook)

### §1.1 2 つの経路

- **解答 (solver)**: 既存 problem を解く。`leanprover/lean-eval-submissions` に
  「Submit benchmark solution」issue を立て、`Submission.lean` (+ `Submission/`) を出す。
  採点 = **comparator が受理するか否かのみ** (Mathlib 自由使用可)。
- **提案 (proposer)**: 新規 problem を `leanprover/lean-eval` に PR (`@[eval_problem]` +
  `manifests/problems/<id>.toml`)。外部コントリビュータの追加 PR は merge 実績あり。
  → 詳細 §7.2。

### §1.2 self-contained 原則 (最重要・0042 で確定、以後不変)

**`import OddOrder` で直接 submit しない。** 依存閉包解決時に、進行中の FT/3 冊形式化の
未公開シンボル名・補助補題・章割り構成が comparator 側へ露出するため (機密性)。

- 別 workspace を切り、**必要最小コードを `Submission.lean` + `Submission/*.lean` に
  rebrand コピー**する。**公開されるのはこの 2 箇所だけ** = 逆に言えばここに入れたものは全部公開。
- 移植コードは命名・コメントを提出側 namespace (`Submission.Helpers` 等) に rebrand。
  `OddOrder.Isaacs.Ch0X` 等の章割り情報は持ち出さない。出典 (Isaacs FGT § 等) のみ記載可。
- model 表記は使用モデル列挙 + human-in-the-loop で正直に (`feit_thompson` 前例:
  Codex 5.5/5.6 + Claude Code Opus 4.7/4.8/Fable 5)。

### §1.3 leanOptions parity (提出 scaffold との整合、issue 0120)

提出側 lakefile は **trusted scaffold で編集不可**、`[leanOptions]` は
**`autoImplicit = false` の 1 行のみ**。Lean のビルド結果は有効 option 依存で option は
import を跨がないので、閉包を提出側 option でそのままビルドすると odd-order 固有 global
option 依存ファイルが落ちる。対策 (odd-order 本体側で非依存化しておくのが堅牢):

1. **autoImplicit**: odd-order 既定 `true` / 提出 `false`。→ 本体 lakefile を
   `autoImplicit = false` 化し fallout を明示バインダに (mathlib 整合の独立価値もある)。
2. **relaxedAutoImplicit**: 厳格→緩和方向ゆえ autoImplicit=false 化後は無効化、単独対応不要。
3. **maxSynthPendingDepth**: odd-order `3` / 提出 既定 `<3`。→ 深さ 3 を要する宣言に
   `set_option maxSynthPendingDepth 3 in` を局所付与、global は除去 (最小介入)。

これにより vendoring が per-file `set_option` 注入なしの import 行書換だけで済む。

### §1.4 提出フロー実務 (solver)

- ソースは 3 通り: (a) 生成済み workspace、(b) `leanprover/lean-eval` fork の `generated/`
  改変、(c) **public gist**。
- ローカル検証 = `lake test` (`landrun` サンドボックス + `lean4export` + `comparator`)。
- private repo から出すなら `lean-eval-bot` GitHub App を install。
- 結果は `results/<github-login>.json` に記録され **sticky** (一度解けば以後の提出が
  再現しなくても消えない)。現在 30 アカウント分。`yawara.json` に既提出 2 件。

### §1.5 提案フロー (proposer) → §7.2 に詳細

---

## §2. 既提出 (2 件)

| problem | 提出日 | Lean 名 | 備考 |
|---|---|---|---|
| `baer_suzuki` | 2026-05-29 (#118) | `Isaacs.Ch02.baerSuzuki_pCore` (`Ch02_Subnormality/Theorem211Wielandt.lean:885`) | p-core 単元版。workspace = `/home/ywr/lean-eval-submissions/baer_suzuki` |
| `feit_thompson` | 2026-07-16 (#828) | `OddOrder.feitThompson` (`FeitThompson.lean:575`) | 奇数位数定理。閉包 565 ファイルを vendoring。workspace = `../odd-order-submission` (`SUBMISSION_STRATEGY.md`) |

**baer_suzuki の移植スコープ (self-contained 化の実例)**: eval signature は
`x ∈ Defs.pCore p G ↔ ∀ g, IsPGroup p (closure {x, gxg⁻¹})`。repo の `opCore = Defs.pCore`
(extensionality + 最大性、橋渡し補題を `Submission/Helpers.lean` に)。抽出した閉包 =
`opCore`/`fitting` の定義と最大性 + Wielandt Zipper Lemma + Isaacs 2.12 iff
(`le_fitting_iff_baer_sup_conj_isNilpotent`) + F(G)→O_p(G) 橋
(`mem_opCore_of_le_fitting_of_isPGroup`) + 本体。

---

## §3. Tier A — 今すぐ submit 可 (ready-now)

いずれも実 sorry 0。**AxiomsCheck 登録の有無で提出前作業が変わる** (未登録は提出前に
`#print axioms` で axiom-clean を確定)。2026-07-22 に 34 件全て存続を再検証済 (file 移動軽微 3 件)。

### §3.1 最優先 5 (bespoke def ほぼ 0)

| # | 定理 | Lean 名 | 知名度 | eval 対応 |
|---|---|---|---|---|
| 1 | **Jordan の定理** (素数長サイクル原始群 ⊇ Aₙ) | `Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` (`Ch08_PermutationGroups/PCycleJordan.lean:352`) | 高 | mathlib が `proof_wanted` で同 signature を明示。理想形 |
| 2 | **Chermak–Delgado** (Isaacs 1.41) | `Subgroup.chermakDelgado` (`GroupTheory/ChermakDelgado.lean:528`) | 高 | statement 1 行・完全 mathlib 語彙 |
| 3 | **Furtwängler 主イデアル定理** (Isaacs 10.18) | `Isaacs.Ch10.transfer_commutator_eq_one` (`Ch10_MoreTransfer/PrincipalIdeal.lean:44`) | 伝説級 | statement 3 行・証明は群環 2,500 行 |
| 4 | **Thompson: FPF 作用⇒冪零** (Isaacs 6.24) | `Isaacs.Ch06.isNilpotent_of_isFrobeniusAction` (`Ch06_FrobeniusActions/KernelNilpotent.lean:365`) | 高 | 既存 `frobenius_kernel_isNormal` の次段 |
| 5 | **PSL(n,K) 単純性** (Isaacs 8.33) | `Isaacs.Ch08.isSimpleGroup_projectiveSpecialLinearGroup` (`Ch08_PermutationGroups/PSLSimple.lean:355`) | 伝説級 | mathlib は単純性のみ欠く |

statement 素案は §3 末尾 (各定理を素の scratch file で通した実測版) 参照 → 旧
`lean_eval_candidates_2026_07_19.md` §2 に温存 (git 履歴)。要点のみ:
- Jordan: `(hG : IsPreprimitive G α) (hp : p.Prime) (hp' : p+3 ≤ Nat.card α) (hgc : g.IsCycle) (hgp : g.support.card = p) (hg : g ∈ G) : alternatingGroup α ≤ G`
- Chermak–Delgado: `∃ N, N.Characteristic ∧ IsMulCommutative N ∧ ∀ A, IsMulCommutative A → N.index ≤ A.index ^ 2`
- Furtwängler: `(g : G) : MonoidHom.transfer (Abelianization.of : commutator G →* Abelianization (commutator G)) g = 1`
- Thompson-FPF: `(h : ∀ a:A, a≠1 → ∀ n:N, n≠1 → a•n ≠ n) : Group.IsNilpotent N`
- PSL: `(h : 3 ≤ Nat.card ι ∨ ∃ β:K, β≠0 ∧ β^2≠1) : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι K)`

### §3.2 strong 候補 全表 (推奨度 ★★★=最優先 / ★★=有力 / ★=優先度低)

| # | 定理 | Lean 名 | file:line | AxiomsCheck | self-contained | 推奨 |
|---|---|---|---|---|---|---|
| 6 | Dietzmann の補題 (Isaacs 5.10) | `Isaacs.Ch05.dietzmann` | Ch05_Transfer/Dietzmann.lean:254 | :1045 | high | ★★ |
| 7 | 既約表現次数 ∣ \|G\| (Frobenius) | `RepresentationTheory.finrank_dvd_card` | RepresentationTheory/ClassSumAlgebra.lean:298 | :2312 | high | ★★ |
| 8 | Burnside (既約表現包絡環 = End V) | `RepresentationTheory.span_range_representation_eq_top` | RepresentationTheory/AbsolutelyIrreducible.lean:192 | 実測 (未登録) | high | ★★ |
| 9 | Alperin–Kuo 系 `g^[G:G'∩Z]=1` (10.28) | `Isaacs.Ch10.pow_index_commutator_inf_center_eq_one` | Ch10/PrincipalIdeal.lean:90 | :10526 | high | ★★ (#3 と資産共有・両方は出さない) |
| 10 | Horoševskii (自己同型位数<\|G\|) | `Isaacs.Ch03.horosevskii_aut_order_lt` | Ch03_SplitExtensions/Basic.lean:124 | :950 | high | ★★ |
| 11 | Lucchini (巡回部分群 core 指数, 2.20) | `Isaacs.Ch04.lucchini_index_normalCore_lt_index` | Ch04_Commutators/ForwardFromCh02.lean:1084 | :941 | high | ★★ |
| 12 | Isaacs 10.25 (transfer 指数消滅) | `Algebra.transfer_pow_relindex_eq_one` | Algebra/PrincipalIdealTheorem.lean:1320 | :10525 | high | ★★ (#3 上流・片方) |
| 13 | 単純群の冪零極大部分群は p-群 (5.24) | `Isaacs.Ch05.exists_isPGroup_of_isCoatom_of_isNilpotent` | Ch05/NilpotentMaximal.lean:249 | :1065 | high | ★★ |
| 14 | transfer 推移律 (Isaacs 10.8) | `GroupTheory.transfer_transfer` | GroupTheory/TransferTransitivity.lean:366 | 実測 (未登録) | high | ★★ |
| 15 | BG Prop 3.9 (奇 p-群 FPF⇒巡回) | `BG.Ch1.S03.isCyclic_of_isPGroup_of_isFrobeniusAction` | BG/…/S03g_Thm310.lean:55 | :5763 | high | ★★ |
| 16 | Hall–Petrescu (class≤3) | `BG.AppE.hallCollection_of_class_le_three` | BG/AppE_CollectionFormula.lean:194 | :10841 | high | ★★ **← 🆕一般版 (§3.3) が上位互換** |
| 17 | 可解群既約表現次数 ∣\|G\| (BG 2.3/Fong) | `RepresentationTheory.finrank_dvd_card_of_isAlgClosed_of_irreducible` | RepresentationTheory/FongSwan.lean:202 | :5425 | high | ★★ (#7 と重複気味・片方) |
| 18 | BG Thm 3.4 (奇数位数可解 coprime 作用) | `BG.Ch1.S03d.thm34` | BG/…/S03d_Thm34.lean:1075 | :5587 | high | ★ (難度上限側) |
| 19 | BG Prop 4.4(b)=G 7.6.5 (SCN 中心化分解) | `GroupTheory.centralizer_eq_dprod_of_isSCN_of_sylow` | BG/…/S04_Prop44b.lean:105 | :5450 | high | ★★ |
| 20 | BG App.C Lemma C.1 (ノルム集合⇒p≤q) | `BG.AppC.NormSet.lemmaC1` | BG/AppC_NormSet.lean:1459 | :5390 | high | ★ |
| 21 | Huppert V.8.15 特別版 (定常点安定化⇒巡回+FPF) | `Peterfalvi.Appendices.Huppert.pGroup_cyclic_fixedPointFree` | Peterfalvi/Appendices/Huppert.lean:720 | :8090 | medium | ★ |
| 22 | Peterfalvi 付録 I Prop 2 (半線形性つき体構造) | `Peterfalvi.Appendices.Huppert.exists_field_semilinear` | Appendices/SemilinearField.lean:199 | :8870 | high | ★ |
| 23 | 忠実既約表現⇒中心巡回 (Gorenstein 3.2.2) | `RepresentationTheory.isCyclic_center_of_faithful_irreducible` | RepresentationTheory/AbsolutelyIrreducible.lean:239 | :5481 | high | ★ (易しめ枠) |
| 24 | \|SL(2,q)\| = q(q−1)(q+1) | `GroupTheory.SpecificGroups.ProjectiveSpecialLinear.natCard_specialLinearGroup_fin_two` | …/RootGroupSylow.lean:106 | :355 | high | ★ (提出時 vestigial `[CharP F 2]` を外す) |
| 25 | Thompson critical subgroup (G 5.3.11) | `GroupTheory.isCritical_exists` | GroupTheory/CriticalSubgroup.lean:434 | 実測 (未登録) | medium | ★★ (docstring 過大表現を写さない) |
| 26 | **Hall の定理 E/C/D** (可解群) | `Isaacs.Ch03.hall_E_exists`/`hall_C`/`hall_D` | Ch03_SplitExtensions/Basic.lean:1002/1375/1675 | :954/1690/1694 | medium | ★★★ |
| 27 | Thompson Frobenius 核冪零 (subgroup-pair 形) | `Isaacs.Ch06.IsFrobeniusGroup.isNilpotent_kernel` | Ch06/KernelNilpotent.lean:382 | :1131 | medium | ★ (#4 action 形を優先) |
| 28 | Huppert metacyclic Sylow (Isaacs 10.12) | `Isaacs.Ch10.dvd_index_commutator_of_metacyclic_sylow` | Ch10/HuppertMetacyclic.lean:751 | :10516 | medium | ★★ |
| 29 | BG Thm 3.5 (Frobenius 群作用・1 次元不動点) | `BG.Ch1.S03e.thm35` | BG/…/S03e_Thm35.lean:1685 | :5672 | high 相当 | ★ (難度上限側) |
| 30 | BG Thm 6.4 (正規 Hall 下の中心化共役) | `BG.Ch1.S06.exists_centralizing_conj_sup_isPiGroup_of_normalHall` | BG/…/S06_Thm64Case2.lean:483 | :2703 | medium | ★ |
| 31 | BG Thm 4.20(a) (r(F(G))≤2 ⇒ G'≤F(G)) | `BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two` | BG/…/S05_NarrowPGroups.lean:763 | :2800 | medium | ★ (⚠ mathlib `Group.rank` と名前衝突) |

### §3.3 🆕 新着 ready-now (2026-07-19 note 後に完成)

| 定理 | Lean 名 | file:line | AxiomsCheck | 知名度 | 備考 |
|---|---|---|---|---|---|
| **Glauberman ZJ 定理** (Z(J) 正規) | `GroupTheory.oPiCorePrime_sup_normalizer_zCenter_thompsonJAbelian` (core 形 `zCenter_thompsonJAbelian_normal`:781) | GroupTheory/GlaubermanZJ.lean:888 | ❌ 未登録 (要 `#print axioms`) | **伝説級** | ⚠ **前 note が「repo に存在しない」と reject した項目が完成**。Gorenstein Thm 2.10/2.11。bespoke = `thompsonJAbelian`/`IsPStableOp`/`opCore`/`oPiCore` |
| Glauberman Replacement 定理 | `GroupTheory.glauberman_replacement` | GroupTheory/GlaubermanReplacement.lean:540 | ❌ 未登録 | 高 | ZJ の前提 (G Ch.8 §2 Thm 2.7)。Hall–Witt 恒等式 (:210) も副産物 |
| **B.H.Neumann 位数 3 定理** (order-3 FPF 自己同型⇒class≤2) | `GroupTheory.lowerCentralSeries_two_eq_bot_of_fixedPointFree_orderOf_eq_three` | GroupTheory/FixedPointFreeOrderThree.lean:456 | ✅ :8350 | 高 | 純 mathlib 語彙・仮説 inline ∀・**bespoke ほぼ 0** = 最も出しやすい |
| **一般 Hall–Petresco 公式** | `GroupTheory.HallPetresco.exists_hallPetresco` (2-gen 版 `BG.AppE.hallCollection`) | GroupTheory/HallPetresco.lean:407 | ✅ :10858 | 高 | class 制約なし・任意 G (Mann 証明)。**#16 (class≤3) を完全に超える** |
| Hall 正則 p-群 (class<p ⇒ p 乗が部分群) | `GroupTheory.pow_mul_eq_one_of_class_lt` | GroupTheory/RegularPGroup.lean:195 | ✅ :10861 | 中 | 上の群論的帰結 (BG E.2) |
| Galois–Burnside (可解 2-可移群極小正規部分群 elementary abelian regular) | `GroupTheory.exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive` | GroupTheory/SolvableTwoTransitive.lean:65 | ❌ 未登録 | 中 | Huppert II Satz 3.2 (issue 9404) |

**新着の推し**: ZJ (伝説級・要登録) → 提案本命 / B.H.Neumann 位数 3 (登録済・bespoke≈0) → 最も出しやすい /
一般 Hall–Petresco → #16 を差し替える。

### §3.4 viable 候補 全表 (bespoke 焼き込み等が必要 / 価値・難度に留保)

| 定理 | Lean 名 | file:line | AxiomsCheck | 備考 |
|---|---|---|---|---|
| Fitting F(G) 冪零性・最大性 (1.28) | `Isaacs.Ch01.fitting.isNilpotent`/`nilpotent_normal_le_fitting` | Ch01_Sylow/Basic.lean:1108/963 | 実測 (Ch01 未登録) | 焼き込み 2 行・実質 strong 寄り |
| Wielandt 自己同型塔定理 (9.10) | `Isaacs.Ch09.exists_card_autTowerType_le` | Ch09/AutTower.lean:364 | :1191 | universe 跨ぎ・正答率≈0 想定 |
| Thompson 正規 p-補群 (7.1) | `Isaacs.Ch07.thompson_normal_p_complement_of_local_hypotheses` | Ch07/S7C_…Final.lean:35 | :1630 | bespoke 5・実質 strong 寄り |
| Glauberman normal-J (7.6 完全形) | `Isaacs.Ch07.normal_J` | Ch07/S7B2_NormalJ_PComplement.lean:1425 | :1569 | bespoke 9。docstring「local axiom 残」は stale |
| Matsuyama (2.13) | `Isaacs.Ch02.matsuyama` | Ch02/Theorem211Wielandt.lean:768 | :933 | eval `pCore` と defeq でなく橋渡し要 |
| Hall–Higman 型 (BG 6.1/A.4(b)) | `BG.Ch1.S06.le_oPiPrimePiCore_of_abelian_normal_in_sylow` | BG/…/S06_Thm61.lean:47 | :2541 | 「Hall–Higman 定理」と称すは過大 |
| BG Thm A.4(a) (O_p(G)=1⇒p-stable) | `BG.AppA.thmA4a` | BG/AppA_PStability.lean:818 | :2527 | 教科書より仮説弱い (solvable 落とし) |
| BG Thm 3.6 (⁅H,R⁆ p-length one) | `BG.Ch1.S03f.thm36` | BG/…/S03f_Thm36.lean:3812 | :5760 | 支持 ~5,700 行・事実上解答不能側 |
| BG Thm 3.10 (\|M\|=\|C_M(R)\|^\|R\|) | `BG.Ch1.S03g.bgThm310_nilpotent` | BG/…/S03g_Thm310Nilpotent.lean:289 | :5455 | 結論 (b)∧(c) 連言・分割提出望ましい |
| BG Cor 1.12 (Ω₁-剛性) | `BG.Ch1.S01.corollary_1_12` | BG/…/S01_Solvable.lean:474 | :2822 | 重い前提 2 本に全面依存 |
| BG App.C Lemma C.2 | `BG.AppC.NormSet.lemmaC2` | BG/AppC_LemmaC2.lean:25 | :5400 | 条件(A)仮説 `_hA` 未使用 (書籍より強い) |
| Huppert (Peterfalvi 付録 I Prop 1) | `Peterfalvi.Appendices.Huppert.fitting_cyclic_fixedPointFree` | Appendices/Huppert.lean:1305 | :8093 | 焼き込めば実質 strong |
| Peterfalvi 付録 I Prop 2(b) | `…Huppert.exists_injective_semilinear_companion` | Appendices/SemilinearField.lean:520 | :8885 | 単独提出不可・#22 とセット |
| Peterfalvi 付録 C Prop 2 既約性段 | `…NearFields.rightMulAction_irreducible_of_index_two` | Appendices/NearFields.lean:405 | :8901 | 近体系を出すならこちら |
| Suzuki 群 Sz(q) 単純性 | `GroupTheory.SpecificGroups.Suzuki.standardPermGroup_isSimpleGroup` | …/Suzuki/Simplicity.lean:268 | :918 | 伝説級。`∧ \|G\|=q²(q²+1)(q−1)` 併記推奨・証明込 preamble 600–700 行 |
| \|Sz(q)\|=q²(q²+1)(q−1) | `…Suzuki.natCard_standardPermGroup` | …/Suzuki/Bruhat.lean:673 | :852 | 単純性と Bruhat 共有 (独立でない) |
| PSU(3,q) (q=2ⁿ>2) 単純性 | `GroupTheory.SpecificGroups.ProjectiveUnitary.standardPermGroup_isSimpleGroup` | …/ProjectiveUnitary/Simplicity.lean:337 | :608 | Suzuki 版と構造同型→両方出さない |
| 第二 (列) 直交関係 (2.18) | `RepresentationTheory.column_orthogonality_diagonal` | RepresentationTheory/ColumnOrthogonality.lean:91 | :1927 | `Fintype (IrreducibleCharacter G)` を仮説に |
| ∑χ(1)²=\|G\| | `RepresentationTheory.sumIrreducibleDegreeSq` | …/ColumnOrthogonality.lean:137 | :1942 | 上と資産共有 |
| \|Irr G\|=\|ConjClasses G\| (2.8) | `RepresentationTheory.card_irreducibleCharacter_eq` | …/CharacterCompleteness.lean:658 | :1919 | `V:Type 0` 制限の非標準エンコード |
| Irr(G) は CF(G) の基底 | `Peterfalvi.S05.classFunction_span_irreducibleCharacter_eq_top` | Peterfalvi/S05_NormThree.lean:54 | :5681 | 難度が preamble 設計で振れる |
| Brauer 置換補題 | `RepresentationTheory.brauer_permutation_lemma'` | …/BrauerPermutationUnconditional.lean:196 | :1966 | docstring「Isaacs Thm 6.32」は誤引用 (別書) |
| 奇数位数群に非自明実既約指標なし (Burnside) | `RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'` | …/BrauerPermutationUnconditional.lean:233 | :1970 | 伝説級 |
| Peterfalvi (3.5.1) ノルム 3 分解 | `Peterfalvi.S05.exists_signedTriple_of_inner_self_three` | Peterfalvi/S05_SignedTripleGrid.lean:73 | :5580 | Fourier 補題与えると残る数学薄い |
| Wielandt 不動点公式 (Peterfalvi (9.1)) | `GroupTheory.wielandt_fixedPoint_frobenius` | GroupTheory/WielandtFixedPoint.lean:52 | :9046 | AxiomsCheck:8944 の「sorried Wielandt cite」は stale |
| 可解 CN 群構造定理 (Gorenstein 1.5) | `GroupTheory.solvableCN_nilpotent_or_frobenius_or_threeStep` | GroupTheory/CNGroupStructure.lean:1048 | :10688 | 弱化版 (補元分類省略) を明示 |

---

## §4. Tier B — frontier 完成で submit 可 (arrives-on-completion)

進捗 % は原文ステップ被覆で測定 (scaffold 数でない)、敵対的検証済。

### §4.1 🎯 `brauer_suzuki` — 既存**未解決** problem を「解答」できる唯一の frontier

- **issue [9318](../../issues/9318-brauer-suzuki-theorem.md)** (lane c、2026-07-22 b→c 移管)。
- **定理**: Brauer–Suzuki (1959)。Sylow-2 が cyclic/一般化四元数 ⟹ `G = O_{2'}(G)·C_G(u)`。
  CFSG 礎石補題。Gorenstein Ch.12 (例外指標論)。
- **eval**: 既存**未解決** `brauer_suzuki` (solver 0) に直接一致 → 完成すれば**提案でなく解答**。
- **進捗 ≈ 38%**: cyclic 版完全証明済 (`brauerSuzuki_of_isCyclic_sylowTwo`, BrauerSuzuki.lean:47)。
  四元数版は Gorenstein Lem 1.2→1.6 landing (Setup/Normalizer/TISubset/Character.lean 各 0 sorry・
  axiom-clean 登録済)。**最難所 = 例外指標 Lem 1.4–1.5 が完了** (θ*=1_G+χ₁−χ 分解)。
- **残り**: Lem 1.7 (β(y) 対合対 counting) → (9.4.2) class-sum 構造定数接続 → Lem 1.8–1.9 算術 →
  純群論 endgame (M=⟨対合⟩⊴G, Burnside) → 一般四元数仮説→setup 橋 → top-level 組立 →
  消費点 `NearFields.lean:789` の sorry 除去。⚠ Q8 (|S|=8) case は Gorenstein 1968 の modular 依存
  で research-adjacent。target `brauerSuzuki` は未作成、active leaf `BrauerSuzukiCharacter.lean`。

### §4.2 `feit_sibley_coherence` — Feit–Sibley 定理 (提案候補)

- **issue [1054](../../issues/1054-feit-sibley-theorem-campaign.md)** (lane a、8-step) +分割 [0141](../../issues/0141-feitsibley-theorem-split.md)。
- **定理**: Feit–Sibley coherence (Peterfalvi App.IV)。d odd ⟹ 𝒮 が τ=Ind_H^G に関し coherent。
  奇数位数定理の coherence keystone。eval 対応なし → **提案候補**、知名度は niche。
- **進捗 ≈ 75%** (敵対的検証で survey 85% を下方修正): 原文 8 step + endgame integrator
  `xset_qder_union_coherent` は全て sorry-free landing (11 leaf、実 sorry は master 定理 1 個
  = FeitSibley.lean:1251)。ただし 8 step は master に未配線。
- **残り**: full-𝒳 の p-進評価下界 (`hXdiff`、**issue 自身が「最大未構築」と flag する新 infra**) +
  anchor χ₁ 選択 + Lemma 1(a) adjoin + 外側 4-way case split + statement に `Odd (Nat.card G)` 追加。

### §4.3 Suzuki Zassenhaus 群分類 (Theorem A) — 遠い提案候補

- **issue [2053](../../issues/2053-pf-suzuki-theorem-b.md)** (lane b) は **Theorem B (First Case) のみ**
  産出 = Theorem A への帰納の 1 case、単独 submit 不可。
- **提出可能な名前付き定理 = Theorem A** (Suzuki 1962: 奇指数正規 L≅PSL(2,q)/Sz(q)/PSU(3,q))。
  自然な eval id = `suzuki_zassenhaus_classification`。
- **進捗**: Theorem B ≈30% (17 step 中 (1)–(6) landing、(7) plan のみ、(8)–(17) 未着手で hard endgame)。
  **Theorem A 全体 ≈15–20%** (Ch.III/IV 未着手・帰納組立未記述)。⚠ `brauer_suzuki` と混同しない
  (2053 step (2) が 9318 を上流消費するだけ)。⚠ step (17) Hall–Wielandt transfer 定理は M. Hall
  教科書が `references/` に無く要 source 追加。**submittable = far**。

### §4.4 (参考) eval 候補で**ない** frontier

- **issue [2052](../../issues/2052-pf-appendix3-e-forward.md)**: Higman Suzuki-2群 App.III (e) 前向き。
  statement が repo carrier に絡む内部完全性補題 → submittableOnCompletion = false。

---

## §5. Tier C — lean-eval 未解決だが 3 冊経路の外 (自然には来ない)

honest に記録 (安易に「近い」と誤認しない)。

| problem | 定理 | 3 冊経路との距離 | 実現可能性 |
|---|---|---|---|
| `glauberman_zStar` | Glauberman Z*-定理 (孤立対合) | **very large**。p=2 の modular 表現論 (Brauer 指標・principal 2-block・Glauberman 対応) 必須で 3 冊は p-odd/char-0 ordinary のみ。repo に modular rep theory 皆無。同名 `GlaubermanZJ`/`Replacement` は**別定理** (p-odd) で転用不可 | **LOW** |
| `gorenstein_walter` | 二面体 Sylow-2 単純群分類 (A₇ or PSL₂(q)) | **enormous**。Bender method + signalizer functor + Z* 必須 (Z* に strictly downstream)。repo は building block (PSL₂(q) 単純性・二面体 2-群基礎) のみ | **LOWEST** |
| `brauer_splitting_field` | ℚ(ζₙ) は G の分裂体 (RepTheory) | **moderate**。値の半分 (指標値∈ℚ(ζₙ)) は `CyclotomicGaloisAction`/`GaloisCharacter` で既済 (姉妹 `brauer_character_in_cyclotomic` は 10 名 solved)。難しい半分 = Schur index=1 が Brauer 誘導定理 + Schur index 降下を要し、FT は Dade isometry/coherence で回避 → **経路上に来ない** | **MEDIUM** (3 問中最良だが off-path) |

`schreier_conjecture`/`five_transitive_card_classification` は CFSG 依存、
`higman_infinite_simple`/`novikov_unsolvable` は組合せ群論で無関係 (着手しない)。

---

## §6. reject / 見送り の記録 (再調査しないこと)

| 対象 | 判定 | 理由 (実測) |
|---|---|---|
| **Glauberman ZJ 定理** | ⚠ **reject 撤回 (2026-07-22)** | 2026-07-19 は「repo に存在しない」と reject したが `GlaubermanZJ.lean` で完成 → §3.3 に昇格 |
| Frobenius の定理 (核の存在) | reject — repo に不在 | 古典 Frobenius の核が部分群/正規部分群という定理が 1 本も無い。repo の `IsFrobeniusGroup` は核を仮定する structure |
| Burnside 正規 p-補群 (5.13) | reject — mathlib 収録済 | `MonoidHom.ker_transferSylow_isComplement'` (Transfer.lean:276) |
| Brauer–Fowler | reject — スコープ外かつ不在 | Gorenstein 由来ゆえ恒久対象外。eval では既に Solved (6 名) |
| BG Thm 6.2 Puig L(S) 版 | weak — 見送り | 書籍が名を与えた statement でない中間主張 |
| `NearFields.nearField_field_structure_of_index_two` | weak — 見送り | 仮説 `A`/`hcomm`/`hidx` が結論に効かない (3 仮説削っても解ける実測) |
| `Huppert.exists_field_of_irreducible` (付録 I Prop 2(a)) | weak — 見送り | `ψ`/`hirr` が結論に現れず GaloisField 経由で解ける。#22 に差替済 |
| operator 群 Maschke (`exists_aInvariant_complement…`) | weak — 見送り | 核は mathlib `MonoidAlgebra.Submodule.exists_isCompl`。repo 分は packaging |
| `AppC.NormSet.normOneFrobenius_isFrobeniusGroup` | weak — 単独提出せず | 番号なし補助構成 |
| Peterfalvi (1.2) `irreducibleCharacter_apply_eq_zero…` | weak — 見送り | 前提を与えないと解不能、与えると残り ~90 行帳簿 |
| Peterfalvi (5.7) `coherent_of_constant_degree` | weak — 見送り | bespoke 15+・6 ファイル焼き込み、かつ特殊化版で「(5.7)」称は過大 |
| Suzuki `Hypothesis.sylowTwo_isMulCommutative_or_isSuzuki2Group` | weak — 参考枠 | 20 フィールド bespoke 仮説束で独立定理として読めない |
| `AppE.hallCollection` (旧・一般版) | ⚠ **提出可に変化 (2026-07-22)** | 旧 note では 130 行 sorry だったが `exists_hallPetresco` として完成 → §3.3 |

---

## §7. lean-eval 側 reference

### §7.1 repo 構造・problem 一覧

```
LeanEval/            trusted な問題文 (topic フォルダ 21 件)
manifests/problems/  1 problem = 1 TOML (<id>.toml)
generated/<id>/      comparator workspace (CI が自動生成)
  ├ Challenge.lean / Solution.lean / config.json / lakefile.toml  ← trusted 読取専用
  └ Submission.lean / Submission/*.lean                           ← solver 所有 (公開範囲)
```

全 problem 数 ≈200。GroupTheory の **未解決** = `glauberman_zStar` / `brauer_suzuki` /
`gorenstein_walter` / `schreier_conjecture` / `five_transitive_card_classification` /
`higman_infinite_simple` / `novikov_unsolvable`。RepresentationTheory 未解決 = `brauer_splitting_field`。
GroupTheory の **solved** = baer_suzuki / feit_thompson / brauer_fowler / frobenius_kernel_isNormal /
Burnside p^a q^b / commProb_closed / golod_shafarevich / boone_higman_{embedding,simple}。
⚠ 全リスト逐語取得は `api.github.com/repos/leanprover/lean-eval/contents/manifests/problems` を
per_page 付き 2 ページで (1 回の要約 fetch は後半を捏造する事故あり)。

### §7.2 新規 problem 提案フロー

1. `lake exe cache get && lake build` で依存用意。
2. `LeanEval/<Topic>/` に `@[eval_problem] theorem my_problem : … := by sorry` を追加。
3. `manifests/problems/<id>.toml` を作成 (必須 = `id`(=ファイル名 stem)/`title`/`test`/`module`/
   `holes`/`submitter`。`holes` = そのモジュールで当該 problem が所有する `@[eval_problem]`
   宣言を全部列挙。multi-hole 可)。
4. `lake exe lean-eval validate-manifest` + `check-problem-build` で検証。
5. PR。CI が `generated/` workspace を再生成。
- **自由度**: mathlib 非収録の定義は `LeanEval/<Topic>/Defs/*.lean` に小さく持ち込める
  (`Defs/PCore.lean`/`Defs/OddCore.lean` 前例) → Suzuki 群・Thompson 部分群・F*(G)・
  Dade isometry のような概念を要する定理も提案可能。
- キュレーション関心 (`PLAN.md`) = topic/difficulty 網羅性・飽和 easy 問題の retire/差し替え・
  手薄領域の穴埋め。明文の受理基準は無いが「mathlib 既存定義で述べられる」「現行モデルに難しい」が事実上の基準。

---

## §8. 次アクション (issue 0050 tracker が正)

1. 🆕 ZJ 定理を AxiomsCheck 登録 → 提案 PR 最有力。
2. Tier A 提案 PR: Jordan / Chermak–Delgado / Furtwängler / Thompson-FPF + 🆕 B.H.Neumann 位数 3
   (登録済) + 一般 Hall–Petresco (#16 差替)。提案先 merge、solver は他者開放 (feit_thompson 前例)。
3. 🎯 9318 完走 → `brauer_suzuki` 解答 (Tier B 唯一の未解決落とし)。lane c 継続。
4. AxiomsCheck 未登録の ready-now を登録 (ZJ/Replacement/Galois–Burnside/Jordan/PSL 単純性/
   `isCritical_exists`/`transfer_transfer`/Ch01 Fitting/`span_range_representation_eq_top`)。
5. stale docstring 掃除 (`burnside_p_pow_q_pow` の「local axiom 封じ込め」、`Ch07.normal_J` の
   「Remaining local axioms」、`AppC_NormSet` の「to be formalized」、`brauer_permutation_lemma'`
   の「Isaacs Thm 6.32」誤引用ほか) — 提出物に写すと誤解を招く。
