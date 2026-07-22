# lean-eval 提出候補 — 前向きリスト (2026-07-22)

> **位置づけ**: [issue 0050](../../issues/0050-lean-eval-submission-candidates.md) の候補表を、
> **「このまま順調に 3 冊の形式化が完了すると自然に submit できる問題」**という前向きの軸で
> 再編したもの。前身 = [`lean_eval_candidates_2026_07_19.md`](lean_eval_candidates_2026_07_19.md)
> (2026-07-19、ready-now 中心の実測棚卸し)。本 note は **その 3 日後 = 1,473 commits 後**の
> 再測 (11 エージェント fan-out: ready-now 34 件の再検証 + 新着 10 件の発掘 + 4 active frontier
> の進捗測定 + lean-eval 未解決 3 問の solver-side 評価 → frontier 判定は敵対的検証済)。
>
> 判定はすべて実測 (identifier grep / comment-strip した実 sorry census / `OddOrder.lean` 配線確認 /
> `AxiomsCheck.lean` 登録確認)。⚠ **前 note からの最大の訂正 = Glauberman ZJ 定理**:
> 2026-07-19 note は §3 で ZJ を「reject — repo に存在しない」としたが、**その後 `GlaubermanZJ.lean`
> で完全形式化された** (下記 Tier A-新)。stale ラベルを鵜呑みにしない。

---

## 3 層構造 — 「自然に submit できる」の内訳

lean-eval 提出には 2 経路: **提案** (`leanprover/lean-eval` に `@[eval_problem]` + manifest を PR)
と **解答** (`leanprover/lean-eval-submissions` に Submission.lean を出す)。3 冊完成に向けて
提出可能になる問題を、**現在との距離**で 3 層に分ける。

| Tier | 意味 | 経路 |
|---|---|---|
| **A. Ready-now** | 既に axiom-clean で証明済。パッケージングすれば**今**出せる | ほぼ全て**提案** (mathlib/eval 未収録の新規 problem) |
| **B. Arrives-on-completion** | 現 active frontier が閉じると submit 可能形になる | 9318 は**解答** (既存未解決 problem)、他は**提案** |
| **C. lean-eval 未解決だが 3 冊経路上に無い** | 完成しても自然には来ない (別プロジェクト級) | 参考。着手是非は別判断 |

**提出の実務規約 (0042 踏襲・不変)**: `import OddOrder` は不可 (依存閉包経由で未公開の FT 構造が
露出)。必要最小コードを `Submission.lean` + `Submission/*.lean` に rebrand コピー。公開されるのは
その 2 箇所のみ。model 表記は使用モデル列挙 + human-in-the-loop で正直に。

---

## Tier A — Ready-now (提案すれば今出せる)

### A-1. 2026-07-19 note の strong 候補 (34 件全て再検証パス)

1,473 commits を経ても **全件が存在・実 sorry 0 のまま**。file 移動は軽微 3 件のみ:
- `finrank_dvd_card` : ClassSumAlgebra.lean **:296→:298**
- `finrank_dvd_card_of_isAlgClosed_of_irreducible` : FongSwan.lean **:201→:202**
- Hall–Petrescu (class≤3) : **`AppE_FurtherResults.lean:218` → `AppE_CollectionFormula.lean:194`** (AppE 分割)

最優先 5 件 (前 note §2 のまま有効、いずれも bespoke def ほぼ 0):

| # | 定理 | Lean 名 | 知名度 | eval 対応 |
|---|---|---|---|---|
| 1 | **Jordan の定理** (素数長サイクル原始群 ⊇ Aₙ) | `Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` | 高 | mathlib が `proof_wanted` で同 signature を明示。理想形 |
| 2 | **Chermak–Delgado** (Isaacs 1.41) | `Subgroup.chermakDelgado` | 高 | statement 1 行・完全 mathlib 語彙 |
| 3 | **Furtwängler 主イデアル定理** (Isaacs 10.18) | `Isaacs.Ch10.transfer_commutator_eq_one` | 伝説級 | statement 3 行・証明は群環 2,500 行 |
| 4 | **Thompson: FPF 作用 ⇒ 冪零** (Isaacs 6.24) | `Isaacs.Ch06.isNilpotent_of_isFrobeniusAction` | 高 | 既存 `frobenius_kernel_isNormal` の次段 |
| 5 | **PSL(n,K) 単純性** (Isaacs 8.33) | `Isaacs.Ch08.isSimpleGroup_projectiveSpecialLinearGroup` | 伝説級 | mathlib は単純性のみ欠く |

以下 #6–#31 は前 note §1-A のまま (Hall E/C/D #26、Dietzmann #6、`finrank_dvd_card` #7、
Thompson critical subgroup #25 ほか)。詳細表・statement 素案・reject 記録は前 note を正本とする。

### A-2. 🆕 2026-07-19 note に **無い** 新着 ready-now (この 3 日で完成)

いずれも実 sorry 0・`OddOrder.lean` 配線済。⚠ **AxiomsCheck 登録の有無で提出前作業が変わる**
(未登録は提出前に `#print axioms` で axiom-clean を確定してから出す)。

| 定理 | Lean 名 | file | AxiomsCheck | 知名度 | 備考 |
|---|---|---|---|---|---|
| **Glauberman ZJ 定理** (Z(J) は G に正規) | `GroupTheory.oPiCorePrime_sup_normalizer_zCenter_thompsonJAbelian` (core 形 `zCenter_thompsonJAbelian_normal`:781) | `GroupTheory/GlaubermanZJ.lean:888` | ❌ 未登録 (`#print axioms` 要) | **伝説級** | ⚠ **前 note が reject した項目が完成**。Gorenstein Thm 2.10/2.11。ZJ (literal J = 極大 abelian 生成) は FT 局所解析の中核。bespoke = `thompsonJAbelian`/`IsPStableOp`/`opCore`/`oPiCore` (~4 def) |
| **Glauberman Replacement 定理** | `GroupTheory.glauberman_replacement` | `GroupTheory/GlaubermanReplacement.lean:540` | ❌ 未登録 | 高 | ZJ の前提 (Gorenstein Ch.8 §2 Thm 2.7)。Hall–Witt 恒等式 (:210) も副産物 |
| **B. H. Neumann 位数 3 定理** (order-3 FPF 自己同型 ⇒ 冪零 class ≤ 2) | `GroupTheory.lowerCentralSeries_two_eq_bot_of_fixedPointFree_orderOf_eq_three` | `GroupTheory/FixedPointFreeOrderThree.lean:456` | ✅ **:8350** | 高 | 結論が純 mathlib 語彙・仮説も inline ∀。**bespoke 0 に近い理想形**。B.H.Neumann 1956 |
| **Hall–Petresco collection 公式 (一般形)** | `GroupTheory.HallPetresco.exists_hallPetresco` (2-gen 版 `BG.AppE.hallCollection`) | `GroupTheory/HallPetresco.lean:407` | ✅ **:10858** | 高 | **前 note #16 (class≤3 版) を完全に超える** — class 制約なし・任意 G。Mann の証明。前 note が「一般版は sorry・提出不可」としていたのが解消 |
| **Hall 正則 p-群 (class < p ⇒ p 乗が部分群)** | `GroupTheory.pow_mul_eq_one_of_class_lt` | `GroupTheory/RegularPGroup.lean:195` | ✅ **:10861** | 中 | 上の Hall–Petresco の群論的帰結 (BG E.2)。純 mathlib 語彙 |
| **Galois–Burnside** (可解 2-可移群の極小正規部分群は elementary abelian regular) | `GroupTheory.exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive` | `GroupTheory/SolvableTwoTransitive.lean:65` | ❌ 未登録 | 中 | Huppert II Satz 3.2 (issue 9404)。mathlib の `IsMultiplyPretransitive` 語彙 |

**新着の推し**: ZJ 定理は伝説級かつ mathlib/eval 双方に無い → **提案の最有力の一つ** (要 AxiomsCheck 登録 →
提出は本命)。B.H.Neumann 位数 3 は bespoke ほぼ 0 で最も出しやすい。一般 Hall–Petresco は前 note の
class≤3 版を差し替える。

---

## Tier B — Arrives-on-completion (active frontier が閉じると出せる)

現在の 4 active frontier issue を「完成時に submit 可能形になる eval 候補」として評価。
進捗 % は**原文ステップ被覆で測定** (scaffold 数でない)。frontier 判定は敵対的検証済。

### B-1. 🎯 `brauer_suzuki` — **既存 lean-eval 未解決 problem を「解答」できる唯一の frontier**

- **issue [9318](../../issues/9318-brauer-suzuki-theorem.md)** (lane c、2026-07-22 に b→c 移管)。
- **定理**: Brauer–Suzuki (1959)。Sylow-2 が cyclic または一般化四元数 ⟹ `G = O_{2'}(G)·C_G(u)`
  (対合 u の像が G/O_{2'}(G) の中心)。CFSG の礎石補題。Gorenstein *Finite Groups* Ch.12 (例外指標論) 経由。
- **eval 対応**: **既存の未解決 problem `brauer_suzuki` (solver 0) に直接一致**。完成すれば
  **提案でなく「解答」**として出せる = Tier B で唯一、未解決 problem を落とせる本命。
- **進捗 ≈ 38%** (敵対的検証: survey の 33% は Lem 1.6 完成分を含まず conservative 側にずれ):
  cyclic 版は完全証明済 (`brauerSuzuki_of_isCyclic_sylowTwo`, BrauerSuzuki.lean:47)。四元数版は
  Gorenstein Lem 1.2→1.6 まで landing (BrauerSuzukiSetup/Normalizer/TISubset/Character.lean、
  各 0 sorry・全 axiom-clean 登録済)。**最難所 = 例外指標構成 (Lem 1.4–1.5) が既に完了**
  (θ*=1_G+χ₁−χ 分解)。
- **残り**: Lem 1.7 (β(y) 対合対 counting) → (9.4.2) class-sum 構造定数接続 → Lem 1.8–1.9 算術 →
  純群論 endgame (M=⟨対合⟩⊴G, Burnside) → 一般四元数仮説→setup 橋 → top-level 定理組立 →
  消費点 `NearFields.lean:789` (`rankOne_affine_nearField`) の sorry 除去。⚠ Q8 (|S|=8) case は
  Gorenstein 1968 の modular 指標依存で research-adjacent (issue 内 flag)。
- top-level target: `brauerSuzuki` (未作成)。active leaf: `GroupTheory/BrauerSuzukiCharacter.lean`。

### B-2. `feit_sibley_coherence` — Feit–Sibley 定理 (提案候補)

- **issue [1054](../../issues/1054-feit-sibley-theorem-campaign.md)** (lane a、8-step campaign) +
  分割 [0141](../../issues/0141-feitsibley-theorem-split.md)。
- **定理**: Feit–Sibley coherence (Peterfalvi App.IV, pp.145–150)。d odd ⟹ 𝒮 が isometry
  τ=Ind_H^G に関して coherent。奇数位数定理の指標論的証明の coherence keystone。
- **eval 対応**: 既存 problem に無 → **完成時に提案候補**。知名度は Z*/Brauer–Suzuki より niche
  (odd-order 論文の appendix coherence 結果)。statement は honest・非 opaque
  (`IsCoherent` は実 structure、`Hypothesis`/`Sset`/`tau` は実定義)。
- **進捗 ≈ 72–78%** (敵対的検証で survey の 85% を下方修正): 原文 8 ステップ + endgame integrator
  `xset_qder_union_coherent` は全て sorry-free で landing (11 leaf、実 sorry は master 定理の
  **1 個のみ** = FeitSibley.lean:1251)。ただし **8 ステップは master にまだ 1 本も配線されていない**。
- **残り**: (a) full-𝒳 の p-進評価下界 (`hXdiff`) — **issue 自身が「最大未構築」と flag する新 infra**
  (既存 pow 補題は 𝒮(S′)/φ_S-linear のみ被覆) / (b) anchor χ₁ 選択 + keystone 構成 /
  (c) Lemma 1(a) adjoin で 𝒮 全体を閉じる / (d) 外側 4-way case split (d=1 / 2素数 / abelian /
  non-abelian p-group) / (e) statement に `Odd (Nat.card G)` 追加。単なる配線でなく実数学が残る。

### B-3. Suzuki の Zassenhaus 群分類 (Theorem A) — 遠い提案候補

- **issue [2053](../../issues/2053-pf-suzuki-theorem-b.md)** (lane b) は **Theorem B (First Case) のみ**を
  産出。Theorem B は Theorem A への帰納の 1 case (「(B1) ⟹ Theorem A 結論」) で、単独では submit 不可。
- **提出可能な名前付き定理 = Theorem A** (Suzuki 1962 の split rank-1 Zassenhaus / 2-可移群分類:
  奇指数正規 L ≅ PSL(2,q) / Sz(q) / PSU(3,q))。自然な eval id は `suzuki_zassenhaus_classification`。
- **進捗**: Theorem B ≈ 30% (17 step 中 (1)–(6) landing、(7) plan のみ、(8)–(17) 未着手で hard endgame)。
  **Theorem A 全体では ≈ 15–20%** (Ch.I §1–3 done、Ch.II ~30%、Ch.III/IV 未着手、帰納組立 未記述)。
- ⚠ `brauer_suzuki` と混同しない (2053 の step (2) が `rankOne_affine_nearField` 経由で 9318 を上流
  消費するだけ)。⚠ 未解決 infra: step (17) の **Hall–Wielandt transfer 定理 (abelian p>2 版)** は
  M. Hall の教科書が `references/` に無く、要 source 追加。**submittable = far**。

### B-4. Peterfalvi App.III Theorem (e) 前向き — eval 候補で**ない**

- **issue [2052](../../issues/2052-pf-appendix3-e-forward.md)**。type-B ⟺ 同型 summands の完成半分
  (⟸ は 2048 で landing)。statement が repo carrier (`IsomorphicOrderQModuleSplit` 等) に絡む
  内部完全性補題で、**自己完結した有名 statement でない → submittableOnCompletion = false**。
  前提 infra は 100% 揃うが、番号付き結果の完全性のために残すだけ。

---

## Tier C — lean-eval 未解決だが 3 冊経路上に**無い** (自然には来ない)

「3 冊完成で自然に submit 可能」の**対象外**。honest に記録しておく (安易に「近い」と誤認しない)。

| problem | 定理 | 3 冊経路との距離 | 実現可能性 |
|---|---|---|---|
| `glauberman_zStar` | Glauberman Z*-定理 (孤立対合) | **very large**。p=2 の modular 表現論 (Brauer 指標・principal 2-block・Glauberman 対応) が必須で、3 冊はいずれも p-odd/char-0 ordinary 指標論のみ。repo に modular rep theory は**皆無**。同名の `GlaubermanZJ`/`Replacement` は**別定理** (p-odd) で転用不可 | **LOW** |
| `gorenstein_walter` | 二面体 Sylow-2 単純群分類 (A₇ or PSL₂(q)) | **enormous**。Bender method + signalizer functor + Z* が必須 (= Z* に strictly downstream)。repo は building block (PSL₂(q) 単純性・二面体 2-群基礎) のみ持ち、専用機構は無 | **LOWEST** |
| `brauer_splitting_field` | ℚ(ζₙ) は G の分裂体 (RepresentationTheory) | **moderate**。値の半分 (指標値 ∈ ℚ(ζₙ)) は `CyclotomicGaloisAction`/`GaloisCharacter` で**既済** (姉妹問題 `brauer_character_in_cyclotomic` は既に 10 名 solved)。難しい半分 = 実現可能性 (Schur index=1) が **Brauer 誘導定理** + Schur index 降下を要し、FT は Dade isometry/coherence で回避するので**経路上に来ない** | **MEDIUM** (3 問中最良だが off-path) |

`schreier_conjecture` / `five_transitive_card_classification` は CFSG 依存、`higman_infinite_simple` /
`novikov_unsolvable` は組合せ群論で無関係 (前 note どおり着手しない)。

---

## 進捗サマリ (2026-07-22 時点)

| | 件数 | 状態 |
|---|---|---|
| **既提出・solved** | 2 | `feit_thompson` (2026-07-16, #828)、`baer_suzuki` (2026-05-29, #118) |
| **Tier A ready-now** | 34 + 🆕6 | 全て axiom-clean で証明済。**提案 PR を出せば即 submit 可**。うち🆕6 は前 note 後に完成 (ZJ 含む) |
| **Tier B 完成待ち** | 3 (+1 除外) | 9318 BrauerSuzuki ≈38% (**未解決 problem を解答できる本命**) / 1054 FeitSibley ≈75% / 2053 Suzuki-A ≈15–20% (遠) / 2052 は eval 対象外 |
| **Tier C off-path** | 3 | Z* / Gorenstein–Walter / brauer_splitting_field。3 冊完成では自然に来ない |

**「自然に submit できる」の結論**: 3 冊が順調に完成すると自然に出せるのは
**(i) Tier A の提案群 (今すぐ〜)**、**(ii) `brauer_suzuki` の解答 (9318 完成時)**、
**(iii) Feit–Sibley・Suzuki 分類の提案 (1054/2053 完成時)** の 3 経路。
Tier C (Z* 等) は 3 冊の外側にあり、別途 modular 表現論を立てない限り来ない。

---

## 次アクション (issue 0050 に反映)

1. **🆕 ZJ 定理を AxiomsCheck 登録 → 提案 PR の最有力に**。`GlaubermanZJ.lean` を `#print axioms` で
   確定 (未登録)。伝説級・mathlib/eval 双方に無く、`Defs/` 持ち込み前例内。
2. **Tier A 提案 PR**: Jordan (mathlib が proof_wanted) / Chermak–Delgado / Furtwängler /
   Thompson-FPF に加え、**B.H.Neumann 位数 3 (登録済・bespoke ほぼ 0)** と **一般 Hall–Petresco**
   (前 note の class≤3 を差し替え) を追加。提案を先に merge、solver は他者開放 (feit_thompson 前例)。
3. **9318 完走 → `brauer_suzuki` 解答**。Tier B で唯一「未解決 problem を落とす」経路。lane c 継続。
4. **AxiomsCheck 未登録の ready-now を登録** (前 note の課題 + 🆕 ZJ/Replacement/Galois–Burnside)。
5. **前 note §3 の ZJ reject 行を訂正済**とマークする (本 note が上書き)。
