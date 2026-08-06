# main 合流モニター — 運用手順 (2026-07-17 全 3 冊フェーズ監視再開)

> **♻ 2026-07-16 再開準備: 全 3 冊完全形式化フェーズ**。レーン配分の正本 =
> [`lane_reallocation_2026_07_16.md`](lane_reallocation_2026_07_16.md) (a = Isaacs 本文 / b = Ch.8+Suzuki 系 /
> c = Ch.10+BG 残+Pf 残; issue base a=1000/b=2000/c=3000 不変)。scope 正本 =
> [`three_books_full_survey_2026_07_16.md`](three_books_full_survey_2026_07_16.md)。レーン再作成 + cron 再作成は
> 新 note §3。以下の合流ゲート・手順 (build green / AxiomsCheck / --no-ff / 所有検査) は新フェーズでも不変。
>
> **▶▶ 2026-08-07 hub tick — 🎯 Q₈ 完了の後始末: open issue が 0 になった**
> ① **`AxiomsCheck` に Q₈ 下流 6 本を登録** (すべて `all in allowlist`):
> `brauerSuzuki_quaternionSylow_q8` / `RankOneHypothesis.brauerSuzuki` /
> `rankOne_affine_nearField` / `FirstCaseHypothesis.theoremB` /
> `nonempty_theoremAConclusion_of_V_ne_bot` / **`theoremA`** (= Peterfalvi Part II の
> Suzuki Theorem A。`ZassenhausClassification` は axiom でなく明示引数)。
> ② **issue 9506 と pending 2053 を close** ⟹ **open issue = 0 / pending = 4**。
> 2053 の唯一の残タスクが「Q₈ の sorry 経由で AxiomsCheck 登録不可」だったので ① で解消。
> ③ **stale docstring 34 箇所を一括修正** (`Peterfalvi/Appendices/` 配下)。
> 「Inherits the step (2)(b) `sorry` (issue 9318)」型の注記が **AxiomsCheck の新 assert と
> 正面から矛盾**していた (「not axiom-clean」と書いてあるものを axiom-clean と assert)。
> ⟹ 依存関係の記述 (`Depends on step (2)(b)`) に置換。
> ③′ **repo 全体の stale sorry docstring 掃討 (第 2 波、41 file)**。sorry 言及行 399 のうち
> **live sorry を主張していた 45 箇所**を修正。⚠ 見落としやすい 4 型:
> (i) 「still-`sorry` §14 / (still `sorry`) BG §14--§15」= 上流が既に landing 済、
> (ii) 「only remaining `sorry`s are …」= 列挙先が全部 closed (issue 2022/1021 等)、
> (iii) **「not axiom-clean」「inherits `sorryAx`」**= repo に `axiom` 宣言 0 + sorry 0 ⟹
> 全部 axiom-clean なので**定義上ありえない**主張、
> (iv) 「once §14 lands / 埋めた時点で unconditional 化する」= 未来形が既に過去。
> ⟹ 現在形の主張は事実に、設計判断の記録は**過去形に書き換えて残す** (「なぜこの分解に
> なっているか」は今も有用なので削除しない)。`sorry`-free / 「no `sorry` of its own」型は
> 現在も真なので touch しない。
> ⑤ **pending issue 4 件を全部 open へ** (0050 lean-eval / 0140 references submodule /
> 0143 blueprint 逆生成 / 0156 (5.2.d) 一般化)。0050・0143 はユーザー凍結の解除、
> **0140 は hub 推奨のトリガー条件「2053 close 後の quiet window」が成立**、
> 0156 は繰延理由 (「書籍被覆を優先」) が sorry 0 到達で消滅。
> ⟹ **open = 4 / pending = 0 / closed = 563**。
> ④ **README.md / README.ja.md / ROADMAP.md を現況へ**: 「残 `sorry` 1 本」→「sorry-free
> (2026-08-07)」、Navarro を Higman/Huppert と並ぶ**書外原典 3 本目**として追加、
> jobs 4,450→5,450 / files ~1,050→~1,680。⚠ **「sorry 0 ≠ 3 冊完了」を明記** (未形式化の
> 結果は `sorry` を生まない)。
> gate: フルビルド EXIT=0 / **5,446 jobs** / error 0、`bin/count-sorry` = **0**、
> `--strict` EXIT=0。
>
> **▶▶ 2026-07-27 昼〜午後 hub 自走 tick 続き (`/loop` self-pacing) — 🎯🎯🎯
> **Peterfalvi (6.5) を一般 kernel で完成 + (6.6) を step 4 直前まで前進**。push →3111f38a5**。
> (直前 tick の記録は下記。以下はその継続分。)
> ① **(6.5) 一般形 完成** (`S08_SixFiveGeneral.lean` 542 行): (5.3.a) の τ 一般形 /
> 部分族の Hypothesis (5.2) ((5.2.e) は**導出**) / (6.3.b) via (5.7) / (6.5)(a) 指数界+chief
> factor / (6.5)(b) `p` 群 / (6.5)(c) `|L:K| ∤ p−1`。
> ② **(6.6) 一般化 (issue 0155 新設)** (`S08_SixSixGeneral.lean` 500+ 行、step 1-3 完了):
> `𝒳 = 𝒮 − 𝒮(Z)` + (5.2) 一式 / 書籍 p.32 の算術 2 本 / 次数平方和恒等式 /
> 最小次数 base block `𝒮₀` / **τ-general chain fold** / **base coherence** /
> `𝒳`-member の routine facts。
> ③ **実測で分かった重要事実 3 つ** (すべて issue 0155 に記録):
> (i) chain レベルの Dade 依存は**実質ゼロ**だった (`exists_conjugatePairCover` は抽象群の
> 集合の補題、`coherentOfPairChainCover` は元から τ-general)。Sibley の `xChainCoherent` は
> Dade に pin しただけの包装。
> (ii) base coherence 「(1.1)+(1.4)」は一般 `K` では **(5.7) を部分族 `𝒮₀` に当てるだけ**。
> (iii) **書籍 p.32 の可除性論法の数学的中身は既に全部一般**だった — Sibley の step 組立が
> 呼ぶ 4 本 (`degreeDivisibilityInputs_of_commonIndex_primePowerData` /
> `sq_dvd_natDegreeSquareSum_of_commonIndex` /
> `S07.sq_dvd_head_of_commonIndex_primePower_sums` / `natDegreeSquareSum_pos_of_memberFamily`)
> はいずれも**抽象群 + 素の数値データ**で、`hyp` を取るのは最後の梱包 1 本だけ。
> ⟹ **残り step 4 は新規の数学を要さない純粋な再梱包** (`S07.xAdjoinStepW_general` へ)。
> ④ **carrier を書籍準拠に修正**: `InducedFamilyImageData` に **`tau_apply_one`** 追加
> (書籍 (5.2.b) の値域は `ℤ[Irr G, G^#]` = 1 で消える。repo は `ℤ[Irr G]` しか課しておらず
> 弱かった)。§11 Dade witness が `dadeIntegralCharacterMap_apply_one_eq_zero` で discharge。
> ⑤ **lane a を 8 回合流** (Isaacs 6C.2 → Ch.6 演習全 22 問完済 → Ch.7 7A.1/7A.2/7A.3 +
> SL2 root-group 補題 (9211 close))。
> gate: 各 commit でフルビルド green (最終 4842 jobs)、AxiomsCheck **新 assert 計 24 本すべて
> axiom-clean**、`--strict` EXIT=0、`bin/count-sorry` = 1 (凍結 Q₈) 非退行、全 push 済。
> ⚠ 運用メモ: フルビルドが 10 分の Bash 上限を超えるようになったので、
> **`run_in_background` でビルド+lint を 1 本にまとめて回す**運用に切替 (完了通知で gate 判定)。

> **▶▶ 2026-07-27 昼 hub 自走 tick (`/loop` self-pacing, ユーザー「自走してください」) — 🎯🎯
> **Peterfalvi (6.5) を一般 kernel で完成** (a)(b)(c) + stale ラベル訂正 + lane a 2 回合流。
> push →7ab50c06c**。
> ① **stale だった「最大の残債」ラベルを実測で撤回**: survey の「(6.2)–(6.6) の general-(6.1) 形 =
> 最大かつ唯一の深い残債」は **issue 0153/0154 (07-27 早朝 landing) で既に解消済**だった —
> `six_two_of_imageData` / `six_three_of_imageData` が oracle 無しの一般 `K` 版で、`#print axioms`
> 実測で axiom-clean。AxiomsCheck の「(10.10) は sorried ゆえ登録しない」NOTE も 3 点とも stale
> ((10.10) は `no_typeV_maximal_unconditional` で landing 済、`S12.Hypothesis.isTypeIIIorIV` は
> **存在すらしない**) → 撤去して `coprime_card_W1_derived` を登録。
> ② **新 leaf `S08_SixFiveGeneral.lean` (525 行)** で **(6.5) を一般の可解正規 `K` で完成**:
> **(5.3.a) を任意 `τ` で** (`nonempty_characterDifferenceImage_of_irreducible`) / **`𝒮(X)` の
> Hypothesis (5.2)** ((5.2.e) は transport でなく書籍 (5.3.a) の論法で**導出**) / **(6.3.b) via
> (5.7)** (`K/X` 可換 ⟹ 全 member 次数 `|L:K|`) / **(6.5)(a)** 指数界 (= (6.3) の対偶) + chief
> factor / **(6.5)(b)** `p` 群 / **(6.5)(c)** `|L:K| ∤ p−1`。新 assert 9 本すべて axiom-clean。
> ③ **carrier を書籍準拠に修正**: `InducedFamilyImageData` に **`tau_apply_one`** を追加 —
> 書籍 (5.2.b) の値域は `ℤ[Irr G, G^#]` (**1 で消える**) なのに repo は `ℤ[Irr G]` しか課して
> おらず carrier が弱かった。§11 Dade witness (唯一の constructor) は
> `dadeIntegralCharacterMap_apply_one_eq_zero` で discharge。これが無いと (5.3.a) の「2 元の符号が
> **逆**」が出ない (`τ(χ−χ̄) = μ + ν` を排除できない)。
> ④ **lane a を 2 回合流** (19 commits, Isaacs 6C.2 完成 → Ch.6 演習 全 22 問 完済 → Ch.7 着手 7A.1)。
> gate: 各 tick フルビルド green (最終 4838 jobs)、AxiomsCheck OK、`--strict` EXIT=0、
> `bin/count-sorry` = 1 (凍結 Q₈) 非退行、全 push 済。
> **残る Pf 特殊化債務 = (6.6) coherence 半分 1 件**(上流は本 tick で全部そろった; 詳細は survey
> の「(6.5)/(6.6) の general-`K` 化」節)。⚠ 教訓 (2 tick 連続): survey の「最大の残債」ラベルすら
> **1 日で陳腐化する**。着手前に `#print axioms` / grep で実測すること。

> **▶▶ 2026-07-27 朝 hub 自走 tick (`/loop` self-pacing, ユーザー「自走してください」) — 🎯🎯
> Peterfalvi 特殊化債務キャンペーンの棚卸し完了: 残 1 件。push →97dccef9e**。
> ① **実際に一般化した 2 件**: **(6.6) X-characterization** を一般 kernel `K` へ
> (`S08_InducedKernelFamily`, 新 leaf) — Sibley の `SsubFiltration` が `inducedKernelFamily H` と
> 逐語同一なのを使い Sibley 版を特殊化に。⚠ import 方向が逆だったので上流へ prefix-split。
> **`K` の正規性が不要**と判明し書籍 (6.1) より強い。/ **(8.18.c)** を型 I-or-II ペアへ — 型 I 限定
> だったのは `A₁(S)` 非空性を `TypeFData.H_nontrivial` から取っていた **1 箇所だけ**で、任意の極大
> 部分群で成立する `Msigma_ne_bot` に置換すれば型 II も通る。
> ② **stale ラベル 9 件を実測で訂正**: (2.6)-(2.10.3) の `hconj` threading (**binder ゼロ**、名指しの
> `S04_InduceConjFinset.lean` には出現すらしない) / (8.15) (claim 1 の `A₁` 節と claim 3 が既に型
> uniform、`A₀`/`A` が型ごとなのは**台集合の定義がそうだから**で債務でない) / (8.18)(a)(b) (元から型
> generic) / (9.7)(b) (`caseB_exists_galoisField_repr_withAut` が**書籍の三層同型そのもの**) /
> (9.11) (`S11.nineEleven_coherent_A0` が Hypothesis (9.2) 上の generic 宣言、型仮説なし) /
> (13.8) (書籍逐語の **S 側** `eta01_Hsharp_norm_lower_core` が在る) + (7.8)/(10.11)/(11.8) の
> 相互参照張り。⟹ **残る Pf 特殊化債務は (6.4)/(6.6) coherence 半分 1 件だけ** (規模 L で繰延)。
> ③ **見せかけ opaque scaffold を 2 件除去**: `CliffordCaseBData.field_model` (唯一の producer が
> `True`、消費者ゼロ; 削除で構造体が `Prop` に落ち linter が `def`→`theorem` を要求 = その Prop
> フィールドだけが「データ」を装っていた証拠) / `OddOrderSpecialization` (消費者ゼロ、書籍の
> 「K/M nilpotent」を自由 Prop に潰していた)。
> ④ **lane a を 2 回合流** (計 79 commits, Isaacs Problems 5C/5D/5E/6A/6B/6C)。
> gate: 各 tick でフルビルド green (最終 4835 jobs)、AxiomsCheck OK (新 assert 計 12 本)、
> `--strict` 警告ゼロ、sorry census 1 (凍結 Q₈) 非退行、全 push 済。
> ⚠ 教訓: survey の未/部分/特殊化ラベルは **2026-07-16 の一度きりのスナップショット**で、
> 実測 25 件中 **9 件が陳腐化**していた。着手前の実測が必須。

> **▶▶ 2026-07-27 早朝 hub 直接作業 tick (「直近の作業から再開」) — 🎯 issue 0154 完済: 加重 (5.6) と
> (6.2)/(6.3) の Dade 依存を完全除去 + lane a 合流。push →756b18f7a**。
> ① **加重 (5.6) engine の τ 一般化** (`59defaf9b`, `c00ca1fd7`): 新 leaf `S08_GeneralAdjoinWeighted`。
> Dade を真に使う helper は実測 **4 つだけ**で、`crux1_of_memberFamilyW` に至っては `hyp`/`_hτ` を
> 証明本体で一度も使っていなかった。可約 break `xAdjoinStepW_k_general` と既約 break
> `xAdjoinStepW_general` + 各対偶を新設し、Dade 版 4 本は `Samb = univ` 特殊化に置換
> (`mem_zSupportedSpan_univ_iff` — Dade は「全 A₀-supported 関数」上の等長なのでこれが正しい)。
> ② **break chain + (6.2)/(6.3)** (`572b9368a`): `S08_SixTwoGeneral` の Dade 依存も実測 **2 箇所だけ**
> (加重 engine 呼び出しと `dadeIntegralCharacterMap_mem_ZIrr_of_supported`)。3 本を `_general` 化。
> `InducedFamilyImageData` は引数を `(hyp) (K)` → `(A₀ : Set ↥L) (K)` に変え **(5.2.b) を 3 フィールド**
> (`tau`/`tau_isometry`/`tau_mem_ZIrr` = 書籍の値域 `ℤ[Irr G, G^#]` 節) で担う。⟹ Dade は bundle の
> **witness の一つ**に降りた。§11/§13/§15 consumer は無変更。
> ③ **付帯: (11.4) 付け替え** (`1565698cd`): `sixTwo_of_hypothesis` 経由に変え、producer 用に担いで
> いた**型仮説 `IsTypeIII ∨ IsTypeIV` を除去** (`≠ ⊤` → `< M'` は `Subgroup.subgroupOf_eq_top` で変換)。
> ④ **lane a 合流** (40 commits, Isaacs Problems 5C/5D/5E/6A) — ⚠ **合流固有の破綻を gate が検出**:
> `Problems6A2`/`Problems6A3` が同 namespace で無名 `instance : Fact (Nat.Prime n)` を宣言し、
> Lean の自動命名が両方 `instFactPrimeOfNatNat_oddOrder` になって root import が
> `environment already contains` で失敗。leaf 単体では出ない。明示名を付けて解消 (`756b18f7a`)。
> **教訓: 兄弟 leaf が同 namespace で同型の無名 instance を宣言してはいけない** (無名 instance の
> 自動名は型の shape だけで決まり、数値リテラルで区別されない)。
> gate: フルビルド green (4820 jobs)、AxiomsCheck OK (**一般形 9 本を新規登録**、全て axiom-clean)、
> `--strict` EXIT=0、sorry census 1 (凍結 Q₈) 非退行、全 push 済。
> issue: 0154 close。lane b/c/d: 変化なし。

> **▶▶ 2026-07-24 夜 hub tick #6 (区切り) — 🎯 App III Prop 1 完成 + Lemma 1(c)(d) 完成 = Lemma 1 全完了。push →a5d9a44b6**。
> ① **Prop 1 後半** (`ff4f5d9d5`): conj = `AdjoinRoot.liftAlgHom` + `AlgEquiv.ofAlgHom` 自己合成
> (有限次元論法・field instance 不要) / `equivProd` (powerBasis' reindex + finTwoArrow) /
> **norm 恒等式 `mul_conj`** (`linear_combination B²·alpha_sq + add_self(…)` — char-2 の 2t=0 を
> 項として渡す) / `isField`。AxiomsCheck 5 assert。
> ② **Lemma 1(c)** (`b20d35942`): 新 leaf `GroupTheory/CentralExtensionAutomorphisms.lean` —
> `twistCoords` で端群 reindex → 同一 square map に還元して既存 `equivOfCommonSquareMap` を cite
> (書籍の基底持ち上げ再実装不要)。necessity は square 座標直計算。AxiomsCheck 2 assert。
> ③ **Lemma 1(d)** (`a5d9a44b6`): 同 leaf — deviation Φe·e⁻¹ の座標化で
> `inducingIdAutsEquivHom : Multiplicative (V →+ W) ≃* inducingIdAuts` +
> `isElementaryAbelian_inducingIdAuts` (= Prop 2 kernel 部の一般核)。AxiomsCheck 2 assert。
> ④ Prop 2 は **6 段分解を issue 0148 に記録** ((i)(ii) 完了)。**(iii) 誘導写像機構は WIP**:
> `Suzuki2Groups/AutomorphismInducedMaps.lean` が worktree に **untracked 未 commit** (main は
> green のまま)。残エラー 4 種の診断と修正手順は 0148 (iii) 項に精密記録済み — 次セッションは
> そこから再開。⚠ 教訓: **Lean 4 の section 変数は proof 内のみの使用だと `include` 必須**
> (statement に現れない hypothesis 変数は Unknown identifier になる; defs は include 前に置く)。
> gate: 3 commit とも leaf+AxiomsCheck green・新 assert 9 本 axiom-clean・`--strict` EXIT=0・
> census 1 (凍結 Q₈) 非退行・全 push 済み。lane a/b/c: 変化なし (a/b 凍結 hub 再割当待ち、c 完済)。
>
> **▶▶ 2026-07-24 深夜 hub tick #5 (区切り) — App III Lemma 2(c) + Prop 1 前半で session close。push →d0c81638b**。
> Lemma 2(c) 独立性 2 定理 (coeff_symm/diag_eq_zero、Pi 空間+Frobenius 全射) と Prop 1 前半
> (新 leaf `Suzuki2Groups/FieldModel.lean`: X²+εX+1 既約 from anisotropy、AdjoinRoot model +
> alpha_sq/aeval_conj_root、hub 配線済) を landing。gate green・census 1 非退行・全 push 済。
> **次セッションの frontier = 0148**: Prop 1 後半 (conj AlgEquiv → (F×F)≃ₗK → norm 恒等式) →
> Prop 2 → 2052。手順・mathlib 部品名・instance の罠は全て 0148 に精密記録済み。
> lane a/b/c: a/b は campaign 凍結中で hub 再割当待ち、c は Q₈ 凍結+territory 完済 (変化なし)。
>
> **▶▶ 2026-07-24 夜 hub 直接作業 tick #4 (「続けてください」) — 🎯 App III Lemma 2(b)(c) 完成 = Lemma 1+2 独立性側 全完了。push →45bed1296**。
> ① **Lemma 2(b)**: `algAutMulBilin` + 独立性 (積 monoid F×F の Dedekind 指標に帰着 — 書籍の
> 二重和不要) + dim n² + card 補題。bundled Basis は入れ子 `F →ₗ F →ₗ F` の instance isDefEq
> 発散で繰延 (diagnostics 付きで 0148 記録; span 版も同根)。
> ② **Lemma 2(c)** (char 2 特有): `autMulQuadraticMap` + `coeff_symm` (polar 化 + swap 再指数 +
> Pi 空間の指標独立) + `diag_eq_zero` (swap involution 打ち消し + Frobenius 全射で (a) 帰着)。
> ordered-pair 供述で Sym2 index を回避。
> ③ 教訓 2 件: (i) 入れ子 LinearMap 空間の module instance は ext/評価/map'/ker_eq_bot 全て
> isDefEq 爆発 — **関数空間 (Pi)+MonoidHom 指標側で証明を組む** (今回 3 回張り直して確立)。
> (ii) `lake env lean f | head; echo $?` は **head の exit code** を拾う偽装 green — 判定は
> エラー行の有無 + 最終 lake build で。⚠ 途中 1 commit を gate 赤 (longLine 1 件) のまま
> `;`-連結ミスで push → 即 follow-up 修正 (`f5b4bde7f`)、以後 `&&` 徹底。
> gate: leaf + AxiomsCheck (4604 jobs) green ×2、`--strict` EXIT=0、AxiomsCheck 新 assert 4 本
> axiom-clean、census 1 非退行。残 (0148): Prop 1 (B(n,1,ε) field model) → Prop 2 (Aut) → 2052。
>
> **▶▶ 2026-07-24 夕 hub 直接作業 tick #3 (「gate green のあと進めて」) — 🎯 App III 実数学に着手: Lemma 1(a) + Lemma 2(a) 完成。push →6e3563335**。
> ① 0149 続き: S04g_Thm418 prefix-split (1965 → Core 958 + 残 1008、消化 2 件目) / 9130 close
> (補題 trio 集約: Ch03 重複削除 + singleton 版の系化)。ユーザー裁定で 0050/0143/1055/2053 凍結
> (lane a/b の次 frontier は hub 再割当待ち)。
> ② **App III Lemma 1(a)** (`QuadraticExtensions.lean`): centralSquare の descend +
> centralCommPairing を **polarization として定義** (well-definedness 証明を構造的に回避) +
> `centralSquareQuadraticMap` (QuadraticMap (ZMod 2) bundle)。P 2-group 仮定は不要なので一般形。
> 知見: `IsMulCommutative.instCommGroup` は scoped — letI 連鎖前に `open scoped IsMulCommutative`。
> ③ **App III Lemma 2(a)** (`SemilinearFieldAut.lean`): Dedekind 独立の転送 + dim 勘定で
> `algAutLinearBasis : Basis (F ≃ₐ[ZMod p] F) F (F →ₗ[ZMod p] F)` (一般標数)。
> gate: 各 commit を leaf+AxiomsCheck (4604 jobs ≈ full) で検証 → `--strict` replay EXIT=0 ×2、
> AxiomsCheck 新 assert 3 本 (centralSquareQuadraticMap / centralCommPairing_mk /
> algAutLinearBasis) 全て axiom-clean。census 1 (凍結 Q₈) 非退行。
> 残 (0148): Lemma 2(b)(c) → Prop 1 → Prop 2、+2052 (e)⟹。手順・部品は 0148 に精密記録済み。
>
> **▶▶ 2026-07-24 午後 hub 直接作業 tick #2 (ユーザー指示「issue を片付ける」+「mathlib 基準で分割」+ 凍結 3 件) — 🎯 longFile 1500 移行 + issue 大量処理。push c5ffbeaf5→6c9928daa (8 commits)**。
> ① **longFile 1500 移行 (0149 新設)**: lakefile を mathlib 素の 1500 に切替、超過 58 file へ
> per-file stamp (candidate−100)。罠 3 件を実測で踏んで解決: stamp は module docstring 後
> (import 直後だと style.header 違反) / docstring 本文の「import …」行を import 文と誤認 /
> linter の行数 = wc+1 (境界 wc1499-1500 の 2 file)。
> ② **分割 1 件目**: FeitSibleyTheorem 1884 → SsetCoherence 892 + 残 1022 (`end Hypothesis`
> 凍結境界 prefix-split、下流無変更、0141 close)。
> ③ **dedup 3 波**: 0127① (cyclic unique-order-2 → CyclicSubgroupUniqueness / mul_right →
> BaerTrick repoint) / 9164 (toAlgAut ×2 → 共有 ringAutMulEquivAlgAut) / 9159
> (`Subgroup.IsPiGroup` を IsPiSubgroup の reducible alias 化 — silent defeq 依存を公式化)。
> ④ 0136② (AppD (D.2) の hne 削除を書籍照合+docstring 注記で仕上げ) / 0139 (notes/meta
> 正本/ログ分離: log/ へ 25 file + merge_monitor 437KB→93KB 分割 + README index + survey 降格ヘッダ)。
> ⑤ **ユーザー裁定の凍結 3 件**: 0143 blueprint / 1055 lane-a Isaacs Problems / 2053 lane-b
> Theorem B → pending/ (lane a/b の次 frontier は hub 再割当待ち、memory 反映済)。
> issue 収支: **close 16** (0006/0123/0124/0127/0129/0133/0136/0138/0139/0141/0144/0145/0146/
> 3029/9159/9164) + freeze 3 + 注記 4 (9130/0132/0149/2052 系)。残 open 6。
> gate: **単独走行 full build + `--strict` EXIT=0** (12m27s、非 sorry 警告 0) + AxiomsCheck
> green (closure 内) + census 1 (凍結 Q₈) 非退行。⚠ 教訓 2 件: (i) 同一 worktree で gate 走行中に
> 自分の leaf build を打つと olean race で gate が偽 fail する (1 回踏んで gate 再走) —
> **gate は単独走行、編集/leaf build は gate の合間に batch**。(ii) fresh cold-graph の lake は
> ごく稀に scheduling race で「Main.olean 無し」fail する (再現せず、要 watch)。
>
> **▶▶ 2026-07-24 1x:xx hub 直接作業 tick (ユーザー指示「lint fix をここで一気に進めます」) — 🎯 lint backlog 47→0 完済 + gate --strict 切替 + issue 監査**。
> ① lint: 残 47 件 (show 31 / sectionVars 8 / Fintype 2 / longLine 2 / flexible 1 / simpa 1 /
> unusedVars 1) を一括解消 (`e6fc21830`)。omit cascade 3 件 (CaseSplitBCD→Classification) を
> fixpoint まで追跡。flexible の linter Try-this が不完全 (omegaProdChar unfold 欠落 → instance
> stuck) だったため実 `simp?` で closed set を取り直した (新知見、CLAUDE.md に記載)。
> ② gate: baseline 空化 + CI `--strict` 切替 + CLAUDE.md/lint_gate note 更新。0138 完了 close
> (0123 統合)、per-lane 0144/0145/0146 close、0133 close (c 完了済)。
> ③ issue 監査 (ユーザー質問起点、open 17 + pending 6 全数): **close 3 件** = 0006 (Tier 2 は
> 実装済みの stale pending) / 3029 (Ch07 stale docstring 3 サイトを on-sight 修正) / 上記 lint 系。
> **注記 4 件** = 0127 (残 = ① dedup 2 件のみ、②③完了) / 9164 (共有 bridge landing 済・差し替え未
> + Higman に同名 private 複製 +1) / 2053 (checklist 遅行: StepNine/Ten 存在・FirstCase sorry 0) /
> 0141 (a の campaign 完了で blocker 解除、分割実施可)。0132 は per-decl 例外化済みを注記。
> gate: **fresh 単発 full build (`rm -rf .lake/build`) + `bin/check-warnings --strict` EXIT=0**
> (16m35s、非 sorry 警告 0)。実 sorry 1 (凍結 Q₈) 非退行。⚠ fresh cold-graph 1 回目に
> Theorem152Assembly が Ch07 Main.olean 未生成で transient fail — 再実行で再現せず (要 watch)。
>
> **▶▶ 2026-07-24 11:xx hub 直接作業セッション (ユーザー裁定「レーンに分配せず hub で b→a→c タスクを閉じる」) — 🎯🎯 残 6 sorry の考察と一括処理。実 sorry 6→1 (残 = 凍結 Q₈ のみ)**。
> 内訳: ① Suzuki2Groups.lean の空 scaffold 4 本削除 (`3adbd2df8`, 0127 ② 実施; honest 残作業 =
> **issue 0148**) ② Aut(Q₈) odd bound 新 leaf `GroupTheory/SpecificGroups/QuaternionGroupMulAut`
> (`30fbf39e1`) ③ near-field units ≅ Q₈ 新 leaf `Appendices/NearFieldUnitsQuaternion` (`9f2a052c0`)
> ④ **StepSix `card_D_le_three_of_noncomm` 実証明 = Pf II Ch.II step (6) 完成** (`f76f13fea`,
> AxiomsCheck 部品 7 本登録; 組み上げ 2 本は step(5)→(4)→(2)(b) 経由で凍結 Q₈ を継承ゆえ意図的未登録)
> ⑤ **凍結 sorry を `brauerSuzuki_quaternionSylow_q8` に単離** (`cbe793db7`): |T|≥16 の
> QuaternionSylowSetup 組み立て + t=z + C₄ 吸収を実証明し、凍結面 = Q₈ statement そのものに縮小
> (0147/project note の参照更新済 `9ed3b437b`)。9501 は superseded で closed。
> gate: full build **4648 jobs EXIT=0** (42s 増分) + AxiomsCheck OK + check-warnings ratchet OK
> (46 ≤ baseline 47) + census 1。⚠ 教訓再演: AxiomsCheck build を `| tail` で確認して偽 green を
> 1 回踏んだ (既知の EXIT 隠蔽罠) — `> log; echo EXIT=$?` で再検証して捕捉、amend 修正済。
> **⚠ 全 4 branch は ahead=0 だったが、lane b の worktree に 02:07 以降 7.5h 放置の未コミット成果**
> (新 leaf `Higman/Suzuki2Groups/ExponentFour.lean` 153 行 + aggregator 配線 + AxiomsCheck 6 assert +
> Pf StepFive の consumer 差し替え) を検出 — b の session が mid-turn で落ちて stranded になっていた。
> hub が read-only 検証 (sorry-free・leaf build green 4468 jobs) の上で **b の branch に b 名義で commit
> (`bcf5dbfa2`) → `--no-ff` 合流**。CLAUDE.md「レーンの genuine output は無駄にしない」に沿った救出であり、
> 破棄・作り直しはしていない。
> 合流 b (**Higman Suzuki 2-groups, Theorem 1(a) = exponent 4、sorry-free・axiom-clean**): 任意の
> `ZMod 2`-quadratic central extension で平方が elementary abelian kernel に落ちる (`x^4 = 1`) を証明し、
> honest type-A/B/C/D model equivalence 経由で transport → 前 tick の分類定理
> (`higmanClassification_of_isSuzuki2Group`) と合成して `pow_four_eq_one_of_isSuzuki2Group`。
> **🎯 実 sorry 削減**: Pf `Appendices/Suzuki/FirstCase/StepFive.lean` の sorried-cite
> `pow_four_eq_one_of_isSuzuki2Group` (issue 2053) を**削除して実証明を cite** — 7→6。
> **gate: green 4646 jobs (前 4645 +1 = ExponentFour.lean ちょうど・orphan 0) / AxiomsCheck OK (3765 assert
> 全通過・failure 0、新 assert 6 本 pow_four_eq_one_of_isType{A,B,C,D}/higmanType/isSuzuki2Group が全て
> 3 axiom allowlist のみ = axiom-clean) / 実 sorry 7→**6** (退行なし・純減) / lint 46 ≤ 47 baseline /
> push 771d421fc→(本 tick)**。範囲逸脱なし。build wall 1:03。
> ℹ **レーン稼働状況**: a/c/d は 2026-07-23 20:3x のユーザー指示で凍結継続 (ahead=0・clean)。b も
> 02:07 以降 file mtime 更新なし = session 停止中 (本 tick は hub 単独操作、cron は動かしていない)。
> 残 実 sorry 6 = Pf Appendices/Suzuki2Groups.lean 4 (`higman_classification` 他、c territory・c 凍結中) +
> RankOneAffineModel 1 (Q₈ 凍結 = issue 0147) + StepSix 1 (同 9318/Q₈ 系)。
>
> **▶▶ 2026-07-24 02:1x 監視 tick (B 単独) — 🎯🎯 b (Higman Suzuki 2-group classification = Lemma 13 完成) 合流**。b=1(flagship)。
> 合流 b (**Higman Lemma 13 + Theorem 1 = Suzuki 2-group classification 完成、sorry-free・axiom-clean**): ξ-length bound が length≥4 chain を排除 → center chain が各 Suzuki 2-group を honest type-A/B/C/D model へ dispatch。新 leaf Classification.lean (higmanClassification + higmanClassification_of_isSuzuki2Group、Suzuki2Groups.lean:37 aggregator 経由 WIRED)。exponent-two (ExponentTwoContradiction) + exponent-four (ExponentFourContradiction) の両分岐がこの上位定理で統合。
> **gate: green 4645 jobs (前 4644 +1 = Classification.lean・orphan 0) / AxiomsCheck OK (新 assert 3 本 higmanLemmaThirteen/higmanClassification/higmanClassification_of_isSuzuki2Group 全通過 = axiom-clean 検証、assert failure 0) / 実 sorry 7→7 非退行 / lint 46 ≤ 47 baseline / push fca642b73→1ab3fd126**。範囲逸脱なし。build wall 1:11。
> 🎯🎯 **Higman Lemma 13 完成**。約 9 tick (~3h) で b が exponent-two/four 両分岐 (~47 leaf) を積み上げ最上位分類へ統合。これは Pf App Suzuki appendix の `higman_classification` gated sorry (Suzuki2Groups.lean:76、c territory) を解消する上流だが、c は凍結中ゆえ下流接続は保留 (凍結解除時に c が接続可能)。b の次は Higman 系の残り (Lemma 12 系・他 Suzuki 定理) or Theorem 完成の見込み。
>
> **▶▶ 2026-07-24 01:4x 監視 tick (B 単独) — b (Higman 🎯exponent-two contradiction 統合 + ξ-length bound 5 leaf) 合流**。b=6。
> 合流 b (**Higman L13 主要マイルストーン**): exponent-two length-four branch close / length-four descent 準備 / exact ξ-length four 排除 / longer ξ-chain descend / **ξ-length bound 証明**。5 新 leaf: **ExponentTwoContradiction** (exponent-two 分岐を統合して閉じる、ExponentFourContradiction と対) / **LengthBound** (ξ-length bound = Higman 分類の中核) / LengthFourContradiction / LengthFourDescent / LengthFourProperDescent。全 WIRED。
> **gate: green 4644 jobs (前 4639 +5 = b の 5 leaf・orphan 0) / AxiomsCheck OK / 実 sorry 7→7 非退行 / lint 46 ≤ 47 baseline / push 7643a2723→a192c296a**。範囲逸脱なし。build wall 1:52。
> 🎯 **exponent-two 分岐が ExponentTwoContradiction で統合完了**。exponent-four (ExponentFourContradiction) と併せ、Higman L13 の両 exponent 分岐が閉じた。次は ξ-length bound を用いた上位統合 (Lemma 13 本体) の見込み。
>
> **▶▶ 2026-07-24 01:1x 監視 tick (B 単独) — b (Higman aligned+all-isomorphic parameter branches close 7 leaf) 合流**。b=8。
> 合流 b (**Higman L13 exponent-two 分岐を集中 close**): three-term graph factor lift / all-isomorphic ambient bracket 消去 / first aligned parameter branch close / graph eigen seed→contradiction / all-isomorphic graph preimage 組立 / aligned parameter branches 全 close / all-isomorphic parameter branch close。7 新 leaf (ThreeTermGraphPreimage / AllIsomorphicAmbientCancellation / FirstAlignedParameterBranch / AllIsomorphicInvariantContradiction / AllIsomorphicGraphPreimage / AlignedParameterBranches / AllIsomorphicParameterBranch) 全 WIRED。既存 PairwiseJoinInfrastructure 更新。
> **gate: green 4639 jobs (前 4632 +7 = b の 7 leaf・orphan 0) / AxiomsCheck OK / 実 sorry 7→7 非退行 / lint 46 ≤ 47 baseline / push 4e8ab2d3e→33f645926**。範囲逸脱なし。build wall 1:29。
>
>
> 📜 **これより古い tick は [`log/merge_monitor_ticks.md`](log/merge_monitor_ticks.md) へ退避** (0139、2026-07-24)。

## レーン (2026-07-17〜 current: a/b/c の 3 レーン)

正本 = [`lane_reallocation_2026_07_16.md`](lane_reallocation_2026_07_16.md) + 本ファイル冒頭
(2026-07-17 / 07-19 更新) の `a_re` / `b_re` / `c_re` / `shared_re`。

| lane | branch | worktree | 現行役割 | 所有 (step 1.5 range-check の正) | issue base |
|---|---|---|---|---|---|
| **a** | `a` | `/home/ywr/odd-order-a` | Isaacs 本文 + Peterfalvi 本文 (2026-07-19 11:29 復帰、9154 の恒久配分) | `^OddOrder/Isaacs/\|^OddOrder/Peterfalvi/S` | 1000 |
| **b** | `b` | `/home/ywr/odd-order-b` | Suzuki 系 + 引用元 Higman 原典 (frontier = issue 2048) | `^OddOrder/Higman/\|^OddOrder/GroupTheory/SpecificGroups/Suzuki2Group/\|^OddOrder/Peterfalvi/Appendices/(Suzuki\|Suzuki2Groups)` | 2000 |
| **c** | `c` | `/home/ywr/odd-order-c` | BG 残 + Pf Appendices の非 Suzuki 系 (issue 0126 / 9132 / 9133) | `^OddOrder/BG/\|^OddOrder/Peterfalvi/Appendices/(NearFields\|Huppert\|SemilinearField\|FeitSibley)` | 3000 |
| ~~**d**~~ | — | — | ⚰ 退役 (2026-07-07) | — | (4000) |

> **✅ 2026-07-19 lane b Higman 継続・module 境界 (ユーザー裁定)**: b は再配分せず
> Higman 原典を完遂する。source-neutral な Suzuki 2-group 基本定義は `OddOrder/GroupTheory/SpecificGroups/Suzuki2Group/**`、
> 原典 Lemmas 1--13 は `OddOrder/Higman/Suzuki2Groups/**`、Peterfalvi Appendix III の再掲・適用は
> `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/**`。詳細と未了dedupは issue 0127。

branch/worktree audit は `a` / `b` / `c` と `main` の **4 本**。
⚠ 2026-07-15 の「A単独 / audit は a と main のみ」体制は**失効** (2026-07-16 レーン再作成)。
以下の旧 a/b/c/d 記述と 🔒 所有マップは FT endgame の裁定履歴としてのみ保存し、
現行 ownership/range-check には使わない。

> 旧クラスタ記述 (2026-07-04/07-07 再々編) は git 履歴参照。**再設計の正本 = `issues/closed/0118`** +
> `ft_lane_reallocation_2026_06_28.md`「3 レーン再設計 (2026-07-15)」節。

> **🤖 lane c = codex 5.6 (GPT-5.6) 運用 (2026-07-10, ユーザー裁定, issue 0105)**: lane c の operator を
> Claude から codex 5.6 に切替 (trial)。**所有・issue base (3000)・合流ゲートは不変** (build green /
> AxiomsCheck / sorry regression / 範囲逸脱チェックはモデル非依存)。handoff・kickoff prompt の正本 =
> [`lane_c_codex_handoff_2026_07_10.md`](log/lane_c_codex_handoff_2026_07_10.md)。旧 lane d 再活性化トリガー (i)
> 「S-side landing → T-side mirror」は 8ff313b1 で成立したが、d 再作成でなく c の operator 切替で対応
> (T-side mirror = c territory)。**hub 追加チェック (最初の ~5 tick 重点)**: c の合流 tick で
> `git diff main...c -- '*.lean' | grep -E '^\+\s*(theorem|lemma|def) '` の新規宣言に対し既存 API との
> dup を spot-grep (旧 lane d の失敗モード = 既存 S01/GroupTheory 補題の複製 churn)。**dup 主体の tick は
> merge せず abort** + issue 0105 に記録 + notes/issue で c に de-dup (cite 置換) を差し戻す — これは
> ⛔ STOP でなく**通常継続** (ループは止めない、ユーザー escalation 不要)。数 tick (~2 日) で
> keep / swap-back を hub が裁定 (評価軸 = genuine landing、sorry 数でない)。裁定は issue 0105 に記録。

> **⚰ 2026-07-07 — lane d (codex) 退役 (ユーザー裁定)**: 徹底調査で **FT frontier (Peterfalvi 72 + BG 15 実 sorry) に codex 単独で閉じられる genuine・on-path・非衝突・非gated な実 sorry は存在しない**と確定 (Peterfalvi=全て gated/深いchar/a-b-c衝突/偽/off-path; BG 非b分=AppD/AppE 全て consumer 0・unimported の off-path scaffold)。構造的理由: FT 残 frontier は深く密結合な char/local-analysis で「切り出せる mechanical leaf」がほぼ無く、codex に軽タスクを与えると dup relocation の churn に流れる (直近 2 tick = 計 14 補題が全て既存 S01 補題の複製、net-genuine 0)。⟹ 3 レーン (a/b/c) に集約。worktree `/home/ywr/odd-order-d` + branch `d` 削除 (churn は net-zero、reflog 復元可)。**♻ 再活性化トリガー (将来)**: (i) proven S-side の **T-side dual** (`V_inf_centralizer_Q_eq_bot` 等) の gate ((14.9) T-typeII 構造) が a/b で landing → codex が template を mirror; (ii) a/b/c が特定 group-theory helper を明示 pull-request。いずれか発生時に `git worktree add /home/ywr/odd-order-d -b d` で再作成 (issue base 4000)。**⚠ ユーザーは codex の /loop セッションを停止すること** (worktree 消失後は codex が git エラーで空転)。

> **⏸ SUPERSEDED→temporary-hold (2026-07-09, issue 9077 HUB RULING #2)**: 下記 (B) の 9078 は **完遂**
> (`SemilinearFieldModel.lean` leaf + T-side `tFieldModelData_of_repr` producer、全 sorry-free、`t_side_frobenius_kernel`
> 構造 discharge)。c は独立 frontier 再枯渇を surface → hub が **3-probe workflow (wf_52474eb0、high-conf)** で裁定 =
> **(A-mod) temporary-hold**。全 probe が「c-buildable ungated non-dup target 無し」を確認: 残 gate (V_inf/13.15 =
> b の active (13.4) `lambda_forces_T_caseB` / t_side field-data = a の active 9000 char body) は全て他レーンの
> **ACTIVE work で降りると policy-8 dup** (9013 案 B は却下済)、GroupTheory/Mathlib shared-infra は real sorry 0。
> c は全 non-dup slice を sorried-cite endpoint 化済 ⟹ **gated-endpoint pattern で self-resume 待機** (lazy idle でない、
> 2026-07-06 DORMANT とは別)。**hub フォロー: a の 9000 / b の (13.4) landing 監視 → landing tick で 9077 に「c 再 engage 可」flag**。詳細 = 9077 RULING #2。
>
> **♻♻ RE-CONFIRMED (2026-07-08, issue 9077 HUB RULING (B))**: lane c が「S16 全 13 sorry は a/b gated、
> 独立 frontier 枯渇」を全数検証で surface (ユーザー「ハブに聞くべき」)。hub が subagent 調査+自己検証で裁定 =
> **c は DORMANT でなく `SemilinearFieldModel.lean` shared leaf + T-side `TFieldModelData` producer を build**
> (= 0098 item 2 の再活性、genuine 未着手 gap、a の Singer と cleanly-separable = dup でない、a は未着手で
> `main..a`=0)。着手 claim = **issue 9078** 起票済。gated-endpoint skeleton パターン (V-abelian を hypothesis 化)。
> 分担境界: c=field-model realization (a の Singer cite) / a=§9 block-decomp + (11.9) char body。詳細 = 9077/9078。
>
> **♻ SUPERSEDED (2026-07-07, issue 0098)**: 下記 DORMANT 化は解除 — 4-agent 再調査 (wf_d4994964) で
> ungated genuine work 5 件 (typeP_pair port / semilinear field-model leaf / βₛ bridge carve-out / §14 Γ-assembly /
> hcard2 verify) を確定し c を REACTIVATE。9013 item (i) mᵀ は c へ de-scope。9000 claim は a 保持 (scope 注記済)。
>
> **⚠ 2026-07-06 夕 — lane c DORMANT cite-sink 化 (hub 裁定, 4-agent 調査 wf_00a0db07)**: c の S16 領域は枯渇
> (0 ahead、S16_NonExistenceG の 10 bare sorry は**全て true carrier gate** = a の typeP_Galois (9000) or b の
> §13/§15/§16 char cascade に gated、sorried-cite assemblable はゼロ; Clifford 9002 完了; reconciled_typePData_T
> は U-side 済・残 W2_le/centralizer_W1 = b territory)。ungated 行き先も無し (shared leaf 全 sorry-free、d が
> shared-infra slot を占有)。⟹ 07-02 教訓どおり **c を DORMANT cite-sink 化** (idle lane を busywork させない)。
> **reactivation trigger** (いずれか landing で c 自動再開 → S16 W-side norm cascade + parity 矛盾を assemble):
> **a: typeP_Galois (9000, root gate)** / **b: §13 v-value lower-bound export (9013) / §15-16 W-factor σ-structure
> (9017) / S-T partner parity (3002)**。c の成果は全 in-place 保全 (revert しない)。⚠ **b は依然 OVERLOADED** ゆえ
> a が 9000 を landing 後に b→c 再配分の余地を再検討。
>
> 例外・共有・凍結の正確な判定は下の 🔒 所有マップが正。**lane d は 2026-07-06 復活** (2026-07-02〜07-06 退役、
旧 branch `d` は削除済ゆえ `git worktree add /home/ywr/odd-order-d -b d` で新規作成)。**d = codex 運用**の
最軽量レーンとして復活した 9006 Hall-lemma relocation は完了済み (closed/9006)。続く 9007 induced-conjugation
hoist も完了済み (closed/9007)。2026-07-06 lane-d audit では shared foundation
(`OddOrder/GroupTheory/**`, `OddOrder/Mathlib/**`, `OddOrder/Algebra/**`, `OddOrder/Isaacs/**`) に bare
`sorry` は無く、残る bare `sorry` は a/b/c 所有の Peterfalvi frontier に集中している。従って d は新しい
open shared claim が立つまで **issue/notes hygiene + open-9000 scan** に限定し、Peterfalvi/BG S-file へは
新 carve-out なしで入らない。

> **♻ 2026-07-06 夕 — lane d DORMANT→再活性化 (hub 裁定)**: DORMANT 化後、d は 4 tick 連続で **genuine な
> shared 群論 API を sorry-free additive に生産** (claim 9018-9031: normal Hall uniqueness / mulAut invariance /
> complementary Hall / **MinimalInvariantNormal** / minimal invariant p-group・commutativity / π-group disjoint /
> Hall action / invariant conjugation 等、Isaacs/GroupTheory/Mathlib)。内容は **coprime-action / minimal-invariant
> subgroup = FT local analysis (typeP_Galois 9000 の σ-theory 基盤含む) が使う foundational 群論**で、chore-churn
> busywork ではない。⟹ 「DORMANT / idle 待機」判定は実態と乖離ゆえ撤回、**d = codex 運用の active shared-infra
> レーン**に再活性化。claim-before-build 継続。**⚠ make-work 化防止**: hub は d の新 API が FT 経路 (特に 9000 /
> BG local analysis) に接続するかを定期確認する (0-consumer 自体は off-path 根拠にしないが、FT-relevance の追跡は
> 続ける)。正本 = 本ブロック + ft_lane_reallocation「lane d 再活性化」節。

> **🔀 2026-07-14 レーン再設計 (issue 0115、ユーザー発議 + hub 3 並列監査 wf_525303b8)**:
> (1) **c 再起動 GO** — 5 endpoint 中 4 workable (07-05 の「c-unreachable」は STALE; campaign A =
> ComparingLM 3-field bridge 配線、campaign B = T-side Singer field model)。operator はユーザー起動待ち。
> (2) **`S15_SAndT_Setup/OrderDetermination.lean` の所有 b→a 移管** (4 sorry; (13.11)/(13.12) は un-gated、
> (13.13)/(13.15) は de-opacify 要)。以後 range-check: a の同 file 編集 = 非逸脱 / b の同 file 編集 = 逸脱。
> (3) **4 レーン目見送り** — Pf Appendices 15 sorry は off-path 確定 (Part II scaffold)。
> (4) NormEstimates/CountingLayer/SAndTBasic の残 5 sorry = layer-inversion 問題、hub relayer (issue 0116)。

**signature-first interface (ゲートは幻)**: 上流が sorried signature を export → 下流が cite。各レーンは独立クラスタを
正面から埋め、cross-cluster は signature contract で媒介 (待たない)。詳細 = ft_lane_reallocation_2026_06_28.md。

**取り決め**: (1) 各レーンは**自所有ファイルのみ編集**、他は cite (要望は notes/issue 経由)。
(2) **新規 `axiom` 宣言は abort + ユーザー承認**。(3) **起動時 main 同期** = `git merge main` (3-way、`--ff-only` 禁止)。
`lake update` 禁止。コミットは main のみ。マージ順 = **a → b → c** (独立ゆえ形式的)。

**🧭 方向性・cross-lane 判断は HUB が自律裁定する (ユーザーに聞きに来ない、ユーザー 2026-07-06)**。
レーンが frontier を自律判断するのと対称に、hub は **(a) レーン間の診断の食い違い** (「X は repo に在るか」
「どちらの grep/診断が正しいか」等) と **(b) レーン方針・cross-lane 設計判断** (carve-out 付与・ファイルの
keep/delete・所有/優先順位・重複解消) を、**hub 自身が必要な調査 (code-level grep・`coq/` の Coq trace・
subagent fan-out) を行って裁定し**、結果を issue (HUB 宛 issue / 該当 shared-infra issue) と notes に記録する。
**この種の裁定に AskUserQuestion を使わない** — 「食い違いがある / 方針が割れている」自体は escalation 理由でなく、
**調査して裁定する**のが hub の仕事。調査もユーザーに投げない。
- **ユーザー escalation は narrow に予約**: (i) 新 `axiom` 宣言、(ii) unsound carrier・signature 無断変更、
  (iii) build 破壊・sorry regression・想定外 git 状態 = **merge-safety STOP** (下記 ⛔、halt+報告)、
  (iv) 既存規約+徹底調査を尽くしてなお真に underdetermined かつ不可逆・影響大の戦略選択 (稀)。
- **先例 (2026-07-06)**: lane-a/lane-b の prime-TI 診断食い違いを hub が 2 subagent + Coq trace で調査し
  「PrimeTIResidue KEEP + 9014 OPEN」を裁定 (issue 9014 HUB RULING)。当初 hub は AskUserQuestion で
  keep/delete を聞いたが、**既存規約 (CLAUDE.md の prime-TI port must-build) + 調査結果で "keep" は既に
  determined** ゆえ聞くべきでなかった — 以後この種は自律裁定 ([[hub-arbitrates-cross-lane-autonomously]])。
- lane が HUB 宛 issue を起票してもよい (title に "HUB:" 冠、選択肢明記) が、hub は待たず各 tick で拾って裁定。
  軽微な signature 不足通知は notes でよい ([[cross-lane-sync-via-notes]] の上位版)。

**🔁 lane 自己復帰**: lane が hub 待ちで停止しても自走再開しうる
(hub の合流手順は不変、lane の自己復帰は通常の作業再開ゆえ区別不要)。

## 🚫 ビルド規律 — フルビルドは hub の合流 gate 1 箇所に集約 (ユーザー 2026-07-19)

**main は hub が合流のたびにフルビルドで gate している**ので、レーンが `git merge main` の直後に
確認目的でフルビルドを回すのは**二重検証で無駄**。10〜16 分 × レーン数 × 同期回数が空費になり、
同一 worktree で並行すると olean が churn して他の leaf build まで巻き添えにする (2026-07-19 実測)。

- **レーン**: 自分が触った leaf を `lake build <Module>` で検証する。それだけ。
  main 取り込みの検証も、commit 直前のフルビルドも原則不要。
- **hub**: 全レーンを `git merge --no-ff` でまとめてから **フルビルドを 1 回**。
  green + AxiomsCheck OK + sorry 非退行 で push。マージ組み合わせ特有の破綻はここで捕まる。
- **subagent**: フルビルド禁止 (leaf build のみ)。親がまとめて 1 回回す。
  ⚠ 禁止しても破る実例があったので**指示の冒頭に明示**する。

正本 = CLAUDE.md「開発規約 > ファイル粒度」の該当 bullet。

## 各イテレーションの手順

> **⛔ 問題発生時はループ停止（ユーザー方針 2026-06-22, 永続）**: 下記のいずれかが起きたら、
> 進行中マージを `git merge --abort`（**冒頭ガード = 他マージ進行中の場合を除く**）し、
> **`CronList` で監視 cron の id を確認 → `CronDelete` でその場で停止** + 問題内容を明示報告し、
> **以降のレーン処理・次 tick を行わない**（ユーザーが解消・再開指示するまで待つ）。黙って次 tick で
> 同じ問題を繰り返さない。**問題 = ** build 失敗 / 内容コンフリクト（AxiomsCheck.lean・OddOrder.lean
> の独立追記**以外**）/ sorry regression（証明済→sorry）/ 新規 `axiom` / push 失敗 / 想定外の git 状態
> / **レーン範囲逸脱（下記 step 1.5 = 自所有外の Pf/BG S-ファイルを編集; ユーザー方針 2026-06-22）**。
> **非問題（通常継続）= ** 「変化なし」/ 新 decl の faithful scaffold sorry 増 / 独立追記コンフリクトの両保持解決
> / 共有ファイル編集（AxiomsCheck.lean 追記・OddOrder.lean import・`OddOrder/GroupTheory/**`・`OddOrder/Mathlib/**` 共有 infra・notes・issues）
> / **上流 signature 変更への機械的 call-site 追従**（下記 🔩）/ **自所有 sorried decl の不要化削除** (sorry 減、
> 上流再配線で obligation 自体が消える型 — 先例 = b の `witness_psi_degree` 削除 49607ba9)。
>
> **🔩 機械的 call-site 追従は非逸脱 (hub 裁定 2026-07-10 tick、一般ルール化)**: レーンが**自所有 upstream 宣言の
> signature を変更** (引数追加・仮説引数化・リネーム) したとき、その **consumer call-site の機械的追従編集**は
> 他レーン所有 file 内であっても範囲逸脱としない。条件 (全て): (i) 追従は引数供給/名前置換のみで対象宣言の
> statement・証明内容を変えない、(ii) 数行規模、(iii) commit message で self-flag、(iv) build green。
> 根拠 = 0096 拡張 (proof-only de-gate) ・「S08_CaseBCoherence2 1 行追従」と同系の先例統合。逸脱判定は
> 「他レーンの active 数学に触ったか」であり「diff が他レーン file に掛かったか」ではない。
> 先例 = b の `witness_L_hzeta0nu` hAH 仮説引数化に伴う S16 下流 2 file × 1 行追従 (49607ba9、
> c は codex 運用中の active file だったが hunk 非交差で問題なし)。
>
> **🔧 範囲逸脱の是正 = 成果を無駄にせず軌道修正（ユーザー方針 2026-07-06）**: レーン範囲逸脱で halt+flag した後、
> その逸脱に **genuine output（実証明・実構成・sorry-free work）が含まれるなら discard/revert せず、hub が軌道修正で
> 保全する** — 正しい file/leaf へ移設 / carve-out 付与 / owner 再割当 / 下流再配線。「軌道修正できれば十分」で、
> genuine math を破棄しない（territorial ルールは coordination 保護であって成果 gate-keep でない）。先例 = lane b の
> `S07_Subcoherent`=carve-out / `mu2Grid`=S05→PrimeTIResidue 移設 / `PrimeTIResidue` 削除=撤回（全て保全）。
> ⚠ 保全対象は **genuine output のみ**; unsound carrier・新 axiom・sorry regression・signature 無断改変 は
> 別カテゴリ（保全すべき成果でない、halt のまま）。正本 = CLAUDE.md「進捗の測り方」の該当 bullet。
>
> **♻ 問題解決後はループ自動再開（ユーザー方針 2026-06-23, 永続）**: 上記 ⛔ で停止した監視ループは、
> **問題が解決したら必ず再開する**。具体的には: (a) 停止した問題（build 失敗 / コンフリクト / sorry
> regression / 新規 axiom / push 失敗 / 想定外 git 状態 / レーン範囲逸脱）が、**ユーザーの指示か hub の
> 修正で解消したことを確認したら**、(b) **監視 cron を `CronCreate` で再作成し**（停止時に `CronDelete`
> したものを復活）、(c) 通常の tick に復帰する。「停止しっぱなし」にしない。再開時はサマリに
> 「監視ループ再開（cron id <new-id>）」を 1 行記録する。**この stop→resolve→resume サイクルが監視ループの
> 正規ライフサイクル**であり、停止は一時退避でしかない。

> **🔒 レーン所有マップ (step 1.5 範囲逸脱チェック用、2026-07-06 lane d 復活を反映)**:
> 正本 = [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md)。
> | lane | クラスタ | 所有 .lean（これ以外の Pf/BG S-ファイル編集 = 逸脱→停止） |
> |---|---|---|
> | **a** | α Pf §10–13 中央指標核 + σ-theory tail **+ S07 ν-constructor carve-out (2026-07-06)** | `OddOrder/Peterfalvi/S(0[3-9]|1[0-3])*` + `OddOrder/FeitThompson.lean`（`card_kappaHall_lt_of_isTypeIIIorIV` (行番号は drift するため decl 名で参照) + 旧 d carrier 宣言群 = 全体、d 退役で fold）+ **S10 bgTheoremE carrier**（旧 carve-out 0086 解消）+ σ-theory tail (S11 imprimitivity + dup retire は S11 内、GroupTheory/** 共有で cite)。**+ carve-out (issue 9016, hub 裁定 2026-07-06 夕・ユーザー裁可)**: gate-2 obligation-2 = **non-orthonormal S₂ 用 `τ₃`/`ν` glue-map constructor** を a が `S07_*` へ **新規 additive 宣言**として build (b の orthonormal glue `S07:3196/3229` 系には非接触)。これが a の唯一 ungated head-on target (a の唯一 bare feitThompson sorry を gate)。obligation-1 hY は b の S07_Subcoherent が producer (sorried-cite) |
> | **b** | β Pf §12 Dade tower + coherence infra **+ BG §15/§16 (2026-07-06 追認)** | `OddOrder/Peterfalvi/S14_MaximalI.lean`（**全体**、旧 carve-out 0088 `exists_typeICovering` は b に解消）+ **coherence infra** = `S07_Coherence*`/`S08_PGroupReduction`（既存 coherence file、(5.7)/(6.5.c)/(6.8) case-B 系、hub authorized 2026-07-02）+ GroupTheory/** coherence leaf。⚠ これらは nominal に a の `S0[3-9]` regex に掛かるが **coherence infra ゆえ b 担当（逸脱でない）**、a の active territory は §9-13 char 核で S07/S08 coherence は非接触。**⚠ b の例外 glob は正確に `S07_Coherence*` + `S08_PGroupReduction` の 2 つのみ** (正本 ft_lane_reallocation §レーン表): `S08_CaseB*`/`S08_CoherenceTheorems` 等その他の S07/S08 file は **lane a 所有** — 2026-07-03 tick で a の `S08_CaseBCoherence2` 1 行追従を「b 所有では」と誤読しかけた (glob 照合で解消、逸脱でない)。**+ BG §15/§16 node (issue 9017, hub 裁定 2026-07-06 夕・ユーザー裁可「drift 追認」)**: `OddOrder/BG/Ch4_FamilyOfMaximal/{S15_MF.lean (§15.8 tau2_transfer_constraint / §15.9 centralizer_escape_final_local), S16_MainResults.lean, S14_TypePCounting.lean (Cor 14.12 `typeP2_neighbor_is_typeF*`、Thm 15.8 の prereq — carve-out 拡張 2026-07-06 tick、signature 保持・他 owner なし)}` の残 bare sorry は **b の active territory** (共有凍結から除外)。Thm 15.8 signature 訂正 (unsound→Coq準拠, consumer 0) + `typeF_frobenius_of_tau2_prime_free` の S16→S15 hoist を承認済 (9017 RULING)。lane c の Peterfalvi `S16_NonExistenceG.lean` には跨らない (別 file) |
> | **c** | γ **S16 非存在 — ⚠ 2026-07-06 夕 DORMANT cite-sink** (領域枯渇の hub 裁定、reactivation trigger は下記) | `OddOrder/Peterfalvi/S16_NonExistenceG.lean`（**2026-07-04 再々編: S15_SAndT_Setup + S15_SAndT は c→b 移管**、c は S16 に集約し S15 を import cite）+ 構成的 Clifford (issue 9002、**完了**) + **carve-out (2026-07-06, hub 裁定, issue 9013)**: `S15_SAndT_Setup.lean` 内の `reconciled_typePData_T` T-side carrier ブロック（現 S15:~4018–4260、`isNilpotent_V` 等の T-side type-P data field discharge）は **c 所有**（退役解除 — c の (14.9) T-side type-IV 排除が本 carrier を要求すると 884a52e0 airtight 分析で確定、on-path 復活）。⟹ step-1.5 で c が S15 の**この T-side 領域のみ**を編集しても逸脱でない（c が S15 の char-family 領域 = b の active `cprimeSharpS`/(C')# 系 ~845 を触ったら逸脱）。b は逆に T-side 領域を触らない。恒久解（reconciled_typePData_T を c-owned/shared T-side leaf へ移設し S15 二重所有を解消）は issue 9013 で追跡 |
> | **b 追加所有 (2026-07-04)** | β §16 char cascade | `OddOrder/Peterfalvi/{S15_SAndT_Setup, S15_SAndT}.lean`（c→b 移管、(13.9)-(13.19) on-path parity/構造/norm を b が担当; off-path S-side cascade 13.5-13.10 は退役）|
> | **d** | δ codex shared-infra hygiene — **2026-07-06 夕: DORMANT** | **2026-07-06 復活 → 同日夕 dormant 化 (分担監査 + ユーザー裁可)**。9006 Hall relocation / 9007 induced-conjugation hoist は完了済み。BG §15/§16 node は **b が owner を追認**したため d の rescue frontier にならず、他に unclaimed shared leaf も監査で発見されず (9014/1017-arith は build 済)。⟹ d は charter どおり **停止 (stop+報告)、checklist/notes の busywork を作らない** (直近 `chore: refresh issue checklist` 連発は CLAUDE.md 禁止の busywork ゆえ即停止)。新しい genuine shared claim が立てば再起動。worktree は保持 (idle 継続なら retire 検討、可逆)。`OddOrder/GroupTheory/**` 等 shared leaf は claim 後のみ。**Peterfalvi/BG S-file は fresh issue/carve-out なしに編集しない**。 |
> | **共有（全 lane 可）** | — | `OddOrder/AxiomsCheck.lean` / `OddOrder.lean` / `OddOrder/GroupTheory/**` / `OddOrder/Mathlib/**` / `OddOrder/Algebra/**` / **`OddOrder/Isaacs/**`**（全 lane 加算可）/ `OddOrder/BG/**`（**大部分は完了・共有凍結。⚠ 例外 = BG §15/§16 node = lane b 所有** (issue 9017, 2026-07-06 追認): `S15_MF.lean` §15.8/15.9 部 + `S16_MainResults.lean` の残 4 bare sorry は共有凍結でなく b active。それ以外の BG/** は従来どおり凍結）/ `notes/**` / `issues/**`。**⚠ Isaacs 追加 (2026-07-04 hub 裁定)**: `OddOrder/Isaacs/**` は基盤 finite-group-theory ライブラリで**どのレーンの active territory でもない**ゆえ shared foundation として扱う (consumer が proven 補題を additive に加算可、GroupTheory/Algebra 同格)。precedent = c の Isaacs 6.11 使用 / a の (7.8.b) 用 `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` 追加 (commit 9f41b6f7)。既存 Isaacs 宣言の statement 改変は要 hub flag (additive のみ非逸脱)。|
> | **凍結 scaffold — ❌ 2026-07-19 失効** | — | `OddOrder/Peterfalvi/Appendices/**` は**もはや凍結でない** (失効の正本 = 本ファイル行 61-62)。新フェーズの所有: **b = Suzuki / Suzuki2Groups 系**、**c = NearFields / Huppert / SemilinearField / FeitSibley**。<br>**2026-07-19 実測 (comment-strip)**: Huppert 0 / NearFields 2 / SemilinearField 0 / Suzuki 0 / Suzuki2Groups 4 / FeitSibley 5。<br>*(履歴: 2026-07-02 census の Huppert 1 / NearFields 2 / Suzuki 5 / Suzuki2Groups 4 / FeitSibley 3 は当時の実測として正しい。以後 Suzuki 系の leaf 化と実証明で分布が変化した。)* |
>
> ⚠ `FeitThompson.lean` は**共有ではなく lane a 所有** (d 退役で carrier 宣言群ごと fold)。他レーンが
> carrier 宣言 (`Section16Inputs` 等) に field を追加する必要があるときは hub/issue 経由で承認合流
> (先例: lane c の `S_U_commutative`/`Sdata_W2_eq` 追加 = 構成子供給付き、hub 承認)。
>
> **carve-out (issue 0086, ユーザー裁可 2026-06-29) — ❌ 解消 (2026-07-02 lane d 退役)**: bgTheoremE
> carrier は **file owner = lane a に fold** (issues/closed/0086)。以下は履歴:
> `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` は
> 原則 lane a 所有だが、その中の `BGTheoremECoverData` 構造 + `BGTheoremETypeICovering` / `BGTheoremENonTypeICovering` +
> **`bgTheoremE_cover_data`** 定理 (BG Theorem E carrier, Pf 8.17、b/c/d 共有 consumer) は **lane d 所有**として扱う。
> ⟹ **step 1.5 の範囲逸脱チェックで、lane d が S10 のうちこれら carrier 宣言**「のみ」**を編集している場合は逸脱としない**
> （S10 のそれ以外を lane d が編集したら逸脱; lane a が carrier ブロックを編集したら逸脱）。判定が曖昧なら
> `git diff main...d -- …S10…` の hunk が line 493–570 周辺の carrier 宣言に限るか確認。恒久解（現状維持 or lane d
> ファイルへ移設）は issue 0086 で追跡。
>
> **carve-out (issue 0087, ユーザー裁可 2026-06-29) — ❌ 撤回済 (issue 0089, 2026-06-30)**:
> `OddOrder/Peterfalvi/S07_RhoProjection.lean` は lane b 所有として導入されたが、S09 `chiRho` 機構の
> 完全重複と判明し**削除済** (issue 0089, ユーザー裁定 D)。以後この carve-out は無効。lane b が
> S07_RhoProjection を再作成したら逸脱。
>
> **carve-out (issue 0088, ユーザー裁可 2026-06-29) — ❌ 解消 (2026-07-02 lane d 退役)**: S14_MaximalI は
> **全体 lane b** (issues/closed/0088)。以下は履歴:
> `OddOrder/Peterfalvi/S14_MaximalI.lean`（原則 lane b）の
> うち **`exists_typeICovering` 定理（line 2639–2798、(8.17.a) type-I covering）の carrier-consumer 部分**は
> **lane d 所有**として扱う。理由: この定理は lane d 所有の S10 carrier `BGTheoremECoverData` /
> `BGTheoremETypeICovering`（carve-out 0086）を直接 consume するので、carrier API の変更
> （例: `thickenedA1`→`cover`, `thickenedA1_card`→`cover_card`, `cover_subset_kernels` 追加）が
> 必然的にこの定理に波及する。⟹ step 1.5 で **lane d が S14_MaximalI のうち `exists_typeICovering`
> のみ**を編集している場合は逸脱としない（S14_MaximalI のそれ以外を lane d が編集したら逸脱; lane b が
> `exists_typeICovering` の carrier-consumer 部分を編集したら逸脱）。判定が曖昧なら
> `git diff main...d -- …S14_MaximalI…` の `@@` hunk が全て `theorem exists_typeICovering` 文脈
> （line 2639–2798）に収まるか確認。恒久解（現状維持 or carrier-consumer を d ファイルへ移設）は issue 0088 で追跡。
>
> **carve-out (issue 0090, ユーザー裁可 2026-06-30)**: `OddOrder/Peterfalvi/S09_CertificateDischarge.lean`
> （lane b が新規作成、§7 (7.7.a) の CF(L,A) spanning 基盤 = S09 の opaque `chiRho_decomp` certificate を
> discharge する欠落インフラ、genuine・非重複と hub 検証済）はファイル名が lane a の S09 namespace
> パターンに掛かるが **lane b 所有**として扱う。⟹ step 1.5 で **lane b がこのファイルを編集していても
> 逸脱としない**（lane a がこのファイルを編集したら逸脱; lane b が他の S09 ファイル＝
> `S09_NonexistenceCertain.lean` 等を編集したら逸脱）。lane b は別ファイル隔離ゆえ lane a の S09 本体と
> 衝突しない。恒久解（現状維持 / `S07_*` rename / S09 統合）は issue 0090 で追跡。
>
> **carve-out 拡張 (issue 0090 同型, hub 裁定 2026-07-14 tick 52 — merge 79920646)**:
> `OddOrder/Peterfalvi/S09_NonexistenceCertain/NormalCase.lean` のうち **b の (7.7.a)
> certificate/rebase cluster 宣言** (`zeta_sum_div_normSq_apply_eq_zero` /
> `chiRho_decomp_rebased` + 今後の同 cluster additive 追加、2035 #22 rebase campaign) は
> **lane b 所有 decl** として扱う (0090 S09_CertificateDischarge と同内容クラス = (7.7.a)
> CF(L,A)/ρ-family 基盤; 名目 regex でなく内容で割当)。根拠: 純 additive (+133/-0)・
> sorry-free・a は S09 非接触。⟹ step 1.5 で b が NormalCase.lean にこの cluster の
> additive 宣言を足しても逸脱でない (既存 a 宣言の statement/proof 改変は従来どおり逸脱;
> 混在 leaf ゆえ decl 単位判定)。
>
> **carve-out (issue 0096, hub 裁定 2026-07-02 ユーザー委任レビュー)**:
> `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean`（原則 lane a）のうち **§8 Dade-support 宣言群**
> — `typeII_A_sets_TI` / `typeII_A_sets_normalizer` / `dadeSupportHypotheses_typeI` /
> `dadeSupportHypotheses_typeP` / `support_mutual_exclusion`（+ これらの直接 helper 新設）— は
> **lane b 所有**として扱う（(8.18.c)→(12.3)→(12.14–16) chain + issue 8022 route B の前提 = β 主題;
> b による `support_mutual_exclusion` の実証明 `65a2be52` は false-statement 修正として受理済 =
> issue 9003 裁定）。`S10_BGInterface.lean` への A₁/σ♯/M̃ bridge 補題の**追加**も b 許容
> (既存宣言の変更は要 hub flag)。⟹ **step 1.5 で lane b の S10/S10_BGInterface 編集は、hunk が
> 上記宣言 (+新 helper) の文脈に収まる場合は逸脱としない**。S10 のそれ以外（bgTheoremE carrier・
> `hall_*`・type-classification structural）を b が編集したら従来通り逸脱; lane a は上記 5 宣言を
> 編集しない。恒久解 = §8 support theory 完成後に dedicated leaf（例 `S10_DadeSupport.lean`）へ
> hub prefix-split（issue 0096 で追跡）。
> **⟹ 2026-07-04 拡張 (ユーザー承認)**: 上記 5 宣言に加え、**§8-support consumer の proof-only
> de-gate** も b 許容 — b が上流 (BG Theorem B 系) を sorry-free 化したとき、consumer 宣言
> (例 `typeI_centralizer_le_and_unique` :1728, Pf 8.12.b) の **証明本体のみ**を now-sorry-free
> upstream cite に差し替える編集は逸脱としない (条件: signature 不変 + sorry/axiom regression なし
> + self-flag)。**statement 改変は依然 out-of-scope** (要 hub flag)。実例 = commit 94a34018 の
> S10 de-gate (B4 full-Theorem-B → `typeP_hall_small_subgroup_cyclic_tau2`)。
> **carve-out (3002 供給編集権, ユーザー裁定 2026-07-05 — 監視 tick で明文化)**: 2026-07-05 hub 裁定
> (9009 選択肢 2 = b への `FeitThompson.lean` `Section16Inputs`/constructor block 一時編集権) を
> **「issue 3002 供給 chain に必要な lane-a 所有ファイルへの additive helper 追加」まで拡張**する。
> 実例 = b の `S05_TICyclic.lean` `omega_inner` (+11、既存 proven `omega_inner_self`/`omega_inner_ne`
> の Kronecker 形合成、`omegaS_inner` 供給用、issue 3002 で self-flag 済) — 本 tick でユーザー受理。
> 条件: (i) 純 additive (既存宣言の statement/proof 改変は従来どおり逸脱)、(ii) proven (sorry 追加なし)、
> (iii) 用途が 3002/9009 供給 chain、(iv) issue/notes で self-flag。**3002 供給完了で失効**
> (以後の b の S05 等 lane-a ファイル編集は通常どおり逸脱)。
>
> **carve-out (issue 0101, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S11_NineElevenCoherence.lean`
> (lane b が新規作成、(9.11) Ptype_core_coherence port の Dade-pair パラメータ化 leaf) は名目上 lane a の
> S11 namespace パターンに掛かるが **lane b 所有**として扱う (9016 hY-producer 裁定の実施 + 1017 G1)。
> ⟹ step 1.5 で b がこのファイルを編集しても逸脱でない (a が編集したら逸脱; b が他の S11 ファイルを
> 編集したら従来どおり逸脱)。**分担境界: caseA (9.7.a) maximality 帰納 = b (本 leaf) / caseB (9.7.b)
> 一様 route = a (S13 landed 済、b は再構築禁止) / full assembly = a (S12/S13 側で S11 leaf を import)**。
> 詳細 = issues/0101。
>
> **carve-out 拡張 (issue 0101, hub 裁定 2026-07-08 監視 tick #4)**: `OddOrder/Peterfalvi/S11_NineElevenCaseA.lean`
> (lane b が新規作成、caseA (9.7.a) entry point `caseA_coherent_sOf_H0Cprime_of_refuter` = caseA coherence を
> maximality-refuter 節へ reduction、namespace は `OddOrder.Peterfalvi.S13`・S13_MaximalIII_IV import) も
> **lane b 所有** carve-out として扱う (S11_NineElevenCoherence と同型 = 内容で割当)。根拠 (hub 自律裁定):
> (1) genuine caseA work = 0101 が b に割当てた caseA territory そのもの、**sorry-free・新 axiom なし**;
> (2) a の base case `sOf_degreeSubfamily_isCoherent` (S13) + b の skeleton `coherent_of_maximal_coherent_pair_refuted`
> (S07_Subcoherent) を signature contract で cite (所有衝突でなく consumer 関係); (3) **lane a は S11/S13 の
> 当該 file を一切編集していない** (`git diff main...a -- 'S11*'` 空、a の active S13 = S13_MaximalIII_IV/
> S13_CoreStructure とは別 file 隔離); (4) merge-safety 全通過 (build green 3941 jobs / AxiomsCheck OK /
> sorry 不変 87 / 新 axiom なし)。⟹ step 1.5 で b が S11_NineElevenCaseA を編集しても逸脱でない
> (a が編集したら逸脱; b は a の S13_MaximalIII_IV/S13_CoreStructure 等 active S13 file には従来どおり
> 触れない = import cite のみ)。詳細 = issues/0101「2026-07-08 追加 carve-out」節。
>
> **⟹ HUB RECONCILIATION (issue 0101, hub 裁定 2026-07-12 監視 tick — merge a85869eb)**: 上記
> 「a が編集したら逸脱」を **(10.8) 閉包 (issue 1025) 期間中に限り緩和**。**ユーザー 2026-07-12「Aで」+
> HUB RULING (9087) が (10.8) knot 閉包を authorize し、その threading target に S11_NineElevenCaseA が
> 明記**されている。⟹ step 1.5 で **a が S11_NineElevenCaseA の 9083 Phase E caseA machinery 宣言**
> (`caseA_two_summand_inertia_inputs`/`NineElevenNormBound`/`C_eq_cSub` 系の signature/proof threading)
> **を編集しても逸脱でない** (b の entry point `caseA_coherent_sOf_H0Cprime_of_refuter` を a が触ったら
> 逸脱; b はこの entry point を専有維持)。判定 = decl 単位 (混在 leaf)。merge-safety 全通過確認済
> (build green 4177 / sorry 65→65 / 新 axiom なし / b entry point preserved decl 16→16 / b 非 ahead で
> collision なし)。**(10.8) 閉包 landing で失効**。詳細 = issues/0101「HUB RECONCILIATION」節。
> **❌ 失効確認 (hub 裁定 2026-07-15 tick #8)**: trigger の (10.8) knot = **issue 1025 CLOSED**
> (`issues/closed/1025-*`)、9087 も CLOSED。⟹ 上記 0101 RECONCILIATION (a への S11_NineElevenCaseA
> 一時編集権) は**失効**。以後 a が S11_NineElevenCaseA を編集したら通常どおり逸脱、**恒久所有 = b**
> (0101 本体 carve-out どおり; Phase E machinery も b 所有として扱う — a は 10.8 閉包で当該 threading を
> 完遂済、追加編集の必要なし)。b は entry point + Phase E 宣言とも専有。
> **carve-out (issue 2035, hub 裁定 2026-07-14 監視 tick 20 — merge 側で記録)**:
> `OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHom.lean` の **caseB-Xi / `CliffordCaseBData`
> reverse-characterization 系宣言** (`caseB_xiOf_H0C_eq_induce_hcPsi` / `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair` /
> `isIndHC_of_source_eq_induce_hcPsiPair` 等、S11 (9.11) caseB Clifford 対応) は名目上 lane a の S11 regex
> (`S(0[3-9]|1[0-3])`) に掛かるが **lane b 所有**として扱う (carve-out 0101/9076/9014 と同型 = 名目 regex でなく
> 内容で割当; 0101 の S11 (9.11) caseB coherence carve-out の同ディレクトリ拡張)。根拠 (hub 自律裁定):
> (1) genuine b content — `CliffordCaseBData` (b の landed 9094 vocabulary) は同 dir の `ChiefFactorCore.lean`
> で定義、本 file は `CaseBXi` を import する caseB-exhaustion 機械 = b の 9094/2035 char cascade;
> (2) **lane a は本 file 非接触** (a 現 0 ahead、`InnerCompHom.lean` の非-refactor 履歴は b の commit のみ;
> dir 内の唯一の a feature commit 30a256cf (11.9.c) は別 file `ThetaCountAssembly.lean` で main 既 merge の
> past work); (3) **a の S13 (9.7.b) 一様 route の dup でない** (3 宣言とも S13/S11_NineEleven の main に不在 =
> 0101「b は (9.7.b) 再構築禁止」に抵触せず — これは 9094 CliffordCaseBData の caseB であって (9.7.b) route でない);
> (4) sorry-free・純 additive (+328/-0)・build green 4197 / AxiomsCheck OK 2399 / 新 axiom なし。b は S15 caseB
> wiring (set-artifact) を自ら revert し InnerCompHom lemma のみ保持 (2035 #34 self-flag) = 「軌道修正で保全」自己適用。
> ⟹ step 1.5 で b が InnerCompHom の caseB-Xi/CliffordCaseBData 宣言を編集しても逸脱でない (a が編集したら逸脱;
> dir の (11.9.c) `ThetaCountAssembly` 系は従来どおり decl-unit で a 領域)。詳細 = issues/closed/2035 #34。
> **carve-out (issue 9076, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S05_GridRigidity.lean`
> (lane c が新規作成、Pf (3.8) abstract norm-2 rigidity engine `orthonormalGrid_diff_rigidity` = S05 σ-image
> と S15 η-grid を de-dup する module-generic 核) は名目上 lane a の S05 regex に掛かるが、issue 9076
> (lane c shared-infra claim、§3 cyclicTI rigidity、claim-before-build 準拠) の abstract engine ゆえ
> **lane c 所有**として扱う (carve-out 0090/0096/0101 と同型 = 名目 regex でなく内容で割当)。根拠: lane a は
> S05 系を一切編集していない (active 衝突なし)、依存 `S05_GridTrichotomy` は既存 grid-rigidity infra、
> 9076 の「§10-13 と重なる可能性」は a が rigidity を **cite** する consumer 関係 (signature contract) で
> 所有衝突でない。⟹ step 1.5 で c が S05_GridRigidity (+ grid-rigidity S05_Grid* 系・S16_GridExpansion)
> を編集しても逸脱でない (lane a が S05_Grid* を編集したら逸脱; c が S05 の char-核 file = S05_TICyclic 等を
> 編集したら従来どおり逸脱)。詳細 = issues/9076。
>
> **carve-out (issue 9014/2038, hub 裁定 2026-07-11 監視 tick — merge 側で記録)**:
> `OddOrder/Peterfalvi/S05_OmegaSpanning.lean` (lane b が新規作成、Pf (3.3)/(1.3) ω-grid spanning +
> Fourier 展開 = (13.18) B(iii) port chain の底、9014 claim の port 対象 `equiv_restrict_compl_ortho`
> 系) は名目上 lane a の S05 regex に掛かるが **lane b 所有**として扱う (carve-out 0090/0101/9076 と
> 同型 = 名目 regex でなく内容で割当)。根拠: (1) sorry-free の genuine port (153 行、汎用核は共有
> `GroupTheory/RepresentationTheory/SupportedSpanOrthogonality.lean` に分離済 = 配置規律も正)、
> (2) 新規宣言に main との dup なし (hub 確認済)、(3) lane a は本 file 非接触 (S05_TICyclic を import
> cite する consumer 関係のみ)、(4) claim = open 9014 (claim-before-build 準拠)。⟹ step 1.5 で b が
> S05_OmegaSpanning を編集しても逸脱でない (a が編集したら逸脱; b が他の S05 char-核 file を編集したら
> 従来どおり逸脱)。⚠ 合流時に root closure 欠落 (どこからも import されず) を hub が検出 →
> OddOrder.lean に import 追記で修正 (step 3b 機械的修正)。b は今後新 leaf 作成時に OddOrder.lean
> 追記まで込みで commit すること。
>
> **carve-out 拡張 (issue 9076 piece 4c, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean`
> (lane c が新規作成、Pf (8.10)/(8.15) honest `'A0(S) = 'A(S) ∪ V^S` 定義 + set-level facts) は名目上
> S15 = **lane b 領域**だが、issue 9076 の piece 4c (A0-Dade correctness fix — 現 (13.18) は 'A(S)-Dade
> だが μ差 support は P^#∪V_S ゆえ A0 化必須) infra ゆえ **lane c 所有**として扱う (S05_GridRigidity と
> 同型 = 内容で割当)。根拠: 新 leaf (b の `S15_SAndT` を編集せず `honestTypeP2ASet` (b の
> `S15_SAndT_Setup:552`) を cite して拡張)、b は S15 を触っていない (衝突なし)。⟹ step 1.5 で c が
> S15_HonestTypeP2A0 を編集しても逸脱でない (b が編集したら逸脱)。
> **⟹ 相互 carve-out 追記 (hub 裁定 2026-07-11 監視 tick)**: 上記「b が編集したら逸脱」を
> **def-層 (語彙) に限り緩和**する。b は自所有 `S15.Hypothesis` carrier の field 追加に必要な
> **上流語彙 def の移設・機械的追従** (実例 = `honestTypeP2A0Set` を SubcoherenceInputs へ移設、
> def 本体は namespace 修飾以外不変、iter32-34 で self-flag) を行ってよい (🔩 + 9014 相互
> carve-out と同型)。条件: (i) def/statement の意味不変、(ii) c の set-level facts・A0-Dade
> content (theorem/lemma) には非接触、(iii) issue self-flag、(iv) build green。c の theorem 層は
> 従来どおり c 専有 (b が触ったら逸脱)。移設後の def-層の恒久所有 = b (SubcoherenceInputs 内)。
> **⟹ 相互 carve-out 拡張 #2 (hub 裁定 2026-07-13 監視 tick — merge 12123d9d)**: def-層に加え、b は
> **自所有 `Hypothesis.*` char-cascade 定理の *additive* 追加**も S15_HonestTypeP2A0 で行ってよい (実例 =
> `Hypothesis.tauS_mu_diff_support`/`tauS_mu_vanish_on_V` = (4.8) full-grid μ差 support/V-value、c の
> `honestTypeP2A0Set` を **cite** して 1017 caseB R-family を閉じる)。条件: (i) **純 additive** (c の
> set-level facts・A0-Dade theorem/lemma の改変・削除は依然逸脱)、(ii) 追加定理は b の `Hypothesis` char
> 系で c の A0 def は cite のみ、(iii) issue self-flag、(iv) build green。根拠: genuine b char output・
> c content 非接触 (merge 検証: `-theorem` 皆無)・c 非 ale ゆえ「軌道修正で保全」policy で受理。⟹ step 1.5 で
> b が S15_HonestTypeP2A0 に additive `Hypothesis.*` char 定理を追加しても逸脱でない (c の A0-Dade
> theorem/lemma 改変は逸脱)。同様に **S15_BridgeCharacter は混在 leaf で decl 単位判定** (b の (13.18/19)
> char 系 = `tauS_mu_cross` 等の追加は b 領域、c の BetaData/tauS_mu_row0 系は c 専有 — tick 9 の decl-unit
> ルール継続)。
>
> **✅ coordination 点 解決 = carve-out 拡張 #2 付与 (issue 9076 piece 4c-3, hub 裁定 2026-07-08 監視 tick)**:
> 上記注記の「⚠ 将来 coordination 点 (`tauS_mu_row0_cross` の A0-Dade 化 statement 変更 = b territory、
> b+c 調整要)」は**解決**。lane c が piece 4c-3 で `S15_SAndT.lean` の **(13.18) S-side A0-rewire ブロック**
> (`tauSbetaGrid` / `tauS_mu_row0_cross` / `gammaGrid_defGamma` の τ_S を `dadeHypS`→`dadeHypS0` に差し替え)
> を直接編集。carve-out 申請より先に着手したが、hub 監視 tick で **「軌道修正で保全」ポリシー**に従い
> **retroactive に carve-out 拡張を付与**して保全: **この (13.18) rewire ブロックは lane c 所有**。
> 根拠 (自律裁定): (1) genuine correctness fix — 旧 `dadeHypS` ('A(S)-Dade) では μ差 support の V_S-part が
> arbitrary-extension 領域に落ち statement が provable でなかった; A0 化が唯一の sound route (issue 9076 4c)。
> (2) **下流 blast radius = ゼロ** — `tauS_mu_row0_cross`/`gammaGrid_defGamma`/`tauSbetaGrid` を cite する
> consumer は S15_SAndT.lean 外に存在しない (grep 確認、S15_HonestTypeP2A0 docstring 言及のみ)。
> (3) **b は S15_SAndT に一切触れていない** (`git diff main...b` 確認) → 調整点の懸念 (b+c 同時編集で衝突) は
> 実際には未発生。(4) merge-safety 全通過: build green (3940 jobs) / AxiomsCheck OK / 新 axiom なし /
> sorry +1 = 新 decl `not_isConj_honestTypeP2ASet_typePV` deep-pin scaffold (regression でない)。
> ⟹ step 1.5 で c が S15_SAndT の **(13.18) S-side rewire ブロックのみ**を編集しても逸脱でない
> (c が S15_SAndT の他領域 = b の char-family/(C')# 系を触ったら従来どおり逸脱; b はこの (13.18) ブロックを
> 触らない)。**b は次回 main sync で c の rewire を取り込むこと、`tauS_mu_row0_cross` を再構築しない。**
> 詳細 = issues/9076 piece 4c-3。
> **⟹ 所在地更新 (2026-07-12 tick 9)**: b の 0103 系 prefix-split (merge 16bd816d) で、この c 所有
> ブロック (BetaData 領域 + tauSbetaGrid/GammaGrid/tauS_mu_row0_cross/gammaGrid_defGamma) は
> **バイト同一のまま `S15_BridgeCharacter.lean` へ移動** (hub 機械検証: 移設 1413 行中 1405 行同一、
> 差分 8 行は b 自身の (13.19) producer 分解のみ)。以後 **c の carve-out はファイル追従 =
> S15_BridgeCharacter.lean 内の当該宣言群** (c がそこを編集しても逸脱でない; b は同 file 内の自分の
> (13.19) producer 系のみ編集し c 宣言に触らない — 混在 leaf につき step 1.5 は decl 単位で判定)。
>
> **carve-out (issue 9014/9076, hub 裁定 2026-07-08 監視 tick — merge 216b605d)**:
> `OddOrder/Peterfalvi/S13_PrimeTIResidueBridge.lean` (lane b が新規作成、86 行、**namespace は
> `OddOrder.Peterfalvi.S15`** = ファイル名 S13_* だが宣言は S15 領域) は名目上 lane a の S1[0-6] regex に
> 掛かるが **lane b 所有**として扱う (carve-out 0090/0101/9076 と同型 = 名目 regex でなく内容で割当)。
> 内容 = (13.18) μ-carrier の honest source (`Hypothesis.s06S`/`residueS` = prime-TI residue grid を
> type-uniform な S06.Hypothesis + sorry-free `PrimeTIResidueData.ofS06Hypothesis` で構成、IsTypeP1 不要;
> §12 muGrid は type-P2 obstruction で dead)。根拠 (自律裁定): (1) genuine b content — (13.18) = §13 char
> cascade = b の S15_SAndT territory; (2) **lane a は S13/S15 活動ゼロ** (0 unmerged、`git diff main...a --
> 'S13_PrimeTIResidueBridge*'` 空) で active 衝突なし; (3) a の S12/S14/shared `PrimeTIResidue` を **cite する
> だけ** (編集せず); (4) merge-safety 全通過 (build green 3942 jobs / AxiomsCheck OK / sorry 86→86 / 新 axiom
> なし / 衝突なし)。⟹ step 1.5 で b が S13_PrimeTIResidueBridge を編集しても逸脱でない (a が編集したら逸脱;
> b が a の active S13 = S13_MaximalIII_IV/S13_CoreStructure 等を触ったら従来どおり逸脱)。⚠ **minor**:
> ファイル名 (S13_*) と namespace (S15) の不一致 — 内容が S15 ゆえ将来 `S15_PrimeTIResidueBridge.lean` への
> rename が自然 (b の裁量、非緊急・非 blocking)。詳細 = issues/9014・9076。
>
> **carve-out 拡張 (issue 9014, hub 裁定 2026-07-09 監視 tick — merge dd18fdc5)**: 上記 b 所有の
> `S13_PrimeTIResidueBridge.lean` のうち **`Hypothesis.residueS` 周辺 (c の (13.18) engine が consume する
> S-side bridge 宣言) は lane c も編集可** (retroactive 保全、9076 4c-3 と同型)。実例 = c の instance-plumbing
> refactor (binder → scoped FiniteInduce 統一、whnf timeout 解消、consumer 0・数学的内容不変)。b の
> (13.18) μ-carrier honest source 側 (`Hypothesis.s06S` 等) は従来どおり b 専有。b は main sync で
> 本 refactor を取り込み、binder 供給へ再変更しない。詳細 = issues/9014 「HUB carve-out 追記 2026-07-09」節。
>
> **carve-out (issue 2038 供給編集権, hub 裁定 2026-07-09 監視 tick — merge 03fd8474)**: 3002 供給編集権
> (上記、失効済) と同型の期限付き編集権を **issue 2038 の (12.14) chiRho 供給 chain** に付与: b は
> **a 所有 S09 chiRho 機構ファイル** (`S09_Building78C.lean`・`S09_NonexistenceCertain/*` 等) への
> **純 additive・proven な helper theorem 追加**を行ってよい (条件 = 3002 先例と同一: (i) additive のみ、
> (ii) proven (sorry 追加なし)、(iii) 用途 = 2038 (12.14) 供給、(iv) issue で self-flag)。既存宣言の
> statement/proof 改変は従来どおり逸脱。**(12.14) 供給完了で失効**。詳細 = issues/2038 「HUB carve-out」節。
>
> **carve-out (issue 9092 供給編集権, hub 裁定 2026-07-13 監視 tick — merge a6fa0ca5)**: 3002/2038 供給編集権と
> 同型の期限付き編集権を **issue 9092 の `mu_isColumnFamily` 供給** に付与: b は **`Hypothesis` (SubcoherenceInputs,
> b territory) への field 追加 + 全 producer 同時放電を 1 coordinated commit** で行ってよく、その放電のうち
> **a 所有 `FeitThompson.lean` の Hypothesis producer (:1392/+1556/1686) への `mu_isColumnFamily` near-definitional
> 供給行の追加**を許容 (`mu:=muS:=columnFamily.mu` ゆえ near-definitional)。条件: (i) FeitThompson は当該 field の
> near-definitional 供給行のみ (他 statement/math 不変)、(ii) **field+全 producer 放電を 1 commit** (build 破壊回避)、
> (iii) issue 9092 で self-flag、(iv) build green。⟹ step 1.5 で b が FeitThompson の当該供給行を編集していても
> 逸脱でない (他の FeitThompson 編集は従来どおり逸脱)。**mu_isColumnFamily 供給完了で失効**。詳細 = issues/9092。
>
> **carve-out (issue 9094 供給編集権, hub 裁定 2026-07-13 監視 tick 4 — merge c14d8a01)**: 3002/2038/9092 と
> 同型の期限付き proof-only 編集権を **issue 9094 の λ-cluster restructure (案 A)** に付与: b は
> **c 所有 `S16_NonExistenceG/TTypeII.lean` の `T_side_caseB_facts` (:191-196) の proof 差し替え**
> (旧 `character_degree_analysis` obtain → 新 dichotomy-split export cite) を行ってよい。statement は
> 無条件のまま正しい (Coq PFsection14 `ltqp`+(13.12)/(13.13)-on-T 準拠、hub 検証済) ゆえ **proof のみ**。
> 条件: (i) statement 不変、(ii) c の A0-Dade/BetaData 領域非接触、(iii) issue 9094+commit self-flag、
> (iv) build green。**移行完了で失効**。NormEstimates 5 定理の dichotomy thread は b 自所有で通常作業。
> 詳細 = issues/9094 HUB RULING (案 A = λ-free Core 分割、右分岐は landed CliffordCaseBData vocabulary、
> 非破壊移行手順つき)。
> **⟹ 拡張 (hub 裁定 2026-07-14 tick 8 — merge 78193bad)**: b の **a 所有 S09 Hypothesis76/chiRho
> 機構ファイル (S09_Building78C 等) への純 additive・proven helper 追加 (用途 = 9094/2035 供給)** を
> retroactive 受理し本編集権に統合 (実例 = `hypothesis76OfDadeBase` (7.7) 任意 base builder +57 行、
> 2035 #24 self-flag 済; 2038 供給編集権 (用途 (12.14)) と同型の 9094 用途版)。条件は 2038 と同一:
> (i) additive のみ、(ii) proven、(iii) 用途 9094/2035、(iv) self-flag。a の active S09
> (S09_FrobeniusParity (7.10) 系) と非交差確認済。**9094 供給完了で失効**。
>
> **carve-out (issue 9087 RULING #4, hub 裁定 2026-07-13 監視 tick 2 — merge da032e55)**: newly-ungated
> 3 decl — `card_LF_coprime_pq` (`S15_Gate3.lean:157`) / `allTypeI_fittingIsTI` (`S14_MaximalI/
> TypeICovering.lean:68`, private) / `not_nonTypeICovering_of_all_typeI` (同 `:95`, private) — を
> **lane a へ decl 単位 carve-out** (両 file は本来 b territory)。根拠: a 自領域 genuine 候補ゼロ
> (census #print axioms 確定) / b は 2035 active で 3 target と非交差 (機械検証済) / ungated genuine
> on-path math ((13.17.b) B2 + (12.17) all-type-I chain) を idle 化しない / unblock 元 = a で文脈鮮度。
> 条件: (i) signature 不変 (statement 改変は要 hub flag、proof 供給 + stale docstring 訂正のみ)、
> (ii) 新規 helper は additive のみ (既存 b 宣言の改変・削除は逸脱)、(iii) 9087+commit で self-flag、
> (iv) build green。**3 decl の sorry-free 化で失効** (完全 b 所有へ復帰)。b は当該 3 decl を再証明
> しない。⟹ step 1.5 で a が S15_Gate3 / TypeICovering の**当該 decl 文脈のみ**を編集しても逸脱で
> ない (a が両 file の他領域 = b の既存宣言を触ったら従来どおり逸脱)。詳細 = issues/9087 RULING #4。
> **⟹ ❌ 失効 (2026-07-14 監視 tick — merge 004be7f0)**: 3 decl 全て sorry-free 化で失効条件充足。
> S15_Gate3 / S14_MaximalI/TypeICovering は完全 b 所有へ復帰。3/3 `not_nonTypeICovering_of_all_typeI`
> の signature 変更 (provenance 引数化) は self-flag → hub 受理 (as-stated は carrier provenance
> 非記録による in-file 循環で証明不能 — producer `bgTheoremE_cover_data` (a 所有 S10) の教科書
> (8.8.b) 準拠強化とセットの honest fix; 他 consumer 無影響を機械検証済)。b は次回 main sync で
> 新 signature を取り込む (再 restate しない)。
>
> **⟹ 拡張 #2 (ユーザー裁定 2026-07-05 tick(3) — Hypothesis76 (7.6) 忠実化 field の包括許可)**:
> 同型逸脱 3 連発 (issue 0091 Hypothesis78 / zeta_induced / zeta_injective、各回ユーザー受理) の
> 反復解消として、**issue 2034/3002 の (13.5) 供給作業中に限り、b による `S09_NonexistenceCertain`
> `structure Hypothesis76` への Pf (7.6) 忠実な field 追加を包括許可**する。条件: (i) field **追加**のみ
> (既存 field の改変・削除は逸脱)、(ii) 教科書 (7.6) に忠実な内容、(iii) 供給 (構築子/consumer 更新)
> 込みで build green、(iv) issue 2034/3002 で self-flag。**2034/3002 完了で失効**。Hypothesis76 以外の
> S09_NonexistenceCertain 編集は従来どおり逸脱。

> **carve-out (issue 0116, hub 裁定 2026-07-15 Codex tick #5)**: lane a の Core η₁₀ correction / full-flip
> relayer が直接必要とする `S15_CharacterDegreeEngines.lean` と
> `S15_SAndT_Setup/DegreesFirstSplit.lean` の proof/API hunk を、0116 完了まで lane a に限定付与する。
> 条件は (i) Core correction と互換入口の配線に直結、(ii) b の別 active 宣言に非接触、
> (iii) signature 破壊・新 axiom・sorry regression なし、(iv) build green。merge `38054779` の
> genuine proven output を保全する軌道修正であり、両 file 全体の所有移管ではない。0116 full flip 完了で失効。
> **⟹ carve-out 拡張 (hub 裁定 2026-07-15 tick #6、merge `4ca952f5`)**: 上記に加え
> `S15_SAndT_Setup/TSideDegrees.lean` の **additive 宣言 `Hypothesis.Q_elementaryAbelian`** (一般 type-P
> の (13.2.b)-for-T Q elementary-abelian、(14.9) 以前に §9 chief-factor collapse で構成、sorry-free) を
> 0116 full flip 完了まで lane a に限定付与する。同 file は名目 b territory (2035 char cascade landing 先)
> だが本宣言は 0116 が producer として明記 (issue 0116:108-109/152 の hQ 場内 discharge) する on-path work。
> 条件: (i) 純 additive (既存 b 宣言の statement/proof 改変は逸脱)、(ii) sorry/axiom regression なし、
> (iii) build green。⟹ step 1.5 で a が TSideDegrees に本宣言 (+同 flip cluster の additive 追加) を
> 足しても逸脱でない (b が編集したら従来どおり b 領域; a が既存 b 宣言を改変したら逸脱)。0116 full flip 完了で失効。
> **⟹ carve-out 拡張 #2 (hub 裁定 2026-07-15 tick #7、merge `5a29403d`)**: `S15_SAndTDefs.lean` の
> **(13.16) W2-side c=1 threading** (`U_inf_centralizer_P_eq_bot` / `normalizer_U_inf_W2_eq_bot(_of_data)` /
> `normalizer_W2_within_S` / `normalizer_W2_structure` / `normalizer_W2` の `_of_c_eq_one` 明示 param 変種
> 追加 + 旧 signature の compatibility-entry 化) を 0116 full flip 完了まで lane a に限定付与する。同 file は
> 名目 b territory (S15_SAndT prefix-split) だが、これら (13.16) mid-layer consumer は 0116:112 が
> full-flip target と明記する on-path 宣言。条件 (全て満たす): (i) **既存 b 宣言の signature を compat entry
> として温存** (下流無破壊、原名は 1 定義ずつ残存)、(ii) 追加は `_of_c_eq_one` 明示 param 変種のみで
> 既存 statement/proof の意味不変、(iii) sorry/axiom regression なし、(iv) build green。⟹ step 1.5 で a が
> S15_SAndTDefs の c=1 threading 系宣言を編集しても逸脱でない (b が編集したら従来どおり b 領域; a が
> compat entry を壊す・既存 b 宣言の statement を改変したら逸脱)。0116 full flip 完了で失効。

> **🚦 現行 = visit-time trial merge (ユーザー裁定 2026-07-15; tick-wide pre-freeze を置換)**:
> tick 冒頭で全レーン tip を一括凍結しない。レーンを一つずつ訪問し、未マージがあれば pre-merge
> sorry 数を取った直後に `git merge --no-ff --no-commit <branch>` を行う。その時点の exact snapshot は
> `MERGE_HEAD` に固定されるため、scope / claim / axiom / sorry / root / build の全検査を
> `MERGE_HEAD` と staged tree に対して行う。検査中に branch が進んでも取り込まれず、次回訪問へ回る。
> 各 lane の commit 後は main clean を確認してから次 lane を訪問する。

1. 各レーンを訪問した時点で未マージ確認: `git log --oneline main..<branch>`。
   **⚠ あわせて未 push も確認する: `git rev-list --count origin/main..main`**
   （2026-07-19 に実害。前 tick がフルビルド実行中にセッション切断で落ち、a/c のマージ commit は
   main に残ったまま **gate も push も未完了**になった。次 tick で「全レーン 0 → 変化なし」と
   即終了すると、この**未検証コミットが main に居座り続ける**。)
   **「全レーン未マージ 0」かつ「未 push 0」の両方が成り立つときだけ**「変化なし」1行報告で
   即終了（build を走らせない）。未 push が残っていれば**マージが 0 でも gate を回して push する**。
   未マージがあれば `bin/count-sorry` を記録し、直ちに
   `git merge --no-ff --no-commit <branch>` → `tip=$(git rev-parse MERGE_HEAD)` とする。
1.5. **レーン範囲逸脱チェック（ユーザー方針 2026-06-22, 永続）**: 未マージがあるレーンについて、
   **visit-time trial merge 直後**に**そのレーンが実際に変更したファイル**を取得し、
   **本ファイル冒頭 (2026-07-17 / 07-19 更新) の `a_re` / `b_re` / `c_re` / `shared_re`** に照らす
   (本文中の 🔒 所有マップは FT endgame の履歴であり、range-check には使わない)。
   **⚠ 必ず 3-dot `main...MERGE_HEAD`（merge-base からの取り込み側差分）を使う** — 2-dot `main..MERGE_HEAD`
   は端点差分で「レーンが main に遅れている分（他レーンの merge で main 側だけ進んだ S05/S06/S11 等）」を
   **誤検出**する（line 192 の罠と同根; 2026-06-22 実害 = lane-f/b が 2-dot で false-positive 逸脱判定）。
   **自所有でも共有でもない `.lean`（典型: 他レーンの Pf/BG S-ファイル）を含むなら範囲逸脱** → そのレーンは
   `git merge --abort` し、⛔ に従いループ停止（`CronDelete` + 報告 + 以降の tick を行わない）。
   報告には逸脱ファイル名 + lane + 所有者を明記。例:
   ```
   # 正本 = 本ファイル冒頭 (2026-07-19 11:29 / issue 9154) の a_re / b_re / c_re / shared_re。
   # ⚠ ここに regex を再掲しない — 二重管理が 2026-07-19 に FT-endgame 版の取り残しを生んだ。
   lane_re="$a_re"   # 訪問中のレーンに応じて a_re / b_re / c_re を選ぶ
   git diff --name-only main...MERGE_HEAD -- '*.lean' | grep -vE "$lane_re" | grep -vE "$shared_re" | grep . && echo "範囲逸脱 → STOP"
   ```
   逸脱なし（空）→ step 1.6 へ。共有ファイル・notes・issues のみの差分は逸脱でない。
1.6. **shared-infra 重複検出（claim-before-build 運用、ユーザー裁定 2026-07-01）**:
   `ft_path_policy.md` §0 policy 6 で、複数の gated レーンが同じ上流 shared infra
   （未所有 leaf `OddOrder/(Algebra|GroupTheory|Mathlib)/**`）を同時並行構築する重複を防ぐ。各 tick で:
   - **(a) 同一 leaf path の衝突**: 2 つ以上のレーンが**同じ新規** shared-infra `.lean` を追加していないか。
     ```
     for L in a b c; do git diff --name-only --diff-filter=A main...$L -- \
       'OddOrder/Algebra/**' 'OddOrder/GroupTheory/**' 'OddOrder/Mathlib/**'; done | sort | uniq -d | grep . \
       && echo "shared-infra path 衝突 → STOP"
     ```
   - **(b) claim なしの新規 shared-infra leaf**: 新規追加された shared-infra `.lean` に対応する open 9000
     番台 claim issue が**無い**（`issues/9*-*.md` を grep）→ ⚠ flag（沈黙構築 = policy 6 違反の疑い）。
   - **(c) 同一 ref の 2 claim**: open 9000 番台 issue に同じ教科書 ref / 補題名の claim が 2 件 → STOP。
   検出したら **STOP + 報告**（より完成度の高い方を残し、他方を cite に rebase させる指示。浪費は ~1 tick に
   有界）。空 → step 2 へ。**grandfather**: 2026-07-01 前 landing 済 leaf（`GaloisRationalInteger.lean` 等）は対象外。
2. **a → b → c の順**で（独立レーンゆえ順序は形式的、上流→下流の自然順）、未マージがあれば自動合流:
   - step 1 で記録した pre-merge 実 sorry 数を使用: `bin/count-sorry`
     （prose 偽陽性 [sorry-free / sorryAx / `sorry'd` / backtick 引用] を除外する判定器。
       旧 `grep '(^|[^a-zA-Z-])sorry'` は 259 と過大計上したが count-sorry は 146 ≈ 実 141。
       絶対数の ground truth は build 警告 `lake build OddOrder 2>&1 | grep -c 'uses .sorry.'`）
   - `git rev-parse MERGE_HEAD` が visit-time `tip` と一致することを確認し、以後は staged tree を検査する。
   - **コンフリクト時**:
     - `AxiomsCheck.lean` / `OddOrder.lean` の**独立追記衝突** = 両ブロック保持で解決して続行
       （A=keystone 系の `#assert_only_allowed_axioms`、B=Peterfalvi 系の同コマンドは別定理ゆえ両方有効）
     - **`issues/**`・`notes/**` (.md) の独立追記衝突も同様に両ブロック保持で続行** (hub 裁定
       2026-07-10 tick で明文化: hub の裁定追記と lane の進捗追記が同一 issue 末尾に付く型は
       AxiomsCheck 独立追記と同じ良性クラス、build 影響なし。実例 = issues/2038 の
       carve-out 記録 vs whnf-wall 診断、merge 68dd36ca)。**同一行・同一節をどちらも書き換える
       絡み衝突は従来どおり abort+報告**
     - それ以外・内容が絡む衝突 = `git merge --abort` で**報告**（自動解決しない）
   - **staged が全て `notes/` 配下なら build 省略**(Lean 不変ゆえ結果不変)し直接 commit へ。
   - **`.lean` を含む場合 — sorry 先行チェックで build 短絡**: build は重い (~3800 jobs) ので**先に**
     `bin/count-sorry` を取る。増えていれば `git diff --cached` で **regression か scaffold か**判定し、
     **regression（証明済→sorry）or 新規 axiom なら build せず即 `git merge --abort`**。
     scaffold（新 decl statement）or 不増なら `lake build OddOrder OddOrder.AxiomsCheck`(background, 完了待ち)へ。
   - **合格条件**（全て満たす）:
     - build exit 0 かつ最終行 "Build completed successfully (N jobs)"
     - AxiomsCheck OK（`#assert_only_allowed_axioms` 由来のエラーなし）
     - **sorry ポリシー（2026-06-15 改定: scaffold 許可, ユーザー裁可）**: `bin/count-sorry` の増加を即不合格にしない。
       hold するのは (a) **regression**（既存の証明済 decl が `sorry` に退化）と (b) **新規 axiom** のみ。
       **新 decl の faithful scaffold statement 追加（`theorem/lemma … := sorry`）は許可**（§13→§14→§16 interface-building の正常進行）。
       - 判定: count 増加時は `git diff --cached -- '*.lean' | grep -E '^[+-].*sorry'` を確認。
         追加 `+… sorry` が同 hunk の追加 `+theorem/+lemma`（=新 decl）に属すれば scaffold ⟹ **ALLOW**。
         既存 decl の proof が `+sorry` に置換（新 decl 行が伴わない）なら regression ⟹ **HOLD+報告**。
       - count-sorry は prose 偽陽性（sorry-free / sorryAx / `sorry'd` / backtick 引用）を除外済（残差 +5 は安定 prose）。
         絶対数 ground truth は build 警告 `uses .sorry.`。
   - 合格 → `git commit`:
     `Merge '<branch>' (<topic>): <要約>` + 本文に各単位 + 末尾に
     現行モデルの trailer (harness 既定; 2026-07-02 現在 Claude Fable 5)
   - 不合格 → `git merge --abort` で**報告**（何が落ちたか・どのファイルか）
   - **lint ratchet (issue 0138, 2026-07-22 正式化)**: build 合格後に `bin/check-warnings --diff`。
     ⚠ **hard-STOP ではない**（genuine math の合流を lint で止めない）:
     - 悪化ゼロ → そのまま。改善あり（hub の frozen wave landing）→ `bin/check-warnings
       --update-baseline` で baseline を下げ同 commit に含める。
     - レーンが新規警告を導入（悪化あり）→ main CI（`lean_action_ci.yml` の check-warnings step）を
       赤にしないため hub が reconcile: frozen×機械で安全に直せるなら in-tick 修正、active-lane 領域
       or owner 判断なら `--update-baseline` で grandfather しつつ owner を issue/note で flag（債務は
       追跡、破棄しない）。
     - tick 報告に「非 sorry 警告 N→M」を記載（従来の非公式メトリックを本 step に正式化）。
     - backlog が sorry のみになったら CI/gate を `--strict`（純ゼロ）へ切替、issue 0123 を 0138 に統合。
3. **新規 forward axiom を含む commit** (`axiom ` 宣言の追加を `git diff --cached` で確認) は
   自動合流せず abort → 報告（上記ポリシー）。
3b. **root closure 検査 (2026-06-11 追加, E の発見)**: 新規追加 `.lean` ファイル
   (`git diff --cached --name-only --diff-filter=A -- '*.lean'`) は **root closure から到達可能**
   でなければならない — `OddOrder.lean` に import 行があるか、closure 内の他 `.lean` が import
   している (例: hub の prefix-split で旧 module 名ファイルが新 Core を import する場合は追記不要)。
   どちらも無いと `lake build OddOrder` の対象外でゲートをすり抜ける (実例: S05b /
   S11_MsigmaANormal が closure 外で未検証だった)。孤立時 = hub が `OddOrder.lean` に import 行を
   追記してから build (機械的修正、abort 不要)。**pure re-export hub file (`Suzuki.lean` 等) の
   import 一覧漏れも同じ穴** — その場合は `OddOrder.lean` でなく該当 hub file に追記する。
   > **⚠ 頻発パターン (2026-07-17 tick、全 3 冊フェーズで再確認)**: 新フェーズは新 leaf を
   > 大量に切るため root closure 漏れが**常態的に起きる**。同 tick で a
   > (`Ch09/{NilpotentResidual,SubnormalSocle}` — `OddOrder.lean` 漏れ) と b
   > (`Suzuki/KCyclic` — `Suzuki.lean` hub 漏れ) の 2 レーンで独立発生。検出の確証 =
   > **build jobs の +N が新 module 数と一致するか** (漏れていた module は「初回 elaborate」ゆえ
   > jobs が増える; 4363→4365 で a の 2 module、4365→4366 で b の 1 module を確認)。
   > lane 側は新 leaf 作成時に hub/`OddOrder.lean` へ import 追記するのがデフォルト (LAUNCH.md
   > 記載) だが徹底されないことがある。hub は **step 3b を毎 tick 必ず実行** (`--diff-filter=A` +
   > importer grep) し、漏れは機械的修正で塞ぐ。lane a は本 tick で自己修正コミット
   > (97540ff6) も出した。
4. **サイズ watch (粒度規約の enforcement, 2026-06-11)**: 合流後に
   `git diff HEAD^ --stat -- '*.lean'` で touched .lean の現在行数を `wc -l` 確認。
   **1,500 行超の既存ファイルへの追記**を検出したら: 合流は維持しつつ ⚠ flag をサマリに含め、
   分割 issue が未起票なら起票する（分割の実施 owner = hub。lane の frontier と衝突しない
   凍結境界で prefix-split する）。lane 側のデフォルト（新主結果番号 = 新 leaf）は LAUNCH.md に記載。
5. **push**: 合流 commit が 1 件以上成立していれば最後に `git push origin main` (exit 0 確認、
   失敗は報告)。変化なし/全 abort なら push しない。
6. **サマリ報告**: 各レーン {マージ済 N commits / コンフリクト abort / 待機 / 変化なし} + 未マージ残数
   + サイズ flag + push 結果。
6.5. **レーン生存確認 (issue 0131、2026-07-25 に正式ステップ化)**: 毎 tick、各稼働レーンの 3 点シグネチャで
   停止を検出する: (i) transcript mtime (`ls -t ~/.claude/projects/-home-ywr-odd-order-<lane>/*.jsonl | head -1`
   が **20 分超凍結**)、(ii) 最終 commit 時刻 (`git -C /home/ywr/odd-order-<lane> log -1 --format=%cd`)、
   (iii) worktree cwd プロセスの child 有無 (idle)。`git log` 単独では「大きめの commit 執筆中」と区別
   できないので必ず transcript mtime と併用。3 点そろったら **transcript 末尾で 3 類型を判定**
   (issue 0131 の 2026-07-20 17:08 追記が正本):
   - `ScheduleWakeup({stop:true})` **無し** + 達成報告で turn 終了 → **障害 (第 1 類型)** → ユーザーへ報告
     (⚠ tail が `assistant text` でも mtime frozen なら停止 — 「稼働中」と即断しない)
   - `stop:true` **有り** + 理由が「区切り/裁定待ち」 → 第 2 類型 (規約と食い違い、要是正) → 報告
   - `stop:true` **有り** + 理由が **context 枯渇** + handoff 完備 → **規約準拠** (是正不要、再開依頼のみ)
   hub からレーンの unsupervised セッションへメッセージは送れない ([[cross-lane-sync-via-notes]]) ため、
   検出時の行動は**報告のみ** (再開はユーザー操作)。
7. **❄ FROZEN 2026-06-18 — LOOP GATE VERDICT 維持 (2026-06-17 追加, [`lane_loop_policy.md`](lane_loop_policy.md); LOOP GATE 機構停止中。⚠ 以下の例中のレーン名 h/G/F/B は 2026-06-28 改名前の旧名 = 履歴。現行レーンは a/b/c)**: 各 worktree の
   `LAUNCH.md` 冒頭「▶ LOOP GATE」ブロックは各レーンが起動時に `/loop` を自己選択する判定材料。**毎 tick で
   再監査はしない** (重い)。代わりに、今 tick のマージが**他レーンの gate を解いた**ときだけ VERDICT を見直す:
   - `typeP_duality` (lane-h) が proved → G の conjunct 2/assembly + F の §16/POLE-2 が解禁 → G/F の VERDICT を
     `STOP`→`LOOP`/`LOOP_THEN_STOP` に更新しうる。
   - σ-gap (`C_M(Q)≤M_σ`, issue 8012) が proved → G の conjunct 3-5 が unconditional 化。
   - (6.8) capstone (`S08_CoherenceTheorems:59`) が閉じた → B を次タスクへ。
   判定 = マージ差分に上記 gate statement の `sorry` 除去が含まれるか。含まれれば該当レーンの LAUNCH.md VERDICT
   行を更新 (worktree LAUNCH.md は git-excluded ゆえ直接編集可・build 不要)、含まれなければ触らない。サマリに
   「VERDICT 更新: \<lane\> \<old\>→\<new\>」を 1 行。**新規レーン投入時や VERDICT が古い疑いがあれば** 単発で
   loop-readiness 監査 (read-only、frontier ファイル + cite 先 sorry 有無を grep) を回して VERDICT を引き直す。

## 注意

- **⚠ live-branch merge race (2026-07-12 tick 15 実害 → 2026-07-15 手順更新)**: レーンは 60s wakeup で数分おきに
  commit するため、hub の step 1.5 scope-check と `git merge <branch>` の**間**に新 commit が積まれると、
  merge は check していない commit まで取り込む (実例: a@29b08747 を check → merge 時に a が 700ba71f を
  積んでおり merge 38df2e1d の第 2 親が 700ba71f になった; 遡及チェックで clean を確認・build/AxiomsCheck は
  merged tree に対して有効だったので実害なし)。当初は tick 冒頭の一括 SHA pin で防止したが、
  **現行は各 lane 訪問直後に branch を trial mergeし、その `MERGE_HEAD` を exact tip として固定する**。
  以後の 1.5/1.6 diff と build は `MERGE_HEAD` / staged tree に対して行う。branch の超過分は次回訪問へ回り、
  commit message の `@<sha>` には `MERGE_HEAD` の SHA を書く。
- A と B は `AxiomsCheck.lean` 末尾を共有 hotspot として両方追記 → **マージ毎にコンフリクトしうる**が、
  独立ブロック（別定理の axiom ガード）なので両保持で機械的に解決可。先頭 import 部も同様。
- `git merge --abort` は `--no-commit` で止めた状態でもコンフリクト状態でも有効。
- `lake update` 禁止（共有 mathlib rev を壊す）。コミットは **main のみ**。
- 各レーンの worktree (`/home/ywr/odd-order-<slug>`) には**触らない**（`git log main..<branch>` で読むだけ）。
- loop は同一セッション継続。マージ済みコミットは git が source of truth ゆえ状態ファイル不要
  （`main..<branch>` が毎回「まだ取り込んでいない分」を正しく返す）。
- **`git diff main..<branch>`（2-dot=端点差分）でマージ内容を判断しない**。各レーンは他レーンの成果を
  恒久的に持たない（例: B=b-peterfalvi は A=a-keystone の RepresentationTheory/Extraspecial 系を持たない）ので、
  端点差分は「他レーンファイルの大量削除」という**幻**を見せる（実測 4149 deletions に見えたことがある）。
  実マージは merge-base からの 3-way ゆえ、それらは「main 側のみ追加」扱いで保持される。マージ内容の確認は
  必ず `git merge --no-ff --no-commit` 後の `git diff --cached --stat`（=実際に staged される加算分）で行う。
  **step 1.5 の範囲逸脱チェックも同じ罠**: マージ前の「レーンが変更したファイル」は必ず 3-dot
  `git diff --name-only main...<branch>`（merge-base からの branch 側）で取る（2-dot だと遅れている分を誤検出）。
- **⚠ 3-dot でも "multiple merge bases" 警告時は誤検出しうる（2026-06-28 実害, lane-f が S11=lane-b 所有を逸脱と誤判定）**:
  レーンが `git merge main` を繰り返すと main↔lane 間に **merge base が複数**でき、`git diff main...<branch>` は
  その中から**1 つ（しばしば古い方）を自動選択**する（`warning: multiple merge bases, using <old-sha>` が出る）。
  古い base を選ぶと「その base 以降に main 側へ入った他レーンの成果」が branch 側差分に紛れ込み、**自所有外
  ファイル（例 S11）が逸脱判定に出る**。これは genuine 逸脱と見分けがつかないので、**即 STOP せず以下で誤検出を排除**:
  (1) **分岐元 merge-base との diff**: `git merge-base --all main <branch>` で全 base を出し、各 base に対し
     `git diff <base> <branch> -- <疑い file>` が **0 行**なら、そのレーンはそのファイルを**一切編集していない**
     （古い base 由来の見かけの差分）。(2) **疑い commit の per-commit 確認**: `git show <lane-HEAD> -- <疑い file>`
     が `+theorem/+lemma/+def` を含まない（merge で取り込んだだけ）なら自作編集でない。(3) **最終確定 = trial-merge
     staged**: `git merge --no-ff --no-commit <branch>` 後 `git diff --cached --name-only` に疑い file が
     **含まれなければ**、3-way が main 側（最新）を保持＝逸脱なし。staged に疑い file が出て内容が絡むなら genuine 逸脱で abort+STOP。
  - 要するに **3-dot の逸脱フラグは「疑い」止まり**。分岐元 base diff=0 + trial-merge staged に無し、で誤検出を排除して合流可。
- **`axiom` 判定 grep は必ず `.lean` に scope する**: `git diff --cached | grep '^\+\s*axiom '` は
  **issue/notes の markdown 中の散文（"axiom footprint = …" 等）を誤検出**する（2026-06-22 実害）。
  正しくは `git diff --cached -- '*.lean' | grep -E '^\+axiom [A-Za-z_]+ *[:({]'`（行頭 `axiom <ident>` の
  実宣言のみ; staged が markdown のみなら空）。sorry +/- 判定も同様に `-- '*.lean'` scope。
- **worktree の working-tree grep (`cd <wt> && grep -rnE … OddOrder/`) は未コミット WIP も数える** →
  sorry 増の**誤報源**。lane が draft 中の未追跡/未コミット `.lean`（実例: Thm 3.6 stub `S03f_Thm36.lean`）の
  sorry も拾うため、worktree では +N に見えても branch HEAD（コミット済）は不変なことがある。**merge が運ぶのは
  コミット済状態のみ**ゆえ、sorry ゲートの authoritative 判定は **trial merge 後に main 側で `grep -rnE … OddOrder/`**
  （= 実際に staged されるコミット済加算分）で行う。staged が notes のみ/該当 .lean を含まなければ worktree の +N は誤報。
- **⚠ 「空 sync merge」判定は stale になる (2026-07-11 実害)**: tick 冒頭で `git diff main <lane>` が
  空 (= sync のみ) でも、a/b の merge・build を待つ間に lane が新 commit を push しうる。空と判断して
  `git merge --no-ff <lane>` を **--no-commit なし + push 連鎖**で実行した結果、未検証 .lean (新 leaf
  74 行) が build 前に main に載った (事後検証で green・実害なし)。対策: (1) **merge 直前に
  `git rev-list main..<lane>` を再確認** (tick 冒頭の値を使い回さない)、(2) sync-only でも
  **常に `--no-commit` で trial merge** し staged を見てから commit、(3) **push は全レーン検証完了後の
  単独コマンド** (merge と同一 bash に連鎖させない)。
  - **⚠⚠ 再発 (2026-07-11 同日 2 度目、今回は実害 = red main push) → SHA 固定を必須化**: 上記 (1)-(3) が
    advice 止まりで再度素通りした (検査は `0a128d16` 時点、merge が未検査の新 tip `5f2e11cb` を取り込み、
    その中の AxiomsCheck assert 5 本が sorryAx 依存で red — c は codex 運用で push が速く、检査→merge の
    数分の窓でも stale 化する)。**以後必須の手順**: tick 冒頭で `TIP=$(git rev-parse <lane>)` を採取し、
    範囲逸脱・axiom・sorry の全検査を **その $TIP に対して**行い、merge も **`git merge --no-ff $TIP`**
    (branch 名でなく **SHA を merge**) で行う。これで検査対象と取り込み対象が構造的に一致し、stale-tip
    混入は不可能になる。tick 中に lane が進んでいれば差分は次 tick に自然に回る。
  - **⚠ `lake build … | tail` は exit code を隠蔽する (2026-07-11 実害の相方)**: pipe の最終コマンド
    (tail/grep) の exit 0 が build 失敗を上書きし、後続の `git push` 連鎖が red を通した。**build は
    `> log 2>&1` リダイレクト + `echo EXIT=$?` で exit code を明示確認**し、push は green 確認を
    **読んだ後の別 bash** で行う (上記 (3) の強化; [[lean-build-discipline]] の「build 検証と commit は
    別 bash」は push にも適用)。
- **lane が merge 済み commit を amend した場合** (実例 2026-06-11, `b582007f`→`9581665d`):
  ff 同期が "Diverging branches" で落ちる。対処: (1) `git log --oneline -3 <branch>` +
  `git merge-base main <branch>` で amend (親が main の merge 前 HEAD) を確認、(2) 通常の
  `--no-ff --no-commit` trial merge — 内容が上位集合なら自動解決またはファイル単位 theirs、
  (3) `git diff main <branch> -- <file>` = 0 なら実差分は付随物 (guard 等) のみ。通常ゲートで commit。
  予防 = 各 LAUNCH.md に「commit 後の amend/rebase 禁止」を明記済み。
- **前セッションがマージ途中で死んだ場合**: 新セッション開始時に `git status` が staged 変更 + `MERGE_HEAD`
  を持ち、`git merge` が `fatal: ... MERGE_HEAD exists` を返す。これは「コンフリクト解決・staged 済みだが
  build/検証/commit 前」の状態。対処: (1) `cat .git/MERGE_HEAD` がどのレーン branch HEAD と一致するか確認、
  (2) `git grep -lE '^(<<<<<<<|=======|>>>>>>>)'` でコンフリクトマーカー残存なしを確認、(3) 通常の
  build + AxiomsCheck + sorry 不増ゲートを通し、(4) 合格なら `git commit` で完結（不合格は `git merge --abort`）。
  注意: 真の pre-merge sorry 数は既にマージ適用後なので、`git show main:<file>` で touched .lean を main HEAD と比較する。
- **⚠ cron × 手動マージの競合 (2026-06-11 実害)**: cron が**並行発火**して、進行中の `--no-commit`
  trial merge を `MERGE_HEAD exists` 検出 → `git merge --abort` で**消す**事故が発生 (F の 12.18
  staged merge が tree-clean に巻き戻り、952 行の取込が消えた)。対策 2 つを cron prompt に組込み済:
  (1) **cron 冒頭ガード**: `.git/MERGE_HEAD` 存在時は「前マージ進行中, skip」で即終了、**絶対に
  abort しない**。(2) **手動マージは atomic**: merge→build→commit を 1 ターンで完結し staged のまま
  長時間放置しない (放置中に次 tick が衝突)。加えて merge 出力は `> /tmp/merge.log 2>&1` へ退避
  (S12_Lemma1218 の大量 hunk で「Auto-merging」が 100+ 行出て端末が壊れ、誤診の元になった)。
  マージ結果の正否は `git show :<file> | wc -l` で**期待行数**を実値確認するのが確実
  (索敵: theirs が取り込まれたか。base==ours で theirs 変更なら theirs 採用が正)。

## 現状メモ

> 📜 旧世代 (list 形式) の tick 記録は全て [`log/merge_monitor_ticks.md`](log/merge_monitor_ticks.md) の
> 「旧『現状メモ』ログ」節へ退避 (0139、2026-07-24)。現況は冒頭の直近 tick を見る。

### ⚠ フルビルドの検証で踏んだ罠 2 件 (2026-08-07, hub session)

1. **`lake build | tail` は EXIT を隠す**。`timeout N lake build OddOrder 2>&1 | tail -6` の
   終了コードは `tail` のもので常に 0。実際には build が失敗していたのに「green」と
   報告してしまった。⟹ **ログをファイルに落として `echo "EXIT=$?"` で捕る**:
   `lake build OddOrder > log 2>&1; echo "EXIT=$?"`。
   (CLAUDE.md の「hub tick gate の罠」に既出だが、background 実行の task-notification が
   返す exit code も**パイプ後のもの**なので同じ罠にかかる。)

2. **同一 worktree で leaf build と full build を並行させない**。background の
   `lake build OddOrder` が走っている最中に leaf を `lake build <Module>` すると、
   leaf の olean が一時的に消えて full build 側が
   `failed to open file '….olean': No such file or directory` で落ちる。
   **偽の赤**なので原因を誤診しやすい。⟹ full build は他のビルドを止めてから逐次で回す。
