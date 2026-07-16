# FT 形式化 — 経路 policy + signature 先行整備（canonical, 2026-06-15）

> **⚠ フェーズ移行 (2026-07-16)**: `feitThompson` axiom-clean 完成 (2026-07-15) を受け、ユーザー指示で
> **全 3 冊完全形式化フェーズ**へ移行。**本ファイルの「FT 経路限定」部分 (§0 item 1・item 4 の限定 bullet・
> §3 の on/off-path 分類) は失効** — 現フェーズの scope 正本 =
> [`three_books_full_survey_2026_07_16.md`](three_books_full_survey_2026_07_16.md)、レーン配分 =
> [`lane_reallocation_2026_07_16.md`](lane_reallocation_2026_07_16.md)。**存続する原則**: §0 item 2 (signature
> 先行 pin)・item 3 (doneness = 構成可能性)・item 4 の順序 (上流優先+文書順; 「FT 経路」→「3 冊スコープ」に
> 読み替え、冊間の文書順 = Isaacs → BG → Pf)・item 5–8 (frontier 自律・claim-before-build・off-spine 手順・
> 重複裁定)。
>
> **このファイルが「何が FT 経路上か / どこを触るか / どう並列化するか」の正本。**(旧フェーズ)
> 毎セッション再発する「これは FT に必要なのか?」の混乱を止めるための単一参照点。
> 横断スナップショット（[`ft_master_roadmap_2026_05_29.md`](ft_master_roadmap_2026_05_29.md),
> [`feitthompson_critical_path_2026_06_03.md`](feitthompson_critical_path_2026_06_03.md),
> [`ft_mainline_dependency_closure_2026_06_02.md`](ft_mainline_dependency_closure_2026_06_02.md)）は
> 履歴として温存するが **scope/policy の判断はこのファイルが優先**（あれらは日付固定で stale）。
> 個別ゲートの掘り下げは各 `notes/peterfalvi/*.md` / `notes/bg/*.md` / `issues/` が正本。

---

## 0. 方針（TL;DR）

1. ~~**作業は FT critical path 上に限定する。**~~ **⚠ 2026-07-16 失効** (FT 完成 → 全 3 冊フェーズ、冒頭注記)。
   off-path という区分自体が解消 — 3 冊の全番号付き結果が in-scope (低優先繰延 2 件のみ後回し)。
2. **FT 経路上の Peterfalvi character-API signature は先行して pin する。**
   §10–16 spine が opaque field を「§3–§9 の faithful signature への cite」に置換できる状態を作る
   → downstream は stable interface を cite、upstream（B）は独立に proof を埋める → **並列化が効く**。
3. **目的 = FT への実質的証明の積み上げ。短期的な `sorry` 削減は目的でも指標でもない**
   (CLAUDE.md「進捗の測り方」が正本)。judge 基準は `sorry` 数でなく
   **opaque carrier / posited data を実際に構成したか・free field を実証明に置換したか**
   （[[scaffold-sorry-free-not-done]]）。
   - ⚠ **逆向きの誤りに注意**: 「上の carrier が free field で bypass しているから、この前提を
     閉じても `feitThompson` の sorry は今は減らない」を deprioritize / hedge の理由にしない。
     それは scaffold の枚数を測っているだけで、その仕事が本物の必要な数学かは別。
     **"FT-orphaned"・"閉じても sorry 減らない" の言い回しは使わない**（自家製ジャーゴン、誤読を招く）。
     honest architecture の genuine prerequisite なら、今 consumer 0 でも淡々と完遂する
     （[[feedback-cite-sorried-lemmas-if-signature-correct]]）。
4. **作業順序 = 上流優先 + 文書順タイブレーク**（全レーン共通の標準方針、ユーザー 2026-06-22）。
   - **上流優先**: 各レーンは依存の**上流側から**進める。下流の gated endpoint を先回りで
     skeleton 化（hypothesis 引数化 engine + assembly）するのは**上流が真に block されているときの
     保険**に留め（[[feedback-gated-endpoint-skeleton-pattern]]）、基本はまず上流 prerequisite を埋める。
   - **文書順タイブレーク**: 着手可能な選択肢が複数あるとき（どれも上流端）は、
     **教科書（BG / Peterfalvi）上で出現が早いもの**（番号の若い §/定理/補題）から着手する。
     線型 spine（BG §1→§16, Pf §3→§16）では「上流＝文書で早い」がほぼ一致する。
   - ~~**FT 経路限定**: 対象は item 1 の on-path のみ。off-path は凍結（順序判断の対象外）。~~
     **⚠ 2026-07-16 失効** — 対象は 3 冊スコープ全体（冊間の文書順 = Isaacs → BG → Pf）。
   - これは**作業の選択順序**の規則であり、doneness 判定（item 3）とは独立。
5. **レーン内 frontier 選択は自律判断する（聞きに来ない）。**（ユーザー裁定 2026-07-01）
   「次に何を触るか」は item 4（上流優先 + 文書順）で一意に決まる ⟹ **frontier 選択で hub/ユーザーに
   聞かない・報告して止まらない**。停止してよいのは STOP 条件（想定違反・allowlist 外新 axiom・
   signature 無断変更）と真の設計分岐のみ（[[feedback-quick-win-not-a-criterion]]）。gated / deep / quick-win
   の有無は着手判断の基準でない。
   - **(A) gated endpoint の扱い**: 自レーン最上流 sorry が他レーン coherence 等に gated でも deferral
     理由でない。**さらに上流の ungated な genuine math（未所有 shared infra を含む）に降りて実証明する**
     （例: Pf (13.9.b) が §13 char に gated → [Is] 3.14 field-norm≥1 =
     `OddOrder/Algebra/GaloisRationalInteger` を実証明）。gated endpoint 自体は sorried-cite skeleton で
     前倒し（[[feedback-gated-endpoint-skeleton-pattern]] [[feedback-cite-sorried-lemmas-if-signature-correct]]）。
   - **(B) shared infra は常に in-scope**: 未所有 leaf（`OddOrder/Algebra|GroupTheory/**` 等）を新設して
     genuine FT math を積むのは、consumer が他レーンの endpoint でも in-scope。territorial なのは
     **所有 file のみ**（[[cross-lane-sync-via-notes]]）。
6. **shared infra は claim-before-build（policy 5(A)(B) の重複防止、ユーザー裁定 2026-07-01）。**
   policy 5(A) で複数の gated レーンが同じ上流 infra に収束しうる ⟹ 未所有 leaf の新設は沈黙で行わない：
   1. **検索必須**: 着手前に repo を教科書番号 + descriptive 名 2 案以上 + import grep で検索
      （[[verify-port-state-by-number-not-coq-name]]、既存を再構築しない — 実例: S09=§7 chiRho 重複、issue 0089）。
   2. **issue で claim**: 不在確認後、**9000 番台（shared-infra 専用レンジ）で issue を 1 件切る**
      （target leaf + 補題名/教科書 ref + lane）。着手の最初の commit で main に乗せる。
   3. **scan 必須**: 全レーンは shared infra 着手前に **open 9000 番台 issue を scan**（定期 main 同期にフック）。
   4. **hub dedup**: merge_monitor が重複 claim / 同一 ref の 2 leaf を検出 → STOP flag。浪費は ~1 tick に有界。
   所有 file 内の work は claim 不要。正本手順 = [`issue_management.md`](issue_management.md) / [`merge_monitor.md`](merge_monitor.md)。
7. **cluster-off-spine 手順（P2「クラスタは枯渇しない」の前提が破れた場合、ユーザー裁定 2026-07-01, issue 4015）。**
   worker が自割当クラスタの on-spine ungated work が枯渇/off-spine（vestigial 含む）と **code-level で検証**したら：
   1. **user に AskUserQuestion しない** — 再配分 *判断* は hub の機能（channel 違い）。
   2. 検証を issue に記録し、**reallocation を hub に defer**（hub 宛 async issue、[[cross-lane-sync-via-notes]]）。
   3. **待たず**、[[lanes-are-equivalent-no-specialty]] + policy 5(A)(B) で価値×独立性の次の on-spine 上流に
      **claim-before-build（9000-issue、policy 6）**で着手する（hub 再配分を待つ間も idle しない）。
   4. **hub は再配分時に既存の off-path/vestigial 判定（issue 1004 等）を必ず勘案する**（issue 0092↔1004 の
      「移し先も vestigial だった」齟齬の再発防止）。
   5. 「off-spine と判明」評価は必ず **code-level（grep / spine footprint / carrier 精読）**で下す
      （[[scaffold-sorry-free-not-done]] [[verify-port-state-by-number-not-coq-name]]）。楽観 label を継承しない。
   - **spine-consumed sorried input の扱い**: 消費が genuine（vestigial でない）と確認されたら、honest 化は
     (α) 構造 route を建てる → (γ) 明示 sorried input として許容し spine が載る事実を**隠さず flag** の順で降りる。
     **(β) vestigial finding での dodge は消費が実際に off-path のときのみ**（消費 footprint を code-level 検証してから）。
8. **重複発覚時は hub 裁定（ユーザー裁定 2026-07-02, issue 9000）。** claim-before-build（policy 6）の search が
   他レーンの **in-progress work を見落とす**ことがある（同一 math が別レーンの *所有 file* 内で別抽象レベル・
   別 namespace で構築中のとき。実例: σ-theory infra を `GroupTheory/**` leaf で claim したが、lane a が S11 で
   **subgroup-level に同じ Singer 機構を concurrent 構築**していた、2026-07-02）。重複を発覚したレーンは：
   1. **不 unilateral**: どちらの版が勝つか / どちらを消すかを沈黙で決めない。
   2. **不 user-ask**: AskUserQuestion しない（home 一本化の *判断* は hub の機能、channel 違い = policy 7 と同型）。
   3. **hub に flag**: 重複を claim issue + hub 宛 async issue に記録（どの補題が重複・どのレーン・どの home が自然か・
      非重複部は何か）、home 一本化を hub に defer。
   4. **待たず非重複部を進める**: genuine に非重複な piece は続行（[[lanes-are-equivalent-no-specialty]]）、
      重複 piece は hub 裁定まで**凍結**（重複を広げない）。
   5. **hub 側の予防（再発防止）**: (a) policy 6 の search は shared-infra namespace だけでなく、**同一 math content が
      他レーンの owned file で in-progress でないか**も確認する（consumer が他レーンにいる infra は特に、grep は
      subgroup-level / module-level 両抽象を跨ぐ）。(b) hub が「lane X が cite する infra」を別レーンに再配分するとき
      は **lane X が既にその infra を build 中でないか先に確認**する（policy 7 step 4「既存判定を勘案」と同型の齟齬防止）。

---

## 1. FT critical path（symbol-anchored, 不変の背骨）

> ✅ **2026-07-02 全面更新**: FT 層の配線は完了 — `FeitThompson.lean` は**実 sorry 0**。旧記述
> （「`sectionSixteenHypothesis_of_isMinimalSimpleOdd` が唯一の実 sorry」「S16⊃…⊃S10 の extends 鎖」）
> は stale だったため書き換え（旧版 = git 履歴）。**行番号は書かない** — 数日で rot する。decl 名で参照。

```
feitThompson                                       OddOrder/FeitThompson.lean   ✅ sorry-free
└ noMinimalSimpleOdd                               ✅ sorry-free（配線済）
  ├ sectionSixteenHypothesis_of_isMinimalSimpleOdd ✅ sorry-free
  │   = sectionSixteenHypothesis_of_inputs ∘ section16Inputs_of_isMinimalSimpleOdd
  │     （3-producer flat assembly — extends 鎖ではない。検証 = ft_frontier_remap_2026_06_25.md §0）
  │     producer 1: Section16MaximalPair       ← S14.theorem88_caseB_holds ✅ proven
  │     producer 2: Section16TypePStructure    ← S12 chain（card_kappaHall_lt_of_isTypeIIIorIV ✅）
  │     producer 3: Section16CharacterData     ← W-side producer ✅（closed/1004; tauS/tauT は vestigial）
  └ noMinimalSimpleOdd_of_section16 → BG.AppC.final_contradiction → S16.nonexistence_of_G   ✅
```

残 obligation は FT 層でなく **Pf §9–§16 の分散実 sorry（~74、comment-strip census 2026-07-02）**に住む:
- **唯一の bare FT-spine sorry** = `S12.exists_zeta_residual_not_orthogonal`（Pf 11.8、lane a frontier）
  — proven な `card_kappaHall_lt_of_isTypeIIIorIV` が cite する唯一の残余。
- theorem88 route の sorried floor = `exists_typeICovering` ×2（lane b、route B = 8022/0096）+
  `S09.card_G0_lower_bound`（lane a、issue 0044 裁定 2026-07-02）。
- `Peterfalvi.S16.Hypothesis` は **flat record**（現在地 = `S16_NonExistenceGCore.lean`）。

---

## 2. 2 トラック構造（合流点 = S16.Hypothesis）

S16.Hypothesis の構成は 2 本の独立トラックの合流:

### Track L — local analysis（→ G1）
Isaacs Ch.1–7 ✅ → BG App.A/B ✅ → BG §1–§16 local 解析 → **BG §16 endpoints**
（`BG.Ch4_FamilyOfMaximal.S16_MainResults`: Thm A–E / Prop 16.1 / Thm I–II）。
Pf §10 が `S16_MainResults` を **import 済**（statements 在・sorried・cite 可）= **G1 ゲート**。
担当 = ~~lanes F / G / H~~（旧レーン名 = 履歴。現行 3 レーン a/b/c、正本 =
[`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md)）。**真の FT ボトルネック**（§14–16 が active frontier）。

### Track C — character theory（→ G2）
Pf §3–§9 character API（Dade isometry, coherence, 指標 index 族）。
Pf §10–16 spine がこれを consume = **G2 ゲート**。担当 = ~~lane B~~（旧レーン名 = 履歴。現行は
coherence infra = lane b、正本 = `ft_lane_reallocation_2026_06_28.md`）。

### 合流 — Pf §10–16 spine
G1（BG §16, import 済 — spine 消費は sorry-free の Prop 16.1 のみ、BG は 2026-07-02 凍結完了）と
G2（§3–§9 char API — **供給側は signature/proof とも完成** (S03–S08 帯 実 sorry 0)、consumer 側
cite 置換 (endpoint A) も wiring 済）を consume し S16.Hypothesis を生む。
**旧「signature gap」（opaque field 代用・§5/§6/§8 未 import）は 2026-06-15〜07-02 に解消済**（§4 は履歴）。

```
Isaacs✅ ─ BG AppA/B✅ ─ BG §1-16 ─┐
                      (Track L=G1) │
                                   ├─→ Pf §10-16 spine ─→ S16.Hypothesis ─→ AppC✅ ─→ feitThompson
   Pf §3-9 char API ───────────────┘
              (Track C=G2)
```

---

## 3. on-path / off-path 分類 + 判定原則 — ⚠ 2026-07-16 失効 (全 3 冊フェーズで区分解消; 以下は履歴)

**判定原則**: 「`sectionSixteenHypothesis_of_isMinimalSimpleOdd` の **honest** な構成が推移的に必要とするか」。
これは **math architecture 上の判断**であって、現在の import / consume 状況ではない。
今 §10–16 spine が opaque field で bypass していて未 cite でも、honest 証明がいずれ必要とするなら **on-path**
（= deferred-payoff な genuine prerequisite。今 consumer 0 でも本物の仕事）。honest 証明が必要としないものだけが off-path。
**「今 consume / import されていない」を off-path の根拠にしない**（[[scaffold-sorry-free-not-done]] の逆向きの誤り）。

### ✅ ON-PATH（ここを作業）
| 区分 | 範囲 | 担当 (⚠ 旧レーン名 = 履歴; 現行 a/b/c は `ft_lane_reallocation_2026_06_28.md`) |
|---|---|---|
| Track L | BG §7–§16 spine + App.A/B/C | ~~F / G / H~~ → BG は完了・共有凍結 (2026-07-02) |
| Track C | Pf §3–§9 character API の **§10–16 が consume する slice のみ**（§4 の surface） | ~~B~~ → b (coherence infra) |
| 合流 | Pf §10–16 spine（opaque→cite 置換 + 実証明） | ~~B / §10–16 owner~~ → a (§10–13) / b (S14) / c (S15–16) |

### ❄ OFF-PATH（honest な FT 証明が必要としない — FT が閉じるまで凍結、新規着手しない）
- **Pf Appendices**（`FeitSibley`/`Huppert`/`NearFields`/`SemilinearField`/`Suzuki`/`Suzuki2Groups`）
  — honest な odd-order 矛盾が推移的に必要としない見込み。⚠ 「§10–16 から未 import / AxiomsCheck guard のみ」は
  off-path の**ヒント**であって基準ではない（未 import = off-path とは限らない）。各 appendix が honest spine に
  本当に不要かは math で再確認してから凍結を当てにする。
- **Pf §5/§6 の full-scope completeness** — honest な §10–16 spine が必要としない部分
  （例: §6 certain-type のうち §4 の μ/η/ν constructor + coherence producer **以外**、
  (3.8) trichotomy の §10–16 非依存部分、(7.10) 等）。
- Isaacs / BG の FT route 外の網羅、3 冊完全形式化の残り。

> ⚠ 旧文 (2026-06-15): 「3 冊全部形式化」は長期スコープだが FT を閉じる作業とは別フェーズ、当面 FT 経路限定。
> **→ 2026-07-16: その「別フェーズ」に正式移行 (FT 完成)。凍結は解除、3 冊の全結果が in-scope。**

---

## 4. signature 先行整備（並列化の核）

> ✅ **2026-07-02: 本節はほぼ discharge 済（履歴として温存）**。§3–§9 supply は全 pin + proof 完
> （S03–S08 帯 実 sorry 0、(6.8) `sibleySetup_is_coherent` も proven）。endpoint A の consumer 側
> wiring も完了。残 = `sibleyTarget_*` producer（issue 7001 — 2026-07-02 裁定: H0C = lane a +
> soundness 監査必須 / S = vestigial 処分 / frobI = TI-case 限定）と E(残) = §10 hard content のみ。
> 下の「問題」「S10 が import するのは…」は当時の記述。

### 問題（2026-06-15 当時）
Pf §10–16 spine は G2（§3–§9 char API）を **opaque field（Prop/carrier）で代用**しており、
§5/§6/§8 を **import も cite もしていない**（S10 が import するのは S04, S07, S09 のみ — その後
S10_CoherenceWiring が S08 を import し解消）。帰結:
1. §3–§9 が landing しても §10–16 は **自動で benefit しない**（手で wiring が要る）。
2. 各 lane が互いの proof を待つ形 → **並列化が効かない**。

### 解（= ユーザー戦略「signature 先行整備」）
FT 経路上の §3–§9 signature を **先に pin**（faithful な `def`/`theorem`、sorried 可、build-green +
axiom-clean）→ §10–16 の opaque field を **その signature への cite に置換**（carrier 実体化）→
§3–§9 lane が **独立に** proof を埋める。interface 固定で lane 間を decouple。
（既存パターンの一般化: S16.Hypothesis / BG §16 statements は既に pin-and-cite 済。）

### inventory — §10–16 が consume する §3–§9 signature surface（pin 対象）
正確な Lean 形は実装時設計。下表は **endpoint の同定**（consumer の opaque field ↔ supplier）。

| # | pin する endpoint | consumer（現 opaque, file:line） | supplier（§3–§9） | 状態 |
|---|---|---|---|---|
| **A** | maximal 族の coherence producer `Nonempty (S07.IsCoherent …)` | S12 `CharacterParameters.coherent_S`:127 / S15 `S_coherent` / §11–13 coherence riders（~27 sorry） | S08 `sibleySetup_is_coherent` | ✅ **(6.8) proven**（S08 帯 実 sorry 0、2026-06 末）。残 = `sibleyTarget_*` producer（issue 7001） |
| **B** | ω-grid constructor `ω : Fin q→Fin p→CF ↥W` | S15 `omega`:130 / S12 `CharacterParameters` | S05 σ-isometry（`chiFam`/`omegaIrrEquiv`, proof 在） | ✅ **pinned** = `S05.TICyclicHypothesis.omegaGrid`（`S05_OmegaGrid.lean`, 2026-06-15; `charEquiv` を W1/W2 両方向に一般化 + 0↦trivial anchor `omegaGrid_zero_zero`, axiom-clean） |
| **C** | (3.2) σ/τ₃ `IntegralCharacterMap ↥W G` | S15 `tau3`:144 + `eta_eq_tau_omega`:146 | S05 `sigma`（proof 在） | ✅ **pinned** = `S05.TICyclicHypothesis.sigmaIntegral`（`S05_IntegralSigma.lean`, 2026-06-15; `sigma.restrictScalars ℤ` + 性質 5 補題, axiom-clean） |
| **D** | μ/ν 族 + (13.1.e) | S15 `mu`:132 / `nu`:133 | S06 (4.3) certainType（proof 在） | 🟡 **(13.1.e) relation pinned** = `S06.Hypothesis.induce_omegaColumnDiff_mu_diff`（`S06_MuColumnBridge.lean`, explicit δ·(μ_i−μ_0) form, `h : S06.Hypothesis` 引数化）。残 = full Fin-grid `muGrid` + S15 整合（W₂-col→Fin p / charEquiv W₁ / Ind の compHom 形 / W-instance context）は **§10-16 owner 側 wiring**（S06.Hypothesis-for-S が要 = §14 構造ゲート） |
| **η** | `eta` + (13.1.d) | S15 `eta`:131 / `eta_eq_tau_omega`:146 | B+C 合成 | ✅ **B+C から自動**（`eta := tau3 ∘ omega`, `eta_eq_tau_omega := rfl`; 新規 pin 不要） |
| **E (ω^σ)** | `omegaSigma` の ω^σ = σ(ω) | S12 `omegaSigma`:111 / S15 `eta`:131 | B+C 合成 | ✅ **pinned** = `S05.TICyclicHypothesis.omegaSigmaGrid`（`S05_OmegaSigmaGrid.lean`, σ∘ω + `ω^σ ∈ ZIrr G`, axiom-clean）。`eta` も同一ゆえ (13.1.d) は rfl |
| **E (残)** | `zeta`(10.2) / `d`,`δ`,`n`(10.3) / `mu`,`alpha` for M + coherent ext | S12 `CharacterParameters` | §10 analysis | ⛔ **§10-gated**（`IsMinimalSimpleOdd` + §10-16 構造に依存、`exists_zeta_degree_w1` 等は genuine §10 hard content = **§3-9 signature gap でない**）→ §12 analysis owner の仕事 |

### 状態（2026-06-15）— supply 側 signature 先行整備 ✅ 一区切り
B/C/E(ω^σ) は ungated で **pin 済**（`omegaGrid`/`sigmaIntegral`/`omegaSigmaGrid`、`S05_*Grid.lean`）;
`eta`/(13.1.d) は B+C から rfl; D は (13.1.e) relation を pin（`induce_omegaColumnDiff_mu_diff`、full
Fin-grid は owner glue）。**残る §3–9 supply gap は無い** — A の proof=(6.8)（B の deep frontier）と、
E(残)=§10 hard content（`zeta`(10.2) 等、§12 analysis owner）と、各 consumer 側 cite 置換（§10–16
owner = HUB 割当）のみ。⟹ HUB は §15（ω/τ₃/η/μ-ν relation）と §12（ω^σ）の wiring を pinned
signature への cite で割当可能。

### 状態（2026-06-15）— **endpoint A consumer-side wiring ✅ landing**（Lane F）
A（coherence producer）の **consumer 側 cite 置換** が landing（lane-f commits `5b95fdb8`/`fec51141`）。
新 engine leaf `OddOrder/Peterfalvi/S10_CoherenceWiring.lean`（sorry-free, root closure）が
(6.8) `S08.sibleySetup_is_coherent` への bridge を供給:
- `coherent_of_sibley`（`SibleyDadeHypothesis` + tau/S/A₀ の 3 等式 → `IsCoherent`、(6.8) を subst で cite）
- `SibleyTarget` carrier + `coherent_of_sibleyTarget`（Nonempty）/ `cohereOfSibleyTarget`（unwrapped）。
wired riders（各 body は engine cite で **sorry-free**、gap は §14 witness `sibleyTarget_*` に局在）:
**S15 `S_coherent`(13.2.d)** / **S11 `coherent_H0C_commutator`(9.11)**（→ S12 `typeII_section11_coherence`
も自動 decouple）/ **S14 `frobenius_typeI_coherent`(12.6)**。⟹ これら rider は **B が (6.8) を埋めれば
engine 経由で自動 unconditional 化**（decouple 成立）。**残る endpoint-A gap = `sibleyTarget_*`
producer（§14/§6 構造 obligation）= issue 7001**。standalone な positive-coherence producer は
これで全 wiring 済（S12 `coherent_S` field は構成箇所が無く対象外、typeV 連言は §12 param 混在で対象外）。

### 手順（per endpoint）
1. §3–§9 に faithful signature を pin（sorried 可, build-green + axiom-clean, AxiomsCheck 登録）。
2. §10–16 の対応 opaque field を、その signature への cite に置換（carrier を実体化）。
3. §3–§9 lane が proof を埋める（独立, 上の cite を壊さない）。

### 優先順（レバレッジ順）
- **A**（coherence producer）= 最大。**signature は既に存在**するので §11–13 は**今すぐ cite で配線可**
  （opaque rider を `Nonempty (S07.IsCoherent …)` への参照へ置換）→ B が (6.8) で proof 充足。
- **C → B → D**（S15 grid の pin）= S15 が S16.Hypothesis の直前ゆえ FT 距離が最短。
- **E**（§12 param）。

---

## 5. lane 割当（❌ SUPERSEDED — 履歴。現行正本 = [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md) の 3 レーン a/b/c、2026-07-02 再編）

> 本節の W1–W4 × F/C/B/H 割当は 2026-06-25 relane #9 時点の記録
> （当時の正本 = [`ft_frontier_remap_2026_06_25.md`](ft_frontier_remap_2026_06_25.md)）。
> **現在の lane↔クラスタ対応・所有はここを読まないこと** — 2026-06-28 に a/b/c/d へ全面再配分、
> 2026-07-02 に lane d 退役で a/b/c の 3 レーン。以下は温存された履歴。

honest FT 経路 (~27 sorry) を **数学的に独立な 4 フロント**に再カット (検証 `wf_33ba58ab-bf5`)。
旧「ファイル所有ベース 4 レーン」は 4 フロントとズレており relane #1-#8 の idle の正体だった。

| lane | フロント | Arm | focus | gate |
|---|---|---|---|---|
| **F** (lane-f) | **W1** BG §16 Prop 16.1 6 bridge + type-P carrier | A (mp) | `proposition_type_classification` (純群論・最大 fan-out) | **無 (今すぐ・最優先)** |
| **C** (lane-c) | **W2** §12 all-Type-I tower | A (mp) | `theorem88_caseB_holds` (§12 char、上流 producer 済) | 無 |
| **B** (lane-b) | **W3** §10-11 中心 char 核 | A | **唯一の bare FT sorry** `card_kappaHall_lt_of_isTypeIIIorIV` (11.9.b) + `no_typeV` (10.8/10.10) | 無 (臨界路最狭点・早期着手) |
| **H** (lane-h) | **W4** POLE-2 field_normalizer §14-16 + §15 S&T | B | `field_normalizer_structure` cascade (独立アーム) | 無 |

> **2 アーム構造**: Arm A = `sectionSixteenHypothesis_of_inputs` で S16.Hypothesis を 3 producer (mp/tp/cd)
> から flat 構成 (W1/W2/W3)。Arm B = `final_contradiction → nonexistence_of_G → field_normalizer_structure`
> (W4)。**W1 と W4 は upstream gate を共有しない完全独立**。4 フロントは最後にアーム合流。
> **凍結**: appendix 23 sorry (import closure 外) + §9/§13 内部矛盾 endpoint + これ以上の §5/§6 coherence supply。

---

## 6. 詳細 pointer（正本）
- §11–13 の gate 内訳・分類表 = [`notes/peterfalvi/s10_13_maximal_structure.md`](../peterfalvi/s10_13_maximal_structure.md)
- B-lane (6.8)/§5–6 の進捗 = [`notes/peterfalvi/s06_dade_certain_subgroup.md`](../peterfalvi/s06_dade_certain_subgroup.md)
- scaffold opaque-Prop 規約 = [`notes/meta/scaffold_opaque_prop_convention.md`](scaffold_opaque_prop_convention.md)
- BG spine の live 状況 = git log + `issues/`（BG は 2026-07-02 凍結完了; 旧 memory [[ft-master-roadmap]] は consolidate 済で不存在）
- merge / 並列運用 = [`notes/meta/merge_monitor.md`](merge_monitor.md)
