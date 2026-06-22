# FT 形式化 — 経路 policy + signature 先行整備（canonical, 2026-06-15）

> **このファイルが「何が FT 経路上か / どこを触るか / どう並列化するか」の正本。**
> 毎セッション再発する「これは FT に必要なのか?」の混乱を止めるための単一参照点。
> 横断スナップショット（[`ft_master_roadmap_2026_05_29.md`](ft_master_roadmap_2026_05_29.md),
> [`feitthompson_critical_path_2026_06_03.md`](feitthompson_critical_path_2026_06_03.md),
> [`ft_mainline_dependency_closure_2026_06_02.md`](ft_mainline_dependency_closure_2026_06_02.md)）は
> 履歴として温存するが **scope/policy の判断はこのファイルが優先**（あれらは日付固定で stale）。
> 個別ゲートの掘り下げは各 `notes/peterfalvi/*.md` / `notes/bg/*.md` / `issues/` が正本。

---

## 0. 方針（TL;DR）

1. **作業は FT critical path 上に限定する。** off-path（= 3 冊完全形式化スコープのうち
   honest な FT 証明が推移的に必要としない部分）は FT が閉じるまで凍結。新規着手しない。
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
     （[[feedback-orphaned-not-reason-to-defer]]）。
4. **作業順序 = 上流優先 + 文書順タイブレーク**（全レーン共通の標準方針、ユーザー 2026-06-22）。
   - **上流優先**: 各レーンは依存の**上流側から**進める。下流の gated endpoint を先回りで
     skeleton 化（hypothesis 引数化 engine + assembly）するのは**上流が真に block されているときの
     保険**に留め（[[feedback-gated-endpoint-skeleton-pattern]]）、基本はまず上流 prerequisite を埋める。
   - **文書順タイブレーク**: 着手可能な選択肢が複数あるとき（どれも上流端）は、
     **教科書（BG / Peterfalvi）上で出現が早いもの**（番号の若い §/定理/補題）から着手する。
     線型 spine（BG §1→§16, Pf §3→§16）では「上流＝文書で早い」がほぼ一致する。
   - **FT 経路限定**: 対象は item 1 の on-path のみ。off-path は凍結（順序判断の対象外）。
   - これは**作業の選択順序**の規則であり、doneness 判定（item 3）とは独立。

---

## 1. FT critical path（symbol-anchored, 不変の背骨）

```
feitThompson                                    OddOrder/FeitThompson.lean:162   ✅ sorry-free
└ noMinimalSimpleOdd                            :76
  ├ sectionSixteenHypothesis_of_isMinimalSimpleOdd  :67   ★★ 唯一の実 sorry（FT 全体の標的）★★
  │     target = Peterfalvi.S16.Hypothesis      Peterfalvi/S16_NonExistenceG.lean:42
  └ noMinimalSimpleOdd_of_section16             :48
        └ BG.AppC.final_contradiction           ✅ done（carrier-conditional, App.C 完成）
```

`feitThompson` を sorry-free にする = `sectionSixteenHypothesis_of_isMinimalSimpleOdd` を埋める
= minimal simple group から `Peterfalvi.S16.Hypothesis` を **honest に構成**する、ただ一点。
それ以外（reduction, App.C 最終矛盾）は既に sorry-free。

`Peterfalvi.S16.Hypothesis` は線型 import 鎖の頂点:
`S16 ⊃ S15 ⊃ S14 ⊃ S13 ⊃ S12 ⊃ S11 ⊃ S10`（各 `Hypothesis` が前段を extends）。
この **Pf §10–16 spine** を構成可能にすることが残作業の実体。

---

## 2. 2 トラック構造（合流点 = S16.Hypothesis）

S16.Hypothesis の構成は 2 本の独立トラックの合流:

### Track L — local analysis（→ G1）
Isaacs Ch.1–7 ✅ → BG App.A/B ✅ → BG §1–§16 local 解析 → **BG §16 endpoints**
（`BG.Ch4_FamilyOfMaximal.S16_MainResults`: Thm A–E / Prop 16.1 / Thm I–II）。
Pf §10 が `S16_MainResults` を **import 済**（statements 在・sorried・cite 可）= **G1 ゲート**。
担当 = lanes **F / G / H**。**真の FT ボトルネック**（§14–16 が active frontier）。

### Track C — character theory（→ G2）
Pf §3–§9 character API（Dade isometry, coherence, 指標 index 族）。
Pf §10–16 spine がこれを consume = **G2 ゲート**。担当 = lane **B**。

### 合流 — Pf §10–16 spine
G1（BG §16, import 済）と G2（§3–§9, **現状 opaque field で代用＝未 cite**）を両方 consume し
S16.Hypothesis を生む。**§10–16 が §5/§6/§8 を import していないのが signature gap の核**（§4）。

```
Isaacs✅ ─ BG AppA/B✅ ─ BG §1-16 ─┐
                      (Track L=G1) │
                                   ├─→ Pf §10-16 spine ─→ S16.Hypothesis ─→ AppC✅ ─→ feitThompson
   Pf §3-9 char API ───────────────┘
              (Track C=G2)
```

---

## 3. on-path / off-path 分類 + 判定原則

**判定原則**: 「`sectionSixteenHypothesis_of_isMinimalSimpleOdd` の **honest** な構成が推移的に必要とするか」。
これは **math architecture 上の判断**であって、現在の import / consume 状況ではない。
今 §10–16 spine が opaque field で bypass していて未 cite でも、honest 証明がいずれ必要とするなら **on-path**
（= deferred-payoff な genuine prerequisite。今 consumer 0 でも本物の仕事）。honest 証明が必要としないものだけが off-path。
**「今 consume / import されていない」を off-path の根拠にしない**（[[scaffold-sorry-free-not-done]] の逆向きの誤り）。

### ✅ ON-PATH（ここを作業）
| 区分 | 範囲 | 担当 |
|---|---|---|
| Track L | BG §7–§16 spine + App.A/B/C | F / G / H |
| Track C | Pf §3–§9 character API の **§10–16 が consume する slice のみ**（§4 の surface） | B |
| 合流 | Pf §10–16 spine（opaque→cite 置換 + 実証明） | B / §10–16 owner |

### ❄ OFF-PATH（honest な FT 証明が必要としない — FT が閉じるまで凍結、新規着手しない）
- **Pf Appendices**（`FeitSibley`/`Huppert`/`NearFields`/`SemilinearField`/`Suzuki`/`Suzuki2Groups`）
  — honest な odd-order 矛盾が推移的に必要としない見込み。⚠ 「§10–16 から未 import / AxiomsCheck guard のみ」は
  off-path の**ヒント**であって基準ではない（未 import = off-path とは限らない）。各 appendix が honest spine に
  本当に不要かは math で再確認してから凍結を当てにする。
- **Pf §5/§6 の full-scope completeness** — honest な §10–16 spine が必要としない部分
  （例: §6 certain-type のうち §4 の μ/η/ν constructor + coherence producer **以外**、
  (3.8) trichotomy の §10–16 非依存部分、(7.10) 等）。
- Isaacs / BG の FT route 外の網羅、3 冊完全形式化の残り。

> ⚠ 「3 冊全部形式化」は CLAUDE.md のプロジェクト長期スコープであり続けるが、**FT を閉じる作業とは
> 別フェーズ**。当面は FT 経路に限定（ユーザー方針 2026-06-15）。off-path は凍結であって放棄ではない。

---

## 4. signature 先行整備（並列化の核）

### 問題
Pf §10–16 spine は G2（§3–§9 char API）を **opaque field（Prop/carrier）で代用**しており、
§5/§6/§8 を **import も cite もしていない**（S10 が import するのは S04, S07, S09 のみ）。帰結:
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
| **A** | maximal 族の coherence producer `Nonempty (S07.IsCoherent …)` | S12 `CharacterParameters.coherent_S`:127 / S15 `S_coherent` / §11–13 coherence riders（~27 sorry） | S08 `sibleySetup_is_coherent`:46 | 🔴 sorry（B (6.8)）。**signature は既に在**＝下流は今すぐ cite 可 |
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

## 5. lane 割当（FT-aligned, 2026-06-15）

| lane | branch | Track | focus（FT 経路上のみ） |
|---|---|---|---|
| **B** | lane-b | C（§3–§9 char API） | endpoint A の proof = **(6.8) `sibleySetup_is_coherent`**（現 frontier）+ B/C/D/E signature pin。**full §6 certain-type completeness はやめ、§10–16 consume surface に絞る** |
| **F** | lane-f | L | BG §13 ✅ done → 次 FT-path（要指示） |
| **G** | lane-g | L | BG §15 M_F + §16 main results（G1 endpoint 製造） |
| **H** | lane-h | L | BG §14 Type-P |
| 合流 | — | — | Pf §10–16 の opaque→cite 置換（signature pin 後; B or §10–16 owner） |

> B の mission 再定義: 「full Pf §6 を完成」ではなく「**§10–16 が consume する G2 surface
> （A coherence producer + B/C/D/E index 族）を供給**」。これが FT-upstream の本体。

---

## 6. 詳細 pointer（正本）
- §11–13 の gate 内訳・分類表 = [`notes/peterfalvi/s10_13_maximal_structure.md`](../peterfalvi/s10_13_maximal_structure.md)
- B-lane (6.8)/§5–6 の進捗 = [`notes/peterfalvi/s06_dade_certain_subgroup.md`](../peterfalvi/s06_dade_certain_subgroup.md)
- scaffold opaque-Prop 規約 = [`notes/meta/scaffold_opaque_prop_convention.md`](scaffold_opaque_prop_convention.md)
- BG spine の live 状況 = memory [[ft-master-roadmap]]（startup 要約）
- merge / 並列運用 = [`notes/meta/merge_monitor.md`](merge_monitor.md)
