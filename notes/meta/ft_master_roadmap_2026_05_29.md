# Feit-Thompson 形式化 マスター実行マップ (2026-05-29)

> ⚠ **scope / policy / 経路・signature 並列化の判断は [`ft_path_policy.md`](ft_path_policy.md) が正本**
> （2026-06-15〜）。本ファイルは横断スナップショット（履歴）として温存。BG spine の live 状況は
> memory [[ft-master-roadmap]]。

> **生成**: `ft-master-roadmap` workflow (run `wf_c3f1f84f-929`, 15 agent / 1.89M tok / 13.4 min)。
> Survey 11 並列 (read-only) → Synthesize 1 → Verify 3 adversarial。
> スクリプト: `~/.claude/projects/.../workflows/scripts/ft-master-roadmap-wf_c3f1f84f-929.js` (再実行可)。
> このファイルは **横断スナップショット**。個別ゲートの掘り下げは各 `notes/` と `issues/` が正本。

---

## ⚠ 2026-06-22 デルタ (最新 — 以下の 2026-06-20 ヘッダに優先)

2026-06-20 ヘッダからの差分のみ (構造は不変、下記を上書き):
- **レーン体制 = 4 (B/F/H/C)**。2026-06-20 の 3 レーン表 (下記) は **lane-c 新設で 4 レーンに再編** (2026-06-21、ユーザー裁可)。所有割当の正本は [`merge_monitor.md`](merge_monitor.md) の「2026-06-22 最小修正」表: **F**=BG §14-16 構造 (S14/S15/S16_MainResults + FeitThompson.lean §16 producer) / **B**=Pf §10/§12/§13 Dade char grid / **H**=Pf §11 Wielandt §9 + §14-15 (type I + S&T) / **C**=Pf §16 endpoint + POLE-2 (field normalizer)。**lane-d/e/g は退役済**。
- **実 sorry = 131** (`bin/count-sorry`, 2026-06-22)。06-20 の 137 から純減。build green **3881 jobs** / AxiomsCheck OK / 新 axiom 0。
- 主着地 (06-20→06-22): BG **Thm 15.2 完全 close** + Thm 15.7(c) を faithful `M'≤F(M)` に修正 (印刷版 overstatement 確定) + **Lemma 14.11 phase 1** / Pf **(9.1) Wielandt unconditional** + (9.4) seed / (10.5) ζ^τ₁ vanish + grid hoist (endgame de-risked)。
- POLE-1/POLE-2 の構造は不変 (下記 §「FT 経路の現在地」参照)。

---

## ⚠ 2026-06-20 現状更新ヘッダ (本体 2026-05-29 + 以下の旧ヘッダすべてに優先)

本体 (2026-05-29) と 05-31/06-03 ヘッダは「BG §7-§16 と Pf §10-§16 は Lean ファイルゼロ」という前提で書かれており、**この骨格部分が最も古い**。2026-06 を通じて BG §1-§16 spine と Peterfalvi §6-§16 が実質的に形式化され、FT 経路は終盤に入った。live 状況は memory [[ft-master-roadmap]] + [[ft-endgame-two-poles]] + [[peterfalvi-work-in-worktree]] が保持。本ブロックは 2026-06-20 時点のスナップショット。

### 進捗の測り方 (CLAUDE.md「進捗の測り方」が正本)
目的 = FT の honest な証明の積み上げ。**`sorry` 数は進捗指標でない** (両方向で誤る; hoist で消える / genuine prerequisite を bypass 理由で hedge するのも誤り)。doneness は carrier・仮説の構成可能性で判定。**"FT-orphaned"・"閉じても sorry 減らない" の言い回しは使わない** ([[feedback-orphaned-not-reason-to-defer]])。以下「実 sorry N」は AxiomsCheck-guard 島でなく `bin/count-sorry` の transitive scaffold 数 ([[scaffold-sorry-free-not-done]])。

### FT 経路の現在地 (2026-06-20)
- **最上位 `feitThompson` は配線済** (還元 `feitThompson_of_noMinimalSimpleOdd` sorry-free)。FT 層の実 obligation は **2 POLE**:
  - **POLE-1** = `sectionSixteenHypothesis_of_isMinimalSimpleOdd` → `Peterfalvi.S16.Hypothesis` carrier (`Section16Inputs` の 3 producer = §16 maximal-pair 構造 [F] / type-P 構造 [F] / character data [B])。
  - **POLE-2** = `field_normalizer_structure` (Pf (14.2), S16, lane-h)。
- これらは **Pf §10-16 spine** に gate され、その spine は **BG §7-§16 (局所解析)** と **Pf §3-§9 (指標論コア)** の合流で構成される。BG §9 Uniqueness / §10 Thm 10.1 / §11 全結果 / §12 大半 / §13 endgame / App.C は **完成・sorry-free・axiom-clean** (2026-06 前半)。

### 2026-06-20 時点の active frontier (3 レーン体制)
| lane | 担当 | 現在地 | 残り |
|---|---|---|---|
| **F** (`lane-f`) | BG §14/§15/§16 + POLE-1 構造側 producer | **BG Thm 15.2 (M_F 構造) を step-1〜(c)/(d)/3 まで sorry-free 構築** | wrapper gate `Q0⊴M` 1 点; §16 Prop 16.1 type classification |
| **B** (`lane-b`) | Pf §6/§8 coherence (6.8 capstone) → §13 Dade char data (POLE-1 char) | **(6.8) case-A producer COMPLETE** + case-B `\|Y\|=2` 数学解決 + cY-rewiring foundation | S08:59 (6.8) dispatch (cY-rewiring 実装) → §13 grid |
| **H** (`lane-h`) | Pf §13/§14 + POLE-2 (field normalizer §14.2) | **(14.12) M_F equivariance reduction** + (13.17) を Phase 0-2 構造プログラム化 (実 assembly + 4 gate 隔離) | (13.17) 4 gate (`P⊓U=⊥` F-ask 含む) → §14 counting → POLE-2 |

- **保留 cross-lane handshake**: lane-h (13.17) の gate `P⊓U=⊥` は carrier enrich を要し `sectionSixteenHypothesis_of_inputs` (FeitThompson.lean = F 領域) に触れる。F-ask は 1 仮説に最小化済、正式要請は未発火。
- 実 sorry = **137** (`bin/count-sorry`, 2026-06-20)。build-green 3869 jobs / AxiomsCheck OK / 新 axiom 0。
- 旧ヘッダの「実 sorry 2 個」は AxiomsCheck-guard 島 (issue 0046/0044) の指標で、transitive closure は上記 137。「Pf §10-16 は BG §16 完成まで着手不可」(本体 §2/§4) も **stale** — §10-16 は 2026-06 に scaffold + 部分形式化が進行済 (BG §16 statement は存在、Thm A-E cite 可)。

以下、さらに古い訂正ヘッダ ↓

## ⚠ 2026-05-31 訂正ヘッダ (本体は 2026-05-29 時点、§4–§6 が drift)

本体は 2026-05-29 のスナップショットで以下が既に古い。**正確な live 状況は memory `ft-master-roadmap` が保持**。2026-05-29 以降の確定差分:

- ✅ **BG App.A 完結**: A.4(c) PSTAB (本体 §0/§4/§5/§6 が 🔴「repo 最高レバレッジ単一 sorry」と呼ぶもの) は**解消済**、A.4(b)/A.5 も完成 (issue 0047/0049 close)。→ §4「Top Blockers」#1・§5 の ⭐`bg-appa-a4c-pstab`・§6 DAG の 🔴`bg-appa-a4c-pstab` は **DONE**。
- ✅ **App.B B.1–B.4(b) + BG Thm 6.2 一般形** `Z(L(S))·O_{p'}(G)⊴G` 完成 (`OddOrder/BG/AppB_Thm62.lean`, issue 2000/2001/2002)。→ §4 #2・§6 DAG の `bg-appb-puig`/`bg-thm-6-2-general` は **DONE** (§7–§16 の normal-J ハブが開いた)。
- ✅ **BG §1 Thm 1.13** critical subgroup (issue 0016)。→ §6 DAG `bg-s01-thm-1-11-1-13` の Thm 1.13 部分は DONE。
- 🔄 **BG §4 Blackburn は「全ファイル無」ではない** (§4/§6/§7 の記述が古い): Thm 4.12(a)(b)(c)/Prop 4.3/4.8/**4.11 Huppert**/Lem 4.9/4.15/GL 橋/Gorenstein Lem 4.12–4.14 が sorry-free 着地。**残 = Gorenstein Thm 4.15(i) precursor (SCN₃=∅⇒pRank≤2) → BG Lem 4.13 → Thm 4.16 apex (未 statement)**。
- 🔄 **Peterfalvi 並行ブランチを main へ merge** (f5bcb14 + 834b76c)。§7 coherence/§8/§9/Dade/Clifford/ZIrr/InflationCharacter 配線済、worktree も ff 同期。
- 実 `sorry` は依然 **2 個** (S08 `sibleySetup_is_coherent`=0046 / S09 `card_G0_lower_bound`=0044)。§0/§1.3 の census 方法論は今も有効。
- **🆕 2026-06-03 追補差分** (本体 §1/§4/§5/§7 の記述はさらに古い): ✅ **BG §4 Thm 4.16 apex 完成** (「未 statement」は stale)。✅ **BG §5 完結** (Thm 5.3–5.7)。✅ **BG §7 Lemma 7.1 (推移性 keystone)** + ✅ **BG Prop 1.16** (`S01b_Prop116.lean`)。→ 本体 §1 の「Prop 1.15(b)/1.16 全部欠落」は **stale** (1.15(b) は App.A で, 1.16 は S01b で形式化済)。
- **🆕 2026-06-03 Gorenstein 監査結論**: 「Isaacs で対応できず Gorenstein を形式化しないといけない部分」= **p-stability (App.A, G 3.8.1/§6.5) + ZJ/Z(J) (App.B Puig L(S) = G 6.5.1/8.2.11 代替) + critical subgroup (Thm 1.13 = G 5.3.11/13) + §4 precursors (Gor Thm 3.7/3.8 = G 3.x)** は**全て形式化済**。BG mmd の Gorenstein "**G**" 引用 12 件は全て Isaacs/mathlib 被覆 or BG 自己再証明 (Thompson Transitivity 8.5.4 = §7 が構築中)。**未形式化で残る "真に Gorenstein 専用" の項目は無い**。残る未形式化は BG 自己完結 (Thm 3.7 coprime case, §7–§16 proof) か rep-theory-via-mathlib (Clifford G 3.4.1 proof = issue 0026)。

以下、2026-05-29 スナップショット原文 ↓

## 0. TL;DR

- **実 `sorry` proof-term は 2 個** (2026-05-29 更新: PSTAB 解消で 3→2)。`axiom` 宣言 **0**、`admit` **0**(全件 grep + `AxiomsCheck.lean` の `#assert_only_allowed_axioms` で検証済み)。
  1. `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean:188` — `sibleySetup_is_coherent` (issue 0046)
  2. `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean:1589` — `card_G0_lower_bound` (issue 0044)
  - ✅ **解消済**: `stability_perFactor` (BG App.A A.4(c) PSTAB, 旧 AppA:1546, issue 0047) — 2026-05-29 sorry-free 化。さらに **A.4(b) `thmA4b`** (= Thm 6.1, normal abelian ≤ O_{p',p}) も同日完成 (Gorenstein 5.2 直接ルート, `stabilityLiftAux`@K=O_p(Ḡ) 再利用)。`thmA4a`/`thmA4b`/`thmA4c` を `AxiomsCheck.lean` で axiom-clean を CI ガード。**issue 0047 (A.4 a/b/c) クローズ済**。次の本線 = **A.5 `thmA5`** (新規ブロッカー = Prop 1.10 coprime-nilpotent のみ) → App.B Puig L(S) → Thm 6.2 一般形 (Z(L(S)) 代替)。
- **完成度: 結果数では ~33%(168/~510)、数学的深さでは ~18-22%**。Isaacs Ch.1-7 の FT ルートは本物の sorry-free・axiom-clean で**最大の堅い土台**。だが残りの大半 = **BG ローカル解析本線 §7-§16(~76 結果・Lean ファイルゼロ)+ Peterfalvi §10-§16(~80 結果・ファイルゼロ)** が**直列ボトルネック**で、ここが FT の実際の深さ。現フロンティアペースでは複数年規模。
- **クリティカルパス長 43 ゲート**。最深の拘束: **Peterfalvi §10-§16 は BG §16 完成まで一切着手できない**(BG Theorems A-E が Peterfalvi §10 の入力)。
- **今日クリーンな tree から着手可能なのは ~15 ゲート**。最高レバレッジは **issue 0047 の単一 sorry**(これを潰すと A.4(b)→A.5→App.B→BG Thm 6.2 一般形が連鎖開放、§7-§16 全体が 7+ 回参照する normal-J ハブ)。

> **重要(`sorry-free ≠ proved`)**: 「sorry が無い」だけで「証明済み」とは限らない。本マップは未充足仮説・条件付きスキャフォールドを `partial` として明示する(§4)。判定は memory `scaffold-sorry-free-not-done` に準拠。

---

## 1. 現状の真実 — 何が「本当に」終わっているか

### 1.1 GENUINELY DONE(数学的内容が放電済み・forward 依存なし)

- **Isaacs Ch.1-7 の FT ルート全体**(~168 flagship 結果, AxiomsCheck 済): Sylow / Fitting `F(G)` / `O_p` / Hall E-C / Schur-Zassenhaus / Hall-Higman 1.2.3 / 交換子・coprime action(4.36 含む) / Transfer + Frobenius normal p-complement / Frobenius 群 API / **Thm 7.5 normal-P** / **Thm 7.6 normal-J (= BG Thm 6.2 reduced)** / **Thm 7.8 Burnside**。
  - mathlib が欠く in-repo インフラもここで全部建っている: `F(G)`, `O_p`, `J(P)`, Frobenius 群, TI-subset, `ZIrr`, `ClassFunction`, ChiefFactor API, TISubset。
- **BG App.A A.1 / A.2 / A.3 / A.4(a)**(p-stability 基盤)、**BG §2 Thm 2.6**(4697 行, odd 2-dim repr ⇒ Sylow abelian)、**BG §2 Thm 2.6** 周辺。
- **Peterfalvi の sorry-free インターフェース層**: Dade adjoint formula (2.7), coherence 定義, isometry-difference-pair, `IndChainDecomposition`。

### 1.2 STRUCTURALLY INCOMPLETE(`sorry-free` だが未証明 = `partial`)

| 箇所 | 見かけ | 実態 | issue |
|---|---|---|---|
| **Isaacs Thm 7.1** `thompson_normal_p_complement` | sorry-free | `hJ_normal : J(P).Normal` を **forward 仮説**で受け取る 4 行 reduction。§7C の 7 ステップ(~350-500 LOC)が未形式化 | 0031 |
| **Peterfalvi column-orth (1.2)** / **Brauer (1.1)** | sorry-free | `CharacterTableIndexing` バンドル必須だが `ofFinite` constructor が無い(0048 の ≥ 方向待ち)。条件付きスキャフォールド | 0027 / 0022 |
| **Peterfalvi Clifford (1.7)** | sorry-free | **トートロジカル**: 証明本体が仮説の再梱包のみ。orbit/inertia/multiplicity の本質は未着手 | 0026 |
| **Peterfalvi (7.7.a)/(7.8.c.i)** | sorry-free | 本質を `Hypothesis76/78` の certificate field に hoist | — |
| **Peterfalvi (7.11)** `not_trivial_G0` | sorry-free | 算術証明は本物だが `card_G0_lower_bound`(sorry)を通過 | 0044 |
| **BG Thm 6.1 / 6.2** | — | **reduced case のみ**(`O_{p'}=1 ∧ P=C_G(Z(P))`)。一般形は App.A→App.B 連鎖待ち | — |

### 1.3 sorry census(検証値)

`grep` の全 "sorry" 出現は 57 だが、**bare proof-term は 3 個のみ**(上記)。残りは docstring / コメント(`AxiomsCheck.lean:40`, `S7A1_JpGL2p.lean:77`, `SchurZassenhausConj.lean:235`「bodies marked sorry need filling」= stale, 実体なし)。

> ⚠ **ROADMAP テキスト訂正**: ROADMAP Phase 2b に「S04_DadeIsometry.lean に残 sorry 1」とあるが **現在 S04 に bare sorry は無い**(解消済み・テキスト stale)。dependency critic も「Dade も実 sorry」と誤記したが grep で否定。

---

## 2. クリティカルパス(最終矛盾までの拘束連鎖, 43 ノード)

```
[Phase 1 Isaacs — DONE]
 ch01-sylow → ch04-commutators → ch05-transfer → ch06-frobenius
   → ch07-thm75-normalP → ch07-thm76-normalJ
[Phase 2a BG local — ほぼ未着手]
   → bg-s02-thm-2-6 → appa-a1-a2-a3-a4a → infra-basechange-rep
   → 🔴 appa-a4c-pstab → appa-a4b-thm61 → appa-a5 → appb-puig
   → bg-thm-6-2-general → s01-thm-1-11-1-13 → s01-lem-1-21-plength
   → s04-pgroups-small-rank → s05-narrow-pgroups
   → s07-transitivity → s08-fitting-of-maximal → s09-uniqueness
   → s10-malpha-msigma → s11-exceptional-maximal → s12-subgroup-e
   → s13-prime-action → s14-type-p-counting → s15-mf → s16-main-results
[Phase 2b Peterfalvi — 大半未着手, §10+ は §16 待ち]
   → infra-irr-conjclasses-count → pf-column-orthogonality → pf-brauer-permutation
   → pf-clifford-core → infra-classsum-algebra
   → 🔴 pf-s08-6-8-coherence → pf-s09-7-1-to-7-9 → 🔴 pf-s09-7-10-card-g0
   → pf-s09-7-11-not-trivial
   → pf-s10-minimal-simple → pf-s11-to-s15-type-analysis → pf-s16-nonexistence-g
[Phase 3-4 — 未着手]
   → bg-appc-final-contradiction → final-phase3-assembly → final-phase4-feit-thompson
```

🔴 = 実 sorry を含むゲート。

---

## 3. 最終矛盾ルート(two legs that meet twice)

**LEG 1 (BG ローカル解析)**: 極小単純奇数位数 G → §7 Thompson 推移性(Hyp 7.1 で反例固定)→ §8 maximal の Fitting 二分 → §9 一意性定理(rank≥2 部分群が maximal を決定)→ §10-§13 maximal 構造(σ/α/β 族, 部分群 E, 素数作用)→ §14-§16 全 maximal の族 → **§16 Theorems A-E**(Type I-V 分類, Thm B が TI-subset + abelian rank≤2 Sylow を指標理論へ手渡す)。

**LEG 2 (Peterfalvi 指標理論)**: Dade isometry (§4) + coherence (§7-§8, (6.8) Sibley sorry でゲート)→ §9 が自己完結の Frobenius 族非存在 (7.11) `not_trivial_G0`(現 sorry-free だが (7.10) sorry に依存)。

**合流点 ①(§16 ↔ §10)**: BG Theorems A-E が Peterfalvi §10 (PeterfalviType 分類) の**入力**。→ Peterfalvi §10-§16 は BG §16 が lands するまで文字通り着手不能。
**合流点 ②(終端矛盾)**: Peterfalvi §16 (14.11.4) が Type 分類から指標ノルム不等式の矛盾を導く。BG App.C (= Peterfalvi §9 の再編集) が途中の Frobenius 族 `p≤q` を供給。
**Phase 3** が両者を `BG.AppC.TheoremC ≅ Peterfalvi.S09.TheoremC` 同値補題 + BG §15 ↔ Pf §15 (M_F ↔ S,T) 整合で接着。**Phase 4** が `FeitThompson`(odd order ⇒ solvable)を G 非存在へ帰着して述べる。

> **最深の拘束**: Peterfalvi §10-§16(~80 結果, 全ファイル無)は BG 本線 §7-§16(~76 結果, 全ファイル無)が完成するまで開始できない。**BG ローカル解析本線が証明全体の支配的直列ボトルネック**。

---

## 4. Top Blockers(下流を最も塞ぐ順)

1. **`bg-appa-a4c-pstab`** — 単一 BG sorry (`stability_perFactor`, AppA:1546)。潰すと **A.4(b)→A.5→App.B B.4→BG Thm 6.2 一般形** が連鎖開放。これは §7-§16 で 7+ 回参照される normal-J ハブ。**repo 最高レバレッジの単一 sorry**。
2. **`bg-thm-6-2-general`** — 一般形 normal-J(reduced のみ済)。§7/§8/§9 と全下流をゲート。上記 App.A→App.B 連鎖待ち。
3. **`bg-s07-transitivity` ～ `bg-s16-main-results`** — BG 本線全体(Ch2 Uniqueness / Ch3 MaximalSubgroups / Ch4 FamilyOfMaximal)が **Lean ファイルゼロ**(~76 結果, ~10 節)。支配的直列ボトルネック。
4. **`bg-s04-pgroups-small-rank`** — §5/§10-§16 の hard gate。ファイル無。Blackburn 4.16 分類 ~30-40 日。BG Thm 1.13(critical subgroup)インフラも要。
5. **`pf-s08-6-8-coherence`** — Sibley coherence sorry (S08:193)。class-sum 代数 `ω:ZC[G]→ℂ` + Clifford core + Brauer 全部要。Peterfalvi (7.10)→(7.11) を塞ぐ。
6. **`infra-irr-conjclasses-count`** — `|Irr|=|ConjClasses|` ≥ 方向 (0048)。column-orth (0027) と Brauer (0022) の**無条件形**を塞ぐ(現状は条件付きスキャフォールドで Peterfalvi §3/§6/§8 を未充足仮説として下支え)。

---

## 5. 今着手可能なゲート(ready-now)

synthesis 由来 15 + 批判で追加 3:

| ゲート | 内容 | issue | 工数 |
|---|---|---|---|
| **`bg-appa-a4c-pstab`** ⭐ | `stability_perFactor`: chief-factor を ZMod-p rep 化 + base-change F_p→AlgClosure + thmA4a 適用。足場は全部ある(~250-400 行) | 0047 | L |
| `infra-basechange-rep` | `baseChangeRepresentation` を S02 から expose(private 解除) | — | S |
| `infra-irr-conjclasses-count` | `|Irr|=|ConjClasses|` ≥ 方向 + `CharacterTableIndexing.ofFinite`。Schur step は `finrank_intertwiningMap_self=1` で供給可 | 0048 | M |
| `infra-frobenius-reciprocity` | 数値 Frobenius 相互律 + 誘導指標値公式 | — | M |
| `infra-classsum-algebra` | class-sum 代数 `ω:ZC[G]→ℂ` + 代数的整数合同 | — | M |
| `bg-s01-thm-1-11-1-13` | Ω₁ 作用 + Thompson critical subgroup | 0015/0016 | M |
| `bg-s01-lem-1-21-plength` | p-length one パッケージ(5 性質) | 0019 | M |
| `bg-s01-prop-1-2-1-4` | chief-factor Fitting / coprime auto faithful | 0011 | M |
| `bg-s01-prop-1-10-1-15b` | Prop 1.10 / Lem 1.9 full / Goldschmidt 1.15(b) / 1.16 | 0014/0017/0018 | M |
| `bg-s02-prop-2-4-eigenspace` | eigenspace 分解 (c)(f)-(k) 残り | 0028 | L |
| `pf-clifford-core` | Clifford 分解の本体(現トートロジー scaffold を本物に) | 0026 | L |
| `pf-s04-dade-isometry` | Dade map 構成 (2.6.b),(2.8)-(2.11) | 0040 | L |
| `pf-s07-coherence-def` | coherence 定義 (5.1)-(5.9) | — | L |
| `isaacs-3-15-3-17-solvability` | 空 body placeholder。Burnside(済)で unblock 済 | — | S |
| `isaacs-baer-suzuki` | §2B Baer / Baer-Suzuki / Matsuyama。Thm 7.8 の下流依存 | — | M |
| **(批判追加)** `infra-schur-center-bound` | SchurCenterBound ([Is] Cor 2.30)。§3 (1.8) / §8 (6.6)-(6.8) が要。~100-150 LOC | — | S |
| **(批判追加)** `pf-s09-7-8ab-norm` | Peterfalvi (7.8.a)/(7.8.b) β 分解 + ノルム評価。**現状 unstated**。(7.10) の前提 | 0044 | M |
| **(批判追加)** `pf-s09-7-9-nonorth` | Peterfalvi (7.9) 2-族 非直交。**statement 完全に欠落**。(7.10) の前提 | 0044 | M |

⭐ = 最優先(連鎖開放レバレッジ最大)。

> **即クローズ候補**: issue **0029**(`sylow_normal_of_elementary_normal_P_theorem` S7A2:1216 が full Thm 7.5 をカバー)、**0030**(`normal_J` sorry-free, docstring の "remaining local axioms" は stale)。`0037`(wrapper 削除 6 件, 機械的)も即実行可。

---

## 6. ゲート DAG 全 68(phase 別)

凡例: ✅ done / 🟡 partial / 🔴 sorry / ⬜ missing ｜ R = ready-now, B = blocked, I = needs-infra ｜ 工数 S/M/L/XL

### Phase 1 — Isaacs(13)

| 状 | ゲート | 書誌 | R | 工 | deps |
|---|---|---|---|---|---|
|✅|isaacs-ch01-sylow|Thm 1.1-1.46|R|L|—|
|🟡|isaacs-ch02-subnormality|Thm 2.1-2.20|R|M|ch01, ch04|
|⬜|isaacs-baer-suzuki|Thm 2.12-2.14|R|M|ch01|
|🟡|isaacs-ch03-splitext|Thm 3.1-3.24|R|L|ch01|
|🟡|isaacs-ch04-commutators|Thm 4.1-4.38 (=BG 1.6)|R|XL|ch01, ch03|
|✅|isaacs-ch05-transfer|Thm 5.1-5.30|R|L|ch01, ch04|
|✅|isaacs-ch06-frobenius|Thm 6.1-6.21 (§6A-B)|R|XL|ch04|
|⬜|isaacs-ch06c-kernel-nilpotent|Thm 6.22-6.24|B|M|thm71-full|
|✅|isaacs-ch07-thm75-normalP|Thm 7.5|R|L|ch06, ch04|
|✅|isaacs-ch07-thm76-normalJ|Thm 7.6 (=BG 6.2 reduced)|R|XL|thm75, ch05|
|🟡|isaacs-ch07-thm71-full|Thm 7.1 §7C 7-step|B|L|thm76, ch06c|
|✅|isaacs-ch07-thm78-burnside|Thm 7.8|R|L|thm76|
|⬜|isaacs-3-15-3-17-solvability|Thm 3.15/3.17|R|S|thm78|

### INFRA(8)

| 状 | ゲート | 内容 | R | 工 | deps |
|---|---|---|---|---|---|
|✅|infra-chieffactor|ChiefFactor API|R|M|ch01|
|✅|infra-tisubset|TI-subset/ZIrr/CF(L,A)|R|M|—|
|🟡|infra-pi-separable|本物の IsPiSeparable (π-series)|R|M|ch03|
|🟡|infra-pi-hall|一般 π-Hall API|R|M|ch03|
|🟡|infra-basechange-rep|baseChangeRep F_p→AlgClosure|R|S|s02-thm-2-6|
|🟡|infra-irr-conjclasses-count|`|Irr|=|ConjClasses|` ≥|R|M|—|
|🟡|infra-frobenius-reciprocity|数値 Frobenius 相互律|R|M|—|
|🟡|infra-classsum-algebra|class-sum 代数 ω:ZC[G]→ℂ (代数射 + classSum 中心性 ✅ `ClassSumAlgebra.lean`; ω(C) 整数性のみ残)|R|M|—|

### Phase 2a — BG local analysis(30)

| 状 | ゲート | 書誌 | R | 工 | deps |
|---|---|---|---|---|---|
|🟡|bg-s01-solvable-core|BG §1(done subset)|R|L|isaacs 多数|
|🟡|bg-s01-prop-1-2-1-4|Prop 1.2-1.4|R|M|solvable-core, chieffactor|
|🟡|bg-s01-prop-1-5-1-6|Prop 1.5-1.6|B|M|solvable-core, pi-hall|
|🟡|bg-s01-prop-1-10-1-15b|Prop 1.9-1.16|R|M|solvable-core|
|⬜|bg-s01-thm-1-11-1-13|Thm 1.11-1.13|R|M|ch04|
|🟡|bg-s01-lem-1-21-plength|Lem 1.21|R|M|solvable-core, pi-separable|
|✅|bg-s02-thm-2-6|Thm 2.6(a)(b)|R|XL|ch05|
|⬜|bg-s02-prop-2-1-absirr|Prop 2.1|I|L|s02-thm-2-6|
|🟡|bg-s02-prop-2-4-eigenspace|Prop 2.4|R|L|s02-thm-2-6|
|⬜|bg-s02-thm-2-5-extraspecial|Thm 2.5|I|L|2-1, 2-4, 1-5-1-6|
|🟡|bg-s03-frobenius-actions|§3 Lem 3.1-3.10|B|L|ch06, 2-5|
|✅|bg-appa-a1-a2-a3-a4a|App.A A.1-A.4(a)|R|XL|s02-thm-2-6, chieffactor, ch01|
|🔴|**bg-appa-a4c-pstab**|App.A A.4(c) PSTAB|R|L|a1-a4a, basechange, chieffactor|
|✅|bg-appa-a4b-thm61|App.A A.4(b)=Thm 6.1|R|S|a4c-pstab|
|⬜|bg-appa-a5|App.A A.5|B|M|a4c-pstab, solvable-core|
|⬜|bg-appb-puig|App.B Puig L(S) B.1-B.4|B|L|a5, chieffactor|
|🟡|bg-thm-6-2-general|Thm 6.2 一般形|B|S|appb-puig|
|🟡|bg-thm-6-1-general|Thm 6.1 一般形|B|S|a4b-thm61|
|⬜|bg-s04-pgroups-small-rank|§4 Blackburn 4.16|B|XL|1-11-1-13, 1-21, ch04|
|⬜|bg-s05-narrow-pgroups|§5 SCN₃|B|L|s04|
|⬜|bg-s07-transitivity|§7 Thompson 推移性|B|XL|6-2-general, s05, 1-5-1-6|
|⬜|bg-s08-fitting-of-maximal|§8 Thm 8.1|B|XL|s07, 6-2-general|
|⬜|bg-s09-uniqueness|§9 Thm 9.6|B|XL|s08, 6-2-general|
|⬜|bg-s10-malpha-msigma|§10 M_α/M_σ|B|L|s09, s07|
|⬜|bg-s11-exceptional-maximal|§11|B|M|s10|
|⬜|bg-s12-subgroup-e|§12 部分群 E(19 結果)|B|XL|s10, s11|
|⬜|bg-s13-prime-action|§13|B|L|s12|
|⬜|bg-s14-type-p-counting|§14|B|L|s13, s09|
|⬜|bg-s15-mf|§15 M_F|B|L|s14, s12|
|⬜|bg-s16-main-results|§16 Thm A-E|B|XL|s15|

### Phase 2b — Peterfalvi(14)

| 状 | ゲート | 書誌 | R | 工 | deps |
|---|---|---|---|---|---|
|🟡|pf-column-orthogonality|(1.2)|B|M|irr-conjclasses|
|🟡|pf-brauer-permutation|(1.1)|B|M|column-orth, irr-conjclasses|
|🟡|pf-clifford-core|(1.7)|R|L|frobenius-recip|
|🟡|pf-s03-preliminary|§3 (1.1)-(1.10)|B|M|column, brauer, clifford|
|🟡|pf-s04-dade-isometry|§4 (2.6.b),(2.8)-(2.11)|R|L|frobenius-recip, tisubset|
|🟡|pf-s05-s06-dade-app|§5-§6|B|L|s04, brauer|
|🟡|pf-s07-coherence-def|§7 (5.1)-(5.9)|R|L|tisubset|
|🔴|**pf-s08-6-8-coherence**|§8 (6.8) Sibley|I|XL|clifford, brauer, s07, classsum|
|🟡|pf-s09-7-1-to-7-9|§9 (7.1)-(7.9)|B|L|s08, s05-s06, s07|
|🔴|**pf-s09-7-10-card-g0**|(7.10)|B|XL|7-1-to-7-9, s08, ch06c|
|🟡|pf-s09-7-11-not-trivial|(7.11)|B|S|7-10-card-g0|
|⬜|pf-s10-minimal-simple|§10 (8.1)-(8.6)|B|L|**bg-s16**, 7-11|
|⬜|pf-s11-to-s15-type-analysis|§11-§15|B|XL|s10, bg-s15|
|⬜|pf-s16-nonexistence-g|§16 (14.1)-(14.11)|B|XL|s11-s15, bg-s16|

### Phase 3-4 — 最終接着(3)

| 状 | ゲート | 内容 | R | 工 | deps |
|---|---|---|---|---|---|
|⬜|bg-appc-final-contradiction|App.C (Thm C, p≤q)|B|M|pf-7-11|
|⬜|final-phase3-assembly|App.C≅Pf§9 接着|B|L|pf-s16, appc, bg-s16|
|⬜|final-phase4-feit-thompson|FeitThompson 本定理|B|M|phase3|

---

## 7. 領域別 主要ギャップ(survey 抜粋)

- **Isaacs Ch.1-4**: §2B Baer-Suzuki(Thm 7.8 下流)、§3E Tier2 / §3F strong / §4B Mann は **0 下流引用で意図的 skip**。`IsPiSeparable := IsSolvable` placeholder(FT パスでは十分, App.A 一般用途には本物要)。
- **Isaacs Ch.5-7**: §6C(Frobenius kernel nilpotent 6.22-6.24)未着手 = Thm 7.1 の欠けたリンク。Thm 7.1 は forward 仮説依存で実質未証明。
- **BG §1**: Prop 1.2 reverse / 1.4 / 1.5(a-c,e) / 1.6(c)(d) / 1.10 / Thm 1.11-1.13 / Prop 1.15(b)/1.16 / Lem 1.21(a-e) が**全部欠落**(issue 0011-0019)。§1 は `partial`。
- **BG §2**: Prop 2.1 absirr / Thm 2.5 extraspecial は skeleton のみ(0033/0034)。Prop 2.4 は (c)(f)-(k) 残(0028)。
- **BG App.A**: PSTAB が要 (1) chief factor を ZMod-p AddCommGroup module 化 (2) `IsPGroup.invariants_ne_bot` (3) thmA4a (4) `baseChangeRepresentation`(private 解除要)(5) `IsPStable`⇒[U,A]≤V。~250-400 行。
- **BG 本線 §4-§16**: 全ファイル無。**mmd 抽出エラー**に注意 — §6 ヘッダ欠落(L1957/1969 inline マーカ)、`MISSING_PAGE_EMPTY:67`、App.C が Nougat で "Appendix D" 誤ラベル(L4763)。**§7 開始前に大量の記法定義が必要**(ℳ, 𝒰, ℋ_H(A;π), SCN₃, σ(M),α(M),β(M),κ(M), M_σ,M_α,M_β,M_F, A(M),A₀(M),R(x))。
- **Peterfalvi**: 0048(|Irr|=|ConjClasses|)が 0027/0022 の無条件化を塞ぐ。0026 Clifford はトートロジー scaffold。0040 Dade 構成は interface のみで τ 存在証明が未。(3.5)/(3.8)/(4.1)/(4.7)/(5.5)/(5.7)-(5.9) 等の主要 statement 未記述。(6.7) は ClassSumAlgebraHom 要。**(7.8.a/b)/(7.9) は statement すら無く (7.10) assembly 不能**。
- **mathlib 欠落**: `F*(G)` 一般 Fitting 完全欠如(IsQuasisimple/IsComponent/E(G)/socle 全無 — FT critical path 外だが Phase 4 + Peterfalvi §10+ で要)。ZJ named module 無(normal_J + App.B L(S) 経路で代替)。`SchurCenterBound`([Is] Cor 2.30)未建。

---

## 8. 批判による補正・未決定事項

3 つの adversarial critic(coverage / dependency / readiness)が指摘した**要対応**:

1. **完成度の分母を明示せよ**: 「18-22%」は深さ基準では妥当だが、結果数基準(168/~510 ≈ 33%)だと土台の堅さを過小評価する。本マップは**両併記**(§0)。
2. **(7.8.a/b)/(7.9) を明示ゲート化**(本マップ §5/§6 で追加済): `card_G0_lower_bound` (7.10) の前提だが synthesis の元 list に欠落していた。
3. **SchurCenterBound を ready-now に昇格**(追加済): §8 coherence を塞ぐ ~100-150 LOC の即着手インフラ。
4. **BG Thm 6.2 の reduced/general を分離記述**: reduced は **DONE**(`S06_Additional.lean:127-137`, Isaacs 7.6 直結)、general のみ App.A→App.B 連鎖待ち。「App.A が §6 上流」は done 部分には逆。
5. **App.B routing を 1 コミットで決着せよ** ⚠ **未決定**: 2026-05-23 audit は「App.B orphan(skip 可)」、2026-05-28 spike は「App.B B.4 = Z(J) substitute(no-Gorenstein 方針で**必須**)」。**現状の正解は後者**(`bg_s6_appAB_route_2026_05_28.md`)= App.B を critical path に戻す。要 decision commit。
6. **Ch06 §6C ↔ Thm 7.1 の循環は解消可**: 6.23 → 7.1 → 6.24 の順序制約(循環でない)。6.23 を先に形式化すれば 7.1 が lands し 6.24 が続く。
7. **並列スパインとして描け**: BG §1-§3 + §6-reduced と Peterfalvi §1-§8 は**相互ブロックなしで並行可能**。両者が合流するのは BG §14-§16 → Peterfalvi §10。Phase 2a/2b は「直列 2 フェーズ」でなく「合流する 2 本のスパイン」。
8. **issue 0029/0030 はクローズ可**、`0031` は `partial` 明記、S7B2 docstring の stale な "remaining local axioms" 記述を削除。

---

## 9. ここからの workflow 戦略(ゲート単位で回す)

この 1 本で FT は終わらない。マップを発射台に、**フェーズごとに別 workflow** を順に回し、各回の結果を読んでから次を決める:

1. **即着手 wave(並列, 低リスク)**: `0047 PSTAB`(⭐ 最優先)/ `infra-basechange-rep` / `0048 Schur step` / `0037 wrapper 削除` / `0029・0030 close`。→ PSTAB が lands すれば A.4(b)→A.5→App.B→Thm 6.2 一般形の **find→implement→verify pipeline** を 1 本。
2. **BG §1 充足 workflow**: 0011-0019 を fan-out(多くが ready-now/M)。§4 の前提を揃える。
3. **BG §4-§5 workflow**(XL, 記法定義先行): Blackburn 4.16。ここから本線。
4. **BG §7-§16 pipeline**(支配的直列): 節ごとに「mmd 精読 → 記法定義 → 定理 → verify」。worktree isolation 推奨(並行編集衝突回避)。
5. **Peterfalvi §1-§8 workflow**(BG と**並行**): 0048→0027→0022→0026→class-sum→0046 coherence→§9 (7.8-7.11)。
6. **合流 + Phase 3-4**: BG §16 lands 後に Peterfalvi §10-§16、最後に App.C 接着 + FeitThompson。

各 workflow は「sorry-free ≠ proved」を全 agent に徹底し、find した主張を adversarial に verify してから commit する(本 workflow と同型)。

---

*Generated by `ft-master-roadmap` workflow, 2026-05-29. 数値は当時のスナップショット — ファイル/フラグ参照は推奨前に再確認のこと。*
