# FeitThompson 実 critical path — 訂正版 roadmap (2026-06-03, upd 2026-06-04)

> ⚠ **STALE（履歴スナップショット）**。scope / policy / 経路・signature 並列化の判断は
> [`ft_path_policy.md`](ft_path_policy.md) が正本（2026-06-15〜）。本ノートは当時の依存監査として温存。

**経緯**: Peterfalvi (6.8) を T6→T7 と drill する過程で方針エラーが頻発 → 全 spine を 4 並列
adversarial 監査 (notes/peterfalvi/s08_6_8_assembly_plan.md §G)。監査で **roadmap memory の
「実 sorry 2 (0046/0044)」framing が FeitThompson への距離を大きく過小評価**と判明。本ノートは
**検証済みの実依存構造**と残作業の正直な sizing をまとめ、優先順位を再設定する。全主張は grep/read で自己検証済。

## ✅ 2026-06-04: 最上位 minimal-counterexample 還元 完成 (下流 spine 接続、選択肢2 前半)

**`feitThompson` の「裸 sorry」を解消し「真の依存木」へ。** `FeitThompson.lean` を再構成:
- **`feitThompson_of_noMinimalSimpleOdd` (axiom-clean, sorry-free, AxiomsCheck 登録済)** = minimal-counterexample
  還元。`Nat.card G` 強帰納: 非可解 odd 群があれば最小位数のものは proper subgroup/quotient が IH で可解 ⟹
  単純 (proper normal N があれば `solvable_of_ker_le_range` で N と G/N の可解性から G 可解=矛盾) ⟹
  `IsMinimalSimpleOdd G`。純群論のみ (文字理論不要)。`#print axioms` = [propext, choice, Quot.sound]。
- **`sectionSixteenHypothesis_of_isMinimalSimpleOdd` (def, 唯一の新 sorry)** = `IsMinimalSimpleOdd G → S16.Hypothesis G`。
  **残る上流ギャップを唯一の名前付き義務に局所化** (= BG §7-16 局所解析 + Pf §10-16 型解析 の全体)。
- **`noMinimalSimpleOdd`** = `noMinimalSimpleOdd_of_section16 hG (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)`
  (既存配線 + 上の gap で `IsMinimalSimpleOdd G → False` を full wiring)。
- `feitThompson` = `feitThompson_of_noMinimalSimpleOdd noMinimalSimpleOdd hodd` (sorryAx 依存は gap 1 個経由のみ)。

⟹ 下の診断の「最上位還元 1 sorry (+構成)」のうち **還元部分は完了**、残は `sectionSixteenHypothesis` 構成 (= 上 2 ブロック)。

## 実 FeitThompson 経路 (Track B、現状唯一配線されている route)

```
feitThompson (odd ⇒ solvable)                      [FeitThompson.lean — ✅ feitThompson_of_noMinimalSimpleOdd 経由]
  └─ feitThompson_of_noMinimalSimpleOdd (hno) (hodd) : IsSolvable G   [✅ axiom-clean, 強帰納還元]
  └─ noMinimalSimpleOdd (hG : IsMinimalSimpleOdd G) : False           [配線済]
       = noMinimalSimpleOdd_of_section16 hG (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)
          ├─ sectionSixteenHypothesis_of_isMinimalSimpleOdd : IsMinimalSimpleOdd G → S16.Hypothesis G
          │     [🔴 唯一の新 sorry = BG §7-16 + Pf §10-16 全体を構成する義務]
          └─ noMinimalSimpleOdd_of_section16 = BG.AppC.final_contradiction hG hyp   [配線済]
                = S16.nonexistence_of_G hG hyp (theoremC hyp)           [AppC:104-108]
                   ├─ theoremC (hyp : S16.Hypothesis) : p ≤ q          [AppC:97 — 🔴 sorry, ~16 S16 sorry に依存]
                   └─ S16.nonexistence_of_G : theoremC の p≤q vs hyp.q_lt_p で False  [健全]
```

**入力 `S16.Hypothesis G` は仮説のまま** — それを**構成**する wiring
(BG §7-16 局所解析 + Pf §10-15 型解析) が未構築。これが「~214 sorry が closure に未登場」の理由
(closure は S16.Hypothesis を hypothesis 取りするので現状小さい)。`IsMinimalSimpleOdd G` は還元側で構成済
(もはや仮説でなく、odd 非可解からの強帰納で生成される)。

## 核心: Track A (文字理論) は代替でなく**相補的**・必要

- `S16` (Pf §14, G の非存在) は **Dade-isometry / Dade extension / three virtual characters** を使う
  (S16:20,121,440)。現状これらは S16 の構造体に **opaque-Prop placeholder で hoist**。
- ⟹ Peterfalvi 文字理論 (§4-§8 の Dade 機構 + **(6.8) Sibley coherence** + (7.10)) は、その hoist された
  文字理論仮説を**放電するために必要**。Track A と Track B は両方要る。現状 **decoupled** (S16 が hoist、
  S08/S09 を消費しない; (6.8)/(7.10) は orphaned leaf)。
- ⟹ T6/T7 の作業は **genuine な必要部品**。ただし FeitThompson への距離は縮めていない (最深 leaf)。

## 残作業の正直な sizing (~214 sorry、4 相補ブロック)

| ブロック | 規模 | 役割 | 現状 |
|---|---|---|---|
| **BG §7-16 局所解析** | ~108 sorry | maximal subgroup 構造 → `IsMinimalSimpleOdd` を供給 | roadmap が「直列ボトルネック」と認識; §7 Lem7.1/Prop1.16 進行中 |
| **Pf §10-16 型解析+最終矛盾** | ~103 sorry | type I/II/.../V 分析 → `S16.Hypothesis` を供給 (BG + 文字理論を消費) | 全 scaffold、opaque-Prop placeholder 多 (vacuity risk は proof-fill 時) |
| **Pf §5-9 文字理論 (Track A)** | **2 sorry** | coherence/Dade/(7.10) → §10-16 の hoist 仮説を放電 | (6.8) T6 完・T7 設計済; **engine bug (§G-A) が T8 を塞ぐ** |
| **最上位還元** | ✅ 還元完了 / 残=S16.Hypothesis 構成 | odd⇒minimal-simple (✅ `feitThompson_of_noMinimalSimpleOdd` axiom-clean) + S16.Hypothesis 構成 (`sectionSixteenHypothesis_of_isMinimalSimpleOdd`、上 2 ブロックに帰着) | 2026-06-04 還元 done; 残 gap は §7-16/§10-16 へ吸収 |

**axiom-laundering・循環は皆無** (scaffold は honest)。但し §10-16/S16/AppC の opaque-Prop placeholder は
proof-fill 時に vacuity risk (現状 consumer も sorry ゆえ benign、`scaffold-opaque_prop_convention` 参照)。

## 優先順位の選択肢 (project owner 判断)

1. **Track A 完遂 (character module 完成)**: engine bug 修正 → (6.8) T8-T11 → (7.10)。§5-9 を 1 つの完結
   モジュールに。Pro: 近い・well-understood・T7 設計済。Con: §10-16 wiring まで orphaned、theorem 距離は不変。
2. **spine 接続**: 最上位還元 (odd⇒minimal-simple) + IsMinimalSimpleOdd/S16.Hypothesis の skeleton を honest に
   構築 → FeitThompson を「裸 sorry」から「真の依存木」に。Pro: theorem への進捗が可視化。Con: scaffold plumbing 大。
3. **BG §7-16 (bulk bottleneck)**: roadmap の stated 直列ボトルネック。Pro: 最大ブロック・全体に効く。Con: 巨大・
   本セッション context (Peterfalvi) 外。
4. **§10-16 wiring**: hoist 仮説のうち (6.8)/(7.10) で放電可能なものを特定し、Track A↔B を実接続。Pro: orphan 解消。
   Con: §10-16 の opaque-Prop を実 statement に materialize する必要 (重い)。

**推奨の考え方**: 「最深 leaf 優先 (Track A drill)」は genuine だが theorem 距離を縮めず proximity 誤認を生む。
goal が「Peterfalvi 文字理論モジュール完成」なら 1、「theorem への測定可能な進捗」なら 2→(4) が筋。
いずれにせよ **engine bug (§G-A) は Track A 継続の前提**、**「2 sorry」表現は今後使わない** (4 ブロック sizing で語る)。

## エンジン bug (§G-A) — Track A 継続時の最初の必須修正
`DadeChainStep`/`peterfalvi_66_coherence_of_X_from_dade`/`dadeOrthonormalCharacterImageFamily`/
`dadeIntegralCharacterMap_inner_eq_on_supported_span` の個別 support 仮説を、Y-family が受けた差分 support
弱化 (`coherentEqualDegree_fromDade`) と同様に弱化。内部は差分しか使わない (監査で trace 済)。これ無しでは
T8 (X coherence) が instantiate 不能。
