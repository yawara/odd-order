# FT フロンティア再設計 — 4 独立フロント W1–W4 (2026-06-25)

> **⚠ レーン配分は `ft_lane_reallocation_2026_06_28.md` が新正本** (2026-06-28〜、ゲートなし・signature
> contract 方式、lane 名 `a/b/c/d`)。本ファイルは **honest FT 経路の構造 (Arm A/B、on-path ~27 宣言、
> 凍結リスト) の参照**として有効 (W1↔δ / W2↔β / W3↔α / W4↔γ に対応)。
> ~~**このファイルが「honest FT 経路の真の構造 + レーン配分」の正本** (2026-06-25〜)。~~
> ~~`ft_path_policy.md` §5 の lane 割当表 / `merge_monitor.md` の 🔒 所有マップは本ファイルへ従属 (relane #9)。~~
> (2026-06-28 に `ft_lane_reallocation_2026_06_28.md` へ移管; 本ファイルは Arm A/B 構造・on-path 宣言リストの
> 履歴参照。注記 2026-07-02)。横断スナップショット (`ft_master_roadmap_2026_05_29.md` 等) は履歴。
>
> **生成**: `ft-frontier-remap` workflow (run `wf_33ba58ab-bf5`, 10 agent / 1.29M tok / 21.5 min)。
> 6 並列 map (read-only, comment-stripped sorry catalog) → 4 adversarial verify (cite-DAG / import-closure)。
> ユーザー裁可 = 「4 フロント並行 W1–W4」(2026-06-25)。

---

## 0. なぜ再設計したか — 旧モデルの 3 つの誤り (検証で判明)

実 sorry 120 のうち honest な `feitThompson` が透過的に必要とするのは **~27 宣言**だけ。それは
**数学的に独立な 4 フロント**に割れる (敵対的 cite-DAG 追跡で検証)。旧「ファイル所有ベース 4 レーン」は
この 4 フロントと**ズレており**、それが idle / relane 連発 (relane #1–#8) の正体だった。

| 旧モデル | 検証結果 (workflow `wf_33ba58ab-bf5`) |
|---|---|
| 「S16⊃S15⊃…⊃S10 が `extends` で直列に積み上がる spine」 | **誤り**。`S15.Hypothesis` は **flat record** (`S15_SAndT_Setup.lean:80`)。honest 構成は `sectionSixteenHypothesis_of_inputs` (`FeitThompson.lean:1804`) による **3 producer mp/tp/cd の flat assembly** (sorry-free + `#print axioms` で `sorryAx`-free 検証)。S10–S14 の per-subgroup `Hypothesis(M)` は局所仮説で**構成の再帰経路上に無い** |
| 「App.C は Peterfalvi §16 の非存在論法を bypass する」 | **誤り**。`BG.AppC.final_contradiction` (`AppC_FinalContradiction.lean:168`) → `S16.nonexistence_of_G` → `field_normalizer_structure` (POLE-2, Pf 14.2, `S16_NonExistenceG.lean:3369`) を**実際に構成・消費**。POLE-2 / §14–16 char cascade は **genuine に on-path** (Arm B) |
| 「残りは char 飽和で群論 runway は枯渇」 | **PARTIAL**。char が数で過半 (~55/89 on-path) は正しいが、**BG §14–16 の carrier/局所解析は char gate の無い群論で actionable-now** (= W1)。群論は枯渇でなく carrier-construction カテゴリへ**移動**しただけ |

**honesty 確認 (vacuity でない)**: `cd` の `tauS:=0, Sset:=∅` placeholder は健全 — `S16.Hypothesis` が
それらに **Prop 制約を課さず** (S16 内で未参照、grep 0 件)、矛盾は `eta = τ₃∘ω` + `FieldNormalizerData`
という genuine な char/構造内容のみを経由する。`section16CharacterData_of_isMinimalSimpleOdd` は
AxiomsCheck `#assert_only_allowed_axioms` 登録済。**vacuity 問題は無い。**

---

## 1. honest FT 経路の真の構造 — 2 アーム / 4 独立フロント

```
feitThompson ✅ (sorry-free reduction)
├ Arm A: sectionSixteenHypothesis_of_isMinimalSimpleOdd
│        → section16Inputs_of_isMinimalSimpleOdd → 3 producer mp/tp/cd で S16.Hypothesis を flat 構成
│   ├─ W1  BG §16 Prop 16.1 bridges + type-P carrier 構成     [純群論・char gate なし]
│   ├─ W2  §12 all-Type-I 非存在 tower → theorem88_caseB       [§12 char cluster]
│   └─ W3  §10–11 (非)coherence → 唯一の bare sorry (11.9.b)   [中心 char 核・臨界路最狭点]
│          + no_typeV (10.8 / 10.10)
└ Arm B: noMinimalSimpleOdd_of_section16 → AppC.final_contradiction → nonexistence_of_G
    └─ W4  POLE-2 field_normalizer §14–16 char cascade + §15 S&T setup  [独立アーム]
```

**検証 (CLAIM B REFUTED)**: 独立な深いフロントは 1–2 でなく **3–4 が同時に存在**。**W1 (群論) と W4
(POLE-2 char) は upstream gate を一切共有しない**。W2/W3 は S10 carrier を共有するが分離可能。
**4 レーン分の独立した幅が数学的に実在する** — 旧 idle は数学が狭いせいでなく所有境界のズレ。

**検証 (CLAIM C, 単一ボトルネック説は否定)**: on-path sorry の大半は**互いを cite しない self-contained
bare stub**。どれか 1 つ上流を埋めても cascade unblock しない。最大 fan-out は
`proposition_type_classification` (W1, 8+ consumer) と `no_typeV_maximal` (W3, 両極から到達)。

---

## 2. 4 フロント定義表

| | フロント | レーン | 中核 sorry (file:line) | 性質 | gate |
|---|---|---|---|---|---|
| **W1** | BG §16 Prop 16.1 + type-P carrier | **lane-f** | `proposition_type_classification` `BG/Ch4_FamilyOfMaximal/S16_MainResults.lean:2404` (6 bridge @2437-2448) | **純群論/局所解析** | **無 (今すぐ)** |
| **W2** | §12 all-Type-I 非存在 tower | **lane-c** | `theorem88_caseB_holds` `Peterfalvi/S14_MaximalI.lean:1040`; `typeI_frobenius:189` (12.7) | §12 char (Dade/coherence/ρ-congruence) | 上流 producer 完成済 → 今すぐ |
| **W3** | §10–11 中心 char 核 | **lane-b** | `card_kappaHall_lt_of_isTypeIIIorIV` **`FeitThompson.lean:426`** (11.9.b, **唯一の bare FT sorry**); `S_not_coherent` `S12_MaximalIII_IV_V.lean:5484` (10.8); `typeV_forces_coherence:5786` (10.10) | 中心 char (§11 Dade-norm engine + §10 非coherence 計数) | 上流 producer 完成済 → 今すぐ |
| **W4** | POLE-2 field normalizer | **lane-h** | `field_normalizer_structure` → `exists_MHypothesis` `S16_NonExistenceG.lean:3338`; `betaM_expansion:1878`; `main_size_bounds_structural:1797`; §15 `basic_structure_gated` `S15_SAndT_Setup.lean:283` | §14–16 char+Dade (一部群論構造) | 今すぐ (独立アーム) |

### W1 (lane-f) — BG §16 Prop 16.1 + type-P carrier 構成 【最優先・最 de-risk】
- **主目標**: `proposition_type_classification` の 6 inline bridge (S16_MainResults.lean:2437-2448) を埋める。
  engine `proposition_type_classification_of_inputs` + 4 input (`isTypeI_of_isTypeF` 等) は sorry-free 済。
- 残 6 bridge = forward 2 (型-P₁ `TypePData` 構成、Pf (8.3)/(8.8)) + reverse 4 (carrier-level
  `π(W₁) ⊆ κ(M)` / W₁=κ-Hall characterization、**issue 8015**)。**いずれも BG 構造理論で char gate 無し。**
- **主所有**: `OddOrder/BG/**` (特に `Ch4_FamilyOfMaximal/{S16_MainResults, S14_TypePCounting, S15_MF, S16_PairIntersection}.lean`)
  + `FeitThompson.lean` の mp-producer / type-P carrier 宣言 (`exists_section16MaximalPair_data`,
  `section16MaximalPair_*`, `typePData_*`, `section16TypePStructure_*`)。
- **検証残し**: `theoremA_maximal_structure` (S16_MainResults.lean:144) が真に on-path か
  (ft-assembly は「Yes, S12:632 経由」、verifier は「docstring 参照のみで off-path、honest 構成は
  sorry-free standalone conjunct を使う」)。**W1 が最初に確定** — off-path なら凍結。

### W2 (lane-c) — §12 all-Type-I 非存在 tower 【theorem88_caseB_holds】
- **主目標**: `theorem88_caseB_holds` (S14_MaximalI.lean:1040) = mp 構成で all-Type-I 枝を排除。
  背後に §12 tower 12.2–12.16 (14 sorry: Dade isometry / coherence / ρ-congruence)。
- **主所有**: `OddOrder/Peterfalvi/S14_MaximalI.lean`。
- 上流 coherence producer ((5.7)/(6.2)/(6.3)/(6.8)) は**完成済** → consumer 側を埋める段階。
  **lane-c が直前まで作った (5.7) はここで消費される見込み** (供給→消費の wiring)。

### W3 (lane-b) — §10–11 中心 char 核 【唯一の bare FT sorry + no_typeV】
- **主目標 (臨界路最狭点)**: (1) `card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson.lean:426, Pf 11.9.b)
  の honest 証明 — §11 coherence/Dade-norm engine を要する。(2) `no_typeV_maximal` (10.10) を
  `S_not_coherent` (10.8, S12:5484) + `typeV_forces_coherence` (10.10, S12:5786) から締める
  (§7 ρ-machinery + (8.8) Type-II partner)。(3) §10 Dade-support `dadeSupportHypotheses_typeP`
  (S10:310, 8.15)、`exists_typeII_maximal_with_w2_of_typeP` (S10:148, 8.8 partner)。
- **主所有**: `OddOrder/Peterfalvi/{S10_MinimalSimpleStructure, S11_MaximalII_III_IV, S12_MaximalIII_IV_V,
  S13_MaximalIII_IV}.lean` + `FeitThompson.lean:426` (card_kappaHall_lt_of_isTypeIIIorIV) +
  必要に応じ §3–§9 char API supply (S03–S09)。**issue 2020 を保持。**
- **⚠ on/off の精密区別**: (11.9.b) の証明が cite する §11/§13 の coherence/Dade-norm **補題は on-path**
  (構築/再利用してよい)。だが Peterfalvi **内部の §13 type-III/IV 矛盾 endpoint**
  (`S13_MaximalIII_IV` の `final_typeIII_conclusions` 系) は honest 構成が **App.C/W4 経由を採ったため
  off-path** (FeitThompson が import すらしない代替路)。**内部矛盾 endpoint を目標にしない。**

### W4 (lane-h) — POLE-2 field normalizer §14–16 char cascade 【独立アーム B】
- **主目標**: `field_normalizer_structure` の §14–16 char cascade を埋める —
  `exists_MHypothesis` (S16:3338)、`betaM_expansion` (1878)、`generic_character_bound` (1970)、
  `main_size_bounds_structural` (1797)、`T_side_caseB_facts` (133)、`U_cyclic` (2361)、`V_cyclic` (2441)、
  `orthogonality_switch`、`exists_LHypothesis`。+ §15 setup: `basic_structure_gated` (S15_SAndT_Setup:283)、
  `c_eq_one` (612, 13.12)、`caseB_order_u` (779, 13.15)。+ §15 S&T 構造: `normalizer_W1` (S15_SAndT:140, 13.16)、
  `card_Q_eq` (426)、`tConjugate_fitting_data` (443)、`card_LF_coprime_pq` (463)、
  `complement_inf_Q_structure` (892, 13.17)。
- **主所有**: `OddOrder/Peterfalvi/{S15_SAndT, S15_SAndT_Setup, S16_NonExistenceG}.lean`。
- §13.17 構造コア (`normalizer_W1` 等) は Frobenius/Hall/centralizer の群論で一部 sorry-free 済
  (`notes/peterfalvi/s13_17_structural_program.md`)。残は char/Theorem-E residual。

---

## 3. 凍結リスト (provably off-path — 割り当てない)

- **23 appendix sorries** — `FeitThompson` の推移 **import closure (283 module) に存在しない**ので cite 不能
  (CLAIM D CONFIRMED, import グラフによる強い保証):
  `Peterfalvi/Appendices/{Suzuki(5), Suzuki2Groups(4), FeitSibley(3), NearFields(2), Huppert(1)}` +
  `BG/{AppD_CNGroups(3), AppE_FurtherResults(5)}`。**⚠ BG App*C* は on-path** (最終矛盾そのもの)、混同しない。
- **Peterfalvi 内部の代替矛盾ルート** (honest 構成が App.C/W4 経由を採ったため未使用):
  §9 Frobenius-family (`S09 card_G0_lower_bound`, 7.10)、repo §13 内部 type-III/IV 矛盾 endpoint
  (`final_typeIII_conclusions`)、`T_typeII` (S16:1564, 14.9)。
- **これ以上の §5/§6 coherence supply** — (5.7)/(6.2)/(6.3)/(6.8) は**完成済**。binding constraint は
  下流 consumer (W2/W3) に移った。**供給を積み増しても on-path は進まない。**

---

## 4. 優先度 + 運用

1. **W1 を先頭** (純群論・gate 無し・最大 fan-out・mp 側を開放 → 最も de-risk)。
2. **W3 を並行で早期着手** (臨界路の最狭点・最深 → 最長リードタイム、(11.9.b) は唯一の bare FT sorry)。
3. W2 / W4 は残り 2 フロントを淡々と。4 フロントは**最後にアーム合流**するので各々独立に積めばよい。
4. **cross-front 規則** (merge_monitor §取り決め踏襲): 各レーンは自フロント主所有のみ編集、他は cite。
   `FeitThompson.lean` は W1 (mp/carrier 宣言) と W3 (:426 bare sorry) が**宣言単位で共有** —
   prefix-split 規約で衝突回避、互いの宣言は触らない。signature 要請は notes/issue 経由で hub へ。
5. **doneness は sorry 数でなく carrier/仮説の構成可能性で判定** ([[scaffold-sorry-free-not-done]])。
   0-consumer は off-path の根拠にしない ([[feedback-orphaned-not-reason-to-defer]])。

---

## 5. 数値サマリ (2026-06-25)

- 実 sorry 総数 ≈ 120 (comment-stripped)。BG 群論 spine §1–13 は **完全 sorry-free**。
- honest FT 経路 = **~27 sorry-bearing 宣言** (1 個 `proposition_type_classification` が 6 token)。
  内訳: W1 (Prop 16.1 6 bridge + carrier) / W2 (§12 tower) / W3 (11.9.b + no_typeV + §10 support) /
  W4 (POLE-2 §14–16 + §15 setup)。
- provably off-path appendix = **23**。残りは「honest-completion-needed だが現 cite 経路外の leaf」
  (per-subgroup Hypothesis producer、§13/§9 内部矛盾、未 wire の §11 engine 等)。
- 全 4 レーン clean / 未マージ作業ゼロ / 全 main 配下。lane-state は再配置に blocker 無し。

> 個別ゲートの掘り下げ: `notes/peterfalvi/s10_13_maximal_structure.md` (W2/W3)、
> `notes/peterfalvi/s13_17_structural_program.md` (W4)、issue 8015 (W1)、issue 2020 (W3)。
