---
id: 81
slug: w2-s12-alltypei-tower
title: "W2 (lane-c): §12 all-Type-I 非存在 tower → theorem88_caseB_holds"
created: 2026-06-25
---

# W2 (lane-c): §12 all-Type-I 非存在 tower → theorem88_caseB_holds

> **⚠ 2026-06-26 status (relane #10→#11)**: W2 owner は lane-c→lane-h (relane #10) →
> **driver/await に降格 (relane #11, 常駐レーンなし)**。監査 `wf_1cb6284d-bb2` で §12 tower の 14 sorry が
> 全て lane-b §11 char に従属 (ungated 0) と判明 → lane-h は独立価値の高い W1 carrier (issue 2027) へ移動。
> **W2 (`theorem88_caseB_holds`, S14_MaximalI) は lane-b の §11 char landing 時に driver で機会的 close**。
> タイトルの「(lane-c)」は旧 (relane #9)。本 issue は char-gated await item。

## 背景

FT フロンティア再設計 (2026-06-25 relane #9、正本 `notes/meta/ft_frontier_remap_2026_06_25.md`)
の **フロント W2** = lane-c 担当。Arm A の mp 側。§12 char cluster。上流 coherence producer
((5.7)/(6.2)/(6.3)/(6.8)) は完成済ゆえ **consumer 側を埋める段階** — lane-c が直前まで作った
(5.7) `coherent_of_constant_degree` がここで消費される見込み (供給→消費 wiring)。

## やること

- [ ] `theorem88_caseB_holds` (`OddOrder/Peterfalvi/S14_MaximalI.lean:1040`) を埋める
      = mp 構成で all-Type-I 枝を排除 ((8.8) の全 Type-I ケースが impossible)。
- [ ] `typeI_frobenius` (S14_MaximalI.lean:189, Pf (12.7)) = 各 Type-I maximal は kernel M_F の Frobenius。
      (W4 の §15 が cite する partner でもある。)
- [ ] 背後の §12 tower 12.2–12.16 (14 sorry: Dade isometry / coherence / ρ-congruence) を上流から順に。

## 完了条件

`theorem88_caseB_holds` が sorry-free + axiom-clean。mp producer の all-Type-I 排除が解消。

## 進捗ログ

### 2026-06-25 (lane-c 再開): §12 型 I Dade foundation を de-opacify + 構成子

調査 (2 Explore agent + 原文 `04.14_*.mmd` = 書籍 §12 精読) で §12 tower の actionability を確定:
深い char leaves ((12.2)-(12.5),(12.14),(12.15)) は Clifford 分解 + lane-b char API gate、
群論 tower ((12.10)-(12.12)) は (11.9.c)/(9.7.b)/(8.6.a) un-isolated/char-gate。
**ungated で最上流の honest 起点 = 型 I `Hypothesis` の foundation 化**と判断 (S12 の
`exists_hypothesis_of_typeIIIorIVorV` を template に、完成署名の `dadeSupportHypotheses_typeI`
= (8.15) を使用)。

**landed (commit 予定)**:
- `S14.Hypothesis` を de-opacify: free field `tau`(Dade isometry=最も hard な hoisted
  content)/`Sset`/`A`/`R` + opaque Prop 5 個を除去 → genuine carrier
  `{finiteG, maximal, typeI, dadeData : (8.15) DadeSupportHypothesisData, hconj}`。
  `tau`/`Sset`/`A`/`H`/`Hprime` は genuine derived def 化 (`dadeIntegralCharacterMap` /
  L_F からの誘導 / `supportInSubgroup`)。
- `exists_typeI_hypothesis` (sorry-free 本体、(8.15) を cite ゆえ axiom = sorryAx; 型 P
  アナログと同 honest status、AxiomsCheck 非登録)。→ carrier 構成可能性を実証。
  **S15 `TypeIOrthogonalityData.typeISetup` の構築を unblock (W4 を補助)**。
- (12.4)/(12.5) の opaque Prop 仮説を genuine 直交性 `∀χ∈S, ∀α∈R(χ), ⟨ψ,α⟩=0` に置換。
- helper `conj_smul_centralizer_singleton`/`supportKernel_conj_invariant` を S14 に複製
  (S12 で private; cross-lane 編集回避)。
- full build 3884 green。

**landing 2 (commits `643e42af`/`a5e64336`、ユーザー裁可で群論 tower 着手)**:
- `typeF_frobenius_of_isZGroup_complement` / `typeI_frobenius_of_isZGroup_complement` (sorry-free +
  axiom-clean、AxiomsCheck 登録) = (12.10) step 2/(12.16) π=∅ が消費する Frobenius 実現 bridge。
  **知見: 「全 Sylow 巡回 ⟹ card U=exp U」は mathlib `IsZGroup.exponent_eq_card` で無料** (Z-群=全
  Sylow 巡回)。完成済 (8.2.b) `typeF_frobenius_of_card_eq_exponent` に投入。
- **`typeI_frobenius_of_pi_empty` (sorry-free 本体) = (12.7) の易しい方向**「π=∅ ⟹ 型 I は Frobenius」
  (Pf (12.16) 証明第一文)。M_F=H 正規 Hall (8.11) ⟹ complement U 互素 ⟹ U の Sylow-q が M で full
  q-order ⟹ 非巡回なら InPi q で π≠∅ 矛盾 ⟹ U は Z-群 ⟹ bridge。`exists_sylow_le_of_hall` の
  factorization パターン再利用。axiom=sorryAx ((8.11) cite、AxiomsCheck 非登録)。

**tower 着手で判明した entanglement**: (12.10) の残り (難しい方向) は深い: type II 排除=(8.16)+x∈A(L)、
type III/IV 排除=**(11.9.c) [char/lane-b]**+(9.7.b)+(8.6.a) [un-isolated §8]、(12.7) 難方向=(12.8)-(12.16)
counterexample machinery。これらは char/un-isolated-§8 gated。

**残 (downstream, 引き続き W2)**: (12.6) coherence dispatch、(12.10) 難方向 (type 判定) + (12.11)/(12.12)、
char leaves (12.2)-(12.5)/(12.14)-(12.16)、エンドポイント (12.7) 難方向 / `theorem88_caseB_holds` (12.17, +(7.11))。

### 2026-06-26 (lane-c 再開²): (12.7) headline を minimal-counterexample 経由で wire + (12.8) 構成

**landed (commit 予定)**:
- **(12.7) `typeI_frobenius` (headline) を bare `sorry` → honest reduction 化** (S14_MaximalI.lean)。
  書籍の最小反例論法を Lean 化: `π = ∅` (`pi_empty`) を (12.16) `counterexample_contradiction`
  から導き、易方向 `typeI_frobenius_of_pi_empty` (完成済) で各型 I maximal の Frobenius 分解を得る。
  唯一の残 gate = (12.16) char 反例 (citing sorried lemma; 真の hard content の正しい所在)。
  ⚠ `TypeIFrobeniusData` 構造は触らず (S15:1057 が構築); `kernel_eq_MF := True` (frobenius field が
  `typeF.H = M_F` を kernel に既に名指すゆえ vacuous)。S15 consumer (516/1037) 不変 (full build green)。
- **(12.8) `exists_counterexampleHypothesis` NEW (sorry-free + axiom-clean、AxiomsCheck 登録)**: π≠∅ ⟹
  最小元 `p = Nat.find` で `CounterexampleHypothesis` 構成 (InPi witness + `Nat.find_min'` minimality)。
  §8-free well-ordering step = 最小反例論法の入口。これが genuine な新規 group-theory content。
- 配置: (12.7) theorem を依存先 (12.16) より後ろへ移動 (Lean 順序; 書籍 (12.7) は前だが proof は後)。
  元位置にはポインタコメント。full build 3884 green、AxiomsCheck 緑。

### 2026-06-26 (lane-c 再開³, W1 寄与): (12.9) Hall complement discharge

ユーザー裁可で lane-c を最上流 W1 (Prop 16.1) へ振り向け。§12 (12.9) の gate そのものが Prop 16.1 の
Hall complement (issue 2016) ゆえ、lane-c 自ファイル (S14) で衝突なく W1 に寄与:
- **`exists_sigmaKappaCompl_hall_ge_P0` を sorry-free 化** (issue 2016 CLOSED)。型 I⟹型 F (κ=∅, clause a)
  + M_F=M_σ (clause f) を cite、M_σ σ-Hall (`S10.isHall_Msigma_Malpha`, proven) で p∉σ、`Ch03.hall_D` で
  P₀ を (κ∪σ)ᶜ-Hall U に格納。**(12.9) `counterexample_P0_K_structure`/`exists_rankTwoWitness` が
  unconditional 化** (§16 cite modulo)。残 gate = prop_classification の型 I clauses (lane-f issue 8015)。
- full build 3884 green。

**§12 ungated runway 評価**: 残りは全て char (lane-b) / BG §16 (lane-f) / 未抽出 §8 gated と再確認:
(12.6)=`sibleyTarget_frobI` は `SibleyDadeHypothesis` (6.8) full 構成要 (deep char/Dade)、
(12.9) Hall complement=Prop 16.1 (lane-f/W1)、(12.10)/(12.11)=未抽出 §8 ((8.13.c1)) + char、
char leaves=lane-b、(12.16)=char 反例の核、(12.17) `theorem88_caseB_holds`=∃ non-type-I maximal
(char (7.11)/(12.17) Frobenius counting) + (8.8) partner assembly (BG §16)。FT consumer
(`FeitThompson:361`) は `cb.S`/`S_maximal`/`S_nonI` のみ消費 (all-type-I 排除)。

### 2026-06-26 (lane-h 継承, relane #10 / issue 2026 = option C): §12 frontier survey 確定

relane #10 で **lane-h が S14_MaximalI を lane-c から継承** (lane-c は W1 Cor 15.3 へ pivot)。
lane-h 起動時 survey (自己復帰モニター発火 → main 取込 → S14_MaximalI leaf green 3846 jobs) で
**§12 全 14 sorry の gating を確定マップ** (lane-c 評価「全 char/BG/§8-gated」を独立確認):

| 行 | 書籍 | theorem/def | gating |
|---|---|---|---|
| 232 | (12.2) | `character_decomposition_and_dade_domain` | char (Clifford 分解) |
| 258 | (12.3) | `nonconjugate_typeI_R_orthogonal` | char (R(χ) 直交性) |
| 271 | (12.4) | `orthogonal_character_constant_on_coset` | char (ρ-reduction、仮説は de-opacify 済) |
| 282 | (12.5) | `rho_constant_on_H_minus_Hprime` | char (同上) |
| 306 | (12.6) | `sibleyTarget_frobI` | Sibley/Dade `SibleyDadeHypothesis` (6.8) full |
| 1040 | (12.10) | `witness_L_frobenius` | char (型 II/III/IV 排除 = 11.9.c) + §8 (9.7.b/8.6.a) |
| 1049 | (12.11) | `intersection_complement_structure` | char + 未抽出 §8 (8.13.c1) |
| 1315 | (12.12) | `complement_cyclic_order_dvd` | rep-theory (lane-c の FPF core 済) + T=Ω₁(Z(O_p)) setup |
| 1343 | (12.14) | `psi_constant_on_xK` | char (Dade ρ) |
| 1352 | (12.15) | `rhoM_integer_values` | char/Dade (ρ_M 整数性) |
| 1360 | (12.16) | `counterexample_contradiction` | **char 反例の核** (最小反例の最終 Dade 矛盾) |
| 1369 | (12.7) | `pi_empty` | (12.16) cite |
| 1383 | (12.7) | `typeI_frobenius` | pi_empty cite (lane-c が headline を reduction 化済) |
| 1396 | (12.17) | `theorem88_caseB_holds` | char (7.11 Frobenius counting) + BG §16 (8.8 partner)。**FT consumer** |

**結論**: §12 の ungated §8-free runway は lane-c が抽出済で**枯渇**。残 14 sorry は全て
char (lane-b §10-13) / Dade (6.8) / 未抽出 §8 / BG §16 (lane-f) gated。lane-h の honest work は
**(1) deep char de-opacify** (残 opaque Prop 9 個: `CharacterDecompositionData` の equal_degree/
tau_restriction_domain/difference_image_formula/R_eq_union、`CrossOrthogonalityData.orthogonal`、
`DadeNotation` の e_eq_index/rhoFormula/rhoMFormula — いずれも concrete char 内容の特定要、e_eq_index
のみ `e=|L:H|` で clean) か **(2) lane-b/c char landing 後の consumer wiring** で、fresh budget 向き。
[[scaffold-sorry-free-not-done]] ゆえ unblock しない marginal de-opacify は commit のため作らない方針。
**次セッション (fresh budget)**: 最高価値 = `theorem88_caseB_holds` (12.17) の W4-style de-opacify
(char 7.11 counting + BG 8.8 partner を faithful producer に isolate、FT consumer 直結)。

### 2026-06-26 (lane-h fresh budget): ✅ (12.17) `theorem88_caseB_holds` を honest reduction 化

前セッション推奨の (12.17) de-opacify を完遂。**bare sorry を消し、書籍の証明構造に忠実な honest
reduction に置換** (S14_MaximalI.lean、leaf 3846 + full build 3884 green、AxiomsCheck OK)。重要な発見:
**FT consumer (`FeitThompson:361`) は `hall` (全 type-I) 枝で `cb.S/S_maximal/S_nonI` のみ消費して
矛盾を導く** = 真に必要なのは「非 type-I な極大が存在」だけ (full pairing は consumer が第2枝で独自再構成)。
原文 (12.17) の証明構造 = 全 type-I 仮定 → 各 type-I maximal は Frobenius (kernel `L_F`, (12.7)) +
`N_G(L_F)=L` → Hypothesis (7.10) 組立 → Theorem (7.11) で矛盾。

**重要: (7.11)/(7.10) は repo に既存・citable**:
- (7.10) `S09.FrobeniusFamily` carrier 完備、(7.11) `S09.not_trivial_G0` (`FrobeniusFamily`+`G0={1}`→`False`、
  char content は `card_G0_lower_bound`=`CharacterEstimateData` に既に isolate 済) を**直接 cite 可能**
  ⟹ survey が想定した「(7.11) を新 producer に isolate」は不要、既存定理を cite するだけで済んだ。

**landed (3 sorry-free + 2 faithful obligation)**:
- **`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`** (sorry-free + **axiom-clean**, AxiomsCheck 登録)
  = (12.17) の genuine group-theory 核「極大 L (L_F≠⊥) ⟹ L=N_G(L_F)」。`maxNilpotentNormalHall_le_normalizer`
  (L≤N) + simplicity (N=⊤⟹L_F⊴G⟹⊥/⊤ 排除) + coatom (L≤N<⊤⟹=)。汎用・再利用可。
- **`not_all_maximal_typeI`** (12.17 本体、sorry-free given carrier) = `TypeICovering` から `FrobeniusFamily`
  を組立 (`normalizer_eq`←bridge / `isFrobenius`←(12.7) / `kernel_le` を**実証明**) → covering から `G0={1}`
  導出 → `not_trivial_G0` (7.11) で `False`。
- **`theorem88_caseB_holds`** (sorry-free) = `theorem88_dichotomy.resolve_left not_all_maximal_typeI`。
- **isolated obligation 2 本** (faithful, 正しい所在に): `exists_typeICovering` (§8 carrier: reps/two_le/isTI←8.13.c1/
  coprime←8.17/covers←8.17.a, BG Theorem E) + `theorem88_dichotomy` (8.8 BG §16 dichotomy)。
- carrier `TypeICovering` = §8/§17 covering 入力を faithful にパッケージ (lane-b/c/f への精密 hand-off)。

**評価**: sorry 数 1→2 だが [[scaffold-sorry-free-not-done]] 基準で genuine 前進 — bare sorry が隠していた
(12.17) の group-theory 本体 (normalizer bridge + Frobenius-family 組立 + (7.11) 接続) を**実証明**し、
照射不能な char (7.11 内 `card_G0_lower_bound`)・§8 (covering)・§16 (8.8 dichotomy) のみを faithful
obligation に分離。relane #11 の「W2 = char 従属で ungated 0」評価に反し、(12.17) は **ungated group-theory
核を持っていた** (bridge は axiom-clean)。**lane-h は relane #11 で W1 (issue 2027) へ移動**、本成果で W2
の FT-critical endpoint は honest reduction として残置 (driver/await、残 = §8 covering producer + 8.8 dichotomy)。

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W2)、relane #10 (LAUNCH.md 冒頭、issue 2026)
- 主所有: `OddOrder/Peterfalvi/S14_MaximalI.lean` (lane-h、2026-06-26 lane-c から継承)
- 関連: `notes/peterfalvi/s10_13_maximal_structure.md`、issue 2018 (§13 char direction)、2026 (W4→W2 relane)
