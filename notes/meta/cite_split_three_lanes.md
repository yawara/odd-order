# 3-lane cite-split (2026-06-19)

> ⚠ **SUPERSEDED (注記 2026-07-02)**: 2026-06-28 に
> [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md) へ移行; B/F/H レーンは消滅。
> cite-split の設計原則のみ履歴として有効。

> FT 終盤の残務を **cite で大粒度に分割**する設計の正本。各レーンは下流 gate を
> named obligation / 既存 sorried producer の cite で切り、独立に大チャンクを進める
> (serial blocking を排除)。プロジェクトの cite-route / gated-endpoint-skeleton 方式
> ([[feedback-gated-endpoint-skeleton-pattern]]) を 3 レーン全域に適用したもの。

## 背景 — なぜ cite-split か

- レーンは **B / F / H の 3 本だけ**(lane-g 退役で BG は F 集約)。
- 残 FT work は本質的に 2 トラック: **Peterfalvi 指標論**(深い char core)と
  **BG 構造**(Prop 16.1 program)。両方 1 レーンずつだと長い直列鎖になり、
  特に H の POLE-2 は §13 char に gate されて停滞していた。
- 解 = **gate を cite して大チャンクに割る**。3 レーンを 2 トラックに配分し、
  **binding constraint = Peterfalvi 指標論に 2 レーン(B+H)**を置く。

### 配分の根拠 (2026-06-19 訂正)

**レーンに固有スキルは無い**(エージェント+worktree、char も構造も等しく可能)。
ゆえに配分は「H の強み」でなく **binding constraint の長さ**で決める:

- **Peterfalvi 指標論が binding**: 最も下流依存が多い(POLE-2 [§13] + POLE-1
  characterData [§13 grid] + **BG §16 の char tail** [§12 の 10.10/10.11 が
  Prop 14.2/tp producer を gate])・最大本体・今 B 単独。**並列化可**(§5/§6 char API
  は sorry-free、§11/§12/§13 は type-case 別クラスタ)。⟹ 2 レーン目 (H) はここ。
- **BG §16 (F 単独) は短い track** + 完全には閉じない(char tail 10.10/10.11 が
  Peterfalvi §12 内)。ゆえに F 単独で可、2 レーン目は不要。
- **当初「H=構造論強み ⟹ BG分担」は誤り**(スキル固有性は無い)。§10-13 を「構造」と
  誤ラベルしたが、§11-13 は chiefFactor/Clifford/coherence/orthogonality = char theory。
  H はそこで **char をやる**(§5/§6 char API を cite)。**leverage: H の §12 (10.10/10.11)
  は POLE-2 と BG §16 char tail の両方を unblock** ⟹ Peterfalvi 配置は BG にも効く。

## 3 大チャンク

| lane | 大チャンク | 主ファイル | cite する gate |
|---|---|---|---|
| **B** | Peterfalvi 指標論コア | S08(6.8) / S15_SAndT(§13 char) / S14_MaximalI / characterData(POLE-1) | (最深=皆がここを cite) |
| **F** | BG 構造 spine (Prop 16.1) | BG/Ch4 S14残 / S15_MF / S16_MainResults | B の char facts + **H の §10-12** |
| **H** | Peterfalvi §10-13 maximal-subgroup 構造 | S10 / S11 / S12 / S13_MaximalIII_IV | B の coherence/Dade |

## cite edges (誰が誰を cite するか)

```
        coherence/Dade
   H  ───────────────►  B   (H が深い char を cite)
   │                    ▲
   │ §10-12 facts       │ §10-12 を §13 の土台に
   │ (10.10/10.11)      │
   ▼                    │
   F  ◄─────────────────┘   (F が B の char + H の §10-12 を cite)
        char + maximal
```

- **H → B**: `dadeSupportHypotheses_typeI/typeP` (Dade), `typeV_forces_coherence` の
  `IsCoherent` (= (6.8) coherence), `support_mutual_exclusion` を named obligation /
  既存 sorried producer の cite で切る。
- **B → H**: §13 char producer (basic_structure 等) は §10-12 の maximal 構造を土台に
  するので、B は H の §10-12 結果を cite。
- **F → B, H**: Prop 16.1 は B の char (exists_L/MHypothesis, characterData) と
  H の §10-12 (10.10/10.11, maximal classification) を named obligation で cite。

## H チャンク詳細 = Pf §10-13 maximal-subgroup 構造 (~37 sorry)

### 構造論で H が証明
- **§10** (S10_MinimalSimpleStructure): `hall_maxNilpotentNormalHall_and_mainSubgroup`,
  `typeF_frobenius_of_card_eq_exponent`, `typeF_card_U0_eq_exponent`,
  `typeII_A_sets_TI`, `typeII_A_sets_normalizer`, `typeI_or_typeII_centralizer_unique`,
  `escapingCentralizers_control`, `bgTheoremE_cover_data`
- **§11-12** (S11_MaximalII_III_IV / S12_MaximalIII_IV_V): maximal type II/III/IV/V 分類,
  **`no_typeV_maximal` (10.10)**, **`theorem88_caseB_prime_orders` (10.11)**
- **§13** (S13_MaximalIII_IV): 構造部

### cite で切る (B 供給, named obligation)
- `dadeSupportHypotheses_typeI` / `dadeSupportHypotheses_typeP` (Dade isometry support)
- `typeV_forces_coherence` の `IsCoherent` 結論 (= S07 coherence, ultimately (6.8))
- `support_mutual_exclusion` (character support)

### leverage (二方向)
- **10.10 / 10.11 → POLE-1**: tp producer (`section16TypePStructure`, F) の prime/ordering
  tail は (10.11) `theorem88_caseB_prime_orders` + (10.10) `no_typeV_maximal` に gate
  ([[s16-typep-producer-unfillable]])。H がここを landing すれば F の POLE-1 char tail が unblock。
- **§10-12 → §13**: B の §13 char cascade は §10-12 maximal 構造を土台に cite。

## POLE-2 (H の旧タスク) の扱い

`field_normalizer_structure` は dispatch + 両主枝 sorry-free、残は §13 char (Lane B) に
bottom-out 済 ([[ft-endgame-two-poles]] issue 2009)。**parked**(named obligation で B を
cite する形で凍結)。H のエネルギーは runway のある §10-13 へ。POLE-2 の残 §13 obligation は
B の char cascade が landing すれば自動 discharge。

## 順序 / 同期

- 3 チャンクは cite で独立ゆえ **着手順序の制約なし**。各レーン即着手可。
- lane↔lane 調整は本ノート + issue 追記 + merge cron ([[cross-lane-sync-via-notes]])。
- B/F の LAUNCH.md は各 worktree ローカル ⟹ 本ノートが合流したら各レーンが読んで再配向。
