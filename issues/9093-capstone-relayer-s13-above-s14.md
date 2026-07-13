---
id: 9093
slug: capstone-relayer-s13-above-s14
title: "§12–16 capstone import inversion — S13 type-determination を §14 上流へ再層化 (FeitThompsonSetup ↔ AppC/S16 instance 依存)"
created: 2026-07-13
---

# §12–16 capstone import inversion — S13_NonGaloisExclusion を §12.10 (WitnessSylowCyclic) の上流へ

> **HUB 裁定依頼 (lane A → hub)**: Peterfalvi (12.10) の型III/IV kernel reduction を実証明したが、
> その唯一の残 obligation `hUcyc` (= `S13.U_isCyclic_of_hypothesis`, proven/sorry-free) を cite する
> には `S13_NonGaloisExclusion` を `WitnessSylowCyclic` に import する必要がある。これが **§12–16
> capstone の import inversion** で阻まれる。back-edge の一方 (edge-1) は lane A が自力で切ったが、
> 残る **edge-2 (FeitThompsonSetup → AppC/S16 capstone) は spine-critical file + b/c territory
> (S15/S16) の instance/scope 配置**に関わるため hub 裁定を要請 (CLAUDE.md「真に判断を要する設計分岐」)。

## 数学的背景 (なぜ §11 が §12 の上流であるべきか)

Peterfalvi 本文の順序では §11.9 (U cyclic, `S13_NonGaloisExclusion`) が §12.10 (Type-I 判定,
`S14_MaximalI/WitnessSylowCyclic`) の**上流**。しかし現 import DAG は逆転しており、
`S13_NonGaloisExclusion` が `WitnessSylowCyclic` を transitively import する (= §12.10 が §11.9 の上流)。
このため §12.10 の証明が §11.9 の結果を cite できない。

## 完了済 (この issue の commit で landed)

- **(12.10) `typeIIIorIV_noncyclic_le_fitting` の reduction を完全証明** (`WitnessSylowCyclic`):
  noncyclic p-group `P₀ ≤ L' = L_F ⋊ U` (U cyclic, `gcd(|L_F|,|U|)=1`) について
  `p ∤ |U|` (さもなくば `P₀ ↪ L'/L_F ≅ U` cyclic で矛盾) → `le_of_coprime_index` で `P₀ ≤ L_F`。
  upstream 6 補題 (`U_isCyclic_of_hypothesis` / `exists_hypothesis_of_*` / `card_U_eq_index` /
  `maxNilpotentNormalHall_isHall` 等) は `#print axioms` で全 axiom-clean 確認済。
- **文の correctness 修正**: 旧文は p-group 仮説欠落で **FALSE** (反例: type III で `P₀ = L' =
  mainSubgroup L III` は noncyclic だが `⊄ L_F`)。`{p} (hp : p.Prime) (hP0p : IsPGroup p ↥P0)` を追加。
- **edge-1 再層化**: §8 centralizer 事実 3 本 (`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall` /
  `typeP_core_centralizer_le_of_mem_fitting` / `typeII_centralizer_le_of_mem_mainSubgroup`) を新 leaf
  **`S14_MaximalI/CentralizerContainment`** へ抽出。`S12_Noncoherence` が `WitnessSylowCyclic` でなく
  これを import → back-edge `S12_Noncoherence → WitnessSylowCyclic` を切った。

## edge-2 blocker (hub 裁定事項)

edge-1 だけでは cycle が残る。第二の back-edge:

```
S13_NonGaloisExclusion → S13_TypeDetermination → S12_Noncoherence
  → S12_TypeIICrossIsometryPair → S12_TypeIIGridTranspose
  → FeitThompsonSetup → AppC_FinalContradiction → S16_NonExistenceG
  → … → S14_MaximalI (hub) → MinimalCounterexample → WitnessSylowCyclic
```

要点: **`FeitThompsonSetup` が `import BG.AppC_FinalContradiction` で capstone (AppC→S16) を引く**。
当初は「AppC の唯一 user は `noMinimalSimpleOdd_of_section16` だけ」と見て、それを downstream file へ
移して AppC import を外す計画だったが、**実測で `FeitThompsonSetup` は AppC→S16 closure から複数を
transitively 必要**とすると判明 (AppC import を外すと build 破壊):

- `Fintype ↥mp.S` instance — `omegaProdCharS_apply_mem_Kstar` (`FeitThompsonSetup:1648`) 他
- `open scoped OddOrder.Peterfalvi.S15.FiniteInduce` scope (`FeitThompsonSetup:70`)
- 追加の instance 群 (`:165`, `:177`, `:182`, `:191`, `:195` …)

`AppC_LemmaC2` (AppC の他方の import、WitnessSylowCyclic 非到達) だけ足しても解決せず → 必要な
instance/scope は **`S16_NonExistenceG` 側 (WitnessSylowCyclic に到達する不安全側)** から来ている。
これは `Section16MaximalPair.S` (FeitThompsonSetup 自身が定義する構造の field) の `Fintype` を
**downstream の S16 closure から借りている architectural inversion** で、9087 RULING #3 の hnoV/hncH0C
threading (§12→§16 を跨ぐ ~120 decl) が作った可能性が高い。

## hub への依頼 = edge-2 の再層化方針を裁定されたい

候補 (いずれも spine-critical `FeitThompsonSetup` + S15/S16 = b/c territory に触れる):

1. **instance/scope を upstream 化**: `Fintype ↥mp.S` は `[Finite G]` から局所導出可能 (`Fintype.ofFinite`)。
   `Section16MaximalPair` 定義付近 (FeitThompsonSetup 内) で instance を供給し、`S15.FiniteInduce` scope の
   供給元 module を直接 import (WitnessSylowCyclic 非到達なら安全) すれば AppC import を外せる可能性。
   ただし defeq diamond リスク (S16 側の既存 instance と不一致だと `rfl` 破綻) を要検証。
2. **FeitThompsonSetup 分割**: Section16 構造体 + 型-P2 machinery を upstream leaf に切り出し、
   AppC を引く最終 assembly (`noMinimalSimpleOdd_of_section16`) を downstream に残す。edge-2 の当初計画の
   拡張版だが、instance/scope 依存も一緒に upstream 化する必要。
3. **S12_TypeIIGridTranspose の Section16MaximalPair 使用を見直す** (9079 obl.2b の産物): §10 の
   grid-transpose が §16 構造体を使うこと自体が inversion。該当 content を §16 側へ移すと edge-2 の
   別経路も切れる。

## 完了条件

edge-2 が解ければ `WitnessSylowCyclic` に `import OddOrder.Peterfalvi.S13_NonGaloisExclusion` を足し、
`hUcyc` の `sorry` (`WitnessSylowCyclic` 内、詳細コメント付き) を 1 行 cite
`OddOrder.Peterfalvi.S13.U_isCyclic_of_hypothesis hG s13` に置換 → (12.10) `witness_L_isTypeI` が
その分 honest 化 (reduction は既に完全証明済ゆえ他に作業なし)。

## 参照

- files: `WitnessSylowCyclic` (reduction + documented sorry), `CentralizerContainment` (edge-1 new leaf),
  `FeitThompsonSetup:1,62,70,1648` (edge-2), `AppC_FinalContradiction` (imports AppC_LemmaC2 + S16).
- 関連 issue: 9087 (lane-A cluster complete + RULING #3 capstone rewire = inversion の起源候補),
  1024 (typeP_Galois/11.9 pending), 9079 (grid transpose obl.2b, Section16MaximalPair 使用元)。
