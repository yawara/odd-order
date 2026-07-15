---
id: 9096
slug: b-frontier-gated-direction
title: "b: S15-solo 9094 完了 (S-side hbridge closed) — 残 T-side/NormEstimates は cross-lane gated、direction 要"
created: 2026-07-14
type: HUB direction 依頼 (lane b frontier gated)
---

# b の S15-solo 9094 frontier が gated — hub direction 依頼

## 状況: b の 9094/2035 char-degree campaign の S15-solo genuine math は完了

**S-side (13.3.b) forward gate `S_caseB_facts_no_lambda` を完全証明** (hbridge closed、commit
a8b777b6、詳細 = issue 2035 #33/#35):
- caseA (`lambdaWitness_of_caseA`、regular-seed witness) + caseB
  (`lambdaWitness_of_caseB_member` via 新 S11 `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair` = pair 版
  Clifford correspondence) 両方 genuine 証明。#print axioms sorryAx なし。
- `lambdaCluster_or_caseB` dichotomy の S-side が honest 化。
- 併せて: TTypeII cross-lane 移行 (overstatement 除去) + dichotomy keystone + translation API 抽出。

## 残る 9094 gate は全て cross-lane gated (b-solo S15 では close 不能)

精査確定 (issue 2035 #29/#36):

1. **`tSide_theta_package_of_not_caseB_core`** (ν-gated (13.4) T-package) と
   **`deltaPrime_eq_one_T`** (ν-gated (13.3.c) T-side): **a-owned ν-carrier** (`nuGridSupply` /
   `NuGridSupplyData`、FeitThompson{,Setup}.lean) 依存。discharge = 「hyp.nu ↔ certainTypeT grid
   同定 + muS_* T-instance readout」で a-territory (FeitThompson.lean 編集要)。

2. **`T_caseB_facts_no_lambda`** (no-λ T-mirror): **S16-gated**。T-side D/v/Galois machinery
   (`v_eq_one_twenty_one_of_caseB` 等) は S16_NonExistenceG/** (S15 の下流)、`q < p` は S16
   Hypothesis の field (S15 に無し)。S15 から到達不可。de-opacify も forward-reference で不適
   (S_caseB_facts_no_lambda が後方定義、reorder churn 過大)。

3. **NormEstimates 5 obtain-site 移行** (§13 analytic overstatement 除去、issue 2035 #29):
   honest producer (S15_CharacterDegreeSupply) が NormEstimates の**下流** (import DAG)。
   relayer に要する S15→S16 inversion `CoherenceEtaOrthogonality → S16_GridExpansion` は
   **genuine** (2 lemma 使用) かつ **S16_GridExpansion = c-owned**。cross-lane relayer。

## A-lane ν-carrier audit (2026-07-14)

### Canonical grid package は着地

`OddOrder/FeitThompsonNuGrid.lean` に、`mp.certainTypeT` から作る canonical `nuT` について
`NuGridSupplyData` の**純粋な grid field 全部**を証明した。具体的には irreducibility、
row injectivity、orthonormality、degree congruence、base sign、row-sum induction、reverse
dichotomy、(4.8) support、(4.3.c) value、(4.9.a) conjugation である。各 theorem の
`#print axioms` は `[propext, Classical.choice, Quot.sound]` のみ。関連 commits:
`bb959962`, `83d63b79`, `d0d3e9ca`, `6e106fdd`, `9d221886`。

### 現行 `NuGridSupplyData` は二つの独立理由で generic producer にできない

1. **generic `hyp.nu` の row-translation gap**: `Hypothesis.nu_definition` は各 row の差だけを
   拘束する。各 row に任意の class function を一様加算しても保存されるため、generic
   `hyp : Hypothesis G` から `nu_irreducible` 等は導けない。canonical `nuT` との同定を
   carrier 契約に明示する必要がある。
2. **`V_commutative` は grid fact ではなく post-(14.9) fact**: canonical `V` は `T_F` の
   `T'` 内補群であり、一般の type-P datumでは nilpotent までしか得られない。既存の正しい
   theorem `S15.isMulCommutative_V` も `IsTypeII T`（(14.9)）を要求する。現行
   `Hypothesis.swap` はすでに `hT2 : IsTypeP2 T` を引数に取る一方、前段の
   `NuGridSupplyData` が `V_commutative` を無条件 field に混在させている。さらに現行
   `S16.T_typeII` / `T_isTypeP2` は `sorryAx` を継承し、その前段には
   `T_side_caseB_facts` があるため、これを A 側 producer から cite して field を埋めるのは
   (13.4)→(14.9) の循環を隠すだけである。

したがって cross-lane API 修正は、(a) canonical grid facts を canonical `nuT` 同定付きで
thread し、(b) `V_commutative` をその bundle から分離して `Hypothesis.swap` の既存 `hT2`
以後に供給する、という依存順を保存する必要がある。A lane は b-owned
`HypothesisSwap.lean` の signature を無断変更しない。

## 🧭 HUB RULING (2026-07-14, tick 32): **(A)-modified — b は待機でなく bundle split を自ら実装して T-side を再開**

1. **a の canonical ν-grid package landing を承認** (tick 29–32、13 grid theorem 全て
   AxiomsCheck assert 登録済み・`#print axioms` clean、hub 合流ゲートで検証済)。
   A-lane audit の 2 主張は hub が code-level で独立確認:
   - `V_commutative` = `HypothesisSwap.lean:119` の無条件 field / 正本供給
     `S15.isMulCommutative_V` (`S15_SAndTBasic.lean:342`) は type-II data を要求 /
     `Hypothesis.swap` は既に `hT2 : IsTypeP2 T` を引数化 (`:154`)。混在は依存順違反 — 確認。
   - row-translation gap: generic `hyp.nu` は `nu_definition` (row 差分拘束) のみでは grid
     facts を導出不能。producer は canonical 構成サイト (`FeitThompson.lean`、そこでは
     `hyp.nu ≡ nuT` が definitional) で供給するのが正 — 確認。`S16.T_typeII`/`T_isTypeP2`
     経由の埋め込みが (13.4)→(14.9) 循環を隠す点も audit のとおり (a producer からの
     `V_commutative` cite は禁止)。
2. **b の次 work (ungated、b-owned)**: `NuGridSupplyData` の分割手術 in `HypothesisSwap.lean` —
   (i) `V_commutative` を bundle から除去して pure grid bundle 化、(ii) `S_U_commutative`
   (`:247`) の供給を `hT2` 以後の supply へ再配線 (swap の追加引数 or (14.9) 系 theorem 経由 —
   実装は b 裁量)、(iii) 新 signature を本 issue に記録して a へ通知。landing 後 b は
   T-side (13.3)/(13.4) (`tSide_theta_package` / `deltaPrime_eq_one_T`) を再開。
3. **a の follow**: b の split landing 後、canonical 構成サイトで pure grid bundle の
   producer を thread (a-territory、`FeitThompson.lean`)。
4. **他 option の処置**: (B) 不要 (a が organic に build 済み)。(C) NormEstimates relayer は
   ν-carrier 経路の完遂後に再評価 (c と coordinate、独立 issue で)。(D) 不要 (b に ungated
   genuine work が発生)。(E) は上流優先タイブレークで後回し (bundle split が b 自身の T-side
   frontier の直接上流で先行)。

## direction 依頼 (hub 裁定)

b の S15-solo char-degree frontier は上記の通り cross-lane gated。次の b work の方向を依頼:

- **(A)** a-lane の ν-carrier (nuGridSupply discharge) を優先させ、b は un-gate 波及を待って
  T-side (13.3) を再開 (tSide_theta_package + deltaPrime_T + 以後の T-side dichotomy)。
- **(B)** b に ν-carrier discharge の carve-out (FeitThompson.lean proof-only) を付与し b が build。
- **(C)** NormEstimates relayer を c と coordinate (S16_GridExpansion の grid lemma を
  CoherenceEtaOrthogonality が要する分だけ S15 へ移す/再配線)。cross-lane、規模大。
- **(D)** b を別クラスタへ reallocation (char-degree S-side 完了ゆえ)。
- **(E)** b-solo prerequisite として T-instance hbridge (S-side の T-analog、S11 char theory、
  ungated だが payoff は上記 gate 依存で deferred/speculative) を build させる。

b 推奨 = 特になし (どれも cross-lane 調整 or a-lane 進捗待ち)。hub の cross-lane 視点で裁定を。
b は待機中 re-assess を continue (a-ν landing で un-gate 波及を検出したら T-side 再開)。

## 参照
- issue 2035 (#33/#35/#36)、issue 9094 (RULING)、commit a8b777b6 (hbridge closed)

## ✅ b 実施報告 (2026-07-14, ruling item 2 完了): bundle split landed

`HypothesisSwap.lean` の分割手術を実装、build green (4132 jobs)。

### 新 signature (a へ通知 — producer thread はこの形を対象に)

1. **`NuGridSupplyData` = pure grid bundle 化**: `V_commutative` field を**削除**。残る field は
   grid-theoretic のみ (`nu_irreducible` / `nu_row_injective` / `nu_orthonormal` /
   `nu_degree_modEq_deltaPrime` / `deltaPrime_zero_eq_one` / `nu_rowSum_eq_induce` /
   `nu_reducible_dichotomy` / `nu_diff_support` / `nu_apply_of_not_mem_W1` / `nu_conj`)。
   全て `FeitThompsonNuGrid.lean` の canonical `nuT_*` theorem と 1:1 対応 (a の 13 assert が
   カバー済み)。a の producer discharge (`Hypothesis.nuGridSupply` の sorry 置換) は
   canonical 構成サイトでの `hyp.nu ≡ nuT` 同定 + これら grid field の readout のみでよい —
   post-(14.9) fact は一切要らない。

2. **`Hypothesis.swap` に明示引数 `hV` を追加** (`hT2` 直後、(14.9)-conclusional グループ):

   ```
   noncomputable def Hypothesis.swap [Finite G] (hyp : Hypothesis (G := G))
       (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
       (hV : IsMulCommutative ↥hyp.V)          -- ← 新引数 (13.2.a at T)
       (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
       (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
       (pins : NuGridSupplyData hyp) : Hypothesis (G := G)
   ```

   `S_U_commutative := hV` に再配線 (依存順保存: V の可換性は `hT2` 以後の supply)。

3. **consumer 2 箇所は signature 不変で内部導出** (「(14.9) 系 theorem 経由」ルート):
   `typeI_caseC_dual_dichotomy` (S15_SAndT.lean) / `typeIBetaL_eta_col_constant`
   (S15_SAndTGrid.lean) は既存引数 `hT2 : IsTypeP2 hyp.T` から
   `(proposition_type_classification _hG hyp.T_maximal).2.1.mpr hT2 : IsTypeII hyp.T`
   (BG Prop 16.1(b) dictionary、axiom-clean) → `isMulCommutative_V` (genuine 証明、
   Schur–Zassenhaus conjugacy) で `hV` を導出して渡す。下流 consumer ゼロにつき波及なし。

### 循環断ち切りの確認

`V_commutative` の供給が `S16.T_typeII` (sorryAx、`T_side_caseB_facts` 前段) を経由する
ルートは存在しなくなった: swap への供給は caller の `hT2` (これ自体が (14.9)-conclusional
引数として上流から供給される) からの dictionary 導出のみ。(13.4)→(14.9) 循環は構造的に
不可能になった。

### b 次 work

ruling item 2 final clause に従い T-side (13.3)/(13.4) を再開
(`tSide_theta_package_of_not_caseB_core` / `deltaPrime_eq_one_T`、issue 2035 文脈)。

## ✅ a 実施報告 (2026-07-14): canonical pure ν-grid carrier producer landed

HUB RULING item 3 を実施した。`Section16CharacterData` と `Section16Inputs` に、split 後の
`NuGridSupplyData` と 1:1 対応する 10 個の pure ν-grid proof fields を thread し、canonical
`nuT_*` 定理から全 field を構成した。named-input boundary の producer は次の通り:

```lean
theorem OddOrder.sectionSixteenNuGridSupplyData_of_inputs
    (hodd : Odd (Nat.card G)) (inp : Section16Inputs G) :
    Peterfalvi.S15.NuGridSupplyData
      (sectionSixteenHypothesis_of_inputs hodd inp).base
```

公理監査は `[propext, Classical.choice, Quot.sound]` のみ。AxiomsCheck assertion 登録済み、
`lake build OddOrder.FeitThompson OddOrder.AxiomsCheck` green (4189 jobs)。post-(14.9) の
`V_commutative` は producer の型にも証明にも現れない。

### 残る consumer rewiring (cross-lane; hub arbitration target)

generic `Hypothesis.nuGridSupply` は引き続き sorried theorem のままであり、置換可能な generic
proof ではない。`nu_definition` は row differences しか拘束せず、各 row の一様平行移動を
排除できないためである。したがって canonical producer を consumer まで明示的に運ぶ必要がある。

最小の依存順保存案は、c-owned `S16.Hypothesis` に
`nuGridSupply : S15.NuGridSupplyData base` を追加し、A の
`sectionSixteenHypothesis_of_inputs` が上記 producer 相当の fields で埋めること。その上で b-owned
S15 の grid-dependent chain (`typeIBetaL_eta_col_constant`, `typeI_caseC_dual_dichotomy`,
`typeIOrthogonalityGridData_of_coherent78`, `typeI_orthogonality_dichotomy`,
`complement_not_le_Q` → `complement_card_eq_pq` → `typeI_overNormalizer_complement` →
`typeII_overNormalizer_frobenius`) に explicit `pins` を通し、c-owned S16 callers が
`hyp.nuGridSupply` を渡す。これにより generic S15 hypothesis を不当に強化せず、canonical
Section 16 construction だけが pure ν-grid facts を供給する。

## 📣 b 追加通知 (2026-07-14, /loop iter 7): swap の hV 供給が unconditional 化

`Hypothesis.isMulCommutative_V_unconditional` (TSideDegrees.lean、sorry-free) が landed:
(11.9.c) chain (S13_NonGaloisExclusion — universal type-IV 排除 + witness conjugacy transfer) に
より、`IsMulCommutative ↥hyp.V` は **(14.9) 入力なし**で証明済み。a の producer threading で
`Hypothesis.swap` の `hV` 引数はこれで直接埋められる (consumer 側の hT2-dictionary 経由も
そのまま有効)。audit の「V_commutative = post-(14.9) fact」判定は audit 時点では正しかったが
現在は解消 (bundle から外す API 設計自体は grid/structural 分離として引き続き正)。

## 🧭 HUB 追記 (2026-07-15, issue 0118 再設計) — bundle split landing 確認 + a-1/b-5 kickoff

- **RULING item 2 (bundle split) の landing を監査で確認** (NuGridSupplyData に V_commutative 無し、
  `Hypothesis.swap` は独立 `hV` 引数で `S_U_commutative := hV` 配線済み)。
- **RULING item 3 (a の follow) を 0118 (a-1) として正式 kickoff**: canonical producer
  `sectionSixteenNuGridSupplyData_of_inputs` (FeitThompson.lean:1583、proven 確認済) を carrier
  threading で FT-layer から供給。generic `Hypothesis.nuGridSupply` は row-translation gap ゆえ
  そのまま討伐不能 — carrier 入力 explicit param 形へ restate し、Supply 層 ~8 consumer の切替は
  **b (0118 b-5、a-1 landing 後)**。分担境界と新 signature は本 issue に記録して相互通知。

## ✅ a-1 実施報告 (2026-07-15, lane a) — canonical ν-supply carrier threading landed

issue 0118 (a-1) の carrier/producer 側を実装した。generic `S15.Hypothesis` は強化せず、
canonical Section 16 context にだけ pure ν-grid package を保持する:

```lean
structure OddOrder.Peterfalvi.S16.Hypothesis where
  base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)
  nuGridSupply :
    @OddOrder.Peterfalvi.S15.NuGridSupplyData G _ base.finiteG base
  q_lt_p : base.q < base.p
```

`sectionSixteenHypothesis_of_inputs` は `Section16Inputs` の既証明 10 fields から
`nuGridSupply` を直接構成する。既存
`sectionSixteenNuGridSupplyData_of_inputs` は同 carrier projection を返す薄い readout に整理した。
したがって `sectionSixteenHypothesis_of_isMinimalSimpleOdd hG` からも
`.nuGridSupply` が axiom-clean に得られる。

- 検証: `lake build OddOrder.FeitThompson` green (4202 jobs)。
- 公理監査: `lake build OddOrder.AxiomsCheck` green (4210 jobs); 既存 assertions
  `sectionSixteenHypothesis_of_inputs` / `sectionSixteenNuGridSupplyData_of_inputs` /
  `sectionSixteenHypothesis_of_isMinimalSimpleOdd` は全て標準 3 公理のみ。
- **b-5 handoff**: S15 consumer chain は explicit `pins : NuGridSupplyData hyp` を受ける形へ
  restate し、c-owned S16 callers が `hyp.nuGridSupply` を渡す。generic sorried theorem
  `S15.Hypothesis.nuGridSupply` は consumer 0 到達後に retire する。a は b-owned consumer files
  および同 theorem declaration には触れていない。

本変更で a-1 は完了。9096 全体の close 条件は b-5 consumer rewiring + generic theorem retire。
