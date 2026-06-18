---
id: 7005
slug: s16-typep-structure-producer
title: "Section16Inputs: section16TypePStructure producer (BG §14, lane-f)"
created: 2026-06-18
---

# Section16Inputs: section16TypePStructure producer (BG §14, lane-f)

## 背景

2026-06-18 post-§14 監査で判明した真の long pole = `Section16Inputs` producer の分配
(skeleton commit `80f9aa39`)。本 issue は BG §14 type-P duality 担当ブロック。
**`typeP_duality` は既に proved** (`S14_TypePCounting.lean:7961`, sorry-free + axiom-clean)
ゆえ、本 producer はその proved 定理を cite して構成できる見込み = 良い lead-in。

## やること

- [ ] `section16TypePStructure_of_isMinimalSimpleOdd hG mp : Section16TypePStructure mp`
      (`OddOrder/FeitThompson.lean:272`, 現 `sorry`) を実証明化する。
- [ ] 入力 = 極大対 `mp : Section16MaximalPair G` (lane-g が構成)。
- [ ] 内容 = 型 P 双対構造: `W1 W2 W U V : Subgroup G`、`W = mp.S ⊓ mp.T = W1 ⊔ W2` cyclic、
      `W1 ⊓ W2 = ⊥`、`W1`/`W2` の可換性、導来部分群分解 `S_deriv_eq_PU`/`T_deriv_eq_QV`、
      `W1`/`W2` の正規化条件、素数 `q p` と counting params `u v c d` + 位数等式 + `q_lt_p`。
- [ ] feeder = BG §14 `typeP_duality` (`S14_TypePCounting.lean:7961`) — W cyclic, W₁/W₂,
      補 U/V, counting を供給。`q_lt_p` は (14.1) 由来。

## 完了条件

`section16TypePStructure_of_isMinimalSimpleOdd` の `sorry` が消え、`lake build OddOrder` 緑。

## 進捗 (2026-06-18 lane-f, 後刻) — ✅ 逆包含 (gap B) landing 完了

hub REASSIGN #2 (option 1「難所に正面」) を受け、**逆包含 `M ⊓ Mstar ≤ K ⊔ Kstar`
(= BG Thm 14.7(4) / Thm C(6) / Thm I(2) の `S ∩ T = W`) を完全形式化**
(`aa177257`, sorry-free + axiom-clean, AxiomsCheck 登録済):

- 新 leaf `OddOrder/BG/Ch4_FamilyOfMaximal/S16_PairIntersection.lean`、定理
  `OddOrder.BG.Ch4.S16.typeP_pair_inf_eq : M ⊓ Mstar = K ⊔ Kstar`。
- canonical packaging (typeP_duality の `∃!` 出力 = `Mstar` maximal/type-P/non-conj、
  `Kstar ≤ Mstar`、`Kstar` Hall κ(Mstar)、`K = Msigma Mstar ⊓ C(Kstar)`、`IsCyclic Z`) を
  そのまま入力に取る → consumer から直接呼べる。
- 証明 = mmd L4063 (Thm 14.7 end-of-proof): Step1 `Msigma M ⊓ Mstar = Kstar`
  (σ-decomposition: `⁅W,K⁆ ⊆ Msigma M ⊓ Msigma Mstar = ⊥`) + Step2 (Prop 14.2(b1) +
  cyclic Kstar の characteristic line `X*`)。
- **caveat 回避確認**: prerequisite (Prop 14.2(b1)/(f)、Thm 13.9、typeP_self_member、
  eq_of_card_eq_prime_of_le_isCyclic) は全て既形式化。未形式化 §16 theory (Prop 16.1 等)
  には bottom-out しなかった。

**残 (gap A = lane-g/hub 領域)**: 元の型欠陥は未解消。`Section16MaximalPair` は依然 partner を
共役までしか固定せず、producer `section16TypePStructure_of_isMinimalSimpleOdd` は本補題が
あっても**まだ discharge できない**。次手 = lane-g が `Section16MaximalPair` を本補題で enrich
(W=S∩T cyclic + dichotomy clause 復活) → そこで初めて typeP producer が discharge 可能。
**→ gap A は issue 7006 に分離 (2026-06-18, hub 伝達用)**。

---

## 調査結果 (2026-06-18 lane-f) — ⚠ 現仕様では sorry-free 化が原理的に不可能

精査の結果、**前提「proved `typeP_duality` を cite すれば構成可」は不正確**で、producer は
`Section16MaximalPair` の現定義のもとでは sorry-free 化できない。3 点で検証済み:

1. **病的 mp が `Section16MaximalPair` 公理を満たす（partner が共役までしか固定されない）**:
   covering 条件 `theorem88_caseB` は「各極大は type-I か S か T に**共役**」としか言わない。
   真の partner を `Mstar`、`T' := Mstar^g`（非自明な共役）とすると `T'` も全公理を満たす:
   maximal ✓ / `T' ≠ S` ✓ / `IsTypeNonI T'`（type-P は共役不変）✓ /
   `one_typeII`（`IsTypeP2 Mstar → IsTypeII Mstar` が共役不変）✓ /
   `theorem88_caseB`（共役類は同じ）✓。しかし `mp.S ⊓ T' = S ⊓ Mstar^g` は一般に位数 `qp`
   の cyclic ではない ⟹ 強制された `W = mp.S ⊓ mp.T` が `W_cyclic` + `W_eq_join`(q<p の素数 2 個)
   を満たせない。**∴ producer の出力型は入力公理より真に強く、証明不能**。

2. **gap B（逆包含 = `W = S ∩ T`）が repo に未形式化**: `typeP_duality` は forward
   `K ⊔ Kstar ≤ M ⊓ Mstar` のみ供給（`K ≤ M`, `Kstar ≤ Msigma M ≤ M`, かつ `K ⊔ Kstar ≤ Mstar`
   = S14:4616/6910）。逆 `M ⊓ Mstar ≤ K ⊔ Kstar`（= `W = S ∩ T`）は**どこにも無い**。
   近い `typeP_normalizer_inf_eq`(S14:4684) は `N_G(X) ⊓ M = K ⊔ Kstar` で別物。

3. **`W = W₁ × W₂ = S ∩ T` は Peterfalvi (13.1) の standing hypothesis**
   (`references/peterfalvi/04.15…The_Subgroups_S_and_T.mmd:5`、"Taking (12.17) into account"):
   対 (S,T) の存在と交差構造は **BG §8 (8.8.b) + §10-13 の構造定理の出力**であり、
   `Section16MaximalPair.theorem88_caseB` は (8.8.b) の **covering disjunction のみ**を捉え、
   W=S∩T cyclic 構造・`S=(P⋊U)⋊W₁` 分解・normalizer 条件を**落としている**。

**根本原因**: skeleton split (`80f9aa39`) が `Section16MaximalPair` を (8.8.b) の covering 部分
だけで定義し、構造部分（W=S∩T cyclic, U/V 分解, normalizer）を tp 側に置いたが、tp は mp から
それを**復元できない**（情報が構造境界で失われる）。`derived_decomposition`
(`derivedInG_eq_Msigma_sup_derivedInG_complement` S14:7720) と counting (Lagrange) は available
だが、W=S∩T が無い限り U/V を pin できず連鎖して全 field が落ちる。

**選択肢**（hub 判断）:
- (A) `Section16MaximalPair` を (8.8.b) の構造出力（W=S∩T cyclic + 分解 + normalizer）まで richen
  → 義務は mp producer (lane-g) に移動（やはり §8/§13 構造論の形式化が必要、総量不変）。
- (B) mp+tp を 1 producer に再統合し pairing witness を内部保持（W=S∩T を内部で構成）。
- (C) tp を honest localized sorry のまま据え置き（gated-endpoint-skeleton の趣旨どおり）、
  lane-f を真に unblocked なタスクへ re-task。
- (D) lane-f が gap B の逆包含 `M ⊓ M* ≤ K ⊔ K*`（§8/§13 構造論）を新 leaf で正面形式化
  — 但し gap A（pinning）は残り、単独では producer を discharge しない。

## 参照

- skeleton commit `80f9aa39`、`OddOrder/FeitThompson.lean:196` (`structure Section16TypePStructure mp`),
  `:272` (producer)
- 既証明 input: `OddOrder.BG.Ch4.S14.typeP_duality` (`S14_TypePCounting.lean:7961`)
- 病的 mp の典拠: `S16_MainResults.lean:1014-1050` (Theorem I で S=非I極大→typeP→partner Mstar 構成)
- standing hypothesis: `references/peterfalvi/04.15_pp_75_86_The_Subgroups_S_and_T.mmd:5` ((13.1)(a)(b))
- 関連: 8014 (maximalPair, lane-g, 上流) / 1004 (character_data, lane-b, 下流) / 2009 (POLE-2, lane-h)
- 旧タスク Wielandt (9.1) `CoprimeAction.lean` は orphaned 判定で park (issue 7004 は据え置き)

---

## フィージビリティ監査 + 部分 landing (2026-06-18 lane-f 再開, hub REASSIGN #3 を受けて)

LAUNCH REASSIGN #3 の option-1 チェーン（②enrich + ③tp discharge）に着手。Explore 全域監査
（§14/§15/§16/Pf S15）+ 確認 grep で、**③ tp producer は現 repo 理論で sorry-free 化不能**と確定。
LAUNCH step 3 の「残（U/V 導来分解・counting・normalizer）は §14 既存補題 + Lagrange」は**過大評価**。

### ① 各 field の feeder 監査（FORMALIZED / ABSENT）

| field | 状態 | 根拠 |
|---|---|---|
| `W_eq_inter : W = S ⊓ T` | ✅ FORMALIZED | gap B `typeP_pair_inf_eq` (S16_PairIntersection) |
| `W_cyclic` | ✅ FORMALIZED | `typeP_Z_isCyclic` (S14:7585) |
| `W_eq_join`(W=W1⊔W2, W1=K/W2=K*) `W1_inf_W2_eq_bot` `W1_commutes` | ✅ (K⊔K* cyclic から) | 同上 |
| `S_deriv_eq_PU` `T_deriv_eq_QV` | ✅ FORMALIZED | `derivedInG_eq_Msigma_sup_derivedInG_complement` (S14:7720) + `typeP_derivedInG_isComplement_kappaHall` (S14:7785) |
| `q_prime`/`p_prime` + `q_eq_card_W1`/`p_eq_card_W2`（**対の両側素数位数**） | ⚠ **PARTIAL** | `isTypeP2_kappaHall_prime` (S14:1555) は **type-P₂ 側のみ**（Thm 3.10(a) Frobenius complement 経由）。`hP2disj : IsTypeP2 S ∨ IsTypeP2 Mstar` は OR ゆえ片側のみ保証。**P₁ partner の κ-Hall 素数位数は ABSENT** |
| `q_lt_p` | ❌ **ABSENT** | §14/§15 に prover 無し（Pf (13.2)(a) 由来＝(10.10)/(11.9.b,c) char-theoretic） |
| `W1_normalizes_U` `W2_normalizes_V` + U/V の (13.1)(b) semidirect 構成 | ❌ **ABSENT** | Pf (13.1)(b)「by the remark following Definition (8.4)」＝§8 構造論、未形式化 |

### ② 構造変更（enrich）は obstruction を**移動するだけ・解消しない**（重要）

`Section16TypePStructure mp` は `W = W₁ × W₂`（**両素数**, q<p）+ U/V semidirect を要求。
`Section16MaximalPair` を W/W_eq_inter/W_cyclic（または K/K* witness）で enrich しても、
tp が要求する**素数位数分解**は「W cyclic」より真に強い ⟹ enrich field を mp producer
(`section16MaximalPair_of_isMinimalSimpleOdd`) が構成する段で**同じ absent theory**（対の素数位数・
W₁-normalizes-U）に bottom-out。情報は構造境界で失われるのでなく、**そもそも repo に無い**。
∴ memory [[s16-typep-producer-unfillable]] の「fix=構造変更必須」は不完全 — 構造変更**かつ**
absent §13/§14 理論の両方が要る（どちらか一方では不可）。

### ③ S15.Hypothesis は repo のどこからも CONSTRUCT されない

Explore 確認: `Peterfalvi.S15.Hypothesis` は全参照が `hyp :` パラメータ消費のみ、producer ゼロ。
下流 `basic_structure` (S15_SAndT:236) / `S_coherent` (:263) も依然 sorry。tp producer はこの
未構成 (13.1) データ束の BG 側構造部分に相当 ⟹ 同根の gate。

### 部分 landing（feasible な faithful 進捗）— `536974a9`

gap B を terminal にせず BG **Theorem I clause (2)** に配線:
`theoremI_nilpotentHall_conjugacy_and_type_dichotomy` の type-P-pair 枝に `S ⊓ T = W` を復活
（`typeP_pair_inf_eq` 適用、sorry-free、full build 3860 green、consumer `maximalSubgroup_type_dichotomy`
透過）。tp producer の sorry は**減らない**（absent theory ゆえ）。

### 推奨（hub 判断）— option (C) 寄り

tp producer を honest localized sorry のまま据え置き、lane-f を re-task。理由:
- 真の gate = (a) 対の素数位数 P₁ 側、(b) q<p（**char-theoretic ＝ lane-b 上流**）、(c) W₁-normalizes-U（§8）。
- (b) は (10.10)/(11.9) ＝ §10/§11 character/structure に依存 ＝ lane-f 単独の clean win でない。
- (a)(c) は深い BG §8/§14 構造論。やるなら独立タスクとして scope（issue 化）すべきで、
  「enrich すれば producer が落ちる」という LAUNCH の前提は不成立。

---

## 🔄 重要訂正 (2026-06-18 lane-f, さらに後刻) — tp producer は当初評価より遥かに tractable

「正面から」攻める方針 (ユーザー裁可) で BG 14.7 + Pf (8.8)/(13.1) を精読した結果、
**前回の監査 (Explore) は `OddOrder/GroupTheory/MaximalSubgroupType.lean` を見落としていた**。
型述語 `IsTypeII/III/IV/V` は `TypeIIData/.../TypeVData` を nonempty 包み、各々:
- `typeP : TypePData M` を carry — `W1, W2, W, U, H` + `W_eq`(W=W1⊔W2) + `W_cyclic` +
  `W1_cyclic/W2_cyclic` + `W1/W2_nontrivial` + `M_complement`(W1 が M' を補元) +
  `derived_complement`(H が U を M' 内で補元 ⟹ derivedInG M = H ⊔ U = M_F ⊔ U) +
  `centralizer_W1`(W2 = C_{M'}(W1#)) + `fitting_eq`(M_F = H ⊔ (U ⊓ C(H)) ⟹ C 構造) +
  `normalizer_V` 等、**tp が要求する構造のほぼ全部**。
- `common : TypePNontrivialCore M typeP`(II–IV のみ)= **`(Nat.card W1).Prime`** を carry。

⟹ `mp.S_nonI : IsTypeNonI S` (= II∨III∨IV∨V) は `TypeXData` を **直接** (sorry'd bridge 不要で)
与える。`proposition_type_classification` (S16:894, sorry) は不要。

### tp field の供給元 (修正版)

| field | 供給 |
|---|---|
| `W1 W2 W U` | TypePData (直接) |
| `W_eq_join` `W_cyclic` `W1_inf_W2_eq_bot`(W cyclic+coprime) `W1_commutes_W2`(W abelian) | TypePData |
| `S_deriv_eq_PU` (derivedInG S = M_F ⊔ U) | `derived_complement` + `H_eq` |
| `q_prime`(II–IV) `q_eq_card_W1` | `TypePNontrivialCore` + **`card_W1_eq_derived_index` (本セッション landing)** |
| `c d u v` + card 恒等式 | `fitting_eq`(C=U⊓C(H)) + Lagrange |
| `V` `T_deriv_eq_QV` `p_prime` 等 (T 側) | TypePData_T (対称) |

### 真の残り core (これだけが genuine work、当初の「全部 absent」は誤り)

1. **pairing reconciliation**: `tp.W = mp.S ⊓ mp.T`(= K⊔Kstar via gap B `typeP_pair_inf_eq`)を
   TypePData_S.W / TypePData_T と同定。鍵 = **W1(S) = κ-Hall K_S**(両方 M' の補元 ⟹ 同位数、
   `card_W1_eq_derived_index` で半分済)+ **W2(S) = Kstar_S = W1(T)**(Pf (8.9) の pairing)。
2. **Type-V member の prime**: pair の一方が Type V なら W1 prime が型データに無い(TypeVData は
   carry せず)→ type-II partner 経由(BG Thm C / duality、Pf (9.2) "type-II S with |S:S'|=|W₂|")。
   ※ Pf (13.2)(a) は S を Type II/III に制限ゆえ、実際の (13.1) では Type V を回避できる可能性大。
3. **q < p**: 両 prime 後に relabel で WLOG だが S/T のラベルに紐付くため要設計。
4. **W1_normalizes_U / W2_normalizes_V**: Pf (13.1)(b)「remark following Def (8.4)」。
   `TypePData.normalizer_V`(V-set の正規化)とは別物。TypePData から導けるか要確認。

### 推奨 (更新) — option (D) tractable program として正面

「全部 absent ゆえ lane-f 単独不可」(前回) は**訂正**。tp producer は型データ経由で大半が
definitional に discharge でき、残り core (1)-(4) が genuine。lane-f で段階的に攻める価値あり:
**Step 1** K_S = W1(S) 同定(card 一致は landing 済、subgroup 同定 or 位数で十分か精査)→
**Step 2** gated-endpoint-skeleton で tp engine 化(型データ供給部を sorry-free、残 core を named
residual)→ **Step 3** residual を 1 つずつ。base 7000、lane-f 所有。

### 本セッション landing
- `TypePData.card_W1_eq_derived_index` (`MaximalSubgroupType.lean`, `dc186aab`): |W1| = |M:M'|。
  K↔W1 bridge + 型 II–IV の |K| prime 化の groundwork。full build 3860 green。

---

## ✅ Step 2 完了 (2026-06-18 lane-f) — honest gated-endpoint-skeleton 配線

producer `section16TypePStructure_of_isMinimalSimpleOdd` を engine 経由に再配線、唯一 sorry を
**explicit residual menu に localize**。実 sorry 140 据え置き、full build 3860 green。

### landing
1. `TypePData.card_W1_eq_derived_index` (`MaximalSubgroupType`, `dc186aab`): |W1| = |M:M'|。
2. `card_kappaHall_eq_derived_index` (`S16_PairIntersection`, `9d500108`): |K| = |M:M'| ⟹ |K|=|W1|。
3. `TypePData.derivedInG_eq_fitting_sup_U` (`MaximalSubgroupType`): M' = M_F ⊔ U (S_deriv_eq_PU 供給)。
4. `typePData_of_isTypeNonI` (`MaximalSubgroupType`): IsTypeNonI → Nonempty TypePData。
5. **`section16TypePStructure_of_typeData` engine** (`FeitThompson`, `1a58f5b7`, **sorry-free**):
   TypePData×2 + residual 仮説 → 完全 Section16TypePStructure。25 field 中 ~18 を型データから
   discharge (S/T_deriv, counting Lagrange, primes, q/p/c/d 定義, W_cyclic 等)。
6. producer 再配線 (`7a6abb2c` → honest 化 `bd97bd2e`): residual を
   `Nonempty (Σ' dataS dataT, pairing ∧ primes ∧ normalizer ∧ q<p)` に (真・構成可能命題)。

### Step 3 = 残 residual の discharge (genuine §16/§14, 次の作業)

producer の唯一 sorry = 上記 `Nonempty (Σ' …)` の構成。中身:
1. **canonical data 存在**: W₁(S) ≤ S∩T (= κ-Hall K_S と一致する TypePData の選択)。
   gap B `typeP_pair_inf_eq` が S∩T = K_S ⊔ Kstar_S を供給、bridge 補題 (3)(4) で |K_S|=|W1|。
   但し **K_S = dataS.W1 の同定** (位数一致でなく subgroup 同定) が要 — TypePData を K_S basis で
   構成し直すか、共役で吸収。**これが core difficulty**。
2. **pairing** `S∩T = W₁(S) ⊔ W₁(T)` cyclic/⊓=⊥/commute: gap B + (8.9)。
3. **primes**: II–IV は `TypePNontrivialCore` + bridge (1)(2); Type-V は type-II partner (BG Thm C)。
4. **normalizer** W₁ ≤ N(U): Pf (13.1.b)「remark following Def (8.4)」。
5. **q<p**: 両 prime 後 relabel (S/T ラベル設計)。
