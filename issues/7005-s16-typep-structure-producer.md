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

---

## ⚠⚠ 重要訂正 (2026-06-18 lane-f, Step 3 深掘り) — type-emptiness は real、enrich 必須を再確認

Step 3 (residual 構成) に入って判明: 上の「tp は tractable」評価は S の**内在構造**には正しいが、
**pairing は arbitrary mp では構成不能**(= 当初の type-emptiness 診断が正しい)。

**論証**: producer は `(mp : Section16MaximalPair G) → Section16TypePStructure mp` で **任意の mp**
を取る。`Section16MaximalPair` 公理 (`theorem88_caseB` = covering) は partner を**共役までしか固定
しない**。canonical partner を `Mstar`、`mp.T := Mstar^g`(g が N(S)∩N(Mstar) 外)とすると:
maximal ✓ / ≠S ✓ / IsTypeNonI ✓(共役不変)/ one_typeII ✓ / covering ✓(共役類同一)を全て満たすが、
`S ⊓ Mstar^g` は一般に位数 pq cyclic でない ⟹ `Section16TypePStructure mp` が**空型** ⟹ residual
`Nonempty(Σ' …, S∩T=W₁⊔W₂ cyclic)` は pathological mp で**偽** ⟹ honestly dischargeable でない。

∴ **producer の sorry は Section16MaximalPair を enrich しない限り honest に埋まらない**(canonical
partner witness を carry させ、mp.T = Mstar を強制)。これは **gap A / LAUNCH step 2 / issue 7006** が
当初から指摘していた通り。「type data で tractable」は **S 内在構造のみ**で、pairing は別問題。

### enrich の entanglement (深掘りで判明)

mp producer `section16MaximalPair_of_isMinimalSimpleOdd` を canonical partner (typeP_duality 経由) で
再構成するには `S14.IsTypeP S`(typeP_duality 入力)が要るが、`IsTypeNonI S → S14.IsTypeP S` の橋は
`proposition_type_classification`(S16:894, **sorry**)に entangle。現 mp producer も既にこれに推移
依存(syntactically sorry-free だが scaffold)。⟹ enrich は §16 sorry'd type-bridge と絡む大きな change。

### 本セッション landing (Step 3 infrastructure)

`typeP_pair_W_structure`(`S16_PairIntersection`): canonical pair の W-side 完全構造
(`S∩T=K⊔Kstar` ∧ cyclic ∧ `K⊓Kstar=⊥` ∧ commute) を gap B + §14 API から組立。enrich 後の tp producer
が pairing 4 field をこれで discharge。

### 正しい次手 (Step 3 本体)

1. **Section16MaximalPair を enrich**: canonical partner witness(K/Kstar/Hall/eq/types/nonconj/
   `IsCyclic(K⊔Kstar)` = `typeP_pair_inf_eq` 入力一式、issue 7006 の field 群)。1 ∃-field でも可。
2. **mp producer 再構成**: typeP_duality 経由で S, Mstar=T を canonical に構成
   (theoremI assembly `S16_MainResults:1047-1078` が template、§16 type-bridge に entangle)。
3. **tp producer discharge**: enriched mp.K/Kstar から `typeP_pair_W_structure` で pairing、
   bridge 補題で prime(II–IV)、type data + coprime 構成で U-side、(14.1)/(13.2) で q<p。
   engine `section16TypePStructure_of_typeData` が assemble(既 sorry-free)。

---

## ✅✅ Step 3 大幅前進 (2026-06-18→19 lane-f) — type-emptiness 解消 + W-side discharge

「続けてください/深いところに」を受け enrich 本体を実行。**type-emptiness を完全解消し、tp producer
の pairing (W-side) を sorry-free 化**。実 sorry 140 据え置き (residual は U-side に縮小)、full build 3860 green。

### landing (全 sorry-free)
1. **`exists_section16MaximalPair_data`** (`FeitThompson`, `852831d0`): canonical type-P dual pair
   `S,T=Mstar` + κ-Hall witness 一式 (BG 14.7)。theoremI branch mirror、case-(a) は Pf (12.17) で排除。
   `open OddOrder.Isaacs` 追加で Ch03 解決、heavy qual。
2. **`Section16MaximalPair` enrich** (`852831d0`): `K, Kstar` + 10 witness field (canonical partner)。
   ⟹ pathological mp.T 排除、`Section16TypePStructure mp` 非空型化。非破壊 (field 追加、lane-b cd 透過)。
3. **mp producer 再構成** (`852831d0`): `exists_section16MaximalPair_data` から choose (nested .choose×4)。
4. **engine → component 化** (`7e970944`): `section16TypePStructure_of_components` (W1/W2/U/V 直接、
   mp.K/mp.Kstar plug-in)。
5. **W-side discharge** (`7e970944`): producer 内で `typeP_pair_W_structure` を mp の witness に適用
   → `S∩T=K⊔Kstar` cyclic + bot + commute を sorry-free 取得。

### 残 residual (U-side のみ、honest = 真・構成可能)

producer の唯一 sorry = `Nonempty (Σ' (U V : Subgroup G), derivedInG S = M_F ⊔ U ∧
derivedInG T = M_F(T) ⊔ V ∧ |K| prime ∧ |Kstar| prime ∧ K ≤ N(U) ∧ Kstar ≤ N(V) ∧ |K| < |Kstar|)`。
= Pf (13.1.b) semidirect data + BG Thm C(10) primality + (13.2.a) ordering。

**残の attack 経路** (genuine §13/§14、bundled ゆえ分割は U が hSderiv∧hSnorm 両方に出るため不可):
- **U-side**: K-normalized complement `U` to M_F in M' (coprime action / Schur-Zassenhaus)。
- **primes**: type-II member は `typeP_structure` の `IsTypeP2→∃q prime |K|=q`; II–IV は bridge
  (`card_kappaHall_eq_derived_index`+`card_W1_eq_derived_index`+型データ common); Type-V は partner 論。
  ⚠ BG 14.7(6) は片側のみ prime 保証 → 両 prime は (13.1)/(8.9) の subtle argument。
- **q<p**: (13.2.a)。

---

## ⛔ U-side residual は Pf §10–12 char theory (lane-b) に gated — loop 診断 (2026-06-19)

`/loop` で U-side residual 攻略を継続 → **primes + ordering は lane-b の char theory に bottom-out**と確定:

- **both-prime** (`|mp.K|`/`|mp.Kstar|` prime) = **Peterfalvi (10.11)** = `theorem88_caseB_prime_orders`
  (`S12_MaximalIII_IV_V.lean:246`, **sorry**)。`Theorem88CaseBData` (W1/W2/W cyclic + S/T nonI + one_typeII)
  から `(|W1|).Prime ∧ (|W2|).Prime` を与える。mp から CaseBData 構成可 (W1=mp.K, W2=mp.Kstar,
  W_cyclic=mp.Z_cyclic) ゆえ **cite 可能だが §12 sorry**。
- **type-V 除外** = **Peterfalvi (10.10)** = `no_typeV_maximal` (`S12:224`, **sorry**)。BG 14.7(6) は片側
  prime のみ保証ゆえ、両 prime は type-V 除外 (III/IV なら型定義 (T7)(1) で prime) に依存。
- **ordering** (`|mp.K| < |mp.Kstar|`) = (13.2.a) "if q<p then S type II" ← (10.10)/(11.9) §10/§11。
  + labeling 問題 (exists_section16MaximalPair_data が κ-Hall size で S/T を選ぶ必要、両 prime 前提で循環的)。
- §10/§11/§12 char files は sorry 多数 (S10_BGInterface 5 / S10_CoherenceWiring 6 /
  S10_MinimalSimpleStructure 13 / S11 9 / S12 10) = lane-b 領域。

### 結論
**tp producer の残 sorry は lane-f では reduce 不能** (primes/ordering は lane-b の §10-12 char theory)。
lane-f は BG 側で producer を限界まで前進させた (type-emptiness 解消 + W-side discharge)。残 residual =
named lane-b 定理 ((10.11) `theorem88_caseB_prime_orders` 等) そのもの。

### lane-f-doable な次手 (count は減らないが residual を精密化)
1. **primes を (10.11) に wire**: mp→`Theorem88CaseBData`→`theorem88_caseB_prime_orders` cite
   (S12 import 要; 依存が lane-b (10.11) に明示化、lane-b landing で auto-resolve)。
2. **U-side complement** (BG-side, 非 char): K-invariant complement U to M_F in M' (coprime action;
   mathlib は `exists_right_complement'_of_coprime` のみ、invariant 版は要構成)。
3. これらを揃えても ordering が gated ゆえ producer は sorry-free 化せず → **真の gate = lane-b §10-12**。

---

## 🤝 引き継ぎ (2026-06-19) — primes cite 済、残 = ordering swap + U-side complement

**producer 現状** (`section16TypePStructure_of_isMinimalSimpleOdd`, `FeitThompson.lean`): honest
gated-endpoint-skeleton。W-side discharge 済 (`typeP_pair_W_structure`)、primes cite 済
(Pf (10.11) `theorem88_caseB_prime_orders`, `70296d47`)。唯一 residual = `Nonempty(Σ' U V, M'=M_F⊔U
∧ M'(T)=M_F(T)⊔V ∧ K≤N(U) ∧ Kstar≤N(V) ∧ |K|<|Kstar|)`。

**残 step 1 = ordering** (`|mp.K|<|mp.Kstar|`, ⚠ honesty 必須):
- `Section16MaximalPair` (`FeitThompson.lean`) に `K_lt_Kstar : Nat.card ↥K < Nat.card ↥Kstar` 追加。
- `exists_section16MaximalPair_data` (同) で確立: `|K|≠|Kstar|` を coprime + `Kstar≠⊥` + `|K|>1` で示し、
  `rcases lt_or_gt_of_ne` で S↔T **swap**（dual witness は typeP_duality の対称出力 +
  `IsConjugateSubgroup.symm`/`Or.symm`/`sup_comm`）。bullet を `have` 化して 2 case 共有すると簡潔。
- mp producer に `K_lt_Kstar := h.<proj>` 追加、tp producer の `hlt := mp.K_lt_Kstar`（residual から除去）。
- ※ cite でなく enrich+swap。count 不変だが residual を honest 化（現状は labeling 次第で偽）。

**残 step 2 = U-side** (`∃U, M'=M_F⊔U ∧ K≤N(U)`, S/T 両側) = Pf (13.1.b):
- K-invariant complement to `M_F` in `M'` (coprime action / Schur-Zassenhaus)。mathlib は
  `Subgroup.exists_right_complement'_of_coprime` のみ → invariant 版要構成（または §12 SubgroupESetup の
  `E₂⊔E₃` 経由を検討、但し M_F vs Msigma の差異注意: type III/IV で M_F≠Msigma）。
- **これで producer 自前 sorry 消滅 → count 140→139**（残依存は named (10.11) のみ = lane-b）。

**終端 gate** = lane-b Pf §10-12 char theory ((10.11)/(10.10)/(13.2))。ordering+U-side 完了でも
primes は (10.11)[sorry] 依存ゆえ axiom-clean 化は lane-b 待ち。

---

## ✅ piece 1 DONE + piece 2 精密スコープ訂正 (2026-06-19 lane-f 再開セッション)

### ✅ piece 1 (ordering honesty) 完了 — commit `b5f05289`
`Section16MaximalPair` に `K_lt_Kstar : Nat.card K < Nat.card K*` を追加し、
`exists_section16MaximalPair_data` で **enrich+swap** により確立 (cite でない):
- 新 S14 補題 `card_kappaHall_ne_one` (type-P の κ-Hall は非自明; `IsTypeP` だけから、
  (10.11) 非依存。`typeP_zTilde_conjClass_gt_half` のインライン重複を抽出・DRY 化) +
  `card_kappaHall_ne_card_Kstar` (|K|≠|K*| = coprime + |K|>1)。
- `lt_or_gt_of_ne` で場合分け、`>` 側は S↔T swap (typeP_duality は (S,K)↔(M*,K*) 対称;
  dual witness = Ne.symm/Or.symm/IsConjugateSubgroup.symm/sup_comm + covering reorder)。
- mp producer を `obtain`(大 And は large-elim 可)で再配線、脆い `.2.2.2…` チェーン排除。
- producer residual から `|K|<|K*|` 除去 (now `mp.K_lt_Kstar`)。**residual が honest 化**
  (旧 residual は labeling 次第で偽)。full build 3657 jobs green、実 sorry 140 維持。

### ⛔ piece 2 (U-side) 精密訂正 — 「TypePData で trivial」は**誤り**、真の (13.1.b) invariant SZ

producer residual = `Nonempty (Σ' U V, derivedInG S = M_F⊔U ∧ derivedInG T = M_F(T)⊔V ∧
mp.K ≤ N(U) ∧ mp.Kstar ≤ N(V))`。本セッションで attack 経路を精査し**2 つの誤った楽観を訂正**:

1. **U=M' (derivedInG S 自身) は CHEAT** (honest でない): `Section16Inputs.U` の拘束は弱い
   (`derivedInG S = M_F⊔U`[M_F≤M' ゆえ U=M' で自明]、`K≤N(U)`[M'◁S ゆえ自明]、counting 定義)
   が、**downstream §16 final-contradiction は強拘束** `u=(p^q-1)/(p-1)`、`N(U)≤L`
   (`S16_NonExistenceG.lean:88,169,45`) を要求。U=M' だと `u=|M'|/c` がこの公式から外れ、
   downstream が **unsatisfiable** ⟹ FT-critical な type-P counting を downstream に hoist する
   だけ ([[scaffold-sorry-free-not-done]])。FT を前進させない。

2. **TypePData.U で conjunct 1 は取れるが conjunct 2 `K≤N(U)` は generic に従わない**:
   - conjunct 1 ✅: `TypePData.derivedInG_eq_fitting_sup_U` (`MaximalSubgroupType:176`) が
     `derivedInG M = M_F ⊔ data.U` を全型で供給 (data.U = 真の complement、|U|=[M':M_F])。
   - conjunct 2 ⛔: **U は M で normal でない** (type-II vacuity 検算): もし U◁M なら U char M'
     (normal Hall) ◁ M ⟹ N(U)⊇M。type II の `normalizer_not_le : ¬N(U)≤M` + M maximal ⟹
     N(U)=G ⟹ U◁G ⟹ U=⊥、しかし type-II core は U≠⊥ で**矛盾**。∴ generic な
     「K≤M≤N(U)」は**偽**。`K≤N(U)` は **κ-Hall/W1 が U を normalize する specific 事実**を要す。

   **原典 Pf (13.1.b)** (`references/peterfalvi/04.15…:7`): "Let U and V be such that
   S=(P⋊U)⋊W₁... **Assume that W₁ normalizes U** ... which is possible by **the remark following
   Definition (8.4)**." ⟹ `W₁ normalizes U` は **W₁-invariant complement の存在 (invariant
   Schur-Zassenhaus)** に依拠する choice。generic data.U では不成立。

### piece 2 の正しいスコープ — multi-step structural assembly (インフラ既存、~150-300 行)

mathlib は basic SZ のみだが **repo に invariant-complement インフラ既存**:
- `exists_subgroupESetup` (`S12_Lemma1211:71`): 任意 maximal M に `SubgroupESetup M E E₁ E₂ E₃`。
- `E ≤ N(E₂⊔E₃)` (`S14:884` `hE23norm`) = E(⊇E₁=κ-part) が E₂⊔E₃ を normalize = **invariant
  complement 内蔵**。
- `aInvariant_piSubgroup_le_aInvariant_hall` (`S01_Solvable:1402`) / `OperatorMaschke` =
  coprime 作用 A-invariant complement (BG §1/§4)。

**route A** (SubgroupESetup): `exists_subgroupESetup mp.S` → E₁ を mp.K (κ-Hall) と同定
[= pairing reconciliation, **crux**] → `derivedInG mp.S = M_F ⊔ (E₂⊔E₃)` 確立 → `hE23norm`。
**route B** (直接): mp.K-invariant complement U を M_F in M' に `aInvariant_*_hall` で構成。
どちらも multi-session、E₁↔mp.K (or 作用 setup) の reconciliation が難所。

**∴ piece 2 = lane-f 所有の genuine 構造論プロジェクト** (char theory でない、正しいレーン)。
quick win でなく loop 不適 (loop は U=M' cheat を取るか空転)。count 140→139 は assembly 完了時。
