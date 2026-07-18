---
id: 9133
slug: cn-three-step-dichotomy
title: "CLAIM: CN 群の 3-step 二者択一 (Gorenstein Ch12 §1 Cor 1.6) — BG App.D の unlock"
created: 2026-07-18
---

# CLAIM (shared infra): CN 群の 3-step 二者択一 — BG App.D D.1/D.2 の unlock

**claim 主体**: lane c。**予定 leaf**: `OddOrder/GroupTheory/CNGroupStructure.lean` (新規)。
**関連**: issue 3020 (App.D de-opacify 済 + 本ブロッカーの特定)。

## ⚠ 原典の所在 (章番号のずれに注意)

BG App.D は「**G**, Corollary 14.1.6」「Section 14.1」と引用するが、手元の
`references/gorenstein/finite-groups.mmd` では該当内容は **Chapter 12
"GROUPS IN WHICH CENTRALIZERS ARE NILPOTENT"** にある (版差または OCR の章番号ずれ):
- `## Chapter 12` = mmd:7767、`## 1 Basic properties of CN-groups` = mmd:7773、
  `## 2 CN-groups of odd order` = mmd:7861。
- **3-step 群の定義** = mmd:7801、**Theorem 1.5** = mmd:7818、**Corollary 1.6** = mmd:7838。

## 原典の内容 (逐語)

**3-step 群の定義** (素数 `p` に関する、mmd:7801) — 次の 3 条件:
1. `O_{p,p'}(G)` は Frobenius 群で、核が `O_p(G)`、**補群は奇数位数の巡回群**。
2. `G = O_{p,p',p}(G)` かつ `G ⊋ O_{p,p'}(G)` (真の包含)。
3. `G/O_p(G)` は Frobenius 群で、核が `O_{p,p'}(G)/O_p(G)`。

**Theorem 1.5** (mmd:7818): `G` が**可解 CN 群**なら次のいずれか —
(i) `G` は冪零 / (ii) `G` は Frobenius 群で補群が巡回 or (奇数位数巡回 × 一般四元数) /
(iii) `G` は 3-step 群。

**Corollary 1.6** (mmd:7838、Thm 1.5 の即系): `G` が**可解 CN 群**かつ `O_p(G) ≠ 1` なら、
`O_p(G)` が `G` の Sylow `p` であるか、`G` が `p` に関する 3-step 群。
⚠ 仮説は「可解**かつ CN**」であって単なる可解ではない (BG は M ⊆ G が CN 群の部分群ゆえ CN、を使う)。

## BG が実際に消費するのは 2 帰結のみ

BG App.D D.1 の証明 (mmd:5155-5178) は Cor 1.6 で M を 3-step と判定した後、
「定義と短い議論から」次の 2 つだけを使う:
- `O_{p'}(M) = 1` — 定義 1 の Frobenius 性から (正規 p'-部分群は核に自明に交わる)。
- `M/O_{p,p'}(M)` が**非自明 p-群** — 定義 2 (`G = O_{p,p',p}(G)` かつ真の包含) から直ちに。

⟹ **定義 + この 2 帰結は tractable**。実質は Cor 1.6 (= Thm 1.5) の証明。

## Thm 1.5 の証明が要する道具 (repo の在庫状況)

- `C_G(F(G)) ⊆ F(G)` (可解、Gorenstein Thm 6.1.3) — **repo に在り** (Isaacs Fitting 系)。
- Hall 部分群の存在 (可解、Thm 6.4.1) — **repo に在り** (Isaacs Ch03)。
- Frobenius 補群の構造 (Thm 10.3.1: 唯一の involution / Sylow 巡回 / metacyclic) —
  **repo に相当量在り** (Isaacs Ch06 Frobenius, `DQSDRecognition` 等) — 要 verify-port-state。
- **Lemma 1.2 (CN 固有)**: `q`-元が `p`-元を中心化するなら Sylow `p` を中心化する等 — **新規**。
- Thm 1.3.1(ii) / 7.6.2 / 10.1.3 (fpf 自己同型) — 一般論、要在庫確認。

## 進捗 (2026-07-18): **Tier B 到達** — 新 leaf `OddOrder/GroupTheory/CNGroupStructure.lean` (516 行)

**新設した基盤** (repo にも mathlib にも `O_{p,p'}` / `O_{p,p',p}` が存在しなかったので自作):
`opPPrimeCore p G` = `O_{p,p'}(G)`、`opPPrimePCore p G` = `O_{p,p',p}(G)` (既存 `Ch03.oPiPrimePiCore`
と同形の `comap (mk' …)`、`Normal` instance 付き)。

**定義** `IsThreeStepGroup G p` — 原典 3 条件を**逐語**で 4 フィールド化 (条件 2 は
`opPPrimePCore = ⊤` と `opPPrimeCore ≠ ⊤` に分解)。自由 Prop フィールド 0 (検証済)。

**Tier A (BG D.1 が実際に消費する 2 帰結) — 両方 sorry-free**:
- `IsThreeStepGroup.oPiCore_pPrime_eq_bot` — `O_{p'}(G) = ⊥`。
- `IsThreeStepGroup.isPGroup_quotient` + `nontrivial_quotient` — `G/O_{p,p'}(G)` が非自明 p-群。
⟹ BG D.1 の「定義と短い議論から」の部分はこれで埋まる。

**Tier B — Gorenstein Ch.12 §1 Lemma 1.2**: `commute_of_cn_of_commute_ne_one` (sorry-free)。
`C_G(x)`→`C_G(x₁)`→`C_G(y)`→`C_G(y₁)` の 4 パス論法。⚠ **Sylow でなく任意の p-/q-部分群**で証明
(証明がそれ以上を使わないため) = 一般化であって弱化ではない。
他に sorry-free: `IsFrobeniusGroup.eq_bot_of_normal_of_inf_kernel_eq_bot` (再利用可能な一般 Frobenius)、
`IsThreeStepGroup.isSolvable` (Lemma 1.4 の可解性半分)、`commute_of_isNilpotent_of_isPGroup` 他。
**全 25 宣言 axiom-clean**、AxiomsCheck に 5 件登録。

### 非空性 (vacuity) の監査結果
1. **符号化が記法どおりであること**を証明で担保: `opPPrimeCore_map_mk_eq` が条件 3 の核 = 
   `O_{p'}(G/O_p(G))`、`oPiCore_subgroupOf_map_subtype` が条件 1 の核 = `O_p(G)` を示す
   ⟹ `comap`/`subgroupOf` 符号化が黙って `⊥`/`⊤` に潰れていないことを排除。
2. **条件群が同時使用可能** (偶然矛盾でない): `isSolvable` が条件 1 (巡回補群) と条件 2 (p-群商) を
   意図した経路で消費して実結論を出す — 退化符号化ならこの経路は通らない。
3. **具体的 witness (議論のみ、Lean 未構成)**: `F_{3⁶} ⋊ (C₇ ⋊ C₃)` (位数 3⁷·7) が `p=3` で 3-step。
   `O_3 = F_{3⁶}`、`O_{3,3'} = F_{3⁶}·C₇` は Frobenius (ord_7(3)=6 ゆえ `F_{3⁶}` は自由 `F_3[C₇]`-加群)、
   `G/O_3 = C₇⋊C₃` は Frobenius (3 ∣ 7−1)、`G/O_{3,3'} = C₃` 非自明。
   ⚠ **これは AppD docstring が D.1 の反例に使う群と同一** — 3-step 群が D.1 の反例形そのものゆえ整合。
   → **Lean での witness 構成は未了 = 監査の唯一の穴** (follow-up)。

### 残 sorry は 1 件のみ = Cor 1.6 (`oPiCore_isSylow_or_isThreeStepGroup`)
正直かつ完全な形で statement 済 (`[IsSolvable G]` + CN + `O_p(G) ≠ ⊥` → Sylow ∨ 3-step)。ブロッカー:
1. `C_G(F(G)) ≤ F(G)` — **repo に在る** (`OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting`) が
   **`OddOrder.BG` 配下**。`GroupTheory` leaf が `BG` を import するのは階層衛生上まずいので、
   まず `Isaacs`/`GroupTheory` へ移設したい。⚠ **数学的障害でなく配置の問題**。
2. Gorenstein Thm 5.3.5 (互いに素な作用 `K = [R,K]·C_K(R)`) — **不在**。
3. Gorenstein Thm 10.3.1(iv)(v) (位数 `qr` の部分群は巡回 / metacyclic 補群) — **不在**
   (`IsMetacyclic` はあるが Frobenius 理論と未接続)。
4. Gorenstein Thm 1.3.1(ii) (全 Sylow が巡回 or 四元数 ⟹ 構造) — **不在**。
5. Gorenstein Lemma 10.1.3 (fpf 自己同型が `K/F` に降りる) — **不在**。
⟹ 2/4/5 が実質的な穴で複数 session 規模。**D.1 は未着地ゆえ `AppD_CNGroups.lean` は無変更**。

⚠ **優先順位の訂正 (2026-07-18)**: 一時「配置問題 (1) を直せばブロッカーが 5→4 に減る」と書いたが
これは**誤解を招く数え方**だった。残る 2/3/4/5 は実質的な数学的欠落なので、**配置を直しても
Cor 1.6 の数学は 1 ミリも進まない** (純粋な準備作業)。移設自体は正当な階層衛生 (P. Hall の一般定理が
BG 固有 file に在る) だが、**Cor 1.6 の数学が揃う段で行うのが適切**で、今単独でやる価値は低い。
移設の規模: `centralizer_fitting_le_fitting` + private helper 2 件
(`exists_minimal_normal_le_not_le` / `inf_subgroupOf_le_center_of_le_centralizer`) の移動 +
BG 内 8 箇所の呼び出し更新 (no-wrapper 方針ゆえ alias は置かない)。

### 申し送り
`IsCNGroup` は現在 `BG/AppD_CNGroups.lean` にある。AppD が Cor 1.6 を消費する段になると
`GroupTheory` leaf ← `AppD` の循環になるため、**そのとき `IsCNGroup` を本 leaf へ移設**すること
(現状 Lemma 1.2 は CN 仮説を展開形 `∀ z ≠ 1, IsNilpotent ↥(centralizer {z})` で取っており、
これは `IsCNGroup` と定義的に同一ゆえ重複定義は無い)。

## 段階的完了条件 (tier)

1. **tier 1**: `IsThreeStepGroup` を定義 → Cor 1.6 を証明 → BG App.D の D.1 → D.2 を閉じる。
2. **tier 2**: 定義 + BG が使う 2 帰結を sorry-free で証明 (これだけでも D.1 の「短い議論」部分が埋まる)
   + Lemma 1.2 (CN 固有) を証明 + Thm 1.5 の骨組み。Cor 1.6 は honest statement + sorry。
3. **tier 3**: 上記が停まるなら、どの補題が抵抗するか・repo/mathlib に何が無いかを precise に記録。

⚠ **Gorenstein の章節を独立に全形式化することはしない** (CLAUDE.md 明示禁止)。
必要なのは Cor 1.6 とその 2 帰結に至る最小経路のみ。

## 参照
- `OddOrder/BG/AppD_CNGroups.lean` (de-opacify 済、`IsCNGroup` は既存)、BG mmd:5132-5199。
- issue 3020 (Isaacs 代替不可の検証結果 — Isaacs に CN 群も 3-step 群も無し)。
- ⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ他レーンは着手前に本 claim を確認のこと。
